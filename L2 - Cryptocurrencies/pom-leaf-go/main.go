// pom-leaf: a REAL zero-knowledge "leaf strike" for Proof of Minting.
//
// One proof certifies that K signed transfers are valid and moves the state
// root from OldRoot to NewRoot:
//   - every transfer carries a valid EdDSA signature (BabyJubjub on BN254) of its sender
//   - sender and receiver are accounts in a Merkle tree of 1024 accounts
//   - sender nonce matches and is incremented (no replay)
//   - balance covers amount + fee (no overspend, 64-bit amounts)
//   - fee is inside the Golden Yen fineness limits: 0.01% <= fee/(amount+fee) <= 2.5%
//   - the sum of all fees is exposed as a public value (the fee pot)
//   - the prover's address is a public input: the proof is only valid with that address,
//     so nobody can take credit for someone else's strike
//
// Proof system: Groth16 over BN254 (gnark). Hash: Poseidon2.
// The setup below is generated locally (fine for a test; a real network needs a ceremony).
//
//   go run . -k 16
package main

import (
	"bytes"
	"crypto/rand"
	"flag"
	"fmt"
	"math/big"
	mrand "math/rand"
	"os"
	"runtime"
	"time"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr/poseidon2"
	tedwards "github.com/consensys/gnark-crypto/ecc/twistededwards"
	nativeeddsa "github.com/consensys/gnark-crypto/signature/eddsa"
	"github.com/consensys/gnark-crypto/signature"
	"github.com/consensys/gnark/backend/groth16"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
	"github.com/consensys/gnark/std/algebra/native/twistededwards"
	"github.com/consensys/gnark/std/hash"
	p2 "github.com/consensys/gnark/std/hash/poseidon2"
	"github.com/consensys/gnark/std/signature/eddsa"
)

const Depth = 10 // 2^10 = 1024 accounts

// ---------------------------------------------------------------- circuit

type TxWitness struct {
	SenderIdx, ReceiverIdx frontend.Variable
	Amount, Fee, Nonce     frontend.Variable
	SenderPub              eddsa.PublicKey
	Sig                    eddsa.Signature
	SenderBal              frontend.Variable
	SenderPath             [Depth]frontend.Variable
	ReceiverPubX           frontend.Variable
	ReceiverPubY           frontend.Variable
	ReceiverBal            frontend.Variable
	ReceiverNonce          frontend.Variable
	ReceiverPath           [Depth]frontend.Variable
}

type LeafCircuit struct {
	OldRoot  frontend.Variable `gnark:",public"`
	NewRoot  frontend.Variable `gnark:",public"`
	FeeTotal frontend.Variable `gnark:",public"`
	Prover   frontend.Variable `gnark:",public"`
	Txs      []TxWitness
}

func hashN(h hash.FieldHasher, xs ...frontend.Variable) frontend.Variable {
	h.Reset()
	h.Write(xs...)
	return h.Sum()
}

func rootFrom(api frontend.API, h hash.FieldHasher, leaf, idx frontend.Variable, path [Depth]frontend.Variable) frontend.Variable {
	bits := api.ToBinary(idx, Depth)
	cur := leaf
	for i := 0; i < Depth; i++ {
		l := api.Select(bits[i], path[i], cur)
		r := api.Select(bits[i], cur, path[i])
		cur = hashN(h, l, r)
	}
	return cur
}

func (c *LeafCircuit) Define(api frontend.API) error {
	curve, err := twistededwards.NewEdCurve(api, tedwards.BN254)
	if err != nil {
		return err
	}
	h, err := p2.NewMerkleDamgardHasher(api)
	if err != nil {
		return err
	}
	root := c.OldRoot
	fees := frontend.Variable(0)
	for _, t := range c.Txs {
		// amounts are 64-bit
		api.ToBinary(t.Amount, 64)
		api.ToBinary(t.Fee, 64)
		// fineness limits: fee*10000 >= amount+fee  and  fee*40 <= amount+fee
		total := api.Add(t.Amount, t.Fee)
		api.ToBinary(api.Sub(api.Mul(t.Fee, 10000), total), 72)
		api.ToBinary(api.Sub(total, api.Mul(t.Fee, 40)), 72)

		// signature of the sender over the transfer
		msg := hashN(h, t.SenderIdx, t.ReceiverIdx, t.Amount, t.Fee, t.Nonce)
		if err := eddsa.Verify(curve, t.Sig, msg, t.SenderPub, h); err != nil {
			return err
		}

		// sender leaf is in the current tree
		oldS := hashN(h, t.SenderPub.A.X, t.SenderPub.A.Y, t.SenderBal, t.Nonce)
		api.AssertIsEqual(rootFrom(api, h, oldS, t.SenderIdx, t.SenderPath), root)
		// balance covers amount + fee
		newBal := api.Sub(t.SenderBal, total)
		api.ToBinary(newBal, 64)
		newS := hashN(h, t.SenderPub.A.X, t.SenderPub.A.Y, newBal, api.Add(t.Nonce, 1))
		root = rootFrom(api, h, newS, t.SenderIdx, t.SenderPath)

		// receiver leaf is in the updated tree, credit the amount
		oldR := hashN(h, t.ReceiverPubX, t.ReceiverPubY, t.ReceiverBal, t.ReceiverNonce)
		api.AssertIsEqual(rootFrom(api, h, oldR, t.ReceiverIdx, t.ReceiverPath), root)
		newR := hashN(h, t.ReceiverPubX, t.ReceiverPubY, api.Add(t.ReceiverBal, t.Amount), t.ReceiverNonce)
		root = rootFrom(api, h, newR, t.ReceiverIdx, t.ReceiverPath)

		fees = api.Add(fees, t.Fee)
	}
	api.AssertIsEqual(root, c.NewRoot)
	api.AssertIsEqual(fees, c.FeeTotal)
	api.AssertIsDifferent(c.Prover, 0) // binds the prover address into the constraint system
	return nil
}

// ---------------------------------------------------------------- native state (minter side)

type Account struct {
	Key   signature.Signer
	PubX  fr.Element
	PubY  fr.Element
	Bal   uint64
	Nonce uint64
}

func nh(xs ...fr.Element) fr.Element {
	h := poseidon2.NewMerkleDamgardHasher()
	for _, x := range xs {
		b := x.Bytes()
		h.Write(b[:])
	}
	var out fr.Element
	out.SetBytes(h.Sum(nil))
	return out
}

func u(v uint64) fr.Element { var e fr.Element; e.SetUint64(v); return e }

type Tree struct {
	Acc   []Account
	nodes [Depth + 1][]fr.Element
}

func (t *Tree) leaf(i int) fr.Element {
	a := t.Acc[i]
	return nh(a.PubX, a.PubY, u(a.Bal), u(a.Nonce))
}

func (t *Tree) rebuild() {
	n := 1 << Depth
	t.nodes[0] = make([]fr.Element, n)
	for i := 0; i < n; i++ {
		t.nodes[0][i] = t.leaf(i)
	}
	for l := 1; l <= Depth; l++ {
		n /= 2
		t.nodes[l] = make([]fr.Element, n)
		for i := 0; i < n; i++ {
			t.nodes[l][i] = nh(t.nodes[l-1][2*i], t.nodes[l-1][2*i+1])
		}
	}
}

func (t *Tree) update(i int) {
	t.nodes[0][i] = t.leaf(i)
	for l := 1; l <= Depth; l++ {
		i /= 2
		t.nodes[l][i] = nh(t.nodes[l-1][2*i], t.nodes[l-1][2*i+1])
	}
}

func (t *Tree) Root() fr.Element { return t.nodes[Depth][0] }

func (t *Tree) path(i int) (p [Depth]frontend.Variable) {
	for l := 0; l < Depth; l++ {
		p[l] = t.nodes[l][i^1]
		i /= 2
	}
	return
}

func newTree(rng *mrand.Rand) *Tree {
	t := &Tree{Acc: make([]Account, 1<<Depth)}
	for i := range t.Acc {
		k, _ := nativeeddsa.New(tedwards.BN254, rand.Reader)
		pb := k.Public().Bytes()
		var pk eddsaPub
		pk.parse(pb)
		t.Acc[i] = Account{Key: k, PubX: pk.x, PubY: pk.y, Bal: uint64(100+rng.Intn(10000)) * 1_000_000_000_000}
	}
	t.rebuild()
	return t
}

type eddsaPub struct{ x, y fr.Element }

// decompress the BN254 twisted-Edwards public key via gnark's circuit-side assigner
func (p *eddsaPub) parse(b []byte) {
	var pk eddsa.PublicKey
	pk.Assign(tedwards.BN254, b)
	p.x.SetBigInt(toBig(pk.A.X))
	p.y.SetBigInt(toBig(pk.A.Y))
}

func toBig(v frontend.Variable) *big.Int {
	switch x := v.(type) {
	case *big.Int:
		return x
	case big.Int:
		return &x
	case []byte:
		return new(big.Int).SetBytes(x)
	default:
		var b big.Int
		b.SetString(fmt.Sprint(x), 10)
		return &b
	}
}

type Transfer struct {
	From, To    int
	Amount, Fee uint64
}

// buildWitness applies the transfers to the tree and returns the full assignment.
func buildWitness(t *Tree, txs []Transfer, prover fr.Element, corruptSig bool) (*LeafCircuit, error) {
	w := &LeafCircuit{Txs: make([]TxWitness, len(txs))}
	w.OldRoot = t.Root()
	var fees uint64
	for i, tx := range txs {
		s, r := &t.Acc[tx.From], &t.Acc[tx.To]
		msg := nh(u(uint64(tx.From)), u(uint64(tx.To)), u(tx.Amount), u(tx.Fee), u(s.Nonce))
		mb := msg.Bytes()
		sig, err := s.Key.Sign(mb[:], poseidon2.NewMerkleDamgardHasher())
		if err != nil {
			return nil, err
		}
		if corruptSig && i == 0 {
			sig[len(sig)-1] ^= 1
		}
		tw := &w.Txs[i]
		tw.SenderIdx, tw.ReceiverIdx = tx.From, tx.To
		tw.Amount, tw.Fee, tw.Nonce = tx.Amount, tx.Fee, s.Nonce
		tw.SenderPub.Assign(tedwards.BN254, s.Key.Public().Bytes())
		tw.Sig.Assign(tedwards.BN254, sig)
		tw.SenderBal = s.Bal
		tw.SenderPath = t.path(tx.From)
		// apply sender side
		if s.Bal < tx.Amount+tx.Fee {
			return nil, fmt.Errorf("overspend")
		}
		s.Bal -= tx.Amount + tx.Fee
		s.Nonce++
		t.update(tx.From)
		// receiver side, path in the updated tree
		tw.ReceiverPubX, tw.ReceiverPubY = r.PubX, r.PubY
		tw.ReceiverBal, tw.ReceiverNonce = r.Bal, r.Nonce
		tw.ReceiverPath = t.path(tx.To)
		r.Bal += tx.Amount
		t.update(tx.To)
		fees += tx.Fee
	}
	w.NewRoot = t.Root()
	w.FeeTotal = fees
	w.Prover = prover
	return w, nil
}

func randomTransfers(rng *mrand.Rand, k int) []Transfer {
	out := make([]Transfer, k)
	for i := range out {
		from, to := rng.Intn(1<<Depth), rng.Intn(1<<Depth)
		for to == from {
			to = rng.Intn(1 << Depth)
		}
		amount := uint64(1+rng.Intn(50)) * 1_000_000_000_000
		rate := 0.0002 + rng.Float64()*0.02 // inside 0.01% .. 2.5%
		fee := uint64(float64(amount) * rate / (1 - rate))
		out[i] = Transfer{from, to, amount, fee}
	}
	return out
}

func cloneTree(t *Tree) *Tree {
	c := &Tree{Acc: make([]Account, len(t.Acc))}
	copy(c.Acc, t.Acc)
	for l := range t.nodes {
		c.nodes[l] = append([]fr.Element(nil), t.nodes[l]...)
	}
	return c
}

// ---------------------------------------------------------------- main

func main() {
	k := flag.Int("k", 16, "transfers per leaf strike")
	runs := flag.Int("runs", 3, "proofs to time")
	flag.Parse()
	rng := mrand.New(mrand.NewSource(7))

	fmt.Printf("Proof of Minting - real leaf strike: %d signed transfers, %d accounts, Groth16/BN254, %d CPU cores\n\n",
		*k, 1<<Depth, runtime.NumCPU())

	t0 := time.Now()
	circuit := &LeafCircuit{Txs: make([]TxWitness, *k)}
	cs, err := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, circuit)
	must(err)
	fmt.Printf("circuit      : %d constraints (%d per transfer), compiled in %s\n",
		cs.GetNbConstraints(), cs.GetNbConstraints() / *k, time.Since(t0).Round(time.Millisecond))

	t0 = time.Now()
	pk, vk, err := groth16.Setup(cs)
	must(err)
	var pkb, vkb bytes.Buffer
	pk.WriteTo(&pkb)
	vk.WriteTo(&vkb)
	fmt.Printf("setup        : %s (proving key %.1f MB, verifying key %d bytes) - local test setup\n",
		time.Since(t0).Round(time.Millisecond), float64(pkb.Len())/1e6, vkb.Len())

	tree := newTree(rng)
	prover := u(0xA11CE) // the minter's address

	var proveTimes []time.Duration
	var lastProof groth16.Proof
	var lastPub *LeafCircuit
	for r := 0; r < *runs; r++ {
		txs := randomTransfers(rng, *k)
		w, err := buildWitness(tree, txs, prover, false)
		must(err)
		full, err := frontend.NewWitness(w, ecc.BN254.ScalarField())
		must(err)
		t0 = time.Now()
		proof, err := groth16.Prove(cs, pk, full)
		must(err)
		proveTimes = append(proveTimes, time.Since(t0))
		pub, _ := full.Public()
		t0 = time.Now()
		must(groth16.Verify(proof, vk, pub))
		vt := time.Since(t0)
		var pb bytes.Buffer
		proof.WriteTo(&pb)
		fmt.Printf("strike %d     : proved in %s, verified in %s, proof %d bytes, fees in strike %.4f YEN\n",
			r+1, proveTimes[r].Round(time.Millisecond), vt.Round(time.Microsecond), pb.Len(), float64(w.FeeTotal.(uint64))/1e12)
		lastProof, lastPub = proof, w
	}

	fmt.Println("\nattacks (each must fail):")
	// 1. someone takes the proof and claims it under their own address
	stolen := *lastPub
	stolen.Prover = u(0xBADBAD)
	sw, _ := frontend.NewWitness(&stolen, ecc.BN254.ScalarField(), frontend.PublicOnly())
	report("claim another minter's proof under a new address", groth16.Verify(lastProof, vk, sw))
	// 2. claim a different resulting state
	forged := *lastPub
	forged.NewRoot = u(12345)
	fw, _ := frontend.NewWitness(&forged, ecc.BN254.ScalarField(), frontend.PublicOnly())
	report("claim a different new state root", groth16.Verify(lastProof, vk, fw))
	// 3. claim more fees than were paid
	inflated := *lastPub
	inflated.FeeTotal = lastPub.FeeTotal.(uint64) + 1
	iw, _ := frontend.NewWitness(&inflated, ecc.BN254.ScalarField(), frontend.PublicOnly())
	report("claim a bigger fee pot", groth16.Verify(lastProof, vk, iw))
	// 4. a forged signature: no valid proof can be produced
	bad, err := buildWitness(cloneTree(tree), randomTransfers(rng, *k), prover, true)
	must(err)
	bw, _ := frontend.NewWitness(bad, ecc.BN254.ScalarField())
	_, err = groth16.Prove(cs, pk, bw)
	report("prove a block containing a forged signature", errOrNil(err))
	// 5. a fee above 2.5%
	txs := randomTransfers(rng, *k)
	txs[0].Fee = txs[0].Amount / 10
	bad2, err := buildWitness(cloneTree(tree), txs, prover, false)
	must(err)
	bw2, _ := frontend.NewWitness(bad2, ecc.BN254.ScalarField())
	_, err = groth16.Prove(cs, pk, bw2)
	report("prove a transfer with a 10% fee", errOrNil(err))

	var sum time.Duration
	for _, d := range proveTimes {
		sum += d
	}
	avg := sum / time.Duration(len(proveTimes))
	fmt.Printf("\nsummary k=%d: %d constraints, average prove %s on %d cores\n", *k, cs.GetNbConstraints(), avg.Round(time.Millisecond), runtime.NumCPU())
}

func report(name string, err error) {
	if err != nil {
		fmt.Printf("  REJECTED  %s\n", name)
	} else {
		fmt.Printf("  ACCEPTED  %s   <-- problem!\n", name)
		os.Exit(1)
	}
}

func errOrNil(err error) error { return err }

func must(err error) {
	if err != nil {
		panic(err)
	}
}
