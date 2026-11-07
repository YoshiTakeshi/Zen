package main

// The leaf circuit of a strike (SPEC 4.3, 4.4) — Jen-0 version.
//
// One proof certifies, for LeafSize transfers:
//   - each carries a valid EdDSA signature by its sender's key,
//   - amount and fee are 64-bit, and the fee is inside Jen's fineness limits,
//   - the public BatchDigest commits to every field of every transfer plus the
//     sender keys, so the proof cannot be reused for other transfers,
//   - the public FeeTotal is the exact sum of fees,
//   - the public Prover (minter index + 1) binds the proof to its minter:
//     changing the minter invalidates the proof ("unique hammer").
//
// Because the proof certifies the signatures, blocks store transfers WITHOUT
// signatures or public keys (types.go: CTx).

import (
	"bytes"
	"fmt"
	"os"
	"path/filepath"
	"time"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	tedwards "github.com/consensys/gnark-crypto/ecc/twistededwards"
	"github.com/consensys/gnark/backend/groth16"
	"github.com/consensys/gnark/constraint"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
	"github.com/consensys/gnark/std/algebra/native/twistededwards"
	"github.com/consensys/gnark/std/hash"
	cmimc "github.com/consensys/gnark/std/hash/mimc"
	"github.com/consensys/gnark/std/signature/eddsa"
)

type txWitness struct {
	From, To, Amount, Fee, Nonce frontend.Variable
	Pub                          eddsa.PublicKey
	Sig                          eddsa.Signature
}

type LeafCircuit struct {
	BatchDigest frontend.Variable `gnark:",public"`
	FeeTotal    frontend.Variable `gnark:",public"`
	Prover      frontend.Variable `gnark:",public"`
	Txs         [LeafSize]txWitness
}

func hashVars(h hash.FieldHasher, xs ...frontend.Variable) frontend.Variable {
	h.Reset()
	h.Write(xs...)
	return h.Sum()
}

func (c *LeafCircuit) Define(api frontend.API) error {
	curve, err := twistededwards.NewEdCurve(api, tedwards.BN254)
	if err != nil {
		return err
	}
	hm, err := cmimc.NewMiMC(api)
	if err != nil {
		return err
	}
	var h hash.FieldHasher = &hm

	fees := frontend.Variable(0)
	digest := frontend.Variable(0)
	for i := range c.Txs {
		t := &c.Txs[i]
		api.ToBinary(t.Amount, 64)
		api.ToBinary(t.Fee, 64)
		total := api.Add(t.Amount, t.Fee)
		// fee * 10000 >= amount + fee
		api.ToBinary(api.Sub(api.Mul(t.Fee, FeeMinDen), total), 80)
		// fee * 100 <= 6 * (amount + fee)
		api.ToBinary(api.Sub(api.Mul(total, FeeMaxNum), api.Mul(t.Fee, FeeMaxDen)), 80)

		msg := hashVars(h, t.From, t.To, t.Amount, t.Fee, t.Nonce)
		h.Reset() // eddsa.Verify writes into the hasher without resetting it
		if err := eddsa.Verify(curve, t.Sig, msg, t.Pub, h); err != nil {
			return err
		}
		// chain the digest: d = MiMC(d, msg, pubX, pubY)
		digest = hashVars(h, digest, msg, t.Pub.A.X, t.Pub.A.Y)
		fees = api.Add(fees, t.Fee)
	}
	api.AssertIsEqual(digest, c.BatchDigest)
	api.AssertIsEqual(fees, c.FeeTotal)
	api.AssertIsDifferent(c.Prover, 0)
	return nil
}

// BatchDigestNative computes the same digest outside the circuit, from compact
// transfers and the senders' public keys (which nodes read from the state).
func BatchDigestNative(txs [LeafSize]CTx, pubs [LeafSize]*PubKey) fr.Element {
	d := feU(0)
	for i := range txs {
		m := TxMessage(txs[i])
		d = mimcHash(d, m, pubs[i].A.X, pubs[i].A.Y)
	}
	return d
}

// ---------------------------------------------------------------- keys on disk

type Prover struct {
	cs constraint.ConstraintSystem
	pk groth16.ProvingKey
	vk groth16.VerifyingKey
}

func compileLeaf() constraint.ConstraintSystem {
	cs, err := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, &LeafCircuit{})
	if err != nil {
		panic(err)
	}
	return cs
}

// SetupKeys runs the local Groth16 setup once and writes the keys.
// A real network needs a multi-party ceremony or a setup-free proof system.
func SetupKeys(dir string) error {
	t0 := time.Now()
	cs := compileLeaf()
	pk, vk, err := groth16.Setup(cs)
	if err != nil {
		return err
	}
	os.MkdirAll(dir, 0o755)
	for name, w := range map[string]interface{ WriteTo(w interface{ Write([]byte) (int, error) }) (int64, error) }{} {
		_, _ = name, w
	}
	var pb, vb bytes.Buffer
	pk.WriteTo(&pb)
	vk.WriteTo(&vb)
	if err := os.WriteFile(filepath.Join(dir, "leaf.pk"), pb.Bytes(), 0o644); err != nil {
		return err
	}
	if err := os.WriteFile(filepath.Join(dir, "leaf.vk"), vb.Bytes(), 0o644); err != nil {
		return err
	}
	fmt.Printf("setup: %d constraints, %.1f MB proving key, %d B verifying key, %s\n",
		cs.GetNbConstraints(), float64(pb.Len())/1e6, vb.Len(), time.Since(t0).Round(time.Millisecond))
	return nil
}

func LoadProver(dir string) (*Prover, error) {
	p := &Prover{cs: compileLeaf(), pk: groth16.NewProvingKey(ecc.BN254), vk: groth16.NewVerifyingKey(ecc.BN254)}
	pb, err := os.ReadFile(filepath.Join(dir, "leaf.pk"))
	if err != nil {
		return nil, err
	}
	vb, err := os.ReadFile(filepath.Join(dir, "leaf.vk"))
	if err != nil {
		return nil, err
	}
	if _, err := p.pk.ReadFrom(bytes.NewReader(pb)); err != nil {
		return nil, err
	}
	if _, err := p.vk.ReadFrom(bytes.NewReader(vb)); err != nil {
		return nil, err
	}
	return p, nil
}

// Prove builds a leaf proof for signed transfers.
func (p *Prover) Prove(txs [LeafSize]Tx, pubs [LeafSize]*PubKey, minter uint32) ([]byte, uint64, error) {
	var w LeafCircuit
	var ctxs [LeafSize]CTx
	fee := uint64(0)
	for i := range txs {
		c := txs[i].Compact()
		ctxs[i] = c
		w.Txs[i] = txWitness{From: c.From, To: c.To, Amount: c.Amount, Fee: c.Fee, Nonce: c.Nonce}
		w.Txs[i].Pub.Assign(tedwards.BN254, pubs[i].Bytes())
		w.Txs[i].Sig.Assign(tedwards.BN254, txs[i].Sig)
		fee += c.Fee
	}
	w.BatchDigest = BatchDigestNative(ctxs, pubs)
	w.FeeTotal = fee
	w.Prover = uint64(minter) + 1
	full, err := frontend.NewWitness(&w, ecc.BN254.ScalarField())
	if err != nil {
		return nil, 0, err
	}
	proof, err := groth16.Prove(p.cs, p.pk, full)
	if err != nil {
		return nil, 0, err
	}
	var b bytes.Buffer
	proof.WriteTo(&b)
	return b.Bytes(), fee, nil
}

// Verify checks a strike's proof against its public inputs (~1–2 ms).
func (p *Prover) Verify(s *Strike, pubs [LeafSize]*PubKey) error {
	proof := groth16.NewProof(ecc.BN254)
	if _, err := proof.ReadFrom(bytes.NewReader(s.Proof)); err != nil {
		return fmt.Errorf("malformed proof: %w", err)
	}
	pub := LeafCircuit{
		BatchDigest: BatchDigestNative(s.Txs, pubs),
		FeeTotal:    s.FeeTotal,
		Prover:      uint64(s.Minter) + 1,
	}
	for i := range pub.Txs { // public-only witness ignores these, but they must be assignable
		pub.Txs[i] = txWitness{From: 0, To: 0, Amount: 0, Fee: 0, Nonce: 0}
	}
	pw, err := frontend.NewWitness(&pub, ecc.BN254.ScalarField(), frontend.PublicOnly())
	if err != nil {
		return err
	}
	return groth16.Verify(proof, p.vk, pw)
}
