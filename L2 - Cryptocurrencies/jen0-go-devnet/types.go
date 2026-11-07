package main

// Data types, hashing and keys (SPEC 3, 4).

import (
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"fmt"
	"math/big"

	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr/mimc"
	"github.com/consensys/gnark-crypto/ecc/bn254/twistededwards/eddsa"
)

// Hash32 is a 32-byte hash, JSON-encoded as hex.
type Hash32 [32]byte

func (h Hash32) String() string            { return hex.EncodeToString(h[:]) }
func (h Hash32) Short() string             { return hex.EncodeToString(h[:4]) }
func (h Hash32) MarshalText() ([]byte, error) { return []byte(h.String()), nil }
func (h *Hash32) UnmarshalText(b []byte) error {
	_, err := hex.Decode(h[:], b)
	return err
}

// ---------------------------------------------------------------- transactions

// Tx is a transfer as it travels through the pool: with its signature.
type Tx struct {
	From   uint32 `json:"from"`   // sender account index
	To     uint32 `json:"to"`     // receiver account index
	Amount uint64 `json:"amount"` // picograms
	Fee    uint64 `json:"fee"`    // picograms
	Nonce  uint64 `json:"nonce"`
	Sig    []byte `json:"sig"` // EdDSA (BabyJubjub over BN254, MiMC) — not stored in blocks
}

// CTx is the compact form stored in a minted block: no signature, no key.
// The leaf proof certifies that a valid signature existed (SPEC 4.4).
type CTx struct {
	From   uint32 `json:"from"`
	To     uint32 `json:"to"`
	Amount uint64 `json:"amount"`
	Fee    uint64 `json:"fee"`
	Nonce  uint64 `json:"nonce"`
}

func (t *Tx) Compact() CTx { return CTx{t.From, t.To, t.Amount, t.Fee, t.Nonce} }

func (c CTx) ID() Hash32 {
	var b bytes.Buffer
	binary.Write(&b, binary.BigEndian, c)
	return sha256.Sum256(b.Bytes())
}

// FeeOK applies the fineness limits (SPEC 3) in integer arithmetic,
// identical to the circuit's constraints.
func FeeOK(amount, fee uint64) bool {
	total := new(big.Int).Add(new(big.Int).SetUint64(amount), new(big.Int).SetUint64(fee))
	lo := new(big.Int).Mul(new(big.Int).SetUint64(fee), big.NewInt(FeeMinDen))
	hi := new(big.Int).Mul(new(big.Int).SetUint64(fee), big.NewInt(FeeMaxDen))
	return lo.Cmp(total) >= 0 && hi.Cmp(new(big.Int).Mul(total, big.NewInt(FeeMaxNum))) <= 0
}

// ---------------------------------------------------------------- MiMC helpers

func feU(v uint64) fr.Element { var e fr.Element; e.SetUint64(v); return e }

// mimcHash hashes field elements exactly as the circuit's MiMC gadget does.
func mimcHash(xs ...fr.Element) fr.Element {
	h := mimc.NewMiMC()
	for _, x := range xs {
		b := x.Bytes()
		h.Write(b[:])
	}
	var out fr.Element
	out.SetBytes(h.Sum(nil))
	return out
}

// TxMessage is what the sender signs: MiMC(from, to, amount, fee, nonce).
func TxMessage(c CTx) fr.Element {
	return mimcHash(feU(uint64(c.From)), feU(uint64(c.To)), feU(c.Amount), feU(c.Fee), feU(c.Nonce))
}

// ---------------------------------------------------------------- keys

// Keys are derived deterministically from a seed, so every node knows the
// genesis accounts' public keys (devnet only).
func KeyFromSeed(seed string) *eddsa.PrivateKey {
	s := sha256.Sum256([]byte(seed))
	s2 := sha256.Sum256(s[:])
	k, err := eddsa.GenerateKey(bytes.NewReader(append(s[:], s2[:]...)))
	if err != nil {
		panic(err)
	}
	return k
}

func SignTx(k *eddsa.PrivateKey, c CTx) []byte {
	m := TxMessage(c)
	mb := m.Bytes()
	sig, err := k.Sign(mb[:], mimc.NewMiMC())
	if err != nil {
		panic(err)
	}
	return sig
}

// ---------------------------------------------------------------- strikes and blocks

// Strike is a leaf strike: one winning blow plus a proof that LeafSize
// transfers are correctly signed and within fee limits (SPEC 4.2, 4.3).
type Strike struct {
	Minter    uint32         `json:"minter"`     // account index of the minter (the "hammer")
	BlowNonce uint64         `json:"blow_nonce"` // nonce of the winning blow
	Txs       [LeafSize]CTx  `json:"txs"`
	FeeTotal  uint64         `json:"fee_total"`
	Proof     []byte         `json:"proof"` // Groth16 proof, 128–164 bytes
	ProveMs   int64          `json:"prove_ms"`
}

// BlowHash = SHA256(prev block ‖ minter ‖ nonce) (SPEC 4.2).
func BlowHash(prev Hash32, minter uint32, nonce uint64) Hash32 {
	var b [44]byte
	copy(b[:32], prev[:])
	binary.BigEndian.PutUint32(b[32:], minter)
	binary.BigEndian.PutUint64(b[36:], nonce)
	return sha256.Sum256(b[:])
}

func (s *Strike) BlowHash(prev Hash32) Hash32 { return BlowHash(prev, s.Minter, s.BlowNonce) }

func (s *Strike) ID() Hash32 {
	var b bytes.Buffer
	binary.Write(&b, binary.BigEndian, s.Minter)
	binary.Write(&b, binary.BigEndian, s.BlowNonce)
	binary.Write(&b, binary.BigEndian, s.Txs)
	binary.Write(&b, binary.BigEndian, s.FeeTotal)
	b.Write(s.Proof)
	return sha256.Sum256(b.Bytes())
}

// MeetsDifficulty: hash interpreted as a 256-bit number is below 2^256 / d.
func MeetsDifficulty(h Hash32, d uint64) bool {
	target := new(big.Int).Lsh(big.NewInt(1), 256)
	target.Div(target, new(big.Int).SetUint64(d))
	return new(big.Int).SetBytes(h[:]).Cmp(target) < 0
}

type Header struct {
	Height      uint64 `json:"height"`
	Prev        Hash32 `json:"prev"`
	Time        int64  `json:"time"` // unix milliseconds
	StrikesRoot Hash32 `json:"strikes_root"`
	StateRoot   Hash32 `json:"state_root"`
	Difficulty  uint64 `json:"difficulty"`
	Miner       uint32 `json:"miner"`
	Nonce       uint64 `json:"nonce"`
}

func (h *Header) Hash() Hash32 {
	var b bytes.Buffer
	binary.Write(&b, binary.BigEndian, h.Height)
	b.Write(h.Prev[:])
	binary.Write(&b, binary.BigEndian, h.Time)
	b.Write(h.StrikesRoot[:])
	b.Write(h.StateRoot[:])
	binary.Write(&b, binary.BigEndian, h.Difficulty)
	binary.Write(&b, binary.BigEndian, h.Miner)
	binary.Write(&b, binary.BigEndian, h.Nonce)
	return sha256.Sum256(b.Bytes())
}

type Block struct {
	Header  Header   `json:"header"`
	Strikes []Strike `json:"strikes"`
}

func (b *Block) Hash() Hash32 { return b.Header.Hash() }

func StrikesRoot(ss []Strike) Hash32 {
	h := sha256.New()
	for i := range ss {
		id := ss[i].ID()
		h.Write(id[:])
	}
	var out Hash32
	copy(out[:], h.Sum(nil))
	return out
}

func fmtJEN(p uint64) string { return fmt.Sprintf("%d.%04d", p/Pico, (p%Pico)/100_000_000) }
