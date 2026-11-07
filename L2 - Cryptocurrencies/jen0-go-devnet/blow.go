package main

// Jen-0.5 blows (SPEC 4.2): signed Argon2id with fixed memory.
//
//	sig  = EdDSA(minter key, M),  M = MiMC-field encoding of SHA256(prev ‖ nonce)
//	blow = Argon2id(prev ‖ minter pubkey ‖ nonce ‖ sig,
//	                salt "Zen-blow-v1" ‖ prev, memory 64 MB, passes 1, lanes 1)
//	winning blow: blow < 2^256 / BlowDifficulty
//
// The signature binds the work to the key that is paid: only the key holder
// can make attempts for it, so minting cannot be farmed out to a pool. The
// memory, refilled on every attempt, keeps special chips from a large edge
// over phones and computers. Checking a blow costs one signature check and
// one Argon2id run; results are cached, so each node pays it once per blow.

import (
	"crypto/sha256"
	"encoding/binary"
	"sync"

	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr/mimc"
	"github.com/consensys/gnark-crypto/ecc/bn254/twistededwards/eddsa"
	"golang.org/x/crypto/argon2"
)

// Devnet-wide consensus values (flags exist so tests can scale them).
var (
	BlowMemKiB uint32 = 64 * 1024 // 64 MB (SPEC 4.2, decided 2026-10-10)
	BlowPasses uint32 = 1
)

// accountPubs: public keys of all genesis accounts. Accounts and keys never
// change in Jen-0.5, so blows can be checked without a state.
var accountPubs []*PubKey

// BlowMessage is what the minter signs for one attempt.
func BlowMessage(prev Hash32, nonce uint64) []byte {
	var b [40]byte
	copy(b[:32], prev[:])
	binary.BigEndian.PutUint64(b[32:], nonce)
	h := sha256.Sum256(b[:])
	var e fr.Element
	e.SetBytes(h[:]) // reduced into the field, as MiMC requires
	out := e.Bytes()
	return out[:]
}

// SignBlow signs one attempt (deterministic EdDSA: same input, same signature).
func SignBlow(k *eddsa.PrivateKey, prev Hash32, nonce uint64) []byte {
	sig, err := k.Sign(BlowMessage(prev, nonce), mimc.NewMiMC())
	if err != nil {
		panic(err)
	}
	return sig
}

var invalidBlow = func() Hash32 {
	var h Hash32
	for i := range h {
		h[i] = 0xff
	}
	return h
}()

// argonSlots bounds how many 64 MB Argon2id runs one process does at once.
var argonSlots = make(chan struct{}, 2)

// rawBlow runs the Argon2id step (no signature check, no cache): used by the
// minter for its own attempts, whose signature it just made.
func rawBlow(prev Hash32, pub *PubKey, nonce uint64, sig []byte) Hash32 {
	pb := pub.Bytes()
	in := make([]byte, 0, 32+len(pb)+8+len(sig))
	in = append(in, prev[:]...)
	in = append(in, pb...)
	var nb [8]byte
	binary.BigEndian.PutUint64(nb[:], nonce)
	in = append(in, nb[:]...)
	in = append(in, sig...)
	salt := append([]byte("Zen-blow-v1"), prev[:]...)
	argonSlots <- struct{}{}
	out := argon2.IDKey(in, salt, BlowPasses, BlowMemKiB, 1, 32)
	<-argonSlots
	var h Hash32
	copy(h[:], out)
	return h
}

var blowCache sync.Map // key -> Hash32

func blowKey(prev Hash32, minter uint32, nonce uint64, sig []byte) Hash32 {
	b := make([]byte, 0, 32+4+8+len(sig))
	b = append(b, prev[:]...)
	var x [12]byte
	binary.BigEndian.PutUint32(x[:4], minter)
	binary.BigEndian.PutUint64(x[4:], nonce)
	b = append(b, x[:]...)
	b = append(b, sig...)
	return sha256.Sum256(b)
}

// BlowOutput checks the signature and returns the blow value, or an
// all-ones value (never winning) if the signature or minter is invalid.
func BlowOutput(prev Hash32, minter uint32, nonce uint64, sig []byte) Hash32 {
	k := blowKey(prev, minter, nonce, sig)
	if v, ok := blowCache.Load(k); ok {
		return v.(Hash32)
	}
	out := invalidBlow
	if int(minter) < len(accountPubs) && len(sig) == 64 {
		if ok, _ := accountPubs[minter].Verify(sig, BlowMessage(prev, nonce), mimc.NewMiMC()); ok {
			out = rawBlow(prev, accountPubs[minter], nonce, sig)
		}
	}
	blowCache.Store(k, out)
	return out
}

// rememberBlow stores a minter's own result so it is not recomputed.
func rememberBlow(prev Hash32, minter uint32, nonce uint64, sig []byte, out Hash32) {
	blowCache.Store(blowKey(prev, minter, nonce, sig), out)
}

// Ticket is a winning blow carried in a block without transfers: it keeps the
// minting gate open in quiet periods and earns a share of the minters' part of
// the new coins (SPEC 4.8).
type Ticket struct {
	Minter    uint32 `json:"minter"`
	BlowNonce uint64 `json:"blow_nonce"`
	Sig       []byte `json:"sig"`
}

func (t *Ticket) BlowHash(prev Hash32) Hash32 { return BlowOutput(prev, t.Minter, t.BlowNonce, t.Sig) }

func (t *Ticket) ID() Hash32 { return blowKey(Hash32{}, t.Minter, t.BlowNonce, t.Sig) }

func TicketsRoot(ts []Ticket) Hash32 {
	h := sha256.New()
	for i := range ts {
		id := ts[i].ID()
		h.Write(id[:])
	}
	var out Hash32
	copy(out[:], h.Sum(nil))
	return out
}
