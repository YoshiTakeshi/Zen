package main

// Chain state and block application rules (SPEC 3, 4.6, 5.4).

import (
	"crypto/sha256"
	"encoding/binary"
	"errors"
	"fmt"
	"sort"
)

type Account struct {
	Pub     *PubKey
	Balance uint64
	Nonce   uint64
}

// State is the full account state after a block. Jen-0 keeps it in memory and
// hashes it whole; Jen-1 replaces this with a Merkle tree proven by strikes.
type State struct {
	Accounts []Account
	Issued   uint64 // total block rewards credited so far (for the supply check)
	Genesis  uint64 // total genesis balances

	// Pending reward: the reward of the latest block is paid when the NEXT
	// block arrives, because its random factor comes from that block's seal.
	PendingMiner  uint32
	PendingHeight uint64
	HasPending    bool
}

func (s *State) Clone() *State {
	c := *s
	c.Accounts = make([]Account, len(s.Accounts))
	copy(c.Accounts, s.Accounts)
	return &c
}

func (s *State) Root() Hash32 {
	h := sha256.New()
	var b [8]byte
	for i, a := range s.Accounts {
		binary.BigEndian.PutUint64(b[:], uint64(i))
		h.Write(b[:])
		binary.BigEndian.PutUint64(b[:], a.Balance)
		h.Write(b[:])
		binary.BigEndian.PutUint64(b[:], a.Nonce)
		h.Write(b[:])
	}
	binary.BigEndian.PutUint64(b[:], s.Issued)
	h.Write(b[:])
	var out Hash32
	copy(out[:], h.Sum(nil))
	return out
}

func (s *State) Supply() uint64 {
	t := uint64(0)
	for _, a := range s.Accounts {
		t += a.Balance
	}
	return t
}

// UserKeySeed / NodeKeySeed: deterministic devnet keys.
func UserKeySeed(i int) string { return fmt.Sprintf("jen0-user-%d", i) }
func NodeKeySeed(j int) string { return fmt.Sprintf("jen0-node-%d", j) }

// UserIndex / NodeIndex: account layout. Users first, then one payout account per node.
func NodeAccount(j int) uint32 { return uint32(GenesisUsers + j) }

func GenesisState(nodes int) *State {
	s := &State{}
	for i := 0; i < GenesisUsers; i++ {
		k := KeyFromSeed(UserKeySeed(i))
		s.Accounts = append(s.Accounts, Account{Pub: &k.PublicKey, Balance: GenesisUserBalance})
	}
	for j := 0; j < nodes; j++ {
		k := KeyFromSeed(NodeKeySeed(j))
		s.Accounts = append(s.Accounts, Account{Pub: &k.PublicKey})
	}
	s.Genesis = s.Supply()
	return s
}

func GenesisBlock() *Block {
	return &Block{Header: Header{Height: 0, Time: 0, Difficulty: GenesisSealDifficulty}}
}

func (s *State) pubs(txs [LeafSize]CTx) ([LeafSize]*PubKey, error) {
	var out [LeafSize]*PubKey
	for i, t := range txs {
		if int(t.From) >= len(s.Accounts) || int(t.To) >= len(s.Accounts) {
			return out, errors.New("unknown account")
		}
		out[i] = s.Accounts[t.From].Pub
	}
	return out, nil
}

// applyTx executes one transfer: nonce and balance checks, then the move.
// The fee leaves the sender here and is redistributed by the block's fee pot.
func (s *State) applyTx(t CTx) error {
	if int(t.From) >= len(s.Accounts) || int(t.To) >= len(s.Accounts) {
		return errors.New("unknown account")
	}
	if !FeeOK(t.Amount, t.Fee) {
		return errors.New("fee outside fineness limits")
	}
	a := &s.Accounts[t.From]
	if a.Nonce != t.Nonce {
		return fmt.Errorf("bad nonce: have %d want %d", t.Nonce, a.Nonce)
	}
	if a.Balance < t.Amount+t.Fee {
		return errors.New("insufficient balance")
	}
	a.Balance -= t.Amount + t.Fee
	a.Nonce++
	s.Accounts[t.To].Balance += t.Amount
	return nil
}

// ApplyBlock checks everything except the strike proofs and the seal (done by
// the caller, which caches proof checks), and returns the new state.
//
// Order: (1) pay the PREVIOUS block's reward using this block's seal as the
// randomness, (2) apply the strikes' transfers in blow-hash order, (3) split
// this block's fee pot: 75% to minters (one share per strike), rest to miner.
func (s *State) ApplyBlock(b *Block, sealHash Hash32) (*State, *BlockStats, error) {
	n := s.Clone()
	st := &BlockStats{Height: b.Header.Height, Strikes: len(b.Strikes)}

	if n.HasPending {
		z := RewardZIndex(sealHash)
		r := RewardPico(n.PendingHeight, z)
		n.Accounts[n.PendingMiner].Balance += r
		n.Issued += r
		st.PaidReward, st.PaidRewardHeight, st.PaidZ = r, n.PendingHeight, PhiInvQ32[z]
	}

	// strikes must be in ascending blow-hash order with unique (minter, nonce)
	seen := map[[2]uint64]bool{}
	var prevBH *Hash32
	fees := uint64(0)
	for i := range b.Strikes {
		sk := &b.Strikes[i]
		if int(sk.Minter) >= len(n.Accounts) {
			return nil, nil, errors.New("unknown minter")
		}
		key := [2]uint64{uint64(sk.Minter), sk.BlowNonce}
		if seen[key] {
			return nil, nil, errors.New("duplicate blow")
		}
		seen[key] = true
		bh := sk.BlowHash(b.Header.Prev)
		if !MeetsDifficulty(bh, BlowDifficulty) {
			return nil, nil, errors.New("blow does not meet blow difficulty")
		}
		if prevBH != nil && string(bh[:]) <= string(prevBH[:]) {
			return nil, nil, errors.New("strikes not in blow-hash order")
		}
		prevBH = &bh
		sum := uint64(0)
		for _, t := range sk.Txs {
			if err := n.applyTx(t); err != nil {
				return nil, nil, fmt.Errorf("strike %d: %w", i, err)
			}
			sum += t.Fee
			st.addTx(t)
		}
		if sum != sk.FeeTotal {
			return nil, nil, errors.New("fee total mismatch")
		}
		fees += sum
	}

	minerCut := fees
	if len(b.Strikes) > 0 {
		pot := fees * MinterSharePct / 100
		share := pot / uint64(len(b.Strikes))
		for _, sk := range b.Strikes {
			n.Accounts[sk.Minter].Balance += share
		}
		minerCut = fees - share*uint64(len(b.Strikes))
	}
	if int(b.Header.Miner) >= len(n.Accounts) {
		return nil, nil, errors.New("unknown miner")
	}
	n.Accounts[b.Header.Miner].Balance += minerCut
	st.Fees = fees

	n.PendingMiner, n.PendingHeight, n.HasPending = b.Header.Miner, b.Header.Height, true

	if n.Supply() != n.Genesis+n.Issued {
		return nil, nil, errors.New("supply invariant violated")
	}
	return n, st, nil
}

// SortStrikes orders strikes by blow hash (the canonical block order).
func SortStrikes(prev Hash32, ss []Strike) {
	sort.Slice(ss, func(i, j int) bool {
		a, b := ss[i].BlowHash(prev), ss[j].BlowHash(prev)
		return string(a[:]) < string(b[:])
	})
}
