package main

// Claim then prove (Jen-1 design, tried in Jen-0 behind --claims).
//
// Problem: proving a strike takes seconds, gossip takes milliseconds. Without
// claims, a minter tells nobody which transfers it picked until its proof is
// done, so two minters can prove the same transfer and one proof is thrown away.
//
// With claims, a minter that wins a blow first gossips a small Claim (its blow
// and the IDs of the transfers it picked), waits ClaimWaitMs for clashes, and
// only then proves:
//
//   - Clash rule: if two live claims of the same round share a transfer, the
//     claim with the LOWER blow hash keeps it (the same order miners use to
//     sort strikes, SortStrikes). The loser keeps its blow — a blow commits to
//     (prev, minter, nonce), not to transfers — and re-picks, gossiping the new
//     pick with a higher Seq. After ClaimMaxRepicks it gives up.
//   - Expiry: a claim lapses ClaimExpireMs after it was first seen unless its
//     strike arrives, so nobody can lock transfers by claiming and not proving.
//     A claim also needs a winning blow, so claims cannot be spammed.
//   - Miners: once a round is ready to seal, the miner waits (at most
//     ClaimHoldMs) for the claims it had already seen to arrive as strikes.
//
// Claims are gossip only (like waiting transfers): they never enter blocks and
// change no consensus rule. A node that ignores them is back to the old way.

import (
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"sort"
	"sync/atomic"
	"time"
)

// Devnet values (miner/minter policy, not consensus).
var (
	ClaimWaitMs     = 400   // wait for clashing claims before proving
	ClaimExpireMs   = 10000 // a claim not followed by its strike lapses
	ClaimHoldMs     = 4000  // longest a miner waits for already-seen claims
	ClaimMaxRepicks = 3     // re-picks after losing clashes before giving up
)

type Claim struct {
	Prev      Hash32           `json:"prev"`
	Minter    uint32           `json:"minter"`
	BlowNonce uint64           `json:"blow_nonce"`
	Seq       uint32           `json:"seq"` // re-pick number; a higher Seq replaces a lower one
	Txs       [LeafSize]Hash32 `json:"txs"` // IDs of the claimed transfers (CTx.ID)
}

func (c *Claim) BlowHash() Hash32 { return BlowHash(c.Prev, c.Minter, c.BlowNonce) }

func (c *Claim) ID() Hash32 {
	var b bytes.Buffer
	binary.Write(&b, binary.BigEndian, c)
	return sha256.Sum256(b.Bytes())
}

// claimEntry is a node's record of one blow's latest claim.
type claimEntry struct {
	Claim
	seen   time.Time // when this node first saw this blow's claim
	proven bool      // its strike has arrived
}

func (e *claimEntry) live(now time.Time) bool {
	return !e.proven && now.Sub(e.seen) < time.Duration(ClaimExpireMs)*time.Millisecond
}

func less(a, b Hash32) bool { return bytes.Compare(a[:], b[:]) < 0 }

// receiveClaim validates, stores and relays a claim. Only claims for the
// current tip with a valid winning blow are kept.
func (n *Node) receiveClaim(c *Claim) {
	if !n.markSeen(c.ID()) {
		return
	}
	tip, _, _ := n.chain.Tip()
	if c.Prev != tip {
		return
	}
	bh := c.BlowHash()
	if !MeetsDifficulty(bh, BlowDifficulty) {
		atomic.AddInt64(&n.ClaimsRejected, 1)
		return
	}
	n.mu.Lock()
	round := n.claims[c.Prev]
	if round == nil {
		round = map[Hash32]*claimEntry{}
		n.claims[c.Prev] = round
	}
	old := round[bh]
	switch {
	case old == nil:
		round[bh] = &claimEntry{Claim: *c, seen: time.Now()}
	case c.Seq > old.Seq:
		old.Claim = *c // re-pick: keep the original "seen" time, so re-picking cannot extend the claim
	default:
		n.mu.Unlock()
		return
	}
	n.mu.Unlock()
	n.broadcast("/claim", c)
}

// takenLocked returns the transfers of this round already in a strike, and,
// for every transfer in a live claim of another blow, the lowest blow hash
// claiming it. Caller holds n.mu.
func (n *Node) takenLocked(prev Hash32, mine Hash32) (inStrike map[Hash32]bool, claimedBy map[Hash32]Hash32) {
	inStrike = map[Hash32]bool{}
	for _, s := range n.strikes[prev] {
		for _, t := range s.Txs {
			inStrike[t.ID()] = true
		}
	}
	claimedBy = map[Hash32]Hash32{}
	now := time.Now()
	for bh, e := range n.claims[prev] {
		if bh == mine || !e.live(now) {
			continue
		}
		for _, id := range e.Txs {
			if cur, ok := claimedBy[id]; !ok || less(bh, cur) {
				claimedBy[id] = bh
			}
		}
	}
	return
}

// markProvenLocked records that a strike for this blow arrived.
func (n *Node) markProvenLocked(prev Hash32, s *Strike) {
	if e := n.claims[prev][s.BlowHash(prev)]; e != nil {
		e.proven = true
	}
}

// pendingClaims counts live claims of this round, first seen before `before`,
// whose strike has not arrived yet (used by the miner's wait).
func (n *Node) pendingClaims(prev Hash32, before time.Time) int {
	n.mu.Lock()
	defer n.mu.Unlock()
	now, k := time.Now(), 0
	for _, e := range n.claims[prev] {
		if e.live(now) && e.seen.Before(before) {
			k++
		}
	}
	return k
}

// pickTxs chooses LeafSize waiting transfers from distinct senders that are
// valid now and not in `skip`. Order: --pick oldest (by arrival) or random.
func (n *Node) pickTxs(st *State, skip func(Hash32) bool, rng interface{ Shuffle(int, func(int, int)) }) ([LeafSize]Tx, bool) {
	n.mu.Lock()
	type c struct {
		t  *Tx
		id Hash32
		at int64
	}
	var cand []c
	for id, t := range n.mempool {
		if !skip(id) && t.Nonce == st.Accounts[t.From].Nonce {
			cand = append(cand, c{t, id, n.arrived[id]})
		}
	}
	n.mu.Unlock()
	sort.Slice(cand, func(i, j int) bool {
		if n.cfg.Pick == "oldest" && cand[i].at != cand[j].at {
			return cand[i].at < cand[j].at
		}
		return less(cand[i].id, cand[j].id)
	})
	if n.cfg.Pick != "oldest" {
		rng.Shuffle(len(cand), func(i, j int) { cand[i], cand[j] = cand[j], cand[i] })
	}
	var pick [LeafSize]Tx
	used := map[uint32]bool{}
	k := 0
	for _, x := range cand {
		if k == LeafSize {
			break
		}
		if !used[x.t.From] {
			used[x.t.From] = true
			pick[k] = *x.t
			k++
		}
	}
	return pick, k == LeafSize
}

// claimTxs runs the claim phase for a won blow: pick, gossip, wait, and
// re-pick after a lost clash. Returns the transfers to prove, or ok=false
// (counted) when the blow cannot be used.
func (n *Node) claimTxs(tip Hash32, st *State, blowNonce uint64, rng interface{ Shuffle(int, func(int, int)) }) (pick [LeafSize]Tx, ok bool) {
	mine := BlowHash(tip, n.me, blowNonce)
	for seq := 0; seq <= ClaimMaxRepicks; seq++ {
		n.mu.Lock()
		inStrike, claimedBy := n.takenLocked(tip, mine)
		n.mu.Unlock()
		pick, ok = n.pickTxs(st, func(id Hash32) bool {
			_, c := claimedBy[id]
			return inStrike[id] || c
		}, rng)
		if !ok {
			atomic.AddInt64(&n.BlowsNoTx, 1)
			return pick, false
		}
		c := &Claim{Prev: tip, Minter: n.me, BlowNonce: blowNonce, Seq: uint32(seq)}
		for i := range pick {
			c.Txs[i] = pick[i].Compact().ID()
		}
		atomic.AddInt64(&n.ClaimsMade, 1)
		n.receiveClaim(c)
		time.Sleep(time.Duration(ClaimWaitMs) * time.Millisecond)
		if cur, _, _ := n.chain.Tip(); cur != tip {
			atomic.AddInt64(&n.BlowsRoundEnded, 1) // a block arrived before proving started: no proof wasted
			return pick, false
		}
		// clash check: does a claim with a lower blow hash, or a strike, hold any of my transfers?
		n.mu.Lock()
		inStrike, claimedBy = n.takenLocked(tip, mine)
		n.mu.Unlock()
		lost := false
		for _, id := range c.Txs {
			if by, ok := claimedBy[id]; inStrike[id] || (ok && less(by, mine)) {
				lost = true
			}
		}
		if !lost {
			return pick, true
		}
		atomic.AddInt64(&n.ClaimClashesLost, 1)
	}
	atomic.AddInt64(&n.BlowsGaveUp, 1)
	return pick, false
}
