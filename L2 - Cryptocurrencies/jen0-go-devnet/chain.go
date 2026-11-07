package main

// Block tree, validation and fork choice (SPEC 5.1–5.3).

import (
	"errors"
	"fmt"
	"math"
	"math/big"
	"sync"
	"time"
)

var ErrMissingParent = errors.New("missing parent")

// BlockStats are per-block measurements. Purity and typical fee are LOGGED
// ONLY in Jen-0 (automatic resizing comes in Jen-1).
type BlockStats struct {
	Height           uint64  `json:"height"`
	Strikes          int     `json:"strikes"`
	Txs              int     `json:"txs"`
	Fees             uint64  `json:"fees"`
	SumLnRate        float64 `json:"-"`
	PaidReward       uint64  `json:"paid_reward"`
	PaidRewardHeight uint64  `json:"paid_reward_height"`
	PaidZ            int64   `json:"-"`
	BlockMs          int64   `json:"block_ms"`
	Miner            uint32  `json:"miner"`
	Hash             string  `json:"hash"`
}

func (st *BlockStats) addTx(t CTx) {
	st.Txs++
	st.SumLnRate += math.Log(float64(t.Fee) / float64(t.Amount+t.Fee))
}

type Chain struct {
	mu       sync.Mutex
	prover   *Prover
	blocks   map[Hash32]*Block
	states   map[Hash32]*State
	work     map[Hash32]*big.Int
	stats    map[Hash32]*BlockStats
	verified map[Hash32]bool // strike IDs whose proofs were already checked
	genesis  Hash32
	tip      Hash32
	onTip    func()

	Rejected map[string]int // reason -> count (for the report)
}

func NewChain(p *Prover, nodes int) *Chain {
	g := GenesisBlock()
	gh := g.Hash()
	c := &Chain{
		prover: p, blocks: map[Hash32]*Block{gh: g}, states: map[Hash32]*State{gh: GenesisState(nodes)},
		work: map[Hash32]*big.Int{gh: big.NewInt(0)}, stats: map[Hash32]*BlockStats{gh: {}},
		verified: map[Hash32]bool{}, genesis: gh, tip: gh, Rejected: map[string]int{},
	}
	return c
}

func (c *Chain) Tip() (Hash32, *Block, *State) {
	c.mu.Lock()
	defer c.mu.Unlock()
	return c.tip, c.blocks[c.tip], c.states[c.tip]
}

func (c *Chain) Has(h Hash32) bool {
	c.mu.Lock()
	defer c.mu.Unlock()
	_, ok := c.blocks[h]
	return ok
}

func (c *Chain) Get(h Hash32) *Block {
	c.mu.Lock()
	defer c.mu.Unlock()
	return c.blocks[h]
}

// NextDifficulty: retarget every block toward TargetBlockSeconds, smoothed and
// clamped so one odd block time cannot swing difficulty much.
func (c *Chain) nextDifficultyLocked(parent *Block) uint64 {
	if parent.Header.Height == 0 {
		return GenesisSealDifficulty
	}
	gp := c.blocks[parent.Header.Prev]
	T := int64(TargetBlockSeconds * 1000)
	dt := parent.Header.Time - gp.Header.Time
	if gp.Header.Height == 0 {
		dt = T
	}
	if dt < T/4 {
		dt = T / 4
	}
	if dt > 4*T {
		dt = 4 * T
	}
	d := new(big.Int).SetUint64(parent.Header.Difficulty)
	d.Mul(d, big.NewInt(4*T))
	d.Div(d, big.NewInt(3*T+dt))
	if d.Sign() == 0 {
		return 1
	}
	return d.Uint64()
}

func (c *Chain) NextDifficulty(parent Hash32) uint64 {
	c.mu.Lock()
	defer c.mu.Unlock()
	return c.nextDifficultyLocked(c.blocks[parent])
}

func (c *Chain) reject(reason string) error {
	c.Rejected[reason]++
	return errors.New(reason)
}

// VerifyStrikeProof checks one strike against a state (used for gossip too).
func (c *Chain) VerifyStrikeProof(s *Strike, st *State) error {
	id := s.ID()
	c.mu.Lock()
	ok := c.verified[id]
	c.mu.Unlock()
	if ok {
		return nil
	}
	pubs, err := st.pubs(s.Txs)
	if err != nil {
		return err
	}
	if err := c.prover.Verify(s, pubs); err != nil {
		return err
	}
	c.mu.Lock()
	c.verified[id] = true
	c.mu.Unlock()
	return nil
}

// AddBlock validates a block completely and updates the best tip.
func (c *Chain) AddBlock(b *Block) error {
	h := b.Hash()
	c.mu.Lock()
	if _, ok := c.blocks[h]; ok {
		c.mu.Unlock()
		return nil
	}
	parent, ok := c.blocks[b.Header.Prev]
	if !ok {
		c.mu.Unlock()
		return ErrMissingParent
	}
	pstate := c.states[b.Header.Prev]
	wantDiff := c.nextDifficultyLocked(parent)
	c.mu.Unlock()

	if b.Header.Height != parent.Header.Height+1 {
		return c.reject("bad height")
	}
	if b.Header.Time <= parent.Header.Time || b.Header.Time > time.Now().UnixMilli()+15_000 {
		return c.reject("bad timestamp")
	}
	if b.Header.Difficulty != wantDiff {
		return c.reject("bad difficulty")
	}
	if !MeetsDifficulty(h, b.Header.Difficulty) {
		return c.reject("seal does not meet difficulty")
	}
	if StrikesRoot(b.Strikes) != b.Header.StrikesRoot {
		return c.reject("strikes root mismatch (block altered after sealing)")
	}
	for i := range b.Strikes {
		if err := c.VerifyStrikeProof(&b.Strikes[i], pstate); err != nil {
			return c.reject("invalid strike proof in block")
		}
	}
	ns, st, err := pstate.ApplyBlock(b, h)
	if err != nil {
		return c.reject("block rules: " + err.Error())
	}
	if ns.Root() != b.Header.StateRoot {
		return c.reject("state root mismatch")
	}
	st.BlockMs = b.Header.Time - parent.Header.Time
	st.Miner = b.Header.Miner
	st.Hash = h.Short()

	c.mu.Lock()
	defer c.mu.Unlock()
	c.blocks[h] = b
	c.states[h] = ns
	c.stats[h] = st
	w := new(big.Int).Add(c.work[b.Header.Prev], new(big.Int).SetUint64(b.Header.Difficulty))
	c.work[h] = w
	// fork choice: most work; equal work -> lower seal hash wins (SPEC 5.2)
	cmp := w.Cmp(c.work[c.tip])
	if cmp > 0 || (cmp == 0 && string(h[:]) < string(c.tip[:])) {
		c.tip = h
		if c.onTip != nil {
			go c.onTip()
		}
	}
	return nil
}

// MainChain returns stats of the best chain from genesis to tip.
func (c *Chain) MainChain() []*BlockStats {
	c.mu.Lock()
	defer c.mu.Unlock()
	var out []*BlockStats
	for h := c.tip; h != c.genesis; h = c.blocks[h].Header.Prev {
		out = append([]*BlockStats{c.stats[h]}, out...)
	}
	return out
}

func (c *Chain) Describe() string {
	h, b, s := c.Tip()
	return fmt.Sprintf("height %d tip %s supply %s", b.Header.Height, h.Short(), fmtJEN(s.Supply()))
}
