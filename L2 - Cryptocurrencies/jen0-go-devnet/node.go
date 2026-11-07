package main

// A Jen-0 node: networking (HTTP gossip), transaction pool, and the three
// roles every devnet node runs: wallet (traffic), minter, miner.

import (
	"bytes"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"log"
	"math/rand"
	"net/http"
	"sort"
	"sync"
	"sync/atomic"
	"time"

	"github.com/consensys/gnark-crypto/ecc/bn254/fr/mimc"
	"github.com/consensys/gnark-crypto/ecc/bn254/twistededwards/eddsa"
)

type Config struct {
	ID        int
	N         int // total nodes in genesis
	Port      int
	Peers     []string
	KeysDir   string
	BlowRate  int  // blow hashes per second (minter power)
	SealRate  int  // seal hashes per second (miner power)
	Mine      bool // run the miner role
	Mint      bool // run the minter role
	Evil      bool // attacker mode: forged and stolen strikes, tampered blocks
	TxEveryMs int  // wallet traffic interval
}

type Node struct {
	cfg    Config
	chain  *Chain
	prover *Prover
	log    *log.Logger
	me     uint32 // payout account index

	mu         sync.Mutex
	mempool    map[Hash32]*Tx     // tx id -> signed tx
	strikes    map[Hash32][]Strike // prev hash -> strikes seen for that round
	seen       map[Hash32]bool     // gossip dedupe
	myUsers    map[uint32]*eddsa.PrivateKey
	lastBlock  *Block

	// measurements
	BlowHashes, BlowsWon, BlowsWasted, StrikesMade, ProveMsTotal int64
	SealHashes, BlocksSealed                                    int64
	TxSent                                                      int64
	StrikeRejects                                               map[string]int
}

func NewNode(cfg Config) (*Node, error) {
	p, err := LoadProver(cfg.KeysDir)
	if err != nil {
		return nil, err
	}
	n := &Node{
		cfg: cfg, prover: p, chain: NewChain(p, cfg.N), me: NodeAccount(cfg.ID),
		log:     log.New(io.Discard, "", 0),
		mempool: map[Hash32]*Tx{}, strikes: map[Hash32][]Strike{}, seen: map[Hash32]bool{},
		myUsers: map[uint32]*eddsa.PrivateKey{}, StrikeRejects: map[string]int{},
	}
	n.log = log.New(logWriter{}, fmt.Sprintf("[node %d] ", cfg.ID), log.Ltime)
	for i := 0; i < GenesisUsers; i++ {
		if i%cfg.N == cfg.ID {
			n.myUsers[uint32(i)] = KeyFromSeed(UserKeySeed(i))
		}
	}
	n.chain.onTip = n.onNewTip
	return n, nil
}

type logWriter struct{}

func (logWriter) Write(b []byte) (int, error) { return fmt.Print(string(b)) }

// ---------------------------------------------------------------- gossip

func (n *Node) broadcast(path string, v any) {
	body, _ := json.Marshal(v)
	for _, p := range n.cfg.Peers {
		go func(p string) {
			c := http.Client{Timeout: 5 * time.Second}
			resp, err := c.Post("http://"+p+path, "application/json", bytes.NewReader(body))
			if err == nil {
				resp.Body.Close()
			}
		}(p)
	}
}

func (n *Node) markSeen(id Hash32) bool {
	n.mu.Lock()
	defer n.mu.Unlock()
	if n.seen[id] {
		return false
	}
	n.seen[id] = true
	return true
}

type StrikeMsg struct {
	Prev   Hash32 `json:"prev"`
	Strike Strike `json:"strike"`
}

func (n *Node) Serve() error {
	mux := http.NewServeMux()
	mux.HandleFunc("/tx", func(w http.ResponseWriter, r *http.Request) {
		var t Tx
		if json.NewDecoder(r.Body).Decode(&t) == nil {
			n.receiveTx(&t)
		}
	})
	mux.HandleFunc("/strike", func(w http.ResponseWriter, r *http.Request) {
		var m StrikeMsg
		if json.NewDecoder(r.Body).Decode(&m) == nil {
			n.receiveStrike(&m)
		}
	})
	mux.HandleFunc("/block", func(w http.ResponseWriter, r *http.Request) {
		if r.Method == http.MethodGet {
			var h Hash32
			h.UnmarshalText([]byte(r.URL.Query().Get("hash")))
			if b := n.chain.Get(h); b != nil {
				json.NewEncoder(w).Encode(b)
				return
			}
			http.NotFound(w, r)
			return
		}
		var b Block
		if json.NewDecoder(r.Body).Decode(&b) == nil {
			n.receiveBlock(&b)
		}
	})
	mux.HandleFunc("/status", func(w http.ResponseWriter, r *http.Request) {
		json.NewEncoder(w).Encode(n.Status())
	})
	mux.HandleFunc("/chain", func(w http.ResponseWriter, r *http.Request) {
		json.NewEncoder(w).Encode(n.chain.MainChain())
	})
	return http.ListenAndServe(fmt.Sprintf("127.0.0.1:%d", n.cfg.Port), mux)
}

// ---------------------------------------------------------------- receiving

func (n *Node) receiveTx(t *Tx) {
	id := t.Compact().ID()
	if !n.markSeen(id) {
		return
	}
	_, _, st := n.chain.Tip()
	if int(t.From) >= len(st.Accounts) || int(t.To) >= len(st.Accounts) || !FeeOK(t.Amount, t.Fee) {
		return
	}
	m := TxMessage(t.Compact())
	mb := m.Bytes()
	if ok, _ := st.Accounts[t.From].Pub.Verify(t.Sig, mb[:], mimc.NewMiMC()); !ok {
		return
	}
	n.mu.Lock()
	n.mempool[id] = t
	n.mu.Unlock()
	n.broadcast("/tx", t)
}

func (n *Node) receiveStrike(m *StrikeMsg) {
	id := m.Strike.ID()
	if !n.markSeen(id) {
		return
	}
	tip, _, st := n.chain.Tip()
	if m.Prev != tip {
		n.countReject("stale (for another tip)")
		return
	}
	if !MeetsDifficulty(m.Strike.BlowHash(m.Prev), BlowDifficulty) {
		n.countReject("blow does not meet difficulty (stolen or fake)")
		return
	}
	if err := n.chain.VerifyStrikeProof(&m.Strike, st); err != nil {
		n.countReject("invalid proof")
		return
	}
	n.mu.Lock()
	n.strikes[m.Prev] = append(n.strikes[m.Prev], m.Strike)
	n.mu.Unlock()
	n.broadcast("/strike", m)
}

func (n *Node) countReject(reason string) {
	n.mu.Lock()
	n.StrikeRejects[reason]++
	n.mu.Unlock()
}

func (n *Node) receiveBlock(b *Block) {
	h := b.Hash()
	if !n.markSeen(h) {
		return
	}
	err := n.chain.AddBlock(b)
	if errors.Is(err, ErrMissingParent) {
		if n.fetchAncestors(b.Header.Prev, 0) {
			err = n.chain.AddBlock(b)
		}
	}
	if err == nil {
		n.mu.Lock()
		n.lastBlock = b
		n.mu.Unlock()
		n.broadcast("/block", b)
	}
}

// fetchAncestors pulls unknown parents from peers (simple sync).
func (n *Node) fetchAncestors(h Hash32, depth int) bool {
	if n.chain.Has(h) {
		return true
	}
	if depth > 500 {
		return false
	}
	for _, p := range n.cfg.Peers {
		c := http.Client{Timeout: 5 * time.Second}
		resp, err := c.Get("http://" + p + "/block?hash=" + h.String())
		if err != nil {
			continue
		}
		var b Block
		err = json.NewDecoder(resp.Body).Decode(&b)
		resp.Body.Close()
		if err != nil || b.Hash() != h {
			continue
		}
		if !n.fetchAncestors(b.Header.Prev, depth+1) {
			return false
		}
		return n.chain.AddBlock(&b) == nil
	}
	return false
}

func (n *Node) onNewTip() {
	_, _, st := n.chain.Tip()
	n.mu.Lock()
	defer n.mu.Unlock()
	for id, t := range n.mempool {
		if t.Nonce < st.Accounts[t.From].Nonce {
			delete(n.mempool, id)
		}
	}
}

// ---------------------------------------------------------------- wallet

// wallet sends random transfers from this node's users. Each user waits until
// its previous transfer is in a block before sending the next (simple nonces).
func (n *Node) wallet(rng *rand.Rand) {
	for {
		time.Sleep(time.Duration(n.cfg.TxEveryMs) * time.Millisecond)
		_, _, st := n.chain.Tip()
		n.mu.Lock()
		busy := map[uint32]bool{}
		for _, t := range n.mempool {
			busy[t.From] = true
		}
		n.mu.Unlock()
		var ids []uint32
		for id := range n.myUsers {
			if !busy[id] {
				ids = append(ids, id)
			}
		}
		if len(ids) == 0 {
			continue
		}
		sort.Slice(ids, func(i, j int) bool { return ids[i] < ids[j] })
		from := ids[rng.Intn(len(ids))]
		to := uint32(rng.Intn(GenesisUsers))
		if to == from {
			continue
		}
		bal := st.Accounts[from].Balance
		amount := bal / 100 * uint64(1+rng.Intn(4)) // 1–4% of balance
		rateBps := uint64(5 + rng.Intn(296))          // 0.05% – 3%
		fee := amount * rateBps / (10000 - rateBps)
		if amount == 0 || !FeeOK(amount, fee) {
			continue
		}
		c := CTx{From: from, To: to, Amount: amount, Fee: fee, Nonce: st.Accounts[from].Nonce}
		t := &Tx{From: c.From, To: c.To, Amount: c.Amount, Fee: c.Fee, Nonce: c.Nonce, Sig: SignTx(n.myUsers[from], c)}
		atomic.AddInt64(&n.TxSent, 1)
		n.receiveTx(t)
	}
}

// ---------------------------------------------------------------- minter

// minter hashes blows; each winning blow becomes a strike: pick LeafSize
// waiting transfers not yet claimed in this round, prove them, broadcast.
func (n *Node) minter(rng *rand.Rand) {
	nonce := rng.Uint64()
	const slice = 50 * time.Millisecond
	perSlice := n.cfg.BlowRate / 20
	for {
		start := time.Now()
		tip, _, st := n.chain.Tip()
		for i := 0; i < perSlice; i++ {
			nonce++
			atomic.AddInt64(&n.BlowHashes, 1)
			if MeetsDifficulty(BlowHash(tip, n.me, nonce), BlowDifficulty) {
				atomic.AddInt64(&n.BlowsWon, 1)
				n.strike(tip, st, nonce, rng)
				break
			}
		}
		if d := slice - time.Since(start); d > 0 {
			time.Sleep(d)
		}
	}
}

func (n *Node) strike(tip Hash32, st *State, blowNonce uint64, rng *rand.Rand) {
	n.mu.Lock()
	claimed := map[Hash32]bool{}
	for _, s := range n.strikes[tip] {
		for _, t := range s.Txs {
			claimed[t.ID()] = true
		}
	}
	var cand []*Tx
	for id, t := range n.mempool {
		if !claimed[id] && t.Nonce == st.Accounts[t.From].Nonce {
			cand = append(cand, t)
		}
	}
	n.mu.Unlock()
	sort.Slice(cand, func(i, j int) bool { a, b := cand[i].Compact().ID(), cand[j].Compact().ID(); return string(a[:]) < string(b[:]) })
	rng.Shuffle(len(cand), func(i, j int) { cand[i], cand[j] = cand[j], cand[i] })
	var pick [LeafSize]Tx
	used := map[uint32]bool{}
	k := 0
	for _, t := range cand {
		if k == LeafSize {
			break
		}
		if !used[t.From] {
			used[t.From] = true
			pick[k] = *t
			k++
		}
	}
	if k < LeafSize {
		atomic.AddInt64(&n.BlowsWasted, 1) // not enough waiting transfers
		return
	}
	var pubs [LeafSize]*PubKey
	for i := range pick {
		pubs[i] = st.Accounts[pick[i].From].Pub
	}
	t0 := time.Now()
	proof, fee, err := n.prover.Prove(pick, pubs, n.me)
	if err != nil {
		n.log.Printf("prove failed: %v", err)
		return
	}
	ms := time.Since(t0).Milliseconds()
	atomic.AddInt64(&n.ProveMsTotal, ms)
	s := Strike{Minter: n.me, BlowNonce: blowNonce, FeeTotal: fee, Proof: proof, ProveMs: ms}
	for i := range pick {
		s.Txs[i] = pick[i].Compact()
	}
	if cur, _, _ := n.chain.Tip(); cur != tip {
		atomic.AddInt64(&n.BlowsWasted, 1) // a block arrived while proving
		return
	}
	atomic.AddInt64(&n.StrikesMade, 1)
	n.receiveStrike(&StrikeMsg{Prev: tip, Strike: s})
}

// ---------------------------------------------------------------- miner

// buildCandidate takes all strikes seen for the tip in blow-hash order and
// keeps those that still apply (a transfer claimed twice is dropped).
func (n *Node) buildCandidate(tip Hash32, st *State, height uint64, diff uint64, prevTime int64) *Block {
	n.mu.Lock()
	ss := append([]Strike(nil), n.strikes[tip]...)
	n.mu.Unlock()
	SortStrikes(tip, ss)
	var keep []Strike
	trial := &Block{Header: Header{Height: height, Prev: tip, Miner: n.me}}
	for _, s := range ss {
		trial.Strikes = append(keep, s)
		if _, _, err := st.ApplyBlock(trial); err == nil {
			keep = append(keep, s)
		}
	}
	b := &Block{Header: Header{Height: height, Prev: tip, Difficulty: diff, Miner: n.me}, Strikes: keep}
	b.Header.Time = time.Now().UnixMilli()
	if b.Header.Time <= prevTime {
		b.Header.Time = prevTime + 1
	}
	ns, _, err := st.ApplyBlock(b)
	if err != nil {
		return nil
	}
	b.Header.StrikesRoot = StrikesRoot(keep)
	b.Header.StateRoot = ns.Root()
	return b
}

func (n *Node) miner(rng *rand.Rand) {
	const slice = 50 * time.Millisecond
	perSlice := n.cfg.SealRate / 20
	for {
		tip, tb, st := n.chain.Tip()
		n.mu.Lock()
		nStrikes := len(n.strikes[tip])
		n.mu.Unlock()
		age := time.Now().UnixMilli() - tb.Header.Time
		if tb.Header.Height == 0 {
			age = 1 << 40
		}
		// policy: seal once the round has density (>= 6 strikes) or is older than 2/3 block time
		if nStrikes < 6 && age < TargetBlockSeconds*1000*2/3 {
			time.Sleep(200 * time.Millisecond)
			continue
		}
		diff := n.chain.NextDifficulty(tip)
		b := n.buildCandidate(tip, st, tb.Header.Height+1, diff, tb.Header.Time)
		if b == nil {
			time.Sleep(200 * time.Millisecond)
			continue
		}
		b.Header.Nonce = rng.Uint64()
		deadline := time.Now().Add(1 * time.Second) // rebuild every second to include new strikes
		for time.Now().Before(deadline) {
			start := time.Now()
			if cur, _, _ := n.chain.Tip(); cur != tip {
				break
			}
			found := false
			for i := 0; i < perSlice; i++ {
				b.Header.Nonce++
				atomic.AddInt64(&n.SealHashes, 1)
				if MeetsDifficulty(b.Header.Hash(), diff) {
					found = true
					break
				}
			}
			if found {
				atomic.AddInt64(&n.BlocksSealed, 1)
				n.receiveBlock(b)
				break
			}
			if d := slice - time.Since(start); d > 0 {
				time.Sleep(d)
			}
		}
	}
}

// ---------------------------------------------------------------- attacker

// evil sends three kinds of attacks; honest nodes must reject all of them.
func (n *Node) evil(rng *rand.Rand) {
	for {
		time.Sleep(3 * time.Second)
		tip, _, _ := n.chain.Tip()
		n.mu.Lock()
		var victim *Strike
		if ss := n.strikes[tip]; len(ss) > 0 {
			v := ss[rng.Intn(len(ss))]
			victim = &v
		}
		last := n.lastBlock
		n.mu.Unlock()
		if victim != nil {
			// 1. stolen strike: claim someone else's proven work as ours
			s := *victim
			s.Minter = n.me
			n.broadcast("/strike", &StrikeMsg{Prev: tip, Strike: s})
			// 2. forged proof: a real winning blow of ours, but a fake proof
			f := *victim
			f.Minter = n.me
			for nonce := rng.Uint64(); ; nonce++ {
				if MeetsDifficulty(BlowHash(tip, n.me, nonce), BlowDifficulty) {
					f.BlowNonce = nonce
					break
				}
			}
			f.Proof = append([]byte(nil), f.Proof...)
			f.Proof[len(f.Proof)/2] ^= 0xff
			n.broadcast("/strike", &StrikeMsg{Prev: tip, Strike: f})
		}
		if last != nil && len(last.Strikes) > 0 {
			// 3. tampered block: change one amount after the block was sealed
			bb := *last
			bb.Strikes = append([]Strike(nil), last.Strikes...)
			bb.Strikes[0].Txs[0].Amount += Pico
			n.broadcast("/block", &bb)
		}
	}
}

// ---------------------------------------------------------------- status

func (n *Node) Status() map[string]any {
	tip, tb, st := n.chain.Tip()
	n.chain.mu.Lock()
	rej := map[string]int{}
	for k, v := range n.chain.Rejected {
		rej["block: "+k] = v
	}
	n.chain.mu.Unlock()
	n.mu.Lock()
	for k, v := range n.StrikeRejects {
		rej["strike: "+k] = v
	}
	pool := len(n.mempool)
	n.mu.Unlock()
	return map[string]any{
		"id": n.cfg.ID, "evil": n.cfg.Evil, "account": n.me,
		"height": tb.Header.Height, "tip": tip.String(), "state_root": st.Root().String(),
		"supply": st.Supply(), "genesis": st.Genesis, "issued": st.Issued,
		"balance": st.Accounts[n.me].Balance,
		"blow_rate": n.cfg.BlowRate, "seal_rate": n.cfg.SealRate,
		"blow_hashes": atomic.LoadInt64(&n.BlowHashes), "blows_won": atomic.LoadInt64(&n.BlowsWon),
		"blows_wasted": atomic.LoadInt64(&n.BlowsWasted), "strikes_made": atomic.LoadInt64(&n.StrikesMade),
		"prove_ms_total": atomic.LoadInt64(&n.ProveMsTotal),
		"seal_hashes": atomic.LoadInt64(&n.SealHashes), "blocks_sealed": atomic.LoadInt64(&n.BlocksSealed),
		"tx_sent": atomic.LoadInt64(&n.TxSent), "mempool": pool, "rejected": rej,
	}
}

func (n *Node) Run() error {
	rng := rand.New(rand.NewSource(int64(n.cfg.ID)*7919 + time.Now().UnixNano()))
	if n.cfg.Evil {
		go n.evil(rand.New(rand.NewSource(rng.Int63())))
	} else {
		go n.wallet(rand.New(rand.NewSource(rng.Int63())))
		if n.cfg.Mint {
			go n.minter(rand.New(rand.NewSource(rng.Int63())))
		}
		if n.cfg.Mine {
			go n.miner(rand.New(rand.NewSource(rng.Int63())))
		}
	}
	n.log.Printf("listening on %d, peers %v", n.cfg.Port, n.cfg.Peers)
	return n.Serve()
}
