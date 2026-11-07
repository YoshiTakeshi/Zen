package main

// Commands:
//
//	jen0 setup  --keys DIR                      one-time local proof setup
//	jen0 node   --id I --n N --port P --peers ... run a node
//	jen0 report --ports 7001,7002,...            measure a running devnet
//	jen0 selftest                                quick checks of reward math and proofs

import (
	"encoding/json"
	"flag"
	"fmt"
	"math"
	"net/http"
	"os"
	"sort"
	"strconv"
	"strings"
	"time"

	"github.com/consensys/gnark/logger"
)

func main() {
	logger.Disable()
	if len(os.Args) < 2 {
		fmt.Println("usage: jen0 setup|node|report|selftest")
		os.Exit(1)
	}
	switch os.Args[1] {
	case "setup":
		fs := flag.NewFlagSet("setup", flag.ExitOnError)
		dir := fs.String("keys", "keys", "output directory")
		fs.Parse(os.Args[2:])
		if err := SetupKeys(*dir); err != nil {
			panic(err)
		}
	case "node":
		fs := flag.NewFlagSet("node", flag.ExitOnError)
		var c Config
		var peers string
		fs.IntVar(&c.ID, "id", 0, "node id")
		fs.IntVar(&c.N, "n", 5, "number of nodes in genesis")
		fs.IntVar(&c.Port, "port", 7000, "listen port")
		fs.StringVar(&peers, "peers", "", "comma-separated host:port of peers")
		fs.StringVar(&c.KeysDir, "keys", "keys", "proving keys directory")
		fs.IntVar(&c.BlowRate, "blowrate", 4000, "blow hashes per second")
		fs.IntVar(&c.SealRate, "sealrate", 60000, "seal hashes per second")
		fs.BoolVar(&c.Mine, "mine", true, "run miner")
		fs.BoolVar(&c.Mint, "mint", true, "run minter")
		fs.BoolVar(&c.Evil, "evil", false, "attacker mode")
		fs.IntVar(&c.TxEveryMs, "txms", 400, "wallet: ms between transfers")
		fs.BoolVar(&c.Claims, "claims", false, "minter: claim transfers before proving (claims.go)")
		fs.StringVar(&c.Pick, "pick", "random", "minter: pick transfers \"random\" or \"oldest\" first")
		fs.Uint64Var(&BlowDifficulty, "blowdiff", BlowDifficulty, "devnet rule: blow difficulty")
		fs.IntVar(&GenesisUsers, "users", GenesisUsers, "devnet rule: funded genesis users")
		fs.IntVar(&MinStrikesToSeal, "minstrikes", MinStrikesToSeal, "miner policy: strikes before sealing")
		fs.IntVar(&AttackerNode, "attacker", AttackerNode, "test label: id of the attacker node")
		fs.Parse(os.Args[2:])
		if peers != "" {
			c.Peers = strings.Split(peers, ",")
		}
		n, err := NewNode(c)
		if err != nil {
			panic(err)
		}
		panic(n.Run())
	case "report":
		fs := flag.NewFlagSet("report", flag.ExitOnError)
		ports := fs.String("ports", "7001,7002,7003,7004,7005", "node ports")
		fs.IntVar(&GenesisUsers, "users", GenesisUsers, "devnet rule: funded genesis users")
		fs.Parse(os.Args[2:])
		report(strings.Split(*ports, ","))
	case "selftest":
		selftest()
		if len(os.Args) > 2 {
			proofSelftest(os.Args[2])
		}
	}
}

func getJSON(url string, v any) error {
	c := http.Client{Timeout: 10 * time.Second}
	r, err := c.Get(url)
	if err != nil {
		return err
	}
	defer r.Body.Close()
	return json.NewDecoder(r.Body).Decode(v)
}

func report(ports []string) {
	type status map[string]any
	var sts []status
	var chains [][]*BlockStats
	for _, p := range ports {
		var s status
		var ch []*BlockStats
		if err := getJSON("http://127.0.0.1:"+p+"/status", &s); err != nil {
			fmt.Println("node on port", p, "unreachable:", err)
			continue
		}
		getJSON("http://127.0.0.1:"+p+"/chain", &ch)
		sts = append(sts, s)
		chains = append(chains, ch)
	}
	num := func(s status, k string) float64 { v, _ := s[k].(float64); return v }

	fmt.Println("=== Jen-0 devnet report ===")
	fmt.Println()
	// 1. agreement: compare block hashes at the lowest common height
	minH := math.MaxInt
	for _, ch := range chains {
		if len(ch) < minH {
			minH = len(ch)
		}
	}
	agree := true
	for i := 1; i < len(chains); i++ {
		for h := 0; h < minH; h++ {
			if chains[i][h].Hash != chains[0][h].Hash {
				agree = false
			}
		}
	}
	fmt.Printf("Agreement   : %d nodes share the same chain up to height %d: %v\n", len(chains), minH, agree)
	for _, s := range sts {
		sup, gen, iss := uint64(num(s, "supply")), uint64(num(s, "genesis")), uint64(num(s, "issued"))
		fmt.Printf("  node %v%s height %v tip %.8s… supply %s = genesis %s + rewards %s : %v\n",
			s["id"], map[bool]string{true: " (attacker)", false: ""}[s["evil"] == true], s["height"], s["tip"],
			fmtJEN(sup), fmtJEN(gen), fmtJEN(iss), s["supply_ok"])
	}

	// 2. blocks
	main := chains[0]
	var times []float64
	strikes, txs := 0, 0
	sumLnRate, sumLnFee, nTx := 0.0, 0.0, 0
	for _, b := range main {
		if b.Height > 1 {
			times = append(times, float64(b.BlockMs)/1000)
		}
		strikes += b.Strikes
		txs += b.Txs
		sumLnRate += b.SumLnRate
		sumLnFee += b.SumLnFee
		nTx += b.Txs
	}
	mean := func(xs []float64) float64 {
		t := 0.0
		for _, x := range xs {
			t += x
		}
		return t / float64(len(xs))
	}
	fmt.Println()
	fmt.Printf("Blocks      : %d blocks, average %.1f s apart (target %d s), %.1f strikes and %.1f transfers per block\n",
		len(main), mean(times), TargetBlockSeconds, float64(strikes)/float64(len(main)), float64(txs)/float64(len(main)))
	if nTx > 0 {
		purity := math.Exp(sumLnRate / float64(nTx))
		typFee := math.Exp(sumLnFee / float64(nTx))
		fmt.Printf("Measured    : purity (geometric mean fee rate) %.3f%% vs standard %.2f%%; coin weight (typical fee / typical rate) = %.2f JEN\n",
			purity*100, float64(StandardFeeBps)/100, typFee/purity/float64(Pico))
	}
	fmt.Printf("Block data  : %d transfers stored as compact records (%d B each, no signatures) + %d leaf proofs of 164 B\n", txs, 32, strikes)

	// 3. fairness of minting: share of blow hashing vs share of minter fees
	minterIncome := map[uint32]uint64{}
	minerIncome := map[uint32]uint64{}
	for _, b := range main {
		for m, k := range b.StrikesBy {
			minterIncome[m] += b.ShareEach * uint64(k)
		}
		minerIncome[b.Miner] += b.MinerCut
	}
	totBlow, totMint, totWon := 0.0, 0.0, 0.0
	for _, s := range sts {
		if s["evil"] != true {
			totBlow += num(s, "blow_hashes")
			totWon += num(s, "blows_won")
		}
	}
	for _, v := range minterIncome {
		totMint += float64(v)
	}
	fmt.Println()
	fmt.Println("Minting fairness (share of blow hashing -> share of winning blows -> share of minter fees):")
	sort.Slice(sts, func(i, j int) bool { return num(sts[i], "id") < num(sts[j], "id") })
	for _, s := range sts {
		if s["evil"] == true {
			continue
		}
		acct := uint32(num(s, "account"))
		made := num(s, "strikes_made")
		avgProve := 0.0
		if made > 0 {
			avgProve = num(s, "prove_ms_total") / made
		}
		fmt.Printf("  node %v: hashing %5.1f%% -> blows won %5.1f%% -> minter fees %5.1f%%   strikes %3.0f (avg prove %4.0f ms, %v blows wasted)   blocks sealed %v\n",
			s["id"], 100*num(s, "blow_hashes")/totBlow, 100*num(s, "blows_won")/totWon, 100*float64(minterIncome[acct])/math.Max(totMint, 1),
			made, avgProve, s["blows_wasted"], s["blocks_sealed"])
	}

	// 4. where the minters' proving work went
	{
		var proofs, discarded, pendingNow, won, noTx, roundEnded, gaveUp, claims, clashes, proveMs float64
		for _, s := range sts {
			if s["evil"] == true {
				continue
			}
			proofs += num(s, "strikes_made") + num(s, "proofs_discarded")
			discarded += num(s, "proofs_discarded")
			pendingNow += num(s, "my_strikes_pending")
			won += num(s, "blows_won")
			noTx += num(s, "blows_no_tx")
			roundEnded += num(s, "blows_round_ended")
			gaveUp += num(s, "blows_gave_up")
			claims += num(s, "claims_made")
			clashes += num(s, "claim_clashes_lost")
			proveMs += num(s, "prove_ms_total")
		}
		broadcast := proofs - discarded
		dropped := broadcast - float64(strikes) - pendingNow // broadcast but not used by the chain
		if dropped < 0 {
			dropped = 0
		}
		wasted := discarded + dropped
		fmt.Println()
		fmt.Printf("Proving work (claims %v, pick %v):\n", sts[0]["claims_on"], sts[0]["pick"])
		fmt.Printf("  blows won %.0f; proofs made %.0f, used in blocks %d, still waiting for the next block %.0f\n", won, proofs, strikes, pendingNow)
		fmt.Printf("  proofs wasted %.0f = %.1f%% of proving time:\n", wasted, 100*wasted/math.Max(proofs, 1))
		fmt.Printf("    %4.0f block arrived while proving\n", discarded)
		fmt.Printf("    %4.0f proven but dropped by miners (transfer already in another strike)\n", dropped)
		fmt.Printf("  blows not proven (no proving time lost): %.0f no free transfers, %.0f block arrived during claim wait, %.0f gave up after clashes\n",
			noTx, roundEnded, gaveUp)
		if claims > 0 {
			fmt.Printf("  claims sent %.0f, clashes lost and re-picked %.0f\n", claims, clashes)
		}
		_ = proveMs
	}

	// 5. attacks
	fmt.Println()
	fmt.Println("Attacks rejected by honest nodes:")
	tot := map[string]float64{}
	for _, s := range sts {
		if s["evil"] == true {
			continue
		}
		if rj, ok := s["rejected"].(map[string]any); ok {
			for k, v := range rj {
				tot[k] += v.(float64)
			}
		}
	}
	keys := make([]string, 0, len(tot))
	for k := range tot {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	for _, k := range keys {
		fmt.Printf("  %-60s %4.0f\n", k, tot[k])
	}
	if len(keys) == 0 {
		fmt.Println("  (none)")
	}
	// rewards sample
	fmt.Println()
	fmt.Println("Rewards paid (first blocks; V drawn from the seal of the next block):")
	for _, b := range main {
		if b.PaidReward > 0 && b.PaidRewardHeight <= 6 {
			raw := RawRewardPico(b.PaidRewardHeight)
			fmt.Printf("  block %d: raw %s JEN x V %.3f = %s JEN (paid in block %d)\n",
				b.PaidRewardHeight, fmtJEN(raw), float64(b.PaidReward)/float64(raw), fmtJEN(b.PaidReward), b.Height)
		}
	}
	_ = strconv.Itoa
}

func selftest() {
	fmt.Println("reward curve (V = 1), integer math vs float reference:")
	for _, h := range []uint64{1, 2, 10, 100, 1000, 729_328, 10_000_000} {
		got := float64(RawRewardPico(h)) / float64(Pico)
		ref := 2520 * math.Pow(float64(h), -0.5801544360679607)
		fmt.Printf("  N=%-9d %14.6f JEN   reference %14.6f   rel.err %.1e\n", h, got, ref, math.Abs(got-ref)/ref)
	}
	var lo, hi float64 = 1e9, 0
	for z := 0; z < 4096; z++ {
		v := float64(RewardPico(1, z)) / float64(RawRewardPico(1))
		lo, hi = math.Min(lo, v), math.Max(hi, v)
	}
	zmin := float64(PhiInvQ32[0]) / (1 << 32)
	fmt.Printf("  V range over the table: %.4f .. %.4f (expected r^%.3f .. r^%.3f = %.4f .. %.4f)\n", lo, hi,
		zmin, -zmin, math.Pow(3.3027756377, zmin), math.Pow(3.3027756377, -zmin))
}

// proofSelftest: one real leaf strike, then the attacks it must stop.
func proofSelftest(keys string) {
	p, err := LoadProver(keys)
	if err != nil {
		panic(err)
	}
	st := GenesisState(5)
	var txs [LeafSize]Tx
	var pubs [LeafSize]*PubKey
	for i := 0; i < LeafSize; i++ {
		c := CTx{From: uint32(i), To: uint32(i + 10), Amount: 10 * Pico, Fee: Pico / 10, Nonce: 0}
		k := KeyFromSeed(UserKeySeed(i))
		txs[i] = Tx{From: c.From, To: c.To, Amount: c.Amount, Fee: c.Fee, Nonce: c.Nonce, Sig: SignTx(k, c)}
		pubs[i] = st.Accounts[i].Pub
	}
	t0 := time.Now()
	proof, fee, err := p.Prove(txs, pubs, NodeAccount(0))
	if err != nil {
		panic(err)
	}
	s := Strike{Minter: NodeAccount(0), FeeTotal: fee, Proof: proof}
	for i := range txs {
		s.Txs[i] = txs[i].Compact()
	}
	fmt.Printf("leaf strike: proved in %s, proof %d bytes\n", time.Since(t0).Round(time.Millisecond), len(proof))
	t1 := time.Now()
	fmt.Printf("  honest strike verifies: %v (%s)\n", p.Verify(&s, pubs) == nil, time.Since(t1).Round(time.Microsecond))
	stolen := s
	stolen.Minter = NodeAccount(1)
	fmt.Printf("  stolen (other minter) rejected: %v\n", p.Verify(&stolen, pubs) != nil)
	alt := s
	alt.Txs[0].Amount++
	fmt.Printf("  altered amount rejected: %v\n", p.Verify(&alt, pubs) != nil)
	more := s
	more.FeeTotal++
	fmt.Printf("  inflated fee total rejected: %v\n", p.Verify(&more, pubs) != nil)
	bad := txs
	bad[1].Sig = append([]byte(nil), bad[1].Sig...)
	bad[1].Sig[len(bad[1].Sig)-1] ^= 1
	_, _, err = p.Prove(bad, pubs, NodeAccount(0))
	fmt.Printf("  cannot prove a forged signature: %v\n", err != nil)
	hi := txs
	hi[2].Fee = hi[2].Amount / 5 // 16.7% fee, above Jen's 6%
	hi[2].Sig = SignTx(KeyFromSeed(UserKeySeed(2)), hi[2].Compact())
	_, _, err = p.Prove(hi, pubs, NodeAccount(0))
	fmt.Printf("  cannot prove a fee above 6%%: %v\n", err != nil)
}
