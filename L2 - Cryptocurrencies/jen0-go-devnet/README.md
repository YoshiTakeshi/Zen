# Jen-0 — first experiment of Proof of Minting and mining on Bronze Jen

Jen-0 is a working devnet: several nodes on one machine (or many machines)
mint blocks together with **real zero-knowledge proofs**, miners seal them,
and rewards follow the metallic curve with a random factor drawn from the next
block. It exists to test the two new ideas of Zen — collaborative minting and
the metallic reward — with real cryptography, before anything else is built.

## Run it

Requires Go 1.24+.

```bash
go build -o jen0 .
./jen0 setup --keys keys          # one-time local proof setup (~10 s)
./jen0 selftest keys              # reward math + one real proof + attacks
./run_devnet.sh 480               # 5 honest nodes + 1 attacker for 8 minutes, then a report
```

If `golang.org` / `proxy.golang.org` are blocked on your network:
`GOPROXY=direct GOSUMDB=off GOFLAGS=-mod=mod go build -o jen0 .`

To run across machines, start `./jen0 node --id I --n N --port P --peers host:port,...`
on each machine with the same `keys/` folder and the same `--n`.

## What a node does

| Role | File | What it does |
|---|---|---|
| Wallet | `node.go: wallet` | sends signed transfers from this node's genesis accounts |
| Minter | `node.go: minter, strike` | hashes blows; each winning blow takes 4 waiting transfers, proves them, broadcasts the strike |
| Miner | `node.go: miner, buildCandidate` | collects strikes, keeps those that still apply, seals the block |
| Validator | `chain.go: AddBlock` | checks seal, difficulty, every proof, every rule, state root; picks the best chain |
| Attacker (`--evil`) | `node.go: evil` | stolen strikes, forged proofs, blocks altered after sealing |

## Rules implemented (SPEC = Zen Protocol Specification, Draft 0.1)

- **Blows** (SPEC 4.2): SHA256(prev block ‖ minter ‖ nonce) below the blow target.
- **Leaf strikes** (SPEC 4.3–4.4): one Groth16 proof (BN254, MiMC) per 4 transfers;
  it certifies signatures and fee limits, commits to every field, exposes the
  fee total and is bound to the minter. Blocks store transfers **without
  signatures** (32 bytes each) plus the proofs (164 bytes each).
- **Fee pot** (SPEC 4.6): 75% to minters, one equal share per strike; the rest to the miner.
- **Seal and fork choice** (SPEC 5.1–5.2): most work wins; equal work, lower hash wins.
- **Difficulty** (SPEC 5.3): retargeted every block toward the block time, smoothed and clamped.
- **Reward** (SPEC 5.4): `2520 × N^(−a) × r^Z`, integer-only (`reward.go`,
  `tables_gen.go`). Z comes from the seal of block N+1, so the reward of block N
  is paid inside block N+2 (a block cannot commit to its own seal).
- **Supply invariant**: every block checks supply = genesis + rewards, exactly.
- **Purity and coin weight** (SPEC 6): measured and reported, not yet used to resize.

## Deliberate simplifications (next: Jen-1)

| Jen-0 | Jen-1 |
|---|---|
| Leaf proofs certify signatures and fee limits; balances and nonces are executed by every node | Leaf proofs also prove the balance-tree update |
| The stamp is the list of leaf proofs | Recursive merge strikes into one stamp |
| Fixed blow difficulty and capacity | Blow difficulty and capacity adjusted (purity rule) |
| HTTP gossip, devnet keys from seeds, local trusted setup | Real P2P, real wallets, setup ceremony or setup-free proofs |
| Block time 15 s | Jen's real 2.5 min |

## Files

| File | Content |
|---|---|
| `params.go` | every consensus constant of the experiment |
| `reward.go`, `tables_gen.go`, `tools/gen_tables.py` | integer reward curve and the generator of its constants |
| `types.go` | transfers, strikes, blocks, hashing, keys |
| `circuit.go` | the leaf circuit, setup, prove, verify |
| `state.go` | accounts and block application rules |
| `chain.go` | block tree, validation, difficulty, fork choice |
| `node.go` | networking and the node roles |
| `main.go` | commands, report, self-tests |
| `run_devnet.sh` | the 6-node test |

## Results (one machine, 2 CPU cores, 6 nodes, 15 minutes)

See `results/`. Summary of `results/devnet_15min_report.txt`:

- 59 blocks, 14.8 s apart on average (target 15 s); all 6 nodes on the same chain.
- Supply = genesis + rewards, exactly, on every node.
- 904 transfers stored without signatures (32 B each) + 226 leaf proofs (164 B each).
- Leaf strike: about 1.4 s to prove with 6 nodes sharing 2 cores (1 s alone), 1.7 ms to verify.
- Fairness: each node's share of minter fees matched its share of winning blows
  within about 2 percentage points (blows themselves follow hashing power, with lottery noise).
- Attacks: all stolen strikes, forged proofs and altered sealed blocks rejected.
- Race detector: no data races (`results/race_detector_run.txt`).

### Network split (`split_test.sh`, `results/split_test.txt`)

6 honest nodes: together 2 min, split into {0,1,2} and {3,4,5} for 3.5 min, reconnected 2.5 min.

- During the split each side built its own chain (heights 8 → 20 separately).
- After reconnecting, every node moved to the side with more work: all 6 at
  height 32, same tip, same state root, supply exact everywhere.
- Nodes 0–2: one reorganization, 12 blocks abandoned. Nodes 3–5: none.

### Bigger blocks (`big_blocks.sh`, `results/big_blocks.txt`)

5 nodes, 600 users, easier blows, 7 minutes.

- 28 blocks at 14.8 s; 46 transfers per block on average, largest 92; 1,288 transfers total.
- Proving costs 2.8–3.1 s per strike when 5 nodes share 2 cores: **minting
  capacity is CPU-bound** — about 600 transfers stayed waiting at each node.
- Fairness still holds under load (fee share vs blow share within ~2 points).
- 4 honest strikes went stale (their transfers were taken by another block first).

### Findings for Jen-1

1. **Keep signed transfers until finality.** Blocks store no signatures, so
   transfers in an abandoned branch cannot be re-broadcast from the blocks
   themselves. Nodes (and wallets) must keep the signed transfers until the block
   is a few blocks deep, and put back into the pool those of abandoned blocks.
2. **Capacity must follow the minters' proving power.** Fixed blow difficulty
   either wastes blows or leaves a backlog; Jen-1 adjusts it (purity rule).
3. **Claim then prove.** Stale strikes waste proving time; minters should claim
   their 4 transfers before proving (Jen-1 design note).

Not yet tested: nodes on separate machines and long runs (hours).
