# Status (round 55)
Every operation is proved: four leaf circuits (vault, channel, order incl. claim, factory), universal merge, shrink, BN254 layer, Groth16. Current verifying key: `out_v7/zen.vk` (older keys, e.g. `out_v6`, do not accept current blocks). Soundness battery: `src/soundness.rs`. Plan and open items: `PROOFS-PLAN.md`; security notes: `SECURITY-REVIEW.md`. Not for real value yet: single-party Groth16 setup, foreign payment proof checked by nodes only.

---

# Builder hardware (decision: option A, every block carries its stamp)
Minters: phones/PCs (CPU). Builder, in practice a mining pool: state leaves, merges, BN254 layer on
server CPU cores, the final Groth16 stamp on an NVIDIA GPU (gnark's ICICLE backend: same proving key,
same 196-byte proof, same verifier). Miners: SHA-256 ASICs over Stratum. GPU prover code, build steps
and a one-command benchmark for a rented GPU server: ../g16wrap/BUILDER-GPU.md, bench_gpu.sh,
zenwrap/accel_icicle.go. It compiles and links here; GPU timings still to be measured.

---

# Round 11: payouts inside the proof (credits), Groth16 for version 4, a pool-compatible seal

## 1. Credits: the prover, the miner and the fee pool are paid inside the proof
A state-leaf slot that the signature leaf left empty can be a CREDIT: no sender, no signature, an
amount added to an account, which is created on first receipt (nonce height << 20, like a payment to
a new address). Nodes compute the exact payout list from the consensus rules and a block is valid only
if its credits, in order, are that list; the proof checks that each one reached the account tree.
- Rule (ported from Go Jen-0.10; 75/25 still Open): half of each leaf's fees goes into the fee pool,
  75% of the rest to the leaf's prover (the minter's own address, one key per person), the remainder to
  the miner; the pool pays 1/32 of what it held per block, 75% shared by the block's paying leaves'
  provers, the rest to the miner; rewards owed from block h-2 (miner, ticket minters) come first.
  One credit per address, in first-appearance order (blockdata::expected_credits).
- A leaf with no payments is a credit-only leaf: its signature leaf is the empty one (no minter), which
  the builder proves once and reuses.
- Block data version 4: per leaf a payment mask and a credit mask (40 B header); a credit is
  u32 receiver | varint amount | 32 B address if new. A new account may not be opened for an address
  that already has one (node rule).
- Circuit cost: none visible. The state leaf still fits 2^13 rows (2.70 s); merges 2.65 s.

Measured (16 x 8, DOUBLESPEND=1 REPLAY=1, POOL=3,200,000, log run_v4_16x8.txt): 112 signed payments,
110 applied, 2 skipped; leaf 7 credit-only with 11 credits (3 rewards incl. one creating the ticket
minter's account, 7 prover shares, the miner's cut); fee pool 3,200,000 -> 8,126,656. Node replay
matches all 16 public values and the payout list. Rejected: one changed byte, S + 1, a node expecting
another miner, and a builder paying one unit too much (OVERPAY=1: its proof is valid, the block is not).

## 2. Groth16 for version 4
Same final circuit size, new constants (the merge key changed): gnark v0.16.4, 4,203,150 constraints,
test engine satisfied; setup 1,246 s (proving key 2.0 GB, verifying key 1,008 B); prove 96.1 s; the
stamp is 196 bytes and verifies in 2.6 ms. The same stamp checked against another block's public
values: rejected. Files: ../g16wrap/result_v4 (log, verifying key, proof, Solidity verifier).

## 3. The seal works with standard SHA-256 hardware and Stratum v1 pools (src/seal.rs, `zenproof seal`)
- Header: Bitcoin's 80 bytes, little-endian, SHA256d, compact nbits target. Test: our code gives
  Bitcoin's genesis block hash 000000000019d668... and its target check (unit test).
- Commitment = SHA256d(SHA256d(coinbase) || body root): exactly a Bitcoin merkle root of one coinbase and
  one branch, which every pool and miner computes. Coinbase = "ZenSeal1" | chain | height | extranonce
  length | extranonce1 (pool) | extranonce2 (miner) | miner address (32 B). Body root = SHA-256 over the
  stamp's public values, the stamp, the block data hash and the tickets root.
- Version rolling (BIP 320 bits 13-28) allowed, so ASICs with version rolling work too.
- Test: a job sent as a real mining.notify; a miner that only knows Stratum (word-swapped prevhash,
  big-endian hex fields) builds the coinbase and header and finds a share; the node rebuilds it and
  accepts it, paying the pool's address. Rejected: the seal reused for a changed block, the miner
  address swapped after solving, the seal shown to another chain, a version outside BIP 320, easier
  bits than asked, a wrong nonce. Log: run_seal.txt.
- Changes from the Go devnet: the time is the header's ntime in seconds (no ms field), the miner address
  lives in the coinbase, and difficulty uses Bitcoin's compact bits (difficulty 1 = 0x1d00ffff).

---

# Blows in Rust, one key per person (src/mint.rs, `zenproof mint [attempts]`)

The minter signs its blows with the SAME EcGFp5 Schnorr key that signs its payments. Its address
(Poseidon hash of the public key) is both its account and its minting identity, so tickets, the
credential, the minters' share of new coins and the 75% leaf-fee share all go to one account, and
giving the key to a pool would give away the account's money (minting stays personal).

- Message: Poseidon("ZenBlow" tag, chain id, previous block as 8 x u32, nonce as 2 x u32). Payment
  messages start with the chain id (1..3), blow messages with the tag: one can never pass as the other,
  and the chain id stops a Jen blow counting on Ken.
- Signature: the payment scheme in compact form (e, s): e = 128 bits of Poseidon(R, A, msg),
  s = r + e*k mod n, checked as R = sG - eA. r = SHA-256(key, msg) reduced mod n (deterministic: a
  phone needs no random source and never reuses r).
- Blow: Argon2id(prev || ticket fields; salt "Zen-blow-v1" || prev; 64 MB, 1 pass, 1 lane, 32 B), wins
  when below 2^256 / difficulty (as in Go Jen-0.5).
- Ticket: 105 bytes = public key compressed to 41 B (x + sign) + nonce 8 + e 16 + s 40. It carries the
  key because accounts store only its hash; a node checks a ticket with no state. Decoding rejects
  non-canonical values and points outside the prime-order group. At most one ticket per (address,
  nonce) per block: re-signing a nonce is possible but costs a new Argon2id run, i.e. just an attempt.
- Difficulty retarget (24 blows per block, +-12.5%) and minting gate (a third of the work average,
  at least one blow) ported from Go.

Measured (2-core server, one core, native Rust): sign 1.2 ms, Argon2id 84 ms, about 13 attempts/s;
node check of a ticket 1.7 ms + one Argon2id (about 75 ms), so 24 tickets cost about 1.8 s of one
core per 2.5-minute block. Rejected: changed nonce, same ticket on another chain, on another round,
another key swapped in, a key with an order-2 part, a payment signature passed off as a blow, a
blow above the target. Unit tests: `cargo test --release mint::` (3 pass). Log: run_mint.txt.

Not yet in Rust: tickets inside blocks and the state (credentials, leaf quota, minters' pool), the
node and the network; those come with the Rust node.

---

# zenproof version 3: signature leaves (minters) + state leaves (builder)

## Why
In version 2 a leaf proved "state root before -> after", so leaf 2 could not be proved before leaf 1:
minters had to know the state and each other's leaves. Proof of Minting needs many minters (phones)
proving at the same time. Version 3 splits the leaf:

1. **Signature leaf (minter, stateless).** For up to 16 signed payments: each signature (chain-tagged
   message, EcGFp5 Schnorr), amount and fee < 2^62, fee band 0.01%-6%, floors in coins (amount >= S/6,
   fee >= S/100), real payments first. Public values: sig hash (the 13 signed fields of every slot plus
   the minter's address) and S. No balances, no tree: any number of minters prove at once.
2. **State leaf (block builder).** Verifies one signature leaf inside it, repeats the signed fields as
   witness (their hash must equal the sig hash, so the builder cannot change a payment, a nonce or the
   minter's address), and applies the payments to the account tree in order. Public values are the
   version-2 ones, so the universal merge, shrink, BN254 layer and Groth16 wrap are unchanged.
3. **Skip.** A signed payment that no longer fits the state (the same nonce spent in two minters'
   leaves, a replay, a balance already spent) is skipped: no state change, no fee, not counted, absent
   from the block data. Skipping needs no proof; leaving the whole leaf out would have the same effect.
   One bad payment therefore no longer spoils a minter's whole leaf.

Block data version 3: per leaf a used-slot mask replaces the payment count (38 B leaf header), since
applied payments need not fill the first slots once some are skipped.

## Results (2-core server, 16 slots x 8 leaves, DOUBLESPEND=1 REPLAY=1)
| step | who | circuit | time | proof |
|---|---|---|---|---|
| signature leaf | minter | 2^14 | 5.98 s each (8) | 142.7 KB, peak 0.9 GB |
| state leaf | builder | 2^13 | 2.84 s each (8) | 130.4 KB |
| merge | builder | 2^13 (same shape as the state leaf) | 2.87 s each (7) | 130.4 KB |
| shrink | builder | 2^12 | 1.47 s | 124.3 KB |
| BN254-Poseidon layer | builder | 2^12 | 84.3 s | 73.5 KB, peak 1.4 GB |
- 128 signed payments: 126 applied, 2 skipped (a double spend: same sender, same nonce, other
  receiver; and a replay of payment 1 with its signature); 21 new accounts, 1 closed.
- Block data 2,580 B for 126 payments; node replay matches all 16 public values; one changed byte or
  S + 1 is rejected; stamp root equals the account tree.
- Builder work for the block: 8 x 2.84 + 7 x 2.87 + 1.5 + 84 = about 128 s on 2 cores (v2: about 125 s,
  but then the minters' leaves also had to wait for each other). Merges got cheaper (2.87 s instead of
  5.66 s) because the state leaf fits 2^13 rows, so the shared shape is 2^13 instead of 2^14.
- Attacks: forged signature (CORRUPT=1): no signature-leaf proof. Builder changes one signed fee
  (TAMPER=1): no state-leaf proof. Applying a skipped payment is impossible (its Merkle checks fail).
- Groth16: the BN254 layer has the same size (2^12) but new constants (the merge key changed), so the
  final Groth16 circuit needs a new setup (about 20 min); not rerun in this round.

  DOUBLESPEND=1 REPLAY=1 BN_OUT=out_v3 ./target/release/zenproof 16 8   (log: run_v3_16x8.txt)
  TAMPER=1 / CORRUPT=1 ./target/release/zenproof 4 2

---

# zenproof: block proof version 2 (Plonky2 + one Groth16 key for every block size)

Builds on p2sigopt (signatures inside the proof, custom EcGFp5 gate) with two changes.

## 1. Leaf circuit round
- Chain id in every signed message: Poseidon(chain id, sender, receiver, amount, fee, nonce, close).
  The same key works on Yen, Ken and Jen; a signature for one chain is useless on another.
- Fee floor in coins, against the block's public value S (base units per coin):
  amount >= S/6 (smallest payment, 1/6 JEN) and fee >= S/100 (smallest fee, 0.01 JEN), plus the
  0.01%-6% rate band as before.
- New accounts: a payment can set `new`; the receiver's slot must hold the empty leaf, and the new
  leaf is (address, amount, nonce = height << 20). The block data carries the 32-byte address once.
- Closing: a payment can set `close` (signed); the sender's balance must end at 0 and its leaf
  becomes empty, freeing the slot. A re-created account starts at nonce height << 20, above every
  nonce the closed one could have used, so old signatures can never be replayed against it.
- Prover address per leaf, inside the leaf's data hash: the block data fixes who earns each leaf's
  fees (credits = leaf fee total per prover, computed by every node from the bytes).
- 16 public values: root before (4), root after (4), fee total, count, data hash (4), S, height.

## 2. Universal merge circuit (one key for any block size)
Leaf proofs and merge proofs have the same circuit shape (same size, same gate set, same 84 public
values: the 16 above + 68 for a verifying key). The merge circuit verifies a left and a right child;
each child is checked either with the leaf's fixed key or with the merge circuit's own key, which a
merge proof carries in its public values (a merge child must carry the same key). The right child can
be marked empty, so an odd child passes through. Any number of leaves therefore ends in a proof of
the same merge circuit, and the wraps above it (shrink, BN254 layer, Groth16) never change.
The shrink wrap checks that the root merge proof's key values are the real merge key.

How the shapes are matched: build the leaf and a first merge, take the union of their gate types,
rebuild both with that gate set and the same row count (2^14 for 16-slot leaves, 2^13 for 4-slot),
and check that their common circuit data are identical (it took one rebuild).

## Results (2-core server)
| block | leaves | payments | new accounts | closed | leaf (avg) | merges | final circuit |
| A | 8 | 128 | 21 | 1 | 5.75 s | 7 x 5.66 s | same |
| B | 3 | 40  | 6  | 1 | 5.36 s | 3 x 5.52 s | same |
| C | 1 | 5   | 2  | 1 | 5.40 s | 1 x 5.32 s | same |
- Block data: 2,596 B for A (128 payments, 21 of them creating accounts at +32 B, 8 leaf headers of
  37 B), 824 B for B, 175 B for C. The node replay matches root, fees, count, data hash, S and height
  in all three; one changed byte, or a wrong S, is rejected.
- Forged signature (CORRUPT=1) and replayed payment (REPLAY=1): no proof.
- Groth16: see ../g16wrap/result_v2 (one setup, three block sizes).

## Run
  RUSTC_BOOTSTRAP=1 cargo build --release
  BN_OUT=out ./target/release/zenproof <slots per leaf> <leaves>
  env: REAL (payments), SEED, S, HEIGHT, NEWACC (every k-th payment to a new address), CLOSE (the k-th
  payment closes its sender), CORRUPT, REPLAY, BN_RATE/BN_QUERIES/BN_POW

## Groth16, one key for three block sizes (result in ../g16wrap/result_v2)
| | constraints | setup | block A (8 leaves) | block B (3 leaves) | block C (1 leaf) |
| gnark v0.16.4 | 4,203,150 (16 public values) | 20.4 min, pk 2.0 GB, vk 1,008 B | 93.8 s, 196 B, verify 3.4 ms | 95.4 s, 196 B, verify 2.9 ms | 96.6 s, 196 B, verify 2.5 ms |
Block C's proof against block A's public values: rejected. Test engine: all three satisfied.


## Round 12: minters are paid by lottery, not by ledger (Justus L. Ludovic)
- Each block's minter share goes straight to that block's winning tickets (reward from block h-2, as before).
  No owed ledger, no per-address state. TARGET_BLOWS is now 24, so a block never spends more than 24 credits
  on minters, whether there are 100 minters or a billion: more minters only raise the difficulty.
- `zenproof payouts` (run_payouts.txt): credits per block 18 to 24 from 100 up to 300,000 simulated minters;
  pay follows work (top 1% of minters get 0.356 of the pay for 0.352 of the work).
- Cost: a small solo minter wins rarely (about one ticket in `minters / 24` blocks). Steady income comes from
  minting pools, which are ordinary addresses paying out with ordinary payments.
- The 32-block bucket ledger (`Owed`) was tried and removed: its saving fell to 1.6x at 10,000 minters.


## Round 13: "each gram counts once" is in the account leaf and in the proof (Justus L. Ludovic)
- Account leaf = address(4), balance, nonce + five peg numbers: `rest` (rested balance), `used` (rested money already
  counted this period), `fd` (day of the last receipt), `rd` (day the rested money counts from, for coin-days),
  `up` (period `used` belongs to). The part of the balance above `rest` is fresh. 11 field elements.
- Rules (src/blockdata.rs `settle`, `pay_from`, `receive_to`; the circuit twin is in `build_state`):
  every send and receive first settles the account at the block's day d = height / 576 and period p = d / 3:
  fresh money matures into `rest` once d >= fd + 3 (then rd = fd); `used` restarts in a new period. A payment spends
  fresh money first, counts min(amount, rest - used), and rested money that leaves is the used money first.
  A receipt adds fresh money and sets fd = d (the clock of all fresh money restarts: conservative).
- The state leaf takes h = 576 d + rem, d = 3 p + q as checked witnesses. Block data format is unchanged (still 2,401 bytes in the
  16 x 8 test block): the peg numbers live only in the leaf; nodes recompute them while replaying.
- Replay now returns what each payment counted (`Counted{amt, age}`; `weight()` = amt x min(age,30)/30, the coin-days weight)
  for the daily histograms of S (still to build).
- Size: the peg added 4 hash rows and about 5 rows per slot, which pushed the state leaf (and so the universal merge) over
  2^13. A cheaper Merkle-path step (3 arithmetic operations per pair instead of 4) took it back to 8,043 gates, 2^13 rows.
  Timings unchanged: state leaf 2.63 s, merge 2.67 s, shrink 1.5 s, BN254 layer 85 s.
- Tests: 3 unit tests (loop counts once per period; fresh-first spending; invariants rest <= bal, used <= rest over 5,000
  random steps); run_v5_peg_16x8.txt (PEGMIX=1 HEIGHT=4000: genesis accounts with maturing, immature, used and expired-used
  money): proof verifies, node replay matches the proof and the builder's counted amounts. PEGCHEAT=1 (builder claims
  more rested money than the leaf holds) gives no proof.
- Balances are now below 2^62 in the circuit (was 2^63), so comparisons fit in one 63-bit split.
- Not redone: the Groth16 setup for this version (the merge key changed, so the shrink and BN254 layer change; same size, a new setup is needed).

## Round 14: the node, stage 1 (src/node.rs, `zenproof node devnet [blocks]`) (Justus L. Ludovic)
- `Chain::validate(&self, block, now)` runs every check in order of cost and changes nothing; `commit` applies a valid block;
  `accept` = validate + append to `blocks.log` + commit.
  1 structure and size limits; 2 seal (Bitcoin header, previous block, bits, coinbase for this chain and height, commitment to
  pubvalues + stamp + block data + tickets, hash below target, time after the previous block and not more than 2 h ahead);
  3 tickets (key, signature, Argon2id work, difficulty; one per (address, nonce); at most 4 x 24; enough minting work);
  4 block data replayed on the node's own state with the payouts owed (rewards of block h-2, prover shares, miner cut, fee pool);
  5 public values equal the replay's and the stamp verifies them (`StampVerifier` trait); 6 state, fee pool, rewards owed
  (paid in h+2), blow difficulty, minting gate, seal difficulty window (every 32 blocks, at most x2) and tip are updated.
- `Block::encode/decode` (bounded sizes), `blocks.log` (length-prefixed), restart replays and fully re-validates the log.
- `audit()`: balances + fee pool + rewards owed = genesis + everything issued, and the peg invariants hold, after every block.
- Devnet: 12 wallets, tickets made with the real memory-hard blow (64 MB Argon2id), random payments, credits placed by the builder,
  a one-thread miner at an easy seal difficulty (run_node_devnet.txt): 12 blocks, supply exact, restart gives the identical state.
  Checking a block costs about 2 s, nearly all of it 24 Argon2id calls (about 75 ms each; they can run in parallel).
- Tests (3 new): a block is rejected for each of 13 faults (previous block, time, time ahead, seal target, body changed after
  sealing, no tickets, same blow twice, ticket from another block, one credit one unit too high, block data changed, public values
  changed with a matching stamp, wrong stamp) and none of them changes the chain; restart from the log; seal difficulty window.
- NOT in stage 1 (and flagged so): the stamp check is `DevStamp` (a hash of the public values, NOT a proof; plug the Plonky2 and
  Groth16 verifiers in behind `StampVerifier`); payments are not signed on the devnet (signatures live in the proof);
  S is a fixed parameter; the reward is flat (the metallic curve with its random factor and the integer Phi^-1 table come later);
  one linear chain, no fork choice or reorgs, no peers, no mempool, no Stratum server, state is kept whole in memory (each block
  clones it: fine for a devnet, a persistent tree comes later).
- Next stages: 2 networking and fork choice (state snapshots per tip, reorgs, block and ticket relay, a Stratum server);
  3 real stamp verification and the reading of S; 4 wallet, mempool and signed payments.

## Round 15: the node, stage 2 (src/p2p.rs, `Node` in src/node.rs) (Justus L. Ludovic)
- Fork tree (`Node`): every valid block is stored with a snapshot of the consensus state after it; switching branches is
  switching a pointer. Fork choice (SPEC 5.2): most total weight, a block's weight = seal work x min(tickets, 2 x recent
  average) / recent average; equal weight: lower seal hash. Orphans (unknown parent) wait, at most 64, and attach when the
  parent arrives. Reorg depth is recorded. All blocks (every branch) go to `blocks.log`; restart replays and revalidates them.
- Peer protocol (TCP, framed): HELLO(genesis, height, tip), INV, GETBLOCK, BLOCK. A node that hears of an unknown tip asks for
  it and walks back through orphans to genesis. Every block is fully validated before it is stored or relayed; a peer sending
  an invalid block, a malformed frame or another genesis is disconnected.
- Stratum v1 server: subscribe, authorize, notify (a fresh job whenever the best tip changes), submit. A share that meets the
  block target is assembled into a sealed block (`Block::with_share`) and submitted like any other block. `TemplateSource` is
  the pool side (tickets, payments, stamp); the devnet one uses the wallets. `stratum_client_mine` is a CPU miner that knows
  only Stratum.
- Tests (3 new): fork choice + out-of-order orphans + a reorg of depth 1 + an invalid block refused + duplicate block;
  two nodes syncing four blocks over TCP and following a fifth, a node on another chain dropped; a Stratum-only miner seals two
  blocks and a second node follows them. Live run (run_node_net.txt): `zenproof node serve` x2 (the second connected to the
  first) and `zenproof node mine`: 4 blocks sealed through Stratum, both nodes at the same tip.
- Run it: `zenproof node serve <p2p addr> <stratum addr> [peer addr]` (set ZEN_DIR for a block log), `zenproof node mine <stratum addr> [blocks]`.
- Not in stage 2: share difficulty below the block target and `mining.set_difficulty` (a real ASIC farm needs them); the exact
  hex byte order of nonce/ntime in `mining.submit` is untested against a real miner; a bounded block-request window (sync is one
  block per round trip); peer discovery, banning scores, DoS limits beyond frame and orphan caps; validation outside the node
  lock (a 2 s block check holds it); snapshot pruning; mempool and signed payments.
- Next: stage 3 = real stamp verification (Plonky2 stamp, then Groth16) and the reading of S; stage 4 = wallet, mempool and signed payments.

## Round 16: real stamps in the node (src/prover.rs) (Justus L. Ludovic)
- `Circuits::build(16)` builds the signature leaf, state leaf, universal merge and shrink wrapper deterministically (about 11 s
  on 2 cores), so every node gets the same keys without a ceremony on this path.
- `ProverMaker` (the pool): from the block's leaves it signs each payment with the sender's key (the wallet's job; the devnet
  wallets' keys live in the pool), proves the signature leaves, the state leaves in block order on the evolving state, the merge
  tree and the shrink wrapper. The shrink proof is the stamp: about 127 KB with Plonky2 (the Groth16 form is 196 B).
- `Plonky2Stamp` (every node): parses the stamp, checks its 16 public values equal the node's own replay of the block data and
  verifies it against the locally built shrink circuit. Both sides plug into the node through `StampMaker` / `StampVerifier`.
- Test `real_stamps_are_verified_by_the_node`: a 20-payment block (2 leaves, real signatures and proofs) proved in 26.5 s on
  2 cores and checked by the node in 1.7 s (tickets, replay and stamp); a stamp that proves another block, a damaged stamp, a
  truncated stamp and a DevStamp-style fake are all refused; the honest block goes in; supply and peg invariants hold.
- Live run (run_node_real.txt): `ZEN_REAL=1 zenproof node serve ...` x2 and `zenproof node mine`: a Stratum-only miner sealed 2
  blocks carrying real stamps, the second node verified and followed both (about 22 s per block, almost all of it the pool proving).
- Not yet: the Groth16 stamp verifier in the node (the gnark proof and key are produced by the Go tool; a Rust verifier needs
  BN254 pairings and the Pedersen commitment check of gnark's key); a second implementation of the verifier for cross-checking;
  proving in parallel across machines (the pipeline runs one block on one machine); the reading of S from payments (S is
  still a fixed parameter); wallets signing for themselves (here the pool signs for the devnet wallets).

## Round 17: the reading of S (src/reading.rs) (Justus L. Ludovic)
- S is no longer a fixed parameter. Each chain keeps a `Reading` (genesis S, anchor, two histograms, the day readings); the block
  replay uses the chain's current S and puts it in the public values, so a builder using any other S is rejected.
- Counted payments (the peg of round 13) are sorted by their full amount: Sen-priced if it is a whole number n of sixths of the S of
  one of the last 8 blocks (S is kept a multiple of 6 so a sixth is a whole number), otherwise ordinary. Each adds its coin-days
  weight to a histogram of 1,024 bins, 1/16 octave wide, built with integer square roots only (no floats in consensus).
- Day end (the last block of every 576): the middle 20% of weight on each side, by log position, gives the typical ordinary value
  and the typical Sen price in sixths; S_day = 6 x ordinary / sixths. S_day is clipped to +-10% of the Fibonacci window before it
  (day groups 1, 2, 3, 5, 8, 13 weighted 32, 16, 8, 4, 2, 1), the anchor follows the window by at most 0.75% a day (settled below), and S stays within
  +-10% of the anchor. A day with fewer than `min_obs` counted payments on either side is skipped and S holds.
- Standard fee: only payments paying at least the standard fee count (1% Jen, 0.4% Ken, 0.1% Yen). Receiver cap: one receiving
  account brings at most 0.03% of the previous day's counted Sen-priced weight (`cap_bp`; off on the devnet).
- Tests: log table spacing; the ratio is read to within 6%; S follows a 2x change in the true Sen value at the anchor's pace and
  stays inside the band; fee and cap rules; maximal push; chain test across a day boundary (S held inside the day, moved +9.6% toward a
  true value 20% higher, a second node replaying the blocks has the same S, anchor and state root, a block using the old S is refused).
  All 27 tests pass (run_tests_round17.txt), including the real-stamp test with S in the proof.
- FINDING and decision on the anchor speed: with the first guess of 2.9% a day (0.005% a block) the hard bound was +34% in 7 days and
  +105% in 30 for unlimited money. Sweep (same rule, honest readings exact; days to be within 5% after a genuine change):
  anchor/day 2.9%: push +34% / +105%, +50% in 27 days, x2 in 47; 1.5%: +22% / +72%, 27, 47; 1.0%: +18% / +48%, 27, 55;
  0.75%: +16% / +38%, 35, 74; 0.5%: +14% / +28%, 52, 110. Above 1.5% the anchor never binds honest convergence (the day clip and
  window do), so the speed only widens the attacker's reach. DECIDED (Proposed): 0.75% a day (ANCHOR_UP 75, ANCHOR_DOWN 74 ten-thousandths,
  about 0.0013% a block). The Rust reading measures +15.8% in 7 days and +37.5% in 30 for unlimited money, in line with the spec's
  simulated 13% / 37%, and an honest +50% change is followed in about 35 days (spec: 37-41). A x2 change takes about 74 days.
- Not built: bond on disagreement and its penalty, the 20% stricter rule when receivers disagree ("the day does not count"),
  watchers; the day length is the circuit's constant (576 blocks), so the chain test moves the height instead of mining a day.
- Snapshots now carry the reading (about 40 KB each); pruning is still open.

## Round 18: wallet, mempool and signed payments (stage 4) (Justus L. Ludovic)
- `src/tx.rs`: the signed payment, 154 bytes: sender public key (41 B compressed point, the address is its Poseidon hash), receiver
  address (32), amount, fee, nonce (8 each), close flag (1), compact Schnorr signature e (16) + s (40) of the same scheme as tickets.
  The signed message is the circuit's own (`msg_native`), so what the mempool checks is what the signature leaf proves. A nonce
  must equal the account's nonce; a new account starts at height << 20. Text addresses are `zen1` + 64 hex + 8 hex checksum.
  `Wallet`: generate from the OS random source (256-bit secrets, as the signing code uses four limbs), save/load a file readable by
  its owner only and never overwritten, sign.
- `src/mempool.rs`: admission in order of cost: the consensus limits the replay enforces (smallest payment and fee from S, fee
  0.01% to 6%), a sender with an account, the signature, the nonce (the account's next nonce plus its own waiting payments, up to 16
  queued), the balance covering everything the sender has waiting; closing accounts is refused (the builder has no close yet).
  Replace-by-fee needs 10% more fee and is refused when it would strand a later payment of the sender. Full pool (50,000): a payment
  is taken only if its fee rate beats the worst, which leaves with the sender's later payments. `select` gives the best fee rate first,
  each sender in nonce order; `on_block` drops what a block confirmed or what no longer applies.
- Peer protocol (p2p.rs): TX (a payment: checked at the best tip, kept, relayed if new, answered by TXACK with the reason when refused),
  GETACCT / ACCT (balance, nonce, next nonce counting waiting payments, height). A refused payment does not drop the peer; a
  malformed frame does. `Chain::account` finds an account by address (an index rebuilt on commit).
- The pool (`PoolSource`) takes its payments from the mempool. With real stamps the signed payments go to the prover's store and
  `prove_sig` uses the wallet's own signature (R = sG - eA recomputed); only if there is none does it sign with a devnet key it holds.
- CLI: `zenproof wallet new|devnet|address|balance|pay`, `zenproof node serve` (now stage 4: a node with mempool and pool).
  run_wallet.txt: a fresh wallet gets two queued payments from a devnet wallet, a mistyped address and an overspend are refused with
  reasons, a Stratum miner seals the block, balances and nonces move, the new wallet pays on (its nonce 1,048,576 = 1 << 20).
- Tests (35 pass, run_tests_round18.txt): signature round trip and every changed field breaking it; address checksum; wallet files
  (this found a real bug: secrets reduced mod the group order were 319 bits and did not fit four limbs); admission rules; RBF; full
  pool; selection order; blocks clearing the pool; wallet to mempool to block over TCP with a Stratum miner and a second node that
  heard the payments by relay and cleared its pool; a real-proof block where a wallet whose secret the pool does not hold pays with its
  own signature (13.7 s to prove), and a block whose store holds a signature that is not the sender's gets no proof.
- Not built: closing accounts (builder and mempool), putting back the payments of a block lost in a reorg, payment fee estimation,
  mempool persistence, relay limits and ban scores for bad payments, a wallet that watches for confirmation and re-sends, hardware or
  seed-phrase key storage, receiver-signed ("two signatures") payments of spec 6.6, and the chain id in the signed message is still the
  Jen constant (3), so Ken and Yen need it passed in.

## Round 19: the Groth16 stamp verifier in Rust (src/groth16.rs) (Justus L. Ludovic)
- The node can now check the 196-byte gnark stamp without Go. `Groth16Stamp` plugs into the node as a `StampVerifier`; the
  stamp's 16 public values go in as the circuit's 16 public inputs (each a Goldilocks number).
- It reads gnark v0.16.4's own formats: the proof (A, B, C, one BSB22 commitment and its proof of knowledge, compressed points) and the
  1,008-byte verifying key (alpha1, beta1, beta2, gamma2, delta1, delta2, K, committed-public lists, one Pedersen key). Compressed
  points are gnark-crypto's (flag in the top two bits, G2 x as A1 then A0); points are checked on the curve and in the subgroup.
- Verification is gnark's, in its order: the commitment hash becomes a public input (RFC 9380 expand_message_xmd with SHA-256, DST
  "bsb22-commitment", over the commitment's 64 uncompressed bytes), the Pedersen proof of knowledge e(C, -GSigma) e(PoK, G) = 1, then
  e(A,B) = e(alpha,beta) e(L,gamma) e(C,delta) with L = K0 + sum x_i K_i + commitment. Built on ark-bn254 (arkworks 0.5).
- Tests: expand_message_xmd against RFC 9380 vectors (K.1); the three real proofs of the version-2 setup (g16wrap/result_v2, blocks
  A, B, C, each with its own public witness) verify; block C's proof with block A's public values, any one of five changed public
  values, a bit flipped in each field of the proof (8 positions), a short proof, swapped A and C, swapped commitment and proof of
  knowledge, 15 public values, a changed value through the node interface: all rejected; the version-4 key and proof parse.
  `zenproof g16verify <vk> <proof> <pub>` checks any gnark proof from the Go tool (run_groth16.txt).
- Speed: about 4.2 ms per stamp in Rust (gnark's Go verifier measured 2.5 to 3.4 ms), single thread, 2 vCPU VM.
- What this is not yet: the key it was tested against is the version-2 key. The current circuit (peg leaf, version 5) needs a new
  Groth16 setup (about 20 min, 6 GB, single party) before a Groth16 stamp of a current block exists, so no current block has been
  checked this way; the node still verifies the 127 KB Plonky2 stamp. After a setup, the pool would run the Go prover and hand the
  196 bytes to the node; nothing in the verifier changes. The setup is single-party (a ceremony is still open), the verifier has had
  no second implementation or outside review, and it is not constant-time (all its inputs are public).

## Round 20: a Groth16 stamp of a current block (Justus L. Ludovic)
- New Groth16 setup for the current circuit (peg leaf, version 6 export): 4,203,150 constraints, 17 public (16 + the commitment hash),
  proving key 2,007 MB, verifying key 1,008 bytes. Setup 1,164 s, peak 6.0 GB (needs about 12 GB swap on this 8 GB VM; the first try was
  killed for memory). Single party.
- A real block (7 merge proofs, 112 payments, fee total 10,054,960) was proved: BN254 layer 81.6 s, Groth16 prove 89.2 s, proof 196 bytes.
  Go verifies it in 2.0 ms; the Rust verifier in 4 to 7 ms (files in g16wrap/result_v6).
- Rust negatives: a changed proof byte, any one of the 16 public values changed (test covers all 16), alpha or K0 of the key changed
  all rejected; a changed G2 point of the key is refused at parsing; the version-2 key does not accept the current block.
  (A bit flipped in the key's unused G1 beta is not caught; the verifier does not use it, as in gnark.)
- Test `a_stamp_of_a_current_block_verifies_under_the_current_key`; 39 tests in all.
- Still open: the setup is single-party (public ceremony needed), no second verifier implementation, the node does not yet call the
  Go prover; the pool would hand the 196 bytes to the node. Logs: run_export_v6.txt, g16wrap/blockC.*.log.

## Round 21: the pool makes Groth16 stamps, nodes check them with the Rust verifier (Justus L. Ludovic)
- `prover::Groth16Maker` (a `StampMaker`): the Plonky2 shrink proof (as before) -> `BnLayer` (the BN254-Poseidon layer, built in Rust,
  deterministic, its digest is part of the Groth16 circuit) -> the Go prover `zenwrap prove` run as a subprocess (one at a time, about
  6 GB) -> 196 bytes. Before it returns, the maker checks that the prover's public witness carries exactly this block's 16 public values.
- `zenproof node serve` with `ZEN_G16=<setup dir with zen.pk, zen.r1cs, zen.vk>` (and `ZEN_WRAP=<zenwrap>`): the pool stamps with Groth16
  and the node verifies with `Groth16Stamp` from `zen.vk` alone. A node never needs Go or the proving key.
- Bug found by the test: Plonky2 can hold a field element as value + p and writes it so; a fee total of 3,000,001 reached the Go
  tool as p + 3,000,001, which is a different number in the Groth16 field, so the node's check failed. The BN254 layer's public values
  are now written reduced. (Block-level public values are always canonical numbers on the node side.)
- Test `a_block_with_a_groth16_stamp_is_accepted_by_a_node_with_only_the_verifying_key` (runs only with ZEN_G16 and ZEN_WRAP set): a
  wallet's payment goes into a block, stamp of 196 bytes, accepted by a node holding only the verifying key (1.4 s with replay);
  a changed stamp byte, changed public values and the devnet's fake stamp are all refused. Whole path on this 2 vCPU machine:
  195 s per block (Plonky2 merge and shrink, 82 s BN254 layer, Go prover including loading the 2 GB key). Log: run_g16_node.txt.
- Not solved: 195 s per block is slower than the 150 s Bronze block time and on a CPU only; GPU proving and a long-running prover
  that keeps the key loaded (instead of one process per block) are the next speed items. Single-party setup still.

## Round 22: a long-running Go prover (Justus L. Ludovic)
- `zenwrap serve <setup dir>`: reads zen.r1cs and zen.pk once, then answers one directory per stdin line (replies start with ZENREPLY;
  the Go libraries' own log lines are ignored). `Groth16Maker` keeps this process alive (restarts it on any error); `ZEN_G16_ONESHOT=1`
  goes back to one process per block.
- Measured (2 vCPU, CPU only): first block 196 s, second block 171 s. Loading the key was only about 25 s of the 196; the rest is
  proving (Plonky2 merge and shrink, 82 s BN254 layer, about 90 s Groth16). So the persistent process helps a little; the time
  does not get below about 170 s on this machine. The real gains are on faster hardware (GPU for the BN254 layer and the Groth16
  MSMs, more cores), which cannot be tested here. Log: run_g16_node_persistent.txt.
- Memory: the Go process keeps the proving key resident (about 3 GB, peak 6 GB while proving) next to the node's circuits; this machine needs swap.

## Round 23: node hardening (Justus L. Ludovic)
- Validation outside the lock: `Node::lookup` (lock) -> `Node::prepare` (no lock: clone the parent's snapshot, validate, commit) -> `Node::store`
  (lock: log, fork choice, prune). Snapshots are `Arc<Chain>`. `Net::add_block` runs the three steps; the node answered in microseconds
  while a 500 ms verifier worked.
- Snapshot pruning: snapshots deeper than `MAX_REORG` = 288 below the best tip are dropped (and dead branches' bodies); a block on a pruned
  parent is `Added::Stale` (not an error). Heights of all blocks and the best chain by height are kept (`locator`, `next_after`).
- Forward sync: `GetNext(locator)` answers with the block after the newest locator hash on the peer's best chain; the requester repeats while the
  peer is higher. A chain longer than the orphan buffer (64) could not be synced backward from its tip; test with a 3-orphan buffer and 12 blocks.
- Peers: ban scoring (undecodable frame, invalid block, message before hello = ban 10 min; flood, second hello, bad address, malformed payment add
  points; points cool by 5 per 10 s), limits (32 inbound, 8 outbound, 4 per address, 15 s to hello, 20 min idle), bounded send queues with a write
  timeout, frames limited to the largest block, hello carries the listen port, GETADDR/ADDR discovery and `Net::maintain` (outbound up to 8).
- Stratum: at most 256 miners, request lines up to 16 KiB, idle timeout 10 minutes, banned addresses refused.
- Mempool: confirmed payments are remembered for 288 blocks (max 20,000) and go back into the pool if a reorg takes their block away.
- `node serve` takes any number of peer addresses and keeps looking for more.
- Tests added (8): validation outside the lock, pruning and stale forks, forward sync, bans (four kinds), limits and timeouts, discovery, Stratum
  line limit, payments back after a reorg. 48 tests pass (run_tests_round23.txt).
- Not done: bodies still all in memory, no persistent state tree, no defense against many-address attackers, limits not tuned on a real network.
  The wire format changed (hello has a port; new message types 9 to 11).

## Round 24: the metallic reward curve in the node (Justus L. Ludovic)
- `src/reward.rs`: Reward(N) = 2520 g x N^(-a) x r^Z in picograms, integers only (fixed-point log2 and exp2, Q32.32 and Q2.62, u128 products).
  Z is read from a 65,536-entry table of the inverse normal distribution (`src/phi_inv_q32.bin`, SHA-256 in `phi_inv_q32.sha256` checked by a test);
  the index is the first 16 bits of SHA-256(seal hash of block N+1 || "reward"). Constants for Yen, Ken and Jen and the exp2 table are in
  `src/reward_tables.rs`. Both are generated by `tools/gen_reward_tables.py` (mpmath, 50 digits). Chain 1 is Yen, 2 Ken, 3 Jen.
- Split (5.4.1): the miner keeps Raw x V when V <= 1, else Raw x V^(1/r); the minters share the rest equally per strike; the remainder goes to the miner.
- In the node: the reward of block N is worked out when block N+1 is committed (`Chain.last` remembers the miner and minters of the previous block),
  put in `pending[N+2]`, and paid by block N+2 as before. `Params.raw_reward` and `minter_pct` are gone. The supply audit holds after every block.
- Checks: Jen equals the Jen-0 Go implementation to the picogram on 400 (height, Z) pairs (`src/reward_reference_jen.txt`, made by /home/claude/jen11/reward.go);
  one year of raw rewards 7,197 / 129,031 / 1,025,830 g against the spec's 7,198 / 129,000 / 1,026,000; table increasing, antisymmetric, mean 0, variance 1;
  average V 1.12 / 1.47 / 2.04, geometric mean 1; miner keeps about 89% / 65% / 45%; payouts add up exactly (3 chains x 300 seals x 4 minter counts);
  a node test that the reward of block N equals the payouts from block N+1's seal, appears in block N+2, and different next blocks draw different factors.
  9 new tests, 57 pass (run_tests_round24.txt).
- Finding: with V's average of 2.04, Jen's supply in picograms reaches about 1.45e19 after 100 years against 1.84e19 for u64 and for the Goldilocks
  field: a margin of 1.27. The unit, or the width of balances and of the supply audit, needs a decision before launch.
- Open: no random factor for Yen's first blocks (spec decision 2), the maturity period (round 27 added it), the total supply width above.

## Round 25: the base unit is the nanogram (Justus L. Ludovic)
- The supply-width question of round 24, settled: balances, fees and payouts are counted in nanograms (10^-9 g) on all three chains; the curve is
  still worked out to the picogram (so it matches the Jen-0 reference) and `reward::payouts` truncates to nanograms. `UNITS_PER_GRAM` = 10^9,
  `PICO_PER_UNIT` = 1000.
- Why: every balance must stay below 2^62 base units (block replay and circuit range checks) and the supply audit sums in 64 bits. In picograms Jen's
  supply passes 2^62 within ten years (1.2 x 2^62; with V's average 2.04) and 2^64 in about 130 years; in nanograms it is 0.0012 of 2^62 after ten
  years and 0.022 after ten thousand (Ken 1.45 million g, Yen 8,124 g). Costs: Yen's late rewards round more coarsely (940 ng at year 100, 34 ng at
  year 1,000: 0.1% and 3%, a few milligrams a century in total), and the smallest payment (1/6 Sen = 3.3 x 10^8 units) keeps room for a 0.01% fee.
- Test `nanograms_keep_every_balance_in_range_for_ten_thousand_years` (ten years summed block by block, then the N^(1-a) growth; also asserts that
  picograms would be past 2^62 within ten years). 58 tests pass (run_tests_round25.txt). The launch-order row ("previous chain's raw reward below 1 coin")
  is in coins, not base units, and does not change.

## Round 26: Yen pays its first 100 blocks without a random factor (Justus L. Ludovic)
- Decided: on Yen, blocks 1..100 use V = 1 (no draw). The miner takes the whole curve reward and the minters have no windfall to share in those blocks;
  from block 101 on, Yen draws like the others. Ken and Jen are fully random from block 1. In code: `Metal.fixed_v_blocks` (Yen 100, others 0), used by `reward::payouts`.
- Why (simulation, 2,000 runs): Yen's raw total is 7,255 g and its first 100 blocks pay 6,504 g (89.6%). With the factor on from block 1 the total supply has a
  median of about 7,900 g (5-95%: 6,100 to 10,900) and block 1 pays anything from about 1,100 to 5,000 g; with V = 1 for the first 100 blocks the total is 7,347 +- 13 g
  and block 1 pays exactly 2,520 g.
- Test `yens_first_hundred_blocks_have_no_random_factor`: for blocks 1, 2, 50, 99, 100 the seal changes nothing, the reward equals the curve, the miner has all of it, the minters 0;
  block 101 on Yen, block 1 and 100 on Jen and block 1 on Ken still vary with the seal. Supply and split tests now include Yen at blocks 101 and 5,000.

## Round 27: reward maturity (Justus L. Ludovic)
- A reward is now released `maturity` blocks later than before: block N's reward, drawn from block N+1's seal, is credited in block N + 2 + maturity
  (`MATURITY_BLOCKS` = 100 on the real chains, 0 on the devnet used by the tests; `ZEN_MATURITY` overrides it in `serve`). 100 is below `MAX_REORG` (288),
  so a reward is released inside the window in which the node still accepts a reorg only if that reorg is shallower than 100; coins nobody can have spent
  are the only ones a reorg can take back.
- No new state: the held rewards sit in `pending`, keyed by the block that releases them, already persisted and counted by the supply audit.
- Test `a_reward_is_held_for_the_maturity_period_and_then_credited` (maturity 3: nothing is released before block 6, block 6 releases block 1's reward, the
  last four rewards are still held after block 9, audit exact every block). 60 tests pass (run_tests_round27.txt).
- Open: the 100 is a placeholder; a time-based wait (so that Yen's 100 blocks are not 25 hours and Jen's 4) may suit better.

## Round 28: the block log on disk (Justus L. Ludovic)
- New `src/store.rs`. `blocks.log` is now `ZENLOG01` + records `len | crc32 | block`, one write and one `sync_data` per block. Opening scans every record once:
  a torn tail (crash during an append: cut anywhere in the header or body, or a last record whose checksum fails) is cut off and reported (`Node::repaired`,
  printed by `serve`); damage with more data after it is an error, never skipped. A file that is not a Zen log (or is the old format) is refused.
- `<dir>/LOCK` (a file lock) keeps a second node from opening the same directory; a node's `Store` is opened with the lock, the demo/test `Chain::open` without.
- Blocks leave memory: with a log, the node keeps only the blocks of the last `max_reorg` heights in RAM and finds the rest by offset in the log
  (an index of 8 + 4 bytes per block); `Node::block` and `next_after` read them back, so a syncing peer can still be served the whole chain.
  Without a log nothing changes (the tests that count blocks in memory).
- Restart replays every record through full validation (the stamp check included) on the way in, as before, but streams the file instead of reading it whole.
- Tests: store (CRC check value, records survive a reopen, the torn tail cut at every possible length and the append after the repair, damage in the middle,
  the lock), and a node test (old blocks leave memory and are served from disk by hash and by locator, restart gives the same tip and state root, a second node is refused,
  a half-written block 10 is cut and can be added again). 66 tests pass (run_tests_round28.txt).
- Open: a restart re-validates the whole chain, which is safe but takes time proportional to its length (a state snapshot with the tree root checked against the
  last block would fix it); the state and the tree are still wholly in memory; no compaction or pruning of old blocks on disk (a pruned node would not serve history).

## Round 29: state snapshots (Justus L. Ludovic)
- A node with a directory now saves `snapshot-<height>.zen` every `SNAPSHOT_EVERY` (1000) blocks: the whole chain state at the block `max_reorg` (288) below the tip,
  the deepest state no reorg can still reach. Written to a `.tmp`, fsynced, renamed, the directory fsynced; the newest two are kept. A failed write only prints a note.
- Contents: balances and the other leaf numbers of every account (sorted by index), the fee pool, the rewards still held, the difficulty and window state, chainwork,
  the last block's miner and minters, and all of what S is read from (`Reading::encode`); ends with a SHA-256 of the file. The tree is rebuilt from the accounts.
- Restart: the newest snapshot is read and checked (file digest, same parameters and genesis allocation, every number in range, supply audit exact); then the log is
  scanned once: records up to the snapshot's block are only decoded and indexed, and when the snapshot's block turns up its height and state root must equal the ones
  in the block's public values. Everything after it is validated as before, so the 288 blocks of the reorg window are rebuilt in full. Anything wrong with a snapshot
  (damaged, foreign, wrong name, not in the log, at odds with its block) is reported and the next older one is tried, then the whole log. `ZEN_REVALIDATE=1` ignores snapshots.
- Tests: a chain restored from a snapshot has the same bytes, then goes on for 5 more blocks (rewards, retarget, S) identical to the original; 40 flipped bytes, a cut,
  another genesis and other parameters are all refused. A node test (window 3, snapshot every 2): files kept, restart from 8 with nothing older rebuilt, old blocks and the locator
  still served, a restart after more blocks, a damaged newest snapshot (older used), a wrong-named one (passed over), none (whole log, same tip and root). 68 tests (run_tests_round29.txt).
- Open: the snapshot is trusted like the log (both are on the node's own disk; a snapshot checks against the block's state root, which covers the accounts but not
  the pool, the held rewards or S, those are covered by the supply audit and the file digest); writing it is done under the node's lock; the accounts are held in memory and
  the tree is rebuilt from them (32 hashes per account) on every start.

## Round 30: prover speed (Justus L. Ludovic)
- Where the time goes (2 vCPU, one block, key loaded): leaves, merges and shrink 11 s (a one-leaf block; an 8-leaf block of 112 payments about 83 s: 41 + 22 + 19 + 1.4), BN254 layer 82 s, Groth16 about 80 to 90 s.
  The BN254 layer is a 2^12-row circuit, but its Merkle trees are hashed with Poseidon over BN254 (254-bit field): about 6 million permutations per proof, at 23.7 us each
  on this machine. That is the whole cost (6.2 million x 23.7 us / 2 threads = 73 s, the rest FFTs).
- Done: (1) ark-ff's assembly multiplication (`asm` feature + `.cargo/config.toml` with `+bmi2,+adx`; any x86-64 since Broadwell / Zen 1; on an older CPU the program would stop with an illegal instruction); (2) `permute_fast`: squarings, and every dot product reduced once (`Fr::sum_of_products`); the old `permute_ref` stays and a test checks
  they give the same states. 23.7 us -> 16.7 us per permutation. Same hashes, so the existing Groth16 setup and keys stay valid (checked: the node test with the old keys passes).
- Measured with the real Groth16 node test (run_g16_node_round30.txt): BN254 layer 52 s (was 82 s); second block, key loaded: leaves/merges/shrink 11.0 s + BN254 52-53 s +
  Groth16 79 s = 144 s (was 171 s). The first block took 285 s because the 2 GB key was read while the machine was swapping (8 GB RAM, Go prover ~6 GB).
- Done: leaf and merge proofs run several at a time (`ProverMaker.par`, `ZEN_PAR_PROOFS`, default a quarter of the cores: 1 on this machine, 8 on 32 cores). Witnesses are still made in
  order (the signatures draw from one random stream), only the proofs run side by side; a level of the merge tree is independent merges. On 2 cores nothing changes
  (25.4 s vs 24.9 s for a 3-leaf block); on a many-core server the 8 + 8 leaf proofs and the merges stop being a serial chain of small proofs that cannot use the cores.
  Plonky2's proof-of-work nonce is found on several threads, so the stamp bytes differ from run to run; the test checks that both stamps verify for the same block.
- `ZEN_TIMING=1` prints the three stage times of every Groth16 stamp.
- Tried, no gain: a different shrink configuration (rate 3..10, 28..8 queries, equal 100-bit security) does not make the BN254 layer smaller: it needs 2,417 gates (rate 6) or
  2,005 (rate 8) before padding plus the circuit's own extras, and 2^11 rows would need under 2,048 in all. Rate 8 would cost 26 s in the shrink to save about 25 s in the layer.
  A lower rate for the BN254 layer itself (4 or 5 instead of 6) cuts its LDE by 2 to 4 times but needs 17 to 21 queries instead of 14, which makes the Groth16 circuit larger
  (4.2 million constraints now); that needs a new setup per try and is not done. Experiments: `cargo test wrap_speed_experiments --ignored` (ZEN_FIN_DUMP, ZEN_WRAPS, ZEN_BNS, ZEN_PROVE_BN).
- Not done / cannot be measured here: GPU for Groth16 (BUILDER-GPU.md has the build; no NVIDIA machine here), the BN254 layer on 16+ cores (it scales with cores: the trees are hashed with rayon),
  a vectorised (AVX-512) Poseidon over BN254 (maybe another 2 to 3 times), pipelining the next block's leaves while this block's Groth16 runs.

## Round 31: the node's local HTTP API, and a bug it found (Justus L. Ludovic)
- New `src/api.rs`, started by `zenproof node serve` (address `ZEN_API`, default `127.0.0.1:18445`, `ZEN_API=off` to turn it off). JSON over plain HTTP/1.1, no new dependency.
  `GET /api/status`, `/api/blocks?limit=&before=`, `/api/block/<height|hash>`, `/api/account/<zen1...>`, `/api/mempool?limit=`, `/api/peers`;
  `POST /api/pay {"tx":"<hex of the signed payment>"}`. Amounts are base units (nanograms) with `*_g` fields in grams to nine decimals (exact).
  The coins are Sen, Ten and Ren; the API shows grams and S (`sen_units`) and leaves coin conversion to the client.
- Safety: binds to a loopback address only (anything else is refused at start); answers only requests whose Host header is localhost, 127.0.0.1 or [::1] on its own port
  (a web page cannot reach it through DNS rebinding); sends no CORS headers (another site cannot read answers in a browser); a payment needs `Authorization: Bearer <token>`
  (random 32 bytes, kept in `<ZEN_DIR>/api.token` with mode 0600, or printed at start when there is no directory); at most 32 connections, 5 s I/O timeouts, 16 KiB head, 4 KiB body,
  no chunked bodies, only GET and POST. It reads public chain data and can only submit a signed payment; it touches no key and no block.
- Tests (4): status, paged blocks, a block by height and by hash (equal), accounts (found, not found, bad checksum), payments refused without or with a wrong token, with a malformed
  body, with a forged signature, then accepted (and "known" the second time), visible in the mempool and in the sender's next nonce; refused: foreign Host, wrong port, no Host,
  DELETE/OPTIONS, unknown paths, bad parameters, junk, chunked, huge head (431) and body (413), no CORS headers, an idle client does not block others, non-loopback bind refused;
  the token file is kept between runs; grams are exact.
- Live check: `node serve` + `node mine 3` over Stratum, then `curl` of the API: height 3, three blocks listed, supply with 5,372 g issued and held.
- Bug found by running the CLI node: a block with no payments and nothing owed had no leaf and was refused ("bad shape"), so `node mine` produced nothing and, with the 100-block
  maturity of round 27, a real chain could not have started (nothing is credited until the first reward matures). The builder now gives such a block one empty leaf.
  Tests `blocks_with_nothing_in_them_are_blocks` (DevStamp) and `an_empty_block_gets_a_real_stamp` (real Plonky2 proof, 100+ KB stamp, accepted by the node).
  Stratum connection errors are now printed (`stratum connection ended: ...`), which is how this was found.

## Round 32 — the explorer page (Justus L. Ludovic)

The node now serves a small web page at its API address (default http://127.0.0.1:18445/): chain height, payout so far, the reward curve, latest blocks, payments waiting, peers, and block and account pages with search. It is built into the binary (`src/ui/`), loopback-only, under a strict content-security policy, and builds its DOM without innerHTML. Checked in a real browser at 1280 and 390 px, light and dark; two bugs found and fixed (null/array children printed as text; phone table clipped). Tests: `api::the_explorer_page_is_served_and_is_safe`.

## Round 33 — testnet preparation: network file, chain choice, network id (Justus L. Ludovic)

- `src/netconf.rs`: a plain-text network file (`chain yen|ken|jen`, genesis time, S, seal bits, window, block time, maturity, standard fee, `seed host:port`, `alloc <zen1…> <base units>`). Each chain has its own defaults (block time 900/300/150 s, standard fee 1/4/10 per thousand, maturity 100). Bad files are refused with the line and the reason.
- `zenproof net init <yen|ken|jen> <dir>` writes `net.conf` (no secrets) and key files for the pool's minters and some test wallets; `net show` prints the file and the network id.
- `ZEN_NET=<net.conf> zenproof node serve …` runs one chain on that file; minters come from `ZEN_MINTERS` (default `minters/` beside the file; no keys = relay-only node, no Stratum); `ZEN_PAYOUT` sets the pool's payout address; seeds in the file are connected at start. Without `ZEN_NET` it is still the devnet, and says so.
- The peer handshake now carries a network id (chain, every parameter, genesis allocation); a node whose file differs in anything that changes validity is refused at HELLO instead of failing later on blocks.
- On a configured network block times come from the wall clock (at least the previous time + 1 s), so the seal difficulty actually follows the real block rate.
- Live check: Yen network, a pool node and a relay-only node with the same file, 4 blocks mined over Stratum, both at height 4, block times current. 5 new tests.

## Round 34 — the three-chain test network, stage 1 (Justus L. Ludovic)

Goal: a test network with Yen, Ken and Jen together, to test the exchange rate, channels, factories and routing (SPEC 7 and 8). Decisions: rules first (stand-in stamps, circuits and the Groth16 setup once the rules settle); claims may read the other chain's headers, everything else in block validity stays independent.
- `zenproof net init all <dir>` writes `<dir>/{yen,ken,jen}/net.conf` with the same minter and wallet keys on all three chains. `zenproof node serve-all <dir> [base port]` runs the three chains in one process: p2p base+0..2, Stratum base+10..12, API base+20..22, each with its own log, pool and explorer page.
- `src/crosschain.rs` (SPEC 8.4): each chain keeps the headers of the other two and checks them as a light client does: seal at the difficulty the header chain dictates, commitment, height, chaining of state roots, and the stamp. It follows reorgs (steps back to the fork, takes the new headers). `/api/chains` and a strip on the explorer page show what each node has checked of the others. Test: honest chain followed header by header and through a reorg; changed public value, stamp, state root, out-of-order block and another chain's block refused.
- Live: three chains mined to heights 3, 2 and 4; each node's page shows the other two as checked, at the same heights.
- Not yet: the follower reads blocks from the other chain's node in the same process; a version that follows over the network is needed before the chains run on separate machines.

Next stages (from the spec):
2. One on-chain primitive for locked funds (lock, claim with a condition, refund after a timeout). Orders (8.2: make, reserve, pay, claim, expire), channel funding and point locks (PTLC) are all built on it. Claims check the other chain's headers.
3. Two-party channels and one-way streams; wallet side (off-chain state, signatures, close and dispute).
4. Routing across chains (7.3) with point locks, stream nodes with an exchange spread (7.4).
5. Channel factories (7.2): many channels under one output.
6. Official exchange rates (8.5) from filled trades; batch auctions (8.3) later.

## Round 35 — locked funds and exchange orders, stage 2a: the rules (Justus L. Ludovic)

- `src/locks.rs`: one on-chain primitive, a lock, in two kinds. A vault (key, owner, timeout) pays out against a signature or refunds after the timeout. An order (maker, amount sold, wanted chain and amount, a fresh pay-to address, expiry, reservation length, deposit) goes through make, reserve (the taker puts down a deposit of at least 1%), claim with a proof of payment on the other chain, reopen (the reservation ran out, the maker gets the deposit), and return (expired and unreserved, the maker gets the funds back).
- A lock is an ordinary leaf of the state tree whose address is the digest of its terms; reserving or reopening changes the terms and so the address. Payments into or out of a lock are refused; only these operations move its funds. Operations are applied after the block's payments, inside the same replay, so every node reaches the same state.
- A claim carries the other chain's block (header, coinbase, body, stamp, data) and the receiver's leaf. The claiming node checks it against the other chain's headers (seal, stamp, height, time) and needs 2, 6 or 12 blocks on top (Yen, Ken, Jen). This is the only place one chain reads another; if the header is not yet known, the block is held back, not rejected, and the sending peer is not punished.
- Snapshots are now `ZENSNAP2` and carry the lock terms; each is checked against its leaf on load. Restart with locks tested.
- Stamps for real proofs (Plonky2, Groth16) cannot yet cover operations; those makers build payment-only blocks. Circuits and a new Groth16 setup come at the end.
- 8 tests in `locks::tests`: encode/decode, vault claim and refund, odd terms refused, the full order path across two chains, short/early/wrong-address/tampered proofs refused, a receiver that already existed, a reservation that runs out, snapshot and restart.

## Round 36 — locked funds and exchange orders, stage 2b: wallet, pool, API, live trade (Justus L. Ludovic)

- `SignedOp`: an operation signed by its sender over (chain, nonce, request), so a key used on three chains cannot be replayed from one to another. `OpPool` holds them (nonce order per sender, at most 4 waiting, balance and fee checked); the pool builder takes them into the next block, keeping only those that leave the block valid.
- P2P message 12 carries an operation (answered like a payment) and relays it; the API has `GET /api/orders`, `/api/order/<lock>`, `/api/find_payment?to=&min=&after=` (finds a payment on the chain and returns its proof) and `POST /api/op` (token).
- Wallet: `wallet orders`, `order-make`, `order-reserve`, `order-claim`, `order-reopen`, `order-return`. A node is given as `<p2p>,<api>`. `order-claim` asks the other chain's API for the proof itself.
- `serve-all` gives each chain a view of the other two chains' headers, so claims verify across chains.
- Live on the three-chain test network: w0 sold 0.1 g on Yen for 0.3 g on Ken; w1 reserved it, paid on Ken, waited 6 blocks, claimed on Yen. Final balances matched to the base unit (fees and the returned deposit included).
- Known limits: payments and operations of one account share the nonce, so send one at a time and wait for the block; a lock cannot be used in the block that creates it; a payment whose receiver was created and closed in the same block cannot be proven; the cross-chain follower still reads the other node in the same process.

## Round 37 — channels and one-way streams, stage 3 (Justus L. Ludovic)

- On chain (`locks.rs`): a third lock kind, `Terms::Channel` (the funder a, the peer b, both keys, a dispute window in blocks, `oneway`). The funder's coins are the lock's balance. Four new operations: `ChanStart` (a or b starts closing a channel that was never updated), `ChanUpdate` (anyone posts a state signed by both sides; it must be newer than the one waiting, and restarts the window), `ChanSettle` (after the window, each side is paid its share) and `ChanClose` (both sign the final balances: paid at once). This is the eltoo rule of the spec: only the newest state counts, so there is nothing to punish and no revocation secrets; the only duty is to post the newest state inside the window if the other side posts an older one.
- Signatures name the chain and a stable channel id (not the lock's address, which changes with its state), so a state cannot be reused on another chain or channel.
- A stream (`oneway`) is one number: the amount paid so far, signed by the payer alone. A larger amount replaces a smaller one, so the payer cannot cheat by signing "newer" states: a newer state only ever gives the receiver more.
- Wallet side (`src/channel.rs`, `zenproof chan ...`): a channel file with the latest doubly signed state; `pay` / `accept` / `commit` pass a payment in three messages (any carrier: file, chat, socket); `close-sign` + `close` for an immediate close; `dispute` (post the latest state) and `settle` for a unilateral close; `open` / `join` against the new `GET /api/channels`; `wallet pubkey`.
- Live on the three-chain network: a two-party channel on Ken (4 payments both ways, then a cooperative close paid 380 000 000 / 120 000 000); a second channel where b posted an old state, a answered with the newest inside the window, and the chain paid the newest (180 000 000 / 20 000 000); a stream on Jen (5 payments of 10 000 000 signed by one side, the receiver closed with the latest, +50 000 000).
- 5 new tests: newest state wins and the window; cooperative close and a close started from nothing; a stream; wallet-side payments both ways, refusals; stream monotonicity.
- Not yet: a network protocol for the off-chain messages (today they are passed by hand), watchtowers (a node that posts your newest state while you are away), dual-funded channels, routing over several channels (stage 4), factories (stage 5). Real-proof stamps cannot yet carry channel operations either.

## Round 38 — routing across channels and chains, stage 4 (Justus L. Ludovic)

- Point locks inside channel states (`locks.rs`): a state is now (update number, a's share, a list of up to 8 point locks). A point lock holds an amount for the other side that is theirs on showing the scalar t with t*G = the lock's point, and goes back to its sender after its expiry. Both signatures cover the lock list. On chain, `ChanUpdate` carries the list, `ChanSettle` carries one witness per lock; a lock that is neither opened nor expired holds the settlement back. Tests: shares plus locks cannot exceed the capacity, signatures do not carry over to another list, opened locks pay the receiver, expired ones refund the sender.
- Channel files (`channel.rs`) now do the four moves of a routed payment: add a lock, open it with its scalar, give it back, and plain payments, each as one signed update the other side checks (it must be exactly that move and nothing else). A node keeps the scalars it learns, so it can settle on chain if its neighbour vanishes.
- The routing node (`src/route.rs`, `zenproof rnode run|add-channel|invoice|pay|status`): a small daemon that holds channel files and talks to its neighbours over TCP.
  - Invoice: the receiver makes a secret r and gives out the point r*G.
  - Route: the sender asks the neighbours for their channels (crawl), tries every path up to 5 hops, computes the amount each hop must lock from the receiver backwards (each node's published prices, fee and spread), checks every sender can afford its lock, and takes the cheapest.
  - Points: the sender gives every hop its own point, P_i = P_(i+1) + d_i*G, so the locks along the route cannot be matched by their points. The receiver's secret opens the last lock; each node adds its offset to open the one before; the sender gets the receipt r from the scalar that opens its own lock.
  - Onion: one encrypted layer per hop, each under a key from a fresh ephemeral key and the hop's node key. A hop learns only the next channel, the amount, the time its outgoing lock runs to and its offset.
  - Stream nodes: a node with channels on two chains asks for the other metal at its own price plus its routing fee and, between chains, its spread. Time-outs are converted between chains with each chain's block time, and an incoming lock must outlast the outgoing one by the node's margin.
  - Failure: a hop that cannot forward (no balance, no price, too little time, peer down) or a receiver that refuses (unknown or paid invoice, wrong amount) gives the lock back, and the refusal runs back to the sender.
- Live (`scripts/demo_routing.sh`): Alice -> S -> T -> Carol over Jen, Ken and Yen channels. Alice locked 20 280 987 Jen units; S paid 6 713 335 Ken units; T paid Carol 2 000 000 Yen units; the receipt matched the invoice. Paying the same invoice again was refused by Carol and every channel went back to its balances (two updates each). Paying while Carol's node was down was refused at T and unwound the same way. The Alice-S channel was then closed on chain from its routed state and paid exactly the off-chain balances.
- Changes you will notice: test wallets from `net init all` now hold 10 g (a Yen channel needs at least 1.6 g); the template of a pool is built when a job starts, so an operation sent just before a block may land one block later.
- Not yet: the exchange rate is each node's own price list (official rates and batch auctions are stage 6); no gossip (the graph is found by asking neighbours); layers are not padded to one size; a watchtower; no automatic on-chain close when a neighbour goes silent (done by hand with `chan dispute` / `chan settle`, which opens locks with the saved scalars); channel factories (stage 5).

## Round 39 — channel factories, stage 5 (Justus L. Ludovic)

One on-chain output now holds the channels of up to 8 members with a single coordinator (`Terms::Factory`). Each member's channel (coordinator, member) is updated by those two alone, with its own signature domain. Every member channel is an ordinary `Chan`, so the stage-3 payments and the stage-4 routing run over it unchanged.

- **Exit alone.** `FactoryStart` / `FactoryPost` (newest signed state wins during the window) and then `FactoryExit`; or `FactoryExitNow` with both signatures. The lock shrinks by that member's capacity and is removed when all members have left. The other members are not touched.
- **Funding.** The coordinator holds the whole capacity at first; a member adds its own coins with `FactoryFund` (`chan factory-fund`) while its channel has no posted state.
- **API / CLI.** `/api/channels` lists one entry per member (fid, idx, state). CLI: `chan factory-open`, `factory-fund`, and the existing adopt/join/pay/dispute/settle/close choose Factory ops by `fid`.
- **Live result** (`scripts/demo_factory.sh`): three members on one Ken output; Alice → coordinator → Carol routed through two sub-channels of the same factory with nothing on chain; Carol leaves alone (post, window, settle) and receives exactly her 50 000 000; Alice keeps paying afterwards.
- **Limits.** Members cannot be added to a live factory; a single coordinator is a point of trust for liveness (any member can always exit); watchtowers are still open.

## Round 40 — official rates and batch auctions, stage 6 (Justus L. Ludovic)

**Official rates (`market.rs`).** Nobody announces a rate. Each chain keeps a tape of its filled orders (an order held by a taker that is spent by its claim). The official rate for selling this chain's metal for another's is the *volume-weighted median* price of the newest 32 fills (not older than 20 000 blocks), and it exists only when the fills come from at least 2 different makers and 2 different takers and there are at least 3 of them. A tiny fill at a wild price does not move a volume median; one account trading with itself makes no rate. `GET /api/rate`, `GET /api/fills`; `zenproof market rates <api1> <api2> <api3>` merges both directions of each pair (geometric mean) and shows the gap between them. The tape is a view over the blocks (not consensus state): every node that replays them gets the same tape, but a node that starts from a snapshot only sees fills after it.

**Batch auctions (rules in `locks.rs`).** An order may be made open to an auction (`OrderState::Auction{window}`). Bids (`Op::Bid`, `wallet order-bid`) escrow coins in the lock; the first bid (at least the order's deposit) opens a window of `window` blocks, a higher bid replaces the waiting one inside the window and the earlier bidder is paid back in the same operation (so nobody's coins are stuck), and when the window closes the highest bid is the taker, with the order's usual reservation time to pay on the other chain and claim. If the winner does not, the escrow goes to the maker and the order is open to a new auction. So the winner is decided by commitment, not by being first in a block (no race to be early, no gain for a miner who orders the block). Orders keep their own price; the auction decides who gets them.

**Live result** (`scripts/demo_market.sh`): three trades between two makers and two takers on Ken against Yen give the rate 0.52 Yen per Ken (after one trade there is none); in an auction a bid of 2 100 000 is outbid by 3 500 000 and the first bidder's escrow comes back at once.

**Limits.** Wash trading with several accounts is possible (it costs the fees of every trade, and deposits are at risk); the rate is a view per chain, other chains cannot read it in a claim yet; no partial fills; a bid escrow is not interest-bearing. Next: watchtowers, dual-funded channels, the network protocol for off-chain messages.

## Round 41 — watchtowers, stage 7 (Justus L. Ludovic)

A channel's safety rests on answering an old-state close inside the dispute window; an owner who is offline loses that race. `zenproof chan watch <dir> <tower wallet> <node> [once]` is a watchtower: a client drops the newest copy of its channel file into the directory after each update; when the channel starts closing at an older update the tower posts the newest state it holds (`ChanUpdate`, or `FactoryPost` for a factory member) inside the window, and after the window it settles (with the point-lock secrets in the file). The tower needs only a wallet with a few coins for fees: the states carry both parties' signatures and the payouts go to the addresses in the channel's terms, so a tower can neither take nor redirect anything, and it is not paid yet. Live (`scripts/demo_tower.sh`): Alice posts update 1 (400 000 000 for her) while Bob is offline; the tower posts update 2 and settles; Bob ends at exactly 10 250 000 000. Limits: the tower sees channel files in the clear (a hint-and-encrypted-blob scheme is the next step for privacy), it is trusted for liveness only, and it has no payment. No consensus rule changed, so the stage 6 full test run (106 passed) still stands; the channel unit tests were re-run.

## Round 42 — dual-funded channels, stage 8 (Justus L. Ludovic)

Until now a channel was funded by side a alone; b could only receive first. Now b can add its own coins: `Op::ChanFund` (`chan fund <wallet> <node> <a's address> <amount>`) is allowed to b only, on a two-way channel that has no posted state yet (more than once if b likes). The lock then holds both contributions and its state is `ChanState::OpenDual{base_a}`: a's start share is what a put in, the rest is b's, so a close with no update gives each side back exactly its own coins (unit test `b_can_add_its_own_coins_to_a_channel_before_any_update`). Signatures name the channel by its stable id, so nothing in the update, dispute, settle, point-lock or routing code changed; the API lists the new capacity and a's base share and `chan adopt` / `chan join` pick them up. Streams (one-way) stay funded by a alone. Live (`scripts/demo_dual.sh`): a puts in 300 000 000, b adds 200 000 000; b pays a 150 000 000 from its own side, a pays b 50 000 000, a closes with the newest state and each side ends 100 000 000 apart (a up, b down) less fees. Limits: b funds in a second step after a's (not one atomic operation; a can start a close on an unfunded channel in between, which just returns a's coins); no splicing yet (adding coins to a channel that has history).

## Round 43 — the network protocol for off-chain messages, stage 9 (Justus L. Ludovic)

The routing daemon (`rnode`, JSON lines over TCP) already carried payment proposals and their acknowledgements. Three messages were still done by hand, and are now part of the protocol:
- **`sync`**: a node asks the peer for a newer agreed state. The reply carries the peer's newest state with both signatures; `Chan::adopt_state` checks both signatures, that it fits the channel and that it is newer, drops a proposal that was waiting and takes it. This heals a crash, a lost acknowledgement or a long absence (without it, a node one update behind could never propose again). Every daemon syncs all its channels a few seconds after start and every 20 s; `rnode sync <dir>` does it on demand.
- **`closesign`** and `rnode close <dir> <channel id>`: a joint close negotiated over the wire. The closer syncs, sends its close signature for the newest state; the peer checks the state, that no update is waiting and that no point lock is held, and answers with its own signature; the closer checks it and sends `ChanClose` (or `FactoryExitNow` for a factory member) to its chain: no dispute window.
- **`tower_dir <folder>`** in `node.conf`: after every change of a channel file the node writes a copy into the folder, which a watchtower (`chan watch`) reads, so the tower is fed without a manual step.
Live (`scripts/demo_network.sh`): Alice pays Bob 100 000 000 over the wire; Bob's node fills the tower folder by itself (update 2); Alice's file is put back to update 0 (a crash that lost state) and `rnode sync` brings it to update 2; a joint close over the network pays Bob exactly his 100 000 000 more. Unit test `a_side_that_missed_the_acknowledgement_catches_up_...`. Limits: the wire is plain TCP (no encryption or peer authentication beyond the signatures on every state, so a listener can read amounts; Noise-style transport is next); no gossip and no automatic on-chain close when a peer stays silent; one proposal at a time per channel.

## Round 44 — an encrypted, authenticated transport, stage 10 (Justus L. Ludovic)

Before, node-to-node messages were plain JSON on TCP: a listener read amounts and anyone could talk to a node's channel port. Now (`transport.rs`) every request and answer between nodes is sealed, in one round trip, with the node's own curve and hash:
- The caller knows the server's static key S (the other side of the channel; for a crawl, the far key of the channel the neighbour listed). It makes an ephemeral key E, seals the request under a key from ECDH(e, S) with a key stream and MAC, and signs (E, S, its own key C), so the server knows the request is from C and cannot be replayed under another E or to another server. A time stamp must be within 60 s.
- The server answers under a key from ECDH(e, S) and ECDH(e_s, E) with its own fresh ephemeral key, so answers stay secret even if a static key leaks later.
- In the daemon: `prop`, `sync` and `closesign` are accepted only when the authenticated caller is that channel's other side; `info` only from an authenticated caller; a plain request from anywhere but this machine is refused, and from this machine it is local control only (invoice, pay, close, status). Routing, the crawl, sync and joint close all go over the new wire; the three-chain routing demo and the network demo pass unchanged.
Unit test `a_request_and_its_answer_open_only_for_the_right_keys_and_only_once_fresh` (not in the clear; wrong server, flipped byte, old time stamp, borrowed identity and another server's wire are all refused). Limits: the request is sealed to the server's long-term key (no forward secrecy for requests); lengths and who-talks-to-whom are visible; no padding; the key stream and MAC are built from SHA-256 (fine for a testnet, replace with a reviewed AEAD before real money); one request per connection (no session reuse).

## Round 45 — a node that protects itself, stage 11 (Justus L. Ludovic)

The watchtower logic (post the newest state inside the window, settle when it is over) moved into one function, `channel::guard`, which the tower and now every routing node use. A node runs it for its own channels (every 2 s), and it also does what a tower cannot know to do: **a silent peer**. A point lock that has stayed open for `guard_wait` seconds (90 by default; a lock is normally open for seconds) and whose expiry is within the dispute window plus `guard_blocks` (6) of the chain's height makes the node start the close on chain with its newest state, so that the window ends before the lock does; the settle then comes by itself, and a lock nobody opened goes back to its sender at its expiry. Settle attempts retry until the chain accepts them (a lock must be opened or expired first). `guard_blocks 0` turns it off. Live (`scripts/demo_guard.sh`): Alice locks 200 000 000 for Bob behind a point nobody can open and Bob's node is gone; when the lock nears its expiry Alice's node closes the channel on chain, and after the window and the expiry settles, getting every coin back (only the 1% open fee is lost); Bob is untouched. `chan lock` (new) proposes a point lock by hand for tests and demos. Limits: the guard watches only open locks (a silent peer with no lock at risk is not closed on: nothing is lost); the trigger uses the chain's block count, so a chain that stops producing blocks stops the clock; fees for the close come from the node's own wallet; the full test suite does not run this live (it is covered by the demo).

## Round 46 — a container image, stage 12 (Justus L. Ludovic)

The node ships as one image (`Dockerfile`, `docker/entrypoint.sh`, `docker-compose.yml`, `k8s/zen.yaml`, `.github/workflows/docker.yml`, `DOCKER.md`): pull and run, on Windows and macOS through Docker Desktop, on Linux, on a Raspberry Pi, on a large server or a cluster, for `linux/amd64` and `linux/arm64`. Changes to the code for this: `ZEN_BIND` / `ZEN_API_BIND` / `ZEN_API_BIND_ANY` (listen on the container's address; the API refuses non-loopback addresses without it), `ZEN_API_HOSTS` (extra Host names for a gateway), and the x86-only CPU flags (`bmi2`, `adx`) in `.cargo/config.toml` now apply to x86-64 only, so the same source builds on ARM. The entrypoint makes the testnet files on first start, serves the three chains, mines by itself (stand-in stamps), stops cleanly and has a health check. Tested here: the binary and entrypoint in a real container with a published port and a volume: the API answers from the host, the health check passes, blocks come by themselves, and a restart on the same volume resumes at the same height without re-initialising. Not tested here: the `docker build` itself (this sandbox cannot reach the image registries), the arm64 image, and a real cluster (the manifests were only checked for syntax). Limits: one pod runs all three chains (the cross-chain follower is in-process; a network follower is needed to split them); routing nodes and towers are run with `docker exec` or as extra containers by hand; no TLS in front of the API (use a gateway).

## Round 47 — the cross-chain follower over the network, stage 13 (Justus L. Ludovic)

Until now the three chains had to run in one process: a claim on one chain read the other chains' headers from in-memory nodes. Now a chain can run alone (`zenproof node serve-chain <net dir> <yen|ken|jen> [base port]`, or the image's `chain <name>` mode) and follow the other two **over the network**:
- **Light client over p2p** (`p2p::Probe`, `HeaderChain::follow`): connect to a full node of the other chain, say hello for that chain's network id (made from its public net.conf: chain, parameters and genesis allocation, so a node of another network is refused), read its tip, and ask for the blocks after a locator, one by one. Nothing the node says is trusted: each block passes the light-client checks (seal at the difficulty the headers dictate, commitment, stamp, height, state chaining), a reorg is followed by stepping back to the common block and taking the new ones, and at most 500 blocks are taken per round.
- **Several nodes per chain** (`Observer::spawn_net`): the other chain's full nodes (the `seed` lines of its net.conf, or `ZEN_FOLLOW_<CHAIN>`) are followed side by side, each with its own header chain, and the longest valid one is the view. A stale node cannot hide newer blocks, a dead one is retried every 10 s, a node that sent a block failing the checks is left alone for 5 min.
- **Same rules for claims**: `CrossMode::View` reads the observer as before, so order claims, stage-6 rates and auctions run unchanged on a split deployment. The explorer's `/api/chains` marks the other chains as followed over the network.
Live (`scripts/demo_split.sh`): three separate processes; Ken sees Yen and Jen at height 3 checked over the wire; a cross-chain trade is claimed and filled. The container entrypoint's `chain` mode and `docker-compose.split.yml` were run natively the same way (three entrypoints, one shared net dir, health check passing); the Docker build itself is still untested here. Unit tests: following, reorg, per-call limit, wrong network, a vanished node is an I/O error and not a verdict, and the observer's choice among a dead, a stale and a current node. Limits: the view picks the longest chain by height, not by chainwork (equal here because difficulty targets a constant block time; a real launch should compare work); a node that withholds blocks can only delay claims, not forge them, and following several nodes (ideally run by different people) is the defence; a node must be reachable on its p2p port, and there is still no seed discovery beyond the net.conf list.

## Round 48 — the security review (Justus L. Ludovic)

An internal review of the whole protocol; the full list, with what was not covered and what an outside auditor should look at, is in `SECURITY-REVIEW.md`. Five findings were fixed, each with a test written first or alongside:
- **Amount plus fee could wrap** in the balance check of `Run::one`: now computed in 128 bits (`an_amount_so_large_that_amount_plus_fee_wraps_is_refused`).
- **A vault claim could be replayed on another chain**: the chain id is now part of what the vault's key signs (`a_vault_claim_signed_for_one_chain_is_refused_on_another`). This changes the claim message: old signatures are not valid.
- **Sealed requests could be replayed** inside the 60 s window: the node keeps the one-time keys it has seen (`a_copy_of_a_request_inside_the_time_window_is_refused_but_a_new_request_is_not`).
- **The routing daemon** now limits a peer's answer to 4 MiB and serves at most 64 connections at once.
- **The cross-chain follower** takes the chain with the most proof of work, not the most blocks (headers carry cumulative work).
Accepted and written down: no forward secrecy for requests, `pay_to` reuse, a Sybil trader can move the official rate for a while, the fill tape is not in snapshots, no replace-by-fee in the pool.

## Round 49 — proofs, step P1: Poseidon addresses and messages (Justus L. Ludovic)

First step of the real proofs for the new operations (`PROOFS-PLAN.md`). The block proof can only check things hashed with Poseidon; lock addresses and every signed message used SHA-256. They are now all Poseidon over field elements in a fixed layout (`locks.rs`, top of the file):
- A number is 32-bit limbs (a u64 is two elements, so nothing is reduced modulo the field and the hash cannot be fooled by two numbers that wrap to the same element); a 41-byte point is eleven limbs; each kind of data starts with its own 8-character domain tag.
- Lists are padded to their maximum (8 point locks, 8 factory members) and carry their length.
- Digests are layered: a factory's address hashes its members' digests, a member's digest hashes its point-lock digest. A circuit can then open one member or one point-lock list at a time without hashing the whole factory.
- Changed: lock address (`Terms::digest`), channel id and factory id, sub-channel id, the signed messages of vault claims, channel states and closes, factory states and closes, and the message a sender signs for an operation (`SignedOp::message`: chain, nonce and the request's fields; terms, proofs and lists enter as digests).
- Unchanged: storage and wire encodings, operation ids, transport, onion routing, the cross-chain header hashes (those are the other chain's own SHA-256 and belong to the order-claim stage).
- This changes every lock address and signature: testnets started before this round do not carry over.
Test: `a_locks_address_follows_every_field_of_its_terms_and_every_state` (about 40 different terms and states all have different addresses; ids ignore the state; messages differ by chain and by subject).

## Round 50 — proofs, step P2: the vault operations are proved (Justus L. Ludovic)

Second step of the real proofs (`PROOFS-PLAN.md`). Make-with-vault-terms, VaultClaim and VaultRefund now have their own leaf circuit (`opcirc.rs`) and ride in the block proof next to payments.
- **Shape.** An operation is its own leaf proof with the same public values as a state leaf (16, plus 68 verifier-data zeros). A fixed-point loop unions the gate sets of the state leaf, the op leaf and the merge, so all three have one shape and the universal merge picks the leaf key with `select_verifier_data`. Leaves stay chained by root, so operations keep their order.
- **What the op leaf checks.** The sender's signature on the Poseidon message, balance (u128-safe) and nonce; the lock's address against its terms; the rule of the op (Make: pay from sender, put the lock in; Claim/Refund: fee, credit the destination, remove the lock; timeout edges for refunds; the claim signature on `vault_claim_msg(chain, lock, dest)`); and the Merkle paths of every account the op touches. The node's replay records those touches (`Touch`, `OpTrace`), so the prover gets exactly the paths it needs.
- **Block totals.** Fee, count and data hash now include operations (payment leaf hashes first, then op hashes in block order). `replay_ctx` computes the same numbers as the circuit.
- **Node side.** `StampMaker` gains `ops` and `accepts`; the builder only takes operations the stamp maker can prove; the serve path attaches the operation pool to the prover.
- **Left to the node (subset principle):** key subgroup check, uniqueness of new addresses, sign of y. Full nodes replay everything natively anyway.
- **Not yet:** only the vault family is provable; `CHAIN_ID` is a constant in the circuit; the Groth16 setup must be redone at P6, so `supports_ops()` stays false for the Groth16 stamp until then.
Tests: 4 in `opcirc` (real proofs; wrong signer, forged vault signature, wrong root, inflated balance, timeout edges and nonce replay all fail to prove), plus an end-to-end test where real stamps carry vault operations and the node's `accept` verifies them.

## Round 51 — proofs, step P3: the channel operations are proved (Justus L. Ludovic)

Third step of the real proofs (`PROOFS-PLAN.md`). Channels (open, fund, start, update, settle, close; streams too) now have their own leaf circuit, `chancirc.rs`, next to the vault leaf and the payment leaf.
- **One circuit, six operations.** A one-hot choice (Make, Fund, Start, Update, Settle, Close) switches the rules on and off. The leaf has the same public values and the same shape as the others (2^13 rows; the channel leaf itself is just over 2^12 before padding), so the merge takes it.
- **The merge now takes any number of leaf families.** `build_node` gets a list of operation verifier keys and a flag per family on each child; the prover proves each family with its own circuit and puts the proofs back in block order. P4 and P5 add families the same way. `build_family` (main.rs) brings all leaf circuits and the merge to one shape.
- **What the leaf checks, besides the sender's signature, balance, nonce, fee floor and the "each gram counts once" bookkeeping:**
  - the channel's address is the Poseidon digest of its terms (and the new address the digest of the new terms: the state changes with the operation);
  - who may send it, the state it needs, the dispute window against the height, the update number grows, a's share and the point locks fit in what the channel holds (checked prefix by prefix so nothing wraps), a stream holds no point locks and its state is the amount paid;
  - Update and Close: a's and b's signatures over the channel state or the close, with the keys that are in the terms (a stream has no signature of b: that slot checks a fixed dummy one);
  - Settle: for each of up to 8 point locks, either the scalar that opens it (the circuit computes t·G and compares) or an expiry in the past; the payouts follow (a opened lock goes to its receiver, an expired one back to its sender); each side is paid only if its share is above zero, and a payout can open a new account;
  - the Merkle updates in the node's order: sender, a's account, b's account, the channel's own slot; the block data hash binds the whole operation, including the destinations, signatures, point-lock list and witnesses.
- **Three consensus rules tightened** so the circuit and the node agree exactly (testnet only): an update number stays below 2^62; a point lock's expiry is below 2^62; a settle's witness must open its point lock (a wrong scalar is refused instead of being treated as absent).
- **Left to the node (subset principle):** keys are points of the prime-order group and belong to the accounts a and b, the sign of a point's y coordinate (so a lock may be opened by a scalar of the negated point), and that a new account's address owns no other account.
- **Not yet:** factories, orders, auctions and the order claim (P4, P5); `CHAIN_ID` is still a constant in the circuits; the Groth16 setup must be redone at P6, so `supports_ops()` stays false for the Groth16 stamp.
Tests: in `chancirc` real proofs for a full life (make, fund, two updates with point locks, settle with one opened and one expired lock), a cooperative close, a start then settle, a stream, a payout into a new account, and about fifteen failures (old update number, update after the window, shares beyond the channel, forged b signature, update number 0, wrong sender, settle too early, point lock neither opened nor expired, wrong scalar, a close nobody signed, other balances than signed); plus an end-to-end test where real stamps carry make, fund, update and settle and the node's `accept` checks each stamp.

## Round 52 — proofs, step P4: orders, auctions and factories are proved (Justus L. Ludovic)

Fourth step of the real proofs (`PROOFS-PLAN.md`). Two new leaf circuits join the vault and channel leaves: `ordercirc.rs` and `factorycirc.rs`. Only the order claim (which carries a foreign payment proof) is still not provable; that is P5.
- **Order leaf (about 2^11 rows before padding).** Make (open, or open to an auction), Reserve, Bid, Reopen, Return. The order's address is the Poseidon digest of its terms; the state (open, reserved, auction, bidding) is part of it. The circuit checks the rules the node checks: maker is sender, sell = amount, other chain's metal, deposit of at least 1%, reservation time, expiry, auction window; a reserve needs an open, unexpired order; a bid beats the one before it (which is refunded) and keeps the window; a reopen needs the reservation (or the auction's winner time) to be over and pays the held deposit or bid to the maker; a return needs the expiry to be past. The block's time (`ntime`), which a reservation stores, is a witness bound in the data hash; the node writes it. Overflow: all money values stay below 2^62.
- **Factory leaf (2^13 rows).** Make, Fund, Start, Post, Exit, ExitNow. The factory's address hashes the digests of up to eight members; the circuit takes all eight as witness, rebuilds their digests, picks the member the operation names (one-hot), checks the rule on it and rebuilds the address with that member's new digest. Post and ExitNow check two signatures (coordinator and member) over the state or close message; Exit checks up to eight point-lock openings and pays coordinator and member; a factory whose last member left is removed.
- **Shared parts** now live in `commoncirc.rs` (public-value head, sender with fee floor and bookkeeping, lock slot).
- **Wired into the block proof.** `build_family` builds and matches five leaf circuits and the merge (now four op keys, selected by chained flags); the prover routes each operation by `leaf_kind` (vault 0, channel 1, order 2, factory 3). `provable` is now everything but the order claim.
- **Consensus tightened** for the circuit: a factory Post has an update number and point-lock expiries below 2^62 (as channels).
- **Left to the node (subset principle):** key subgroup and key/address binding, the sign of a point's y, new-address uniqueness, distinct factory members.
- **Not yet:** the order claim (P5); the Groth16 setup and BN254 layer (P6), so `supports_ops()` stays false for the Groth16 stamp; `CHAIN_ID` is still a constant in the circuits.
Tests: real proofs in `ordercirc` (made, reserved, reopened, returned; an auction with bids, a refund and a reopen) and `factorycirc` (make, fund, start, close by agreement, post with point locks, exit with one opened and one expired lock, factory gone), with failures (wrong sender, amounts that do not add up, forged member signature, update number 0, shares beyond the channel, early exit, unopened lock, wrong scalar); plus an end-to-end test where real stamps carry order and factory operations and the node's `accept` checks each stamp.

## Round 53 — proofs, step P5: the order claim is proved (Justus L. Ludovic)

Fifth step of the real proofs (`PROOFS-PLAN.md`). The order claim is now the sixth kind of the order leaf (`ordercirc.rs`), so **every operation can now be carried by the block proof** (`provable` is true for all of them).
- **What the circuit checks:** the order is reserved (or its auction is closed and a winner stands); the claim is within the reservation (the last block to claim is `until`, or `close + reserve blocks` for a won auction); the taker is paid the lock's whole balance (sale plus the deposit or bid) into the account the claim names (an existing one or a new one); the order's slot is emptied; the sender's signature covers the claim, including a digest of the payment proof.
- **What it does not check, and why:** the foreign payment proof itself (the other chain's header at that height, with enough blocks on top; the block body; the payment's place, amount, receiver and time after the reservation). That needs the other chains' headers, which are a node's own view and not part of this chain's state, and hashing a whole foreign block body inside a circuit is far beyond the leaf's size. The circuit binds the proof's Poseidon digest in the sender's signature and in the block data hash, so a block cannot carry a different proof than the one the sender signed, and **every node still checks the proof when it accepts the block** (`check_payment_proof`, unchanged). The consequence to know: a stamp alone does not tell a light client that the foreign payment was made; it tells it that the node rules, which include that check, were applied by whoever built the block, and full nodes re-check. Making the stamp cover this too would need the foreign header chain as public input and an in-circuit body check (a later, heavy stage).
- **Node side:** the block-data hash of a claim now holds the proof digest (the order layout got four more elements at its end, zero for the other order operations). The prover replays claims with the checks already done when the block was built.
Tests: in `ordercirc` a reserved order is claimed in the last block of its reservation (the taker has the sale and its deposit back, the lock is gone), with failures (open order, claim one block late, wrong sender, a different proof gives a different data hash); the end-to-end test now also has a real stamp carrying a claim.

## Round 54 — proofs, step P6: Groth16 stamps carry operations (Justus L. Ludovic)

Sixth step of the real proofs (`PROOFS-PLAN.md`). The merge (since P3) takes every leaf kind; P6 rebuilds what sits above it and proves the whole path with real operations.
- **Shrink and BN254 layer rebuilt for the new merge.** The merge circuit now holds four operation keys, so its key, the shrink circuit over it and the BN254-Poseidon layer over that are new. Measured: leaves and merge 2^13 rows (state, channel, factory; vault and order about 2^11, padded to 2^13), shrink 2^13 (was 2^12), BN254 layer 2^12, 54.6 s to prove here (was about 82 s). Log: `run_export_v7.txt`, files in `out_v7/`.
- **New Groth16 setup** for that layer: 4,203,150 constraints, 17 public values (16 block values plus gnark's commitment), proving key 2007 MB, verifying key 1008 bytes. Setup took 1008 s with a peak of 5966 MB (the machine needed a 10 GB swap file; the first try was killed for memory). Logs: `run_g16_setup_v7.txt`, `run_g16_setup_v7b.txt`. `out_v7/` here keeps the verifying key (`zen.vk`), the Solidity verifier and the circuit files; the proving key and R1CS (about 2 GB and more) stay out of the zip.
- **`supports_ops()` is true in effect:** the Groth16 maker accepts every operation request (`accepts` is true since P5), so a pool with `ZEN_G16` stamps blocks with operations of all four families. The old gate, "the Groth16 stamp refuses ops", is gone.
- Full suite: 132 passed, 1 failed (a fragile balance assertion in my own end-to-end test, fixed and re-run: passes), 2 ignored (`run_tests_round54.txt`). The older payment-only Groth16 node test also passes under the new key (`run_node_v7`: `run_g16_node_v7.txt`).
- **Test** `groth16_stamps_carry_operations_of_every_family` (runs with `ZEN_G16=<dir with zen.pk, zen.r1cs, zen.vk>` and `ZEN_WRAP=<zenwrap>`): block 1 carries an order, a channel and a factory being made (three families in one block), block 2 a reservation and the start of a factory member's close; every stamp is 196 bytes, a node holding only `zen.vk` accepts it, a changed stamp byte is refused. Both blocks proved in 402 s all told on this 2 vCPU machine (log `run_g16_ops_v7.txt`).
- **This setup is single-party** (one machine made it), fine for tests and a testnet, **not for real use**: whoever ran it could, in principle, have kept the secret randomness and forge stamps. A real launch needs a public multi-party ceremony for exactly this circuit (the same compile and setup steps, with many contributors); that cannot be done from this sandbox, so it stays a launch step. The old `zen.vk` of earlier rounds does not accept blocks of this circuit and must be replaced everywhere (`out_v6` is the old one).

## Round 55 — proofs, step P7: soundness tests for the operation circuits (Justus L. Ludovic)

Seventh step of the real proofs (`PROOFS-PLAN.md`). The question: can a circuit be made to prove an operation that the node would refuse? New test-only file `soundness.rs`, four tests (vault, channel, order, factory), each walking a story of real operations and, at every step, trying to break it.
- **What is tried at each step.** (1) Tampering: one field of the operation changed (amount, fee, destination, sender, signature bytes, terms, lock index, proof digest, and so on). (2) Height scan: the same operation tried six blocks before to six after its honest height, so every time rule (expiry, reservation window, bidding window, exit delay) is probed on both sides of its edge. (3) Fee variants (below the floor, above the balance). (4) Rule-breaking variants specific to the family: unfunded Make, early Reopen, bid that does not beat the last, claim after the window, post with update number 0, shares beyond the channel, unopened or wrong-scalar point lock, early exit, forged member signature, and so on.
- **Verdict for each try.** The node's own `apply` is run first. If the node accepts, nothing to check. If the node refuses, the circuit is asked to prove it with a real plonky2 proof; the try passes if it does **not prove**, or if it proves exactly the honest statement (harmless: the same data hash as the real operation), and fails if the proof's data hash is that of the refused operation (it would vouch for something the node refuses) or if it proves some other statement. One exception is accepted on purpose: a Make moved to another empty slot is a different valid operation, and the data hash binds the slot.
- **Result:** factory 6 operations / 144 tries; channel 9 / 181; vault 3 / 62; order 9 / 196 (28 at heights the node refuses); 583 tries in all, **0 failures**, a handful harmless (5 in all; each proves the honest statement). About 65 s for the four tests.
- **Does the battery catch a bug? Checked.** I switched off one rule on purpose (the order Reopen window) and ran the order test: it failed with eleven tries where the node refuses and the circuit proves ("the proof vouches for the refused operation", Reopen at heights 4 to 9 and 9 to 13). The rule was restored (the file equals the earlier backup) and the four tests pass again.
- **Not covered, and why.**
  - Rules left to the node by design (subset principle): key subgroup, key/address binding, the sign of a point's y, new-address uniqueness, distinct factory members, and the foreign payment proof of an order claim. These are not circuit rules, so they cannot be tested here; the node tests cover them.
  - The height scan is plus or minus 6 blocks, so a rule that breaks only far from its edge would not be seen; it is a probe, not a proof.
  - `ntime` and `CHAIN_ID` are constants in the test world, so a circuit that ignored them would not be caught.
  - Tampering is a set of chosen mutations, not an exhaustive search. A fuzzer over random mutations is a later item.
- Full suite: 137 passed, 0 failed, 2 ignored (`run_tests_round55.txt`).

## Round 56 — a wallet page in the browser (Justus L. Ludovic)
- `zenproof wallet web <key file> [port]` (new `src/walletweb.rs`, page in `src/ui/wallet.html`): a small program for one key file that serves a page on `http://127.0.0.1:18470/` (default). The page shows the address, the balance on Yen, Ken and Jen (asks the three nodes on this computer over the p2p port; `ZEN_BASE_PORT` moves them), and sends a payment: chain, address, amount in grams (converted exactly to nanogram base units, no floats), fee 1% + 1. A payment is refused with a clear message when the node is down, the wallet has no account on that chain yet, or the balance does not cover amount plus fee.
- Safety: listens on 127.0.0.1 only; answers only to `localhost` or `127.0.0.1` with its own port (a page from another site cannot reach it through DNS tricks); a payment needs a random token that is put in the page when it is served (compared in constant time); the key is read once from the file and never sent to the browser; no cache, a content-security policy that allows only its own origin.
- Tests: 2 unit tests (grams to base units, token compare); live on a three-chain network: balances shown, payment of 1.5 g received after one block, no token / wrong host / overspend refused.
- Not yet: history, orders, channels in the page; a payment is not shown as pending until it is in a block.
