# Groth16 wrap of the Zen stamp (BN254, gnark v0.16.4)

Pipeline (one block = one stamp, fixed shape: 8 leaves x 16 payment slots):
  leaves (payments + Schnorr signatures, custom EcGFp5 gate)  ->  2-to-1 merges  ->  stamp
  -> shrink wrap (Plonky2, standard config, 2^13 rows)
  -> BN254 layer (Plonky2, Merkle trees hashed with Poseidon over BN254, rate_bits 6, 14 queries, pow 16)
  -> Groth16 on BN254 (gnark v0.16.4): verifies the whole BN254-layer proof inside the circuit
The Plonky2 proof is a PRIVATE witness; the verifier key of the Plonky2 circuit is fixed in the
circuit; the 14 stamp values (root before 4, root after 4, fee total, payment count, block-data hash 4)
are public. The block format and node checks are in ../BLOCKS.md.

## Files
- ../p2sigopt/src/ec.rs        signature circuit (EcGFp5 Schnorr, DblAdd gate, checks listed below)
- ../p2sigopt/src/bn.rs        Plonky2 1.1 hasher/config "PoseidonBn254GoldilocksConfig" (same
                               construction as gnark-plonky2-verifier's poseidon/bn254.go)
- ../p2sigopt/src/main.rs      blocks with padding slots; exports the BN254-layer proof as JSON
                               (env BN_OUT, BN_RATE, BN_QUERIES, REAL, SEED)
- zenwrap/main.go              gnark program: compile | setup | prove | verify | test | gates | chal
- gnark-plonky2-verifier-zen.patch   against succinctlabs/gnark-plonky2-verifier @ 7025b2e (Feb 2024):
    * port to gnark v0.16.4 / gnark-crypto (go.mod, go.sum; drops the unused trusted_setup
      package and benchmark.go, which pinned old gnark). No code change was needed for the port.
    * 3 fixes so it accepts Plonky2 1.1 proofs:
      1. Fiat-Shamir: Plonky2 >= 1.0 first observes the FRI parameters (FriParams::observe)
      2. Goldilocks two-adic generator changed: 1753635133440165772 -> 7277203076849721926
      3. multiplicative group generator (LDE coset shift) changed: 7 -> 14293326489335486720
- tools/goproxy.py, tools/fill.sh   build a local GOPROXY from GitHub clones (go.sum hashes matched)
- result/blockA, result/blockB      two blocks proved with ONE Groth16 key (proofs, public inputs,
                                    vk, Solidity verifier, logs)

## Build / run
  cd p2sigopt && RUSTC_BOOTSTRAP=1 cargo build --release
  NO_SHRINK=1 BN_RATE=6 BN_QUERIES=14 BN_OUT=blockA ./target/release/p2sigopt 16 8
  SEED=2 REAL=77 NO_SHRINK=1 BN_RATE=6 BN_QUERIES=14 BN_OUT=blockB ./target/release/p2sigopt 16 8
  git clone https://github.com/succinctlabs/gnark-plonky2-verifier gpv && cd gpv && git checkout 7025b2e
  git apply ../gnark-plonky2-verifier-zen.patch && mkdir -p cmd/zenwrap && cp ../zenwrap/main.go cmd/zenwrap/
  go build -o zenwrap ./cmd/zenwrap          # needs Go >= 1.26.8
  ./zenwrap compile blockA && ./zenwrap setup blockA && ./zenwrap prove blockA && ./zenwrap verify blockA
  (block B: link zen.r1cs, zen.pk, zen.vk from blockA, then prove/verify)

## Signature checks inside the leaf circuit (sixth round)
- s is reduced mod n, the prime order of EcGFp5 (n = 1067993516717146951041484916571792702745057740581727230159139685185762082554198619328292418486241,
  319 bits, from T. Pornin's ecgfp5 reference). The program checks (n-1)*G == -G at start, so G has order n.
  The circuit checks s < n (canonical s); the scalar loop is now 319 bits instead of 385.
- The challenge e is cut from two Poseidon outputs with a CANONICAL 64-bit decomposition (value < p),
  so each signature has exactly one challenge.
- DblAdd gate: two extra inverse witnesses prove xq != x and x != xr, so the incomplete addition
  formulas can never be used on an exceptional input (P = +-Q, P+Q = +-P). An honest prover
  meets such a case with negligible probability; a cheating prover cannot use one.
  Half-used gate rows are filled with a real dummy operation (an all-zero row would not pass).
- A and R are checked to be on the curve; A is bound to the account by its Poseidon hash.
- Unit tests (cargo test): s < n accepts 0, 12345, n/2, n-1 and rejects n, n+1, 2^319-1;
  DblAdd with P == Q gives no proof. Forged s (CORRUPT=1): no proof.

## Results (2 vCPU, 7 GB RAM + 12 GB swap for setup/prove; timings on this VM vary ~30% run to run)
| step                                   | result |
| leaf, 16 payments (hardened)           | 2^14 rows, 5-6.5 s |
| leaf, 4 payments                       | 2^12 rows, 1.6 s |
| merge                                  | 2^14 rows, 4-5 s |
| shrink + BN254 layer (Plonky2)         | ~3 s + ~85 s |
| Groth16 circuit (gnark v0.16.4)        | 4,203,106 constraints (14 public values) |
| Groth16 setup (one time, single party) | 23 min, proving key 2.0 GB, verifying key 944 B, peak 6.0 GB |
| Groth16 prove, block A (128 payments)  | 112 s, proof 196 bytes, verify ok (2.8 ms); payment data 1,632 B |
| Groth16 prove, block B (77 + padding)  | 108 s, proof 196 bytes, verify ok (3.9 ms); payment data 999 B |
| block A proof + block B public values  | rejected |
| test engine: payment count +1          | rejected |
| test engine: one FRI value changed     | rejected |
Block A and block B have byte-identical Plonky2 verifier data, so one Groth16 key serves every block.

## Fixed block shape
Every payment slot has an `enabled` flag. A padding slot (enabled = 0) changes no state, adds no fee
and is not counted; it still carries a valid signature from a fixed padding key. A padding slot
costs the same proving time as a real one.

## BN254-layer speed
On this VM one BN254 field multiplication takes 28 ns, one Poseidon permutation ~28 us, and the
layer needs ~6 million permutations (2^18-row LDE x 135 wire columns). That is the design, not slow
code; it scales with cores (~10 s on 16 cores) or a GPU.

## Caveats
- Setup here is single-party (fine for a benchmark). A real launch needs a multi-party ceremony
  (Groth16 keys are per circuit), or gnark PLONK with a universal setup (bigger proof, ~1 KB).
- gnark advisories checked: GHSA-9xcg-3q8v-7fq6 / CVE-2024-45040 (commitment not hiding) and
  GHSA-q3hw-3gm4-w5cr / CVE-2024-45039 (multiple commitments) are fixed since v0.11.0;
  CVE-2025-57801 (gnark's EdDSA/ECDSA gadgets) and CVE-2025-58157 (fake-GLV, v0.12.0) do not
  apply to this circuit.
- s mod n is now canonical, but this is still a benchmark signature scheme, not an audited one.

## Block data (seventh round) -> see ../BLOCKS.md
The leaf circuits hash their slot entries [enabled, sender, receiver, amount, fee] and the merges
hash pairs, so the proof commits to the published payment data (public values 11-14). Real payments
must be a prefix of each leaf. result/block*/block.bin are the published bytes; the program rebuilds
the state from them (like a node) and checks root, fee total, count and data hash against the proof.
Tests: node replay matches (A and B); one changed byte is rejected; REPLAY=1 (a signed payment
submitted twice) gives no proof.
