# Zen merge benchmark (Rust), October 2026

Same leaf workload in three proof systems: per payment, sender and receiver updates in a depth-32
Poseidon Merkle tree (4 paths), a payment digest hash, and range checks on balance and fee rate
(0.01%-6%). Signature verification is NOT included in any of them.

Machine: 2 CPU cores, 7 GB RAM. Build: `RUSTC_BOOTSTRAP=1 cargo build --release` in each folder
(plonky2 needs nightly features).

- p2/   Plonky2 1.1: leaf proofs + recursive 2-to-1 merges in a tree (no trusted setup).
        run: ./target/release/p2 <payments per leaf> <leaves>
- nova/ Nova 0.76: one leaf per folding step, then a compressed SNARK.
        BN254/Grumpkin + HyperKZG (needs powers of tau; test setup used) or `--features pasta`
        (Pallas/Vesta + IPA, no trusted setup). run: ./target/release/nova <payments> <leaves>
- g16/  Groth16 on BLS12-381 (bellperson 0.27) + SnarkPack aggregation (test setups used).
        run: ./target/release/g16 <payments> <leaves>

Raw outputs: */run_*.txt

## With real signatures (second round)
- p2sig/  Plonky2 + Schnorr on the EcGFp5 curve equation over GF(p^5) (own gadget, affine
          coordinates, fixed-base table for s*G, double-and-add for e*A).
          run: ./target/release/p2sig <payments> <leaves> [nosig]
- g16sig/ Groth16 + SnarkPack + the same Schnorr scheme on Jubjub (complete Edwards formulas).
          run: ./target/release/g16sig <payments> <leaves>
Scheme in both: e = 128-bit Poseidon challenge, s = r + e*k as an integer (385 bits), check s*G == R + e*A.
Set CORRUPT=1 to forge one signature: Plonky2 refuses to prove, Groth16 proofs fail verification.

## Optimised signatures + smaller blocks (third round)
- p2sigopt/  Same scheme and same payment workload as p2sig, signatures still checked INSIDE the
             proof (proving is paid work; nothing extra in the block). Changes in src/ec.rs:
             * custom Plonky2 gate DblAddGate: acc' = 2*acc + Q in one op, 2 ops per row
               (short Weierstrass coordinates, so an all-zero row is valid);
             * one joint loop over the 385 bits for s*G and e*A (picks H, H+G, H-A or H+G-A);
             * no table of constant points; R and A are checked to be on the curve.
             * final "shrink" wraps of the stamp with a large FRI blowup and few queries.
             build: RUSTC_BOOTSTRAP=1 cargo build --release
             run:   ./target/release/p2sigopt <payments> <leaves> [nosig]   (CORRUPT=1 forges s)
  Results (2 threads):
  | 16 payments/leaf          | p2sig (old) | p2sigopt  | g16sig  |
  | leaf rows                 | 2^17        | 2^14      | -       |
  | leaf prove                | 30.67 s     | 4.05 s    | 33.5 s  |
  | leaf peak memory          | 4.3 GB      | 0.58 GB   | 1.9 GB  |
  | 4 payments/leaf prove     | 7.79 s      | 0.98 s    |         |
  | 64 payments/leaf prove    | -           | 15.85 s   |         |
  | merge prove               | 4.2 s       | 4.0 s     |         |
  Stamp in the block (128 payments, 100-bit conjectured security):
    plain 131.7 KB | shrink rate 6/14 queries 69.7 KB (+8 s) | rate 7/12 63.2 KB (+14 s)
    | rate 8/10 56.6 KB (+27 s); verify 2-3 ms.
  Forged signature: prover stops ("Partition ... set twice"), no proof.

## Groth16 wrap (fourth round) -> see g16wrap/README.md
  Stamp of 128 payments -> one Groth16 proof on BN254: 196 bytes, verify 2.6 ms.
  Extra prover work per block: ~2 s + 80 s (BN254-Poseidon Plonky2 layer) + 92.5 s (Groth16).

## Fixed block shape (fifth round) -> see g16wrap/README.md
  Padding slots (enabled flag) give every block the same circuits: blocks of 128 and of 77 payments
  proved and verified with ONE Groth16 key (196-byte proofs, ~2 ms verify).

## Signature hardening + gnark v0.16.4 (sixth round) -> see g16wrap/README.md
  s mod n (canonical, 319-bit loop), canonical challenge, no exceptional cases in the DblAdd gate.
  Verifier ported to gnark v0.16.4: 4.2 M constraints, one key for blocks A and B, 196-byte proofs.

## Block data and nonces (seventh round) -> see BLOCKS.md
  Proof commits to the payment data (data hash public value). Block of 128 payments = 1,632 B of
  payments + 112 B public values + 196 B proof = ~1.9 KB (~15 B per payment). Nodes rebuild the
  state from the bytes and must match the proof; a re-submitted signed payment gives no proof.

## Version 2: leaf rules + universal merge (eighth round) -> see zenproof/README.md
  Chain id in signatures, fee floor (S/6, S/100), new accounts, closing, prover address in the data.
  Leaf and merge proofs share one circuit shape, so blocks of 8, 3 and 1 leaves end in the same final
  circuit: one Groth16 key proved and verified all three (196 B, about 3 ms).
