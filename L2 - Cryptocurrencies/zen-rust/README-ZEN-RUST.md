# Zen reference node (Rust) and proof pipeline

`zenproof/` is the node, wallet, three-chain test network and proof pipeline. Start with `zenproof/MAC-TEST.md` (build and run on a Mac, Linux works the same) and `zenproof/README.md` (every build round, in order). `zenproof/PROOFS-PLAN.md` and `zenproof/SECURITY-REVIEW.md` list what is proved and what is open. Tests: `cd zenproof && RUSTC_BOOTSTRAP=1 cargo test --release` (137 pass). `g16wrap/` is the Groth16 prover in Go; `p2`, `p2sig`, `p2sigopt`, `g16`, `g16sig` and `nova` are earlier benchmarks.

Test network only: the coins have no value, the code is not audited, and the proof key (`zenproof/out_v7/zen.vk`) comes from a single-party setup that must be replaced by a public ceremony before any real use. Large generated keys and build folders are not in the repository.
