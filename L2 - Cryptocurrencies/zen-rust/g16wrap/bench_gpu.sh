#!/bin/bash
# Zen builder benchmark: leaves on CPU, stamp on GPU. Run on a many-core server with an NVIDIA GPU.
# Needs: Rust (nightly features via RUSTC_BOOTSTRAP), Go >= 1.26.8, CUDA + ICICLE (see BUILDER-GPU.md),
# and a proving key from one setup (zenwrap setup <dir>, about 20 min on 2 cores; copy zen.pk/zen.r1cs).
set -e
ROOT=$(cd "$(dirname "$0")/.." && pwd)
DIR=${1:-$ROOT/bench_block}
WRAP=${WRAP:-./zenwrap}
echo "== cores: $(nproc) | GPU: $(nvidia-smi --query-gpu=name --format=csv,noheader 2>/dev/null || echo none)"
( cd $ROOT/zenproof && RUSTC_BOOTSTRAP=1 cargo build --release -q )
echo "== leaves, merges, shrink, BN254 layer (CPU, all cores)"
( cd $ROOT/zenproof && BN_OUT=$DIR ./target/release/zenproof 16 8 | grep RESULT )
[ -f $DIR/zen.r1cs ] || { echo "== compile + setup (once)"; $WRAP compile $DIR; $WRAP setup $DIR; }
echo "== Groth16 on the CPU"; $WRAP prove $DIR; $WRAP verify $DIR
echo "== Groth16 on the GPU"; ZEN_ACCEL=cuda $WRAP prove $DIR; $WRAP verify $DIR
