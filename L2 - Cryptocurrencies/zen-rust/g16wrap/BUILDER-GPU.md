# Zen builder: leaves on CPU, final stamp on GPU, sealing on ASICs

Decision (option A): every block carries its stamp. The protocol names no machine; the block time does:
a builder too slow to finish the stamp misses the block. Roles and hardware:

| role | does | hardware |
|---|---|---|
| minter | blows (Argon2id 64 MB), signature leaves (about 5-6 s per 16 payments) | phone or PC, CPU |
| builder (in practice: a mining pool) | state leaves, merges, shrink, BN254-Poseidon layer (Plonky2, CPU, all cores); final Groth16 stamp | server CPU + one NVIDIA GPU |
| miner | seals the block: SHA256d over the 80-byte Bitcoin header, via Stratum v1 | SHA-256 ASIC |

Measured on a 2-core server (no GPU): state leaves 8 x 2.7 s, merges 7 x 2.65 s, shrink 1.4 s,
BN254 layer 84 s, Groth16 96 s = about 3.7 minutes. Target: the stamp ready about 60 s after the last
leaf, inside Jen's 2.5-minute block. Not measured yet: the same steps on a many-core server and the
Groth16 step on a GPU (run bench_gpu.sh below on such a machine).

## GPU prover (gnark's ICICLE backend)
gnark v0.16.4 ships a GPU Groth16 prover (backend/accelerated/icicle, Ingonyama ICICLE, MIT). It reads
the same proving key file and outputs a standard Groth16 proof: the 196-byte stamp, checked by the same
verifying key and the same Solidity verifier. Only the prover changes.

    # 1. NVIDIA driver + CUDA toolkit (gnark tests CUDA 13 on Ubuntu 24.04), clang, cmake
    # 2. ICICLE with the CUDA backend
    git clone --branch v3.2.2 https://github.com/ingonyama-zk/icicle-gnark
    cd icicle-gnark/wrappers/golang && sudo ./build.sh -curve=all
    export CGO_LDFLAGS="-L/usr/local/lib -licicle_device -lstdc++ -lm -Wl,-rpath=/usr/local/lib"
    export ICICLE_BACKEND_INSTALL_DIR=/usr/local/lib/backend/
    # 3. the wrapper with GPU support (from gnark-plonky2-verifier + gnark-plonky2-verifier-zen.patch,
    #    with zenwrap/main.go, accel_icicle.go, accel_none.go in cmd/zenwrap)
    go build -tags=icicle -o zenwrap ./cmd/zenwrap
    # 4. prove on the GPU
    ZEN_ACCEL=cuda ./zenwrap prove <dir>      # ZEN_ACCEL unset: the CPU prover

Checked here (no GPU on this server): the GPU build compiles and links against ICICLE v3.2.2 (built from
source, CPU backend, all four curves gnark links). Running it needs a real NVIDIA GPU: gnark's ICICLE
prover uses device streams and a warm-up call that ICICLE's CPU backend does not implement
(EIcicleError.ApiNotImplemented, result_v4/accel_cpu_attempt.log). First run on a GPU machine: check
that `./zenwrap verify <dir>` accepts the GPU stamp (bench_gpu.sh does this).

## One-command benchmark for a rented machine
bench_gpu.sh runs a 128-payment block end to end and prints each step's time: signature leaves and
state leaves, merges, shrink, BN254 layer (zenproof, all CPU cores), then Groth16 on the CPU and on the
GPU, and verifies both stamps.
