//go:build icicle

package main

// GPU proving for the final stamp (Groth16 on BN254) through gnark's ICICLE backend.
// Build: go build -tags=icicle (needs the ICICLE libraries; see ../../../ZEN-GPU.md).
// ZEN_ACCEL=cuda uses the NVIDIA GPU; ZEN_ACCEL=cpu runs the same code path on ICICLE's CPU backend
// (used to check correctness on a machine without a GPU). The proving key file is the same one the
// CPU prover uses, and the proof is a standard Groth16 proof checked by the same verifying key.

import (
	"io"
	"os"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/backend/accelerated/icicle"
	icicle_groth "github.com/consensys/gnark/backend/accelerated/icicle/groth16"
	"github.com/consensys/gnark/backend/groth16"
	"github.com/consensys/gnark/backend/witness"
	"github.com/consensys/gnark/constraint"
)

const accelBuilt = true

func accelProve(cs constraint.ConstraintSystem, pkPath string, w witness.Witness, mode string) (groth16.Proof, error) {
	pk := icicle_groth.NewProvingKey(ecc.BN254)
	f, err := os.Open(pkPath)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	if _, err := pk.(interface{ UnsafeReadFrom(io.Reader) (int64, error) }).UnsafeReadFrom(f); err != nil {
		return nil, err
	}
	b := icicle.CUDA
	if mode == "cpu" {
		b = icicle.CPU
	}
	return icicle_groth.Prove(cs, pk, w, icicle.WithBackend(b))
}
