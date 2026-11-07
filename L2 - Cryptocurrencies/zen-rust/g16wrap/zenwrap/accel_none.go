//go:build !icicle

package main

import (
	"errors"

	"github.com/consensys/gnark/backend/groth16"
	"github.com/consensys/gnark/backend/witness"
	"github.com/consensys/gnark/constraint"
)

const accelBuilt = false

func accelProve(cs constraint.ConstraintSystem, pkPath string, w witness.Witness, mode string) (groth16.Proof, error) {
	return nil, errors.New("built without GPU support: rebuild with -tags=icicle")
}
