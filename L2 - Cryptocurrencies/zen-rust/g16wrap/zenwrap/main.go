// Groth16 (BN254) wrapper for the Zen stamp: verifies the final Plonky2 proof (BN254-Poseidon
// Merkle layer) inside gnark. The proof is a PRIVATE witness, the verifier key of the Plonky2
// circuit is a constant, the 10 stamp values (root before/after, fee total, count) are public.
// Phases run as separate processes to keep peak memory low:
//   zenwrap compile <dir> | setup <dir> | prove <dir> | verify <dir>
package main

import (
	"bufio"
	"bytes"
	"fmt"
	"os"
	"runtime"
	"runtime/debug"
	"strings"
	"syscall"
	"time"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/backend/groth16"
	"github.com/consensys/gnark/backend/witness"
	"github.com/consensys/gnark/constraint"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
	"github.com/consensys/gnark/std"
	"github.com/consensys/gnark/test"
	gl "github.com/succinctlabs/gnark-plonky2-verifier/goldilocks"
	"github.com/succinctlabs/gnark-plonky2-verifier/plonk/gates"
	"github.com/succinctlabs/gnark-plonky2-verifier/types"
	"github.com/succinctlabs/gnark-plonky2-verifier/variables"
	"github.com/succinctlabs/gnark-plonky2-verifier/verifier"
)

type ZenWrap struct {
	PublicInputs            []gl.Variable `gnark:",public"`
	Proof                   variables.Proof
	VerifierOnlyCircuitData variables.VerifierOnlyCircuitData `gnark:"-"`
	CommonCircuitData       types.CommonCircuitData           `gnark:"-"`
}

func (c *ZenWrap) Define(api frontend.API) error {
	verifier.NewVerifierChip(api, c.CommonCircuitData).Verify(c.Proof, c.PublicInputs, c.VerifierOnlyCircuitData)
	return nil
}

type ChalDebug struct{ ZenWrap }

func (c *ChalDebug) Define(api frontend.API) error {
	ch := verifier.NewVerifierChip(api, c.CommonCircuitData)
	pih := ch.GetPublicInputsHash(c.PublicInputs)
	api.Println("pi_hash", pih[0].Limb, pih[1].Limb, pih[2].Limb, pih[3].Limb)
	x := ch.GetChallenges(c.Proof, pih, c.VerifierOnlyCircuitData)
	api.Println("betas", x.PlonkBetas[0].Limb, x.PlonkBetas[1].Limb, "gammas", x.PlonkGammas[0].Limb, x.PlonkGammas[1].Limb)
	api.Println("alphas", x.PlonkAlphas[0].Limb, x.PlonkAlphas[1].Limb, "zeta", x.PlonkZeta[0].Limb, x.PlonkZeta[1].Limb)
	api.Println("fri_alpha", x.FriChallenges.FriAlpha[0].Limb, x.FriChallenges.FriAlpha[1].Limb, "pow", x.FriChallenges.FriPowResponse.Limb)
	return nil
}

type GateDebug struct{ ZenWrap }

func (c *GateDebug) Define(api frontend.API) error {
	ch := verifier.NewVerifierChip(api, c.CommonCircuitData)
	pih := ch.GetPublicInputsHash(c.PublicInputs)
	glApi := gl.New(api)
	ns := c.CommonCircuitData.SelectorsInfo.NumSelectors()
	for _, id := range c.CommonCircuitData.GateIds {
		g := gates.GateInstanceFromId(id)
		vars := gates.NewEvaluationVars(c.Proof.Openings.Constants[ns:], c.Proof.Openings.Wires, pih)
		out := g.EvalUnfiltered(api, glApi, *vars)
		sum := gl.ZeroExtension()
		for _, x := range out { sum = glApi.AddExtension(sum, x) }
		sum = glApi.ReduceExtension(sum)
		n := len(id); if n > 40 { n = 40 }
		api.Println("GATE", id[:n], len(out), sum[0].Limb, sum[1].Limb)
	}
	return nil
}

func load(dir string) (ZenWrap, ZenWrap) {
	cd := types.ReadCommonCircuitData(dir + "/common_circuit_data.json")
	p := variables.DeserializeProofWithPublicInputs(types.ReadProofWithPublicInputs(dir + "/proof_with_public_inputs.json"))
	vd := variables.DeserializeVerifierOnlyCircuitData(types.ReadVerifierOnlyCircuitData(dir + "/verifier_only_circuit_data.json"))
	circuit := ZenWrap{PublicInputs: p.PublicInputs, Proof: p.Proof, VerifierOnlyCircuitData: vd, CommonCircuitData: cd}
	assign := ZenWrap{PublicInputs: p.PublicInputs, Proof: p.Proof}
	return circuit, assign
}

func peakMB() int64 {
	var ru syscall.Rusage
	syscall.Getrusage(syscall.RUSAGE_SELF, &ru)
	return ru.Maxrss / 1024
}
func must(err error) { if err != nil { panic(err) } }
func fsize(p string) float64 { st, err := os.Stat(p); if err != nil { return 0 }; return float64(st.Size()) }
func readCS(dir string) constraint.ConstraintSystem {
	cs := groth16.NewCS(ecc.BN254)
	f, err := os.Open(dir + "/zen.r1cs"); must(err); defer f.Close()
	_, err = cs.ReadFrom(f); must(err)
	return cs
}

func main() {
	debug.SetGCPercent(40)
	std.RegisterHints()
	phase, dir := os.Args[1], os.Args[2]
	t := time.Now()
	switch phase {
	case "compile":
		circuit, _ := load(dir)
		cs, err := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, &circuit)
		must(err)
		f, _ := os.Create(dir + "/zen.r1cs"); _, err = cs.WriteTo(f); must(err); f.Close()
		fmt.Printf("RESULT compile: %d constraints | %d public | %d secret | %.1fs | peak %d MB\n", cs.GetNbConstraints(), cs.GetNbPublicVariables(), cs.GetNbSecretVariables(), time.Since(t).Seconds(), peakMB())
	case "setup":
		cs := readCS(dir)
		runtime.GC()
		pk, vk, err := groth16.Setup(cs) // single-party setup: fine for a benchmark, a real launch needs an MPC ceremony
		must(err)
		f, _ := os.Create(dir + "/zen.pk"); pk.WriteRawTo(f); f.Close()
		f, _ = os.Create(dir + "/zen.vk"); vk.WriteTo(f); f.Close()
		f, _ = os.Create(dir + "/Verifier.sol"); must(vk.ExportSolidity(f)); f.Close()
		fmt.Printf("RESULT setup: %.1fs | proving key %.0f MB | verifying key %.0f bytes | peak %d MB\n", time.Since(t).Seconds(), fsize(dir+"/zen.pk")/1e6, fsize(dir+"/zen.vk"), peakMB())
	case "prove":
		_, assign := load(dir)
		w, err := frontend.NewWitness(&assign, ecc.BN254.ScalarField())
		must(err)
		cs := readCS(dir)
		var proof groth16.Proof
		if mode := os.Getenv("ZEN_ACCEL"); mode != "" {
			// GPU (or ICICLE CPU) prover: same key file, same proof format (accel_icicle.go)
			t = time.Now()
			proof, err = accelProve(cs, dir+"/zen.pk", w, mode)
			must(err)
			fmt.Printf("RESULT accelerated prover (ICICLE %s) including key load\n", mode)
		} else {
			pk := groth16.NewProvingKey(ecc.BN254)
			f, _ := os.Open(dir + "/zen.pk"); _, err = pk.UnsafeReadFrom(f); must(err); f.Close()
			runtime.GC()
			t = time.Now()
			proof, err = groth16.Prove(cs, pk, w)
			must(err)
		}
		var buf bytes.Buffer
		proof.WriteTo(&buf)
		f, _ := os.Create(dir + "/zen.proof"); f.Write(buf.Bytes()); f.Close()
		pub, _ := w.Public()
		f, _ = os.Create(dir + "/zen.pub"); pub.WriteTo(f); f.Close()
		fmt.Printf("RESULT prove: %.1fs | proof %d bytes (compressed points) | peak %d MB\n", time.Since(t).Seconds(), buf.Len(), peakMB())
	case "serve":
		// a long-running prover: reads zen.r1cs and zen.pk from `dir` once, then answers requests on stdin, one directory per
		// line (that directory holds the BN254-layer proof files and gets zen.proof and zen.pub). Replies start with ZENREPLY.
		cs := readCS(dir)
		pk := groth16.NewProvingKey(ecc.BN254)
		f, err := os.Open(dir + "/zen.pk"); must(err)
		_, err = pk.UnsafeReadFrom(f); must(err); f.Close()
		runtime.GC()
		fmt.Printf("ZENREPLY READY %.1f\n", time.Since(t).Seconds())
		sc := bufio.NewScanner(os.Stdin)
		for sc.Scan() {
			req := strings.TrimSpace(sc.Text())
			if req == "" { continue }
			func() {
				defer func() {
					if r := recover(); r != nil { fmt.Printf("ZENREPLY ERR %s\n", strings.ReplaceAll(fmt.Sprint(r), "\n", " ")) }
				}()
				t0 := time.Now()
				_, assign := load(req)
				w, err := frontend.NewWitness(&assign, ecc.BN254.ScalarField()); must(err)
				proof, err := groth16.Prove(cs, pk, w); must(err)
				var buf bytes.Buffer
				proof.WriteTo(&buf)
				must(os.WriteFile(req+"/zen.proof", buf.Bytes(), 0o644))
				pub, _ := w.Public()
				pf, err := os.Create(req + "/zen.pub"); must(err); pub.WriteTo(pf); pf.Close()
				runtime.GC()
				fmt.Printf("ZENREPLY OK %.1f %d\n", time.Since(t0).Seconds(), peakMB())
			}()
		}
	case "test":
		circuit, assign := load(dir)
		err := test.IsSolved(&circuit, &assign, ecc.BN254.ScalarField())
		fmt.Printf("RESULT test engine: satisfied=%v | %.1fs | peak %d MB\n", err == nil, time.Since(t).Seconds(), peakMB())
		if err != nil { fmt.Println(err); os.Exit(1) }
	case "chal":
		circuit, assign := load(dir)
		_ = test.IsSolved(&ChalDebug{circuit}, &ChalDebug{assign}, ecc.BN254.ScalarField())
	case "gates":
		circuit, assign := load(dir)
		_ = test.IsSolved(&GateDebug{circuit}, &GateDebug{assign}, ecc.BN254.ScalarField())
	case "solve":
		_, assign := load(dir)
		w, err := frontend.NewWitness(&assign, ecc.BN254.ScalarField())
		must(err)
		cs := readCS(dir)
		err = cs.IsSolved(w)
		fmt.Printf("RESULT solve: satisfied=%v | %.1fs | peak %d MB\n", err == nil, time.Since(t).Seconds(), peakMB())
		if err != nil { fmt.Println(err); os.Exit(1) }
	case "verify":
		vk := groth16.NewVerifyingKey(ecc.BN254)
		f, _ := os.Open(dir + "/zen.vk"); _, err := vk.ReadFrom(f); must(err); f.Close()
		proof := groth16.NewProof(ecc.BN254)
		f, _ = os.Open(dir + "/zen.proof"); _, err = proof.ReadFrom(f); must(err); f.Close()
		pub, _ := witness.New(ecc.BN254.ScalarField())
		f, _ = os.Open(dir + "/zen.pub"); _, err = pub.ReadFrom(f); must(err); f.Close()
		t = time.Now()
		err = groth16.Verify(proof, vk, pub)
		fmt.Printf("RESULT verify: ok=%v | %.2f ms | public inputs %d\n", err == nil, float64(time.Since(t).Microseconds())/1000, len(os.Args))
		if err != nil { fmt.Println(err); os.Exit(1) }
	}
}
