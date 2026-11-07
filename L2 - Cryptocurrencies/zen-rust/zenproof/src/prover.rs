// Real stamps for the node (Justus L. Ludovic): the block builder's side (`ProverMaker`) and the node's side
// (`Plonky2Stamp`) of the same pipeline the benchmark runs:
//   signature leaves (one per leaf of the block, by the minters) -> state leaves (by the builder, in block order)
//   -> the universal merge tree -> the shrink wrapper. The shrink proof is the stamp: 124 KB, public values
//   [root before (4), root after (4), fee total, payment count, data hash (4), S, height].
// A node verifies it against the shrink circuit it rebuilds locally (no trusted setup on this path); the Groth16 form
// (196 bytes) wraps the same proof (`Groth16Maker`: BN254 layer in Rust, then the Go prover as a subprocess); nodes check it with `groth16::Groth16Stamp`.
use crate::blockdata::{self, LeafData};
use crate::node::{Chain, StampMaker, StampVerifier};
use crate::{ec, leaf_hash, Acct, Tree, C, D, DEPTH, F, NONCE_SHIFT};
use crate::{build_node, build_sig, build_state, build_wrap_node, gate_union, key_big, msg_native, sign_native, set_peg, set_sig, empty_leaf, CHAIN_ID};
use crate::opcirc::{self, OpLeaf};
use crate::{Node as MergeNode, SigCircuit, StateCircuit};
use anyhow::{anyhow, bail, Result};
use num_bigint::BigUint;
use plonky2::field::types::{Field, PrimeField64};
use plonky2::hash::hash_types::HashOut;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_data::{CircuitData, CommonCircuitData, VerifierOnlyCircuitData};
use plonky2::plonk::proof::{ProofWithPublicInputs, ProofWithPublicInputsTarget};
use rand::SeedableRng;
use std::collections::HashMap;
use std::sync::Arc;

/// a payment as the signature leaf and the state leaf see it
struct SigP { slot: usize, s_pk: [F; 4], r_pk: [F; 4], amt: u64, fee: u64, nonce: u64, close: bool }

/// all the circuits for blocks of `n` slots per leaf (built deterministically, so every node gets the same keys)
pub struct Circuits {
    pub n: usize,
    prm: ec::Params,
    sig: SigCircuit,
    st: StateCircuit,
    op: OpLeaf,
    chan: crate::chancirc::ChanLeaf,
    order: crate::ordercirc::OrderLeaf,
    fact: crate::factorycirc::FactoryLeaf,
    node: MergeNode,
    w1: CircuitData<F, C, D>,
    t1: ProofWithPublicInputsTarget<D>,
}
impl Circuits {
    pub fn build(n: usize) -> Result<Circuits> {
        let prm = ec::params();
        let sig = build_sig(n, &prm);
        let crate::Family { st, op, chan, order, fact, node } = crate::build_family(n, &sig.data, &prm, None)?;
        let (w1, t1) = build_wrap_node(&node.data);
        Ok(Circuits { n, prm, sig, st, op, chan, order, fact, node, w1, t1 })
    }
    pub fn stamp_common(&self) -> &CommonCircuitData<F, D> { &self.w1.common }
    pub fn stamp_verifier_only(&self) -> &VerifierOnlyCircuitData<C, D> { &self.w1.verifier_only }
}

/// the node's check of a stamp: a Plonky2 proof of the shrink circuit whose public values are the block's
pub struct Plonky2Stamp { vd: plonky2::plonk::circuit_data::VerifierCircuitData<F, C, D> }
impl Plonky2Stamp {
    pub fn new(c: &Circuits) -> Plonky2Stamp { Plonky2Stamp { vd: plonky2::plonk::circuit_data::VerifierCircuitData { verifier_only: c.stamp_verifier_only().clone(), common: c.stamp_common().clone() } } }
}
impl StampVerifier for Plonky2Stamp {
    fn verify(&self, pubvalues: &[u64], stamp: &[u8]) -> Result<()> {
        let proof = ProofWithPublicInputs::<F, C, D>::from_bytes(stamp.to_vec(), &self.vd.common).map_err(|e| anyhow!("stamp does not parse: {e}"))?;
        if proof.public_inputs.len() != pubvalues.len() { bail!("stamp has {} public values", proof.public_inputs.len()); }
        for (a, b) in proof.public_inputs.iter().zip(pubvalues) { if a.to_canonical_u64() != *b { bail!("stamp proves other public values"); } }
        self.vd.verify(proof).map_err(|e| anyhow!("stamp does not verify: {e}"))
    }
}

/// the builder's prover: signs nothing itself (the wallets do), but the devnet wallets' keys live here
/// signed payments the wallets made, by (sender address, nonce): the prover uses their signatures as they are
pub type SigStore = Arc<std::sync::Mutex<HashMap<([u64; 4], u64), crate::tx::SignedPay>>>;
/// `keys` are devnet wallets whose secrets the pool holds (it signs for them when no signed payment is in the store)
pub struct ProverMaker { pub circ: Arc<Circuits>, pub keys: Vec<crate::mint::Key>, pub store: SigStore,
                         /// the operation pool of the node: the wallets' signed operations, whose signatures the proofs of operations carry
                         pub ops_pool: Arc<std::sync::Mutex<Option<Arc<std::sync::Mutex<crate::locks::OpPool>>>>>,
                         /// how many leaf and merge proofs run at the same time (each one also uses all cores inside itself)
                         pub par: usize }
impl ProverMaker { pub fn new(circ: Arc<Circuits>, keys: Vec<crate::mint::Key>) -> Self { ProverMaker { circ, keys, store: Default::default(), ops_pool: Default::default(), par: default_par() } }
    pub fn attach_ops(&self, pool: Arc<std::sync::Mutex<crate::locks::OpPool>>) { *self.ops_pool.lock().unwrap() = Some(pool); } }
/// proofs in flight at once: `ZEN_PAR_PROOFS`, else a quarter of the cores (one on a 2-core machine, 8 on 32 cores); a proof of a leaf needs about 0.9 GB
pub fn default_par() -> usize {
    std::env::var("ZEN_PAR_PROOFS").ok().and_then(|v| v.parse().ok()).unwrap_or_else(|| std::thread::available_parallelism().map_or(1, |n| n.get() / 4)).clamp(1, 16)
}
/// prove the witnesses of one circuit, `par` at a time, results in order
fn prove_many(data: &CircuitData<F, C, D>, pws: Vec<PartialWitness<F>>, par: usize) -> Result<Vec<ProofWithPublicInputs<F, C, D>>> {
    use rayon::prelude::*;
    let mut out = Vec::with_capacity(pws.len());
    let mut it = pws.into_iter();
    loop {
        let chunk: Vec<PartialWitness<F>> = it.by_ref().take(par.max(1)).collect();
        if chunk.is_empty() { break; }
        let done: Vec<Result<ProofWithPublicInputs<F, C, D>>> = if chunk.len() == 1 { chunk.into_iter().map(|pw| data.prove(pw)).collect() } else { chunk.into_par_iter().map(|pw| data.prove(pw)).collect() };
        for r in done { out.push(r?); }
    }
    Ok(out)
}
impl ProverMaker {
    /// the shrink proof of a block (the Plonky2 stamp), its public values checked against the replay's
    pub fn prove(&self, pre: &Chain, height: u64, leaves: &[LeafData], ops: &[crate::locks::Op], ntime: u32, pubvalues: &[u64]) -> Result<ProofWithPublicInputs<F, C, D>> {
        let secret: HashMap<[u64; 4], (ec::P, [u64; 4])> = self.keys.iter().map(|k| (k.addr.map(|x| x.to_canonical_u64()), (k.a, k.secret_limbs()))).collect();
        if !ops.is_empty() && pre.p.chain as u64 != CHAIN_ID { bail!("the operation circuit is built for chain {CHAIN_ID}, this is chain {}", pre.p.chain); }
        let pool = self.ops_pool.lock().unwrap().clone();
        let proof = prove_block(&self.circ, self.par, &pre.state, &pre.tree, height, pre.reading.s, leaves, &|addr| secret.get(&addr.map(|x| x.to_canonical_u64())).copied(),
                                 &|a, n| self.store.lock().unwrap().get(&(a.map(|x| x.to_canonical_u64()), n)).cloned(),
                                 ops, ntime, &pre.locks, &|a, n| pool.as_ref().and_then(|p| p.lock().unwrap().find(a, n)))?;
        let got: Vec<u64> = proof.public_inputs.iter().map(|x| x.to_canonical_u64()).collect();
        if got != pubvalues { bail!("the proof's public values differ from the replay's"); }
        Ok(proof)
    }
}
impl StampMaker for ProverMaker {
    fn accepts(&self, req: &crate::locks::OpReq) -> bool { crate::locks::provable_req(req) }
    fn stamp(&self, pre: &Chain, height: u64, leaves: &[LeafData], ops: &[crate::locks::Op], ntime: u32, pubvalues: &[u64]) -> Result<Vec<u8>> { Ok(self.prove(pre, height, leaves, ops, ntime, pubvalues)?.to_bytes()) }
}

// ---- the Groth16 stamp: shrink proof -> BN254-Poseidon layer (Rust) -> gnark prover (Go, run as a subprocess) -> 196 bytes
type C2 = crate::bn::PoseidonBn254GoldilocksConfig;
/// the layer that checks the shrink proof in a circuit whose hash is Poseidon over BN254 (what the Groth16 circuit can check cheaply).
/// Built deterministically from the shrink circuit; its digest is part of the Groth16 circuit, so a setup belongs to exactly this shape.
pub struct BnLayer { data: CircuitData<F, C2, D>, pt: ProofWithPublicInputsTarget<D> }
impl BnLayer {
    pub fn build(c: &Circuits) -> BnLayer {
        let cfg = crate::small_cfg(crate::env_u64("BN_RATE", 6) as usize, crate::env_u64("BN_QUERIES", 14) as usize, crate::env_u64("BN_POW", 16) as u32);
        BnLayer::build_over(&c.w1, cfg)
    }
    /// the layer over any shrink circuit and layer configuration (the speed experiments try several)
    pub fn build_over(w1: &CircuitData<F, C, D>, cfg: plonky2::plonk::circuit_data::CircuitConfig) -> BnLayer {
        use plonky2::plonk::circuit_builder::CircuitBuilder;
        let mut bld = CircuitBuilder::<F, D>::new(cfg);
        let vd = bld.constant_verifier_data(&w1.verifier_only);
        let pt = bld.add_virtual_proof_with_pis(&w1.common);
        bld.verify_proof::<C>(&pt, &vd, &w1.common);
        let pis = pt.public_inputs.clone();
        bld.register_public_inputs(&pis);
        if std::env::var("ZEN_GATES").is_ok() { println!("SPEED   gates before padding: {}", bld.num_gates()); }
        BnLayer { data: bld.build::<C2>(), pt }
    }
    pub fn prove(&self, shrink: &ProofWithPublicInputs<F, C, D>) -> Result<ProofWithPublicInputs<F, C2, D>> {
        let mut pw = PartialWitness::new();
        pw.set_proof_with_pis_target(&self.pt, shrink)?;
        let pb = self.data.prove(pw)?;
        self.data.verify(pb.clone())?;
        Ok(pb)
    }
    /// the three files the Go tool reads
    pub fn write(&self, dir: &std::path::Path, pb: &ProofWithPublicInputs<F, C2, D>) -> Result<()> {
        std::fs::create_dir_all(dir)?;
        // Plonky2 may hold a field element as value + p internally and writes it that way; the Groth16 public input must be the
        // canonical number (the one the node puts in), so the public values are written reduced
        let mut pb = pb.clone();
        for x in pb.public_inputs.iter_mut() { *x = F::from_canonical_u64(x.to_canonical_u64()); }
        std::fs::write(dir.join("proof_with_public_inputs.json"), serde_json::to_string(&pb)?)?;
        std::fs::write(dir.join("common_circuit_data.json"), serde_json::to_string(&self.data.common)?)?;
        let caps: Vec<String> = self.data.verifier_only.constants_sigmas_cap.0.iter().map(|h| serde_json::to_value(h).unwrap().as_str().unwrap().to_string()).collect();
        let vo = serde_json::json!({ "constants_sigmas_cap": caps, "circuit_digest": serde_json::to_value(&self.data.verifier_only.circuit_digest)? });
        std::fs::write(dir.join("verifier_only_circuit_data.json"), vo.to_string())?;
        Ok(())
    }
    pub fn digest_json(&self) -> String { serde_json::to_string(&self.data.verifier_only.circuit_digest).unwrap() }
}

/// Makes a 196-byte Groth16 stamp. `keys` holds the setup (zen.pk, zen.r1cs, zen.vk), `tool` is the `zenwrap` binary.
/// One Go prover runs at a time (it needs about 6 GB).
pub struct Groth16Maker { pub inner: ProverMaker, pub bn: BnLayer, pub tool: std::path::PathBuf, pub keys: std::path::PathBuf, pub work: std::path::PathBuf,
                          /// one process per block (false) or one long-running process that keeps the key loaded (true, the default)
                          pub persistent: bool, gate: std::sync::Mutex<Option<GoServer>> }
/// the Go prover running as `zenwrap serve <keys>`: the key is read once, then each request is a directory on stdin
struct GoServer { child: std::process::Child, stdin: std::process::ChildStdin, out: std::io::BufReader<std::process::ChildStdout> }
impl GoServer {
    fn start(tool: &std::path::Path, keys: &std::path::Path) -> Result<GoServer> {
        use std::process::Stdio;
        let mut child = std::process::Command::new(tool).arg("serve").arg(keys).stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::null()).spawn().map_err(|e| anyhow!("could not start the Go prover: {e}"))?;
        let stdin = child.stdin.take().unwrap();
        let out = std::io::BufReader::new(child.stdout.take().unwrap());
        let mut g = GoServer { child, stdin, out };
        let r = g.reply()?;
        if !r.starts_with("READY") { bail!("the Go prover did not start: {r}"); }
        Ok(g)
    }
    /// the next protocol line (the Go libraries also log; only lines that start with ZENREPLY count)
    fn reply(&mut self) -> Result<String> {
        use std::io::BufRead;
        loop {
            let mut line = String::new();
            if self.out.read_line(&mut line)? == 0 { bail!("the Go prover stopped"); }
            if let Some(r) = line.trim_end().strip_prefix("ZENREPLY ") { return Ok(r.to_string()); }
        }
    }
    fn prove(&mut self, dir: &std::path::Path) -> Result<()> {
        use std::io::Write;
        writeln!(self.stdin, "{}", dir.display())?; self.stdin.flush()?;
        let r = self.reply()?;
        if r.starts_with("OK") { Ok(()) } else { bail!("the Go prover failed: {r}") }
    }
}
impl Drop for GoServer { fn drop(&mut self) { let _ = self.child.kill(); let _ = self.child.wait(); } }
impl Groth16Maker {
    pub fn new(inner: ProverMaker, tool: std::path::PathBuf, keys: std::path::PathBuf, work: std::path::PathBuf) -> Result<Groth16Maker> {
        for f in ["zen.pk", "zen.r1cs", "zen.vk"] { if !keys.join(f).exists() { bail!("{} is missing from the setup directory {}", f, keys.display()); } }
        if !tool.exists() { bail!("the Go prover {} does not exist", tool.display()); }
        let bn = BnLayer::build(&inner.circ);
        Ok(Groth16Maker { inner, bn, tool, keys, work, persistent: std::env::var("ZEN_G16_ONESHOT").is_err(), gate: std::sync::Mutex::new(None) })
    }
}
impl StampMaker for Groth16Maker {
    fn accepts(&self, req: &crate::locks::OpReq) -> bool { crate::locks::provable_req(req) }
    fn stamp(&self, pre: &Chain, height: u64, leaves: &[LeafData], ops: &[crate::locks::Op], ntime: u32, pubvalues: &[u64]) -> Result<Vec<u8>> {
        let t0 = std::time::Instant::now();
        let shrink = self.inner.prove(pre, height, leaves, ops, ntime, pubvalues)?;
        let t1 = t0.elapsed().as_secs_f64();
        let pb = self.bn.prove(&shrink)?;
        let t2 = t0.elapsed().as_secs_f64() - t1;
        drop(shrink);
        let got: Vec<u64> = pb.public_inputs.iter().map(|x| x.to_canonical_u64()).collect();
        if got != pubvalues { bail!("the BN254 layer's public values differ from the replay's"); }
        let mut gate = self.gate.lock().unwrap();
        let dir = self.work.join(format!("g16-{}-{}", std::process::id(), height));
        let _ = std::fs::remove_dir_all(&dir);
        self.bn.write(&dir, &pb)?;
        drop(pb);
        for f in ["zen.pk", "zen.r1cs", "zen.vk"] { std::os::unix::fs::symlink(std::fs::canonicalize(self.keys.join(f))?, dir.join(f))?; }
        let result = (|| -> Result<Vec<u8>> {
            if self.persistent {
                if gate.is_none() { *gate = Some(GoServer::start(&self.tool, &self.keys)?); }
                if let Err(e) = gate.as_mut().unwrap().prove(&dir) { *gate = None; bail!("{e}"); }   // a failed server is dropped; the next block starts a new one
            } else {
                let out = std::process::Command::new(&self.tool).arg("prove").arg(&dir).output().map_err(|e| anyhow!("could not run the Go prover: {e}"))?;
                if !out.status.success() {
                    let err = String::from_utf8_lossy(&out.stderr); let tail: String = err.lines().rev().take(6).collect::<Vec<_>>().into_iter().rev().collect::<Vec<_>>().join(" | ");
                    bail!("the Go prover failed ({}): {}", out.status, tail);
                }
            }
            let proof = std::fs::read(dir.join("zen.proof"))?;
            if proof.len() != crate::groth16::PROOF_BYTES { bail!("the Go prover wrote {} bytes", proof.len()); }
            // the witness file the prover wrote must carry this block's public values
            let w = std::fs::read(dir.join("zen.pub"))?;
            let n = u32::from_be_bytes(w.get(8..12).ok_or_else(|| anyhow!("short witness file"))?.try_into()?) as usize;
            if n != pubvalues.len() || w.len() != 12 + 32 * n { bail!("the prover's public witness has the wrong shape"); }
            for (i, v) in pubvalues.iter().enumerate() {
                let el = &w[12 + 32 * i..44 + 32 * i];
                if el[..24].iter().any(|b| *b != 0) || u64::from_be_bytes(el[24..].try_into().unwrap()) != *v { bail!("the prover's public value {i} differs from the block's: {} vs {} (element {})", u64::from_be_bytes(el[24..].try_into().unwrap()), v, el.iter().map(|b| format!("{b:02x}")).collect::<String>()); }
            }
            Ok(proof)
        })();
        if result.is_ok() { let _ = std::fs::remove_dir_all(&dir); }
        if std::env::var("ZEN_TIMING").is_ok() {
            println!("TIMING block {height}: leaves, merges and shrink {t1:.1}s | BN254 layer {t2:.1}s | Groth16 {:.1}s | total {:.1}s", t0.elapsed().as_secs_f64() - t1 - t2, t0.elapsed().as_secs_f64());
        }
        result
    }
}

/// Prove a block: `leaves` are the block's leaves as the builder arranged them (payments, then credits), `state` and
/// `tree` the state before the block, `key_of` gives a sender's public point and secret to sign with.
pub fn prove_block(c: &Circuits, par: usize, state0: &HashMap<u64, Acct>, tree0: &Tree, height: u64, s: u64, leaves: &[LeafData],
                   key_of: &dyn Fn(&[F; 4]) -> Option<(ec::P, [u64; 4])>,
                   given: &dyn Fn(&[F; 4], u64) -> Option<crate::tx::SignedPay>,
                   ops: &[crate::locks::Op], ntime: u32, locks0: &crate::locks::LockTable,
                   opsig: &dyn Fn(&[F; 4], u64) -> Option<crate::locks::SignedOp>) -> Result<ProofWithPublicInputs<F, C, D>> {
    let n = c.n;
    let (day, per) = blockdata::day_period(height);
    let z4 = [F::ZERO; 4];
    let mut krng = rand::rngs::StdRng::seed_from_u64(height);
    let pad = { let k = [7u64, 7, 7, 7]; let a = ec::mul_g(&c.prm, &key_big(&k)); Acct { pk: ec::pk_hash(a), bal: 0, nonce: 0, rest: 0, used: 0, fd: 0, rd: 0, up: 0, a, k } };
    let (pad_rp, pad_sv) = sign_native(&c.prm, &pad, msg_native(&pad.pk, &z4, 0, 0, 0, false), &mut krng);

    // pass A: the nonce each payment must carry (the sender's nonce when the block reaches it), and its addresses
    let mut nonce_of: HashMap<u64, u64> = state0.iter().map(|(i, a)| (*i, a.nonce)).collect();
    let mut addr_of: HashMap<u64, [F; 4]> = state0.iter().map(|(i, a)| (*i, a.pk)).collect();
    let mut plan: Vec<Vec<SigP>> = vec![];
    for l in leaves {
        let mut v = vec![];
        for e in &l.pays {
            if let Some(a) = e.new_r { addr_of.insert(e.r_idx as u64, a); nonce_of.insert(e.r_idx as u64, height << NONCE_SHIFT); }
            if e.credit { continue; }
            let si = e.s_idx as u64;
            let nonce = *nonce_of.get(&si).ok_or_else(|| anyhow!("unknown sender"))?;
            *nonce_of.get_mut(&si).unwrap() += 1;
            let s_pk = *addr_of.get(&si).ok_or_else(|| anyhow!("unknown sender"))?;
            let r_pk = *addr_of.get(&(e.r_idx as u64)).ok_or_else(|| anyhow!("unknown receiver"))?;
            v.push(SigP { slot: e.slot as usize, s_pk, r_pk, amt: e.amt, fee: e.fee, nonce, close: e.close });
        }
        plan.push(v);
    }

    // signature leaves (the minters' work; independent of each other and of the order): the witnesses are made in order (the signatures draw from one
    // random stream), the proofs run `par` at a time
    let mut sig_pws: Vec<PartialWitness<F>> = vec![];
    let mut sig_of: Vec<usize> = vec![];                         // which witness each leaf uses
    let mut empty_sig: Option<usize> = None;
    for (li, l) in leaves.iter().enumerate() {
        if l.pays.iter().all(|e| e.credit) {
            if l.prover != z4 { bail!("a credit-only leaf has no prover"); }
            if empty_sig.is_none() { empty_sig = Some(sig_pws.len()); sig_pws.push(sig_witness(c, s, &z4, &[], &pad, pad_rp, &pad_sv, key_of, given, &mut krng)?); }
            sig_of.push(empty_sig.unwrap());
        } else {
            sig_of.push(sig_pws.len());
            sig_pws.push(sig_witness(c, s, &l.prover, &plan[li], &pad, pad_rp, &pad_sv, key_of, given, &mut krng)?);
        }
    }
    let proved = prove_many(&c.sig.data, sig_pws, par)?;
    let sig_proofs: Vec<ProofWithPublicInputs<F, C, D>> = sig_of.iter().map(|i| proved[*i].clone()).collect();

    // state leaves, in block order, on the evolving state
    let mut state = state0.clone();
    let mut tree = tree0.clone();
    let mut st_pws = vec![];
    for (li, l) in leaves.iter().enumerate() {
        let mut pw = PartialWitness::new();
        pw.set_proof_with_pis_target(&c.st.sig_pt, &sig_proofs[li])?;
        pw.set_hash_target(c.st.root0, tree.root())?;
        pw.set_target(c.st.h_t, F::from_canonical_u64(height))?;
        pw.set_target_arr(&c.st.prover, &l.prover)?;
        for (t, v) in c.st.day.iter().zip([day, height - day * blockdata::BPD, per, day - per * blockdata::REST_DAYS]) { pw.set_target(*t, F::from_canonical_u64(v))?; }
        let by_slot: HashMap<usize, &blockdata::BlockEntry> = l.pays.iter().map(|e| (e.slot as usize, e)).collect();
        let mut pi = 0usize;       // index into plan[li] (payments, in slot order)
        for (i, sl) in c.st.slots.iter().enumerate() {
            let zero_s = |pw: &mut PartialWitness<F>| -> Result<()> {
                for k in 0..DEPTH { pw.set_bool_target(sl.s_bits[k], false)?; pw.set_hash_target(sl.s_sib[k], HashOut { elements: z4 })?; }
                pw.set_target(sl.s_bal, F::ZERO)?; for t in sl.s_peg { pw.set_target(t, F::ZERO)?; } Ok(())
            };
            let zero_r = |pw: &mut PartialWitness<F>| -> Result<()> {
                for k in 0..DEPTH { pw.set_bool_target(sl.r_bits[k], false)?; pw.set_hash_target(sl.r_sib[k], HashOut { elements: z4 })?; }
                for t in [sl.r_bal, sl.r_nonce] { pw.set_target(t, F::ZERO)?; } for t in sl.r_peg { pw.set_target(t, F::ZERO)?; } Ok(())
            };
            let Some(e) = by_slot.get(&i) else {
                for bt in [sl.en, sl.skip, sl.close, sl.new_r, sl.cr] { pw.set_bool_target(bt, false)?; }
                pw.set_target_arr(&sl.s_pk, &pad.pk)?; pw.set_target_arr(&sl.r_pk, &z4)?;
                for t in [sl.amt, sl.fee, sl.nonce] { pw.set_target(t, F::ZERO)?; }
                zero_s(&mut pw)?; zero_r(&mut pw)?;
                continue;
            };
            let ri = e.r_idx as u64;
            if e.credit {
                let addr = match e.new_r { Some(a) => a, None => state.get(&ri).ok_or_else(|| anyhow!("unknown receiver"))?.pk };
                let ra = state.get(&ri).copied().unwrap_or(Acct::blank(addr, height << NONCE_SHIFT, &pad));
                for bt in [sl.en, sl.skip, sl.close] { pw.set_bool_target(bt, false)?; }
                pw.set_bool_target(sl.cr, true)?; pw.set_bool_target(sl.new_r, e.new_r.is_some())?;
                pw.set_target_arr(&sl.s_pk, &pad.pk)?; for t in [sl.fee, sl.nonce] { pw.set_target(t, F::ZERO)?; }
                zero_s(&mut pw)?;
                pw.set_target_arr(&sl.r_pk, &addr)?; pw.set_target(sl.amt, F::from_canonical_u64(e.amt))?;
                pw.set_target(sl.r_bal, F::from_canonical_u64(ra.bal))?; pw.set_target(sl.r_nonce, F::from_canonical_u64(ra.nonce))?;
                set_peg(&mut pw, &sl.r_peg, &ra)?;
                for k in 0..DEPTH { pw.set_bool_target(sl.r_bits[k], (ri >> k) & 1 == 1)?; }
                for (k, h) in tree.path(ri).into_iter().enumerate() { pw.set_hash_target(sl.r_sib[k], h)?; }
                let mut ra2 = ra; blockdata::receive_to(&mut ra2, e.amt, day, per);
                state.insert(ri, ra2); tree.set(ri, leaf_hash(&ra2));
                continue;
            }
            let p = &plan[li][pi]; pi += 1;
            if p.slot != i { bail!("payment slots out of order"); }
            let si = e.s_idx as u64;
            for bt in [sl.skip, sl.cr] { pw.set_bool_target(bt, false)?; }
            pw.set_bool_target(sl.en, true)?; pw.set_bool_target(sl.close, p.close)?;
            pw.set_target_arr(&sl.s_pk, &p.s_pk)?; pw.set_target_arr(&sl.r_pk, &p.r_pk)?;
            pw.set_target(sl.amt, F::from_canonical_u64(p.amt))?; pw.set_target(sl.fee, F::from_canonical_u64(p.fee))?; pw.set_target(sl.nonce, F::from_canonical_u64(p.nonce))?;
            let mut sa = *state.get(&si).ok_or_else(|| anyhow!("unknown sender"))?;
            pw.set_target(sl.s_bal, F::from_canonical_u64(sa.bal))?;
            set_peg(&mut pw, &sl.s_peg, &sa)?;
            for k in 0..DEPTH { pw.set_bool_target(sl.s_bits[k], (si >> k) & 1 == 1)?; }
            for (k, h) in tree.path(si).into_iter().enumerate() { pw.set_hash_target(sl.s_sib[k], h)?; }
            blockdata::pay_from(&mut sa, p.amt, p.fee, day, per);
            if p.close { state.remove(&si); tree.set(si, empty_leaf()); } else { state.insert(si, sa); tree.set(si, leaf_hash(&sa)); }
            let new_r = !state.contains_key(&ri);
            let ra = state.get(&ri).copied().unwrap_or(Acct::blank(p.r_pk, height << NONCE_SHIFT, &sa));
            pw.set_bool_target(sl.new_r, new_r)?;
            pw.set_target(sl.r_bal, F::from_canonical_u64(ra.bal))?; pw.set_target(sl.r_nonce, F::from_canonical_u64(ra.nonce))?;
            set_peg(&mut pw, &sl.r_peg, &ra)?;
            for k in 0..DEPTH { pw.set_bool_target(sl.r_bits[k], (ri >> k) & 1 == 1)?; }
            for (k, h) in tree.path(ri).into_iter().enumerate() { pw.set_hash_target(sl.r_sib[k], h)?; }
            let mut ra2 = ra; blockdata::receive_to(&mut ra2, p.amt, day, per);
            state.insert(ri, ra2); tree.set(ri, leaf_hash(&ra2));
        }
        st_pws.push(pw);
    }
    let st_proofs = prove_many(&c.st.data, st_pws, par)?;

    // operation leaves, after the payments and payouts, in the block's order, each on the state the one before left
    let mut op_pws = vec![];
    {
        use crate::locks::{apply_ops_traced, CrossMode, Ctx, SignedOp};
        let mut locks = locks0.clone();
        let tmpl = *state0.values().next().ok_or_else(|| anyhow!("empty state"))?;
        let ctx = Ctx { chain: CHAIN_ID as u8, ntime, cross: &CrossMode::Trust };   // claims were checked against the headers when the block was built; the proof binds their digest
        for op in ops {
            if !crate::locks::provable(op) { bail!("the block proof cannot carry this operation yet"); }
            let root0 = tree.root();
            let req = opcirc::req_of(op, &state)?;
            let mut tr = vec![];
            apply_ops_traced(std::slice::from_ref(op), &mut state, &mut tree, &mut locks, s, height, &ctx, tmpl, Some(&mut tr))?;
            let trace = tr.remove(0);
            let sender = trace.touches[0].old.ok_or_else(|| anyhow!("unknown sender"))?;
            let (a, sig) = match opsig(&sender.pk, sender.nonce) {
                Some(so) => (crate::mint::decode_point(&so.from_a)?, (so.e, BigUint::from_bytes_le(&so.s))),
                None => {
                    let (a, k) = key_of(&sender.pk).ok_or_else(|| anyhow!("no key or signed operation for a sender"))?;
                    let key = crate::mint::Key::from_secret(key_big(&k));
                    if key.a != a { bail!("the devnet key does not match the sender"); }
                    (a, crate::mint::sign(&key, SignedOp::message(CHAIN_ID as u8, sender.nonce, &req)))
                }
            };
            let mut pw = PartialWitness::new();
            let kind = crate::locks::leaf_kind(op).ok_or_else(|| anyhow!("the block proof cannot carry this operation yet"))?;
            if kind == 0 {
                let inp = opcirc::OpInput { op, trace: &trace, height, s, root0, chain: CHAIN_ID as u8, sender_a: a, sender_sig: sig };
                opcirc::set_witness(&c.op, &mut pw, &inp)?;
            } else if kind == 2 {
                let inp = crate::ordercirc::OrderInput { op, trace: &trace, height, s, root0, ntime, sender_a: a, sender_sig: sig };
                crate::ordercirc::set_witness(&c.order, &mut pw, &inp)?;
            } else if kind == 3 {
                let inp = crate::factorycirc::FactoryInput { op, trace: &trace, height, s, root0, chain: CHAIN_ID as u8, sender_a: a, sender_sig: sig };
                crate::factorycirc::set_witness(&c.fact, &mut pw, &inp)?;
            } else {
                let inp = crate::chancirc::ChanInput { op, trace: &trace, height, s, root0, chain: CHAIN_ID as u8, sender_a: a, sender_sig: sig };
                crate::chancirc::set_witness(&c.chan, &mut pw, &inp)?;
            }
            op_pws.push((kind, pw));
        }
    }
    // each family has its own leaf circuit: prove the families one after the other, then put the proofs back in the block's order
    let op_kinds: Vec<usize> = op_pws.iter().map(|(k, _)| *k).collect();
    let mut by_kind: Vec<std::collections::VecDeque<ProofWithPublicInputs<F, C, D>>> = vec![];
    for (k, data) in [(0usize, &c.op.data), (1, &c.chan.data), (2, &c.order.data), (3, &c.fact.data)] {
        let (pws, _): (Vec<_>, Vec<_>) = op_pws.iter().filter(|(kk, _)| *kk == k).map(|(_, pw)| (pw.clone(), ())).unzip();
        by_kind.push(if pws.is_empty() { Default::default() } else { prove_many(data, pws, par)?.into() });
    }
    let op_proofs: Vec<(usize, ProofWithPublicInputs<F, C, D>)> = op_kinds.iter().map(|k| (*k, by_kind[*k].pop_front().unwrap())).collect();

    // the universal merge tree, then the shrink wrapper: a level of the tree is independent merges, proved `par` at a time
    let mut level: Vec<(bool, Option<usize>, ProofWithPublicInputs<F, C, D>)> = st_proofs.into_iter().map(|p| (true, None, p)).chain(op_proofs.into_iter().map(|(k, p)| (true, Some(k), p))).collect();
    while level.len() > 1 || level[0].0 {
        let mut pws = vec![];
        for pair in level.chunks(2) {
            let (l_leaf, l_op, lpf) = &pair[0];
            let (r_leaf, r_op, rpf, empty) = if pair.len() == 2 { (pair[1].0, pair[1].1, &pair[1].2, false) } else { (*l_leaf, *l_op, lpf, true) };
            let (l_op, r_op) = (*l_op, r_op);
            let mut pw = PartialWitness::new();
            pw.set_proof_with_pis_target(&c.node.left, lpf)?;
            pw.set_proof_with_pis_target(&c.node.right, rpf)?;
            pw.set_bool_target(c.node.l_leaf, *l_leaf)?;
            pw.set_bool_target(c.node.r_leaf, r_leaf)?;
            for (j, x) in c.node.l_op.iter().enumerate() { pw.set_bool_target(*x, l_op == Some(j))?; }
            for (j, x) in c.node.r_op.iter().enumerate() { pw.set_bool_target(*x, r_op == Some(j))?; }
            pw.set_bool_target(c.node.r_empty, empty)?;
            pw.set_verifier_data_target(&c.node.own_vd, &c.node.data.verifier_only)?;
            pws.push(pw);
        }
        level = prove_many(&c.node.data, pws, par)?.into_iter().map(|p| (false, None, p)).collect();
    }
    let fin = level.pop().unwrap().2;
    // for the speed experiments: keep the root merge proof so they need not build a block each time
    if let Ok(path) = std::env::var("ZEN_FIN_DUMP") { std::fs::write(path, fin.to_bytes())?; }
    let mut pw = PartialWitness::new();
    pw.set_proof_with_pis_target(&c.t1, &fin)?;
    Ok(c.w1.prove(pw)?)
}

fn sig_witness(c: &Circuits, s: u64, prover: &[F; 4], pays: &[SigP], pad: &Acct, pad_rp: ec::P, pad_sv: &BigUint,
             key_of: &dyn Fn(&[F; 4]) -> Option<(ec::P, [u64; 4])>, given: &dyn Fn(&[F; 4], u64) -> Option<crate::tx::SignedPay>, krng: &mut rand::rngs::StdRng) -> Result<PartialWitness<F>> {
    let z4 = [F::ZERO; 4];
    let mut pw = PartialWitness::new();
    pw.set_target(c.sig.s_t, F::from_canonical_u64(s))?;
    pw.set_target_arr(&c.sig.prover, prover)?;
    let by_slot: HashMap<usize, &SigP> = pays.iter().map(|p| (p.slot, p)).collect();
    for (i, sl) in c.sig.slots.iter().enumerate() {
        match by_slot.get(&i) {
            Some(p) => {
                // the wallet's own signature when there is one; otherwise a devnet wallet whose secret the pool holds
                let (a, rp, sv) = match given(&p.s_pk, p.nonce) {
                    Some(t) => {
                        if t.to != p.r_pk || t.amt != p.amt || t.fee != p.fee || t.close != p.close { bail!("the signed payment is not the one in the block"); }
                        let (a, from) = t.sender()?;
                        if from != p.s_pk { bail!("the signed payment is from another sender"); }
                        let (rp, sv) = t.r_point()?;
                        (a, rp, sv)
                    }
                    None => {
                        let (a, k) = key_of(&p.s_pk).ok_or_else(|| anyhow!("no key or signed payment for a sender"))?;
                        let mut sa = Acct::blank(p.s_pk, p.nonce, pad); sa.a = a; sa.k = k;
                        let (rp, sv) = sign_native(&c.prm, &sa, msg_native(&p.s_pk, &p.r_pk, p.amt, p.fee, p.nonce, p.close), krng);
                        (a, rp, sv)
                    }
                };
                pw.set_bool_target(sl.en, true)?; pw.set_bool_target(sl.close, p.close)?;
                pw.set_target_arr(&sl.s_pk, &p.s_pk)?; pw.set_target_arr(&sl.r_pk, &p.r_pk)?;
                pw.set_target(sl.amt, F::from_canonical_u64(p.amt))?; pw.set_target(sl.fee, F::from_canonical_u64(p.fee))?; pw.set_target(sl.nonce, F::from_canonical_u64(p.nonce))?;
                set_sig(&mut pw, &sl.sig, a, rp, &sv, false)?;
            }
            None => {
                pw.set_bool_target(sl.en, false)?; pw.set_bool_target(sl.close, false)?;
                pw.set_target_arr(&sl.s_pk, &pad.pk)?; pw.set_target_arr(&sl.r_pk, &z4)?;
                for t in [sl.amt, sl.fee, sl.nonce] { pw.set_target(t, F::ZERO)?; }
                set_sig(&mut pw, &sl.sig, pad.a, pad_rp, pad_sv, false)?;
            }
        }
    }
    Ok(pw)
}

#[cfg(test)]
mod speed {
    use super::*;
    fn cfgs(var: &str, default: &str) -> Vec<(usize, usize, u32)> {
        std::env::var(var).unwrap_or(default.to_string()).split(',').map(|x| { let v: Vec<u64> = x.split(':').map(|y| y.parse().unwrap()).collect(); (v[0] as usize, v[1] as usize, v[2] as u32) }).collect()
    }
    /// ZEN_FIN_DUMP=<file> (a root merge proof written by a real block), ZEN_WRAPS=rate:queries:pow,... for the shrink, ZEN_BNS=... for the BN254 layer,
    /// ZEN_PROVE_BN=1 to prove the layer as well as build it
    #[test]
    #[ignore]
    fn wrap_speed_experiments() {
        let t = std::time::Instant::now();
        let c = Circuits::build(16).unwrap();
        println!("SPEED circuits built in {:.1}s", t.elapsed().as_secs_f64());
        let bytes = std::fs::read(std::env::var("ZEN_FIN_DUMP").unwrap()).unwrap();
        let fin = ProofWithPublicInputs::<F, C, D>::from_bytes(bytes, &c.node.data.common).unwrap();
        for (wr, wq, wp) in cfgs("ZEN_WRAPS", "3:28:16") {
            let (w, pt) = crate::build_wrap_node_cfg(&c.node.data, crate::small_cfg(wr, wq, wp));
            let mut pw = PartialWitness::new(); pw.set_proof_with_pis_target(&pt, &fin).unwrap();
            let t = std::time::Instant::now();
            let sp = w.prove(pw).unwrap();
            let ts = t.elapsed().as_secs_f64();
            w.verify(sp.clone()).unwrap();
            println!("SPEED shrink rate {wr} queries {wq} pow {wp} ({} bits): 2^{} rows, prove {:.1}s, proof {:.0} KB", wr * wq + wp as usize, w.common.degree_bits(), ts, sp.to_bytes().len() as f64 / 1024.0);
            for (br, bq, bp) in cfgs("ZEN_BNS", "6:14:16") {
                let t = std::time::Instant::now();
                let bl = BnLayer::build_over(&w, crate::small_cfg(br, bq, bp));
                let tb = t.elapsed().as_secs_f64();
                let mut line = format!("SPEED   layer rate {br} queries {bq} pow {bp} ({} bits): 2^{} rows, built {:.1}s", br * bq + bp as usize, bl.data.common.degree_bits(), tb);
                if std::env::var("ZEN_PROVE_BN").is_ok() {
                    let t = std::time::Instant::now();
                    let pb = bl.prove(&sp).unwrap();
                    line += &format!(", prove {:.1}s, proof {:.0} KB", t.elapsed().as_secs_f64(), pb.to_bytes().len() as f64 / 1024.0);
                }
                println!("{line}");
            }
        }
    }
}

#[cfg(test)]
mod op_tests {
    use super::*;
    use crate::locks::{Terms, vault_claim_msg};
    use crate::node::dev::{self, DevPay, OpReq};
    use crate::{mint, node::Params};

    fn vault(owner: &mint::Key, claimer: &mint::Key, timeout: u64) -> Terms { Terms::Vault { key: mint::encode_point(claimer.a), owner: owner.addr, timeout, salt: 0 } }
    fn ops_of(b: &crate::node::Block) -> Vec<crate::locks::Op> { crate::locks::decode_ops(&b.data[blockdata::decode_prefix(&b.data).unwrap().2..]).unwrap() }

    /// real stamps carry the vault family: a block with payments and a new vault, then a claim and a new vault, then a refund; the node checks each stamp
    /// against its own replay (the public values: roots, fee, count and data hash all include the operations)
    #[test]
    fn real_stamps_carry_vault_operations_and_the_node_checks_them() {
        use crate::prover::{Circuits, Plonky2Stamp, ProverMaker};
        assert_eq!(Params::devnet().chain as u64, CHAIN_ID);
        let circ = Arc::new(Circuits::build(16).unwrap());
        let keys = dev::devnet_keys(8);
        let maker: Arc<dyn crate::node::StampMaker> = Arc::new(ProverMaker::new(circ.clone(), keys.clone()));
        let mut net = dev::Devnet::with(None, 8, Box::new(Plonky2Stamp::new(&circ)), Some(maker.clone())).unwrap();
        let (owner, claimer, dest, anyone) = (keys[4].clone(), keys[5].clone(), keys[6].clone(), keys[7].clone());
        let chain_id = net.chain.p.chain;
        let mut build = |net: &mut dev::Devnet, pays: &[DevPay], reqs: &[OpReq]| {
            let t = std::time::Instant::now();
            let tickets = dev::make_tickets(&net.chain, &keys[..4], 24);
            let b = dev::build_block_ops(&net.chain, keys[0].addr, tickets, pays, reqs, net.chain.tip_ntime + 150, maker.as_ref()).unwrap();
            println!("block {}: {} operations, proved in {:.1}s", net.chain.height + 1, ops_of(&b).len(), t.elapsed().as_secs_f64());
            net.chain.accept(&b, u32::MAX).unwrap();
            b
        };
        // block 1: some payments and a vault of 500 000 000 that times out at height 20
        let pays: Vec<DevPay> = (0..5).map(|i| DevPay { from: keys[i].addr, to: keys[(i + 1) % 5].addr, amt: 20_000_000 + i as u64, fee: 400_000 }).collect();
        let b1 = build(&mut net, &pays, &[OpReq::Make { from: owner.addr, amt: 500_000_000, fee: 10_000, terms: vault(&owner, &claimer, 20) }]);
        assert_eq!(ops_of(&b1).len(), 1);
        assert_eq!(b1.pubvalues[9], 5 + 1, "five payments and one operation are counted");
        let lock_addr = net.chain.locks.values().next().unwrap().digest();
        let before = net.chain.account(&dest.addr).unwrap().1.bal;
        // block 2: the vault's key says where the money goes; a new vault times out soon
        let (e, sv) = mint::sign(&claimer, vault_claim_msg(chain_id, &lock_addr, &dest.addr));
        let b2 = build(&mut net, &[], &[
            OpReq::VaultClaim { from: anyone.addr, fee: 10_000, lock: lock_addr, to: dest.addr, e, s: mint::s_bytes(&sv) },
            OpReq::Make { from: owner.addr, amt: 300_000_000, fee: 10_000, terms: vault(&owner, &claimer, 3) },
        ]);
        assert_eq!(ops_of(&b2).len(), 2);
        assert_eq!(net.chain.account(&dest.addr).unwrap().1.bal, before + 500_000_000);
        // block 3 carries nothing; block 4 is after the timeout (3), so the owner's vault comes back
        build(&mut net, &[], &[]);
        let lock2 = net.chain.locks.values().next().unwrap().digest();
        let b4 = build(&mut net, &[], &[OpReq::VaultRefund { from: anyone.addr, fee: 10_000, lock: lock2, to: owner.addr }]);
        assert_eq!(ops_of(&b4).len(), 1);
        assert!(net.chain.locks.is_empty());
        net.chain.audit().unwrap();
        // the proof of block 2 does not pass for another block: a stamp is bound to the operations it proved
        let mut forged = b2.clone();
        forged.pubvalues[8] += 1;
        assert!(Plonky2Stamp::new(&circ).verify(&forged.pubvalues, &forged.stamp).is_err());
    }

    /// real stamps carry the channel family: a channel is made, funded by b, updated with a point lock and settled; every block's stamp is the node's own check
    #[test]
    fn real_stamps_carry_channel_operations_and_the_node_checks_them() {
        use crate::prover::{Circuits, Plonky2Stamp, ProverMaker};
        use crate::locks::{ChanSigs, PLock};
        let circ = Arc::new(Circuits::build(16).unwrap());
        let keys = dev::devnet_keys(8);
        let maker: Arc<dyn crate::node::StampMaker> = Arc::new(ProverMaker::new(circ.clone(), keys.clone()));
        let mut net = dev::Devnet::with(None, 8, Box::new(Plonky2Stamp::new(&circ)), Some(maker.clone())).unwrap();
        let (a, b, anyone) = (keys[4].clone(), keys[5].clone(), keys[7].clone());
        let chain_id = net.chain.p.chain;
        let mut build = |net: &mut dev::Devnet, pays: &[DevPay], reqs: &[OpReq]| {
            let t = std::time::Instant::now();
            let tickets = dev::make_tickets(&net.chain, &keys[..4], 24);
            let blk = dev::build_block_ops(&net.chain, keys[0].addr, tickets, pays, reqs, net.chain.tip_ntime + 150, maker.as_ref()).unwrap();
            println!("block {}: {} operations, proved in {:.1}s", net.chain.height + 1, ops_of(&blk).len(), t.elapsed().as_secs_f64());
            net.chain.accept(&blk, u32::MAX).unwrap();
            blk
        };
        let nonce = net.chain.account(&a.addr).unwrap().1.nonce;
        let terms = Terms::Channel { a: a.addr, b: b.addr, key_a: mint::encode_point(a.a), key_b: mint::encode_point(b.a), delay: 2, oneway: false, salt: nonce, state: crate::locks::ChanState::Open };
        let pays: Vec<DevPay> = (0..3).map(|i| DevPay { from: keys[i].addr, to: keys[i + 1].addr, amt: 20_000_000 + i as u64, fee: 400_000 }).collect();
        // block 1: payments and the new channel; block 2: b adds coins
        let b1 = build(&mut net, &pays, &[OpReq::Make { from: a.addr, amt: 500_000_000, fee: 10_000, terms: terms.clone() }]);
        assert_eq!(b1.pubvalues[9], 3 + 1);
        let lock = net.chain.locks.values().next().unwrap().digest();
        build(&mut net, &[], &[OpReq::ChanFund { from: b.addr, fee: 10_000, lock, amt: 100_000_000 }]);
        // block 3: a state with a point lock, signed by both
        let cap = 600_000_000u64;
        let t1 = num_bigint::BigUint::from(31u32);
        let pl = vec![PLock { amt: 50_000_000, to_b: true, point: mint::encode_point(ec::mul_g(&ec::params(), &t1)), expiry: 1000 }];
        let msg = crate::locks::chan_state_msg(chain_id, &terms.channel_id().unwrap(), 1, 250_000_000, cap, &pl);
        let ((ea, sa), (eb, sb)) = (mint::sign(&a, msg), mint::sign(&b, msg));
        let sigs = ChanSigs { ea, sa: mint::s_bytes(&sa), eb, sb: mint::s_bytes(&sb) };
        let lock = net.chain.locks.values().next().unwrap().digest();
        let b3 = build(&mut net, &[], &[OpReq::ChanUpdate { from: anyone.addr, fee: 10_000, lock, seq: 1, bal_a: 250_000_000, locks: pl, sigs }]);
        assert_eq!(ops_of(&b3).len(), 1);
        // blocks 4 and 5 are empty; block 6 settles (the window of 2 blocks is over), the lock opened with its scalar
        for _ in 0..3 { build(&mut net, &[], &[]); }
        let lock = net.chain.locks.values().next().unwrap().digest();
        let before = (net.chain.account(&a.addr).unwrap().1.bal, net.chain.account(&b.addr).unwrap().1.bal);
        let b6 = build(&mut net, &[], &[OpReq::ChanSettle { from: anyone.addr, fee: 10_000, lock, wits: vec![Some(mint::s_bytes(&t1))] }]);
        assert_eq!(ops_of(&b6).len(), 1);
        assert!(net.chain.locks.is_empty());
        assert_eq!(net.chain.account(&a.addr).unwrap().1.bal, before.0 + 250_000_000);
        assert_eq!(net.chain.account(&b.addr).unwrap().1.bal, before.1 + 350_000_000);
        net.chain.audit().unwrap();
    }

    /// real stamps carry orders and factories: an order is made, reserved and reopened; a factory is made, one member's channel is started and closed by agreement
    #[test]
    fn real_stamps_carry_order_and_factory_operations_and_the_node_checks_them() {
        use crate::prover::{Circuits, Plonky2Stamp, ProverMaker};
        use crate::locks::{FMember, OrderState, SubState};
        let circ = Arc::new(Circuits::build(16).unwrap());
        let keys = dev::devnet_keys(8);
        let maker: Arc<dyn crate::node::StampMaker> = Arc::new(ProverMaker::new(circ.clone(), keys.clone()));
        let mut net = dev::Devnet::with(None, 8, Box::new(Plonky2Stamp::new(&circ)), Some(maker.clone())).unwrap();
        net.chain.cross = crate::locks::CrossMode::Trust;   // the foreign proofs are the node's own check; here the stamp is what is tested
        let (mk, taker, coord, m0, m1) = (keys[4].clone(), keys[5].clone(), keys[6].clone(), keys[7].clone(), keys[3].clone());
        let chain_id = net.chain.p.chain;
        let mut build = |net: &mut dev::Devnet, reqs: &[OpReq]| {
            let t = std::time::Instant::now();
            let tickets = dev::make_tickets(&net.chain, &keys[..2], 24);
            let blk = dev::build_block_ops(&net.chain, keys[0].addr, tickets, &[], reqs, net.chain.tip_ntime + 150, maker.as_ref()).unwrap();
            println!("block {}: {} operations, proved in {:.1}s", net.chain.height + 1, ops_of(&blk).len(), t.elapsed().as_secs_f64());
            net.chain.accept(&blk, u32::MAX).unwrap();
        };
        let n_mk = net.chain.account(&mk.addr).unwrap().1.nonce;
        let n_co = net.chain.account(&coord.addr).unwrap().1.nonce;
        let (mk2, taker2) = (keys[2].clone(), keys[1].clone());
        let n_mk2 = net.chain.account(&mk2.addr).unwrap().1.nonce;
        let order2 = Terms::Order { maker: mk2.addr, sell: 400_000_000, want_chain: 1, want_amt: 5_000, pay_to: taker2.addr, expiry: 100, reserve_blocks: 2, deposit: 8_000_000, salt: n_mk2, state: OrderState::Open };
        let order = Terms::Order { maker: mk.addr, sell: 600_000_000, want_chain: 1, want_amt: 5_000, pay_to: taker.addr, expiry: 100, reserve_blocks: 2, deposit: 12_000_000, salt: n_mk, state: OrderState::Open };
        let fm = |k: &mint::Key, cap: u64| FMember { addr: k.addr, key: mint::encode_point(k.a), cap, base: cap, state: SubState::Open };
        let fact = Terms::Factory { coord: coord.addr, key_c: mint::encode_point(coord.a), delay: 2, salt: n_co, members: vec![fm(&m0, 300_000_000), fm(&m1, 200_000_000)] };
        build(&mut net, &[OpReq::Make { from: mk.addr, amt: 600_000_000, fee: 10_000, terms: order }, OpReq::Make { from: mk2.addr, amt: 400_000_000, fee: 10_000, terms: order2 }, OpReq::Make { from: coord.addr, amt: 500_000_000, fee: 10_000, terms: fact.clone() }]);
        let find = |net: &dev::Devnet, f: &dyn Fn(&Terms) -> bool| net.chain.locks.values().find(|t| f(t)).unwrap().clone();
        let is_order = |t: &Terms| matches!(t, Terms::Order { maker, .. } if *maker == mk.addr);
        let is_order2 = |t: &Terms| matches!(t, Terms::Order { maker, .. } if *maker == mk2.addr);
        let is_fact = |t: &Terms| matches!(t, Terms::Factory { .. });
        let ol = find(&net, &is_order).digest();
        let fl = find(&net, &is_fact).digest();
        let ol2 = find(&net, &is_order2).digest();
        build(&mut net, &[OpReq::Reserve { from: taker.addr, fee: 10_000, lock: ol, taker: taker.addr }, OpReq::Reserve { from: taker2.addr, fee: 10_000, lock: ol2, taker: taker2.addr }, OpReq::FactoryStart { from: coord.addr, fee: 10_000, lock: fl, idx: 0 }]);
        let ft = find(&net, &is_fact);
        let fid = ft.factory_id().unwrap();
        let msg = crate::locks::fact_close_msg(chain_id, &fid, 0, 100_000_000, 300_000_000);
        let ((ea, sa), (eb, sb)) = (mint::sign(&coord, msg), mint::sign(&m0, msg));
        let sigs = crate::locks::ChanSigs { ea, sa: mint::s_bytes(&sa), eb, sb: mint::s_bytes(&sb) };
        let fl = ft.digest();
        let before = net.chain.account(&m0.addr).unwrap().1.bal;
        build(&mut net, &[OpReq::FactoryExitNow { from: m1.addr, fee: 10_000, lock: fl, idx: 0, bal_c: 100_000_000, sigs }]);
        assert_eq!(net.chain.account(&m0.addr).unwrap().1.bal, before + 200_000_000, "the member left with its share");
        assert_eq!(net.chain.locks.len(), 3, "the factory goes on with the other member (and both orders stand)");
        // the reservation (2 blocks from block 2) runs out: anyone reopens the order, the deposit goes to the maker
        // block 4 is the last of the second order's reservation: its taker's claim is carried by the stamp
        let ol2 = find(&net, &is_order2).digest();
        let before2 = net.chain.account(&taker2.addr).unwrap().1.bal;
        build(&mut net, &[OpReq::OrderClaim { from: m1.addr, fee: 10_000, lock: ol2, proof: vec![1, 2, 3] }]);
        assert!(net.chain.account(&taker2.addr).unwrap().1.bal >= before2 + 408_000_000, "the taker has the sale and its deposit back (a minter's block payout may come on top)");
        assert_eq!(net.chain.locks.len(), 2);
        let ol = find(&net, &is_order).digest();
        build(&mut net, &[OpReq::Reopen { from: m1.addr, fee: 10_000, lock: ol }]);
        assert!(matches!(find(&net, &is_order), Terms::Order { state: OrderState::Open, .. }));
        net.chain.audit().unwrap();
    }
}
