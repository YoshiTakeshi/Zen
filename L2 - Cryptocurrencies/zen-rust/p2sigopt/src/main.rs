// Zen merge benchmark, Plonky2 (FRI, no trusted setup, recursion).
//
// Leaf workload (the same in every framework of this benchmark), per payment:
//   - sender account: check its leaf in a depth-32 Poseidon Merkle tree, update balance and nonce,
//     recompute the root (2 x 32 hashes);
//   - receiver account: same against the intermediate root (2 x 32 hashes);
//   - payment digest hash (stand-in for the signature message; the signature check itself is
//     NOT included, see the report);
//   - range checks: new sender balance >= 0, amount and fee < 2^62, fee between 0.01% and 6%.
// Public inputs of every proof: root before (4), root after (4), fee total, payment count.
// Merge: a recursive circuit verifies two child proofs, checks left.root_after == right.root_before,
// and outputs left.root_before, right.root_after, summed fees and counts. A tree of merges gives
// one proof for the block (the "stamp").
use anyhow::Result;
use plonky2::field::types::{Field, PrimeField64};
use plonky2::hash::hash_types::{HashOut, HashOutTarget};
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::iop::target::{BoolTarget, Target};
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CircuitData};
use plonky2::plonk::config::{GenericConfig, Hasher, PoseidonGoldilocksConfig};
use plonky2::plonk::proof::ProofWithPublicInputs;
use std::collections::HashMap;
use std::time::Instant;
mod ec;
mod bn;
mod bn_consts;
mod blockdata;
use blockdata::BlockEntry;
use num_bigint::BigUint;
use rand::{Rng, SeedableRng};

const D: usize = 2;
type C = PoseidonGoldilocksConfig;
type F = <C as GenericConfig<D>>::F;
const DEPTH: usize = 32;

fn peak_mb() -> f64 {
    let s = std::fs::read_to_string("/proc/self/status").unwrap_or_default();
    for l in s.lines() {
        if l.starts_with("VmHWM:") {
            let kb: f64 = l.split_whitespace().nth(1).unwrap().parse().unwrap();
            return kb / 1024.0;
        }
    }
    0.0
}

fn h2(l: HashOut<F>, r: HashOut<F>) -> HashOut<F> {
    let mut v = l.elements.to_vec();
    v.extend_from_slice(&r.elements);
    PoseidonHash::hash_no_pad(&v)
}

#[derive(Clone, Copy)]
struct Acct { pk: [F; 4], bal: u64, nonce: u64, a: ec::P, k: [u64; 4] }
fn leaf_hash(a: &Acct) -> HashOut<F> {
    let mut v = a.pk.to_vec();
    v.push(F::from_canonical_u64(a.bal));
    v.push(F::from_canonical_u64(a.nonce));
    PoseidonHash::hash_no_pad(&v)
}

#[derive(Clone)]
struct Tree { nodes: HashMap<(usize, u64), HashOut<F>>, defaults: Vec<HashOut<F>> }
impl Tree {
    fn new() -> Self {
        let mut defaults = vec![PoseidonHash::hash_no_pad(&[F::ZERO; 6])];
        for i in 0..DEPTH { let d = defaults[i]; defaults.push(h2(d, d)); }
        Tree { nodes: HashMap::new(), defaults }
    }
    fn get(&self, lvl: usize, idx: u64) -> HashOut<F> { *self.nodes.get(&(lvl, idx)).unwrap_or(&self.defaults[lvl]) }
    fn root(&self) -> HashOut<F> { self.get(DEPTH, 0) }
    fn path(&self, idx: u64) -> Vec<HashOut<F>> { (0..DEPTH).map(|l| self.get(l, (idx >> l) ^ 1)).collect() }
    fn set(&mut self, idx: u64, leaf: HashOut<F>) {
        self.nodes.insert((0, idx), leaf);
        let mut cur = leaf;
        for l in 0..DEPTH {
            let i = idx >> l;
            let sib = self.get(l, i ^ 1);
            cur = if i & 1 == 0 { h2(cur, sib) } else { h2(sib, cur) };
            self.nodes.insert((l + 1, i >> 1), cur);
        }
    }
}

// ---------------------------------------------------------------- circuit gadgets
fn hash_t(b: &mut CircuitBuilder<F, D>, v: Vec<Target>) -> HashOutTarget { b.hash_n_to_hash_no_pad::<PoseidonHash>(v) }
fn root_from(b: &mut CircuitBuilder<F, D>, leaf: HashOutTarget, bits: &[BoolTarget], sibs: &[HashOutTarget]) -> HashOutTarget {
    let mut cur = leaf;
    for l in 0..DEPTH {
        let mut v = Vec::with_capacity(8);
        for k in 0..4 { v.push(b.select(bits[l], sibs[l].elements[k], cur.elements[k])); }
        for k in 0..4 { v.push(b.select(bits[l], cur.elements[k], sibs[l].elements[k])); }
        cur = hash_t(b, v);
    }
    cur
}
fn connect_hash(b: &mut CircuitBuilder<F, D>, x: HashOutTarget, y: HashOutTarget) { for k in 0..4 { b.connect(x.elements[k], y.elements[k]); } }
/// x == y when en = 1 (no constraint on a padding slot)
fn connect_hash_if(b: &mut CircuitBuilder<F, D>, en: BoolTarget, x: HashOutTarget, y: HashOutTarget) {
    for k in 0..4 { let d = b.sub(x.elements[k], y.elements[k]); let m = b.mul(d, en.target); b.assert_zero(m); }
}

struct PayT { s_pk: [Target; 4], s_bal: Target, s_nonce: Target, s_bits: Vec<BoolTarget>, s_sib: Vec<HashOutTarget>,
              r_pk: [Target; 4], r_bal: Target, r_nonce: Target, r_bits: Vec<BoolTarget>, r_sib: Vec<HashOutTarget>,
              amt: Target, fee: Target, sig: Option<ec::SigT>, en: BoolTarget }
struct LeafCircuit { data: CircuitData<F, C, D>, root0: HashOutTarget, pays: Vec<PayT> }

fn build_leaf(n: usize, prm: &ec::Params, with_sig: bool) -> LeafCircuit {
    let mut b = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());
    ec::dbladd_reset();
    let root0 = b.add_virtual_hash();
    let mut cur = root0;
    let mut fee_total = b.zero();
    let mut count = b.zero();
    let mut pays = vec![];
    // block data entries (one per slot): [enabled, sender index, receiver index, amount, fee],
    // all zero on a padding slot; real payments must come first in the leaf
    let mut entries: Vec<Target> = vec![];
    let mut prev_en: Option<BoolTarget> = None;
    let ten_k = b.constant(F::from_canonical_u64(10_000));
    let hundred = b.constant(F::from_canonical_u64(100));
    let six = b.constant(F::from_canonical_u64(6));
    for _ in 0..n {
        let s_pk = [b.add_virtual_target(), b.add_virtual_target(), b.add_virtual_target(), b.add_virtual_target()];
        let r_pk = [b.add_virtual_target(), b.add_virtual_target(), b.add_virtual_target(), b.add_virtual_target()];
        let (s_bal, s_nonce, r_bal, r_nonce, amt, fee) = (b.add_virtual_target(), b.add_virtual_target(), b.add_virtual_target(), b.add_virtual_target(), b.add_virtual_target(), b.add_virtual_target());
        let s_bits: Vec<BoolTarget> = (0..DEPTH).map(|_| b.add_virtual_bool_target_safe()).collect();
        let r_bits: Vec<BoolTarget> = (0..DEPTH).map(|_| b.add_virtual_bool_target_safe()).collect();
        let s_sib: Vec<HashOutTarget> = (0..DEPTH).map(|_| b.add_virtual_hash()).collect();
        // enabled = 1: a real payment; 0: a padding slot (no state change, no fee, not counted)
        let en = b.add_virtual_bool_target_safe();
        let r_sib: Vec<HashOutTarget> = (0..DEPTH).map(|_| b.add_virtual_hash()).collect();
        // sender: old leaf in current root
        let mut v = s_pk.to_vec(); v.push(s_bal); v.push(s_nonce);
        let s_old = hash_t(&mut b, v);
        let r = root_from(&mut b, s_old, &s_bits, &s_sib);
        connect_hash_if(&mut b, en, r, cur);
        // balance and fee checks
        b.range_check(amt, 62); b.range_check(fee, 62);
        let spend = b.add(amt, fee);
        let new_bal = b.sub(s_bal, spend);
        b.range_check(new_bal, 62);
        let lo = b.mul_sub(fee, ten_k, spend); b.range_check(lo, 62);           // fee*10000 >= amount+fee  (>= 0.01%)
        let six_spend = b.mul(six, spend); let hi = b.mul_sub(fee, hundred, six_spend); // fee*100 - 6*(amount+fee) <= 0
        let neg_hi = b.neg(hi); b.range_check(neg_hi, 62);
        let one = b.one();
        let new_nonce = b.add(s_nonce, one);
        // payment digest (signature message)
        let mut dv = s_pk.to_vec(); dv.extend_from_slice(&r_pk); dv.push(amt); dv.push(fee); dv.push(s_nonce);
        let digest = hash_t(&mut b, dv);
        let sig = if with_sig { let (st, pk) = ec::verify_sig(&mut b, prm, digest.elements); for k in 0..4 { b.connect(pk[k], s_pk[k]); } Some(st) } else { None };
        // sender new root
        let mut v = s_pk.to_vec(); v.push(new_bal); v.push(new_nonce);
        let s_new = hash_t(&mut b, v);
        let mid = root_from(&mut b, s_new, &s_bits, &s_sib);
        // receiver: old leaf in mid root, new leaf
        let mut v = r_pk.to_vec(); v.push(r_bal); v.push(r_nonce);
        let r_old = hash_t(&mut b, v);
        let r2 = root_from(&mut b, r_old, &r_bits, &r_sib);
        connect_hash_if(&mut b, en, r2, mid);
        let r_new_bal = b.add(r_bal, amt);
        b.range_check(r_new_bal, 63);
        let mut v = r_pk.to_vec(); v.push(r_new_bal); v.push(r_nonce);
        let r_new = hash_t(&mut b, v);
        let next = root_from(&mut b, r_new, &r_bits, &r_sib);
        cur = HashOutTarget { elements: core::array::from_fn(|k| b.select(en, next.elements[k], cur.elements[k])) };
        fee_total = b.mul_add(en.target, fee, fee_total);
        count = b.add(count, en.target);
        if let Some(pe) = prev_en { let not_pe = b.not(pe); let bad = b.mul(en.target, not_pe.target); b.assert_zero(bad); }
        prev_en = Some(en);
        let s_idx = b.le_sum(s_bits.iter()); let r_idx = b.le_sum(r_bits.iter());
        entries.push(en.target);
        for v in [s_idx, r_idx, amt, fee] { let m = b.mul(v, en.target); entries.push(m); }
        pays.push(PayT { s_pk, s_bal, s_nonce, s_bits, s_sib, r_pk, r_bal, r_nonce, r_bits, r_sib, amt, fee, sig, en });
    }
    ec::dbladd_pad(&mut b, prm);
    b.register_public_inputs(&root0.elements);
    b.register_public_inputs(&cur.elements);
    b.register_public_input(fee_total);
    b.register_public_input(count);
    let data = hash_t(&mut b, entries);
    b.register_public_inputs(&data.elements);
    let data = b.build::<C>();
    LeafCircuit { data, root0, pays }
}

struct Merge { data: CircuitData<F, C, D>, a: plonky2::plonk::proof::ProofWithPublicInputsTarget<D>, b: plonky2::plonk::proof::ProofWithPublicInputsTarget<D> }
fn build_merge(child: &CircuitData<F, C, D>) -> Merge {
    let mut bld = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());
    let vd = bld.constant_verifier_data(&child.verifier_only);
    let pa = bld.add_virtual_proof_with_pis(&child.common);
    let pb = bld.add_virtual_proof_with_pis(&child.common);
    bld.verify_proof::<C>(&pa, &vd, &child.common);
    bld.verify_proof::<C>(&pb, &vd, &child.common);
    for k in 0..4 { bld.connect(pa.public_inputs[4 + k], pb.public_inputs[k]); }
    let pis: Vec<Target> = pa.public_inputs[0..4].to_vec();
    bld.register_public_inputs(&pis);
    let pis: Vec<Target> = pb.public_inputs[4..8].to_vec();
    bld.register_public_inputs(&pis);
    let f = bld.add(pa.public_inputs[8], pb.public_inputs[8]); bld.register_public_input(f);
    let c = bld.add(pa.public_inputs[9], pb.public_inputs[9]); bld.register_public_input(c);
    // block data commitment: hash(left data, right data)
    let mut v: Vec<Target> = pa.public_inputs[10..14].to_vec(); v.extend_from_slice(&pb.public_inputs[10..14]);
    let d = bld.hash_n_to_hash_no_pad::<PoseidonHash>(v); bld.register_public_inputs(&d.elements);
    let data = bld.build::<C>();
    Merge { data, a: pa, b: pb }
}

/// re-prove a proof inside a circuit with its own config (same public inputs)
fn build_wrap(child: &CircuitData<F, C, D>, cfg: CircuitConfig) -> (CircuitData<F, C, D>, plonky2::plonk::proof::ProofWithPublicInputsTarget<D>) {
    let mut bld = CircuitBuilder::<F, D>::new(cfg);
    let vd = bld.constant_verifier_data(&child.verifier_only);
    let pt = bld.add_virtual_proof_with_pis(&child.common);
    bld.verify_proof::<C>(&pt, &vd, &child.common);
    let pis = pt.public_inputs.clone();
    bld.register_public_inputs(&pis);
    (bld.build::<C>(), pt)
}
fn small_cfg(rate_bits: usize, queries: usize, pow: u32) -> CircuitConfig {
    let mut c = CircuitConfig::standard_recursion_config();
    c.fri_config.rate_bits = rate_bits; c.fri_config.num_query_rounds = queries; c.fri_config.proof_of_work_bits = pow;
    c
}
fn set_sig(pw: &mut PartialWitness<F>, st: &ec::SigT, a: ec::P, rp: ec::P, sv: &BigUint, corrupt: bool) -> Result<()> {
    ec::set_pt(pw, st.a, a)?; ec::set_pt(pw, st.r, rp)?;
    for i in 0..ec::S_BITS { pw.set_bool_target(st.s_bits[i], sv.bit(i as u64) ^ (corrupt && i == 3))?; }
    Ok(())
}
fn sign_into(pw: &mut PartialWitness<F>, st: &ec::SigT, prm: &ec::Params, sa: &Acct, msg: [F; 4], krng: &mut rand::rngs::StdRng, corrupt: bool) -> Result<(ec::P, BigUint)> {
    let kb = BigUint::from_slice(&sa.k.iter().flat_map(|w| [*w as u32, (*w >> 32) as u32]).collect::<Vec<u32>>());
    let rw: [u64; 4] = krng.r#gen();
    let rb = BigUint::from_slice(&rw.iter().flat_map(|w| [*w as u32, (*w >> 32) as u32]).collect::<Vec<u32>>());
    let rp = ec::mul_g(prm, &rb);
    let e = ec::challenge(rp, sa.a, msg);
    let sv = (&rb + &e * &kb) % ec::n_order();
    assert!(sv.bits() as usize <= ec::S_BITS);
    if !corrupt { assert!(ec::native_check(prm, sa.a, rp, &sv, &e), "native model of the circuit check failed"); }
    set_sig(pw, st, sa.a, rp, &sv, corrupt)?;
    Ok((rp, sv))
}
fn size_kb(p: &ProofWithPublicInputs<F, C, D>) -> f64 { p.to_bytes().len() as f64 / 1024.0 }

fn main() -> Result<()> {
    let args: Vec<String> = std::env::args().collect();
    let n: usize = args.get(1).map(|s| s.parse().unwrap()).unwrap_or(16);
    let leaves: usize = args.get(2).map(|s| s.parse().unwrap()).unwrap_or(8);
    let with_sig = args.get(3).map(|s| s != "nosig").unwrap_or(true);
    println!("plonky2 (optimised EcGFp5 gate) | payments per leaf {n} | leaves {leaves} | signatures {with_sig} | threads {}", std::thread::available_parallelism()?.get());
    let t = Instant::now();
    let prm = ec::params();
    {   // the generator has prime order n: (n-1)*G == -G
        let nm1 = ec::n_order() - BigUint::from(1u32);
        assert_eq!(ec::mul(prm.g, &nm1), ec::neg(prm.g), "G does not have order n");
        println!("check: G has prime order n (319 bits)");
    }
    assert!(ec::on_curve(prm.g) && ec::on_curve(prm.h1) && ec::on_curve(prm.h0) && ec::on_curve(prm.cp));
    println!("curve params {:.1}s", t.elapsed().as_secs_f64());
    let mut krng = rand::rngs::StdRng::seed_from_u64(42);

    // accounts
    let mut tree = Tree::new();
    let mut accts: Vec<Acct> = (0..64u64).map(|_| {
        let k: [u64; 4] = krng.r#gen();
        let kb = BigUint::from_slice(&k.iter().flat_map(|w| [*w as u32, (*w >> 32) as u32]).collect::<Vec<u32>>());
        let a = ec::mul_g(&prm, &kb);
        Acct { pk: ec::pk_hash(a), bal: 1_000_000_000, nonce: 0, a, k }
    }).collect();
    let t = Instant::now();
    let idx: Vec<u64> = (0..64u64).map(|i| (i * 2654435761) & ((1u64 << DEPTH) - 1)).collect();
    for (i, a) in accts.iter().enumerate() { tree.set(idx[i], leaf_hash(a)); }

    let t = Instant::now();
    let leaf = build_leaf(n, &prm, with_sig);
    println!("leaf circuit: degree 2^{} ({} gates) | build {:.1}s | peak {:.0} MB", leaf.data.common.degree_bits(), leaf.data.common.degree(), t.elapsed().as_secs_f64(), peak_mb());

    let n_real: usize = std::env::var("REAL").ok().and_then(|v| v.parse().ok()).unwrap_or(n * leaves);
    let mut slot = 0usize;
    let pad = { let k = [7u64, 7, 7, 7]; let kb = BigUint::from_slice(&k.iter().flat_map(|w| [*w as u32, (*w >> 32) as u32]).collect::<Vec<u32>>()); let a = ec::mul_g(&prm, &kb); Acct { pk: ec::pk_hash(a), bal: 0, nonce: 0, a, k } };
    println!("block: {n_real} real payments in {} slots", n * leaves);
    let mut seed: u64 = std::env::var("SEED").ok().and_then(|v| v.parse().ok()).unwrap_or(1);
    let mut rnd = || { seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); seed >> 33 };
    let mut proofs = vec![];
    let mut leaf_times = vec![];
    let genesis = (accts.clone(), tree.clone());
    let mut block: Vec<Vec<BlockEntry>> = vec![];
    let replay_test = std::env::var("REPLAY").is_ok();
    let mut first: Option<(usize, usize, u64, u64, Acct, ec::P, BigUint)> = None;
    for _ in 0..leaves {
        block.push(vec![]);
        let mut pw = PartialWitness::new();
        pw.set_hash_target(leaf.root0, tree.root())?;
        for p in &leaf.pays {
            let real = slot < n_real; slot += 1;
            pw.set_bool_target(p.en, real)?;
            if !real {
                // padding slot: zero accounts, zero amounts, signed by the fixed padding key
                let z = [F::ZERO; 4];
                pw.set_target_arr(&p.s_pk, &pad.pk)?; pw.set_target(p.s_bal, F::ZERO)?; pw.set_target(p.s_nonce, F::ZERO)?;
                pw.set_target_arr(&p.r_pk, &z)?; pw.set_target(p.r_bal, F::ZERO)?; pw.set_target(p.r_nonce, F::ZERO)?;
                pw.set_target(p.amt, F::ZERO)?; pw.set_target(p.fee, F::ZERO)?;
                for l in 0..DEPTH {
                    pw.set_bool_target(p.s_bits[l], false)?; pw.set_bool_target(p.r_bits[l], false)?;
                    pw.set_hash_target(p.s_sib[l], HashOut { elements: z })?; pw.set_hash_target(p.r_sib[l], HashOut { elements: z })?;
                }
                if let Some(st) = &p.sig {
                    let mut dv = pad.pk.to_vec(); dv.extend(z); dv.push(F::ZERO); dv.push(F::ZERO); dv.push(F::ZERO);
                    let msg = PoseidonHash::hash_no_pad(&dv).elements;
                    sign_into(&mut pw, st, &prm, &pad, msg, &mut krng, false)?;
                }
                continue;
            }
            let s = (rnd() % 64) as usize; let mut r = (rnd() % 64) as usize; if r == s { r = (r + 1) % 64; }
            let amt = 1000 + rnd() % 100_000; let fee = amt / 100;
            let sa = accts[s];
            // REPLAY=1: the second payment re-submits the first one (same signed message, same signature)
            let replay = if replay_test && slot == 2 { first.clone() } else { None };
            let (s, r, amt, fee, sa) = match &replay { Some((s0, r0, a0, f0, sa0, _, _)) => (*s0, *r0, *a0, *f0, *sa0), None => (s, r, amt, fee, sa) };
            pw.set_target_arr(&p.s_pk, &sa.pk)?; pw.set_target(p.s_bal, F::from_canonical_u64(sa.bal))?; pw.set_target(p.s_nonce, F::from_canonical_u64(sa.nonce))?;
            for l in 0..DEPTH { pw.set_bool_target(p.s_bits[l], (idx[s] >> l) & 1 == 1)?; }
            for (l, h) in tree.path(idx[s]).into_iter().enumerate() { pw.set_hash_target(p.s_sib[l], h)?; }
            pw.set_target(p.amt, F::from_canonical_u64(amt))?; pw.set_target(p.fee, F::from_canonical_u64(fee))?;
            if let Some(st) = &p.sig {
                let mut dv = sa.pk.to_vec(); dv.extend(accts[r].pk); dv.push(F::from_canonical_u64(amt)); dv.push(F::from_canonical_u64(fee)); dv.push(F::from_canonical_u64(sa.nonce));
                let msg = PoseidonHash::hash_no_pad(&dv).elements;
                let (rp, sv) = match &replay {
                    Some((_, _, _, _, _, rp0, sv0)) => { set_sig(&mut pw, st, sa.a, *rp0, sv0, false)?; (*rp0, sv0.clone()) }
                    None => sign_into(&mut pw, st, &prm, &sa, msg, &mut krng, std::env::var("CORRUPT").is_ok())?,
                };
                if first.is_none() { first = Some((s, r, amt, fee, sa, rp, sv)); }
            }
            block.last_mut().unwrap().push(BlockEntry { s_idx: idx[s] as u32, r_idx: idx[r] as u32, amt, fee });
            accts[s].bal -= amt + fee; accts[s].nonce += 1; tree.set(idx[s], leaf_hash(&accts[s]));
            let ra = accts[r];
            pw.set_target_arr(&p.r_pk, &ra.pk)?; pw.set_target(p.r_bal, F::from_canonical_u64(ra.bal))?; pw.set_target(p.r_nonce, F::from_canonical_u64(ra.nonce))?;
            for l in 0..DEPTH { pw.set_bool_target(p.r_bits[l], (idx[r] >> l) & 1 == 1)?; }
            for (l, h) in tree.path(idx[r]).into_iter().enumerate() { pw.set_hash_target(p.r_sib[l], h)?; }
            accts[r].bal += amt; tree.set(idx[r], leaf_hash(&accts[r]));
        }
        let t = Instant::now();
        let proof = leaf.data.prove(pw)?;
        leaf_times.push(t.elapsed().as_secs_f64());
        proofs.push(proof);
    }
    let t = Instant::now(); leaf.data.verify(proofs[0].clone())?; let vt = t.elapsed().as_secs_f64() * 1000.0;
    let lt: f64 = leaf_times.iter().sum::<f64>() / leaf_times.len() as f64;
    println!("RESULT leaf: prove {:.2}s (avg of {}) | proof {:.1} KB | verify {:.1} ms | peak {:.0} MB", lt, leaves, size_kb(&proofs[0]), vt, peak_mb());

    // merge tree
    let mut child_i: Option<usize> = None;
    let mut merges: Vec<Merge> = vec![];
    let mut level = 1;
    while proofs.len() > 1 {
        let t = Instant::now();
        let m = build_merge(match child_i { None => &leaf.data, Some(i) => &merges[i].data });
        let bt = t.elapsed().as_secs_f64();
        let mut next = vec![];
        let mut times = vec![];
        for pair in proofs.chunks(2) {
            let mut pw = PartialWitness::new();
            pw.set_proof_with_pis_target(&m.a, &pair[0])?;
            pw.set_proof_with_pis_target(&m.b, &pair[1])?;
            let t = Instant::now();
            let p = m.data.prove(pw)?;
            times.push(t.elapsed().as_secs_f64());
            next.push(p);
        }
        let t = Instant::now(); m.data.verify(next[0].clone())?; let vt = t.elapsed().as_secs_f64() * 1000.0;
        println!("RESULT merge level {level}: circuit 2^{} | build {:.1}s | prove {:.2}s per merge ({} merges) | proof {:.1} KB | verify {:.1} ms | peak {:.0} MB",
            m.data.common.degree_bits(), bt, times.iter().sum::<f64>() / times.len() as f64, times.len(), size_kb(&next[0]), vt, peak_mb());
        proofs = next;
        merges.push(m);
        child_i = Some(merges.len() - 1);
        level += 1;
    }
    let fin = &proofs[0];
    let comp = merges.last().map(|m| m.data.compress(fin.clone())).transpose()?;
    if let Some(c) = comp { println!("RESULT stamp: {} payments | fee total {} | proof {:.1} KB (compressed {:.1} KB)", fin.public_inputs[9].to_canonical_u64(), fin.public_inputs[8].to_canonical_u64(), size_kb(fin), c.to_bytes().len() as f64 / 1024.0); }
    // shrink the stamp for the block: first wrap (standard config, fewer rows), then a wrap with a
    // large FRI blowup and few queries (100-bit conjectured security either way: rate_bits*queries + pow)
    if let Some(last) = merges.last() {
        let (w1, t1) = build_wrap(&last.data, CircuitConfig::standard_recursion_config());
        let mut pw = PartialWitness::new(); pw.set_proof_with_pis_target(&t1, fin)?;
        let t = Instant::now(); let p1 = w1.prove(pw)?; let pt1 = t.elapsed().as_secs_f64();
        println!("RESULT shrink 1 (standard, 3x28+16): circuit 2^{} | prove {:.2}s | proof {:.1} KB (compressed {:.1} KB)", w1.common.degree_bits(), pt1, size_kb(&p1), w1.compress(p1.clone())?.to_bytes().len() as f64 / 1024.0);
        // final layer for Groth16: same config, but Merkle trees hashed with Poseidon over BN254
        {
            type C2 = bn::PoseidonBn254GoldilocksConfig;
            let t = Instant::now();
            let env = |k: &str, d: usize| std::env::var(k).ok().and_then(|v| v.parse().ok()).unwrap_or(d);
            let bcfg = small_cfg(env("BN_RATE", 3), env("BN_QUERIES", 28), env("BN_POW", 16) as u32);
            println!("bn254 layer FRI: rate_bits {} | queries {} | pow {}", bcfg.fri_config.rate_bits, bcfg.fri_config.num_query_rounds, bcfg.fri_config.proof_of_work_bits);
            let mut bld = CircuitBuilder::<F, D>::new(bcfg);
            let vd = bld.constant_verifier_data(&w1.verifier_only);
            let pt = bld.add_virtual_proof_with_pis(&w1.common);
            bld.verify_proof::<C>(&pt, &vd, &w1.common);
            let pis = pt.public_inputs.clone();
            bld.register_public_inputs(&pis);
            let wb = bld.build::<C2>();
            let bt = t.elapsed().as_secs_f64();
            let mut pw = PartialWitness::new(); pw.set_proof_with_pis_target(&pt, &p1)?;
            let t = Instant::now(); let pb = wb.prove(pw)?; let ptb = t.elapsed().as_secs_f64();
            wb.verify(pb.clone())?;
            println!("RESULT bn254-poseidon layer: circuit 2^{} | build {:.1}s | prove {:.2}s | proof {:.1} KB | peak {:.0} MB",
                wb.common.degree_bits(), bt, ptb, pb.to_bytes().len() as f64 / 1024.0, peak_mb());
            let dir = std::env::var("BN_OUT").unwrap_or("bn_out".into());
            std::fs::create_dir_all(&dir)?;
            std::fs::write(format!("{dir}/proof_with_public_inputs.json"), serde_json::to_string(&pb)?)?;
            std::fs::write(format!("{dir}/common_circuit_data.json"), serde_json::to_string(&wb.common)?)?;
            let caps: Vec<String> = wb.verifier_only.constants_sigmas_cap.0.iter().map(|h| serde_json::to_value(h).unwrap().as_str().unwrap().to_string()).collect();
            let vo = serde_json::json!({ "constants_sigmas_cap": caps, "circuit_digest": serde_json::to_value(&wb.verifier_only.circuit_digest)? });
            std::fs::write(format!("{dir}/verifier_only_circuit_data.json"), vo.to_string())?;
            let ch = pb.get_challenges(pb.get_public_inputs_hash(), &wb.verifier_only.circuit_digest, &wb.common)?;
            let u = |v: &[F]| v.iter().map(|x| x.to_canonical_u64()).collect::<Vec<_>>();
            let ue = |x: &plonky2::field::extension::quadratic::QuadraticExtension<F>| u(&x.0);
            let cj = serde_json::json!({ "plonk_betas": u(&ch.plonk_betas), "plonk_gammas": u(&ch.plonk_gammas), "plonk_alphas": u(&ch.plonk_alphas),
                "plonk_zeta": ue(&ch.plonk_zeta), "fri_alpha": ue(&ch.fri_challenges.fri_alpha),
                "fri_betas": ch.fri_challenges.fri_betas.iter().map(|b| ue(b)).collect::<Vec<_>>(),
                "fri_pow_response": ch.fri_challenges.fri_pow_response.to_canonical_u64(), "fri_query_indices": ch.fri_challenges.fri_query_indices,
                "pi_hash": u(&pb.get_public_inputs_hash().elements) });
            std::fs::write(format!("{dir}/challenges.json"), cj.to_string())?;
            {   // per-gate filtered constraint values at zeta (debug, compared with gnark)
                let o = &pb.proof.openings;
                let pih = pb.get_public_inputs_hash();
                let si = &wb.common.selectors_info;
                let mut rows = vec![];
                for (i, g) in wb.common.gates.iter().enumerate() {
                    let ns = si.num_selectors() + wb.common.num_lookup_selectors;
                    let vars = plonky2::plonk::vars::EvaluationVars { local_constants: &o.constants[ns..], local_wires: &o.wires, public_inputs_hash: &pih };
                    let c = g.0.eval_unfiltered(vars);
                    let mut sum = plonky2::field::extension::quadratic::QuadraticExtension::<F>::default();
                    for x in &c { sum += *x; }
                    rows.push(serde_json::json!({ "gate": g.0.id(), "n": c.len(), "sum": ue(&sum) }));
                }
                std::fs::write(format!("{dir}/gate_debug.json"), serde_json::to_string_pretty(&rows)?)?;
            }
            println!("wrote {dir}/ (public inputs: {:?})", pb.public_inputs.iter().map(|x| x.to_canonical_u64()).collect::<Vec<_>>());
        }
        let shrink_cfgs: Vec<(usize, usize, u32)> = if std::env::var("NO_SHRINK").is_ok() { vec![] } else { vec![(6, 14, 16), (7, 12, 16), (8, 10, 20)] };
        for (rb, q, pow) in shrink_cfgs {
            let (w2, t2) = build_wrap(&w1, small_cfg(rb, q, pow));
            let mut pw = PartialWitness::new(); pw.set_proof_with_pis_target(&t2, &p1)?;
            let t = Instant::now(); let p2 = w2.prove(pw)?; let pt2 = t.elapsed().as_secs_f64();
            let t = Instant::now(); w2.verify(p2.clone())?; let vt = t.elapsed().as_secs_f64() * 1000.0;
            let c2 = w2.compress(p2.clone())?;
            println!("RESULT shrink 2 (rate_bits {rb}, {q} queries, pow {pow}): circuit 2^{} | prove {:.2}s | proof {:.1} KB (compressed {:.1} KB) | verify {:.1} ms | peak {:.0} MB",
                w2.common.degree_bits(), pt2, size_kb(&p2), c2.to_bytes().len() as f64 / 1024.0, vt, peak_mb());
        }
    }
    // check the stamp's roots match the real tree
    // ---- block data: serialize, then rebuild the state from (previous state, bytes) like a node would
    let bytes = blockdata::encode(n, &block);
    let pis: Vec<u64> = fin.public_inputs.iter().map(|x| x.to_canonical_u64()).collect();
    let n_pay: usize = block.iter().map(|l| l.len()).sum();
    println!("RESULT block data: {} bytes for {} payments ({:.1} bytes/payment, header + counts {} bytes)", bytes.len(), n_pay, (bytes.len() as f64 - 5.0 - leaves as f64) / n_pay.max(1) as f64, 5 + leaves);
    let node = |b: &[u8]| -> Result<blockdata::Replayed> { blockdata::replay(&genesis.0, &genesis.1, &idx, b) };
    let rp = node(&bytes)?;
    let ok = rp.public_inputs() == pis;
    println!("RESULT node replay from bytes: state root, fee total, count and data hash match the proof: {ok}");
    let mut bad = bytes.clone(); let last = bad.len() - 1; bad[last] ^= 1;   // change the last fee
    let r2 = node(&bad).map(|r| r.public_inputs() == pis);
    println!("RESULT node replay with one changed byte: accepted = {}", matches!(r2, Ok(true)));
    if let Ok(dir) = std::env::var("BN_OUT") { std::fs::create_dir_all(&dir)?; std::fs::write(format!("{dir}/block.bin"), &bytes)?; }
    let root_ok = (0..4).all(|k| fin.public_inputs[4 + k] == tree.root().elements[k]);
    println!("RESULT stamp root matches the account tree: {root_ok} | peak {:.0} MB", peak_mb());
    Ok(())
}
