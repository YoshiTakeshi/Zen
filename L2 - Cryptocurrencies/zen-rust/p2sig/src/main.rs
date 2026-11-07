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

struct PayT { s_pk: [Target; 4], s_bal: Target, s_nonce: Target, s_bits: Vec<BoolTarget>, s_sib: Vec<HashOutTarget>,
              r_pk: [Target; 4], r_bal: Target, r_nonce: Target, r_bits: Vec<BoolTarget>, r_sib: Vec<HashOutTarget>,
              amt: Target, fee: Target, sig: Option<ec::SigT> }
struct LeafCircuit { data: CircuitData<F, C, D>, root0: HashOutTarget, pays: Vec<PayT> }

fn build_leaf(n: usize, prm: &ec::Params, with_sig: bool) -> LeafCircuit {
    let mut b = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());
    let root0 = b.add_virtual_hash();
    let mut cur = root0;
    let mut fee_total = b.zero();
    let mut pays = vec![];
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
        let r_sib: Vec<HashOutTarget> = (0..DEPTH).map(|_| b.add_virtual_hash()).collect();
        // sender: old leaf in current root
        let mut v = s_pk.to_vec(); v.push(s_bal); v.push(s_nonce);
        let s_old = hash_t(&mut b, v);
        let r = root_from(&mut b, s_old, &s_bits, &s_sib);
        connect_hash(&mut b, r, cur);
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
        connect_hash(&mut b, r2, mid);
        let r_new_bal = b.add(r_bal, amt);
        b.range_check(r_new_bal, 63);
        let mut v = r_pk.to_vec(); v.push(r_new_bal); v.push(r_nonce);
        let r_new = hash_t(&mut b, v);
        cur = root_from(&mut b, r_new, &r_bits, &r_sib);
        fee_total = b.add(fee_total, fee);
        pays.push(PayT { s_pk, s_bal, s_nonce, s_bits, s_sib, r_pk, r_bal, r_nonce, r_bits, r_sib, amt, fee, sig });
    }
    b.register_public_inputs(&root0.elements);
    b.register_public_inputs(&cur.elements);
    b.register_public_input(fee_total);
    let cnt = b.constant(F::from_canonical_u64(n as u64));
    b.register_public_input(cnt);
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
    let data = bld.build::<C>();
    Merge { data, a: pa, b: pb }
}

fn size_kb(p: &ProofWithPublicInputs<F, C, D>) -> f64 { p.to_bytes().len() as f64 / 1024.0 }

fn main() -> Result<()> {
    let args: Vec<String> = std::env::args().collect();
    let n: usize = args.get(1).map(|s| s.parse().unwrap()).unwrap_or(16);
    let leaves: usize = args.get(2).map(|s| s.parse().unwrap()).unwrap_or(8);
    let with_sig = args.get(3).map(|s| s != "nosig").unwrap_or(true);
    println!("plonky2 | payments per leaf {n} | leaves {leaves} | signatures {with_sig} | threads {}", std::thread::available_parallelism()?.get());
    let t = Instant::now();
    let prm = ec::params();
    assert!(ec::on_curve(prm.g) && ec::on_curve(prm.h1) && ec::on_curve(prm.h2));
    println!("curve params {:.1}s", t.elapsed().as_secs_f64());
    let mut krng = rand::rngs::StdRng::seed_from_u64(42);

    // accounts
    let mut tree = Tree::new();
    let mut accts: Vec<Acct> = (0..64u64).map(|_| {
        let k: [u64; 4] = krng.r#gen();
        let kb = BigUint::from_slice(&k.iter().flat_map(|w| [*w as u32, (*w >> 32) as u32]).collect::<Vec<u32>>());
        let a = ec::add(ec::mul_fixed(&prm.table, &kb, prm.h1), ec::neg(prm.h1));
        Acct { pk: ec::pk_hash(a), bal: 1_000_000_000, nonce: 0, a, k }
    }).collect();
    let t = Instant::now();
    let idx: Vec<u64> = (0..64u64).map(|i| (i * 2654435761) & ((1u64 << DEPTH) - 1)).collect();
    for (i, a) in accts.iter().enumerate() { tree.set(idx[i], leaf_hash(a)); }

    let t = Instant::now();
    let leaf = build_leaf(n, &prm, with_sig);
    println!("leaf circuit: degree 2^{} ({} gates) | build {:.1}s | peak {:.0} MB", leaf.data.common.degree_bits(), leaf.data.common.degree(), t.elapsed().as_secs_f64(), peak_mb());

    let mut seed = 1u64;
    let mut rnd = || { seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); seed >> 33 };
    let mut proofs = vec![];
    let mut leaf_times = vec![];
    for _ in 0..leaves {
        let mut pw = PartialWitness::new();
        pw.set_hash_target(leaf.root0, tree.root())?;
        for p in &leaf.pays {
            let s = (rnd() % 64) as usize; let mut r = (rnd() % 64) as usize; if r == s { r = (r + 1) % 64; }
            let amt = 1000 + rnd() % 100_000; let fee = amt / 100;
            let sa = accts[s];
            pw.set_target_arr(&p.s_pk, &sa.pk)?; pw.set_target(p.s_bal, F::from_canonical_u64(sa.bal))?; pw.set_target(p.s_nonce, F::from_canonical_u64(sa.nonce))?;
            for l in 0..DEPTH { pw.set_bool_target(p.s_bits[l], (idx[s] >> l) & 1 == 1)?; }
            for (l, h) in tree.path(idx[s]).into_iter().enumerate() { pw.set_hash_target(p.s_sib[l], h)?; }
            pw.set_target(p.amt, F::from_canonical_u64(amt))?; pw.set_target(p.fee, F::from_canonical_u64(fee))?;
            if let Some(st) = &p.sig {
                let mut dv = sa.pk.to_vec(); dv.extend(accts[r].pk); dv.push(F::from_canonical_u64(amt)); dv.push(F::from_canonical_u64(fee)); dv.push(F::from_canonical_u64(sa.nonce));
                let msg = PoseidonHash::hash_no_pad(&dv).elements;
                let kb = BigUint::from_slice(&sa.k.iter().flat_map(|w| [*w as u32, (*w >> 32) as u32]).collect::<Vec<u32>>());
                let rw: [u64; 4] = krng.r#gen();
                let rb = BigUint::from_slice(&rw.iter().flat_map(|w| [*w as u32, (*w >> 32) as u32]).collect::<Vec<u32>>());
                let rp = ec::add(ec::mul_fixed(&prm.table, &rb, prm.h1), ec::neg(prm.h1));
                let e = ec::challenge(rp, sa.a, msg);
                let sv = &rb + &e * &kb;
                assert!(sv.bits() as usize <= ec::S_BITS);
                ec::set_pt(&mut pw, st.a, sa.a)?; ec::set_pt(&mut pw, st.r, rp)?;
                let corrupt = std::env::var("CORRUPT").is_ok();
                for i in 0..ec::S_BITS { pw.set_bool_target(st.s_bits[i], sv.bit(i as u64) ^ (corrupt && i == 3))?; }
            }
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
    // check the stamp's roots match the real tree
    let root_ok = (0..4).all(|k| fin.public_inputs[4 + k] == tree.root().elements[k]);
    println!("RESULT stamp root matches the account tree: {root_ok} | peak {:.0} MB", peak_mb());
    Ok(())
}
