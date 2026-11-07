// Zen merge benchmark, Nova folding (BN254/Grumpkin cycle, HyperKZG + IPA compressed SNARK).
// Same leaf workload as the Plonky2 benchmark (see p2/src/main.rs): per payment, sender and
// receiver Merkle updates in a depth-32 Poseidon tree (4 paths), a payment digest hash, and range
// checks on balances and the fee rate. Signature checks are not included.
// Folding is sequential: each step proves one leaf and folds it into the running proof (IVC);
// the final compressed SNARK is the block's stamp.
use ff::{Field, PrimeField};
use generic_array::typenum::U2;
use nova_snark::{
    frontend::{
        gadgets::{
            boolean::AllocatedBit,
            poseidon::{Elt, IOPattern, PoseidonConstants, Simplex, Sponge, SpongeAPI, SpongeCircuit, SpongeOp, SpongeTrait, Strength},
        },
        num::AllocatedNum,
        ConstraintSystem, SynthesisError,
    },
    nova::{CompressedSNARK, PublicParams, RecursiveSNARK},
    provider::{Bn256EngineKZG, GrumpkinEngine},
    traits::{circuit::StepCircuit, snark::RelaxedR1CSSNARKTrait, Engine},
};
use std::collections::HashMap;
use std::time::Instant;

#[cfg(not(feature = "pasta"))] type E1 = Bn256EngineKZG;
#[cfg(not(feature = "pasta"))] type E2 = GrumpkinEngine;
#[cfg(not(feature = "pasta"))] type EE1 = nova_snark::provider::hyperkzg::EvaluationEngine<E1>;
#[cfg(feature = "pasta")] type E1 = nova_snark::provider::PallasEngine;
#[cfg(feature = "pasta")] type E2 = nova_snark::provider::VestaEngine;
#[cfg(feature = "pasta")] type EE1 = nova_snark::provider::ipa_pc::EvaluationEngine<E1>;
type EE2 = nova_snark::provider::ipa_pc::EvaluationEngine<E2>;
type S1 = nova_snark::spartan::snark::RelaxedR1CSSNARK<E1, EE1>;
type S2 = nova_snark::spartan::snark::RelaxedR1CSSNARK<E2, EE2>;
type F = <E1 as Engine>::Scalar;
const DEPTH: usize = 32;

fn peak_mb() -> f64 {
    let s = std::fs::read_to_string("/proc/self/status").unwrap_or_default();
    s.lines().find(|l| l.starts_with("VmHWM:")).map(|l| l.split_whitespace().nth(1).unwrap().parse::<f64>().unwrap() / 1024.0).unwrap_or(0.0)
}
fn consts() -> PoseidonConstants<F, U2> { Sponge::<F, U2>::api_constants(Strength::Standard) }
fn hash_native(pc: &PoseidonConstants<F, U2>, xs: &[F]) -> F {
    let n = xs.len() as u32;
    let mut s = Sponge::new_with_constants(pc, Simplex);
    let acc = &mut ();
    s.start(IOPattern(vec![SpongeOp::Absorb(n), SpongeOp::Squeeze(1)]), None, acc);
    SpongeAPI::absorb(&mut s, n, xs, acc);
    let o = SpongeAPI::squeeze(&mut s, 1, acc);
    s.finish(acc).unwrap();
    o[0]
}
fn hash_c<CS: ConstraintSystem<F>>(mut cs: CS, pc: &PoseidonConstants<F, U2>, xs: &[AllocatedNum<F>]) -> Result<AllocatedNum<F>, SynthesisError> {
    let n = xs.len() as u32;
    let elts: Vec<Elt<F>> = xs.iter().map(|x| Elt::Allocated(x.clone())).collect();
    let out = {
        let mut sponge = SpongeCircuit::new_with_constants(pc, Simplex);
        let acc = &mut cs.namespace(|| "sponge");
        sponge.start(IOPattern(vec![SpongeOp::Absorb(n), SpongeOp::Squeeze(1)]), None, acc);
        SpongeAPI::absorb(&mut sponge, n, &elts, acc);
        let o = SpongeAPI::squeeze(&mut sponge, 1, acc);
        sponge.finish(acc).unwrap();
        o
    };
    Elt::ensure_allocated(&out[0], &mut cs.namespace(|| "out"))
}

#[derive(Clone, Copy)]
struct Acct { pk: [F; 4], bal: u64, nonce: u64 }
fn leaf_native(pc: &PoseidonConstants<F, U2>, a: &Acct) -> F {
    let mut v = a.pk.to_vec(); v.push(F::from(a.bal)); v.push(F::from(a.nonce)); hash_native(pc, &v)
}
struct Tree { nodes: HashMap<(usize, u64), F>, defaults: Vec<F> }
impl Tree {
    fn new(pc: &PoseidonConstants<F, U2>) -> Self {
        let mut d = vec![hash_native(pc, &[F::ZERO; 6])];
        for i in 0..DEPTH { let x = d[i]; d.push(hash_native(pc, &[x, x])); }
        Tree { nodes: HashMap::new(), defaults: d }
    }
    fn get(&self, l: usize, i: u64) -> F { *self.nodes.get(&(l, i)).unwrap_or(&self.defaults[l]) }
    fn root(&self) -> F { self.get(DEPTH, 0) }
    fn path(&self, idx: u64) -> Vec<F> { (0..DEPTH).map(|l| self.get(l, (idx >> l) ^ 1)).collect() }
    fn set(&mut self, pc: &PoseidonConstants<F, U2>, idx: u64, leaf: F) {
        self.nodes.insert((0, idx), leaf);
        let mut cur = leaf;
        for l in 0..DEPTH {
            let i = idx >> l; let sib = self.get(l, i ^ 1);
            cur = if i & 1 == 0 { hash_native(pc, &[cur, sib]) } else { hash_native(pc, &[sib, cur]) };
            self.nodes.insert((l + 1, i >> 1), cur);
        }
    }
}

#[derive(Clone)]
struct PayW { s: Acct, s_idx: u64, s_sib: Vec<F>, r: Acct, r_idx: u64, r_sib: Vec<F>, amt: u64, fee: u64 }
#[derive(Clone)]
struct Leaf { pays: Vec<PayW> }

fn alloc<CS: ConstraintSystem<F>>(mut cs: CS, v: F) -> Result<AllocatedNum<F>, SynthesisError> { AllocatedNum::alloc(cs.namespace(|| "a"), || Ok(v)) }
fn range<CS: ConstraintSystem<F>>(mut cs: CS, x: &AllocatedNum<F>, v: u64, bits: usize) -> Result<(), SynthesisError> {
    let mut lc = nova_snark::frontend::LinearCombination::zero();
    let mut c = F::ONE;
    for i in 0..bits {
        let b = AllocatedBit::alloc(cs.namespace(|| format!("b{i}")), Some((v >> i) & 1 == 1))?;
        lc = lc + (c, b.get_variable());
        c = c.double();
    }
    cs.enforce(|| "sum", |_| lc, |l| l + CS::one(), |l| l + x.get_variable());
    Ok(())
}
// root from leaf, bits of idx and siblings
fn root_c<CS: ConstraintSystem<F>>(mut cs: CS, pc: &PoseidonConstants<F, U2>, leaf: AllocatedNum<F>, idx: &[AllocatedBit], sibs: &[AllocatedNum<F>]) -> Result<AllocatedNum<F>, SynthesisError> {
    let mut cur = leaf;
    for l in 0..DEPTH {
        let b = &idx[l]; let s = &sibs[l];
        let bv = b.get_value().unwrap_or(false);
        let (cv, sv) = (cur.get_value().unwrap_or(F::ZERO), s.get_value().unwrap_or(F::ZERO));
        let left = alloc(cs.namespace(|| format!("l{l}")), if bv { sv } else { cv })?;
        let right = alloc(cs.namespace(|| format!("r{l}")), if bv { cv } else { sv })?;
        // left - cur = b * (s - cur);  right = cur + s - left
        cs.enforce(|| format!("sel{l}"), |lc| lc + b.get_variable(), |lc| lc + s.get_variable() - cur.get_variable(), |lc| lc + left.get_variable() - cur.get_variable());
        cs.enforce(|| format!("rgt{l}"), |lc| lc + CS::one(), |lc| lc + cur.get_variable() + s.get_variable() - left.get_variable(), |lc| lc + right.get_variable());
        cur = hash_c(cs.namespace(|| format!("h{l}")), pc, &[left, right])?;
    }
    Ok(cur)
}

impl StepCircuit<F> for Leaf {
    fn arity(&self) -> usize { 3 }
    fn synthesize<CS: ConstraintSystem<F>>(&self, cs: &mut CS, z: &[AllocatedNum<F>]) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
        let pc = consts();
        let mut root = z[0].clone();
        let mut fee_total = z[1].clone();
        for (i, p) in self.pays.iter().enumerate() {
            let mut cs = cs.namespace(|| format!("pay{i}"));
            let spk: Vec<AllocatedNum<F>> = (0..4).map(|k| alloc(cs.namespace(|| format!("spk{k}")), p.s.pk[k])).collect::<Result<_, _>>()?;
            let rpk: Vec<AllocatedNum<F>> = (0..4).map(|k| alloc(cs.namespace(|| format!("rpk{k}")), p.r.pk[k])).collect::<Result<_, _>>()?;
            let sbal = alloc(cs.namespace(|| "sbal"), F::from(p.s.bal))?;
            let snon = alloc(cs.namespace(|| "snon"), F::from(p.s.nonce))?;
            let rbal = alloc(cs.namespace(|| "rbal"), F::from(p.r.bal))?;
            let rnon = alloc(cs.namespace(|| "rnon"), F::from(p.r.nonce))?;
            let amt = alloc(cs.namespace(|| "amt"), F::from(p.amt))?;
            let fee = alloc(cs.namespace(|| "fee"), F::from(p.fee))?;
            let sbits: Vec<AllocatedBit> = (0..DEPTH).map(|l| AllocatedBit::alloc(cs.namespace(|| format!("sb{l}")), Some((p.s_idx >> l) & 1 == 1))).collect::<Result<_, _>>()?;
            let rbits: Vec<AllocatedBit> = (0..DEPTH).map(|l| AllocatedBit::alloc(cs.namespace(|| format!("rb{l}")), Some((p.r_idx >> l) & 1 == 1))).collect::<Result<_, _>>()?;
            let ssib: Vec<AllocatedNum<F>> = (0..DEPTH).map(|l| alloc(cs.namespace(|| format!("ss{l}")), p.s_sib[l])).collect::<Result<_, _>>()?;
            let rsib: Vec<AllocatedNum<F>> = (0..DEPTH).map(|l| alloc(cs.namespace(|| format!("rs{l}")), p.r_sib[l])).collect::<Result<_, _>>()?;
            // sender old leaf in root
            let mut v = spk.clone(); v.push(sbal.clone()); v.push(snon.clone());
            let s_old = hash_c(cs.namespace(|| "sold"), &pc, &v)?;
            let r0 = root_c(cs.namespace(|| "sp0"), &pc, s_old, &sbits, &ssib)?;
            cs.enforce(|| "root0", |lc| lc + r0.get_variable(), |lc| lc + CS::one(), |lc| lc + root.get_variable());
            // checks
            range(cs.namespace(|| "ramt"), &amt, p.amt, 62)?;
            range(cs.namespace(|| "rfee"), &fee, p.fee, 62)?;
            let nb = p.s.bal - p.amt - p.fee;
            let newbal = alloc(cs.namespace(|| "newbal"), F::from(nb))?;
            cs.enforce(|| "nb", |lc| lc + CS::one(), |lc| lc + sbal.get_variable() - amt.get_variable() - fee.get_variable(), |lc| lc + newbal.get_variable());
            range(cs.namespace(|| "rnb"), &newbal, nb, 62)?;
            let spend = p.amt + p.fee;
            let lo_v = p.fee * 10_000 - spend;
            let lo = alloc(cs.namespace(|| "lo"), F::from(lo_v))?;
            cs.enforce(|| "lo", |lc| lc + CS::one(), |lc| lc + (F::from(9_999u64), fee.get_variable()) - amt.get_variable(), |lc| lc + lo.get_variable());
            range(cs.namespace(|| "rlo"), &lo, lo_v, 62)?;
            let hi_v = 6 * spend - 100 * p.fee;
            let hi = alloc(cs.namespace(|| "hi"), F::from(hi_v))?;
            cs.enforce(|| "hi", |lc| lc + CS::one(), |lc| lc + (F::from(6u64), amt.get_variable()) - (F::from(94u64), fee.get_variable()), |lc| lc + hi.get_variable());
            range(cs.namespace(|| "rhi"), &hi, hi_v, 62)?;
            let nn = alloc(cs.namespace(|| "nn"), F::from(p.s.nonce + 1))?;
            cs.enforce(|| "nn", |lc| lc + CS::one(), |lc| lc + snon.get_variable() + CS::one(), |lc| lc + nn.get_variable());
            // digest
            let mut dv = spk.clone(); dv.extend(rpk.clone()); dv.push(amt.clone()); dv.push(fee.clone()); dv.push(snon.clone());
            let _d = hash_c(cs.namespace(|| "digest"), &pc, &dv)?;
            // sender new root
            let mut v = spk.clone(); v.push(newbal.clone()); v.push(nn.clone());
            let s_new = hash_c(cs.namespace(|| "snew"), &pc, &v)?;
            let mid = root_c(cs.namespace(|| "sp1"), &pc, s_new, &sbits, &ssib)?;
            // receiver
            let mut v = rpk.clone(); v.push(rbal.clone()); v.push(rnon.clone());
            let r_old = hash_c(cs.namespace(|| "rold"), &pc, &v)?;
            let r1 = root_c(cs.namespace(|| "rp0"), &pc, r_old, &rbits, &rsib)?;
            cs.enforce(|| "mid", |lc| lc + r1.get_variable(), |lc| lc + CS::one(), |lc| lc + mid.get_variable());
            let rnb = alloc(cs.namespace(|| "rnb"), F::from(p.r.bal + p.amt))?;
            cs.enforce(|| "rnbc", |lc| lc + CS::one(), |lc| lc + rbal.get_variable() + amt.get_variable(), |lc| lc + rnb.get_variable());
            range(cs.namespace(|| "rrnb"), &rnb, p.r.bal + p.amt, 63)?;
            let mut v = rpk.clone(); v.push(rnb.clone()); v.push(rnon.clone());
            let r_new = hash_c(cs.namespace(|| "rnew"), &pc, &v)?;
            root = root_c(cs.namespace(|| "rp1"), &pc, r_new, &rbits, &rsib)?;
            let ft = alloc(cs.namespace(|| "ft"), fee_total.get_value().unwrap_or(F::ZERO) + F::from(p.fee))?;
            cs.enforce(|| "ftc", |lc| lc + CS::one(), |lc| lc + fee_total.get_variable() + fee.get_variable(), |lc| lc + ft.get_variable());
            fee_total = ft;
        }
        let n = self.pays.len() as u64;
        let cnt = alloc(cs.namespace(|| "cnt"), z[2].get_value().unwrap_or(F::ZERO) + F::from(n))?;
        cs.enforce(|| "cntc", |lc| lc + CS::one(), |lc| lc + z[2].get_variable() + (F::from(n), CS::one()), |lc| lc + cnt.get_variable());
        Ok(vec![root, fee_total, cnt])
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n: usize = args.get(1).map(|s| s.parse().unwrap()).unwrap_or(16);
    let steps: usize = args.get(2).map(|s| s.parse().unwrap()).unwrap_or(8);
    println!("nova [{}] | payments per leaf {n} | leaves (folding steps) {steps}", if cfg!(feature = "pasta") { "Pallas/Vesta + IPA, no trusted setup" } else { "BN254/Grumpkin + HyperKZG (needs powers-of-tau)" });
    let pc = consts();
    let mut tree = Tree::new(&pc);
    let mut accts: Vec<Acct> = (0..64u64).map(|i| Acct { pk: [F::from(i + 1), F::from(7u64), F::from(i * 3), F::ONE], bal: 1_000_000_000, nonce: 0 }).collect();
    let idx: Vec<u64> = (0..64u64).map(|i| (i * 2654435761) & ((1u64 << DEPTH) - 1)).collect();
    for (i, a) in accts.iter().enumerate() { let h = leaf_native(&pc, a); tree.set(&pc, idx[i], h); }
    let root0 = tree.root();
    let mut seed = 1u64;
    let mut rnd = || { seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); seed >> 33 };
    let mut leaves = vec![];
    for _ in 0..steps {
        let mut pays = vec![];
        for _ in 0..n {
            let s = (rnd() % 64) as usize; let mut r = (rnd() % 64) as usize; if r == s { r = (r + 1) % 64; }
            let amt = 1000 + rnd() % 100_000; let fee = amt / 100;
            let s_sib = tree.path(idx[s]); let sa = accts[s];
            accts[s].bal -= amt + fee; accts[s].nonce += 1; let h = leaf_native(&pc, &accts[s]); tree.set(&pc, idx[s], h);
            let r_sib = tree.path(idx[r]); let ra = accts[r];
            accts[r].bal += amt; let h = leaf_native(&pc, &accts[r]); tree.set(&pc, idx[r], h);
            pays.push(PayW { s: sa, s_idx: idx[s], s_sib, r: ra, r_idx: idx[r], r_sib, amt, fee });
        }
        leaves.push(Leaf { pays });
    }
    let t = Instant::now();
    let pp = PublicParams::<E1, E2, Leaf>::setup(&leaves[0], &*S1::ck_floor(), &*S2::ck_floor()).unwrap();
    println!("setup {:.1}s | constraints per step: primary {} secondary {} | peak {:.0} MB", t.elapsed().as_secs_f64(), pp.num_constraints().0, pp.num_constraints().1, peak_mb());
    let z0 = vec![root0, F::ZERO, F::ZERO];
    let mut rs = RecursiveSNARK::<E1, E2, Leaf>::new(&pp, &leaves[0], &z0).unwrap();
    let mut times = vec![];
    for (i, leaf) in leaves.iter().enumerate() {
        let t = Instant::now();
        rs.prove_step(&pp, leaf).unwrap();
        let dt = t.elapsed().as_secs_f64();
        times.push(dt);
        println!("  fold step {i}: {:.2}s", dt);
    }
    let avg = times[1..].iter().sum::<f64>() / (times.len() - 1).max(1) as f64;
    println!("RESULT fold: {:.2}s per leaf (steps 2..{}) | peak {:.0} MB", avg, steps, peak_mb());
    let t = Instant::now();
    let zn = rs.verify(&pp, steps, &z0).unwrap();
    println!("RESULT recursive verify: {:.0} ms | root matches tree: {} | fees {:?}", t.elapsed().as_secs_f64() * 1000.0, zn[0] == tree.root(), zn[1]);
    let t = Instant::now();
    let (pk, vk) = CompressedSNARK::<_, _, _, S1, S2>::setup(&pp).unwrap();
    let st = t.elapsed().as_secs_f64();
    let t = Instant::now();
    let cs = CompressedSNARK::<_, _, _, S1, S2>::prove(&pp, &pk, &rs).unwrap();
    let pt = t.elapsed().as_secs_f64();
    let bytes = bincode::serde::encode_to_vec(&cs, bincode::config::legacy()).unwrap();
    let t = Instant::now();
    cs.verify(&vk, steps, &z0).unwrap();
    let vt = t.elapsed().as_secs_f64() * 1000.0;
    println!("RESULT stamp (compressed SNARK): setup {:.1}s | prove {:.1}s | size {:.1} KB | verify {:.0} ms | {} payments | peak {:.0} MB", st, pt, bytes.len() as f64 / 1024.0, vt, n * steps, peak_mb());
}
