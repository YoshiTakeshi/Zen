// Zen merge benchmark, Groth16 (BLS12-381, bellperson) + SnarkPack aggregation.
// Same leaf workload as the Plonky2 and Nova benchmarks (Poseidon sponge with rate 2, as in Nova).
// Each leaf is its own Groth16 proof (192 bytes on BLS12-381); SnarkPack then aggregates N leaf proofs
// into one proof of size O(log N). The verifier also receives every leaf's public inputs and checks
// that the roots chain (leaf i's root after = leaf i+1's root before).
use bellpepper_core::{num::AllocatedNum, boolean::AllocatedBit, Circuit, ConstraintSystem, SynthesisError};
use bellperson::groth16::{aggregate::{aggregate_proofs, setup_fake_srs, verify_aggregate_proof, AggregateProof, AggregateVersion}, create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof, Proof};
use blstrs::{Bls12, Scalar as F};
use ff::{Field, PrimeField};
use generic_array::typenum::U2;
use neptune::{circuit2::Elt, poseidon::PoseidonConstants, sponge::{api::{IOPattern, SpongeAPI, SpongeOp}, circuit::SpongeCircuit, vanilla::{Mode::Simplex, Sponge, SpongeTrait}}, Strength};
use rand::SeedableRng;
use std::collections::HashMap;
use std::time::Instant;
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
    out[0].ensure_allocated(&mut cs.namespace(|| "out"), true)
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

fn alloc<CS: ConstraintSystem<F>>(mut cs: CS, v: F) -> Result<AllocatedNum<F>, SynthesisError> { AllocatedNum::alloc(cs.namespace(|| "a"), || Ok(v)) }
fn range<CS: ConstraintSystem<F>>(mut cs: CS, x: &AllocatedNum<F>, v: u64, bits: usize) -> Result<(), SynthesisError> {
    let mut lc = bellpepper_core::LinearCombination::zero();
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

#[derive(Clone)]
struct LeafC { root0: F, pays: Vec<PayW> }
impl Circuit<F> for LeafC {
    fn synthesize<CS: ConstraintSystem<F>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        let r0 = AllocatedNum::alloc(cs.namespace(|| "root0"), || Ok(self.root0))?;
        r0.inputize(cs.namespace(|| "in_root0"))?;
        let zf = AllocatedNum::alloc(cs.namespace(|| "zero_fee"), || Ok(F::ZERO))?;
        cs.enforce(|| "zf", |lc| lc + zf.get_variable(), |lc| lc + CS::one(), |lc| lc);
        let zc = AllocatedNum::alloc(cs.namespace(|| "zero_cnt"), || Ok(F::ZERO))?;
        cs.enforce(|| "zc", |lc| lc + zc.get_variable(), |lc| lc + CS::one(), |lc| lc);
        let z = vec![r0, zf, zc];
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
        root.inputize(cs.namespace(|| "in_root1"))?;
        fee_total.inputize(cs.namespace(|| "in_fee"))?;
        cnt.inputize(cs.namespace(|| "in_cnt"))?;
        Ok(())
    }
}


fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n: usize = args.get(1).map(|s| s.parse().unwrap()).unwrap_or(16);
    let leaves_n: usize = args.get(2).map(|s| s.parse().unwrap()).unwrap_or(8);
    println!("groth16 + snarkpack (BLS12-381) | payments per leaf {n} | leaves {leaves_n}");
    let pc = consts();
    let mut tree = Tree::new(&pc);
    let mut accts: Vec<Acct> = (0..64u64).map(|i| Acct { pk: [F::from(i + 1), F::from(7u64), F::from(i * 3), F::ONE], bal: 1_000_000_000, nonce: 0 }).collect();
    let idx: Vec<u64> = (0..64u64).map(|i| (i * 2654435761) & ((1u64 << DEPTH) - 1)).collect();
    for (i, a) in accts.iter().enumerate() { let h = leaf_native(&pc, a); tree.set(&pc, idx[i], h); }
    let mut seed = 1u64;
    let mut rnd = || { seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); seed >> 33 };
    let mut circuits = vec![];
    for _ in 0..leaves_n {
        let root0 = tree.root();
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
        circuits.push(LeafC { root0, pays });
    }
    let mut rng = rand_chacha::ChaCha20Rng::seed_from_u64(7);
    let t = Instant::now();
    let params = generate_random_parameters::<Bls12, _, _>(circuits[0].clone(), &mut rng).unwrap();
    let pvk = prepare_verifying_key(&params.vk);
    println!("setup (per-circuit, insecure test ceremony) {:.1}s | peak {:.0} MB", t.elapsed().as_secs_f64(), peak_mb());
    let mut proofs: Vec<Proof<Bls12>> = vec![];
    let mut statements: Vec<Vec<F>> = vec![];
    let mut times = vec![];
    for c in circuits.iter() {
        let t = Instant::now();
        let p = create_random_proof(c.clone(), &params, &mut rng).unwrap();
        times.push(t.elapsed().as_secs_f64());
        proofs.push(p);
    }
    // statements: recompute public inputs natively
    let mut fee_root = vec![];
    for c in circuits.iter() {
        let mut ft = 0u64; for p in &c.pays { ft += p.fee; }
        fee_root.push(ft);
    }
    for (i, c) in circuits.iter().enumerate() {
        let after = if i + 1 < circuits.len() { circuits[i + 1].root0 } else { tree.root() };
        statements.push(vec![c.root0, after, F::from(fee_root[i]), F::from(n as u64)]);
    }
    let mut buf = vec![]; proofs[0].write(&mut buf).unwrap();
    let t = Instant::now();
    let ok = verify_proof(&pvk, &proofs[0], &statements[0]).unwrap();
    let vt = t.elapsed().as_secs_f64() * 1000.0;
    println!("RESULT leaf: prove {:.2}s (avg of {}) | proof {} bytes | verify {:.1} ms ({}) | peak {:.0} MB", times.iter().sum::<f64>() / times.len() as f64, times.len(), buf.len(), vt, ok, peak_mb());
    let t = Instant::now();
    let srs = setup_fake_srs::<Bls12, _>(&mut rng, leaves_n.next_power_of_two());
    let (spk, svk) = srs.specialize(leaves_n.next_power_of_two());
    println!("aggregation SRS (universal, insecure test setup) {:.1}s", t.elapsed().as_secs_f64());
    let t = Instant::now();
    let agg = aggregate_proofs::<Bls12>(&spk, b"zen", &proofs, AggregateVersion::V2).unwrap();
    let at = t.elapsed().as_secs_f64();
    let mut abuf = vec![]; agg.write(&mut abuf).unwrap();
    let t = Instant::now();
    let chain_ok = (0..leaves_n - 1).all(|i| statements[i][1] == statements[i + 1][0]);
    let vok = verify_aggregate_proof(&svk, &pvk, &mut rng, &statements, &agg, b"zen", AggregateVersion::V2).unwrap();
    let avt = t.elapsed().as_secs_f64() * 1000.0;
    let _ = AggregateProof::<Bls12>::read(std::io::Cursor::new(&abuf)).unwrap();
    println!("RESULT aggregate of {} leaves: prove {:.2}s | proof {:.1} KB | verify {:.0} ms ({} , roots chain {}) | peak {:.0} MB", leaves_n, at, abuf.len() as f64 / 1024.0, avt, vok, chain_ok, peak_mb());

    // scaling: aggregate copies of the real proofs (valid proofs; same statements repeated)
    for &m in &[64usize, 256, 1024] {
        let srs = setup_fake_srs::<Bls12, _>(&mut rng, m);
        let (spk, svk) = srs.specialize(m);
        let ps: Vec<Proof<Bls12>> = (0..m).map(|i| proofs[i % leaves_n].clone()).collect();
        let st: Vec<Vec<F>> = (0..m).map(|i| statements[i % leaves_n].clone()).collect();
        let t = Instant::now();
        let agg = aggregate_proofs::<Bls12>(&spk, b"zen", &ps, AggregateVersion::V2).unwrap();
        let at = t.elapsed().as_secs_f64();
        let mut abuf = vec![]; agg.write(&mut abuf).unwrap();
        let t = Instant::now();
        let vok = verify_aggregate_proof(&svk, &pvk, &mut rng, &st, &agg, b"zen", AggregateVersion::V2).unwrap();
        println!("RESULT aggregate of {} proofs: prove {:.2}s | proof {:.1} KB | verify {:.0} ms ({}) | peak {:.0} MB", m, at, abuf.len() as f64 / 1024.0, t.elapsed().as_secs_f64() * 1000.0, vok, peak_mb());
    }
}
