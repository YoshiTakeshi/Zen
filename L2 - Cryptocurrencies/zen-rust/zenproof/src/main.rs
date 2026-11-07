// Zen block proof, Plonky2 (FRI, no trusted setup, recursion), version 3: the leaf is split in two.
//   1. Signature leaf (minter, stateless): signatures, fee band and floors over a group of signed
//      payments; any number of minters prove at once without knowing the state or each other.
//   2. State leaf (block builder): verifies one signature leaf, applies its payments to the account
//      tree in order (skipping any that no longer fit), and outputs the version-2 public values.
// Then one universal merge circuit (state leaf and merge proofs share one circuit shape), so any
// number of leaves ends in the same final circuit and the same Groth16 key.
// (Version 2 header follows.)
// (Original header follows.)
//
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
use plonky2::plonk::circuit_data::{CircuitConfig, CircuitData, CommonCircuitData, VerifierCircuitTarget, VerifierOnlyCircuitData};
use plonky2::plonk::proof::ProofWithPublicInputsTarget;
use plonky2::gates::gate::GateRef;
use plonky2::gates::noop::NoopGate;
use plonky2::plonk::config::{GenericConfig, Hasher, PoseidonGoldilocksConfig};
use plonky2::plonk::proof::ProofWithPublicInputs;
use std::collections::HashMap;
use std::time::Instant;
mod ec;
mod bn;
mod bn_consts;
mod blockdata;
mod mint;
mod seal;
mod node;
mod store;
mod api;
mod p2p;
mod prover;
mod reading;
mod reward;
mod reward_tables;
mod groth16;
mod opcirc;
mod chancirc;
mod commoncirc;
mod ordercirc;
mod factorycirc;
#[cfg(test)]
mod soundness;
mod tx;
mod walletweb;
mod mempool;
mod netconf;
mod crosschain;
mod locks;
mod channel;
mod route;
mod market;
mod transport;
mod testnet;
use blockdata::{BlockEntry, LeafData, NONCE_SHIFT};
use num_bigint::BigUint;
use rand::{Rng, SeedableRng};

const D: usize = 2;
type C = PoseidonGoldilocksConfig;
type F = <C as GenericConfig<D>>::F;
pub const DEPTH: usize = 32;

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
/// An account leaf: address, balance, nonce, then the five numbers of "each gram counts once":
///   rest  = rested balance (unmoved for REST_DAYS), the rest of the balance is fresh
///   used  = rested money already counted toward S in period `up`
///   fd    = day of the last receipt (fresh money matures REST_DAYS after it)
///   rd    = day from which the rested money counts as aged (coin-days)
///   up    = period (REST_DAYS-day block of days) that `used` belongs to
struct Acct { pk: [F; 4], bal: u64, nonce: u64, rest: u64, used: u64, fd: u64, rd: u64, up: u64, a: ec::P, k: [u64; 4] }
impl Acct {
    /// a brand-new account at an address: nothing in it, nothing rested
    fn blank(pk: [F; 4], nonce: u64, like: &Acct) -> Acct { Acct { pk, bal: 0, nonce, rest: 0, used: 0, fd: 0, rd: 0, up: 0, ..*like } }
}
fn leaf_hash(a: &Acct) -> HashOut<F> {
    let mut v = a.pk.to_vec();
    v.push(F::from_canonical_u64(a.bal));
    v.push(F::from_canonical_u64(a.nonce));
    for x in [a.rest, a.used, a.fd, a.rd, a.up] { v.push(F::from_canonical_u64(x)); }
    PoseidonHash::hash_no_pad(&v)
}

#[derive(Clone)]
struct Tree { nodes: HashMap<(usize, u64), HashOut<F>>, defaults: Vec<HashOut<F>> }
impl Tree {
    fn new() -> Self {
        let mut defaults = vec![PoseidonHash::hash_no_pad(&[F::ZERO; 11])];
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
        // (left, right) = bit ? (sibling, current) : (current, sibling), in three arithmetic operations per pair
        let (mut lo, mut hi) = (Vec::with_capacity(4), Vec::with_capacity(4));
        for k in 0..4 {
            let diff = b.sub(sibs[l].elements[k], cur.elements[k]);
            lo.push(b.arithmetic(F::ONE, F::ONE, bits[l].target, diff, cur.elements[k]));
            hi.push(b.arithmetic(-F::ONE, F::ONE, bits[l].target, diff, sibs[l].elements[k]));
        }
        let mut v = lo; v.extend(hi);
        cur = hash_t(b, v);
    }
    cur
}
fn empty_leaf() -> HashOut<F> { PoseidonHash::hash_no_pad(&[F::ZERO; 11]) }
/// chain ids: 1 = Golden Yen, 2 = Silver Ken, 3 = Bronze Jen (this benchmark)
const CHAIN_ID: u64 = 3;
/// public values of every leaf, merge and stamp: root before (4), root after (4), fee total, count,
/// data hash (4), S (base units per coin), block height
const NPI: usize = 16;
/// verifier-data public values after them (circuit digest 4 + constants cap 16 x 4)
const VDPI: usize = 68;

fn connect_hash_if(b: &mut CircuitBuilder<F, D>, en: BoolTarget, x: HashOutTarget, y: HashOutTarget) {
    for k in 0..4 { cond_eq(b, en, x.elements[k], y.elements[k]); }
}
/// x == y when c = 1
fn cond_eq(b: &mut CircuitBuilder<F, D>, c: BoolTarget, x: Target, y: Target) { let d = b.sub(x, y); let m = b.mul(d, c.target); b.assert_zero(m); }
/// c = 1 implies x = 0
fn imply_zero(b: &mut CircuitBuilder<F, D>, c: BoolTarget, x: Target) { let m = b.mul(x, c.target); b.assert_zero(m); }
fn select_hash_c(b: &mut CircuitBuilder<F, D>, c: BoolTarget, x: HashOut<F>, y: HashOutTarget) -> HashOutTarget {
    HashOutTarget { elements: core::array::from_fn(|k| { let xc = b.constant(x.elements[k]); b.select(c, xc, y.elements[k]) }) }
}
/// x >= y for x, y < 2^62
fn ge62(b: &mut CircuitBuilder<F, D>, x: Target, y: Target) -> BoolTarget {
    let d = b.sub(x, y);
    let t = b.add_const(d, F::from_canonical_u64(1 << 62));
    let bits = b.split_le(t, 63);
    bits[62]
}
/// the circuit twin of blockdata::settle: fresh money matures after REST_DAYS, `used` restarts in a new period
fn settle_t(b: &mut CircuitBuilder<F, D>, bal: Target, rest: Target, used: Target, fd: Target, rd: Target, up: Target, d: Target, p: Target)
    -> (Target, Target, Target, Target) {
    let zero = b.zero();
    let eq = b.is_equal(bal, rest);
    let fresh_nz = b.not(eq);
    let due_day = b.add_const(fd, F::from_canonical_u64(blockdata::REST_DAYS));
    let due = ge62(b, d, due_day);
    let mat = b.and(fresh_nz, due);
    let rest1 = b.select(mat, bal, rest);
    let rd1 = b.select(mat, fd, rd);
    let same = b.is_equal(up, p);
    let used1 = b.select(same, used, zero);
    (rest1, used1, rd1, p)
}
fn set_peg(pw: &mut PartialWitness<F>, t: &[Target; 5], a: &Acct) -> Result<()> {
    for (t, v) in t.iter().zip([a.rest, a.used, a.fd, a.rd, a.up]) { pw.set_target(*t, F::from_canonical_u64(v))?; }
    Ok(())
}
fn pad_to(b: &mut CircuitBuilder<F, D>, degree_bits: usize) { while b.num_gates() <= (1usize << degree_bits) / 2 { b.add_gate(NoopGate, vec![]); } }

/// signed message: Poseidon(chain id, sender, receiver, amount, fee, nonce, close)
fn msg_native(s_pk: &[F; 4], r_pk: &[F; 4], amt: u64, fee: u64, nonce: u64, close: bool) -> [F; 4] {
    let mut v = vec![F::from_canonical_u64(CHAIN_ID)]; v.extend(s_pk); v.extend(r_pk);
    v.extend([F::from_canonical_u64(amt), F::from_canonical_u64(fee), F::from_canonical_u64(nonce), F::from_bool(close)]);
    PoseidonHash::hash_no_pad(&v).elements
}
/// signed-payment entries per slot, hashed by both leaves: [en, sender x4, receiver x4, amount, fee, nonce, close]
const SIG_ENTRY: usize = 13;
fn sig_hash_native(slots: usize, pays: &[&Pay], prover: &[F; 4]) -> HashOut<F> {
    let mut v = vec![];
    for p in pays {
        v.push(F::ONE); v.extend(p.s_pk); v.extend(p.r_pk);
        v.extend([F::from_canonical_u64(p.amt), F::from_canonical_u64(p.fee), F::from_canonical_u64(p.nonce), F::from_bool(p.close)]);
    }
    v.resize(SIG_ENTRY * slots, F::ZERO);
    v.extend(prover);
    PoseidonHash::hash_no_pad(&v)
}

// ------------------------------------------------------------------ 1. signature leaf (minter)
// Stateless: it knows nothing about balances or the tree, so any number of minters can prove leaves
// at the same time from the waiting payments. It checks, for each slot: the signature over the
// chain-tagged message, amount and fee < 2^62, the fee band (0.01%..6%), the floors in coins
// (amount >= S/6, fee >= S/100), real payments first. Public values: the hash of its signed
// payments and the minter's address (sig hash, 4) and S.
struct SigSlotT { en: BoolTarget, s_pk: [Target; 4], r_pk: [Target; 4], amt: Target, fee: Target, nonce: Target, close: BoolTarget, sig: ec::SigT }
struct SigCircuit { data: CircuitData<F, C, D>, s_t: Target, prover: [Target; 4], slots: Vec<SigSlotT> }

fn build_sig(n: usize, prm: &ec::Params) -> SigCircuit {
    let mut b = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());
    ec::dbladd_reset();
    let s_t = b.add_virtual_target(); b.range_check(s_t, 62);
    let prover: [Target; 4] = core::array::from_fn(|_| b.add_virtual_target());
    let ten_k = b.constant(F::from_canonical_u64(10_000));
    let hundred = b.constant(F::from_canonical_u64(100));
    let six = b.constant(F::from_canonical_u64(6));
    let one = b.one();
    let chain = b.constant(F::from_canonical_u64(CHAIN_ID));
    let mut entries = vec![];
    let mut slots = vec![];
    let mut prev_en: Option<BoolTarget> = None;
    for _ in 0..n {
        let s_pk: [Target; 4] = core::array::from_fn(|_| b.add_virtual_target());
        let r_pk: [Target; 4] = core::array::from_fn(|_| b.add_virtual_target());
        let (amt, fee, nonce) = (b.add_virtual_target(), b.add_virtual_target(), b.add_virtual_target());
        let en = b.add_virtual_bool_target_safe();
        let close = b.add_virtual_bool_target_safe();
        let not_en = b.not(en);
        imply_zero(&mut b, close, not_en.target);
        b.range_check(amt, 62); b.range_check(fee, 62); b.range_check(nonce, 62);
        let spend = b.add(amt, fee);
        let lo = b.mul_sub(fee, ten_k, spend); b.range_check(lo, 62);                    // fee >= 0.01% of amount+fee
        let six_spend = b.mul(six, spend); let hi = b.mul_sub(fee, hundred, six_spend);  // fee <= 6% of amount+fee
        let neg_hi = b.neg(hi); b.range_check(neg_hi, 62);
        let t1 = b.arithmetic(F::from_canonical_u64(6), F::NEG_ONE, amt, one, s_t); let m1 = b.mul(t1, en.target); b.range_check(m1, 62);
        let t2 = b.arithmetic(F::from_canonical_u64(100), F::NEG_ONE, fee, one, s_t); let m2 = b.mul(t2, en.target); b.range_check(m2, 62);
        let mut dv = vec![chain]; dv.extend_from_slice(&s_pk); dv.extend_from_slice(&r_pk); dv.extend([amt, fee, nonce, close.target]);
        let digest = hash_t(&mut b, dv);
        let (sig, pk) = ec::verify_sig(&mut b, prm, digest.elements);
        for k in 0..4 { b.connect(pk[k], s_pk[k]); }
        if let Some(pe) = prev_en { let not_pe = b.not(pe); let bad = b.mul(en.target, not_pe.target); b.assert_zero(bad); }
        prev_en = Some(en);
        entries.push(en.target);
        for v in s_pk.iter().chain(r_pk.iter()).chain([amt, fee, nonce].iter()) { let m = b.mul(*v, en.target); entries.push(m); }
        entries.push(close.target);
        slots.push(SigSlotT { en, s_pk, r_pk, amt, fee, nonce, close, sig });
    }
    ec::dbladd_pad(&mut b, prm);
    entries.extend(prover);
    let h = hash_t(&mut b, entries);
    b.register_public_inputs(&h.elements);
    b.register_public_input(s_t);
    SigCircuit { data: b.build::<C>(), s_t, prover, slots }
}

// ------------------------------------------------------------------ 2. state leaf (block builder)
// Verifies one signature leaf inside it and applies its payments to the account tree, in order.
// Each slot repeats the signed fields as witness; their hash must equal the signature leaf's sig hash,
// so the builder cannot change a payment, its nonce or the minter's address. A signed payment that no
// longer fits the state (spent twice across two minters' leaves, nonce already used, balance gone)
// is SKIPPED: no state change, no fee, not counted, and absent from the block data. Skipping is the
// builder's choice and needs no proof (leaving the whole leaf out would have the same effect).
// Credit slots (version 4): a slot the signature leaf left empty may carry a payout (prover's fee share,
// miner's cut, fee-pool payout, block reward): no sender, no signature, the amount added to the
// receiver's account (created on first receipt). Nodes check that the credits are exactly the payouts
// the consensus rules owe (blockdata::expected_credits); the proof checks they reached the tree.
// Public values: identical to version 2 (root before, root after, fee, count, data hash, S, height,
// then 68 verifier-data values), so the universal merge and every wrap above it are unchanged.
struct StSlotT { en: BoolTarget, skip: BoolTarget, close: BoolTarget, new_r: BoolTarget, cr: BoolTarget,
                 s_pk: [Target; 4], r_pk: [Target; 4], amt: Target, fee: Target, nonce: Target,
                 s_bal: Target, s_peg: [Target; 5], s_bits: Vec<BoolTarget>, s_sib: Vec<HashOutTarget>,
                 r_bal: Target, r_nonce: Target, r_peg: [Target; 5], r_bits: Vec<BoolTarget>, r_sib: Vec<HashOutTarget> }
struct StateCircuit { data: CircuitData<F, C, D>, sig_pt: ProofWithPublicInputsTarget<D>, root0: HashOutTarget, h_t: Target, day: [Target; 4], prover: [Target; 4], slots: Vec<StSlotT> }

fn build_state(n: usize, sig: &CircuitData<F, C, D>, gates: &[GateRef<F, D>], degree_bits: usize) -> StateCircuit {
    let mut b = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());
    for g in gates { b.add_gate_to_gate_set(g.clone()); }
    let sig_pt = b.add_virtual_proof_with_pis(&sig.common);
    let sig_vd = b.constant_verifier_data(&sig.verifier_only);
    b.verify_proof::<C>(&sig_pt, &sig_vd, &sig.common);
    let s_t = sig_pt.public_inputs[4];
    let root0 = b.add_virtual_hash();
    let h_t = b.add_virtual_target(); b.range_check(h_t, 32);
    let prover: [Target; 4] = core::array::from_fn(|_| b.add_virtual_target());
    // the block's day and rest period, from its height: h = BPD d + rem (rem < BPD), d = REST_DAYS p + q (q < REST_DAYS)
    let day: [Target; 4] = core::array::from_fn(|_| b.add_virtual_target());
    let (d_t, rem_t, p_t, q_t) = (day[0], day[1], day[2], day[3]);
    b.range_check(d_t, 32); b.range_check(p_t, 32); b.range_check(rem_t, 10);
    let hh = b.mul_const_add(F::from_canonical_u64(blockdata::BPD), d_t, rem_t); b.connect(hh, h_t);
    let top = b.constant(F::from_canonical_u64(blockdata::BPD - 1));
    let rem_ok = ge62(&mut b, top, rem_t); b.assert_one(rem_ok.target);
    let dd = b.mul_const_add(F::from_canonical_u64(blockdata::REST_DAYS), p_t, q_t); b.connect(dd, d_t);
    { let q1 = b.add_const(q_t, -F::ONE); let q2 = b.add_const(q_t, -F::TWO); let m1 = b.mul(q_t, q1); let m2 = b.mul(m1, q2); b.assert_zero(m2); }
    let empty = empty_leaf();
    let one = b.one();
    let mut cur = root0;
    let mut fee_total = b.zero();
    let mut count = b.zero();
    let mut sig_entries = vec![];
    let mut data_entries = vec![];
    let mut slots = vec![];
    if degree_bits == 0 { println!("state leaf: {} gates before the slots (proof check, day)", b.num_gates()); }
    for si in 0..n {
        let g0 = b.num_gates();
        let s_pk: [Target; 4] = core::array::from_fn(|_| b.add_virtual_target());
        let r_pk: [Target; 4] = core::array::from_fn(|_| b.add_virtual_target());
        let (amt, fee, nonce, s_bal, r_bal, r_nonce) = (b.add_virtual_target(), b.add_virtual_target(), b.add_virtual_target(), b.add_virtual_target(), b.add_virtual_target(), b.add_virtual_target());
        let s_peg: [Target; 5] = core::array::from_fn(|_| b.add_virtual_target());
        let r_peg: [Target; 5] = core::array::from_fn(|_| b.add_virtual_target());
        let s_bits: Vec<BoolTarget> = (0..DEPTH).map(|_| b.add_virtual_bool_target_safe()).collect();
        let r_bits: Vec<BoolTarget> = (0..DEPTH).map(|_| b.add_virtual_bool_target_safe()).collect();
        let s_sib: Vec<HashOutTarget> = (0..DEPTH).map(|_| b.add_virtual_hash()).collect();
        let r_sib: Vec<HashOutTarget> = (0..DEPTH).map(|_| b.add_virtual_hash()).collect();
        let en = b.add_virtual_bool_target_safe();      // a signed payment in this slot (from the signature leaf)
        let skip = b.add_virtual_bool_target_safe();    // the builder leaves it out
        let close = b.add_virtual_bool_target_safe();   // signed: the payment closes its sender
        let new_r = b.add_virtual_bool_target_safe();   // the receiver's slot is empty and gets a new account
        let cr = b.add_virtual_bool_target_safe();      // a credit (payout): no sender, no signature
        imply_zero(&mut b, cr, en.target);              // only in a slot the signature leaf left empty
        let not_en = b.not(en);
        imply_zero(&mut b, skip, not_en.target);
        let not_skip = b.not(skip);
        let ap = b.and(en, not_skip);                   // applied payment
        let rx = BoolTarget::new_unsafe(b.add(ap.target, cr.target));   // the receiver side changes (ap, cr exclusive)
        let not_rx = b.not(rx);
        imply_zero(&mut b, new_r, not_rx.target);
        b.range_check(amt, 62);
        let close_ap = b.and(close, ap);
        // sender: old leaf in the current root; the signed nonce must be the account's nonce
        let mut v = s_pk.to_vec(); v.push(s_bal); v.push(nonce); v.extend(s_peg);
        let s_old = hash_t(&mut b, v);
        let r = root_from(&mut b, s_old, &s_bits, &s_sib);
        connect_hash_if(&mut b, ap, r, cur);
        let spend = b.add(amt, fee);                    // amount and fee < 2^62: checked in the signature leaf
        let new_bal = b.sub(s_bal, spend);
        let nb = b.mul(new_bal, ap.target); b.range_check(nb, 62);
        imply_zero(&mut b, close_ap, new_bal);
        let new_nonce = b.add(nonce, one);
        // each gram counts once: settle, spend fresh money first, count the unused rested money
        let zero = b.zero();
        let (s_r1, s_u1, s_rd1, s_up1) = settle_t(&mut b, s_bal, s_peg[0], s_peg[1], s_peg[2], s_peg[3], s_peg[4], d_t, p_t);
        let sp = b.mul(spend, ap.target);
        let am = b.mul(amt, ap.target);
        let f1 = b.sub(s_bal, s_r1);
        let c1 = ge62(&mut b, sp, f1);
        let from_f = b.select(c1, f1, sp);
        let from_r = b.sub(sp, from_f);
        let s_r2 = b.sub(s_r1, from_r);
        let avail = b.sub(s_r1, s_u1);
        let c2 = ge62(&mut b, am, avail);
        let cnt = b.select(c2, avail, am);
        let usum = b.add(s_u1, cnt);
        let c3 = ge62(&mut b, usum, from_r);
        let ud = b.sub(usum, from_r);
        let s_u2 = b.select(c3, ud, zero);
        let mut v = s_pk.to_vec(); v.push(new_bal); v.push(new_nonce); v.extend([s_r2, s_u2, s_peg[2], s_rd1, s_up1]);
        let s_full = hash_t(&mut b, v);
        let s_new = select_hash_c(&mut b, close_ap, empty, s_full);
        let mid = root_from(&mut b, s_new, &s_bits, &s_sib);
        let mid = HashOutTarget { elements: core::array::from_fn(|k| b.select(ap, mid.elements[k], cur.elements[k])) };
        // receiver: old leaf (empty for a new account) in the mid root
        let mut v = r_pk.to_vec(); v.push(r_bal); v.push(r_nonce); v.extend(r_peg);
        let r_full = hash_t(&mut b, v);
        let r_old = select_hash_c(&mut b, new_r, empty, r_full);
        let r2 = root_from(&mut b, r_old, &r_bits, &r_sib);
        connect_hash_if(&mut b, rx, r2, mid);
        imply_zero(&mut b, new_r, r_bal);
        for t in r_peg { imply_zero(&mut b, new_r, t); }
        let nd = b.arithmetic(-F::from_canonical_u64(1 << NONCE_SHIFT), F::ONE, h_t, one, r_nonce);
        imply_zero(&mut b, new_r, nd);
        let r_new_bal = b.add(r_bal, amt);
        let rb = b.mul(r_new_bal, rx.target); b.range_check(rb, 62);
        let (r_r1, r_u1, r_rd1, r_up1) = settle_t(&mut b, r_bal, r_peg[0], r_peg[1], r_peg[2], r_peg[3], r_peg[4], d_t, p_t);
        let mut v = r_pk.to_vec(); v.push(r_new_bal); v.push(r_nonce); v.extend([r_r1, r_u1, d_t, r_rd1, r_up1]);
        let r_new = hash_t(&mut b, v);
        let next = root_from(&mut b, r_new, &r_bits, &r_sib);
        cur = HashOutTarget { elements: core::array::from_fn(|k| b.select(rx, next.elements[k], cur.elements[k])) };
        fee_total = b.mul_add(ap.target, fee, fee_total);
        count = b.add(count, ap.target);
        // the signed payments, exactly as the signature leaf hashed them
        sig_entries.push(en.target);
        for v in s_pk.iter().chain(r_pk.iter()).chain([amt, fee, nonce].iter()) { let m = b.mul(*v, en.target); sig_entries.push(m); }
        sig_entries.push(close.target);
        // block data: applied payments only (a skipped slot hashes like an empty one)
        let s_idx = b.le_sum(s_bits.iter()); let r_idx = b.le_sum(r_bits.iter());
        data_entries.push(ap.target);
        for (v, f) in [(s_idx, ap), (r_idx, rx), (amt, rx), (fee, ap)] { let m = b.mul(v, f.target); data_entries.push(m); }
        data_entries.push(new_r.target); data_entries.push(close_ap.target); data_entries.push(cr.target);
        for k in 0..4 { let m = b.mul(r_pk[k], new_r.target); data_entries.push(m); }
        if degree_bits == 0 && si == 1 { println!("state leaf: slot gates {}", b.num_gates() - g0); }
        slots.push(StSlotT { en, skip, close, new_r, cr, s_pk, r_pk, amt, fee, nonce, s_bal, s_peg, s_bits, s_sib, r_bal, r_nonce, r_peg, r_bits, r_sib });
    }
    sig_entries.extend(prover);
    let sh = hash_t(&mut b, sig_entries);
    for k in 0..4 { b.connect(sh.elements[k], sig_pt.public_inputs[k]); }
    data_entries.extend(prover);
    let data = hash_t(&mut b, data_entries);
    b.register_public_inputs(&root0.elements);
    b.register_public_inputs(&cur.elements);
    b.register_public_input(fee_total);
    b.register_public_input(count);
    b.register_public_inputs(&data.elements);
    b.register_public_input(s_t);
    b.register_public_input(h_t);
    let z = b.zero();
    for _ in 0..VDPI { b.register_public_input(z); }      // same public-value layout as a merge proof
    if degree_bits == 0 { println!("state leaf: {} gates before padding", b.num_gates()); }
    pad_to(&mut b, degree_bits);
    StateCircuit { data: b.build::<C>(), sig_pt, root0, h_t, day, prover, slots }
}

fn flat_vd(vd: &VerifierCircuitTarget) -> Vec<Target> {
    let mut v = vd.circuit_digest.elements.to_vec();
    for h in &vd.constants_sigmas_cap.0 { v.extend(h.elements); }
    v
}
struct Node { data: CircuitData<F, C, D>, left: ProofWithPublicInputsTarget<D>, right: ProofWithPublicInputsTarget<D>,
              l_leaf: BoolTarget, r_leaf: BoolTarget, l_op: Vec<BoolTarget>, r_op: Vec<BoolTarget>, r_empty: BoolTarget, own_vd: VerifierCircuitTarget }
/// The universal merge: verifies a left and a right child, each a leaf proof (checked with the leaf's
/// fixed verifying key) or a merge proof of this same circuit (checked with this circuit's own key,
/// which it carries in its public values). The right child can be marked empty; the left one then
/// passes through. Leaf and merge proofs have identical circuit shapes, so one verifier serves both.
fn build_node(common: &CommonCircuitData<F, D>, leaf_vd: &VerifierOnlyCircuitData<C, D>, op_vds: &[&VerifierOnlyCircuitData<C, D>], gates: &[GateRef<F, D>], degree_bits: usize) -> Node {
    let mut b = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());
    for g in gates { b.add_gate_to_gate_set(g.clone()); }
    let left = b.add_virtual_proof_with_pis(common);
    let right = b.add_virtual_proof_with_pis(common);
    let l_leaf = b.add_virtual_bool_target_safe();
    let r_leaf = b.add_virtual_bool_target_safe();
    // a leaf child is an operation leaf of family j when its flag j is set (else a state leaf); the flags pick the verifier key in turn
    let l_op: Vec<BoolTarget> = op_vds.iter().map(|_| b.add_virtual_bool_target_safe()).collect();
    let r_op: Vec<BoolTarget> = op_vds.iter().map(|_| b.add_virtual_bool_target_safe()).collect();
    let r_empty = b.add_virtual_bool_target_safe();
    let lp = left.public_inputs.clone(); let rp = right.public_inputs.clone();
    let ne = b.not(r_empty);
    for k in 0..4 { cond_eq(&mut b, ne, lp[4 + k], rp[k]); }     // left's root after = right's root before
    cond_eq(&mut b, ne, lp[14], rp[14]);                            // same S
    cond_eq(&mut b, ne, lp[15], rp[15]);                            // same height
    let root1: Vec<Target> = (0..4).map(|k| b.select(r_empty, lp[4 + k], rp[4 + k])).collect();
    let fee = b.mul_add(ne.target, rp[8], lp[8]);
    let cnt = b.mul_add(ne.target, rp[9], lp[9]);
    let mut v = lp[10..14].to_vec(); v.extend_from_slice(&rp[10..14]);
    let h = hash_t(&mut b, v);
    let data: Vec<Target> = (0..4).map(|k| b.select(r_empty, lp[10 + k], h.elements[k])).collect();
    b.register_public_inputs(&lp[0..4]);
    b.register_public_inputs(&root1);
    b.register_public_input(fee);
    b.register_public_input(cnt);
    b.register_public_inputs(&data);
    b.register_public_input(lp[14]);
    b.register_public_input(lp[15]);
    let own_vd = b.add_verifier_data_public_inputs();
    let leaf_vd_t = b.constant_verifier_data(leaf_vd);
    let mut leaf_l = leaf_vd_t.clone(); let mut leaf_r = leaf_vd_t.clone();
    for (j, vd) in op_vds.iter().enumerate() {
        let vd_t = b.constant_verifier_data(vd);
        leaf_l = b.select_verifier_data(l_op[j], &vd_t, &leaf_l);
        leaf_r = b.select_verifier_data(r_op[j], &vd_t, &leaf_r);
    }
    let vd_l = b.select_verifier_data(l_leaf, &leaf_l, &own_vd);
    let vd_r = b.select_verifier_data(r_leaf, &leaf_r, &own_vd);
    b.verify_proof::<C>(&left, &vd_l, common);
    b.verify_proof::<C>(&right, &vd_r, common);
    // a merge child must have been checked with this same circuit's key
    let own = flat_vd(&own_vd);
    for (pis, is_leaf) in [(&lp, l_leaf), (&rp, r_leaf)] {
        let not_leaf = b.not(is_leaf);
        for k in 0..VDPI { cond_eq(&mut b, not_leaf, pis[NPI + k], own[k]); }
    }
    pad_to(&mut b, degree_bits);
    let data = b.build::<C>();
    Node { data, left, right, l_leaf, r_leaf, l_op, r_op, r_empty, own_vd }
}
/// The leaf circuits (state leaf, vault leaf, channel leaf) and the universal merge, brought to one shape: a gate union and a row count, repeated until
/// every circuit comes out with the same common data.
pub(crate) struct Family { pub st: StateCircuit, pub op: opcirc::OpLeaf, pub chan: chancirc::ChanLeaf, pub order: ordercirc::OrderLeaf, pub fact: factorycirc::FactoryLeaf, pub node: Node }
pub(crate) fn build_family(n: usize, sig: &CircuitData<F, C, D>, prm: &ec::Params, st0: Option<StateCircuit>) -> anyhow::Result<Family> {
    let st0 = match st0 { Some(s) => s, None => build_state(n, sig, &[], 0) };
    let op0 = opcirc::build_op(CHAIN_ID, prm, &[], 0);
    let ch0 = chancirc::build_chan(CHAIN_ID, prm, &[], 0);
    let or0 = ordercirc::build_order(CHAIN_ID, prm, &[], 0);
    let fa0 = factorycirc::build_factory(CHAIN_ID, prm, &[], 0);
    let node0 = build_node(&st0.data.common, &st0.data.verifier_only, &[&op0.data.verifier_only, &ch0.data.verifier_only, &or0.data.verifier_only, &fa0.data.verifier_only], &st0.data.common.gates, 0);
    let mut gates = st0.data.common.gates.clone();
    let mut deg = st0.data.common.degree_bits().max(node0.data.common.degree_bits());
    for c in [&node0.data.common, &op0.data.common, &ch0.data.common, &or0.data.common, &fa0.data.common] { gates = gate_union(&gates, &c.gates); deg = deg.max(c.degree_bits()); }
    println!("first pass: state leaf 2^{} | vault 2^{} | channel 2^{} | order 2^{} | factory 2^{} | merge 2^{} | {} gate types in the union", st0.data.common.degree_bits(), op0.data.common.degree_bits(), ch0.data.common.degree_bits(), or0.data.common.degree_bits(), fa0.data.common.degree_bits(), node0.data.common.degree_bits(), gates.len());
    loop {
        let st = build_state(n, sig, &gates, deg);
        let op = opcirc::build_op(CHAIN_ID, prm, &gates, deg);
        let chan = chancirc::build_chan(CHAIN_ID, prm, &gates, deg);
        let order = ordercirc::build_order(CHAIN_ID, prm, &gates, deg);
        let fact = factorycirc::build_factory(CHAIN_ID, prm, &gates, deg);
        let node = build_node(&st.data.common, &st.data.verifier_only, &[&op.data.verifier_only, &chan.data.verifier_only, &order.data.verifier_only, &fact.data.verifier_only], &gates, deg);
        let commons = [&node.data.common, &st.data.common, &op.data.common, &chan.data.common, &order.data.common, &fact.data.common];
        if commons.iter().all(|c| **c == st.data.common) { return Ok(Family { st, op, chan, order, fact, node }); }
        let ds: Vec<usize> = commons.iter().map(|c| c.degree_bits()).collect();
        println!("shapes differ (degrees {:?}), again", ds);
        for c in commons { gates = gate_union(&gates, &c.gates); }
        deg = deg.max(*ds.iter().max().unwrap());
        if deg > 17 { anyhow::bail!("could not match the leaf and merge shapes"); }
    }
}
fn gate_union(a: &[GateRef<F, D>], b: &[GateRef<F, D>]) -> Vec<GateRef<F, D>> {
    let mut out: Vec<GateRef<F, D>> = a.to_vec();
    for g in b { if !out.iter().any(|x| x.0.id() == g.0.id()) { out.push(g.clone()); } }
    out
}

/// wrap the root merge proof: checks that its verifier-data public values are the merge circuit's
/// real key, and keeps only the 16 block values
fn build_wrap_node(node: &CircuitData<F, C, D>) -> (CircuitData<F, C, D>, ProofWithPublicInputsTarget<D>) {
    build_wrap_node_cfg(node, CircuitConfig::standard_recursion_config())
}
fn build_wrap_node_cfg(node: &CircuitData<F, C, D>, cfg: CircuitConfig) -> (CircuitData<F, C, D>, ProofWithPublicInputsTarget<D>) {
    let mut bld = CircuitBuilder::<F, D>::new(cfg);
    let vd = bld.constant_verifier_data(&node.verifier_only);
    let pt = bld.add_virtual_proof_with_pis(&node.common);
    bld.verify_proof::<C>(&pt, &vd, &node.common);
    let flat = flat_vd(&vd);
    for k in 0..VDPI { bld.connect(pt.public_inputs[NPI + k], flat[k]); }
    let pis = pt.public_inputs[0..NPI].to_vec();
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
fn key_big(k: &[u64; 4]) -> BigUint { BigUint::from_slice(&k.iter().flat_map(|w| [*w as u32, (*w >> 32) as u32]).collect::<Vec<u32>>()) }
fn sign_native(prm: &ec::Params, sa: &Acct, msg: [F; 4], krng: &mut rand::rngs::StdRng) -> (ec::P, BigUint) {
    let kb = key_big(&sa.k);
    let rw: [u64; 4] = krng.r#gen();
    let rb = key_big(&rw);
    let rp = ec::mul_g(prm, &rb);
    let e = ec::challenge(rp, sa.a, msg);
    let sv = (&rb + &e * &kb) % ec::n_order();
    assert!(ec::native_check(prm, sa.a, rp, &sv, &e), "native model of the circuit check failed");
    (rp, sv)
}
/// a signed payment as a wallet sends it (indices are where the builder will find the accounts)
#[derive(Clone)]
struct Pay { s_pk: [F; 4], r_pk: [F; 4], amt: u64, fee: u64, nonce: u64, close: bool, a: ec::P, rp: ec::P, sv: BigUint, s_idx: u64, r_idx: u64, corrupt: bool, tag: &'static str }
fn new_acct(prm: &ec::Params, krng: &mut rand::rngs::StdRng, bal: u64, nonce: u64) -> Acct {
    let k: [u64; 4] = krng.r#gen();
    let a = ec::mul_g(prm, &key_big(&k));
    Acct { pk: ec::pk_hash(a), bal, nonce, rest: bal, used: 0, fd: 0, rd: 0, up: 0, a, k }
}
fn size_kb(p: &ProofWithPublicInputs<F, C, D>) -> f64 { p.to_bytes().len() as f64 / 1024.0 }
fn env_u64(k: &str, d: u64) -> u64 { std::env::var(k).ok().and_then(|v| v.parse().ok()).unwrap_or(d) }
fn idx_of(i: u64) -> u64 { (i * 2654435761) & ((1u64 << DEPTH) - 1) }

/// `zenproof seal`: a Stratum v1 job for a minted block, a miner that knows only Stratum, and the node's check
fn seal_bench() -> Result<()> {
    use sha2::Digest;
    let chain = CHAIN_ID as u8; let height = 101u64;
    let prev: [u8; 32] = sha2::Sha256::digest(b"Zen Jen block 100").into();
    // the minted block: the stamp's public values, the 196-byte stamp, the block data, the tickets root
    let dir = std::env::var("BLOCK").unwrap_or("out_v4".into());
    let data = std::fs::read(format!("{dir}/block.bin")).unwrap_or_else(|_| vec![4u8; 2401]);
    let pis: Vec<u64> = (0..16).map(|i| i * 7919).collect();
    let stamp = [9u8; 196];
    let tickets_root: [u8; 32] = sha2::Sha256::digest(b"tickets").into();
    let body = seal::body_root(&pis, &stamp, &data, &tickets_root);
    let pool_addr = [0x11u8; 32];           // the pool's own address: it receives the miner's part
    let bits = 0x1f00ffff;                  // an easy target for the test (about 2^16 hashes)
    let job = seal::make_job("zen1", chain, height, &prev, &body, &pool_addr, 4 + 4, bits, 1_790_000_000);
    println!("seal bench | Bitcoin 80-byte header, SHA256d | Stratum v1 job:\n{}", job.notify_json());
    let en1 = [0xde, 0xad, 0xbe, 0xef];      // set by the pool per connection
    let t = Instant::now();
    let (share, hashes) = seal::stratum_mine(&job, &en1, 4, 50_000_000).ok_or_else(|| anyhow::anyhow!("no share"))?;
    let secs = t.elapsed().as_secs_f64();
    println!("RESULT Stratum miner: share after {hashes} hashes, {secs:.2}s ({:.2} MH/s on one CPU core) | extranonce2 {} | nonce {}", hashes as f64 / secs / 1e6, seal::hex(&share.extranonce2), share.nonce);
    // the node: rebuild the coinbase and header from the share and check everything
    let cb = { let mut v = seal::coinb1(chain, height, 8); v.extend(en1); v.extend(&share.extranonce2); v.extend(seal::coinb2(&pool_addr)); v };
    let hdr = seal::Header { version: share.version, prev, commitment: seal::merkle_root(&cb, &[body]), ntime: share.ntime, nbits: bits, nonce: share.nonce };
    let mut hh = hdr.hash(); hh.reverse();
    match seal::check_seal(&hdr, &cb, chain, height, &prev, &body, bits) {
        Ok(m) => println!("RESULT node: seal valid | block hash {} | miner's part to {}", seal::hex(&hh), if m == pool_addr { "the pool's address" } else { "?" }),
        Err(e) => println!("RESULT node: seal REJECTED ({e})"),
    }
    let reject = |name: &str, r: Result<[u8; 32]>| println!("RESULT attack {name}: {}", match r { Ok(_) => "ACCEPTED (bad)".to_string(), Err(e) => format!("rejected ({e})") });
    let other_body = seal::body_root(&pis, &stamp, &data[..data.len() - 1], &tickets_root);
    reject("seal reused for a changed block", seal::check_seal(&hdr, &cb, chain, height, &prev, &other_body, bits));
    let mut cb2 = cb.clone(); let l = cb2.len(); cb2[l - 1] ^= 1;
    reject("miner address swapped after solving", seal::check_seal(&hdr, &cb2, chain, height, &prev, &body, bits));
    reject("seal shown to Ken (other chain)", seal::check_seal(&hdr, &cb, 2, height, &prev, &body, bits));
    reject("version outside BIP 320 bits", seal::check_seal(&seal::Header { version: 0x6000_0000, ..hdr }, &cb, chain, height, &prev, &body, bits));
    reject("easier bits than the chain asks", seal::check_seal(&seal::Header { nbits: 0x207fffff, ..hdr }, &cb, chain, height, &prev, &body, bits));
    reject("wrong nonce", seal::check_seal(&seal::Header { nonce: hdr.nonce ^ 1, ..hdr }, &cb, chain, height, &prev, &body, bits));
    println!("RESULT difficulty 1 -> bits {:08x}, difficulty 1,000,000 -> bits {:08x}", seal::difficulty_bits(1), seal::difficulty_bits(1_000_000));
    Ok(())
}

/// `zenproof payouts`: the minter share of every block goes straight to the winning tickets (TARGET_BLOWS of
/// them), whatever the number of minters. Counts credits per block and checks the pay follows the work.
fn payouts_sim() -> Result<()> {
    let tb = mint::TARGET_BLOWS as usize;
    let mut seed = 7u64;
    let mut rnd = || { seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); seed >> 11 };
    println!("payout sim | {tb} winning tickets per block | minters' share 24,000 units per block | 2000 blocks");
    println!("{:>11} | {:>26} | {:>20} | {:>16}", "minters", "credits per block avg/max", "blocks to first win", "pay vs work (top 1%)");
    for n in [100usize, 1_000, 10_000, 100_000, 300_000] {
        let nn = n;
        let w: Vec<f64> = (0..nn).map(|i| 1.0 / ((i + 1) as f64).powf(0.8)).collect();
        let tot: f64 = w.iter().sum();
        let mut cum = Vec::with_capacity(nn); let mut c = 0.0; for x in &w { c += x / tot; cum.push(c); }
        let mut paid = vec![0u64; nn];
        let (mut sum, mut max) = (0usize, 0usize);
        let blocks = 2000;
        for _ in 0..blocks {
            let mut got: Vec<usize> = (0..tb).map(|_| { let u = (rnd() % 1_000_000_000) as f64 / 1e9; cum.partition_point(|x| *x < u).min(nn - 1) }).collect();
            got.sort();
            let each = 24_000 / tb as u64;          // every winning ticket carries an equal share
            let mut credited = 0usize;
            let mut k = 0;
            while k < got.len() { let mut j = k; while j < got.len() && got[j] == got[k] { j += 1; } paid[got[k]] += each * (j - k) as u64; credited += 1; k = j; }
            sum += credited; max = max.max(credited);
        }
        let top = nn / 100; let top_paid: u64 = paid[..top.max(1)].iter().sum(); let all: u64 = paid.iter().sum();
        let top_work: f64 = cum[top.max(1) - 1];
        println!("RESULT {:>11} | {:>16.1} / {:>6} | {:>20} | {:>7.3} vs {:>5.3}", n, sum as f64 / blocks as f64, max,
            format!("~{}", (n / tb).max(1)), top_paid as f64 / all as f64, top_work);
    }
    println!("credits per block never exceed {tb}: the difficulty rises with the number of minters, not the block size");
    Ok(())
}

/// `zenproof mint [attempts]`: blows and tickets with one key per person (see mint.rs)
fn mint_bench() -> Result<()> {
    use sha2::Digest;
    let prm = ec::params();
    let mut krng = rand::rngs::StdRng::seed_from_u64(7);
    let acct = new_acct(&prm, &mut krng, 0, 0);             // the same kind of key that signs payments
    let key = mint::Key::from_secret(key_big(&acct.k));
    assert_eq!(key.addr, acct.pk, "minting identity = account address");
    let other = { let a = new_acct(&prm, &mut krng, 0, 0); mint::Key::from_secret(key_big(&a.k)) };
    let prev: [u8; 32] = sha2::Sha256::digest(b"Zen Jen devnet block 41").into();
    println!("mint bench | chain {CHAIN_ID} | Argon2id {} MB, {} pass, 1 lane | ticket {} bytes | threads {}", mint::MEM_KIB / 1024, mint::PASSES, mint::TICKET_BYTES, std::thread::available_parallelism()?.get());
    let n = 20;
    let t = Instant::now();
    let tickets: Vec<mint::Ticket> = (0..n).map(|i| mint::make_ticket(&key, CHAIN_ID, &prev, i)).collect();
    let sign_ms = t.elapsed().as_secs_f64() * 1000.0 / n as f64;
    let t = Instant::now();
    for tk in &tickets { let a = mint::decode_point(&tk.a)?; assert!(mint::verify(a, mint::blow_msg(CHAIN_ID, &prev, tk.nonce), tk.e, &BigUint::from_bytes_le(&tk.s))); }
    let ver_ms = t.elapsed().as_secs_f64() * 1000.0 / n as f64;
    let t = Instant::now();
    for tk in tickets.iter().take(10) { mint::blow_value(&prev, tk); }
    let argon_ms = t.elapsed().as_secs_f64() * 1000.0 / 10.0;
    println!("RESULT per attempt: sign {sign_ms:.2} ms | Argon2id {argon_ms:.0} ms | node check of a ticket: decode + verify {ver_ms:.2} ms + one Argon2id | peak {:.0} MB", peak_mb());
    // mine: difficulty 4 -> about one attempt in four wins
    let diff = 4u64;
    let attempts = std::env::args().nth(2).and_then(|s| s.parse().ok()).unwrap_or(24u64);
    let t = Instant::now();
    let mut won = vec![];
    for nonce in 0..attempts {
        let tk = if (nonce as usize) < tickets.len() { tickets[nonce as usize] } else { mint::make_ticket(&key, CHAIN_ID, &prev, nonce) };
        let v = mint::blow_value(&prev, &tk);
        if mint::wins(&v, diff) { won.push(tk); }
    }
    println!("RESULT minting: {attempts} attempts at difficulty {diff} -> {} winning blows in {:.1}s ({:.2} attempts/s on one core)", won.len(), t.elapsed().as_secs_f64(), attempts as f64 / t.elapsed().as_secs_f64());
    let t = Instant::now();
    for tk in &won {
        let bytes = tk.to_bytes();
        let back = mint::Ticket::from_bytes(&bytes)?;
        let (addr, _) = mint::check_ticket(CHAIN_ID, &prev, &back, diff)?;
        assert_eq!(addr, acct.pk);
    }
    println!("RESULT node: {} tickets checked, {:.0} ms each, every one credited to the minter's own account address", won.len(), t.elapsed().as_secs_f64() * 1000.0 / won.len().max(1) as f64);
    // attacks: each must be rejected
    let w = won.first().copied().ok_or_else(|| anyhow::anyhow!("no winning blow; run more attempts"))?;
    let reject = |name: &str, r: Result<([F; 4], [u8; 32])>| println!("RESULT attack {name}: {}", match r { Ok(_) => "ACCEPTED (bad)".to_string(), Err(e) => format!("rejected ({e})") });
    reject("changed nonce", mint::check_ticket(CHAIN_ID, &prev, &mint::Ticket { nonce: w.nonce + 1000, ..w }, 1));
    reject("same ticket on another chain (Ken)", mint::check_ticket(2, &prev, &w, 1));
    reject("same ticket on another round", mint::check_ticket(CHAIN_ID, &[1u8; 32], &w, 1));
    reject("claim someone else's blow (swap in another key)", mint::check_ticket(CHAIN_ID, &prev, &mint::Ticket { a: mint::encode_point(other.a), ..w }, 1));
    let t2 = ec::P { x: ec::E::ZERO, y: ec::E::ZERO };
    reject("key with an order-2 part", mint::check_ticket(CHAIN_ID, &prev, &mint::Ticket { a: mint::encode_point(ec::add(key.a, t2)), ..w }, 1));
    // a payment signature cannot be passed off as a blow: sign a payment message, present it as a ticket
    let pay = msg_native(&acct.pk, &other.addr, 5000, 50, w.nonce, false);
    let (e, s) = mint::sign(&key, pay);
    let mut sb = [0u8; 40]; let b = s.to_bytes_le(); sb[..b.len()].copy_from_slice(&b);
    reject("payment signature used as a blow", mint::check_ticket(CHAIN_ID, &prev, &mint::Ticket { e, s: sb, ..w }, 1));
    reject("winning blow at a harder difficulty", mint::check_ticket(CHAIN_ID, &prev, &w, u64::MAX));
    // difficulty rule
    let mut d = 1000u64; let mut ema = 0u64; let mut trace = vec![];
    for blows in [100u64, 300, 300, 300, 50, 0, 100] { ema = mint::next_work_ema(ema, blows * d); d = mint::retarget(d, blows); trace.push(d); }
    println!("RESULT blow difficulty from 1000 for blows/block 100,300,300,300,50,0,100: {:?} | gate now {} (work EMA {})", trace, mint::min_work(ema, d), ema);
    Ok(())
}

fn main() -> Result<()> {
    if std::env::args().nth(1).as_deref() == Some("mint") { return mint_bench(); }
    if std::env::args().nth(1).as_deref() == Some("seal") { return seal_bench(); }
    if std::env::args().nth(1).as_deref() == Some("node") { return node::serve_main(); }
    if std::env::args().nth(1).as_deref() == Some("g16verify") { return groth16::g16verify_main(); }
    if std::env::args().nth(1).as_deref() == Some("wallet") { return tx::wallet_main(); }
    if std::env::args().nth(1).as_deref() == Some("chan") { return channel::chan_main(); }
    if std::env::args().nth(1).as_deref() == Some("market") { return market::market_main(); }
    if std::env::args().nth(1).as_deref() == Some("rnode") { return route::rnode_main(); }
    if std::env::args().nth(1).as_deref() == Some("net") { return netconf::net_main(); }
    if std::env::args().nth(1).as_deref() == Some("payouts") { return payouts_sim(); }
    let args: Vec<String> = std::env::args().collect();
    let n: usize = args.get(1).map(|s| s.parse().unwrap()).unwrap_or(16);
    let leaves: usize = args.get(2).map(|s| s.parse().unwrap()).unwrap_or(8);
    let s_coin = env_u64("S", 1000);          // base units per coin (1 JEN), a public value of the block
    let height = env_u64("HEIGHT", 100);      // block height, a public value of the block
    let double = std::env::var("DOUBLESPEND").is_ok();   // a sender signs two payments with the same nonce
    let replay_test = std::env::var("REPLAY").is_ok();   // a payment is submitted twice with its signature
    let tamper = std::env::var("TAMPER").is_ok();        // the builder changes a signed fee
    println!("zenproof v3 (signature leaves + state leaves) | slots per leaf {n} | leaves {leaves} | S {s_coin} | height {height} | threads {}", std::thread::available_parallelism()?.get());
    let prm = ec::params();
    let nm1 = ec::n_order() - BigUint::from(1u32);
    assert_eq!(ec::mul(prm.g, &nm1), ec::neg(prm.g), "G does not have order n");
    let mut krng = rand::rngs::StdRng::seed_from_u64(42);

    // ---- circuits: the minters' signature leaf; the builder's state leaf and the universal merge,
    //      which share one shape
    let t = Instant::now();
    let sig = build_sig(n, &prm);
    println!("RESULT signature leaf circuit: 2^{} rows | build {:.1}s", sig.data.common.degree_bits(), t.elapsed().as_secs_f64());
    let t = Instant::now();
    let st0 = build_state(n, &sig.data, &[], 0);
    let Family { st, node, .. } = build_family(n, &sig.data, &prm, Some(st0))?;
    println!("RESULT circuits: state leaf and merge share one shape, 2^{} rows, {} public values | build {:.1}s",
        st.data.common.degree_bits(), st.data.common.num_public_inputs, t.elapsed().as_secs_f64());

    // ---- genesis state
    let mut tree = Tree::new();
    let mut accts: Vec<Acct> = (0..64u64).map(|_| new_acct(&prm, &mut krng, 1_000_000_000, 0)).collect();
    if std::env::var("PEGMIX").is_ok() {
        // some genesis accounts hold fresh money (maturing or not) or already-counted money, to exercise every peg rule
        let (dg, pg) = blockdata::day_period(height);
        for (i, a) in accts.iter_mut().enumerate() {
            let b = a.bal;
            match i % 6 {
                1 => { a.rest = b / 2; a.fd = dg.saturating_sub(5); a.rd = 0; }
                2 => { a.rest = b / 2; a.fd = dg.saturating_sub(1); }
                3 => { a.used = b / 3; a.up = pg; }
                4 => { a.used = b / 3; a.up = pg.saturating_sub(1); }
                5 => { a.rest = b / 4; a.used = b / 8; a.fd = dg.saturating_sub(4); a.rd = 1; a.up = pg; }
                _ => {}
            }
        }
    }
    let mut idx: Vec<u64> = (0..64u64).map(idx_of).collect();
    let mut alive: Vec<bool> = vec![true; 64];
    for (i, a) in accts.iter().enumerate() { tree.set(idx[i], leaf_hash(a)); }
    let genesis_state: HashMap<u64, Acct> = idx.iter().zip(&accts).map(|(i, a)| (*i, *a)).collect();
    let genesis_tree = tree.clone();

    // ---- wallets: signed payments waiting to be minted (the wallets' own view of their balances)
    let extra = (double as usize) + (replay_test as usize);
    // by default one leaf's worth of slots stays free for the block's credits (payouts)
    let n_real: usize = env_u64("REAL", (n * leaves - extra).saturating_sub(n) as u64) as usize;
    let newacc_every = env_u64("NEWACC", 6) as usize;
    let close_at = env_u64("CLOSE", 3) as usize;
    let corrupt = std::env::var("CORRUPT").is_ok();
    let mut seed: u64 = env_u64("SEED", 1);
    let mut rnd = || { seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); seed >> 33 };
    let mut pays: Vec<Pay> = vec![];
    for real_no in 1..=n_real {
        let mut s = (rnd() % accts.len() as u64) as usize; while !alive[s] || accts[s].bal < 10_000_000 { s = (s + 1) % accts.len(); }
        let mut r = (rnd() % accts.len() as u64) as usize; while !alive[r] || r == s { r = (r + 1) % accts.len(); }
        let mut amt = 1000 + rnd() % 100_000; let mut fee = amt / 100;
        let closing = close_at != 0 && real_no == close_at;
        if closing { fee = accts[s].bal / 100; amt = accts[s].bal - fee; }
        let creating = newacc_every != 0 && real_no % newacc_every == 0 && !closing;
        if creating {
            accts.push(new_acct(&prm, &mut krng, 0, height << NONCE_SHIFT));
            idx.push(idx_of(accts.len() as u64 - 1)); alive.push(false);
            r = accts.len() - 1;
        }
        let sa = accts[s];
        let msg = msg_native(&sa.pk, &accts[r].pk, amt, fee, sa.nonce, closing);
        let (rp, sv) = sign_native(&prm, &sa, msg, &mut krng);
        pays.push(Pay { s_pk: sa.pk, r_pk: accts[r].pk, amt, fee, nonce: sa.nonce, close: closing, a: sa.a, rp, sv, s_idx: idx[s], r_idx: idx[r], corrupt: corrupt && real_no == 1, tag: "" });
        if double && real_no == 2 {
            // the same sender, the same nonce, another receiver: both payments are validly signed and
            // may land in two different minters' leaves; only one can be applied
            let mut r2 = (r + 1) % 64; while !alive[r2] || r2 == s { r2 = (r2 + 1) % 64; }
            let msg = msg_native(&sa.pk, &accts[r2].pk, amt, fee, sa.nonce, false);
            let (rp, sv) = sign_native(&prm, &sa, msg, &mut krng);
            pays.push(Pay { s_pk: sa.pk, r_pk: accts[r2].pk, amt, fee, nonce: sa.nonce, close: false, a: sa.a, rp, sv, s_idx: idx[s], r_idx: idx[r2], corrupt: false, tag: "double spend" });
        }
        if replay_test && real_no == 4 { let mut p = pays[0].clone(); p.tag = "replay"; pays.push(p); }
        accts[s].bal -= amt + fee; accts[s].nonce += 1;
        if closing { alive[s] = false; }
        accts[r].bal += amt; alive[r] = true;
    }
    println!("block: {} signed payments in {} slots", pays.len(), n * leaves);
    let pad = { let k = [7u64, 7, 7, 7]; let a = ec::mul_g(&prm, &key_big(&k)); Acct { pk: ec::pk_hash(a), bal: 0, nonce: 0, rest: 0, used: 0, fd: 0, rd: 0, up: 0, a, k } };
    let z4 = [F::ZERO; 4];
    let (pad_rp, pad_sv) = sign_native(&prm, &pad, msg_native(&pad.pk, &z4, 0, 0, 0, false), &mut krng);

    // ---- minters: signature leaves. Stateless and independent: each could run on a different phone at
    //      the same time, before anyone knows the order of the leaves in the block.
    let chunks: Vec<Vec<Pay>> = (0..leaves).map(|li| pays.iter().skip(li * n).take(n).cloned().collect()).collect();
    // a leaf with no payments (credit-only) has no minter: its signature leaf is the empty one, which
    // the builder can prove once and reuse
    let provers: Vec<[F; 4]> = (0..leaves).map(|li| if chunks[li].is_empty() { z4 } else { accts[li % 64].pk }).collect();
    let mut sig_proofs = vec![];
    let mut sig_times = vec![];
    for li in 0..leaves {
        let mut pw = PartialWitness::new();
        pw.set_target(sig.s_t, F::from_canonical_u64(s_coin))?;
        pw.set_target_arr(&sig.prover, &provers[li])?;
        for (i, sl) in sig.slots.iter().enumerate() {
            match chunks[li].get(i) {
                Some(p) => {
                    pw.set_bool_target(sl.en, true)?; pw.set_bool_target(sl.close, p.close)?;
                    pw.set_target_arr(&sl.s_pk, &p.s_pk)?; pw.set_target_arr(&sl.r_pk, &p.r_pk)?;
                    pw.set_target(sl.amt, F::from_canonical_u64(p.amt))?; pw.set_target(sl.fee, F::from_canonical_u64(p.fee))?; pw.set_target(sl.nonce, F::from_canonical_u64(p.nonce))?;
                    set_sig(&mut pw, &sl.sig, p.a, p.rp, &p.sv, p.corrupt)?;
                }
                None => {
                    pw.set_bool_target(sl.en, false)?; pw.set_bool_target(sl.close, false)?;
                    pw.set_target_arr(&sl.s_pk, &pad.pk)?; pw.set_target_arr(&sl.r_pk, &z4)?;
                    for t in [sl.amt, sl.fee, sl.nonce] { pw.set_target(t, F::ZERO)?; }
                    set_sig(&mut pw, &sl.sig, pad.a, pad_rp, &pad_sv, false)?;
                }
            }
        }
        let t = Instant::now();
        let proof = match sig.data.prove(pw) {
            Ok(p) => p,
            Err(e) => { println!("RESULT signature leaf {li}: no proof ({})", e.to_string().lines().next().unwrap_or("")); return Ok(()); }
        };
        sig_times.push(t.elapsed().as_secs_f64());
        sig.data.verify(proof.clone())?;
        let refs: Vec<&Pay> = chunks[li].iter().collect();
        assert_eq!(proof.public_inputs[0..4], sig_hash_native(n, &refs, &provers[li]).elements);
        sig_proofs.push(proof);
    }
    println!("RESULT signature leaves (minters): {} proved, {:.2}s each on average | proof {:.1} KB | peak {:.0} MB",
        leaves, sig_times.iter().sum::<f64>() / leaves as f64, size_kb(&sig_proofs[0]), peak_mb());

    // ---- builder, step 1: which signed payments still fit, each leaf's fees, and the payouts owed.
    //      The payout inputs (miner, fee pool, rewards owed from block h-2) are what every node knows.
    let fits = |state: &HashMap<u64, Acct>, p: &Pay| -> bool {
        let spend = p.amt + p.fee;
        state.get(&p.s_idx).is_some_and(|a| a.pk == p.s_pk && a.nonce == p.nonce && a.bal >= spend && (!p.close || a.bal == spend))
            && p.r_idx != p.s_idx && state.get(&p.r_idx).is_none_or(|a| a.pk == p.r_pk && a.bal + p.amt < 1 << 62)
    };
    let mut sim = genesis_state.clone();
    let mut leaf_fees = vec![];
    for li in 0..leaves {
        let mut f = 0;
        for p in &chunks[li] {
            if !fits(&sim, p) { continue; }
            let mut sa = sim[&p.s_idx]; sa.bal -= p.amt + p.fee; sa.nonce += 1;
            if p.close { sim.remove(&p.s_idx); } else { sim.insert(p.s_idx, sa); }
            let mut ra = sim.get(&p.r_idx).copied().unwrap_or(Acct::blank(p.r_pk, 0, &sa)); ra.bal += p.amt; sim.insert(p.r_idx, ra);
            f += p.fee;
        }
        leaf_fees.push((provers[li], f));
    }
    let ticket_minter = new_acct(&prm, &mut krng, 0, 0);     // a minter with no account yet: its first credit creates it
    let rule = blockdata::PayoutRule { miner: accts[10].pk, pool_before: env_u64("POOL", 3_200_000),
        rewards: vec![(accts[11].pk, 5_000_000), (ticket_minter.pk, 400_000), (accts[12].pk, 400_000)] };
    let (mut owed, pool_after) = blockdata::expected_credits(&leaf_fees, &rule);
    if std::env::var("OVERPAY").is_ok() { owed[0].1 += 1; }   // the builder pays someone one unit too much
    let first_free = pays.len();
    if first_free + owed.len() > n * leaves { anyhow::bail!("no room for {} credits", owed.len()); }
    let credit_at = |li: usize, i: usize| -> Option<([F; 4], u64)> { let g = li * n + i; if g >= first_free { owed.get(g - first_free).copied() } else { None } };
    let mut fresh_idx = 1000u64;

    // ---- builder, step 2: state leaves, in order
    let mut state = genesis_state.clone();
    let mut block: Vec<LeafData> = vec![];
    let mut st_proofs = vec![];
    let mut st_times = vec![];
    let (mut n_new, mut n_close, mut skipped, mut n_credits) = (0, 0, vec![], 0);
    let mut tampered = false;
    let mut counted: Vec<blockdata::Counted> = vec![];
    for li in 0..leaves {
        block.push(LeafData { prover: provers[li], pays: vec![] });
        let mut pw = PartialWitness::new();
        pw.set_proof_with_pis_target(&st.sig_pt, &sig_proofs[li])?;
        pw.set_hash_target(st.root0, tree.root())?;
        pw.set_target(st.h_t, F::from_canonical_u64(height))?;
        let (day_n, per_n) = blockdata::day_period(height);
        for (t, v) in st.day.iter().zip([day_n, height - day_n * blockdata::BPD, per_n, day_n - per_n * blockdata::REST_DAYS]) { pw.set_target(*t, F::from_canonical_u64(v))?; }
        pw.set_target_arr(&st.prover, &provers[li])?;
        for (i, sl) in st.slots.iter().enumerate() {
            let zero_s = |pw: &mut PartialWitness<F>| -> Result<()> {
                for l in 0..DEPTH { pw.set_bool_target(sl.s_bits[l], false)?; pw.set_hash_target(sl.s_sib[l], HashOut { elements: z4 })?; }
                pw.set_target(sl.s_bal, F::ZERO)?; for t in sl.s_peg { pw.set_target(t, F::ZERO)?; } Ok(())
            };
            let zero_r = |pw: &mut PartialWitness<F>| -> Result<()> {
                for l in 0..DEPTH { pw.set_bool_target(sl.r_bits[l], false)?; pw.set_hash_target(sl.r_sib[l], HashOut { elements: z4 })?; }
                for t in [sl.r_bal, sl.r_nonce] { pw.set_target(t, F::ZERO)?; } for t in sl.r_peg { pw.set_target(t, F::ZERO)?; } Ok(())
            };
            let zero_paths = |pw: &mut PartialWitness<F>| -> Result<()> { zero_s(pw)?; zero_r(pw) };
            let Some(p) = chunks[li].get(i) else {
                for bt in [sl.en, sl.skip, sl.close] { pw.set_bool_target(bt, false)?; }
                pw.set_target_arr(&sl.s_pk, &pad.pk)?;
                for t in [sl.fee, sl.nonce] { pw.set_target(t, F::ZERO)?; }
                zero_s(&mut pw)?;
                let Some((addr, amount)) = credit_at(li, i) else {
                    for bt in [sl.new_r, sl.cr] { pw.set_bool_target(bt, false)?; }
                    pw.set_target_arr(&sl.r_pk, &z4)?; pw.set_target(sl.amt, F::ZERO)?;
                    zero_r(&mut pw)?;
                    continue;
                };
                // a credit: the payout goes to the address's account, or creates it
                let found = state.iter().find(|(_, a)| a.pk == addr).map(|(k, _)| *k);
                let ri = found.unwrap_or_else(|| { while state.contains_key(&idx_of(fresh_idx)) { fresh_idx += 1; } idx_of(fresh_idx) });
                let ra = state.get(&ri).copied().unwrap_or(Acct::blank(addr, height << NONCE_SHIFT, &pad));
                pw.set_bool_target(sl.cr, true)?; pw.set_bool_target(sl.new_r, found.is_none())?;
                pw.set_target_arr(&sl.r_pk, &addr)?; pw.set_target(sl.amt, F::from_canonical_u64(amount))?;
                pw.set_target(sl.r_bal, F::from_canonical_u64(ra.bal))?; pw.set_target(sl.r_nonce, F::from_canonical_u64(ra.nonce))?;
                set_peg(&mut pw, &sl.r_peg, &ra)?;
                for l in 0..DEPTH { pw.set_bool_target(sl.r_bits[l], (ri >> l) & 1 == 1)?; }
                for (l, h) in tree.path(ri).into_iter().enumerate() { pw.set_hash_target(sl.r_sib[l], h)?; }
                let mut ra2 = ra; blockdata::receive_to(&mut ra2, amount, day_n, per_n);
                state.insert(ri, ra2); tree.set(ri, leaf_hash(&ra2));
                if found.is_none() { n_new += 1; }
                n_credits += 1;
                block.last_mut().unwrap().pays.push(BlockEntry { slot: i as u8, credit: true, s_idx: 0, r_idx: ri as u32, amt: amount, fee: 0, new_r: if found.is_none() { Some(addr) } else { None }, close: false });
                continue;
            };
            pw.set_bool_target(sl.cr, false)?;
            pw.set_bool_target(sl.en, true)?; pw.set_bool_target(sl.close, p.close)?;
            pw.set_target_arr(&sl.s_pk, &p.s_pk)?; pw.set_target_arr(&sl.r_pk, &p.r_pk)?;
            let fee_w = if tamper && !tampered { tampered = true; p.fee + 1 } else { p.fee };
            pw.set_target(sl.amt, F::from_canonical_u64(p.amt))?; pw.set_target(sl.fee, F::from_canonical_u64(fee_w))?; pw.set_target(sl.nonce, F::from_canonical_u64(p.nonce))?;
            // does the payment still fit the state?
            let spend = p.amt + p.fee;
            if !fits(&state, p) {
                pw.set_bool_target(sl.skip, true)?; pw.set_bool_target(sl.new_r, false)?;
                zero_paths(&mut pw)?;
                skipped.push(format!("leaf {li} slot {i}{}", if p.tag.is_empty() { String::new() } else { format!(" ({})", p.tag) }));
                continue;
            }
            pw.set_bool_target(sl.skip, false)?;
            // sender
            let mut sa = state[&p.s_idx];
            pw.set_target(sl.s_bal, F::from_canonical_u64(sa.bal))?;
            if std::env::var("PEGCHEAT").is_ok() && !tampered { tampered = true; let mut lie = sa; lie.rest = lie.bal; lie.used = 0; set_peg(&mut pw, &sl.s_peg, &lie)?; } else { set_peg(&mut pw, &sl.s_peg, &sa)?; }
            for l in 0..DEPTH { pw.set_bool_target(sl.s_bits[l], (p.s_idx >> l) & 1 == 1)?; }
            for (l, h) in tree.path(p.s_idx).into_iter().enumerate() { pw.set_hash_target(sl.s_sib[l], h)?; }
            counted.push(blockdata::pay_from(&mut sa, p.amt, p.fee, day_n, per_n));
            if p.close { state.remove(&p.s_idx); tree.set(p.s_idx, empty_leaf()); n_close += 1; } else { state.insert(p.s_idx, sa); tree.set(p.s_idx, leaf_hash(&sa)); }
            // receiver
            let new_r = !state.contains_key(&p.r_idx);
            let ra = state.get(&p.r_idx).copied().unwrap_or(Acct::blank(p.r_pk, height << NONCE_SHIFT, &sa));
            pw.set_bool_target(sl.new_r, new_r)?;
            pw.set_target(sl.r_bal, F::from_canonical_u64(ra.bal))?; pw.set_target(sl.r_nonce, F::from_canonical_u64(ra.nonce))?;
            set_peg(&mut pw, &sl.r_peg, &ra)?;
            for l in 0..DEPTH { pw.set_bool_target(sl.r_bits[l], (p.r_idx >> l) & 1 == 1)?; }
            for (l, h) in tree.path(p.r_idx).into_iter().enumerate() { pw.set_hash_target(sl.r_sib[l], h)?; }
            let mut ra2 = ra; blockdata::receive_to(&mut ra2, p.amt, day_n, per_n);
            state.insert(p.r_idx, ra2); tree.set(p.r_idx, leaf_hash(&ra2));
            if new_r { n_new += 1; }
            block.last_mut().unwrap().pays.push(BlockEntry { slot: i as u8, credit: false, s_idx: p.s_idx as u32, r_idx: p.r_idx as u32, amt: p.amt, fee: p.fee, new_r: if new_r { Some(p.r_pk) } else { None }, close: p.close });
        }
        let t = Instant::now();
        let proof = match st.data.prove(pw) {
            Ok(p) => p,
            Err(e) => { println!("RESULT state leaf {li}: no proof ({})", e.to_string().lines().next().unwrap_or("")); return Ok(()); }
        };
        st_times.push(t.elapsed().as_secs_f64());
        st.data.verify(proof.clone())?;
        st_proofs.push(proof);
    }
    println!("RESULT state leaves (builder): {} proved, {:.2}s each on average | {} credits (payouts), {} new accounts, {} closed, {} skipped {:?} | proof {:.1} KB | peak {:.0} MB",
        leaves, st_times.iter().sum::<f64>() / leaves as f64, n_credits, n_new, n_close, skipped.len(), skipped, size_kb(&st_proofs[0]), peak_mb());
    println!("RESULT payouts: {:?} | fee pool {} -> {}", owed.iter().map(|(_, v)| *v).collect::<Vec<_>>(), rule.pool_before, pool_after);

    // ---- universal merge tree: any number of leaves ends in a proof of the same merge circuit
    let mut level: Vec<(bool, ProofWithPublicInputs<F, C, D>)> = st_proofs.into_iter().map(|p| (true, p)).collect();
    let mut merge_times = vec![];
    while level.len() > 1 || level[0].0 {
        let mut next = vec![];
        for pair in level.chunks(2) {
            let (l_leaf, lpf) = &pair[0];
            let (r_leaf, rpf, empty) = if pair.len() == 2 { (pair[1].0, &pair[1].1, false) } else { (*l_leaf, lpf, true) };
            let mut pw = PartialWitness::new();
            pw.set_proof_with_pis_target(&node.left, lpf)?;
            pw.set_proof_with_pis_target(&node.right, rpf)?;
            pw.set_bool_target(node.l_leaf, *l_leaf)?;
            pw.set_bool_target(node.r_leaf, r_leaf)?;
            for x in node.l_op.iter().chain(node.r_op.iter()) { pw.set_bool_target(*x, false)?; }
            pw.set_bool_target(node.r_empty, empty)?;
            pw.set_verifier_data_target(&node.own_vd, &node.data.verifier_only)?;
            let t = Instant::now();
            let p = node.data.prove(pw)?;
            merge_times.push(t.elapsed().as_secs_f64());
            next.push((false, p));
        }
        level = next;
    }
    let fin = level.pop().unwrap().1;
    node.data.verify(fin.clone())?;
    plonky2::recursion::cyclic_recursion::check_cyclic_proof_verifier_data(&fin, &node.data.verifier_only, &node.data.common)?;
    println!("RESULT merges: {} merge proofs, {:.2}s each on average | stamp {} payments, fee total {} | proof {:.1} KB | peak {:.0} MB",
        merge_times.len(), merge_times.iter().sum::<f64>() / merge_times.len() as f64, fin.public_inputs[9].to_canonical_u64(), fin.public_inputs[8].to_canonical_u64(), size_kb(&fin), peak_mb());

    // ---- wraps: shrink (checks the merge key), then the BN254-Poseidon layer for Groth16
    let (w1, t1) = build_wrap_node(&node.data);
    let mut pw = PartialWitness::new(); pw.set_proof_with_pis_target(&t1, &fin)?;
    let t = Instant::now(); let p1 = w1.prove(pw)?;
    println!("RESULT shrink: circuit 2^{} | prove {:.2}s | proof {:.1} KB", w1.common.degree_bits(), t.elapsed().as_secs_f64(), size_kb(&p1));
    if let Ok(dir) = std::env::var("BN_OUT") {
        type C2 = bn::PoseidonBn254GoldilocksConfig;
        let bcfg = small_cfg(env_u64("BN_RATE", 6) as usize, env_u64("BN_QUERIES", 14) as usize, env_u64("BN_POW", 16) as u32);
        let mut bld = CircuitBuilder::<F, D>::new(bcfg);
        let vd = bld.constant_verifier_data(&w1.verifier_only);
        let pt = bld.add_virtual_proof_with_pis(&w1.common);
        bld.verify_proof::<C>(&pt, &vd, &w1.common);
        let pis = pt.public_inputs.clone();
        bld.register_public_inputs(&pis);
        let wb = bld.build::<C2>();
        let mut pw = PartialWitness::new(); pw.set_proof_with_pis_target(&pt, &p1)?;
        let t = Instant::now(); let pb = wb.prove(pw)?; let ptb = t.elapsed().as_secs_f64();
        wb.verify(pb.clone())?;
        println!("RESULT bn254-poseidon layer: circuit 2^{} | prove {:.2}s | proof {:.1} KB | peak {:.0} MB", wb.common.degree_bits(), ptb, pb.to_bytes().len() as f64 / 1024.0, peak_mb());
        std::fs::create_dir_all(&dir)?;
        std::fs::write(format!("{dir}/proof_with_public_inputs.json"), serde_json::to_string(&pb)?)?;
        std::fs::write(format!("{dir}/common_circuit_data.json"), serde_json::to_string(&wb.common)?)?;
        let caps: Vec<String> = wb.verifier_only.constants_sigmas_cap.0.iter().map(|h| serde_json::to_value(h).unwrap().as_str().unwrap().to_string()).collect();
        let vo = serde_json::json!({ "constants_sigmas_cap": caps, "circuit_digest": serde_json::to_value(&wb.verifier_only.circuit_digest)? });
        std::fs::write(format!("{dir}/verifier_only_circuit_data.json"), vo.to_string())?;
        println!("wrote {dir}/");
    }

    // ---- block data: bytes, then the node's replay from (previous state, bytes, S, height)
    let bytes = blockdata::encode(n, &block);
    let pis: Vec<u64> = fin.public_inputs[0..NPI].iter().map(|x| x.to_canonical_u64()).collect();
    let n_pay: usize = block.iter().map(|l| l.pays.len()).sum();
    println!("RESULT block data: {} bytes for {} payments and credits ({} new accounts at +32 B; header 5 B + 40 B per leaf)", bytes.len(), n_pay, n_new);
    let node_check = |b: &[u8]| -> Result<blockdata::Replayed> { blockdata::replay(&genesis_state, &genesis_tree, s_coin, height, &rule, b) };
    let rp = match node_check(&bytes) { Ok(r) => r, Err(e) => { println!("RESULT node replay: block rejected ({e})"); return Ok(()); } };
    println!("RESULT node replay: root, fee total, count, data hash, S and height match the proof: {} | credits match the payouts owed: {} | fee pool after {}", rp.public_inputs() == pis, rp.credits.len(), rp.pool_after);
    println!("RESULT peg: node replay and builder agree on what every payment counts: {} | counted {} of {} paid, weighted by age {}",
        rp.counted == counted, rp.counted.iter().map(|c| c.amt).sum::<u64>(), block.iter().flat_map(|l| l.pays.iter()).filter(|e| !e.credit).map(|e| e.amt).sum::<u64>(), rp.counted.iter().map(blockdata::weight).sum::<u64>());
    let mut bad = bytes.clone(); let last = bad.len() - 1; bad[last] ^= 1;
    println!("RESULT node replay with one changed byte: accepted = {}", matches!(node_check(&bad).map(|r| r.public_inputs() == pis), Ok(true)));
    println!("RESULT node replay with S + 1: accepted = {}", matches!(blockdata::replay(&genesis_state, &genesis_tree, s_coin + 1, height, &rule, &bytes).map(|r| r.public_inputs() == pis), Ok(true)));
    let mut rule2 = rule.clone(); rule2.miner = accts[13].pk;
    println!("RESULT node replay expecting another miner: accepted = {}", matches!(blockdata::replay(&genesis_state, &genesis_tree, s_coin, height, &rule2, &bytes).map(|r| r.public_inputs() == pis), Ok(true)));
    if let Ok(dir) = std::env::var("BN_OUT") { std::fs::write(format!("{dir}/block.bin"), &bytes)?; }
    println!("RESULT stamp root matches the account tree: {} | peak {:.0} MB", (0..4).all(|k| fin.public_inputs[4 + k] == tree.root().elements[k]), peak_mb());
    Ok(())
}
