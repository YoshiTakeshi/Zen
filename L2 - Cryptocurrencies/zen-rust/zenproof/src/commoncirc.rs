// Pieces every operation leaf shares (stage P4, Justus L. Ludovic): the block header values and day/period split, the sender's account touch
// with the fee floor and the "each gram counts once" bookkeeping, and the lock's own slot. The vault and channel leaves carry their own copies of this
// (they were written first); the order and factory leaves use these.
use crate::opcirc::{limbs62, set_acct, set_path};
use crate::{ge62, hash_t, root_from, settle_t};
use crate::{Acct, D, DEPTH, F};
use anyhow::{anyhow, Result};
use plonky2::field::types::Field;
use plonky2::hash::hash_types::{HashOut, HashOutTarget};
use plonky2::iop::target::{BoolTarget, Target};
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;

pub(crate) struct Head { pub root0: HashOutTarget, pub h_t: Target, pub s_t: Target, pub day: [Target; 4] }
pub(crate) fn head(b: &mut CircuitBuilder<F, D>) -> Head {
    let root0 = b.add_virtual_hash();
    let h_t = b.add_virtual_target(); b.range_check(h_t, 32);
    let s_t = b.add_virtual_target(); b.range_check(s_t, 62);
    let day: [Target; 4] = core::array::from_fn(|_| b.add_virtual_target());
    let (d_t, rem_t, p_t, q_t) = (day[0], day[1], day[2], day[3]);
    b.range_check(d_t, 32); b.range_check(p_t, 32); b.range_check(rem_t, 10);
    let hh = b.mul_const_add(F::from_canonical_u64(crate::blockdata::BPD), d_t, rem_t); b.connect(hh, h_t);
    let top = b.constant(F::from_canonical_u64(crate::blockdata::BPD - 1));
    let rem_ok = ge62(b, top, rem_t); b.assert_one(rem_ok.target);
    let dd = b.mul_const_add(F::from_canonical_u64(crate::blockdata::REST_DAYS), p_t, q_t); b.connect(dd, d_t);
    { let q1 = b.add_const(q_t, -F::ONE); let q2 = b.add_const(q_t, -F::TWO); let m1 = b.mul(q_t, q1); let m2 = b.mul(m1, q2); b.assert_zero(m2); }
    Head { root0, h_t, s_t, day }
}
pub(crate) fn set_head(pw: &mut PartialWitness<F>, hd: &Head, height: u64, s: u64, root0: HashOut<F>) -> Result<()> {
    let (day, per) = crate::blockdata::day_period(height);
    pw.set_hash_target(hd.root0, root0)?;
    pw.set_target(hd.h_t, F::from_canonical_u64(height))?;
    pw.set_target(hd.s_t, F::from_canonical_u64(s))?;
    for (x, v) in hd.day.iter().zip([day, height - day * crate::blockdata::BPD, per, day - per * crate::blockdata::REST_DAYS]) { pw.set_target(*x, F::from_canonical_u64(v))?; }
    Ok(())
}
pub(crate) struct SndT { pub pk: [Target; 4], bal: Target, pub nonce: Target, peg: [Target; 5], bits: Vec<BoolTarget>, sib: Vec<HashOutTarget>, pub n_lo: Target, pub n_hi: Target, pub idx: Target }
/// the sender pays `give` and the fee: returns the sender's touch and the root after it
impl SndT { pub fn nonce_t(&self) -> Target { self.nonce } }
pub(crate) fn sender(b: &mut CircuitBuilder<F, D>, hd: &Head, fee: Target, give: Target) -> (SndT, HashOutTarget) {
    let (zero, one) = (b.zero(), b.one());
    let (d_t, p_t, s_t) = (hd.day[0], hd.day[2], hd.s_t);
    let t2 = b.arithmetic(F::from_canonical_u64(100), F::NEG_ONE, fee, one, s_t); b.range_check(t2, 62);       // fee >= S/100
    let pk: [Target; 4] = core::array::from_fn(|_| b.add_virtual_target());
    let (s_bal, s_nonce) = (b.add_virtual_target(), b.add_virtual_target());
    let s_peg: [Target; 5] = core::array::from_fn(|_| b.add_virtual_target());
    let bits: Vec<BoolTarget> = (0..DEPTH).map(|_| b.add_virtual_bool_target_safe()).collect();
    let sib: Vec<HashOutTarget> = (0..DEPTH).map(|_| b.add_virtual_hash()).collect();
    let (n_lo, n_hi) = limbs62(b, s_nonce);
    let mut v = pk.to_vec(); v.push(s_bal); v.push(s_nonce); v.extend(s_peg);
    let s_old = hash_t(b, v);
    let r0 = root_from(b, s_old, &bits, &sib);
    for k in 0..4 { b.connect(r0.elements[k], hd.root0.elements[k]); }
    let spend = b.add(give, fee);
    let new_bal = b.sub(s_bal, spend); b.range_check(new_bal, 62);
    let new_nonce = b.add(s_nonce, one);
    let (s_r1, s_u1, s_rd1, s_up1) = settle_t(b, s_bal, s_peg[0], s_peg[1], s_peg[2], s_peg[3], s_peg[4], d_t, p_t);
    let f1 = b.sub(s_bal, s_r1);
    let c1 = ge62(b, spend, f1);
    let from_f = b.select(c1, f1, spend);
    let from_r = b.sub(spend, from_f);
    let s_r2 = b.sub(s_r1, from_r);
    let avail = b.sub(s_r1, s_u1);
    let c2 = ge62(b, give, avail);
    let cnt = b.select(c2, avail, give);
    let usum = b.add(s_u1, cnt);
    let c3 = ge62(b, usum, from_r);
    let ud = b.sub(usum, from_r);
    let s_u2 = b.select(c3, ud, zero);
    let mut v = pk.to_vec(); v.push(new_bal); v.push(new_nonce); v.extend([s_r2, s_u2, s_peg[2], s_rd1, s_up1]);
    let s_new = hash_t(b, v);
    let cur1 = root_from(b, s_new, &bits, &sib);
    let idx = b.le_sum(bits.iter());
    (SndT { pk, bal: s_bal, nonce: s_nonce, peg: s_peg, bits, sib, n_lo, n_hi, idx }, cur1)
}
pub(crate) fn set_sender(pw: &mut PartialWitness<F>, s: &SndT, t: &crate::locks::Touch) -> Result<Acct> {
    let a = t.old.ok_or_else(|| anyhow!("the sender has no account"))?;
    set_acct(pw, &s.pk, s.bal, s.nonce, &s.peg, &a)?;
    set_path(pw, &s.bits, &s.sib, t.idx, &t.sibs)?;
    Ok(a)
}
/// the lock's own slot: its old leaf (balance, nonce, rest values), the path
pub(crate) struct LockT { pub bal: Target, pub nonce: Target, pub peg: [Target; 5], pub bits: Vec<BoolTarget>, pub sib: Vec<HashOutTarget> }
pub(crate) fn add_lock(b: &mut CircuitBuilder<F, D>) -> LockT {
    LockT { bal: b.add_virtual_target(), nonce: b.add_virtual_target(), peg: core::array::from_fn(|_| b.add_virtual_target()),
            bits: (0..DEPTH).map(|_| b.add_virtual_bool_target_safe()).collect(), sib: (0..DEPTH).map(|_| b.add_virtual_hash()).collect() }
}
pub(crate) fn set_lock(pw: &mut PartialWitness<F>, l: &LockT, t: &crate::locks::Touch) -> Result<()> {
    match t.old {
        Some(a) => { pw.set_target(l.bal, F::from_canonical_u64(a.bal))?; pw.set_target(l.nonce, F::from_canonical_u64(a.nonce))?; crate::set_peg(pw, &l.peg, &a)?; }
        None => { pw.set_target(l.bal, F::ZERO)?; pw.set_target(l.nonce, F::ZERO)?; for x in l.peg { pw.set_target(x, F::ZERO)?; } }
    }
    set_path(pw, &l.bits, &l.sib, t.idx, &t.sibs)
}
