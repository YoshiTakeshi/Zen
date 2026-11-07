// The operation leaf of the block proof, channel family (stage P3, Justus L. Ludovic).
//
// Same public values and the same shape as the vault leaf (`opcirc.rs`) and the state leaf, so the universal merge takes it too.
// One operation of
//   Make    a new channel (state open): the sender (a) pays the amount and the fee, the channel's leaf appears in an empty slot;
//   Fund    b adds coins to a channel with no posted state (the channel becomes dual-funded);
//   Start   a or b starts closing a channel nobody has updated (state 0: the share of the funder);
//   Update  anyone: a newer state signed by a and b (a alone for a stream) replaces the one waiting; the dispute window starts again;
//   Settle  after the window: a and b are paid, point locks go to their receiver when opened by a scalar (t*G = point) or back to their sender once expired;
//   Close   both sign the final balances: paid out at once.
// What each proves, besides the sender's signature, balance, nonce, fee floor and the "each gram counts once" bookkeeping (the gadgets of a payment):
//   * the lock's address is the Poseidon digest of the terms given, in the layout of `locks.rs`; a new address is the digest of the new terms;
//   * the rule of the kind: who may send it, the state it needs, the dispute window against the height, the numbers (a's share and the point locks fit in
//     what the channel holds, a stream's state, the update number grows);
//   * Update and Close: the two signatures over `chan_state_msg` / `chan_close_msg`, whose keys are the ones in the terms;
//   * Settle: for each point lock, either the scalar that opens it (the circuit computes t*G and compares) or an expiry in the past; the payouts follow;
//   * the Merkle updates in the order the node applies them: sender; a's account (if a is paid); b's account (if b is paid); the channel's own slot.
// Left to the node's own replay (the circuit holds a subset of the node's rules): that keys are points of the prime-order group and belong to the
// accounts a and b, the sign of a point's y coordinate, that a new account's address owns no other account.
use crate::opcirc::{empty_leaf_t, limbs, limbs62, limbs_of_bits, sel_hash, set_acct, set_path, tag_felt, r_of};
use crate::{cond_eq, connect_hash_if, empty_leaf, ge62, hash_t, imply_zero, pad_to, root_from, select_hash_c, settle_t};
use crate::{ec, Acct, C, D, DEPTH, F, NONCE_SHIFT, VDPI};
use anyhow::{anyhow, bail, Result};
use num_bigint::BigUint;
use plonky2::field::types::{Field, PrimeField64};
use plonky2::gates::gate::GateRef;
use plonky2::hash::hash_types::{HashOut, HashOutTarget};
use plonky2::iop::target::{BoolTarget, Target};
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CircuitData};

const NP: usize = crate::locks::MAX_PLOCKS;
/// domain tag of a channel operation's block-data hash
pub const CHAN_DATA_TAG: u64 = u64::from_le_bytes(*b"ZenChDat");
/// the message the unused signature slots verify (with a fixed key), so that they are always satisfiable
const DUMMY_MSG: [u64; 4] = [11, 22, 33, 44];

pub struct ChanLeaf { pub data: CircuitData<F, C, D>, pub t: ChT }
/// a list of up to MAX_PLOCKS point locks as witness targets
pub(crate) struct PlT { pub len: Target, pub amt: Vec<Target>, pub to_b: Vec<BoolTarget>, pub point: Vec<[Target; 11]>, pub expiry: Vec<Target> }
pub(crate) struct RcT { pub o_pk: [Target; 4], pub o_bal: Target, pub o_nonce: Target, pub o_peg: [Target; 5], pub new_r: BoolTarget, pub bits: Vec<BoolTarget>, pub sib: Vec<HashOutTarget> }
pub struct ChT {
    pub root0: HashOutTarget, pub h_t: Target, pub day: [Target; 4], pub s_t: Target,
    kinds: [BoolTarget; 6],
    fee: Target, amt: Target,
    s_pk: [Target; 4], s_bal: Target, s_nonce: Target, s_peg: [Target; 5], s_bits: Vec<BoolTarget>, s_sib: Vec<HashOutTarget>,
    sig1: ec::SigT,
    a: [Target; 4], pb: [Target; 4], ka: [Target; 11], kb: [Target; 11],
    delay: Target, oneway: BoolTarget, salt: Target, s_closing: BoolTarget, s_dual: BoolTarget,
    seq_o: Target, bala_o: Target, until_o: Target, base_o: Target,
    pl_o: PlT, pl_n: PlT, seq_n: Target, bala_n: Target,
    eb_w: [Target; 4], sb_w: [Target; 10],
    siga: ec::SigT, sigb: ec::SigT,
    wf: Vec<BoolTarget>, wpy: Vec<[Target; 5]>, wbits: Vec<Vec<BoolTarget>>,
    l_bal: Target, l_nonce: Target, l_peg: [Target; 5], lbits: Vec<BoolTarget>, lsib: Vec<HashOutTarget>,
    ra: RcT, rb: RcT,
}

pub(crate) fn add_pl(b: &mut CircuitBuilder<F, D>) -> PlT {
    PlT { len: b.add_virtual_target(),
          amt: (0..NP).map(|_| b.add_virtual_target()).collect(),
          to_b: (0..NP).map(|_| b.add_virtual_bool_target_safe()).collect(),
          point: (0..NP).map(|_| core::array::from_fn(|_| b.add_virtual_target())).collect(),
          expiry: (0..NP).map(|_| b.add_virtual_target()).collect() }
}
pub(crate) fn add_rc(b: &mut CircuitBuilder<F, D>) -> RcT {
    RcT { o_pk: core::array::from_fn(|_| b.add_virtual_target()), o_bal: b.add_virtual_target(), o_nonce: b.add_virtual_target(),
          o_peg: core::array::from_fn(|_| b.add_virtual_target()), new_r: b.add_virtual_bool_target_safe(),
          bits: (0..DEPTH).map(|_| b.add_virtual_bool_target_safe()).collect(), sib: (0..DEPTH).map(|_| b.add_virtual_hash()).collect() }
}
/// the digest of a point-lock list (the layout of `locks::plocks_digest`); also fixes the length (at most NP) and zeroes the unused slots; gives which slots are used
pub(crate) fn pl_hash(b: &mut CircuitBuilder<F, D>, p: &PlT) -> (HashOutTarget, Vec<BoolTarget>) {
    b.range_check(p.len, 4);
    let eight = b.constant(F::from_canonical_usize(NP));
    let ok = ge62(b, eight, p.len); b.assert_one(ok.target);
    let mut v = vec![b.constant(tag_felt(b"ZenPLock")), p.len];
    let mut act = vec![];
    for i in 0..NP {
        let ge = { let c = b.constant(F::from_canonical_usize(i + 1)); ge62(b, p.len, c) };
        let off = b.not(ge);
        for t in [p.amt[i], p.to_b[i].target, p.expiry[i]].into_iter().chain(p.point[i]) { imply_zero(b, off, t); }
        let (al, ah) = limbs62(b, p.amt[i]); let (el, eh) = limbs62(b, p.expiry[i]);
        v.extend([al, ah, p.to_b[i].target]); v.extend(p.point[i]); v.extend([el, eh]);
        act.push(ge);
    }
    (hash_t(b, v), act)
}
/// the digest of a channel's terms in a state (the layout of `Terms::digest`)
#[allow(clippy::too_many_arguments)]
pub(crate) fn chan_addr(b: &mut CircuitBuilder<F, D>, a: [Target; 4], pb: [Target; 4], ka: [Target; 11], kb: [Target; 11], delay: (Target, Target), oneway: Target, salt: (Target, Target),
             kind: Target, seq: (Target, Target), bala: (Target, Target), until: (Target, Target), base: (Target, Target), pl: HashOutTarget) -> HashOutTarget {
    let mut v = vec![b.constant(tag_felt(b"ZenChan."))];
    v.extend(a); v.extend(pb); v.extend(ka); v.extend(kb);
    v.extend([delay.0, delay.1, oneway, salt.0, salt.1, kind, seq.0, seq.1, bala.0, bala.1, until.0, until.1, base.0, base.1]);
    v.extend(pl.elements);
    hash_t(b, v)
}
/// x words of a 41-byte point (eleven limbs): the coordinate in the circuit's short Weierstrass form
pub(crate) fn x_words(b: &mut CircuitBuilder<F, D>, p: &[Target; 11]) -> [Target; 5] {
    core::array::from_fn(|k| { let w = b.mul_const_add(F::from_canonical_u64(1 << 32), p[2 * k + 1], p[2 * k]); b.add_const(w, ec::shift().0[k]) })
}
/// guard implies cond
pub(crate) fn need(b: &mut CircuitBuilder<F, D>, guard: BoolTarget, cond: BoolTarget) { let n = b.not(cond); let m = b.mul(guard.target, n.target); b.assert_zero(m); }
pub(crate) fn all_eq4(b: &mut CircuitBuilder<F, D>, x: [Target; 4], y: [Target; 4]) -> BoolTarget {
    let mut e = b.constant_bool(true);
    for k in 0..4 { let q = b.is_equal(x[k], y[k]); e = b.and(e, q); }
    e
}
/// receive `amount` in the account of one side: the touch is skipped unless `active`
#[allow(clippy::too_many_arguments)]
pub(crate) fn recv(b: &mut CircuitBuilder<F, D>, r: &RcT, active: BoolTarget, amount: Target, expect: [Target; 4], h_t: Target, d_t: Target, p_t: Target, cur: HashOutTarget) -> HashOutTarget {
    let mut v = r.o_pk.to_vec(); v.push(r.o_bal); v.push(r.o_nonce); v.extend(r.o_peg);
    let full = hash_t(b, v);
    let old = select_hash_c(b, r.new_r, empty_leaf(), full);
    let r0 = root_from(b, old, &r.bits, &r.sib);
    connect_hash_if(b, active, r0, cur);
    for k in 0..4 { cond_eq(b, active, r.o_pk[k], expect[k]); }
    // a new account starts blank at its address with the block's nonce
    imply_zero(b, r.new_r, r.o_bal);
    for t in r.o_peg { imply_zero(b, r.new_r, t); }
    let nonce_new = b.mul_const(F::from_canonical_u64(1 << NONCE_SHIFT), h_t);
    { let nd = b.sub(nonce_new, r.o_nonce); imply_zero(b, r.new_r, nd); }
    let nb = b.add(r.o_bal, amount);
    let rb = b.mul(nb, active.target); b.range_check(rb, 62);
    let (r1, u1, rd1, up1) = settle_t(b, r.o_bal, r.o_peg[0], r.o_peg[1], r.o_peg[2], r.o_peg[3], r.o_peg[4], d_t, p_t);
    let mut v = r.o_pk.to_vec(); v.push(nb); v.push(r.o_nonce); v.extend([r1, u1, d_t, rd1, up1]);
    let leaf = hash_t(b, v);
    let new = root_from(b, leaf, &r.bits, &r.sib);
    sel_hash(b, active, new, cur)
}

pub fn build_chan(chain: u64, prm: &ec::Params, gates: &[GateRef<F, D>], degree_bits: usize) -> ChanLeaf {
    let mut b = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());
    for g in gates { b.add_gate_to_gate_set(g.clone()); }
    ec::dbladd_reset();
    let (zero, one) = (b.zero(), b.one());
    let root0 = b.add_virtual_hash();
    let h_t = b.add_virtual_target(); b.range_check(h_t, 32);
    let s_t = b.add_virtual_target(); b.range_check(s_t, 62);
    let day: [Target; 4] = core::array::from_fn(|_| b.add_virtual_target());
    let (d_t, rem_t, p_t, q_t) = (day[0], day[1], day[2], day[3]);
    b.range_check(d_t, 32); b.range_check(p_t, 32); b.range_check(rem_t, 10);
    let hh = b.mul_const_add(F::from_canonical_u64(crate::blockdata::BPD), d_t, rem_t); b.connect(hh, h_t);
    let top = b.constant(F::from_canonical_u64(crate::blockdata::BPD - 1));
    let rem_ok = ge62(&mut b, top, rem_t); b.assert_one(rem_ok.target);
    let dd = b.mul_const_add(F::from_canonical_u64(crate::blockdata::REST_DAYS), p_t, q_t); b.connect(dd, d_t);
    { let q1 = b.add_const(q_t, -F::ONE); let q2 = b.add_const(q_t, -F::TWO); let m1 = b.mul(q_t, q1); let m2 = b.mul(m1, q2); b.assert_zero(m2); }
    let chain_t = b.constant(F::from_canonical_u64(chain));

    // ---- which operation
    let kinds: [BoolTarget; 6] = core::array::from_fn(|_| b.add_virtual_bool_target_safe());
    let [mk, st, up, se, cl, fu] = kinds;
    { let mut s = b.zero(); for k in kinds { s = b.add(s, k.target); } b.connect(s, one); }
    let gives = BoolTarget::new_unsafe(b.add(mk.target, fu.target));
    let ngives = b.not(gives);
    let pays = BoolTarget::new_unsafe(b.add(se.target, cl.target));
    let usesig = BoolTarget::new_unsafe(b.add(up.target, cl.target));
    let nse = b.not(se);
    let nmk = b.not(mk);

    // ---- the sender
    let (fee, amt) = (b.add_virtual_target(), b.add_virtual_target());
    let (fee_lo, fee_hi) = limbs62(&mut b, fee);
    let (amt_lo, amt_hi) = limbs62(&mut b, amt);
    imply_zero(&mut b, ngives, amt);                                          // only a Make and a Fund carry an amount
    let t2 = b.arithmetic(F::from_canonical_u64(100), F::NEG_ONE, fee, one, s_t); b.range_check(t2, 62);
    let t1 = b.arithmetic(F::from_canonical_u64(6), F::NEG_ONE, amt, one, s_t); let m1 = b.mul(t1, mk.target); b.range_check(m1, 62);   // a Make: amount >= S/6
    { let z = b.is_equal(amt, zero); let nz = b.not(z); need(&mut b, fu, nz); }          // a Fund adds something
    let s_pk: [Target; 4] = core::array::from_fn(|_| b.add_virtual_target());
    let (s_bal, s_nonce) = (b.add_virtual_target(), b.add_virtual_target());
    let s_peg: [Target; 5] = core::array::from_fn(|_| b.add_virtual_target());
    let s_bits: Vec<BoolTarget> = (0..DEPTH).map(|_| b.add_virtual_bool_target_safe()).collect();
    let s_sib: Vec<HashOutTarget> = (0..DEPTH).map(|_| b.add_virtual_hash()).collect();
    let (n_lo, n_hi) = limbs62(&mut b, s_nonce);
    let mut v = s_pk.to_vec(); v.push(s_bal); v.push(s_nonce); v.extend(s_peg);
    let s_old = hash_t(&mut b, v);
    let r0 = root_from(&mut b, s_old, &s_bits, &s_sib);
    for k in 0..4 { b.connect(r0.elements[k], root0.elements[k]); }
    let spend = b.add(amt, fee);
    let new_bal = b.sub(s_bal, spend); b.range_check(new_bal, 62);
    let new_nonce = b.add(s_nonce, one);
    let (s_r1, s_u1, s_rd1, s_up1) = settle_t(&mut b, s_bal, s_peg[0], s_peg[1], s_peg[2], s_peg[3], s_peg[4], d_t, p_t);
    let f1 = b.sub(s_bal, s_r1);
    let c1 = ge62(&mut b, spend, f1);
    let from_f = b.select(c1, f1, spend);
    let from_r = b.sub(spend, from_f);
    let s_r2 = b.sub(s_r1, from_r);
    let avail = b.sub(s_r1, s_u1);
    let c2 = ge62(&mut b, amt, avail);
    let cnt = b.select(c2, avail, amt);
    let usum = b.add(s_u1, cnt);
    let c3 = ge62(&mut b, usum, from_r);
    let ud = b.sub(usum, from_r);
    let s_u2 = b.select(c3, ud, zero);
    let mut v = s_pk.to_vec(); v.push(new_bal); v.push(new_nonce); v.extend([s_r2, s_u2, s_peg[2], s_rd1, s_up1]);
    let s_new = hash_t(&mut b, v);
    let cur1 = root_from(&mut b, s_new, &s_bits, &s_sib);

    // ---- the channel's terms (a Make: the new terms) and its address
    let a: [Target; 4] = core::array::from_fn(|_| b.add_virtual_target());
    let pb: [Target; 4] = core::array::from_fn(|_| b.add_virtual_target());
    let ka: [Target; 11] = core::array::from_fn(|_| b.add_virtual_target());
    let kb: [Target; 11] = core::array::from_fn(|_| b.add_virtual_target());
    let (delay, salt) = (b.add_virtual_target(), b.add_virtual_target());
    let oneway = b.add_virtual_bool_target_safe();
    let (s_closing, s_dual) = (b.add_virtual_bool_target_safe(), b.add_virtual_bool_target_safe());
    { let m = b.mul(s_closing.target, s_dual.target); b.assert_zero(m); }
    let (seq_o, bala_o, until_o, base_o) = (b.add_virtual_target(), b.add_virtual_target(), b.add_virtual_target(), b.add_virtual_target());
    let pl_o = add_pl(&mut b);
    let pl_n = add_pl(&mut b);
    let (seq_n, bala_n) = (b.add_virtual_target(), b.add_virtual_target());
    let (pld_o, act_o) = pl_hash(&mut b, &pl_o);
    let (pld_n, act_n) = pl_hash(&mut b, &pl_n);
    let (dl, salt_l) = (limbs62(&mut b, delay), limbs62(&mut b, salt));
    let (seq_ol, bala_ol, until_ol, base_ol) = (limbs62(&mut b, seq_o), limbs62(&mut b, bala_o), limbs62(&mut b, until_o), limbs62(&mut b, base_o));
    let (seq_nl, bala_nl) = (limbs62(&mut b, seq_n), limbs62(&mut b, bala_n));
    let kind_o = { let t = b.mul_const(F::TWO, s_dual.target); b.add(s_closing.target, t) };
    let addr_old = chan_addr(&mut b, a, pb, ka, kb, dl, oneway.target, salt_l, kind_o, seq_ol, bala_ol, until_ol, base_ol, pld_o);
    let s_open = { let t = b.add(s_closing.target, s_dual.target); let t = b.sub(one, t); BoolTarget::new_unsafe(t) };
    let not_closing = b.not(s_closing);

    // the lock's own leaf (a Make: nothing yet), and what an old lock must hold
    let l_bal = b.add_virtual_target();
    let l_nonce = b.add_virtual_target();
    let l_peg: [Target; 5] = core::array::from_fn(|_| b.add_virtual_target());
    let lbits: Vec<BoolTarget> = (0..DEPTH).map(|_| b.add_virtual_bool_target_safe()).collect();
    let lsib: Vec<HashOutTarget> = (0..DEPTH).map(|_| b.add_virtual_hash()).collect();
    let cap = l_bal;
    let nonce_new = b.mul_const(F::from_canonical_u64(1 << NONCE_SHIFT), h_t);

    // ---- Make: a new channel
    for k in 0..4 { cond_eq(&mut b, mk, a[k], s_pk[k]); }                                  // a is the sender
    { let e = all_eq4(&mut b, a, pb); imply_zero(&mut b, mk, e.target); }                  // a and b are two accounts
    { let c = ge62(&mut b, delay, one); need(&mut b, mk, c); let hi = b.constant(F::from_canonical_u64(100_000)); let c = ge62(&mut b, hi, delay); need(&mut b, mk, c); }
    imply_zero(&mut b, mk, s_closing.target); imply_zero(&mut b, mk, s_dual.target);       // a new channel is open
    cond_eq(&mut b, mk, salt, s_nonce);                                                   // its salt is the sender's nonce
    // ---- Start: a or b, a channel that is not closing
    { let ea = all_eq4(&mut b, s_pk, a); let eb = all_eq4(&mut b, s_pk, pb); let o = b.or(ea, eb); need(&mut b, st, o); }
    imply_zero(&mut b, st, s_closing.target);
    // ---- Fund: b, a two-way channel that is not closing
    for k in 0..4 { cond_eq(&mut b, fu, pb[k], s_pk[k]); }
    imply_zero(&mut b, fu, oneway.target);
    imply_zero(&mut b, fu, s_closing.target);
    // ---- Update
    { let z = b.is_equal(seq_n, zero); let nz = b.not(z); need(&mut b, up, nz); }                      // update numbers start at 1
    {
        let g = b.and(up, s_closing);
        let w = ge62(&mut b, until_o, h_t); need(&mut b, g, w);                                       // the window is still open
        let s1 = b.add_const(seq_o, F::ONE); let newer = ge62(&mut b, seq_n, s1); need(&mut b, g, newer);
    }
    {   // the shares and the point locks fit in what the channel holds (prefix sums, so nothing wraps)
        let mut tot = bala_n;
        let r = b.sub(cap, tot); let r = b.mul(r, up.target); b.range_check(r, 62);
        for i in 0..NP {
            tot = b.add(tot, pl_n.amt[i]);
            let r = b.sub(cap, tot); let r = b.mul(r, up.target); b.range_check(r, 62);
            // an used point lock has an amount and a future expiry
            let z = b.is_equal(pl_n.amt[i], zero); let nz = b.not(z);
            let g = b.and(up, act_n[i]); need(&mut b, g, nz);
            let h1 = b.add_const(h_t, F::ONE); let fut = ge62(&mut b, pl_n.expiry[i], h1); need(&mut b, g, fut);
        }
        // a stream holds no point locks, and its state is the amount paid
        let g = b.and(up, oneway); imply_zero(&mut b, g, pl_n.len);
        let left = b.sub(cap, seq_n); let d = b.sub(bala_n, left); imply_zero(&mut b, g, d);
        let ok = b.mul(left, g.target); b.range_check(ok, 62);
    }
    // the new point locks are given only for an update; the update's numbers only for an update or a close
    { let nup = b.not(up); imply_zero(&mut b, nup, pl_n.len); imply_zero(&mut b, nup, seq_n); let nus = b.not(usesig); imply_zero(&mut b, nus, bala_n); }
    // ---- Close
    {
        imply_zero(&mut b, cl, pl_o.len);                                                           // no point locks waiting
        let g = b.and(cl, s_closing); let w = ge62(&mut b, until_o, h_t); need(&mut b, g, w);        // the window is still open
        let w = ge62(&mut b, cap, bala_n); need(&mut b, cl, w);                                     // a's share is within the channel
    }

    // ---- the new state of the terms (Start, Update, Fund) and the lock's leaves
    let st_up = BoolTarget::new_unsafe(b.add(st.target, up.target));
    let cap_a = b.select(s_dual, base_o, cap);
    let nk = { let t = b.mul_const(F::TWO, fu.target); b.add(st_up.target, t) };
    let nseq = { let z = b.mul(up.target, seq_n); limbs62(&mut b, z) };
    let nbala = { let x = b.mul(up.target, bala_n); let y = b.mul(st.target, cap_a); let z = b.add(x, y); limbs62(&mut b, z) };
    let nuntil = { let hd = b.add(h_t, delay); let z = b.mul(st_up.target, hd); limbs62(&mut b, z) };
    let nbase = { let z = b.mul(fu.target, cap_a); limbs62(&mut b, z) };
    let addr_new = chan_addr(&mut b, a, pb, ka, kb, dl, oneway.target, salt_l, nk, nseq, nbala, nuntil, nbase, pld_n);
    let lbal_new = { let t = b.mul(fu.target, amt); b.add(cap, t) }; b.range_check(lbal_new, 62);
    let mk_leaf = { let mut v = addr_old.elements.to_vec(); v.push(amt); v.push(nonce_new); v.extend([zero; 5]); hash_t(&mut b, v) };
    let ret_leaf = { let mut v = addr_new.elements.to_vec(); v.push(lbal_new); v.push(l_nonce); v.extend([zero; 5]); hash_t(&mut b, v) };
    let old_leaf = { let mut v = addr_old.elements.to_vec(); v.push(l_bal); v.push(l_nonce); v.extend(l_peg); hash_t(&mut b, v) };

    // ---- the channel's id, and what a and b sign
    let id = { let mut v = vec![b.constant(tag_felt(b"ZenChnId"))]; v.extend(a); v.extend(pb); v.extend(ka); v.extend(kb); v.extend([dl.0, dl.1, oneway.target, salt_l.0, salt_l.1]); hash_t(&mut b, v) };
    let (cap_l, _) = (limbs62(&mut b, cap), 0);
    let msg_state = { let mut v = vec![b.constant(tag_felt(b"ZenCSta.")), chain_t]; v.extend(id.elements); v.extend([seq_nl.0, seq_nl.1, bala_nl.0, bala_nl.1, cap_l.0, cap_l.1]); v.extend(pld_n.elements); hash_t(&mut b, v) };
    let msg_close = { let mut v = vec![b.constant(tag_felt(b"ZenCClo.")), chain_t]; v.extend(id.elements); v.extend([bala_nl.0, bala_nl.1, cap_l.0, cap_l.1]); hash_t(&mut b, v) };
    let msg_real = sel_hash(&mut b, up, msg_state, msg_close);
    let dummy = HashOutTarget { elements: core::array::from_fn(|k| b.constant(F::from_canonical_u64(DUMMY_MSG[k]))) };
    let use_a = usesig;
    let use_b = { let no = b.not(oneway); b.and(usesig, no) };
    let msg_a = sel_hash(&mut b, use_a, msg_real, dummy);
    let msg_b = sel_hash(&mut b, use_b, msg_real, dummy);
    let (siga, _pka, ea_bits) = ec::verify_sig_e(&mut b, prm, msg_a.elements);
    let xa = x_words(&mut b, &ka);
    for k in 0..5 { cond_eq(&mut b, use_a, siga.a.x[k], xa[k]); }
    let (sigb, _pkb, eb_bits) = ec::verify_sig_e(&mut b, prm, msg_b.elements);
    let xb = x_words(&mut b, &kb);
    for k in 0..5 { cond_eq(&mut b, use_b, sigb.a.x[k], xb[k]); }
    let ea_l = limbs_of_bits(&mut b, &ea_bits);
    let eb_d = limbs_of_bits(&mut b, &eb_bits);
    let mut sa_bits = siga.s_bits.clone(); sa_bits.push(BoolTarget::new_unsafe(zero));
    let sa_l = limbs_of_bits(&mut b, &sa_bits);
    let mut sb_bits = sigb.s_bits.clone(); sb_bits.push(BoolTarget::new_unsafe(zero));
    let sb_d = limbs_of_bits(&mut b, &sb_bits);
    // a stream has no signature of b: the operation carries whatever it likes in its place, which the sender signs
    let eb_w: [Target; 4] = core::array::from_fn(|_| b.add_virtual_target());
    let sb_w: [Target; 10] = core::array::from_fn(|_| b.add_virtual_target());
    for t in eb_w.iter().chain(sb_w.iter()) { b.range_check(*t, 32); }
    let eb_l: Vec<Target> = (0..4).map(|k| b.select(oneway, eb_w[k], eb_d[k])).collect();
    let sb_l: Vec<Target> = (0..10).map(|k| b.select(oneway, sb_w[k], sb_d[k])).collect();
    let mut sigs28: Vec<Target> = ea_l.clone(); sigs28.extend(sa_l.iter().copied()); sigs28.extend(eb_l); sigs28.extend(sb_l);

    // ---- Settle: the point locks. Per slot: an opening scalar (or not), the payout side that follows
    let gx = ec::sw(prm.g);
    let mut wf = vec![]; let mut wpy = vec![]; let mut wbits = vec![];
    let mut wit_v = vec![b.constant(tag_felt(b"ZenWits.")), pl_o.len];
    let mut pay_a_se = bala_o;
    for i in 0..NP {
        let flag = b.add_virtual_bool_target_safe();
        imply_zero(&mut b, nse, flag.target);
        let off = b.not(act_o[i]); imply_zero(&mut b, off, flag.target);
        let py: [Target; 5] = core::array::from_fn(|_| b.add_virtual_target());
        let xw = x_words(&mut b, &pl_o.point[i]);
        let px_u: [Target; 5] = core::array::from_fn(|k| { let gk = b.constant(gx.0.0[k]); b.select(flag, xw[k], gk) });
        let py_u: [Target; 5] = core::array::from_fn(|k| { let gk = b.constant(gx.1.0[k]); b.select(flag, py[k], gk) });
        let tb = ec::verify_mul_g(&mut b, prm, ec::PT { x: px_u, y: py_u });
        // not opened: the lock must have expired (a Settle only)
        let e1 = b.add_const(pl_o.expiry[i], F::ONE);
        let past = ge62(&mut b, h_t, e1);
        let g = b.and(se, act_o[i]);
        let ok = b.or(flag, past); need(&mut b, g, ok);
        // the side that gets it: its receiver if opened, its sender if not
        let nf = b.not(flag);
        let x = b.mul(pl_o.to_b[i].target, nf.target);
        let eff = { let t = b.add(pl_o.to_b[i].target, nf.target); let t2 = b.mul_const(F::TWO, x); b.sub(t, t2) };
        let keep = b.sub(one, eff);
        pay_a_se = b.mul_add(pl_o.amt[i], keep, pay_a_se);
        // the witnesses as the sender signs them: a flag and the scalar, zero when absent
        let mut tbz = tb.clone(); tbz.push(BoolTarget::new_unsafe(zero));
        let tl = limbs_of_bits(&mut b, &tbz);
        wit_v.push(flag.target);
        for l in tl { let m = b.mul(l, flag.target); wit_v.push(m); }
        wf.push(flag); wpy.push(py); wbits.push(tb);
    }
    let wits_d = hash_t(&mut b, wit_v);
    // the settle needs a closing channel whose window has run out
    need(&mut b, se, s_closing);
    { let u1 = b.add_const(until_o, F::ONE); let over = ge62(&mut b, h_t, u1); need(&mut b, se, over); }
    // payouts
    let pay_a = { let x = b.mul(se.target, pay_a_se); let y = b.mul(cl.target, bala_n); b.add(x, y) };
    b.range_check(pay_a, 62);
    let pay_b = { let r = b.sub(cap, pay_a); b.mul(r, pays.target) };
    b.range_check(pay_b, 62);
    let act_a = { let z = b.is_equal(pay_a, zero); let nz = b.not(z); b.and(pays, nz) };
    let act_b = { let z = b.is_equal(pay_b, zero); let nz = b.not(z); b.and(pays, nz) };
    let (ra, rb) = (add_rc(&mut b), add_rc(&mut b));
    let cur2 = recv(&mut b, &ra, act_a, pay_a, a, h_t, d_t, p_t, cur1);
    let cur3 = recv(&mut b, &rb, act_b, pay_b, pb, h_t, d_t, p_t, cur2);

    // ---- the channel's own slot: a Make fills it, a Settle and a Close empty it, the rest change it
    let old_l = select_hash_c(&mut b, mk, empty_leaf(), old_leaf);
    let r3 = root_from(&mut b, old_l, &lbits, &lsib);
    for k in 0..4 { b.connect(r3.elements[k], cur3.elements[k]); }
    let el = empty_leaf_t(&mut b);
    let new_l = {
        let moved = sel_hash(&mut b, mk, mk_leaf, ret_leaf);
        sel_hash(&mut b, pays, el, moved)
    };
    let fin = root_from(&mut b, new_l, &lbits, &lsib);

    // ---- the sender's signature over the operation message
    let head = |b: &mut CircuitBuilder<F, D>, kind: u64| -> Vec<Target> {
        let mut v = vec![b.constant(tag_felt(b"ZenOp...")), chain_t, n_lo, n_hi, b.constant(F::from_canonical_u64(kind))]; v.extend(s_pk); v.extend([fee_lo, fee_hi]); v
    };
    let m_mk = { let mut v = head(&mut b, 1); v.extend([amt_lo, amt_hi]); v.extend(addr_old.elements); hash_t(&mut b, v) };
    let m_st = { let mut v = head(&mut b, 8); v.extend(addr_old.elements); hash_t(&mut b, v) };
    let m_up = { let mut v = head(&mut b, 9); v.extend(addr_old.elements); v.extend([seq_nl.0, seq_nl.1, bala_nl.0, bala_nl.1]); v.extend(pld_n.elements); v.extend(sigs28.iter().copied()); hash_t(&mut b, v) };
    let m_se = { let mut v = head(&mut b, 10); v.extend(addr_old.elements); v.extend(wits_d.elements); hash_t(&mut b, v) };
    let m_cl = { let mut v = head(&mut b, 11); v.extend(addr_old.elements); v.extend([bala_nl.0, bala_nl.1]); v.extend(sigs28.iter().copied()); hash_t(&mut b, v) };
    let m_fu = { let mut v = head(&mut b, 18); v.extend(addr_old.elements); v.extend([amt_lo, amt_hi]); hash_t(&mut b, v) };
    let msg1: [Target; 4] = core::array::from_fn(|k| {
        let mut acc = b.zero();
        for (kd, m) in [(mk, &m_mk), (st, &m_st), (up, &m_up), (se, &m_se), (cl, &m_cl), (fu, &m_fu)] { acc = b.mul_add(kd.target, m.elements[k], acc); }
        acc
    });
    let (sig1, pk1) = ec::verify_sig(&mut b, prm, msg1);
    for k in 0..4 { b.connect(pk1[k], s_pk[k]); }
    ec::dbladd_pad(&mut b, prm);

    // ---- block data: the operation as the node writes it
    let s_idx = b.le_sum(s_bits.iter()); let l_idx = b.le_sum(lbits.iter());
    let (ia, ib) = (b.le_sum(ra.bits.iter()), b.le_sum(rb.bits.iter()));
    let mut kind = b.zero();
    for (kd, code) in [(mk, 1u64), (st, 8), (up, 9), (se, 10), (cl, 11), (fu, 18)] { kind = b.mul_const_add(F::from_canonical_u64(code), kd.target, kind); }
    let mut data = vec![b.constant(F::from_canonical_u64(CHAN_DATA_TAG)), kind, s_idx, fee_lo, fee_hi, amt_lo, amt_hi, l_idx];
    for (idx, r) in [(ia, &ra), (ib, &rb)] {
        data.push(idx); data.push(r.new_r.target);
        for k in 0..4 { data.push(b.mul(r.o_pk[k], r.new_r.target)); }
    }
    for k in 0..4 { data.push(b.mul(addr_old.elements[k], mk.target)); }
    data.push(b.mul(seq_nl.0, up.target)); data.push(b.mul(seq_nl.1, up.target));
    data.push(b.mul(bala_nl.0, usesig.target)); data.push(b.mul(bala_nl.1, usesig.target));
    for k in 0..4 { data.push(b.mul(pld_n.elements[k], up.target)); }
    for x in &sigs28 { data.push(b.mul(*x, usesig.target)); }
    for k in 0..4 { data.push(b.mul(wits_d.elements[k], se.target)); }
    let data_h = hash_t(&mut b, data);

    b.register_public_inputs(&root0.elements);
    b.register_public_inputs(&fin.elements);
    b.register_public_input(fee);
    b.register_public_input(one);
    b.register_public_inputs(&data_h.elements);
    b.register_public_input(s_t);
    b.register_public_input(h_t);
    for _ in 0..VDPI { b.register_public_input(zero); }
    pad_to(&mut b, degree_bits);
    let t = ChT { root0, h_t, day, s_t, kinds, fee, amt, s_pk, s_bal, s_nonce, s_peg, s_bits, s_sib, sig1, a, pb, ka, kb, delay, oneway, salt, s_closing, s_dual,
                  seq_o, bala_o, until_o, base_o, pl_o, pl_n, seq_n, bala_n, eb_w, sb_w, siga, sigb, wf, wpy, wbits, l_bal, l_nonce, l_peg, lbits, lsib, ra, rb };
    let _ = (s_open, not_closing, nmk, act_a, act_b);
    ChanLeaf { data: b.build::<C>(), t }
}

// ---------------------------------------------------------------- the witness
pub struct ChanInput<'a> {
    pub op: &'a crate::locks::Op, pub trace: &'a crate::locks::OpTrace, pub height: u64, pub s: u64, pub root0: HashOut<F>, pub chain: u8,
    /// the sender's key and its signature (e, s) over `SignedOp::message` of this operation
    pub sender_a: ec::P, pub sender_sig: (u128, BigUint),
}
pub(crate) fn set_pl(pw: &mut PartialWitness<F>, p: &PlT, l: &[crate::locks::PLock]) -> Result<()> {
    pw.set_target(p.len, F::from_canonical_usize(l.len()))?;
    for i in 0..NP {
        let z = crate::locks::PLock { amt: 0, to_b: false, point: [0u8; 41], expiry: 0 };
        let x = l.get(i).unwrap_or(&z);
        pw.set_target(p.amt[i], F::from_canonical_u64(x.amt))?; pw.set_bool_target(p.to_b[i], x.to_b)?;
        pw.set_target_arr(&p.point[i], &limbs(&x.point))?; pw.set_target(p.expiry[i], F::from_canonical_u64(x.expiry))?;
    }
    Ok(())
}
pub(crate) fn set_rc(pw: &mut PartialWitness<F>, r: &RcT, touch: Option<&crate::locks::Touch>, dest: Option<&crate::locks::Dest>, height: u64, like: &Acct) -> Result<()> {
    let z4 = [F::ZERO; 4];
    match touch {
        Some(t) => {
            let new = t.old.is_none();
            let acct = match t.old { Some(a) => a, None => Acct::blank(dest.and_then(|d| d.new).ok_or_else(|| anyhow!("an empty slot needs a new address"))?, height << NONCE_SHIFT, like) };
            set_acct(pw, &r.o_pk, r.o_bal, r.o_nonce, &r.o_peg, &acct)?; pw.set_bool_target(r.new_r, new)?;
            set_path(pw, &r.bits, &r.sib, t.idx, &t.sibs)?;
        }
        None => {
            // not paid: the destination as the operation names it, bound by the data hash, nothing else checked
            let (idx, new) = match dest { Some(d) => (d.idx as u64, d.new), None => (0, None) };
            let acct = Acct { pk: new.unwrap_or(z4), bal: 0, nonce: if new.is_some() { height << NONCE_SHIFT } else { 0 }, rest: 0, used: 0, fd: 0, rd: 0, up: 0, ..*like };
            set_acct(pw, &r.o_pk, r.o_bal, r.o_nonce, &r.o_peg, &acct)?; pw.set_bool_target(r.new_r, new.is_some())?;
            let zs = vec![HashOut { elements: z4 }; DEPTH];
            set_path(pw, &r.bits, &r.sib, idx, &zs)?;
        }
    }
    Ok(())
}
pub(crate) fn bits_of(x: &BigUint) -> Vec<bool> { (0..ec::S_BITS).map(|i| x.bit(i as u64)).collect() }
pub fn set_witness(l: &ChanLeaf, pw: &mut PartialWitness<F>, inp: &ChanInput) -> Result<()> {
    use crate::locks::{ChanSigs, ChanState, Op, Terms};
    let t = &l.t;
    let prm = ec::params();
    let (day, per) = crate::blockdata::day_period(inp.height);
    pw.set_hash_target(t.root0, inp.root0)?;
    pw.set_target(t.h_t, F::from_canonical_u64(inp.height))?;
    pw.set_target(t.s_t, F::from_canonical_u64(inp.s))?;
    for (x, v) in t.day.iter().zip([day, inp.height - day * crate::blockdata::BPD, per, day - per * crate::blockdata::REST_DAYS]) { pw.set_target(*x, F::from_canonical_u64(v))?; }
    let tc = &inp.trace.touches;
    if tc.len() < 2 { bail!("an operation touches at least the sender and the channel"); }
    let sender = tc[0].old.ok_or_else(|| anyhow!("the sender has no account"))?;
    let (fee, amt) = match inp.op {
        Op::Make { fee, amt, .. } => (*fee, *amt),
        Op::ChanFund { fee, amt, .. } => (*fee, *amt),
        Op::ChanStart { fee, .. } | Op::ChanUpdate { fee, .. } | Op::ChanSettle { fee, .. } | Op::ChanClose { fee, .. } => (*fee, 0),
        _ => bail!("not a channel operation"),
    };
    let which = match inp.op { Op::Make { .. } => 0, Op::ChanStart { .. } => 1, Op::ChanUpdate { .. } => 2, Op::ChanSettle { .. } => 3, Op::ChanClose { .. } => 4, _ => 5 };
    for (i, bt) in t.kinds.iter().enumerate() { pw.set_bool_target(*bt, i == which)?; }
    pw.set_target(t.fee, F::from_canonical_u64(fee))?; pw.set_target(t.amt, F::from_canonical_u64(amt))?;
    set_acct(pw, &t.s_pk, t.s_bal, t.s_nonce, &t.s_peg, &sender)?;
    set_path(pw, &t.s_bits, &t.s_sib, tc[0].idx, &tc[0].sibs)?;
    // the terms
    let terms = inp.trace.terms.clone().ok_or_else(|| anyhow!("no terms"))?;
    let Terms::Channel { a, b: pb, key_a, key_b, delay, oneway, salt, state } = terms.clone() else { bail!("not a channel") };
    pw.set_target_arr(&t.a, &a)?; pw.set_target_arr(&t.pb, &pb)?;
    pw.set_target_arr(&t.ka, &limbs(&key_a))?; pw.set_target_arr(&t.kb, &limbs(&key_b))?;
    pw.set_target(t.delay, F::from_canonical_u64(delay))?; pw.set_bool_target(t.oneway, oneway)?; pw.set_target(t.salt, F::from_canonical_u64(salt))?;
    let (mut closing, mut dual, mut seq_o, mut bala_o, mut until_o, mut base_o) = (false, false, 0, 0, 0, 0);
    let mut plocks_o = vec![];
    match &state {
        ChanState::Open => {}
        ChanState::OpenDual { base_a } => { dual = true; base_o = *base_a; }
        ChanState::Closing { seq, bal_a, until, locks } => { closing = true; seq_o = *seq; bala_o = *bal_a; until_o = *until; plocks_o = locks.clone(); }
    }
    pw.set_bool_target(t.s_closing, closing)?; pw.set_bool_target(t.s_dual, dual)?;
    for (x, v) in [(t.seq_o, seq_o), (t.bala_o, bala_o), (t.until_o, until_o), (t.base_o, base_o)] { pw.set_target(x, F::from_canonical_u64(v))?; }
    set_pl(pw, &t.pl_o, &plocks_o)?;
    // the operation's own numbers
    let (mut plocks_n, mut seq_n, mut bala_n) = (vec![], 0u64, 0u64);
    let mut sigs: Option<ChanSigs> = None;
    match inp.op {
        Op::ChanUpdate { seq, bal_a, locks, sigs: g, .. } => { plocks_n = locks.clone(); seq_n = *seq; bala_n = *bal_a; sigs = Some(*g); }
        Op::ChanClose { bal_a, sigs: g, .. } => { bala_n = *bal_a; sigs = Some(*g); }
        _ => {}
    }
    set_pl(pw, &t.pl_n, &plocks_n)?;
    pw.set_target(t.seq_n, F::from_canonical_u64(seq_n))?; pw.set_target(t.bala_n, F::from_canonical_u64(bala_n))?;
    let g = sigs.unwrap_or(ChanSigs::NONE);
    let l32 = |b: &[u8]| limbs(b);
    pw.set_target_arr(&t.eb_w, &l32(&g.eb.to_le_bytes()))?; pw.set_target_arr(&t.sb_w, &l32(&g.sb))?;
    // the lock's own leaf (the last touch)
    let lt = tc.last().unwrap();
    let cap = match inp.op { Op::Make { .. } => 0, _ => lt.old.ok_or_else(|| anyhow!("no channel leaf"))?.bal };
    match lt.old {
        Some(a) => { pw.set_target(t.l_bal, F::from_canonical_u64(a.bal))?; pw.set_target(t.l_nonce, F::from_canonical_u64(a.nonce))?; crate::set_peg(pw, &t.l_peg, &a)?; }
        None => { pw.set_target(t.l_bal, F::ZERO)?; pw.set_target(t.l_nonce, F::ZERO)?; for x in t.l_peg { pw.set_target(x, F::ZERO)?; } }
    }
    set_path(pw, &t.lbits, &t.lsib, lt.idx, &lt.sibs)?;
    // payouts: who is paid, which touches are theirs
    let (mut pay_a, mut pay_b) = (0u128, 0u128);
    let (mut to_a, mut to_b) = (None, None);
    let mut wits: Vec<Option<[u8; 40]>> = vec![];
    match inp.op {
        Op::ChanSettle { wits: w, to_a: x, to_b: y, .. } => {
            to_a = Some(*x); to_b = Some(*y); wits = w.clone();
            let total: u128 = plocks_o.iter().map(|p| p.amt as u128).sum();
            pay_a = bala_o as u128; pay_b = cap as u128 - bala_o as u128 - total;
            for (p, w) in plocks_o.iter().zip(&wits) {
                let opened = w.as_ref().map_or(false, |s| p.opened_by(s));
                if if opened { p.to_b } else { !p.to_b } { pay_b += p.amt as u128 } else { pay_a += p.amt as u128 }
            }
        }
        Op::ChanClose { bal_a, to_a: x, to_b: y, .. } => { to_a = Some(*x); to_b = Some(*y); pay_a = *bal_a as u128; pay_b = cap as u128 - *bal_a as u128; }
        _ => {}
    }
    let mid = &tc[1..tc.len() - 1];
    let mut it = mid.iter();
    let ta = if pay_a > 0 { it.next() } else { None };
    let tb = if pay_b > 0 { it.next() } else { None };
    if it.next().is_some() { bail!("more touches than payouts"); }
    set_rc(pw, &t.ra, ta, to_a.as_ref(), inp.height, &sender)?;
    set_rc(pw, &t.rb, tb, to_b.as_ref(), inp.height, &sender)?;
    // the opening scalars of a settle, else the dummy scalar 1
    let gy = ec::sw(prm.g).1;
    for i in 0..NP {
        let open = if let Op::ChanSettle { .. } = inp.op { wits.get(i).and_then(|w| *w).filter(|_| i < plocks_o.len()) } else { None };
        match open {
            Some(s) => {
                let sv = BigUint::from_bytes_le(&s);
                let p = crate::mint::decode_point(&plocks_o[i].point)?;
                pw.set_bool_target(t.wf[i], true)?;
                for (k, v) in ec::sw(p).1.0.iter().enumerate() { pw.set_target(t.wpy[i][k], *v)?; }
                for (k, bt) in bits_of(&sv).into_iter().enumerate() { pw.set_bool_target(t.wbits[i][k], bt)?; }
            }
            None => {
                pw.set_bool_target(t.wf[i], false)?;
                for (k, v) in gy.0.iter().enumerate() { pw.set_target(t.wpy[i][k], *v)?; }
                for (k, bt) in bits_of(&BigUint::from(1u32)).into_iter().enumerate() { pw.set_bool_target(t.wbits[i][k], bt)?; }
            }
        }
    }
    // the signatures: the sender's; a's and b's over the state or the close, else a fixed key's over the dummy message
    let (e1, s1) = &inp.sender_sig;
    crate::set_sig(pw, &t.sig1, inp.sender_a, r_of(inp.sender_a, *e1, s1), s1, false)?;
    let pad = crate::mint::Key::from_secret(BigUint::from(7777u32));
    let dummy: [F; 4] = std::array::from_fn(|k| F::from_canonical_u64(DUMMY_MSG[k]));
    let (de, ds) = crate::mint::sign(&pad, dummy);
    let usesig = matches!(inp.op, Op::ChanUpdate { .. } | Op::ChanClose { .. });
    let fixed = |pw: &mut PartialWitness<F>, st: &ec::SigT| crate::set_sig(pw, st, pad.a, r_of(pad.a, de, &ds), &ds, false);
    if usesig {
        let pa = crate::mint::decode_point(&key_a)?;
        let sa = BigUint::from_bytes_le(&g.sa);
        crate::set_sig(pw, &t.siga, pa, r_of(pa, g.ea, &sa), &sa, false)?;
        if !oneway {
            let pbk = crate::mint::decode_point(&key_b)?;
            let sb = BigUint::from_bytes_le(&g.sb);
            crate::set_sig(pw, &t.sigb, pbk, r_of(pbk, g.eb, &sb), &sb, false)?;
        } else { fixed(pw, &t.sigb)?; }
    } else { fixed(pw, &t.siga)?; fixed(pw, &t.sigb)?; }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::locks::{self, ChanSigs, ChanState, CrossMode, Ctx, Dest, Op, OpReq, PLock, SignedOp, Terms};
    use crate::mint;
    use crate::node::dev;
    use crate::node::{Chain, DevStamp, Params};
    use crate::Tree;
    use std::collections::HashMap;
    use std::sync::OnceLock;

    const FEE: u64 = 10_000;
    const S: u64 = 1_000_000;
    fn leaf() -> &'static ChanLeaf { static L: OnceLock<ChanLeaf> = OnceLock::new(); L.get_or_init(|| build_chan(Params::devnet().chain as u64, &ec::params(), &[], 0)) }
    #[derive(Clone)]
    struct World { state: HashMap<u64, Acct>, tree: Tree, locks: locks::LockTable, chain: u8, tmpl: Acct }
    fn keys() -> Vec<mint::Key> { dev::devnet_keys(8) }
    fn world() -> World {
        let ks = keys();
        let c = Chain::open(Params::devnet(), &dev::genesis_of(&ks), Box::new(DevStamp), None).unwrap();
        let tmpl = *c.state.values().next().unwrap();
        World { state: c.state.clone(), tree: c.tree.clone(), locks: c.locks.clone(), chain: c.p.chain, tmpl }
    }
    impl World {
        fn idx(&self, k: &mint::Key) -> u32 { self.state.iter().find(|(_, a)| a.pk == k.addr).map(|(i, _)| *i as u32).unwrap() }
        fn nonce(&self, k: &mint::Key) -> u64 { self.state[&(self.idx(k) as u64)].nonce }
        fn native(&mut self, op: &Op, height: u64) -> locks::OpTrace {
            let mut traces = vec![];
            let ctx = Ctx { chain: self.chain, ntime: 0, cross: &CrossMode::Off };
            locks::apply_ops_traced(std::slice::from_ref(op), &mut self.state, &mut self.tree, &mut self.locks, S, height, &ctx, self.tmpl, Some(&mut traces)).unwrap();
            traces.remove(0)
        }
        fn try_native(&self, op: &Op, height: u64) -> bool {
            let mut w = self.clone();
            let ctx = Ctx { chain: w.chain, ntime: 0, cross: &CrossMode::Off };
            locks::apply_ops_traced(std::slice::from_ref(op), &mut w.state, &mut w.tree, &mut w.locks, S, height, &ctx, w.tmpl, None).is_ok()
        }
        /// prove: the public values when the proof comes out and checks; none when the witness is refused or the proof is bad
        fn attempt(&self, op: &Op, trace: &locks::OpTrace, height: u64, root0: HashOut<F>, signer: &mint::Key) -> Option<Vec<u64>> {
            let req = crate::opcirc::req_of(op, &self.state).ok()?;
            let nonce = trace.touches[0].old.unwrap().nonce;
            let (e, sv) = mint::sign(signer, SignedOp::message(self.chain, nonce, &req));
            let inp = ChanInput { op, trace, height, s: S, root0, chain: self.chain, sender_a: signer.a, sender_sig: (e, sv) };
            let mut pw = PartialWitness::new();
            if set_witness(leaf(), &mut pw, &inp).is_err() { return None; }
            let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| leaf().data.prove(pw)));
            let Ok(Ok(proof)) = r else { return None };
            let pis: Vec<u64> = proof.public_inputs.iter().map(|x| x.to_canonical_u64()).collect();
            leaf().data.verify(proof).ok().map(|_| pis)
        }
        /// the operation on the node and in the circuit: the public values must be the node's
        fn both(&mut self, op: &Op, height: u64, signer: &mint::Key) -> Vec<u64> {
            let root0 = self.tree.root();
            let before = self.clone();
            let tr = self.native(op, height);
            let pis = before.attempt(op, &tr, height, root0, signer).unwrap_or_else(|| panic!("the circuit does not prove {:?}", std::mem::discriminant(op)));
            check_pis(&pis, root0, self.tree.root(), op, height);
            pis
        }
    }
    fn felts(h: HashOut<F>) -> Vec<u64> { h.elements.iter().map(|x| x.to_canonical_u64()).collect() }
    fn check_pis(pis: &[u64], root0: HashOut<F>, root1: HashOut<F>, op: &Op, h: u64) {
        assert_eq!(pis.len(), 84);
        assert_eq!(&pis[0..4], &felts(root0)[..], "root before");
        assert_eq!(&pis[4..8], &felts(root1)[..], "root after");
        assert_eq!((pis[8], pis[9]), (op.fee(), 1), "fee and count");
        assert_eq!(&pis[10..14], &locks::chan_data_hash(op).unwrap().map(|x| x.to_canonical_u64())[..], "the data hash is the node's");
        assert_eq!((pis[14], pis[15]), (S, h));
        assert!(pis[16..].iter().all(|x| *x == 0));
    }
    fn chan(a: &mint::Key, b: &mint::Key, delay: u64, oneway: bool, salt: u64) -> Terms {
        Terms::Channel { a: a.addr, b: b.addr, key_a: mint::encode_point(a.a), key_b: mint::encode_point(b.a), delay, oneway, salt, state: ChanState::Open }
    }
    fn state_sigs(w: &World, t: &Terms, a: &mint::Key, b: Option<&mint::Key>, seq: u64, bal_a: u64, cap: u64, pl: &[PLock]) -> ChanSigs {
        let msg = locks::chan_state_msg(w.chain, &t.channel_id().unwrap(), seq, bal_a, cap, pl);
        let (ea, sa) = mint::sign(a, msg);
        let (eb, sb) = b.map_or((0, num_bigint::BigUint::from(0u32)), |b| mint::sign(b, msg));
        ChanSigs { ea, sa: mint::s_bytes(&sa), eb, sb: mint::s_bytes(&sb) }
    }
    fn close_sigs(w: &World, t: &Terms, a: &mint::Key, b: &mint::Key, bal_a: u64, cap: u64) -> ChanSigs {
        let msg = locks::chan_close_msg(w.chain, &t.channel_id().unwrap(), bal_a, cap);
        let (ea, sa) = mint::sign(a, msg); let (eb, sb) = mint::sign(b, msg);
        ChanSigs { ea, sa: mint::s_bytes(&sa), eb, sb: mint::s_bytes(&sb) }
    }
    fn plock(t: u32, amt: u64, to_b: bool, expiry: u64) -> (PLock, [u8; 40]) {
        let k = num_bigint::BigUint::from(t);
        (PLock { amt, to_b, point: mint::encode_point(ec::mul_g(&ec::params(), &k)), expiry }, mint::s_bytes(&k))
    }
    fn open_channel(w: &mut World, ks: &[mint::Key], at: u32, amt: u64, delay: u64, oneway: bool, h: u64) -> Terms {
        let (a, b) = (&ks[4], &ks[5]);
        let nonce = w.nonce(a);
        let terms = chan(a, b, delay, oneway, nonce);
        let make = Op::Make { from: w.idx(a), fee: FEE, amt, at, terms: terms.clone() };
        w.both(&make, h, a);
        terms
    }

    #[test]
    fn the_channel_leaf_builds_and_its_size_is_known() {
        let t = std::time::Instant::now();
        let l = leaf();
        println!("RESULT channel leaf: 2^{} rows, {} gates, {} public values, build {:.1}s", l.data.common.degree_bits(), l.data.common.gates.len(), l.data.common.num_public_inputs, t.elapsed().as_secs_f64());
    }

    #[test]
    fn a_channel_is_made_funded_updated_and_settled_with_point_locks() {
        let ks = keys();
        let mut w = world();
        let (a, b, anyone) = (ks[4].clone(), ks[5].clone(), ks[7].clone());
        let terms = open_channel(&mut w, &ks, 5000, 600_000_000, 5, false, 3);
        // b adds coins
        let fund = Op::ChanFund { from: w.idx(&b), fee: FEE, lock: 5000, amt: 200_000_000 };
        w.both(&fund, 4, &b);
        let cap = 800_000_000u64;
        // a newer state with two point locks, signed by both; anyone sends it
        let (p1, t1) = plock(11, 100_000_000, true, 100);
        let (p2, _t2) = plock(12, 50_000_000, false, 8);
        let pl = vec![p1.clone(), p2.clone()];
        let upd = |seq, bal_a, pl: &Vec<PLock>, w: &World| Op::ChanUpdate { from: w.idx(&anyone), fee: FEE, lock: 5000, seq, bal_a, locks: pl.clone(), sigs: state_sigs(w, &terms, &a, Some(&b), seq, bal_a, cap, pl) };
        let u1 = upd(1, 300_000_000, &pl, &w);
        w.both(&u1, 5, &anyone);
        // the settled copy of the world, for the failures below
        let at_update = w.clone();
        let u2 = upd(2, 250_000_000, &pl, &w);
        w.both(&u2, 6, &anyone);     // replaces the waiting state: the window starts again (until 11)
        // failures on updates, each on the world as it was before the update
        {
            let mut v = at_update.clone();
            let good = upd(2, 250_000_000, &pl, &v);
            let root0 = v.tree.root();
            let tr = v.native(&good, 6);
            let w0 = at_update.clone();
            let older = upd(1, 250_000_000, &pl, &w0);            // not newer than the state waiting
            assert!(w0.attempt(&older, &tr, 6, root0, &anyone).is_none(), "an update that is not newer is not proved");
            let late = upd(2, 250_000_000, &pl, &w0);
            assert!(w0.attempt(&late, &tr, 11, root0, &anyone).is_none(), "an update after the window is not proved");
            let greedy = upd(2, 700_000_000, &pl, &w0);           // shares and point locks beyond the channel
            assert!(w0.attempt(&greedy, &tr, 6, root0, &anyone).is_none(), "a state that holds more than the channel is not proved");
            let mut forged = good.clone();
            if let Op::ChanUpdate { sigs, .. } = &mut forged { let m = locks::chan_state_msg(w0.chain, &terms.channel_id().unwrap(), 2, 250_000_000, cap, &pl); let (e, s) = mint::sign(&ks[3], m); sigs.eb = e; sigs.sb = mint::s_bytes(&s); }
            assert!(w0.attempt(&forged, &tr, 6, root0, &anyone).is_none(), "b's signature must be b's");
            let mut zero = good.clone();
            if let Op::ChanUpdate { seq, .. } = &mut zero { *seq = 0; }
            assert!(w0.attempt(&zero, &tr, 6, root0, &anyone).is_none(), "update numbers start at 1");
            assert!(w0.attempt(&good, &tr, 6, root0, &ks[3]).is_none(), "the sender's signature must be the sender's");
        }
        // settle after the window: the first point lock is opened (b gets it), the second has expired
        let at_state = w.clone();
        let settle = |wits: Vec<Option<[u8; 40]>>, w: &World| Op::ChanSettle { from: w.idx(&anyone), fee: FEE, lock: 5000, wits, to_a: Dest { idx: w.idx(&a), new: None }, to_b: Dest { idx: w.idx(&b), new: None } };
        {
            let mut v = at_state.clone();
            let good = settle(vec![Some(t1), None], &v);
            let root0 = v.tree.root();
            let tr = v.native(&good, 12);
            assert!(at_state.attempt(&good, &tr, 11, root0, &anyone).is_none(), "a settle while the window is open is not proved");
            let unopened = settle(vec![None, None], &at_state);
            assert!(at_state.attempt(&unopened, &tr, 12, root0, &anyone).is_none(), "a point lock neither opened nor expired holds the settlement back");
            let wrong = settle(vec![Some(mint::s_bytes(&num_bigint::BigUint::from(99u32))), None], &at_state);
            assert!(at_state.attempt(&wrong, &tr, 12, root0, &anyone).is_none(), "a scalar that does not open the lock is not proved");
        }
        let good = settle(vec![Some(t1), None], &w);
        w.both(&good, 12, &anyone);
        assert!(w.locks.is_empty(), "the channel is gone");
    }

    #[test]
    fn a_channel_closes_by_agreement_and_a_stream_settles() {
        let ks = keys();
        let mut w = world();
        let (a, b, anyone) = (ks[4].clone(), ks[5].clone(), ks[7].clone());
        let terms = open_channel(&mut w, &ks, 5100, 600_000_000, 5, false, 3);
        // start closing a channel nobody has updated: a's share is everything; then settle after the window
        let mut v = w.clone();
        let start = Op::ChanStart { from: v.idx(&a), fee: FEE, lock: 5100 };
        v.both(&start, 4, &a);
        let settle = Op::ChanSettle { from: v.idx(&anyone), fee: FEE, lock: 5100, wits: vec![], to_a: Dest { idx: v.idx(&a), new: None }, to_b: Dest { idx: v.idx(&b), new: None } };
        v.both(&settle, 10, &anyone);
        assert_eq!(v.state[&(v.idx(&b) as u64)].bal, 1_000_000_000 - 0, "b gets nothing from an unupdated channel (a settle with no share for b skips b's account)");
        // both sign the final balances: paid at once
        let cap = 600_000_000u64;
        let close = Op::ChanClose { from: w.idx(&anyone), fee: FEE, lock: 5100, bal_a: 450_000_000, sigs: close_sigs(&w, &terms, &a, &b, 450_000_000, cap), to_a: Dest { idx: w.idx(&a), new: None }, to_b: Dest { idx: w.idx(&b), new: None } };
        {
            let mut u = w.clone();
            let root0 = u.tree.root();
            let tr = u.native(&close, 4);
            let forged = Op::ChanClose { from: w.idx(&anyone), fee: FEE, lock: 5100, bal_a: 450_000_000, sigs: close_sigs(&w, &terms, &a, &ks[3], 450_000_000, cap), to_a: Dest { idx: w.idx(&a), new: None }, to_b: Dest { idx: w.idx(&b), new: None } };
            assert!(w.attempt(&forged, &tr, 4, root0, &anyone).is_none(), "a close that b did not sign is not proved");
            let other = Op::ChanClose { from: w.idx(&anyone), fee: FEE, lock: 5100, bal_a: 500_000_000, sigs: close_sigs(&w, &terms, &a, &b, 450_000_000, cap), to_a: Dest { idx: w.idx(&a), new: None }, to_b: Dest { idx: w.idx(&b), new: None } };
            assert!(w.attempt(&other, &tr, 4, root0, &anyone).is_none(), "the balances must be the signed ones");
        }
        w.both(&close, 4, &anyone);
        assert!(w.locks.is_empty());
        // a stream: only a signs; the state is the amount paid
        let mut s = world();
        let t2 = open_channel(&mut s, &ks, 5200, 400_000_000, 4, true, 3);
        let paid = 100_000_000u64;
        let upd = Op::ChanUpdate { from: s.idx(&anyone), fee: FEE, lock: 5200, seq: paid, bal_a: 400_000_000 - paid, locks: vec![], sigs: state_sigs(&s, &t2, &a, None, paid, 400_000_000 - paid, 400_000_000, &[]) };
        s.both(&upd, 4, &anyone);
        let settle = Op::ChanSettle { from: s.idx(&anyone), fee: FEE, lock: 5200, wits: vec![], to_a: Dest { idx: s.idx(&a), new: None }, to_b: Dest { idx: s.idx(&b), new: None } };
        s.both(&settle, 9, &anyone);
        assert!(s.locks.is_empty());
    }

    #[test]
    fn a_payout_can_open_a_new_account_and_a_dual_funded_channel_starts_at_its_base() {
        let ks = keys();
        let mut w = world();
        let (a, b, anyone) = (ks[4].clone(), ks[5].clone(), ks[7].clone());
        open_channel(&mut w, &ks, 5300, 600_000_000, 3, false, 3);
        let fund = Op::ChanFund { from: w.idx(&b), fee: FEE, lock: 5300, amt: 150_000_000 };
        w.both(&fund, 4, &b);
        // b starts the close: the state is 0, a's share is what a put in (600 000 000), b's is what b added
        let start = Op::ChanStart { from: w.idx(&b), fee: FEE, lock: 5300 };
        w.both(&start, 5, &b);
        // a's account is closed (as a payment that empties it would do), so a is paid into a new account at a free slot
        let ai = w.idx(&a) as u64;
        w.state.remove(&ai); w.tree.set(ai, crate::empty_leaf());
        let settle = Op::ChanSettle { from: w.idx(&anyone), fee: FEE, lock: 5300, wits: vec![], to_a: Dest { idx: 7777, new: Some(a.addr) }, to_b: Dest { idx: w.idx(&b), new: None } };
        w.both(&settle, 9, &anyone);
        assert_eq!(w.state[&7777].bal, 600_000_000);
        assert!(w.locks.is_empty());
    }
}
