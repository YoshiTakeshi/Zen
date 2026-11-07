// The operation leaf of the block proof, factory family (stage P4, Justus L. Ludovic).
//
// Same public values and shape as the other leaves. A factory (SPEC 7.2) is one output behind up to eight members, each with a channel to the coordinator.
// One operation of
//   Make      a new factory: the members' channel sizes add up to what the coordinator puts in;
//   Fund      a member adds coins to its own channel while it has no posted state;
//   Start     the coordinator or the member starts closing that member's channel (state 0: all the coordinator's);
//   Post      a newer state of that member's channel, signed by the coordinator and the member (point locks included);
//   Exit      after that member's window: the coordinator and the member are paid; the member leaves, the factory goes on without it;
//   ExitNow   both sign the final balances: the member leaves at once.
// The factory's address is the Poseidon digest of its terms, which hashes the digests of its (up to eight) members; the circuit takes all eight members
// as witness, rebuilds their digests, picks the member the operation names, checks the rule on it, and rebuilds the address with that member's new digest.
// A factory with every member gone is emptied. Merkle updates in the node's order: sender; the coordinator's account; the member's account; the factory's slot.
use crate::chancirc::{add_pl, add_rc, all_eq4, need, pl_hash, recv, set_pl, set_rc, x_words, PlT, RcT};
use crate::commoncirc::{add_lock, head, set_head, set_lock, set_sender, sender, Head, LockT, SndT};
use crate::opcirc::{empty_leaf_t, limbs, limbs62, limbs_of_bits, sel_hash, tag_felt, r_of};
use crate::{cond_eq, empty_leaf, ge62, hash_t, imply_zero, pad_to, root_from, select_hash_c, ec, D, F, C, NONCE_SHIFT, VDPI};
use anyhow::{anyhow, bail, Result};
use num_bigint::BigUint;
use plonky2::field::types::Field;
use plonky2::gates::gate::GateRef;
use plonky2::hash::hash_types::{HashOut, HashOutTarget};
use plonky2::iop::target::{BoolTarget, Target};
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CircuitData};

const NM: usize = crate::locks::MAX_FACTORY;
const NP: usize = crate::locks::MAX_PLOCKS;
pub const FACT_DATA_TAG: u64 = u64::from_le_bytes(*b"ZenFcDat");
const DUMMY_MSG: [u64; 4] = [55, 66, 77, 88];

pub struct FactoryLeaf { pub data: CircuitData<F, C, D>, pub t: FaT }
struct MemT { addr: [Target; 4], key: [Target; 11], cap: Target, base: Target, k1: BoolTarget, k2: BoolTarget, seq: Target, balc: Target, until: Target, pld: [Target; 4] }
pub struct FaT {
    hd: Head, kinds: [BoolTarget; 6], fee: Target, amt: Target, idx: Target,
    snd: SndT, sig1: ec::SigT,
    coord: [Target; 4], key_c: [Target; 11], delay: Target, salt: Target, nmem: Target, mems: Vec<MemT>,
    pl_o: PlT, pl_n: PlT, seq_n: Target, balc_n: Target, eb_w: [Target; 0], 
    sigc: ec::SigT, sigm: ec::SigT,
    wf: Vec<BoolTarget>, wpy: Vec<[Target; 5]>, wbits: Vec<Vec<BoolTarget>>,
    lk: LockT, ra: RcT, rb: RcT,
}
fn lim(b: &mut CircuitBuilder<F, D>, x: Target) -> (Target, Target) { limbs62(b, x) }
fn member_digest(b: &mut CircuitBuilder<F, D>, m: &MemT, cap: Target, kind: Target, seq: Target, balc: Target, until: Target, pld: [Target; 4], base: Target) -> HashOutTarget {
    let mut v = vec![b.constant(tag_felt(b"ZenFMemb"))];
    v.extend(m.addr); v.extend(m.key);
    for x in [cap, base] { let (l, h) = lim(b, x); v.extend([l, h]); }
    v.push(kind);
    for x in [seq, balc, until] { let (l, h) = lim(b, x); v.extend([l, h]); }
    v.extend(pld);
    hash_t(b, v)
}
fn fact_addr(b: &mut CircuitBuilder<F, D>, coord: [Target; 4], key_c: [Target; 11], delay: (Target, Target), salt: (Target, Target), n: Target, digs: &[[Target; 4]]) -> HashOutTarget {
    let mut v = vec![b.constant(tag_felt(b"ZenFact."))];
    v.extend(coord); v.extend(key_c); v.extend([delay.0, delay.1, salt.0, salt.1, n]);
    for d in digs { v.extend(*d); }
    hash_t(b, v)
}
/// the settlement of up to eight point locks: the witnesses (a flag, the scalar that opens the lock and its point's y), the expiry rule, a's gain
struct Slots { wf: Vec<BoolTarget>, wpy: Vec<[Target; 5]>, wbits: Vec<Vec<BoolTarget>>, wits_d: HashOutTarget, pay_c: Target }
#[allow(clippy::too_many_arguments)]
fn settle_slots(b: &mut CircuitBuilder<F, D>, prm: &ec::Params, pl: &PlT, act: &[BoolTarget], ex: BoolTarget, balc_m: Target, h_t: Target) -> Slots {
    let (zero, one) = (b.zero(), b.one());
    let nex = b.not(ex);
    let gx = ec::sw(prm.g);
    let mut wf = vec![]; let mut wpy = vec![]; let mut wbits = vec![];
    let mut wit_v = vec![b.constant(tag_felt(b"ZenWits.")), pl.len];
    let mut pay_c = balc_m;
    for i in 0..NP {
        let flag = b.add_virtual_bool_target_safe();
        imply_zero(b, nex, flag.target);
        let off = b.not(act[i]); imply_zero(b, off, flag.target);
        let py: [Target; 5] = core::array::from_fn(|_| b.add_virtual_target());
        let xw = x_words(b, &pl.point[i]);
        let px_u: [Target; 5] = core::array::from_fn(|k| { let gk = b.constant(gx.0.0[k]); b.select(flag, xw[k], gk) });
        let py_u: [Target; 5] = core::array::from_fn(|k| { let gk = b.constant(gx.1.0[k]); b.select(flag, py[k], gk) });
        let tb = ec::verify_mul_g(b, prm, ec::PT { x: px_u, y: py_u });
        let e1 = b.add_const(pl.expiry[i], F::ONE);
        let past = ge62(b, h_t, e1);
        let g = b.and(ex, act[i]);
        let ok = b.or(flag, past); need(b, g, ok);
        let nf = b.not(flag);
        let x = b.mul(pl.to_b[i].target, nf.target);
        let eff = { let t = b.add(pl.to_b[i].target, nf.target); let t2 = b.mul_const(F::TWO, x); b.sub(t, t2) };
        let keep = b.sub(one, eff);
        pay_c = b.mul_add(pl.amt[i], keep, pay_c);
        let mut tbz = tb.clone(); tbz.push(BoolTarget::new_unsafe(zero));
        let tl = limbs_of_bits(b, &tbz);
        wit_v.push(flag.target);
        for l in tl { let m = b.mul(l, flag.target); wit_v.push(m); }
        wf.push(flag); wpy.push(py); wbits.push(tb);
    }
    Slots { wf, wpy, wbits, wits_d: hash_t(b, wit_v), pay_c }
}

pub fn build_factory(chain: u64, prm: &ec::Params, gates: &[GateRef<F, D>], degree_bits: usize) -> FactoryLeaf {
    let mut b = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());
    for g in gates { b.add_gate_to_gate_set(g.clone()); }
    ec::dbladd_reset();
    let (zero, one) = (b.zero(), b.one());
    let hd = head(&mut b);
    let (h_t, d_t, p_t) = (hd.h_t, hd.day[0], hd.day[2]);
    let chain_t = b.constant(F::from_canonical_u64(chain));
    let kinds: [BoolTarget; 6] = core::array::from_fn(|_| b.add_virtual_bool_target_safe());
    let [mk, st, po, ex, en, fu] = kinds;
    { let mut s = b.zero(); for k in kinds { s = b.add(s, k.target); } b.connect(s, one); }
    let nmk = b.not(mk);
    let pays = BoolTarget::new_unsafe(b.add(ex.target, en.target));
    let usesig = BoolTarget::new_unsafe(b.add(po.target, en.target));
    let st_po = BoolTarget::new_unsafe(b.add(st.target, po.target));
    let nex = b.not(ex);

    // ---- operation fields and the sender
    let (fee, amt, idx) = (b.add_virtual_target(), b.add_virtual_target(), b.add_virtual_target());
    b.range_check(idx, 3);
    let (fee_lo, fee_hi) = lim(&mut b, fee);
    let (amt_lo, amt_hi) = lim(&mut b, amt);
    let gives = BoolTarget::new_unsafe(b.add(mk.target, fu.target));
    let ngives = b.not(gives);
    imply_zero(&mut b, ngives, amt);
    imply_zero(&mut b, mk, idx);
    let (snd, cur1) = sender(&mut b, &hd, fee, amt);
    { let t1 = b.arithmetic(F::from_canonical_u64(6), F::NEG_ONE, amt, one, hd.s_t); let m1 = b.mul(t1, mk.target); b.range_check(m1, 62); }
    { let z = b.is_equal(amt, zero); let nz = b.not(z); need(&mut b, fu, nz); }
    let nonce_new = b.mul_const(F::from_canonical_u64(1 << NONCE_SHIFT), h_t);

    // ---- the terms: coordinator, key, delay, salt and eight member slots
    let coord: [Target; 4] = core::array::from_fn(|_| b.add_virtual_target());
    let key_c: [Target; 11] = core::array::from_fn(|_| b.add_virtual_target());
    let (delay, salt, nmem) = (b.add_virtual_target(), b.add_virtual_target(), b.add_virtual_target());
    b.range_check(nmem, 4);
    let eight = b.constant(F::from_canonical_usize(NM));
    { let ok = ge62(&mut b, eight, nmem); b.assert_one(ok.target); }
    let mems: Vec<MemT> = (0..NM).map(|_| MemT {
        addr: core::array::from_fn(|_| b.add_virtual_target()), key: core::array::from_fn(|_| b.add_virtual_target()),
        cap: b.add_virtual_target(), base: b.add_virtual_target(), k1: b.add_virtual_bool_target_safe(), k2: b.add_virtual_bool_target_safe(),
        seq: b.add_virtual_target(), balc: b.add_virtual_target(), until: b.add_virtual_target(), pld: core::array::from_fn(|_| b.add_virtual_target()) }).collect();
    let empty_pl = crate::locks::plocks_digest(&[]);
    let epl: [Target; 4] = core::array::from_fn(|k| b.constant(empty_pl[k]));
    let (dl, sl) = (lim(&mut b, delay), lim(&mut b, salt));
    let mut present = vec![]; let mut sel = vec![]; let mut digs = vec![];
    for i in 0..NM {
        let m = &mems[i];
        let pr = { let c = b.constant(F::from_canonical_usize(i + 1)); ge62(&mut b, nmem, c) };
        let off = b.not(pr);
        for t in m.addr.iter().chain(m.key.iter()).chain([&m.cap, &m.base, &m.seq, &m.balc, &m.until, &m.k1.target, &m.k2.target]).chain(m.pld.iter()) { imply_zero(&mut b, off, *t); }
        { let mm = b.mul(m.k1.target, m.k2.target); b.assert_zero(mm); }
        let kind = { let t = b.mul_const(F::TWO, m.k2.target); b.add(m.k1.target, t) };
        let dg = member_digest(&mut b, m, m.cap, kind, m.seq, m.balc, m.until, m.pld, m.base);
        let dgz: [Target; 4] = core::array::from_fn(|k| b.mul(dg.elements[k], pr.target));
        let ci = b.constant(F::from_canonical_usize(i));
        let s = b.is_equal(idx, ci);
        present.push(pr); sel.push(s); digs.push(dgz);
    }
    let addr_old = fact_addr(&mut b, coord, key_c, dl, sl, nmem, &digs);
    let fid = {
        let mut v = vec![b.constant(tag_felt(b"ZenFctId"))];
        v.extend(coord); v.extend(key_c); v.extend([dl.0, dl.1, sl.0, sl.1, nmem]);
        for m in &mems { v.extend(m.addr); v.extend(m.key); }
        hash_t(&mut b, v)
    };
    // the member the operation names (not for a Make)
    let mux = |b: &mut CircuitBuilder<F, D>, f: &dyn Fn(&MemT) -> Target| -> Target { let mut acc = b.zero(); for i in 0..NM { let x = f(&mems[i]); acc = b.mul_add(sel[i].target, x, acc); } acc };
    let m_addr: [Target; 4] = core::array::from_fn(|k| mux(&mut b, &|m| m.addr[k]));
    let m_key: [Target; 11] = core::array::from_fn(|k| mux(&mut b, &|m| m.key[k]));
    let m_pld: [Target; 4] = core::array::from_fn(|k| mux(&mut b, &|m| m.pld[k]));
    let (m_cap, m_base, m_seq, m_balc, m_until) = (mux(&mut b, &|m| m.cap), mux(&mut b, &|m| m.base), mux(&mut b, &|m| m.seq), mux(&mut b, &|m| m.balc), mux(&mut b, &|m| m.until));
    let m1 = mux(&mut b, &|m| m.k1.target); let m2 = mux(&mut b, &|m| m.k2.target);
    let (mk1, mk2) = (BoolTarget::new_unsafe(m1), BoolTarget::new_unsafe(m2));
    let m_present = { let mut acc = b.zero(); for i in 0..NM { acc = b.mul_add(sel[i].target, present[i].target, acc); } BoolTarget::new_unsafe(acc) };
    need(&mut b, nmk, m_present);                                                              // the operation names a member
    let m_open = { let a = b.not(mk1); let c = b.not(mk2); b.and(a, c) };

    // ---- the point locks: the selected member's list (old) and the new one (Post)
    let pl_o = add_pl(&mut b); let pl_n = add_pl(&mut b);
    let (pld_o, act_o) = pl_hash(&mut b, &pl_o);
    let (pld_n, act_n) = pl_hash(&mut b, &pl_n);
    for k in 0..4 { cond_eq(&mut b, nmk, pld_o.elements[k], m_pld[k]); }
    let (seq_n, balc_n) = (b.add_virtual_target(), b.add_virtual_target());
    let (seq_nl, balc_nl) = (lim(&mut b, seq_n), lim(&mut b, balc_n));
    { let nup = b.not(po); imply_zero(&mut b, nup, pl_n.len); imply_zero(&mut b, nup, seq_n); let nus = b.not(usesig); imply_zero(&mut b, nus, balc_n); }
    let lk = add_lock(&mut b);
    let cap = lk.bal;

    // ---- Make
    for k in 0..4 { cond_eq(&mut b, mk, coord[k], snd.pk[k]); }
    cond_eq(&mut b, mk, salt, snd.nonce_t());
    {
        let c = ge62(&mut b, delay, one); need(&mut b, mk, c);
        let hi = b.constant(F::from_canonical_u64(100_000)); let c = ge62(&mut b, hi, delay); need(&mut b, mk, c);
        let c = ge62(&mut b, nmem, one); need(&mut b, mk, c);
        let mut tot = b.zero();
        for i in 0..NM {
            let m = &mems[i];
            let g = b.and(mk, present[i]);
            let z = b.is_equal(m.cap, zero); let nz = b.not(z); need(&mut b, g, nz);                  // something in each channel
            let d = b.sub(m.base, m.cap); imply_zero(&mut b, g, d);                                   // the coordinator holds all of it at first
            for t in [m.k1.target, m.k2.target, m.seq, m.balc, m.until] { imply_zero(&mut b, g, t); } // each channel starts open
            for k in 0..4 { cond_eq(&mut b, g, m.pld[k], epl[k]); }
            tot = b.add(tot, m.cap);
            let r = b.sub(amt, tot); let r = b.mul(r, mk.target); b.range_check(r, 62);              // no wrap: every prefix fits in the amount
        }
        let d = b.sub(tot, amt); imply_zero(&mut b, mk, d);                                           // the channels add up to what the factory holds
    }
    // ---- Fund: the member, a channel that is open
    for k in 0..4 { cond_eq(&mut b, fu, m_addr[k], snd.pk[k]); }
    need(&mut b, fu, m_open);
    // ---- Start: the coordinator or the member, a channel that is open
    { let ea = all_eq4(&mut b, snd.pk, coord); let eb = all_eq4(&mut b, snd.pk, m_addr); let o = b.or(ea, eb); need(&mut b, st, o); need(&mut b, st, m_open); }
    // ---- Post
    {
        { let n = b.not(mk2); need(&mut b, po, n); }                                                           // the member has not left
        let z = b.is_equal(seq_n, zero); let nz = b.not(z); need(&mut b, po, nz);
        let g = b.and(po, mk1);
        let w = ge62(&mut b, m_until, h_t); need(&mut b, g, w);
        let s1 = b.add_const(m_seq, F::ONE); let newer = ge62(&mut b, seq_n, s1); need(&mut b, g, newer);
        let mut tot = balc_n;
        let r = b.sub(m_cap, tot); let r = b.mul(r, po.target); b.range_check(r, 62);
        for i in 0..NP {
            tot = b.add(tot, pl_n.amt[i]);
            let r = b.sub(m_cap, tot); let r = b.mul(r, po.target); b.range_check(r, 62);
            let z = b.is_equal(pl_n.amt[i], zero); let nz = b.not(z);
            let g = b.and(po, act_n[i]); need(&mut b, g, nz);
            let h1 = b.add_const(h_t, F::ONE); let fut = ge62(&mut b, pl_n.expiry[i], h1); need(&mut b, g, fut);
        }
    }
    // ---- ExitNow
    {
        { let n = b.not(mk2); need(&mut b, en, n); }
        let g = b.and(en, mk1);
        imply_zero(&mut b, g, pl_o.len);
        let w = ge62(&mut b, m_until, h_t); need(&mut b, g, w);
        let w = ge62(&mut b, m_cap, balc_n); need(&mut b, en, w);
    }
    // ---- Exit: a channel that is closing, whose window has run out
    need(&mut b, ex, mk1);
    { let u1 = b.add_const(m_until, F::ONE); let over = ge62(&mut b, h_t, u1); need(&mut b, ex, over); }
    let slots = settle_slots(&mut b, prm, &pl_o, &act_o, ex, m_balc, h_t);

    // ---- the member's new digest and the factory's new address
    let nkind = {
        let a = b.mul_const(F::TWO, pays.target);
        let c = { let t = b.mul_const(F::TWO, m2); let u = b.add(m1, t); b.mul(fu.target, u) };
        let t = b.add(st_po.target, a); b.add(t, c)
    };
    let nseq = { let z = b.mul(po.target, seq_n); z };
    let nbalc = { let x = b.mul(po.target, balc_n); let y = b.mul(st.target, m_base); b.add(x, y) };
    let nuntil = { let hd_ = b.add(h_t, delay); b.mul(st_po.target, hd_) };
    let ncap = { let t = b.mul(fu.target, amt); b.add(m_cap, t) };
    b.range_check(ncap, 62);
    let proto = MemT { addr: m_addr, key: m_key, cap: m_cap, base: m_base, k1: mk1, k2: mk2, seq: m_seq, balc: m_balc, until: m_until, pld: m_pld };
    let nm_dig = member_digest(&mut b, &proto, ncap, nkind, nseq, nbalc, nuntil, pld_n.elements, m_base);
    let ndigs: Vec<[Target; 4]> = (0..NM).map(|i| core::array::from_fn(|k| { let x = b.mul(sel[i].target, nm_dig.elements[k]); let ns = nmk_t(&mut b, sel[i]); let y = b.mul(ns, digs[i][k]); b.add(x, y) })).collect();
    let addr_new = fact_addr(&mut b, coord, key_c, dl, sl, nmem, &ndigs);
    // the factory is emptied when every other member has left and this one leaves now
    let others_gone = {
        let mut acc = b.constant_bool(true);
        for i in 0..NM {
            let np_ = present_not(&mut b, present[i]); let gone = b.or(np_, mems_exited(&mems[i]));
            let ok = b.or(gone, sel[i]);
            acc = b.and(acc, ok);
        }
        acc
    };
    let rm = b.and(pays, others_gone);
    let new_bal = { let t = b.mul(fu.target, amt); let u = b.mul(pays.target, m_cap); let s = b.add(cap, t); b.sub(s, u) };
    b.range_check(new_bal, 62);
    let mk_leaf = { let mut v = addr_old.elements.to_vec(); v.push(amt); v.push(nonce_new); v.extend([zero; 5]); hash_t(&mut b, v) };
    let ret_leaf = { let mut v = addr_new.elements.to_vec(); v.push(new_bal); v.push(lk.nonce); v.extend([zero; 5]); hash_t(&mut b, v) };
    let old_leaf = { let mut v = addr_old.elements.to_vec(); v.push(lk.bal); v.push(lk.nonce); v.extend(lk.peg); hash_t(&mut b, v) };

    // ---- what the coordinator and the member sign
    let (cap_l, idx_t) = (lim(&mut b, m_cap), idx);
    let msg_state = { let mut v = vec![b.constant(tag_felt(b"ZenFSta.")), chain_t]; v.extend(fid.elements); v.push(idx_t); v.extend([seq_nl.0, seq_nl.1, balc_nl.0, balc_nl.1, cap_l.0, cap_l.1]); v.extend(pld_n.elements); hash_t(&mut b, v) };
    let msg_close = { let mut v = vec![b.constant(tag_felt(b"ZenFClo.")), chain_t]; v.extend(fid.elements); v.push(idx_t); v.extend([balc_nl.0, balc_nl.1, cap_l.0, cap_l.1]); hash_t(&mut b, v) };
    let msg_real = sel_hash(&mut b, po, msg_state, msg_close);
    let dummy = HashOutTarget { elements: core::array::from_fn(|k| b.constant(F::from_canonical_u64(DUMMY_MSG[k]))) };
    let msg_c = sel_hash(&mut b, usesig, msg_real, dummy);
    let (sigc, _pc, ec_bits) = ec::verify_sig_e(&mut b, prm, msg_c.elements);
    let xc = x_words(&mut b, &key_c);
    for k in 0..5 { cond_eq(&mut b, usesig, sigc.a.x[k], xc[k]); }
    let (sigm, _pm, em_bits) = ec::verify_sig_e(&mut b, prm, msg_c.elements);
    let xm = x_words(&mut b, &m_key);
    for k in 0..5 { cond_eq(&mut b, usesig, sigm.a.x[k], xm[k]); }
    let mut sigs28 = limbs_of_bits(&mut b, &ec_bits);
    { let mut sb = sigc.s_bits.clone(); sb.push(BoolTarget::new_unsafe(zero)); sigs28.extend(limbs_of_bits(&mut b, &sb)); }
    sigs28.extend(limbs_of_bits(&mut b, &em_bits));
    { let mut sb = sigm.s_bits.clone(); sb.push(BoolTarget::new_unsafe(zero)); sigs28.extend(limbs_of_bits(&mut b, &sb)); }

    // ---- payouts: the coordinator, then the member
    let pay_c = { let x = b.mul(ex.target, slots.pay_c); let y = b.mul(en.target, balc_n); b.add(x, y) };
    b.range_check(pay_c, 62);
    let pay_m = { let r = b.sub(m_cap, pay_c); b.mul(r, pays.target) };
    b.range_check(pay_m, 62);
    let act_a = { let z = b.is_equal(pay_c, zero); let nz = b.not(z); b.and(pays, nz) };
    let act_b = { let z = b.is_equal(pay_m, zero); let nz = b.not(z); b.and(pays, nz) };
    let (ra, rb) = (add_rc(&mut b), add_rc(&mut b));
    let cur2 = recv(&mut b, &ra, act_a, pay_c, coord, h_t, d_t, p_t, cur1);
    let cur3 = recv(&mut b, &rb, act_b, pay_m, m_addr, h_t, d_t, p_t, cur2);

    // ---- the factory's own slot
    let old_l = select_hash_c(&mut b, mk, empty_leaf(), old_leaf);
    let r3 = root_from(&mut b, old_l, &lk.bits, &lk.sib);
    for k in 0..4 { b.connect(r3.elements[k], cur3.elements[k]); }
    let el = empty_leaf_t(&mut b);
    let new_l = { let moved = sel_hash(&mut b, mk, mk_leaf, ret_leaf); sel_hash(&mut b, rm, el, moved) };
    let fin = root_from(&mut b, new_l, &lk.bits, &lk.sib);
    // an old factory's address is the one in its leaf: checked through the leaf above; the member named exists (m_present)

    // ---- the sender's signature
    let head_v = |b: &mut CircuitBuilder<F, D>, kind: u64| -> Vec<Target> {
        let mut v = vec![b.constant(tag_felt(b"ZenOp...")), chain_t, snd.n_lo, snd.n_hi, b.constant(F::from_canonical_u64(kind))]; v.extend(snd.pk); v.extend([fee_lo, fee_hi]); v
    };
    let m_mk = { let mut v = head_v(&mut b, 1); v.extend([amt_lo, amt_hi]); v.extend(addr_old.elements); hash_t(&mut b, v) };
    let m_st = { let mut v = head_v(&mut b, 12); v.extend(addr_old.elements); v.push(idx); hash_t(&mut b, v) };
    let m_po = { let mut v = head_v(&mut b, 13); v.extend(addr_old.elements); v.push(idx); v.extend([seq_nl.0, seq_nl.1, balc_nl.0, balc_nl.1]); v.extend(pld_n.elements); v.extend(sigs28.iter().copied()); hash_t(&mut b, v) };
    let m_ex = { let mut v = head_v(&mut b, 14); v.extend(addr_old.elements); v.push(idx); v.extend(slots.wits_d.elements); hash_t(&mut b, v) };
    let m_en = { let mut v = head_v(&mut b, 15); v.extend(addr_old.elements); v.push(idx); v.extend([balc_nl.0, balc_nl.1]); v.extend(sigs28.iter().copied()); hash_t(&mut b, v) };
    let m_fu = { let mut v = head_v(&mut b, 16); v.extend(addr_old.elements); v.push(idx); v.extend([amt_lo, amt_hi]); hash_t(&mut b, v) };
    let msg1: [Target; 4] = core::array::from_fn(|k| {
        let mut acc = b.zero();
        for (kd, m) in [(mk, &m_mk), (st, &m_st), (po, &m_po), (ex, &m_ex), (en, &m_en), (fu, &m_fu)] { acc = b.mul_add(kd.target, m.elements[k], acc); }
        acc
    });
    let (sig1, pk1) = ec::verify_sig(&mut b, prm, msg1);
    for k in 0..4 { b.connect(pk1[k], snd.pk[k]); }
    ec::dbladd_pad(&mut b, prm);

    // ---- block data
    let l_idx = b.le_sum(lk.bits.iter());
    let (ia, ib) = (b.le_sum(ra.bits.iter()), b.le_sum(rb.bits.iter()));
    let mut kind = b.zero();
    for (kd, code) in [(mk, 1u64), (st, 12), (po, 13), (ex, 14), (en, 15), (fu, 16)] { kind = b.mul_const_add(F::from_canonical_u64(code), kd.target, kind); }
    let mut data = vec![b.constant(F::from_canonical_u64(FACT_DATA_TAG)), kind, snd.idx, fee_lo, fee_hi, amt_lo, amt_hi, l_idx, idx];
    for (i, r) in [(ia, &ra), (ib, &rb)] {
        data.push(i); data.push(r.new_r.target);
        for k in 0..4 { data.push(b.mul(r.o_pk[k], r.new_r.target)); }
    }
    for k in 0..4 { data.push(b.mul(addr_old.elements[k], mk.target)); }
    data.push(seq_nl.0); data.push(seq_nl.1); data.push(b.mul(balc_nl.0, usesig.target)); data.push(b.mul(balc_nl.1, usesig.target));
    for k in 0..4 { data.push(b.mul(pld_n.elements[k], po.target)); }
    for x in &sigs28 { data.push(b.mul(*x, usesig.target)); }
    for k in 0..4 { data.push(b.mul(slots.wits_d.elements[k], ex.target)); }
    let data_h = hash_t(&mut b, data);

    b.register_public_inputs(&hd.root0.elements);
    b.register_public_inputs(&fin.elements);
    b.register_public_input(fee);
    b.register_public_input(one);
    b.register_public_inputs(&data_h.elements);
    b.register_public_input(hd.s_t);
    b.register_public_input(hd.h_t);
    for _ in 0..VDPI { b.register_public_input(zero); }
    pad_to(&mut b, degree_bits);
    let t = FaT { hd, kinds, fee, amt, idx, snd, sig1, coord, key_c, delay, salt, nmem, mems, pl_o, pl_n, seq_n, balc_n, eb_w: [], sigc, sigm,
                  wf: slots.wf, wpy: slots.wpy, wbits: slots.wbits, lk, ra, rb };
    let _ = (nex, ngives);
    FactoryLeaf { data: b.build::<C>(), t }
}
fn nmk_t(b: &mut CircuitBuilder<F, D>, s: BoolTarget) -> Target { let n = b.not(s); n.target }
fn present_not(b: &mut CircuitBuilder<F, D>, p: BoolTarget) -> BoolTarget { b.not(p) }
fn mems_exited(m: &MemT) -> BoolTarget { m.k2 }

// ---------------------------------------------------------------- the witness
pub struct FactoryInput<'a> {
    pub op: &'a crate::locks::Op, pub trace: &'a crate::locks::OpTrace, pub height: u64, pub s: u64, pub root0: HashOut<F>, pub chain: u8,
    pub sender_a: ec::P, pub sender_sig: (u128, BigUint),
}
fn bits_of(x: &BigUint) -> Vec<bool> { (0..ec::S_BITS).map(|i| x.bit(i as u64)).collect() }
pub fn set_witness(l: &FactoryLeaf, pw: &mut PartialWitness<F>, inp: &FactoryInput) -> Result<()> {
    use crate::locks::{ChanSigs, Dest, Op, SubState, Terms};
    let t = &l.t;
    let prm = ec::params();
    set_head(pw, &t.hd, inp.height, inp.s, inp.root0)?;
    let tc = &inp.trace.touches;
    if tc.len() < 2 { bail!("an operation touches at least the sender and the factory"); }
    let sender = set_sender(pw, &t.snd, &tc[0])?;
    let which = match inp.op { Op::Make { .. } => 0, Op::FactoryStart { .. } => 1, Op::FactoryPost { .. } => 2, Op::FactoryExit { .. } => 3, Op::FactoryExitNow { .. } => 4, Op::FactoryFund { .. } => 5, _ => bail!("not a factory operation") };
    for (i, bt) in t.kinds.iter().enumerate() { pw.set_bool_target(*bt, i == which)?; }
    let (fee, amt, idx) = match inp.op {
        Op::Make { fee, amt, .. } => (*fee, *amt, 0u8),
        Op::FactoryFund { fee, amt, idx, .. } => (*fee, *amt, *idx),
        Op::FactoryStart { fee, idx, .. } | Op::FactoryPost { fee, idx, .. } | Op::FactoryExit { fee, idx, .. } | Op::FactoryExitNow { fee, idx, .. } => (*fee, 0, *idx),
        _ => unreachable!(),
    };
    pw.set_target(t.fee, F::from_canonical_u64(fee))?; pw.set_target(t.amt, F::from_canonical_u64(amt))?; pw.set_target(t.idx, F::from_canonical_u64(idx as u64))?;
    let terms = inp.trace.terms.clone().ok_or_else(|| anyhow!("no terms"))?;
    let Terms::Factory { coord, key_c, members, delay, salt } = terms else { bail!("not a factory") };
    pw.set_target_arr(&t.coord, &coord)?; pw.set_target_arr(&t.key_c, &limbs(&key_c))?;
    pw.set_target(t.delay, F::from_canonical_u64(delay))?; pw.set_target(t.salt, F::from_canonical_u64(salt))?; pw.set_target(t.nmem, F::from_canonical_usize(members.len()))?;
    let empty_pl = crate::locks::plocks_digest(&[]);
    let mut sel_plocks = vec![]; let mut sel_state = None;
    for i in 0..NM {
        let m = &t.mems[i];
        match members.get(i) {
            Some(fm) => {
                let (k1, k2, seq, balc, until, pl) = match &fm.state {
                    SubState::Open => (false, false, 0, 0, 0, empty_pl),
                    SubState::Exited => (false, true, 0, 0, 0, empty_pl),
                    SubState::Closing { seq, bal_c, until, locks } => (true, false, *seq, *bal_c, *until, crate::locks::plocks_digest(locks)),
                };
                pw.set_target_arr(&m.addr, &fm.addr)?; pw.set_target_arr(&m.key, &limbs(&fm.key))?;
                pw.set_target(m.cap, F::from_canonical_u64(fm.cap))?; pw.set_target(m.base, F::from_canonical_u64(fm.base))?;
                pw.set_bool_target(m.k1, k1)?; pw.set_bool_target(m.k2, k2)?;
                for (x, v) in [(m.seq, seq), (m.balc, balc), (m.until, until)] { pw.set_target(x, F::from_canonical_u64(v))?; }
                pw.set_target_arr(&m.pld, &pl)?;
                if i == idx as usize && which != 0 { if let SubState::Closing { locks, .. } = &fm.state { sel_plocks = locks.clone(); } sel_state = Some((fm.clone(), balc)); }
            }
            None => {
                pw.set_target_arr(&m.addr, &[F::ZERO; 4])?; pw.set_target_arr(&m.key, &[F::ZERO; 11])?;
                for x in [m.cap, m.base, m.seq, m.balc, m.until] { pw.set_target(x, F::ZERO)?; }
                pw.set_bool_target(m.k1, false)?; pw.set_bool_target(m.k2, false)?; pw.set_target_arr(&m.pld, &[F::ZERO; 4])?;
            }
        }
    }
    set_pl(pw, &t.pl_o, &sel_plocks)?;
    let (mut plocks_n, mut seq_n, mut balc_n) = (vec![], 0u64, 0u64);
    let mut sigs: Option<ChanSigs> = None;
    match inp.op {
        Op::FactoryPost { seq, bal_c, locks, sigs: g, .. } => { plocks_n = locks.clone(); seq_n = *seq; balc_n = *bal_c; sigs = Some(*g); }
        Op::FactoryExitNow { bal_c, sigs: g, .. } => { balc_n = *bal_c; sigs = Some(*g); }
        _ => {}
    }
    set_pl(pw, &t.pl_n, &plocks_n)?;
    pw.set_target(t.seq_n, F::from_canonical_u64(seq_n))?; pw.set_target(t.balc_n, F::from_canonical_u64(balc_n))?;
    let lt = tc.last().unwrap();
    let cap_lock = match inp.op { Op::Make { .. } => 0, _ => lt.old.ok_or_else(|| anyhow!("no factory leaf"))?.bal };
    set_lock(pw, &t.lk, lt)?;
    // payouts
    let (mut pay_c, mut pay_m) = (0u128, 0u128);
    let (mut to_c, mut to_m) = (None, None);
    let mut wits: Vec<Option<[u8; 40]>> = vec![];
    if let Some((fm, balc_m)) = &sel_state {
        let plocks = &sel_plocks;
        match inp.op {
            Op::FactoryExit { wits: w, to_c: x, to_m: y, .. } => {
                to_c = Some(*x); to_m = Some(*y); wits = w.clone();
                let total: u128 = plocks.iter().map(|p| p.amt as u128).sum();
                pay_c = *balc_m as u128; pay_m = fm.cap as u128 - *balc_m as u128 - total;
                for (p, w) in plocks.iter().zip(&wits) {
                    let opened = w.as_ref().map_or(false, |s| p.opened_by(s));
                    if if opened { p.to_b } else { !p.to_b } { pay_m += p.amt as u128 } else { pay_c += p.amt as u128 }
                }
            }
            Op::FactoryExitNow { bal_c, to_c: x, to_m: y, .. } => { to_c = Some(*x); to_m = Some(*y); pay_c = *bal_c as u128; pay_m = fm.cap as u128 - *bal_c as u128; }
            _ => {}
        }
    }
    let _ = cap_lock;
    let mid = &tc[1..tc.len() - 1];
    let mut it = mid.iter();
    let ta = if pay_c > 0 { it.next() } else { None };
    let tb = if pay_m > 0 { it.next() } else { None };
    if it.next().is_some() { bail!("more touches than payouts"); }
    set_rc(pw, &t.ra, ta, to_c.as_ref(), inp.height, &sender)?;
    set_rc(pw, &t.rb, tb, to_m.as_ref(), inp.height, &sender)?;
    let gy = ec::sw(prm.g).1;
    for i in 0..NP {
        let open = if let Op::FactoryExit { .. } = inp.op { wits.get(i).and_then(|w| *w).filter(|_| i < sel_plocks.len()) } else { None };
        match open {
            Some(s) => {
                let sv = BigUint::from_bytes_le(&s);
                let p = crate::mint::decode_point(&sel_plocks[i].point)?;
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
    let (e1, s1) = &inp.sender_sig;
    crate::set_sig(pw, &t.sig1, inp.sender_a, r_of(inp.sender_a, *e1, s1), s1, false)?;
    let pad = crate::mint::Key::from_secret(BigUint::from(7777u32));
    let dummy: [F; 4] = std::array::from_fn(|k| F::from_canonical_u64(DUMMY_MSG[k]));
    let (de, ds) = crate::mint::sign(&pad, dummy);
    let fixed = |pw: &mut PartialWitness<F>, st: &ec::SigT| crate::set_sig(pw, st, pad.a, r_of(pad.a, de, &ds), &ds, false);
    match (sigs, &sel_state) {
        (Some(g), Some((fm, _))) => {
            let (pc, pm) = (crate::mint::decode_point(&key_c)?, crate::mint::decode_point(&fm.key)?);
            let (sa, sb) = (BigUint::from_bytes_le(&g.sa), BigUint::from_bytes_le(&g.sb));
            crate::set_sig(pw, &t.sigc, pc, r_of(pc, g.ea, &sa), &sa, false)?;
            crate::set_sig(pw, &t.sigm, pm, r_of(pm, g.eb, &sb), &sb, false)?;
        }
        _ => { fixed(pw, &t.sigc)?; fixed(pw, &t.sigm)?; }
    }
    let _ = Dest { idx: 0, new: None };
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::locks::{self, ChanSigs, CrossMode, Ctx, Dest, FMember, Op, PLock, SignedOp, SubState, Terms};
    use crate::mint;
    use crate::node::dev;
    use crate::node::{Chain, DevStamp, Params};
    use crate::{Acct, Tree};
    use plonky2::field::types::PrimeField64;
    use std::collections::HashMap;
    use std::sync::OnceLock;

    const FEE: u64 = 10_000;
    const S: u64 = 1_000_000;
    fn leaf() -> &'static FactoryLeaf { static L: OnceLock<FactoryLeaf> = OnceLock::new(); L.get_or_init(|| build_factory(Params::devnet().chain as u64, &ec::params(), &[], 0)) }
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
        fn attempt(&self, op: &Op, trace: &locks::OpTrace, height: u64, root0: HashOut<F>, signer: &mint::Key) -> Option<Vec<u64>> {
            let req = crate::opcirc::req_of(op, &self.state).ok()?;
            let nonce = trace.touches[0].old.unwrap().nonce;
            let (e, sv) = mint::sign(signer, SignedOp::message(self.chain, nonce, &req));
            let inp = FactoryInput { op, trace, height, s: S, root0, chain: self.chain, sender_a: signer.a, sender_sig: (e, sv) };
            let mut pw = PartialWitness::new();
            if let Err(e) = set_witness(leaf(), &mut pw, &inp) { if std::env::var("ZEN_DEBUG").is_ok() { println!("witness error: {e}"); } return None; }
            let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| leaf().data.prove(pw)));
            if std::env::var("ZEN_DEBUG").is_ok() { match &r { Ok(Err(e)) => println!("prove error: {e}"), Err(e) => println!("prove panic: {:?}", e.downcast_ref::<String>()), _ => {} } }
            let Ok(Ok(proof)) = r else { return None };
            let pis: Vec<u64> = proof.public_inputs.iter().map(|x| x.to_canonical_u64()).collect();
            leaf().data.verify(proof).ok().map(|_| pis)
        }
        fn both(&mut self, op: &Op, height: u64, signer: &mint::Key) -> Vec<u64> {
            let root0 = self.tree.root();
            let before = self.clone();
            let tr = self.native(op, height);
            let pis = before.attempt(op, &tr, height, root0, signer).unwrap_or_else(|| panic!("the circuit does not prove {:?}", std::mem::discriminant(op)));
            let felts = |h: HashOut<F>| -> Vec<u64> { h.elements.iter().map(|x| x.to_canonical_u64()).collect() };
            assert_eq!(pis.len(), 84);
            assert_eq!(&pis[0..4], &felts(root0)[..], "root before");
            assert_eq!(&pis[4..8], &felts(self.tree.root())[..], "root after");
            assert_eq!((pis[8], pis[9]), (op.fee(), 1));
            assert_eq!(&pis[10..14], &locks::factory_data_hash(op).unwrap().map(|x| x.to_canonical_u64())[..], "the data hash is the node's");
            assert_eq!((pis[14], pis[15]), (S, height));
            pis
        }
        fn trace_of(&self, op: &Op, height: u64) -> (locks::OpTrace, HashOut<F>) { let mut v = self.clone(); let r = v.tree.root(); (v.native(op, height), r) }
    }
    fn sign2(a: &mint::Key, b: &mint::Key, msg: [F; 4]) -> ChanSigs {
        let (ea, sa) = mint::sign(a, msg); let (eb, sb) = mint::sign(b, msg);
        ChanSigs { ea, sa: mint::s_bytes(&sa), eb, sb: mint::s_bytes(&sb) }
    }
    fn plock(t: u32, amt: u64, to_b: bool, expiry: u64) -> (PLock, [u8; 40]) {
        let k = num_bigint::BigUint::from(t);
        (PLock { amt, to_b, point: mint::encode_point(ec::mul_g(&ec::params(), &k)), expiry }, mint::s_bytes(&k))
    }
    fn factory(c: &mint::Key, ms: &[(&mint::Key, u64)], delay: u64, salt: u64) -> Terms {
        Terms::Factory { coord: c.addr, key_c: mint::encode_point(c.a), delay, salt,
                         members: ms.iter().map(|(k, cap)| FMember { addr: k.addr, key: mint::encode_point(k.a), cap: *cap, base: *cap, state: SubState::Open }).collect() }
    }

    #[test]
    fn the_factory_leaf_builds_and_its_size_is_known() {
        let t = std::time::Instant::now();
        let l = leaf();
        println!("RESULT factory leaf: 2^{} rows, {} gates, {} public values, build {:.1}s", l.data.common.degree_bits(), l.data.common.gates.len(), l.data.common.num_public_inputs, t.elapsed().as_secs_f64());
    }

    #[test]
    fn a_factory_is_made_funded_closed_by_agreement_and_left_by_the_window() {
        let ks = keys();
        let mut w = world();
        let (coord, m0, m1, anyone) = (ks[4].clone(), ks[5].clone(), ks[6].clone(), ks[7].clone());
        let terms = factory(&coord, &[(&m0, 300_000_000), (&m1, 300_000_000)], 3, w.nonce(&coord));
        let mk = Op::Make { from: w.idx(&coord), fee: FEE, amt: 600_000_000, at: 5000, terms: terms.clone() };
        // a make that holds more than its channels, or is not the coordinator's own, is not proved
        {
            let (tr, root0) = w.trace_of(&mk, 3);
            let mut greedy = mk.clone();
            if let Op::Make { amt, .. } = &mut greedy { *amt = 700_000_000; }
            assert!(w.attempt(&greedy, &tr, 3, root0, &coord).is_none(), "the channels must add up to the amount");
            assert!(w.attempt(&mk, &tr, 3, root0, &m0).is_none(), "the sender's signature must be the sender's");
        }
        w.both(&mk, 3, &coord);
        // member 0 adds coins to its channel
        let fund = Op::FactoryFund { from: w.idx(&m0), fee: FEE, lock: 5000, idx: 0, amt: 50_000_000 };
        {
            let (tr, root0) = w.trace_of(&fund, 4);
            assert!(w.attempt(&fund, &tr, 4, root0, &coord).is_none(), "the sender's signature must be the sender's");
        }
        w.both(&fund, 4, &m0);
        // the coordinator starts closing member 0's channel; the two agree on a close in the window
        let start = Op::FactoryStart { from: w.idx(&coord), fee: FEE, lock: 5000, idx: 0 };
        w.both(&start, 5, &coord);
        let fid = w.locks[&5000].factory_id().unwrap();
        let cap0 = 350_000_000u64;
        let now = |w: &World, bal_c: u64, signer: &mint::Key| Op::FactoryExitNow { from: w.idx(&anyone), fee: FEE, lock: 5000, idx: 0, bal_c, sigs: sign2(&coord, signer, locks::fact_close_msg(w.chain, &fid, 0, bal_c, cap0)),
                                                                                to_c: Dest { idx: w.idx(&coord), new: None }, to_m: Dest { idx: w.idx(&m0), new: None } };
        {
            let good = now(&w, 100_000_000, &m0);
            let (tr, root0) = w.trace_of(&good, 6);
            assert!(w.attempt(&good, &tr, 6, root0, &anyone).is_some());
            let forged = now(&w, 100_000_000, &m1);
            assert!(w.attempt(&forged, &tr, 6, root0, &anyone).is_none(), "the member's signature must be the member's");
            let late = good.clone();
            assert!(w.attempt(&late, &tr, 9, root0, &anyone).is_none(), "an agreement after the window is not proved");
        }
        let good = now(&w, 100_000_000, &m0);
        w.both(&good, 6, &anyone);
        assert_eq!(w.locks.len(), 1);
        // member 1 posts a state with two point locks (the two of them sign), then leaves after the window
        let (p1, t1) = plock(11, 100_000_000, true, 100);
        let (p2, _) = plock(12, 50_000_000, false, 8);
        let pl = vec![p1, p2];
        let fid = w.locks[&5000].factory_id().unwrap();
        let post = |w: &World, seq: u64, bal_c: u64| Op::FactoryPost { from: w.idx(&anyone), fee: FEE, lock: 5000, idx: 1, seq, bal_c, locks: pl.clone(), sigs: sign2(&coord, &m1, locks::fact_state_msg(w.chain, &fid, 1, seq, bal_c, 300_000_000, &pl)) };
        {
            let zero = post(&w, 0, 100_000_000);
            let ok = post(&w, 1, 100_000_000);
            let (tr, root0) = w.trace_of(&ok, 7);
            assert!(w.attempt(&ok, &tr, 7, root0, &anyone).is_some());
            assert!(w.attempt(&zero, &tr, 7, root0, &anyone).is_none(), "update numbers start at 1");
            let greedy = post(&w, 1, 300_000_000);
            assert!(w.attempt(&greedy, &tr, 7, root0, &anyone).is_none(), "shares and point locks beyond the channel are not proved");
        }
        let p = post(&w, 1, 100_000_000);
        w.both(&p, 7, &anyone);
        let exit = |wits: Vec<Option<[u8; 40]>>, w: &World| Op::FactoryExit { from: w.idx(&anyone), fee: FEE, lock: 5000, idx: 1, wits, to_c: Dest { idx: w.idx(&coord), new: None }, to_m: Dest { idx: w.idx(&m1), new: None } };
        {
            let at_state = w.clone();
            let mut v = at_state.clone();
            let good = exit(vec![Some(t1), None], &v);
            let root0 = v.tree.root();
            let tr = v.native(&good, 11);
            assert!(at_state.attempt(&good, &tr, 8, root0, &anyone).is_none(), "an exit while the window is open is not proved");
            let unopened = exit(vec![None, None], &at_state);
            assert!(at_state.attempt(&unopened, &tr, 11, root0, &anyone).is_none(), "a point lock neither opened nor expired holds the exit back");
            let wrong = exit(vec![Some(mint::s_bytes(&num_bigint::BigUint::from(99u32))), None], &at_state);
            assert!(at_state.attempt(&wrong, &tr, 11, root0, &anyone).is_none(), "a scalar that does not open the lock is not proved");
        }
        let good = exit(vec![Some(t1), None], &w);
        w.both(&good, 11, &anyone);
        assert!(w.locks.is_empty(), "the last member left: the factory is gone");
    }
}
