// The operation leaf of the block proof, order family (stage P4, Justus L. Ludovic).
//
// Same public values and shape as the other leaves. One operation of
//   Make     a new sell order (open, or open to an auction): the maker pays the sale and the fee; the order's leaf appears in an empty slot;
//   Reserve  the sender pays the order's deposit and names the taker; the order is reserved until a block;
//   Bid      a bid in an auction: escrow `bid`; an earlier, lower bid is paid back to its taker;
//   Reopen   after a reservation has run out the escrow goes to the maker and the order is open again (to a new auction, if it was one);
//   Return   after the order's expiry the sale goes back to the maker and the order is gone.
//   Claim    (stage P5) the taker takes the lock's whole balance within the reservation; the order is gone. The claim carries the other chain's payment proof:
//            the circuit binds the proof's digest (the sender signs it; the block data holds it), and every node checks the proof itself (the foreign headers
//            are a node's view, not part of the state); a stamp alone does not say the payment was made.
// The lock's address is the Poseidon digest of the order's terms and state in the layout of `locks.rs`; a Reserve or Bid keeps the block's time in the
// terms (`since`), which the circuit takes from the operation's witness and binds in the block-data hash, where the node writes the block's own time.
// Merkle updates in the node's order: sender; the paid account (a refund, the maker's escrow or sale); the order's own slot.
use crate::chancirc::{add_rc, need, recv, set_rc, RcT};
use crate::commoncirc::{add_lock, head, set_head, set_lock, set_sender, sender, Head, LockT, SndT};
use crate::opcirc::{empty_leaf_t, limbs62, sel_hash, tag_felt, r_of};
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

pub const ORDER_DATA_TAG: u64 = u64::from_le_bytes(*b"ZenOrDat");
pub struct OrderLeaf { pub data: CircuitData<F, C, D>, pub t: OrT }
pub struct OrT {
    hd: Head, kinds: [BoolTarget; 6], pdig: [Target; 4], fee: Target, amt: Target, taker: [Target; 4], bid: Target, ntime: Target,
    snd: SndT, sig1: ec::SigT,
    maker: [Target; 4], sell: Target, want_chain: Target, want_amt: Target, pay_to: [Target; 4], expiry: Target, rblocks: Target, deposit: Target, salt: Target,
    sk1: BoolTarget, sk2: BoolTarget, taker_o: [Target; 4], until_o: Target, since_o: Target, window_o: Target, bid_o: Target, close_o: Target,
    lk: LockT, ra: RcT,
}
/// the digest of order terms in a state (the layout of `Terms::digest`)
#[allow(clippy::too_many_arguments)]
fn order_addr(b: &mut CircuitBuilder<F, D>, maker: [Target; 4], sell: (Target, Target), want_chain: Target, want_amt: (Target, Target), pay_to: [Target; 4], expiry: (Target, Target),
              rblocks: (Target, Target), deposit: (Target, Target), salt: (Target, Target), kind: Target, taker: [Target; 4], until: (Target, Target), since: Target,
              window: (Target, Target), bid: (Target, Target), close: (Target, Target)) -> HashOutTarget {
    let mut v = vec![b.constant(tag_felt(b"ZenOrder"))];
    v.extend(maker); v.extend([sell.0, sell.1, want_chain, want_amt.0, want_amt.1]); v.extend(pay_to);
    v.extend([expiry.0, expiry.1, rblocks.0, rblocks.1, deposit.0, deposit.1, salt.0, salt.1]);
    v.push(kind); v.extend(taker); v.extend([until.0, until.1, since, window.0, window.1, bid.0, bid.1, close.0, close.1]);
    hash_t(b, v)
}
pub fn build_order(chain: u64, prm: &ec::Params, gates: &[GateRef<F, D>], degree_bits: usize) -> OrderLeaf {
    let mut b = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());
    for g in gates { b.add_gate_to_gate_set(g.clone()); }
    ec::dbladd_reset();
    let (zero, one) = (b.zero(), b.one());
    let hd = head(&mut b);
    let (h_t, d_t, p_t) = (hd.h_t, hd.day[0], hd.day[2]);
    let chain_t = b.constant(F::from_canonical_u64(chain));
    let kinds: [BoolTarget; 6] = core::array::from_fn(|_| b.add_virtual_bool_target_safe());
    let [mk, rs, bd, ro, rt, cl] = kinds;
    // a claim carries the other chain's payment proof: the circuit binds its digest (signed, and in the block data); the node checks the proof itself
    let pdig: [Target; 4] = core::array::from_fn(|_| b.add_virtual_target());
    let ncl = b.not(cl);
    for t in pdig { imply_zero(&mut b, ncl, t); }
    { let mut s = b.zero(); for k in kinds { s = b.add(s, k.target); } b.connect(s, one); }
    let rs_bd = BoolTarget::new_unsafe(b.add(rs.target, bd.target));
    let n_rs_bd = b.not(rs_bd);
    let nmk = b.not(mk); let nbd = b.not(bd);

    // ---- operation fields
    let (fee, amt, bid, ntime) = (b.add_virtual_target(), b.add_virtual_target(), b.add_virtual_target(), b.add_virtual_target());
    let taker: [Target; 4] = core::array::from_fn(|_| b.add_virtual_target());
    imply_zero(&mut b, nmk, amt); imply_zero(&mut b, nbd, bid); imply_zero(&mut b, n_rs_bd, ntime);
    for t in taker { imply_zero(&mut b, n_rs_bd, t); }
    b.range_check(ntime, 32);
    let (fee_lo, fee_hi) = limbs62(&mut b, fee);
    let (amt_lo, amt_hi) = limbs62(&mut b, amt);
    let (bid_lo, bid_hi) = limbs62(&mut b, bid);
    // ---- the terms
    let maker: [Target; 4] = core::array::from_fn(|_| b.add_virtual_target());
    let pay_to: [Target; 4] = core::array::from_fn(|_| b.add_virtual_target());
    let taker_o: [Target; 4] = core::array::from_fn(|_| b.add_virtual_target());
    let (sell, want_chain, want_amt, expiry, rblocks, deposit, salt) = (b.add_virtual_target(), b.add_virtual_target(), b.add_virtual_target(), b.add_virtual_target(), b.add_virtual_target(), b.add_virtual_target(), b.add_virtual_target());
    let (until_o, since_o, window_o, bid_o, close_o) = (b.add_virtual_target(), b.add_virtual_target(), b.add_virtual_target(), b.add_virtual_target(), b.add_virtual_target());
    b.range_check(since_o, 32);
    let (sk1, sk2) = (b.add_virtual_bool_target_safe(), b.add_virtual_bool_target_safe());
    let (nsk1, nsk2) = (b.not(sk1), b.not(sk2));
    let is_open = b.and(nsk1, nsk2); let is_res = b.and(sk1, nsk2); let is_auc = b.and(nsk1, sk2); let is_bid = b.and(sk1, sk2);
    let kind_o = { let t = b.mul_const(F::TWO, sk2.target); b.add(sk1.target, t) };
    let (sell_l, wa_l, ex_l, rb_l, dp_l, salt_l) = (limbs62(&mut b, sell), limbs62(&mut b, want_amt), limbs62(&mut b, expiry), limbs62(&mut b, rblocks), limbs62(&mut b, deposit), limbs62(&mut b, salt));
    let (un_l, wi_l, bo_l, cl_l) = (limbs62(&mut b, until_o), limbs62(&mut b, window_o), limbs62(&mut b, bid_o), limbs62(&mut b, close_o));
    let addr_old = order_addr(&mut b, maker, sell_l, want_chain, wa_l, pay_to, ex_l, rb_l, dp_l, salt_l, kind_o, taker_o, un_l, since_o, wi_l, bo_l, cl_l);

    // ---- the sender pays: a Make the sale, a Reserve the deposit, a Bid the bid
    let give = { let x = b.mul(mk.target, amt); let y = b.mul(rs.target, deposit); let z = b.mul(bd.target, bid); let t = b.add(x, y); b.add(t, z) };
    let (snd, cur1) = sender(&mut b, &hd, fee, give);
    let t1 = b.arithmetic(F::from_canonical_u64(6), F::NEG_ONE, amt, one, hd.s_t); let m1 = b.mul(t1, mk.target); b.range_check(m1, 62);   // a Make: amount >= S/6
    let lk = add_lock(&mut b);
    let nonce_new = b.mul_const(F::from_canonical_u64(1 << NONCE_SHIFT), h_t);
    let one_c = |b: &mut CircuitBuilder<F, D>, v: u64| b.constant(F::from_canonical_u64(v));
    let h1 = b.add_const(h_t, F::ONE);
    let not_expired = ge62(&mut b, expiry, h1);        // height < expiry
    let past_expiry = ge62(&mut b, h_t, h1);           // placeholder, replaced below
    let _ = past_expiry;

    // ---- Make
    for k in 0..4 { cond_eq(&mut b, mk, maker[k], snd.pk[k]); }
    cond_eq(&mut b, mk, sell, amt);
    cond_eq(&mut b, mk, salt, snd.nonce_t());
    {
        let (o1, o2, o3) = (one_c(&mut b, 1), one_c(&mut b, 2), one_c(&mut b, 3));
        let (d1, d2, d3) = (b.sub(want_chain, o1), b.sub(want_chain, o2), b.sub(want_chain, o3));
        let m = b.mul(d1, d2); let m = b.mul(m, d3); imply_zero(&mut b, mk, m);                    // 1, 2 or 3
        let same = b.is_equal(want_chain, chain_t); imply_zero(&mut b, mk, same.target);           // another chain's metal
        let z = b.is_equal(want_amt, zero); imply_zero(&mut b, mk, z.target);                      // something asked
        need(&mut b, mk, not_expired);                                                             // not expired already
        let ge1 = ge62(&mut b, rblocks, one); need(&mut b, mk, ge1);
        let hi = one_c(&mut b, 100_000); let le = ge62(&mut b, hi, rblocks); need(&mut b, mk, le);
        let t = b.arithmetic(F::from_canonical_u64(100), F::NEG_ONE, deposit, one, sell); let t = b.mul(t, mk.target); b.range_check(t, 62);   // deposit >= 1% of the sale
        imply_zero(&mut b, mk, sk1.target);                                                        // open or auction
        let g = b.and(mk, is_auc);
        let ge1 = ge62(&mut b, window_o, one); need(&mut b, g, ge1);
        let hi = one_c(&mut b, 10_000); let le = ge62(&mut b, hi, window_o); need(&mut b, g, le);
        // a new order has no state beyond its kind
        for t in taker_o.iter().chain([&until_o, &since_o, &bid_o, &close_o]) { imply_zero(&mut b, mk, *t); }
        let g = b.and(mk, is_open); imply_zero(&mut b, g, window_o);
    }
    // ---- Reserve: an open order that has not expired
    need(&mut b, rs, is_open); need(&mut b, rs, not_expired);
    // ---- Bid: an auction or a standing bid, not expired
    let aucbid = BoolTarget::new_unsafe(b.add(is_auc.target, is_bid.target));
    need(&mut b, bd, aucbid); need(&mut b, bd, not_expired);
    { let z = b.is_equal(bid, zero); imply_zero(&mut b, bd, z.target); }
    let g_auc = b.and(bd, is_auc);
    { let w = ge62(&mut b, bid, deposit); need(&mut b, g_auc, w); }
    let g_bid = b.and(bd, is_bid);
    { let w = ge62(&mut b, close_o, h_t); need(&mut b, g_bid, w);                                    // the auction is not over
      let bo1 = b.add_const(bid_o, F::ONE); let hi = ge62(&mut b, bid, bo1); need(&mut b, g_bid, hi); }  // higher than the bid waiting
    // ---- Reopen: reserved, or bidding with the auction closed; the reservation must have run out
    let resbid = BoolTarget::new_unsafe(b.add(is_res.target, is_bid.target));
    let ro_cl = BoolTarget::new_unsafe(b.add(ro.target, cl.target));
    need(&mut b, ro_cl, resbid);
    let g_robid = b.and(ro_cl, is_bid);
    { let c1 = b.add_const(close_o, F::ONE); let w = ge62(&mut b, h_t, c1); need(&mut b, g_robid, w); }
    let until_eff = { let cb = b.add(close_o, rblocks); let d = b.sub(cb, until_o); let m = b.mul(is_bid.target, d); b.add(until_o, m) };    // reserved: until; bidding: close + reserve blocks
    { let u1 = b.add_const(until_eff, F::ONE); let w = ge62(&mut b, h_t, u1); need(&mut b, ro, w); }
    // ---- Claim: the reservation is still running (the last block to claim is until_eff)
    { let w = ge62(&mut b, until_eff, h_t); need(&mut b, cl, w); }
    let held = b.select(is_bid, bid_o, deposit);
    // ---- Return: an open order (or an open auction) past its expiry
    { let oa = b.or(is_open, is_auc); need(&mut b, rt, oa); let e1 = b.add_const(expiry, F::ONE); let w = ge62(&mut b, h_t, e1); need(&mut b, rt, w); }

    // ---- the new state and the lock's leaves
    let rb_sum = b.add(h_t, rblocks);
    let close_n = { let hw = b.add(h_t, window_o); b.select(is_auc, hw, close_o) };
    let nk = { let x = b.mul_const(F::from_canonical_u64(3), bd.target); let y = b.mul(ro.target, is_bid.target); let y2 = b.mul_const(F::TWO, y); let t = b.add(rs.target, x); b.add(t, y2) };
    let ntaker: [Target; 4] = core::array::from_fn(|k| b.mul(rs_bd.target, taker[k]));
    let nuntil = { let z = b.mul(rs.target, rb_sum); limbs62(&mut b, z) };
    let nsince = b.mul(rs_bd.target, ntime);
    let nwindow = { let x = b.mul(bd.target, window_o); let g = b.mul(ro.target, is_bid.target); let y = b.mul(g, window_o); let z = b.add(x, y); limbs62(&mut b, z) };
    let nbid = limbs62(&mut b, bid);
    let nclose = { let z = b.mul(bd.target, close_n); limbs62(&mut b, z) };
    let addr_new = order_addr(&mut b, maker, sell_l, want_chain, wa_l, pay_to, ex_l, rb_l, dp_l, salt_l, nk, ntaker, nuntil, nsince, nwindow, nbid, nclose);
    let new_bal = { let x = b.mul(rs.target, deposit); let y = b.mul(bd.target, bid); let t = b.add(x, y); b.add(sell, t) };
    b.range_check(new_bal, 62);
    let mk_leaf = { let mut v = addr_old.elements.to_vec(); v.push(amt); v.push(nonce_new); v.extend([zero; 5]); hash_t(&mut b, v) };
    let ret_leaf = { let mut v = addr_new.elements.to_vec(); v.push(new_bal); v.push(lk.nonce); v.extend([zero; 5]); hash_t(&mut b, v) };
    let old_leaf = { let mut v = addr_old.elements.to_vec(); v.push(lk.bal); v.push(lk.nonce); v.extend(lk.peg); hash_t(&mut b, v) };

    // ---- the paid account: a refund (Bid on a standing bid), the maker's escrow (Reopen) or sale (Return)
    let act = { let t = b.add(ro.target, rt.target); let u = b.add(g_bid.target, t); BoolTarget::new_unsafe(b.add(u, cl.target)) };
    let amount = { let x = b.mul(g_bid.target, bid_o); let y = b.mul(ro.target, held); let z = b.mul(rt.target, sell); let w = b.mul(cl.target, lk.bal); let t = b.add(x, y); let u = b.add(t, z); b.add(u, w) };
    let to_taker = b.or(g_bid, cl);
    let expect: [Target; 4] = core::array::from_fn(|k| b.select(to_taker, taker_o[k], maker[k]));
    let ra = add_rc(&mut b);
    let cur2 = recv(&mut b, &ra, act, amount, expect, h_t, d_t, p_t, cur1);

    // ---- the order's own slot: a Make fills it, a Return empties it, the rest change it
    let old_l = select_hash_c(&mut b, mk, empty_leaf(), old_leaf);
    let r3 = root_from(&mut b, old_l, &lk.bits, &lk.sib);
    for k in 0..4 { b.connect(r3.elements[k], cur2.elements[k]); }
    let el = empty_leaf_t(&mut b);
    let gone = b.or(rt, cl);
    let new_l = { let moved = sel_hash(&mut b, mk, mk_leaf, ret_leaf); sel_hash(&mut b, gone, el, moved) };
    let fin = root_from(&mut b, new_l, &lk.bits, &lk.sib);

    // ---- the sender's signature over the operation message
    let head_v = |b: &mut CircuitBuilder<F, D>, kind: u64| -> Vec<Target> {
        let mut v = vec![b.constant(tag_felt(b"ZenOp...")), chain_t, snd.n_lo, snd.n_hi, b.constant(F::from_canonical_u64(kind))]; v.extend(snd.pk); v.extend([fee_lo, fee_hi]); v
    };
    let m_mk = { let mut v = head_v(&mut b, 1); v.extend([amt_lo, amt_hi]); v.extend(addr_old.elements); hash_t(&mut b, v) };
    let m_rs = { let mut v = head_v(&mut b, 4); v.extend(addr_old.elements); v.extend(taker); hash_t(&mut b, v) };
    let m_bd = { let mut v = head_v(&mut b, 17); v.extend(addr_old.elements); v.extend(taker); v.extend([bid_lo, bid_hi]); hash_t(&mut b, v) };
    let m_ro = { let mut v = head_v(&mut b, 6); v.extend(addr_old.elements); hash_t(&mut b, v) };
    let m_rt = { let mut v = head_v(&mut b, 7); v.extend(addr_old.elements); hash_t(&mut b, v) };
    let m_cl = { let mut v = head_v(&mut b, 5); v.extend(addr_old.elements); v.extend(pdig); hash_t(&mut b, v) };
    let msg1: [Target; 4] = core::array::from_fn(|k| {
        let mut acc = b.zero();
        for (kd, m) in [(mk, &m_mk), (rs, &m_rs), (bd, &m_bd), (ro, &m_ro), (rt, &m_rt), (cl, &m_cl)] { acc = b.mul_add(kd.target, m.elements[k], acc); }
        acc
    });
    let (sig1, pk1) = ec::verify_sig(&mut b, prm, msg1);
    for k in 0..4 { b.connect(pk1[k], snd.pk[k]); }
    ec::dbladd_pad(&mut b, prm);

    // ---- block data: the operation as the node writes it
    let l_idx = b.le_sum(lk.bits.iter()); let ia = b.le_sum(ra.bits.iter());
    let mut kind = b.zero();
    for (kd, code) in [(mk, 1u64), (rs, 4), (bd, 17), (ro, 6), (rt, 7), (cl, 5)] { kind = b.mul_const_add(F::from_canonical_u64(code), kd.target, kind); }
    let mut data = vec![b.constant(F::from_canonical_u64(ORDER_DATA_TAG)), kind, snd.idx, fee_lo, fee_hi, amt_lo, amt_hi, l_idx, ia, ra.new_r.target];
    for k in 0..4 { data.push(b.mul(ra.o_pk[k], ra.new_r.target)); }
    for k in 0..4 { data.push(b.mul(addr_old.elements[k], mk.target)); }
    data.extend(taker); data.extend([bid_lo, bid_hi, ntime]); data.extend(pdig);
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
    let t = OrT { hd, kinds, pdig, fee, amt, taker, bid, ntime, snd, sig1, maker, sell, want_chain, want_amt, pay_to, expiry, rblocks, deposit, salt, sk1, sk2, taker_o, until_o, since_o, window_o, bid_o, close_o, lk, ra };
    let _ = (nbd, d_t);
    OrderLeaf { data: b.build::<C>(), t }
}

pub struct OrderInput<'a> {
    pub op: &'a crate::locks::Op, pub trace: &'a crate::locks::OpTrace, pub height: u64, pub s: u64, pub root0: HashOut<F>, pub ntime: u32,
    pub sender_a: ec::P, pub sender_sig: (u128, BigUint),
}
pub fn set_witness(l: &OrderLeaf, pw: &mut PartialWitness<F>, inp: &OrderInput) -> Result<()> {
    use crate::locks::{Dest, Op, OrderState, Terms};
    let t = &l.t;
    set_head(pw, &t.hd, inp.height, inp.s, inp.root0)?;
    let tc = &inp.trace.touches;
    if tc.len() < 2 { bail!("an operation touches at least the sender and the order"); }
    let sender = set_sender(pw, &t.snd, &tc[0])?;
    let which = match inp.op { Op::Make { .. } => 0, Op::Reserve { .. } => 1, Op::Bid { .. } => 2, Op::Reopen { .. } => 3, Op::Return { .. } => 4, Op::OrderClaim { .. } => 5, _ => bail!("not an order operation") };
    for (i, bt) in t.kinds.iter().enumerate() { pw.set_bool_target(*bt, i == which)?; }
    let z4 = [F::ZERO; 4];
    let (fee, amt, bid, taker, ntime, dest): (u64, u64, u64, [F; 4], u32, Option<Dest>) = match inp.op {
        Op::Make { fee, amt, .. } => (*fee, *amt, 0, z4, 0, None),
        Op::Reserve { fee, taker, .. } => (*fee, 0, 0, *taker, inp.ntime, None),
        Op::Bid { fee, taker, bid, refund, .. } => (*fee, 0, *bid, *taker, inp.ntime, Some(*refund)),
        Op::Reopen { fee, to, .. } | Op::Return { fee, to, .. } | Op::OrderClaim { fee, to, .. } => (*fee, 0, 0, z4, 0, Some(*to)),
        _ => unreachable!(),
    };
    for (x, v) in [(t.fee, fee), (t.amt, amt), (t.bid, bid), (t.ntime, ntime as u64)] { pw.set_target(x, F::from_canonical_u64(v))?; }
    pw.set_target_arr(&t.taker, &taker)?;
    let pd = if let Op::OrderClaim { proof, .. } = inp.op { crate::locks::bytes_digest(proof) } else { z4 };
    pw.set_target_arr(&t.pdig, &pd)?;
    let terms = inp.trace.terms.clone().ok_or_else(|| anyhow!("no terms"))?;
    let Terms::Order { maker, sell, want_chain, want_amt, pay_to, expiry, reserve_blocks, deposit, salt, state } = terms else { bail!("not an order") };
    pw.set_target_arr(&t.maker, &maker)?; pw.set_target_arr(&t.pay_to, &pay_to)?;
    for (x, v) in [(t.sell, sell), (t.want_chain, want_chain as u64), (t.want_amt, want_amt), (t.expiry, expiry), (t.rblocks, reserve_blocks), (t.deposit, deposit), (t.salt, salt)] { pw.set_target(x, F::from_canonical_u64(v))?; }
    let (mut k, mut tk, mut until, mut since, mut window, mut bo, mut close) = (0u8, z4, 0u64, 0u32, 0u64, 0u64, 0u64);
    match &state {
        OrderState::Open => {}
        OrderState::Reserved { taker, until: u, since: s } => { k = 1; tk = *taker; until = *u; since = *s; }
        OrderState::Auction { window: w } => { k = 2; window = *w; }
        OrderState::Bidding { window: w, taker, bid, close: c, since: s } => { k = 3; window = *w; tk = *taker; bo = *bid; close = *c; since = *s; }
    }
    pw.set_bool_target(t.sk1, k & 1 == 1)?; pw.set_bool_target(t.sk2, k & 2 == 2)?;
    pw.set_target_arr(&t.taker_o, &tk)?;
    for (x, v) in [(t.until_o, until), (t.since_o, since as u64), (t.window_o, window), (t.bid_o, bo), (t.close_o, close)] { pw.set_target(x, F::from_canonical_u64(v))?; }
    // the lock (last touch) and the paid account (the middle one, if any)
    set_lock(pw, &t.lk, tc.last().unwrap())?;
    let paid = matches!(inp.op, Op::Reopen { .. } | Op::Return { .. } | Op::OrderClaim { .. }) || (matches!(inp.op, Op::Bid { .. }) && k == 3);
    let mid = &tc[1..tc.len() - 1];
    if mid.len() != paid as usize { bail!("{} touches between the sender and the order for a payout that is {}", mid.len(), paid); }
    set_rc(pw, &t.ra, mid.first(), dest.as_ref(), inp.height, &sender)?;
    let (e1, s1) = &inp.sender_sig;
    crate::set_sig(pw, &t.sig1, inp.sender_a, r_of(inp.sender_a, *e1, s1), s1, false)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::locks::{self, CrossMode, Ctx, Dest, Op, OpReq, OrderState, SignedOp, Terms};
    use crate::mint;
    use crate::node::dev;
    use crate::node::{Chain, DevStamp, Params};
    use crate::{Acct, Tree};
    use plonky2::field::types::PrimeField64;
    use std::collections::HashMap;
    use std::sync::OnceLock;

    const FEE: u64 = 10_000;
    const S: u64 = 1_000_000;
    const NT: u32 = 777_777;
    fn leaf() -> &'static OrderLeaf { static L: OnceLock<OrderLeaf> = OnceLock::new(); L.get_or_init(|| build_order(Params::devnet().chain as u64, &ec::params(), &[], 0)) }
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
            let ctx = Ctx { chain: self.chain, ntime: NT, cross: &CrossMode::Trust };
            locks::apply_ops_traced(std::slice::from_ref(op), &mut self.state, &mut self.tree, &mut self.locks, S, height, &ctx, self.tmpl, Some(&mut traces)).unwrap();
            traces.remove(0)
        }
        fn attempt(&self, op: &Op, trace: &locks::OpTrace, height: u64, root0: HashOut<F>, signer: &mint::Key) -> Option<Vec<u64>> {
            self.attempt_nt(op, trace, height, root0, signer, NT)
        }
        fn attempt_nt(&self, op: &Op, trace: &locks::OpTrace, height: u64, root0: HashOut<F>, signer: &mint::Key, ntime: u32) -> Option<Vec<u64>> {
            let req = crate::opcirc::req_of(op, &self.state).ok()?;
            let nonce = trace.touches[0].old.unwrap().nonce;
            let (e, sv) = mint::sign(signer, SignedOp::message(self.chain, nonce, &req));
            let inp = OrderInput { op, trace, height, s: S, root0, ntime, sender_a: signer.a, sender_sig: (e, sv) };
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
            check_pis(&pis, root0, self.tree.root(), op, height);
            pis
        }
        /// the operation's trace on a copy of the world (the node's rules), for the failure cases that need a valid trace
        fn trace_of(&self, op: &Op, height: u64) -> (locks::OpTrace, HashOut<F>) { let mut v = self.clone(); let r = v.tree.root(); (v.native(op, height), r) }
    }
    fn felts(h: HashOut<F>) -> Vec<u64> { h.elements.iter().map(|x| x.to_canonical_u64()).collect() }
    fn check_pis(pis: &[u64], root0: HashOut<F>, root1: HashOut<F>, op: &Op, h: u64) {
        assert_eq!(pis.len(), 84);
        assert_eq!(&pis[0..4], &felts(root0)[..], "root before");
        assert_eq!(&pis[4..8], &felts(root1)[..], "root after");
        assert_eq!((pis[8], pis[9]), (op.fee(), 1), "fee and count");
        assert_eq!(&pis[10..14], &locks::order_data_hash(op, NT).unwrap().map(|x| x.to_canonical_u64())[..], "the data hash is the node's");
        assert_eq!((pis[14], pis[15]), (S, h));
        assert!(pis[16..].iter().all(|x| *x == 0));
    }
    fn order(maker: &mint::Key, pay_to: &mint::Key, sell: u64, expiry: u64, state: OrderState, salt: u64) -> Terms {
        Terms::Order { maker: maker.addr, sell, want_chain: 1, want_amt: 5_000, pay_to: pay_to.addr, expiry, reserve_blocks: 5, deposit: sell / 50, salt, state }
    }
    fn make(w: &World, maker: &mint::Key, pay_to: &mint::Key, at: u32, sell: u64, expiry: u64, state: OrderState) -> Op {
        Op::Make { from: w.idx(maker), fee: FEE, amt: sell, at, terms: order(maker, pay_to, sell, expiry, state, w.nonce(maker)) }
    }

    #[test]
    fn the_order_leaf_builds_and_its_size_is_known() {
        let t = std::time::Instant::now();
        let l = leaf();
        println!("RESULT order leaf: 2^{} rows, {} gates, {} public values, build {:.1}s", l.data.common.degree_bits(), l.data.common.gates.len(), l.data.common.num_public_inputs, t.elapsed().as_secs_f64());
    }

    #[test]
    fn an_order_is_made_reserved_reopened_and_returned() {
        let ks = keys();
        let mut w = world();
        let (maker, taker, payto, anyone) = (ks[4].clone(), ks[5].clone(), ks[6].clone(), ks[7].clone());
        let mk = make(&w, &maker, &payto, 5000, 600_000_000, 40, OrderState::Open);
        w.both(&mk, 3, &maker);
        let at_open = w.clone();
        // the taker reserves it: pays the deposit, the order keeps the block's time
        let rs = Op::Reserve { from: w.idx(&taker), fee: FEE, lock: 5000, taker: taker.addr };
        w.both(&rs, 4, &taker);
        let reserved = w.clone();
        // reopen: not while the reservation runs (until 9), then the deposit goes to the maker
        let ro = Op::Reopen { from: w.idx(&anyone), fee: FEE, lock: 5000, to: Dest { idx: w.idx(&maker), new: None } };
        {
            let mut v = reserved.clone();
            let late = Op::Reopen { from: v.idx(&anyone), fee: FEE, lock: 5000, to: Dest { idx: v.idx(&maker), new: None } };
            let root0 = v.tree.root();
            let tr = v.native(&late, 10);
            assert!(reserved.attempt(&ro, &tr, 9, root0, &anyone).is_none(), "a reservation that still runs is not reopened");
            assert!(reserved.attempt(&ro, &tr, 10, root0, &anyone).is_some(), "after it has run out it is");
            let robbed = Op::Reopen { from: v.idx(&anyone), fee: FEE, lock: 5000, to: Dest { idx: v.idx(&anyone), new: None } };
            assert!(reserved.attempt(&robbed, &tr, 10, root0, &anyone).map_or(true, |p| p[10..14] != locks::order_data_hash(&robbed, NT).unwrap().map(|x| x.to_canonical_u64())[..]), "the data hash binds where the escrow goes");
            assert!(reserved.attempt(&ro, &tr, 10, root0, &ks[3]).is_none(), "the sender's signature must be the sender's");
        }
        w.both(&ro, 10, &anyone);
        // open again: a second reserve works, with another time bound into the data
        let rs2 = Op::Reserve { from: w.idx(&taker), fee: FEE, lock: 5000, taker: payto.addr };
        {
            let mut v = w.clone();
            let root0 = v.tree.root();
            let tr = v.native(&rs2, 11);
            assert!(w.attempt_nt(&rs2, &tr, 11, root0, &taker, NT + 1).map_or(true, |p| p[10..14] != locks::order_data_hash(&rs2, NT).unwrap().map(|x| x.to_canonical_u64())[..]), "another block time is another data hash");
        }
        // return after the expiry (40): the sale goes back to the maker and the order is gone
        let ret = |w: &World| Op::Return { from: w.idx(&anyone), fee: FEE, lock: 5000, to: Dest { idx: w.idx(&maker), new: None } };
        let mut v = at_open.clone();
        let r = ret(&v);
        let (tr, root0) = v.trace_of(&r, 41);
        assert!(at_open.attempt(&r, &tr, 40, root0, &anyone).is_none(), "an order that has not expired is not returned");
        v.both(&r, 41, &anyone);
        assert!(v.locks.is_empty());
        // (a reserved order is not returned: tested with a borrowed trace in `soundness.rs`)
    }

    #[test]
    fn an_auction_takes_bids_refunds_the_lower_one_and_reopens() {
        let ks = keys();
        let mut w = world();
        let (maker, b1, b2, payto, anyone) = (ks[4].clone(), ks[5].clone(), ks[6].clone(), ks[3].clone(), ks[7].clone());
        let mk = make(&w, &maker, &payto, 5100, 500_000_000, 60, OrderState::Auction { window: 3 });
        w.both(&mk, 3, &maker);
        let deposit = 500_000_000 / 50;
        // the first bid (not below the deposit)
        let bid1 = Op::Bid { from: w.idx(&b1), fee: FEE, lock: 5100, taker: b1.addr, bid: deposit + 1_000, refund: Dest { idx: 0, new: None } };
        {
            let mut v = w.clone();
            let low = Op::Bid { from: v.idx(&b1), fee: FEE, lock: 5100, taker: b1.addr, bid: deposit - 1, refund: Dest { idx: 0, new: None } };
            let (tr, root0) = v.trace_of(&bid1, 4);
            assert!(w.attempt(&low, &tr, 4, root0, &b1).is_none(), "a bid below the deposit is not proved");
        }
        w.both(&bid1, 4, &b1);
        // a higher bid refunds the first
        let bid2 = Op::Bid { from: w.idx(&b2), fee: FEE, lock: 5100, taker: b2.addr, bid: deposit + 9_000, refund: Dest { idx: w.idx(&b1), new: None } };
        {
            let mut v = w.clone();
            let (tr, root0) = v.trace_of(&bid2, 5);
            let same = Op::Bid { from: v.idx(&b2), fee: FEE, lock: 5100, taker: b2.addr, bid: deposit + 1_000, refund: Dest { idx: v.idx(&b1), new: None } };
            assert!(w.attempt(&same, &tr, 5, root0, &b2).is_none(), "a bid that is not higher is not proved");
            assert!(w.attempt(&bid2, &tr, 8, root0, &b2).is_none(), "a bid after the auction closed (7) is not proved");
            let wrong = Op::Bid { from: v.idx(&b2), fee: FEE, lock: 5100, taker: b2.addr, bid: deposit + 9_000, refund: Dest { idx: w.idx(&anyone), new: None } };
            assert!(w.attempt(&wrong, &tr, 5, root0, &b2).map_or(true, |p| p[10..14] != locks::order_data_hash(&wrong, NT).unwrap().map(|x| x.to_canonical_u64())[..]), "the data hash binds where the refund goes");
        }
        w.both(&bid2, 5, &b2);
        // the auction closed at 7; the winner's reservation lasts 5 more blocks (until 12); then the escrow goes to the maker and the order is an auction again
        let ro = Op::Reopen { from: w.idx(&anyone), fee: FEE, lock: 5100, to: Dest { idx: w.idx(&maker), new: None } };
        {
            let mut v = w.clone();
            let (tr, root0) = v.trace_of(&ro, 13);
            assert!(w.attempt(&ro, &tr, 12, root0, &anyone).is_none(), "the winner still holds its reservation");
        }
        w.both(&ro, 13, &anyone);
        assert!(matches!(w.locks.values().next().unwrap(), Terms::Order { state: OrderState::Auction { window: 3 }, .. }));
        // and an auction past its expiry is returned
        let ret = Op::Return { from: w.idx(&anyone), fee: FEE, lock: 5100, to: Dest { idx: w.idx(&maker), new: None } };
        w.both(&ret, 61, &anyone);
        assert!(w.locks.is_empty());
    }

    #[test]
    fn a_reserved_order_is_claimed_by_its_taker_within_the_reservation() {
        let ks = keys();
        let mut w = world();
        let (maker, taker, payto, anyone) = (ks[4].clone(), ks[5].clone(), ks[6].clone(), ks[7].clone());
        let mk = make(&w, &maker, &payto, 5000, 600_000_000, 40, OrderState::Open);
        w.both(&mk, 3, &maker);
        let open = w.clone();
        let rs = Op::Reserve { from: w.idx(&taker), fee: FEE, lock: 5000, taker: taker.addr };
        w.both(&rs, 4, &taker);                                    // reserved until 9
        let claim = |w: &World, proof: Vec<u8>| Op::OrderClaim { from: w.idx(&anyone), fee: FEE, lock: 5000, to: Dest { idx: w.idx(&taker), new: None }, proof };
        {
            // an open order cannot be claimed (the node refuses it too: no taker)
            let mut v = w.clone();
            let good = claim(&v, vec![1, 2, 3]);
            let root0 = v.tree.root();
            let tr = v.native(&good, 6);
            assert!(open.attempt(&good, &tr, 6, root0, &anyone).is_none(), "an open order has no taker to claim it");
            assert!(w.attempt(&good, &tr, 10, root0, &anyone).is_none(), "a claim after the reservation is not proved");
            assert!(w.attempt(&good, &tr, 6, root0, &taker).is_none(), "the sender's signature must be the sender's");
            let mut other = good.clone();
            if let Op::OrderClaim { proof, .. } = &mut other { *proof = vec![9, 9]; }
            let pis = w.attempt(&good, &tr, 6, root0, &anyone).expect("the claim proves");
            assert_ne!(&pis[10..14], &locks::order_data_hash(&other, NT).unwrap().map(|x| x.to_canonical_u64())[..], "the data hash binds the proof");
        }
        let c = claim(&w, vec![1, 2, 3]);
        let before = w.state[&(w.idx(&taker) as u64)].bal;
        w.both(&c, 9, &anyone);                                    // the last block of the reservation
        assert_eq!(w.state[&(w.idx(&taker) as u64)].bal, before + 600_000_000 + 12_000_000, "the taker has the sale and its deposit back");
        assert!(w.locks.is_empty(), "the order is gone");
    }
}
