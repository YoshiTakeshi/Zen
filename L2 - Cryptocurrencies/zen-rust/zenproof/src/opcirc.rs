// The operation leaf of the block proof, vault family (stage P2, Justus L. Ludovic).
//
// One operation is one leaf proof. It has the same public values as a state leaf (root before, root after, fee, count, data hash, S, height,
// then 68 zero verifier-data values), so the universal merge takes it like any other leaf; leaves are chained by root, so operations keep the
// order the block gives them.
//
// What it proves, for an operation that is one of
//   Make   a new vault: the sender pays `amt` and the fee, the vault's leaf (address = Poseidon digest of its terms) appears in an empty slot;
//   Claim  the vault's key signs where its money goes; the sender (anyone) pays the fee; the money moves to the named account (new or old);
//   Refund after the timeout the money goes back to the vault's owner;
//   * the sender's signature over the operation message (chain, nonce, request fields: exactly `SignedOp::message`), and that the key is the
//     sender's account address;
//   * the sender's leaf is in the root, its balance covers amount and fee, the fee floor, the amount floor, the "each gram counts once" bookkeeping
//     (same gadgets as a payment), the nonce goes up by one;
//   * the lock's address is the Poseidon digest of the terms given, and the rules of the kind (owner, salt, timeout against the height);
//   * Claim: the vault key's signature over (chain, lock, destination), whose key is the one in the terms;
//   * the Merkle updates, in the order the node applies them: sender; then the vault's slot (Make) or the receiving account (Claim, Refund);
//     then the vault's slot is emptied (Claim, Refund).
// Left to the node's own replay (the circuit holds a subset of the node's rules, which can only make the circuit accept fewer blocks than it should
// in the direction that matters: no money is made or taken): that a key is a point of the prime-order group, that a new address owns no other
// account, the sign of the key's y coordinate.
use crate::{cond_eq, connect_hash_if, empty_leaf, ge62, hash_t, imply_zero, pad_to, root_from, select_hash_c, settle_t};
use crate::{ec, Acct, C, D, DEPTH, F, NONCE_SHIFT, NPI, VDPI};
use num_bigint::BigUint;
use plonky2::field::types::{Field, PrimeField64};
use plonky2::gates::gate::GateRef;
use plonky2::hash::hash_types::{HashOut, HashOutTarget};
use plonky2::iop::target::{BoolTarget, Target};
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CircuitData};
use anyhow::Result;

pub struct OpLeaf { pub data: CircuitData<F, C, D>, pub t: OpT }
pub struct OpT {
    pub root0: HashOutTarget, pub h_t: Target, pub day: [Target; 4], pub s_t: Target,
    mk: BoolTarget, cl: BoolTarget, rf: BoolTarget, new_r: BoolTarget,
    fee: Target, amt: Target,
    s_pk: [Target; 4], s_bal: Target, s_nonce: Target, s_peg: [Target; 5], s_bits: Vec<BoolTarget>, s_sib: Vec<HashOutTarget>,
    sig1: ec::SigT,
    o2_pk: [Target; 4], o2_bal: Target, o2_nonce: Target, o2_peg: [Target; 5], b2_bits: Vec<BoolTarget>, b2_sib: Vec<HashOutTarget>,
    l_bal: Target, l_nonce: Target, l_peg: [Target; 5], b3_bits: Vec<BoolTarget>, b3_sib: Vec<HashOutTarget>,
    key: [Target; 11], owner: [Target; 4], timeout: [Target; 2], salt: [Target; 2],
    dest: [Target; 4],
    sig2: ec::SigT,
}

pub(crate) fn tag_felt(t: &[u8; 8]) -> F { F::from_canonical_u64(u64::from_le_bytes(*t)) }
pub(crate) fn sel4(b: &mut CircuitBuilder<F, D>, c: BoolTarget, x: [Target; 4], y: [Target; 4]) -> [Target; 4] { core::array::from_fn(|k| b.select(c, x[k], y[k])) }
pub(crate) fn sel_hash(b: &mut CircuitBuilder<F, D>, c: BoolTarget, x: HashOutTarget, y: HashOutTarget) -> HashOutTarget { HashOutTarget { elements: sel4(b, c, x.elements, y.elements) } }
/// 32-bit limbs of a value below 2^62
pub(crate) fn limbs62(b: &mut CircuitBuilder<F, D>, x: Target) -> (Target, Target) {
    let bits = b.split_le(x, 62);
    (b.le_sum(bits[..32].iter()), b.le_sum(bits[32..].iter()))
}
pub(crate) fn limbs_of_bits(b: &mut CircuitBuilder<F, D>, bits: &[BoolTarget]) -> Vec<Target> {
    bits.chunks(32).map(|c| b.le_sum(c.iter())).collect()
}

pub fn build_op(chain: u64, prm: &ec::Params, gates: &[GateRef<F, D>], degree_bits: usize) -> OpLeaf {
    let mut b = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());
    for g in gates { b.add_gate_to_gate_set(g.clone()); }
    ec::dbladd_reset();
    let (zero, one) = (b.zero(), b.one());
    let root0 = b.add_virtual_hash();
    let h_t = b.add_virtual_target(); b.range_check(h_t, 32);
    let s_t = b.add_virtual_target(); b.range_check(s_t, 62);
    // the block's day and rest period from its height (as in the state leaf)
    let day: [Target; 4] = core::array::from_fn(|_| b.add_virtual_target());
    let (d_t, rem_t, p_t, q_t) = (day[0], day[1], day[2], day[3]);
    b.range_check(d_t, 32); b.range_check(p_t, 32); b.range_check(rem_t, 10);
    let hh = b.mul_const_add(F::from_canonical_u64(crate::blockdata::BPD), d_t, rem_t); b.connect(hh, h_t);
    let top = b.constant(F::from_canonical_u64(crate::blockdata::BPD - 1));
    let rem_ok = ge62(&mut b, top, rem_t); b.assert_one(rem_ok.target);
    let dd = b.mul_const_add(F::from_canonical_u64(crate::blockdata::REST_DAYS), p_t, q_t); b.connect(dd, d_t);
    { let q1 = b.add_const(q_t, -F::ONE); let q2 = b.add_const(q_t, -F::TWO); let m1 = b.mul(q_t, q1); let m2 = b.mul(m1, q2); b.assert_zero(m2); }

    // which operation
    let (mk, cl, rf) = (b.add_virtual_bool_target_safe(), b.add_virtual_bool_target_safe(), b.add_virtual_bool_target_safe());
    { let s1 = b.add(mk.target, cl.target); let s2 = b.add(s1, rf.target); b.connect(s2, one); }
    let op_dest = BoolTarget::new_unsafe(b.add(cl.target, rf.target));      // Claim or Refund: money goes to an account, the vault is emptied
    let new_r = b.add_virtual_bool_target_safe();
    imply_zero(&mut b, mk, new_r.target);
    let not_mk = b.not(mk);
    let chain_t = b.constant(F::from_canonical_u64(chain));

    // ---- the sender
    let (fee, amt) = (b.add_virtual_target(), b.add_virtual_target());
    let (fee_lo, fee_hi) = limbs62(&mut b, fee);
    let (amt_lo, amt_hi) = limbs62(&mut b, amt);
    imply_zero(&mut b, not_mk, amt);                                          // only a Make carries an amount
    let t2 = b.arithmetic(F::from_canonical_u64(100), F::NEG_ONE, fee, one, s_t); b.range_check(t2, 62);   // fee >= S/100
    let t1 = b.arithmetic(F::from_canonical_u64(6), F::NEG_ONE, amt, one, s_t); let m1 = b.mul(t1, mk.target); b.range_check(m1, 62);   // amount >= S/6
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

    // ---- the vault's terms and address
    let key: [Target; 11] = core::array::from_fn(|_| b.add_virtual_target());
    for k in 0..10 { b.range_check(key[k], 32); }
    b.range_check(key[10], 8);
    let owner: [Target; 4] = core::array::from_fn(|_| b.add_virtual_target());
    let timeout: [Target; 2] = core::array::from_fn(|_| b.add_virtual_target());
    let salt: [Target; 2] = core::array::from_fn(|_| b.add_virtual_target());
    for t in timeout.iter().chain(salt.iter()) { b.range_check(*t, 32); }
    let mut v = vec![b.constant(tag_felt(b"ZenVault"))]; v.extend(key); v.extend(owner); v.extend(timeout); v.extend(salt);
    let d_t_addr = hash_t(&mut b, v);                                           // the lock's address
    // Make: the owner is the sender, the salt is the sender's nonce
    for k in 0..4 { cond_eq(&mut b, mk, owner[k], s_pk[k]); }
    cond_eq(&mut b, mk, salt[0], n_lo); cond_eq(&mut b, mk, salt[1], n_hi);
    // timeout against the height (the timeout is a 64-bit number in two limbs)
    let t_big = b.is_equal(timeout[1], zero); let t_big = b.not(t_big);
    let h1 = b.add_const(h_t, F::ONE);
    let ge_h = ge62(&mut b, timeout[0], h_t);
    let ge_h1 = ge62(&mut b, timeout[0], h1);
    let ok_claim = b.or(t_big, ge_h);                                           // timeout >= height
    let ok_make = b.or(t_big, ge_h1);                                           // timeout > height
    { let n = b.not(ok_make); let m = b.mul(mk.target, n.target); b.assert_zero(m); }
    { let n = b.not(ok_claim); let m = b.mul(cl.target, n.target); b.assert_zero(m); }
    { let m = b.mul(rf.target, ok_claim.target); b.assert_zero(m); }

    // ---- where the money goes (Claim, Refund) and the vault's own slot
    let dest: [Target; 4] = core::array::from_fn(|_| b.add_virtual_target());
    for k in 0..4 { cond_eq(&mut b, rf, dest[k], owner[k]); }
    let o2_pk: [Target; 4] = core::array::from_fn(|_| b.add_virtual_target());
    let (o2_bal, o2_nonce) = (b.add_virtual_target(), b.add_virtual_target());
    let o2_peg: [Target; 5] = core::array::from_fn(|_| b.add_virtual_target());
    let b2_bits: Vec<BoolTarget> = (0..DEPTH).map(|_| b.add_virtual_bool_target_safe()).collect();
    let b2_sib: Vec<HashOutTarget> = (0..DEPTH).map(|_| b.add_virtual_hash()).collect();
    let l_bal = b.add_virtual_target();
    let l_nonce = b.add_virtual_target();
    let l_peg: [Target; 5] = core::array::from_fn(|_| b.add_virtual_target());
    let b3_bits: Vec<BoolTarget> = (0..DEPTH).map(|_| b.add_virtual_bool_target_safe()).collect();
    let b3_sib: Vec<HashOutTarget> = (0..DEPTH).map(|_| b.add_virtual_hash()).collect();

    // the receiver's old leaf (empty for a Make's free slot and for a new account)
    let use_empty = BoolTarget::new_unsafe(b.add(mk.target, new_r.target));
    let mut v = o2_pk.to_vec(); v.push(o2_bal); v.push(o2_nonce); v.extend(o2_peg);
    let o2_full = hash_t(&mut b, v);
    let old2 = select_hash_c(&mut b, use_empty, empty_leaf(), o2_full);
    let r2 = root_from(&mut b, old2, &b2_bits, &b2_sib);
    for k in 0..4 { b.connect(r2.elements[k], cur1.elements[k]); }
    // a new account starts blank at its address with the block's nonce; an old one has the address named
    for k in 0..4 { cond_eq(&mut b, op_dest, o2_pk[k], dest[k]); }
    imply_zero(&mut b, new_r, o2_bal);
    for t in o2_peg { imply_zero(&mut b, new_r, t); }
    let nonce_new = b.mul_const(F::from_canonical_u64(1 << NONCE_SHIFT), h_t);
    { let nd = b.sub(nonce_new, o2_nonce); imply_zero(&mut b, new_r, nd); }
    // receiving: the vault's balance arrives as fresh money
    let r_new_bal = b.add(o2_bal, l_bal);
    let rb = b.mul(r_new_bal, op_dest.target); b.range_check(rb, 62);
    let (r_r1, r_u1, r_rd1, r_up1) = settle_t(&mut b, o2_bal, o2_peg[0], o2_peg[1], o2_peg[2], o2_peg[3], o2_peg[4], d_t, p_t);
    let mut v = o2_pk.to_vec(); v.push(r_new_bal); v.push(o2_nonce); v.extend([r_r1, r_u1, d_t, r_rd1, r_up1]);
    let recv_leaf = hash_t(&mut b, v);
    // a Make's new vault leaf: address, the amount, the block's nonce, nothing rested
    let mut v = d_t_addr.elements.to_vec(); v.push(amt); v.push(nonce_new); v.extend([zero; 5]);
    let lock_leaf = hash_t(&mut b, v);
    let new2 = sel_hash(&mut b, mk, lock_leaf, recv_leaf);
    let cur2 = root_from(&mut b, new2, &b2_bits, &b2_sib);

    // the emptied vault (Claim, Refund): its leaf is in the root with the address of the terms
    let mut v = d_t_addr.elements.to_vec(); v.push(l_bal); v.push(l_nonce); v.extend(l_peg);
    let l_old = hash_t(&mut b, v);
    let r3 = root_from(&mut b, l_old, &b3_bits, &b3_sib);
    connect_hash_if(&mut b, op_dest, r3, cur2);
    let el = empty_leaf_t(&mut b);
    let cur3 = root_from(&mut b, el, &b3_bits, &b3_sib);
    let fin = sel_hash(&mut b, op_dest, cur3, cur2);

    // ---- the vault key's signature (Claim)
    let claim_msg = {
        let mut v = vec![b.constant(tag_felt(b"ZenVClm.")), chain_t]; v.extend(d_t_addr.elements); v.extend(dest);
        hash_t(&mut b, v)
    };
    let (sig2, _pk2, e_bits) = ec::verify_sig_e(&mut b, prm, claim_msg.elements);
    for k in 0..5 {
        let word = b.mul_const_add(F::from_canonical_u64(1 << 32), key[2 * k + 1], key[2 * k]);
        let word = b.add_const(word, ec::shift().0[k]);
        cond_eq(&mut b, cl, sig2.a.x[k], word);
    }
    let e_limbs = limbs_of_bits(&mut b, &e_bits);
    let mut s2_bits = sig2.s_bits.clone(); s2_bits.push(BoolTarget::new_unsafe(zero));
    let s_limbs = limbs_of_bits(&mut b, &s2_bits);

    // ---- the sender's signature over the operation message
    let m_mk = { let mut v = vec![b.constant(tag_felt(b"ZenOp...")), chain_t, n_lo, n_hi, b.constant(F::ONE)]; v.extend(s_pk); v.extend([fee_lo, fee_hi, amt_lo, amt_hi]); v.extend(d_t_addr.elements); hash_t(&mut b, v) };
    let m_cl = { let mut v = vec![b.constant(tag_felt(b"ZenOp...")), chain_t, n_lo, n_hi, b.constant(F::TWO)]; v.extend(s_pk); v.extend([fee_lo, fee_hi]); v.extend(d_t_addr.elements); v.extend(dest); v.extend(e_limbs.iter().copied()); v.extend(s_limbs.iter().copied()); hash_t(&mut b, v) };
    let m_rf = { let mut v = vec![b.constant(tag_felt(b"ZenOp...")), chain_t, n_lo, n_hi, b.constant(F::from_canonical_u64(3))]; v.extend(s_pk); v.extend([fee_lo, fee_hi]); v.extend(d_t_addr.elements); v.extend(dest); hash_t(&mut b, v) };
    let m_dest = sel_hash(&mut b, cl, m_cl, m_rf);
    let msg1 = sel_hash(&mut b, mk, m_mk, m_dest);
    let (sig1, pk1) = ec::verify_sig(&mut b, prm, msg1.elements);
    for k in 0..4 { b.connect(pk1[k], s_pk[k]); }
    ec::dbladd_pad(&mut b, prm);

    // ---- block data: the operation as the node writes it
    let s_idx = b.le_sum(s_bits.iter()); let i2 = b.le_sum(b2_bits.iter()); let i3 = b.le_sum(b3_bits.iter());
    let kind = { let a = b.mul_const(F::TWO, cl.target); let c = b.mul_const(F::from_canonical_u64(3), rf.target); let s = b.add(mk.target, a); b.add(s, c) };
    let mut data = vec![kind, s_idx, fee_lo, fee_hi, amt_lo, amt_hi];
    data.push(b.mul(mk.target, i2));                  // the slot a new vault takes
    data.push(b.mul(op_dest.target, i3));             // the vault that is emptied
    data.push(b.mul(op_dest.target, i2));             // the receiving account
    data.push(new_r.target);
    for k in 0..4 { data.push(b.mul(dest[k], new_r.target)); }
    for k in 0..4 { data.push(b.mul(d_t_addr.elements[k], mk.target)); }
    for k in 0..4 { data.push(b.mul(e_limbs[k], cl.target)); }
    for k in 0..10 { data.push(b.mul(s_limbs[k], cl.target)); }
    let tagt = b.constant(F::from_canonical_u64(OP_DATA_TAG));
    data.insert(0, tagt);
    let data_h = hash_t(&mut b, data);

    b.register_public_inputs(&root0.elements);
    b.register_public_inputs(&fin.elements);
    b.register_public_input(fee);
    b.register_public_input(one);
    b.register_public_inputs(&data_h.elements);
    b.register_public_input(s_t);
    b.register_public_input(h_t);
    for _ in 0..VDPI { b.register_public_input(zero); }
    let _ = NPI;
    pad_to(&mut b, degree_bits);
    let t = OpT { root0, h_t, day, s_t, mk, cl, rf, new_r, fee, amt, s_pk, s_bal, s_nonce, s_peg, s_bits, s_sib, sig1,
                  o2_pk, o2_bal, o2_nonce, o2_peg, b2_bits, b2_sib, l_bal, l_nonce, l_peg, b3_bits, b3_sib, key, owner, timeout, salt, dest, sig2 };
    OpLeaf { data: b.build::<C>(), t }
}
pub(crate) fn empty_leaf_t(b: &mut CircuitBuilder<F, D>) -> HashOutTarget {
    let e = empty_leaf();
    HashOutTarget { elements: core::array::from_fn(|k| b.constant(e.elements[k])) }
}
/// domain tag of an operation's block-data hash
pub const OP_DATA_TAG: u64 = u64::from_le_bytes(*b"ZenOpDat");


/// everything the witness of one operation leaf is made of
pub struct OpInput<'a> {
    pub op: &'a crate::locks::Op, pub trace: &'a crate::locks::OpTrace, pub height: u64, pub s: u64, pub root0: HashOut<F>, pub chain: u8,
    /// the sender's key and its signature (e, s) over `SignedOp::message` of this operation
    pub sender_a: ec::P, pub sender_sig: (u128, BigUint),
}
/// the request a sender signs for this resolved operation, read from the state before it (the lock's address, where the money goes)
pub fn req_of(op: &crate::locks::Op, state: &std::collections::HashMap<u64, Acct>) -> Result<crate::locks::OpReq> {
    use crate::locks::{Dest, Op, OpReq};
    let addr = |d: &Dest| -> Result<[F; 4]> { match d.new { Some(a) => Ok(a), None => Ok(state.get(&(d.idx as u64)).ok_or_else(|| anyhow::anyhow!("unknown receiver"))?.pk) } };
    let pk = |i: u32| -> Result<[F; 4]> { Ok(state.get(&(i as u64)).ok_or_else(|| anyhow::anyhow!("unknown account {i}"))?.pk) };
    Ok(match op {
        Op::Make { from, fee, amt, terms, .. } => OpReq::Make { from: pk(*from)?, amt: *amt, fee: *fee, terms: terms.clone() },
        Op::VaultClaim { from, fee, lock, to, e, s } => OpReq::VaultClaim { from: pk(*from)?, fee: *fee, lock: pk(*lock)?, to: addr(to)?, e: *e, s: *s },
        Op::VaultRefund { from, fee, lock, to } => OpReq::VaultRefund { from: pk(*from)?, fee: *fee, lock: pk(*lock)?, to: addr(to)? },
        Op::ChanStart { from, fee, lock } => OpReq::ChanStart { from: pk(*from)?, fee: *fee, lock: pk(*lock)? },
        Op::ChanUpdate { from, fee, lock, seq, bal_a, locks, sigs } => OpReq::ChanUpdate { from: pk(*from)?, fee: *fee, lock: pk(*lock)?, seq: *seq, bal_a: *bal_a, locks: locks.clone(), sigs: *sigs },
        Op::ChanSettle { from, fee, lock, wits, .. } => OpReq::ChanSettle { from: pk(*from)?, fee: *fee, lock: pk(*lock)?, wits: wits.clone() },
        Op::ChanClose { from, fee, lock, bal_a, sigs, .. } => OpReq::ChanClose { from: pk(*from)?, fee: *fee, lock: pk(*lock)?, bal_a: *bal_a, sigs: *sigs },
        Op::ChanFund { from, fee, lock, amt } => OpReq::ChanFund { from: pk(*from)?, fee: *fee, lock: pk(*lock)?, amt: *amt },
        Op::Reserve { from, fee, lock, taker } => OpReq::Reserve { from: pk(*from)?, fee: *fee, lock: pk(*lock)?, taker: *taker },
        Op::Bid { from, fee, lock, taker, bid, .. } => OpReq::Bid { from: pk(*from)?, fee: *fee, lock: pk(*lock)?, taker: *taker, bid: *bid },
        Op::Reopen { from, fee, lock, .. } => OpReq::Reopen { from: pk(*from)?, fee: *fee, lock: pk(*lock)? },
        Op::OrderClaim { from, fee, lock, proof, .. } => OpReq::OrderClaim { from: pk(*from)?, fee: *fee, lock: pk(*lock)?, proof: proof.clone() },
        Op::Return { from, fee, lock, .. } => OpReq::Return { from: pk(*from)?, fee: *fee, lock: pk(*lock)? },
        Op::FactoryStart { from, fee, lock, idx } => OpReq::FactoryStart { from: pk(*from)?, fee: *fee, lock: pk(*lock)?, idx: *idx },
        Op::FactoryPost { from, fee, lock, idx, seq, bal_c, locks, sigs } => OpReq::FactoryPost { from: pk(*from)?, fee: *fee, lock: pk(*lock)?, idx: *idx, seq: *seq, bal_c: *bal_c, locks: locks.clone(), sigs: *sigs },
        Op::FactoryExit { from, fee, lock, idx, wits, .. } => OpReq::FactoryExit { from: pk(*from)?, fee: *fee, lock: pk(*lock)?, idx: *idx, wits: wits.clone() },
        Op::FactoryExitNow { from, fee, lock, idx, bal_c, sigs, .. } => OpReq::FactoryExitNow { from: pk(*from)?, fee: *fee, lock: pk(*lock)?, idx: *idx, bal_c: *bal_c, sigs: *sigs },
        Op::FactoryFund { from, fee, lock, idx, amt } => OpReq::FactoryFund { from: pk(*from)?, fee: *fee, lock: pk(*lock)?, idx: *idx, amt: *amt },
        _ => anyhow::bail!("not a provable operation"),
    })
}
/// R = sG - eA, what the circuit takes in place of e
pub fn r_of(a: ec::P, e: u128, s: &BigUint) -> ec::P { ec::add(ec::mul_g(&ec::params(), s), ec::neg(ec::mul(a, &BigUint::from(e)))) }
pub(crate) fn limbs(b: &[u8]) -> Vec<F> { b.chunks(4).map(|c| { let mut l = [0u8; 4]; l[..c.len()].copy_from_slice(c); F::from_canonical_u32(u32::from_le_bytes(l)) }).collect() }
pub(crate) fn set_path(pw: &mut PartialWitness<F>, bits: &[BoolTarget], sib: &[HashOutTarget], idx: u64, sibs: &[HashOut<F>]) -> Result<()> {
    for k in 0..DEPTH { pw.set_bool_target(bits[k], (idx >> k) & 1 == 1)?; pw.set_hash_target(sib[k], sibs[k])?; }
    Ok(())
}
pub(crate) fn set_acct(pw: &mut PartialWitness<F>, pk: &[Target; 4], bal: Target, nonce: Target, peg: &[Target; 5], a: &Acct) -> Result<()> {
    pw.set_target_arr(pk, &a.pk)?; pw.set_target(bal, F::from_canonical_u64(a.bal))?; pw.set_target(nonce, F::from_canonical_u64(a.nonce))?;
    crate::set_peg(pw, peg, a)
}
pub fn set_witness(l: &OpLeaf, pw: &mut PartialWitness<F>, inp: &OpInput) -> Result<()> {
    use crate::locks::{Op, OpReq, Terms, SignedOp, vault_claim_msg};
    let t = &l.t;
    let (day, per) = crate::blockdata::day_period(inp.height);
    pw.set_hash_target(t.root0, inp.root0)?;
    pw.set_target(t.h_t, F::from_canonical_u64(inp.height))?;
    pw.set_target(t.s_t, F::from_canonical_u64(inp.s))?;
    for (x, v) in t.day.iter().zip([day, inp.height - day * crate::blockdata::BPD, per, day - per * crate::blockdata::REST_DAYS]) { pw.set_target(*x, F::from_canonical_u64(v))?; }
    let tc = &inp.trace.touches;
    let sender = tc[0].old.ok_or_else(|| anyhow::anyhow!("the sender has no account"))?;
    let (kind, fee, amt) = match inp.op {
        Op::Make { fee, amt, .. } => (1, *fee, *amt),
        Op::VaultClaim { fee, .. } => (2, *fee, 0),
        Op::VaultRefund { fee, .. } => (3, *fee, 0),
        _ => anyhow::bail!("not a vault operation"),
    };
    for (bt, v) in [(t.mk, kind == 1), (t.cl, kind == 2), (t.rf, kind == 3)] { pw.set_bool_target(bt, v)?; }
    pw.set_target(t.fee, F::from_canonical_u64(fee))?; pw.set_target(t.amt, F::from_canonical_u64(amt))?;
    set_acct(pw, &t.s_pk, t.s_bal, t.s_nonce, &t.s_peg, &sender)?;
    set_path(pw, &t.s_bits, &t.s_sib, tc[0].idx, &tc[0].sibs)?;
    let terms = inp.trace.terms.clone().ok_or_else(|| anyhow::anyhow!("no terms"))?;
    let Terms::Vault { key, owner, timeout, salt } = terms.clone() else { anyhow::bail!("not a vault") };
    pw.set_target_arr(&t.key, &limbs(&key))?;
    pw.set_target_arr(&t.owner, &owner)?;
    for (x, v) in t.timeout.iter().zip([timeout & 0xffff_ffff, timeout >> 32]) { pw.set_target(*x, F::from_canonical_u64(v))?; }
    for (x, v) in t.salt.iter().zip([salt & 0xffff_ffff, salt >> 32]) { pw.set_target(*x, F::from_canonical_u64(v))?; }
    let lock_addr = terms.digest();
    let z4 = [F::ZERO; 4];
    // the second touch: a new vault's slot, or the receiving account
    let t2 = &tc[1];
    set_path(pw, &t.b2_bits, &t.b2_sib, t2.idx, &t2.sibs)?;
    let (dest, new_r) = match inp.op {
        Op::Make { .. } => { for x in t.o2_pk.iter() { pw.set_target(*x, F::ZERO)?; } for x in [t.o2_bal, t.o2_nonce].into_iter().chain(t.o2_peg) { pw.set_target(x, F::ZERO)?; } (z4, false) }
        Op::VaultClaim { to, .. } | Op::VaultRefund { to, .. } => {
            let (acct, new_r) = match t2.old { Some(a) => (a, false), None => (Acct::blank(to.new.ok_or_else(|| anyhow::anyhow!("an empty slot needs a new address"))?, inp.height << NONCE_SHIFT, &sender), true) };
            set_acct(pw, &t.o2_pk, t.o2_bal, t.o2_nonce, &t.o2_peg, &acct)?;
            (acct.pk, new_r)
        }
        _ => unreachable!(),
    };
    pw.set_bool_target(t.new_r, new_r)?;
    pw.set_target_arr(&t.dest, &dest)?;
    // the third: the emptied vault
    match tc.get(2) {
        Some(t3) => {
            let a = t3.old.ok_or_else(|| anyhow::anyhow!("no vault leaf"))?;
            pw.set_target(t.l_bal, F::from_canonical_u64(a.bal))?; pw.set_target(t.l_nonce, F::from_canonical_u64(a.nonce))?;
            crate::set_peg(pw, &t.l_peg, &a)?;
            set_path(pw, &t.b3_bits, &t.b3_sib, t3.idx, &t3.sibs)?;
        }
        None => {
            pw.set_target(t.l_bal, F::ZERO)?; pw.set_target(t.l_nonce, F::ZERO)?; for x in t.l_peg { pw.set_target(x, F::ZERO)?; }
            for k in 0..DEPTH { pw.set_bool_target(t.b3_bits[k], false)?; pw.set_hash_target(t.b3_sib[k], HashOut { elements: z4 })?; }
        }
    }
    // the sender's signature
    let (e1, s1) = &inp.sender_sig;
    crate::set_sig(pw, &t.sig1, inp.sender_a, r_of(inp.sender_a, *e1, s1), s1, false)?;
    let _ = SignedOp::message; let _ = OpReq::Reopen { from: z4, fee: 0, lock: z4 };
    // the vault key's signature (Claim), else a dummy one of a fixed key over the same message
    let claim_msg = vault_claim_msg(inp.chain, &lock_addr, &dest);
    match inp.op {
        Op::VaultClaim { e, s, .. } => {
            let a = crate::mint::decode_point(&key)?;
            let sv = BigUint::from_bytes_le(s);
            crate::set_sig(pw, &t.sig2, a, r_of(a, *e, &sv), &sv, false)?;
        }
        _ => {
            let pad = crate::mint::Key::from_secret(BigUint::from(7777u32));
            let (e, sv) = crate::mint::sign(&pad, claim_msg);
            crate::set_sig(pw, &t.sig2, pad.a, r_of(pad.a, e, &sv), &sv, false)?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::locks::{self, Dest, Op, OpReq, SignedOp, Terms, CrossMode, Ctx};
    use crate::mint;
    use crate::node::dev;
    use crate::node::{Chain, DevStamp, Params};
    use crate::Tree;
    use std::collections::HashMap;
    use std::sync::OnceLock;

    const FEE: u64 = 10_000;
    const S: u64 = 1_000_000;
    fn leaf() -> &'static OpLeaf { static L: OnceLock<OpLeaf> = OnceLock::new(); L.get_or_init(|| build_op(Params::devnet().chain as u64, &ec::params(), &[], 0)) }
    struct World { state: HashMap<u64, Acct>, tree: Tree, locks: locks::LockTable, keys: Vec<mint::Key>, chain: u8, tmpl: Acct }
    fn world() -> World {
        let keys = dev::devnet_keys(8);
        let c = Chain::open(Params::devnet(), &dev::genesis_of(&keys), Box::new(DevStamp), None).unwrap();
        let tmpl = *c.state.values().next().unwrap();
        World { state: c.state.clone(), tree: c.tree.clone(), locks: c.locks.clone(), keys, chain: c.p.chain, tmpl }
    }
    impl World {
        fn idx(&self, k: &mint::Key) -> u32 { self.state.iter().find(|(_, a)| a.pk == k.addr).map(|(i, _)| *i as u32).unwrap() }
        fn nonce(&self, k: &mint::Key) -> u64 { self.state[&(self.idx(k) as u64)].nonce }
        fn addr_of_dest(&self, to: &Dest) -> [F; 4] { to.new.unwrap_or_else(|| self.state[&(to.idx as u64)].pk) }
        /// the request the sender signs for this operation, from the state before it
        fn req(&self, op: &Op) -> OpReq {
            let from = self.state[&(op.from() as u64)].pk;
            match op {
                Op::Make { fee, amt, terms, .. } => OpReq::Make { from, amt: *amt, fee: *fee, terms: terms.clone() },
                Op::VaultClaim { fee, lock, to, e, s, .. } => OpReq::VaultClaim { from, fee: *fee, lock: self.state[&(*lock as u64)].pk, to: self.addr_of_dest(to), e: *e, s: *s },
                Op::VaultRefund { fee, lock, to, .. } => OpReq::VaultRefund { from, fee: *fee, lock: self.state[&(*lock as u64)].pk, to: self.addr_of_dest(to) },
                _ => unreachable!(),
            }
        }
        /// the node's own application of the operation: changes the world, gives the trace
        fn native(&mut self, op: &Op, height: u64) -> locks::OpTrace {
            let mut traces = vec![];
            let ctx = Ctx { chain: self.chain, ntime: 0, cross: &CrossMode::Off };
            locks::apply_ops_traced(std::slice::from_ref(op), &mut self.state, &mut self.tree, &mut self.locks, S, height, &ctx, self.tmpl, Some(&mut traces)).unwrap();
            traces.remove(0)
        }
        /// try to prove: the public values when the proof comes out and checks, none when the witness is refused or the proof is bad
        fn attempt(&self, op: &Op, req: &OpReq, trace: &locks::OpTrace, height: u64, root0: HashOut<F>, signer: &mint::Key) -> Option<Vec<u64>> {
            let nonce = trace.touches[0].old.unwrap().nonce;
            let (e, sv) = mint::sign(signer, SignedOp::message(self.chain, nonce, req));
            let inp = OpInput { op, trace, height, s: S, root0, chain: self.chain, sender_a: signer.a, sender_sig: (e, sv) };
            let mut pw = PartialWitness::new();
            if set_witness(leaf(), &mut pw, &inp).is_err() { return None; }
            let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| leaf().data.prove(pw)));
            let Ok(Ok(proof)) = r else { return None };
            let pis: Vec<u64> = proof.public_inputs.iter().map(|x| x.to_canonical_u64()).collect();
            leaf().data.verify(proof).ok().map(|_| pis)
        }
    }
    fn vault(owner: &mint::Key, claimer: &mint::Key, timeout: u64, salt: u64) -> Terms { Terms::Vault { key: mint::encode_point(claimer.a), owner: owner.addr, timeout, salt } }
    fn felts(h: HashOut<F>) -> Vec<u64> { h.elements.iter().map(|x| x.to_canonical_u64()).collect() }
    fn check_pis(pis: &[u64], root0: HashOut<F>, root1: HashOut<F>, op: &Op, h: u64) {
        assert_eq!(pis.len(), 84);
        assert_eq!(&pis[0..4], &felts(root0)[..], "root before");
        assert_eq!(&pis[4..8], &felts(root1)[..], "root after");
        assert_eq!((pis[8], pis[9]), (op.fee(), 1), "fee and count");
        assert_eq!(&pis[10..14], &locks::op_data_hash(op).unwrap().map(|x| x.to_canonical_u64())[..], "the data hash is the node's");
        assert_eq!((pis[14], pis[15]), (S, h));
        assert!(pis[16..].iter().all(|x| *x == 0));
    }

    #[test]
    fn the_vault_leaf_builds_and_its_size_is_known() {
        let t = std::time::Instant::now();
        let op = leaf();
        println!("RESULT op leaf: 2^{} rows, {} gates, {} public values, build {:.1}s", op.data.common.degree_bits(), op.data.common.gates.len(), op.data.common.num_public_inputs, t.elapsed().as_secs_f64());
    }

    #[test]
    fn a_vault_is_made_claimed_and_refunded_with_proofs_that_match_the_nodes_own_replay() {
        let mut w = world();
        let (owner, claimer, dest, anyone) = (w.keys[4].clone(), w.keys[5].clone(), w.keys[6].clone(), w.keys[7].clone());
        let h = 5;
        // make a vault of 500 000 000 at slot 5000, timing out at height 20
        let (from, nonce) = (w.idx(&owner), w.nonce(&owner));
        let make = Op::Make { from, fee: FEE, amt: 500_000_000, at: 5000, terms: vault(&owner, &claimer, 20, nonce) };
        let (req, root0) = (w.req(&make), w.tree.root());
        let tr = w.native(&make, h);
        let pis = w.attempt(&make, &req, &tr, h, root0, &owner).expect("the make proves");
        check_pis(&pis, root0, w.tree.root(), &make, h);
        let lock_addr = w.state[&5000].pk;
        // the vault's key signs: the money goes to `dest`, the fee is paid by someone else
        let (e, sv) = mint::sign(&claimer, locks::vault_claim_msg(w.chain, &lock_addr, &dest.addr));
        let claim = Op::VaultClaim { from: w.idx(&anyone), fee: FEE, lock: 5000, to: Dest { idx: w.idx(&dest), new: None }, e, s: mint::s_bytes(&sv) };
        // a copy of the world to try the refund and the failures on the same state
        let before = (w.state.clone(), w.tree.clone(), w.locks.clone());
        let (req, root0) = (w.req(&claim), w.tree.root());
        let tr_claim = w.native(&claim, h + 1);
        let pis = w.attempt(&claim, &req, &tr_claim, h + 1, root0, &anyone).expect("the claim proves");
        check_pis(&pis, root0, w.tree.root(), &claim, h + 1);
        assert!(w.locks.is_empty(), "the vault is gone");
        // the same claim, with failures built in
        let bad_signer = w.keys[3].clone();
        assert!(w.attempt(&claim, &req, &tr_claim, h + 1, root0, &bad_signer).is_none(), "the sender's signature must be the sender's");
        assert!(w.attempt(&claim, &req, &tr_claim, 25, root0, &anyone).is_none(), "a claim after the timeout is not proved");
        let (e2, s2) = mint::sign(&dest, locks::vault_claim_msg(w.chain, &lock_addr, &dest.addr));
        let forged = Op::VaultClaim { from: w.idx(&anyone), fee: FEE, lock: 5000, to: Dest { idx: w.idx(&dest), new: None }, e: e2, s: mint::s_bytes(&s2) };
        let forged_req = OpReq::VaultClaim { from: anyone.addr, fee: FEE, lock: lock_addr, to: dest.addr, e: e2, s: mint::s_bytes(&s2) };
        assert!(w.attempt(&forged, &forged_req, &tr_claim, h + 1, root0, &anyone).is_none(), "a claim signed by another key than the vault's is not proved");
        assert!(w.attempt(&claim, &req, &tr_claim, h + 1, felts_to_hash(&[1, 2, 3, 4]), &anyone).is_none(), "the root before must be the real one");
        let mut greedy = tr_claim.clone(); { let mut a = greedy.touches[0].old.unwrap(); a.bal += 1; greedy.touches[0].old = Some(a); }
        assert!(w.attempt(&claim, &req, &greedy, h + 1, root0, &anyone).is_none(), "the sender's leaf must be the one in the tree");
        // refund: back to the world with the vault; before the timeout it is not proved, after it is
        w.state = before.0; w.tree = before.1; w.locks = before.2;
        let refund = Op::VaultRefund { from: w.idx(&anyone), fee: FEE, lock: 5000, to: Dest { idx: w.idx(&owner), new: None } };
        let (req, root0) = (w.req(&refund), w.tree.root());
        let tr_refund = w.native(&refund, 21);
        assert!(w.attempt(&refund, &req, &tr_refund, 15, root0, &anyone).is_none(), "a refund before the timeout is not proved");
        let pis = w.attempt(&refund, &req, &tr_refund, 21, root0, &anyone).expect("the refund proves");
        check_pis(&pis, root0, w.tree.root(), &refund, 21);
        assert!(w.locks.is_empty());
    }

    #[test]
    fn a_claim_can_open_a_new_account_for_the_money() {
        let mut w = world();
        let (owner, claimer, anyone) = (w.keys[4].clone(), w.keys[5].clone(), w.keys[7].clone());
        let (from, nonce) = (w.idx(&owner), w.nonce(&owner));
        let make = Op::Make { from, fee: FEE, amt: 300_000_000, at: 7000, terms: vault(&owner, &claimer, 50, nonce) };
        let root0 = w.tree.root(); let _ = w.req(&make);
        w.native(&make, 3);
        let fresh = mint::Key::from_secret(num_bigint::BigUint::from(424242u32));
        let lock_addr = w.state[&7000].pk;
        let (e, sv) = mint::sign(&claimer, locks::vault_claim_msg(w.chain, &lock_addr, &fresh.addr));
        let claim = Op::VaultClaim { from: w.idx(&anyone), fee: FEE, lock: 7000, to: Dest { idx: 7001, new: Some(fresh.addr) }, e, s: mint::s_bytes(&sv) };
        let (req, root1) = (w.req(&claim), w.tree.root());
        let tr = w.native(&claim, 4);
        let pis = w.attempt(&claim, &req, &tr, 4, root1, &anyone).expect("the claim into a new account proves");
        check_pis(&pis, root1, w.tree.root(), &claim, 4);
        assert_eq!(w.state[&7001].bal, 300_000_000);
        let _ = root0;
    }
    #[test]
    fn the_timeout_edge_and_inflated_balances_are_exact() {
        let mut w = world();
        let (owner, claimer, dest, anyone) = (w.keys[4].clone(), w.keys[5].clone(), w.keys[6].clone(), w.keys[7].clone());
        let (from, nonce) = (w.idx(&owner), w.nonce(&owner));
        let make = Op::Make { from, fee: FEE, amt: 400_000_000, at: 6000, terms: vault(&owner, &claimer, 20, nonce) };
        let (_req, _root0) = (w.req(&make), w.tree.root());
        w.native(&make, 3);
        let lock_addr = w.state[&6000].pk;
        let (e, sv) = mint::sign(&claimer, locks::vault_claim_msg(w.chain, &lock_addr, &dest.addr));
        let claim = Op::VaultClaim { from: w.idx(&anyone), fee: FEE, lock: 6000, to: Dest { idx: w.idx(&dest), new: None }, e, s: mint::s_bytes(&sv) };
        let refund = Op::VaultRefund { from: w.idx(&anyone), fee: FEE, lock: 6000, to: Dest { idx: w.idx(&owner), new: None } };
        let root0 = w.tree.root();
        // the claim's trace and the refund's trace on the same state (the node applies them separately)
        let (creq, rreq) = (w.req(&claim), w.req(&refund));
        let snap = (w.state.clone(), w.tree.clone(), w.locks.clone());
        let ctrace = w.native(&claim, 20);
        w.state = snap.0.clone(); w.tree = snap.1.clone(); w.locks = snap.2.clone();
        let rtrace = w.native(&refund, 21);
        for (h, claim_ok, refund_ok) in [(19, true, false), (20, true, false), (21, false, true), (22, false, true)] {
            assert_eq!(w.attempt(&claim, &creq, &ctrace, h, root0, &anyone).is_some(), claim_ok, "claim at height {h}");
            assert_eq!(w.attempt(&refund, &rreq, &rtrace, h, root0, &anyone).is_some(), refund_ok, "refund at height {h}");
        }
        // a bigger vault balance, or a bigger receiver balance than the tree holds, does not prove (no money is made on the way)
        let mut inflated = ctrace.clone(); { let mut a = inflated.touches[2].old.unwrap(); a.bal += 1; inflated.touches[2].old = Some(a); }
        assert!(w.attempt(&claim, &creq, &inflated, 20, root0, &anyone).is_none(), "the vault's balance is what the tree says");
        let mut rich = ctrace.clone(); { let mut a = rich.touches[1].old.unwrap(); a.bal += 1; rich.touches[1].old = Some(a); }
        assert!(w.attempt(&claim, &creq, &rich, 20, root0, &anyone).is_none(), "the receiver's balance is what the tree says");
        // the sender's nonce is part of what it signs: a signature for the next nonce is another message
        let mut replay = ctrace.clone(); { let mut a = replay.touches[0].old.unwrap(); a.nonce += 1; replay.touches[0].old = Some(a); }
        assert!(w.attempt(&claim, &creq, &replay, 20, root0, &anyone).is_none());
    }
    fn felts_to_hash(v: &[u64; 4]) -> HashOut<F> { HashOut { elements: v.map(F::from_canonical_u64) } }
}
