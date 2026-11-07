// Block data, version 4: what a block carries besides the proof, and the check every node runs.
//
// Version 4 adds CREDIT slots: payouts applied inside the proof (the leaf provers' fee shares, the
// miner's cut, fee-pool payouts, block rewards). A credit slot has no sender and no signature; it adds
// an amount to an account (created on first receipt, like a payment to a new address). Nodes compute
// the exact payout list from consensus rules (`expected_credits`) and a block is valid only if its
// credit slots, in order, are exactly that list. The proof makes sure each one was applied to the tree.
//
// The stamp commits to the block: each state leaf hashes its slot entries
//   [applied payment, sender index, receiver index, amount, fee, new, close, credit, receiver address x4 if new]
// (12 field elements per slot, all zero on a padding or skipped slot) followed by the leaf's prover
// address (4 elements); the universal merge hashes two child hashes and passes a lone hash through.
//
// Byte format (version 4, little endian):
//   u8 version | u16 slots per leaf | u16 leaves
//   per leaf: u16 payment mask | u16 credit mask | u16 new-account mask | u16 close mask | 32 B prover
//   then, leaf by leaf, slot by slot:
//     payment: u32 sender | u32 receiver | varint amount | varint fee | 32 B receiver address if new
//     credit:  u32 receiver | varint amount | 32 B receiver address if new
//
// A node keeps the previous state and replays the bytes with the circuit's rules, given the block's
// public values S (base units per coin) and height and the payout inputs, then compares (root before,
// root after, fee total, count, data hash, S, height) with the stamp's public values.
use crate::{empty_leaf, leaf_hash, Acct, Tree, F};
use anyhow::{anyhow, bail, Result};
use plonky2::field::types::{Field, Field64, PrimeField64};
use plonky2::hash::hash_types::HashOut;
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::plonk::config::Hasher;
use std::collections::HashMap;

pub const VERSION: u8 = 4;
pub const NONCE_SHIFT: u32 = 20;
pub const ENTRY: usize = 12;
/// fee split (Go Jen-0.10 rule, SPEC 4.6, 75/25 still Open): half of each leaf's fees into the fee pool,
/// 75% of the rest to the leaf's prover, the remainder to the miner; the pool pays 1/32 of what it held
/// per block, 75% shared equally by the block's leaves' provers, the rest to the miner
pub const POOL_PCT: u64 = 50;
pub const PROVER_PCT: u64 = 75;
pub const POOL_DIV: u64 = 32;

// ---------------------------------------------------------------- each gram counts once (SPEC 6.6)
// Per account: rest (rested balance), used (rested money already counted in period `up`), fd (day of the
// last receipt), rd (day the rested money counts from). The part of the balance above `rest` is fresh.
// Every send and receive first SETTLES the account at the block's day d and period p:
//   - fresh money matures into rest when d >= fd + REST_DAYS (then rd = fd: the aged-from day);
//   - used starts again from 0 in a new period.
// A payment spends fresh money first, then rested. It COUNTS min(amount, rest - used) of rested money
// (`used` grows by that; rested money that leaves the account is the used money first). A receipt adds fresh money and sets fd = d,
// so money paid around in a loop counts once per rest period. The circuit applies the same rules.
pub const BPD: u64 = 576;          // blocks per day (Jen: 150 s)
pub const REST_DAYS: u64 = 3;
pub const AGE_CAP_DAYS: u64 = 30;
pub fn day_period(height: u64) -> (u64, u64) { let d = height / BPD; (d, d / REST_DAYS) }
/// what one payment contributed: the amount that counts and how many days its money has aged
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Counted { pub amt: u64, pub age: u64 }
pub fn settle(a: &mut Acct, d: u64, p: u64) {
    if a.bal > a.rest && d >= a.fd + REST_DAYS { a.rest = a.bal; a.rd = a.fd; }
    if a.up != p { a.used = 0; a.up = p; }
}
/// the sender's side of a payment (amount and fee leave the balance); returns what counts toward S
pub fn pay_from(a: &mut Acct, amt: u64, fee: u64, d: u64, p: u64) -> Counted {
    settle(a, d, p);
    let spend = amt + fee;
    let fresh = a.bal - a.rest;
    let from_fresh = spend.min(fresh);
    let from_rest = spend - from_fresh;
    let c = amt.min(a.rest - a.used);
    let age = d - a.rd;
    a.rest -= from_rest;
    a.used = (a.used + c).saturating_sub(from_rest);   // rested money that leaves is the counted money first
    a.bal -= spend; a.nonce += 1;
    Counted { amt: c, age }
}
/// the receiver's side: fresh money arrives today
pub fn receive_to(a: &mut Acct, amt: u64, d: u64, p: u64) {
    settle(a, d, p);
    a.bal += amt; a.fd = d;
}
/// coin-days weight of a counted payment: value x min(age, 30) / 30
pub fn weight(c: &Counted) -> u64 { ((c.amt as u128) * (c.age.min(AGE_CAP_DAYS) as u128) / AGE_CAP_DAYS as u128) as u64 }

#[derive(Clone, Copy, Debug)]
pub struct BlockEntry { pub slot: u8, pub credit: bool, pub s_idx: u32, pub r_idx: u32, pub amt: u64, pub fee: u64, pub new_r: Option<[F; 4]>, pub close: bool }
#[derive(Clone, Debug, Default)]
pub struct LeafData { pub prover: [F; 4], pub pays: Vec<BlockEntry> }

/// what nodes know before the block about who is owed what
#[derive(Clone, Debug)]
pub struct PayoutRule { pub miner: [F; 4], pub pool_before: u64, pub rewards: Vec<([F; 4], u64)> }

/// The payout list of a block, in canonical order (first appearance), one credit per address:
/// rewards owed from earlier blocks, then each leaf's prover share, the miner's cut and the pool payout.
/// Leaves with no applied payment (credit-only leaves) take no share. Zero amounts are dropped.
pub fn expected_credits(leaf_fees: &[([F; 4], u64)], rule: &PayoutRule) -> (Vec<([F; 4], u64)>, u64) {
    let mut out: Vec<([F; 4], u64)> = vec![];
    let mut add = |a: [F; 4], v: u64| { if v == 0 { return; } match out.iter_mut().find(|(x, _)| *x == a) { Some(e) => e.1 += v, None => out.push((a, v)) } };
    for (a, v) in &rule.rewards { add(*a, *v); }
    let (mut fees, mut to_pool, mut shares) = (0u64, 0u64, 0u64);
    let paying: Vec<&([F; 4], u64)> = leaf_fees.iter().filter(|(_, f)| *f > 0).collect();
    for (p, f) in &paying {
        let tp = f * POOL_PCT / 100;
        let share = (f - tp) * PROVER_PCT / 100;
        add(*p, share);
        fees += f; to_pool += tp; shares += share;
    }
    add(rule.miner, fees - to_pool - shares);
    let pay = rule.pool_before / POOL_DIV;
    let mut paid = 0;
    if !paying.is_empty() {
        let each = pay * PROVER_PCT / 100 / paying.len() as u64;
        for (p, _) in &paying { add(*p, each); paid += each; }
    }
    add(rule.miner, pay - paid);
    (out, rule.pool_before - pay + to_pool)
}

fn put_var(v: &mut Vec<u8>, mut x: u64) {
    loop { let b = (x & 0x7f) as u8; x >>= 7; if x == 0 { v.push(b); break; } v.push(b | 0x80); }
}
fn get_var(b: &[u8], pos: &mut usize) -> Result<u64> {
    let (mut x, mut sh) = (0u64, 0u32);
    loop {
        let c = *b.get(*pos).ok_or_else(|| anyhow!("truncated varint"))?; *pos += 1;
        if sh > 63 || (sh == 63 && c > 1) { bail!("varint too long"); }
        x |= ((c & 0x7f) as u64) << sh;
        if c & 0x80 == 0 { if c == 0 && sh > 0 { bail!("non-minimal varint"); } return Ok(x); }
        sh += 7;
    }
}
fn get<const N: usize>(b: &[u8], pos: &mut usize) -> Result<[u8; N]> {
    let s = b.get(*pos..*pos + N).ok_or_else(|| anyhow!("truncated"))?; *pos += N;
    Ok(s.try_into().unwrap())
}
fn put_addr(v: &mut Vec<u8>, a: &[F; 4]) { for x in a { v.extend(x.to_canonical_u64().to_le_bytes()); } }
fn get_addr(b: &[u8], pos: &mut usize) -> Result<[F; 4]> {
    let mut a = [F::ZERO; 4];
    for x in a.iter_mut() {
        let w = u64::from_le_bytes(get::<8>(b, pos)?);
        if w >= F::ORDER { bail!("non-canonical address"); }
        *x = F::from_canonical_u64(w);
    }
    Ok(a)
}

pub fn encode(slots: usize, block: &[LeafData]) -> Vec<u8> {
    let mut v = vec![VERSION];
    v.extend((slots as u16).to_le_bytes());
    v.extend((block.len() as u16).to_le_bytes());
    for l in block {
        let (mut pm, mut cm, mut nm, mut xm) = (0u16, 0u16, 0u16, 0u16);
        for e in &l.pays {
            if e.credit { cm |= 1 << e.slot } else { pm |= 1 << e.slot }
            if e.new_r.is_some() { nm |= 1 << e.slot; }
            if e.close { xm |= 1 << e.slot; }
        }
        for m in [pm, cm, nm, xm] { v.extend(m.to_le_bytes()); }
        put_addr(&mut v, &l.prover);
    }
    for l in block {
        for e in &l.pays {
            if !e.credit { v.extend(e.s_idx.to_le_bytes()); }
            v.extend(e.r_idx.to_le_bytes()); put_var(&mut v, e.amt);
            if !e.credit { put_var(&mut v, e.fee); }
            if let Some(a) = &e.new_r { put_addr(&mut v, a); }
        }
    }
    v
}

pub fn decode(b: &[u8]) -> Result<(usize, Vec<LeafData>)> {
    let (slots, block, used) = decode_prefix(b)?;
    if used != b.len() { bail!("trailing bytes"); }
    Ok((slots, block))
}
/// the leaves, and how many bytes they took (what follows is the operations trailer, see locks.rs)
pub fn decode_prefix(b: &[u8]) -> Result<(usize, Vec<LeafData>, usize)> {
    let mut pos = 0;
    if get::<1>(b, &mut pos)?[0] != VERSION { bail!("unknown version"); }
    let slots = u16::from_le_bytes(get::<2>(b, &mut pos)?) as usize;
    let leaves = u16::from_le_bytes(get::<2>(b, &mut pos)?) as usize;
    if leaves == 0 || slots > 16 { bail!("bad shape"); }
    let mut heads = vec![];
    for _ in 0..leaves {
        let m: Vec<u16> = (0..4).map(|_| get::<2>(b, &mut pos).map(u16::from_le_bytes)).collect::<Result<_>>()?;
        let (pm, cm, nm, xm) = (m[0], m[1], m[2], m[3]);
        let used = pm | cm;
        if (slots < 16 && (used >> slots) != 0) || pm & cm != 0 || nm & !used != 0 || xm & !pm != 0 || nm & xm != 0 { bail!("bad leaf header"); }
        heads.push((pm, cm, nm, xm, get_addr(b, &mut pos)?));
    }
    let mut block = vec![];
    for (pm, cm, nm, xm, prover) in heads {
        let mut pays = vec![];
        for i in (0..16u8).filter(|i| (pm | cm) >> i & 1 == 1) {
            let credit = cm >> i & 1 == 1;
            let s_idx = if credit { 0 } else { u32::from_le_bytes(get::<4>(b, &mut pos)?) };
            let r_idx = u32::from_le_bytes(get::<4>(b, &mut pos)?);
            let amt = get_var(b, &mut pos)?;
            let fee = if credit { 0 } else { get_var(b, &mut pos)? };
            let new_r = if nm >> i & 1 == 1 { Some(get_addr(b, &mut pos)?) } else { None };
            pays.push(BlockEntry { slot: i, credit, s_idx, r_idx, amt, fee, new_r, close: xm >> i & 1 == 1 });
        }
        block.push(LeafData { prover, pays });
    }
    Ok((slots, block, pos))
}

/// slot entries of one leaf, as the state leaf hashes them
pub fn leaf_data_hash(slots: usize, l: &LeafData) -> HashOut<F> {
    let mut v = vec![F::ZERO; ENTRY * slots];
    for e in &l.pays {
        let a = e.new_r.unwrap_or([F::ZERO; 4]);
        let c = |x: u64| F::from_canonical_u64(x);
        let mut x = vec![F::from_bool(!e.credit), c(e.s_idx as u64), c(e.r_idx as u64), c(e.amt), c(e.fee),
                         F::from_bool(e.new_r.is_some()), F::from_bool(e.close), F::from_bool(e.credit)];
        x.extend(a);
        let o = ENTRY * e.slot as usize; v[o..o + ENTRY].copy_from_slice(&x);
    }
    v.extend(l.prover);
    PoseidonHash::hash_no_pad(&v)
}
/// the universal merge's data combination: pairs are hashed, a lone child passes through
pub fn combine(mut hs: Vec<HashOut<F>>) -> HashOut<F> {
    while hs.len() > 1 {
        hs = hs.chunks(2).map(|p| if p.len() == 2 { let mut v = p[0].elements.to_vec(); v.extend(p[1].elements); PoseidonHash::hash_no_pad(&v) } else { p[0] }).collect();
    }
    hs[0]
}

pub struct Replayed { pub root0: HashOut<F>, pub root: HashOut<F>, pub fee: u64, pub count: u64, pub data: HashOut<F>, pub s: u64, pub height: u64, pub credits: Vec<([F; 4], u64)>, pub pool_after: u64, pub counted: Vec<Counted>, pub reads: Vec<crate::reading::Observed>, pub state: HashMap<u64, Acct>, pub tree: Tree, pub locks: crate::locks::LockTable }
impl Replayed {
    /// same layout as the stamp's 16 public values
    pub fn public_inputs(&self) -> Vec<u64> {
        let mut v: Vec<u64> = self.root0.elements.iter().map(|x| x.to_canonical_u64()).collect();
        v.extend(self.root.elements.iter().map(|x| x.to_canonical_u64()));
        v.push(self.fee); v.push(self.count);
        v.extend(self.data.elements.iter().map(|x| x.to_canonical_u64()));
        v.push(self.s); v.push(self.height);
        v
    }
}

/// credit an account (a new one must take an empty index, and its address may not already own one)
pub(crate) fn credit_to(state: &mut HashMap<u64, Acct>, tree: &mut Tree, ri: u64, new_r: Option<[F; 4]>, amt: u64, height: u64, tmpl: Acct) -> Result<[F; 4]> {
    let (d, p) = day_period(height);
    let mut ra = match new_r {
        Some(addr) => {
            if state.contains_key(&ri) { bail!("new account in a used slot"); }
            if state.values().any(|a| a.pk == addr) { bail!("new account for an address that has one"); }
            Acct::blank(addr, height << NONCE_SHIFT, &tmpl)
        }
        None => *state.get(&ri).ok_or_else(|| anyhow!("unknown receiver {ri}"))?,
    };
    if ra.bal.checked_add(amt).is_none_or(|b| b >= 1 << 62) { bail!("receiver balance overflow"); }
    receive_to(&mut ra, amt, d, p);
    state.insert(ri, ra); tree.set(ri, leaf_hash(&ra));
    Ok(ra.pk)
}

/// Rebuild the new state from the previous one and the block bytes, with the circuit's rules, and
/// check that the block's credits are exactly the payouts the consensus rules owe.
pub fn replay(prev: &HashMap<u64, Acct>, prev_tree: &Tree, s: u64, height: u64, rule: &PayoutRule, bytes: &[u8]) -> Result<Replayed> {
    let ctx = crate::locks::Ctx { chain: 3, ntime: 0, cross: &crate::locks::CrossMode::Off };
    replay_ctx(prev, prev_tree, &Default::default(), s, height, rule, bytes, &ctx)
}
/// the same with locks: payments and credits may not touch a lock; the operations run after the leaves
pub fn replay_ctx(prev: &HashMap<u64, Acct>, prev_tree: &Tree, locks0: &crate::locks::LockTable, s: u64, height: u64, rule: &PayoutRule, bytes: &[u8], ctx: &crate::locks::Ctx) -> Result<Replayed> {
    let (slots, block, used) = decode_prefix(bytes)?;
    let ops = crate::locks::decode_ops(&bytes[used..])?;
    let mut locks = locks0.clone();
    let mut state = prev.clone();
    let mut tree = prev_tree.clone();
    let root0 = tree.root();
    let tmpl = *prev.values().next().ok_or_else(|| anyhow!("empty state"))?;
    let (mut fee_total, mut count) = (0u64, 0u64);
    let mut hashes = vec![];
    let mut leaf_fees = vec![];
    let mut credits = vec![];
    let mut counted = vec![];
    let mut reads = vec![];
    for l in &block {
        let mut leaf_fee = 0u64;
        for e in &l.pays {
            if e.amt >= 1 << 62 || e.fee >= 1 << 62 { bail!("amount or fee out of range"); }
            if e.credit {
                if e.new_r.is_none() && locks.contains_key(&(e.r_idx as u64)) { bail!("a payout cannot go into a lock"); }
                credits.push((credit_to(&mut state, &mut tree, e.r_idx as u64, e.new_r, e.amt, height, tmpl)?, e.amt));
                continue;
            }
            let (si, ri) = (e.s_idx as u64, e.r_idx as u64);
            if si == ri { bail!("payment to its own index"); }
            if locks.contains_key(&si) || (e.new_r.is_none() && locks.contains_key(&ri)) { bail!("a payment cannot go from or into a lock"); }
            if (e.amt as u128) * 6 < s as u128 { bail!("below the smallest payment"); }
            if (e.fee as u128) * 100 < s as u128 { bail!("below the smallest fee"); }
            let spend = e.amt + e.fee;
            if e.fee as u128 * 10_000 < spend as u128 { bail!("fee below 0.01%"); }
            if e.fee as u128 * 100 > 6 * spend as u128 { bail!("fee above 6%"); }
            let mut sa = *state.get(&si).ok_or_else(|| anyhow!("unknown sender {si}"))?;
            if sa.bal < spend { bail!("balance too low"); }
            let (d, p) = day_period(height);
            let cn = pay_from(&mut sa, e.amt, e.fee, d, p);
            counted.push(cn);
            reads.push(crate::reading::Observed { c: cn, pay: e.amt, fee: e.fee, to: ri });
            if e.close {
                if sa.bal != 0 { bail!("close leaves a balance"); }
                state.remove(&si); tree.set(si, empty_leaf());
            } else { state.insert(si, sa); tree.set(si, leaf_hash(&sa)); }
            credit_to(&mut state, &mut tree, ri, e.new_r, e.amt, height, tmpl)?;
            fee_total += e.fee; leaf_fee += e.fee; count += 1;
        }
        hashes.push(leaf_data_hash(slots, l));
        leaf_fees.push((l.prover, leaf_fee));
    }
    let (want, mut pool_after) = expected_credits(&leaf_fees, rule);
    if credits != want { bail!("credits differ from the payouts owed ({} given, {} owed)", credits.len(), want.len()); }
    // operations (locks and orders): what they pay in fees goes to the fee pool
    if !ops.is_empty() {
        pool_after += crate::locks::apply_ops(&ops, &mut state, &mut tree, &mut locks, s, height, ctx, tmpl)?;
        // each operation is part of the proof's public values: its fee, one in the count, and (when the proof carries its kind) a data hash after the leaves'
        for op in &ops {
            fee_total += op.fee(); count += 1;
            if let Some(h) = crate::locks::proved_data_hash(op, ctx.ntime) { hashes.push(HashOut { elements: h }); }
        }
    }
    let root = tree.root();
    Ok(Replayed { root0, root, fee: fee_total, count, data: combine(hashes), s, height, credits, pool_after, counted, reads, state, tree, locks })
}

#[cfg(test)]
mod peg_tests {
    use super::*;
    fn acct(bal: u64, rested: bool) -> Acct {
        let prm = crate::ec::params();
        let a = crate::ec::mul_g(&prm, &num_bigint::BigUint::from(5u32));
        Acct { pk: crate::ec::pk_hash(a), bal, nonce: 0, rest: if rested { bal } else { 0 }, used: 0, fd: 0, rd: 0, up: 0, a, k: [5; 4] }
    }
    #[test]
    fn loop_counts_once_per_rest_period() {
        let (mut a, mut b) = (acct(100, true), acct(0, false));
        let (d, p) = (10, 10 / REST_DAYS);
        let c = pay_from(&mut a, 100, 0, d, p); receive_to(&mut b, 100, d, p);
        assert_eq!(c.amt, 100);
        // b's money is fresh: it moves on at once and counts nothing
        let c = pay_from(&mut b, 100, 0, d, p);
        assert_eq!(c.amt, 0);
        // paid back and forth within the rest period: nothing counts
        let (mut a2, mut b2) = (acct(0, false), acct(100, true));
        receive_to(&mut a2, 100, d, p);
        assert_eq!(pay_from(&mut a2, 100, 0, d + 1, (d + 1) / REST_DAYS).amt, 0);
        // after the rest period the same money counts again
        let (mut x, mut y) = (acct(0, false), acct(0, false));
        receive_to(&mut x, 100, 10, 3);
        let c = pay_from(&mut x, 100, 0, 13, 4); receive_to(&mut y, 100, 13, 4);
        assert_eq!(c.amt, 100); assert_eq!(c.age, 3);
        assert_eq!(b2.bal, 100); b2.bal = 0;
    }
    #[test]
    fn rested_money_counts_once_per_period_even_when_fresh_is_spent_first() {
        // 100 rested, 100 fresh: the fresh money is spent first, so the rested money would count twice
        let mut a = acct(100, true);
        receive_to(&mut a, 100, 10, 3);
        assert_eq!(pay_from(&mut a, 100, 0, 10, 3).amt, 100);
        assert_eq!((a.rest, a.used, a.bal), (100, 100, 100));
        assert_eq!(pay_from(&mut a, 100, 0, 10, 3).amt, 0);
        assert_eq!((a.rest, a.used, a.bal), (0, 0, 0));
        // a new period starts the count again
        let mut b = acct(100, true);
        assert_eq!(pay_from(&mut b, 40, 0, 10, 3).amt, 40);
        assert_eq!(pay_from(&mut b, 40, 0, 10, 3).amt, 40);
        assert_eq!(pay_from(&mut b, 20, 0, 10, 3).amt, 20);
    }
    #[test]
    fn invariants_hold_under_random_use() {
        let mut s = 99u64;
        let mut r = || { s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); s >> 33 };
        let mut a = acct(10_000, true);
        let mut day = 5;
        for _ in 0..5000 {
            day += r() % 2;
            let (d, p) = day_period(day * BPD);
            if r() % 2 == 0 { receive_to(&mut a, r() % 500, d, p); }
            else if a.bal > 0 { let spend = r() % (a.bal + 1); let fee = spend / 100; let amt = spend - fee; let c = pay_from(&mut a, amt, fee, d, p); assert!(c.amt <= amt); }
            assert!(a.rest <= a.bal && a.used <= a.rest, "{:?}", (a.bal, a.rest, a.used));
        }
    }
}
