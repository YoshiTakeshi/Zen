// Block data: what a block carries besides the proof, and the check every node runs.
//
// The proof shows that the new state root is correct, but people still need the payments to know
// their balances and to keep building on the tree. So every block publishes its payments (no
// signatures: those were checked inside the proof) and the proof COMMITS to them: each leaf
// circuit hashes its slot entries [enabled, sender index, receiver index, amount, fee] (zeros for
// a padding slot) and the merges hash pairs of those hashes, so the stamp's public inputs end with
// a data hash. A prover cannot publish a valid proof with missing or different data.
//
// Byte format (version 1, little endian):
//   u8 version | u16 slots per leaf | u16 leaves | leaves x u8 payment count
//   then for each payment, leaf by leaf: u32 sender index | u32 receiver index | varint amount | varint fee
// (varint = LEB128, minimal encoding only). Real payments fill the first slots of a leaf (the circuit
// enforces it), so the counts are enough to place them.
//
// A node keeps the previous state (accounts + tree), replays the bytes with the same rules as the
// circuit and compares (root before, root after, fee total, count, data hash) with the proof's
// public inputs.
use crate::{leaf_hash, Acct, Tree, F};
use anyhow::{anyhow, bail, Result};
use plonky2::field::types::{Field, PrimeField64};
use plonky2::hash::hash_types::HashOut;
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::plonk::config::Hasher;
use std::collections::HashMap;

pub const VERSION: u8 = 1;

#[derive(Clone, Copy, Debug)]
pub struct BlockEntry { pub s_idx: u32, pub r_idx: u32, pub amt: u64, pub fee: u64 }

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

pub fn encode(slots: usize, block: &[Vec<BlockEntry>]) -> Vec<u8> {
    let mut v = vec![VERSION];
    v.extend((slots as u16).to_le_bytes());
    v.extend((block.len() as u16).to_le_bytes());
    for l in block { v.push(l.len() as u8); }
    for l in block {
        for e in l { v.extend(e.s_idx.to_le_bytes()); v.extend(e.r_idx.to_le_bytes()); put_var(&mut v, e.amt); put_var(&mut v, e.fee); }
    }
    v
}

pub fn decode(b: &[u8]) -> Result<(usize, Vec<Vec<BlockEntry>>)> {
    let mut pos = 0;
    if get::<1>(b, &mut pos)?[0] != VERSION { bail!("unknown version"); }
    let slots = u16::from_le_bytes(get::<2>(b, &mut pos)?) as usize;
    let leaves = u16::from_le_bytes(get::<2>(b, &mut pos)?) as usize;
    if leaves == 0 || !leaves.is_power_of_two() { bail!("leaves must be a power of two"); }
    let counts: Vec<usize> = (0..leaves).map(|_| get::<1>(b, &mut pos).map(|c| c[0] as usize)).collect::<Result<_>>()?;
    let mut block = vec![];
    for &c in &counts {
        if c > slots { bail!("more payments than slots"); }
        let mut l = vec![];
        for _ in 0..c {
            let s_idx = u32::from_le_bytes(get::<4>(b, &mut pos)?);
            let r_idx = u32::from_le_bytes(get::<4>(b, &mut pos)?);
            let amt = get_var(b, &mut pos)?; let fee = get_var(b, &mut pos)?;
            l.push(BlockEntry { s_idx, r_idx, amt, fee });
        }
        block.push(l);
    }
    if pos != b.len() { bail!("trailing bytes"); }
    Ok((slots, block))
}

pub struct Replayed { pub root0: HashOut<F>, pub root: HashOut<F>, pub fee: u64, pub count: u64, pub data: HashOut<F> }
impl Replayed {
    /// same layout as the stamp's public inputs
    pub fn public_inputs(&self) -> Vec<u64> {
        let mut v: Vec<u64> = self.root0.elements.iter().map(|x| x.to_canonical_u64()).collect();
        v.extend(self.root.elements.iter().map(|x| x.to_canonical_u64()));
        v.push(self.fee); v.push(self.count);
        v.extend(self.data.elements.iter().map(|x| x.to_canonical_u64()));
        v
    }
}

/// Rebuild the new state from the previous one and the block bytes, with the circuit's rules.
pub fn replay(prev_accts: &[Acct], prev_tree: &Tree, prev_idx: &[u64], bytes: &[u8]) -> Result<Replayed> {
    let (slots, block) = decode(bytes)?;
    let mut state: HashMap<u64, Acct> = prev_idx.iter().zip(prev_accts).map(|(i, a)| (*i, *a)).collect();
    let mut tree = prev_tree.clone();
    let root0 = tree.root();
    let (mut fee_total, mut count) = (0u64, 0u64);
    let mut leaf_hashes = vec![];
    for l in &block {
        let mut entries = vec![];
        for e in l {
            let (s, r) = (e.s_idx as u64, e.r_idx as u64);
            if e.amt >= 1 << 62 || e.fee >= 1 << 62 { bail!("amount or fee out of range"); }
            let spend = e.amt + e.fee;
            if e.fee as u128 * 10_000 < spend as u128 { bail!("fee below 0.01%"); }
            if e.fee as u128 * 100 > 6 * spend as u128 { bail!("fee above 6%"); }
            let mut sa = *state.get(&s).ok_or_else(|| anyhow!("unknown sender {s}"))?;
            if sa.bal < spend { bail!("balance too low"); }
            sa.bal -= spend; sa.nonce += 1;
            state.insert(s, sa); tree.set(s, leaf_hash(&sa));
            let mut ra = *state.get(&r).ok_or_else(|| anyhow!("unknown receiver {r}"))?;
            ra.bal = ra.bal.checked_add(e.amt).filter(|b| *b < 1 << 63).ok_or_else(|| anyhow!("receiver balance overflow"))?;
            state.insert(r, ra); tree.set(r, leaf_hash(&ra));
            fee_total += e.fee; count += 1;
            entries.extend([F::ONE, F::from_canonical_u64(s), F::from_canonical_u64(r), F::from_canonical_u64(e.amt), F::from_canonical_u64(e.fee)]);
        }
        entries.resize(5 * slots, F::ZERO);
        leaf_hashes.push(PoseidonHash::hash_no_pad(&entries));
    }
    while leaf_hashes.len() > 1 {
        leaf_hashes = leaf_hashes.chunks(2).map(|p| { let mut v = p[0].elements.to_vec(); v.extend(p[1].elements); PoseidonHash::hash_no_pad(&v) }).collect();
    }
    Ok(Replayed { root0, root: tree.root(), fee: fee_total, count, data: leaf_hashes[0] })
}
