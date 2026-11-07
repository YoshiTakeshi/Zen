// Blows and tickets (Proof of Minting), Rust port of the Go devnet's blow.go, with ONE KEY PER PERSON:
// the minter signs its blows with the same EcGFp5 Schnorr key that signs its payments, so its address
// (Poseidon hash of the public key) is both its account and its minting identity. Handing the key to
// a pool would hand over the account's money, so minting stays personal.
//
//   msg   = Poseidon(BLOW_TAG, chain id, prev (8 x u32), nonce lo, nonce hi)       (4 field elements)
//   sig   = (e, s): R = r*G with r derived from (key, msg), e = 128 bits of Poseidon(R, A, msg),
//           s = r + e*k mod n                          (the payment scheme, in its compact (e, s) form)
//   blow  = Argon2id(prev || A || nonce || e || s; salt "Zen-blow-v1" || prev; 64 MB, 1 pass, 1 lane)
//   win   : blow, read as a 256-bit big-endian number, < 2^256 / difficulty
//
// Domain separation: a payment message is Poseidon(chain id 1..3, ...), a blow message starts with
// BLOW_TAG, so one can never be taken for the other; the chain id stops a blow on Jen counting on Ken.
// A ticket carries the compressed public key (41 B), so a node checks it without any state:
// 41 (A) + 8 (nonce) + 16 (e) + 40 (s) = 105 bytes. A minter may sign the same nonce twice (the
// verifier cannot enforce determinism), but each signature costs its own Argon2id run, so that is just
// another attempt; a block counts at most one ticket per (minter address, nonce).
use crate::ec::{self, E, P};
use anyhow::{anyhow, bail, Result};
use num_bigint::BigUint;
use plonky2::field::types::{Field, Field64, PrimeField64};
use plonky2::field::goldilocks_field::GoldilocksField as F;
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::plonk::config::Hasher;
use sha2::{Digest, Sha256};

/// "ZenBlow" as a field constant: the first element of every blow message
pub const BLOW_TAG: u64 = 0x5A_65_6E_42_6C_6F_77;
pub const SALT: &[u8] = b"Zen-blow-v1";
pub const MEM_KIB: u32 = 64 * 1024;
pub const PASSES: u32 = 1;
pub const TICKET_BYTES: usize = 41 + 8 + 16 + 40;
/// difficulty retarget aims at this many winning blows per block. It is also the most credits a block
/// spends on minters, however many minters there are: more minters only raise the difficulty.
pub const TARGET_BLOWS: u64 = 24;

#[derive(Clone)]
pub struct Key { k: BigUint, pub a: P, pub addr: [F; 4] }
impl Key {
    /// the secret as four 64-bit limbs (what the wallet code signs with)
    pub fn secret_limbs(&self) -> [u64; 4] { let d = self.k.to_u64_digits(); assert!(d.len() <= 4, "secret too long"); let mut o = [0u64; 4]; o[..d.len()].copy_from_slice(&d); o }
    pub fn from_secret(k: BigUint) -> Self { let a = ec::mul_g(&ec::params(), &k); Key { k, a, addr: ec::pk_hash(a) } }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Ticket { pub a: [u8; 41], pub nonce: u64, pub e: u128, pub s: [u8; 40] }

// ------------------------------------------------------------------ points: 41-byte compression
fn ext_sign(y: E) -> u8 { y.0.iter().map(|c| c.to_canonical_u64()).find(|c| *c != 0).map_or(0, |c| (c & 1) as u8) }
pub fn encode_point(p: P) -> [u8; 41] {
    let mut o = [0u8; 41];
    for i in 0..5 { o[8 * i..8 * i + 8].copy_from_slice(&p.x.0[i].to_canonical_u64().to_le_bytes()); }
    o[40] = ext_sign(p.y);
    o
}
/// decode, and require a point of the prime-order group (n*A = O, checked as (n-1)*A = -A)
pub fn decode_point(b: &[u8; 41]) -> Result<P> {
    let mut c = [F::ZERO; 5];
    for i in 0..5 {
        let w = u64::from_le_bytes(b[8 * i..8 * i + 8].try_into().unwrap());
        if w >= F::ORDER { bail!("non-canonical point"); }
        c[i] = F::from_canonical_u64(w);
    }
    if b[40] > 1 { bail!("bad sign byte"); }
    let x = ec::e(c.map(|v| v.to_canonical_u64()));
    let mut p = ec::lift(x).ok_or_else(|| anyhow!("not on the curve"))?;
    if ext_sign(p.y) != b[40] { p = ec::neg(p); }
    if p.y == E::ZERO { bail!("point of order 2"); }
    let nm1 = ec::n_order() - BigUint::from(1u32);
    if ec::mul(p, &nm1) != ec::neg(p) { bail!("point outside the prime-order group"); }
    Ok(p)
}

// ------------------------------------------------------------------ messages and signatures
pub fn blow_msg(chain: u64, prev: &[u8; 32], nonce: u64) -> [F; 4] {
    let mut v = vec![F::from_canonical_u64(BLOW_TAG), F::from_canonical_u64(chain)];
    for i in 0..8 { v.push(F::from_canonical_u32(u32::from_le_bytes(prev[4 * i..4 * i + 4].try_into().unwrap()))); }
    v.push(F::from_canonical_u32(nonce as u32)); v.push(F::from_canonical_u32((nonce >> 32) as u32));
    PoseidonHash::hash_no_pad(&v).elements
}
fn msg_bytes(m: &[F; 4]) -> Vec<u8> { m.iter().flat_map(|x| x.to_canonical_u64().to_le_bytes()).collect() }
pub fn s_bytes(s: &BigUint) -> [u8; 40] { let mut o = [0u8; 40]; let b = s.to_bytes_le(); o[..b.len()].copy_from_slice(&b); o }

/// deterministic Schnorr: r from SHA-256(key, msg) (512 bits, reduced mod n), so a phone never needs
/// a good random source and never reuses r for two messages
pub fn sign(key: &Key, msg: [F; 4]) -> (u128, BigUint) {
    let prm = ec::params();
    let kb = key.k.to_bytes_le();
    let mut wide = vec![];
    for ctr in 0u8..2 {
        let mut h = Sha256::new();
        h.update(b"Zen-sig-r"); h.update([ctr]); h.update(&kb); h.update(msg_bytes(&msg));
        wide.extend(h.finalize());
    }
    let r = BigUint::from_bytes_le(&wide) % ec::n_order();
    let rp = ec::mul_g(&prm, &r);
    let e = ec::challenge(rp, key.a, msg);
    let s = (&r + &e * &key.k) % ec::n_order();
    (u128::try_from(&e).unwrap(), s)
}
/// R = s*G - e*A, then e must be the challenge of (R, A, msg)
pub fn verify(a: P, msg: [F; 4], e: u128, s: &BigUint) -> bool {
    let n = ec::n_order();
    if *s >= n || *s == BigUint::ZERO || e == 0 { return false; }
    let prm = ec::params();
    let sg = ec::mul_g(&prm, s);
    let ea = ec::mul(a, &BigUint::from(e));
    if sg.x == ea.x { return false; }                         // R would be O, or doubling: reject
    let r = ec::add(sg, ec::neg(ea));
    ec::challenge(r, a, msg) == BigUint::from(e)
}

// ------------------------------------------------------------------ blows and tickets
pub fn make_ticket(key: &Key, chain: u64, prev: &[u8; 32], nonce: u64) -> Ticket {
    let (e, s) = sign(key, blow_msg(chain, prev, nonce));
    Ticket { a: encode_point(key.a), nonce, e, s: s_bytes(&s) }
}
impl Ticket {
    pub fn to_bytes(&self) -> [u8; TICKET_BYTES] {
        let mut o = [0u8; TICKET_BYTES];
        o[..41].copy_from_slice(&self.a); o[41..49].copy_from_slice(&self.nonce.to_le_bytes());
        o[49..65].copy_from_slice(&self.e.to_le_bytes()); o[65..].copy_from_slice(&self.s);
        o
    }
    pub fn from_bytes(b: &[u8]) -> Result<Self> {
        if b.len() != TICKET_BYTES { bail!("ticket length"); }
        Ok(Ticket { a: b[..41].try_into()?, nonce: u64::from_le_bytes(b[41..49].try_into()?), e: u128::from_le_bytes(b[49..65].try_into()?), s: b[65..].try_into()? })
    }
}
/// the memory-hard step (the minter runs it for each attempt; a node once per ticket)
pub fn blow_value(prev: &[u8; 32], t: &Ticket) -> [u8; 32] {
    let mut input = Vec::with_capacity(32 + TICKET_BYTES);
    input.extend_from_slice(prev); input.extend_from_slice(&t.to_bytes());
    let mut salt = SALT.to_vec(); salt.extend_from_slice(prev);
    let params = argon2::Params::new(MEM_KIB, PASSES, 1, Some(32)).unwrap();
    let a2 = argon2::Argon2::new(argon2::Algorithm::Argon2id, argon2::Version::V0x13, params);
    let mut out = [0u8; 32];
    a2.hash_password_into(&input, &salt, &mut out).unwrap();
    out
}
pub fn wins(v: &[u8; 32], difficulty: u64) -> bool {
    let target = (BigUint::from(1u32) << 256u32) / BigUint::from(difficulty.max(1));
    BigUint::from_bytes_be(v) < target
}
/// everything a node checks for a ticket: the key, the signature, the Argon2id work, the difficulty.
/// Returns the minter's address (its account) and the blow value.
pub fn check_ticket(chain: u64, prev: &[u8; 32], t: &Ticket, difficulty: u64) -> Result<([F; 4], [u8; 32])> {
    let a = decode_point(&t.a)?;
    let s = BigUint::from_bytes_le(&t.s);
    if !verify(a, blow_msg(chain, prev, t.nonce), t.e, &s) { bail!("bad blow signature"); }
    let v = blow_value(prev, t);
    if !wins(&v, difficulty) { bail!("blow above the target"); }
    Ok((ec::pk_hash(a), v))
}

// ------------------------------------------------------------------ difficulty and the minting gate
/// toward TARGET_BLOWS winning blows per block: diff x (3T + blows) / 4T, at most +-12.5% per block
pub fn retarget(diff: u64, blows: u64) -> u64 {
    let t = TARGET_BLOWS as u128;
    let mut v = (diff as u128 * (3 * t + blows as u128) / (4 * t)) as u64;
    if blows > TARGET_BLOWS && v == diff { v = diff + 1; }
    let step = (diff / 8).max(1);
    if diff > step && v < diff - step { v = diff - step; }
    if v > diff.saturating_add(step) { v = diff + step; }
    v.max(1)
}
/// the least minting work (sum of the tickets' difficulties) a block needs: a third of the recent
/// average, never less than one blow at the current difficulty
pub fn min_work(work_ema: u64, diff: u64) -> u64 { (work_ema / 3).max(diff) }
pub fn next_work_ema(ema: u64, work: u64) -> u64 { (ema as i128 + (work as i128 - ema as i128) / 32) as u64 }

#[cfg(test)]
mod tests {
    use super::*;
    fn key(seed: u64) -> Key { Key::from_secret(BigUint::from(seed) * BigUint::from(0x9E3779B97F4A7C15u64) + BigUint::from(12345u32)) }
    #[test]
    fn point_roundtrip_and_subgroup() {
        let k = key(1);
        assert_eq!(decode_point(&encode_point(k.a)).unwrap(), k.a);
        assert_eq!(decode_point(&encode_point(ec::neg(k.a))).unwrap(), ec::neg(k.a));
        // A + T, T = (0, 0) the point of order 2: on the curve, outside the prime-order group
        let t = P { x: E::ZERO, y: E::ZERO };
        let bad = ec::add(k.a, t);
        assert!(ec::on_curve(bad));
        assert!(decode_point(&encode_point(bad)).is_err());
    }
    #[test]
    fn signatures() {
        let (k, k2) = (key(2), key(3));
        let prev = [7u8; 32];
        let m = blow_msg(3, &prev, 42);
        let (e, s) = sign(&k, m);
        assert!(verify(k.a, m, e, &s));
        assert_eq!(sign(&k, m), (e, s.clone()), "deterministic");
        assert!(!verify(k2.a, m, e, &s), "other key");
        assert!(!verify(k.a, blow_msg(3, &prev, 43), e, &s), "other nonce");
        assert!(!verify(k.a, blow_msg(2, &prev, 42), e, &s), "other chain");
        assert!(!verify(k.a, m, e ^ 1, &s), "other e");
    }
    #[test]
    fn retarget_rule() {
        assert_eq!(retarget(1000, TARGET_BLOWS), 1000);
        assert_eq!(retarget(1000, 10 * TARGET_BLOWS), 1125);
        assert_eq!(retarget(1000, 0), 875);
        assert_eq!(retarget(1, 0), 1);
    }
}
