// Plonky2 config whose Merkle trees use Poseidon over the BN254 scalar field, so that a Groth16
// (gnark, BN254) circuit can verify the proof cheaply. Byte-for-byte the same construction as
// gnark-plonky2-verifier's poseidon/bn254.go (iden3 Poseidon, width 4, 8 full + 56 partial rounds):
//   hash_no_pad: chunks of 9 Goldilocks elements; every 3 elements are packed as
//                e0 + e1*2^64 + e2*2^128 and written over state[1..4]; then permute; output state[0]
//   hash_or_noop: <= 3 elements are packed directly, otherwise hash_no_pad
//   two_to_one:  permute([0, 0, left, right])[0]
//   to_vec:      the 254-bit value cut into 56-bit Goldilocks elements (5 of them)
// The Fiat-Shamir challenger and the public-input hash stay Poseidon over Goldilocks.
use crate::bn_consts;
use ark_bn254::Fr;
use ark_ff::{AdditiveGroup, BigInteger, PrimeField};
use num_bigint::BigUint;
use plonky2::field::extension::quadratic::QuadraticExtension;
use plonky2::field::goldilocks_field::GoldilocksField;
use plonky2::field::types::{Field, PrimeField64};
use plonky2::hash::poseidon::{PoseidonHash, PoseidonPermutation};
use plonky2::plonk::config::{GenericConfig, GenericHashOut, Hasher};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::str::FromStr;
use std::sync::OnceLock;

type F = GoldilocksField;

struct K { c: Vec<Fr>, s: Vec<Fr>, m: [[Fr; 4]; 4], p: [[Fr; 4]; 4] }
fn k() -> &'static K {
    static KS: OnceLock<K> = OnceLock::new();
    KS.get_or_init(|| {
        let f = |s: &str| Fr::from_str(s).ok().expect("const");
        K {
            c: bn_consts::C.iter().map(|s| f(s)).collect(),
            s: bn_consts::S.iter().map(|s| f(s)).collect(),
            m: bn_consts::M.map(|r| r.map(|s| f(s))),
            p: bn_consts::P.map(|r| r.map(|s| f(s))),
        }
    })
}
const W: usize = 4;
const FULL: usize = 8;
const PARTIAL: usize = 56;
fn exp5(x: Fr) -> Fr { let x2 = x * x; x2 * x2 * x }
fn ark(s: [Fr; 4], it: usize) -> [Fr; 4] { let c = &k().c; core::array::from_fn(|i| s[i] + c[it + i]) }
fn mix(s: [Fr; 4], m: &[[Fr; 4]; 4]) -> [Fr; 4] {
    core::array::from_fn(|i| { let mut r = Fr::from(0u64); for j in 0..W { r += m[j][i] * s[j]; } r })
}
fn full(mut s: [Fr; 4], first: bool) -> [Fr; 4] {
    for i in 0..FULL / 2 - 1 {
        s = s.map(exp5);
        s = if first { ark(s, (i + 1) * W) } else { ark(s, (FULL / 2 + 1) * W + PARTIAL + i * W) };
        s = mix(s, &k().m);
    }
    s = s.map(exp5);
    if first { s = ark(s, (FULL / 2) * W); mix(s, &k().p) } else { mix(s, &k().m) }
}
fn partial(mut s: [Fr; 4]) -> [Fr; 4] {
    let (c, sc) = (&k().c, &k().s);
    for i in 0..PARTIAL {
        s[0] = exp5(s[0]) + c[(FULL / 2 + 1) * W + i];
        let mut n0 = Fr::from(0u64);
        for j in 0..W { n0 += sc[(W * 2 - 1) * i + j] * s[j]; }
        for kk in 1..W { s[kk] += s[0] * sc[(W * 2 - 1) * i + W + kk - 1]; }
        s[0] = n0;
    }
    s
}
pub fn permute(s: [Fr; 4]) -> [Fr; 4] { let s = ark(s, 0); let s = full(s, true); let s = partial(s); full(s, false) }

/// e0 + e1*2^64 + e2*2^128 (< 2^192 < BN254 modulus, so no reduction)
fn pack(chunk: &[F]) -> Fr {
    let mut l = [0u64; 4];
    for (i, e) in chunk.iter().enumerate() { l[i] = e.to_canonical_u64(); }
    Fr::from_bigint(ark_ff::BigInt::new(l)).expect("< modulus")
}
fn to_big(x: &Fr) -> BigUint { BigUint::from_bytes_le(&x.into_bigint().to_bytes_le()) }

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BnHash(pub Fr);
impl Serialize for BnHash {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> { s.serialize_str(&to_big(&self.0).to_string()) }
}
impl<'de> Deserialize<'de> for BnHash {
    fn deserialize<De: Deserializer<'de>>(d: De) -> Result<Self, De::Error> {
        let s = String::deserialize(d)?;
        Fr::from_str(&s).map(BnHash).map_err(|_| serde::de::Error::custom("bad BN254 element"))
    }
}
impl GenericHashOut<F> for BnHash {
    fn to_bytes(&self) -> Vec<u8> { let mut b = self.0.into_bigint().to_bytes_le(); b.resize(32, 0); b }
    fn from_bytes(bytes: &[u8]) -> Self { BnHash(Fr::from_le_bytes_mod_order(bytes)) }
    fn to_vec(&self) -> Vec<F> {
        // 56-bit chunks of the canonical value, least significant first (as gnark's ToVec)
        let l = self.0.into_bigint().0;
        (0..5).map(|i| {
            let off = 56 * i; let (w, sh) = (off / 64, off % 64);
            let mut v = l[w] >> sh;
            if sh > 8 && w + 1 < 4 { v |= l[w + 1] << (64 - sh); }
            F::from_canonical_u64(v & ((1u64 << 56) - 1))
        }).collect()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoseidonBn254Hash;
impl Hasher<F> for PoseidonBn254Hash {
    const HASH_SIZE: usize = 32;
    type Hash = BnHash;
    type Permutation = PoseidonPermutation<F>;
    fn hash_no_pad(input: &[F]) -> BnHash {
        let mut s = [Fr::ZERO; 4];
        for chunk in input.chunks(9) {
            for (idx, c3) in chunk.chunks(3).enumerate() { s[idx + 1] = pack(c3); }
            s = permute(s);
        }
        BnHash(s[0])
    }
    fn hash_or_noop(inputs: &[F]) -> BnHash { if inputs.len() <= 3 { BnHash(pack(inputs)) } else { Self::hash_no_pad(inputs) } }
    fn two_to_one(l: BnHash, r: BnHash) -> BnHash { BnHash(permute([Fr::from(0u64), Fr::from(0u64), l.0, r.0])[0]) }
}

#[derive(Debug, Copy, Clone, Default, Eq, PartialEq, Serialize)]
pub struct PoseidonBn254GoldilocksConfig;
impl GenericConfig<2> for PoseidonBn254GoldilocksConfig {
    type F = GoldilocksField;
    type FE = QuadraticExtension<Self::F>;
    type Hasher = PoseidonBn254Hash;
    type InnerHasher = PoseidonHash;
}

#[cfg(test)]
mod tests {
    use super::*;
    // the fast pack/to_vec must agree with the straightforward big-integer versions
    #[test]
    fn pack_and_to_vec_match_bigint() {
        let mut x = 0x9E3779B97F4A7C15u64;
        for _ in 0..1000 {
            let e: Vec<F> = (0..3).map(|_| { x = x.wrapping_mul(6364136223846793005).wrapping_add(1); F::from_noncanonical_u64(x) }).collect();
            let mut v = BigUint::from(0u32);
            for (i, a) in e.iter().enumerate() { v += BigUint::from(a.to_canonical_u64()) << (64 * i); }
            assert_eq!(pack(&e), Fr::from_le_bytes_mod_order(&v.to_bytes_le()));
            let h = PoseidonBn254Hash::hash_no_pad(&e);
            let big = to_big(&h.0);
            let mask = (BigUint::from(1u32) << 56) - BigUint::from(1u32);
            let slow: Vec<F> = (0..5).map(|i| { let c: BigUint = (&big >> (56 * i)) & &mask; F::from_canonical_u64(c.iter_u64_digits().next().unwrap_or(0)) }).collect();
            assert_eq!(h.to_vec(), slow);
        }
    }
}
#[cfg(test)]
mod bench {
    use super::*;
    #[test]
    fn permute_speed() {
        let mut s = [Fr::from(1u64), Fr::from(2u64), Fr::from(3u64), Fr::from(4u64)];
        let t = std::time::Instant::now();
        for _ in 0..100_000 { s = permute(s); }
        println!("PERMUTE {:.2} us each ({:?})", t.elapsed().as_secs_f64() * 10.0, s[0].into_bigint().0[0] & 1);
    }
}
#[cfg(test)]
mod bench2 {
    use super::*;
    #[test]
    fn mul_speed() {
        let mut a = Fr::from(3u64); let b = Fr::from(123456789u64);
        let t = std::time::Instant::now();
        for _ in 0..10_000_000 { a *= b; }
        println!("FRMUL {:.1} ns ({})", t.elapsed().as_secs_f64() * 100.0, a.into_bigint().0[0] & 1);
        let t = std::time::Instant::now();
        for _ in 0..1_000_000 { let _ = std::hint::black_box(k()); }
        println!("KCALL {:.1} ns", t.elapsed().as_secs_f64() * 1000.0);
    }
}
