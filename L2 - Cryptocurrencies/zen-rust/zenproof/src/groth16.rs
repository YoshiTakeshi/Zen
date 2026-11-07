// A Groth16 verifier for the Zen stamp in Rust (Justus L. Ludovic).
//
// The final stamp is a gnark (v0.16.4) Groth16 proof on BN254: 196 bytes, with one BSB22 (Pedersen) commitment that gnark
// adds for the range checks. This module reads gnark's own byte formats and does gnark's own verification, so a node can
// check the 196-byte stamp without Go:
//   proof      A (G1, 32 B) | B (G2, 64 B) | C (G1, 32 B) | u32 count (1) | commitment (G1, 32 B) | commitment proof of knowledge (G1, 32 B)
//   vk         alpha1 | beta1 | beta2 | gamma2 | delta1 | delta2 | u32 n, K[n] (G1) | committed-public lists | u32 keys, per key G (G2) | GSigmaNeg (G2)
//   points     gnark-crypto's compressed form: big-endian x, the top two bits of the first byte are the flag
//              (0b10 y is the smaller root, 0b11 the larger, 0b01 infinity); a G2 x is A1 then A0
// Checks, in gnark's order: all points on the curve and in the right subgroup; the commitment's hash becomes one more public
// input (expand_message_xmd with SHA-256, DST "bsb22-commitment", over the commitment's 64 uncompressed bytes); the Pedersen
// proof of knowledge e(C, GSigmaNeg) e(PoK, G) = 1; then e(A,B) = e(alpha,beta) e(K0 + sum x_i K_i + commitment, gamma) e(C, delta).
// The public inputs are the stamp's 16 public values (each a Goldilocks number, so far below the BN254 scalar order).
use crate::node::StampVerifier;
use anyhow::{anyhow, bail, Result};
use ark_bn254::{Bn254, Fq, Fq2, Fr, G1Affine, G1Projective, G2Affine};
use ark_ec::{pairing::Pairing, AffineRepr, CurveGroup};
use ark_ff::{BigInteger, PrimeField, Zero};
use sha2::{Digest, Sha256};

pub const PROOF_BYTES: usize = 196;
pub const COMMITMENT_DST: &[u8] = b"bsb22-commitment";

fn fq_from(b: &[u8]) -> Result<Fq> {
    let v = Fq::from_be_bytes_mod_order(b);
    if v.into_bigint().to_bytes_be() != b { bail!("field element not canonical"); }
    Ok(v)
}
fn split_flag(b: &[u8]) -> (u8, Vec<u8>) { let mut c = b.to_vec(); let f = c[0] >> 6; c[0] &= 0x3f; (f, c) }

pub fn g1_from(b: &[u8]) -> Result<G1Affine> {
    if b.len() != 32 { bail!("a G1 point is 32 bytes"); }
    let (flag, xb) = split_flag(b);
    match flag {
        1 => { if xb.iter().any(|v| *v != 0) { bail!("bad infinity encoding"); } Ok(G1Affine::zero()) }
        2 | 3 => {
            let x = fq_from(&xb)?;
            let p = G1Affine::get_point_from_x_unchecked(x, flag == 3).ok_or_else(|| anyhow!("G1 point not on the curve"))?;
            if !p.is_on_curve() || !p.is_in_correct_subgroup_assuming_on_curve() { bail!("G1 point not in the group"); }
            Ok(p)
        }
        _ => bail!("not a compressed G1 point"),
    }
}
pub fn g2_from(b: &[u8]) -> Result<G2Affine> {
    if b.len() != 64 { bail!("a G2 point is 64 bytes"); }
    let (flag, mut c) = split_flag(b);
    match flag {
        1 => { if c.iter().any(|v| *v != 0) { bail!("bad infinity encoding"); } Ok(G2Affine::zero()) }
        2 | 3 => {
            c[0] &= 0x3f;
            let (a1, a0) = (fq_from(&c[..32])?, fq_from(&c[32..])?);
            let p = G2Affine::get_point_from_x_unchecked(Fq2::new(a0, a1), flag == 3).ok_or_else(|| anyhow!("G2 point not on the curve"))?;
            if !p.is_on_curve() || !p.is_in_correct_subgroup_assuming_on_curve() { bail!("G2 point not in the group"); }
            Ok(p)
        }
        _ => bail!("not a compressed G2 point"),
    }
}
fn g1_uncompressed(p: &G1Affine) -> [u8; 64] {
    let mut o = [0u8; 64];
    if p.is_zero() { o[0] = 0b01 << 6; return o; }
    o[..32].copy_from_slice(&p.x.into_bigint().to_bytes_be()); o[32..].copy_from_slice(&p.y.into_bigint().to_bytes_be());
    o
}

/// RFC 9380 expand_message_xmd with SHA-256
pub fn expand_message_xmd(msg: &[u8], dst: &[u8], len: usize) -> Vec<u8> {
    let ell = len.div_ceil(32);
    let mut dst_prime = dst.to_vec(); dst_prime.push(dst.len() as u8);
    let mut h = Sha256::new();
    h.update([0u8; 64]); h.update(msg); h.update((len as u16).to_be_bytes()); h.update([0u8]); h.update(&dst_prime);
    let b0 = h.finalize();
    let mut h = Sha256::new(); h.update(b0); h.update([1u8]); h.update(&dst_prime);
    let mut bi: [u8; 32] = h.finalize().into();
    let mut out = bi.to_vec();
    for i in 2..=ell {
        let x: Vec<u8> = b0.iter().zip(bi.iter()).map(|(a, b)| a ^ b).collect();
        let mut h = Sha256::new(); h.update(&x); h.update([i as u8]); h.update(&dst_prime);
        bi = h.finalize().into(); out.extend(bi);
    }
    out.truncate(len);
    out
}
/// gnark-crypto fr.Hash(msg, dst, 1): 48 bytes reduced modulo the scalar order
pub fn hash_to_fr(msg: &[u8], dst: &[u8]) -> Fr { Fr::from_be_bytes_mod_order(&expand_message_xmd(msg, dst, 48)) }

struct Reader<'a> { b: &'a [u8], p: usize }
impl<'a> Reader<'a> {
    fn take(&mut self, n: usize) -> Result<&'a [u8]> { let s = self.b.get(self.p..self.p + n).ok_or_else(|| anyhow!("truncated"))?; self.p += n; Ok(s) }
    fn u32(&mut self) -> Result<usize> { Ok(u32::from_be_bytes(self.take(4)?.try_into()?) as usize) }
}

pub struct Proof { pub a: G1Affine, pub b: G2Affine, pub c: G1Affine, pub commitments: Vec<G1Affine>, pub pok: G1Affine }
impl Proof {
    pub fn from_bytes(b: &[u8]) -> Result<Proof> {
        if b.len() != PROOF_BYTES { bail!("a stamp is {} bytes, not {}", b.len(), PROOF_BYTES); }
        let mut r = Reader { b, p: 0 };
        let (a, bb, c) = (g1_from(r.take(32)?)?, g2_from(r.take(64)?)?, g1_from(r.take(32)?)?);
        let n = r.u32()?;
        if n != 1 { bail!("expected one commitment, found {n}"); }
        let commitments = vec![g1_from(r.take(32)?)?];
        let pok = g1_from(r.take(32)?)?;
        Ok(Proof { a, b: bb, c, commitments, pok })
    }
}

pub struct Vk {
    alpha: G1Affine, beta: ark_bn254::G2Affine, gamma: G2Affine, delta: G2Affine,
    k: Vec<G1Affine>,
    committed: Vec<Vec<u64>>,
    ped_g: G2Affine, ped_gsigma_neg: G2Affine,
}
impl Vk {
    pub fn from_bytes(b: &[u8]) -> Result<Vk> {
        let mut r = Reader { b, p: 0 };
        let alpha = g1_from(r.take(32)?)?;
        let _beta1 = g1_from(r.take(32)?)?;
        let beta = g2_from(r.take(64)?)?; let gamma = g2_from(r.take(64)?)?;
        let _delta1 = g1_from(r.take(32)?)?;
        let delta = g2_from(r.take(64)?)?;
        let nk = r.u32()?;
        if nk == 0 || nk > 4096 { bail!("implausible key length {nk}"); }
        let k = (0..nk).map(|_| g1_from(r.take(32)?)).collect::<Result<Vec<_>>>()?;
        let nc = r.u32()?;
        if nc != 1 { bail!("expected one commitment, key has {nc}"); }
        let mut committed = vec![];
        for _ in 0..nc { let m = r.u32()?; committed.push((0..m).map(|_| Ok(u64::from_be_bytes(r.take(8)?.try_into()?))).collect::<Result<Vec<u64>>>()?); }
        let nkeys = r.u32()?;
        if nkeys != 1 { bail!("expected one commitment key, found {nkeys}"); }
        let ped_g = g2_from(r.take(64)?)?; let ped_gsigma_neg = g2_from(r.take(64)?)?;
        if r.p != b.len() { bail!("trailing bytes in the verifying key"); }
        Ok(Vk { alpha, beta, gamma, delta, k, committed, ped_g, ped_gsigma_neg })
    }
    /// number of public inputs a proof under this key takes (the commitment's own input excluded)
    pub fn public_len(&self) -> usize { self.k.len() - 1 - self.committed.len() }

    pub fn verify(&self, proof: &Proof, public: &[Fr]) -> Result<()> {
        if public.len() != self.public_len() { bail!("{} public inputs, the key takes {}", public.len(), self.public_len()); }
        // the commitment's hash is one more public input (nothing but the commitment is hashed: the key lists no committed public values)
        if self.committed.iter().any(|c| !c.is_empty()) { bail!("keys with committed public values are not supported"); }
        let mut inputs = public.to_vec();
        for c in &proof.commitments { inputs.push(hash_to_fr(&g1_uncompressed(c), COMMITMENT_DST)); }
        // Pedersen proof of knowledge of the commitment's opening: e(C, -GSigma) e(PoK, G) = 1
        let ok = Bn254::multi_pairing([proof.commitments[0], proof.pok], [self.ped_gsigma_neg, self.ped_g]);
        if !ok.is_zero() { bail!("commitment proof rejected"); }
        // L = K0 + sum x_i K_i + commitments
        let mut l = G1Projective::from(self.k[0]);
        for (x, kp) in inputs.iter().zip(&self.k[1..]) { l += *kp * x; }
        for c in &proof.commitments { l += c; }
        let l = l.into_affine();
        // e(A, B) = e(alpha, beta) e(L, gamma) e(C, delta)
        let r = Bn254::multi_pairing([proof.a, -self.alpha, -l, -proof.c], [proof.b, self.beta, self.gamma, self.delta]);
        if !r.is_zero() { bail!("proof rejected"); }
        Ok(())
    }
}

/// `zenproof g16verify <zen.vk> <zen.proof> <zen.pub>`: check a gnark proof with its public witness file
pub fn g16verify_main() -> Result<()> {
    let a: Vec<String> = std::env::args().collect();
    if a.len() < 5 { bail!("usage: g16verify <zen.vk> <zen.proof> <zen.pub>"); }
    let vk = Vk::from_bytes(&std::fs::read(&a[2])?)?;
    let proof = Proof::from_bytes(&std::fs::read(&a[3])?)?;
    let w = std::fs::read(&a[4])?;
    let n = u32::from_be_bytes(w.get(8..12).ok_or_else(|| anyhow!("short witness file"))?.try_into()?) as usize;
    if w.len() != 12 + 32 * n { bail!("witness file has the wrong length"); }
    let public: Vec<Fr> = (0..n).map(|i| Fr::from_be_bytes_mod_order(&w[12 + 32 * i..44 + 32 * i])).collect();
    let t = std::time::Instant::now();
    let r = vk.verify(&proof, &public);
    println!("RESULT groth16 verify: ok={} | {:.2} ms | {} public inputs{}", r.is_ok(), t.elapsed().as_secs_f64() * 1e3, n, r.err().map(|e| format!(" | {e}")).unwrap_or_default());
    Ok(())
}

/// The node's check of a 196-byte Groth16 stamp: the stamp's public values go in as the circuit's public inputs.
pub struct Groth16Stamp { vk: Vk }
impl Groth16Stamp {
    pub fn new(vk_bytes: &[u8]) -> Result<Groth16Stamp> { Ok(Groth16Stamp { vk: Vk::from_bytes(vk_bytes)? }) }
}
impl StampVerifier for Groth16Stamp {
    fn verify(&self, pubvalues: &[u64], stamp: &[u8]) -> Result<()> {
        let proof = Proof::from_bytes(stamp)?;
        let public: Vec<Fr> = pubvalues.iter().map(|v| Fr::from(*v)).collect();
        self.vk.verify(&proof, &public)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;
    fn dir() -> PathBuf { PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../g16wrap/result_v2") }
    /// gnark's public witness file: u32 public, u32 secret, u32 length, then 32-byte big-endian elements
    fn read_pub(p: &std::path::Path) -> Vec<Fr> {
        let b = std::fs::read(p).unwrap();
        let n = u32::from_be_bytes(b[8..12].try_into().unwrap()) as usize;
        assert_eq!(b.len(), 12 + 32 * n);
        (0..n).map(|i| Fr::from_be_bytes_mod_order(&b[12 + 32 * i..44 + 32 * i])).collect()
    }
    fn load() -> Option<(Vk, Vec<(Proof, Vec<Fr>, Vec<u8>)>)> {
        let d = dir();
        let vk = Vk::from_bytes(&std::fs::read(d.join("zen.vk")).ok()?).unwrap();
        let blocks = ["v2A", "v2B", "v2C"].iter().map(|n| {
            let raw = std::fs::read(d.join(n).join("zen.proof")).unwrap();
            (Proof::from_bytes(&raw).unwrap(), read_pub(&d.join(n).join("zen.pub")), raw)
        }).collect();
        Some((vk, blocks))
    }
    #[test]
    fn expand_message_xmd_matches_rfc_9380_vectors() {
        // RFC 9380, appendix K.1: expand_message_xmd(SHA-256), DST QUUX-V01-CS02-with-expander-SHA256-128
        let dst = b"QUUX-V01-CS02-with-expander-SHA256-128";
        let hx = |b: Vec<u8>| b.iter().map(|x| format!("{x:02x}")).collect::<String>();
        assert_eq!(hx(expand_message_xmd(b"", dst, 0x20)), "68a985b87eb6b46952128911f2a4412bbc302a9d759667f87f7a21d803f07235");
        assert_eq!(hx(expand_message_xmd(b"abc", dst, 0x20)), "d8ccab23b5985ccea865c6c97b6e5b8350e794e603b4b97902f53a8a0d605615");
        assert_eq!(hx(expand_message_xmd(b"", dst, 0x80)), "af84c27ccfd45d41914fdff5df25293e221afc53d8ad2ac06d5e3e29485dadbee0d121587713a3e0dd4d5e69e93eb7cd4f5df4cd103e188cf60cb02edc3edf18eda8576c412b18ffb658e3dd6ec849469b979d444cf7b26911a08e63cf31f9dcc541708d3491184472c2c29bb749d4286b004ceb5ee6b9a7fa5b646c993f0ced");
    }
    #[test]
    fn gnark_proofs_verify_and_everything_else_does_not() {
        let Some((vk, blocks)) = load() else { println!("g16wrap results not present: skipped"); return };
        assert_eq!(vk.public_len(), 16);
        for (i, (proof, public, _)) in blocks.iter().enumerate() {
            assert_eq!(public.len(), 16);
            vk.verify(proof, public).unwrap_or_else(|e| panic!("block {i}: {e}"));
        }
        let (p0, pub0, raw0) = &blocks[0];
        let (_, pub1, _) = &blocks[1];
        // another block's public values
        assert!(vk.verify(p0, pub1).is_err());
        // one public value changed by one
        for k in [0usize, 8, 10, 14, 15] { let mut m = pub0.clone(); m[k] += Fr::from(1u64); assert!(vk.verify(p0, &m).is_err(), "public value {k}"); }
        // every byte of the stamp matters: flip one bit in each field
        for byte in [3usize, 20, 40, 70, 100, 140, 170, 195] {
            let mut r = raw0.clone(); r[byte] ^= 0x01;
            let ok = Proof::from_bytes(&r).and_then(|p| vk.verify(&p, pub0)).is_ok();
            assert!(!ok, "a flipped bit at byte {byte} was accepted");
        }
        // wrong length, empty
        assert!(Proof::from_bytes(&raw0[..195]).is_err());
        // swapping A and C (both G1) or the commitment and its proof
        let mut sw = raw0.clone(); let a = sw[..32].to_vec(); let c = sw[96..128].to_vec(); sw[..32].copy_from_slice(&c); sw[96..128].copy_from_slice(&a);
        assert!(Proof::from_bytes(&sw).and_then(|p| vk.verify(&p, pub0)).is_err());
        let mut sw = raw0.clone(); let c1 = sw[132..164].to_vec(); let c2 = sw[164..196].to_vec(); sw[132..164].copy_from_slice(&c2); sw[164..196].copy_from_slice(&c1);
        assert!(Proof::from_bytes(&sw).and_then(|p| vk.verify(&p, pub0)).is_err());
    }
    #[test]
    fn a_stamp_of_a_current_block_verifies_under_the_current_key() {
        // version-6 setup: the peg circuit, a fresh single-party Groth16 setup, a block proved with it
        let d = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../g16wrap/result_v6");
        let Ok(vkb) = std::fs::read(d.join("zen.vk")) else { println!("result_v6 not present: skipped"); return };
        let raw = std::fs::read(d.join("zen.proof")).unwrap();
        assert_eq!(raw.len(), 196);
        let pubs: Vec<u64> = read_pub(&d.join("zen.pub")).iter().map(|f| { let b = f.into_bigint(); assert!(b.0[1..].iter().all(|w| *w == 0)); b.0[0] }).collect();
        assert_eq!(pubs.len(), 16);
        assert_eq!((pubs[8], pubs[9]), (10054960, 112)); // fee total and payment count of the exported block
        let g = Groth16Stamp::new(&vkb).unwrap();
        g.verify(&pubs, &raw).unwrap();
        for k in 0..16 { let mut m = pubs.clone(); m[k] ^= 1; assert!(g.verify(&m, &raw).is_err(), "public value {k}"); }
        for byte in [3usize, 40, 70, 100, 140, 170, 195] { let mut r = raw.clone(); r[byte] ^= 1; assert!(g.verify(&pubs, &r).is_err(), "byte {byte}"); }
        // the older key does not accept the current block
        if let Ok(old) = std::fs::read(dir().join("zen.vk")) { assert!(Groth16Stamp::new(&old).unwrap().verify(&pubs, &raw).is_err()); }
    }
    #[test]
    fn as_a_node_stamp_verifier() {
        let d = dir();
        let Ok(vkb) = std::fs::read(d.join("zen.vk")) else { return };
        let g = Groth16Stamp::new(&vkb).unwrap();
        let raw = std::fs::read(d.join("v2A/zen.proof")).unwrap();
        let pubs: Vec<u64> = read_pub(&d.join("v2A/zen.pub")).iter().map(|f| { let b = f.into_bigint(); assert!(b.0[1..].iter().all(|w| *w == 0)); b.0[0] }).collect();
        g.verify(&pubs, &raw).unwrap();
        let t = std::time::Instant::now();
        for _ in 0..20 { g.verify(&pubs, &raw).unwrap(); }
        println!("groth16 verify in Rust: {:.2} ms per stamp (average of 20)", t.elapsed().as_secs_f64() * 50.0);
        let mut bad = pubs.clone(); bad[9] ^= 1;
        assert!(g.verify(&bad, &raw).is_err());
        assert!(g.verify(&pubs[..15], &raw).is_err());
        assert!(g.verify(&pubs, &raw[..100]).is_err());
        // the key of the newer circuit version parses too
        let v4 = std::fs::read(d.join("../result_v4/zen.vk")).unwrap();
        assert_eq!(Vk::from_bytes(&v4).unwrap().public_len(), 16);
        Proof::from_bytes(&std::fs::read(d.join("../result_v4/zen.proof")).unwrap()).unwrap();
    }
}
