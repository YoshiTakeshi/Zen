// The seal: Bitcoin's 80-byte header, byte for byte, so SHA-256 ASICs, their firmware and Stratum v1
// pool software can seal Zen blocks unchanged.
//
//   header     = version (4, LE) | prev (32) | commitment (32) | ntime (4, LE) | nbits (4, LE) | nonce (4, LE)
//   block hash = SHA256d(header); the seal is valid when the hash, read as a little-endian 256-bit
//                number (Bitcoin's convention), is <= the target encoded by nbits (Bitcoin's compact form)
//
// The commitment is built exactly like a Bitcoin merkle root over a one-transaction "coinbase" with
// one branch, which is what every Stratum pool and miner computes:
//
//   coinbase   = coinb1 || extranonce1 || extranonce2 || coinb2
//   commitment = SHA256d( SHA256d(coinbase) || body root )
//   coinb1     = "ZenSeal1" | chain id (1) | height (8, LE) | extranonce length (1)
//   coinb2     = miner address (32)          who receives the miner's reward and fee cut
//   body root  = SHA256("Zen-body-v1" | the stamp's 16 public values | stamp proof | SHA256(block data)
//                       | tickets root)
//
// The pool fills in its extranonce1 per connection and the miner rolls extranonce2, ntime and the nonce
// (and version bits 13-28, BIP 320), so a modern ASIC never runs out of work. The miner address sits in
// the coinbase, so a pool sets its own address and pays its miners as it does for Bitcoin. Nothing the
// miner can change touches the minted block: everything else is under the body root.
use anyhow::{bail, Result};
use num_bigint::BigUint;
use sha2::{Digest, Sha256};

pub const VERSION_BASE: u32 = 0x2000_0000;
/// BIP 320: bits a miner may roll
pub const VERSION_ROLL_MASK: u32 = 0x1fff_e000;
pub const MAGIC: &[u8; 8] = b"ZenSeal1";
pub const MAX_EXTRANONCE: usize = 32;

pub fn sha256d(b: &[u8]) -> [u8; 32] { let h = Sha256::digest(b); Sha256::digest(h).into() }
pub fn hex(b: &[u8]) -> String { b.iter().map(|x| format!("{x:02x}")).collect() }
pub fn unhex(s: &str) -> Vec<u8> { (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect() }

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Header { pub version: u32, pub prev: [u8; 32], pub commitment: [u8; 32], pub ntime: u32, pub nbits: u32, pub nonce: u32 }
impl Header {
    pub fn bytes(&self) -> [u8; 80] {
        let mut o = [0u8; 80];
        o[0..4].copy_from_slice(&self.version.to_le_bytes()); o[4..36].copy_from_slice(&self.prev);
        o[36..68].copy_from_slice(&self.commitment); o[68..72].copy_from_slice(&self.ntime.to_le_bytes());
        o[72..76].copy_from_slice(&self.nbits.to_le_bytes()); o[76..80].copy_from_slice(&self.nonce.to_le_bytes());
        o
    }
    pub fn hash(&self) -> [u8; 32] { sha256d(&self.bytes()) }
}

// ------------------------------------------------------------------ targets (Bitcoin compact form)
pub fn bits_to_target(bits: u32) -> Result<BigUint> {
    let (exp, mant) = (bits >> 24, bits & 0x007f_ffff);
    if bits & 0x0080_0000 != 0 && mant != 0 { bail!("negative target"); }
    if mant == 0 { bail!("zero target"); }
    let t = if exp <= 3 { BigUint::from(mant >> (8 * (3 - exp))) } else { BigUint::from(mant) << (8 * (exp - 3)) };
    if t.bits() > 256 { bail!("target overflow"); }
    Ok(t)
}
pub fn target_to_bits(t: &BigUint) -> u32 {
    let mut size = t.to_bytes_be().len() as u32;
    let mut mant: u32 = if size <= 3 { (t.iter_u64_digits().next().unwrap_or(0) as u32) << (8 * (3 - size)) } else { (t >> (8 * (size - 3))).iter_u64_digits().next().unwrap_or(0) as u32 };
    if mant & 0x0080_0000 != 0 { mant >>= 8; size += 1; }
    (size << 24) | mant
}
/// Zen difficulty D (expected hashes = D x 2^32 at D = 1, as in Bitcoin) to a compact target
pub fn difficulty_bits(d: u64) -> u32 { let max = bits_to_target(0x1d00_ffff).unwrap(); target_to_bits(&(max / BigUint::from(d.max(1)))) }
pub fn meets(hash: &[u8; 32], bits: u32) -> bool {
    match bits_to_target(bits) { Ok(t) => BigUint::from_bytes_le(hash) <= t, Err(_) => false }
}

// ------------------------------------------------------------------ coinbase and commitment
pub fn coinb1(chain: u8, height: u64, xlen: usize) -> Vec<u8> {
    let mut v = MAGIC.to_vec(); v.push(chain); v.extend(height.to_le_bytes()); v.push(xlen as u8); v
}
pub fn coinb2(miner: &[u8; 32]) -> Vec<u8> { miner.to_vec() }
pub fn body_root(public_values: &[u64], stamp: &[u8], block_data: &[u8], tickets_root: &[u8; 32]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"Zen-body-v1");
    for v in public_values { h.update(v.to_le_bytes()); }
    h.update(stamp); h.update(Sha256::digest(block_data)); h.update(tickets_root);
    h.finalize().into()
}
/// the Stratum merkle-root computation: SHA256d(coinbase), folded with each branch hash
pub fn merkle_root(coinbase: &[u8], branch: &[[u8; 32]]) -> [u8; 32] {
    let mut r = sha256d(coinbase);
    for b in branch { let mut x = r.to_vec(); x.extend_from_slice(b); r = sha256d(&x); }
    r
}

/// What a node reads from a sealed block's coinbase.
pub struct Coinbase { pub chain: u8, pub height: u64, pub miner: [u8; 32] }
pub fn parse_coinbase(cb: &[u8]) -> Result<Coinbase> {
    if cb.len() < 18 + 32 || &cb[..8] != MAGIC { bail!("not a Zen coinbase"); }
    let chain = cb[8];
    let height = u64::from_le_bytes(cb[9..17].try_into()?);
    let xlen = cb[17] as usize;
    if xlen > MAX_EXTRANONCE || cb.len() != 18 + xlen + 32 { bail!("bad extranonce length"); }
    Ok(Coinbase { chain, height, miner: cb[18 + xlen..].try_into()? })
}

/// Everything a node checks about a seal, given the minted block it expects (chain, height, prev, body).
pub fn check_seal(h: &Header, coinbase: &[u8], chain: u8, height: u64, prev: &[u8; 32], body: &[u8; 32], bits: u32) -> Result<[u8; 32]> {
    if h.version & !VERSION_ROLL_MASK != VERSION_BASE { bail!("version outside the rollable bits"); }
    if h.prev != *prev { bail!("wrong previous block"); }
    if h.nbits != bits { bail!("wrong difficulty bits"); }
    let cb = parse_coinbase(coinbase)?;
    if cb.chain != chain || cb.height != height { bail!("coinbase for another chain or height"); }
    if merkle_root(coinbase, &[*body]) != h.commitment { bail!("commitment does not match the minted block"); }
    if !meets(&h.hash(), h.nbits) { bail!("hash above the target"); }
    Ok(cb.miner)
}

// ------------------------------------------------------------------ Stratum v1 (mining.notify)
/// A job as a Stratum v1 pool sends it. Field encodings follow the protocol as pools and cgminer-style
/// miners use it: prevhash with each 4-byte word byte-swapped, version/nbits/ntime as big-endian hex.
pub struct Job { pub job_id: String, pub prevhash: String, pub coinb1: String, pub coinb2: String, pub merkle_branch: Vec<String>, pub version: String, pub nbits: String, pub ntime: String }
fn swap_words(b: &[u8]) -> Vec<u8> { b.chunks(4).flat_map(|c| c.iter().rev().copied().collect::<Vec<_>>()).collect() }
pub fn make_job(id: &str, chain: u8, height: u64, prev: &[u8; 32], body: &[u8; 32], miner: &[u8; 32], xlen: usize, bits: u32, ntime: u32) -> Job {
    Job { job_id: id.into(), prevhash: hex(&swap_words(prev)), coinb1: hex(&coinb1(chain, height, xlen)), coinb2: hex(&coinb2(miner)),
          merkle_branch: vec![hex(body)], version: format!("{VERSION_BASE:08x}"), nbits: format!("{bits:08x}"), ntime: format!("{ntime:08x}") }
}
impl Job {
    pub fn notify_json(&self) -> String {
        format!(r#"{{"id":null,"method":"mining.notify","params":["{}","{}","{}","{}",[{}],"{}","{}","{}",true]}}"#,
            self.job_id, self.prevhash, self.coinb1, self.coinb2, self.merkle_branch.iter().map(|b| format!("\"{b}\"")).collect::<Vec<_>>().join(","), self.version, self.nbits, self.ntime)
    }
}

/// A miner that knows only Stratum: builds the coinbase and header from the job the standard way and
/// grinds the nonce (rolling extranonce2 when the nonce space runs out). Returns the share it found.
pub struct Share { pub extranonce2: Vec<u8>, pub ntime: u32, pub nonce: u32, pub version: u32 }
pub fn stratum_mine(job: &Job, extranonce1: &[u8], en2_size: usize, max_hashes: u64) -> Option<(Share, u64)> {
    let prev: [u8; 32] = swap_words(&unhex(&job.prevhash)).try_into().unwrap();
    let branch: Vec<[u8; 32]> = job.merkle_branch.iter().map(|b| unhex(b).try_into().unwrap()).collect();
    let (version, nbits, ntime) = (u32::from_str_radix(&job.version, 16).ok()?, u32::from_str_radix(&job.nbits, 16).ok()?, u32::from_str_radix(&job.ntime, 16).ok()?);
    let target = bits_to_target(nbits).ok()?;
    let mut hashes = 0u64;
    for en2 in 0u64.. {
        let en2b = en2.to_le_bytes()[..en2_size].to_vec();
        let mut cb = unhex(&job.coinb1); cb.extend_from_slice(extranonce1); cb.extend_from_slice(&en2b); cb.extend(unhex(&job.coinb2));
        let mut h = Header { version, prev, commitment: merkle_root(&cb, &branch), ntime, nbits, nonce: 0 };
        let mut hb = h.bytes();
        for nonce in 0..=u32::MAX {
            hb[76..80].copy_from_slice(&nonce.to_le_bytes());
            hashes += 1;
            if BigUint::from_bytes_le(&sha256d(&hb)) <= target { h.nonce = nonce; return Some((Share { extranonce2: en2b, ntime, nonce, version }, hashes)); }
            if hashes >= max_hashes { return None; }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    /// Bitcoin's genesis block: our header layout, hashing and target check give the known hash
    #[test]
    fn bitcoin_genesis() {
        let mut root: [u8; 32] = unhex("4a5e1e4baab89f3a32518a88c31bc87f618f76673e2cc77ab2127b7afdeda33b").try_into().unwrap();
        root.reverse(); // displayed big-endian, stored little-endian
        let h = Header { version: 1, prev: [0; 32], commitment: root, ntime: 1231006505, nbits: 0x1d00ffff, nonce: 2083236893 };
        let mut hash = h.hash(); hash.reverse();
        assert_eq!(hex(&hash), "000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f");
        assert!(meets(&h.hash(), h.nbits));
        assert!(!meets(&Header { nonce: 1, ..h }.hash(), h.nbits));
    }
    #[test]
    fn compact_bits() {
        for b in [0x1d00ffffu32, 0x1b0404cb, 0x207fffff, 0x1f00ffff, 0x170331db] { assert_eq!(target_to_bits(&bits_to_target(b).unwrap()), b); }
        assert_eq!(difficulty_bits(1), 0x1d00ffff);
        assert!(bits_to_target(0x1d80ffff).is_err());
    }
}
