//! The wire between two nodes (stage 10, Justus L. Ludovic): every request and answer is encrypted and the caller proves who it is.
//!
//! One request, one answer, on one connection (a Noise-N/X-like handshake over the node's own curve):
//!   * the caller knows the server's static public key S (it is the other side of a channel, or the key a crawl was told about);
//!   * it makes an ephemeral key e (E = eG), and works out k_req from ECDH(e, S) and E; the request is XORed with a key stream and covered by a MAC;
//!   * it signs (E, S, its own static key C) with C's key, so the server knows the request comes from C (and nobody else can replay it under a new E);
//!   * the server opens it with ECDH(s, E), checks the MAC, the signature and the time stamp (60 s), and answers under a key from ECDH(s, E) and
//!     ECDH(e_s, E) with its own fresh ephemeral key: the answer stays secret even if a static key leaks later (the request does not: it is sealed to S).
//! What this does not give: hiding that two addresses talk, padding of lengths, or protection of a request against the later leak of S's secret key.
use crate::{ec, mint, F};
use anyhow::{anyhow, bail, Result};
use num_bigint::BigUint;
use plonky2::field::types::Field;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

const MAC: usize = 16;
pub const MAX_SKEW: u64 = 60;
fn hex(b: &[u8]) -> String { b.iter().map(|x| format!("{x:02x}")).collect() }
fn unhex(s: &str) -> Result<Vec<u8>> { (0..s.len() / 2).map(|i| Ok(u8::from_str_radix(s.get(2 * i..2 * i + 2).ok_or_else(|| anyhow!("bad hex"))?, 16)?)).collect() }
fn h(parts: &[&[u8]]) -> [u8; 32] { let mut x = Sha256::new(); for p in parts { x.update((p.len() as u32).to_le_bytes()); x.update(p); } x.finalize().into() }
fn dh(sk: &BigUint, pt: &[u8; 41]) -> Result<[u8; 32]> { Ok(h(&[b"Zen-tr-dh", &mint::encode_point(ec::mul(mint::decode_point(pt)?, sk))])) }
fn stream(k: &[u8; 32], n: usize) -> Vec<u8> { let mut o = vec![]; let mut c = 0u32; while o.len() < n { o.extend(h(&[b"Zen-tr-ks", k, &c.to_le_bytes()])); c += 1; } o.truncate(n); o }
fn xor(k: &[u8; 32], d: &[u8]) -> Vec<u8> { d.iter().zip(stream(k, d.len())).map(|(a, b)| a ^ b).collect() }
fn tag(k: &[u8; 32], parts: &[&[u8]]) -> [u8; MAC] { let mut v = vec![b"Zen-tr-mac".as_slice(), k.as_slice()]; v.extend_from_slice(parts); h(&v)[..MAC].try_into().unwrap() }
fn to_msg(d: [u8; 32]) -> [F; 4] { std::array::from_fn(|i| F::from_noncanonical_u64(u64::from_le_bytes(d[8 * i..8 * i + 8].try_into().unwrap()))) }
fn rand_scalar() -> BigUint { loop { let mut b = [0u8; 64]; rand::RngCore::fill_bytes(&mut rand::rngs::OsRng, &mut b); let k = BigUint::from_bytes_le(&b) % ec::n_order(); if k != BigUint::ZERO { return k; } } }
fn point_of(k: &BigUint) -> [u8; 41] { mint::encode_point(ec::mul_g(&ec::params(), k)) }
fn arr<const N: usize>(v: &Value, k: &str) -> Result<[u8; N]> { unhex(v[k].as_str().unwrap_or(""))?.try_into().map_err(|_| anyhow!("{k}: expected {N} bytes")) }
fn k_req(d1: &[u8; 32], e: &[u8; 41]) -> [u8; 32] { h(&[b"Zen-tr-req", d1, e]) }
fn k_resp(d1: &[u8; 32], d2: &[u8; 32], e: &[u8; 41], es: &[u8; 41]) -> [u8; 32] { h(&[b"Zen-tr-resp", d1, d2, e, es]) }
fn auth_msg(e: &[u8; 41], s: &[u8; 41], c: &[u8; 41]) -> [F; 4] { to_msg(h(&[b"Zen-tr-auth", e, s, c])) }

/// the caller's side of one exchange; keep it to read the answer
pub struct Call { e: BigUint, e_pub: [u8; 41], d1: [u8; 32] }
/// seal `req` for the server with static key `server`; `me` is the caller's static key pair (its secret scalar and signing key)
pub fn seal_request(my_sk: &BigUint, me: &mint::Key, server: &[u8; 41], req: &Value, now: u64) -> Result<(Value, Call)> {
    let e = rand_scalar(); let e_pub = point_of(&e);
    let d1 = dh(&e, server)?;
    let mut body = req.clone(); body["ts"] = json!(now);
    let ct = xor(&k_req(&d1, &e_pub), &serde_json::to_vec(&body)?);
    let c = mint::encode_point(me.a);
    let (se, ss) = mint::sign(me, auth_msg(&e_pub, server, &c));
    let mut sig = se.to_le_bytes().to_vec(); sig.extend(mint::s_bytes(&ss));
    let m = tag(&k_req(&d1, &e_pub), &[&e_pub, &c, &sig, &ct]);
    let _ = my_sk;
    Ok((json!({"hs": hex(&e_pub), "c": hex(&c), "sig": hex(&sig), "ct": hex(&ct), "mac": hex(&m)}), Call { e, e_pub, d1 }))
}
/// what the server learns from a sealed request: the request, who sent it, and what it needs to answer
pub struct Opened { pub req: Value, pub caller: [u8; 41], e_pub: [u8; 41], d1: [u8; 32] }
pub fn open_request(server_sk: &BigUint, server_pub: &[u8; 41], wire: &Value, now: u64) -> Result<Opened> {
    let e_pub: [u8; 41] = arr(wire, "hs")?; let c: [u8; 41] = arr(wire, "c")?; let sig = unhex(wire["sig"].as_str().unwrap_or(""))?; let ct = unhex(wire["ct"].as_str().unwrap_or(""))?;
    let m: [u8; MAC] = arr(wire, "mac")?;
    if sig.len() != 56 { bail!("bad signature"); }
    let d1 = dh(server_sk, &e_pub)?;
    let k = k_req(&d1, &e_pub);
    if tag(&k, &[&e_pub, &c, &sig, &ct]) != m { bail!("the request does not open"); }
    let pc = mint::decode_point(&c)?;
    if !mint::verify(pc, auth_msg(&e_pub, server_pub, &c), u128::from_le_bytes(sig[..16].try_into()?), &BigUint::from_bytes_le(&sig[16..])) { bail!("the caller's signature is bad"); }
    let req: Value = serde_json::from_slice(&xor(&k, &ct))?;
    let ts = req["ts"].as_u64().ok_or_else(|| anyhow!("no time stamp"))?;
    if ts.abs_diff(now) > MAX_SKEW { bail!("the request is too old or too new ({}s)", ts.abs_diff(now)); }
    Ok(Opened { req, caller: c, e_pub, d1 })
}
/// the one-time keys of the requests a server has opened lately: inside the allowed skew a copy of a request is refused
#[derive(Default)]
pub struct Replays { seen: std::sync::Mutex<std::collections::HashMap<[u8; 41], u64>> }
impl Replays {
    const MAX: usize = 100_000;
    /// true the first time a one-time key is seen; false for a copy (or when the cache is full: refusing is the safe side)
    pub fn first(&self, n: &[u8; 41], now: u64) -> bool {
        let mut m = self.seen.lock().unwrap();
        m.retain(|_, at| now.saturating_sub(*at) <= 2 * MAX_SKEW);
        if m.len() >= Self::MAX { return false; }
        m.insert(*n, now).is_none()
    }
}
impl Opened { /// the one-time key of this request: a server that has seen it before has a replay
    pub fn nonce(&self) -> [u8; 41] { self.e_pub } }
pub fn seal_answer(o: &Opened, ans: &Value) -> Result<Value> {
    let es = rand_scalar(); let es_pub = point_of(&es);
    let d2 = dh(&es, &o.e_pub)?;
    let k = k_resp(&o.d1, &d2, &o.e_pub, &es_pub);
    let ct = xor(&k, &serde_json::to_vec(ans)?);
    Ok(json!({"hs": hex(&es_pub), "ct": hex(&ct), "mac": hex(&tag(&k, &[&es_pub, &ct]))}))
}
pub fn open_answer(call: &Call, wire: &Value) -> Result<Value> {
    if let Some(e) = wire["err"].as_str() { bail!("{e}"); }
    let es_pub: [u8; 41] = arr(wire, "hs")?; let ct = unhex(wire["ct"].as_str().unwrap_or(""))?; let m: [u8; MAC] = arr(wire, "mac")?;
    let d2 = dh(&call.e, &es_pub)?;
    let k = k_resp(&call.d1, &d2, &call.e_pub, &es_pub);
    if tag(&k, &[&es_pub, &ct]) != m { bail!("the answer does not open"); }
    Ok(serde_json::from_slice(&xor(&k, &ct))?)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn key(n: u32) -> (BigUint, mint::Key) { let s = BigUint::from(n); (s.clone(), mint::Key::from_secret(s)) }
    #[test]
    fn a_copy_of_a_request_inside_the_time_window_is_refused_but_a_new_request_is_not() {
        let ((cs, ck), (ss, sk)) = (key(1234), key(5678));
        let spub = mint::encode_point(sk.a);
        let rp = Replays::default();
        let (w1, _) = seal_request(&cs, &ck, &spub, &json!({"t": "sync"}), 1000).unwrap();
        let (w2, _) = seal_request(&cs, &ck, &spub, &json!({"t": "sync"}), 1000).unwrap();
        let o1 = open_request(&ss, &spub, &w1, 1001).unwrap();
        assert!(rp.first(&o1.nonce(), 1001), "the first time");
        let again = open_request(&ss, &spub, &w1, 1002).unwrap();
        assert!(!rp.first(&again.nonce(), 1002), "the same bytes again are a replay");
        let o2 = open_request(&ss, &spub, &w2, 1002).unwrap();
        assert!(rp.first(&o2.nonce(), 1002), "the same words in a new request are fine");
        // far past the window the old copy would be refused by its time stamp anyway, and the cache forgets it
        assert!(open_request(&ss, &spub, &w1, 1000 + MAX_SKEW + 5).is_err());
        assert!(rp.first(&o1.nonce(), 1000 + 3 * MAX_SKEW));
    }
    #[test]
    fn a_request_and_its_answer_open_only_for_the_right_keys_and_only_once_fresh() {
        let ((cs, ck), (ss, sk)) = (key(1234), key(5678));
        let (spub, cpub) = (mint::encode_point(sk.a), mint::encode_point(ck.a));
        let req = json!({"t": "sync", "chan": "ab", "seq": 3});
        let (wire, call) = seal_request(&cs, &ck, &spub, &req, 1000).unwrap();
        assert!(!wire.to_string().contains("sync"), "the request is not in the clear");
        let o = open_request(&ss, &spub, &wire, 1010).unwrap();
        assert_eq!((o.req["t"].as_str(), o.req["seq"].as_u64(), o.caller), (Some("sync"), Some(3), cpub));
        let ans = seal_answer(&o, &json!({"seq": 9, "state": "00ff"})).unwrap();
        assert!(!ans.to_string().contains("state"));
        assert_eq!(open_answer(&call, &ans).unwrap()["seq"], 9);
        // another caller's exchange cannot read it
        let (_, call2) = seal_request(&cs, &ck, &spub, &req, 1000).unwrap();
        assert!(open_answer(&call2, &ans).is_err());
        // a wrong server key, a flipped byte, a replay far in time, or a request that claims another caller's identity are all refused
        let (os, ok) = key(999); let opub = mint::encode_point(ok.a);
        assert!(open_request(&os, &opub, &wire, 1010).is_err());
        let mut bad = wire.clone(); let ct = bad["ct"].as_str().unwrap().to_string(); bad["ct"] = json!(format!("{}{}", if ct.starts_with('0') { "1" } else { "0" }, &ct[1..]));
        assert!(open_request(&ss, &spub, &bad, 1010).is_err());
        assert!(open_request(&ss, &spub, &wire, 1000 + MAX_SKEW + 1).is_err());
        let mut fake = wire.clone(); fake["c"] = json!(hex(&opub));
        assert!(open_request(&ss, &spub, &fake, 1010).is_err());
        // a request sealed for one server is not accepted by another server that holds the same wire (the signature names the server)
        assert!(open_request(&ss, &opub, &wire, 1010).is_err());
    }
}
