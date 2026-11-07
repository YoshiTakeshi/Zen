// Signed payments and the wallet (stage 4, Justus L. Ludovic).
//
// A signed payment is what a wallet sends and what the mempool holds. The signature is checked by the mempool and, inside
// the block's proof, by the signature leaf; the block data itself carries no signatures (SPEC 4.12).
//   from public key A  41 B (compressed EcGFp5 point; the sender's address is the Poseidon hash of A)
//   to address         32 B (4 x u64, little-endian)
//   amount, fee, nonce 8 B each, little-endian
//   close              1 B (0 or 1)
//   e (16 B), s (40 B) compact Schnorr signature of the same scheme as tickets: R = s*G - e*A, e = challenge(R, A, msg)
//   msg = Poseidon(chain id, sender address, receiver address, amount, fee, nonce, close)   (main.rs `msg_native`)
// 154 bytes. The nonce must equal the sender's account nonce when the payment is applied; a new account starts at
// (height of its first receipt) << NONCE_SHIFT, so a closed and reopened address cannot replay old payments.
use crate::{ec, mint, F};
use anyhow::{anyhow, bail, Result};
use num_bigint::BigUint;
use plonky2::field::types::{Field, Field64, PrimeField64};
use sha2::{Digest, Sha256};
use std::path::Path;

pub const TX_BYTES: usize = 41 + 32 + 8 + 8 + 8 + 1 + 16 + 40;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SignedPay { pub from_a: [u8; 41], pub to: [F; 4], pub amt: u64, pub fee: u64, pub nonce: u64, pub close: bool, pub e: u128, pub s: [u8; 40] }

pub fn addr_bytes(a: &[F; 4]) -> [u8; 32] { let mut o = [0u8; 32]; for i in 0..4 { o[8 * i..8 * i + 8].copy_from_slice(&a[i].to_canonical_u64().to_le_bytes()); } o }
pub fn addr_key(a: &[F; 4]) -> [u64; 4] { a.map(|x| x.to_canonical_u64()) }

impl SignedPay {
    pub fn to_bytes(&self) -> [u8; TX_BYTES] {
        let mut o = [0u8; TX_BYTES];
        o[..41].copy_from_slice(&self.from_a); o[41..73].copy_from_slice(&addr_bytes(&self.to));
        o[73..81].copy_from_slice(&self.amt.to_le_bytes()); o[81..89].copy_from_slice(&self.fee.to_le_bytes()); o[89..97].copy_from_slice(&self.nonce.to_le_bytes());
        o[97] = self.close as u8; o[98..114].copy_from_slice(&self.e.to_le_bytes()); o[114..].copy_from_slice(&self.s);
        o
    }
    pub fn from_bytes(b: &[u8]) -> Result<SignedPay> {
        if b.len() != TX_BYTES { bail!("payment is {} bytes, not {}", b.len(), TX_BYTES); }
        if b[97] > 1 { bail!("bad close flag"); }
        let to = crate::node::addr_from(b[41..73].try_into()?)?;
        Ok(SignedPay { from_a: b[..41].try_into()?, to, amt: u64::from_le_bytes(b[73..81].try_into()?), fee: u64::from_le_bytes(b[81..89].try_into()?),
                       nonce: u64::from_le_bytes(b[89..97].try_into()?), close: b[97] == 1, e: u128::from_le_bytes(b[98..114].try_into()?), s: b[114..].try_into()? })
    }
    pub fn id(&self) -> [u8; 32] { let mut h = Sha256::new(); h.update(b"Zen-tx-v1"); h.update(self.to_bytes()); h.finalize().into() }
    /// the sender's public point and address (checks the point is in the prime-order group)
    pub fn sender(&self) -> Result<(ec::P, [F; 4])> { let a = mint::decode_point(&self.from_a)?; Ok((a, ec::pk_hash(a))) }
    pub fn message(&self, from: &[F; 4]) -> [F; 4] { crate::msg_native(from, &self.to, self.amt, self.fee, self.nonce, self.close) }
    /// the signature checks out for this payment; returns the sender's point and address
    pub fn verify(&self) -> Result<(ec::P, [F; 4])> {
        let (a, from) = self.sender()?;
        let s = BigUint::from_bytes_le(&self.s);
        if !mint::verify(a, self.message(&from), self.e, &s) { bail!("bad signature"); }
        Ok((a, from))
    }
    /// R = s*G - e*A (what the signature leaf takes as its witness)
    pub fn r_point(&self) -> Result<(ec::P, BigUint)> {
        let (a, _) = self.sender()?;
        let s = BigUint::from_bytes_le(&self.s);
        let r = ec::add(ec::mul_g(&ec::params(), &s), ec::neg(ec::mul(a, &BigUint::from(self.e))));
        Ok((r, s))
    }
}

// ------------------------------------------------------------------ addresses as text
// "zen1" + 64 hex digits of the address + 8 hex digits of a checksum (SHA-256d of the address, first 4 bytes)
fn checksum(a: &[u8; 32]) -> [u8; 4] { let h = Sha256::digest(Sha256::digest(a)); h[..4].try_into().unwrap() }
pub fn address_string(a: &[F; 4]) -> String {
    let b = addr_bytes(a);
    format!("zen1{}{}", hex(&b), hex(&checksum(&b)))
}
pub fn parse_address(s: &str) -> Result<[F; 4]> {
    let s = s.trim().strip_prefix("zen1").ok_or_else(|| anyhow!("an address starts with zen1"))?;
    if s.len() != 72 { bail!("an address has 72 characters after zen1"); }
    let raw = unhex(s)?;
    let (b, c): (&[u8], &[u8]) = raw.split_at(32);
    let b: [u8; 32] = b.try_into()?;
    if checksum(&b) != c { bail!("address checksum does not match (a typo?)"); }
    crate::node::addr_from(&b)
}
fn hex(b: &[u8]) -> String { b.iter().map(|x| format!("{x:02x}")).collect() }
fn unhex(s: &str) -> Result<Vec<u8>> { (0..s.len() / 2).map(|i| Ok(u8::from_str_radix(s.get(2 * i..2 * i + 2).ok_or_else(|| anyhow!("bad hex"))?, 16)?)).collect() }

// ------------------------------------------------------------------ the wallet
/// One key, one address. The key is the same one that signs tickets, so a minter's address is its account.
pub struct Wallet { pub key: mint::Key }
impl Wallet {
    /// secrets are 256 bits (four u64 limbs), as everywhere in the signing code; a larger number is cut to its low 256 bits
    pub fn from_secret(k: BigUint) -> Wallet { Wallet { key: mint::Key::from_secret(k % (BigUint::from(1u8) << 256u32)) } }
    /// a fresh key from the operating system's random source
    pub fn generate() -> Wallet {
        let mut b = [0u8; 32];
        rand::RngCore::fill_bytes(&mut rand::rngs::OsRng, &mut b);
        Wallet::from_secret(BigUint::from_bytes_le(&b))
    }
    pub fn address(&self) -> [F; 4] { self.key.addr }
    pub fn address_string(&self) -> String { address_string(&self.key.addr) }
    /// the secret as 64 hex digits; `save` writes it readable by the owner only
    pub fn secret_hex(&self) -> String { let mut b = self.key.secret_limbs().iter().flat_map(|w| w.to_le_bytes()).collect::<Vec<u8>>(); b.reverse(); hex(&b) }
    pub fn save(&self, path: &Path) -> Result<()> {
        if path.exists() { bail!("{} exists; a wallet file is never overwritten", path.display()); }
        std::fs::write(path, format!("{}\n", self.secret_hex()))?;
        #[cfg(unix)] { use std::os::unix::fs::PermissionsExt; std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o600))?; }
        Ok(())
    }
    pub fn load(path: &Path) -> Result<Wallet> {
        let t = std::fs::read_to_string(path)?;
        let mut b = unhex(t.trim())?; if b.len() != 32 { bail!("a wallet file holds 64 hex digits"); }
        b.reverse();
        Ok(Wallet::from_secret(BigUint::from_bytes_le(&b)))
    }
    /// sign a payment with the given nonce (the sender's account nonce, plus the payments of its own already waiting)
    pub fn pay(&self, to: [F; 4], amt: u64, fee: u64, nonce: u64) -> SignedPay {
        let mut p = SignedPay { from_a: mint::encode_point(self.key.a), to, amt, fee, nonce, close: false, e: 0, s: [0; 40] };
        let (e, s) = mint::sign(&self.key, p.message(&self.key.addr));
        p.e = e; p.s = mint::s_bytes(&s);
        p
    }
    /// the usual fee: 1% of the amount (Jen's standard, SPEC 6.6), at least the smallest allowed
    pub fn standard_fee(amt: u64) -> u64 { amt / 100 + 1 }
}

// ------------------------------------------------------------------ `zenproof wallet ...`
//   wallet new <file>                       make a key, write the secret to <file> (never overwrites), print the address
//   wallet devnet <i> <file>                write the secret of devnet wallet i (funded at genesis) to <file>
//   wallet address <file>
//   wallet web <file> [port]                a wallet page for this key on http://127.0.0.1:<port>/ (default 18470): balances, send
//   wallet balance <file> <node addr>       balance and nonce at the node's best tip
//   wallet pay <file> <node addr> <to address> <amount> [fee]    sign and send (fee defaults to 1% + 1)
pub fn wallet_main() -> Result<()> {
    let a: Vec<String> = std::env::args().collect();
    let arg = |i: usize, what: &str| a.get(i).cloned().ok_or_else(|| anyhow!("usage: wallet <new|devnet|address|balance|pay> ... (missing {what})"));
    match a.get(2).map(|s| s.as_str()) {
        Some("web") => { let port: u16 = a.get(4).map(|p| p.parse()).transpose()?.unwrap_or(18470); return crate::walletweb::run(Path::new(&arg(3, "key file")?), port); }
        Some("new") => { let w = Wallet::generate(); w.save(Path::new(&arg(3, "file")?))?; println!("address {}", w.address_string()); }
        Some("devnet") => {
            let i: usize = arg(3, "index")?.parse()?;
            let k = crate::node::dev::devnet_keys(i + 1).pop().unwrap();
            let w = Wallet { key: k }; w.save(Path::new(&arg(4, "file")?))?; println!("address {}", w.address_string());
        }
        Some("pubkey") => println!("{}", hex(&mint::encode_point(Wallet::load(Path::new(&arg(3, "file")?))?.key.a))),
        Some("address") => println!("{}", Wallet::load(Path::new(&arg(3, "file")?))?.address_string()),
        Some("balance") => {
            let w = Wallet::load(Path::new(&arg(3, "file")?))?;
            let i = crate::p2p::query_account(arg(4, "node")?.parse()?, &w.address())?;
            if i.found { println!("{} | balance {} base units | nonce {} (next {}) | node height {}", w.address_string(), i.balance, i.nonce, i.next_nonce, i.height); }
            else { println!("{} | no account yet | node height {}", w.address_string(), i.height); }
        }
        Some("pay") => {
            let w = Wallet::load(Path::new(&arg(3, "file")?))?;
            let node = arg(4, "node")?.parse()?;
            let to = parse_address(&arg(5, "to address")?)?;
            let amt: u64 = arg(6, "amount")?.parse()?;
            let fee: u64 = match a.get(7) { Some(f) => f.parse()?, None => Wallet::standard_fee(amt) };
            let info = crate::p2p::query_account(node, &w.address())?;
            if !info.found { bail!("this wallet has no account yet"); }
            let p = w.pay(to, amt, fee, info.next_nonce);
            crate::p2p::send_payment(node, &p)?;
            println!("sent {} base units (fee {}) | nonce {} | payment id {}", amt, fee, p.nonce, hex(&p.id()));
        }
        Some(c @ ("orders" | "order-make" | "order-reserve" | "order-bid" | "order-claim" | "order-reopen" | "order-return")) => order_cmd(c, &a)?,
        _ => bail!("usage: wallet <new|devnet|address|balance|pay|orders|order-make|order-reserve|order-claim|order-reopen|order-return> ..."),
    }
    Ok(())
}

// ------------------------------------------------------------------ orders (locks.rs)
//   wallet orders <node>
//   wallet order-make <file> <node> <sell amount> <want chain 1|2|3> <want amount> <pay-to address> [blocks until it expires (1000)] [blocks a reservation lasts (20)]
//   wallet order-reserve <file> <node> <lock address> [taker address (default: this wallet)]
//   wallet order-claim <file> <node> <lock address> <node of the chain that was paid on>
//   wallet order-reopen <file> <node> <lock address>      (after a reservation ran out)
//   wallet order-return <file> <node> <lock address>      (after the order expired)
// <node> is "p2p address,api address" (the API answers on localhost only): 127.0.0.1:18440,127.0.0.1:18460
pub(crate) fn split_node(s: &str) -> Result<(std::net::SocketAddr, String)> {
    let (p, a) = s.split_once(',').ok_or_else(|| anyhow!("give the node as <p2p address>,<api address>"))?;
    Ok((p.parse()?, a.to_string()))
}
pub(crate) fn http_get(api: &str, path: &str) -> Result<serde_json::Value> {
    use std::io::{Read, Write};
    let addr: std::net::SocketAddr = api.parse()?;
    let mut st = std::net::TcpStream::connect_timeout(&addr, std::time::Duration::from_secs(5))?;
    st.set_read_timeout(Some(std::time::Duration::from_secs(20)))?;
    write!(st, "GET {path} HTTP/1.1\r\nHost: {api}\r\nConnection: close\r\n\r\n")?;
    let mut buf = vec![]; st.read_to_end(&mut buf)?;
    let text = String::from_utf8_lossy(&buf);
    let (head, body) = text.split_once("\r\n\r\n").ok_or_else(|| anyhow!("no answer from the API"))?;
    let v: serde_json::Value = serde_json::from_str(body.trim())?;
    if !head.starts_with("HTTP/1.1 200") { bail!("the API said: {}", v["error"].as_str().unwrap_or("?")); }
    Ok(v)
}
fn order_cmd(c: &str, a: &[String]) -> Result<()> {
    use crate::locks::{OpReq, OrderState, SignedOp, Terms};
    let arg = |i: usize, what: &str| a.get(i).cloned().ok_or_else(|| anyhow!("missing {what}"));
    if c == "orders" {
        let (_, api) = split_node(&arg(3, "node")?)?;
        let v = http_get(&api, "/api/orders")?;
        let h = v["orders"].get(0).map_or(0, |o| o["height"].as_u64().unwrap_or(0));
        println!("{} order(s){}", v["count"], if h > 0 { format!(" at height {h}") } else { String::new() });
        for o in v["orders"].as_array().into_iter().flatten() {
            println!("{} | {} | sells {} for {} of {} (pay to {}) | expires at {} | reserve {} blocks, deposit {}{}", o["lock"].as_str().unwrap_or(""), o["state"].as_str().unwrap_or(""),
                     o["sell"], o["want_amount"], o["want_chain_name"].as_str().unwrap_or(""), o["pay_to"].as_str().unwrap_or(""), o["expiry_height"], o["reserve_blocks"], o["deposit"],
                     if o["state"] == "reserved" { format!(" | taker {} until {}", o["taker"].as_str().unwrap_or(""), o["reserved_until"]) } else { String::new() });
        }
        return Ok(());
    }
    let w = Wallet::load(Path::new(&arg(3, "wallet file")?))?;
    let (p2p, api) = split_node(&arg(4, "node")?)?;
    let info = crate::p2p::query_account(p2p, &w.address())?;
    if !info.found { bail!("this wallet has no account yet"); }
    let chain = http_get(&api, "/api/status")?["chain"]["id"].as_u64().unwrap_or(0) as u8;
    let min_fee = { let s = http_get(&api, "/api/status")?["sen_units"].as_u64().unwrap_or(1); (s + 99) / 100 };
    let from = w.address();
    let lock_of = |i: usize| -> Result<([F; 4], serde_json::Value)> {
        let l = parse_address(&arg(i, "lock address")?)?;
        let o = http_get(&api, &format!("/api/order/{}", address_string(&l)))?;
        Ok((l, o))
    };
    let (req, what) = match c {
        "order-make" => {
            let sell: u64 = arg(5, "sell amount")?.parse()?;
            let want_chain: u8 = arg(6, "want chain")?.parse()?;
            let want_amt: u64 = arg(7, "want amount")?.parse()?;
            let pay_to = parse_address(&arg(8, "pay-to address")?)?;
            let expiry_in: u64 = a.get(9).map(|x| x.parse()).transpose()?.unwrap_or(1000);
            let reserve_blocks: u64 = a.get(10).map(|x| x.parse()).transpose()?.unwrap_or(20);
            let terms = Terms::Order { maker: from, sell, want_chain, want_amt, pay_to, expiry: info.height + expiry_in, reserve_blocks, deposit: sell / 100 + 1, salt: 0,
                state: match a.get(11).map(|x| x.parse::<u64>()).transpose()? { Some(w) if w > 0 => OrderState::Auction { window: w }, _ => OrderState::Open } };
            (OpReq::Make { from, amt: sell, fee: Wallet::standard_fee(sell).max(min_fee), terms }, "order made")
        }
        "order-reserve" => {
            let (lock, _) = lock_of(5)?;
            let taker = match a.get(6) { Some(t) => parse_address(t)?, None => from };
            (OpReq::Reserve { from, fee: min_fee.max(1), lock, taker }, "reservation sent")
        }
        "order-bid" => {
            // order-bid <wallet> <node> <lock> <bid> [taker]: a bid in the order's batch auction (the highest escrow wins; a lower bid is paid back)
            let (lock, o) = lock_of(5)?;
            if o["state"] != "auction" && o["state"] != "bidding" { bail!("the order is not open to an auction"); }
            let bid: u64 = arg(6, "bid (escrowed until the trade is done)")?.parse()?;
            let taker = match a.get(7) { Some(t) => parse_address(t)?, None => from };
            (OpReq::Bid { from, fee: min_fee.max(1), lock, taker, bid }, "bid sent")
        }
        "order-claim" => {
            let (lock, o) = lock_of(5)?;
            if o["state"] != "reserved" { bail!("the order is not reserved"); }
            let pay = arg(6, "node of the chain that was paid on")?;
            let pay_api = pay.split_once(',').map_or(pay.as_str(), |x| x.1).to_string();
            let q = format!("/api/find_payment?to={}&min={}&after={}", o["pay_to"].as_str().unwrap_or(""), o["want_amount"], o["reserved_since"]);
            let f = http_get(&pay_api, &q)?;
            if f["found"] != true { bail!("no payment of {} to {} yet on that chain", o["want_amount"], o["pay_to"].as_str().unwrap_or("")); }
            let proof: Vec<u8> = f["proof"].as_str().unwrap_or("").as_bytes().chunks(2).map(|p| u8::from_str_radix(std::str::from_utf8(p).unwrap_or("zz"), 16)).collect::<std::result::Result<_, _>>()?;
            println!("payment found in block {} of that chain ({} blocks deep)", f["block"], f["confirmations"]);
            (OpReq::OrderClaim { from, fee: min_fee.max(1), lock, proof }, "claim sent")
        }
        "order-reopen" => (OpReq::Reopen { from, fee: min_fee.max(1), lock: lock_of(5)?.0 }, "reopen sent"),
        "order-return" => (OpReq::Return { from, fee: min_fee.max(1), lock: lock_of(5)?.0 }, "return sent"),
        _ => unreachable!(),
    };
    let nonce = info.nonce;
    let op = SignedOp::sign(&w.key, chain, nonce, req);
    crate::p2p::send_op(p2p, &op)?;
    println!("{what} | chain {chain} | nonce {nonce} | operation id {}", hex(&op.id()));
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn roundtrip_sign_verify_and_tamper() {
        let w = Wallet::from_secret(BigUint::from(123_456_789u64));
        let to = Wallet::from_secret(BigUint::from(42u64)).address();
        let p = w.pay(to, 5_000_000, 50_000, 7);
        assert_eq!(p.to_bytes().len(), 154);
        let q = SignedPay::from_bytes(&p.to_bytes()).unwrap();
        assert_eq!(p, q);
        let (_, from) = q.verify().unwrap();
        assert_eq!(from, w.address());
        // any changed field breaks the signature
        for f in 0..5 {
            let mut t = p.clone();
            match f { 0 => t.amt += 1, 1 => t.fee += 1, 2 => t.nonce += 1, 3 => t.to[0] += F::ONE, _ => t.close = true }
            assert!(t.verify().is_err(), "field {f} changed but the signature held");
        }
        let mut t = p.clone(); t.s[0] ^= 1; assert!(t.verify().is_err());
        let mut t = p.clone(); t.e ^= 1; assert!(t.verify().is_err());
        // another sender's key cannot sign for this address: swapping the public point fails
        let mut t = p.clone(); t.from_a = mint::encode_point(Wallet::from_secret(BigUint::from(9u64)).key.a); assert!(t.verify().is_err());
        assert!(SignedPay::from_bytes(&p.to_bytes()[..100]).is_err());
        // R as the signature leaf will take it
        let (r, s) = q.r_point().unwrap();
        let e = ec::challenge(r, q.sender().unwrap().0, q.message(&w.address()));
        assert_eq!(e, BigUint::from(q.e)); assert!(s < ec::n_order());
    }
    #[test]
    fn addresses_and_wallet_files() {
        let w = Wallet::from_secret(BigUint::from(777u64));
        let s = w.address_string();
        assert_eq!(s.len(), 4 + 64 + 8);
        assert_eq!(parse_address(&s).unwrap(), w.address());
        let mut bad = s.clone().into_bytes(); bad[10] = if bad[10] == b'0' { b'1' } else { b'0' };
        assert!(parse_address(std::str::from_utf8(&bad).unwrap()).is_err());
        assert!(parse_address("zen1abcd").is_err());
        let dir = std::env::temp_dir().join(format!("zen-wallet-{}", std::process::id()));
        let _ = std::fs::remove_file(&dir);
        w.save(&dir).unwrap();
        assert!(w.save(&dir).is_err(), "never overwrites");
        let l = Wallet::load(&dir).unwrap();
        assert_eq!(l.address(), w.address());
        std::fs::remove_file(&dir).unwrap();
        let g = Wallet::generate(); assert_ne!(g.address(), Wallet::generate().address());
        // a generated key survives the file (256-bit secrets) and still signs
        let f = std::env::temp_dir().join(format!("zen-wallet-g-{}", std::process::id()));
        let _ = std::fs::remove_file(&f);
        g.save(&f).unwrap();
        let gl = Wallet::load(&f).unwrap(); std::fs::remove_file(&f).unwrap();
        assert_eq!(gl.address(), g.address());
        assert!(gl.pay(w.address(), 1_000_000, 10_001, 0).verify().is_ok());
    }
}
