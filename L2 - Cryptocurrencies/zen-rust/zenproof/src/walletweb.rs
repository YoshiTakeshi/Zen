//! `zenproof wallet web <key file> [port]`: a small wallet page for one key file, on this computer only.
//!   GET  /            the page
//!   GET  /w/info      the address and the balance on each chain (asks the three nodes on this computer)
//!   POST /w/pay       {"chain":0|1|2,"to":"zen1...","amount":"<grams>"}  signs with the key file and sends (needs the page's token)
//! The key never leaves this program. It listens on 127.0.0.1 only, answers only to the names localhost / 127.0.0.1 with its own port, and
//! a payment needs a random token that is put into the page when it is served, so another web page in the browser cannot make it pay.
use anyhow::{anyhow, bail, Result};
use serde_json::{json, Value};
use std::io::{Read, Write};
use std::net::{SocketAddr, TcpListener, TcpStream};
use std::path::Path;
use std::time::Duration;
use crate::tx::{parse_address, Wallet};

const PAGE: &str = include_str!("ui/wallet.html");
const UNITS_PER_GRAM: u128 = 1_000_000_000;
const BLOCK_SECS: [u64; 3] = [900, 300, 150];

/// "0.25" grams -> base units (nanograms), exactly, no floats; at most 9 decimals
pub fn grams_to_units(s: &str) -> Result<u64> {
    let s = s.trim();
    let (w, f) = s.split_once('.').unwrap_or((s, ""));
    if w.is_empty() && f.is_empty() { bail!("give an amount"); }
    if !w.chars().all(|c| c.is_ascii_digit()) || !f.chars().all(|c| c.is_ascii_digit()) { bail!("the amount is a number of grams, like 0.5"); }
    if f.len() > 9 { bail!("at most 9 decimals (a base unit is a nanogram)"); }
    let w: u128 = if w.is_empty() { 0 } else { w.parse().map_err(|_| anyhow!("amount too large"))? };
    let f: u128 = if f.is_empty() { 0 } else { format!("{f:0<9}").parse()? };
    let u = w.checked_mul(UNITS_PER_GRAM).and_then(|x| x.checked_add(f)).ok_or_else(|| anyhow!("amount too large"))?;
    if u == 0 { bail!("the amount is zero"); }
    u64::try_from(u).map_err(|_| anyhow!("amount too large"))
}

struct Req { method: String, path: String, host: String, token: String, body: Vec<u8> }

fn read_request(s: &mut TcpStream) -> Result<Req> {
    let mut buf = Vec::new(); let mut chunk = [0u8; 2048];
    let end = loop {
        if let Some(p) = buf.windows(4).position(|w| w == b"\r\n\r\n") { break p + 4; }
        if buf.len() > 16384 { bail!("request too large"); }
        let n = s.read(&mut chunk)?; if n == 0 { bail!("closed"); }
        buf.extend_from_slice(&chunk[..n]);
    };
    let head = String::from_utf8_lossy(&buf[..end]).to_string();
    let mut lines = head.lines();
    let first = lines.next().unwrap_or("");
    let mut it = first.split_whitespace();
    let (method, path) = (it.next().unwrap_or("").to_string(), it.next().unwrap_or("").to_string());
    let (mut host, mut token, mut len) = (String::new(), String::new(), 0usize);
    for l in lines {
        if let Some((k, v)) = l.split_once(':') {
            match k.trim().to_ascii_lowercase().as_str() {
                "host" => host = v.trim().to_string(),
                "x-zen-token" => token = v.trim().to_string(),
                "content-length" => len = v.trim().parse().unwrap_or(0),
                _ => {}
            }
        }
    }
    if len > 4096 { bail!("body too large"); }
    while buf.len() < end + len { let n = s.read(&mut chunk)?; if n == 0 { bail!("closed"); } buf.extend_from_slice(&chunk[..n]); }
    Ok(Req { method, path, host, token, body: buf[end..end + len].to_vec() })
}

fn respond(mut s: &TcpStream, code: u16, ctype: &str, body: &str) {
    let reason = match code { 200 => "OK", 400 => "Bad Request", 401 => "Unauthorized", 403 => "Forbidden", 404 => "Not Found", _ => "Error" };
    let _ = write!(s, "HTTP/1.1 {code} {reason}\r\nContent-Type: {ctype}\r\nContent-Length: {}\r\nCache-Control: no-store\r\nX-Content-Type-Options: nosniff\r\nContent-Security-Policy: default-src 'self' 'unsafe-inline'; connect-src 'self'\r\nConnection: close\r\n\r\n{body}", body.len());
}

fn same_token(a: &str, b: &str) -> bool {
    a.len() == b.len() && a.bytes().zip(b.bytes()).fold(0u8, |d, (x, y)| d | (x ^ y)) == 0
}

struct App { wallet: Wallet, base: u16, port: u16, token: String }

impl App {
    fn node(&self, chain: usize) -> SocketAddr { SocketAddr::from(([127, 0, 0, 1], self.base + chain as u16)) }
    fn info(&self) -> Value {
        let chains: Vec<Value> = (0..3).map(|i| match crate::p2p::query_account(self.node(i), &self.wallet.address()) {
            Ok(a) => json!({"found": a.found, "balance": a.balance, "nonce": a.nonce, "height": a.height}),
            Err(e) => json!({"error": e.to_string()}),
        }).collect();
        json!({"address": self.wallet.address_string(), "base": self.base, "chains": chains})
    }
    fn pay(&self, body: &[u8]) -> Result<Value> {
        let v: Value = serde_json::from_slice(body).map_err(|_| anyhow!("bad request"))?;
        let chain = v["chain"].as_u64().filter(|c| *c < 3).ok_or_else(|| anyhow!("choose a chain"))? as usize;
        let to = parse_address(v["to"].as_str().unwrap_or(""))?;
        let amt = grams_to_units(v["amount"].as_str().unwrap_or(""))?;
        let fee = Wallet::standard_fee(amt);
        let node = self.node(chain);
        let info = crate::p2p::query_account(node, &self.wallet.address()).map_err(|_| anyhow!("the node on this chain is not reachable (is it running?)"))?;
        if !info.found { bail!("this wallet has no account on this chain yet: receive some coins first"); }
        if info.balance < amt.saturating_add(fee) { bail!("not enough: you have {} base units, this needs {} (amount plus fee)", info.balance, amt.saturating_add(fee)); }
        let p = self.wallet.pay(to, amt, fee, info.next_nonce);
        crate::p2p::send_payment(node, &p)?;
        Ok(json!({"sent": amt, "fee": fee, "wait": BLOCK_SECS[chain]}))
    }
    fn handle(&self, mut s: TcpStream) {
        let _ = s.set_read_timeout(Some(Duration::from_secs(10))); let _ = s.set_write_timeout(Some(Duration::from_secs(10)));
        let Ok(r) = read_request(&mut s) else { return respond(&s, 400, "application/json", "{\"error\":\"bad request\"}") };
        let ok_host = r.host == format!("127.0.0.1:{}", self.port) || r.host == format!("localhost:{}", self.port);
        if !ok_host { return respond(&s, 403, "application/json", "{\"error\":\"this wallet answers only to localhost\"}"); }
        match (r.method.as_str(), r.path.as_str()) {
            ("GET", "/") | ("GET", "/index.html") => respond(&s, 200, "text/html; charset=utf-8", &PAGE.replace("__TOKEN__", &self.token)),
            ("GET", "/w/info") => respond(&s, 200, "application/json", &self.info().to_string()),
            ("POST", "/w/pay") => {
                if !same_token(&r.token, &self.token) { return respond(&s, 401, "application/json", "{\"error\":\"reload the page\"}"); }
                match self.pay(&r.body) {
                    Ok(v) => respond(&s, 200, "application/json", &v.to_string()),
                    Err(e) => respond(&s, 400, "application/json", &json!({"error": e.to_string()}).to_string()),
                }
            }
            _ => respond(&s, 404, "application/json", "{\"error\":\"not found\"}"),
        }
    }
}

pub fn run(key: &Path, port: u16) -> Result<()> {
    let base: u16 = std::env::var("ZEN_BASE_PORT").ok().and_then(|v| v.parse().ok()).unwrap_or(18440);
    let wallet = Wallet::load(key)?;
    let token = crate::api::new_token();
    let l = TcpListener::bind(("127.0.0.1", port))?;
    println!("Zen wallet for {}\nopen http://127.0.0.1:{port}/ in your browser (Ctrl+C to stop)", wallet.address_string());
    let app = std::sync::Arc::new(App { wallet, base, port, token });
    for s in l.incoming().flatten() { let a = app.clone(); std::thread::spawn(move || a.handle(s)); }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn grams_become_exact_base_units() {
        assert_eq!(grams_to_units("1").unwrap(), 1_000_000_000);
        assert_eq!(grams_to_units("0.5").unwrap(), 500_000_000);
        assert_eq!(grams_to_units("0.000000001").unwrap(), 1);
        assert_eq!(grams_to_units(" 12.34 ").unwrap(), 12_340_000_000);
        for bad in ["", ".", "0", "0.0", "-1", "1e3", "1.0000000001", "abc", "99999999999999999999"] { assert!(grams_to_units(bad).is_err(), "{bad}"); }
    }
    #[test]
    fn the_token_compare_is_exact() { assert!(same_token("abc", "abc")); assert!(!same_token("abc", "abd")); assert!(!same_token("abc", "ab")); }
}
