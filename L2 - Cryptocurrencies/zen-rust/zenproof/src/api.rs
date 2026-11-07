//! The node's local HTTP API (Justus L. Ludovic).
//!
//! JSON over plain HTTP/1.1 for the programs that sit beside the node: a block explorer, an operator dashboard, a wallet. It is not a public
//! service: it binds to a loopback address only, answers only requests whose Host header names this machine (so a web page cannot reach it
//! through DNS rebinding), sends no CORS headers (another site cannot read the answers in a browser), and takes a payment only from a caller
//! that holds the access token. Everything it shows is public chain data; nothing it does can touch a key or a block.
//!
//!   GET  /api/status                  chain, height, tip, difficulty, S, supply, peers, mempool
//!   GET  /api/blocks?limit=&before=   block summaries, newest first (limit up to 100, `before` is a height)
//!   GET  /api/block/<height|hash>     one block (hash: 64 hex digits)
//!   GET  /api/account/<zen1...>       balance, nonce and the nonce the next payment must carry
//!   GET  /api/mempool?limit=          payments waiting, best fee rate first
//!   GET  /api/peers                   connected peers
//!   POST /api/pay  {"tx":"<hex>"}     submit a signed payment (needs `Authorization: Bearer <token>`)
//! Amounts are base units (nanograms); `*_g` fields give the same in grams with nine decimals.
use crate::node::Block;
use crate::p2p::Net;
use crate::reward::{self, Metal};
use crate::tx::{address_string, parse_address, SignedPay, TX_BYTES};
use anyhow::{anyhow, bail, Result};
use serde_json::{json, Value};
use std::io::{Read, Write};
use std::net::{SocketAddr, TcpListener, TcpStream};
use std::path::Path;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::Duration;

const MAX_CONNS: usize = 32;
const MAX_HEAD: usize = 16 * 1024;
const MAX_BODY: usize = 200 * 1024;   // an order claim carries a block as proof
const IO_TIMEOUT: Duration = Duration::from_secs(5);
const MAX_LIST: usize = 100;

fn hex(b: &[u8]) -> String { b.iter().map(|x| format!("{x:02x}")).collect() }
fn unhex(s: &str) -> Result<Vec<u8>> {
    if s.len() % 2 != 0 || !s.is_ascii() { bail!("bad hex"); }
    (0..s.len() / 2).map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).map_err(|_| anyhow!("bad hex"))).collect()
}
/// base units (nanograms) as grams, exactly, with nine decimals
pub fn grams(units: u64) -> String { format!("{}.{:09}", units / 1_000_000_000, units % 1_000_000_000) }
fn chain_name(chain: u8) -> (&'static str, &'static str) { match chain { 1 => ("Yen", "gold"), 2 => ("Ken", "silver"), _ => ("Jen", "copper") } }

/// a fresh access token: 32 random bytes as hex
pub fn new_token() -> String { let mut b = [0u8; 32]; rand::RngCore::fill_bytes(&mut rand::rngs::OsRng, &mut b); hex(&b) }
/// the token kept in `<dir>/api.token` (made, readable by the owner only, when it is not there yet); without a directory a fresh one
pub fn load_or_create_token(dir: Option<&Path>) -> Result<String> {
    let Some(d) = dir else { return Ok(new_token()) };
    let path = d.join("api.token");
    if let Ok(t) = std::fs::read_to_string(&path) { let t = t.trim().to_string(); if t.len() == 64 && unhex(&t).is_ok() { return Ok(t); } }
    let t = new_token();
    std::fs::create_dir_all(d)?;
    std::fs::write(&path, format!("{t}\n"))?;
    #[cfg(unix)] { use std::os::unix::fs::PermissionsExt; std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o600))?; }
    Ok(t)
}

/// listen on a loopback address and serve in the background; returns the address (useful with port 0)
pub fn start(net: Net, addr: &str, token: String) -> Result<SocketAddr> {
    let sa: SocketAddr = addr.parse().map_err(|_| anyhow!("bad API address {addr}"))?;
    // a container has to listen on its own network address for a published port to reach it: ZEN_API_BIND_ANY=1 says the operator keeps the
    // outside safe (publish the port on the host's loopback, or put a gateway in front); the token still guards every write
    let any_ok = std::env::var("ZEN_API_BIND_ANY").map_or(false, |v| v == "1");
    if !sa.ip().is_loopback() && !any_ok { bail!("the API listens on a loopback address only, not {} (set ZEN_API_BIND_ANY=1 inside a container)", sa.ip()); }
    let l = TcpListener::bind(sa)?;
    let local = l.local_addr()?;
    let live = Arc::new(AtomicUsize::new(0));
    let token = Arc::new(token);
    std::thread::spawn(move || {
        for s in l.incoming().flatten() {
            if live.fetch_add(1, Ordering::SeqCst) >= MAX_CONNS {
                live.fetch_sub(1, Ordering::SeqCst);
                let _ = respond(&s, 503, &json!({"error": "too many connections"}));
                continue;
            }
            let (net, token, live) = (net.clone(), token.clone(), live.clone());
            std::thread::spawn(move || { let _ = serve(&net, &token, local.port(), s); live.fetch_sub(1, Ordering::SeqCst); });
        }
    });
    Ok(local)
}

const INDEX_HTML: &str = include_str!("ui/index.html");
const APP_CSS: &str = include_str!("ui/app.css");
const APP_JS: &str = include_str!("ui/app.js");
/// the explorer page: three files served from the binary. The page may load only its own script and style, and talk only to this API.
fn asset(path: &str) -> Option<(&'static str, &'static str)> {
    match path {
        "/" | "/index.html" => Some(("text/html; charset=utf-8", INDEX_HTML)),
        "/app.css" => Some(("text/css; charset=utf-8", APP_CSS)),
        "/app.js" => Some(("text/javascript; charset=utf-8", APP_JS)),
        _ => None,
    }
}
fn respond_asset(mut s: &TcpStream, ctype: &str, body: &str) -> std::io::Result<()> {
    let head = format!("HTTP/1.1 200 OK\r\nContent-Type: {ctype}\r\nContent-Length: {}\r\nCache-Control: no-store\r\nX-Content-Type-Options: nosniff\r\nX-Frame-Options: DENY\r\nReferrer-Policy: no-referrer\r\n\
Content-Security-Policy: default-src 'none'; script-src 'self'; style-src 'self'; connect-src 'self'; img-src 'self'; base-uri 'none'; form-action 'none'; frame-ancestors 'none'\r\nConnection: close\r\n\r\n", body.len());
    s.write_all(head.as_bytes())?; s.write_all(body.as_bytes())
}

fn respond(mut s: &TcpStream, code: u16, body: &Value) -> std::io::Result<()> {
    let text = match code { 200 => "OK", 400 => "Bad Request", 401 => "Unauthorized", 403 => "Forbidden", 404 => "Not Found", 405 => "Method Not Allowed",
                            413 => "Payload Too Large", 431 => "Request Header Fields Too Large", 503 => "Service Unavailable", _ => "Error" };
    let b = body.to_string();
    let head = format!("HTTP/1.1 {code} {text}\r\nContent-Type: application/json\r\nContent-Length: {}\r\nCache-Control: no-store\r\nX-Content-Type-Options: nosniff\r\nConnection: close\r\n\r\n", b.len());
    s.write_all(head.as_bytes())?; s.write_all(b.as_bytes())
}

struct Req { method: String, path: String, query: Vec<(String, String)>, host: String, auth: String, body: Vec<u8> }

fn read_request(s: &mut TcpStream) -> Result<Req, (u16, &'static str)> {
    let mut buf = vec![];
    let mut tmp = [0u8; 2048];
    let end = loop {
        if let Some(i) = buf.windows(4).position(|w| w == b"\r\n\r\n") { break i; }
        if buf.len() > MAX_HEAD { return Err((431, "request head too large")); }
        let n = s.read(&mut tmp).map_err(|_| (400, "could not read the request"))?;
        if n == 0 { return Err((400, "connection closed")); }
        buf.extend_from_slice(&tmp[..n]);
    };
    let head = std::str::from_utf8(&buf[..end]).map_err(|_| (400, "request is not text"))?;
    let mut lines = head.split("\r\n");
    let first = lines.next().ok_or((400, "empty request"))?;
    let mut parts = first.split(' ');
    let (method, target, version) = (parts.next().unwrap_or(""), parts.next().unwrap_or(""), parts.next().unwrap_or(""));
    if !version.starts_with("HTTP/1.") || parts.next().is_some() { return Err((400, "not an HTTP/1 request")); }
    let (mut host, mut auth, mut clen) = (String::new(), String::new(), 0usize);
    for l in lines {
        let Some((k, v)) = l.split_once(':') else { return Err((400, "bad header")) };
        match k.trim().to_ascii_lowercase().as_str() {
            "host" => host = v.trim().to_string(),
            "authorization" => auth = v.trim().to_string(),
            "content-length" => clen = v.trim().parse().map_err(|_| (400, "bad content-length"))?,
            "transfer-encoding" => return Err((400, "chunked bodies are not accepted")),
            _ => {}
        }
    }
    if clen > MAX_BODY { return Err((413, "body too large")); }
    let mut body = buf[end + 4..].to_vec();
    if body.len() > clen { body.truncate(clen); }
    while body.len() < clen {
        let n = s.read(&mut tmp).map_err(|_| (400, "could not read the body"))?;
        if n == 0 { return Err((400, "body ends early")); }
        body.extend_from_slice(&tmp[..n]);
        if body.len() > clen { body.truncate(clen); }
    }
    let (path, q) = target.split_once('?').unwrap_or((target, ""));
    let query = q.split('&').filter(|x| !x.is_empty()).map(|kv| { let (k, v) = kv.split_once('=').unwrap_or((kv, "")); (k.to_string(), v.to_string()) }).collect();
    Ok(Req { method: method.to_string(), path: path.to_string(), query, host, auth, body })
}

/// the Host header names this machine and this port (anything else could be a web page reaching us through a name it controls)
fn host_ok(host: &str, port: u16) -> bool {
    let h = host.to_ascii_lowercase();
    // more names this API may be reached by (a gateway, a cluster name): ZEN_API_HOSTS=name1,name2
    let extra = std::env::var("ZEN_API_HOSTS").unwrap_or_default().to_ascii_lowercase();
    ["localhost", "127.0.0.1", "[::1]"].iter().copied().chain(extra.split(',').map(str::trim).filter(|x| !x.is_empty())).any(|n| h == *n || h == format!("{n}:{port}"))
}
fn token_ok(auth: &str, token: &str) -> bool {
    let Some(t) = auth.strip_prefix("Bearer ") else { return false };
    let (a, b) = (t.trim().as_bytes(), token.as_bytes());
    a.len() == b.len() && a.iter().zip(b).fold(0u8, |d, (x, y)| d | (x ^ y)) == 0
}

fn serve(net: &Net, token: &str, port: u16, mut s: TcpStream) -> std::io::Result<()> {
    s.set_read_timeout(Some(IO_TIMEOUT))?; s.set_write_timeout(Some(IO_TIMEOUT))?;
    let req = match read_request(&mut s) { Ok(r) => r, Err((c, m)) => return respond(&s, c, &json!({"error": m})) };
    if !host_ok(&req.host, port) { return respond(&s, 403, &json!({"error": "this API answers only to localhost"})); }
    if req.method == "GET" { if let Some((ctype, body)) = asset(&req.path) { return respond_asset(&s, ctype, body); } }
    let (code, body) = route(net, token, &req);
    respond(&s, code, &body)
}

fn route(net: &Net, token: &str, r: &Req) -> (u16, Value) {
    let seg: Vec<&str> = r.path.trim_matches('/').split('/').collect();
    let q = |k: &str| r.query.iter().find(|(a, _)| a == k).map(|(_, v)| v.as_str());
    let res: Result<Value, (u16, String)> = (|| {
        match (r.method.as_str(), seg.as_slice()) {
            ("GET", ["api"]) => Ok(json!({"name": "zen node API", "endpoints": ["GET /api/status", "GET /api/blocks?limit=&before=", "GET /api/block/<height|hash>",
                "GET /api/account/<zen1...>", "GET /api/mempool?limit=", "GET /api/peers", "GET /api/chains", "GET /api/orders", "GET /api/rate", "GET /api/fills", "GET /api/channels?addr=", "GET /api/order/<lock address>", "GET /api/find_payment?to=&min=&after=", "POST /api/op {\"op\":\"<hex>\"} (Bearer token)", "POST /api/pay {\"tx\":\"<hex>\"} (Bearer token)"]})),
            ("GET", ["api", "status"]) => Ok(status(net)),
            ("GET", ["api", "chains"]) => Ok(match net.chains.lock().unwrap().as_ref() { Some(f) => f(), None => json!([]) }),
            ("GET", ["api", "blocks"]) => {
                let limit = q("limit").map_or(Ok(20), |v| v.parse::<usize>()).map_err(|_| (400, "bad limit".to_string()))?.clamp(1, MAX_LIST);
                let before = q("before").map(|v| v.parse::<u64>()).transpose().map_err(|_| (400, "bad before".to_string()))?;
                Ok(blocks(net, limit, before))
            }
            ("GET", ["api", "block", id]) => block(net, id).ok_or((404, "no such block".to_string())),
            ("GET", ["api", "account", a]) => {
                let addr = parse_address(a).map_err(|e| (400, e.to_string()))?;
                Ok(account(net, &addr))
            }
            ("GET", ["api", "mempool"]) => {
                let limit = q("limit").map_or(Ok(50), |v| v.parse::<usize>()).map_err(|_| (400, "bad limit".to_string()))?.clamp(1, MAX_LIST);
                Ok(mempool(net, limit))
            }
            ("GET", ["api", "peers"]) => Ok(peers(net)),
            ("GET", ["api", "orders"]) => Ok(orders(net, None)),
            ("GET", ["api", "rate"]) => { let n = net.node.lock().unwrap(); let c = n.tip(); Ok(crate::market::fills_json(&c.fills, c.height)) }
            ("GET", ["api", "fills"]) => { let n = net.node.lock().unwrap(); let c = n.tip(); Ok(json!({"count": c.fills.len(), "fills": c.fills.iter().rev().take(50).map(|f| json!({"height": f.height, "sell": f.sell, "want_chain": f.want_chain, "want_amount": f.want_amt, "price": crate::market::price_of(f).to_string()})).collect::<Vec<_>>()})) }
            ("GET", ["api", "channels"]) => {
                let who = q("addr").map(|a| parse_address(a)).transpose().map_err(|e| (400, e.to_string()))?;
                Ok(channels(net, who))
            }
            ("GET", ["api", "order", a]) => {
                let addr = parse_address(a).map_err(|e| (400, e.to_string()))?;
                let v = orders(net, Some(addr));
                if v["orders"].as_array().map_or(true, |l| l.is_empty()) { Err((404, "no such order".to_string())) } else { Ok(v["orders"][0].clone()) }
            }
            ("GET", ["api", "find_payment"]) => {
                let to = parse_address(q("to").ok_or((400, "give to=<address>".to_string()))?).map_err(|e| (400, e.to_string()))?;
                let min = q("min").map_or(Ok(1), |v| v.parse::<u64>()).map_err(|_| (400, "bad min".to_string()))?;
                let after = q("after").map_or(Ok(0), |v| v.parse::<u32>()).map_err(|_| (400, "bad after".to_string()))?;
                let n = net.node.lock().unwrap();
                match n.find_payment(&to, min, after, 5000) {
                    None => Ok(json!({"found": false, "height": n.tip().height})),
                    Some((h, e)) => {
                        let pr = n.payment_proof(h, e).map_err(|e| (500, e.to_string()))?;
                        Ok(json!({"found": true, "chain": n.tip().p.chain, "block": h, "entry": e, "confirmations": n.tip().height - h, "proof": hex(&pr.encode()), "height": n.tip().height}))
                    }
                }
            }
            ("POST", ["api", "op"]) => {
                if !token_ok(&r.auth, token) { return Err((401, "an operation needs the access token (Authorization: Bearer ...)".to_string())); }
                let v: Value = serde_json::from_slice(&r.body).map_err(|_| (400, "the body is not JSON".to_string()))?;
                let h = v.get("op").and_then(|t| t.as_str()).ok_or((400, "give {\"op\": \"<hex of the signed operation>\"}".to_string()))?;
                let o = crate::locks::SignedOp::from_bytes(&unhex(h).map_err(|e| (400, e.to_string()))?).map_err(|e| (400, e.to_string()))?;
                let id = o.id();
                net.submit_op(o, None).map_err(|e| (400, e.to_string()))?;
                Ok(json!({"ok": true, "id": hex(&id)}))
            }
            ("POST", ["api", "pay"]) => {
                if !token_ok(&r.auth, token) { return Err((401, "a payment needs the access token (Authorization: Bearer ...)".to_string())); }
                pay(net, &r.body)
            }
            (m, ["api", ..]) | (m, [""]) if m != "GET" && m != "POST" => Err((405, "only GET and POST".to_string())),
            _ => Err((404, "no such endpoint".to_string())),
        }
    })();
    match res { Ok(v) => (200, v), Err((c, m)) => (c, json!({"error": m})) }
}

fn status(net: &Net) -> Value {
    let n = net.node.lock().unwrap();
    let c = n.tip();
    let (name, metal) = chain_name(c.p.chain);
    let held: u64 = c.pending.values().flatten().map(|(_, v)| *v).sum();
    let next_curve = reward::raw_pico(Metal::of_chain(c.p.chain), c.height + 1) / reward::PICO_PER_UNIT;
    let reorgs: Vec<u64> = n.reorgs.iter().rev().take(10).copied().collect();
    let (peers_n, known) = (net.peer_count(), net.known_addr_count());
    let mempool = net.pool.lock().unwrap().len();
    json!({
        "version": env!("CARGO_PKG_VERSION"),
        "chain": {"id": c.p.chain, "name": name, "metal": metal},
        "height": c.height, "tip": hex(&c.tip), "tip_time": c.tip_ntime, "now": crate::p2p::now(),
        "seal_bits": format!("{:08x}", c.bits), "blow_difficulty": c.blow_diff, "total_work": c.total_work.to_string(),
        "block_secs": c.p.block_secs, "maturity_blocks": c.p.maturity,
        "unit": "nanogram", "sen_units": c.reading.s,
        "fee_pool": c.pool, "fee_pool_g": grams(c.pool),
        "supply": {"genesis": c.genesis_supply, "issued": c.emitted, "held_rewards": held, "genesis_g": grams(c.genesis_supply), "issued_g": grams(c.emitted), "held_rewards_g": grams(held)},
        "next_block_curve_reward": next_curve, "next_block_curve_reward_g": grams(next_curve),
        "state_root": hex(&c.root().iter().flat_map(|x| x.to_le_bytes()).collect::<Vec<u8>>()),
        "mempool": mempool, "peers": peers_n, "known_addresses": known,
        "recent_reorg_depths": reorgs, "started_from_snapshot": n.from_snapshot,
    })
}

fn block_json(blk: &Block, main: bool) -> Value {
    let pv = &blk.pubvalues;
    let hash = blk.hash();
    json!({
        "height": pv[15], "hash": hex(&hash), "prev": hex(&blk.header.prev), "main_chain": main,
        "time": blk.header.ntime, "version": blk.header.version, "bits": format!("{:08x}", blk.header.nbits), "nonce": blk.header.nonce,
        "payments": pv[9], "fees": pv[8], "fees_g": grams(pv[8]), "sen_units": pv[14], "tickets": blk.tickets.len(),
        "state_root": hex(&pv[4..8].iter().flat_map(|x| x.to_le_bytes()).collect::<Vec<u8>>()),
        "stamp_bytes": blk.stamp.len(), "data_bytes": blk.data.len(), "size_bytes": blk.encode().len(), "coinbase": hex(&blk.coinbase),
    })
}
fn blocks(net: &Net, limit: usize, before: Option<u64>) -> Value {
    let n = net.node.lock().unwrap();
    let top = n.tip().height;
    let start = before.map_or(top, |b| b.saturating_sub(1).min(top));
    let mut out = vec![];
    if before != Some(0) {
        let mut h = start as i64;
        while h >= 1 && out.len() < limit {
            if let Some(b) = n.hash_at(h as u64).and_then(|x| n.block(&x)) { out.push(block_json(&b, true)); }
            h -= 1;
        }
    }
    json!({"height": top, "blocks": out})
}
fn block(net: &Net, id: &str) -> Option<Value> {
    let n = net.node.lock().unwrap();
    if id.len() == 64 {
        let h: [u8; 32] = unhex(id).ok()?.try_into().ok()?;
        let b = n.block(&h)?;
        return Some(block_json(&b, n.main_height_of(&h).is_some()));
    }
    let height: u64 = id.parse().ok()?;
    if height == 0 || height > n.tip().height { return None; }
    let h = n.hash_at(height)?;
    Some(block_json(&n.block(&h)?, true))
}
fn account(net: &Net, addr: &[crate::F; 4]) -> Value {
    let n = net.node.lock().unwrap();
    let c = n.tip();
    let (found, bal, nonce) = c.account(addr).map_or((false, 0, 0), |(_, a)| (true, a.bal, a.nonce));
    let next = net.pool.lock().unwrap().next_nonce(c, addr);
    json!({"address": address_string(addr), "found": found, "balance": bal, "balance_g": grams(bal), "nonce": nonce, "next_nonce": next.unwrap_or(nonce), "height": c.height})
}
fn mempool(net: &Net, limit: usize) -> Value {
    let p = net.pool.lock().unwrap();
    let list: Vec<Value> = p.list(limit).into_iter().map(|(id, t, from)| json!({"id": hex(&id), "from": address_string(&from), "to": address_string(&t.to), "amount": t.amt,
        "amount_g": grams(t.amt), "fee": t.fee, "fee_g": grams(t.fee), "nonce": t.nonce, "close": t.close})).collect();
    json!({"count": p.len(), "shown": list.len(), "payments": list})
}
/// the orders on this chain (or the one at `only`, by its address now): terms, state, what a taker or the maker needs next
fn orders(net: &Net, only: Option<[crate::F; 4]>) -> Value {
    use crate::locks::{OrderState, Terms};
    let n = net.node.lock().unwrap();
    let c = n.tip();
    let mut list: Vec<(u64, Value)> = vec![];
    for (idx, t) in c.locks.iter() {
        let Terms::Order { maker, sell, want_chain, want_amt, pay_to, expiry, reserve_blocks, deposit, salt, state } = t else { continue };
        let Some(a) = c.state.get(idx) else { continue };
        if only.map_or(false, |o| o != a.pk) { continue; }
        let (name, _) = chain_name(*want_chain);
        let (st, taker, until, since, best_bid, close) = match state {
            OrderState::Open => ("open", None, 0, 0, 0, 0),
            OrderState::Reserved { taker, until, since } => ("reserved", Some(address_string(taker)), *until, *since, 0, 0),
            OrderState::Auction { .. } => ("auction", None, 0, 0, 0, 0),
            OrderState::Bidding { taker, bid, close, since, .. } if c.height <= *close => ("bidding", Some(address_string(taker)), 0, *since, *bid, *close),
            OrderState::Bidding { taker, bid, close, since, .. } => ("reserved", Some(address_string(taker)), *close + reserve_blocks, *since, *bid, *close),
        };
        list.push((*salt, json!({"lock": address_string(&a.pk), "state": st, "maker": address_string(maker), "sell": sell, "sell_g": grams(*sell), "balance": a.bal,
            "want_chain": want_chain, "want_chain_name": name, "want_amount": want_amt, "want_amount_g": grams(*want_amt), "pay_to": address_string(pay_to),
            "expiry_height": expiry, "reserve_blocks": reserve_blocks, "deposit": deposit, "taker": taker, "reserved_until": until, "reserved_since": since, "best_bid": best_bid, "auction_close": close,
            "salt": salt, "height": c.height, "min_fee": (c.reading.s as u64 + 99) / 100 })));
    }
    list.sort_by_key(|(s, _)| *s);
    json!({"count": list.len(), "orders": list.into_iter().map(|(_, v)| v).collect::<Vec<_>>()})
}
/// the channels on this chain (those of one account when `who` is given): the terms an off-chain wallet needs, and what the chain holds now
fn channels(net: &Net, who: Option<[crate::F; 4]>) -> Value {
    use crate::locks::{ChanState, Terms};
    let n = net.node.lock().unwrap();
    let c = n.tip();
    let mut list: Vec<(u64, Value)> = vec![];
    for (idx, t) in c.locks.iter() {
        let Terms::Channel { a, b, key_a, key_b, delay, oneway, salt, state } = t else { continue };
        if who.map_or(false, |w| w != *a && w != *b) { continue; }
        let Some(acct) = c.state.get(idx) else { continue };
        let (st, seq, bal_a, until, plocks) = match state { ChanState::Open => ("open", 0, acct.bal, 0, vec![]), ChanState::OpenDual { base_a } => ("open", 0, *base_a, 0, vec![]), ChanState::Closing { seq, bal_a, until, locks } => ("closing", *seq, *bal_a, *until, locks.clone()) };
        list.push((*salt, json!({"id": hex(&t.channel_id().unwrap()), "lock": address_string(&acct.pk), "a": address_string(a), "b": address_string(b), "key_a": hex(key_a), "key_b": hex(key_b),
            "capacity": acct.bal, "capacity_g": grams(acct.bal), "delay": delay, "oneway": oneway, "salt": salt, "state": st, "seq": seq, "bal_a": bal_a, "until": until, "height": c.height,
            "locks": plocks.iter().map(|l| json!({"amt": l.amt, "to_b": l.to_b, "point": hex(&l.point), "expiry": l.expiry})).collect::<Vec<_>>(),
            "chain": c.p.chain, "min_fee": (c.reading.s as u64 + 99) / 100})));
    }
    // the channels inside factories: one entry per member, named by the coordinator (a) and the member (b)
    for (idx, t) in c.locks.iter() {
        let Terms::Factory { coord, key_c, members, delay, salt } = t else { continue };
        let Some(acct) = c.state.get(idx) else { continue };
        let fid = t.factory_id().unwrap();
        for (i, m) in members.iter().enumerate() {
            if who.map_or(false, |w| w != *coord && w != m.addr) { continue; }
            let (st, seq, bal_c, until, plocks) = match &m.state {
                crate::locks::SubState::Open => ("open", 0, m.base, 0, vec![]),
                crate::locks::SubState::Exited => ("exited", 0, 0, 0, vec![]),
                crate::locks::SubState::Closing { seq, bal_c, until, locks } => ("closing", *seq, *bal_c, *until, locks.clone()),
            };
            list.push((*salt * 16 + i as u64, json!({"id": hex(&crate::locks::sub_id(&fid, i as u8)), "fid": hex(&fid), "idx": i, "lock": address_string(&acct.pk), "a": address_string(coord), "b": address_string(&m.addr),
                "key_a": hex(key_c), "key_b": hex(&m.key), "capacity": m.cap, "capacity_g": grams(m.cap), "delay": delay, "oneway": false, "salt": salt, "state": st, "seq": seq, "bal_a": bal_c, "until": until, "height": c.height,
                "locks": plocks.iter().map(|l| json!({"amt": l.amt, "to_b": l.to_b, "point": hex(&l.point), "expiry": l.expiry})).collect::<Vec<_>>(),
                "chain": c.p.chain, "min_fee": (c.reading.s as u64 + 99) / 100})));
        }
    }
    list.sort_by_key(|(s, _)| *s);
    json!({"count": list.len(), "channels": list.into_iter().map(|(_, v)| v).collect::<Vec<_>>()})
}
fn peers(net: &Net) -> Value {
    let list: Vec<Value> = net.peer_list().into_iter().map(|(ip, inbound, addr)| json!({"ip": ip.to_string(), "inbound": inbound, "listens_on": addr.map(|a| a.to_string())})).collect();
    json!({"count": list.len(), "known_addresses": net.known_addr_count(), "peers": list})
}
fn pay(net: &Net, body: &[u8]) -> Result<Value, (u16, String)> {
    let v: Value = serde_json::from_slice(body).map_err(|_| (400, "the body is not JSON".to_string()))?;
    let h = v.get("tx").and_then(|t| t.as_str()).ok_or((400, "give {\"tx\": \"<hex of the signed payment>\"}".to_string()))?;
    if h.len() != 2 * TX_BYTES { return Err((400, format!("a payment is {TX_BYTES} bytes ({} hex digits)", 2 * TX_BYTES))); }
    let t = SignedPay::from_bytes(&unhex(h).map_err(|e| (400, e.to_string()))?).map_err(|e| (400, e.to_string()))?;
    let id = t.id();
    match net.submit_tx(t, None) {
        Ok(a) => Ok(json!({"ok": true, "id": hex(&id), "result": format!("{a:?}").to_lowercase()})),
        Err(e) => Err((400, e.to_string())),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::node::{dev, DevStamp, Node, Params};
    use crate::tx::Wallet;

    fn setup(blocks: usize) -> (Net, SocketAddr, dev::Devnet) {
        let mut dn = dev::Devnet::new(None, 8).unwrap();
        let node = Node::open(Params::devnet(), &dev::genesis_of(&dn.keys), Box::new(DevStamp), None).unwrap();
        let net = Net::new(node);
        for _ in 0..blocks { let b = dn.next_block(24, 6).unwrap(); dn.chain.accept(&b, u32::MAX).unwrap(); net.add_block(&b).unwrap(); }
        let addr = start(net.clone(), "127.0.0.1:0", "t0ken".into()).unwrap();
        (net, addr, dn)
    }
    /// one raw request, the status code and the JSON body
    fn call(addr: SocketAddr, raw: &str) -> (u16, Value) {
        let mut s = TcpStream::connect(addr).unwrap();
        s.set_read_timeout(Some(Duration::from_secs(10))).unwrap();
        s.write_all(raw.as_bytes()).unwrap();
        let mut out = vec![]; let _ = s.read_to_end(&mut out);
        let text = String::from_utf8_lossy(&out).to_string();
        let code: u16 = text.split(' ').nth(1).unwrap_or("0").parse().unwrap_or(0);
        let body = text.split_once("\r\n\r\n").map_or("", |x| x.1);
        (code, serde_json::from_str(body).unwrap_or(Value::Null))
    }
    fn get(addr: SocketAddr, path: &str) -> (u16, Value) { call(addr, &format!("GET {path} HTTP/1.1\r\nHost: 127.0.0.1:{}\r\n\r\n", addr.port())) }
    fn post(addr: SocketAddr, path: &str, token: Option<&str>, body: &str) -> (u16, Value) {
        let auth = token.map_or(String::new(), |t| format!("Authorization: Bearer {t}\r\n"));
        call(addr, &format!("POST {path} HTTP/1.1\r\nHost: localhost:{}\r\n{auth}Content-Length: {}\r\n\r\n{body}", addr.port(), body.len()))
    }

    #[test]
    fn the_api_shows_the_chain_and_takes_a_payment_only_with_the_token() {
        let (net, addr, dn) = setup(5);
        // status
        let (c, st) = get(addr, "/api/status");
        assert_eq!(c, 200);
        assert_eq!((st["height"].as_u64(), st["chain"]["name"].as_str(), st["unit"].as_str()), (Some(5), Some("Jen"), Some("nanogram")));
        assert_eq!(st["tip"].as_str().unwrap(), hex(&net.best()));
        assert_eq!(st["supply"]["genesis"].as_u64(), Some(8 * 1_000_000_000));
        assert_eq!(st["supply"]["genesis_g"].as_str(), Some("8.000000000"));
        // blocks, newest first, paged
        assert_eq!(get(addr, "/api/chains").1, json!([]), "a lone node has no sibling chains");
        let (_, bl) = get(addr, "/api/blocks?limit=3");
        let hs: Vec<u64> = bl["blocks"].as_array().unwrap().iter().map(|b| b["height"].as_u64().unwrap()).collect();
        assert_eq!(hs, vec![5, 4, 3]);
        let (_, bl) = get(addr, "/api/blocks?limit=10&before=3");
        let hs: Vec<u64> = bl["blocks"].as_array().unwrap().iter().map(|b| b["height"].as_u64().unwrap()).collect();
        assert_eq!(hs, vec![2, 1]);
        // one block by height and by hash
        let (_, by_h) = get(addr, "/api/block/4");
        let hash = by_h["hash"].as_str().unwrap().to_string();
        let (_, by_hash) = get(addr, &format!("/api/block/{hash}"));
        assert_eq!(by_h, by_hash);
        assert_eq!((by_h["main_chain"].as_bool(), by_h["tickets"].as_u64().is_some(), by_h["payments"].as_u64()), (Some(true), true, Some(by_h["payments"].as_u64().unwrap())));
        assert_eq!(get(addr, "/api/block/6").0, 404);
        assert_eq!(get(addr, "/api/block/0").0, 404);
        assert_eq!(get(addr, &format!("/api/block/{}", "ab".repeat(32))).0, 404);
        assert_eq!(get(addr, "/api/block/zzz").0, 404);
        // an account
        let w0 = Wallet { key: dn.keys[7].clone() };
        let newcomer = Wallet::from_secret(num_bigint::BigUint::from(31_337u64));
        let (c, a) = get(addr, &format!("/api/account/{}", w0.address_string()));
        assert_eq!((c, a["found"].as_bool()), (200, Some(true)));
        let n0 = a["next_nonce"].as_u64().unwrap();      // the devnet blocks already carry some payments of this wallet
        assert_eq!(a["nonce"].as_u64().unwrap(), n0);
        assert!(a["balance"].as_u64().unwrap() >= 1_000_000_000);
        let (_, a) = get(addr, &format!("/api/account/{}", newcomer.address_string()));
        assert_eq!((a["found"].as_bool(), a["balance"].as_u64()), (Some(false), Some(0)));
        let mut typo = newcomer.address_string(); typo.replace_range(10..11, if &typo[10..11] == "a" { "b" } else { "a" });
        assert_eq!(get(addr, &format!("/api/account/{typo}")).0, 400);
        assert_eq!(get(addr, "/api/account/hello").0, 400);
        // a payment: no token, a wrong token, bad bodies, then the right one
        let t = w0.pay(newcomer.address(), 20_000_000, Wallet::standard_fee(20_000_000), n0);
        let body = format!("{{\"tx\":\"{}\"}}", hex(&t.to_bytes()));
        assert_eq!(post(addr, "/api/pay", None, &body).0, 401);
        assert_eq!(post(addr, "/api/pay", Some("t0kens"), &body).0, 401);
        assert_eq!(post(addr, "/api/pay", Some("wrong"), &body).0, 401);
        assert_eq!(post(addr, "/api/pay", Some("t0ken"), "not json").0, 400);
        assert_eq!(post(addr, "/api/pay", Some("t0ken"), "{\"tx\":\"abcd\"}").0, 400);
        assert_eq!(post(addr, "/api/pay", Some("t0ken"), &format!("{{\"tx\":\"{}\"}}", "zz".repeat(TX_BYTES))).0, 400);
        let mut forged = t.clone(); forged.amt += 1;
        let (c, e) = post(addr, "/api/pay", Some("t0ken"), &format!("{{\"tx\":\"{}\"}}", hex(&forged.to_bytes())));
        assert_eq!(c, 400); assert!(e["error"].as_str().unwrap().contains("signature"), "{e}");
        assert_eq!(get(addr, "/api/mempool").1["count"].as_u64(), Some(0), "nothing got in yet");
        let (c, ok) = post(addr, "/api/pay", Some("t0ken"), &body);
        assert_eq!((c, ok["ok"].as_bool(), ok["result"].as_str()), (200, Some(true), Some("new")));
        assert_eq!(ok["id"].as_str().unwrap(), hex(&t.id()));
        let (_, again) = post(addr, "/api/pay", Some("t0ken"), &body);
        assert_eq!(again["error"].as_str(), Some("known"));
        // it shows in the mempool and in the sender's next nonce
        let (_, mp) = get(addr, "/api/mempool");
        assert_eq!(mp["count"].as_u64(), Some(1));
        let p = &mp["payments"][0];
        assert_eq!((p["from"].as_str(), p["to"].as_str(), p["amount"].as_u64()), (Some(w0.address_string().as_str()), Some(newcomer.address_string().as_str()), Some(20_000_000)));
        assert_eq!(get(addr, &format!("/api/account/{}", w0.address_string())).1["next_nonce"].as_u64(), Some(n0 + 1));
        assert_eq!(get(addr, "/api/status").1["mempool"].as_u64(), Some(1));
        assert_eq!(net.pool.lock().unwrap().len(), 1);
        // peers
        let (_, pe) = get(addr, "/api/peers");
        assert_eq!(pe["count"].as_u64(), Some(0));
    }

    #[test]
    fn the_api_refuses_what_it_should() {
        let (_net, addr, _dn) = setup(1);
        let port = addr.port();
        // another machine's name in the Host header (DNS rebinding), none at all
        let evil = call(addr, "GET /api/status HTTP/1.1\r\nHost: evil.example\r\n\r\n");
        assert_eq!(evil.0, 403);
        assert_eq!(call(addr, "GET /api/status HTTP/1.1\r\nHost: localhost:1\r\n\r\n").0, 403, "a name with another port is not us");
        assert_eq!(call(addr, "GET /api/status HTTP/1.1\r\n\r\n").0, 403);
        assert_eq!(call(addr, &format!("GET /api/status HTTP/1.1\r\nHost: [::1]:{port}\r\n\r\n")).0, 200);
        // methods, paths, junk
        assert_eq!(call(addr, &format!("DELETE /api/status HTTP/1.1\r\nHost: localhost:{port}\r\n\r\n")).0, 405);
        assert_eq!(call(addr, &format!("OPTIONS /api/pay HTTP/1.1\r\nHost: localhost:{port}\r\n\r\n")).0, 405);
        assert_eq!(get(addr, "/api/nothing").0, 404);
        assert_eq!(get(addr, "/api/blocks?limit=abc").0, 400);
        assert_eq!(call(addr, "hello\r\n\r\n").0, 400);
        assert_eq!(call(addr, &format!("POST /api/pay HTTP/1.1\r\nHost: localhost:{port}\r\nTransfer-Encoding: chunked\r\n\r\n")).0, 400);
        // a huge head and a huge body
        let big = format!("GET /api/status HTTP/1.1\r\nHost: localhost:{port}\r\nX-Pad: {}\r\n\r\n", "a".repeat(40_000));
        assert_eq!(call(addr, &big).0, 431);
        assert_eq!(call(addr, &format!("POST /api/pay HTTP/1.1\r\nHost: localhost:{port}\r\nContent-Length: 300000\r\n\r\n")).0, 413);
        // no CORS: a browser on another site cannot read an answer
        let mut s = TcpStream::connect(addr).unwrap();
        s.write_all(format!("GET /api/status HTTP/1.1\r\nHost: localhost:{port}\r\nOrigin: https://evil.example\r\n\r\n").as_bytes()).unwrap();
        let mut out = String::new(); s.read_to_string(&mut out).unwrap();
        assert!(!out.to_ascii_lowercase().contains("access-control"), "{out}");
        // a client that sends nothing is let go, and the server still answers
        let idle = TcpStream::connect(addr).unwrap();
        assert_eq!(get(addr, "/api/status").0, 200);
        drop(idle);
        // only a loopback address can be bound
        let (net, _, _) = setup(0);
        for bad in ["0.0.0.0:0", "192.168.1.5:0", "nonsense"] { assert!(start(net.clone(), bad, "x".into()).is_err(), "{bad}"); }
    }

    #[test]
    fn the_explorer_page_is_served_and_is_safe() {
        let (_net, addr, _dn) = setup(2);
        let port = addr.port();
        let raw = |path: &str, host: &str| {
            let mut s = TcpStream::connect(addr).unwrap();
            s.write_all(format!("GET {path} HTTP/1.1\r\nHost: {host}\r\n\r\n").as_bytes()).unwrap();
            let mut out = String::new(); s.read_to_string(&mut out).unwrap();
            let (head, body) = out.split_once("\r\n\r\n").map(|(a, b)| (a.to_string(), b.to_string())).unwrap_or_default();
            (head, body)
        };
        let host = format!("localhost:{port}");
        let (head, html) = raw("/", &host);
        assert!(head.starts_with("HTTP/1.1 200") && head.contains("text/html"), "{head}");
        assert!(head.contains("Content-Security-Policy: default-src 'none'; script-src 'self'; style-src 'self'; connect-src 'self'"), "{head}");
        assert!(head.contains("X-Frame-Options: DENY") && head.contains("nosniff") && head.contains("no-referrer"));
        assert!(html.contains("<script src=\"/app.js\">") && html.contains("href=\"/app.css\""));
        // nothing inline: the policy would stop it, and the page does not rely on it
        assert!(!html.contains("<script>") && !html.contains("onclick") && !html.contains("style=\""));
        let (head, js) = raw("/app.js", &host);
        assert!(head.contains("text/javascript"));
        // the page builds its DOM with textContent / createElement; chain data is never parsed as markup
        let js = js.replace("http://www.w3.org/2000/svg", "");          // the SVG namespace is a name, not a request
        for bad in ["innerHTML", "outerHTML", "insertAdjacentHTML", "document.write", "eval(", "new Function", "setTimeout(\"", "http://", "https://"] {
            assert!(!js.contains(bad), "app.js uses {bad}");
        }
        let (head, css) = raw("/app.css", &host);
        assert!(head.contains("text/css") && !css.contains("@import") && !css.contains("url("));
        assert_eq!(raw("/", "evil.example").0.split(' ').nth(1), Some("403"), "the page is for this machine only");
        assert_eq!(raw("/app.js", "evil.example").0.split(' ').nth(1), Some("403"));
        assert_eq!(raw("/nothing.png", &host).0.split(' ').nth(1), Some("404"));
        // the page's own API calls work with the same Host
        let (code, api) = get(addr, "/api");
        assert_eq!(code, 200); assert!(api["endpoints"].as_array().unwrap().len() >= 6);
    }

    #[test]
    fn the_token_is_kept_between_runs() {
        let d = std::env::temp_dir().join(format!("zen-api-token-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&d);
        let t1 = load_or_create_token(Some(&d)).unwrap();
        assert_eq!(t1.len(), 64);
        assert_eq!(load_or_create_token(Some(&d)).unwrap(), t1);
        assert_ne!(load_or_create_token(None).unwrap(), load_or_create_token(None).unwrap());
        #[cfg(unix)] { use std::os::unix::fs::PermissionsExt; assert_eq!(std::fs::metadata(d.join("api.token")).unwrap().permissions().mode() & 0o777, 0o600); }
        let _ = std::fs::remove_dir_all(&d);
    }

    #[test]
    fn amounts_in_grams_are_exact() {
        assert_eq!(grams(0), "0.000000000");
        assert_eq!(grams(1), "0.000000001");
        assert_eq!(grams(2_520_000_000_000), "2520.000000000");
        assert_eq!(grams(u64::MAX), "18446744073.709551615");
    }
}
