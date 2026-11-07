// Routing node: payments across several channels and across chains (stage 4, Justus L. Ludovic).
//
// A node holds channels (channel.rs) and forwards point-locked payments between them (SPEC 7.3, 7.4):
//   * every hop is a point lock; the sender gives each hop its own point, P_i = P_(i+1) + d_i*G, so the locks along a route cannot be matched by
//     their points, and the scalar that opens the last one (the receiver's invoice secret) opens all of them once each offset d_i is added back;
//   * the route is a nest of encrypted layers (one key per hop, from a fresh ephemeral key), so a hop sees only the channel it forwards to, the
//     amount, the time its outgoing lock runs to, and its offset;
//   * a stream node (channels on two chains) forwards one metal into another at its own published price, plus a routing fee and, between chains,
//     a spread. The same lock family on every chain makes a route such as Jen -> Ken -> Yen complete on every chain or on none;
//   * a hop that cannot forward, or a receiver that refuses, gives the lock back; the refusal runs back to the sender hop by hop.
// If a neighbour stops answering, the channel is closed on chain (`chan dispute` / `chan settle`): the point locks are opened with the scalars the node
// learned, or go back to their senders after their expiry.
//
// Limits (testnet): layers are not padded to one size; the onion is not tied into the lock (a hop trusts what it can decrypt); the graph is found by asking
// the neighbours for their channels (no gossip, no privacy for balances); time-outs are converted between chains with each chain's block time.
//
//   rnode run <dir>                      the daemon (wallet.key, node.conf and channels/ in <dir>)
//   rnode add-channel <dir> <channel file> <peer address>
//   rnode invoice <dir> <amount> <chain>       -> an invoice string
//   rnode pay <dir> <invoice>                  find a route, pay, wait for the receipt
//   rnode status <dir>
use crate::channel::Chan;
use crate::locks::PLock;
use crate::tx::{http_get, Wallet};
use crate::{ec, mint};
use anyhow::{anyhow, bail, Result};
use num_bigint::BigUint;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::io::{BufRead, BufReader, Write};
use std::net::{TcpListener, TcpStream};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};
use std::time::Duration;

fn hex(b: &[u8]) -> String { b.iter().map(|x| format!("{x:02x}")).collect() }
fn unhex(s: &str) -> Result<Vec<u8>> { (0..s.len() / 2).map(|i| Ok(u8::from_str_radix(s.get(2 * i..2 * i + 2).ok_or_else(|| anyhow!("bad hex"))?, 16)?)).collect() }
fn arr<const N: usize>(s: &str) -> Result<[u8; N]> { unhex(s)?.try_into().map_err(|_| anyhow!("expected {N} bytes")) }
fn now() -> u64 { crate::p2p::now() as u64 }
fn n() -> BigUint { ec::n_order() }
fn scalar(b: &[u8; 40]) -> BigUint { BigUint::from_bytes_le(b) }
fn rand_scalar() -> BigUint { loop { let mut b = [0u8; 64]; rand::RngCore::fill_bytes(&mut rand::rngs::OsRng, &mut b); let k = BigUint::from_bytes_le(&b) % n(); if k != BigUint::ZERO { return k; } } }
fn point_of(k: &BigUint) -> [u8; 41] { mint::encode_point(ec::mul_g(&ec::params(), k)) }
fn id_hex(id: &[u8; 32]) -> String { hex(id) }

// ------------------------------------------------------------------ the onion
const MAC: usize = 16;
fn keystream(ss: &[u8; 32], len: usize) -> Vec<u8> {
    let mut out = vec![];
    let mut ctr = 0u32;
    while out.len() < len { let mut h = Sha256::new(); h.update(b"Zen-onion-ks"); h.update(ss); h.update(ctr.to_le_bytes()); out.extend(h.finalize()); ctr += 1; }
    out.truncate(len); out
}
fn shared(sk: &BigUint, pt: &[u8; 41]) -> Result<[u8; 32]> {
    let q = ec::mul(mint::decode_point(pt)?, sk);
    let mut h = Sha256::new(); h.update(b"Zen-onion-ss"); h.update(mint::encode_point(q)); Ok(h.finalize().into())
}
fn mac(ss: &[u8; 32], ct: &[u8]) -> [u8; MAC] { let mut h = Sha256::new(); h.update(b"Zen-onion-mac"); h.update(ss); h.update(ct); h.finalize()[..MAC].try_into().unwrap() }

/// what a hop learns
#[derive(Clone, Debug, PartialEq)]
pub enum Hop {
    /// forward over this channel: `amount` (in that channel's chain) in a lock that runs until unix time `expiry_time`, with this offset
    Forward { chan: [u8; 32], amount: u64, expiry_time: u64, offset: [u8; 40] },
    /// this node is the receiver of `amount`
    Final { amount: u64 },
}
impl Hop {
    fn encode(&self) -> Vec<u8> {
        match self {
            Hop::Forward { chan, amount, expiry_time, offset } => { let mut v = vec![1]; v.extend(chan); v.extend(amount.to_le_bytes()); v.extend(expiry_time.to_le_bytes()); v.extend(offset); v }
            Hop::Final { amount } => { let mut v = vec![2]; v.extend(amount.to_le_bytes()); v }
        }
    }
    /// the hop at the start of `b` and the length it took
    fn decode(b: &[u8]) -> Result<(Hop, usize)> {
        match b.first() {
            Some(1) if b.len() >= 89 => Ok((Hop::Forward { chan: b[1..33].try_into()?, amount: u64::from_le_bytes(b[33..41].try_into()?), expiry_time: u64::from_le_bytes(b[41..49].try_into()?), offset: b[49..89].try_into()? }, 89)),
            Some(2) if b.len() >= 9 => Ok((Hop::Final { amount: u64::from_le_bytes(b[1..9].try_into()?) }, 9)),
            _ => bail!("not a hop"),
        }
    }
}
/// layers for `hops` (the node keys, first hop first, with what each learns)
pub fn onion_build(hops: &[([u8; 41], Hop)]) -> Result<Vec<u8>> {
    let mut inner: Vec<u8> = vec![];
    for (pk, hop) in hops.iter().rev() {
        let e = rand_scalar();
        let ep = point_of(&e);
        let ss = shared(&e, pk)?;
        let mut plain = hop.encode(); plain.extend(&inner);
        let ks = keystream(&ss, plain.len());
        let ct: Vec<u8> = plain.iter().zip(ks).map(|(a, b)| a ^ b).collect();
        let mut layer = ep.to_vec(); layer.extend(mac(&ss, &ct)); layer.extend(&ct);
        inner = layer;
    }
    Ok(inner)
}
/// open the outer layer with this node's secret: what it learns and the layers left for the next hop (empty for the last)
pub fn onion_peel(sk: &BigUint, layer: &[u8]) -> Result<(Hop, Vec<u8>)> {
    if layer.len() < 41 + MAC + 9 { bail!("short onion"); }
    let ep: [u8; 41] = layer[..41].try_into()?;
    let ss = shared(sk, &ep)?;
    let ct = &layer[41 + MAC..];
    if mac(&ss, ct) != layer[41..41 + MAC] { bail!("the onion is not for this node"); }
    let ks = keystream(&ss, ct.len());
    let plain: Vec<u8> = ct.iter().zip(ks).map(|(a, b)| a ^ b).collect();
    let (hop, used) = Hop::decode(&plain)?;
    Ok((hop, plain[used..].to_vec()))
}

// ------------------------------------------------------------------ configuration
#[derive(Clone, Debug)]
pub struct Cfg {
    pub name: String, pub listen: String,
    /// chain id -> (node API address, node p2p address)
    pub chains: HashMap<u8, (String, String)>,
    /// a price per base unit of each chain, in any common unit (only the ratios matter)
    pub prices: HashMap<u8, u64>,
    pub fee_ppm: u64, pub spread_ppm: u64, pub fee_base: u64, pub margin_secs: u64,
    /// where a copy of every channel file goes after each change (a watchtower's folder)
    pub tower_dir: Option<String>,
    /// blocks before a point lock's expiry (beyond the dispute window) at which a silent peer makes this node close on chain; 0 turns the guard off
    pub guard_blocks: u64,
    /// seconds a point lock may stay open before the guard counts the peer as silent
    pub guard_wait: u64,
}
impl Cfg {
    pub fn parse(t: &str) -> Result<Cfg> {
        let mut c = Cfg { name: "node".into(), listen: "127.0.0.1:0".into(), chains: HashMap::new(), prices: HashMap::new(), fee_ppm: 1000, spread_ppm: 3000, fee_base: 1, margin_secs: 120, tower_dir: None, guard_blocks: 6, guard_wait: 90 };
        for l in t.lines().map(|l| l.trim()).filter(|l| !l.is_empty() && !l.starts_with('#')) {
            let v: Vec<&str> = l.split_whitespace().collect();
            let chain = |x: &str| -> Result<u8> { Ok(match x { "yen" | "1" => 1, "ken" | "2" => 2, "jen" | "3" => 3, _ => bail!("chain {x}?") }) };
            match v.as_slice() {
                ["name", x] => c.name = x.to_string(),
                ["listen", x] => c.listen = x.to_string(),
                ["chain", ch, api, p2p] => { c.chains.insert(chain(ch)?, (api.to_string(), p2p.to_string())); }
                ["price", ch, p] => { c.prices.insert(chain(ch)?, p.parse()?); }
                ["fee_ppm", x] => c.fee_ppm = x.parse()?,
                ["spread_ppm", x] => c.spread_ppm = x.parse()?,
                ["fee_base", x] => c.fee_base = x.parse()?,
                ["margin_secs", x] => c.margin_secs = x.parse()?,
                ["tower_dir", x] => c.tower_dir = Some(x.to_string()),
                ["guard_blocks", x] => c.guard_blocks = x.parse()?,
                ["guard_wait", x] => c.guard_wait = x.parse()?,
                _ => bail!("unknown line in node.conf: {l}"),
            }
        }
        Ok(c)
    }
}
/// what `amount_out` of `out_chain` costs to forward from `in_chain`, at these prices and fees
pub fn quote(prices: &HashMap<u8, u64>, fee_ppm: u64, spread_ppm: u64, fee_base: u64, amount_out: u64, out_chain: u8, in_chain: u8) -> Option<u64> {
    let (po, pi) = (*prices.get(&out_chain)?, *prices.get(&in_chain)?);
    if pi == 0 { return None; }
    let conv = (amount_out as u128 * po as u128 + pi as u128 - 1) / pi as u128;
    let ppm = fee_ppm as u128 + if in_chain != out_chain { spread_ppm as u128 } else { 0 };
    let total = conv + (conv * ppm + 999_999) / 1_000_000 + fee_base as u128;
    u64::try_from(total).ok()
}

// ------------------------------------------------------------------ the node
#[derive(Clone, Debug)]
struct Fwd { in_chan: [u8; 32], in_point: [u8; 41], offset: [u8; 40] }
#[derive(Clone, Debug)]
struct Invoice { r: [u8; 40], amount: u64, chain: u8, paid: bool }
#[derive(Clone, Debug)]
struct Pay { sum_offsets: [u8; 40], invoice_point: [u8; 41], status: String, receipt: Option<String>, reason: String, chan: [u8; 32], amount: u64 }

pub struct RNode {
    dir: PathBuf, pub cfg: Cfg, wallet: Wallet,
    /// every read-modify-write of a channel file happens under this
    mu: Mutex<()>,
    fwds: Mutex<HashMap<[u8; 41], Fwd>>,
    invoices: Mutex<HashMap<[u8; 41], Invoice>>,
    pays: Mutex<HashMap<[u8; 41], Pay>>,
    log: Mutex<Vec<String>>,
    /// one-time keys of the sealed requests seen in the last two skew windows (a replay inside the 60 s is refused)
    seen: crate::transport::Replays,
}
type Node = Arc<RNode>;

fn open_answer_from(call: &crate::transport::Call, v: &Value) -> Result<Value> { crate::transport::open_answer(call, v) }
fn peer_key(c: &Chan) -> [u8; 41] { if c.role_a { c.key_b } else { c.key_a } }
const MAX_ANSWER: u64 = 4 << 20;
/// connections the node serves at once (each has its own thread)
const MAX_WIRE_CONNS: usize = 64;
fn rpc(addr: &str, req: &Value) -> Result<Value> {
    let sa: std::net::SocketAddr = addr.parse().map_err(|_| anyhow!("bad address {addr}"))?;
    let mut s = TcpStream::connect_timeout(&sa, Duration::from_secs(5))?;
    s.set_read_timeout(Some(Duration::from_secs(60)))?;
    writeln!(s, "{}", req)?;
    let mut line = String::new();
    // a peer's answer is read up to a limit, so a hostile peer cannot fill memory with one endless line
    std::io::Read::take(BufReader::new(s), MAX_ANSWER).read_line(&mut line)?;
    Ok(serde_json::from_str(line.trim())?)
}

impl RNode {
    pub fn open(dir: &Path) -> Result<RNode> {
        let cfg = Cfg::parse(&std::fs::read_to_string(dir.join("node.conf"))?)?;
        let wallet = Wallet::load(&dir.join("wallet.key"))?;
        std::fs::create_dir_all(dir.join("channels"))?;
        Ok(RNode { dir: dir.to_path_buf(), cfg, wallet, mu: Mutex::new(()), fwds: Mutex::new(HashMap::new()), invoices: Mutex::new(HashMap::new()), pays: Mutex::new(HashMap::new()), seen: Default::default(), log: Mutex::new(vec![]) })
    }
    fn say(&self, s: String) { eprintln!("[{}] {s}", self.cfg.name); let mut l = self.log.lock().unwrap(); l.push(s); if l.len() > 200 { l.remove(0); } }
    fn pubkey(&self) -> [u8; 41] { mint::encode_point(self.wallet.key.a) }
    fn secret(&self) -> BigUint { let l = self.wallet.key.secret_limbs(); let mut b = vec![]; for x in l { b.extend(x.to_le_bytes()); } BigUint::from_bytes_le(&b) }
    fn chan_path(&self, id: &[u8; 32]) -> PathBuf { self.dir.join("channels").join(format!("{}.chan", id_hex(id))) }
    /// write a channel file, and a copy for the watchtower when one is set
    fn save_chan(&self, c: &Chan) -> Result<()> {
        c.save(&self.chan_path(&c.id))?;
        if let Some(t) = &self.cfg.tower_dir { let _ = std::fs::create_dir_all(t); let _ = c.save(&Path::new(t).join(format!("{}.chan", id_hex(&c.id)))); }
        Ok(())
    }
    /// ask a channel's peer for a newer agreed state (after a crash, a lost acknowledgement or a long absence)
    fn sync_one(&self, id: &[u8; 32]) -> Result<bool> {
        let (seq, addr) = { let c = self.load(id)?; (c.seq, c.peer_addr.clone().ok_or_else(|| anyhow!("no peer address"))?) };
        let pk = peer_key(&self.load(id)?);
        let v = self.call(&addr, &pk, &json!({"t": "sync", "chan": id_hex(id), "seq": seq}))?;
        let Some(b) = v["state"].as_str() else { return Ok(false) };
        let _g = self.mu.lock().unwrap();
        let mut c = self.load(id)?;
        c.adopt_state(&unhex(b)?)?;
        self.save_chan(&c)?;
        self.say(format!("channel {} caught up to update {}", &id_hex(id)[..8], c.seq));
        Ok(true)
    }
    /// negotiate a joint close with the peer and send it to the chain
    fn close_chan(&self, prefix: &str) -> Result<String> {
        let c = self.all_chans().into_iter().find(|c| id_hex(&c.id).starts_with(prefix)).ok_or_else(|| anyhow!("no such channel"))?;
        let _ = self.sync_one(&c.id);
        let c = self.load(&c.id)?;
        if c.pending.is_some() { bail!("an update is waiting for its acknowledgement"); }
        let addr = c.peer_addr.clone().ok_or_else(|| anyhow!("no peer address"))?;
        let (e, s) = c.close_sig(&self.wallet);
        let mut mine = e.to_le_bytes().to_vec(); mine.extend(s);
        let v = self.call(&addr, &peer_key(&c), &json!({"t": "closesign", "chan": id_hex(&c.id), "seq": c.seq, "bal_a": c.bal_a, "sig": hex(&mine)}))?;
        let b = unhex(v["sig"].as_str().ok_or_else(|| anyhow!("the peer refused: {}", v["err"].as_str().unwrap_or("?")))?)?;
        if b.len() != 56 { bail!("not a close signature"); }
        let theirs = (u128::from_le_bytes(b[..16].try_into()?), <[u8; 40]>::try_from(&b[16..])?);
        if !c.close_sig_ok(c.bal_a, theirs.0, &theirs.1) { bail!("the peer's close signature is bad"); }
        let (api, p2p) = self.cfg.chains.get(&c.chain).ok_or_else(|| anyhow!("no node for chain {}", c.chain))?;
        let op = crate::channel::coop_close(&c, &self.wallet, crate::tx::split_node(&format!("{p2p},{api}"))?.0, api, theirs)?;
        self.say(format!("channel {} closed together at update {} | {}", &id_hex(&c.id)[..8], c.seq, op));
        Ok(op)
    }
    fn on_closesign(&self, req: &Value) -> Result<Value> {
        let id: [u8; 32] = arr(req["chan"].as_str().unwrap_or(""))?;
        let _g = self.mu.lock().unwrap();
        let c = self.load(&id).map_err(|_| anyhow!("no such channel"))?;
        if c.pending.is_some() { return Ok(json!({"err": "busy"})); }
        if c.oneway || !c.locks.is_empty() { bail!("a joint close needs a two-way channel with no point lock waiting"); }
        if req["seq"].as_u64() != Some(c.seq) || req["bal_a"].as_u64() != Some(c.bal_a) { bail!("not the state this side holds (update {}, a has {})", c.seq, c.bal_a); }
        let b = unhex(req["sig"].as_str().unwrap_or(""))?;
        if b.len() != 56 || !c.close_sig_ok(c.bal_a, u128::from_le_bytes(b[..16].try_into()?), &b[16..].try_into()?) { bail!("the close signature is bad"); }
        let (e, s) = c.close_sig(&self.wallet);
        let mut mine = e.to_le_bytes().to_vec(); mine.extend(s);
        self.say(format!("signed a joint close of {} at update {}", &id_hex(&id)[..8], c.seq));
        Ok(json!({"sig": hex(&mine)}))
    }
    /// one encrypted, authenticated request to a node whose static key is `server` (transport.rs)
    fn call(&self, addr: &str, server: &[u8; 41], req: &Value) -> Result<Value> {
        let (wire, call) = crate::transport::seal_request(&self.secret(), &self.wallet.key, server, req, now())?;
        open_answer_from(&call, &rpc(addr, &wire)?)
    }
    fn load(&self, id: &[u8; 32]) -> Result<Chan> { Chan::load(&self.chan_path(id)) }
    fn all_chans(&self) -> Vec<Chan> {
        let mut v = vec![];
        if let Ok(rd) = std::fs::read_dir(self.dir.join("channels")) { for e in rd.flatten() { if e.path().extension().map_or(false, |x| x == "chan") { if let Ok(c) = Chan::load(&e.path()) { v.push(c); } } } }
        v.sort_by_key(|c| c.id); v
    }
    /// (height, block seconds, now) of a chain, from the node API
    fn clock(&self, chain: u8) -> Result<(u64, u64, u64)> {
        let (api, _) = self.cfg.chains.get(&chain).ok_or_else(|| anyhow!("this node does not follow chain {chain}"))?;
        let st = http_get(api, "/api/status")?;
        Ok((st["height"].as_u64().unwrap_or(0), st["block_secs"].as_u64().unwrap_or(150).max(1), now()))
    }
    fn expiry_height(&self, chain: u8, expiry_time: u64) -> Result<u64> {
        let (h, bs, t) = self.clock(chain)?;
        Ok(h + ((expiry_time.saturating_sub(t) + bs - 1) / bs).max(2))
    }
    fn expiry_time(&self, chain: u8, expiry_height: u64) -> Result<u64> {
        let (h, bs, t) = self.clock(chain)?;
        Ok(t + expiry_height.saturating_sub(h) * bs)
    }
    fn info(&self) -> Value {
        let chans: Vec<Value> = self.all_chans().iter().map(|c| json!({"id": id_hex(&c.id), "chain": c.chain, "oneway": c.oneway, "a": hex(&c.key_a), "b": hex(&c.key_b), "peer_addr": c.peer_addr,
            "mine": c.mine(), "theirs": c.theirs(), "locks": c.locks.len()})).collect();
        json!({"name": self.cfg.name, "pubkey": hex(&self.pubkey()), "listen": self.cfg.listen, "channels": chans, "fee_ppm": self.cfg.fee_ppm, "spread_ppm": self.cfg.spread_ppm,
               "fee_base": self.cfg.fee_base, "margin_secs": self.cfg.margin_secs, "prices": self.cfg.prices.iter().map(|(k, v)| (k.to_string(), json!(v))).collect::<serde_json::Map<_, _>>()})
    }

    /// Make a proposal on a channel, send it to the peer, and store the result. `build` makes the proposal from the channel. A busy peer is retried.
    fn exchange(&self, id: &[u8; 32], onion: Option<&[u8]>, build: &dyn Fn(&mut Chan) -> Result<Vec<u8>>) -> Result<()> {
        let mut last = String::new();
        for attempt in 0..8 {
            let (prop, addr) = {
                let _g = self.mu.lock().unwrap();
                let mut c = self.load(id)?;
                if c.pending.is_some() { c.drop_pending(); }
                let p = build(&mut c)?;
                let addr = c.peer_addr.clone().ok_or_else(|| anyhow!("no address for this channel's peer"))?;
                self.save_chan(&c)?;
                (p, addr)
            };
            let mut req = json!({"t": "prop", "chan": id_hex(id), "prop": hex(&prop)});
            if let Some(o) = onion { req["onion"] = json!(hex(o)); }
            let res = { let pk = peer_key(&self.load(id)?); self.call(&addr, &pk, &req) };
            let _g = self.mu.lock().unwrap();
            let mut c = self.load(id)?;
            match res {
                Ok(v) if v["ack"].is_string() => { c.commit(&unhex(v["ack"].as_str().unwrap())?)?; self.save_chan(&c)?; return Ok(()); }
                Ok(v) => { last = v["err"].as_str().unwrap_or("?").to_string(); c.drop_pending(); self.save_chan(&c)?; if last != "busy" { bail!("{last}"); } }
                Err(e) => { last = e.to_string(); c.drop_pending(); self.save_chan(&c)?; bail!("the peer did not answer: {last}"); }
            }
            std::thread::sleep(Duration::from_millis(60 + 90 * attempt));
        }
        bail!("the peer stayed busy: {last}")
    }

    // ---- the receiving side of a proposal
    fn on_prop(self: &Arc<Self>, req: &Value) -> Result<Value> {
        let id: [u8; 32] = arr(req["chan"].as_str().unwrap_or(""))?;
        let prop = unhex(req["prop"].as_str().unwrap_or(""))?;
        let onion = req["onion"].as_str().map(unhex).transpose()?;
        let (ack, before, after, secrets_before, chain_id, my_pending) = {
            let _g = self.mu.lock().unwrap();
            let mut c = self.load(&id).map_err(|_| anyhow!("no such channel"))?;
            if c.pending.is_some() { return Ok(json!({"err": "busy"})); }
            let before = c.locks.clone(); let sb = c.secrets.len();
            let ack = c.accept(&self.wallet, &prop)?;
            self.save_chan(&c)?;
            (ack, before, c.locks.clone(), sb, c.chain, false)
        };
        let _ = (chain_id, my_pending);
        // what changed decides what to do next, after the acknowledgement has gone back
        let me = self.clone();
        std::thread::spawn(move || {
            if let Err(e) = me.after_accept(id, before, after, secrets_before, onion) { me.say(format!("after update on {}: {e}", &id_hex(&id)[..8])); }
        });
        Ok(json!({"ack": hex(&ack)}))
    }
    fn after_accept(self: &Arc<Self>, id: [u8; 32], before: Vec<PLock>, after: Vec<PLock>, secrets_before: usize, onion: Option<Vec<u8>>) -> Result<()> {
        if after.len() > before.len() {
            let lock = after.last().unwrap().clone();
            let res = self.forward(id, lock.clone(), onion);
            if let Err(e) = res {
                self.say(format!("cannot forward {} on {}: {e}", lock.amt, &id_hex(&id)[..8]));
                self.give_back(id, &lock.point)?;
            }
        } else if after.len() < before.len() {
            let gone = before.iter().find(|l| !after.contains(l)).cloned().ok_or_else(|| anyhow!("no lock went"))?;
            let secret = { let _g = self.mu.lock().unwrap(); let c = self.load(&id)?; c.secrets.iter().skip(secrets_before).find(|(p, _)| *p == gone.point).map(|(_, t)| *t) };
            match secret { Some(t) => self.opened(&gone.point, t), None => self.failed_downstream(&gone.point, "refused downstream") }
        }
        Ok(())
    }
    /// a new lock for this node arrived on `id`: pay on, or take it if this node is the receiver
    fn forward(self: &Arc<Self>, id: [u8; 32], lock: PLock, onion: Option<Vec<u8>>) -> Result<()> {
        let onion = onion.ok_or_else(|| anyhow!("a lock without an onion"))?;
        let (hop, rest) = onion_peel(&self.secret(), &onion)?;
        let in_chain = { let _g = self.mu.lock().unwrap(); self.load(&id)?.chain };
        match hop {
            Hop::Final { amount } => {
                let inv = self.invoices.lock().unwrap().get(&lock.point).cloned().ok_or_else(|| anyhow!("no invoice for this payment"))?;
                if inv.paid { bail!("the invoice is already paid"); }
                if inv.chain != in_chain { bail!("the invoice is for another chain"); }
                if lock.amt < amount || amount < inv.amount { bail!("the payment is {} but the invoice asks {}", lock.amt.min(amount), inv.amount); }
                self.say(format!("invoice paid: {} on chain {}", lock.amt, in_chain));
                self.invoices.lock().unwrap().get_mut(&lock.point).unwrap().paid = true;
                self.fulfil_lock(id, &lock.point, inv.r)
            }
            Hop::Forward { chan, amount, expiry_time, offset } => {
                let out = self.load(&chan).map_err(|_| anyhow!("no channel {}", &id_hex(&chan)[..8]))?;
                if self.load(&id)?.oneway || out.oneway { bail!("a stream does not forward"); }
                // the fee: what this node asked for, at its own prices
                let need = quote(&self.cfg.prices, self.cfg.fee_ppm, self.cfg.spread_ppm, self.cfg.fee_base, amount, out.chain, in_chain).ok_or_else(|| anyhow!("no price for these chains"))?;
                if lock.amt < need { bail!("the lock is {} but forwarding {} needs {}", lock.amt, amount, need); }
                // time: the lock coming in must outlast the lock going out by this node's margin
                let in_time = self.expiry_time(in_chain, lock.expiry)?;
                if in_time < expiry_time + self.cfg.margin_secs { bail!("too little time: the incoming lock runs {}s past the outgoing one, this node needs {}", in_time.saturating_sub(expiry_time), self.cfg.margin_secs); }
                // P_out = P_in - d*G
                let d = scalar(&offset);
                let pin = mint::decode_point(&lock.point)?;
                let dg = ec::mul_g(&ec::params(), &d);
                let pout = mint::encode_point(ec::add(pin, ec::neg(dg)));
                let eh = self.expiry_height(out.chain, expiry_time)?;
                self.fwds.lock().unwrap().insert(pout, Fwd { in_chan: id, in_point: lock.point, offset });
                self.say(format!("forwarding {} (chain {}) -> {} (chain {}) over {}", lock.amt, in_chain, amount, out.chain, &id_hex(&chan)[..8]));
                let r = self.exchange(&chan, Some(&rest), &|c: &mut Chan| c.add_lock(&self.wallet, amount, pout, eh));
                if r.is_err() { self.fwds.lock().unwrap().remove(&pout); }
                r
            }
        }
    }
    fn fulfil_lock(self: &Arc<Self>, id: [u8; 32], point: &[u8; 41], t: [u8; 40]) -> Result<()> {
        let p = *point;
        self.exchange(&id, None, &|c: &mut Chan| { let i = c.locks.iter().position(|l| l.point == p).ok_or_else(|| anyhow!("the lock is gone"))?; c.fulfil(&self.wallet, i, t) })
    }
    fn give_back(self: &Arc<Self>, id: [u8; 32], point: &[u8; 41]) -> Result<()> {
        let p = *point;
        self.exchange(&id, None, &|c: &mut Chan| { let i = c.locks.iter().position(|l| l.point == p).ok_or_else(|| anyhow!("the lock is gone"))?; c.fail(&self.wallet, i) })
    }
    /// a scalar came back for the lock we made with `out_point`: open the lock upstream (or, as the sender, learn the receipt)
    fn opened(self: &Arc<Self>, out_point: &[u8; 41], t: [u8; 40]) {
        let fwd = self.fwds.lock().unwrap().remove(out_point);
        if let Some(f) = fwd {
            let p_in = (scalar(&t) + scalar(&f.offset)) % n();
            let p_in = crate::mint::s_bytes(&p_in);
            if let Err(e) = self.fulfil_lock(f.in_chan, &f.in_point, p_in) { self.say(format!("could not open the incoming lock: {e}")); }
            return;
        }
        let mut pays = self.pays.lock().unwrap();
        if let Some(p) = pays.get_mut(out_point) {
            let r = (scalar(&t) + n() - scalar(&p.sum_offsets)) % n();
            let ok = point_of(&r) == p.invoice_point;
            p.status = if ok { "done".into() } else { "failed".into() };
            p.receipt = Some(hex(&mint::s_bytes(&r)));
            if !ok { p.reason = "the scalar does not match the invoice".into(); }
            self.say(format!("payment {}: receipt {}", p.status, &hex(&mint::s_bytes(&r))[..16]));
        }
    }
    fn failed_downstream(self: &Arc<Self>, out_point: &[u8; 41], why: &str) {
        let fwd = self.fwds.lock().unwrap().remove(out_point);
        if let Some(f) = fwd {
            if let Err(e) = self.give_back(f.in_chan, &f.in_point) { self.say(format!("could not give the incoming lock back: {e}")); }
            return;
        }
        let mut pays = self.pays.lock().unwrap();
        if let Some(p) = pays.get_mut(out_point) { p.status = "failed".into(); p.reason = why.to_string(); self.say(format!("payment failed: {why}")); }
    }

    // ---- finding a route
    fn crawl(&self) -> Result<Vec<Value>> {
        let mut seen: HashMap<String, Value> = HashMap::new();
        let mut todo: Vec<(String, [u8; 41])> = self.all_chans().iter().filter_map(|c| Some((c.peer_addr.clone()?, peer_key(c)))).collect();
        let mut mine = self.info();
        mine["addr"] = json!(self.cfg.listen);
        seen.insert(hex(&self.pubkey()), mine);
        while let Some((addr, pk)) = todo.pop() {
            let Ok(v) = self.call(&addr, &pk, &json!({"t": "info"})) else { continue };
            let Some(pk) = v["pubkey"].as_str().map(|s| s.to_string()) else { continue };
            if seen.contains_key(&pk) { continue; }
            let mut v = v; v["addr"] = json!(addr);
            for c in v["channels"].as_array().into_iter().flatten() {
                // the far side of that node's channel: the key of the two that is not the node's own
                let (ka, kb) = (c["a"].as_str().and_then(|x| arr::<41>(x).ok()), c["b"].as_str().and_then(|x| arr::<41>(x).ok()));
                let node: Option<[u8; 41]> = v["pubkey"].as_str().and_then(|x| arr(x).ok());
                if let (Some(a), Some(ka), Some(kb)) = (c["peer_addr"].as_str(), ka, kb) { let other = if Some(ka) == node { kb } else { ka }; todo.push((a.to_string(), other)); }
            }
            seen.insert(pk, v);
        }
        Ok(seen.into_values().collect())
    }
    /// the cheapest route from this node to `dest` that ends in a channel of `chain`: [(channel id, from node key, to node key, chain, amount locked on it)]
    fn route(&self, nodes: &[Value], dest: &str, chain: u8, amount: u64) -> Result<Vec<([u8; 32], String, String, u8, u64)>> {
        let me = hex(&self.pubkey());
        // edges: channel id -> (a key, b key, chain, a's spendable, b's spendable, oneway)
        let mut chans: HashMap<String, (String, String, u8, Option<u64>, Option<u64>)> = HashMap::new();
        for nd in nodes {
            let pk = nd["pubkey"].as_str().unwrap_or("");
            for c in nd["channels"].as_array().into_iter().flatten() {
                if c["oneway"].as_bool() == Some(true) { continue; }
                let id = c["id"].as_str().unwrap_or("").to_string();
                let (a, b) = (c["a"].as_str().unwrap_or("").to_string(), c["b"].as_str().unwrap_or("").to_string());
                let e = chans.entry(id).or_insert((a.clone(), b.clone(), c["chain"].as_u64().unwrap_or(0) as u8, None, None));
                let mine = c["mine"].as_u64();
                if pk == a { e.3 = mine; } else if pk == b { e.4 = mine; }
            }
        }
        let by_node: HashMap<&str, &Value> = nodes.iter().filter_map(|n| n["pubkey"].as_str().map(|p| (p, n))).collect();
        type Path = Vec<(String, String, String, u8)>;   // (chan id, from, to, chain)
        let mut best: Option<(u64, Path, Vec<u64>)> = None;
        fn dfs(me: &str, dest: &str, chans: &HashMap<String, (String, String, u8, Option<u64>, Option<u64>)>, cur: &str, path: &mut Path, visited: &mut Vec<String>, out: &mut Vec<Path>) {
            if cur == dest { if !path.is_empty() { out.push(path.clone()); } return; }
            if path.len() >= 5 { return; }
            for (id, (a, b, ch, _, _)) in chans { let next = if a == cur { b } else if b == cur { a } else { continue };
                if visited.contains(next) { continue; }
                path.push((id.clone(), cur.to_string(), next.clone(), *ch)); visited.push(next.clone());
                dfs(me, dest, chans, next, path, visited, out);
                path.pop(); visited.pop(); }
        }
        let mut paths = vec![];
        dfs(&me, dest, &chans, &me, &mut vec![], &mut vec![me.clone()], &mut paths);
        for p in paths {
            if p.last().map(|x| x.3) != Some(chain) { continue; }
            // amounts from the receiver backwards
            let k = p.len();
            let mut amts = vec![0u64; k];
            amts[k - 1] = amount;
            let mut ok = true;
            for i in (0..k - 1).rev() {
                let node = by_node.get(p[i].2.as_str());
                let Some(nd) = node else { ok = false; break };
                let prices: HashMap<u8, u64> = nd["prices"].as_object().map(|m| m.iter().filter_map(|(k, v)| Some((k.parse().ok()?, v.as_u64()?))).collect()).unwrap_or_default();
                match quote(&prices, nd["fee_ppm"].as_u64().unwrap_or(0), nd["spread_ppm"].as_u64().unwrap_or(0), nd["fee_base"].as_u64().unwrap_or(0), amts[i + 1], p[i + 1].3, p[i].3) { Some(q) => amts[i] = q, None => { ok = false; break } }
            }
            if !ok { continue; }
            // can each sender afford its lock?
            for (i, (id, from, _, _)) in p.iter().enumerate() {
                let e = &chans[id];
                let spend = if *from == e.0 { e.3 } else { e.4 };
                if spend.map_or(true, |s| s < amts[i]) { ok = false; break; }
            }
            if !ok { continue; }
            if best.as_ref().map_or(true, |(_, bp, ba)| amts[0] < ba[0] || (amts[0] == ba[0] && p.len() < bp.len())) { best = Some((amts[0], p.clone(), amts.clone())); }
        }
        let (_, p, amts) = best.ok_or_else(|| anyhow!("no route with enough balance to pay {amount} on chain {chain}"))?;
        p.iter().enumerate().map(|(i, (id, f, t, ch))| Ok((arr::<32>(id)?, f.clone(), t.clone(), *ch, amts[i]))).collect()
    }
    fn pay(self: &Arc<Self>, invoice: &str) -> Result<Value> {
        let v: Vec<&str> = invoice.split(':').collect();
        if v.len() != 5 || v[0] != "zeninv" { bail!("not an invoice"); }
        let (ipoint, amount, chain, dest): ([u8; 41], u64, u8, &str) = (arr(v[1])?, v[2].parse()?, v[3].parse()?, v[4]);
        let nodes = self.crawl()?;
        let route = self.route(&nodes, dest, chain, amount)?;
        let k = route.len();
        // lock times: the last lock runs `base` seconds, each earlier hop adds that hop's margin
        let base = 900u64;
        let mut times = vec![0u64; k];
        times[k - 1] = now() + base;
        for i in (0..k - 1).rev() {
            let m = nodes.iter().find(|nd| nd["pubkey"].as_str() == Some(route[i].2.as_str())).and_then(|nd| nd["margin_secs"].as_u64()).unwrap_or(120);
            times[i] = times[i + 1] + m + 30;
        }
        // offsets d_1..d_(k-1): P_i = P_(i+1) + d_i*G, P_k = the invoice point
        let offsets: Vec<BigUint> = (0..k - 1).map(|_| rand_scalar()).collect();
        let mut points = vec![ipoint; k];
        for i in (0..k - 1).rev() {
            let q = mint::decode_point(&points[i + 1])?;
            points[i] = mint::encode_point(ec::add(q, ec::mul_g(&ec::params(), &offsets[i])));
        }
        let sum = offsets.iter().fold(BigUint::ZERO, |a, d| (a + d) % n());
        // the onion for the nodes after this one: hop i (i = 1..k-1) is the node at the end of route[i-1]
        let mut hops = vec![];
        for i in 0..k {
            let node_pk: [u8; 41] = arr(&route[i].2)?;
            let hop = if i + 1 < k { Hop::Forward { chan: route[i + 1].0, amount: route[i + 1].4, expiry_time: times[i + 1], offset: mint::s_bytes(&offsets[i]) } } else { Hop::Final { amount: route[k - 1].4 } };
            hops.push((node_pk, hop));
        }
        let onion = onion_build(&hops)?;
        let first = route[0].0;
        let eh = self.expiry_height(route[0].3, times[0])?;
        let amt0 = route[0].4;
        self.pays.lock().unwrap().insert(points[0], Pay { sum_offsets: mint::s_bytes(&sum), invoice_point: ipoint, status: "pending".into(), receipt: None, reason: String::new(), chan: first, amount: amt0 });
        self.say(format!("paying {amount} on chain {chain}: {} hops, {} locked on the first channel (chain {})", k, amt0, route[0].3));
        let p0 = points[0];
        if let Err(e) = self.exchange(&first, Some(&onion), &|c: &mut Chan| c.add_lock(&self.wallet, amt0, p0, eh)) {
            self.pays.lock().unwrap().remove(&points[0]);
            bail!("the first hop refused: {e}");
        }
        Ok(json!({"point": hex(&points[0]), "hops": k, "locked": amt0, "route": route.iter().map(|r| json!({"chan": id_hex(&r.0), "chain": r.3, "amount": r.4})).collect::<Vec<_>>()}))
    }

    // ---- requests
    /// a request from the wire: sealed, or plain from this machine only (the CLI)
    fn handle_wire(self: &Arc<Self>, req: &Value, local: bool) -> Value {
        if req["hs"].is_string() {
            let opened = crate::transport::open_request(&self.secret(), &self.pubkey(), req, now());
            return match opened {
                Ok(o) if !self.seen.first(&o.nonce(), now()) => { let _ = o; json!({"err": "this request was already seen"}) }
                Ok(o) => { let ans = self.handle(&o.req, false, Some(o.caller)); crate::transport::seal_answer(&o, &ans).unwrap_or_else(|e| json!({"err": e.to_string()})) }
                Err(e) => json!({"err": e.to_string()}),
            };
        }
        if !local { return json!({"err": "this node talks over the encrypted transport only"}); }
        self.handle(req, true, None)
    }
    /// the caller of a channel message must be that channel's other side
    fn authz(&self, id: &[u8; 32], caller: Option<[u8; 41]>) -> Result<()> {
        let caller = caller.ok_or_else(|| anyhow!("an authenticated peer is required"))?;
        let c = self.load(id).map_err(|_| anyhow!("no such channel"))?;
        if peer_key(&c) != caller { bail!("the caller is not this channel's peer"); }
        Ok(())
    }
    fn handle(self: &Arc<Self>, req: &Value, local: bool, caller: Option<[u8; 41]>) -> Value {
        let r: Result<Value> = (|| match req["t"].as_str().unwrap_or("") {
            "info" if local || caller.is_some() => Ok(self.info()),
            "prop" => { self.authz(&arr(req["chan"].as_str().unwrap_or(""))?, caller)?; self.on_prop(req) }
            "sync" => {
                let id: [u8; 32] = arr(req["chan"].as_str().unwrap_or(""))?;
                self.authz(&id, caller)?;
                let c = self.load(&id).map_err(|_| anyhow!("no such channel"))?;
                if c.seq > req["seq"].as_u64().unwrap_or(u64::MAX) { Ok(json!({"seq": c.seq, "state": hex(&c.state_blob())})) } else { Ok(json!({"seq": c.seq})) }
            }
            "closesign" => { self.authz(&arr(req["chan"].as_str().unwrap_or(""))?, caller)?; self.on_closesign(req) }
            "close" if local => self.close_chan(req["chan"].as_str().unwrap_or("")).map(|op| json!({"op": op})),
            "sync_all" if local => { let mut n = 0; for c in self.all_chans() { if self.sync_one(&c.id).unwrap_or(false) { n += 1; } } Ok(json!({"caught_up": n})) }
            "invoice" if local => {
                let (amount, chain): (u64, u8) = (req["amount"].as_u64().ok_or_else(|| anyhow!("amount?"))?, req["chain"].as_u64().ok_or_else(|| anyhow!("chain?"))? as u8);
                let r = rand_scalar(); let p = point_of(&r);
                self.invoices.lock().unwrap().insert(p, Invoice { r: mint::s_bytes(&r), amount, chain, paid: false });
                Ok(json!({"invoice": format!("zeninv:{}:{}:{}:{}", hex(&p), amount, chain, hex(&self.pubkey()))}))
            }
            "pay" if local => self.pay(req["invoice"].as_str().unwrap_or("")),
            "paystatus" if local => {
                let p: [u8; 41] = arr(req["point"].as_str().unwrap_or(""))?;
                let pays = self.pays.lock().unwrap();
                let x = pays.get(&p).ok_or_else(|| anyhow!("no such payment"))?;
                Ok(json!({"status": x.status, "receipt": x.receipt, "reason": x.reason}))
            }
            "status" if local => {
                let inv: Vec<Value> = self.invoices.lock().unwrap().iter().map(|(p, i)| json!({"point": &hex(p)[..16], "amount": i.amount, "chain": i.chain, "paid": i.paid})).collect();
                let chans: Vec<Value> = self.all_chans().iter().map(|c| json!({"id": &id_hex(&c.id)[..8], "chain": c.chain, "update": c.seq, "mine": c.mine(), "theirs": c.theirs(), "locks": c.locks.len(), "peer": c.peer_addr})).collect();
                Ok(json!({"name": self.cfg.name, "channels": chans, "invoices": inv, "log": self.log.lock().unwrap().iter().rev().take(12).cloned().collect::<Vec<_>>()}))
            }
            other => bail!("unknown or not allowed request {other}"),
        })();
        match r { Ok(v) => v, Err(e) => json!({"err": e.to_string()}) }
    }
}

pub fn run(dir: &Path) -> Result<()> {
    let node: Node = Arc::new(RNode::open(dir)?);
    let l = TcpListener::bind(&node.cfg.listen)?;
    eprintln!("[{}] listening on {} | node key {}", node.cfg.name, l.local_addr()?, &hex(&node.pubkey())[..16]);
    // catch up with every peer now and then: a crash or a lost acknowledgement leaves this side one update behind
    { let node = node.clone(); std::thread::spawn(move || loop { std::thread::sleep(Duration::from_secs(3)); for c in node.all_chans() { let _ = node.sync_one(&c.id); } std::thread::sleep(Duration::from_secs(17)); }); }
    // the guard: answers an old-state close, settles when the window is over, and closes on chain when a point lock nears its expiry
    if node.cfg.guard_blocks > 0 {
        let node = node.clone();
        std::thread::spawn(move || {
            let mut done = std::collections::HashSet::new();
            // a point lock is normally open for seconds; only one that has stayed open (the peer is silent) can trigger a close
            let mut since: HashMap<([u8; 32], u64), std::time::Instant> = HashMap::new();
            loop {
                std::thread::sleep(Duration::from_secs(2));
                for c in node.all_chans() {
                    let Some((api, p2p)) = node.cfg.chains.get(&c.chain) else { continue };
                    let Ok((sa, _)) = crate::tx::split_node(&format!("{p2p},{api}")) else { continue };
                    let c = { let _g = node.mu.lock().unwrap(); node.load(&c.id).unwrap_or(c) };
                    since.retain(|(id, seq), _| *id != c.id || *seq == c.seq);
                    let stuck = !c.locks.is_empty() && since.entry((c.id, c.seq)).or_insert_with(std::time::Instant::now).elapsed() >= Duration::from_secs(node.cfg.guard_wait);
                    for line in crate::channel::guard(&c, &node.wallet, sa, api, &mut done, if stuck { Some(node.cfg.guard_blocks) } else { None }) { node.say(line); }
                }
            }
        });
    }
    let live = Arc::new(std::sync::atomic::AtomicUsize::new(0));
    for s in l.incoming().flatten() {
        let node = node.clone();
        use std::sync::atomic::Ordering::SeqCst;
        if live.fetch_add(1, SeqCst) >= MAX_WIRE_CONNS { live.fetch_sub(1, SeqCst); continue; }
        let live = live.clone();
        std::thread::spawn(move || {
            struct Done(Arc<std::sync::atomic::AtomicUsize>);
            impl Drop for Done { fn drop(&mut self) { self.0.fetch_sub(1, SeqCst); } }
            let _done = Done(live);
            let local = s.peer_addr().map_or(false, |a| a.ip().is_loopback());
            let _ = s.set_read_timeout(Some(Duration::from_secs(30)));
            let mut line = String::new();
            let mut rd = BufReader::new(&s).take_line_limited();
            if rd.read_line(&mut line).is_err() { return; }
            let resp = match serde_json::from_str::<Value>(line.trim()) { Ok(req) => node.handle_wire(&req, local), Err(_) => json!({"err": "not JSON"}) };
            let mut s = s; let _ = writeln!(s, "{}", resp);
        });
    }
    Ok(())
}
trait LimitedLine { fn take_line_limited(self) -> std::io::Take<Self> where Self: Sized + std::io::Read; }
impl<R: std::io::Read> LimitedLine for BufReader<R> { fn take_line_limited(self) -> std::io::Take<Self> { std::io::Read::take(self, 1 << 20) } }

pub fn rnode_main() -> Result<()> {
    let a: Vec<String> = std::env::args().collect();
    let arg = |i: usize, what: &str| a.get(i).cloned().ok_or_else(|| anyhow!("missing {what}"));
    let dir = PathBuf::from(arg(3, "dir")?);
    let listen = || -> Result<String> { Ok(Cfg::parse(&std::fs::read_to_string(dir.join("node.conf"))?)?.listen) };
    match a.get(2).map(|s| s.as_str()) {
        Some("run") => run(&dir)?,
        Some("add-channel") => {
            let mut c = Chan::load(Path::new(&arg(4, "channel file")?))?;
            c.peer_addr = Some(arg(5, "peer address")?);
            std::fs::create_dir_all(dir.join("channels"))?;
            c.save(&dir.join("channels").join(format!("{}.chan", id_hex(&c.id))))?;
            println!("channel {} added (chain {}, peer {})", &id_hex(&c.id)[..8], c.chain, c.peer_addr.as_deref().unwrap_or(""));
        }
        Some("invoice") => {
            let v = rpc(&listen()?, &json!({"t": "invoice", "amount": arg(4, "amount")?.parse::<u64>()?, "chain": arg(5, "chain")?.parse::<u64>()?}))?;
            println!("{}", v["invoice"].as_str().ok_or_else(|| anyhow!("{}", v["err"]))?);
        }
        Some("pay") => {
            let addr = listen()?;
            let v = rpc(&addr, &json!({"t": "pay", "invoice": arg(4, "invoice")?}))?;
            if let Some(e) = v["err"].as_str() { bail!("{e}"); }
            println!("route: {} hop(s), {} locked on the first channel", v["hops"], v["locked"]);
            for r in v["route"].as_array().into_iter().flatten() { println!("  channel {} (chain {}) carries {}", &r["chan"].as_str().unwrap_or("")[..8], r["chain"], r["amount"]); }
            for _ in 0..120 {
                std::thread::sleep(Duration::from_millis(500));
                let s = rpc(&addr, &json!({"t": "paystatus", "point": v["point"]}))?;
                match s["status"].as_str() {
                    Some("done") => { println!("paid | receipt (the invoice secret) {}", s["receipt"].as_str().unwrap_or("")); return Ok(()); }
                    Some("failed") => bail!("payment failed: {}", s["reason"].as_str().unwrap_or("")),
                    _ => {}
                }
            }
            bail!("still pending after 60 s");
        }
        Some("close") => { let v = rpc(&listen()?, &json!({"t": "close", "chan": arg(4, "channel id (start of it)")?}))?; println!("{}", v["op"].as_str().map(|o| format!("joint close sent | operation id {o}")).ok_or_else(|| anyhow!("{}", v["err"]))?); }
        Some("sync") => { let v = rpc(&listen()?, &json!({"t": "sync_all"}))?; println!("caught up on {} channel(s)", v["caught_up"]); }
        Some("status") => println!("{}", serde_json::to_string_pretty(&rpc(&listen()?, &json!({"t": "status"}))?)?),
        _ => bail!("usage: rnode <run|add-channel|invoice|pay|close|sync|status> <dir> ..."),
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn an_onion_reaches_each_hop_in_turn_and_only_the_right_node_can_open_its_layer() {
        let ks: Vec<mint::Key> = (1..=3u32).map(|i| mint::Key::from_secret(BigUint::from(1000 + i))).collect();
        let sk = |k: &mint::Key| { let l = k.secret_limbs(); let mut b = vec![]; for x in l { b.extend(x.to_le_bytes()); } BigUint::from_bytes_le(&b) };
        let hops = vec![
            (mint::encode_point(ks[0].a), Hop::Forward { chan: [1; 32], amount: 500, expiry_time: 7000, offset: mint::s_bytes(&BigUint::from(5u32)) }),
            (mint::encode_point(ks[1].a), Hop::Forward { chan: [2; 32], amount: 400, expiry_time: 6000, offset: mint::s_bytes(&BigUint::from(6u32)) }),
            (mint::encode_point(ks[2].a), Hop::Final { amount: 390 }),
        ];
        let o = onion_build(&hops).unwrap();
        assert!(onion_peel(&sk(&ks[1]), &o).is_err(), "the second hop cannot open the first layer");
        let (h0, rest) = onion_peel(&sk(&ks[0]), &o).unwrap();
        assert_eq!(h0, hops[0].1);
        let (h1, rest) = onion_peel(&sk(&ks[1]), &rest).unwrap();
        assert_eq!(h1, hops[1].1);
        let (h2, rest) = onion_peel(&sk(&ks[2]), &rest).unwrap();
        assert_eq!((h2, rest.len()), (hops[2].1.clone(), 0));
        let mut bad = o.clone(); let l = bad.len(); bad[l - 1] ^= 1;
        assert!(onion_peel(&sk(&ks[0]), &bad).is_err(), "a changed byte is noticed");
    }
    #[test]
    fn a_stream_node_asks_for_the_other_metal_at_its_price_plus_fee_and_spread() {
        let prices: HashMap<u8, u64> = [(1, 100), (2, 10), (3, 1)].into_iter().collect();
        // 1000 of chain 2 (price 10) costs 100 of chain 1 (price 100) before fees: +0.1% routing +0.3% spread +1
        assert_eq!(quote(&prices, 1000, 3000, 1, 1000, 2, 1), Some(100 + 1 + 1));
        assert_eq!(quote(&prices, 1000, 3000, 1, 1_000_000, 2, 1), Some(100_000 + 400 + 1));
        // within a chain no spread
        assert_eq!(quote(&prices, 1000, 3000, 1, 1_000_000, 2, 2), Some(1_000_000 + 1000 + 1));
        assert_eq!(quote(&prices, 1000, 3000, 1, 5, 2, 9), None);
    }
    #[test]
    fn offsets_make_each_hops_point_different_and_the_receivers_secret_opens_them_all() {
        let r = rand_scalar(); let d1 = rand_scalar(); let d2 = rand_scalar();
        let g = |k: &BigUint| ec::mul_g(&ec::params(), k);
        let p3 = g(&r);
        let p2 = ec::add(p3, g(&d2)); let p1 = ec::add(p2, g(&d1));
        assert!(p1 != p2 && p2 != p3);
        // the receiver's scalar r opens P3; the node before adds d2 to open P2, the sender's node adds d1 to open P1
        let t2 = (&r + &d2) % n(); let t1 = (&t2 + &d1) % n();
        assert_eq!(g(&t2), p2); assert_eq!(g(&t1), p1);
        // the sender recovers r from the scalar that opened the first lock
        assert_eq!((&t1 + n() * 2u32 - &d1 - &d2) % n(), r);
    }
}
