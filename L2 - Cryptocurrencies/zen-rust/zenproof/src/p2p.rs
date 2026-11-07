// Zen node, stage 2: peers and a Stratum server (Justus L. Ludovic).
//
// Peer protocol (TCP, frames of u32 length + u8 type + payload, at most 8 MiB):
//   HELLO(genesis hash, height, tip hash)   sent by both sides on connect; a different genesis ends the connection
//   INV(hash)                               "I have this block"; the peer asks for it if it does not
//   GETBLOCK(hash)                          ask for a block
//   BLOCK(bytes)                            a block (Block::encode)
//   TX(bytes)                               a signed payment (154 B); checked against the tip, kept in the mempool, relayed if new
//   TXACK(text)                             the answer to a TX: empty = taken, else the reason it was not
//   GETACCT(address)                        wallet query: ACCT(found, balance, nonce, next nonce, height) answers
// Sync is the same exchange repeated: a node that hears of a tip it does not have asks for it; a block whose parent
// is unknown waits as an orphan and the parent is asked for next, so a fresh node walks back to genesis and then
// the orphans attach in order. Every block is fully validated (Chain::validate) before it is stored or relayed;
// a peer that sends an invalid block or a malformed frame is disconnected.
//
// Stratum v1 server: mining.subscribe, mining.authorize, mining.notify (a new job when the best tip changes),
// mining.submit. A share that meets the block target is assembled into a sealed block (`Block::with_share`) and
// submitted like any other block. Share difficulty below the block target (pool accounting) is not in stage 2.
use crate::mempool::{Admit, Mempool};
use crate::node::{Added, Block, Chain, Lookup, Node, Outcome};
use crate::tx::{self, SignedPay};
use crate::seal;
use anyhow::{anyhow, bail, Result};
use std::io::{BufRead, BufReader, Read, Write};
use std::collections::{HashMap, HashSet};
use std::net::{IpAddr, SocketAddr, TcpListener, TcpStream};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{mpsc, Arc, Mutex};
use std::time::{Duration, Instant};

/// the largest frame: a block (stamp up to MAX_STAMP, data up to MAX_DATA, tickets) with room to spare
const MAX_FRAME: usize = (crate::node::MAX_STAMP + crate::node::MAX_DATA + (1 << 20)) as usize;
const SEND_QUEUE: usize = 256;
const MAX_ADDR: usize = 32;
const MAX_KNOWN_ADDRS: usize = 1000;
const WINDOW_SECS: u64 = 10;
const BAN_SCORE: u32 = 100;

#[derive(Debug, Clone)]
pub enum Msg { Hello { genesis: [u8; 32], height: u64, tip: [u8; 32], port: u16 }, Inv([u8; 32]), GetBlock([u8; 32]), Block(Vec<u8>),
    Tx(Vec<u8>), TxAck(String), GetAcct([u8; 32]), Acct { found: bool, balance: u64, nonce: u64, next_nonce: u64, height: u64 },
    GetNext(Vec<[u8; 32]>), GetAddr, Addr(Vec<SocketAddr>),
    /// a signed operation (locks.rs), answered with TxAck
    Op(Vec<u8>) }
impl Msg {
    fn encode(&self) -> Vec<u8> {
        match self {
            Msg::Hello { genesis, height, tip, port } => { let mut v = vec![1]; v.extend(genesis); v.extend(height.to_le_bytes()); v.extend(tip); v.extend(port.to_le_bytes()); v }
            Msg::Inv(h) => { let mut v = vec![2]; v.extend(h); v }
            Msg::GetBlock(h) => { let mut v = vec![3]; v.extend(h); v }
            Msg::Block(b) => { let mut v = vec![4]; v.extend(b); v }
            Msg::Tx(b) => { let mut v = vec![5]; v.extend(b); v }
            Msg::TxAck(t) => { let mut v = vec![6]; v.extend(t.as_bytes().iter().take(200)); v }
            Msg::GetAcct(a) => { let mut v = vec![7]; v.extend(a); v }
            Msg::Acct { found, balance, nonce, next_nonce, height } => { let mut v = vec![8, *found as u8]; for x in [balance, nonce, next_nonce, height] { v.extend(x.to_le_bytes()); } v }
            Msg::GetNext(l) => { let mut v = vec![9]; for h in l.iter().take(32) { v.extend(h); } v }
            Msg::GetAddr => vec![10],
            Msg::Op(b) => { let mut v = vec![12]; v.extend(b); v }
            Msg::Addr(a) => { let mut v = vec![11]; for x in a.iter().take(MAX_ADDR) { if let SocketAddr::V4(x) = x { v.extend(x.ip().octets()); v.extend(x.port().to_le_bytes()); } } v }
        }
    }
    fn decode(b: &[u8]) -> Result<Msg> {
        let (t, p) = b.split_first().ok_or_else(|| anyhow!("empty frame"))?;
        let h32 = |x: &[u8]| -> Result<[u8; 32]> { Ok(x.try_into().map_err(|_| anyhow!("bad hash length"))?) };
        Ok(match t {
            1 if p.len() == 74 => Msg::Hello { genesis: h32(&p[..32])?, height: u64::from_le_bytes(p[32..40].try_into()?), tip: h32(&p[40..72])?, port: u16::from_le_bytes(p[72..74].try_into()?) },
            2 => Msg::Inv(h32(p)?),
            3 => Msg::GetBlock(h32(p)?),
            4 => Msg::Block(p.to_vec()),
            5 if p.len() == tx::TX_BYTES => Msg::Tx(p.to_vec()),
            6 => Msg::TxAck(String::from_utf8_lossy(p).into_owned()),
            7 => Msg::GetAcct(h32(p)?),
            8 if p.len() == 33 => { let u = |i: usize| u64::from_le_bytes(p[1 + 8 * i..9 + 8 * i].try_into().unwrap()); Msg::Acct { found: p[0] == 1, balance: u(0), nonce: u(1), next_nonce: u(2), height: u(3) } }
            9 if p.len() % 32 == 0 && p.len() <= 32 * 32 => Msg::GetNext(p.chunks(32).map(|c| h32(c)).collect::<Result<_>>()?),
            10 if p.is_empty() => Msg::GetAddr,
            11 if p.len() % 6 == 0 && p.len() <= 6 * MAX_ADDR => Msg::Addr(p.chunks(6).map(|c| SocketAddr::from((std::net::Ipv4Addr::new(c[0], c[1], c[2], c[3]), u16::from_le_bytes([c[4], c[5]])))).collect()),
            12 if p.len() <= crate::locks::MAX_SIGNED_OP => Msg::Op(p.to_vec()),
            _ => bail!("unknown or malformed message {t}"),
        })
    }
}
fn write_msg(w: &mut impl Write, m: &Msg) -> std::io::Result<()> {
    let b = m.encode();
    w.write_all(&(b.len() as u32).to_le_bytes())?; w.write_all(&b)?; w.flush()
}
/// An `std::io::Error` inside the error means the connection failed (closed, timed out); anything else is the peer's fault.
fn read_msg(r: &mut impl Read) -> Result<Msg> {
    let mut l = [0u8; 4]; r.read_exact(&mut l)?;
    let n = u32::from_le_bytes(l) as usize;
    if n == 0 || n > MAX_FRAME { bail!("frame of {n} bytes"); }
    let mut b = vec![0u8; n]; r.read_exact(&mut b)?;
    Msg::decode(&b)
}
fn is_io(e: &anyhow::Error) -> bool { e.downcast_ref::<std::io::Error>().is_some() }
pub fn now() -> u32 { std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_secs() as u32).unwrap_or(0) }

/// The limits a node puts on its peers (SPEC 10.7).
#[derive(Debug, Clone)]
pub struct Limits {
    pub max_inbound: usize, pub max_outbound: usize, pub per_ip: usize,
    /// seconds a banned address is refused
    pub ban_secs: u64,
    /// seconds a new connection has to say hello (wallets and peers alike)
    pub hello_secs: u64,
    /// seconds of silence after which a connection is closed
    pub idle_secs: u64,
    /// messages per 10 seconds before the peer is penalized
    pub msgs_per_window: u32,
}
impl Default for Limits { fn default() -> Limits { Limits { max_inbound: 32, max_outbound: 8, per_ip: 4, ban_secs: 600, hello_secs: 15, idle_secs: 1200, msgs_per_window: 1000 } } }

struct PeerInfo { id: u64, tx: mpsc::SyncSender<Msg>, ip: IpAddr, inbound: bool, addr: Option<SocketAddr> }
/// what the reader thread of one connection remembers
struct Session { id: u64, ip: IpAddr, score: u32, greeted: bool, peer_height: u64, asked_addr: bool, win_start: Instant, win_count: u32 }
fn push(tx: &mpsc::SyncSender<Msg>, m: Msg) { let _ = tx.try_send(m); }       // a peer that cannot keep up misses messages and is closed by the write timeout

#[derive(Clone)]
pub struct Net {
    pub node: Arc<Mutex<Node>>,
    peers: Arc<Mutex<Vec<PeerInfo>>>,
    next_id: Arc<AtomicU64>,
    pub genesis: [u8; 32],
    /// signed payments waiting for a block
    pub pool: Arc<Mutex<Mempool>>,
    /// blocks refused (invalid) and peers dropped, for tests and logs
    pub refused: Arc<AtomicU64>,
    pub limits: Limits,
    bans: Arc<Mutex<HashMap<IpAddr, Instant>>>,
    /// addresses of peers that listen, learned from hellos and ADDR messages
    addrs: Arc<Mutex<HashSet<SocketAddr>>>,
    my_addr: Arc<Mutex<Option<SocketAddr>>>,
    /// set when this node runs beside the other two chains: what `/api/chains` shows
    pub chains: Arc<Mutex<Option<Arc<dyn Fn() -> serde_json::Value + Send + Sync>>>>,
    /// signed operations (locks, orders) waiting for a block
    pub ops: Arc<Mutex<crate::locks::OpPool>>,
}
impl Net {
    pub fn new(node: Node) -> Net {
        let genesis = node.network_id();   // chain, parameters and genesis allocation: peers that differ in any of them cannot agree on a block
        Net { node: Arc::new(Mutex::new(node)), peers: Arc::new(Mutex::new(vec![])), next_id: Arc::new(AtomicU64::new(1)), genesis, pool: Arc::new(Mutex::new(Mempool::new(50_000))),
              refused: Arc::new(AtomicU64::new(0)), limits: Limits::default(), bans: Arc::new(Mutex::new(HashMap::new())), addrs: Arc::new(Mutex::new(HashSet::new())), my_addr: Arc::new(Mutex::new(None)), chains: Arc::new(Mutex::new(None)), ops: Arc::new(Mutex::new(crate::locks::OpPool::new(2000))) }
    }
    pub fn with_limits(mut self, l: Limits) -> Net { self.limits = l; self }
    pub fn peer_count(&self) -> usize { self.peers.lock().unwrap().len() }
    /// the connected peers: address, whether they connected to us, and the address they listen on when known
    pub fn peer_list(&self) -> Vec<(IpAddr, bool, Option<SocketAddr>)> { self.peers.lock().unwrap().iter().map(|p| (p.ip, p.inbound, p.addr)).collect() }
    pub fn known_addr_count(&self) -> usize { self.addrs.lock().unwrap().len() }
    pub fn height(&self) -> u64 { self.node.lock().unwrap().tip().height }
    pub fn best(&self) -> [u8; 32] { self.node.lock().unwrap().best }
    pub fn known_addrs(&self) -> usize { self.addrs.lock().unwrap().len() }
    pub fn is_banned(&self, ip: IpAddr) -> bool {
        let mut b = self.bans.lock().unwrap();
        match b.get(&ip) { Some(t) if t.elapsed().as_secs() < self.limits.ban_secs => true, Some(_) => { b.remove(&ip); false } None => false }
    }
    fn ban(&self, ip: IpAddr) { self.bans.lock().unwrap().insert(ip, Instant::now()); }

    pub fn listen(&self, addr: &str) -> Result<SocketAddr> {
        let l = TcpListener::bind(addr)?;
        let a = l.local_addr()?;
        *self.my_addr.lock().unwrap() = Some(a);
        let me = self.clone();
        std::thread::spawn(move || {
            for s in l.incoming().flatten() {
                let Ok(pa) = s.peer_addr() else { continue };
                if me.is_banned(pa.ip()) { continue; }
                { let ps = me.peers.lock().unwrap();
                  if ps.iter().filter(|p| p.inbound).count() >= me.limits.max_inbound || ps.iter().filter(|p| p.inbound && p.ip == pa.ip()).count() >= me.limits.per_ip { continue; } }
                me.spawn_peer(s, true);
            }
        });
        Ok(a)
    }
    pub fn connect(&self, addr: SocketAddr) -> Result<()> {
        if self.is_banned(addr.ip()) { bail!("that address is banned"); }
        let s = TcpStream::connect_timeout(&addr, Duration::from_secs(5))?;
        self.spawn_peer(s, false);
        if let Some(p) = self.peers.lock().unwrap().last_mut() { if !p.inbound { p.addr = Some(addr); } }
        Ok(())
    }
    /// connect to known addresses until there are `max_outbound` outbound peers
    pub fn maintain(&self) {
        let (out, connected): (usize, HashSet<SocketAddr>) = { let ps = self.peers.lock().unwrap(); (ps.iter().filter(|p| !p.inbound).count(), ps.iter().filter_map(|p| p.addr).collect()) };
        if out >= self.limits.max_outbound { return; }
        let me = *self.my_addr.lock().unwrap();
        let cands: Vec<SocketAddr> = self.addrs.lock().unwrap().iter().copied().filter(|a| !connected.contains(a) && Some(*a) != me && !self.is_banned(a.ip())).take(self.limits.max_outbound - out).collect();
        for a in cands {
            if self.connect(a).is_err() { self.addrs.lock().unwrap().remove(&a); }
        }
    }
    /// run `maintain` in the background
    pub fn spawn_maintainer(&self, every: Duration) { let me = self.clone(); std::thread::spawn(move || loop { std::thread::sleep(every); me.maintain(); }); }

    fn hello(&self) -> Msg {
        let n = self.node.lock().unwrap();
        let port = self.my_addr.lock().unwrap().map_or(0, |a| a.port());
        Msg::Hello { genesis: self.genesis, height: n.tip().height, tip: n.best, port }
    }

    fn spawn_peer(&self, stream: TcpStream, inbound: bool) {
        let Ok(pa) = stream.peer_addr() else { return };
        let id = self.next_id.fetch_add(1, Ordering::SeqCst);
        let (tx, rx) = mpsc::sync_channel::<Msg>(SEND_QUEUE);
        self.peers.lock().unwrap().push(PeerInfo { id, tx: tx.clone(), ip: pa.ip(), inbound, addr: None });
        let mut ws = match stream.try_clone() { Ok(s) => s, Err(_) => return };
        let _ = ws.set_write_timeout(Some(Duration::from_secs(30)));
        std::thread::spawn(move || { for m in rx { if write_msg(&mut ws, &m).is_err() { break; } } let _ = ws.shutdown(std::net::Shutdown::Both); });
        let me = self.clone();
        std::thread::spawn(move || {
            push(&tx, me.hello());
            let mut rs = stream;
            let _ = rs.set_read_timeout(Some(Duration::from_secs(me.limits.hello_secs)));
            let mut sess = Session { id, ip: pa.ip(), score: 0, greeted: false, peer_height: 0, asked_addr: false, win_start: Instant::now(), win_count: 0 };
            loop {
                match read_msg(&mut rs) {
                    Ok(m) => {
                        // a rate limit per window; the score cools down 5 points per window
                        if sess.win_start.elapsed().as_secs() >= WINDOW_SECS { sess.win_start = Instant::now(); sess.win_count = 0; sess.score = sess.score.saturating_sub(5); }
                        sess.win_count += 1;
                        let r = if sess.win_count > me.limits.msgs_per_window { me.punish(&mut sess, 10, "too many messages") } else { Ok(()) };   // 10 points per message over the limit
                        let r = r.and_then(|_| {
                            // before the hello only the hello and wallet requests are taken
                            if !sess.greeted && !matches!(m, Msg::Hello { .. } | Msg::Tx(_) | Msg::Op(_) | Msg::GetAcct(_)) { return me.punish(&mut sess, BAN_SCORE, "message before hello"); }
                            me.handle(&mut sess, &tx, m)
                        });
                        if let Err(_e) = r { me.refused.fetch_add(1, Ordering::SeqCst); break; }
                        if sess.greeted { let _ = rs.set_read_timeout(Some(Duration::from_secs(me.limits.idle_secs))); }
                    }
                    Err(e) => { if !is_io(&e) { let _ = me.punish(&mut sess, BAN_SCORE, "malformed frame"); me.refused.fetch_add(1, Ordering::SeqCst); } break; }
                }
            }
            let _ = rs.shutdown(std::net::Shutdown::Both);
            me.peers.lock().unwrap().retain(|p| p.id != id);
        });
    }

    /// add penalty points; at BAN_SCORE the address is banned and the connection ends
    fn punish(&self, s: &mut Session, pts: u32, _why: &str) -> Result<()> {
        s.score += pts;
        if s.score >= BAN_SCORE { self.ban(s.ip); bail!("banned: {_why}"); }
        Ok(())
    }

    fn handle(&self, s: &mut Session, tx: &mpsc::SyncSender<Msg>, msg: Msg) -> Result<()> {
        match msg {
            Msg::Hello { genesis, tip, height, port } => {
                if genesis != self.genesis { bail!("another chain"); }
                if s.greeted { return self.punish(s, 20, "second hello"); }
                s.greeted = true; s.peer_height = height;
                if port != 0 {
                    let a = SocketAddr::new(s.ip, port);
                    if let Some(p) = self.peers.lock().unwrap().iter_mut().find(|p| p.id == s.id) { if p.addr.is_none() { p.addr = Some(a); } }
                    let mut k = self.addrs.lock().unwrap();
                    if k.len() < MAX_KNOWN_ADDRS { k.insert(a); }
                }
                let (known, mine, loc) = { let n = self.node.lock().unwrap(); (n.have(&tip), n.tip().height, n.locator()) };
                if !known { push(tx, Msg::GetBlock(tip)); }
                if height > mine { push(tx, Msg::GetNext(loc)); }
                if !s.asked_addr { s.asked_addr = true; push(tx, Msg::GetAddr); }
            }
            Msg::Inv(h) => { if !self.node.lock().unwrap().have(&h) { push(tx, Msg::GetBlock(h)); } }
            Msg::GetBlock(h) => { let b = self.node.lock().unwrap().block(&h); if let Some(b) = b { push(tx, Msg::Block(b.encode())); } }
            Msg::GetNext(loc) => { let b = self.node.lock().unwrap().next_after(&loc).map(|b| b.encode()); if let Some(b) = b { push(tx, Msg::Block(b)); } }
            Msg::GetAddr => {
                let mut v: Vec<SocketAddr> = self.addrs.lock().unwrap().iter().copied().filter(|a| a.is_ipv4()).take(MAX_ADDR).collect();
                if let Some(a) = *self.my_addr.lock().unwrap() { if v.len() < MAX_ADDR && a.is_ipv4() && !a.ip().is_unspecified() { v.push(a); } }
                push(tx, Msg::Addr(v));
            }
            Msg::Addr(list) => {
                let me = *self.my_addr.lock().unwrap();
                let mut k = self.addrs.lock().unwrap();
                for a in list { if k.len() < MAX_KNOWN_ADDRS && Some(a) != me && a.port() != 0 && !a.ip().is_unspecified() && !self.is_banned(a.ip()) { k.insert(a); } }
            }
            Msg::Tx(bytes) => {
                let t = match SignedPay::from_bytes(&bytes) { Ok(t) => t, Err(_) => return self.punish(s, 50, "malformed payment") };
                let r = self.submit_tx(t, Some(s.id));
                let e = r.err().map(|e| e.to_string());
                if matches!(&e, Some(m) if m != "known") { self.punish(s, 1, "refused payment")?; }
                push(tx, Msg::TxAck(e.unwrap_or_default()));
            }
            Msg::Op(bytes) => {
                let o = match crate::locks::SignedOp::from_bytes(&bytes) { Ok(o) => o, Err(_) => return self.punish(s, 50, "malformed operation") };
                let e = self.submit_op(o, Some(s.id)).err().map(|e| e.to_string());
                if matches!(&e, Some(m) if m != "known") { self.punish(s, 1, "refused operation")?; }
                push(tx, Msg::TxAck(e.unwrap_or_default()));
            }
            Msg::TxAck(_) | Msg::Acct { .. } => {}
            Msg::GetAcct(a) => {
                let addr = match crate::node::addr_from(&a) { Ok(a) => a, Err(_) => return self.punish(s, 20, "bad address") };
                let n = self.node.lock().unwrap();
                let c = n.tip();
                let next = self.pool.lock().unwrap().next_nonce(c, &addr);
                let r = match c.account(&addr) {
                    Some((_, acct)) => Msg::Acct { found: true, balance: acct.bal, nonce: acct.nonce, next_nonce: next.unwrap_or(acct.nonce), height: c.height },
                    None => Msg::Acct { found: false, balance: 0, nonce: 0, next_nonce: 0, height: c.height },
                };
                push(tx, r);
            }
            Msg::Block(bytes) => {
                let blk = match Block::decode(&bytes) { Ok(b) => b, Err(_) => return self.punish(s, BAN_SCORE, "undecodable block") };
                let out = match self.add_block(&blk) { Ok(o) => o, Err(e) if e.downcast_ref::<crate::locks::Unavailable>().is_some() => return Ok(()),   // a claim waiting for another chain's header: not the sender's fault
                    Err(_) => return self.punish(s, BAN_SCORE, "invalid block") };
                self.pool_after_block();
                match out.main {
                    Added::Known | Added::Stale => {}
                    Added::Orphan(parent) => push(tx, Msg::GetBlock(parent)),
                    _ => self.relay(blk.hash(), Some(s.id)),
                }
                for h in &out.attached { self.relay(*h, Some(s.id)); }
                // still behind this peer: ask for the next block on its chain
                if !matches!(out.main, Added::Known | Added::Stale | Added::Orphan(_)) {
                    let (mine, loc) = { let n = self.node.lock().unwrap(); (n.tip().height, n.locator()) };
                    if s.peer_height > mine { push(tx, Msg::GetNext(loc)); }
                }
            }
        }
        Ok(())
    }
    fn relay(&self, hash: [u8; 32], except: Option<u64>) {
        for p in self.peers.lock().unwrap().iter() { if Some(p.id) != except { push(&p.tx, Msg::Inv(hash)); } }
    }
    /// the mempool follows the best tip: confirmed payments and ones that no longer apply go; payments of blocks
    /// lost in a reorg come back
    fn pool_after_block(&self) { let n = self.node.lock().unwrap(); self.pool.lock().unwrap().on_block(n.tip()); self.ops.lock().unwrap().on_block(n.tip()); }
    /// a payment from a wallet or a peer: check it against the best tip, keep it, tell the other peers if it is new
    pub fn submit_tx(&self, t: SignedPay, from_peer: Option<u64>) -> Result<Admit> {
        let r = { let n = self.node.lock().unwrap(); self.pool.lock().unwrap().admit(n.tip(), t.clone())? };
        for p in self.peers.lock().unwrap().iter() { if Some(p.id) != from_peer { push(&p.tx, Msg::Tx(t.to_bytes().to_vec())); } }
        Ok(r)
    }
    /// an operation from a wallet or a peer: same path as a payment
    pub fn submit_op(&self, o: crate::locks::SignedOp, from_peer: Option<u64>) -> Result<()> {
        { let n = self.node.lock().unwrap(); self.ops.lock().unwrap().admit(n.tip(), o.clone())?; }
        for p in self.peers.lock().unwrap().iter() { if Some(p.id) != from_peer { push(&p.tx, Msg::Op(o.to_bytes())); } }
        Ok(())
    }
    /// Add a block from anywhere. The expensive part, validating it on its parent's snapshot (replay, seal, stamp), runs
    /// WITHOUT the node's lock, so the node keeps answering while a block is checked.
    pub fn add_block(&self, blk: &Block) -> Result<Outcome> {
        let now = now();
        let main = self.process(blk, now)?;
        if let Added::Orphan(_) = main { self.node.lock().unwrap().park(blk); return Ok(Outcome { main, attached: vec![] }); }
        let mut attached = vec![];
        loop {
            let o = self.node.lock().unwrap().next_attachable();
            let Some(o) = o else { break };
            if let Ok(a) = self.process(&o, now) { if !matches!(a, Added::Known | Added::Stale) { attached.push(o.hash()); } }
        }
        Ok(Outcome { main, attached })
    }
    fn process(&self, blk: &Block, now: u32) -> Result<Added> {
        let look = self.node.lock().unwrap().lookup(blk);
        match look {
            Lookup::Known => Ok(Added::Known),
            Lookup::Stale => Ok(Added::Stale),
            Lookup::Orphan(p) => Ok(Added::Orphan(p)),
            Lookup::Parent(pc) => { let c = Node::prepare(&pc, blk, now)?; self.node.lock().unwrap().store(blk, c) }
        }
    }
    /// a block made here (a Stratum share, a local miner): validate, store, tell the peers
    pub fn submit(&self, blk: &Block) -> Result<Outcome> {
        let out = self.add_block(blk)?;
        self.pool_after_block();
        self.relay(blk.hash(), None);
        for h in &out.attached { self.relay(*h, None); }
        Ok(out)
    }
}

// ---------------------------------------------------------------- wallet client
/// What a node says about an account (balance and nonce at its best tip; `next_nonce` counts payments already waiting).
#[derive(Debug, Clone, Copy)]
pub struct AcctInfo { pub found: bool, pub balance: u64, pub nonce: u64, pub next_nonce: u64, pub height: u64 }
fn ask(addr: SocketAddr, m: Msg, want: impl Fn(&Msg) -> bool) -> Result<Msg> {
    let mut s = TcpStream::connect_timeout(&addr, Duration::from_secs(5))?;
    s.set_read_timeout(Some(Duration::from_secs(10)))?;
    write_msg(&mut s, &m)?;
    for _ in 0..8 { let r = read_msg(&mut s)?; if want(&r) { return Ok(r); } }
    bail!("no answer from the node")
}
/// A light follower's connection to a full node of some chain (cross-chain headers, stage 13): says hello for the chain's network, learns the node's tip,
/// and asks for the blocks after a locator, one at a time. It never serves anything and sends no transactions.
pub struct Probe { s: TcpStream, pub height: u64, pub tip: [u8; 32] }
impl Probe {
    pub fn connect(addr: SocketAddr, network_id: [u8; 32], genesis_hash: [u8; 32]) -> Result<Probe> {
        let mut s = TcpStream::connect_timeout(&addr, Duration::from_secs(5))?;
        s.set_read_timeout(Some(Duration::from_secs(10)))?;
        write_msg(&mut s, &Msg::Hello { genesis: network_id, height: 0, tip: genesis_hash, port: 0 })?;
        for _ in 0..16 {
            if let Msg::Hello { genesis, height, tip, .. } = read_msg(&mut s)? {
                if genesis != network_id { bail!("that node is on another network"); }
                return Ok(Probe { s, height, tip });
            }
        }
        bail!("the node did not say hello")
    }
    /// the block after the first locator hash the node has on its best chain; None when it has nothing newer to give
    pub fn next(&mut self, locator: &[[u8; 32]]) -> Result<Option<Block>> {
        write_msg(&mut self.s, &Msg::GetNext(locator.iter().take(32).copied().collect()))?;
        self.s.set_read_timeout(Some(Duration::from_secs(6)))?;
        for _ in 0..16 {
            match read_msg(&mut self.s) {
                Ok(Msg::Block(b)) => return Ok(Some(Block::decode(&b)?)),
                Ok(_) => continue,
                Err(e) if e.downcast_ref::<std::io::Error>().map_or(false, |e| matches!(e.kind(), std::io::ErrorKind::WouldBlock | std::io::ErrorKind::TimedOut)) => return Ok(None),
                Err(e) => return Err(e),
            }
        }
        Ok(None)
    }
}
pub fn query_account(node: SocketAddr, address: &[crate::F; 4]) -> Result<AcctInfo> {
    match ask(node, Msg::GetAcct(tx::addr_bytes(address)), |m| matches!(m, Msg::Acct { .. }))? {
        Msg::Acct { found, balance, nonce, next_nonce, height } => Ok(AcctInfo { found, balance, nonce, next_nonce, height }),
        _ => unreachable!(),
    }
}
/// send a signed payment to a node; Ok when the node's mempool took it
pub fn send_payment(node: SocketAddr, t: &SignedPay) -> Result<()> {
    match ask(node, Msg::Tx(t.to_bytes().to_vec()), |m| matches!(m, Msg::TxAck(_)))? {
        Msg::TxAck(e) if e.is_empty() => Ok(()),
        Msg::TxAck(e) => bail!("the node refused the payment: {e}"),
        _ => unreachable!(),
    }
}

/// send a signed operation to a node; Ok when its operation pool took it
pub fn send_op(node: SocketAddr, o: &crate::locks::SignedOp) -> Result<()> {
    match ask(node, Msg::Op(o.to_bytes()), |m| matches!(m, Msg::TxAck(_)))? {
        Msg::TxAck(e) if e.is_empty() => Ok(()),
        Msg::TxAck(e) => bail!("the node refused the operation: {e}"),
        _ => unreachable!(),
    }
}

// ---------------------------------------------------------------- Stratum v1
/// the pool side: builds the minted block (tickets, payments, stamp) that miners then seal
pub trait TemplateSource: Send + Sync { fn template(&self, tip: &Chain) -> Result<Block>; }

struct Jobs { next: u64, list: Vec<(String, Block)> }
#[derive(Clone)]
pub struct Stratum { net: Net, source: Arc<dyn TemplateSource>, jobs: Arc<Mutex<Jobs>>, conns: Arc<AtomicU64>, active: Arc<AtomicU64>, pub accepted: Arc<AtomicU64>, pub rejected: Arc<AtomicU64> }

/// Stratum limits: connections at once, bytes in one request line, seconds a connection may stay silent before it is closed
const MAX_STRATUM_CONNS: u64 = 256;
const MAX_LINE: u64 = 16 * 1024;
const STRATUM_IDLE_SECS: u64 = 600;
fn hex32(s: &str) -> Result<u32> { Ok(u32::from_str_radix(s, 16)?) }
impl Stratum {
    pub fn new(net: Net, source: Arc<dyn TemplateSource>) -> Stratum {
        Stratum { net, source, jobs: Arc::new(Mutex::new(Jobs { next: 1, list: vec![] })), conns: Arc::new(AtomicU64::new(1)), active: Arc::new(AtomicU64::new(0)), accepted: Arc::new(AtomicU64::new(0)), rejected: Arc::new(AtomicU64::new(0)) }
    }
    pub fn listen(&self, addr: &str) -> Result<SocketAddr> {
        let l = TcpListener::bind(addr)?;
        let a = l.local_addr()?;
        let me = self.clone();
        std::thread::spawn(move || {
            for s in l.incoming().flatten() {
                // at most MAX_STRATUM_CONNS miners at once, none from a banned address
                if me.active.load(Ordering::SeqCst) >= MAX_STRATUM_CONNS || s.peer_addr().map_or(true, |a| me.net.is_banned(a.ip())) { continue; }
                me.active.fetch_add(1, Ordering::SeqCst);
                let me = me.clone();
                std::thread::spawn(move || { if let Err(e) = me.serve(s) { if std::env::var("ZEN_LOG_STRATUM").is_ok() || !e.to_string().contains("closed") { eprintln!("stratum connection ended: {e}"); } } me.active.fetch_sub(1, Ordering::SeqCst); });
            }
        });
        Ok(a)
    }
    /// the job for the current best tip (a new template when the tip has moved)
    fn current_job(&self) -> Result<(String, Block)> {
        loop {
            let (best, snap) = { let n = self.net.node.lock().unwrap(); (n.best, n.tip().clone()) };
            { let j = self.jobs.lock().unwrap(); if let Some((id, b)) = j.list.last() { if b.header.prev == best { return Ok((id.clone(), b.clone())); } } }
            let tpl = self.source.template(&snap)?;
            if self.net.best() != best { continue; }
            let mut j = self.jobs.lock().unwrap();
            let id = format!("j{}", j.next); j.next += 1;
            j.list.push((id.clone(), tpl.clone()));
            if j.list.len() > 8 { j.list.remove(0); }
            return Ok((id, tpl));
        }
    }
    fn notify(&self, w: &mut TcpStream, id: &str, tpl: &Block) -> Result<()> {
        let cb = seal::parse_coinbase(&tpl.coinbase)?;
        let job = seal::make_job(id, cb.chain, cb.height, &tpl.header.prev, &tpl.body_root(), &cb.miner, 8, tpl.header.nbits, tpl.header.ntime);
        writeln!(w, "{}", job.notify_json())?; w.flush()?;
        Ok(())
    }
    fn serve(&self, stream: TcpStream) -> Result<()> {
        stream.set_read_timeout(Some(Duration::from_millis(100)))?;
        let mut w = stream.try_clone()?;
        let mut r = BufReader::new(stream);
        let cid = self.conns.fetch_add(1, Ordering::SeqCst);
        let en1 = (cid as u32).to_be_bytes();
        let (mut line, mut sent_for, mut authorized) = (String::new(), [0u8; 32], false);
        let mut last_seen = Instant::now();
        loop {
            if line.len() as u64 > MAX_LINE { bail!("request line too long"); }
            if last_seen.elapsed().as_secs() > STRATUM_IDLE_SECS { return Ok(()); }
            match (&mut r).take(MAX_LINE).read_line(&mut line) {
                Ok(0) => return Ok(()),
                Ok(_) if line.ends_with('\n') => {
                    last_seen = Instant::now();
                    let v: serde_json::Value = serde_json::from_str(line.trim())?; line.clear();
                    let (id, method, p) = (v["id"].clone(), v["method"].as_str().unwrap_or(""), v["params"].as_array().cloned().unwrap_or_default());
                    let reply = |w: &mut TcpStream, result: serde_json::Value, err: serde_json::Value| -> Result<()> { writeln!(w, "{}", serde_json::json!({"id": id, "result": result, "error": err}))?; Ok(()) };
                    match method {
                        "mining.subscribe" => reply(&mut w, serde_json::json!([[["mining.notify", "zen"]], seal::hex(&en1), 4]), serde_json::Value::Null)?,
                        "mining.authorize" => { authorized = true; reply(&mut w, serde_json::json!(true), serde_json::Value::Null)?; }
                        "mining.submit" if authorized => {
                            let res = (|| -> Result<Outcome> {
                                let s = |i: usize| p.get(i).and_then(|x| x.as_str()).ok_or_else(|| anyhow!("bad submit"));
                                let job_id = s(1)?;
                                let tpl = { let j = self.jobs.lock().unwrap(); j.list.iter().find(|(i, _)| i == job_id).map(|(_, b)| b.clone()) }.ok_or_else(|| anyhow!("unknown job"))?;
                                let share = seal::Share { extranonce2: seal::unhex(s(2)?), ntime: hex32(s(3)?)?, nonce: hex32(s(4)?)?, version: p.get(5).and_then(|x| x.as_str()).map(hex32).transpose()?.unwrap_or(tpl.header.version) };
                                if share.extranonce2.len() != 4 { bail!("extranonce2 must be 4 bytes"); }
                                let blk = tpl.with_share(tpl_chain(&tpl)?, &en1, &share)?;
                                if !seal::meets(&blk.header.hash(), blk.header.nbits) { bail!("share above the block target"); }
                                self.net.submit(&blk)
                            })();
                            match res {
                                Ok(_) => { self.accepted.fetch_add(1, Ordering::SeqCst); reply(&mut w, serde_json::json!(true), serde_json::Value::Null)? }
                                Err(e) => { self.rejected.fetch_add(1, Ordering::SeqCst); reply(&mut w, serde_json::json!(false), serde_json::json!([20, e.to_string(), null]))? }
                            }
                        }
                        _ => reply(&mut w, serde_json::Value::Null, serde_json::json!([20, "unsupported", null]))?,
                    }
                    if authorized && sent_for == [0u8; 32] { let (id, tpl) = self.current_job()?; self.notify(&mut w, &id, &tpl)?; sent_for = tpl.header.prev; }
                }
                Ok(_) => {}
                Err(e) if matches!(e.kind(), std::io::ErrorKind::WouldBlock | std::io::ErrorKind::TimedOut) => {}
                Err(e) => return Err(e.into()),
            }
            // a new best tip: a new job
            if authorized && self.net.best() != sent_for {
                let (id, tpl) = self.current_job()?;
                self.notify(&mut w, &id, &tpl)?; sent_for = tpl.header.prev;
            }
        }
    }
}
fn tpl_chain(tpl: &Block) -> Result<u8> { Ok(seal::parse_coinbase(&tpl.coinbase)?.chain) }

/// A miner that knows only Stratum (a CPU stand-in for an ASIC farm): subscribe, authorize, mine each job, submit.
pub fn stratum_client_mine(addr: SocketAddr, blocks: usize, max_hashes: u64) -> Result<usize> {
    let s = TcpStream::connect(addr)?;
    s.set_read_timeout(Some(Duration::from_secs(120)))?;
    let mut w = s.try_clone()?;
    let mut r = BufReader::new(s);
    writeln!(w, r#"{{"id":1,"method":"mining.subscribe","params":["zen-cpu-miner/0.1"]}}"#)?;
    writeln!(w, r#"{{"id":2,"method":"mining.authorize","params":["worker","x"]}}"#)?;
    let (mut en1, mut en2_size, mut done, mut next_id) = (vec![], 4usize, 0usize, 3u64);
    let mut line = String::new();
    while done < blocks {
        line.clear();
        if r.read_line(&mut line)? == 0 { break; }
        let v: serde_json::Value = serde_json::from_str(line.trim())?;
        if v["id"] == 1 { en1 = seal::unhex(v["result"][1].as_str().unwrap_or("")); en2_size = v["result"][2].as_u64().unwrap_or(4) as usize; continue; }
        if v["method"] == "mining.notify" {
            let p = &v["params"];
            let st = |i: usize| p[i].as_str().unwrap_or("").to_string();
            let job = seal::Job { job_id: st(0), prevhash: st(1), coinb1: st(2), coinb2: st(3),
                merkle_branch: p[4].as_array().map(|a| a.iter().map(|x| x.as_str().unwrap_or("").to_string()).collect()).unwrap_or_default(),
                version: st(5), nbits: st(6), ntime: st(7) };
            if let Some((sh, _)) = seal::stratum_mine(&job, &en1, en2_size, max_hashes) {
                writeln!(w, "{}", serde_json::json!({"id": next_id, "method": "mining.submit", "params": ["worker", job.job_id, seal::hex(&sh.extranonce2), format!("{:08x}", sh.ntime), format!("{:08x}", sh.nonce), format!("{:08x}", sh.version)]}))?;
                next_id += 1;
            }
            continue;
        }
        if v["id"].as_u64().is_some_and(|i| i >= 3) { if v["result"] == true { done += 1; } }
    }
    Ok(done)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::node::{dev, DevStamp, Params};

    fn wait(what: &str, f: impl Fn() -> bool) { let t = std::time::Instant::now(); while !f() { assert!(t.elapsed().as_secs() < 240, "timeout waiting for {what}"); std::thread::sleep(Duration::from_millis(50)); } }
    fn node_of(net: &dev::Devnet) -> Node { Node::open(Params::devnet(), &dev::genesis_of(&net.keys), Box::new(DevStamp), None).unwrap() }

    #[test]
    fn fork_choice_orphans_and_reorg() {
        let mut net = dev::Devnet::new(None, 8).unwrap();
        let mut node = node_of(&net);
        let now = u32::MAX;
        // a common trunk of two blocks
        let mut parent = net.chain.clone();
        let mut trunk = vec![];
        for _ in 0..2 { let b = net.block_on(&parent, 24, 8).unwrap(); parent.accept(&b, now).unwrap(); trunk.push(b); }
        for b in &trunk { assert_eq!(node.add_block(b, now).unwrap().main, Added::Extended); }
        let fork_point = parent.clone();
        // branch Y: one heavy block (48 tickets, weight about double)
        let y = net.block_on(&fork_point, 48, 8).unwrap();
        assert_eq!(node.add_block(&y, now).unwrap().main, Added::Extended);
        assert_eq!(node.best, y.hash());
        // branch X: three ordinary blocks, built apart from Y; the first two are lighter and do not take over
        let mut xc = fork_point.clone();
        let mut xs = vec![];
        for _ in 0..3 { let b = net.block_on(&xc, 24, 8).unwrap(); xc.accept(&b, now).unwrap(); xs.push(b); }
        // delivered out of order: the tip first is an orphan, then its parents arrive and everything attaches
        assert_eq!(node.add_block(&xs[2], now).unwrap().main, Added::Orphan(xs[1].hash()));
        assert_eq!(node.add_block(&xs[1], now).unwrap().main, Added::Orphan(xs[0].hash()));
        assert_eq!(node.best, y.hash(), "orphans change nothing");
        let out = node.add_block(&xs[0], now).unwrap();
        assert_eq!(out.attached, vec![xs[1].hash(), xs[2].hash()]);
        // X is three blocks of weight 1 against Y's two of weight about 1 and 2: X now has more work
        assert_eq!(node.best, xs[2].hash(), "the heavier branch wins");
        assert_eq!(node.reorgs, vec![1], "one block of Y was abandoned");
        assert_eq!(node.tip().root(), xc.root());
        node.tip().audit().unwrap();
        // the abandoned branch is still stored, and the same block twice is harmless
        assert!(node.have(&y.hash()));
        assert_eq!(node.add_block(&y, now).unwrap().main, Added::Known);
        // an invalid block is an error and changes nothing
        let mut bad = net.block_on(&xc, 24, 8).unwrap(); bad.stamp[0] ^= 1;
        assert!(node.add_block(&bad, now).is_err());
        assert_eq!(node.best, xs[2].hash());
    }

    #[test]
    fn two_nodes_sync_and_relay_over_tcp() {
        let mut dn = dev::Devnet::new(None, 8).unwrap();
        let a = Net::new(node_of(&dn));
        let b = Net::new(node_of(&dn));
        // A already has four blocks
        for _ in 0..4 { let blk = dn.next_block(24, 8).unwrap(); dn.chain.accept(&blk, u32::MAX).unwrap(); a.submit(&blk).unwrap(); }
        assert_eq!(a.height(), 4);
        let addr = a.listen("127.0.0.1:0").unwrap();
        // B connects: it hears A's tip, asks for it, walks back through the orphans, validates all four
        b.connect(addr).unwrap();
        wait("B to sync", || b.height() == 4);
        assert_eq!(b.best(), a.best());
        // A makes block five: B gets it by INV and GETBLOCK
        let blk = dn.next_block(24, 8).unwrap(); dn.chain.accept(&blk, u32::MAX).unwrap();
        a.submit(&blk).unwrap();
        wait("B to follow", || b.height() == 5);
        assert_eq!(b.best(), a.best());
        // a node on another chain is dropped
        let other = Net::new(Node::open(Params { chain: 2, ..Params::devnet() }, &dev::genesis_of(&dn.keys), Box::new(DevStamp), None).unwrap());
        other.connect(addr).unwrap();
        wait("the other chain to be dropped", || other.peer_count() == 0);
        assert_eq!(other.height(), 0);
    }

    #[test]
    fn stratum_miner_seals_a_block_and_the_node_relays_it() {
        let dn = dev::Devnet::new(None, 8).unwrap();
        let a = Net::new(node_of(&dn));
        let b = Net::new(node_of(&dn));
        let pool = Stratum::new(a.clone(), Arc::new(dev::DevSource { keys: dn.keys.clone(), miner: dn.keys[0].addr, maker: dn.maker.clone() }));
        let saddr = pool.listen("127.0.0.1:0").unwrap();
        let paddr = a.listen("127.0.0.1:0").unwrap();
        b.connect(paddr).unwrap();
        // a miner that knows only Stratum: two blocks
        let miner = std::thread::spawn(move || stratum_client_mine(saddr, 2, 50_000_000).unwrap());
        assert_eq!(miner.join().unwrap(), 2);
        assert_eq!(pool.accepted.load(Ordering::SeqCst), 2);
        assert_eq!(a.height(), 2);
        wait("B to follow the mined blocks", || b.height() == 2);
        assert_eq!(a.best(), b.best());
        a.node.lock().unwrap().tip().audit().unwrap();
    }

    /// the first blocks of a chain carry nothing: they get a real stamp all the same
    #[test]
    fn an_empty_block_gets_a_real_stamp() {
        use crate::prover::{Circuits, Plonky2Stamp, ProverMaker};
        let circ = Arc::new(Circuits::build(16).unwrap());
        let keys = dev::devnet_keys(6);
        let maker: Arc<dyn crate::node::StampMaker> = Arc::new(ProverMaker::new(circ.clone(), keys));
        let mut net = dev::Devnet::with(None, 6, Box::new(Plonky2Stamp::new(&circ)), Some(maker)).unwrap();
        net.chain.p.maturity = 2;
        for _ in 0..2 {
            let b = net.next_block(24, 0).unwrap();
            assert_eq!(b.pubvalues[9], 0, "no payments");
            assert!(b.stamp.len() > 100_000);
            net.chain.accept(&b, u32::MAX).unwrap();
        }
        net.chain.audit().unwrap();
    }

    /// proving the leaves and merges several at a time gives a valid stamp for the same block
    #[test]
    fn proving_in_parallel_gives_a_valid_stamp() {
        use crate::prover::{Circuits, Plonky2Stamp, ProverMaker};
        let circ = Arc::new(Circuits::build(16).unwrap());
        let keys = dev::devnet_keys(6);
        let stamp_with = |par: usize| {
            let mut pm = ProverMaker::new(circ.clone(), keys.clone());
            pm.par = par;
            let maker: Arc<dyn crate::node::StampMaker> = Arc::new(pm);
            let mut net = dev::Devnet::with(None, 6, Box::new(Plonky2Stamp::new(&circ)), Some(maker)).unwrap();
            let t = std::time::Instant::now();
            let b = net.next_block(24, 36).unwrap();       // three leaves
            println!("par {par}: block proved in {:.1}s", t.elapsed().as_secs_f64());
            net.chain.accept(&b, u32::MAX).unwrap();          // the node's check: replay, then the stamp against the public values
            assert!(b.stamp.len() > 100_000);
            b.pubvalues
        };
        // (the stamp bytes themselves differ from run to run: Plonky2 grinds its proof-of-work nonce on several threads and takes any that works)
        let (one, three) = (stamp_with(1), stamp_with(3));
        assert_eq!(one, three, "the same block, proved one at a time or three at a time, and both stamps verify");
    }

    #[test]
    fn real_stamps_are_verified_by_the_node() {
        use crate::prover::{Circuits, Plonky2Stamp, ProverMaker};
        let t0 = std::time::Instant::now();
        let circ = Arc::new(Circuits::build(16).unwrap());
        println!("circuits built in {:.1}s", t0.elapsed().as_secs_f64());
        let keys = dev::devnet_keys(6);
        let maker: Arc<dyn crate::node::StampMaker> = Arc::new(ProverMaker::new(circ.clone(), keys.clone()));
        let mut net = dev::Devnet::with(None, 6, Box::new(Plonky2Stamp::new(&circ)), Some(maker)).unwrap();
        let now = u32::MAX;
        // a block of 20 payments: two leaves (the second one carries the credits), real signatures, real proofs
        let t = std::time::Instant::now();
        let b1 = net.next_block(24, 20).unwrap();
        println!("block 1: proved in {:.1}s | stamp {} bytes", t.elapsed().as_secs_f64(), b1.stamp.len());
        let t = std::time::Instant::now();
        net.chain.accept(&b1, now).unwrap();
        println!("block 1: node check (tickets, replay, stamp) {:.2}s", t.elapsed().as_secs_f64());
        assert!(b1.stamp.len() > 100_000);
        net.chain.audit().unwrap();
        // two candidates on the new tip; a stamp that proves another block is refused
        let a = net.next_block(24, 3).unwrap();
        let b = net.next_block(24, 4).unwrap();
        let c = &net.chain;
        let mut swapped = a.clone(); swapped.stamp = b.stamp.clone(); dev::reseal(c, &mut swapped);
        let e = c.validate(&swapped, now).err().map(|e| e.to_string()).unwrap_or("ACCEPTED".into());
        assert!(e.contains("other public values"), "{e}");
        // a damaged stamp
        let mut damaged = a.clone(); let mid = damaged.stamp.len() / 2; damaged.stamp[mid] ^= 1; dev::reseal(c, &mut damaged);
        let e = c.validate(&damaged, now).err().map(|e| e.to_string()).unwrap_or("ACCEPTED".into());
        assert!(e.contains("stamp"), "{e}");
        // a stamp cut short, and one padded
        let mut short = a.clone(); short.stamp.truncate(1000); dev::reseal(c, &mut short);
        assert!(c.validate(&short, now).is_err());
        // the honest candidate goes in
        net.chain.accept(&a, now).unwrap();
        net.chain.audit().unwrap();
        assert_eq!(net.chain.height, 2);
        // DevStamp-style fakes do not pass the real verifier
        let mut fake = b.clone(); fake.stamp = DevStamp::make(&fake.pubvalues); dev::reseal(&net.chain, &mut fake);
        assert!(net.chain.validate(&fake, now).is_err());
    }

    fn devnet_wallet(i: usize) -> crate::tx::Wallet { crate::tx::Wallet { key: dev::devnet_keys(i + 1).pop().unwrap() } }

    #[test]
    fn wallet_to_mempool_to_block_over_tcp() {
        use crate::tx::Wallet;
        let dn = dev::Devnet::new(None, 8).unwrap();
        let a = Net::new(node_of(&dn));
        let b = Net::new(node_of(&dn));
        let pool = Stratum::new(a.clone(), Arc::new(dev::PoolSource { minters: dn.keys.clone(), miner: dn.keys[0].addr, maker: dn.maker.clone(), pool: a.pool.clone(), store: None, max_pays: 32, wall_clock: false, ops: None }));
        let saddr = pool.listen("127.0.0.1:0").unwrap();
        let paddr = a.listen("127.0.0.1:0").unwrap();
        b.connect(paddr).unwrap();
        wait("peers", || a.peer_count() == 1 && b.peer_count() == 1);
        let (w0, w1) = (devnet_wallet(5), devnet_wallet(6));   // not minters, so no payout lands in them
        let newcomer = Wallet::from_secret(num_bigint::BigUint::from(31_337u64));
        // the wallet asks the node for its account, then sends two payments in a row (queued nonces)
        let before = query_account(paddr, &w0.address()).unwrap();
        assert!(before.found && before.balance == 1_000_000_000 && before.nonce == 0 && before.next_nonce == 0);
        assert!(!query_account(paddr, &newcomer.address()).unwrap().found);
        send_payment(paddr, &w0.pay(w1.address(), 10_000_000, Wallet::standard_fee(10_000_000), before.next_nonce)).unwrap();
        let mid = query_account(paddr, &w0.address()).unwrap();
        assert_eq!(mid.next_nonce, 1, "one payment waits");
        send_payment(paddr, &w0.pay(newcomer.address(), 20_000_000, Wallet::standard_fee(20_000_000), mid.next_nonce)).unwrap();   // opens an account
        // refused with a reason: wrong nonce, no funds, bad signature
        let e = send_payment(paddr, &w0.pay(w1.address(), 1_000_000, 10_001, 9)).unwrap_err().to_string();
        assert!(e.contains("nonce 9 (the next is 2)"), "{e}");
        let e = send_payment(paddr, &w1.pay(w0.address(), 2_000_000_000, 1_000_000, 0)).unwrap_err().to_string();
        assert!(e.contains("does not cover"), "{e}");
        let mut forged = w1.pay(w0.address(), 1_000_000, 10_001, 0); forged.amt += 1;
        let e = send_payment(paddr, &forged).unwrap_err().to_string();
        assert!(e.contains("signature"), "{e}");
        // the other node heard of the two good payments
        wait("B's mempool", || b.pool.lock().unwrap().len() == 2);
        // a Stratum miner seals the block the pool built from the mempool
        let miner = std::thread::spawn(move || stratum_client_mine(saddr, 1, 50_000_000).unwrap());
        assert_eq!(miner.join().unwrap(), 1);
        wait("B to follow", || b.height() == 1);
        assert_eq!(a.best(), b.best());
        assert_eq!(a.pool.lock().unwrap().len(), 0, "the block confirmed both");
        wait("B's mempool to clear", || b.pool.lock().unwrap().len() == 0);
        let after = query_account(paddr, &w0.address()).unwrap();
        assert_eq!(after.nonce, 2);
        assert_eq!(after.balance, 1_000_000_000 - 30_000_000 - Wallet::standard_fee(10_000_000) - Wallet::standard_fee(20_000_000));
        let nc = query_account(paddr, &newcomer.address()).unwrap();
        assert!(nc.found && nc.balance == 20_000_000, "the new account was opened");
        a.node.lock().unwrap().tip().audit().unwrap();
        // the newcomer can now pay; the nonce of a fresh account starts at height << 20, and the node says so
        assert_eq!(nc.nonce, 1u64 << crate::blockdata::NONCE_SHIFT);
        send_payment(paddr, &newcomer.pay(w1.address(), 5_000_000, Wallet::standard_fee(5_000_000), nc.next_nonce)).unwrap();
        // a payment replayed after confirmation is refused
        let old = w0.pay(w1.address(), 10_000_000, Wallet::standard_fee(10_000_000), 0);
        assert!(send_payment(paddr, &old).unwrap_err().to_string().contains("nonce"));
    }

    /// Needs the Groth16 setup and the Go prover (about 6 GB, several minutes): ZEN_G16=<dir with zen.pk, zen.r1cs, zen.vk> ZEN_WRAP=<zenwrap>.
    /// A wallet's payment travels in a block whose stamp is 196 bytes; a node that has only zen.vk accepts it.
    #[test]
    fn a_block_with_a_groth16_stamp_is_accepted_by_a_node_with_only_the_verifying_key() {
        use crate::prover::{Circuits, Groth16Maker, ProverMaker};
        use crate::tx::Wallet;
        let (Ok(kd), Ok(tool)) = (std::env::var("ZEN_G16"), std::env::var("ZEN_WRAP")) else { println!("ZEN_G16 / ZEN_WRAP not set: skipped"); return };
        let kd = std::path::PathBuf::from(kd);
        let circ = Arc::new(Circuits::build(16).unwrap());
        let keys = dev::devnet_keys(6);
        let pm = ProverMaker::new(circ.clone(), keys.clone());
        let store = pm.store.clone();
        let gm = Groth16Maker::new(pm, tool.into(), kd.clone(), std::env::temp_dir()).unwrap();
        // the BN254 layer built here is the one the setup was made for
        let vo: serde_json::Value = serde_json::from_slice(&std::fs::read(kd.join("verifier_only_circuit_data.json")).unwrap_or_else(|_| b"{}".to_vec())).unwrap();
        if let Some(d) = vo.get("circuit_digest") { assert_eq!(serde_json::to_string(d).unwrap(), gm.bn.digest_json(), "the setup is for another circuit"); }
        let vk = std::fs::read(kd.join("zen.vk")).unwrap();
        let maker: Arc<dyn crate::node::StampMaker> = Arc::new(gm);
        let mut net = dev::Devnet::with(None, 6, Box::new(crate::groth16::Groth16Stamp::new(&vk).unwrap()), Some(maker.clone())).unwrap();
        let src = dev::PoolSource { minters: keys.clone(), miner: keys[0].addr, maker: maker.clone(), pool: Arc::new(Mutex::new(crate::mempool::Mempool::new(1000))), store: Some(store), max_pays: 32, wall_clock: false, ops: None };
        let alice = Wallet::from_secret(num_bigint::BigUint::from(424_242u64));
        let w0 = Wallet { key: keys[0].clone() };
        src.pool.lock().unwrap().admit(&net.chain, w0.pay(alice.address(), 300_000_000, Wallet::standard_fee(300_000_000), 0)).unwrap();
        let t = std::time::Instant::now();
        let mut blk = crate::p2p::TemplateSource::template(&src, &net.chain).unwrap();
        dev::reseal(&net.chain, &mut blk);
        println!("block with a Groth16 stamp made in {:.1}s", t.elapsed().as_secs_f64());
        assert_eq!(blk.stamp.len(), 196);
        // another node that has the verifying key and nothing else
        let mut other = net.chain.clone();
        let t = std::time::Instant::now();
        other.accept(&blk, u32::MAX).unwrap();
        println!("accepted by a node with only zen.vk in {:.2}s (replay and the pairing check)", t.elapsed().as_secs_f64());
        assert_eq!(other.account(&alice.address()).unwrap().1.bal, 300_000_000);
        // the same block with a changed stamp byte, other public values, or the devnet's fake stamp
        let mut bad = blk.clone(); bad.stamp[100] ^= 1; dev::reseal(&net.chain, &mut bad);
        assert!(net.chain.clone().accept(&bad, u32::MAX).is_err());
        let mut bad = blk.clone(); bad.pubvalues[9] += 1; dev::reseal(&net.chain, &mut bad);
        assert!(net.chain.clone().accept(&bad, u32::MAX).is_err());
        let mut bad = blk.clone(); bad.stamp = crate::node::DevStamp::make(&bad.pubvalues); dev::reseal(&net.chain, &mut bad);
        assert!(net.chain.clone().accept(&bad, u32::MAX).is_err());
        net.chain.accept(&blk, u32::MAX).unwrap();
        net.chain.audit().unwrap();
        // a second block: the long-running Go prover has the key loaded already
        src.pool.lock().unwrap().on_block(&net.chain);
        let a = net.chain.account(&alice.address()).unwrap().1.clone();
        src.pool.lock().unwrap().admit(&net.chain, alice.pay(keys[2].addr, 50_000_000, Wallet::standard_fee(50_000_000), a.nonce)).unwrap();
        let t = std::time::Instant::now();
        let mut blk2 = crate::p2p::TemplateSource::template(&src, &net.chain).unwrap();
        dev::reseal(&net.chain, &mut blk2);
        println!("second block (prover already loaded) made in {:.1}s", t.elapsed().as_secs_f64());
        assert_eq!(blk2.stamp.len(), 196);
        net.chain.accept(&blk2, u32::MAX).unwrap();
        net.chain.audit().unwrap();
        assert_eq!(net.chain.account(&alice.address()).unwrap().1.bal, 300_000_000 - 50_000_000 - Wallet::standard_fee(50_000_000));
    }
    /// Needs the same setup as the test above. Blocks that carry operations of the channel, order and factory families get 196-byte Groth16 stamps
    /// that a node with only zen.vk accepts (stage P6): the merge picks the leaf key of each family, the shrink and BN254 layers check it all.
    #[test]
    fn groth16_stamps_carry_operations_of_every_family() {
        use crate::locks::{FMember, OpReq, OrderState, SubState, Terms};
        use crate::mint;
        use crate::prover::{Circuits, Groth16Maker, ProverMaker};
        let (Ok(kd), Ok(tool)) = (std::env::var("ZEN_G16"), std::env::var("ZEN_WRAP")) else { println!("ZEN_G16 / ZEN_WRAP not set: skipped"); return };
        let kd = std::path::PathBuf::from(kd);
        let circ = Arc::new(Circuits::build(16).unwrap());
        let keys = dev::devnet_keys(8);
        let gm = Groth16Maker::new(ProverMaker::new(circ.clone(), keys.clone()), tool.into(), kd.clone(), std::env::temp_dir()).unwrap();
        let vo: serde_json::Value = serde_json::from_slice(&std::fs::read(kd.join("verifier_only_circuit_data.json")).unwrap_or_else(|_| b"{}".to_vec())).unwrap();
        if let Some(d) = vo.get("circuit_digest") { assert_eq!(serde_json::to_string(d).unwrap(), gm.bn.digest_json(), "the setup is for another circuit"); }
        let vk = std::fs::read(kd.join("zen.vk")).unwrap();
        let maker: Arc<dyn crate::node::StampMaker> = Arc::new(gm);
        let mut net = dev::Devnet::with(None, 8, Box::new(crate::groth16::Groth16Stamp::new(&vk).unwrap()), Some(maker.clone())).unwrap();
        net.chain.cross = crate::locks::CrossMode::Trust;
        let (mk, taker, a, b, coord, m0) = (keys[4].clone(), keys[5].clone(), keys[6].clone(), keys[7].clone(), keys[3].clone(), keys[2].clone());
        let mut build = |net: &mut dev::Devnet, reqs: &[OpReq]| {
            let t = std::time::Instant::now();
            let tickets = dev::make_tickets(&net.chain, &keys[..2], 24);
            let blk = dev::build_block_ops(&net.chain, keys[0].addr, tickets, &[], reqs, net.chain.tip_ntime + 150, maker.as_ref()).unwrap();
            println!("block {} with {} operations and a stamp of {} bytes made in {:.1}s", net.chain.height + 1, reqs.len(), blk.stamp.len(), t.elapsed().as_secs_f64());
            assert_eq!(blk.stamp.len(), 196);
            let mut other = net.chain.clone();
            other.accept(&blk, u32::MAX).unwrap();
            let mut bad = blk.clone(); bad.stamp[100] ^= 1; dev::reseal(&net.chain, &mut bad);
            assert!(net.chain.clone().accept(&bad, u32::MAX).is_err(), "a changed stamp byte is refused");
            net.chain.accept(&blk, u32::MAX).unwrap();
        };
        let nonce = |net: &dev::Devnet, k: &mint::Key| net.chain.account(&k.addr).unwrap().1.nonce;
        let order = Terms::Order { maker: mk.addr, sell: 600_000_000, want_chain: 1, want_amt: 5_000, pay_to: taker.addr, expiry: 100, reserve_blocks: 3, deposit: 12_000_000, salt: nonce(&net, &mk), state: OrderState::Open };
        let chan = Terms::Channel { a: a.addr, b: b.addr, key_a: mint::encode_point(a.a), key_b: mint::encode_point(b.a), delay: 2, oneway: false, salt: nonce(&net, &a), state: crate::locks::ChanState::Open };
        let fm = |k: &mint::Key, cap: u64| FMember { addr: k.addr, key: mint::encode_point(k.a), cap, base: cap, state: SubState::Open };
        let fact = Terms::Factory { coord: coord.addr, key_c: mint::encode_point(coord.a), delay: 2, salt: nonce(&net, &coord), members: vec![fm(&m0, 300_000_000)] };
        // block 1: one operation of each of three families; block 2: a reservation and the start of a factory member's close
        build(&mut net, &[OpReq::Make { from: mk.addr, amt: 600_000_000, fee: 10_000, terms: order }, OpReq::Make { from: a.addr, amt: 500_000_000, fee: 10_000, terms: chan }, OpReq::Make { from: coord.addr, amt: 300_000_000, fee: 10_000, terms: fact }]);
        assert_eq!(net.chain.locks.len(), 3);
        let find = |net: &dev::Devnet, f: &dyn Fn(&Terms) -> bool| net.chain.locks.values().find(|t| f(t)).unwrap().digest();
        let ol = find(&net, &|t| matches!(t, Terms::Order { .. }));
        let fl = find(&net, &|t| matches!(t, Terms::Factory { .. }));
        build(&mut net, &[OpReq::Reserve { from: taker.addr, fee: 10_000, lock: ol, taker: taker.addr }, OpReq::FactoryStart { from: coord.addr, fee: 10_000, lock: fl, idx: 0 }]);
        net.chain.audit().unwrap();
    }
    #[test]
    fn real_proofs_carry_a_new_wallets_own_signature() {
        use crate::prover::{Circuits, Plonky2Stamp, ProverMaker};
        use crate::tx::Wallet;
        let circ = Arc::new(Circuits::build(16).unwrap());
        let keys = dev::devnet_keys(6);
        let pm = Arc::new(ProverMaker::new(circ.clone(), keys.clone()));
        let maker: Arc<dyn crate::node::StampMaker> = pm.clone();
        let mut net = dev::Devnet::with(None, 6, Box::new(Plonky2Stamp::new(&circ)), Some(maker.clone())).unwrap();
        let src = dev::PoolSource { minters: keys.clone(), miner: keys[0].addr, maker: maker.clone(), pool: Arc::new(Mutex::new(crate::mempool::Mempool::new(1000))), store: Some(pm.store.clone()), max_pays: 32, wall_clock: false, ops: None };
        let mut mine = |net: &mut dev::Devnet, txs: Vec<crate::tx::SignedPay>| -> Result<crate::node::Block> {
            for t in txs { src.pool.lock().unwrap().admit(&net.chain, t)?; }
            let mut blk = crate::p2p::TemplateSource::template(&src, &net.chain)?;
            dev::reseal(&net.chain, &mut blk);
            Ok(blk)
        };
        // a wallet whose secret the pool does NOT hold
        let alice = Wallet::from_secret(num_bigint::BigUint::from(424_242u64));
        let w0 = Wallet { key: keys[0].clone() };
        let pool_has_alice = keys.iter().any(|k| k.addr == alice.address());
        assert!(!pool_has_alice);
        // block 1: a devnet wallet funds alice (signature from the mempool store as well)
        let b1 = mine(&mut net, vec![w0.pay(alice.address(), 300_000_000, Wallet::standard_fee(300_000_000), 0)]).unwrap();
        net.chain.accept(&b1, u32::MAX).unwrap();
        src.pool.lock().unwrap().on_block(&net.chain);
        let a_acct = net.chain.account(&alice.address()).unwrap().1.clone();
        assert_eq!(a_acct.bal, 300_000_000);
        // block 2: alice pays with a signature only she can make; the proof carries it
        let t = std::time::Instant::now();
        let pay = alice.pay(keys[2].addr, 50_000_000, Wallet::standard_fee(50_000_000), a_acct.nonce);
        let b2 = mine(&mut net, vec![pay.clone()]).unwrap();
        println!("block 2 (alice's own signature) proved in {:.1}s", t.elapsed().as_secs_f64());
        net.chain.accept(&b2, u32::MAX).unwrap();
        net.chain.audit().unwrap();
        assert_eq!(net.chain.account(&alice.address()).unwrap().1.bal, 300_000_000 - 50_000_000 - Wallet::standard_fee(50_000_000));
        // the pool cannot prove a payment for alice with a signature that is not hers: no proof exists
        let mallory = Wallet::from_secret(num_bigint::BigUint::from(666u64));
        let mut forged = alice.pay(keys[3].addr, 40_000_000, Wallet::standard_fee(40_000_000), net.chain.account(&alice.address()).unwrap().1.nonce);
        let m = mallory.pay(keys[3].addr, 40_000_000, Wallet::standard_fee(40_000_000), forged.nonce);
        forged.e = m.e; forged.s = m.s;                          // alice's key point, mallory's signature
        assert!(forged.verify().is_err());
        pm.store.lock().unwrap().insert((crate::tx::addr_key(&alice.address()), forged.nonce), forged);
        let pays = [dev::DevPay { from: alice.address(), to: keys[3].addr, amt: 40_000_000, fee: Wallet::standard_fee(40_000_000) }];
        let parent = net.chain.clone();
        let r = dev::build_block(&parent, keys[0].addr, dev::make_tickets(&parent, &keys[..4], 24), &pays, parent.tip_ntime + 150, maker.as_ref());
        assert!(r.is_err(), "a forged signature must not give a proof");
    }

    // ---------------------------------------------------------------- hardening (SPEC 10.7)
    /// a verifier that takes its time, to see whether the node stays responsive while it works
    struct SlowStamp(u64);
    impl crate::node::StampVerifier for SlowStamp {
        fn verify(&self, pubvalues: &[u64], stamp: &[u8]) -> Result<()> { std::thread::sleep(Duration::from_millis(self.0)); DevStamp.verify(pubvalues, stamp) }
    }
    fn raw_hello(net: &Net, height: u64) -> Msg { Msg::Hello { genesis: net.genesis, height, tip: net.best(), port: 0 } }
    /// a plain TCP connection to a node: the node's hello is read first
    fn raw_peer(addr: SocketAddr) -> TcpStream { let mut s = TcpStream::connect(addr).unwrap(); s.set_read_timeout(Some(Duration::from_secs(5))).unwrap(); assert!(matches!(read_msg(&mut s).unwrap(), Msg::Hello { .. })); s }
    fn closed(s: &mut TcpStream) -> bool { let mut b = [0u8; 1]; matches!(s.read(&mut b), Ok(0) | Err(_)) }

    #[test]
    fn validation_runs_outside_the_node_lock() {
        let mut dn = dev::Devnet::new(None, 8).unwrap();
        let net = Net::new(Node::open(Params::devnet(), &dev::genesis_of(&dn.keys), Box::new(SlowStamp(500)), None).unwrap());
        let blk = dn.next_block(24, 8).unwrap();
        let (n2, b2) = (net.clone(), blk.clone());
        let t = std::time::Instant::now();
        let h = std::thread::spawn(move || n2.add_block(&b2).unwrap());
        std::thread::sleep(Duration::from_millis(150));            // the stamp check is under way
        let t1 = std::time::Instant::now();
        let (height, _best, _peers) = (net.height(), net.best(), net.peer_count());
        let answered = t1.elapsed();
        let out = h.join().unwrap();
        println!("the node answered in {:?} while a block took {:?} to validate", answered, t.elapsed());
        assert!(t.elapsed() >= Duration::from_millis(500), "the slow verifier ran");
        assert!(answered < Duration::from_millis(100), "the node was blocked for {answered:?}");
        assert_eq!(height, 0, "the block was not in yet");
        assert_eq!(out.main, Added::Extended);
        assert_eq!(net.height(), 1);
        // the same block offered twice at once is stored once
        dn.chain.accept(&blk, u32::MAX).unwrap();
        let blk2 = dn.next_block(24, 8).unwrap();
        let (n3, b3) = (net.clone(), blk2.clone());
        let h = std::thread::spawn(move || n3.add_block(&b3).unwrap().main);
        let m = net.add_block(&blk2).unwrap().main;
        let m2 = h.join().unwrap();
        assert!(matches!((m, m2), (Added::Extended, Added::Known) | (Added::Known, Added::Extended) | (Added::Extended, Added::Extended)));
        assert_eq!(net.height(), 2);
    }

    /// the log is the node's memory: old blocks leave RAM but are served from disk, a restart gives the same chain, a torn write is repaired
    #[test]
    fn a_node_restarts_from_its_log_serves_old_blocks_from_disk_and_repairs_a_torn_write() {
        let dir = std::env::temp_dir().join(format!("zen-node-store-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let mut dn = dev::Devnet::new(None, 8).unwrap();
        let open = |dn: &dev::Devnet| Node::open(Params::devnet(), &dev::genesis_of(&dn.keys), Box::new(DevStamp), Some(&dir));
        let mut node = open(&dn).unwrap();
        node.max_reorg = 3;
        let now = u32::MAX;
        let mut blocks = vec![];
        for _ in 0..9 { let b = dn.next_block(24, 8).unwrap(); dn.chain.accept(&b, now).unwrap(); node.add_block(&b, now).unwrap(); blocks.push(b); }
        assert!(node.blocks.len() <= 4, "only the recent blocks stay in memory: {}", node.blocks.len());
        assert!(open(&dn).err().unwrap().to_string().contains("in use"), "a second node cannot open the same directory");
        // block 1 left memory, and is still served: by hash and by locator
        assert!(!node.blocks.contains_key(&blocks[0].hash()));
        assert_eq!(node.block(&blocks[0].hash()).unwrap().encode(), blocks[0].encode());
        let genesis = crate::node::genesis_hash(node.tip().p.chain);
        assert_eq!(node.next_after(&[genesis]).unwrap().encode(), blocks[0].encode());
        assert_eq!(node.next_after(&[blocks[3].hash()]).unwrap().encode(), blocks[4].encode());
        let (tip, tip_state) = (node.best, node.tip().root());
        drop(node);
        // restart: same chain, same state
        let mut node = open(&dn).unwrap();
        assert_eq!((node.best, node.height(), node.tip().root()), (tip, 9, tip_state));
        assert_eq!(node.block(&blocks[1].hash()).unwrap().encode(), blocks[1].encode());
        node.tip().audit().unwrap();
        drop(node);
        // a crash in the middle of writing block 10: the log ends with half a record
        let b10 = dn.next_block(24, 8).unwrap();
        { let mut n = open(&dn).unwrap(); n.add_block(&b10, now).unwrap(); }
        let path = dir.join("blocks.log");
        let len = std::fs::metadata(&path).unwrap().len();
        std::fs::OpenOptions::new().write(true).open(&path).unwrap().set_len(len - 40).unwrap();
        let mut node = open(&dn).unwrap();
        assert_eq!(node.height(), 9, "block 10 was not whole, so it is gone");
        assert!(node.repaired() > 0);
        assert!(matches!(node.add_block(&b10, now).unwrap().main, Added::Extended), "and can be added again");
        assert_eq!(node.height(), 10);
        drop(node);
        assert_eq!(open(&dn).unwrap().height(), 10);
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// a node restarts from a snapshot of the state and only validates the blocks after it; a snapshot that is damaged, foreign or at odds with the log is passed over
    #[test]
    fn a_node_restarts_from_a_snapshot_and_falls_back_to_the_whole_log_when_it_must() {
        let dir = std::env::temp_dir().join(format!("zen-node-snap-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let mut dn = dev::Devnet::new(None, 8).unwrap();
        let open = |dn: &dev::Devnet| Node::open_with(Params::devnet(), &dev::genesis_of(&dn.keys), Box::new(DevStamp), Some(&dir), 3, 2);
        let snaps = || { let mut v: Vec<u64> = std::fs::read_dir(&dir).unwrap().flatten().filter_map(|e| e.file_name().into_string().ok()?.strip_prefix("snapshot-")?.strip_suffix(".zen")?.parse().ok()).collect(); v.sort(); v };
        let mut node = open(&dn).unwrap();
        let now = u32::MAX;
        let mut blocks = vec![];
        for _ in 0..12 { let b = dn.next_block(24, 8).unwrap(); dn.chain.accept(&b, now).unwrap(); node.add_block(&b, now).unwrap(); blocks.push(b); }
        // the window is 3 and a snapshot is due every 2 heights: with the tip at 12 the state at 9 is the newest no reorg can reach, snapshots were written
        // at 2, 4, 6 and 8 and only the newest two stay
        assert_eq!(snaps(), vec![6, 8]);
        let (tip, root) = (node.best, node.tip().root());
        drop(node);
        let node = open(&dn).unwrap();
        assert_eq!((node.from_snapshot, node.best, node.height(), node.tip().root()), (8, tip, 12, root));
        assert!(node.snaps.values().all(|c| c.height >= 8), "nothing before the snapshot was rebuilt");
        assert_eq!(node.block(&blocks[0].hash()).unwrap().encode(), blocks[0].encode(), "old blocks are still served");
        assert_eq!(node.next_after(&[crate::node::genesis_hash(3)]).unwrap().encode(), blocks[0].encode());
        assert_eq!(node.locator().last(), Some(&crate::node::genesis_hash(3)));
        node.tip().audit().unwrap();
        drop(node);
        // it goes on, and a block added after a restart from a snapshot reaches the next restart
        let mut node = open(&dn).unwrap();
        for _ in 0..4 { let b = dn.next_block(24, 8).unwrap(); dn.chain.accept(&b, now).unwrap(); node.add_block(&b, now).unwrap(); }
        let (tip, root) = (node.best, node.tip().root());
        assert_eq!(snaps(), vec![10, 12]);
        drop(node);
        let node = open(&dn).unwrap();
        assert_eq!((node.from_snapshot, node.best, node.height(), node.tip().root()), (12, tip, 16, root));
        drop(node);
        // a damaged newest snapshot: the older one is used
        let newest = dir.join("snapshot-12.zen");
        let mut b = std::fs::read(&newest).unwrap(); let n = b.len() / 2; b[n] ^= 1; std::fs::write(&newest, b).unwrap();
        let node = open(&dn).unwrap();
        assert_eq!((node.from_snapshot, node.best, node.tip().root()), (10, tip, root));
        drop(node);
        // that open wrote a fresh snapshot (13) over the damaged one; a snapshot under the wrong name is passed over for the next one
        assert_eq!(snaps(), vec![12, 13]);
        std::fs::copy(dir.join("snapshot-13.zen"), dir.join("snapshot-99.zen")).unwrap();
        let node = open(&dn).unwrap();
        assert_eq!((node.from_snapshot, node.best, node.tip().root()), (13, tip, root), "99 is refused, 13 is used");
        drop(node);
        for (_, f) in Node::snapshot_files_for_test(&dir) { std::fs::remove_file(f).unwrap(); }
        let node = open(&dn).unwrap();
        assert_eq!((node.from_snapshot, node.best, node.height(), node.tip().root()), (0, tip, 16, root));
        drop(node);
        // ZEN_REVALIDATE ignores snapshots even when they are fine
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn old_snapshots_are_dropped_and_forks_too_deep_are_stale() {
        let mut dn = dev::Devnet::new(None, 8).unwrap();
        let mut node = node_of(&dn);
        node.max_reorg = 3;
        let now = u32::MAX;
        let mut at = vec![dn.chain.clone()];                       // the chain after each height
        for _ in 0..9 { let b = dn.next_block(24, 8).unwrap(); dn.chain.accept(&b, now).unwrap(); node.add_block(&b, now).unwrap(); at.push(dn.chain.clone()); }
        assert_eq!(node.tip().height, 9);
        assert!(node.snaps.len() <= 5, "{} snapshots kept", node.snaps.len());
        assert_eq!(node.blocks.len(), 9, "the best chain's blocks stay");
        // a branch from a block that is too old: not an error, not kept
        let old = dn.block_on(&at[2], 24, 8).unwrap();
        assert_eq!(node.add_block(&old, now).unwrap().main, Added::Stale);
        assert!(!node.have(&old.hash()));
        // a branch inside the window still competes
        let near = dn.block_on(&at[8], 24, 8).unwrap();
        let r = node.add_block(&near, now).unwrap().main;
        assert!(matches!(r, Added::Side | Added::Reorg(_)), "{r:?}");
        // a heavier branch inside the window wins and the best chain follows it
        let heavy = dn.block_on(&at[7], 48, 8).unwrap();
        let r = node.add_block(&heavy, now).unwrap().main;
        assert!(matches!(r, Added::Side | Added::Reorg(_)), "{r:?}");
        let c = node.tip();
        c.audit().unwrap();
        assert_eq!(node.locator().first(), Some(&node.best));
        assert_eq!(node.locator().last(), Some(&crate::node::genesis_hash(node.tip().p.chain)), "the locator ends at genesis");
    }

    #[test]
    fn a_chain_longer_than_the_orphan_buffer_syncs_forward() {
        let mut dn = dev::Devnet::new(None, 8).unwrap();
        let (a, b) = (Net::new(node_of(&dn)), Net::new(node_of(&dn)));
        // B holds only 3 orphans, so walking back from the tip (the old way) cannot reach genesis in 12 blocks; asking forward can
        b.node.lock().unwrap().max_orphans = 3;
        for _ in 0..12 { let blk = dn.next_block(24, 8).unwrap(); dn.chain.accept(&blk, u32::MAX).unwrap(); a.submit(&blk).unwrap(); }
        assert_eq!(a.height(), 12);
        let addr = a.listen("127.0.0.1:0").unwrap();
        b.connect(addr).unwrap();
        wait("B to sync 12 blocks", || b.height() == 12);
        assert_eq!(b.best(), a.best());
        b.node.lock().unwrap().tip().audit().unwrap();
    }

    #[test]
    fn peers_that_break_the_rules_are_banned() {
        let dn = dev::Devnet::new(None, 4).unwrap();
        // a frame of unknown type
        let a = Net::new(node_of(&dn));
        let addr = a.listen("127.0.0.1:0").unwrap();
        let mut s = raw_peer(addr);
        s.write_all(&1u32.to_le_bytes()).unwrap(); s.write_all(&[99]).unwrap();
        wait("the ban", || a.is_banned("127.0.0.1".parse().unwrap()));
        assert!(closed(&mut s));
        let mut again = TcpStream::connect(addr).unwrap(); again.set_read_timeout(Some(Duration::from_secs(5))).unwrap();
        assert!(closed(&mut again), "a banned address is refused");
        // a block that does not validate
        let mut dn2 = dev::Devnet::new(None, 4).unwrap();
        let b = Net::new(node_of(&dn2));
        let addr = b.listen("127.0.0.1:0").unwrap();
        let mut s = raw_peer(addr);
        write_msg(&mut s, &raw_hello(&b, 0)).unwrap();
        let mut bad = dn2.next_block(24, 8).unwrap(); bad.stamp[0] ^= 1;
        write_msg(&mut s, &Msg::Block(bad.encode())).unwrap();
        wait("the ban for a bad block", || b.is_banned("127.0.0.1".parse().unwrap()));
        assert_eq!(b.height(), 0);
        // anything but a hello or a wallet request before the hello
        let c = Net::new(node_of(&dn));
        let addr = c.listen("127.0.0.1:0").unwrap();
        let mut s = raw_peer(addr);
        write_msg(&mut s, &Msg::GetBlock([1; 32])).unwrap();
        wait("the ban for skipping the hello", || c.is_banned("127.0.0.1".parse().unwrap()));
        // a flood: more messages than the window allows
        let d = Net::new(node_of(&dn)).with_limits(Limits { msgs_per_window: 50, ..Limits::default() });
        let addr = d.listen("127.0.0.1:0").unwrap();
        let mut s = raw_peer(addr);
        write_msg(&mut s, &raw_hello(&d, 0)).unwrap();
        for _ in 0..200 { if write_msg(&mut s, &Msg::GetBlock([2; 32])).is_err() { break; } }
        wait("the ban for flooding", || d.is_banned("127.0.0.1".parse().unwrap()) || false);
    }

    #[test]
    fn connection_limits_and_timeouts() {
        let dn = dev::Devnet::new(None, 4).unwrap();
        let a = Net::new(node_of(&dn)).with_limits(Limits { per_ip: 2, hello_secs: 2, ..Limits::default() });
        let addr = a.listen("127.0.0.1:0").unwrap();
        let socks: Vec<TcpStream> = (0..5).map(|_| TcpStream::connect(addr).unwrap()).collect();
        std::thread::sleep(Duration::from_millis(500));
        assert_eq!(a.peer_count(), 2, "two connections per address");
        // silent connections are closed once the time to say hello is up
        wait("silent connections to be closed", || a.peer_count() == 0);
        drop(socks);
        // the inbound cap
        let b = Net::new(node_of(&dn)).with_limits(Limits { max_inbound: 3, per_ip: 10, ..Limits::default() });
        let addr = b.listen("127.0.0.1:0").unwrap();
        let _keep: Vec<TcpStream> = (0..6).map(|_| TcpStream::connect(addr).unwrap()).collect();
        std::thread::sleep(Duration::from_millis(500));
        assert_eq!(b.peer_count(), 3);
    }

    #[test]
    fn peers_find_each_other() {
        let dn = dev::Devnet::new(None, 4).unwrap();
        let (a, b, c) = (Net::new(node_of(&dn)), Net::new(node_of(&dn)), Net::new(node_of(&dn)));
        let aa = a.listen("127.0.0.1:0").unwrap();
        let _ = b.listen("127.0.0.1:0").unwrap();
        let cc = c.listen("127.0.0.1:0").unwrap();
        c.connect(aa).unwrap();
        wait("A to hear C", || a.known_addrs() >= 1 && a.peer_count() == 1);
        b.connect(aa).unwrap();
        // B asks A for addresses and learns C's
        wait("B to learn C's address", || b.known_addrs() >= 2);
        b.maintain();
        wait("B and C to be connected", || c.peer_count() == 2 && b.peer_count() == 2);
        let _ = cc;
    }

    #[test]
    fn a_stratum_client_cannot_send_an_endless_line() {
        let dn = dev::Devnet::new(None, 4).unwrap();
        let a = Net::new(node_of(&dn));
        let pool = Stratum::new(a.clone(), Arc::new(dev::DevSource { keys: dn.keys.clone(), miner: dn.keys[0].addr, maker: dn.maker.clone() }));
        let saddr = pool.listen("127.0.0.1:0").unwrap();
        let mut s = TcpStream::connect(saddr).unwrap(); s.set_read_timeout(Some(Duration::from_secs(5))).unwrap();
        let junk = vec![b'a'; 4096];
        for _ in 0..20 { if s.write_all(&junk).is_err() { break; } }
        assert!(closed(&mut s));
    }
}
