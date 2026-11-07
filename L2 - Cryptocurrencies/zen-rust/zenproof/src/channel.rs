// Off-chain channel state and the `zenproof chan ...` commands (stage 3, Justus L. Ludovic).
//
// A channel (locks.rs, Terms::Channel) holds the coins on chain. Off chain, the two sides keep a file with the latest state both have signed:
// update number `seq` and a's share `bal_a` (b's is the rest). A payment is a new state with the payer's share lower, in three messages passed by any
// means (a file, a chat, a socket): `pay` makes a proposal, the other side checks it and `accept`s with a counter-signature, the payer `commit`s.
// Only the newest state ever matters on chain (an older one posted late is replaced), so there is nothing to punish and nothing to watch for except
// that the latest state is posted within the window if the other side posts an older one.
// A stream (oneway) is one number signed by the payer alone: seq = the amount paid so far.
//
//   chan open <wallet> <node> <peer address> <peer pubkey> <amount> <window blocks> [oneway]   fund a channel (the peer is b)
//   chan join <file> <wallet> <node> <funder address>                                           the peer writes its file once the channel is on chain
//   chan adopt <file> <wallet> <node> <peer address>            the funder writes its file for a channel it opened with the peer (a factory member's too)
//   chan factory-open <wallet> <node> <window blocks> <member address> <member pubkey> <capacity> [more members]
//   chan show <file>
//   chan pay <file> <wallet> <amount>         -> proposal (hex)       (streams: signs and updates the file; prints the signed state)
//   chan accept <file> <wallet> <proposal>    -> acknowledgement (hex)
//   chan commit <file> <acknowledgement>
//   chan close-sign <file> <wallet>           -> my signature on closing at the current balances
//   chan close <file> <wallet> <node> [peer's close signature]    close at once (a stream: the payer alone)
//   chan dispute <file> <wallet> <node>       post the latest state on chain (starts the window)
//   chan settle <file> <wallet> <node>        after the window: each side is paid
// <node> is "p2p address,api address".
use crate::locks::{chan_close_msg, chan_state_msg, fact_close_msg, fact_state_msg, plocks_total, ChanSigs, OpReq, PLock, SignedOp, MAX_PLOCKS};
use crate::tx::{http_get, parse_address, split_node, address_string, Wallet};
use crate::{mint, F};
use anyhow::{anyhow, bail, Result};
use std::path::Path;

fn hex(b: &[u8]) -> String { b.iter().map(|x| format!("{x:02x}")).collect() }
fn unhex(s: &str) -> Result<Vec<u8>> { (0..s.len() / 2).map(|i| Ok(u8::from_str_radix(s.get(2 * i..2 * i + 2).ok_or_else(|| anyhow!("bad hex"))?, 16)?)).collect() }

/// A channel's latest doubly signed state, as one side keeps it.
pub struct Chan {
    pub chain: u8, pub id: [u8; 32], pub role_a: bool, pub a: [F; 4], pub b: [F; 4], pub key_a: [u8; 41], pub key_b: [u8; 41], pub cap: u64, pub delay: u64, pub oneway: bool,
    pub seq: u64, pub bal_a: u64, pub locks: Vec<PLock>, pub sigs: ChanSigs,
    /// a proposal this side made and is waiting to see acknowledged (its bytes)
    pub pending: Option<Vec<u8>>,
    /// scalars learned that open point locks of this channel: (point, scalar). Needed to settle on chain if the other side vanishes.
    pub secrets: Vec<([u8; 41], [u8; 40])>,
    /// where the other side listens for routing messages (route.rs)
    pub peer_addr: Option<String>,
    /// a channel inside a factory: the factory's id and the member's number (the coordinator is always side a)
    pub fid: Option<([u8; 32], u8)>,
}
/// what a proposal says, parsed
pub struct Prop { pub seq: u64, pub bal_a: u64, pub locks: Vec<PLock>, pub witness: Option<[u8; 40]>, pub e: u128, pub s: [u8; 40] }
impl Prop {
    pub fn encode(&self) -> Vec<u8> {
        let mut w = crate::store::Wr::new();
        w.u64(self.seq); w.u64(self.bal_a); w.u8(self.locks.len() as u8); for l in &self.locks { l.encode(&mut w); }
        match &self.witness { Some(t) => { w.u8(1); w.raw(t); } None => w.u8(0) }
        w.u128(self.e); w.raw(&self.s); w.0
    }
    pub fn decode(b: &[u8]) -> Result<Prop> {
        let mut r = crate::store::Rd::new(b);
        let (seq, bal_a) = (r.u64()?, r.u64()?);
        let n = r.u8()? as usize; if n > MAX_PLOCKS { bail!("too many point locks"); }
        let locks = (0..n).map(|_| PLock::decode(&mut r)).collect::<Result<Vec<_>>>()?;
        let witness = match r.u8()? { 0 => None, 1 => Some(r.take(40)?.try_into()?), _ => bail!("bad flag") };
        let (e, s) = (r.u128()?, r.take(40)?.try_into()?);
        r.done()?;
        Ok(Prop { seq, bal_a, locks, witness, e, s })
    }
}
impl Chan {
    pub fn bal_b(&self) -> u64 { self.cap - self.bal_a - plocks_total(&self.locks) as u64 }
    pub fn mine(&self) -> u64 { if self.role_a { self.bal_a } else { self.bal_b() } }
    pub fn theirs(&self) -> u64 { if self.role_a { self.bal_b() } else { self.bal_a } }
    fn msg(&self, seq: u64, bal_a: u64, locks: &[PLock]) -> [F; 4] {
        match &self.fid { Some((f, i)) => fact_state_msg(self.chain, f, *i, seq, bal_a, self.cap, locks), None => chan_state_msg(self.chain, &self.id, seq, bal_a, self.cap, locks) }
    }
    /// what both sign to close at once with a's share `bal_a`
    pub fn close_msg(&self, bal_a: u64) -> [F; 4] {
        match &self.fid { Some((f, i)) => fact_close_msg(self.chain, f, *i, bal_a, self.cap), None => chan_close_msg(self.chain, &self.id, bal_a, self.cap) }
    }
    fn check(&self, key: &[u8; 41], seq: u64, bal_a: u64, locks: &[PLock], e: u128, s: &[u8; 40]) -> bool {
        mint::decode_point(key).map_or(false, |p| mint::verify(p, self.msg(seq, bal_a, locks), e, &num_bigint::BigUint::from_bytes_le(s)))
    }
    pub fn to_text(&self) -> String {
        let mut t = format!("chain {}\nid {}\nrole {}\na {}\nb {}\nkey_a {}\nkey_b {}\ncap {}\ndelay {}\noneway {}\nseq {}\nbal_a {}\nea {}\nsa {}\neb {}\nsb {}\n",
            self.chain, hex(&self.id), if self.role_a { "a" } else { "b" }, address_string(&self.a), address_string(&self.b), hex(&self.key_a), hex(&self.key_b), self.cap, self.delay, self.oneway,
            self.seq, self.bal_a, hex(&self.sigs.ea.to_le_bytes()), hex(&self.sigs.sa), hex(&self.sigs.eb.to_le_bytes()), hex(&self.sigs.sb));
        for l in &self.locks { t += &format!("lock {} {} {} {}\n", l.amt, l.to_b, hex(&l.point), l.expiry); }
        for (p, k) in &self.secrets { t += &format!("secret {} {}\n", hex(p), hex(k)); }
        if let Some(p) = &self.pending { t += &format!("pending {}\n", hex(p)); }
        if let Some(a) = &self.peer_addr { t += &format!("peer_addr {a}\n"); }
        if let Some((f, i)) = &self.fid { t += &format!("fid {} {i}\n", hex(f)); }
        t
    }
    pub fn parse(t: &str) -> Result<Chan> {
        let get = |k: &str| t.lines().find_map(|l| l.strip_prefix(&format!("{k} "))).ok_or_else(|| anyhow!("the channel file has no {k}"));
        let u128of = |h: &str| -> Result<u128> { Ok(u128::from_le_bytes(unhex(h)?.try_into().map_err(|_| anyhow!("bad e"))?)) };
        let arr = |h: &str| -> Result<[u8; 40]> { unhex(h)?.try_into().map_err(|_| anyhow!("bad signature")) };
        let mut locks = vec![]; let mut secrets = vec![];
        for l in t.lines() {
            if let Some(r) = l.strip_prefix("lock ") { let v: Vec<&str> = r.split(' ').collect(); if v.len() != 4 { bail!("bad lock line"); }
                locks.push(PLock { amt: v[0].parse()?, to_b: v[1] == "true", point: unhex(v[2])?.try_into().map_err(|_| anyhow!("bad point"))?, expiry: v[3].parse()? }); }
            if let Some(r) = l.strip_prefix("secret ") { let v: Vec<&str> = r.split(' ').collect(); if v.len() != 2 { bail!("bad secret line"); }
                secrets.push((unhex(v[0])?.try_into().map_err(|_| anyhow!("bad point"))?, arr(v[1])?)); }
        }
        let pending = t.lines().find_map(|l| l.strip_prefix("pending ")).map(unhex).transpose()?;
        Ok(Chan { chain: get("chain")?.parse()?, id: unhex(get("id")?)?.try_into().map_err(|_| anyhow!("bad id"))?, role_a: get("role")? == "a", a: parse_address(get("a")?)?, b: parse_address(get("b")?)?,
            key_a: unhex(get("key_a")?)?.try_into().map_err(|_| anyhow!("bad key"))?, key_b: unhex(get("key_b")?)?.try_into().map_err(|_| anyhow!("bad key"))?,
            cap: get("cap")?.parse()?, delay: get("delay")?.parse()?, oneway: get("oneway")? == "true", seq: get("seq")?.parse()?, bal_a: get("bal_a")?.parse()?, locks,
            sigs: ChanSigs { ea: u128of(get("ea")?)?, sa: arr(get("sa")?)?, eb: u128of(get("eb")?)?, sb: arr(get("sb")?)? }, pending, secrets, peer_addr: t.lines().find_map(|l| l.strip_prefix("peer_addr ")).map(|x| x.to_string()),
            fid: match t.lines().find_map(|l| l.strip_prefix("fid ")) { Some(l) => { let v: Vec<&str> = l.split(' ').collect(); if v.len() != 2 { bail!("bad fid line"); } Some((unhex(v[0])?.try_into().map_err(|_| anyhow!("bad fid"))?, v[1].parse()?)) } None => None } })
    }
    pub fn load(p: &Path) -> Result<Chan> { Chan::parse(&std::fs::read_to_string(p)?) }
    pub fn save(&self, p: &Path) -> Result<()> { let tmp = p.with_extension("tmp"); std::fs::write(&tmp, self.to_text())?; std::fs::rename(&tmp, p)?; Ok(()) }

    /// sign the next state (this side proposes it)
    fn propose(&mut self, w: &Wallet, bal_a: u64, locks: Vec<PLock>, witness: Option<[u8; 40]>) -> Result<Vec<u8>> {
        if self.pending.is_some() { bail!("a proposal is still waiting for its acknowledgement"); }
        if locks.len() > MAX_PLOCKS { bail!("at most {MAX_PLOCKS} point locks at once"); }
        let seq = self.seq + 1;
        let (e, s) = mint::sign(&w.key, self.msg(seq, bal_a, &locks));
        let p = Prop { seq, bal_a, locks, witness, e, s: mint::s_bytes(&s) }.encode();
        self.pending = Some(p.clone());
        Ok(p)
    }
    /// pay `amt` to the other side
    pub fn pay(&mut self, w: &Wallet, amt: u64) -> Result<Vec<u8>> {
        if amt == 0 { bail!("nothing to pay"); }
        if self.oneway {
            if !self.role_a { bail!("only the payer of a stream signs its payments"); }
            let paid = self.seq.checked_add(amt).filter(|p| *p <= self.cap).ok_or_else(|| anyhow!("the stream holds only {} more", self.cap - self.seq))?;
            let bal_a = self.cap - paid;
            let (e, s) = mint::sign(&w.key, self.msg(paid, bal_a, &[]));
            let s = mint::s_bytes(&s);
            self.seq = paid; self.bal_a = bal_a; self.sigs = ChanSigs { ea: e, sa: s, eb: 0, sb: [0; 40] };
            return Ok(Prop { seq: paid, bal_a, locks: vec![], witness: None, e, s }.encode());
        }
        if self.mine() < amt { bail!("this side has {} in the channel, not {amt}", self.mine()); }
        let bal_a = if self.role_a { self.bal_a - amt } else { self.bal_a + amt };
        self.propose(w, bal_a, self.locks.clone(), None)
    }
    /// put `amt` into a point lock for the other side: they get it on showing the scalar of `point`, it comes back here after `expiry` (a height of this chain)
    pub fn add_lock(&mut self, w: &Wallet, amt: u64, point: [u8; 41], expiry: u64) -> Result<Vec<u8>> {
        if self.oneway { bail!("a stream holds no point locks"); }
        if amt == 0 || self.mine() < amt { bail!("this side has {} in the channel, not {amt}", self.mine()); }
        let mut locks = self.locks.clone(); locks.push(PLock { amt, to_b: self.role_a, point, expiry });
        let bal_a = if self.role_a { self.bal_a - amt } else { self.bal_a };
        self.propose(w, bal_a, locks, None)
    }
    /// take a point lock the other side made for this side, showing its scalar
    pub fn fulfil(&mut self, w: &Wallet, idx: usize, t: [u8; 40]) -> Result<Vec<u8>> {
        let l = self.locks.get(idx).ok_or_else(|| anyhow!("no point lock {idx}"))?.clone();
        if l.to_b != !self.role_a { bail!("this point lock is not for this side"); }
        if !l.opened_by(&t) { bail!("that scalar does not open the lock"); }
        let mut locks = self.locks.clone(); locks.remove(idx);
        let bal_a = if self.role_a { self.bal_a + l.amt } else { self.bal_a };
        self.propose(w, bal_a, locks, Some(t))
    }
    /// give a point lock the other side made back to them, unopened
    pub fn fail(&mut self, w: &Wallet, idx: usize) -> Result<Vec<u8>> {
        let l = self.locks.get(idx).ok_or_else(|| anyhow!("no point lock {idx}"))?.clone();
        if l.to_b != !self.role_a { bail!("this point lock is not for this side"); }
        let mut locks = self.locks.clone(); locks.remove(idx);
        let bal_a = if self.role_a { self.bal_a } else { self.bal_a + l.amt };
        self.propose(w, bal_a, locks, None)
    }
    /// the other side's proposal. It must be the next update, be signed by the proposer, and be one of: a payment to this side, a new point lock for this side
    /// (paid for by the proposer), a lock of the proposer's opened with its scalar, or a lock of this side's given back. Returns the acknowledgement.
    pub fn accept(&mut self, w: &Wallet, prop: &[u8]) -> Result<Vec<u8>> {
        if self.oneway { bail!("a stream's receiver does not accept payments, it holds the latest signed amount: use `commit`"); }
        if self.pending.is_some() { bail!("this side has a proposal waiting"); }
        let p = Prop::decode(prop)?;
        if p.seq != self.seq + 1 { bail!("the proposal is update {}, the next is {}", p.seq, self.seq + 1); }
        let prop_a = !self.role_a;
        let pk = if prop_a { self.key_a } else { self.key_b };
        if !self.check(&pk, p.seq, p.bal_a, &p.locks, p.e, &p.s) { bail!("the proposer's signature is bad"); }
        if p.locks.len() > MAX_PLOCKS || p.bal_a as u128 + plocks_total(&p.locks) > self.cap as u128 { bail!("more than the channel holds"); }
        // the proposer's and this side's shares, before and after
        let share = |bal_a: u64, locks: &[PLock], a: bool| if a { bal_a } else { self.cap - bal_a - plocks_total(locks) as u64 };
        let (pb0, pb1) = (share(self.bal_a, &self.locks, prop_a), share(p.bal_a, &p.locks, prop_a));
        let (ob0, ob1) = (share(self.bal_a, &self.locks, !prop_a), share(p.bal_a, &p.locks, !prop_a));
        let (old, new) = (&self.locks, &p.locks);
        if new.len() == old.len() {
            if new != old { bail!("a payment cannot change the point locks"); }
            if p.witness.is_some() { bail!("no witness is needed here"); }
            if !(pb1 <= pb0 && ob1 >= ob0 && pb0 - pb1 == ob1 - ob0) { bail!("the proposal takes money from this side"); }
        } else if new.len() == old.len() + 1 {
            if new[..old.len()] != old[..] { bail!("a new lock goes at the end"); }
            let l = &new[old.len()];
            if l.to_b != prop_a || l.amt == 0 { bail!("the new lock is not for this side"); }
            mint::decode_point(&l.point)?;
            if pb0 - pb1.min(pb0) != l.amt || ob1 != ob0 { bail!("a new lock is paid for by its sender alone"); }
        } else if new.len() + 1 == old.len() {
            let idx = (0..old.len()).find(|i| old[*i] != *new.get(*i).unwrap_or(&PLock { amt: 0, to_b: false, point: [0; 41], expiry: 0 })).unwrap_or(new.len());
            let mut rest = old.clone(); let l = rest.remove(idx);
            if rest != *new { bail!("exactly one lock may go"); }
            // the receiver of the lock is the proposer
            if l.to_b == prop_a { bail!("only the receiver of a point lock takes or gives it up"); }
            match p.witness {
                Some(t) => {
                    if !l.opened_by(&t) { bail!("the scalar does not open the lock"); }
                    if pb1 != pb0 + l.amt || ob1 != ob0 { bail!("an opened lock goes to its receiver"); }
                    self.secrets.push((l.point, t));
                }
                None => { if ob1 != ob0 + l.amt || pb1 != pb0 { bail!("an unopened lock goes back to its sender"); } }
            }
        } else { bail!("one change at a time"); }
        let (e2, s2) = mint::sign(&w.key, self.msg(p.seq, p.bal_a, &p.locks));
        let mine = (e2, mint::s_bytes(&s2));
        self.sigs = if prop_a { ChanSigs { ea: p.e, sa: p.s, eb: mine.0, sb: mine.1 } } else { ChanSigs { ea: mine.0, sa: mine.1, eb: p.e, sb: p.s } };
        self.seq = p.seq; self.bal_a = p.bal_a; self.locks = p.locks;
        let mut v = p.seq.to_le_bytes().to_vec(); v.extend(e2.to_le_bytes()); v.extend(mine.1);
        Ok(v)
    }
    /// the other side's acknowledgement of the proposal this side made. (A stream's receiver instead stores the payer's newest proposal with `commit_stream`.)
    pub fn commit(&mut self, ack: &[u8]) -> Result<()> {
        if ack.len() != 8 + 16 + 40 { bail!("not an acknowledgement"); }
        let seq = u64::from_le_bytes(ack[..8].try_into()?);
        let (e, s): (u128, [u8; 40]) = (u128::from_le_bytes(ack[8..24].try_into()?), ack[24..64].try_into()?);
        let pend = Prop::decode(self.pending.as_ref().ok_or_else(|| anyhow!("no proposal is waiting"))?)?;
        if seq != pend.seq { bail!("this acknowledges update {seq}, not {}", pend.seq); }
        let other = if self.role_a { self.key_b } else { self.key_a };
        if !self.check(&other, pend.seq, pend.bal_a, &pend.locks, e, &s) { bail!("the other side's signature is bad"); }
        self.sigs = if self.role_a { ChanSigs { ea: pend.e, sa: pend.s, eb: e, sb: s } } else { ChanSigs { ea: e, sa: s, eb: pend.e, sb: pend.s } };
        if let Some(t) = pend.witness { let l = self.locks.iter().find(|l| l.opened_by(&t)); if let Some(l) = l { self.secrets.push((l.point, t)); } }
        self.seq = pend.seq; self.bal_a = pend.bal_a; self.locks = pend.locks; self.pending = None;
        Ok(())
    }
    /// a stream's receiver stores the payer's newest signed amount
    pub fn commit_stream(&mut self, msg: &[u8]) -> Result<()> {
        if !self.oneway || self.role_a { bail!("only a stream's receiver does this"); }
        let p = Prop::decode(msg)?;
        if p.seq <= self.seq || p.bal_a != self.cap.checked_sub(p.seq).ok_or_else(|| anyhow!("more than the stream holds"))? || !p.locks.is_empty() { bail!("not a newer state of this stream"); }
        if !self.check(&self.key_a.clone(), p.seq, p.bal_a, &[], p.e, &p.s) { bail!("the payer's signature is bad"); }
        self.seq = p.seq; self.bal_a = p.bal_a; self.sigs = ChanSigs { ea: p.e, sa: p.s, eb: 0, sb: [0; 40] };
        Ok(())
    }
    /// the newest agreed state with both signatures, as one message (what a peer that missed it needs): update, a's share, point locks, both signatures
    pub fn state_blob(&self) -> Vec<u8> {
        let mut w = crate::store::Wr::new();
        w.u64(self.seq); w.u64(self.bal_a); w.u8(self.locks.len() as u8); for l in &self.locks { l.encode(&mut w); }
        w.u128(self.sigs.ea); w.raw(&self.sigs.sa); w.u128(self.sigs.eb); w.raw(&self.sigs.sb); w.0
    }
    /// take a newer state the peer holds: both signatures must check, and it must fit in the channel. A proposal this side had waiting is dropped
    /// (the peer's state is the one that was agreed). Nothing else changes: the secrets learned stay, a lock that is gone needs none.
    pub fn adopt_state(&mut self, blob: &[u8]) -> Result<()> {
        let mut r = crate::store::Rd::new(blob);
        let (seq, bal_a) = (r.u64()?, r.u64()?);
        let n = r.u8()? as usize; if n > MAX_PLOCKS { bail!("too many point locks"); }
        let locks = (0..n).map(|_| PLock::decode(&mut r)).collect::<Result<Vec<_>>>()?;
        let sigs = ChanSigs { ea: r.u128()?, sa: r.take(40)?.try_into()?, eb: r.u128()?, sb: r.take(40)?.try_into()? };
        r.done()?;
        if seq <= self.seq { bail!("not newer than this side's state"); }
        if self.oneway { bail!("a stream's receiver keeps the payer's signature, not a two-sided state"); }
        if bal_a as u128 + plocks_total(&locks) > self.cap as u128 { bail!("more than the channel holds"); }
        if !self.check(&self.key_a.clone(), seq, bal_a, &locks, sigs.ea, &sigs.sa) || !self.check(&self.key_b.clone(), seq, bal_a, &locks, sigs.eb, &sigs.sb) { bail!("a signature on the state is bad"); }
        self.seq = seq; self.bal_a = bal_a; self.locks = locks; self.sigs = sigs; self.pending = None;
        Ok(())
    }
    /// does `(e, s)` sign the close of this channel at a's share `bal_a`, by the other side
    pub fn close_sig_ok(&self, bal_a: u64, e: u128, s: &[u8; 40]) -> bool {
        let other = if self.role_a { self.key_b } else { self.key_a };
        mint::decode_point(&other).map_or(false, |p| mint::verify(p, self.close_msg(bal_a), e, &num_bigint::BigUint::from_bytes_le(s)))
    }
    /// this side's signature to close at the newest state
    pub fn close_sig(&self, w: &Wallet) -> (u128, [u8; 40]) { let (e, s) = mint::sign(&w.key, self.close_msg(self.bal_a)); (e, mint::s_bytes(&s)) }
    /// forget a proposal the other side never acknowledged (it is not a state: nothing was agreed)
    pub fn drop_pending(&mut self) { self.pending = None; }
}

fn parse_node(a: &[String], i: usize) -> Result<(std::net::SocketAddr, String)> { split_node(a.get(i).ok_or_else(|| anyhow!("missing node"))?) }
fn find(api: &str, mine: &[F; 4], pred: impl Fn(&serde_json::Value) -> bool) -> Result<serde_json::Value> {
    let v = http_get(api, &format!("/api/channels?addr={}", address_string(mine)))?;
    v["channels"].as_array().into_iter().flatten().find(|c| pred(c)).cloned().ok_or_else(|| anyhow!("no such channel on chain yet"))
}
fn from_api(c: &serde_json::Value, role_a: bool) -> Result<Chan> {
    let s = |k: &str| c[k].as_str().unwrap_or("");
    Ok(Chan { chain: c["chain"].as_u64().unwrap_or(0) as u8, id: unhex(s("id"))?.try_into().map_err(|_| anyhow!("bad id"))?, role_a, a: parse_address(s("a"))?, b: parse_address(s("b"))?,
        key_a: unhex(s("key_a"))?.try_into().map_err(|_| anyhow!("bad key"))?, key_b: unhex(s("key_b"))?.try_into().map_err(|_| anyhow!("bad key"))?,
        cap: c["capacity"].as_u64().unwrap_or(0), delay: c["delay"].as_u64().unwrap_or(0), oneway: c["oneway"].as_bool().unwrap_or(false), seq: 0, bal_a: c["bal_a"].as_u64().unwrap_or(0),
        locks: vec![], sigs: ChanSigs::NONE, pending: None, secrets: vec![], peer_addr: None,
        fid: match c["fid"].as_str() { Some(f) => Some((unhex(f)?.try_into().map_err(|_| anyhow!("bad fid"))?, c["idx"].as_u64().unwrap_or(0) as u8)), None => None } })
}
fn send(w: &Wallet, p2p: std::net::SocketAddr, api: &str, chain: u8, req: OpReq) -> Result<SignedOp> {
    let info = crate::p2p::query_account(p2p, &w.address())?;
    if !info.found { bail!("this wallet has no account yet"); }
    let _ = api;
    let op = SignedOp::sign(&w.key, chain, info.nonce, req);
    crate::p2p::send_op(p2p, &op)?;
    Ok(op)
}

/// close together at the newest state with the other side's signature, on the chain at `p2p` / `api`
pub fn coop_close(c: &Chan, w: &Wallet, p2p: std::net::SocketAddr, api: &str, other: (u128, [u8; 40])) -> Result<String> {
    if c.oneway || !c.locks.is_empty() { bail!("a joint close needs a two-way channel with no point lock waiting"); }
    let me = w.address();
    let lock = find(api, &me, |x| x["id"] == hex(&c.id).as_str())?["lock"].as_str().map(|s| parse_address(s)).transpose()?.ok_or_else(|| anyhow!("no lock"))?;
    let (me_e, me_s) = c.close_sig(w);
    let sigs = if c.role_a { ChanSigs { ea: me_e, sa: me_s, eb: other.0, sb: other.1 } } else { ChanSigs { ea: other.0, sa: other.1, eb: me_e, sb: me_s } };
    let fee = http_get(api, "/api/status")?["sen_units"].as_u64().map_or(1, |s| (s + 99) / 100).max(1);
    let req = match c.fid { Some((_, idx)) => OpReq::FactoryExitNow { from: me, fee, lock, idx, bal_c: c.bal_a, sigs }, None => OpReq::ChanClose { from: me, fee, lock, bal_a: c.bal_a, sigs } };
    Ok(hex(&send(w, p2p, api, c.chain, req)?.id()))
}
/// What a guard does for one channel (a watchtower for any file in its folder, a node for its own channels), once. Returns what it did.
///   * the chain shows the channel closing at an OLDER update than this file's: post the newest state inside the window;
///   * the window is over: settle (with the point-lock secrets in the file);
///   * `lock_margin` (a node's own guard only): the channel is still open but a point lock is near its expiry, so the peer's silence would cost
///     money: start the close now, with the newest state, so that the window ends before the lock does.
pub fn guard(c: &Chan, w: &Wallet, p2p: std::net::SocketAddr, api: &str, done: &mut std::collections::HashSet<(String, u64, u8)>, lock_margin: Option<u64>) -> Vec<String> {
    let mut out = vec![];
    let Ok(on) = find(api, &c.a, |x| x["id"] == hex(&c.id).as_str()) else { return out };
    let (seq, until, height) = (on["seq"].as_u64().unwrap_or(0), on["until"].as_u64().unwrap_or(0), on["height"].as_u64().unwrap_or(0));
    let Ok(lock) = parse_address(on["lock"].as_str().unwrap_or("")) else { return out };
    let Ok(st) = http_get(api, "/api/status") else { return out };
    let fee = st["sen_units"].as_u64().map_or(1, |s| (s + 99) / 100).max(1);
    let id = hex(&c.id)[..8].to_string();
    let post = || match c.fid {
        None if c.seq == 0 => OpReq::ChanStart { from: w.address(), fee, lock },
        None => OpReq::ChanUpdate { from: w.address(), fee, lock, seq: c.seq, bal_a: c.bal_a, locks: c.locks.clone(), sigs: c.sigs },
        Some((_, idx)) if c.seq == 0 => OpReq::FactoryStart { from: w.address(), fee, lock, idx },
        Some((_, idx)) => OpReq::FactoryPost { from: w.address(), fee, lock, idx, seq: c.seq, bal_c: c.bal_a, locks: c.locks.clone(), sigs: c.sigs },
    };
    if on["state"] == "closing" {
        if height <= until && c.seq > seq && done.insert((id.clone(), c.seq, 0)) {
            match send(w, p2p, api, c.chain, post()) { Ok(op) => out.push(format!("guard: channel {id} closed at update {seq}, posted update {} | {}", c.seq, hex(&op.id()))), Err(e) => { done.remove(&(id.clone(), c.seq, 0)); out.push(format!("guard: channel {id}: {e}")) } }
        } else if height > until && c.seq <= seq && done.insert((id.clone(), seq, 1)) {
            let on_locks: Vec<PLock> = on["locks"].as_array().into_iter().flatten().filter_map(|l| Some(PLock { amt: l["amt"].as_u64()?, to_b: l["to_b"].as_bool()?, point: unhex(l["point"].as_str()?).ok()?.try_into().ok()?, expiry: l["expiry"].as_u64()? })).collect();
            let wits: Vec<Option<[u8; 40]>> = on_locks.iter().map(|l| c.secrets.iter().find(|(p, _)| *p == l.point).map(|(_, t)| *t)).collect();
            let req = match c.fid { Some((_, idx)) => OpReq::FactoryExit { from: w.address(), fee, lock, idx, wits }, None => OpReq::ChanSettle { from: w.address(), fee, lock, wits } };
            match send(w, p2p, api, c.chain, req) { Ok(op) => out.push(format!("guard: channel {id}: window over, settled | {}", hex(&op.id()))), Err(e) => { done.remove(&(id.clone(), seq, 1)); out.push(format!("guard: channel {id}: {e}")) } }
        }
    } else if on["state"] == "open" {
        if let Some(m) = lock_margin {
            let near = c.locks.iter().map(|l| l.expiry).min().map_or(false, |x| x <= height + c.delay + m);
            if near && done.insert((id.clone(), c.seq, 2)) {
                match send(w, p2p, api, c.chain, post()) { Ok(op) => out.push(format!("guard: channel {id}: a point lock expires at block {} (now {height}, window {}): closing on chain with update {} | {}", c.locks.iter().map(|l| l.expiry).min().unwrap_or(0), c.delay, c.seq, hex(&op.id()))), Err(e) => out.push(format!("guard: channel {id}: {e}")) }
            }
        }
    }
    out
}
pub fn chan_main() -> Result<()> {
    let a: Vec<String> = std::env::args().collect();
    let arg = |i: usize, what: &str| a.get(i).cloned().ok_or_else(|| anyhow!("missing {what}"));
    match a.get(2).map(|s| s.as_str()) {
        Some("open") => {
            let w = Wallet::load(Path::new(&arg(3, "wallet file")?))?;
            let (p2p, api) = parse_node(&a, 4)?;
            let peer = parse_address(&arg(5, "peer address")?)?;
            let key_b: [u8; 41] = unhex(&arg(6, "peer pubkey")?)?.try_into().map_err(|_| anyhow!("a public key is 41 bytes"))?;
            let amt: u64 = arg(7, "amount")?.parse()?; let delay: u64 = arg(8, "window blocks")?.parse()?;
            let oneway = a.get(9).map_or(false, |x| x == "oneway");
            let st = http_get(&api, "/api/status")?;
            let chain = st["chain"]["id"].as_u64().unwrap_or(0) as u8;
            let fee = crate::tx::Wallet::standard_fee(amt).max((st["sen_units"].as_u64().unwrap_or(1) + 99) / 100);
            let terms = crate::locks::Terms::Channel { a: w.address(), b: peer, key_a: mint::encode_point(w.key.a), key_b, delay, oneway, salt: 0, state: crate::locks::ChanState::Open };
            let op = send(&w, p2p, &api, chain, OpReq::Make { from: w.address(), amt, fee, terms })?;
            println!("channel funding sent | operation id {} | the other side runs `chan join` once it is in a block", hex(&op.id()));
        }
        Some("join") => {
            let w = Wallet::load(Path::new(&arg(4, "wallet file")?))?;
            let (_, api) = parse_node(&a, 5)?;
            let funder = parse_address(&arg(6, "funder address")?)?;
            let me = w.address();
            let c = find(&api, &me, |c| c["a"] == address_string(&funder).as_str() && c["b"] == address_string(&me).as_str() && c["state"] == "open")?;
            let ch = from_api(&c, false)?; ch.save(Path::new(&arg(3, "file")?))?;
            println!("joined: capacity {} | id {}", ch.cap, hex(&ch.id));
        }
        Some("adopt") => {
            // the funding side writes its file for a channel (or a factory member's channel) it opened with `peer`
            let w = Wallet::load(Path::new(&arg(4, "wallet file")?))?;
            let (_, api) = parse_node(&a, 5)?;
            let peer = parse_address(&arg(6, "peer address")?)?;
            let me = w.address();
            let c = find(&api, &me, |c| c["a"] == address_string(&me).as_str() && c["b"] == address_string(&peer).as_str() && c["state"] == "open")?;
            let ch = from_api(&c, true)?; ch.save(Path::new(&arg(3, "file")?))?;
            println!("adopted: capacity {} | id {}", ch.cap, hex(&ch.id));
        }
        Some("factory-open") => {
            // factory-open <wallet> <node> <window blocks> <member address> <member pubkey> <capacity> [...more members]
            let w = Wallet::load(Path::new(&arg(3, "wallet file")?))?;
            let (p2p, api) = parse_node(&a, 4)?;
            let delay: u64 = arg(5, "window blocks")?.parse()?;
            let rest = &a[6.min(a.len())..];
            if rest.is_empty() || rest.len() % 3 != 0 { bail!("each member is <address> <pubkey> <capacity>"); }
            let mut members = vec![];
            for m in rest.chunks(3) {
                members.push(crate::locks::FMember { addr: parse_address(&m[0])?, key: unhex(&m[1])?.try_into().map_err(|_| anyhow!("a public key is 41 bytes"))?, cap: m[2].parse()?, base: m[2].parse()?, state: crate::locks::SubState::Open });
            }
            let total: u64 = members.iter().map(|m| m.cap).sum();
            let st = http_get(&api, "/api/status")?;
            let chain = st["chain"]["id"].as_u64().unwrap_or(0) as u8;
            let fee = Wallet::standard_fee(total).max((st["sen_units"].as_u64().unwrap_or(1) + 99) / 100);
            let terms = crate::locks::Terms::Factory { coord: w.address(), key_c: mint::encode_point(w.key.a), members, delay, salt: 0 };
            let op = send(&w, p2p, &api, chain, OpReq::Make { from: w.address(), amt: total, fee, terms })?;
            println!("factory funding sent ({total} for {} members) | operation id {} | everyone runs `chan join` (members) or `chan adopt` (coordinator) once it is in a block", rest.len() / 3, hex(&op.id()));
        }
        Some("factory-fund") => {
            // factory-fund <wallet> <node> <coordinator address> <amount>: the member adds its own coins to its channel (before using it)
            let w = Wallet::load(Path::new(&arg(3, "wallet file")?))?;
            let (p2p, api) = parse_node(&a, 4)?;
            let coord = parse_address(&arg(5, "coordinator address")?)?; let amt: u64 = arg(6, "amount")?.parse()?;
            let me = w.address();
            let c = find(&api, &me, |c| c["a"] == address_string(&coord).as_str() && c["b"] == address_string(&me).as_str() && c["state"] == "open" && c["fid"].is_string())?;
            let fee = Wallet::standard_fee(amt).max((http_get(&api, "/api/status")?["sen_units"].as_u64().unwrap_or(1) + 99) / 100);
            let op = send(&w, p2p, &api, c["chain"].as_u64().unwrap_or(0) as u8, OpReq::FactoryFund { from: me, fee, lock: parse_address(c["lock"].as_str().unwrap_or(""))?, idx: c["idx"].as_u64().unwrap_or(0) as u8, amt })?;
            println!("channel funding sent: {amt} added to member {} | operation id {}", c["idx"], hex(&op.id()));
        }
        Some("show") => {
            let c = Chan::load(Path::new(&arg(3, "file")?))?;
            println!("channel {} on chain {} | {} | capacity {} | update {} | a has {} b has {} | this side is {} and has {} | window {} blocks", hex(&c.id), c.chain, if c.oneway { "stream" } else { "two-party" },
                     c.cap, c.seq, c.bal_a, c.bal_b(), if c.role_a { "a" } else { "b" }, c.mine(), c.delay);
        }
        Some("pay") => {
            let (f, w) = (arg(3, "file")?, Wallet::load(Path::new(&arg(4, "wallet file")?))?);
            let mut c = Chan::load(Path::new(&f))?; let amt: u64 = arg(5, "amount")?.parse()?;
            let p = c.pay(&w, amt)?; c.save(Path::new(&f))?;
            println!("{}", hex(&p));
        }
        Some("lock") => {
            // lock <file> <wallet> <amount> <point hex> <expiry height>: propose a point lock (what a routed payment does; for tests and demos)
            let (f, w) = (arg(3, "file")?, Wallet::load(Path::new(&arg(4, "wallet file")?))?);
            let mut c = Chan::load(Path::new(&f))?;
            let p = c.add_lock(&w, arg(5, "amount")?.parse()?, unhex(&arg(6, "point")?)?.try_into().map_err(|_| anyhow!("a point is 41 bytes"))?, arg(7, "expiry height")?.parse()?)?;
            c.save(Path::new(&f))?; println!("{}", hex(&p));
        }
        Some("accept") => {
            let (f, w) = (arg(3, "file")?, Wallet::load(Path::new(&arg(4, "wallet file")?))?);
            let mut c = Chan::load(Path::new(&f))?;
            let ack = c.accept(&w, &unhex(&arg(5, "proposal")?)?)?; c.save(Path::new(&f))?;
            println!("{}", hex(&ack));
        }
        Some("commit") => {
            let f = arg(3, "file")?; let mut c = Chan::load(Path::new(&f))?;
            let m = unhex(&arg(4, "message")?)?;
            if c.oneway { c.commit_stream(&m)?; } else { c.commit(&m)?; }
            c.save(Path::new(&f))?;
            println!("update {} stored: a has {} b has {}", c.seq, c.bal_a, c.bal_b());
        }
        Some("close-sign") => {
            let (c, w) = (Chan::load(Path::new(&arg(3, "file")?))?, Wallet::load(Path::new(&arg(4, "wallet file")?))?);
            let (e, s) = mint::sign(&w.key, c.close_msg(c.bal_a));
            let mut v = e.to_le_bytes().to_vec(); v.extend(mint::s_bytes(&s)); println!("{}", hex(&v));
        }
        Some("close") => {
            let (c, w) = (Chan::load(Path::new(&arg(3, "file")?))?, Wallet::load(Path::new(&arg(4, "wallet file")?))?);
            let (p2p, api) = parse_node(&a, 5)?;
            let lock = find(&api, &w.address(), |x| x["id"] == hex(&c.id).as_str())?["lock"].as_str().map(|s| parse_address(s)).transpose()?.ok_or_else(|| anyhow!("no lock"))?;
            let sig = |h: &str| -> Result<(u128, [u8; 40])> { let b = unhex(h)?; if b.len() != 56 { bail!("not a close signature"); } Ok((u128::from_le_bytes(b[..16].try_into()?), b[16..].try_into()?)) };
            let (mine_e, mine_s) = { let (e, s) = mint::sign(&w.key, c.close_msg(c.bal_a)); (e, mint::s_bytes(&s)) };
            let sigs = if c.oneway {
                if !c.role_a { bail!("a stream is closed by its payer's signature; the payer runs this"); }
                ChanSigs { ea: mine_e, sa: mine_s, eb: 0, sb: [0; 40] }
            } else {
                let (pe, ps) = sig(&arg(6, "the other side's close signature")?)?;
                if c.role_a { ChanSigs { ea: mine_e, sa: mine_s, eb: pe, sb: ps } } else { ChanSigs { ea: pe, sa: ps, eb: mine_e, sb: mine_s } }
            };
            let fee = http_get(&api, "/api/status")?["sen_units"].as_u64().map_or(1, |s| (s + 99) / 100).max(1);
            let op = send(&w, p2p, &api, c.chain, match c.fid { Some((_, idx)) => OpReq::FactoryExitNow { from: w.address(), fee, lock, idx, bal_c: c.bal_a, sigs }, None => OpReq::ChanClose { from: w.address(), fee, lock, bal_a: c.bal_a, sigs } })?;
            println!("close sent | a gets {} b gets {} | operation id {}", c.bal_a, c.bal_b(), hex(&op.id()));
        }
        Some("dispute") => {
            let (c, w) = (Chan::load(Path::new(&arg(3, "file")?))?, Wallet::load(Path::new(&arg(4, "wallet file")?))?);
            let (p2p, api) = parse_node(&a, 5)?;
            let on = find(&api, &w.address(), |x| x["id"] == hex(&c.id).as_str())?;
            let lock = parse_address(on["lock"].as_str().unwrap_or(""))?;
            let fee = http_get(&api, "/api/status")?["sen_units"].as_u64().map_or(1, |s| (s + 99) / 100).max(1);
            let req = match (c.fid, c.seq) {
                (None, 0) => OpReq::ChanStart { from: w.address(), fee, lock },
                (None, _) => OpReq::ChanUpdate { from: w.address(), fee, lock, seq: c.seq, bal_a: c.bal_a, locks: c.locks.clone(), sigs: c.sigs },
                (Some((_, idx)), 0) => OpReq::FactoryStart { from: w.address(), fee, lock, idx },
                (Some((_, idx)), _) => OpReq::FactoryPost { from: w.address(), fee, lock, idx, seq: c.seq, bal_c: c.bal_a, locks: c.locks.clone(), sigs: c.sigs },
            };
            let op = send(&w, p2p, &api, c.chain, req)?;
            println!("state {} posted (on chain it is {}{}) | operation id {}", c.seq, on["state"].as_str().unwrap_or(""), if on["state"] == "closing" { format!(" at update {}", on["seq"]) } else { String::new() }, hex(&op.id()));
        }
        Some("settle") => {
            let (c, w) = (Chan::load(Path::new(&arg(3, "file")?))?, Wallet::load(Path::new(&arg(4, "wallet file")?))?);
            let (p2p, api) = parse_node(&a, 5)?;
            let on = find(&api, &w.address(), |x| x["id"] == hex(&c.id).as_str())?;
            let lock = parse_address(on["lock"].as_str().unwrap_or(""))?;
            let fee = http_get(&api, "/api/status")?["sen_units"].as_u64().map_or(1, |s| (s + 99) / 100).max(1);
            // one witness entry per point lock the chain is holding: the scalar, where this side has learned it
            let on_locks: Vec<PLock> = on["locks"].as_array().into_iter().flatten().map(|l| Ok(PLock { amt: l["amt"].as_u64().unwrap_or(0), to_b: l["to_b"].as_bool().unwrap_or(false), point: unhex(l["point"].as_str().unwrap_or(""))?.try_into().map_err(|_| anyhow!("bad point"))?, expiry: l["expiry"].as_u64().unwrap_or(0) })).collect::<Result<_>>()?;
            let wits: Vec<Option<[u8; 40]>> = on_locks.iter().map(|l| c.secrets.iter().find(|(p, _)| *p == l.point).map(|(_, t)| *t)).collect();
            let op = send(&w, p2p, &api, c.chain, match c.fid { Some((_, idx)) => OpReq::FactoryExit { from: w.address(), fee, lock, idx, wits: wits.clone() }, None => OpReq::ChanSettle { from: w.address(), fee, lock, wits: wits.clone() } })?;
            println!("settle sent | {} point lock(s) held, {} opened by a scalar this side has | operation id {}", on_locks.len(), wits.iter().flatten().count(), hex(&op.id()));
        }
        Some("fund") => {
            // fund <wallet> <node> <a's address> <amount>: b adds its own coins to a channel a opened (before any update): a dual-funded channel.
            // Both sides then run `chan adopt` / `chan join` again to pick up the new capacity and shares.
            let w = Wallet::load(Path::new(&arg(3, "wallet file")?))?;
            let (p2p, api) = parse_node(&a, 4)?;
            let peer = parse_address(&arg(5, "a's address")?)?; let amt: u64 = arg(6, "amount")?.parse()?;
            let me = w.address();
            let c = find(&api, &me, |c| c["a"] == address_string(&peer).as_str() && c["b"] == address_string(&me).as_str() && c["state"] == "open" && c["fid"].is_null())?;
            let fee = Wallet::standard_fee(amt).max((http_get(&api, "/api/status")?["sen_units"].as_u64().unwrap_or(1) + 99) / 100);
            let op = send(&w, p2p, &api, c["chain"].as_u64().unwrap_or(0) as u8, OpReq::ChanFund { from: me, fee, lock: parse_address(c["lock"].as_str().unwrap_or(""))?, amt })?;
            println!("channel funding sent: {amt} added by b | operation id {}", hex(&op.id()));
        }
        Some("watch") => {
            // chan watch <dir of .chan files> <tower wallet> <node> [once]: a watchtower. Clients drop the newest copy of their channel file in the
            // directory after each update. When a channel starts closing at an OLDER update, the tower posts the newest state it holds inside the
            // dispute window; when the window is over it settles. It needs only a wallet with a few coins for fees and never holds anyone's funds.
            let dir = std::path::PathBuf::from(arg(3, "directory")?); let w = Wallet::load(Path::new(&arg(4, "tower wallet file")?))?;
            let (p2p, api) = parse_node(&a, 5)?; let once = a.get(6).map_or(false, |x| x == "once");
            let mut done: std::collections::HashSet<(String, u64, u8)> = Default::default();
            loop {
                for e in std::fs::read_dir(&dir)?.flatten() {
                    if e.path().extension().map_or(true, |x| x != "chan") { continue; }
                    let Ok(c) = Chan::load(&e.path()) else { continue };
                    for l in guard(&c, &w, p2p, &api, &mut done, None) { println!("{l}"); }
                }
                if once { break; }
                std::thread::sleep(std::time::Duration::from_secs(2));
            }
        }
        _ => bail!("usage: chan <open|join|show|pay|accept|commit|close-sign|close|dispute|settle|watch> ..."),
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    fn pair(oneway: bool) -> (Chan, Chan, Wallet, Wallet) {
        let (wa, wb) = (Wallet::from_secret(num_bigint::BigUint::from(11u32)), Wallet::from_secret(num_bigint::BigUint::from(22u32)));
        let mk = |role_a| Chan { chain: 3, id: [7; 32], role_a, a: wa.address(), b: wb.address(), key_a: mint::encode_point(wa.key.a), key_b: mint::encode_point(wb.key.a), cap: 1000, delay: 5, oneway,
                                 seq: 0, bal_a: 1000, locks: vec![], sigs: ChanSigs::NONE, pending: None, secrets: vec![], peer_addr: None, fid: None };
        (mk(true), mk(false), wa, wb)
    }
    fn scalar(n: u32) -> ([u8; 41], [u8; 40]) { let k = mint::Key::from_secret(num_bigint::BigUint::from(n)); (mint::encode_point(k.a), mint::s_bytes(&num_bigint::BigUint::from(n))) }
    #[test]
    fn a_side_that_missed_the_acknowledgement_catches_up_from_the_peers_signed_state_and_a_joint_close_is_signed_by_both() {
        let (mut a, mut b, wa, wb) = pair(false);
        // a proposes, b accepts, the acknowledgement is lost: a still waits at update 0, b is at update 1
        let p = a.pay(&wa, 300).unwrap(); let _lost = b.accept(&wb, &p).unwrap();
        assert!(a.pending.is_some() && a.seq == 0 && b.seq == 1);
        let blob = b.state_blob();
        a.adopt_state(&blob).unwrap();
        assert_eq!((a.seq, a.bal_a, a.pending.is_none()), (1, 700, true));
        assert_eq!(a.sigs, b.sigs);
        assert!(a.adopt_state(&blob).is_err(), "not newer any more");
        // a state with a bad signature, or one that was never signed by the other side, is refused
        let mut bad = Chan::parse(&b.to_text()).unwrap(); bad.seq = 2; bad.bal_a = 600;
        let mut a2 = Chan::parse(&a.to_text()).unwrap();
        assert!(a2.adopt_state(&bad.state_blob()).is_err());
        // both can pay on from the common state, and sign a joint close that the other side can check
        let p = a.pay(&wa, 100).unwrap(); let ack = b.accept(&wb, &p).unwrap(); a.commit(&ack).unwrap();
        let (ea, sa) = a.close_sig(&wa); let (eb, sb) = b.close_sig(&wb);
        assert!(b.close_sig_ok(b.bal_a, ea, &sa) && a.close_sig_ok(a.bal_a, eb, &sb));
        assert!(!b.close_sig_ok(b.bal_a - 1, ea, &sa), "a close signature is for one split only");
    }

    #[test]
    fn payments_go_both_ways_and_the_file_survives_a_save() {
        let (mut a, mut b, wa, wb) = pair(false);
        let p = a.pay(&wa, 300).unwrap(); let ack = b.accept(&wb, &p).unwrap(); a.commit(&ack).unwrap();
        assert_eq!((a.seq, a.bal_a, b.seq, b.bal_a), (1, 700, 1, 700));
        let p = b.pay(&wb, 100).unwrap(); let ack = a.accept(&wa, &p).unwrap(); b.commit(&ack).unwrap();
        assert_eq!((a.seq, a.bal_a, b.bal_a), (2, 800, 800));
        assert_eq!(Chan::parse(&a.to_text()).unwrap().sigs, a.sigs);
        for (k, e, s) in [(&a.key_a, a.sigs.ea, &a.sigs.sa), (&a.key_b, a.sigs.eb, &a.sigs.sb)] { assert!(a.check(k, 2, 800, &[], e, s)); }
        let mut a2 = Chan::parse(&a.to_text()).unwrap();
        assert!(a2.pay(&wa, 801).is_err());
        let p = a.pay(&wa, 50).unwrap();
        assert!(a.pay(&wa, 1).is_err(), "one proposal at a time");
        let mut b3 = Chan::parse(&b.to_text()).unwrap(); b3.seq += 5;
        assert!(b3.accept(&wb, &p).is_err(), "not the next update");
        let (_, mut b4, _, wb4) = pair(false); b4.seq = 2; b4.bal_a = 800; b4.key_a = mint::encode_point(Wallet::from_secret(num_bigint::BigUint::from(99u32)).key.a);
        assert!(b4.accept(&wb4, &p).is_err(), "a proposal signed by a different key");
    }
    #[test]
    fn a_point_lock_is_added_opened_or_given_back_and_nothing_else_is_accepted() {
        let (mut a, mut b, wa, wb) = pair(false);
        let (pt, t) = scalar(5);
        // a locks 400 for b
        let p = a.add_lock(&wa, 400, pt, 90).unwrap(); let ack = b.accept(&wb, &p).unwrap(); a.commit(&ack).unwrap();
        assert_eq!((a.bal_a, a.bal_b(), a.locks.len(), b.locks.len()), (600, 0, 1, 1));
        // b cannot open it with a wrong scalar, a cannot open its own lock for itself
        assert!(b.fulfil(&wb, 0, scalar(6).1).is_err());
        assert!(a.fulfil(&wa, 0, t).is_err());
        // b opens it: a learns the scalar, b is paid
        let p = b.fulfil(&wb, 0, t).unwrap(); let ack = a.accept(&wa, &p).unwrap(); b.commit(&ack).unwrap();
        assert_eq!((a.bal_a, a.bal_b(), a.locks.len(), b.locks.len()), (600, 400, 0, 0));
        assert_eq!(a.secrets, vec![(pt, t)], "the payer learns the scalar: the receipt");
        // a second lock, which b gives back
        let p = a.add_lock(&wa, 100, scalar(8).0, 95).unwrap(); let ack = b.accept(&wb, &p).unwrap(); a.commit(&ack).unwrap();
        let p = b.fail(&wb, 0).unwrap(); let ack = a.accept(&wa, &p).unwrap(); b.commit(&ack).unwrap();
        assert_eq!((a.bal_a, a.bal_b(), a.locks.len()), (600, 400, 0));
        // refused: a lock that pays the proposer, an opened lock paid to the wrong side, two changes at once
        let mut a2 = Chan::parse(&a.to_text()).unwrap(); let mut b2 = Chan::parse(&b.to_text()).unwrap();
        let p = a2.add_lock(&wa, 50, scalar(9).0, 99).unwrap();
        let mut bad = Prop::decode(&p).unwrap(); bad.bal_a += 10; bad.e = 0;
        assert!(b2.accept(&wb, &bad.encode()).is_err());
        assert!(b2.accept(&wb, &p).is_ok());
    }
    #[test]
    fn a_stream_is_signed_by_the_payer_alone_and_only_forward() {
        let (mut a, mut b, wa, _) = pair(true);
        let m1 = a.pay(&wa, 10).unwrap(); b.commit_stream(&m1).unwrap();
        let m2 = a.pay(&wa, 15).unwrap(); b.commit_stream(&m2).unwrap();
        assert_eq!((b.seq, b.bal_a), (25, 975));
        assert!(b.commit_stream(&m1).is_err(), "an older amount is not newer");
        assert!(a.pay(&wa, 2000).is_err());
        assert!(b.pay(&wa, 1).is_err(), "the receiver does not sign payments");
    }
    #[test]
    fn a_factory_members_channel_signs_with_the_factorys_message_and_not_a_plain_channels() {
        let (mut a, mut b, wa, wb) = pair(false);
        a.fid = Some(([9; 32], 2)); b.fid = Some(([9; 32], 2));
        let p = a.pay(&wa, 100).unwrap(); let ack = b.accept(&wb, &p).unwrap(); a.commit(&ack).unwrap();
        assert_eq!((a.seq, a.bal_a), (1, 900));
        // the signatures verify as a factory state of member 2 and as nothing else
        assert!(a.check(&a.key_a, 1, 900, &[], a.sigs.ea, &a.sigs.sa));
        let msg = fact_state_msg(3, &[9; 32], 2, 1, 900, 1000, &[]);
        assert!(mint::verify(mint::decode_point(&a.key_b).unwrap(), msg, a.sigs.eb, &num_bigint::BigUint::from_bytes_le(&a.sigs.sb)));
        let other = fact_state_msg(3, &[9; 32], 1, 1, 900, 1000, &[]);
        assert!(!mint::verify(mint::decode_point(&a.key_b).unwrap(), other, a.sigs.eb, &num_bigint::BigUint::from_bytes_le(&a.sigs.sb)), "not valid for another member");
        assert_eq!(Chan::parse(&a.to_text()).unwrap().fid, Some(([9; 32], 2)));
        // a plain channel's proposal is not accepted inside the factory
        let (mut pa, _, wpa, _) = pair(false);
        let p = pa.pay(&wpa, 10).unwrap();
        assert!(b.accept(&wb, &p).is_err());
    }
}
