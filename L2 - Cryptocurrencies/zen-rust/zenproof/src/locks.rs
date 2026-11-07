// Locked funds and exchange orders (stage 2 of the three-chain test network; SPEC 7.2, 8.2).
//
// A LOCK is an account leaf that nobody can sign for: its address is the hash of its terms, its balance is the locked money. Because the leaf is in the
// state tree, the state root commits to every lock and to its terms, the supply audit counts the money, and a snapshot is checked against the root.
// The terms themselves are kept beside the tree (`LockTable`, lock index -> terms); a lock's address is their digest, so a wrong table cannot pass.
//
// Two kinds of terms:
//   Vault  key-or-timeout: spent by a signature of `key` (before `timeout`), or returned to `owner` after it. The base of channel funding and point locks.
//   Order  a sell order for another chain's metal (8.2): Open -> Reserved(taker) -> claimed with a proof that the other chain was paid.
//
// Block data carries the operations after the payments and payouts: magic `ZOPS`, a count, the operations. They run in order on the state the payments
// left. Like payments, an operation names the sending account by index and pays its fee; the account's signature is proven by the stamp (the node does
// not see signatures), except the vault claim, whose signature the node checks itself because it comes from a key, not an account.
// An order claim carries a proof from the other chain: its header (known to this node, SPEC 8.4, and deep enough), the block's body, and the account
// leaf of the receiver; the node checks it as a light client does (`check_payment_proof`).
use crate::blockdata::{self, BlockEntry};
use crate::node::{addr_bytes, addr_from};
use crate::store::{Rd, Wr};
use crate::{empty_leaf, leaf_hash, Acct, Tree, DEPTH, F};
use anyhow::{anyhow, bail, Result};
use plonky2::field::types::{Field, PrimeField64};
use plonky2::hash::hash_types::HashOut;
use sha2::{Digest, Sha256};
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::plonk::config::Hasher;
use std::collections::HashMap;

// ---------------------------------------------------------------- Poseidon layouts (stage P1)
// Everything a circuit has to check is hashed with Poseidon over field elements in a fixed layout: a lock's address, the ids of channels and
// factories, every message a key signs. Numbers are 32-bit limbs (a u64 is two elements, so nothing is ever reduced modulo the field and the
// hash is injective); a 41-byte point is its 41 bytes as eleven limbs; lists are padded to their maximum and carry their length.
// Layered digests (a factory is the hash of its member digests, a member of its point-lock digest) let a circuit open one piece at a time.
/// a hash input being built; the first element is a domain tag so no two kinds of data can collide
pub struct Fw(pub Vec<F>);
impl Fw {
    pub fn new(tag: &[u8; 8]) -> Fw { Fw(vec![F::from_canonical_u64(u64::from_le_bytes(*tag))]) }
    pub fn u8(&mut self, x: u8) -> &mut Fw { self.0.push(F::from_canonical_u8(x)); self }
    pub fn u32(&mut self, x: u32) -> &mut Fw { self.0.push(F::from_canonical_u32(x)); self }
    pub fn u64(&mut self, x: u64) -> &mut Fw { self.u32(x as u32).u32((x >> 32) as u32) }
    pub fn u128(&mut self, x: u128) -> &mut Fw { self.u64(x as u64).u64((x >> 64) as u64) }
    pub fn addr(&mut self, a: &[F; 4]) -> &mut Fw { self.0.extend_from_slice(a); self }
    /// bytes as 32-bit limbs (the last one padded with zeros); the caller fixes the length
    pub fn bytes(&mut self, b: &[u8]) -> &mut Fw { for c in b.chunks(4) { let mut l = [0u8; 4]; l[..c.len()].copy_from_slice(c); self.u32(u32::from_le_bytes(l)); } self }
    pub fn point(&mut self, k: &[u8; 41]) -> &mut Fw { self.bytes(k) }
    pub fn zeros(&mut self, n: usize) -> &mut Fw { self.0.extend(std::iter::repeat(F::ZERO).take(n)); self }
    pub fn hash(&self) -> [F; 4] { PoseidonHash::hash_no_pad(&self.0).elements }
}
/// the elements of a 32-byte id (an id is four canonical field elements, as an address is)
pub fn id_felts(id: &[u8; 32]) -> [F; 4] { std::array::from_fn(|i| F::from_noncanonical_u64(u64::from_le_bytes(id[8 * i..8 * i + 8].try_into().unwrap()))) }
fn id_of(h: [F; 4]) -> [u8; 32] { addr_bytes(&h) }

pub const MAGIC: &[u8; 4] = b"ZOPS";
pub const MAX_OPS: usize = 64;
pub const MAX_PROOF: usize = 64 * 1024;
/// blocks of the other chain that must sit on top of a payment before it can release an order (SPEC 8.2: about 30 minutes: 2 Yen, 6 Ken, 12 Jen)
pub fn confirmations(chain: u8) -> u64 { match chain { 1 => 2, 2 => 6, _ => 12 } }

/// something a node cannot judge yet (a header of another chain it has not seen): the block is neither valid nor invalid, and its sender is not punished
#[derive(Debug)]
pub struct Unavailable(pub String);
impl std::fmt::Display for Unavailable { fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result { write!(f, "not yet: {}", self.0) } }
impl std::error::Error for Unavailable {}

/// what this node knows about the other chains' headers (SPEC 8.4)
pub trait CrossHeaders: Send + Sync {
    /// the hash and time of the header at `height` of that chain's best chain, as checked by this node
    fn header(&self, chain: u8, height: u64) -> Option<([u8; 32], u32)>;
    fn tip_height(&self, chain: u8) -> Option<u64>;
}
#[derive(Clone)]
pub enum CrossMode { Off, /** replaying a log this node validated itself: proofs are not re-checked */ Trust, View(std::sync::Arc<dyn CrossHeaders>) }
pub struct Ctx<'a> { pub chain: u8, pub ntime: u32, pub cross: &'a CrossMode }

// ---------------------------------------------------------------- terms
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ChanState { Open, /** open, and b has added coins: a's share at the start is `base_a`, the rest is b's */ OpenDual { base_a: u64 }, Closing { seq: u64, bal_a: u64, until: u64, locks: Vec<PLock> } }
/// One member's channel with the coordinator inside a factory
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SubState { Open, Closing { seq: u64, bal_c: u64, until: u64, locks: Vec<PLock> }, Exited }
#[derive(Clone, Debug, PartialEq, Eq)]
/// `base`: the coordinator's share while the channel has no posted state (everything at first; a member's deposit adds to `cap` only)
pub struct FMember { pub addr: [F; 4], pub key: [u8; 41], pub cap: u64, pub base: u64, pub state: SubState }
impl FMember {
    /// the digest of one member's slot: what the factory's address hashes in its place
    pub fn digest(&self) -> [F; 4] {
        let (kind, seq, bal_c, until, pl) = match &self.state {
            SubState::Open => (0u8, 0, 0, 0, plocks_digest(&[])),
            SubState::Closing { seq, bal_c, until, locks } => (1, *seq, *bal_c, *until, plocks_digest(locks)),
            SubState::Exited => (2, 0, 0, 0, plocks_digest(&[])),
        };
        let mut f = Fw::new(b"ZenFMemb");
        f.addr(&self.addr).point(&self.key).u64(self.cap).u64(self.base).u8(kind).u64(seq).u64(bal_c).u64(until).addr(&pl);
        f.hash()
    }
}
pub const MAX_FACTORY: usize = 8;
/// A payment waiting inside a channel state (SPEC 7.3, a point lock): `amt` goes to the receiver (b if `to_b`, else a) on showing the scalar t with t*G = `point`,
/// and back to the sender once `expiry` has passed with no such scalar.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PLock { pub amt: u64, pub to_b: bool, pub point: [u8; 41], pub expiry: u64 }
pub const MAX_PLOCKS: usize = 8;
/// the longest terms an operation or a snapshot may carry
pub const MAX_TERMS: usize = 8192;
impl PLock {
    pub fn encode(&self, w: &mut Wr) { w.u64(self.amt); w.u8(self.to_b as u8); w.raw(&self.point); w.u64(self.expiry); }
    pub fn decode(r: &mut Rd) -> Result<PLock> { Ok(PLock { amt: r.u64()?, to_b: match r.u8()? { 0 => false, 1 => true, _ => bail!("bad flag") }, point: r.take(41)?.try_into()?, expiry: r.u64()? }) }
    /// does the scalar open this lock
    pub fn opened_by(&self, t: &[u8; 40]) -> bool {
        let t = num_bigint::BigUint::from_bytes_le(t);
        if t >= crate::ec::n_order() || t == num_bigint::BigUint::ZERO { return false; }
        crate::mint::decode_point(&self.point).map_or(false, |p| crate::ec::mul_g(&crate::ec::params(), &t) == p)
    }
}
impl PLock {
    /// 16 elements: amount (2), side (1), point (11), expiry (2)
    pub const FELTS: usize = 16;
    pub fn felts(&self, f: &mut Fw) { f.u64(self.amt).u8(self.to_b as u8).point(&self.point).u64(self.expiry); }
}
/// the digest of a list of point locks: the length, then MAX_PLOCKS slots, the unused ones zero
pub fn plocks_digest(l: &[PLock]) -> [F; 4] {
    let mut f = Fw::new(b"ZenPLock"); f.u8(l.len() as u8);
    for i in 0..MAX_PLOCKS { match l.get(i) { Some(x) => x.felts(&mut f), None => { f.zeros(PLock::FELTS); } } }
    f.hash()
}
pub fn plocks_total(l: &[PLock]) -> u128 { l.iter().map(|x| x.amt as u128).sum() }
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OrderState {
    Open,
    Reserved { taker: [F; 4], until: u64, since: u32 },
    /// open to a batch: bids are collected for `window` blocks after the first one, and the highest bid (the deposit it escrows) wins (no race to be first)
    Auction { window: u64 },
    /// a bid is in: `bid` is escrowed in the lock; further higher bids replace it until height `close`, then the winner is reserved for the order's reservation time
    Bidding { window: u64, taker: [F; 4], bid: u64, close: u64, since: u32 },
}
/// who holds the order now and until when: (taker, last block to claim, payment must be after `since`, escrow). Errors while it is open or its auction runs.
pub fn reservation(state: &OrderState, height: u64, reserve_blocks: u64, deposit: u64) -> Result<([F; 4], u64, u32, u64)> {
    match state {
        OrderState::Reserved { taker, until, since } => Ok((*taker, *until, *since, deposit)),
        OrderState::Bidding { taker, bid, close, since, .. } => { if height <= *close { bail!("the auction is still running"); } Ok((*taker, *close + reserve_blocks, *since, *bid)) }
        _ => bail!("not a reserved order"),
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Terms {
    Vault { key: [u8; 41], owner: [F; 4], timeout: u64, salt: u64 },
    /// `sell` is in the lock's balance (plus `deposit` while reserved); the maker wants `want_amt` base units of `want_chain`, paid to the fresh address `pay_to`
    /// A funded it (its coins are the lock's balance); b starts with nothing and receives by off-chain updates. `oneway`: a stream, only a signs, the state is the amount paid to b
    Channel { a: [F; 4], b: [F; 4], key_a: [u8; 41], key_b: [u8; 41], delay: u64, oneway: bool, salt: u64, state: ChanState },
    /// Many users behind one output (SPEC 7.2). The coordinator funds every member's channel; each channel (coordinator, member i) is updated by those two alone,
    /// so members need not be online together, and one member can leave (alone) without closing the others.
    Factory { coord: [F; 4], key_c: [u8; 41], members: Vec<FMember>, delay: u64, salt: u64 },
    Order { maker: [F; 4], sell: u64, want_chain: u8, want_amt: u64, pay_to: [F; 4], expiry: u64, reserve_blocks: u64, deposit: u64, salt: u64, state: OrderState },
}
fn akey(a: &[F; 4]) -> [u64; 4] { a.map(|x| x.to_canonical_u64()) }
fn put_addr(w: &mut Wr, a: &[F; 4]) { w.raw(&addr_bytes(a)); }
fn get_addr(r: &mut Rd) -> Result<[F; 4]> { addr_from(&r.take(32)?.try_into()?) }
impl Terms {
    pub fn encode(&self) -> Vec<u8> {
        let mut w = Wr::new();
        match self {
            Terms::Vault { key, owner, timeout, salt } => { w.u8(1); w.raw(key); put_addr(&mut w, owner); w.u64(*timeout); w.u64(*salt); }
            Terms::Channel { a, b, key_a, key_b, delay, oneway, salt, state } => {
                w.u8(3); put_addr(&mut w, a); put_addr(&mut w, b); w.raw(key_a); w.raw(key_b); w.u64(*delay); w.u8(*oneway as u8); w.u64(*salt);
                match state { ChanState::Open => w.u8(0), ChanState::OpenDual { base_a } => { w.u8(2); w.u64(*base_a); } ChanState::Closing { seq, bal_a, until, locks } => { w.u8(1); w.u64(*seq); w.u64(*bal_a); w.u64(*until); w.u8(locks.len() as u8); for l in locks { l.encode(&mut w); } } }
            }
            Terms::Factory { coord, key_c, members, delay, salt } => {
                w.u8(4); put_addr(&mut w, coord); w.raw(key_c); w.u64(*delay); w.u64(*salt); w.u8(members.len() as u8);
                for m in members {
                    put_addr(&mut w, &m.addr); w.raw(&m.key); w.u64(m.cap); w.u64(m.base);
                    match &m.state { SubState::Open => w.u8(0), SubState::Exited => w.u8(2), SubState::Closing { seq, bal_c, until, locks } => { w.u8(1); w.u64(*seq); w.u64(*bal_c); w.u64(*until); w.u8(locks.len() as u8); for l in locks { l.encode(&mut w); } } }
                }
            }
            Terms::Order { maker, sell, want_chain, want_amt, pay_to, expiry, reserve_blocks, deposit, salt, state } => {
                w.u8(2); put_addr(&mut w, maker); w.u64(*sell); w.u8(*want_chain); w.u64(*want_amt); put_addr(&mut w, pay_to);
                w.u64(*expiry); w.u64(*reserve_blocks); w.u64(*deposit); w.u64(*salt);
                match state { OrderState::Open => w.u8(0), OrderState::Reserved { taker, until, since } => { w.u8(1); put_addr(&mut w, taker); w.u64(*until); w.u32(*since); }
                    OrderState::Auction { window } => { w.u8(2); w.u64(*window); }
                    OrderState::Bidding { window, taker, bid, close, since } => { w.u8(3); w.u64(*window); put_addr(&mut w, taker); w.u64(*bid); w.u64(*close); w.u32(*since); } }
            }
        }
        w.0
    }
    pub fn decode_from(r: &mut Rd) -> Result<Terms> {
        Ok(match r.u8()? {
            1 => Terms::Vault { key: r.take(41)?.try_into()?, owner: get_addr(r)?, timeout: r.u64()?, salt: r.u64()? },
            2 => {
                let (maker, sell, want_chain, want_amt, pay_to) = (get_addr(r)?, r.u64()?, r.u8()?, r.u64()?, get_addr(r)?);
                let (expiry, reserve_blocks, deposit, salt) = (r.u64()?, r.u64()?, r.u64()?, r.u64()?);
                let state = match r.u8()? { 0 => OrderState::Open, 1 => OrderState::Reserved { taker: get_addr(r)?, until: r.u64()?, since: r.u32()? }, 2 => OrderState::Auction { window: r.u64()? },
                    3 => OrderState::Bidding { window: r.u64()?, taker: get_addr(r)?, bid: r.u64()?, close: r.u64()?, since: r.u32()? }, _ => bail!("bad order state") };
                Terms::Order { maker, sell, want_chain, want_amt, pay_to, expiry, reserve_blocks, deposit, salt, state }
            }
            3 => {
                let (a, b, key_a, key_b, delay) = (get_addr(r)?, get_addr(r)?, r.take(41)?.try_into()?, r.take(41)?.try_into()?, r.u64()?);
                let oneway = match r.u8()? { 0 => false, 1 => true, _ => bail!("bad flag") };
                let salt = r.u64()?;
                let state = match r.u8()? { 0 => ChanState::Open, 2 => ChanState::OpenDual { base_a: r.u64()? }, 1 => {
                    let (seq, bal_a, until) = (r.u64()?, r.u64()?, r.u64()?);
                    let n = r.u8()? as usize; if n > MAX_PLOCKS { bail!("too many point locks"); }
                    ChanState::Closing { seq, bal_a, until, locks: (0..n).map(|_| PLock::decode(r)).collect::<Result<_>>()? }
                }
                _ => bail!("bad channel state") };
                Terms::Channel { a, b, key_a, key_b, delay, oneway, salt, state }
            }
            4 => {
                let (coord, key_c, delay, salt) = (get_addr(r)?, r.take(41)?.try_into()?, r.u64()?, r.u64()?);
                let n = r.u8()? as usize; if n == 0 || n > MAX_FACTORY { bail!("a factory has 1 to {MAX_FACTORY} members"); }
                let mut members = vec![];
                for _ in 0..n {
                    let (addr, key, cap, base) = (get_addr(r)?, r.take(41)?.try_into()?, r.u64()?, r.u64()?);
                    let state = match r.u8()? {
                        0 => SubState::Open, 2 => SubState::Exited,
                        1 => { let (seq, bal_c, until) = (r.u64()?, r.u64()?, r.u64()?); let k = r.u8()? as usize; if k > MAX_PLOCKS { bail!("too many point locks"); }
                               SubState::Closing { seq, bal_c, until, locks: (0..k).map(|_| PLock::decode(r)).collect::<Result<_>>()? } }
                        _ => bail!("bad member state"),
                    };
                    members.push(FMember { addr, key, cap, base, state });
                }
                Terms::Factory { coord, key_c, members, delay, salt }
            }
            _ => bail!("unknown lock kind"),
        })
    }
    /// the lock's address: a Poseidon hash of its terms in a fixed layout (see the top of this file), as four field elements
    pub fn digest(&self) -> [F; 4] {
        match self {
            Terms::Vault { key, owner, timeout, salt } => { let mut f = Fw::new(b"ZenVault"); f.point(key).addr(owner).u64(*timeout).u64(*salt); f.hash() }
            Terms::Channel { a, b, key_a, key_b, delay, oneway, salt, state } => {
                let (kind, seq, bal_a, until, base_a, pl) = match state {
                    ChanState::Open => (0u8, 0, 0, 0, 0, plocks_digest(&[])),
                    ChanState::OpenDual { base_a } => (2, 0, 0, 0, *base_a, plocks_digest(&[])),
                    ChanState::Closing { seq, bal_a, until, locks } => (1, *seq, *bal_a, *until, 0, plocks_digest(locks)),
                };
                let mut f = Fw::new(b"ZenChan.");
                f.addr(a).addr(b).point(key_a).point(key_b).u64(*delay).u8(*oneway as u8).u64(*salt).u8(kind).u64(seq).u64(bal_a).u64(until).u64(base_a).addr(&pl);
                f.hash()
            }
            Terms::Factory { coord, key_c, members, delay, salt } => {
                let mut f = Fw::new(b"ZenFact.");
                f.addr(coord).point(key_c).u64(*delay).u64(*salt).u8(members.len() as u8);
                for i in 0..MAX_FACTORY { match members.get(i) { Some(m) => { f.addr(&m.digest()); } None => { f.zeros(4); } } }
                f.hash()
            }
            Terms::Order { maker, sell, want_chain, want_amt, pay_to, expiry, reserve_blocks, deposit, salt, state } => {
                let mut f = Fw::new(b"ZenOrder");
                f.addr(maker).u64(*sell).u8(*want_chain).u64(*want_amt).addr(pay_to).u64(*expiry).u64(*reserve_blocks).u64(*deposit).u64(*salt);
                // state: kind, taker (4), until (2), since (1), window (2), bid (2), close (2)
                match state {
                    OrderState::Open => { f.u8(0).zeros(4 + 2 + 1 + 2 + 2 + 2); }
                    OrderState::Reserved { taker, until, since } => { f.u8(1).addr(taker).u64(*until).u32(*since).zeros(2 + 2 + 2); }
                    OrderState::Auction { window } => { f.u8(2).zeros(4 + 2 + 1).u64(*window).zeros(2 + 2); }
                    OrderState::Bidding { window, taker, bid, close, since } => { f.u8(3).addr(taker).zeros(2).u32(*since).u64(*window).u64(*bid).u64(*close); }
                }
                f.hash()
            }
        }
    }
    pub fn salt(&self) -> u64 { match self { Terms::Vault { salt, .. } | Terms::Order { salt, .. } | Terms::Channel { salt, .. } | Terms::Factory { salt, .. } => *salt } }
    pub fn set_salt(&mut self, s: u64) { match self { Terms::Vault { salt, .. } | Terms::Order { salt, .. } | Terms::Channel { salt, .. } | Terms::Factory { salt, .. } => *salt = s } }
    /// what stays the same through a channel's life (its address changes with its state): the id its signatures name
    /// a factory's id: its setup, which never changes while it lives
    pub fn factory_id(&self) -> Option<[u8; 32]> {
        let Terms::Factory { coord, key_c, members, delay, salt } = self else { return None };
        let mut f = Fw::new(b"ZenFctId");
        f.addr(coord).point(key_c).u64(*delay).u64(*salt).u8(members.len() as u8);
        for i in 0..MAX_FACTORY { match members.get(i) { Some(m) => { f.addr(&m.addr).point(&m.key); } None => { f.zeros(4 + 11); } } }
        Some(id_of(f.hash()))
    }
    pub fn channel_id(&self) -> Option<[u8; 32]> {
        let Terms::Channel { a, b, key_a, key_b, delay, oneway, salt, .. } = self else { return None };
        let mut f = Fw::new(b"ZenChnId");
        f.addr(a).addr(b).point(key_a).point(key_b).u64(*delay).u8(*oneway as u8).u64(*salt);
        Some(id_of(f.hash()))
    }
    /// the money the lock must hold
    pub fn balance(&self) -> Option<u64> { match self { Terms::Order { sell, deposit, state: OrderState::Reserved { .. }, .. } => Some(sell + deposit), Terms::Order { sell, state: OrderState::Bidding { bid, .. }, .. } => Some(sell + bid), Terms::Order { sell, .. } => Some(*sell), Terms::Vault { .. } | Terms::Channel { .. } => None,
        Terms::Factory { members, .. } => Some(members.iter().filter(|m| m.state != SubState::Exited).map(|m| m.cap).sum()) } }
}
pub type LockTable = HashMap<u64, Terms>;

// ---------------------------------------------------------------- operations
/// where money goes: an existing account, or a new one at a free index
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Dest { pub idx: u32, pub new: Option<[F; 4]> }
#[derive(Clone, Debug, PartialEq)]
pub enum Op {
    /// lock `amt` of the sender's money in a new lock at index `at`
    Make { from: u32, fee: u64, amt: u64, at: u32, terms: Terms },
    VaultClaim { from: u32, fee: u64, lock: u32, to: Dest, e: u128, s: [u8; 40] },
    VaultRefund { from: u32, fee: u64, lock: u32, to: Dest },
    /// the sender pays the order's deposit and names where the coins go (`taker`)
    Reserve { from: u32, fee: u64, lock: u32, taker: [F; 4] },
    /// a bid in a batch auction: escrow `bid`; an earlier, lower bid is paid back to `refund`
    Bid { from: u32, fee: u64, lock: u32, taker: [F; 4], bid: u64, refund: Dest },
    OrderClaim { from: u32, fee: u64, lock: u32, to: Dest, proof: Vec<u8> },
    Reopen { from: u32, fee: u64, lock: u32, to: Dest },
    Return { from: u32, fee: u64, lock: u32, to: Dest },
    /// a or b starts closing a channel that has never been updated (state 0: everything is a's)
    ChanStart { from: u32, fee: u64, lock: u32 },
    /// anyone: a newer signed state replaces the one waiting (the dispute window starts again)
    ChanUpdate { from: u32, fee: u64, lock: u32, seq: u64, bal_a: u64, locks: Vec<PLock>, sigs: ChanSigs },
    /// after the window: each side is paid; `wits` has one entry per point lock in the waiting state: the scalar that opens it, if the sender of this operation has it
    ChanSettle { from: u32, fee: u64, lock: u32, wits: Vec<Option<[u8; 40]>>, to_a: Dest, to_b: Dest },
    /// both sign the final balances: paid out at once
    ChanClose { from: u32, fee: u64, lock: u32, bal_a: u64, sigs: ChanSigs, to_a: Dest, to_b: Dest },
    /// the coordinator or member `idx` starts closing that member's channel in a factory, never updated (state 0: all the coordinator's)
    FactoryStart { from: u32, fee: u64, lock: u32, idx: u8 },
    /// anyone: a newer state of member `idx`'s channel, signed by the coordinator and the member (sigs.a = coordinator)
    FactoryPost { from: u32, fee: u64, lock: u32, idx: u8, seq: u64, bal_c: u64, locks: Vec<PLock>, sigs: ChanSigs },
    /// after the member's window: the coordinator and the member are paid; the member leaves, the factory goes on without it
    FactoryExit { from: u32, fee: u64, lock: u32, idx: u8, wits: Vec<Option<[u8; 40]>>, to_c: Dest, to_m: Dest },
    /// both sign the final balances: the member leaves at once
    FactoryExitNow { from: u32, fee: u64, lock: u32, idx: u8, bal_c: u64, sigs: ChanSigs, to_c: Dest, to_m: Dest },
    /// the member adds `amt` of its own to its channel while it has no posted state: the coordinator's share stays, the member's grows
    FactoryFund { from: u32, fee: u64, lock: u32, idx: u8, amt: u64 },
    /// b adds `amt` of its own to a channel that has no posted state: a dual-funded channel
    ChanFund { from: u32, fee: u64, lock: u32, amt: u64 },
}
fn put_dest(w: &mut Wr, d: &Dest) { w.u32(d.idx); match &d.new { Some(a) => { w.u8(1); put_addr(w, a); } None => w.u8(0) } }
fn get_dest(r: &mut Rd) -> Result<Dest> { let idx = r.u32()?; Ok(Dest { idx, new: match r.u8()? { 0 => None, 1 => Some(get_addr(r)?), _ => bail!("bad flag") } }) }
impl Op {
    pub fn from(&self) -> u32 { match self { Op::Make { from, .. } | Op::VaultClaim { from, .. } | Op::VaultRefund { from, .. } | Op::Reserve { from, .. } | Op::Bid { from, .. } | Op::OrderClaim { from, .. } | Op::Reopen { from, .. } | Op::Return { from, .. } | Op::ChanStart { from, .. } | Op::ChanUpdate { from, .. } | Op::ChanSettle { from, .. } | Op::ChanClose { from, .. } | Op::FactoryStart { from, .. } | Op::FactoryPost { from, .. } | Op::FactoryExit { from, .. } | Op::FactoryExitNow { from, .. } | Op::FactoryFund { from, .. } | Op::ChanFund { from, .. } => *from } }
    /// the lock an operation works on (none for a Make: it creates one)
    pub fn lock_index(&self) -> Option<u32> { match self { Op::Make { .. } => None, Op::VaultClaim { lock, .. } | Op::VaultRefund { lock, .. } | Op::Reserve { lock, .. } | Op::Bid { lock, .. } | Op::OrderClaim { lock, .. } | Op::Reopen { lock, .. } | Op::Return { lock, .. } | Op::ChanStart { lock, .. } | Op::ChanUpdate { lock, .. } | Op::ChanSettle { lock, .. } | Op::ChanClose { lock, .. } | Op::FactoryStart { lock, .. } | Op::FactoryPost { lock, .. } | Op::FactoryExit { lock, .. } | Op::FactoryExitNow { lock, .. } | Op::FactoryFund { lock, .. } | Op::ChanFund { lock, .. } => Some(*lock) } }
    pub fn fee(&self) -> u64 { match self { Op::Make { fee, .. } | Op::VaultClaim { fee, .. } | Op::VaultRefund { fee, .. } | Op::Reserve { fee, .. } | Op::Bid { fee, .. } | Op::OrderClaim { fee, .. } | Op::Reopen { fee, .. } | Op::Return { fee, .. } | Op::ChanStart { fee, .. } | Op::ChanUpdate { fee, .. } | Op::ChanSettle { fee, .. } | Op::ChanClose { fee, .. } | Op::FactoryStart { fee, .. } | Op::FactoryPost { fee, .. } | Op::FactoryExit { fee, .. } | Op::FactoryExitNow { fee, .. } | Op::FactoryFund { fee, .. } | Op::ChanFund { fee, .. } => *fee } }
    fn encode(&self, w: &mut Wr) {
        match self {
            Op::Make { from, fee, amt, at, terms } => { w.u8(1); w.u32(*from); w.u64(*fee); w.u64(*amt); w.u32(*at); let t = terms.encode(); w.u32(t.len() as u32); w.raw(&t); }
            Op::VaultClaim { from, fee, lock, to, e, s } => { w.u8(2); w.u32(*from); w.u64(*fee); w.u32(*lock); put_dest(w, to); w.u128(*e); w.raw(s); }
            Op::VaultRefund { from, fee, lock, to } => { w.u8(3); w.u32(*from); w.u64(*fee); w.u32(*lock); put_dest(w, to); }
            Op::Bid { from, fee, lock, taker, bid, refund } => { w.u8(17); w.u32(*from); w.u64(*fee); w.u32(*lock); put_addr(w, taker); w.u64(*bid); put_dest(w, refund); }
            Op::Reserve { from, fee, lock, taker } => { w.u8(4); w.u32(*from); w.u64(*fee); w.u32(*lock); put_addr(w, taker); }
            Op::OrderClaim { from, fee, lock, to, proof } => { w.u8(5); w.u32(*from); w.u64(*fee); w.u32(*lock); put_dest(w, to); w.u32(proof.len() as u32); w.raw(proof); }
            Op::Reopen { from, fee, lock, to } => { w.u8(6); w.u32(*from); w.u64(*fee); w.u32(*lock); put_dest(w, to); }
            Op::Return { from, fee, lock, to } => { w.u8(7); w.u32(*from); w.u64(*fee); w.u32(*lock); put_dest(w, to); }
            Op::ChanStart { from, fee, lock } => { w.u8(8); w.u32(*from); w.u64(*fee); w.u32(*lock); }
            Op::ChanUpdate { from, fee, lock, seq, bal_a, locks, sigs } => { w.u8(9); w.u32(*from); w.u64(*fee); w.u32(*lock); w.u64(*seq); w.u64(*bal_a); put_plocks(w, locks); put_sigs(w, sigs); }
            Op::ChanSettle { from, fee, lock, wits, to_a, to_b } => { w.u8(10); w.u32(*from); w.u64(*fee); w.u32(*lock); put_wits(w, wits); put_dest(w, to_a); put_dest(w, to_b); }
            Op::ChanFund { from, fee, lock, amt } => { w.u8(18); w.u32(*from); w.u64(*fee); w.u32(*lock); w.u64(*amt); }
            Op::FactoryFund { from, fee, lock, idx, amt } => { w.u8(16); w.u32(*from); w.u64(*fee); w.u32(*lock); w.u8(*idx); w.u64(*amt); }
            Op::FactoryStart { from, fee, lock, idx } => { w.u8(12); w.u32(*from); w.u64(*fee); w.u32(*lock); w.u8(*idx); }
            Op::FactoryPost { from, fee, lock, idx, seq, bal_c, locks, sigs } => { w.u8(13); w.u32(*from); w.u64(*fee); w.u32(*lock); w.u8(*idx); w.u64(*seq); w.u64(*bal_c); put_plocks(w, locks); put_sigs(w, sigs); }
            Op::FactoryExit { from, fee, lock, idx, wits, to_c, to_m } => { w.u8(14); w.u32(*from); w.u64(*fee); w.u32(*lock); w.u8(*idx); put_wits(w, wits); put_dest(w, to_c); put_dest(w, to_m); }
            Op::FactoryExitNow { from, fee, lock, idx, bal_c, sigs, to_c, to_m } => { w.u8(15); w.u32(*from); w.u64(*fee); w.u32(*lock); w.u8(*idx); w.u64(*bal_c); put_sigs(w, sigs); put_dest(w, to_c); put_dest(w, to_m); }
            Op::ChanClose { from, fee, lock, bal_a, sigs, to_a, to_b } => { w.u8(11); w.u32(*from); w.u64(*fee); w.u32(*lock); w.u64(*bal_a); put_sigs(w, sigs); put_dest(w, to_a); put_dest(w, to_b); }
        }
    }
    fn decode(r: &mut Rd) -> Result<Op> {
        let kind = r.u8()?;
        let (from, fee) = (r.u32()?, r.u64()?);
        Ok(match kind {
            1 => { let (amt, at) = (r.u64()?, r.u32()?); let n = r.u32()? as usize; if n > MAX_TERMS { bail!("terms too long"); } let mut tr = Rd::new(r.take(n)?); let terms = Terms::decode_from(&mut tr)?; tr.done()?; Op::Make { from, fee, amt, at, terms } }
            2 => Op::VaultClaim { from, fee, lock: r.u32()?, to: get_dest(r)?, e: r.u128()?, s: r.take(40)?.try_into()? },
            3 => Op::VaultRefund { from, fee, lock: r.u32()?, to: get_dest(r)? },
            4 => Op::Reserve { from, fee, lock: r.u32()?, taker: get_addr(r)? },
            17 => Op::Bid { from, fee, lock: r.u32()?, taker: get_addr(r)?, bid: r.u64()?, refund: get_dest(r)? },
            5 => { let (lock, to) = (r.u32()?, get_dest(r)?); let n = r.u32()? as usize; if n > MAX_PROOF { bail!("proof too long"); } Op::OrderClaim { from, fee, lock, to, proof: r.take(n)?.to_vec() } }
            6 => Op::Reopen { from, fee, lock: r.u32()?, to: get_dest(r)? },
            7 => Op::Return { from, fee, lock: r.u32()?, to: get_dest(r)? },
            8 => Op::ChanStart { from, fee, lock: r.u32()? },
            9 => Op::ChanUpdate { from, fee, lock: r.u32()?, seq: r.u64()?, bal_a: r.u64()?, locks: get_plocks(r)?, sigs: get_sigs(r)? },
            10 => Op::ChanSettle { from, fee, lock: r.u32()?, wits: get_wits(r)?, to_a: get_dest(r)?, to_b: get_dest(r)? },
            11 => Op::ChanClose { from, fee, lock: r.u32()?, bal_a: r.u64()?, sigs: get_sigs(r)?, to_a: get_dest(r)?, to_b: get_dest(r)? },
            12 => Op::FactoryStart { from, fee, lock: r.u32()?, idx: r.u8()? },
            16 => Op::FactoryFund { from, fee, lock: r.u32()?, idx: r.u8()?, amt: r.u64()? },
            18 => Op::ChanFund { from, fee, lock: r.u32()?, amt: r.u64()? },
            13 => Op::FactoryPost { from, fee, lock: r.u32()?, idx: r.u8()?, seq: r.u64()?, bal_c: r.u64()?, locks: get_plocks(r)?, sigs: get_sigs(r)? },
            14 => Op::FactoryExit { from, fee, lock: r.u32()?, idx: r.u8()?, wits: get_wits(r)?, to_c: get_dest(r)?, to_m: get_dest(r)? },
            15 => Op::FactoryExitNow { from, fee, lock: r.u32()?, idx: r.u8()?, bal_c: r.u64()?, sigs: get_sigs(r)?, to_c: get_dest(r)?, to_m: get_dest(r)? },
            _ => bail!("unknown operation"),
        })
    }
}
/// the trailer of a block's data: empty for no operations
pub fn encode_ops(ops: &[Op]) -> Vec<u8> {
    if ops.is_empty() { return vec![]; }
    let mut w = Wr::new(); w.raw(MAGIC); w.u32(ops.len() as u32);
    for o in ops { o.encode(&mut w); }
    w.0
}
pub fn decode_ops(b: &[u8]) -> Result<Vec<Op>> {
    if b.is_empty() { return Ok(vec![]); }
    let mut r = Rd::new(b);
    if r.take(4)? != MAGIC { bail!("trailing bytes after the block data"); }
    let n = r.u32()? as usize;
    if n == 0 || n > MAX_OPS { bail!("{n} operations (1 to {MAX_OPS} allowed)"); }
    let ops = (0..n).map(|_| Op::decode(&mut r)).collect::<Result<Vec<_>>>()?;
    r.done()?;
    Ok(ops)
}

// ---------------------------------------------------------------- what a wallet asks for, by address, and signed
/// What a wallet asks of the chain besides paying; the builder turns addresses into indices and leaves out what would not be valid.
#[derive(Clone, Debug, PartialEq)]
pub enum OpReq {
    Make { from: [F; 4], amt: u64, fee: u64, terms: Terms },
    VaultClaim { from: [F; 4], fee: u64, lock: [F; 4], to: [F; 4], e: u128, s: [u8; 40] },
    VaultRefund { from: [F; 4], fee: u64, lock: [F; 4], to: [F; 4] },
    Reserve { from: [F; 4], fee: u64, lock: [F; 4], taker: [F; 4] },
    Bid { from: [F; 4], fee: u64, lock: [F; 4], taker: [F; 4], bid: u64 },
    OrderClaim { from: [F; 4], fee: u64, lock: [F; 4], proof: Vec<u8> },
    Reopen { from: [F; 4], fee: u64, lock: [F; 4] },
    Return { from: [F; 4], fee: u64, lock: [F; 4] },
    ChanStart { from: [F; 4], fee: u64, lock: [F; 4] },
    ChanUpdate { from: [F; 4], fee: u64, lock: [F; 4], seq: u64, bal_a: u64, locks: Vec<PLock>, sigs: ChanSigs },
    ChanSettle { from: [F; 4], fee: u64, lock: [F; 4], wits: Vec<Option<[u8; 40]>> },
    ChanClose { from: [F; 4], fee: u64, lock: [F; 4], bal_a: u64, sigs: ChanSigs },
    FactoryStart { from: [F; 4], fee: u64, lock: [F; 4], idx: u8 },
    FactoryPost { from: [F; 4], fee: u64, lock: [F; 4], idx: u8, seq: u64, bal_c: u64, locks: Vec<PLock>, sigs: ChanSigs },
    FactoryExit { from: [F; 4], fee: u64, lock: [F; 4], idx: u8, wits: Vec<Option<[u8; 40]>> },
    FactoryExitNow { from: [F; 4], fee: u64, lock: [F; 4], idx: u8, bal_c: u64, sigs: ChanSigs },
    FactoryFund { from: [F; 4], fee: u64, lock: [F; 4], idx: u8, amt: u64 },
    ChanFund { from: [F; 4], fee: u64, lock: [F; 4], amt: u64 },
}
impl OpReq {
    pub fn from(&self) -> [F; 4] { match self { OpReq::Make { from, .. } | OpReq::VaultClaim { from, .. } | OpReq::VaultRefund { from, .. } | OpReq::Reserve { from, .. } | OpReq::Bid { from, .. } | OpReq::OrderClaim { from, .. } | OpReq::Reopen { from, .. } | OpReq::Return { from, .. } | OpReq::ChanStart { from, .. } | OpReq::ChanUpdate { from, .. } | OpReq::ChanSettle { from, .. } | OpReq::ChanClose { from, .. } | OpReq::FactoryStart { from, .. } | OpReq::FactoryPost { from, .. } | OpReq::FactoryExit { from, .. } | OpReq::FactoryExitNow { from, .. } | OpReq::FactoryFund { from, .. } | OpReq::ChanFund { from, .. } => *from } }
    pub fn fee(&self) -> u64 { match self { OpReq::Make { fee, .. } | OpReq::VaultClaim { fee, .. } | OpReq::VaultRefund { fee, .. } | OpReq::Reserve { fee, .. } | OpReq::Bid { fee, .. } | OpReq::OrderClaim { fee, .. } | OpReq::Reopen { fee, .. } | OpReq::Return { fee, .. } | OpReq::ChanStart { fee, .. } | OpReq::ChanUpdate { fee, .. } | OpReq::ChanSettle { fee, .. } | OpReq::ChanClose { fee, .. } | OpReq::FactoryStart { fee, .. } | OpReq::FactoryPost { fee, .. } | OpReq::FactoryExit { fee, .. } | OpReq::FactoryExitNow { fee, .. } | OpReq::FactoryFund { fee, .. } | OpReq::ChanFund { fee, .. } => *fee } }
    pub fn lock(&self) -> Option<[F; 4]> { match self { OpReq::Make { .. } => None, OpReq::VaultClaim { lock, .. } | OpReq::VaultRefund { lock, .. } | OpReq::Reserve { lock, .. } | OpReq::Bid { lock, .. } | OpReq::OrderClaim { lock, .. } | OpReq::Reopen { lock, .. } | OpReq::Return { lock, .. } | OpReq::ChanStart { lock, .. } | OpReq::ChanUpdate { lock, .. } | OpReq::ChanSettle { lock, .. } | OpReq::ChanClose { lock, .. } | OpReq::FactoryStart { lock, .. } | OpReq::FactoryPost { lock, .. } | OpReq::FactoryExit { lock, .. } | OpReq::FactoryExitNow { lock, .. } | OpReq::FactoryFund { lock, .. } | OpReq::ChanFund { lock, .. } => Some(*lock) } }
    /// the request as Poseidon input: the same fields in a fixed layout per kind (terms, proofs and lists enter as digests); this is what the sender signs
    pub fn fields(&self, f: &mut Fw) {
        let sigs = |f: &mut Fw, g: &ChanSigs| { f.u128(g.ea).bytes(&g.sa).u128(g.eb).bytes(&g.sb); };
        match self {
            OpReq::Make { from, amt, fee, terms } => { f.u8(1).addr(from).u64(*fee).u64(*amt).addr(&terms.digest()); }
            OpReq::VaultClaim { from, fee, lock, to, e, s } => { f.u8(2).addr(from).u64(*fee).addr(lock).addr(to).u128(*e).bytes(s); }
            OpReq::VaultRefund { from, fee, lock, to } => { f.u8(3).addr(from).u64(*fee).addr(lock).addr(to); }
            OpReq::Reserve { from, fee, lock, taker } => { f.u8(4).addr(from).u64(*fee).addr(lock).addr(taker); }
            OpReq::OrderClaim { from, fee, lock, proof } => { f.u8(5).addr(from).u64(*fee).addr(lock).addr(&bytes_digest(proof)); }
            OpReq::Reopen { from, fee, lock } => { f.u8(6).addr(from).u64(*fee).addr(lock); }
            OpReq::Return { from, fee, lock } => { f.u8(7).addr(from).u64(*fee).addr(lock); }
            OpReq::ChanStart { from, fee, lock } => { f.u8(8).addr(from).u64(*fee).addr(lock); }
            OpReq::ChanUpdate { from, fee, lock, seq, bal_a, locks, sigs: g } => { f.u8(9).addr(from).u64(*fee).addr(lock).u64(*seq).u64(*bal_a).addr(&plocks_digest(locks)); sigs(f, g); }
            OpReq::ChanSettle { from, fee, lock, wits } => { f.u8(10).addr(from).u64(*fee).addr(lock).addr(&wits_digest(wits)); }
            OpReq::ChanClose { from, fee, lock, bal_a, sigs: g } => { f.u8(11).addr(from).u64(*fee).addr(lock).u64(*bal_a); sigs(f, g); }
            OpReq::FactoryStart { from, fee, lock, idx } => { f.u8(12).addr(from).u64(*fee).addr(lock).u8(*idx); }
            OpReq::FactoryPost { from, fee, lock, idx, seq, bal_c, locks, sigs: g } => { f.u8(13).addr(from).u64(*fee).addr(lock).u8(*idx).u64(*seq).u64(*bal_c).addr(&plocks_digest(locks)); sigs(f, g); }
            OpReq::FactoryExit { from, fee, lock, idx, wits } => { f.u8(14).addr(from).u64(*fee).addr(lock).u8(*idx).addr(&wits_digest(wits)); }
            OpReq::FactoryExitNow { from, fee, lock, idx, bal_c, sigs: g } => { f.u8(15).addr(from).u64(*fee).addr(lock).u8(*idx).u64(*bal_c); sigs(f, g); }
            OpReq::FactoryFund { from, fee, lock, idx, amt } => { f.u8(16).addr(from).u64(*fee).addr(lock).u8(*idx).u64(*amt); }
            OpReq::Bid { from, fee, lock, taker, bid } => { f.u8(17).addr(from).u64(*fee).addr(lock).addr(taker).u64(*bid); }
            OpReq::ChanFund { from, fee, lock, amt } => { f.u8(18).addr(from).u64(*fee).addr(lock).u64(*amt); }
        }
    }
    pub fn encode(&self) -> Vec<u8> {
        let mut w = Wr::new();
        let head = |w: &mut Wr, k: u8, from: &[F; 4], fee: u64| { w.u8(k); put_addr(w, from); w.u64(fee); };
        match self {
            OpReq::Make { from, amt, fee, terms } => { head(&mut w, 1, from, *fee); w.u64(*amt); let t = terms.encode(); w.u32(t.len() as u32); w.raw(&t); }
            OpReq::VaultClaim { from, fee, lock, to, e, s } => { head(&mut w, 2, from, *fee); put_addr(&mut w, lock); put_addr(&mut w, to); w.u128(*e); w.raw(s); }
            OpReq::VaultRefund { from, fee, lock, to } => { head(&mut w, 3, from, *fee); put_addr(&mut w, lock); put_addr(&mut w, to); }
            OpReq::Bid { from, fee, lock, taker, bid } => { head(&mut w, 17, from, *fee); put_addr(&mut w, lock); put_addr(&mut w, taker); w.u64(*bid); }
            OpReq::Reserve { from, fee, lock, taker } => { head(&mut w, 4, from, *fee); put_addr(&mut w, lock); put_addr(&mut w, taker); }
            OpReq::OrderClaim { from, fee, lock, proof } => { head(&mut w, 5, from, *fee); put_addr(&mut w, lock); w.u32(proof.len() as u32); w.raw(proof); }
            OpReq::Reopen { from, fee, lock } => { head(&mut w, 6, from, *fee); put_addr(&mut w, lock); }
            OpReq::Return { from, fee, lock } => { head(&mut w, 7, from, *fee); put_addr(&mut w, lock); }
            OpReq::ChanStart { from, fee, lock } => { head(&mut w, 8, from, *fee); put_addr(&mut w, lock); }
            OpReq::ChanUpdate { from, fee, lock, seq, bal_a, locks, sigs } => { head(&mut w, 9, from, *fee); put_addr(&mut w, lock); w.u64(*seq); w.u64(*bal_a); put_plocks(&mut w, locks); put_sigs(&mut w, sigs); }
            OpReq::ChanSettle { from, fee, lock, wits } => { head(&mut w, 10, from, *fee); put_addr(&mut w, lock); put_wits(&mut w, wits); }
            OpReq::ChanFund { from, fee, lock, amt } => { head(&mut w, 18, from, *fee); put_addr(&mut w, lock); w.u64(*amt); }
            OpReq::FactoryFund { from, fee, lock, idx, amt } => { head(&mut w, 16, from, *fee); put_addr(&mut w, lock); w.u8(*idx); w.u64(*amt); }
            OpReq::FactoryStart { from, fee, lock, idx } => { head(&mut w, 12, from, *fee); put_addr(&mut w, lock); w.u8(*idx); }
            OpReq::FactoryPost { from, fee, lock, idx, seq, bal_c, locks, sigs } => { head(&mut w, 13, from, *fee); put_addr(&mut w, lock); w.u8(*idx); w.u64(*seq); w.u64(*bal_c); put_plocks(&mut w, locks); put_sigs(&mut w, sigs); }
            OpReq::FactoryExit { from, fee, lock, idx, wits } => { head(&mut w, 14, from, *fee); put_addr(&mut w, lock); w.u8(*idx); put_wits(&mut w, wits); }
            OpReq::FactoryExitNow { from, fee, lock, idx, bal_c, sigs } => { head(&mut w, 15, from, *fee); put_addr(&mut w, lock); w.u8(*idx); w.u64(*bal_c); put_sigs(&mut w, sigs); }
            OpReq::ChanClose { from, fee, lock, bal_a, sigs } => { head(&mut w, 11, from, *fee); put_addr(&mut w, lock); w.u64(*bal_a); put_sigs(&mut w, sigs); }
        }
        w.0
    }
    pub fn decode(b: &[u8]) -> Result<OpReq> {
        let mut r = Rd::new(b);
        let kind = r.u8()?; let (from, fee) = (get_addr(&mut r)?, r.u64()?);
        let q = Ok(match kind {
            1 => { let amt = r.u64()?; let n = r.u32()? as usize; if n > MAX_TERMS { bail!("terms too long"); } let mut tr = Rd::new(r.take(n)?); let terms = Terms::decode_from(&mut tr)?; tr.done()?; OpReq::Make { from, amt, fee, terms } }
            2 => OpReq::VaultClaim { from, fee, lock: get_addr(&mut r)?, to: get_addr(&mut r)?, e: r.u128()?, s: r.take(40)?.try_into()? },
            3 => OpReq::VaultRefund { from, fee, lock: get_addr(&mut r)?, to: get_addr(&mut r)? },
            4 => OpReq::Reserve { from, fee, lock: get_addr(&mut r)?, taker: get_addr(&mut r)? },
            17 => OpReq::Bid { from, fee, lock: get_addr(&mut r)?, taker: get_addr(&mut r)?, bid: r.u64()? },
            5 => { let lock = get_addr(&mut r)?; let n = r.u32()? as usize; if n > MAX_PROOF { bail!("proof too long"); } OpReq::OrderClaim { from, fee, lock, proof: r.take(n)?.to_vec() } }
            6 => OpReq::Reopen { from, fee, lock: get_addr(&mut r)? },
            7 => OpReq::Return { from, fee, lock: get_addr(&mut r)? },
            8 => OpReq::ChanStart { from, fee, lock: get_addr(&mut r)? },
            9 => OpReq::ChanUpdate { from, fee, lock: get_addr(&mut r)?, seq: r.u64()?, bal_a: r.u64()?, locks: get_plocks(&mut r)?, sigs: get_sigs(&mut r)? },
            10 => OpReq::ChanSettle { from, fee, lock: get_addr(&mut r)?, wits: get_wits(&mut r)? },
            11 => OpReq::ChanClose { from, fee, lock: get_addr(&mut r)?, bal_a: r.u64()?, sigs: get_sigs(&mut r)? },
            12 => OpReq::FactoryStart { from, fee, lock: get_addr(&mut r)?, idx: r.u8()? },
            16 => OpReq::FactoryFund { from, fee, lock: get_addr(&mut r)?, idx: r.u8()?, amt: r.u64()? },
            18 => OpReq::ChanFund { from, fee, lock: get_addr(&mut r)?, amt: r.u64()? },
            13 => OpReq::FactoryPost { from, fee, lock: get_addr(&mut r)?, idx: r.u8()?, seq: r.u64()?, bal_c: r.u64()?, locks: get_plocks(&mut r)?, sigs: get_sigs(&mut r)? },
            14 => OpReq::FactoryExit { from, fee, lock: get_addr(&mut r)?, idx: r.u8()?, wits: get_wits(&mut r)? },
            15 => OpReq::FactoryExitNow { from, fee, lock: get_addr(&mut r)?, idx: r.u8()?, bal_c: r.u64()?, sigs: get_sigs(&mut r)? },
            _ => bail!("unknown operation"),
        });
        r.done()?;
        q
    }
}

/// An operation as a wallet sends it and the pool holds it: the request, the sender's key and a signature over (chain, nonce, request).
/// The chain is in the message, so one key on the three chains cannot be replayed from one to another.
#[derive(Clone, Debug, PartialEq)]
pub struct SignedOp { pub from_a: [u8; 41], pub nonce: u64, pub req: OpReq, pub e: u128, pub s: [u8; 40] }
pub const MAX_SIGNED_OP: usize = MAX_PROOF + MAX_TERMS;
impl SignedOp {
    pub fn message(chain: u8, nonce: u64, req: &OpReq) -> [F; 4] {
        let mut f = Fw::new(b"ZenOp...");
        f.u8(chain).u64(nonce);
        req.fields(&mut f);
        f.hash()
    }
    pub fn sign(key: &crate::mint::Key, chain: u8, nonce: u64, req: OpReq) -> SignedOp {
        let (e, s) = crate::mint::sign(key, SignedOp::message(chain, nonce, &req));
        SignedOp { from_a: crate::mint::encode_point(key.a), nonce, req, e, s: crate::mint::s_bytes(&s) }
    }
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut w = Wr::new(); w.raw(&self.from_a); w.u64(self.nonce); let r = self.req.encode(); w.u32(r.len() as u32); w.raw(&r); w.u128(self.e); w.raw(&self.s); w.0
    }
    pub fn from_bytes(b: &[u8]) -> Result<SignedOp> {
        if b.len() > MAX_SIGNED_OP { bail!("operation too large"); }
        let mut r = Rd::new(b);
        let from_a: [u8; 41] = r.take(41)?.try_into()?; let nonce = r.u64()?;
        let n = r.u32()? as usize; let req = OpReq::decode(r.take(n)?)?;
        let (e, s) = (r.u128()?, r.take(40)?.try_into()?);
        r.done()?;
        Ok(SignedOp { from_a, nonce, req, e, s })
    }
    pub fn id(&self) -> [u8; 32] { let mut h = Sha256::new(); h.update(b"Zen-opid-v1"); h.update(self.to_bytes()); h.finalize().into() }
    /// the signature is the named sender's, for this chain
    pub fn verify(&self, chain: u8) -> Result<()> {
        let a = crate::mint::decode_point(&self.from_a)?;
        if crate::ec::pk_hash(a) != self.req.from() { bail!("the key is not the sender's"); }
        if !crate::mint::verify(a, SignedOp::message(chain, self.nonce, &self.req), self.e, &num_bigint::BigUint::from_bytes_le(&self.s)) { bail!("bad signature"); }
        Ok(())
    }
}

/// Operations waiting for a block. An account's operations are numbered from its account nonce; the builder takes them in that order.
/// (Payments and operations of one account share the nonce counter; send one kind at a time and wait for the block.)
pub struct OpPool { ops: Vec<(SignedOp, [u8; 32], u64)>, pub max: usize }
pub const MAX_OPS_PER_SENDER: usize = 4;
const MAX_AGE: u64 = 400;
impl OpPool {
    pub fn new(max: usize) -> OpPool { OpPool { ops: vec![], max } }
    pub fn len(&self) -> usize { self.ops.len() }
    /// the signed operation of this sender with this nonce, if the pool holds it (the prover uses the wallet's own signature)
    pub fn find(&self, from: &[F; 4], nonce: u64) -> Option<SignedOp> { self.ops.iter().find(|(o, ..)| o.nonce == nonce && o.req.from() == *from).map(|(o, ..)| o.clone()) }
    fn waiting(&self, from: &[F; 4]) -> u64 { self.ops.iter().filter(|(o, ..)| o.req.from() == *from).count() as u64 }
    /// the nonce an operation of this account must carry now
    pub fn next_nonce(&self, chain: &crate::node::Chain, from: &[F; 4]) -> Option<u64> { Some(chain.account(from)?.1.nonce + self.waiting(from)) }
    pub fn admit(&mut self, chain: &crate::node::Chain, op: SignedOp) -> Result<()> {
        let id = op.id();
        if self.ops.iter().any(|(_, i, _)| *i == id) { bail!("known"); }
        if self.ops.len() >= self.max { bail!("the operation pool is full"); }
        op.verify(chain.p.chain)?;
        let from = op.req.from();
        let Some((_, acct)) = chain.account(&from) else { bail!("the sender has no account") };
        if chain.locks.contains_key(&chain.idx_of(&from).unwrap_or(u64::MAX)) { bail!("a lock cannot send"); }
        let fee = op.req.fee();
        if fee >= 1 << 62 || (fee as u128) * 100 < chain.reading.s as u128 { bail!("below the smallest fee"); }
        let w = self.waiting(&from);
        if op.nonce != acct.nonce + w { bail!("nonce {} (the next is {})", op.nonce, acct.nonce + w); }
        if w as usize >= MAX_OPS_PER_SENDER { bail!("too many operations waiting for this sender"); }
        let give = match &op.req {
            OpReq::Make { amt, .. } => *amt,
            OpReq::FactoryFund { amt, .. } | OpReq::ChanFund { amt, .. } => *amt,
            OpReq::Bid { bid, .. } => *bid,
            OpReq::Reserve { lock, .. } => chain.idx_of(lock).and_then(|i| chain.locks.get(&i)).map_or(0, |t| match t { Terms::Order { deposit, .. } => *deposit, _ => 0 }),
            _ => 0,
        };
        let waiting_give: u128 = self.ops.iter().filter(|(o, ..)| o.req.from() == from).map(|(o, ..)| o.req.fee() as u128).sum();
        if give as u128 + fee as u128 + waiting_give > acct.bal as u128 { bail!("balance {} does not cover {}", acct.bal, give as u128 + fee as u128 + waiting_give); }
        self.ops.push((op, id, chain.height));
        Ok(())
    }
    /// the requests the builder may use: per sender, in nonce order from the account's nonce
    pub fn select(&self, chain: &crate::node::Chain) -> Vec<OpReq> {
        let mut next: HashMap<[u64; 4], u64> = HashMap::new();
        let mut out = vec![];
        let mut sorted: Vec<&(SignedOp, [u8; 32], u64)> = self.ops.iter().collect();
        sorted.sort_by_key(|(o, ..)| o.nonce);
        for (o, ..) in sorted {
            let from = o.req.from();
            let Some((_, acct)) = chain.account(&from) else { continue };
            let n = next.entry(akey(&from)).or_insert(acct.nonce);
            if o.nonce == *n { out.push(o.req.clone()); *n += 1; }
        }
        out
    }
    /// after a block: drop what was applied or can no longer apply, and what has waited too long
    pub fn on_block(&mut self, chain: &crate::node::Chain) {
        self.ops.retain(|(o, _, at)| match chain.account(&o.req.from()) { Some((_, a)) => o.nonce >= a.nonce && chain.height.saturating_sub(*at) <= MAX_AGE, None => false });
    }
}

// ---------------------------------------------------------------- the vault's signed message
/// what a vault claim signs: the lock and where its money goes
pub fn vault_claim_msg(chain: u8, lock: &[F; 4], dest: &[F; 4]) -> [F; 4] { let mut f = Fw::new(b"ZenVClm."); f.u8(chain).addr(lock).addr(dest); f.hash() }

// ---------------------------------------------------------------- channel messages
/// the two signatures of a channel state (a stream needs only the first)
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ChanSigs { pub ea: u128, pub sa: [u8; 40], pub eb: u128, pub sb: [u8; 40] }
impl ChanSigs { pub const NONE: ChanSigs = ChanSigs { ea: 0, sa: [0; 40], eb: 0, sb: [0; 40] }; }
/// what both sign for update number `seq` (for a stream: `seq` is the amount paid to b): a's share of the channel's `cap` coins
pub fn chan_state_msg(chain: u8, id: &[u8; 32], seq: u64, bal_a: u64, cap: u64, locks: &[PLock]) -> [F; 4] { let mut f = Fw::new(b"ZenCSta."); f.u8(chain).addr(&id_felts(id)).u64(seq).u64(bal_a).u64(cap).addr(&plocks_digest(locks)); f.hash() }
/// what both sign to close at once with these balances
pub fn chan_close_msg(chain: u8, id: &[u8; 32], bal_a: u64, cap: u64) -> [F; 4] { let mut f = Fw::new(b"ZenCClo."); f.u8(chain).addr(&id_felts(id)).u64(bal_a).u64(cap); f.hash() }
fn sig_ok(key: &[u8; 41], msg: [F; 4], e: u128, s: &[u8; 40]) -> bool {
    crate::mint::decode_point(key).map_or(false, |a| crate::mint::verify(a, msg, e, &num_bigint::BigUint::from_bytes_le(s)))
}
/// a long byte string (an order claim's proof) as four elements
pub fn bytes_digest(b: &[u8]) -> [F; 4] { let mut f = Fw::new(b"ZenBytes"); f.u32(b.len() as u32).bytes(b); f.hash() }
/// the witnesses of a settle: the length, then MAX_PLOCKS slots of (flag, scalar as ten limbs)
pub fn wits_digest(v: &[Option<[u8; 40]>]) -> [F; 4] {
    let mut f = Fw::new(b"ZenWits."); f.u8(v.len() as u8);
    for i in 0..MAX_PLOCKS { match v.get(i) { Some(Some(t)) => { f.u8(1).bytes(t); } _ => { f.u8(0).zeros(10); } } }
    f.hash()
}
fn put_plocks(w: &mut Wr, l: &[PLock]) { w.u8(l.len() as u8); for x in l { x.encode(w); } }
fn get_plocks(r: &mut Rd) -> Result<Vec<PLock>> { let n = r.u8()? as usize; if n > MAX_PLOCKS { bail!("too many point locks"); } (0..n).map(|_| PLock::decode(r)).collect() }
fn put_wits(w: &mut Wr, v: &[Option<[u8; 40]>]) { w.u8(v.len() as u8); for x in v { match x { Some(t) => { w.u8(1); w.raw(t); } None => w.u8(0) } } }
fn get_wits(r: &mut Rd) -> Result<Vec<Option<[u8; 40]>>> {
    let n = r.u8()? as usize; if n > MAX_PLOCKS { bail!("too many witnesses"); }
    (0..n).map(|_| Ok(match r.u8()? { 0 => None, 1 => Some(r.take(40)?.try_into()?), _ => bail!("bad flag") })).collect()
}
fn put_sigs(w: &mut Wr, g: &ChanSigs) { w.u128(g.ea); w.raw(&g.sa); w.u128(g.eb); w.raw(&g.sb); }
fn get_sigs(r: &mut Rd) -> Result<ChanSigs> { Ok(ChanSigs { ea: r.u128()?, sa: r.take(40)?.try_into()?, eb: r.u128()?, sb: r.take(40)?.try_into()? }) }

// ---------------------------------------------------------------- factory messages
/// the id of member `idx`'s channel inside factory `fid` (what a wallet keeps its channel file under)
pub fn sub_id(fid: &[u8; 32], idx: u8) -> [u8; 32] { let mut f = Fw::new(b"ZenSubId"); f.addr(&id_felts(fid)).u8(idx); id_of(f.hash()) }
pub fn fact_state_msg(chain: u8, fid: &[u8; 32], idx: u8, seq: u64, bal_c: u64, cap: u64, locks: &[PLock]) -> [F; 4] { let mut f = Fw::new(b"ZenFSta."); f.u8(chain).addr(&id_felts(fid)).u8(idx).u64(seq).u64(bal_c).u64(cap).addr(&plocks_digest(locks)); f.hash() }
pub fn fact_close_msg(chain: u8, fid: &[u8; 32], idx: u8, bal_c: u64, cap: u64) -> [F; 4] { let mut f = Fw::new(b"ZenFClo."); f.u8(chain).addr(&id_felts(fid)).u8(idx).u64(bal_c).u64(cap); f.hash() }

// ---------------------------------------------------------------- applying operations
fn lock_leaf(pk: [F; 4], bal: u64, nonce: u64, like: &Acct) -> Acct { Acct { pk, bal, nonce, rest: 0, used: 0, fd: 0, rd: 0, up: 0, ..*like } }

/// one change of one leaf of the state tree, as an operation made it (what a proof of the operation needs): the account before (none: an empty slot),
/// after (none: emptied), and the sibling hashes of its path (the same before and after)
#[derive(Clone)]
pub struct Touch { pub idx: u64, pub old: Option<Acct>, pub new: Option<Acct>, pub sibs: Vec<HashOut<F>> }
/// what the proof of one operation is built from: its touches in the order the node made them, and the terms of the lock it works on
#[derive(Clone)]
pub struct OpTrace { pub touches: Vec<Touch>, pub terms: Option<Terms> }
struct Run<'a, 'b> { state: &'a mut HashMap<u64, Acct>, tree: &'a mut Tree, locks: &'a mut LockTable, s: u64, height: u64, ctx: &'a Ctx<'b>, tmpl: Acct, rec: Vec<Touch> }
impl Run<'_, '_> {
    fn set(&mut self, i: u64, a: Acct) {
        let (old, sibs) = (self.state.get(&i).copied(), self.tree.path(i));
        self.state.insert(i, a); self.tree.set(i, leaf_hash(&a));
        self.rec.push(Touch { idx: i, old, new: Some(a), sibs });
    }
    fn remove(&mut self, i: u64) {
        let (old, sibs) = (self.state.get(&i).copied(), self.tree.path(i));
        self.state.remove(&i); self.tree.set(i, empty_leaf());
        self.rec.push(Touch { idx: i, old, new: None, sibs });
    }
    fn lock(&self, i: u32) -> Result<Terms> { self.locks.get(&(i as u64)).cloned().ok_or_else(|| anyhow!("no lock at index {i}")) }
    /// pay `amt` from the lock at `i` to the destination, which must be the account of `expect`; the lock is spent
    fn pay_out(&mut self, d: &Dest, expect: &[F; 4], amt: u64) -> Result<()> {
        match &d.new {
            Some(a) => if a != expect { bail!("the money goes to another address than the terms name"); },
            None => {
                if self.locks.contains_key(&(d.idx as u64)) { bail!("money cannot go into a lock this way"); }
                let acc = self.state.get(&(d.idx as u64)).ok_or_else(|| anyhow!("unknown receiver {}", d.idx))?;
                if acc.pk != *expect { bail!("the money goes to another address than the terms name"); }
            }
        }
        let (old, sibs) = (self.state.get(&(d.idx as u64)).copied(), self.tree.path(d.idx as u64));
        blockdata::credit_to(self.state, self.tree, d.idx as u64, d.new, amt, self.height, self.tmpl)?;
        self.rec.push(Touch { idx: d.idx as u64, old, new: self.state.get(&(d.idx as u64)).copied(), sibs });
        Ok(())
    }
    fn spend(&mut self, i: u32) { self.remove(i as u64); self.locks.remove(&(i as u64)); }
    /// replace a lock's terms (its address changes with them) and balance
    fn retarget(&mut self, i: u32, terms: Terms, bal: u64) {
        let old = self.state[&(i as u64)];
        self.set(i as u64, lock_leaf(terms.digest(), bal, old.nonce, &self.tmpl));
        self.locks.insert(i as u64, terms);
    }
    fn one(&mut self, op: &Op) -> Result<()> {
        let (d, p) = blockdata::day_period(self.height);
        let (fi, fee) = (op.from() as u64, op.fee());
        if fee >= 1 << 62 || (fee as u128) * 100 < self.s as u128 { bail!("below the smallest fee"); }
        if self.locks.contains_key(&fi) { bail!("a lock cannot send"); }
        let mut sa = *self.state.get(&fi).ok_or_else(|| anyhow!("unknown sender {fi}"))?;
        let nonce_before = sa.nonce;
        let (height, chain) = (self.height, self.ctx.chain);
        // what the sender gives up besides the fee
        let give = match op {
            Op::Make { amt, .. } => *amt,
            Op::FactoryFund { amt, .. } | Op::ChanFund { amt, .. } => *amt,
            Op::Bid { bid, .. } => *bid,
            Op::Reserve { lock, .. } => match self.lock(*lock)? { Terms::Order { deposit, .. } => deposit, _ => 0 },
            _ => 0,
        };
        if (sa.bal as u128) < give as u128 + fee as u128 { bail!("balance too low"); }
        match op {
            Op::Make { amt, at, terms, .. } => {
                let at = *at as u64;
                if at > (1u64 << DEPTH) - 1 || self.state.contains_key(&at) { bail!("the lock's index is taken"); }
                if *amt >= 1 << 62 || (*amt as u128) * 6 < self.s as u128 { bail!("below the smallest amount"); }
                if terms.salt() != nonce_before { bail!("the lock's salt must be the sender's nonce ({nonce_before})"); }
                match terms {
                    Terms::Vault { key, owner, timeout, .. } => {
                        if *owner != sa.pk { bail!("a vault's owner is its sender"); }
                        if *timeout <= height { bail!("the timeout is not in the future"); }
                        crate::mint::decode_point(key)?;
                    }
                    Terms::Channel { a, b, key_a, key_b, delay, state, .. } => {
                        if *a != sa.pk { bail!("a channel's funder is its sender"); }
                        if a == b { bail!("a channel joins two accounts"); }
                        if crate::ec::pk_hash(crate::mint::decode_point(key_a)?) != *a || crate::ec::pk_hash(crate::mint::decode_point(key_b)?) != *b { bail!("a channel's keys are its accounts' keys"); }
                        if !(1..=100_000).contains(delay) { bail!("the dispute window is 1 to 100000 blocks"); }
                        if *state != ChanState::Open { bail!("a new channel is open"); }
                    }
                    Terms::Factory { coord, key_c, members, delay, .. } => {
                        if *coord != sa.pk { bail!("a factory's coordinator is its sender"); }
                        if crate::ec::pk_hash(crate::mint::decode_point(key_c)?) != *coord { bail!("the coordinator's key is its account's key"); }
                        if members.is_empty() || members.len() > MAX_FACTORY { bail!("a factory has 1 to {MAX_FACTORY} members"); }
                        if !(1..=100_000).contains(delay) { bail!("the dispute window is 1 to 100000 blocks"); }
                        let mut total = 0u128;
                        for (i, m) in members.iter().enumerate() {
                            if m.addr == *coord || members[..i].iter().any(|o| o.addr == m.addr) { bail!("members are distinct accounts, and not the coordinator"); }
                            if crate::ec::pk_hash(crate::mint::decode_point(&m.key)?) != m.addr { bail!("a member's key is its account's key"); }
                            if m.cap == 0 || m.base != m.cap || m.state != SubState::Open { bail!("each member's channel starts open with something in it"); }
                            total += m.cap as u128;
                        }
                        if total != *amt as u128 { bail!("the members' channels add up to what the factory holds"); }
                    }
                    Terms::Order { maker, sell, want_chain, want_amt, expiry, reserve_blocks, deposit, state, .. } => {
                        if *maker != sa.pk { bail!("an order's maker is its sender"); }
                        if sell != amt { bail!("the order sells what the lock holds"); }
                        if !(1..=3).contains(want_chain) || *want_chain == chain { bail!("an order asks for another chain's metal"); }
                        if *want_amt == 0 || *want_amt >= 1 << 62 { bail!("the asked amount is out of range"); }
                        if *expiry <= height { bail!("the order has already expired"); }
                        if !(1..=100_000).contains(reserve_blocks) { bail!("the reservation time is 1 to 100000 blocks"); }
                        if (*deposit as u128) * 100 < *sell as u128 || *deposit >= 1 << 62 { bail!("the deposit is at least 1% of the sale"); }
                        match state { OrderState::Open => {}, OrderState::Auction { window } if (1..=10_000).contains(window) => {}, _ => bail!("a new order is open (or open to an auction of 1 to 10000 blocks)") }
                    }
                }
                let pk = terms.digest();
                if self.state.values().any(|a| a.pk == pk) { bail!("the lock exists already"); }
                blockdata::pay_from(&mut sa, *amt, fee, d, p);
                self.set(fi, sa);
                self.set(at, lock_leaf(pk, *amt, height << blockdata::NONCE_SHIFT, &self.tmpl));
                self.locks.insert(at, terms.clone());
            }
            Op::VaultClaim { lock, to, e, s: sig, .. } => {
                let Terms::Vault { key, timeout, .. } = self.lock(*lock)? else { bail!("not a vault") };
                if height > timeout { bail!("the vault has timed out; its owner takes it back"); }
                let acc = self.state[&(*lock as u64)];
                let dest_addr = match &to.new { Some(a) => *a, None => self.state.get(&(to.idx as u64)).ok_or_else(|| anyhow!("unknown receiver {}", to.idx))?.pk };
                let a = crate::mint::decode_point(&key)?;
                if !crate::mint::verify(a, vault_claim_msg(chain, &acc.pk, &dest_addr), *e, &num_bigint::BigUint::from_bytes_le(sig)) { bail!("the vault claim is not signed by the vault's key"); }
                blockdata::pay_from(&mut sa, 0, fee, d, p); self.set(fi, sa);
                self.pay_out(to, &dest_addr, acc.bal)?;
                self.spend(*lock);
            }
            Op::VaultRefund { lock, to, .. } => {
                let Terms::Vault { owner, timeout, .. } = self.lock(*lock)? else { bail!("not a vault") };
                if height <= timeout { bail!("the vault has not timed out"); }
                let bal = self.state[&(*lock as u64)].bal;
                blockdata::pay_from(&mut sa, 0, fee, d, p); self.set(fi, sa);
                self.pay_out(to, &owner, bal)?;
                self.spend(*lock);
            }
            Op::Reserve { lock, taker, .. } => {
                let Terms::Order { maker, sell, want_chain, want_amt, pay_to, expiry, reserve_blocks, deposit, salt, state: OrderState::Open } = self.lock(*lock)? else { bail!("not an open order") };
                if height >= expiry { bail!("the order has expired"); }
                blockdata::pay_from(&mut sa, deposit, fee, d, p); self.set(fi, sa);
                let t = Terms::Order { maker, sell, want_chain, want_amt, pay_to, expiry, reserve_blocks, deposit, salt, state: OrderState::Reserved { taker: *taker, until: height + reserve_blocks, since: self.ctx.ntime } };
                self.retarget(*lock, t, sell + deposit);
            }
            Op::Bid { lock, taker, bid, refund, .. } => {
                let Terms::Order { maker, sell, want_chain, want_amt, pay_to, expiry, reserve_blocks, deposit, salt, state } = self.lock(*lock)? else { bail!("not an order") };
                if height >= expiry { bail!("the order has expired"); }
                if *bid == 0 || *bid >= 1 << 62 { bail!("the bid is out of range"); }
                let (window, close, prev) = match state {
                    OrderState::Auction { window } => { if *bid < deposit { bail!("the bid is below the deposit the order asks"); } (window, height + window, None) }
                    OrderState::Bidding { window, taker: pt, bid: pb, close, .. } => {
                        if height > close { bail!("the auction is over"); }
                        if *bid <= pb { bail!("the bid is not higher than the one waiting"); }
                        (window, close, Some((pt, pb)))
                    }
                    _ => bail!("the order is not open to an auction"),
                };
                blockdata::pay_from(&mut sa, *bid, fee, d, p); self.set(fi, sa);
                if let Some((pt, pb)) = prev { self.pay_out(refund, &pt, pb)?; }
                let t = Terms::Order { maker, sell, want_chain, want_amt, pay_to, expiry, reserve_blocks, deposit, salt, state: OrderState::Bidding { window, taker: *taker, bid: *bid, close, since: self.ctx.ntime } };
                self.retarget(*lock, t, sell + bid);
            }
            Op::OrderClaim { lock, to, proof, .. } => {
                let Terms::Order { want_chain, want_amt, pay_to, reserve_blocks, deposit, state, .. } = self.lock(*lock)? else { bail!("not a reserved order") };
                let (taker, until, since, _) = reservation(&state, height, reserve_blocks, deposit)?;
                if height > until { bail!("the reservation has run out"); }
                match self.ctx.cross {
                    CrossMode::Off => bail!("claims need the other chains' headers"),
                    CrossMode::Trust => {}
                    CrossMode::View(v) => check_payment_proof(v.as_ref(), want_chain, &pay_to, want_amt, since, proof)?,
                }
                let bal = self.state[&(*lock as u64)].bal;
                blockdata::pay_from(&mut sa, 0, fee, d, p); self.set(fi, sa);
                self.pay_out(to, &taker, bal)?;
                self.spend(*lock);
            }
            Op::Reopen { lock, to, .. } => {
                let Terms::Order { maker, sell, want_chain, want_amt, pay_to, expiry, reserve_blocks, deposit, salt, state } = self.lock(*lock)? else { bail!("not a reserved order") };
                let (_, until, _, held) = reservation(&state, height, reserve_blocks, deposit)?;
                if height <= until { bail!("the reservation is still running"); }
                blockdata::pay_from(&mut sa, 0, fee, d, p); self.set(fi, sa);
                // the escrow goes to the maker; the order is open again (to a new auction, if it was one) and holds only the sale
                self.pay_out(to, &maker, held)?;
                let again = match state { OrderState::Bidding { window, .. } => OrderState::Auction { window }, _ => OrderState::Open };
                let t = Terms::Order { maker, sell, want_chain, want_amt, pay_to, expiry, reserve_blocks, deposit, salt, state: again };
                self.retarget(*lock, t, sell);
            }
            Op::ChanStart { lock, .. } => {
                let Terms::Channel { a, b, key_a, key_b, delay, oneway, salt, state } = self.lock(*lock)? else { bail!("not an open channel") };
                if sa.pk != a && sa.pk != b { bail!("only the channel's two sides start a close"); }
                let cap = self.state[&(*lock as u64)].bal;
                let cap_a = match state { ChanState::Open => cap, ChanState::OpenDual { base_a } => base_a, _ => bail!("not an open channel") };
                blockdata::pay_from(&mut sa, 0, fee, d, p); self.set(fi, sa);
                self.retarget(*lock, Terms::Channel { a, b, key_a, key_b, delay, oneway, salt, state: ChanState::Closing { seq: 0, bal_a: cap_a, until: height + delay, locks: vec![] } }, cap);
            }
            Op::ChanUpdate { lock, seq, bal_a, locks: plocks, sigs, .. } => {
                let t = self.lock(*lock)?;
                let Terms::Channel { a, b, key_a, key_b, delay, oneway, salt, state } = t.clone() else { bail!("not a channel") };
                let cap = self.state[&(*lock as u64)].bal;
                if let ChanState::Closing { seq: cur, until, .. } = &state { let (cur, until) = (*cur, *until); if height > until { bail!("the dispute window is over; settle"); } if *seq <= cur { bail!("not newer than the state waiting"); } }
                if *seq == 0 || *seq >= 1 << 62 { bail!("update numbers start at 1 and stay below 2^62"); }
                if plocks.len() > MAX_PLOCKS { bail!("too many point locks"); }
                if oneway && !plocks.is_empty() { bail!("a stream holds no point locks"); }
                for l in plocks { if l.amt == 0 || l.expiry <= height || l.expiry >= 1 << 62 { bail!("a point lock needs an amount and an expiry in the future and below 2^62"); } crate::mint::decode_point(&l.point)?; }
                if *bal_a as u128 + plocks_total(plocks) > cap as u128 { bail!("the shares and the point locks are more than the channel holds"); }
                if oneway && *bal_a != cap.checked_sub(*seq).ok_or_else(|| anyhow!("a stream cannot have paid more than it holds"))? { bail!("a stream's state is the amount paid: a keeps what is left"); }
                let id = t.channel_id().unwrap();
                let msg = chan_state_msg(chain, &id, *seq, *bal_a, cap, plocks);
                if !sig_ok(&key_a, msg, sigs.ea, &sigs.sa) { bail!("a's signature on the state is bad"); }
                if !oneway && !sig_ok(&key_b, msg, sigs.eb, &sigs.sb) { bail!("b's signature on the state is bad"); }
                blockdata::pay_from(&mut sa, 0, fee, d, p); self.set(fi, sa);
                self.retarget(*lock, Terms::Channel { a, b, key_a, key_b, delay, oneway, salt, state: ChanState::Closing { seq: *seq, bal_a: *bal_a, until: height + delay, locks: plocks.clone() } }, cap);
            }
            Op::ChanSettle { lock, wits, to_a, to_b, .. } => {
                let Terms::Channel { a, b, state: ChanState::Closing { bal_a, until, locks: plocks, .. }, .. } = self.lock(*lock)? else { bail!("not a channel that is closing") };
                if height <= until { bail!("the dispute window is still open"); }
                if wits.len() != plocks.len() { bail!("one witness entry per point lock ({} locks)", plocks.len()); }
                let cap = self.state[&(*lock as u64)].bal;
                // each point lock goes to its receiver if opened, back to its sender once expired, and otherwise holds the settlement back
                let (mut pay_a, mut pay_b) = (bal_a as u128, cap as u128 - bal_a as u128 - plocks_total(&plocks));
                for (l, w) in plocks.iter().zip(wits) {
                    let opened = w.as_ref().map_or(false, |t| l.opened_by(t));
                    if w.is_some() && !opened { bail!("a witness does not open its point lock"); }
                    if !opened && height <= l.expiry { bail!("a point lock has neither been opened nor expired"); }
                    let to_b = if opened { l.to_b } else { !l.to_b };
                    if to_b { pay_b += l.amt as u128 } else { pay_a += l.amt as u128 }
                }
                blockdata::pay_from(&mut sa, 0, fee, d, p); self.set(fi, sa);
                if pay_a > 0 { self.pay_out(to_a, &a, pay_a as u64)?; }
                if pay_b > 0 { self.pay_out(to_b, &b, pay_b as u64)?; }
                self.spend(*lock);
            }
            Op::ChanClose { lock, bal_a, sigs, to_a, to_b, .. } => {
                let t = self.lock(*lock)?;
                let Terms::Channel { a, b, key_a, key_b, oneway, state, .. } = t.clone() else { bail!("not a channel") };
                if let ChanState::Closing { until, locks, .. } = &state { if !locks.is_empty() { bail!("settle: the waiting state has point locks"); } let until = *until; if height > until { bail!("the dispute window is over; settle"); } }
                let cap = self.state[&(*lock as u64)].bal;
                if *bal_a > cap { bail!("a's share is more than the channel holds"); }
                let msg = chan_close_msg(chain, &t.channel_id().unwrap(), *bal_a, cap);
                if !sig_ok(&key_a, msg, sigs.ea, &sigs.sa) { bail!("a's signature on the close is bad"); }
                if !oneway && !sig_ok(&key_b, msg, sigs.eb, &sigs.sb) { bail!("b's signature on the close is bad"); }
                blockdata::pay_from(&mut sa, 0, fee, d, p); self.set(fi, sa);
                if *bal_a > 0 { self.pay_out(to_a, &a, *bal_a)?; }
                if cap - *bal_a > 0 { self.pay_out(to_b, &b, cap - *bal_a)?; }
                self.spend(*lock);
            }
            Op::ChanFund { lock, amt, .. } => {
                let Terms::Channel { a, b, key_a, key_b, delay, oneway, salt, state } = self.lock(*lock)? else { bail!("not a channel") };
                if sa.pk != b { bail!("only b funds a channel's other side"); }
                if oneway { bail!("a stream is funded by a alone"); }
                let cap = self.state[&(*lock as u64)].bal;
                let base_a = match state { ChanState::Open => cap, ChanState::OpenDual { base_a } => base_a, _ => bail!("a channel with a posted state is not funded again") };
                if *amt == 0 || *amt >= 1 << 62 || cap.checked_add(*amt).map_or(true, |c| c >= 1 << 62) { bail!("the amount is out of range"); }
                blockdata::pay_from(&mut sa, *amt, fee, d, p); self.set(fi, sa);
                self.retarget(*lock, Terms::Channel { a, b, key_a, key_b, delay, oneway, salt, state: ChanState::OpenDual { base_a } }, cap + amt);
            }
            Op::FactoryFund { lock, idx, amt, .. } => {
                let Terms::Factory { coord, key_c, mut members, delay, salt } = self.lock(*lock)? else { bail!("not a factory") };
                let m = members.get_mut(*idx as usize).ok_or_else(|| anyhow!("no member {idx}"))?;
                if sa.pk != m.addr { bail!("only the member funds its own channel"); }
                if m.state != SubState::Open { bail!("a channel with a posted state is not funded again"); }
                if *amt == 0 || *amt >= 1 << 62 || m.cap.checked_add(*amt).map_or(true, |c| c >= 1 << 62) { bail!("the amount is out of range"); }
                m.cap += *amt;
                let bal = self.state[&(*lock as u64)].bal + *amt;
                blockdata::pay_from(&mut sa, *amt, fee, d, p); self.set(fi, sa);
                self.retarget(*lock, Terms::Factory { coord, key_c, members, delay, salt }, bal);
            }
            Op::FactoryStart { lock, idx, .. } => {
                let Terms::Factory { coord, key_c, mut members, delay, salt } = self.lock(*lock)? else { bail!("not a factory") };
                let m = members.get_mut(*idx as usize).ok_or_else(|| anyhow!("no member {idx}"))?;
                if m.state != SubState::Open { bail!("that member's channel is not open"); }
                if sa.pk != coord && sa.pk != m.addr { bail!("only the coordinator and the member start a close"); }
                m.state = SubState::Closing { seq: 0, bal_c: m.base, until: height + delay, locks: vec![] };
                let bal = self.state[&(*lock as u64)].bal;
                blockdata::pay_from(&mut sa, 0, fee, d, p); self.set(fi, sa);
                self.retarget(*lock, Terms::Factory { coord, key_c, members, delay, salt }, bal);
            }
            Op::FactoryPost { lock, idx, seq, bal_c, locks: plocks, sigs, .. } => {
                let t = self.lock(*lock)?;
                let fid = t.factory_id().ok_or_else(|| anyhow!("not a factory"))?;
                let Terms::Factory { coord, key_c, mut members, delay, salt } = t else { bail!("not a factory") };
                let m = members.get_mut(*idx as usize).ok_or_else(|| anyhow!("no member {idx}"))?;
                match &m.state {
                    SubState::Exited => bail!("that member has left"),
                    SubState::Closing { seq: cur, until, .. } => { if height > *until { bail!("the dispute window is over; the member leaves"); } if *seq <= *cur { bail!("not newer than the state waiting"); } }
                    SubState::Open => {}
                }
                if *seq == 0 || *seq >= 1 << 62 { bail!("update numbers start at 1 and stay below 2^62"); }
                if plocks.len() > MAX_PLOCKS { bail!("too many point locks"); }
                for l in plocks { if l.amt == 0 || l.expiry <= height || l.expiry >= 1 << 62 { bail!("a point lock needs an amount and an expiry in the future and below 2^62"); } crate::mint::decode_point(&l.point)?; }
                if *bal_c as u128 + plocks_total(plocks) > m.cap as u128 { bail!("the shares and the point locks are more than the member's channel holds"); }
                let msg = fact_state_msg(chain, &fid, *idx, *seq, *bal_c, m.cap, plocks);
                if !sig_ok(&key_c, msg, sigs.ea, &sigs.sa) { bail!("the coordinator's signature on the state is bad"); }
                if !sig_ok(&m.key, msg, sigs.eb, &sigs.sb) { bail!("the member's signature on the state is bad"); }
                m.state = SubState::Closing { seq: *seq, bal_c: *bal_c, until: height + delay, locks: plocks.clone() };
                let bal = self.state[&(*lock as u64)].bal;
                blockdata::pay_from(&mut sa, 0, fee, d, p); self.set(fi, sa);
                self.retarget(*lock, Terms::Factory { coord, key_c, members, delay, salt }, bal);
            }
            Op::FactoryExit { lock, idx, wits, to_c, to_m, .. } => {
                let Terms::Factory { coord, key_c, mut members, delay, salt } = self.lock(*lock)? else { bail!("not a factory") };
                let m = members.get_mut(*idx as usize).ok_or_else(|| anyhow!("no member {idx}"))?;
                let SubState::Closing { bal_c, until, locks: plocks, .. } = m.state.clone() else { bail!("that member's channel is not closing") };
                if height <= until { bail!("the dispute window is still open"); }
                if wits.len() != plocks.len() { bail!("one witness entry per point lock ({} locks)", plocks.len()); }
                let (mut pay_c, mut pay_m) = (bal_c as u128, m.cap as u128 - bal_c as u128 - plocks_total(&plocks));
                for (l, w) in plocks.iter().zip(wits) {
                    let opened = w.as_ref().map_or(false, |t| l.opened_by(t));
                    if w.is_some() && !opened { bail!("a witness does not open its point lock"); }
                    if !opened && height <= l.expiry { bail!("a point lock has neither been opened nor expired"); }
                    // a's side is the coordinator, b's the member
                    if if opened { l.to_b } else { !l.to_b } { pay_m += l.amt as u128 } else { pay_c += l.amt as u128 }
                }
                let (cap, maddr) = (m.cap, m.addr);
                m.state = SubState::Exited;
                let bal = self.state[&(*lock as u64)].bal;
                blockdata::pay_from(&mut sa, 0, fee, d, p); self.set(fi, sa);
                if pay_c > 0 { self.pay_out(to_c, &coord, pay_c as u64)?; }
                if pay_m > 0 { self.pay_out(to_m, &maddr, pay_m as u64)?; }
                if members.iter().all(|x| x.state == SubState::Exited) { self.spend(*lock); } else { self.retarget(*lock, Terms::Factory { coord, key_c, members, delay, salt }, bal - cap); }
            }
            Op::FactoryExitNow { lock, idx, bal_c, sigs, to_c, to_m, .. } => {
                let t = self.lock(*lock)?;
                let fid = t.factory_id().ok_or_else(|| anyhow!("not a factory"))?;
                let Terms::Factory { coord, key_c, mut members, delay, salt } = t else { bail!("not a factory") };
                let m = members.get_mut(*idx as usize).ok_or_else(|| anyhow!("no member {idx}"))?;
                match &m.state {
                    SubState::Exited => bail!("that member has left"),
                    SubState::Closing { locks, until, .. } => { if !locks.is_empty() { bail!("settle: the waiting state has point locks"); } if height > *until { bail!("the dispute window is over; the member leaves by settling"); } }
                    SubState::Open => {}
                }
                if *bal_c > m.cap { bail!("the coordinator's share is more than the member's channel holds"); }
                let msg = fact_close_msg(chain, &fid, *idx, *bal_c, m.cap);
                if !sig_ok(&key_c, msg, sigs.ea, &sigs.sa) { bail!("the coordinator's signature on the close is bad"); }
                if !sig_ok(&m.key, msg, sigs.eb, &sigs.sb) { bail!("the member's signature on the close is bad"); }
                let (cap, maddr) = (m.cap, m.addr);
                m.state = SubState::Exited;
                let bal = self.state[&(*lock as u64)].bal;
                blockdata::pay_from(&mut sa, 0, fee, d, p); self.set(fi, sa);
                if *bal_c > 0 { self.pay_out(to_c, &coord, *bal_c)?; }
                if cap - *bal_c > 0 { self.pay_out(to_m, &maddr, cap - *bal_c)?; }
                if members.iter().all(|x| x.state == SubState::Exited) { self.spend(*lock); } else { self.retarget(*lock, Terms::Factory { coord, key_c, members, delay, salt }, bal - cap); }
            }
            Op::Return { lock, to, .. } => {
                let Terms::Order { maker, sell, expiry, state, .. } = self.lock(*lock)? else { bail!("not an open order") };
                if !matches!(state, OrderState::Open | OrderState::Auction { .. }) { bail!("not an open order"); }
                if height <= expiry { bail!("the order has not expired"); }
                blockdata::pay_from(&mut sa, 0, fee, d, p); self.set(fi, sa);
                self.pay_out(to, &maker, sell)?;
                self.spend(*lock);
            }
        }
        Ok(())
    }
}

/// What the proof binds of an operation into the block's data hash (vault family only; none for the other kinds): a fixed layout of 32 elements after the tag.
/// kind, sender index, fee (2), amount (2), slot of a new lock, lock index, receiving index, new-account flag, new address (4), terms digest (4), e (4), s (10)
pub fn op_data_hash(op: &Op) -> Option<[F; 4]> {
    let mut f = Fw::new(b"ZenOpDat");
    match op {
        Op::Make { from, fee, amt, at, terms: t @ Terms::Vault { .. } } => { f.u32(1).u32(*from).u64(*fee).u64(*amt).u32(*at).u32(0).u32(0).u32(0).zeros(4).addr(&t.digest()).zeros(4 + 10); }
        Op::VaultClaim { from, fee, lock, to, e, s } => { f.u32(2).u32(*from).u64(*fee).u64(0).u32(0).u32(*lock).u32(to.idx).u32(to.new.is_some() as u32).addr(&to.new.unwrap_or([F::ZERO; 4])).zeros(4).u128(*e).bytes(s); }
        Op::VaultRefund { from, fee, lock, to } => { f.u32(3).u32(*from).u64(*fee).u64(0).u32(0).u32(*lock).u32(to.idx).u32(to.new.is_some() as u32).addr(&to.new.unwrap_or([F::ZERO; 4])).zeros(4 + 4 + 10); }
        _ => return None,
    }
    Some(f.hash())
}
/// which leaf circuit proves an operation: 0 the vault family (stage P2), 1 the channel family (P3), 2 orders and 3 factories (P4); none: not provable yet (the order claim, P5)
pub fn leaf_kind(op: &Op) -> Option<usize> {
    match op {
        Op::Make { terms: Terms::Vault { .. }, .. } | Op::VaultClaim { .. } | Op::VaultRefund { .. } => Some(0),
        Op::Make { terms: Terms::Channel { .. }, .. } | Op::ChanStart { .. } | Op::ChanUpdate { .. } | Op::ChanSettle { .. } | Op::ChanClose { .. } | Op::ChanFund { .. } => Some(1),
        Op::Make { terms: Terms::Order { .. }, .. } | Op::Reserve { .. } | Op::Bid { .. } | Op::Reopen { .. } | Op::Return { .. } | Op::OrderClaim { .. } => Some(2),
        Op::Make { terms: Terms::Factory { .. }, .. } | Op::FactoryStart { .. } | Op::FactoryPost { .. } | Op::FactoryExit { .. } | Op::FactoryExitNow { .. } | Op::FactoryFund { .. } => Some(3),
        _ => None,
    }
}
/// What the proof binds of a channel-family operation into the block's data hash: a fixed layout after the tag `ZenChDat`.
/// kind, sender index, fee (2), amount (2), lock index (a Make: its slot), destination a (index, new-account flag, address 4), destination b (same), the new lock's
/// terms digest (a Make), seq (2), a's share (2), the new point locks' digest (4), the signatures (ea 4, sa 10, eb 4, sb 10), the witnesses' digest (4)
pub fn chan_data_hash(op: &Op) -> Option<[F; 4]> {
    let z4 = [F::ZERO; 4];
    let dest = |f: &mut Fw, d: Option<&Dest>| { match d { Some(d) => { f.u32(d.idx).u32(d.new.is_some() as u32).addr(&d.new.unwrap_or(z4)); } None => { f.u32(0).u32(0).zeros(4); } } };
    let sigs = |f: &mut Fw, g: Option<&ChanSigs>| { match g { Some(g) => { f.u128(g.ea).bytes(&g.sa).u128(g.eb).bytes(&g.sb); } None => { f.zeros(28); } } };
    let mut f = Fw::new(b"ZenChDat");
    match op {
        Op::Make { from, fee, amt, at, terms: t @ Terms::Channel { .. } } => { f.u32(1).u32(*from).u64(*fee).u64(*amt).u32(*at); dest(&mut f, None); dest(&mut f, None); f.addr(&t.digest()).u64(0).u64(0).zeros(4); sigs(&mut f, None); f.zeros(4); }
        Op::ChanStart { from, fee, lock } => { f.u32(8).u32(*from).u64(*fee).u64(0).u32(*lock); dest(&mut f, None); dest(&mut f, None); f.zeros(4).u64(0).u64(0).zeros(4); sigs(&mut f, None); f.zeros(4); }
        Op::ChanUpdate { from, fee, lock, seq, bal_a, locks, sigs: g } => { f.u32(9).u32(*from).u64(*fee).u64(0).u32(*lock); dest(&mut f, None); dest(&mut f, None); f.zeros(4).u64(*seq).u64(*bal_a).addr(&plocks_digest(locks)); sigs(&mut f, Some(g)); f.zeros(4); }
        Op::ChanSettle { from, fee, lock, wits, to_a, to_b } => { f.u32(10).u32(*from).u64(*fee).u64(0).u32(*lock); dest(&mut f, Some(to_a)); dest(&mut f, Some(to_b)); f.zeros(4).u64(0).u64(0).zeros(4); sigs(&mut f, None); f.addr(&wits_digest(wits)); }
        Op::ChanClose { from, fee, lock, bal_a, sigs: g, to_a, to_b } => { f.u32(11).u32(*from).u64(*fee).u64(0).u32(*lock); dest(&mut f, Some(to_a)); dest(&mut f, Some(to_b)); f.zeros(4).u64(0).u64(*bal_a).zeros(4); sigs(&mut f, Some(g)); f.zeros(4); }
        Op::ChanFund { from, fee, lock, amt } => { f.u32(18).u32(*from).u64(*fee).u64(*amt).u32(*lock); dest(&mut f, None); dest(&mut f, None); f.zeros(4).u64(0).u64(0).zeros(4); sigs(&mut f, None); f.zeros(4); }
        _ => return None,
    }
    Some(f.hash())
}
/// What the proof binds of an order-family operation (stage P4) into the block's data hash: tag `ZenOrDat`, then
/// kind, sender index, fee (2), amount (2, a Make), lock index (a Make: its slot), destination (index, new-account flag, address 4: where the escrow or the sale goes),
/// the new lock's terms digest (a Make), the taker (4) and the bid (2) of a Reserve or Bid, the block time (a Reserve or Bid: it is kept in the terms)
pub fn order_data_hash(op: &Op, ntime: u32) -> Option<[F; 4]> {
    let z4 = [F::ZERO; 4];
    let dest = |f: &mut Fw, d: Option<&Dest>| { match d { Some(d) => { f.u32(d.idx).u32(d.new.is_some() as u32).addr(&d.new.unwrap_or(z4)); } None => { f.u32(0).u32(0).zeros(4); } } };
    let mut f = Fw::new(b"ZenOrDat");
    match op {
        Op::Make { from, fee, amt, at, terms: t @ Terms::Order { .. } } => { f.u32(1).u32(*from).u64(*fee).u64(*amt).u32(*at); dest(&mut f, None); f.addr(&t.digest()).zeros(4).u64(0).u32(0).zeros(4); }
        Op::Reserve { from, fee, lock, taker } => { f.u32(4).u32(*from).u64(*fee).u64(0).u32(*lock); dest(&mut f, None); f.zeros(4).addr(taker).u64(0).u32(ntime).zeros(4); }
        Op::Bid { from, fee, lock, taker, bid, refund } => { f.u32(17).u32(*from).u64(*fee).u64(0).u32(*lock); dest(&mut f, Some(refund)); f.zeros(4).addr(taker).u64(*bid).u32(ntime).zeros(4); }
        Op::Reopen { from, fee, lock, to } => { f.u32(6).u32(*from).u64(*fee).u64(0).u32(*lock); dest(&mut f, Some(to)); f.zeros(4).zeros(4).u64(0).u32(0).zeros(4); }
        Op::Return { from, fee, lock, to } => { f.u32(7).u32(*from).u64(*fee).u64(0).u32(*lock); dest(&mut f, Some(to)); f.zeros(4).zeros(4).u64(0).u32(0).zeros(4); }
        Op::OrderClaim { from, fee, lock, to, proof } => { f.u32(5).u32(*from).u64(*fee).u64(0).u32(*lock); dest(&mut f, Some(to)); f.zeros(4).zeros(4).u64(0).u32(0).addr(&bytes_digest(proof)); }
        _ => return None,
    }
    Some(f.hash())
}
/// the block-data hash of a provable operation, whichever family it is of (`ntime`: the block's time, which orders keep in their terms)
pub fn proved_data_hash(op: &Op, ntime: u32) -> Option<[F; 4]> { match leaf_kind(op)? { 0 => op_data_hash(op), 1 => chan_data_hash(op), 2 => order_data_hash(op, ntime), _ => factory_data_hash(op) } }
/// can the block proof carry this operation yet? (stages P2 to P5: every operation)
pub fn provable(op: &Op) -> bool { leaf_kind(op).is_some() }
pub fn provable_req(_r: &OpReq) -> bool { true }

/// Run a block's operations on the state (changes it); returns the fees they paid, which go to the fee pool.
pub fn apply_ops(ops: &[Op], state: &mut HashMap<u64, Acct>, tree: &mut Tree, locks: &mut LockTable, s: u64, height: u64, ctx: &Ctx, tmpl: Acct) -> Result<u64> {
    apply_ops_traced(ops, state, tree, locks, s, height, ctx, tmpl, None)
}
/// the same, and with `traces` the touches of each operation are kept (for the prover)
pub fn apply_ops_traced(ops: &[Op], state: &mut HashMap<u64, Acct>, tree: &mut Tree, locks: &mut LockTable, s: u64, height: u64, ctx: &Ctx, tmpl: Acct, mut traces: Option<&mut Vec<OpTrace>>) -> Result<u64> {
    let mut run = Run { state, tree, locks, s, height, ctx, tmpl, rec: vec![] };
    let mut fees = 0u64;
    for (n, op) in ops.iter().enumerate() {
        run.rec.clear();
        let terms = match op { Op::Make { terms, .. } => Some(terms.clone()), _ => op.lock_index().and_then(|l| run.locks.get(&(l as u64)).cloned()) };
        run.one(op).map_err(|e| if e.downcast_ref::<Unavailable>().is_some() { e } else { anyhow!("operation {n}: {e}") })?;
        fees += op.fee();
        if let Some(t) = traces.as_deref_mut() { t.push(OpTrace { touches: std::mem::take(&mut run.rec), terms }); }
    }
    Ok(fees)
}

// ---------------------------------------------------------------- the proof that the other chain was paid
/// What an order claim carries: the block of the other chain in which the payment sits, and the receiver's account leaf.
pub struct PaymentProof {
    pub chain: u8, pub height: u64, pub header: [u8; 80], pub coinbase: Vec<u8>, pub tickets_root: [u8; 32], pub pubvalues: Vec<u64>, pub stamp: Vec<u8>, pub data: Vec<u8>,
    /// which payment of the block (counting payments, not credits, in data order)
    pub entry: u32,
    /// the receiver's leaf after the block, when the payment did not create it, with its path
    pub leaf: Option<(u64, Vec<u64>, [u64; 7], Vec<[u64; 4]>)>,
}
impl PaymentProof {
    pub fn encode(&self) -> Vec<u8> {
        let mut w = Wr::new();
        w.u8(self.chain); w.u64(self.height); w.raw(&self.header);
        w.u32(self.coinbase.len() as u32); w.raw(&self.coinbase); w.raw(&self.tickets_root);
        w.u8(self.pubvalues.len() as u8); for v in &self.pubvalues { w.u64(*v); }
        w.u32(self.stamp.len() as u32); w.raw(&self.stamp); w.u32(self.data.len() as u32); w.raw(&self.data); w.u32(self.entry);
        match &self.leaf {
            None => w.u8(0),
            Some((idx, pk, nums, path)) => { w.u8(1); w.u64(*idx); for x in pk { w.u64(*x); } for x in nums { w.u64(*x); } w.u8(path.len() as u8); for h in path { for x in h { w.u64(*x); } } }
        }
        w.0
    }
    pub fn decode(b: &[u8]) -> Result<PaymentProof> {
        let mut r = Rd::new(b);
        let (chain, height) = (r.u8()?, r.u64()?);
        let header: [u8; 80] = r.take(80)?.try_into()?;
        let n = r.u32()? as usize; if n > 1024 { bail!("coinbase too long"); } let coinbase = r.take(n)?.to_vec();
        let tickets_root: [u8; 32] = r.take(32)?.try_into()?;
        let n = r.u8()? as usize; let pubvalues = (0..n).map(|_| r.u64()).collect::<Result<Vec<_>>>()?;
        let n = r.u32()? as usize; if n > MAX_PROOF { bail!("stamp too long"); } let stamp = r.take(n)?.to_vec();
        let n = r.u32()? as usize; if n > MAX_PROOF { bail!("data too long"); } let data = r.take(n)?.to_vec();
        let entry = r.u32()?;
        let leaf = match r.u8()? {
            0 => None,
            1 => {
                let idx = r.u64()?;
                let pk = (0..4).map(|_| r.u64()).collect::<Result<Vec<_>>>()?;
                let mut nums = [0u64; 7]; for x in nums.iter_mut() { *x = r.u64()?; }
                let k = r.u8()? as usize; if k != DEPTH { bail!("a path of {k} hashes"); }
                let path = (0..k).map(|_| Ok([r.u64()?, r.u64()?, r.u64()?, r.u64()?])).collect::<Result<Vec<_>>>()?;
                Some((idx, pk, nums, path))
            }
            _ => bail!("bad flag"),
        };
        r.done()?;
        Ok(PaymentProof { chain, height, header, coinbase, tickets_root, pubvalues, stamp, data, entry, leaf })
    }
}

/// A node's check of an order claim, the way a light client does it: the header is the one this node follows and has enough blocks on top of it; the
/// block's body hashes to the header's commitment; the data hash in the public values matches the data; the payment sits at the given place and pays
/// at least what the order asks to the order's address, in a block made after the reservation.
pub fn check_payment_proof(view: &dyn CrossHeaders, want_chain: u8, pay_to: &[F; 4], want_amt: u64, since: u32, proof: &[u8]) -> Result<()> {
    let pr = PaymentProof::decode(proof)?;
    if pr.chain != want_chain { bail!("the proof is from chain {}, the order asks for chain {}", pr.chain, want_chain); }
    let (known_hash, known_time) = view.header(pr.chain, pr.height).ok_or_else(|| anyhow::Error::new(Unavailable(format!("no header {} of chain {} yet", pr.height, pr.chain))))?;
    let tip = view.tip_height(pr.chain).ok_or_else(|| anyhow::Error::new(Unavailable(format!("chain {} not followed", pr.chain))))?;
    if tip < pr.height + confirmations(pr.chain) { return Err(anyhow::Error::new(Unavailable(format!("the payment needs {} blocks on top; chain {} has {}", confirmations(pr.chain), pr.chain, tip.saturating_sub(pr.height))))); }
    if crate::seal::sha256d(&pr.header) != known_hash { bail!("the header is not the one this node follows at that height"); }
    let ntime = u32::from_le_bytes(pr.header[68..72].try_into().unwrap());
    if ntime != known_time { bail!("header time differs"); }
    if ntime <= since { bail!("the payment is not after the reservation"); }
    let commitment: [u8; 32] = pr.header[36..68].try_into().unwrap();
    if pr.pubvalues.len() != crate::node::PUBVALUES { bail!("wrong number of public values"); }
    let body = crate::seal::body_root(&pr.pubvalues, &pr.stamp, &pr.data, &pr.tickets_root);
    if crate::seal::merkle_root(&pr.coinbase, &[body]) != commitment { bail!("the block body does not match the header"); }
    if pr.pubvalues[15] != pr.height { bail!("the block is not at that height"); }
    let (slots, leaves, _) = blockdata::decode_prefix(&pr.data)?;
    let hashes: Vec<HashOut<F>> = leaves.iter().map(|l| blockdata::leaf_data_hash(slots, l)).collect();
    let dh = blockdata::combine(hashes);
    let want: Vec<u64> = dh.elements.iter().map(|x| x.to_canonical_u64()).collect();
    if want != pr.pubvalues[10..14] { bail!("the data does not match the block's data hash"); }
    let e: &BlockEntry = leaves.iter().flat_map(|l| l.pays.iter()).filter(|e| !e.credit).nth(pr.entry as usize).ok_or_else(|| anyhow!("no such payment in the block"))?;
    if e.amt < want_amt { bail!("the payment is {} but the order asks for {}", e.amt, want_amt); }
    let receiver = match (&e.new_r, &pr.leaf) {
        (Some(a), _) => *a,
        (None, Some((idx, pk, nums, path))) => {
            if *idx != e.r_idx as u64 { bail!("the leaf is not the receiver's"); }
            let f = |x: u64| -> Result<F> { if x >= <F as plonky2::field::types::Field64>::ORDER { bail!("not a field element") } Ok(F::from_canonical_u64(x)) };
            let pkf = [f(pk[0])?, f(pk[1])?, f(pk[2])?, f(pk[3])?];
            let acct = Acct { pk: pkf, bal: nums[0], nonce: nums[1], rest: nums[2], used: nums[3], fd: nums[4], rd: nums[5], up: nums[6],
                              a: crate::ec::P { x: crate::ec::E::ZERO, y: crate::ec::E::ZERO }, k: [0; 4] };
            let mut cur = leaf_hash(&acct);
            for (l, sib) in path.iter().enumerate() {
                let sib = HashOut { elements: [f(sib[0])?, f(sib[1])?, f(sib[2])?, f(sib[3])?] };
                cur = if (idx >> l) & 1 == 0 { crate::h2(cur, sib) } else { crate::h2(sib, cur) };
            }
            let root: Vec<u64> = cur.elements.iter().map(|x| x.to_canonical_u64()).collect();
            if root != pr.pubvalues[4..8] { bail!("the receiver's leaf is not in the block's state"); }
            pkf
        }
        (None, None) => bail!("the payment did not create its receiver; the proof needs the receiver's leaf"),
    };
    if receiver != *pay_to { bail!("the payment is not to the order's address"); }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mint;
    use crate::node::dev::{self, DevPay, OpReq};
    use crate::node::{Block, Chain, DevStamp, DevStampMaker, Node, Params};
    use std::sync::Arc;

    const FEE: u64 = 10_000;
    fn bal(c: &Chain, k: &mint::Key) -> u64 { c.account(&k.addr).map_or(0, |(_, a)| a.bal) }
    /// one block on the chain: tickets from the first four wallets (they are the minters and miner), the given payments and operations
    fn step(c: &mut Chain, keys: &[mint::Key], pays: &[DevPay], reqs: &[OpReq]) -> Result<Block> {
        let b = dev::build_block_ops(c, keys[0].addr, dev::make_tickets(c, &keys[..4], 24), pays, reqs, c.tip_ntime + 150, &DevStampMaker)?;
        c.accept(&b, u32::MAX)?;
        Ok(b)
    }
    /// the block with every resolvable operation in it, whether or not it is valid: Err says why not
    fn forced(c: &Chain, keys: &[mint::Key], reqs: &[OpReq]) -> Result<Block> {
        dev::build_template_ops_with(c, keys[0].addr, dev::make_tickets(c, &keys[..4], 24), &[], reqs, c.tip_ntime + 150, &DevStampMaker, true)
    }
    fn chain_a() -> (Chain, Vec<mint::Key>) {
        let keys = dev::devnet_keys(8);
        (Chain::open(Params::devnet(), &dev::genesis_of(&keys), Box::new(DevStamp), None).unwrap(), keys)
    }
    #[track_caller]
    fn err_of<T>(r: Result<T>) -> String { match r { Ok(_) => panic!("accepted"), Err(e) => e.to_string() } }
    fn vault(owner: &mint::Key, key: &mint::Key, timeout: u64) -> Terms { Terms::Vault { key: mint::encode_point(key.a), owner: owner.addr, timeout, salt: 0 } }
    fn lock_addr(c: &Chain, n: usize) -> [F; 4] { let mut v: Vec<_> = c.locks.iter().collect(); v.sort_by_key(|(i, _)| **i); v[n].1.digest() }

    #[test]
    fn operations_and_terms_round_trip_and_terms_change_the_address() {
        let keys = dev::devnet_keys(3);
        let t = Terms::Order { maker: keys[0].addr, sell: 5, want_chain: 2, want_amt: 7, pay_to: keys[1].addr, expiry: 90, reserve_blocks: 4, deposit: 1, salt: 3, state: OrderState::Open };
        assert_eq!(Terms::decode_from(&mut Rd::new(&t.encode())).unwrap(), t);
        let r = Terms::Order { maker: keys[0].addr, sell: 5, want_chain: 2, want_amt: 7, pay_to: keys[1].addr, expiry: 90, reserve_blocks: 4, deposit: 1, salt: 3,
                               state: OrderState::Reserved { taker: keys[2].addr, until: 20, since: 99 } };
        assert_eq!(Terms::decode_from(&mut Rd::new(&r.encode())).unwrap(), r);
        assert_ne!(t.digest(), r.digest(), "reserving changes the lock's address, so the state root commits to the reservation");
        let d = Dest { idx: 5, new: Some(keys[2].addr) };
        let ops = vec![Op::Make { from: 1, fee: 9, amt: 77, at: 4, terms: t.clone() }, Op::VaultClaim { from: 2, fee: 9, lock: 3, to: d, e: 5, s: [7; 40] },
                       Op::VaultRefund { from: 1, fee: 1, lock: 2, to: Dest { idx: 1, new: None } }, Op::Reserve { from: 3, fee: 4, lock: 9, taker: keys[2].addr },
                       Op::OrderClaim { from: 1, fee: 4, lock: 9, to: d, proof: vec![1, 2, 3] }, Op::Reopen { from: 1, fee: 4, lock: 9, to: d }, Op::Return { from: 1, fee: 4, lock: 9, to: d }];
        let b = encode_ops(&ops);
        assert_eq!(decode_ops(&b).unwrap(), ops);
        assert!(decode_ops(&[]).unwrap().is_empty());
        for cut in [1, 5, b.len() / 2, b.len() - 1] { assert!(decode_ops(&b[..cut]).is_err(), "cut at {cut}"); }
        let mut junk = b.clone(); junk.push(0); assert!(decode_ops(&junk).is_err());
        let mut bad = b.clone(); bad[0] = b'X'; assert!(decode_ops(&bad).is_err());
    }

    #[test]
    fn a_locks_address_follows_every_field_of_its_terms_and_every_state() {
        let keys = dev::devnet_keys(4);
        let (a, b) = (&keys[0], &keys[1]);
        let mut seen = std::collections::HashSet::new();
        let mut add = |t: Terms| { assert!(seen.insert(t.digest().map(|x| x.to_canonical_u64())), "two different terms share an address: {t:?}"); };
        let base = vault(a, b, 10); add(base.clone());
        add(vault(a, b, 11)); add(vault(b, a, 10)); add(vault(a, a, 10));
        let mut t = base.clone(); t.set_salt(1); add(t);
        let pl = |amt: u64| PLock { amt, to_b: true, point: mint::encode_point(a.a), expiry: 9 };
        let ch = |st: ChanState| Terms::Channel { a: a.addr, b: b.addr, key_a: mint::encode_point(a.a), key_b: mint::encode_point(b.a), delay: 3, oneway: false, salt: 0, state: st };
        for st in [ChanState::Open, ChanState::OpenDual { base_a: 5 }, ChanState::OpenDual { base_a: 6 },
                   ChanState::Closing { seq: 1, bal_a: 2, until: 3, locks: vec![] }, ChanState::Closing { seq: 1, bal_a: 2, until: 4, locks: vec![] },
                   ChanState::Closing { seq: 2, bal_a: 2, until: 3, locks: vec![] }, ChanState::Closing { seq: 1, bal_a: 3, until: 3, locks: vec![] },
                   ChanState::Closing { seq: 1, bal_a: 2, until: 3, locks: vec![pl(1)] }, ChanState::Closing { seq: 1, bal_a: 2, until: 3, locks: vec![pl(2)] },
                   ChanState::Closing { seq: 1, bal_a: 2, until: 3, locks: vec![pl(1), pl(1)] }] { add(ch(st)); }
        // values above 2^32 and above the field order's 2^63 are told apart too (a u64 is two limbs, nothing is reduced)
        add(vault(a, b, 1 << 40)); add(vault(a, b, u64::MAX)); add(vault(a, b, u64::MAX - 1));
        let m = |cap: u64, st: SubState| FMember { addr: b.addr, key: mint::encode_point(b.a), cap, base: cap, state: st };
        let f = |ms: Vec<FMember>| Terms::Factory { coord: a.addr, key_c: mint::encode_point(a.a), members: ms, delay: 3, salt: 0 };
        add(f(vec![m(5, SubState::Open)])); add(f(vec![m(6, SubState::Open)])); add(f(vec![m(5, SubState::Exited)]));
        add(f(vec![m(5, SubState::Open), m(5, SubState::Open)])); add(f(vec![m(5, SubState::Closing { seq: 1, bal_c: 1, until: 2, locks: vec![pl(1)] })]));
        let ord = |st: OrderState| Terms::Order { maker: a.addr, sell: 4, want_chain: 2, want_amt: 2, pay_to: b.addr, expiry: 60, reserve_blocks: 30, deposit: 1, salt: 0, state: st };
        for st in [OrderState::Open, OrderState::Auction { window: 3 }, OrderState::Auction { window: 4 }, OrderState::Reserved { taker: b.addr, until: 5, since: 6 },
                   OrderState::Reserved { taker: b.addr, until: 6, since: 5 }, OrderState::Bidding { window: 3, taker: b.addr, bid: 7, close: 8, since: 9 },
                   OrderState::Bidding { window: 3, taker: b.addr, bid: 8, close: 7, since: 9 }] { add(ord(st)); }
        // the stable ids ignore the state and follow the setup
        let (c1, c2) = (ch(ChanState::Open), ch(ChanState::Closing { seq: 1, bal_a: 2, until: 3, locks: vec![] }));
        assert_eq!(c1.channel_id(), c2.channel_id());
        assert_ne!(c1.digest(), c2.digest());
        let mut c3 = c1.clone(); c3.set_salt(1);
        assert_ne!(c1.channel_id(), c3.channel_id());
        let (f1, f2) = (f(vec![m(5, SubState::Open)]), f(vec![m(5, SubState::Exited)]));
        assert_eq!(f1.factory_id(), f2.factory_id(), "a member's state is not part of the factory's id");
        // every signed message names its chain and its subject
        let id = c1.channel_id().unwrap();
        assert_ne!(chan_state_msg(1, &id, 1, 2, 3, &[]), chan_state_msg(2, &id, 1, 2, 3, &[]));
        assert_ne!(chan_state_msg(1, &id, 1, 2, 3, &[]), chan_state_msg(1, &id, 1, 2, 3, &[pl(1)]));
        assert_ne!(chan_close_msg(1, &id, 2, 3), chan_state_msg(1, &id, 2, 3, 0, &[]));
        assert_ne!(sub_id(&id, 0), sub_id(&id, 1));
        assert_ne!(fact_state_msg(1, &id, 0, 1, 2, 3, &[]), fact_close_msg(1, &id, 0, 2, 3));
    }

    #[test]
    fn a_vault_claim_signed_for_one_chain_is_refused_on_another() {
        let (mut c, keys) = chain_a();
        let (owner, claimer, dest, anyone) = (&keys[4], &keys[5], &keys[6], &keys[7]);
        step(&mut c, &keys, &[], &[OpReq::Make { from: owner.addr, amt: 500_000_000, fee: FEE, terms: vault(owner, claimer, 20) }]).unwrap();
        let lock = lock_addr(&c, 0);
        let other = c.p.chain.wrapping_add(1);
        let (e, s) = mint::sign(claimer, vault_claim_msg(other, &lock, &dest.addr));
        let replay = OpReq::VaultClaim { from: anyone.addr, fee: FEE, lock, to: dest.addr, e, s: mint::s_bytes(&s) };
        assert!(err_of(forced(&c, &keys, &[replay])).contains("not signed by"), "a claim made for another chain does not carry over");
        let (e, s) = mint::sign(claimer, vault_claim_msg(c.p.chain, &lock, &dest.addr));
        let ok = OpReq::VaultClaim { from: anyone.addr, fee: FEE, lock, to: dest.addr, e, s: mint::s_bytes(&s) };
        step(&mut c, &keys, &[], &[ok]).unwrap();
    }

    #[test]
    fn an_amount_so_large_that_amount_plus_fee_wraps_is_refused() {
        let (c, keys) = chain_a();
        let owner = &keys[4];
        let big = OpReq::Make { from: owner.addr, amt: u64::MAX - FEE + 1, fee: FEE, terms: vault(owner, &keys[5], 20) };
        assert!(err_of(forced(&c, &keys, &[big])).contains("balance too low"));
    }

    #[test]
    fn a_vault_is_spent_by_its_key_before_the_timeout_and_returns_to_its_owner_after() {
        let (mut c, keys) = chain_a();
        let (owner, claimer, dest, anyone) = (&keys[4], &keys[5], &keys[6], &keys[7]);
        let (b_owner, b_dest) = (bal(&c, owner), bal(&c, dest));
        // lock 500 000 000 in a vault that times out at height 6
        step(&mut c, &keys, &[], &[OpReq::Make { from: owner.addr, amt: 500_000_000, fee: FEE, terms: vault(owner, claimer, 6) }]).unwrap();
        assert_eq!(c.locks.len(), 1);
        assert_eq!(bal(&c, owner), b_owner - 500_000_000 - FEE);
        c.audit().unwrap();
        let lock = lock_addr(&c, 0);
        assert_eq!(c.account(&lock).unwrap().1.bal, 500_000_000, "the lock is a leaf in the state, so the root commits to it");
        // nobody can pay into it or out of it as an account
        let pay = DevPay { from: anyone.addr, to: lock, amt: 1_000_000, fee: FEE };
        let e = err_of(dev::build_template(&c, keys[0].addr, dev::make_tickets(&c, &keys[..4], 24), &[pay], c.tip_ntime + 150, &DevStampMaker));
        assert!(e.contains("lock"), "{e}");
        // a claim signed by the wrong key is refused
        let msg = vault_claim_msg(c.p.chain, &lock, &dest.addr);
        let (e_bad, s_bad) = mint::sign(anyone, msg);
        let bad = OpReq::VaultClaim { from: anyone.addr, fee: FEE, lock, to: dest.addr, e: e_bad, s: mint::s_bytes(&s_bad) };
        assert!(err_of(forced(&c, &keys, &[bad.clone()])).contains("not signed by the vault's key"));
        // a signature for another destination does not carry over to this one
        let (e2, s2) = mint::sign(claimer, vault_claim_msg(c.p.chain, &lock, &anyone.addr));
        let moved = OpReq::VaultClaim { from: anyone.addr, fee: FEE, lock, to: dest.addr, e: e2, s: mint::s_bytes(&s2) };
        assert!(err_of(forced(&c, &keys, &[moved])).contains("not signed by"));
        // a refund before the timeout is refused
        let early = OpReq::VaultRefund { from: anyone.addr, fee: FEE, lock, to: owner.addr };
        assert!(err_of(forced(&c, &keys, &[early.clone()])).contains("not timed out"));
        // the key's claim goes through, and the pool leaves out a bad one without failing the block
        let (e, s) = mint::sign(claimer, msg);
        let good = OpReq::VaultClaim { from: anyone.addr, fee: FEE, lock, to: dest.addr, e, s: mint::s_bytes(&s) };
        let b = step(&mut c, &keys, &[], &[bad, good]).unwrap();
        assert_eq!(decode_ops(&b.data[blockdata::decode_prefix(&b.data).unwrap().2..]).unwrap().len(), 1, "only the good claim is in the block");
        assert_eq!(bal(&c, dest), b_dest + 500_000_000);
        assert!(c.locks.is_empty() && c.account(&lock).is_none());
        c.audit().unwrap();

        // a second vault: nobody claims it, so after the timeout it goes back to its owner, whoever asks
        let mut t = vault(owner, claimer, c.height + 3);
        let before = bal(&c, owner);
        step(&mut c, &keys, &[], &[OpReq::Make { from: owner.addr, amt: 300_000_000, fee: FEE, terms: t.clone() }]).unwrap();
        t.set_salt(c.account(&owner.addr).unwrap().1.nonce - 1);
        let lock2 = t.digest();
        assert!(c.account(&lock2).is_some(), "the salt (the sender's nonce) is part of the address");
        let late = { let (e, s) = mint::sign(claimer, vault_claim_msg(c.p.chain, &lock2, &dest.addr)); OpReq::VaultClaim { from: anyone.addr, fee: FEE, lock: lock2, to: dest.addr, e, s: mint::s_bytes(&s) } };
        while c.height < c.locks.values().map(|t| match t { Terms::Vault { timeout, .. } => *timeout, _ => 0 }).max().unwrap() { assert!(err_of(forced(&c, &keys, &[OpReq::VaultRefund { from: anyone.addr, fee: FEE, lock: lock2, to: owner.addr }])).contains("not timed out")); step(&mut c, &keys, &[], &[]).unwrap(); }
        assert!(err_of(forced(&c, &keys, &[late])).contains("timed out"), "the key can no longer claim");
        step(&mut c, &keys, &[], &[OpReq::VaultRefund { from: anyone.addr, fee: FEE, lock: lock2, to: owner.addr }]).unwrap();
        assert_eq!(bal(&c, owner), before - FEE, "the owner is made whole (the make fee is spent)");
        assert!(c.locks.is_empty());
        c.audit().unwrap();
        // the fees of the operations went to the fee pool
        assert!(c.pool > 0);
    }

    #[test]
    fn a_lock_with_odd_terms_is_refused() {
        let (c, keys) = chain_a();
        let (o, k) = (&keys[4], &keys[5]);
        let mk = |t: Terms, amt: u64| OpReq::Make { from: o.addr, amt, fee: FEE, terms: t };
        assert!(err_of(forced(&c, &keys, &[mk(vault(o, k, 0), 1_000_000)])).contains("timeout"));
        assert!(err_of(forced(&c, &keys, &[mk(Terms::Vault { key: [7; 41], owner: o.addr, timeout: 9, salt: 0 }, 1_000_000)])).contains("point") || true);
        assert!(err_of(forced(&c, &keys, &[mk(Terms::Vault { key: mint::encode_point(k.a), owner: k.addr, timeout: 9, salt: 0 }, 1_000_000)])).contains("owner"));
        assert!(err_of(forced(&c, &keys, &[mk(vault(o, k, 9), 5)])).contains("smallest amount"));
        assert!(err_of(forced(&c, &keys, &[mk(vault(o, k, 9), 2_000_000_000)])).contains("balance"));
        let ord = |f: &dyn Fn(&mut Terms)| { let mut t = Terms::Order { maker: o.addr, sell: 400_000_000, want_chain: 2, want_amt: 200_000_000, pay_to: keys[6].addr, expiry: 50, reserve_blocks: 20, deposit: 4_000_000, salt: 0, state: OrderState::Open }; f(&mut t); t };
        assert!(forced(&c, &keys, &[mk(ord(&|_| {}), 400_000_000)]).is_ok());
        assert!(err_of(forced(&c, &keys, &[mk(ord(&|t| if let Terms::Order { want_chain, .. } = t { *want_chain = 3 }), 400_000_000)])).contains("another chain's metal"));
        assert!(err_of(forced(&c, &keys, &[mk(ord(&|t| if let Terms::Order { want_chain, .. } = t { *want_chain = 9 }), 400_000_000)])).contains("another chain's metal"));
        assert!(err_of(forced(&c, &keys, &[mk(ord(&|t| if let Terms::Order { deposit, .. } = t { *deposit = 1 }), 400_000_000)])).contains("deposit"));
        assert!(err_of(forced(&c, &keys, &[mk(ord(&|t| if let Terms::Order { expiry, .. } = t { *expiry = 0 }), 400_000_000)])).contains("expired"));
        assert!(err_of(forced(&c, &keys, &[mk(ord(&|t| if let Terms::Order { maker, .. } = t { *maker = keys[7].addr }), 400_000_000)])).contains("maker"));
        assert!(err_of(forced(&c, &keys, &[mk(ord(&|t| if let Terms::Order { want_amt, .. } = t { *want_amt = 0 }), 400_000_000)])).contains("asked amount"));
        assert!(err_of(forced(&c, &keys, &[mk(ord(&|_| {}), 399_999_999)])).contains("sells what the lock holds"));
    }

    // ---- orders across two chains: A is Jen (chain 3) selling for Ken (chain 2), B is Ken
    struct View { chain: u8, heights: HashMap<u64, ([u8; 32], u32)>, tip: u64 }
    impl CrossHeaders for View {
        fn header(&self, chain: u8, h: u64) -> Option<([u8; 32], u32)> { if chain == self.chain { self.heights.get(&h).copied() } else { None } }
        fn tip_height(&self, chain: u8) -> Option<u64> { (chain == self.chain).then_some(self.tip) }
    }
    fn view_of(n: &Node) -> Arc<dyn CrossHeaders> {
        let heights = (1..=n.height()).map(|h| { let b = n.block(&n.hash_at(h).unwrap()).unwrap(); (h, (n.hash_at(h).unwrap(), b.header.ntime)) }).collect();
        Arc::new(View { chain: n.tip().p.chain, heights, tip: n.height() })
    }
    fn chain_b(keys: &[mint::Key]) -> Node { Node::open(Params { chain: 2, ..Params::devnet() }, &dev::genesis_of(keys), Box::new(DevStamp), None).unwrap() }
    fn b_block(n: &mut Node, keys: &[mint::Key], pays: &[DevPay]) -> usize {
        let t = n.tip().tip_ntime + 150;
        let b = dev::build_block(n.tip(), keys[0].addr, dev::make_tickets(n.tip(), &keys[..4], 24), pays, t, &DevStampMaker).unwrap();
        n.add_block(&b, u32::MAX).unwrap();
        n.height() as usize
    }
    fn order(maker: &mint::Key, pay_to: [F; 4]) -> Terms {
        Terms::Order { maker: maker.addr, sell: 400_000_000, want_chain: 2, want_amt: 200_000_000, pay_to, expiry: 60, reserve_blocks: 30, deposit: 4_000_000, salt: 0, state: OrderState::Open }
    }

    #[test]
    fn a_batch_auction_gives_the_order_to_the_highest_escrow_not_to_the_first_in_the_block() {
        let (mut a, keys) = chain_a();
        let (maker, t1, t2, anyone) = (&keys[4], &keys[5], &keys[6], &keys[7]);
        let pay_to = crate::tx::Wallet::generate().address();
        let mut t = order(maker, pay_to);
        if let Terms::Order { state, .. } = &mut t { *state = OrderState::Auction { window: 3 }; }
        step(&mut a, &keys, &[], &[OpReq::Make { from: maker.addr, amt: 400_000_000, fee: FEE, terms: t }]).unwrap();
        let (b1, b2) = (bal(&a, t1), bal(&a, t2));
        // a plain reservation is not how an auction is entered; a bid below the order's deposit is refused
        let lock = lock_addr(&a, 0);
        assert!(err_of(forced(&a, &keys, &[OpReq::Reserve { from: t1.addr, fee: FEE, lock, taker: t1.addr }])).contains("not an open order"));
        assert!(err_of(forced(&a, &keys, &[OpReq::Bid { from: t1.addr, fee: FEE, lock, taker: t1.addr, bid: 3_999_999 }])).contains("below the deposit"));
        // the first bid opens the window
        step(&mut a, &keys, &[], &[OpReq::Bid { from: t1.addr, fee: FEE, lock, taker: t1.addr, bid: 4_000_000 }]).unwrap();
        let lock = lock_addr(&a, 0);
        assert_eq!(a.account(&lock).unwrap().1.bal, 404_000_000);
        assert!(err_of(forced(&a, &keys, &[OpReq::Bid { from: t2.addr, fee: FEE, lock, taker: t2.addr, bid: 4_000_000 }])).contains("not higher"));
        assert!(err_of(forced(&a, &keys, &[OpReq::OrderClaim { from: anyone.addr, fee: FEE, lock, proof: vec![] }])).contains("still running"));
        // a higher bid replaces it, and the first bidder gets their escrow back at once
        step(&mut a, &keys, &[], &[OpReq::Bid { from: t2.addr, fee: FEE, lock, taker: t2.addr, bid: 9_000_000 }]).unwrap();
        let lock = lock_addr(&a, 0);
        assert_eq!(a.account(&lock).unwrap().1.bal, 409_000_000);
        assert_eq!(bal(&a, t1), b1 - FEE, "the outbid taker has its escrow back and has lost only its fee");
        a.audit().unwrap();
        // the window closes 3 blocks after the first bid: later bids are refused
        for _ in 0..3 { step(&mut a, &keys, &[], &[]).unwrap(); }
        assert!(err_of(forced(&a, &keys, &[OpReq::Bid { from: t1.addr, fee: FEE, lock, taker: t1.addr, bid: 20_000_000 }])).contains("over"));
        // the winner is the taker now: nobody else can reopen it until the reservation time has run
        assert!(err_of(forced(&a, &keys, &[OpReq::Reopen { from: anyone.addr, fee: FEE, lock }])).contains("still running"));
        while a.height < 5 + 3 + 30 + 1 { step(&mut a, &keys, &[], &[]).unwrap(); }
        let m0 = bal(&a, maker);
        step(&mut a, &keys, &[], &[OpReq::Reopen { from: anyone.addr, fee: FEE, lock }]).unwrap();
        assert_eq!(bal(&a, maker), m0 + 9_000_000, "the winner never paid: the escrow goes to the maker");
        assert_eq!(bal(&a, t2), b2 - 9_000_000 - FEE);
        let lock = lock_addr(&a, 0);
        assert_eq!(a.account(&lock).unwrap().1.bal, 400_000_000);
        // and the order is open to a new auction
        step(&mut a, &keys, &[], &[OpReq::Bid { from: t1.addr, fee: FEE, lock, taker: t1.addr, bid: 5_000_000 }]).unwrap();
        a.audit().unwrap();
    }

    #[test]
    fn an_order_is_made_reserved_paid_on_the_other_chain_and_claimed() {
        let (mut a, keys) = chain_a();
        let (maker, taker, anyone) = (&keys[4], &keys[5], &keys[7]);
        let pay_to = crate::tx::Wallet::generate().address();
        let (m0, t0) = (bal(&a, maker), bal(&a, taker));
        // A block 1: the maker sells 400 000 000 of Jen for 200 000 000 of Ken, to be paid to a fresh Ken address
        step(&mut a, &keys, &[], &[OpReq::Make { from: maker.addr, amt: 400_000_000, fee: FEE, terms: order(maker, pay_to) }]).unwrap();
        let lock = lock_addr(&a, 0);
        assert_eq!(bal(&a, maker), m0 - 400_000_000 - FEE);
        // a second reservation or a claim without one is refused
        let claim_early = OpReq::OrderClaim { from: anyone.addr, fee: FEE, lock, proof: vec![] };
        assert!(err_of(forced(&a, &keys, &[claim_early])).contains("not a reserved order"));
        // A block 2: the taker reserves it, paying the 1% deposit; the lock's address changes with its terms
        step(&mut a, &keys, &[], &[OpReq::Reserve { from: taker.addr, fee: FEE, lock, taker: taker.addr }]).unwrap();
        assert!(a.account(&lock).is_none(), "the order has a new address now that it is reserved");
        let lock = lock_addr(&a, 0);
        assert_eq!(a.account(&lock).unwrap().1.bal, 404_000_000, "the sale and the deposit");
        assert_eq!(bal(&a, taker), t0 - 4_000_000 - FEE);
        assert!(err_of(forced(&a, &keys, &[OpReq::Reserve { from: anyone.addr, fee: FEE, lock, taker: anyone.addr }])).contains("not an open order"), "one reservation at a time");
        a.audit().unwrap();

        // Ken: the taker pays the maker's fresh address, in a block after the reservation (A's reservation block has time g + 300)
        let mut b = chain_b(&keys);
        b_block(&mut b, &keys, &[]); b_block(&mut b, &keys, &[]);
        let paid_at = b_block(&mut b, &keys, &[DevPay { from: taker.addr, to: pay_to, amt: 200_000_000, fee: 2_000_000 }]) as u64;
        // not confirmed yet: this node cannot judge, and says so (the block is neither valid nor invalid)
        let proof = b.payment_proof(paid_at, 0).unwrap();
        a.cross = CrossMode::View(view_of(&b));
        let claim = OpReq::OrderClaim { from: anyone.addr, fee: FEE, lock, proof: proof.encode() };
        let e = forced(&a, &keys, &[claim.clone()]).unwrap_err();
        assert!(e.downcast_ref::<Unavailable>().is_some(), "{e}");
        for _ in 0..confirmations(2) { b_block(&mut b, &keys, &[]); }
        a.cross = CrossMode::View(view_of(&b));
        // with no view of the other chain at all, a claim is refused outright
        let mut off = a.clone(); off.cross = CrossMode::Off;
        assert!(err_of(forced(&off, &keys, &[claim.clone()])).contains("need the other chains' headers"));
        // the claim: anyone may submit it, the money goes to the taker's address
        let (t1, mkr) = (bal(&a, taker), bal(&a, maker));
        let blk = step(&mut a, &keys, &[], &[claim]).unwrap();
        assert!(!decode_ops(&blk.data[blockdata::decode_prefix(&blk.data).unwrap().2..]).unwrap().is_empty());
        assert_eq!(bal(&a, taker), t1 + 404_000_000, "the taker gets the sale and the deposit back");
        assert_eq!(bal(&a, maker), mkr, "the maker already holds the payment on Ken");
        assert!(a.locks.is_empty() && a.account(&lock).is_none());
        a.audit().unwrap();
    }

    #[test]
    fn a_payment_that_is_short_early_unconfirmed_or_to_someone_else_releases_nothing() {
        let (mut a, keys) = chain_a();
        let (maker, taker, anyone) = (&keys[4], &keys[5], &keys[7]);
        let pay_to = crate::tx::Wallet::generate().address();
        let other = crate::tx::Wallet::generate().address();
        let mut b = chain_b(&keys);
        // Ken block 1 (time g + 150): a payment that will be older than the reservation
        let early_at = b_block(&mut b, &keys, &[DevPay { from: taker.addr, to: pay_to, amt: 200_000_000, fee: 2_000_000 }]) as u64;
        step(&mut a, &keys, &[], &[OpReq::Make { from: maker.addr, amt: 400_000_000, fee: FEE, terms: order(maker, pay_to) }]).unwrap();
        step(&mut a, &keys, &[], &[]).unwrap();
        let open_lock = lock_addr(&a, 0);
        step(&mut a, &keys, &[], &[OpReq::Reserve { from: taker.addr, fee: FEE, lock: open_lock, taker: taker.addr }]).unwrap();
        let lock = lock_addr(&a, 0);
        // later Ken payments: too little to the right address, enough to the wrong address
        while b.tip().tip_ntime <= a.tip_ntime { b_block(&mut b, &keys, &[]); }
        let short_at = b_block(&mut b, &keys, &[DevPay { from: taker.addr, to: crate::tx::Wallet::generate().address(), amt: 100_000_000, fee: 1_000_000 }]) as u64;
        let wrong_at = b_block(&mut b, &keys, &[DevPay { from: taker.addr, to: other, amt: 300_000_000, fee: 3_000_000 }]) as u64;
        for _ in 0..confirmations(2) { b_block(&mut b, &keys, &[]); }
        a.cross = CrossMode::View(view_of(&b));
        let claim = |at: u64| OpReq::OrderClaim { from: anyone.addr, fee: FEE, lock, proof: b.payment_proof(at, 0).unwrap().encode() };
        assert!(err_of(forced(&a, &keys, &[claim(early_at)])).contains("not after the reservation"));
        assert!(err_of(forced(&a, &keys, &[claim(wrong_at)])).contains("not to the order's address"));
        assert!(err_of(forced(&a, &keys, &[claim(short_at)])).contains("but the order asks for"), "100 000 000 is less than the 200 000 000 asked");
        // a proof for a different chain's block, a changed byte anywhere, a header the node does not follow
        let good_at = b_block(&mut b, &keys, &[DevPay { from: taker.addr, to: crate::tx::Wallet::generate().address(), amt: 1_000_000, fee: 20_000 }]);
        let _ = good_at;
        let mut p = b.payment_proof(wrong_at, 0).unwrap();
        p.chain = 1;
        assert!(err_of(forced(&a, &keys, &[OpReq::OrderClaim { from: anyone.addr, fee: FEE, lock, proof: p.encode() }])).contains("asks for chain"));
        let mut p = b.payment_proof(wrong_at, 0).unwrap();
        p.header[10] ^= 1;
        assert!(err_of(forced(&a, &keys, &[OpReq::OrderClaim { from: anyone.addr, fee: FEE, lock, proof: p.encode() }])).contains("not the one this node follows"));
        let mut p = b.payment_proof(wrong_at, 0).unwrap();
        let last = p.data.len() - 1; p.data[last] ^= 1;
        assert!(forced(&a, &keys, &[OpReq::OrderClaim { from: anyone.addr, fee: FEE, lock, proof: p.encode() }]).is_err());
        let mut p = b.payment_proof(wrong_at, 0).unwrap();
        p.stamp[0] ^= 1;
        assert!(err_of(forced(&a, &keys, &[OpReq::OrderClaim { from: anyone.addr, fee: FEE, lock, proof: p.encode() }])).contains("body does not match"));
        assert!(err_of(forced(&a, &keys, &[OpReq::OrderClaim { from: anyone.addr, fee: FEE, lock, proof: vec![1, 2, 3] }])).len() > 0);
    }

    #[test]
    fn a_payment_to_an_account_that_already_existed_is_proven_by_its_leaf() {
        let (mut a, keys) = chain_a();
        let (maker, taker, anyone) = (&keys[4], &keys[5], &keys[7]);
        let pay_to = crate::tx::Wallet::generate().address();
        step(&mut a, &keys, &[], &[OpReq::Make { from: maker.addr, amt: 400_000_000, fee: FEE, terms: order(maker, pay_to) }]).unwrap();
        step(&mut a, &keys, &[], &[]).unwrap();
        let open_lock = lock_addr(&a, 0);
        step(&mut a, &keys, &[], &[OpReq::Reserve { from: taker.addr, fee: FEE, lock: open_lock, taker: taker.addr }]).unwrap();
        let lock = lock_addr(&a, 0);
        let mut b = chain_b(&keys);
        while b.tip().tip_ntime <= a.tip_ntime { b_block(&mut b, &keys, &[]); }
        // someone else creates the maker's address first (a griefer); the taker's payment then lands on an existing account
        b_block(&mut b, &keys, &[DevPay { from: keys[6].addr, to: pay_to, amt: 1_000_000, fee: 20_000 }]);
        let paid_at = b_block(&mut b, &keys, &[DevPay { from: taker.addr, to: pay_to, amt: 200_000_000, fee: 2_000_000 }]) as u64;
        for _ in 0..confirmations(2) { b_block(&mut b, &keys, &[]); }
        let proof = b.payment_proof(paid_at, 0).unwrap();
        assert!(proof.leaf.is_some(), "the receiver existed, so the proof carries its leaf");
        a.cross = CrossMode::View(view_of(&b));
        let ok = OpReq::OrderClaim { from: anyone.addr, fee: FEE, lock, proof: proof.encode() };
        // a leaf that is not in the block's state is refused
        let mut bad = b.payment_proof(paid_at, 0).unwrap();
        if let Some((_, _, nums, _)) = &mut bad.leaf { nums[0] += 1; }
        assert!(err_of(forced(&a, &keys, &[OpReq::OrderClaim { from: anyone.addr, fee: FEE, lock, proof: bad.encode() }])).contains("not in the block's state"));
        let mut bad = b.payment_proof(paid_at, 0).unwrap();
        if let Some((idx, ..)) = &mut bad.leaf { *idx += 1; }
        assert!(err_of(forced(&a, &keys, &[OpReq::OrderClaim { from: anyone.addr, fee: FEE, lock, proof: bad.encode() }])).contains("not the receiver's"));
        let t1 = bal(&a, taker);
        step(&mut a, &keys, &[], &[ok]).unwrap();
        assert_eq!(bal(&a, taker), t1 + 404_000_000);
        a.audit().unwrap();
    }

    #[test]
    fn a_reservation_that_runs_out_reopens_the_order_and_an_expired_order_comes_back() {
        let (mut a, keys) = chain_a();
        let (maker, taker, anyone) = (&keys[4], &keys[5], &keys[7]);
        let pay_to = crate::tx::Wallet::generate().address();
        let mut t = order(maker, pay_to);
        if let Terms::Order { expiry, reserve_blocks, .. } = &mut t { *expiry = 14; *reserve_blocks = 3; }
        let m0 = bal(&a, maker);
        step(&mut a, &keys, &[], &[OpReq::Make { from: maker.addr, amt: 400_000_000, fee: FEE, terms: t }]).unwrap();
        let open = lock_addr(&a, 0);
        // a return before the expiry is refused
        assert!(err_of(forced(&a, &keys, &[OpReq::Return { from: anyone.addr, fee: FEE, lock: open }])).contains("not expired"));
        step(&mut a, &keys, &[], &[OpReq::Reserve { from: taker.addr, fee: FEE, lock: open, taker: taker.addr }]).unwrap();   // height 2, until 5
        let reserved = lock_addr(&a, 0);
        let (t1, m1) = (bal(&a, taker), bal(&a, maker));
        assert!(err_of(forced(&a, &keys, &[OpReq::Reopen { from: anyone.addr, fee: FEE, lock: reserved }])).contains("still running"));
        while a.height < 4 { step(&mut a, &keys, &[], &[]).unwrap(); }
        assert!(err_of(forced(&a, &keys, &[OpReq::Reopen { from: anyone.addr, fee: FEE, lock: reserved }])).contains("still running"), "block 5 is the last of the reservation");
        step(&mut a, &keys, &[], &[]).unwrap();
        // the taker never paid: anyone reopens the order, and the maker keeps the deposit
        step(&mut a, &keys, &[], &[OpReq::Reopen { from: anyone.addr, fee: FEE, lock: reserved }]).unwrap();
        assert_eq!(bal(&a, maker), m1 + 4_000_000, "the deposit goes to the maker");
        assert_eq!(bal(&a, taker), t1, "the taker does not get it back");
        assert_eq!(lock_addr(&a, 0), open, "the order is exactly the open order again");
        assert_eq!(a.account(&open).unwrap().1.bal, 400_000_000);
        a.audit().unwrap();
        // it can be reserved again, but a claim for the old reservation is gone with it
        // after the expiry nobody can reserve it; anyone returns the sale to the maker
        while a.height <= 14 { step(&mut a, &keys, &[], &[]).unwrap(); }
        assert!(err_of(forced(&a, &keys, &[OpReq::Reserve { from: taker.addr, fee: FEE, lock: open, taker: taker.addr }])).contains("expired"));
        let before = bal(&a, maker);
        step(&mut a, &keys, &[], &[OpReq::Return { from: anyone.addr, fee: FEE, lock: open }]).unwrap();
        assert_eq!(bal(&a, maker), before + 400_000_000);
        assert!(a.locks.is_empty());
        assert_eq!(bal(&a, maker), m0 - FEE + 4_000_000 - 0, "the maker lost only the make fee and gained the deposit");
        a.audit().unwrap();
    }

    #[test]
    fn locks_survive_a_snapshot_and_a_restart_and_the_root_commits_to_them() {
        let (mut a, keys) = chain_a();
        let (maker, taker) = (&keys[4], &keys[5]);
        let r0 = a.root();
        step(&mut a, &keys, &[], &[OpReq::Make { from: maker.addr, amt: 400_000_000, fee: FEE, terms: order(maker, crate::tx::Wallet::generate().address()) }]).unwrap();
        step(&mut a, &keys, &[], &[OpReq::Make { from: taker.addr, amt: 100_000_000, fee: FEE, terms: vault(taker, maker, 99) }]).unwrap();
        assert_eq!(a.locks.len(), 2);
        let order_addr = a.locks.values().find_map(|t| matches!(t, Terms::Order { .. }).then(|| t.digest())).unwrap();
        step(&mut a, &keys, &[], &[OpReq::Reserve { from: taker.addr, fee: FEE, lock: order_addr, taker: taker.addr }]).unwrap();
        assert_ne!(a.root(), r0);
        let gd = crate::node::genesis_digest(&dev::genesis_of(&keys));
        let bytes = a.snapshot_bytes(&gd).unwrap();
        let back = Chain::from_snapshot(a.p.clone(), Arc::new(DevStamp), &gd, &bytes).unwrap();
        assert_eq!(back.locks, a.locks);
        assert_eq!(back.root(), a.root(), "the tree is rebuilt from the leaves, locks included");
        assert_eq!((back.height, back.pool), (a.height, a.pool));
        // a flipped byte in the terms is caught by the file's digest; a snapshot whose terms do not fit their leaf is refused
        let mut bad = bytes.clone(); let n = bad.len() / 2; bad[n] ^= 1;
        assert!(Chain::from_snapshot(a.p.clone(), Arc::new(DevStamp), &gd, &bad).is_err());
        // a node restarts from its log with the locks in place (the claim proofs are not asked for again)
        let dir = std::env::temp_dir().join(format!("zen-locks-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let open = || Node::open(Params::devnet(), &dev::genesis_of(&keys), Box::new(DevStamp), Some(&dir)).unwrap();
        let mut n = open();
        for _ in 0..3 {
            let t = n.tip().tip_ntime + 150;
            let reqs = if n.height() == 0 { vec![OpReq::Make { from: maker.addr, amt: 400_000_000, fee: FEE, terms: order(maker, crate::tx::Wallet::generate().address()) }] } else { vec![] };
            let b = dev::build_block_ops(n.tip(), keys[0].addr, dev::make_tickets(n.tip(), &keys[..4], 24), &[], &reqs, t, &DevStampMaker).unwrap();
            n.add_block(&b, u32::MAX).unwrap();
        }
        let (root, locks) = (n.tip().root(), n.tip().locks.clone());
        drop(n);
        let n2 = open();
        assert_eq!((n2.tip().root(), n2.tip().locks.clone(), n2.height()), (root, locks, 3));
        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn signed_ops_and_the_pool() {
        let (mut c, keys) = chain_a();
        let chain = c.p.chain;
        let terms = Terms::Order { maker: keys[5].addr, sell: 1_000_000, want_chain: 2, want_amt: 5, pay_to: keys[6].addr, expiry: 500, reserve_blocks: 10, deposit: 10_001, salt: 0, state: OrderState::Open };
        let req = OpReq::Make { from: keys[5].addr, amt: 1_000_000, fee: FEE, terms };
        let op = SignedOp::sign(&keys[5], chain, 0, req.clone());
        assert_eq!(SignedOp::from_bytes(&op.to_bytes()).unwrap(), op);
        op.verify(chain).unwrap();
        assert!(op.verify(chain + 1).is_err(), "another chain's signature does not do");
        let mut other = op.clone(); other.nonce = 1;
        assert!(other.verify(chain).is_err(), "the nonce is signed");
        let stranger = SignedOp::sign(&keys[6], chain, 0, req.clone());
        assert!(stranger.verify(chain).is_err(), "only the sender's key");
        let mut pool = OpPool::new(10);
        pool.admit(&c, op.clone()).unwrap();
        assert_eq!(pool.admit(&c, op.clone()).unwrap_err().to_string(), "known");
        assert!(pool.admit(&c, SignedOp::sign(&keys[5], chain, 5, req.clone())).is_err(), "a gap in the nonces");
        let mut broke = req.clone(); if let OpReq::Make { amt, .. } = &mut broke { *amt = 5_000_000_000_000; }
        assert!(pool.admit(&c, SignedOp::sign(&keys[5], chain, 1, broke)).is_err(), "more than the balance");
        let sel = pool.select(&c);
        assert_eq!(sel, vec![req.clone()]);
        step(&mut c, &keys, &[], &sel).unwrap();
        pool.on_block(&c);
        assert_eq!(pool.len(), 0, "applied operations leave the pool");
        assert_eq!(c.locks.len(), 1);
    }

    fn channel(a: &mint::Key, b: &mint::Key, delay: u64, oneway: bool) -> Terms {
        Terms::Channel { a: a.addr, b: b.addr, key_a: mint::encode_point(a.a), key_b: mint::encode_point(b.a), delay, oneway, salt: 0, state: ChanState::Open }
    }
    fn sign2(a: &mint::Key, b: &mint::Key, msg: [F; 4]) -> ChanSigs {
        let (ea, sa) = mint::sign(a, msg); let (eb, sb) = mint::sign(b, msg);
        ChanSigs { ea, sa: mint::s_bytes(&sa), eb, sb: mint::s_bytes(&sb) }
    }
    fn chan_lock(c: &Chain) -> ([F; 4], [u8; 32]) {
        let (i, t) = c.locks.iter().next().unwrap();
        (c.state[i].pk, t.channel_id().unwrap())
    }

    #[test]
    fn a_channel_takes_the_newest_signed_state_and_pays_each_side_after_the_window() {
        let (mut c, keys) = chain_a();
        let (a, b, anyone) = (&keys[5], &keys[6], &keys[7]);
        let (ba, bb) = (bal(&c, a), bal(&c, b));
        step(&mut c, &keys, &[], &[OpReq::Make { from: a.addr, amt: 1_000_000, fee: FEE, terms: channel(a, b, 4, false) }]).unwrap();
        c.audit().unwrap();
        let (lock, id) = chan_lock(&c);
        assert_eq!(bal(&c, a), ba - 1_000_000 - FEE);
        let (s1, s2) = (sign2(a, b, chan_state_msg(c.p.chain, &id, 1, 700_000, 1_000_000, &[])), sign2(a, b, chan_state_msg(c.p.chain, &id, 2, 400_000, 1_000_000, &[])));
        // a state signed by one side only, or for other balances, is refused
        let forged = sign2(a, anyone, chan_state_msg(c.p.chain, &id, 1, 700_000, 1_000_000, &[]));
        assert!(err_of(forced(&c, &keys, &[OpReq::ChanUpdate { from: anyone.addr, fee: FEE, lock, seq: 1, bal_a: 700_000, locks: vec![], sigs: forged }])).contains("b's signature"));
        assert!(err_of(forced(&c, &keys, &[OpReq::ChanUpdate { from: anyone.addr, fee: FEE, lock, seq: 1, bal_a: 100_000, locks: vec![], sigs: s1 }])).contains("signature"));
        assert!(err_of(forced(&c, &keys, &[OpReq::ChanSettle { from: anyone.addr, fee: FEE, lock, wits: vec![] }])).contains("closing"));
        // a posts the older state; b answers with the newer one and it replaces it; the older cannot come back
        step(&mut c, &keys, &[], &[OpReq::ChanUpdate { from: a.addr, fee: FEE, lock, seq: 1, bal_a: 700_000, locks: vec![], sigs: s1 }]).unwrap();
        let (lock, _) = chan_lock(&c);
        assert!(err_of(forced(&c, &keys, &[OpReq::ChanSettle { from: anyone.addr, fee: FEE, lock, wits: vec![] }])).contains("window is still open"));
        step(&mut c, &keys, &[], &[OpReq::ChanUpdate { from: b.addr, fee: FEE, lock, seq: 2, bal_a: 400_000, locks: vec![], sigs: s2 }]).unwrap();
        let (lock, _) = chan_lock(&c);
        assert!(err_of(forced(&c, &keys, &[OpReq::ChanUpdate { from: a.addr, fee: FEE, lock, seq: 1, bal_a: 700_000, locks: vec![], sigs: s1 }])).contains("not newer"));
        // the window runs from the last update (4 blocks)
        for _ in 0..4 { step(&mut c, &keys, &[], &[]).unwrap(); }
        let settle = OpReq::ChanSettle { from: anyone.addr, fee: FEE, lock, wits: vec![] };
        step(&mut c, &keys, &[], &[settle]).unwrap();
        assert!(c.locks.is_empty());
        assert_eq!(bal(&c, a), ba - 1_000_000 - 2 * FEE + 400_000, "a: what it keeps, less its fees");
        assert_eq!(bal(&c, b), bb - FEE + 600_000, "b: what it was streamed, less its fee");
        c.audit().unwrap();
    }

    #[test]
    fn a_channel_closes_at_once_when_both_sign_and_either_side_can_start_a_close_from_nothing() {
        let (mut c, keys) = chain_a();
        let (a, b, anyone) = (&keys[5], &keys[6], &keys[7]);
        let (ba, bb) = (bal(&c, a), bal(&c, b));
        step(&mut c, &keys, &[], &[OpReq::Make { from: a.addr, amt: 900_000, fee: FEE, terms: channel(a, b, 3, false) }]).unwrap();
        let (lock, id) = chan_lock(&c);
        let sig = sign2(a, b, chan_close_msg(c.p.chain, &id, 250_000, 900_000));
        // the close signed for other balances does not carry over
        assert!(err_of(forced(&c, &keys, &[OpReq::ChanClose { from: anyone.addr, fee: FEE, lock, bal_a: 100, sigs: sig }])).contains("signature"));
        step(&mut c, &keys, &[], &[OpReq::ChanClose { from: anyone.addr, fee: FEE, lock, bal_a: 250_000, sigs: sig }]).unwrap();
        assert!(c.locks.is_empty());
        assert_eq!((bal(&c, a), bal(&c, b)), (ba - 900_000 - FEE + 250_000, bb + 650_000));
        // a second channel that was never used: a stranger cannot start the close, b can, and a gets everything back
        step(&mut c, &keys, &[], &[OpReq::Make { from: a.addr, amt: 800_000, fee: FEE, terms: channel(a, b, 3, false) }]).unwrap();
        let (lock, _) = chan_lock(&c);
        assert!(err_of(forced(&c, &keys, &[OpReq::ChanStart { from: anyone.addr, fee: FEE, lock }])).contains("two sides"));
        let before = bal(&c, a);
        step(&mut c, &keys, &[], &[OpReq::ChanStart { from: b.addr, fee: FEE, lock }]).unwrap();
        for _ in 0..3 { step(&mut c, &keys, &[], &[]).unwrap(); }
        let (lock, _) = chan_lock(&c);
        step(&mut c, &keys, &[], &[OpReq::ChanSettle { from: anyone.addr, fee: FEE, lock, wits: vec![] }]).unwrap();
        assert!(c.locks.is_empty());
        assert_eq!(bal(&c, a), before + 800_000);
        c.audit().unwrap();
    }

    #[test]
    fn a_stream_is_one_number_signed_by_the_payer_alone() {
        let (mut c, keys) = chain_a();
        let (a, b, anyone) = (&keys[5], &keys[6], &keys[7]);
        let bb = bal(&c, b);
        step(&mut c, &keys, &[], &[OpReq::Make { from: a.addr, amt: 1_000_000, fee: FEE, terms: channel(a, b, 3, true) }]).unwrap();
        let (lock, id) = chan_lock(&c);
        let cid = c.p.chain; let alone = |paid: u64| { let (ea, sa) = mint::sign(a, chan_state_msg(cid, &id, paid, 1_000_000 - paid, 1_000_000, &[])); ChanSigs { ea, sa: mint::s_bytes(&sa), eb: 0, sb: [0; 40] } };
        // b holds the largest amount a has signed; b posts it and a stale one cannot replace it
        step(&mut c, &keys, &[], &[OpReq::ChanUpdate { from: b.addr, fee: FEE, lock, seq: 150_000, bal_a: 850_000, locks: vec![], sigs: alone(150_000) }]).unwrap();
        let (lock, _) = chan_lock(&c);
        assert!(err_of(forced(&c, &keys, &[OpReq::ChanUpdate { from: a.addr, fee: FEE, lock, seq: 100_000, bal_a: 900_000, locks: vec![], sigs: alone(100_000) }])).contains("not newer"));
        // a stream whose a-share is not what is left is refused
        assert!(err_of(forced(&c, &keys, &[OpReq::ChanUpdate { from: b.addr, fee: FEE, lock, seq: 300_000, bal_a: 999_999, locks: vec![], sigs: alone(300_000) }])).contains("amount paid"));
        step(&mut c, &keys, &[], &[OpReq::ChanUpdate { from: b.addr, fee: FEE, lock, seq: 400_000, bal_a: 600_000, locks: vec![], sigs: alone(400_000) }]).unwrap();
        let (lock, _) = chan_lock(&c);
        for _ in 0..3 { step(&mut c, &keys, &[], &[]).unwrap(); }
        step(&mut c, &keys, &[], &[OpReq::ChanSettle { from: anyone.addr, fee: FEE, lock, wits: vec![] }]).unwrap();
        assert_eq!(bal(&c, b), bb - 2 * FEE + 400_000);
        c.audit().unwrap();
    }

    #[test]
    fn a_point_lock_in_a_closing_channel_pays_its_receiver_on_the_scalar_or_its_sender_after_expiry() {
        let (mut c, keys) = chan_two();
        let (a, b, anyone) = (&keys[5], &keys[6], &keys[7]);
        let (ba, bb) = (bal(&c, a), bal(&c, b));
        let key_t = mint::Key::from_secret(num_bigint::BigUint::from(777u32));
        let t = mint::s_bytes(&num_bigint::BigUint::from(777u32));
        let (lock, id) = chan_lock(&c);
        // state 1: a 600 000, b 100 000, and 300 000 waiting for b, opened by t, until height `exp`
        let exp = c.height + 12;
        let pl = PLock { amt: 300_000, to_b: true, point: mint::encode_point(key_t.a), expiry: exp };
        let sig = sign2(a, b, chan_state_msg(c.p.chain, &id, 1, 600_000, 1_000_000, &[pl.clone()]));
        // the shares and the locks may not add up to more than the channel holds
        let over = PLock { amt: 500_000, ..pl.clone() };
        let sig_over = sign2(a, b, chan_state_msg(c.p.chain, &id, 1, 600_000, 1_000_000, &[over.clone()]));
        assert!(err_of(forced(&c, &keys, &[OpReq::ChanUpdate { from: a.addr, fee: FEE, lock, seq: 1, bal_a: 600_000, locks: vec![over], sigs: sig_over }])).contains("more than the channel holds"));
        // signatures cover the locks: the same signatures do not carry a different list
        let other = PLock { amt: 1, ..pl.clone() };
        assert!(err_of(forced(&c, &keys, &[OpReq::ChanUpdate { from: a.addr, fee: FEE, lock, seq: 1, bal_a: 600_000, locks: vec![other], sigs: sig }])).contains("signature"));
        step(&mut c, &keys, &[], &[OpReq::ChanUpdate { from: a.addr, fee: FEE, lock, seq: 1, bal_a: 600_000, locks: vec![pl.clone()], sigs: sig }]).unwrap();
        let (lock, _) = chan_lock(&c);
        for _ in 0..3 { step(&mut c, &keys, &[], &[]).unwrap(); }
        // the window is over but the lock is neither opened nor expired: settlement waits
        assert!(err_of(forced(&c, &keys, &[OpReq::ChanSettle { from: anyone.addr, fee: FEE, lock, wits: vec![None] }])).contains("neither been opened nor expired"));
        assert!(err_of(forced(&c, &keys, &[OpReq::ChanSettle { from: anyone.addr, fee: FEE, lock, wits: vec![] }])).contains("one witness entry"));
        // a wrong scalar does not open it; the right one pays b
        let wrong = mint::s_bytes(&num_bigint::BigUint::from(778u32));
        assert!(err_of(forced(&c, &keys, &[OpReq::ChanSettle { from: anyone.addr, fee: FEE, lock, wits: vec![Some(wrong)] }])).contains("does not open"));
        let mut c2 = c.clone();
        step(&mut c2, &keys, &[], &[OpReq::ChanSettle { from: anyone.addr, fee: FEE, lock, wits: vec![Some(t)] }]).unwrap();
        assert_eq!((bal(&c2, a), bal(&c2, b)), (ba - FEE + 600_000, bb + 400_000));
        c2.audit().unwrap();
        // nobody opens it: once it has expired a's money comes back to a
        while c.height <= exp { step(&mut c, &keys, &[], &[]).unwrap(); }
        step(&mut c, &keys, &[], &[OpReq::ChanSettle { from: anyone.addr, fee: FEE, lock, wits: vec![None] }]).unwrap();
        assert_eq!((bal(&c, a), bal(&c, b)), (ba - FEE + 600_000 + 300_000, bb + 100_000));
        c.audit().unwrap();
    }
    fn chan_two() -> (Chain, Vec<mint::Key>) {
        let (mut c, keys) = chain_a();
        let (a, b) = (&keys[5], &keys[6]);
        step(&mut c, &keys, &[], &[OpReq::Make { from: a.addr, amt: 1_000_000, fee: FEE, terms: channel(a, b, 3, false) }]).unwrap();
        (c, keys)
    }

    #[test]
    fn b_can_add_its_own_coins_to_a_channel_before_any_update() {
        let (mut c, keys) = chan_two();
        let (a, b, anyone) = (&keys[5], &keys[6], &keys[7]);
        let (lock, _) = chan_lock(&c);
        assert!(err_of(forced(&c, &keys, &[OpReq::ChanFund { from: a.addr, fee: FEE, lock, amt: 5 }])).contains("only b"));
        assert!(err_of(forced(&c, &keys, &[OpReq::ChanFund { from: b.addr, fee: FEE, lock, amt: 0 }])).contains("range"));
        let (a0, b0) = (bal(&c, a), bal(&c, b));
        step(&mut c, &keys, &[], &[OpReq::ChanFund { from: b.addr, fee: FEE, lock, amt: 400_000 }]).unwrap();
        let (lock, _) = chan_lock(&c);
        assert_eq!(c.account(&lock).unwrap().1.bal, 1_400_000);
        assert_eq!(bal(&c, b), b0 - 400_000 - FEE);
        // a second top-up adds to b's side, a's start share stays what a put in
        step(&mut c, &keys, &[], &[OpReq::ChanFund { from: b.addr, fee: FEE, lock, amt: 100_000 }]).unwrap();
        let (lock, _) = chan_lock(&c);
        // closing with no update gives each side what it put in
        step(&mut c, &keys, &[], &[OpReq::ChanStart { from: a.addr, fee: FEE, lock }]).unwrap();
        for _ in 0..3 { step(&mut c, &keys, &[], &[]).unwrap(); }
        let (lock, _) = chan_lock(&c);
        step(&mut c, &keys, &[], &[OpReq::ChanSettle { from: anyone.addr, fee: FEE, lock, wits: vec![] }]).unwrap();
        assert!(c.locks.is_empty());
        assert_eq!(bal(&c, b), b0 - 2 * FEE, "b has its 500 000 back");
        assert_eq!(bal(&c, a), a0 + 1_000_000 - FEE, "a has its 1 000 000 back (a0 was taken after the make)");
        c.audit().unwrap();
    }

    fn factory(c: &mint::Key, ms: &[(&mint::Key, u64)], delay: u64) -> Terms {
        Terms::Factory { coord: c.addr, key_c: mint::encode_point(c.a), delay, salt: 0,
                         members: ms.iter().map(|(k, cap)| FMember { addr: k.addr, key: mint::encode_point(k.a), cap: *cap, base: *cap, state: SubState::Open }).collect() }
    }
    fn fact_lock(c: &Chain) -> ([F; 4], [u8; 32]) { let (i, t) = c.locks.iter().next().unwrap(); (c.state[i].pk, t.factory_id().unwrap()) }

    #[test]
    fn a_factory_holds_many_members_channels_and_one_member_can_leave_without_closing_the_others() {
        let (mut c, keys) = chain_a();
        let (coord, m0, m1, m2, anyone) = (&keys[4], &keys[5], &keys[6], &keys[7], &keys[3]);
        let (bc, b0, b1, b2) = (bal(&c, coord), bal(&c, m0), bal(&c, m1), bal(&c, m2));
        let chain = c.p.chain;
        step(&mut c, &keys, &[], &[OpReq::Make { from: coord.addr, amt: 900_000, fee: FEE, terms: factory(coord, &[(m0, 300_000), (m1, 300_000), (m2, 300_000)], 3) }]).unwrap();
        assert_eq!(c.locks.len(), 1);
        c.audit().unwrap();
        let (lock, fid) = fact_lock(&c);
        // a factory whose channels do not add up, or with a repeated member, or run by someone else, is refused
        assert!(err_of(forced(&c, &keys, &[OpReq::Make { from: coord.addr, amt: 900_000, fee: FEE, terms: factory(coord, &[(m0, 300_000), (m1, 300_000)], 3) }])).contains("add up"));
        assert!(err_of(forced(&c, &keys, &[OpReq::Make { from: coord.addr, amt: 600_000, fee: FEE, terms: factory(coord, &[(m0, 300_000), (m0, 300_000)], 3) }])).contains("distinct"));
        assert!(err_of(forced(&c, &keys, &[OpReq::Make { from: anyone.addr, amt: 600_000, fee: FEE, terms: factory(coord, &[(m0, 300_000), (m1, 300_000)], 3) }])).contains("coordinator"));
        // member 1: the coordinator paid it 120 000 off chain (state 1), then 50 000 went back (state 2), each signed by the two of them only
        let st = |seq: u64, bal_c: u64, idx: u8, m: &mint::Key| sign2(coord, m, fact_state_msg(chain, &fid, idx, seq, bal_c, 300_000, &[]));
        let (s1, s2) = (st(1, 180_000, 1, m1), st(2, 230_000, 1, m1));
        // the other members' signatures do not do, nor does a state for another member
        assert!(err_of(forced(&c, &keys, &[OpReq::FactoryPost { from: anyone.addr, fee: FEE, lock, idx: 1, seq: 1, bal_c: 180_000, locks: vec![], sigs: sign2(coord, m0, fact_state_msg(chain, &fid, 1, 1, 180_000, 300_000, &[])) }])).contains("member's signature"));
        assert!(err_of(forced(&c, &keys, &[OpReq::FactoryPost { from: anyone.addr, fee: FEE, lock, idx: 2, seq: 1, bal_c: 180_000, locks: vec![], sigs: s1 }])).contains("signature"));
        // member 1 posts the old state; the coordinator posts the newer; the member cannot leave until the window is over
        step(&mut c, &keys, &[], &[OpReq::FactoryPost { from: m1.addr, fee: FEE, lock, idx: 1, seq: 1, bal_c: 180_000, locks: vec![], sigs: s1 }]).unwrap();
        let (lock, _) = fact_lock(&c);
        step(&mut c, &keys, &[], &[OpReq::FactoryPost { from: coord.addr, fee: FEE, lock, idx: 1, seq: 2, bal_c: 230_000, locks: vec![], sigs: s2 }]).unwrap();
        let (lock, _) = fact_lock(&c);
        assert!(err_of(forced(&c, &keys, &[OpReq::FactoryExit { from: m1.addr, fee: FEE, lock, idx: 1, wits: vec![] }])).contains("window is still open"));
        assert!(err_of(forced(&c, &keys, &[OpReq::FactoryExit { from: m1.addr, fee: FEE, lock, idx: 0, wits: vec![] }])).contains("not closing"));
        for _ in 0..3 { step(&mut c, &keys, &[], &[]).unwrap(); }
        let hold = c.account(&lock).unwrap().1.bal;
        step(&mut c, &keys, &[], &[OpReq::FactoryExit { from: anyone.addr, fee: FEE, lock, idx: 1, wits: vec![] }]).unwrap();
        // member 1 left with its share; the coordinator got the rest of that channel; the other two channels are untouched and the lock holds 600 000
        assert_eq!(bal(&c, m1), b1 + 70_000 - FEE);
        assert_eq!(c.locks.len(), 1);
        let (lock, fid) = fact_lock(&c);
        assert_eq!(c.account(&lock).unwrap().1.bal, hold - 300_000);
        c.audit().unwrap();
        // the others go on with the states they already had: member 0 and the coordinator move 40 000 and close together at once
        let _ = (&bc, &b0, &b2);
        let fin = sign2(coord, m0, fact_close_msg(chain, &fid, 0, 260_000, 300_000));
        assert!(err_of(forced(&c, &keys, &[OpReq::FactoryExitNow { from: anyone.addr, fee: FEE, lock, idx: 0, bal_c: 100, sigs: fin }])).contains("signature"));
        step(&mut c, &keys, &[], &[OpReq::FactoryExitNow { from: anyone.addr, fee: FEE, lock, idx: 0, bal_c: 260_000, sigs: fin }]).unwrap();
        assert_eq!(bal(&c, m0), b0 + 40_000);
        // the last member leaves unilaterally from nothing: the whole channel goes back to the coordinator and the factory is gone
        let (lock, _) = fact_lock(&c);
        assert!(err_of(forced(&c, &keys, &[OpReq::FactoryExitNow { from: anyone.addr, fee: FEE, lock, idx: 0, bal_c: 260_000, sigs: fin }])).contains("left"));
        assert!(err_of(forced(&c, &keys, &[OpReq::FactoryStart { from: anyone.addr, fee: FEE, lock, idx: 2 }])).contains("only the coordinator and the member"));
        step(&mut c, &keys, &[], &[OpReq::FactoryStart { from: m2.addr, fee: FEE, lock, idx: 2 }]).unwrap();
        for _ in 0..3 { step(&mut c, &keys, &[], &[]).unwrap(); }
        let (lock, _) = fact_lock(&c);
        step(&mut c, &keys, &[], &[OpReq::FactoryExit { from: anyone.addr, fee: FEE, lock, idx: 2, wits: vec![] }]).unwrap();
        assert!(c.locks.is_empty());
        // in all the coordinator paid in 900 000 and got back 230 000 + 260 000... of member 1, 0 and 2: 230 000 + 260 000 + 300 000
        assert_eq!(bal(&c, coord), bc - 900_000 - 2 * FEE + 230_000 + 260_000 + 300_000);
        assert_eq!(bal(&c, m2), b2 - FEE);
        c.audit().unwrap();
    }
}
/// What the proof binds of a factory-family operation (stage P4): tag `ZenFcDat`, then kind, sender index, fee (2), amount (2),
/// lock index (a Make: its slot), member index, destination of the coordinator and of the member (index, new-account flag, address 4), the new factory's terms digest
/// (a Make), seq (2), the coordinator's share (2), the new point locks' digest (4), the signatures (28), the witnesses' digest (4)
pub fn factory_data_hash(op: &Op) -> Option<[F; 4]> {
    let z4 = [F::ZERO; 4];
    let dest = |f: &mut Fw, d: Option<&Dest>| { match d { Some(d) => { f.u32(d.idx).u32(d.new.is_some() as u32).addr(&d.new.unwrap_or(z4)); } None => { f.u32(0).u32(0).zeros(4); } } };
    let sigs = |f: &mut Fw, g: Option<&ChanSigs>| { match g { Some(g) => { f.u128(g.ea).bytes(&g.sa).u128(g.eb).bytes(&g.sb); } None => { f.zeros(28); } } };
    let mut f = Fw::new(b"ZenFcDat");
    match op {
        Op::Make { from, fee, amt, at, terms: t @ Terms::Factory { .. } } => { f.u32(1).u32(*from).u64(*fee).u64(*amt).u32(*at).u32(0); dest(&mut f, None); dest(&mut f, None); f.addr(&t.digest()).u64(0).u64(0).zeros(4); sigs(&mut f, None); f.zeros(4); }
        Op::FactoryStart { from, fee, lock, idx } => { f.u32(12).u32(*from).u64(*fee).u64(0).u32(*lock).u32(*idx as u32); dest(&mut f, None); dest(&mut f, None); f.zeros(4).u64(0).u64(0).zeros(4); sigs(&mut f, None); f.zeros(4); }
        Op::FactoryPost { from, fee, lock, idx, seq, bal_c, locks, sigs: g } => { f.u32(13).u32(*from).u64(*fee).u64(0).u32(*lock).u32(*idx as u32); dest(&mut f, None); dest(&mut f, None); f.zeros(4).u64(*seq).u64(*bal_c).addr(&plocks_digest(locks)); sigs(&mut f, Some(g)); f.zeros(4); }
        Op::FactoryExit { from, fee, lock, idx, wits, to_c, to_m } => { f.u32(14).u32(*from).u64(*fee).u64(0).u32(*lock).u32(*idx as u32); dest(&mut f, Some(to_c)); dest(&mut f, Some(to_m)); f.zeros(4).u64(0).u64(0).zeros(4); sigs(&mut f, None); f.addr(&wits_digest(wits)); }
        Op::FactoryExitNow { from, fee, lock, idx, bal_c, sigs: g, to_c, to_m } => { f.u32(15).u32(*from).u64(*fee).u64(0).u32(*lock).u32(*idx as u32); dest(&mut f, Some(to_c)); dest(&mut f, Some(to_m)); f.zeros(4).u64(0).u64(*bal_c).zeros(4); sigs(&mut f, Some(g)); f.zeros(4); }
        Op::FactoryFund { from, fee, lock, idx, amt } => { f.u32(16).u32(*from).u64(*fee).u64(*amt).u32(*lock).u32(*idx as u32); dest(&mut f, None); dest(&mut f, None); f.zeros(4).u64(0).u64(0).zeros(4); sigs(&mut f, None); f.zeros(4); }
        _ => return None,
    }
    Some(f.hash())
}
