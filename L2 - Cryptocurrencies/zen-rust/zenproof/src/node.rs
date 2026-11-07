// Zen node, stage 1: the consensus core (Justus L. Ludovic).
//
// What a node does with a block, in the order of cost (cheap checks first):
//   1. structure and size limits
//   2. the SEAL (80-byte Bitcoin header, SHA256d): previous block, difficulty bits, coinbase for this chain and
//      height, commitment to the minted block (pubvalues, stamp, block data, tickets), hash below the target
//   3. the TICKETS: each one's key, signature, Argon2id work and difficulty; one per (address, nonce); enough work
//   4. the BLOCK DATA, replayed on the node's own state with the circuit's rules (blockdata::replay), with the
//      payout list the consensus rules owe (rewards from block h-2, prover shares, miner cut, fee pool)
//   5. the STAMP: the replay's public values must equal the block's, and the stamp must verify them
//   6. only then is the state changed: new accounts and tree, fee pool, rewards owed from this block (paid in
//      block h+2), blow difficulty, work average, seal difficulty window, tip.
//
// A block that fails any step changes nothing (`validate` takes &self; `commit` applies the result).
//
// Stage 1 is deliberately small: one linear chain, no network, no fork choice, a fixed S, a flat reward split.
// The stamp check is pluggable (`StampVerifier`): the devnet uses `DevStamp`, which is NOT a proof; the real
// verifiers (Plonky2 stamp, Groth16 for the on-chain form) plug in behind the same trait.
// Not here yet (stage 2 and later): peer-to-peer, fork choice and reorgs, mempool, the reward curve with its random
// factor, the reading of S from payments, wallets, Stratum server, stamp verification against the real circuit.
use crate::blockdata::{self, BlockEntry, LeafData, PayoutRule, Replayed};
use crate::mint::{self, Ticket};
use crate::seal::{self, Header};
use crate::{ec, Acct, Tree, DEPTH, F};
use anyhow::{anyhow, bail, Result};
use plonky2::field::types::{Field, PrimeField64};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::Arc;

pub const SLOTS_PER_LEAF: usize = 16;
pub const MAX_STAMP: usize = 1 << 20;
pub const MAX_DATA: usize = 2 << 20;
pub const MAX_COINBASE: usize = 18 + seal::MAX_EXTRANONCE + 32;
pub const PUBVALUES: usize = 16;
const BLOCK_MAGIC: &[u8; 8] = b"ZenBlk01";

// ---------------------------------------------------------------- addresses
pub fn addr_bytes(a: &[F; 4]) -> [u8; 32] {
    let mut o = [0u8; 32];
    for (i, x) in a.iter().enumerate() { o[8 * i..8 * i + 8].copy_from_slice(&x.to_canonical_u64().to_le_bytes()); }
    o
}
pub fn addr_from(b: &[u8; 32]) -> Result<[F; 4]> {
    let mut a = [F::ZERO; 4];
    for i in 0..4 {
        let w = u64::from_le_bytes(b[8 * i..8 * i + 8].try_into()?);
        if w >= <F as plonky2::field::types::Field64>::ORDER { bail!("non-canonical address"); }
        a[i] = F::from_canonical_u64(w);
    }
    Ok(a)
}
fn akey(a: &[F; 4]) -> [u64; 4] { a.map(|x| x.to_canonical_u64()) }

// ---------------------------------------------------------------- parameters and the stamp check
#[derive(Clone, Debug)]
pub struct Params {
    pub chain: u8,
    /// base units per coin, a public value of every block (stage 1: fixed; later read from payments)
    pub s: u64,
    pub bits0: u32,
    pub blow_diff0: u64,
    pub max_tickets: usize,
    /// seal difficulty adjusts every `window` blocks toward `block_secs` per block, by at most x2 either way
    pub window: u64,
    pub block_secs: u64,
    pub genesis_time: u32,
    /// blocks a reward waits after the block that would have paid it (`MATURITY_BLOCKS` on the real chains): a reorg then can never take back coins
    /// somebody already spent; the held coins sit in `pending`, which the supply audit counts
    pub maturity: u64,
    /// how S is read from payments (stage 5)
    pub read: crate::reading::ReadParams,
}
impl Params {
    pub fn devnet() -> Self {
        Params { chain: 3, s: 1000, bits0: 0x1f00_ffff, blow_diff0: 1,
                 max_tickets: 4 * mint::TARGET_BLOWS as usize, window: 32, block_secs: 150, genesis_time: 1_700_000_000,
                 maturity: 0,
                 read: crate::reading::ReadParams { std_fee_pm: 10, cap_bp: 0, min_obs: 5 } }
    }
}

/// Checks that a stamp proves a block's public values.
pub trait StampVerifier { fn verify(&self, pubvalues: &[u64], stamp: &[u8]) -> Result<()>; }
/// Makes the stamp for a block the builder has arranged (the leaves) and replayed (the public values).
pub trait StampMaker: Send + Sync {
    fn stamp(&self, pre: &Chain, height: u64, leaves: &[LeafData], ops: &[crate::locks::Op], ntime: u32, pubvalues: &[u64]) -> Result<Vec<u8>>;
    /// whether the stamp can cover this operation (real proofs carry the vault family so far (stage P2), the stand-in everything)
    fn accepts(&self, _req: &crate::locks::OpReq) -> bool { true }
}
/// Devnet stand-in: the "stamp" is a hash of the public values. NOT A PROOF; it only keeps the pipeline honest
/// about which bytes must travel with a block.
pub struct DevStamp;
impl DevStamp {
    pub fn make(pubvalues: &[u64]) -> Vec<u8> {
        let mut h = Sha256::new(); h.update(b"Zen-dev-stamp");
        for v in pubvalues { h.update(v.to_le_bytes()); }
        h.finalize().to_vec()
    }
}
pub struct DevStampMaker;
impl StampMaker for DevStampMaker {
    fn stamp(&self, _pre: &Chain, _h: u64, _leaves: &[LeafData], _ops: &[crate::locks::Op], _ntime: u32, pubvalues: &[u64]) -> Result<Vec<u8>> { Ok(DevStamp::make(pubvalues)) }
}
impl StampVerifier for DevStamp {
    fn verify(&self, pubvalues: &[u64], stamp: &[u8]) -> Result<()> {
        if stamp != DevStamp::make(pubvalues).as_slice() { bail!("stamp does not match the public values"); }
        Ok(())
    }
}

// ---------------------------------------------------------------- the block
#[derive(Clone, Debug)]
pub struct Block { pub header: Header, pub coinbase: Vec<u8>, pub pubvalues: Vec<u64>, pub stamp: Vec<u8>, pub data: Vec<u8>, pub tickets: Vec<Ticket> }

pub fn tickets_root(ts: &[Ticket]) -> [u8; 32] {
    let mut h = Sha256::new(); h.update(b"Zen-tickets-v1");
    for t in ts { h.update(t.to_bytes()); }
    h.finalize().into()
}
pub fn coinbase_for(chain: u8, h: u64, extranonce: &[u8], miner: &[F; 4]) -> Vec<u8> {
    let mut v = seal::coinb1(chain, h, extranonce.len());
    v.extend(extranonce); v.extend(seal::coinb2(&addr_bytes(miner)));
    v
}
impl Block {
    /// a sealed block from a template and a Stratum share (the pool's extranonce1, the miner's extranonce2, ntime, nonce, version)
    pub fn with_share(&self, chain: u8, en1: &[u8], share: &seal::Share) -> Result<Block> {
        let cb0 = seal::parse_coinbase(&self.coinbase)?;
        let mut en = en1.to_vec(); en.extend(&share.extranonce2);
        let coinbase = coinbase_for(chain, cb0.height, &en, &addr_from(&cb0.miner)?);
        let header = Header { version: share.version, prev: self.header.prev, commitment: seal::merkle_root(&coinbase, &[self.body_root()]),
                              ntime: share.ntime, nbits: self.header.nbits, nonce: share.nonce };
        Ok(Block { header, coinbase, ..self.clone() })
    }
    pub fn body_root(&self) -> [u8; 32] { seal::body_root(&self.pubvalues, &self.stamp, &self.data, &tickets_root(&self.tickets)) }
    pub fn hash(&self) -> [u8; 32] { self.header.hash() }
    pub fn encode(&self) -> Vec<u8> {
        let mut v = BLOCK_MAGIC.to_vec();
        v.extend(self.header.bytes());
        v.extend((self.coinbase.len() as u16).to_le_bytes()); v.extend(&self.coinbase);
        v.push(self.pubvalues.len() as u8); for x in &self.pubvalues { v.extend(x.to_le_bytes()); }
        v.extend((self.stamp.len() as u32).to_le_bytes()); v.extend(&self.stamp);
        v.extend((self.data.len() as u32).to_le_bytes()); v.extend(&self.data);
        v.extend((self.tickets.len() as u16).to_le_bytes()); for t in &self.tickets { v.extend(t.to_bytes()); }
        v
    }
    pub fn decode(b: &[u8]) -> Result<Block> {
        let mut p = 0usize;
        let mut take = |n: usize| -> Result<&[u8]> { let s = b.get(p..p + n).ok_or_else(|| anyhow!("truncated block"))?; p += n; Ok(s) };
        if take(8)? != BLOCK_MAGIC { bail!("not a Zen block"); }
        let h = take(80)?;
        let header = Header { version: u32::from_le_bytes(h[0..4].try_into()?), prev: h[4..36].try_into()?, commitment: h[36..68].try_into()?,
                              ntime: u32::from_le_bytes(h[68..72].try_into()?), nbits: u32::from_le_bytes(h[72..76].try_into()?), nonce: u32::from_le_bytes(h[76..80].try_into()?) };
        let cl = u16::from_le_bytes(take(2)?.try_into()?) as usize;
        if cl > MAX_COINBASE { bail!("coinbase too long"); }
        let coinbase = take(cl)?.to_vec();
        let np = take(1)?[0] as usize;
        if np != PUBVALUES { bail!("wrong number of public values"); }
        let mut pubvalues = vec![]; for _ in 0..np { pubvalues.push(u64::from_le_bytes(take(8)?.try_into()?)); }
        let sl = u32::from_le_bytes(take(4)?.try_into()?) as usize;
        if sl > MAX_STAMP { bail!("stamp too large"); }
        let stamp = take(sl)?.to_vec();
        let dl = u32::from_le_bytes(take(4)?.try_into()?) as usize;
        if dl > MAX_DATA { bail!("block data too large"); }
        let data = take(dl)?.to_vec();
        let nt = u16::from_le_bytes(take(2)?.try_into()?) as usize;
        if nt > 1024 { bail!("too many tickets"); }
        let mut tickets = vec![]; for _ in 0..nt { tickets.push(Ticket::from_bytes(take(mint::TICKET_BYTES)?)?); }
        if p != b.len() { bail!("trailing bytes after the block"); }
        Ok(Block { header, coinbase, pubvalues, stamp, data, tickets })
    }
}

// ---------------------------------------------------------------- the chain
#[derive(Clone)]
pub struct Chain {
    pub p: Params,
    pub height: u64,
    pub tip: [u8; 32],
    pub tip_ntime: u32,
    pub state: HashMap<u64, Acct>,
    pub tree: Tree,
    pub pool: u64,
    /// rewards owed, by the height of the block that pays them
    pub pending: BTreeMap<u64, Vec<([F; 4], u64)>>,
    pub blow_diff: u64,
    pub work_ema: u64,
    pub bits: u32,
    win_start: u32,
    win_n: u64,
    pub genesis_supply: u64,
    pub emitted: u64,
    /// chainwork: the sum of each block's weight (seal work x its tickets over the recent average, capped at 2)
    pub total_work: u128,
    pub blows_ema: u64,
    /// S and everything it is read from
    pub reading: crate::reading::Reading,
    /// the last block's height, miner and minters: its reward is worked out when the next block's seal is known
    last: Option<(u64, [F; 4], Vec<[F; 4]>)>,
    /// address -> account index (rebuilt when a block is committed)
    idx: HashMap<[u64; 4], u64>,
    verifier: Arc<dyn StampVerifier + Send + Sync>,
    log: Option<Arc<crate::store::Store>>,
    /// locks and orders (locks.rs): index -> terms; the leaf of each is in `state`
    pub locks: crate::locks::LockTable,
    /// filled orders, newest last (a view over the blocks, see market.rs)
    pub fills: Vec<crate::market::Fill>,
    /// how an order claim's proof from another chain is judged
    pub cross: crate::locks::CrossMode,
}

/// expected hashes to meet a target (Bitcoin's chainwork)
pub fn work_of_bits(bits: u32) -> u128 {
    let t = seal::bits_to_target(bits).unwrap();
    let w = (num_bigint::BigUint::from(1u8) << 256u32) / (t + 1u32);
    u128::try_from(&w).unwrap_or(u128::MAX)
}

/// seal difficulty after a window that took `span` seconds: the target moves in proportion, by at most x2 either way,
/// and never above the starting target
pub fn retarget_bits(p: &Params, bits: u32, span: u64) -> u32 {
    let expected = p.window * p.block_secs;
    let span = span.clamp(expected / 2, expected * 2);
    let max = seal::bits_to_target(p.bits0).unwrap();
    let t = seal::bits_to_target(bits).unwrap() * num_bigint::BigUint::from(span) / num_bigint::BigUint::from(expected);
    seal::target_to_bits(&t.min(max))
}

/// what a valid block does to the chain (computed without changing it)
pub struct Applied { pub rp: Replayed, pub miner: [F; 4], pub minters: Vec<[F; 4]>, pub work: u64, pub hash: [u8; 32] }

/// where a new account goes: the address picks a starting index and probes for a free one
pub fn free_index(taken: &dyn Fn(u64) -> bool, addr: &[F; 4]) -> u64 {
    let mask = (1u64 << DEPTH) - 1;
    let mut i = addr[0].to_canonical_u64().wrapping_mul(0x9E37_79B9_7F4A_7C15) >> 20 & mask;
    while taken(i) { i = (i + 1) & mask; }
    i
}
fn dummy_acct(pk: [F; 4], bal: u64) -> Acct {
    Acct { pk, bal, nonce: 0, rest: bal, used: 0, fd: 0, rd: 0, up: 0, a: ec::P { x: ec::E::ZERO, y: ec::E::ZERO }, k: [0; 4] }
}
pub fn genesis_hash(chain: u8) -> [u8; 32] { Sha256::digest([b"Zen-genesis-v1".as_slice(), &[chain]].concat()).into() }

const SNAP_MAGIC: &[u8; 8] = b"ZENSNAP2";

impl Chain {
    /// a new chain from a genesis allocation; with a directory, blocks are appended to `<dir>/blocks.log` and
    /// replayed (fully validated) when the directory already has a log
    pub fn open(p: Params, genesis: &[([F; 4], u64)], verifier: Box<dyn StampVerifier + Send + Sync>, dir: Option<&Path>) -> Result<Chain> {
        let mut state: HashMap<u64, Acct> = HashMap::new();
        let mut tree = Tree::new();
        let mut supply = 0u64;
        for (a, bal) in genesis {
            if state.values().any(|x| x.pk == *a) { bail!("duplicate genesis address"); }
            let i = free_index(&|i| state.contains_key(&i), a);
            let acct = dummy_acct(*a, *bal);
            tree.set(i, crate::leaf_hash(&acct)); state.insert(i, acct); supply += bal;
        }
        let bits = p.bits0;
        let mut c = Chain { height: 0, tip: genesis_hash(p.chain), tip_ntime: p.genesis_time, state, tree, pool: 0, pending: BTreeMap::new(),
                            blow_diff: p.blow_diff0, work_ema: 0, bits, win_start: p.genesis_time, win_n: 0, genesis_supply: supply, emitted: 0,
                            total_work: 0, blows_ema: mint::TARGET_BLOWS, verifier: Arc::from(verifier), log: None, reading: crate::reading::Reading::new(p.read.clone(), p.s), last: None, idx: HashMap::new(), locks: HashMap::new(), fills: vec![], cross: crate::locks::CrossMode::Off, p };
        c.idx = c.state.iter().map(|(i, a)| (akey(&a.pk), *i)).collect();
        if let Some(d) = dir {
            let store = crate::store::Store::open(d, false)?;
            for i in 0..store.len() {
                let blk = Block::decode(&store.read(store.record(i).unwrap())?)?;
                c.accept(&blk, u32::MAX)?;
            }
            c.log = Some(Arc::new(store));
        }
        Ok(c)
    }


    // ------------------------------------------------------------ snapshots
    /// the part of a snapshot that says which chain it belongs to: parameters, genesis allocation
    pub(crate) fn snap_binding(p: &Params, gd: &[u8; 32]) -> Vec<u8> {
        let mut w = crate::store::Wr::new();
        w.u8(p.chain); w.u64(p.s); w.u32(p.bits0); w.u64(p.blow_diff0); w.u64(p.max_tickets as u64); w.u64(p.window); w.u64(p.block_secs);
        w.u32(p.genesis_time); w.u64(p.maturity); w.u64(p.read.std_fee_pm); w.u64(p.read.cap_bp); w.u64(p.read.min_obs);
        w.raw(gd);
        w.0
    }
    /// the chain as it stands, as bytes: `gd` is the digest of the genesis allocation. Fails when an account carries circuit-only data the node does
    /// not keep (it never does).
    pub fn snapshot_bytes(&self, gd: &[u8; 32]) -> Result<Vec<u8>> {
        use crate::store::Wr;
        let mut w = Wr::new();
        w.raw(SNAP_MAGIC);
        w.raw(&Chain::snap_binding(&self.p, gd));
        w.u64(self.height); w.raw(&self.tip); w.u32(self.tip_ntime); w.u64(self.pool);
        w.u64(self.blow_diff); w.u64(self.work_ema); w.u32(self.bits); w.u32(self.win_start); w.u64(self.win_n);
        w.u64(self.genesis_supply); w.u64(self.emitted); w.u128(self.total_work); w.u64(self.blows_ema);
        let mut accts: Vec<(&u64, &Acct)> = self.state.iter().collect();
        accts.sort_by_key(|(i, _)| **i);
        w.u64(accts.len() as u64);
        for (i, a) in accts {
            if a.a.x != ec::E::ZERO || a.a.y != ec::E::ZERO || a.k != [0; 4] { bail!("an account carries data a snapshot does not hold"); }
            w.u64(*i);
            for x in a.pk { w.u64(x.to_canonical_u64()); }
            for x in [a.bal, a.nonce, a.rest, a.used, a.fd, a.rd, a.up] { w.u64(x); }
        }
        let mut locks: Vec<(&u64, &crate::locks::Terms)> = self.locks.iter().collect();
        locks.sort_by_key(|(i, _)| **i);
        w.u64(locks.len() as u64);
        for (i, t) in locks { w.u64(*i); let b = t.encode(); w.u32(b.len() as u32); w.raw(&b); }
        w.u64(self.pending.len() as u64);
        for (h, v) in &self.pending {
            w.u64(*h); w.u64(v.len() as u64);
            for (a, x) in v { for l in a { w.u64(l.to_canonical_u64()); } w.u64(*x); }
        }
        match &self.last {
            None => w.u8(0),
            Some((h, m, ms)) => {
                w.u8(1); w.u64(*h);
                for l in m { w.u64(l.to_canonical_u64()); }
                w.u64(ms.len() as u64);
                for a in ms { for l in a { w.u64(l.to_canonical_u64()); } }
            }
        }
        self.reading.encode(&mut w);
        let digest: [u8; 32] = Sha256::digest(&w.0).into();
        w.raw(&digest);
        Ok(w.0)
    }
    /// the chain a snapshot describes. Checks the file's own digest, that it belongs to this chain (parameters and genesis), that every number is in range, that
    /// the supply adds up, and rebuilds the tree from the accounts (the caller compares its root with the block at that height).
    pub fn from_snapshot(p: Params, verifier: Arc<dyn StampVerifier + Send + Sync>, gd: &[u8; 32], bytes: &[u8]) -> Result<Chain> {
        use crate::store::Rd;
        if bytes.len() < 8 + 32 { bail!("snapshot too short"); }
        let (body, digest) = bytes.split_at(bytes.len() - 32);
        if Sha256::digest(body).as_slice() != digest { bail!("snapshot digest differs"); }
        let mut r = Rd::new(body);
        if r.take(8)? != SNAP_MAGIC { bail!("not a snapshot"); }
        let binding = Chain::snap_binding(&p, gd);
        if r.take(binding.len())? != binding.as_slice() { bail!("the snapshot belongs to another chain or other parameters"); }
        let height = r.u64()?; let tip: [u8; 32] = r.take(32)?.try_into()?; let tip_ntime = r.u32()?; let pool = r.u64()?;
        let blow_diff = r.u64()?; let work_ema = r.u64()?; let bits = r.u32()?; let win_start = r.u32()?; let win_n = r.u64()?;
        let genesis_supply = r.u64()?; let emitted = r.u64()?; let total_work = r.u128()?; let blows_ema = r.u64()?;
        if win_n >= p.window { bail!("window position out of range"); }
        seal::bits_to_target(bits).map_err(|_| anyhow!("bad difficulty bits"))?;
        let fe = |r: &mut Rd| -> Result<F> { let x = r.u64()?; if x >= <F as plonky2::field::types::Field64>::ORDER { bail!("field element out of range"); } Ok(F::from_canonical_u64(x)) };
        let f4 = |r: &mut Rd| -> Result<[F; 4]> { Ok([fe(r)?, fe(r)?, fe(r)?, fe(r)?]) };
        let n = r.count(12 * 8)?;
        let mut state = HashMap::new();
        let mut tree = Tree::new();
        let mask = (1u64 << DEPTH) - 1;
        let mut prev_i: Option<u64> = None;
        for _ in 0..n {
            let i = r.u64()?;
            if i > mask || prev_i.is_some_and(|q| i <= q) { bail!("account indices out of order"); }
            prev_i = Some(i);
            let pk = f4(&mut r)?;
            let (bal, nonce, rest, used, fd, rd, up) = (r.u64()?, r.u64()?, r.u64()?, r.u64()?, r.u64()?, r.u64()?, r.u64()?);
            if bal >= 1 << 62 || rest > bal || used > rest { bail!("account numbers out of range"); }
            let a = Acct { pk, bal, nonce, rest, used, fd, rd, up, a: ec::P { x: ec::E::ZERO, y: ec::E::ZERO }, k: [0; 4] };
            tree.set(i, crate::leaf_hash(&a));
            state.insert(i, a);
        }
        let n = r.count(12)?;
        let mut locks: crate::locks::LockTable = HashMap::new();
        for _ in 0..n {
            let i = r.u64()?; let len = r.u32()? as usize;
            if len > crate::locks::MAX_TERMS { bail!("lock terms too long"); }
            let mut tr = Rd::new(r.take(len)?);
            let t = crate::locks::Terms::decode_from(&mut tr)?; tr.done()?;
            let a = state.get(&i).ok_or_else(|| anyhow!("a lock without a leaf"))?;
            if a.pk != t.digest() { bail!("a lock's terms do not match its leaf"); }
            if let Some(b) = t.balance() { if a.bal != b { bail!("an order's balance does not match its terms"); } }
            if locks.insert(i, t).is_some() { bail!("a lock twice"); }
        }
        let n = r.count(16)?;
        let mut pending = BTreeMap::new();
        for _ in 0..n {
            let h = r.u64()?; let m = r.count(40)?;
            let mut v = vec![];
            for _ in 0..m { let a = f4(&mut r)?; v.push((a, r.u64()?)); }
            if pending.insert(h, v).is_some() { bail!("a payout height twice"); }
        }
        let last = match r.u8()? {
            0 => None,
            1 => { let h = r.u64()?; let m = f4(&mut r)?; let k = r.count(32)?; let mut ms = vec![]; for _ in 0..k { ms.push(f4(&mut r)?); } Some((h, m, ms)) }
            _ => bail!("bad flag"),
        };
        let reading = crate::reading::Reading::decode(&mut r, &p.read)?;
        r.done()?;
        let idx = state.iter().map(|(i, a)| (akey(&a.pk), *i)).collect::<HashMap<_, _>>();
        if idx.len() != state.len() { bail!("an address twice"); }
        let c = Chain { height, tip, tip_ntime, state, tree, pool, pending, blow_diff, work_ema, bits, win_start, win_n, genesis_supply, emitted, total_work, blows_ema,
                        reading, last, idx, verifier, log: None, locks, fills: vec![], cross: crate::locks::CrossMode::Off, p };
        c.audit()?;
        Ok(c)
    }

    /// everything a node checks, in order of cost; changes nothing
    pub fn validate(&self, blk: &Block, now: u32) -> Result<Applied> {
        let h = self.height + 1;
        // 1. structure
        if blk.pubvalues.len() != PUBVALUES { bail!("wrong number of public values"); }
        if blk.stamp.len() > MAX_STAMP || blk.data.len() > MAX_DATA { bail!("block too large"); }
        if blk.tickets.is_empty() || blk.tickets.len() > self.p.max_tickets { bail!("{} tickets (1 to {} allowed)", blk.tickets.len(), self.p.max_tickets); }
        if blk.coinbase.len() > MAX_COINBASE { bail!("coinbase too long"); }
        // 2. seal
        let hdr = &blk.header;
        if hdr.ntime <= self.tip_ntime { bail!("time not after the previous block"); }
        if hdr.ntime as u64 > now as u64 + 7200 { bail!("time too far ahead"); }
        let miner_b = seal::check_seal(hdr, &blk.coinbase, self.p.chain, h, &self.tip, &blk.body_root(), self.bits)?;
        let miner = addr_from(&miner_b)?;
        // 3. tickets
        let mut seen: HashSet<([u64; 4], u64)> = HashSet::new();
        let mut minters = vec![];
        for t in &blk.tickets {
            let (a, _v) = mint::check_ticket(self.p.chain as u64, &self.tip, t, self.blow_diff)?;
            if !seen.insert((akey(&a), t.nonce)) { bail!("a blow used twice"); }
            minters.push(a);
        }
        let work = self.blow_diff * blk.tickets.len() as u64;
        if work < mint::min_work(self.work_ema, self.blow_diff) { bail!("not enough minting work ({} < {})", work, mint::min_work(self.work_ema, self.blow_diff)); }
        // 4. block data on our own state, with the payouts the rules owe
        let rule = PayoutRule { miner, pool_before: self.pool, rewards: self.pending.get(&h).cloned().unwrap_or_default() };
        let ctx = crate::locks::Ctx { chain: self.p.chain, ntime: hdr.ntime, cross: &self.cross };
        let rp = blockdata::replay_ctx(&self.state, &self.tree, &self.locks, self.reading.s, h, &rule, &blk.data, &ctx)?;
        // 5. the stamp
        if rp.public_inputs() != blk.pubvalues { bail!("public values differ from the replay of the block data"); }
        self.verifier.verify(&blk.pubvalues, &blk.stamp)?;
        Ok(Applied { rp, miner, minters, work, hash: hdr.hash() })
    }

    /// apply a validated block
    pub fn commit(&mut self, blk: &Block, ap: Applied) {
        let h = self.height + 1;
        let Applied { rp, miner, minters, work, hash } = ap;
        self.pending.remove(&h);
        // The reward of the PREVIOUS block is known now: its random factor comes from the seal of this block (SPEC 5.4), so no
        // miner can see or steer their own draw. It is paid in block h + 1 + maturity: N + 2 with no maturity, N + 2 + maturity with it.
        if let Some((ph, pminer, pminters)) = self.last.take() {
            let (total, owed) = crate::reward::payouts(crate::reward::Metal::of_chain(self.p.chain), ph, &hash, pminer, &pminters);
            self.pending.insert(h + 1 + self.p.maturity, owed);
            self.emitted += total;
        }
        self.last = Some((h, miner, minters));
        // S: this block's counted payments go into today's histograms; the last block of a day closes the day
        for o in &rp.reads { self.reading.observe(o); }
        self.reading.block_done(rp.s);
        if crate::reading::Reading::is_day_end(h) { self.reading.end_day(); }
        // orders that were held by a taker and are gone now were filled: that is the tape the official rates come from
        for (i, t) in &self.locks {
            if let crate::locks::Terms::Order { maker, sell, want_chain, want_amt, state: crate::locks::OrderState::Reserved { taker, .. } | crate::locks::OrderState::Bidding { taker, .. }, .. } = t {
                if !rp.locks.contains_key(i) { self.fills.push(crate::market::Fill { height: h, sell: *sell, want_chain: *want_chain, want_amt: *want_amt, maker: *maker, taker: *taker }); }
            }
        }
        if self.fills.len() > crate::market::TAPE { let n = self.fills.len() - crate::market::TAPE; self.fills.drain(..n); }
        self.state = rp.state; self.tree = rp.tree; self.pool = rp.pool_after; self.locks = rp.locks;
        self.idx = self.state.iter().map(|(i, a)| (akey(&a.pk), *i)).collect();
        // this block's weight, by the seal difficulty it was sealed at
        let n = blk.tickets.len() as u64;
        let ema = self.blows_ema.max(1);
        self.total_work += work_of_bits(self.bits).saturating_mul(n.min(2 * ema) as u128) / ema as u128;
        self.blows_ema = (ema as i128 + (n as i128 - ema as i128) / 32) as u64;
        // blow difficulty and the minting gate
        self.work_ema = mint::next_work_ema(self.work_ema, work);
        self.blow_diff = mint::retarget(self.blow_diff, blk.tickets.len() as u64);
        // seal difficulty: every `window` blocks, by the time the window took
        self.win_n += 1;
        if self.win_n == self.p.window {
            self.bits = retarget_bits(&self.p, self.bits, (blk.header.ntime - self.win_start) as u64);
            self.win_start = blk.header.ntime; self.win_n = 0;
        }
        self.height = h; self.tip = hash; self.tip_ntime = blk.header.ntime;
    }

    pub fn accept(&mut self, blk: &Block, now: u32) -> Result<()> {
        let ap = self.validate(blk, now)?;
        if let Some(store) = &self.log {
            if !std::env::var("ZEN_NOLOG").is_ok() { store.append(&blk.encode())?; }
        }
        self.commit(blk, ap);
        Ok(())
    }

    /// no coin is created or lost: balances + fee pool + rewards owed = genesis + everything issued
    pub fn audit(&self) -> Result<()> {
        let bal: u64 = self.state.values().map(|a| a.bal).sum();
        let owed: u64 = self.pending.values().flatten().map(|(_, v)| *v).sum();
        if bal + self.pool + owed != self.genesis_supply + self.emitted {
            bail!("supply mismatch: {} + {} + {} != {} + {}", bal, self.pool, owed, self.genesis_supply, self.emitted);
        }
        for a in self.state.values() { if a.rest > a.bal || a.used > a.rest { bail!("peg invariant broken"); } }
        Ok(())
    }
    /// an account by address: its index and leaf
    pub fn idx_of(&self, addr: &[F; 4]) -> Option<u64> { self.idx.get(&akey(addr)).copied() }
    pub fn account(&self, addr: &[F; 4]) -> Option<(u64, &Acct)> { let i = *self.idx.get(&akey(addr))?; self.state.get(&i).map(|a| (i, a)) }
    pub fn root(&self) -> [u64; 4] { self.tree.root().elements.map(|x| x.to_canonical_u64()) }
}

// ---------------------------------------------------------------- the fork tree: fork choice and reorgs
// Every valid block is kept with a snapshot of the consensus state after it, so switching to a heavier branch is
// switching a pointer. Snapshots are shared (`Arc`), so a block can be validated on its parent's snapshot without holding
// the node's lock (`lookup`, `Node::prepare`, `store`: the three steps `Net::add_block` runs, only the first and last
// under the lock). Snapshots deeper than `max_reorg` below the best tip are dropped, and with them the ability to build
// a branch there: a block whose parent is that old is `Stale` (not an error, just not worth keeping). Block bodies of the
// best chain stay in memory (moving them to the log on disk is open); bodies of dead branches go with their snapshots.
// Fork choice (SPEC 5.2): the branch with the most total weight wins, a block's weight being its seal work times
// its tickets over the recent average (capped at 2); at equal weight the lower seal hash wins.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Added { Known, Orphan([u8; 32]), Stale, Extended, Side, Reorg(u64) }
pub struct Outcome { pub main: Added, /// orphans that attached once their parent arrived
    pub attached: Vec<[u8; 32]> }
const MAX_ORPHANS: usize = 64;
/// how deep a reorg may go (half a day of blocks); deeper snapshots are dropped
pub const MAX_REORG: u64 = 288;
/// SPEC 5.4: a reward is spendable this many blocks after it would have been paid. Below MAX_REORG, so a reward is released well inside the
/// window in which the node still accepts a reorg.
pub const MATURITY_BLOCKS: u64 = 100;
/// what the node knows about a block it is offered
pub enum Lookup { Known, Stale, Orphan([u8; 32]), Parent(Arc<Chain>) }
pub struct Node {
    pub snaps: HashMap<[u8; 32], Arc<Chain>>,
    pub blocks: HashMap<[u8; 32], Block>,
    /// height of every block ever stored (kept after its snapshot is dropped)
    heights: HashMap<[u8; 32], u64>,
    /// the best chain, by height
    main: Vec<[u8; 32]>,
    pub best: [u8; 32],
    pub max_reorg: u64,
    pub max_orphans: usize,
    orphans: Vec<Block>,
    log: Option<crate::store::Store>,
    /// where each logged block lives in the log (every block ever stored, kept after the block leaves memory)
    index: HashMap<[u8; 32], (u64, u32)>,
    /// blocks are on disk, so old ones can leave memory
    durable: bool,
    pub reorgs: Vec<u64>,
    dir: Option<PathBuf>,
    /// digest of the genesis allocation (a snapshot belongs to one genesis)
    gd: [u8; 32],
    /// a snapshot is written when the block `max_reorg` below the tip is `snap_every` heights above the last one (0 = never)
    pub snap_every: u64,
    last_snap: u64,
    /// the height of the snapshot this node started from (0: it validated the whole log)
    pub from_snapshot: u64,
    /// the chain at genesis, to start a replay over
    g0: Arc<Chain>,
}
/// how often (in blocks) the node saves a snapshot of the state at the depth where no reorg can reach
pub const SNAPSHOT_EVERY: u64 = 1000;
/// what two nodes must share to be on one chain: the chain, every parameter, the genesis allocation (peers compare it in HELLO)
pub fn network_id_of(p: &Params, gd: &[u8; 32]) -> [u8; 32] {
    let mut h = Sha256::new(); h.update(b"Zen-network-v1"); h.update(Chain::snap_binding(p, gd)); h.finalize().into()
}
pub fn genesis_digest(genesis: &[([F; 4], u64)]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"Zen-genesis-allocation-v1");
    for (a, b) in genesis { for x in a { h.update(x.to_canonical_u64().to_le_bytes()); } h.update(b.to_le_bytes()); }
    h.finalize().into()
}
impl Node {
    pub fn network_id(&self) -> [u8; 32] { network_id_of(&self.g0.p, &self.gd) }
    pub fn genesis_root(&self) -> [u64; 4] { self.g0.root() }
    pub fn open(p: Params, genesis: &[([F; 4], u64)], verifier: Box<dyn StampVerifier + Send + Sync>, dir: Option<&Path>) -> Result<Node> {
        Node::open_with(p, genesis, verifier, dir, MAX_REORG, SNAPSHOT_EVERY)
    }
    /// With a directory the node replays its log; when a snapshot of the state is there and agrees with the log, it starts from the snapshot
    /// (the blocks before it are only indexed, the blocks after it are validated as ever). `ZEN_REVALIDATE=1` ignores snapshots and validates everything.
    pub fn open_with(p: Params, genesis: &[([F; 4], u64)], verifier: Box<dyn StampVerifier + Send + Sync>, dir: Option<&Path>, max_reorg: u64, snap_every: u64) -> Result<Node> {
        let mut g0 = Chain::open(p, genesis, verifier, None)?;
        g0.cross = crate::locks::CrossMode::Trust;       // the node's own log was judged when it was written
        let g = Arc::new(g0);
        let best = g.tip;
        let mut n = Node { snaps: HashMap::from([(best, g.clone())]), blocks: HashMap::new(), heights: HashMap::from([(best, 0)]), main: vec![best], best, max_reorg, max_orphans: MAX_ORPHANS,
                           orphans: vec![], log: None, index: HashMap::new(), durable: false, reorgs: vec![],
                           dir: dir.map(|d| d.to_path_buf()), gd: genesis_digest(genesis), snap_every, last_snap: 0, from_snapshot: 0, g0: g.clone() };
        if let Some(d) = dir {
            let store = crate::store::Store::open(d, true)?;
            n.durable = true;
            let mut started = false;
            if std::env::var("ZEN_REVALIDATE").is_err() {
                for (height, path) in Node::snapshot_files(d) {
                    let tried = std::fs::read(&path).map_err(anyhow::Error::from)
                        .and_then(|b| Chain::from_snapshot(g.p.clone(), g.verifier.clone(), &n.gd, &b)).map(|mut c| { c.cross = crate::locks::CrossMode::Trust; c })
                        .and_then(|c| { if c.height != height { bail!("the file name and the snapshot disagree on the height") } n.replay(&store, Some(c)) });
                    match tried {
                        Ok(()) => { n.last_snap = height; n.from_snapshot = height; started = true; break; }
                        Err(e) => { eprintln!("snapshot at height {height} not used: {e}"); n.fresh(); }
                    }
                }
            }
            if !started { n.replay(&store, None)?; }
            n.log = Some(store);
            n.maybe_snapshot();
        }
        n.set_cross(crate::locks::CrossMode::Off);
        Ok(n)
    }
    /// how new blocks' order claims are judged from now on (existing states and the ones built on them)
    pub fn set_cross(&mut self, mode: crate::locks::CrossMode) {
        for c in self.snaps.values_mut() { Arc::make_mut(c).cross = mode.clone(); }
    }
    fn fresh(&mut self) {
        let g = self.g0.clone();
        self.best = g.tip; self.snaps = HashMap::from([(g.tip, g.clone())]); self.heights = HashMap::from([(g.tip, 0)]);
        self.main = vec![g.tip]; self.blocks.clear(); self.index.clear(); self.orphans.clear(); self.reorgs.clear();
    }
    /// run the log into the node; with a snapshot, the records up to the snapshot's block are only indexed
    fn replay(&mut self, store: &crate::store::Store, snap: Option<Chain>) -> Result<()> {
        let mut pre: Option<(Chain, HashMap<[u8; 32], [u8; 32]>)> = snap.map(|c| (c, HashMap::new()));
        for i in 0..store.len() {
            let loc = store.record(i).unwrap();
            let blk = Block::decode(&store.read(loc)?)?;
            let h = blk.hash();
            self.index.insert(h, loc);
            if let Some((c, prevs)) = &mut pre {
                let ph = *self.heights.get(&blk.header.prev).ok_or_else(|| anyhow!("the log is not in order"))?;
                self.heights.insert(h, ph + 1);
                prevs.insert(h, blk.header.prev);
                if h == c.tip {
                    // the stored block says what the state must be: its height and the root of the state it leaves
                    if c.height != ph + 1 || blk.pubvalues[15] != c.height || blk.pubvalues[4..8] != c.root() { bail!("the snapshot does not match its block"); }
                    let (mut path, mut x) = (vec![], h);
                    while x != self.g0.tip { path.push(x); x = prevs[&x]; }
                    path.push(x);
                    path.reverse();
                    let (c, _) = pre.take().unwrap();
                    self.main = path; self.best = h; self.snaps = HashMap::from([(h, Arc::new(c))]);
                }
                continue;
            }
            self.add_block(&blk, u32::MAX)?;
        }
        if pre.is_some() { bail!("the snapshot's block is not in the log"); }
        Ok(())
    }
    #[cfg(test)]
    pub fn snapshot_files_for_test(dir: &Path) -> Vec<(u64, PathBuf)> { Node::snapshot_files(dir) }
    /// snapshot files in the directory, newest first
    fn snapshot_files(dir: &Path) -> Vec<(u64, PathBuf)> {
        let mut v: Vec<(u64, PathBuf)> = std::fs::read_dir(dir).into_iter().flatten().flatten().filter_map(|e| {
            let name = e.file_name().into_string().ok()?;
            let h = name.strip_prefix("snapshot-")?.strip_suffix(".zen")?.parse::<u64>().ok()?;
            Some((h, e.path()))
        }).collect();
        v.sort_by(|a, b| b.0.cmp(&a.0));
        v
    }
    /// save the state at the depth where no reorg can reach, when it is time (never fails the node: a snapshot is only a shortcut)
    fn maybe_snapshot(&mut self) {
        let (Some(_), Some(dir)) = (&self.log, self.dir.clone()) else { return };
        let bh = self.height();
        if self.snap_every == 0 || bh <= self.max_reorg { return; }
        let floor = bh - self.max_reorg;
        if floor < self.last_snap + self.snap_every { return; }
        let Some(c) = self.snaps.get(&self.main[floor as usize]) else { return };
        let res = (|| -> Result<()> {
            let bytes = c.snapshot_bytes(&self.gd)?;
            let tmp = dir.join(format!("snapshot-{floor}.tmp"));
            { use std::io::Write; let mut f = std::fs::File::create(&tmp)?; f.write_all(&bytes)?; f.sync_all()?; }
            std::fs::rename(&tmp, dir.join(format!("snapshot-{floor}.zen")))?;
            std::fs::File::open(&dir)?.sync_all()?;
            for (_, old) in Node::snapshot_files(&dir).into_iter().skip(2) { let _ = std::fs::remove_file(old); }
            Ok(())
        })();
        match res { Ok(()) => self.last_snap = floor, Err(e) => eprintln!("snapshot at height {floor} not written: {e}") }
    }
    pub fn tip(&self) -> &Chain { &self.snaps[&self.best] }
    /// the proof an order claim carries (locks.rs): payment number `entry` of the block at `height` of the best chain, with the receiver's leaf when
    /// the payment did not create it (needs the state after that block, which the node keeps for recent blocks)
    pub fn payment_proof(&self, height: u64, entry: u32) -> Result<crate::locks::PaymentProof> {
        let hash = self.hash_at(height).ok_or_else(|| anyhow!("no block at height {height}"))?;
        let blk = self.block(&hash).ok_or_else(|| anyhow!("the block is not available"))?;
        let (_, leaves, _) = blockdata::decode_prefix(&blk.data)?;
        let e = leaves.iter().flat_map(|l| l.pays.iter()).filter(|e| !e.credit).nth(entry as usize).ok_or_else(|| anyhow!("no payment number {entry} in block {height}"))?;
        let leaf = if e.new_r.is_some() { None } else {
            let post = self.snaps.get(&hash).ok_or_else(|| anyhow!("the state after block {height} is no longer kept"))?;
            let a = post.state.get(&(e.r_idx as u64)).ok_or_else(|| anyhow!("the receiver is gone"))?;
            let path = post.tree.path(e.r_idx as u64).iter().map(|h| h.elements.map(|x| x.to_canonical_u64())).collect();
            Some((e.r_idx as u64, a.pk.iter().map(|x| x.to_canonical_u64()).collect(), [a.bal, a.nonce, a.rest, a.used, a.fd, a.rd, a.up], path))
        };
        Ok(crate::locks::PaymentProof { chain: self.tip().p.chain, height, header: blk.header.bytes(), coinbase: blk.coinbase.clone(), tickets_root: tickets_root(&blk.tickets),
                                        pubvalues: blk.pubvalues.clone(), stamp: blk.stamp.clone(), data: blk.data.clone(), entry, leaf })
    }
    /// the newest payment on the best chain to `to` of at least `min`, made in a block after time `after`, looking back `back` blocks: (height, number)
    pub fn find_payment(&self, to: &[F; 4], min: u64, after: u32, back: u64) -> Option<(u64, u32)> {
        let top = self.tip().height;
        for h in (top.saturating_sub(back).max(1)..=top).rev() {
            let hash = self.hash_at(h)?;
            let blk = self.block(&hash)?;
            if blk.header.ntime <= after { return None; }
            let Ok((_, leaves, _)) = blockdata::decode_prefix(&blk.data) else { continue };
            for (n, e) in leaves.iter().flat_map(|l| l.pays.iter()).filter(|e| !e.credit).enumerate() {
                if e.amt < min { continue; }
                let pk = match (&e.new_r, self.snaps.get(&hash)) {
                    (Some(a), _) => Some(*a),
                    (None, Some(post)) => post.state.get(&(e.r_idx as u64)).map(|a| a.pk),
                    _ => None,
                };
                if pk.as_ref() == Some(to) { return Some((h, n as u32)); }
            }
        }
        None
    }
    /// the block at a height of the best chain
    pub fn hash_at(&self, h: u64) -> Option<[u8; 32]> { self.main.get(h as usize).copied() }
    /// the height of a block that is on the best chain
    pub fn main_height_of(&self, hash: &[u8; 32]) -> Option<u64> { let h = *self.heights.get(hash)?; (self.main.get(h as usize) == Some(hash)).then_some(h) }
    /// bytes of a torn write cut from the log when it was opened
    pub fn repaired(&self) -> u64 { self.log.as_ref().map_or(0, |l| l.repaired) }
    /// a block we stored: from memory when recent, else read back from the log
    pub fn block(&self, h: &[u8; 32]) -> Option<Block> {
        if let Some(b) = self.blocks.get(h) { return Some(b.clone()); }
        let loc = *self.index.get(h)?;
        Block::decode(&self.log.as_ref()?.read(loc).ok()?).ok()
    }
    pub fn have(&self, h: &[u8; 32]) -> bool { self.heights.contains_key(h) || self.orphans.iter().any(|o| o.hash() == *h) }
    fn height_of(&self, h: &[u8; 32]) -> u64 { self.heights[h] }
    pub fn height(&self) -> u64 { self.main.len() as u64 - 1 }

    /// the hashes of the best chain a peer can use to find where we agree: the tip, then steps back by 1, 2, 4, 8, ... to genesis
    pub fn locator(&self) -> Vec<[u8; 32]> {
        let (mut out, mut step, mut i) = (vec![], 1usize, self.main.len() - 1);
        loop {
            out.push(self.main[i]);
            if i == 0 { break; }
            i = i.saturating_sub(step);
            if out.len() >= 10 { step *= 2; }
        }
        out
    }
    /// the block after the first locator hash that is on our best chain (what a syncing peer asks for next)
    pub fn next_after(&self, locator: &[[u8; 32]]) -> Option<Block> {
        for h in locator.iter().take(32) {
            if let Some(&ht) = self.heights.get(h) {
                if self.main.get(ht as usize) == Some(h) { return self.main.get(ht as usize + 1).and_then(|n| self.block(n)); }
            }
        }
        None
    }

    /// step 1 (under the lock): where does this block stand
    pub fn lookup(&self, blk: &Block) -> Lookup {
        if self.heights.contains_key(&blk.hash()) { return Lookup::Known; }
        let parent = blk.header.prev;
        match self.snaps.get(&parent) {
            Some(pc) => Lookup::Parent(pc.clone()),
            None if self.heights.contains_key(&parent) => Lookup::Stale,
            None => Lookup::Orphan(parent),
        }
    }
    /// step 2 (no lock needed): the chain after the block, validated on its parent's snapshot
    pub fn prepare(parent: &Chain, blk: &Block, now: u32) -> Result<Chain> {
        let mut c = parent.clone();
        let ap = c.validate(blk, now)?;
        c.commit(blk, ap);
        Ok(c)
    }
    /// step 3 (under the lock): store a prepared block, choose the best chain, drop what is too deep
    pub fn store(&mut self, blk: &Block, c: Chain) -> Result<Added> {
        let h = blk.hash();
        if self.heights.contains_key(&h) { return Ok(Added::Known); }
        let parent = blk.header.prev;
        if !self.snaps.contains_key(&parent) { return Ok(Added::Stale); }      // pruned while we validated
        if let Some(store) = &self.log {
            let loc = store.append(&blk.encode())?;
            self.index.insert(h, loc);
        }
        let old = self.best;
        let better = { let b = &self.snaps[&old];
            c.total_work > b.total_work || (c.total_work == b.total_work && num_bigint::BigUint::from_bytes_le(&h) < num_bigint::BigUint::from_bytes_le(&old)) };
        self.heights.insert(h, c.height);
        self.snaps.insert(h, Arc::new(c));
        self.blocks.insert(h, blk.clone());
        if !better { self.prune(); return Ok(Added::Side); }
        self.best = h;
        // the best chain by height: walk back to where it joins the old one
        let mut path = vec![];
        let mut x = h;
        loop {
            let ht = self.heights[&x] as usize;
            if self.main.get(ht) == Some(&x) { self.main.truncate(ht + 1); break; }
            path.push(x);
            x = self.blocks[&x].header.prev;
        }
        let fork_height = self.main.len() as u64 - 1;
        self.main.extend(path.into_iter().rev());
        self.prune();
        if parent == old { return Ok(Added::Extended); }
        let depth = self.height_of(&old) - fork_height;
        self.reorgs.push(depth);
        Ok(Added::Reorg(depth))
    }
    fn prune(&mut self) {
        let bh = self.height();
        if bh <= self.max_reorg { return; }
        let floor = bh - self.max_reorg;
        let heights = &self.heights;
        self.snaps.retain(|h, _| heights[h] >= floor);
        let main = &self.main;
        let durable = self.durable;
        self.blocks.retain(|h, _| heights[h] >= floor || (!durable && main.get(heights[h] as usize) == Some(h)));
        self.maybe_snapshot();
    }
    /// park a block whose parent we do not have
    pub fn park(&mut self, blk: &Block) {
        if !self.orphans.iter().any(|o| o.hash() == blk.hash()) {
            if self.orphans.len() >= self.max_orphans { self.orphans.remove(0); }
            self.orphans.push(blk.clone());
        }
    }
    /// an orphan whose parent has arrived (it leaves the waiting list)
    pub fn next_attachable(&mut self) -> Option<Block> {
        let i = self.orphans.iter().position(|o| self.heights.contains_key(&o.header.prev))?;
        Some(self.orphans.remove(i))
    }

    /// add a block from anywhere, all steps under one hold (replaying the log, tests); `Net::add_block` does the same with
    /// the validation outside the lock. An invalid block is an error, a block with an unknown parent waits as an orphan.
    pub fn add_block(&mut self, blk: &Block, now: u32) -> Result<Outcome> {
        let main = self.process(blk, now)?;
        if let Added::Orphan(_) = main { self.park(blk); return Ok(Outcome { main, attached: vec![] }); }
        let mut attached = vec![];
        while let Some(o) = self.next_attachable() {
            if let Ok(a) = self.process(&o, now) { if !matches!(a, Added::Known | Added::Stale) { attached.push(o.hash()); } }
        }
        Ok(Outcome { main, attached })
    }
    fn process(&mut self, blk: &Block, now: u32) -> Result<Added> {
        match self.lookup(blk) {
            Lookup::Known => Ok(Added::Known),
            Lookup::Stale => Ok(Added::Stale),
            Lookup::Orphan(p) => Ok(Added::Orphan(p)),
            Lookup::Parent(pc) => { let c = Node::prepare(&pc, blk, now)?; self.store(blk, c) }
        }
    }
}

// ---------------------------------------------------------------- devnet: tickets, blocks, a miner
pub mod dev {
    use super::*;
    use rand::{Rng, SeedableRng};

    pub struct DevPay { pub from: [F; 4], pub to: [F; 4], pub amt: u64, pub fee: u64 }

    /// winning blows from the given keys at the chain's current difficulty (round robin over the keys)
    pub fn make_tickets(chain: &Chain, keys: &[mint::Key], n: usize) -> Vec<Ticket> {
        let mut out = vec![];
        let mut nonce = 0u64;
        while out.len() < n {
            let k = &keys[(nonce as usize) % keys.len()];
            let t = mint::make_ticket(k, chain.p.chain as u64, &chain.tip, nonce / keys.len() as u64 + 1_000_000 * (nonce % keys.len() as u64));
            nonce += 1;
            if mint::wins(&mint::blow_value(&chain.tip, &t), chain.blow_diff) { out.push(t); }
        }
        out
    }

    /// Build and stamp (DevStamp) a block on the chain's tip, unsealed. Payments that do not fit are left out.
    pub fn build_template(chain: &Chain, miner: [F; 4], tickets: Vec<Ticket>, pays: &[DevPay], ntime: u32, maker: &dyn StampMaker) -> Result<Block> {
        build_template_ops(chain, miner, tickets, pays, &[], ntime, maker)
    }
    pub use crate::locks::OpReq;
    pub fn build_template_ops(chain: &Chain, miner: [F; 4], tickets: Vec<Ticket>, pays: &[DevPay], reqs: &[OpReq], ntime: u32, maker: &dyn StampMaker) -> Result<Block> {
        build_template_ops_with(chain, miner, tickets, pays, reqs, ntime, maker, false)
    }
    /// `force`: keep every operation that can be resolved even if the block then does not replay (the call fails with the reason; a test tool)
    pub fn build_template_ops_with(chain: &Chain, miner: [F; 4], tickets: Vec<Ticket>, pays: &[DevPay], reqs: &[OpReq], ntime: u32, maker: &dyn StampMaker, force: bool) -> Result<Block> {
        let h = chain.height + 1;
        let reqs: Vec<OpReq> = reqs.iter().filter(|r| maker.accepts(r)).cloned().collect();
        let mut addr_idx: HashMap<[u64; 4], u64> = chain.state.iter().map(|(i, a)| (akey(&a.pk), *i)).collect();
        let mut taken: HashSet<u64> = chain.state.keys().copied().collect();
        let mut bal: HashMap<u64, u64> = chain.state.iter().map(|(i, a)| (*i, a.bal)).collect();
        let mut nonce: HashMap<u64, u64> = HashMap::new();
        let minters: Vec<[F; 4]> = tickets.iter().map(|t| ec::pk_hash(mint::decode_point(&t.a).unwrap())).collect();
        let mut leaves: Vec<LeafData> = vec![];
        let mut leaf_fees: Vec<([F; 4], u64)> = vec![];
        let mut slot = SLOTS_PER_LEAF;
        let s = chain.reading.s;
        for p in pays {
            let (Some(&si), spend) = (addr_idx.get(&akey(&p.from)), p.amt + p.fee) else { continue };
            if p.amt >= 1 << 62 || p.fee >= 1 << 62 { continue; }
            if (p.amt as u128) * 6 < s as u128 || (p.fee as u128) * 100 < s as u128 { continue; }
            if (p.fee as u128) * 10_000 < spend as u128 || (p.fee as u128) * 100 > 6 * spend as u128 { continue; }
            if bal[&si] < spend || p.from == p.to { continue; }
            let (ri, new_r) = match addr_idx.get(&akey(&p.to)) {
                Some(&r) => { if bal[&r] + p.amt >= 1 << 62 { continue; } (r, None) }
                None => { let r = free_index(&|i| taken.contains(&i), &p.to); (r, Some(p.to)) }
            };
            if slot == SLOTS_PER_LEAF {
                leaves.push(LeafData { prover: minters[leaves.len() % minters.len()], pays: vec![] });
                leaf_fees.push((leaves.last().unwrap().prover, 0)); slot = 0;
            }
            *bal.get_mut(&si).unwrap() -= spend;
            *nonce.entry(si).or_insert(chain.state[&si].nonce) += 1;
            if new_r.is_some() { taken.insert(ri); addr_idx.insert(akey(&p.to), ri); bal.insert(ri, p.amt); } else { *bal.get_mut(&ri).unwrap() += p.amt; }
            leaves.last_mut().unwrap().pays.push(BlockEntry { slot: slot as u8, credit: false, s_idx: si as u32, r_idx: ri as u32, amt: p.amt, fee: p.fee, new_r, close: false });
            leaf_fees.last_mut().unwrap().1 += p.fee;
            slot += 1;
        }
        // the payouts the rules owe, as credit slots after the payments
        let rule = PayoutRule { miner, pool_before: chain.pool, rewards: chain.pending.get(&h).cloned().unwrap_or_default() };
        let (credits, _pool_after) = blockdata::expected_credits(&leaf_fees, &rule);
        for (a, amt) in credits {
            if slot == SLOTS_PER_LEAF { leaves.push(LeafData { prover: [F::ZERO; 4], pays: vec![] }); slot = 0; }
            let (ri, new_r) = match addr_idx.get(&akey(&a)) {
                Some(&r) => (r, None),
                None => { let r = free_index(&|i| taken.contains(&i), &a); taken.insert(r); addr_idx.insert(akey(&a), r); (r, Some(a)) }
            };
            leaves.last_mut().unwrap().pays.push(BlockEntry { slot: slot as u8, credit: true, s_idx: 0, r_idx: ri as u32, amt, fee: 0, new_r, close: false });
            slot += 1;
        }
        // a block with no payments and nothing owed (the first blocks of a chain, when rewards wait their maturity) still has one leaf, an empty one
        if leaves.is_empty() { leaves.push(LeafData { prover: [F::ZERO; 4], pays: vec![] }); }
        let mut data = blockdata::encode(SLOTS_PER_LEAF, &leaves);
        // operations: each is tried on the block built so far and kept only if the whole block still replays
        let cx = crate::locks::Ctx { chain: chain.p.chain, ntime, cross: &chain.cross };
        let mut ops: Vec<crate::locks::Op> = vec![];
        for req in &reqs {
            if ops.len() >= crate::locks::MAX_OPS { break; }
            let (mut ai, mut tk, mut nn) = (addr_idx.clone(), taken.clone(), nonce.clone());
            let Some(op) = resolve_op(chain, req, &mut ai, &mut tk, &mut nn) else { continue };
            let mut trial = ops.clone(); trial.push(op);
            let mut bytes = data.clone(); bytes.extend(crate::locks::encode_ops(&trial));
            if force || blockdata::replay_ctx(&chain.state, &chain.tree, &chain.locks, s, h, &rule, &bytes, &cx).is_ok() { ops = trial; addr_idx = ai; taken = tk; nonce = nn; }
        }
        data.extend(crate::locks::encode_ops(&ops));
        let rp = blockdata::replay_ctx(&chain.state, &chain.tree, &chain.locks, s, h, &rule, &data, &cx)?;
        let pubvalues = rp.public_inputs();
        let stamp = maker.stamp(chain, h, &leaves, &ops, ntime, &pubvalues)?;
        let blk = Block { header: Header { version: seal::VERSION_BASE, prev: chain.tip, commitment: [0; 32], ntime, nbits: chain.bits, nonce: 0 },
                          coinbase: coinbase_for(chain.p.chain, h, &[0; 4], &miner), pubvalues, stamp, data, tickets };
        Ok(blk)
    }

    /// the indices an operation needs, from addresses; None when something it names is not there
    fn resolve_op(chain: &Chain, req: &OpReq, addr_idx: &mut HashMap<[u64; 4], u64>, taken: &mut HashSet<u64>, nonce: &mut HashMap<u64, u64>) -> Option<crate::locks::Op> {
        use crate::locks::{Dest, Op};
        let idx = |a: &[F; 4], m: &HashMap<[u64; 4], u64>| m.get(&akey(a)).copied();
        let mut dest = |a: &[F; 4], addr_idx: &mut HashMap<[u64; 4], u64>, taken: &mut HashSet<u64>| -> Dest {
            match addr_idx.get(&akey(a)) { Some(&i) => Dest { idx: i as u32, new: None }, None => { let i = free_index(&|x| taken.contains(&x), a); taken.insert(i); addr_idx.insert(akey(a), i); Dest { idx: i as u32, new: Some(*a) } } }
        };
        let from_addr = match req { OpReq::Bid { from, .. } | OpReq::Make { from, .. } | OpReq::VaultClaim { from, .. } | OpReq::VaultRefund { from, .. } | OpReq::Reserve { from, .. } | OpReq::OrderClaim { from, .. } | OpReq::Reopen { from, .. } | OpReq::Return { from, .. } | OpReq::ChanStart { from, .. } | OpReq::ChanUpdate { from, .. } | OpReq::ChanSettle { from, .. } | OpReq::ChanClose { from, .. } | OpReq::FactoryStart { from, .. } | OpReq::FactoryPost { from, .. } | OpReq::FactoryExit { from, .. } | OpReq::FactoryExitNow { from, .. } | OpReq::FactoryFund { from, .. } | OpReq::ChanFund { from, .. } => from };
        let fi = idx(from_addr, addr_idx)?;
        let n = *nonce.entry(fi).or_insert(chain.state.get(&fi)?.nonce);
        nonce.insert(fi, n + 1);
        let from = fi as u32;
        let lock_of = |a: &[F; 4], m: &HashMap<[u64; 4], u64>| -> Option<u32> { let i = *m.get(&akey(a))?; chain.locks.contains_key(&i).then_some(i as u32) };
        let terms_of = |l: u32| chain.locks.get(&(l as u64)).cloned();
        Some(match req {
            OpReq::Make { amt, fee, terms, .. } => {
                let mut t = terms.clone(); t.set_salt(n);
                let at = free_index(&|x| taken.contains(&x), &t.digest()); taken.insert(at); addr_idx.insert(akey(&t.digest()), at);
                Op::Make { from, fee: *fee, amt: *amt, at: at as u32, terms: t }
            }
            OpReq::VaultClaim { fee, lock, to, e, s, .. } => { let l = lock_of(lock, addr_idx)?; Op::VaultClaim { from, fee: *fee, lock: l, to: dest(to, addr_idx, taken), e: *e, s: *s } }
            OpReq::VaultRefund { fee, lock, to, .. } => { let l = lock_of(lock, addr_idx)?; Op::VaultRefund { from, fee: *fee, lock: l, to: dest(to, addr_idx, taken) } }
            OpReq::Reserve { fee, lock, taker, .. } => { let l = lock_of(lock, addr_idx)?; Op::Reserve { from, fee: *fee, lock: l, taker: *taker } }
            OpReq::Bid { fee, lock, taker, bid, .. } => {
                let l = lock_of(lock, addr_idx)?;
                let refund = match terms_of(l)? { crate::locks::Terms::Order { state: crate::locks::OrderState::Bidding { taker, .. }, .. } => dest(&taker, addr_idx, taken), _ => Dest { idx: from, new: None } };
                Op::Bid { from, fee: *fee, lock: l, taker: *taker, bid: *bid, refund }
            }
            OpReq::OrderClaim { fee, lock, proof, .. } => {
                let l = lock_of(lock, addr_idx)?;
                let to = match terms_of(l)? { crate::locks::Terms::Order { state: crate::locks::OrderState::Reserved { taker, .. } | crate::locks::OrderState::Bidding { taker, .. }, .. } => dest(&taker, addr_idx, taken), _ => Dest { idx: from, new: None } };
                Op::OrderClaim { from, fee: *fee, lock: l, to, proof: proof.clone() }
            }
            OpReq::Reopen { fee, lock, .. } => {
                let l = lock_of(lock, addr_idx)?;
                let to = match terms_of(l)? { crate::locks::Terms::Order { maker, .. } => dest(&maker, addr_idx, taken), _ => Dest { idx: from, new: None } };
                Op::Reopen { from, fee: *fee, lock: l, to }
            }
            OpReq::Return { fee, lock, .. } => {
                let l = lock_of(lock, addr_idx)?;
                let to = match terms_of(l)? { crate::locks::Terms::Order { maker, .. } => dest(&maker, addr_idx, taken), _ => Dest { idx: from, new: None } };
                Op::Return { from, fee: *fee, lock: l, to }
            }
            OpReq::ChanStart { fee, lock, .. } => Op::ChanStart { from, fee: *fee, lock: lock_of(lock, addr_idx)? },
            OpReq::ChanUpdate { fee, lock, seq, bal_a, locks, sigs, .. } => Op::ChanUpdate { from, fee: *fee, lock: lock_of(lock, addr_idx)?, seq: *seq, bal_a: *bal_a, locks: locks.clone(), sigs: *sigs },
            OpReq::ChanSettle { fee, lock, wits, .. } => {
                let l = lock_of(lock, addr_idx)?;
                let (ta, tb) = match terms_of(l)? { crate::locks::Terms::Channel { a, b, .. } => (a, b), _ => return None };
                let (to_a, to_b) = (dest(&ta, addr_idx, taken), dest(&tb, addr_idx, taken));
                Op::ChanSettle { from, fee: *fee, lock: l, wits: wits.clone(), to_a, to_b }
            }
            OpReq::ChanFund { fee, lock, amt, .. } => Op::ChanFund { from, fee: *fee, lock: lock_of(lock, addr_idx)?, amt: *amt },
            OpReq::FactoryFund { fee, lock, idx, amt, .. } => Op::FactoryFund { from, fee: *fee, lock: lock_of(lock, addr_idx)?, idx: *idx, amt: *amt },
            OpReq::FactoryStart { fee, lock, idx, .. } => Op::FactoryStart { from, fee: *fee, lock: lock_of(lock, addr_idx)?, idx: *idx },
            OpReq::FactoryPost { fee, lock, idx, seq, bal_c, locks, sigs, .. } => Op::FactoryPost { from, fee: *fee, lock: lock_of(lock, addr_idx)?, idx: *idx, seq: *seq, bal_c: *bal_c, locks: locks.clone(), sigs: *sigs },
            OpReq::FactoryExit { fee, lock, idx, wits, .. } => {
                let l = lock_of(lock, addr_idx)?;
                let (tc, tm) = match terms_of(l)? { crate::locks::Terms::Factory { coord, members, .. } => (coord, members.get(*idx as usize)?.addr), _ => return None };
                let (to_c, to_m) = (dest(&tc, addr_idx, taken), dest(&tm, addr_idx, taken));
                Op::FactoryExit { from, fee: *fee, lock: l, idx: *idx, wits: wits.clone(), to_c, to_m }
            }
            OpReq::FactoryExitNow { fee, lock, idx, bal_c, sigs, .. } => {
                let l = lock_of(lock, addr_idx)?;
                let (tc, tm) = match terms_of(l)? { crate::locks::Terms::Factory { coord, members, .. } => (coord, members.get(*idx as usize)?.addr), _ => return None };
                let (to_c, to_m) = (dest(&tc, addr_idx, taken), dest(&tm, addr_idx, taken));
                Op::FactoryExitNow { from, fee: *fee, lock: l, idx: *idx, bal_c: *bal_c, sigs: *sigs, to_c, to_m }
            }
            OpReq::ChanClose { fee, lock, bal_a, sigs, .. } => {
                let l = lock_of(lock, addr_idx)?;
                let (ta, tb) = match terms_of(l)? { crate::locks::Terms::Channel { a, b, .. } => (a, b), _ => return None };
                let (to_a, to_b) = (dest(&ta, addr_idx, taken), dest(&tb, addr_idx, taken));
                Op::ChanClose { from, fee: *fee, lock: l, bal_a: *bal_a, sigs: *sigs, to_a, to_b }
            }
        })
    }

    /// build, stamp and seal a block with operations
    pub fn build_block_ops(chain: &Chain, miner: [F; 4], tickets: Vec<Ticket>, pays: &[DevPay], reqs: &[OpReq], ntime: u32, maker: &dyn StampMaker) -> Result<Block> {
        let mut blk = build_template_ops(chain, miner, tickets, pays, reqs, ntime, maker)?;
        reseal(chain, &mut blk);
        Ok(blk)
    }
    /// Build, stamp and seal a block (the seal is ground here by one thread at easy difficulty)
    pub fn build_block(chain: &Chain, miner: [F; 4], tickets: Vec<Ticket>, pays: &[DevPay], ntime: u32, maker: &dyn StampMaker) -> Result<Block> {
        let mut blk = build_template(chain, miner, tickets, pays, ntime, maker)?;
        reseal(chain, &mut blk);
        Ok(blk)
    }

    /// re-seal a block whose body was changed (a test tool: the seal commits to the body)
    pub fn reseal(chain: &Chain, blk: &mut Block) {
        let body = blk.body_root();
        let mut en: u32 = 0;
        loop {
            let mut cb = seal::coinb1(chain.p.chain, chain.height + 1, 4);
            cb.extend(en.to_le_bytes());
            cb.extend(&blk.coinbase[blk.coinbase.len() - 32..]);
            blk.coinbase = cb;
            blk.header.commitment = seal::merkle_root(&blk.coinbase, &[body]);
            for nonce in 0..=u32::MAX { blk.header.nonce = nonce; if seal::meets(&blk.header.hash(), blk.header.nbits) { return; } }
            en += 1;
        }
    }

    pub struct Devnet { pub chain: Chain, pub keys: Vec<mint::Key>, pub rng: rand::rngs::StdRng, pub now: u32, pub maker: Arc<dyn StampMaker> }
    impl Devnet {
        pub fn new(dir: Option<&Path>, wallets: usize) -> Result<Devnet> {
            Devnet::with(dir, wallets, Box::new(DevStamp), None)
        }
        /// a devnet whose stamps are real proofs (`maker` builds them, `verifier` checks them)
        pub fn with(dir: Option<&Path>, wallets: usize, verifier: Box<dyn StampVerifier + Send + Sync>, maker: Option<Arc<dyn StampMaker>>) -> Result<Devnet> {
            let keys: Vec<mint::Key> = devnet_keys(wallets);
            let chain = Chain::open(Params::devnet(), &genesis_of(&keys), verifier, dir)?;
            let now = chain.tip_ntime;
            Ok(Devnet { chain, keys, rng: rand::rngs::StdRng::seed_from_u64(7), now, maker: maker.unwrap_or_else(|| Arc::new(DevStampMaker)) })
        }
        /// the next block, not yet accepted: `n_tickets` winning blows, random payments among the wallets, a miner, a seal
        pub fn next_block(&mut self, n_tickets: usize, n_pays: usize) -> Result<Block> {
            let parent = self.chain.clone();
            self.block_on(&parent, n_tickets, n_pays)
        }
        /// a block on any snapshot (a fork): same wallets, same randomness source
        pub fn block_on(&mut self, parent: &Chain, n_tickets: usize, n_pays: usize) -> Result<Block> {
            let w = self.keys.len();
            let tickets = make_tickets(parent, &self.keys[..4.min(w)], n_tickets);
            let miner = self.keys[self.rng.gen_range(0..w)].addr;
            let pays: Vec<DevPay> = (0..n_pays).map(|_| {
                let a = self.rng.gen_range(0..w); let mut b = self.rng.gen_range(0..w); if b == a { b = (b + 1) % w; }
                let amt = 10_000 + self.rng.gen_range(0..2_000_000u64);
                DevPay { from: self.keys[a].addr, to: self.keys[b].addr, amt, fee: amt / 100 }
            }).collect();
            self.now = parent.tip_ntime + self.rng.gen_range(120..180);
            build_block(parent, miner, tickets, &pays, self.now, self.maker.as_ref())
        }
    }
    /// the pool side of the Stratum server on a devnet: tickets from the wallets, a few payments, an unsealed template
    pub struct DevSource { pub keys: Vec<mint::Key>, pub miner: [F; 4], pub maker: Arc<dyn StampMaker> }
    impl crate::p2p::TemplateSource for DevSource {
        fn template(&self, tip: &Chain) -> Result<Block> {
            let tickets = make_tickets(tip, &self.keys[..4.min(self.keys.len())], mint::TARGET_BLOWS as usize);
            let pays: Vec<DevPay> = (0..6).map(|i| { let a = (tip.height as usize + i) % self.keys.len(); let b = (a + 1) % self.keys.len();
                DevPay { from: self.keys[a].addr, to: self.keys[b].addr, amt: 50_000 + 1_000 * i as u64, fee: 600 } }).collect();
            build_template(tip, self.miner, tickets, &pays, tip.tip_ntime + 150, self.maker.as_ref())
        }
    }
    /// the pool of a node with a mempool: tickets from the pool's minter keys, payments from the mempool (best fee rate first).
    /// With real stamps the signed payments go to the prover's store first, so the proof carries the wallets' own signatures.
    pub struct PoolSource { pub minters: Vec<mint::Key>, pub miner: [F; 4], pub maker: Arc<dyn StampMaker>, pub pool: Arc<std::sync::Mutex<crate::mempool::Mempool>>,
                            pub store: Option<crate::prover::SigStore>, pub max_pays: usize,
                            /// operations (locks.rs) wallets sent; None: payments only
                            pub ops: Option<Arc<std::sync::Mutex<crate::locks::OpPool>>>,
                            /// block times from the wall clock (a real network); false: tip time + 150 s (the devnet's own clock)
                            pub wall_clock: bool }
    impl crate::p2p::TemplateSource for PoolSource {
        fn template(&self, tip: &Chain) -> Result<Block> {
            let tickets = make_tickets(tip, &self.minters[..4.min(self.minters.len())], mint::TARGET_BLOWS as usize);
            let txs = self.pool.lock().unwrap().select(tip, self.max_pays);
            if let Some(st) = &self.store {
                let mut st = st.lock().unwrap();
                for t in &txs { st.insert((crate::tx::addr_key(&t.verify()?.1), t.nonce), t.clone()); }
            }
            let pays: Vec<DevPay> = txs.iter().map(|t| Ok(DevPay { from: t.verify()?.1, to: t.to, amt: t.amt, fee: t.fee })).collect::<Result<_>>()?;
            let ntime = if self.wall_clock { crate::p2p::now().max(tip.tip_ntime + 1) } else { tip.tip_ntime + 150 };
            let reqs = self.ops.as_ref().map(|o| o.lock().unwrap().select(tip)).unwrap_or_default();
            if reqs.is_empty() { build_template(tip, self.miner, tickets, &pays, ntime, self.maker.as_ref()) }
            else { build_template_ops(tip, self.miner, tickets, &pays, &reqs, ntime, self.maker.as_ref()) }
        }
    }
    pub fn devnet_keys(wallets: usize) -> Vec<mint::Key> {
        (0..wallets).map(|i| mint::Key::from_secret(num_bigint::BigUint::from(1_000_003u64 + 7919 * i as u64))).collect()
    }
    pub fn genesis_of(keys: &[mint::Key]) -> Vec<([F; 4], u64)> { keys.iter().map(|k| (k.addr, 1_000_000_000)).collect() }
}

// ---------------------------------------------------------------- `zenproof node devnet [blocks]`
/// `zenproof node serve <p2p addr> <stratum addr> [peer addr]`: a devnet node with a pool (tickets from 12 devnet wallets)
/// `zenproof node mine <stratum addr> [blocks]`: a CPU miner that knows only Stratum
pub fn serve_main() -> Result<()> {
    use crate::p2p::{self, Net, Stratum};
    let a: Vec<String> = std::env::args().collect();
    match a.get(2).map(|s| s.as_str()) {
        Some("serve") => {
            // ZEN_REAL=1: every block carries a real Plonky2 stamp (the pool proves it, every node verifies it)
            // ZEN_G16=<setup dir with zen.pk, zen.r1cs, zen.vk> (and ZEN_WRAP=<path of the Go prover>): the stamp is the 196-byte
            // Groth16 proof instead; every node checks it with the Rust verifier from zen.vk alone
            let g16 = std::env::var("ZEN_G16").ok().map(PathBuf::from);
            let real = std::env::var("ZEN_REAL").is_ok() || g16.is_some();
            // ZEN_NET=<net.conf>: a configured network (one chain, its own parameters and genesis); without it, the devnet (Jen, 12 public wallets)
            let conf = match std::env::var("ZEN_NET") { Ok(f) => Some((crate::netconf::NetConf::load(Path::new(&f))?, PathBuf::from(f))), Err(_) => None };
            let keys: Vec<mint::Key> = match &conf {
                None => dev::devnet_keys(12),
                Some((c, f)) => {
                    let dir = std::env::var("ZEN_MINTERS").map(PathBuf::from).unwrap_or_else(|_| f.parent().map(|d| d.join("minters")).unwrap_or_else(|| PathBuf::from("minters")));
                    if !dir.is_dir() { println!("no minter keys in {} (set ZEN_MINTERS): this node relays and validates, it does not run a pool", dir.display()); vec![] }
                    else {
                        let ks: Vec<mint::Key> = crate::netconf::load_minters(&dir)?.into_iter().map(|w| w.key).collect();
                        if ks.len() > 4 { bail!("{} minter keys in {}: the pool draws tickets from at most four", ks.len(), dir.display()); }
                        for k in &ks { if !c.alloc.iter().any(|(a, _)| *a == k.addr) { bail!("minter {} is not in the genesis allocation of {}: add an alloc line for it, or remove its key", crate::tx::address_string(&k.addr), f.display()); } }
                        ks
                    }
                }
            };
            let genesis: Vec<([F; 4], u64)> = match &conf { Some((c, _)) => c.genesis(), None => dev::genesis_of(&keys) };
            let circ = if real {
                let t = std::time::Instant::now();
                let c = std::sync::Arc::new(crate::prover::Circuits::build(SLOTS_PER_LEAF)?);
                println!("circuits built in {:.1}s", t.elapsed().as_secs_f64());
                Some(c)
            } else { None };
            let g16vk = match &g16 { Some(d) => Some(std::fs::read(d.join("zen.vk")).map_err(|e| anyhow!("no zen.vk in the ZEN_G16 directory: {e}"))?), None => None };
            let verifier = || -> Box<dyn StampVerifier + Send + Sync> {
                match (&g16vk, &circ) { (Some(vk), _) => Box::new(crate::groth16::Groth16Stamp::new(vk).expect("zen.vk does not parse")), (None, Some(c)) => Box::new(crate::prover::Plonky2Stamp::new(c)), _ => Box::new(DevStamp) }
            };
            let pm = circ.as_ref().map(|c| crate::prover::ProverMaker::new(c.clone(), keys.clone()));
            let store = pm.as_ref().map(|p| p.store.clone());
            let ops_slot = pm.as_ref().map(|p| p.ops_pool.clone());
            let maker: Option<std::sync::Arc<dyn StampMaker>> = match (pm, &g16) {
                (Some(p), Some(d)) => {
                    let tool = std::env::var("ZEN_WRAP").map(PathBuf::from).unwrap_or_else(|_| d.join("zenwrap"));
                    let t = std::time::Instant::now();
                    let m = crate::prover::Groth16Maker::new(p, tool, d.clone(), std::env::temp_dir())?;
                    println!("BN254 layer built in {:.1}s | stamps are Groth16 (196 bytes)", t.elapsed().as_secs_f64());
                    Some(std::sync::Arc::new(m))
                }
                (Some(p), None) => Some(std::sync::Arc::new(p)),
                _ => None,
            };
            let maker: std::sync::Arc<dyn StampMaker> = maker.unwrap_or_else(|| std::sync::Arc::new(DevStampMaker));
            let dir = std::env::var("ZEN_DIR").ok().map(PathBuf::from);
            let params = match &conf {
                Some((c, _)) => c.params.clone(),
                None => Params { maturity: std::env::var("ZEN_MATURITY").ok().and_then(|v| v.parse().ok()).unwrap_or(MATURITY_BLOCKS), ..Params::devnet() },
            };
            let node = Node::open(params, &genesis, verifier(), dir.as_deref())?;
            match &conf {
                Some((c, f)) => println!("network {} ({}) from {} | id {}", c.name, crate::netconf::chain_name(node.tip().p.chain), f.display(), seal::hex(&node.network_id())),
                None => println!("devnet: chain Jen, 12 wallets whose secrets are public. For a real test network use ZEN_NET=<net.conf> (zenproof net init)"),
            }
            if node.repaired() > 0 { println!("the log ended in a half-written block: cut {} bytes", node.repaired()); }
            if dir.is_some() { println!("restored height {} from the log{}", node.height(), if node.from_snapshot > 0 { format!(" (state snapshot at height {}, the blocks after it validated)", node.from_snapshot) } else { " (every block validated)".to_string() }); }
            let net = Net::new(node);
            // real proofs of operations carry the wallets' own signatures, found in the node's operation pool
            if let Some(slot) = &ops_slot { *slot.lock().unwrap() = Some(net.ops.clone()); }
            // the local HTTP API for the programs beside the node (ZEN_API=off turns it off)
            let api_addr = std::env::var("ZEN_API").unwrap_or_else(|_| "127.0.0.1:18445".to_string());
            if api_addr != "off" {
                let token = crate::api::load_or_create_token(dir.as_deref())?;
                let at = crate::api::start(net.clone(), &api_addr, token.clone())?;
                match &dir { Some(d) => println!("API on http://{at}/api/status | payments need the token in {}", d.join("api.token").display()), None => println!("API on http://{at}/api/status | token for payments: {token}") }
            }
            let p2p_addr = net.listen(a.get(3).map(|s| s.as_str()).unwrap_or("127.0.0.1:18444"))?;
            // the pool takes its payments from the mempool (wallets send them with `zenproof wallet pay`); a node without minter keys has no pool
            let payout = match std::env::var("ZEN_PAYOUT") { Ok(a) => Some(crate::tx::parse_address(&a)?), Err(_) => keys.first().map(|k| k.addr) };
            let pool = Stratum::new(net.clone(), std::sync::Arc::new(dev::PoolSource { minters: keys.clone(), miner: payout.unwrap_or([F::ZERO; 4]), maker: maker.clone(),
                                                                        pool: net.pool.clone(), store, max_pays: 2 * SLOTS_PER_LEAF, wall_clock: conf.is_some(), ops: Some(net.ops.clone()) }));
            let st_addr = if keys.is_empty() { None } else { Some(pool.listen(a.get(4).map(|s| s.as_str()).unwrap_or("127.0.0.1:13333"))?) };
            // seeds from the file, then any peer addresses on the command line; peers tell each other about more (ADDR), and the node keeps up to 8 outbound
            let mut peers: Vec<String> = conf.as_ref().map(|(c, _)| c.seeds.clone()).unwrap_or_default();
            peers.extend(a.iter().skip(5).cloned());
            for peer in &peers {
                use std::net::ToSocketAddrs;
                match peer.to_socket_addrs().ok().and_then(|mut i| i.next()) {
                    Some(sa) => if let Err(e) = net.connect(sa) { println!("peer {peer}: {e}"); },
                    None => println!("peer {peer}: cannot resolve"),
                }
            }
            net.spawn_maintainer(std::time::Duration::from_secs(10));
            println!("zen node stage 4 | p2p {p2p_addr} | stratum {} | height {}", st_addr.map_or("off (relay only)".to_string(), |a| a.to_string()), net.height());
            let mut last = u64::MAX;
            loop {
                std::thread::sleep(std::time::Duration::from_millis(500));
                let (h, best) = (net.height(), net.best());
                if h != last { last = h; println!("height {h} | tip {} | peers {} | shares accepted {} rejected {}", seal::hex(&best[..8]), net.peer_count(), pool.accepted.load(std::sync::atomic::Ordering::SeqCst), pool.rejected.load(std::sync::atomic::Ordering::SeqCst)); }
            }
        }
        Some("serve-all") => crate::testnet::serve_all(),
        Some("serve-chain") => crate::testnet::serve_chain(),
        Some("mine") => {
            let addr = a.get(3).ok_or_else(|| anyhow!("usage: node mine <stratum addr> [blocks]"))?.parse()?;
            let blocks = a.get(4).and_then(|s| s.parse().ok()).unwrap_or(3);
            let t = std::time::Instant::now();
            let n = p2p::stratum_client_mine(addr, blocks, u64::MAX)?;
            println!("RESULT miner: {n} blocks accepted in {:.1}s", t.elapsed().as_secs_f64());
            Ok(())
        }
        _ => devnet_main(),
    }
}

pub fn devnet_main() -> Result<()> {
    let blocks: usize = std::env::args().nth(3).and_then(|s| s.parse().ok()).unwrap_or(12);
    if std::env::args().nth(2).as_deref() != Some("devnet") && std::env::args().nth(2).is_some() { bail!("unknown node command"); }
    let dir = std::env::temp_dir().join(format!("zen-devnet-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    let mut net = dev::Devnet::new(Some(&dir), 12)?;
    println!("zen node stage 1 | devnet | chain {} | S {} | {} tickets per block | log {}", net.chain.p.chain, net.chain.reading.s, mint::TARGET_BLOWS, dir.display());
    println!("{:>4} | {:>7} | {:>8} | {:>7} | {:>7} | {:>9} | {:>9} | {:>16}", "h", "tickets", "payments", "credits", "bytes", "blow diff", "check (s)", "state root");
    let t_all = std::time::Instant::now();
    for i in 0..blocks {
        // a busier block now and then, so the blow difficulty has something to follow
        let nt = if i % 5 == 3 { 2 * mint::TARGET_BLOWS as usize } else { mint::TARGET_BLOWS as usize };
        let blk = net.next_block(nt, 20 + i % 7)?;
        let t = std::time::Instant::now();
        net.chain.accept(&blk, u32::MAX)?;
        let secs = t.elapsed().as_secs_f64();
        let (_, leaves) = blockdata::decode(&blk.data)?;
        let (np, nc) = leaves.iter().flat_map(|l| l.pays.iter()).fold((0, 0), |(p, c), e| if e.credit { (p, c + 1) } else { (p + 1, c) });
        println!("{:>4} | {:>7} | {:>8} | {:>7} | {:>7} | {:>9} | {:>9.2} | {:016x}", net.chain.height, blk.tickets.len(), np, nc, blk.encode().len(), net.chain.blow_diff, secs, net.chain.root()[0]);
        net.chain.audit()?;
    }
    println!("RESULT {} blocks in {:.1}s | tip {} | supply exact: {} (genesis {} + issued {})", blocks, t_all.elapsed().as_secs_f64(), seal::hex(&net.chain.tip[..8]), net.chain.audit().is_ok(), net.chain.genesis_supply, net.chain.emitted);
    // restart: replay the log, every block fully validated again
    let t = std::time::Instant::now();
    let reopened = Chain::open(Params::devnet(), &dev::genesis_of(&net.keys), Box::new(DevStamp), Some(&dir))?;
    println!("RESULT restart from the log: height {} tip {} {} | {:.1}s to validate {} blocks again", reopened.height, seal::hex(&reopened.tip[..8]),
        if reopened.root() == net.chain.root() && reopened.tip == net.chain.tip && reopened.pool == net.chain.pool { "identical state" } else { "DIFFERENT" }, t.elapsed().as_secs_f64(), reopened.height);
    let _ = std::fs::remove_dir_all(&dir);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    fn err(r: Result<Applied>) -> String { match r { Ok(_) => "ACCEPTED".into(), Err(e) => e.to_string() } }

    /// a snapshot restores a chain that goes on exactly like the original, and a damaged or foreign one is refused
    #[test]
    fn a_snapshot_restores_the_chain_exactly_and_bad_ones_are_refused() {
        let mut net = dev::Devnet::new(None, 8).unwrap();
        net.chain.p.maturity = 2;
        let now = u32::MAX;
        let mut chain = net.chain.clone();
        for _ in 0..7 { let b = net.block_on(&chain, 24, 8).unwrap(); chain.accept(&b, now).unwrap(); }
        let gd = genesis_digest(&dev::genesis_of(&net.keys));
        let bytes = chain.snapshot_bytes(&gd).unwrap();
        assert_eq!(bytes, chain.snapshot_bytes(&gd).unwrap(), "the same state gives the same bytes");
        let verifier = chain.verifier.clone();
        let ver = || verifier.clone();
        let mut back = Chain::from_snapshot(chain.p.clone(), ver(), &gd, &bytes).unwrap();
        assert_eq!((back.height, back.tip, back.root(), back.pool, back.emitted, back.reading.s), (chain.height, chain.tip, chain.root(), chain.pool, chain.emitted, chain.reading.s));
        assert_eq!(back.pending, chain.pending);
        assert_eq!(back.snapshot_bytes(&gd).unwrap(), bytes, "and writes the same snapshot again");
        // both go on alike for more blocks (rewards, retargets, S) and agree at every step
        for _ in 0..5 {
            let b = net.block_on(&chain, 24, 8).unwrap();
            chain.accept(&b, now).unwrap(); back.accept(&b, now).unwrap();
            assert_eq!((back.root(), back.tip, back.emitted, back.pool), (chain.root(), chain.tip, chain.emitted, chain.pool));
            assert_eq!(back.pending, chain.pending);
        }
        assert_eq!(back.snapshot_bytes(&gd).unwrap(), chain.snapshot_bytes(&gd).unwrap());
        back.audit().unwrap();
        // refused: any flipped byte, a cut, another genesis, other parameters
        for i in (0..bytes.len()).step_by(bytes.len() / 40 + 1) {
            let mut bad = bytes.clone(); bad[i] ^= 1;
            assert!(Chain::from_snapshot(chain.p.clone(), ver(), &gd, &bad).is_err(), "byte {i}");
        }
        assert!(Chain::from_snapshot(chain.p.clone(), ver(), &gd, &bytes[..bytes.len() - 1]).is_err());
        assert!(Chain::from_snapshot(chain.p.clone(), ver(), &[7u8; 32], &bytes).is_err(), "another genesis");
        assert!(Chain::from_snapshot(Params { s: 2000, ..chain.p.clone() }, ver(), &gd, &bytes).is_err(), "other parameters");
        assert!(Chain::from_snapshot(chain.p.clone(), ver(), &gd, b"").is_err());
    }

    /// a chain can start with blocks that carry no payments and owe nothing (nothing is credited until the first reward matures)
    #[test]
    fn blocks_with_nothing_in_them_are_blocks() {
        let mut net = dev::Devnet::new(None, 8).unwrap();
        net.chain.p.maturity = 3;
        let now = u32::MAX;
        let mut chain = net.chain.clone();
        for k in 1..=6u64 {
            let b = net.block_on(&chain, 24, 0).unwrap();
            let (_, leaves) = blockdata::decode(&b.data).unwrap();
            if k <= 5 { assert!(leaves.len() == 1 && leaves[0].pays.is_empty(), "block {k} has one empty leaf"); }
            chain.accept(&b, now).unwrap();
            chain.audit().unwrap();
        }
        // block 6 releases block 1's reward: its leaf is not empty any more
        let b = net.block_on(&chain, 24, 0).unwrap();
        let (_, leaves) = blockdata::decode(&b.data).unwrap();
        assert!(!leaves[0].pays.is_empty());
        chain.accept(&b, now).unwrap();
        assert_eq!(chain.height, 7);
    }

    /// a reward waits `maturity` blocks: it is held in `pending` (and counted by the audit), then credited to the miner in the block that releases it
    #[test]
    fn a_reward_is_held_for_the_maturity_period_and_then_credited() {
        let mut net = dev::Devnet::new(None, 8).unwrap();
        net.chain.p.maturity = 3;
        let now = u32::MAX;
        let mut chain = net.chain.clone();
        for k in 1..=9u64 {
            let b = net.block_on(&chain, 24, 8).unwrap();
            let ap = chain.validate(&b, now).unwrap();
            let before: u64 = chain.pending.get(&k).map(|v| v.iter().map(|(_, x)| *x).sum()).unwrap_or(0);
            chain.commit(&b, ap);
            if k >= 2 { assert!(chain.pending.contains_key(&(k + 4)), "the reward of block {} is released in block {}", k - 1, k + 4); }
            if k >= 6 { assert!(before > 0, "block {k} releases the reward of block {}", k - 5); }
            assert!(!chain.pending.contains_key(&k), "block {k}'s entry is spent");
            if k <= 5 { assert_eq!(before, 0, "nothing is released before block 6"); }
            chain.audit().unwrap();
        }
        // block 1's reward (drawn in block 2) is released in block 2 + 1 + 3 = 6; blocks 3..5 have nothing to release
        assert!(chain.pending.keys().all(|h| *h > 9), "everything due by block 9 has been released");
        assert_eq!(chain.pending.keys().copied().collect::<Vec<_>>(), vec![10, 11, 12, 13], "the last four rewards are still held");
    }

    /// SPEC 5.4: the reward of block N is drawn from the seal of block N + 1 and paid in block N + 2; the supply stays exact
    #[test]
    fn a_reward_is_drawn_from_the_next_seal_and_paid_two_blocks_later() {
        let mut net = dev::Devnet::new(None, 8).unwrap();
        let metal = crate::reward::Metal::of_chain(net.chain.p.chain);
        let now = u32::MAX;
        let mut chain = net.chain.clone();
        let mut applied: Vec<(u64, [F; 4], Vec<[F; 4]>, [u8; 32])> = vec![];     // (height, miner, minters, hash) of each block
        let mut expect_emitted = 0u64;
        for k in 1..=6u64 {
            let b = net.block_on(&chain, 24, 8).unwrap();
            let ap = chain.validate(&b, now).unwrap();
            let (miner, minters, hash) = (ap.miner, ap.minters.clone(), ap.hash);
            chain.commit(&b, ap);
            if k >= 2 {
                // block k's seal fixes block k - 1's reward, owed in block k + 1
                let (ph, pm, pms, _) = &applied[k as usize - 2];
                let (total, owed) = crate::reward::payouts(metal, *ph, &hash, *pm, pms);
                expect_emitted += total;
                assert_eq!(chain.pending[&(k + 1)], owed, "block {} is owed in block {}", ph, k + 1);
                assert_eq!(owed.iter().map(|(_, v)| *v).sum::<u64>(), total);
                assert_eq!(chain.emitted, expect_emitted);
            } else { assert!(chain.pending.is_empty() && chain.emitted == 0, "nothing is known after block 1"); }
            applied.push((k, miner, minters, hash));
            chain.audit().unwrap();
        }
        // the same parent with another next block gives another draw for the same block: the miner of block N cannot know V
        let (mut c1, mut c2) = (net.chain.clone(), net.chain.clone());
        let b1 = net.block_on(&c1, 24, 8).unwrap(); c1.accept(&b1, now).unwrap(); c2.accept(&b1, now).unwrap();
        let mut idx = std::collections::HashSet::new();
        for _ in 0..4 { let b2 = net.block_on(&c1, 24, 8).unwrap(); idx.insert(crate::reward::z_index(&b2.header.hash())); }
        assert!(idx.len() >= 3, "different next blocks draw different factors: {idx:?}");
        // rewards are real amounts: block 1 pays between 0 and 2520 x V g, a share of it to the miner
        let (total, _) = crate::reward::payouts(metal, 1, &applied[1].3, applied[0].1, &applied[0].2);
        assert!(total > 0 && total < 300 * crate::reward::INITIAL_REWARD as u64 * crate::reward::UNITS_PER_GRAM);
    }

    /// S is read from the day's counted payments, moves at the anchor's pace, and a second node replaying the same blocks gets the same S
    #[test]
    fn s_is_read_from_payments_across_a_day_boundary() {
        use crate::blockdata::BPD;
        let mut net = dev::Devnet::new(None, 12).unwrap();
        let fresh = |net: &dev::Devnet| Chain::open(Params::devnet(), &dev::genesis_of(&net.keys), Box::new(DevStamp), None).unwrap();
        let mut replica = fresh(&net);
        net.chain.height = BPD * 4 - 3;           // day 3 (rested money counts), two blocks before the day ends
        replica.height = net.chain.height;
        let s0 = net.chain.reading.s;
        let true_s = s0 + s0 / 5;                  // shops now price goods 20% above the genesis guess
        let mut used = vec![];
        for b in 0..3u64 {
            let u = net.chain.reading.s / 6;
            let w = net.keys.len();
            let mut pays = vec![];
            for k in 0..14usize {
                let g = [12u64, 6, 18, 9][k % 4];
                let (a, c) = ((k + b as usize) % w, (k + b as usize + 3) % w);
                let sen = g * u;                                   // Sen-priced: g sixths of a Sen
                let ord = g * true_s / 6 + 1 + k as u64;           // the same goods valued in base units
                pays.push(dev::DevPay { from: net.keys[a].addr, to: net.keys[c].addr, amt: sen, fee: sen / 50 + 1 });
                pays.push(dev::DevPay { from: net.keys[c].addr, to: net.keys[a].addr, amt: ord, fee: ord / 50 + 1 });
            }
            let parent = net.chain.clone();
            let tickets = dev::make_tickets(&parent, &net.keys[..4], 24);
            let blk = dev::build_block(&parent, net.keys[0].addr, tickets, &pays, parent.tip_ntime + 150, &DevStampMaker).unwrap();
            used.push(net.chain.reading.s);
            net.chain.accept(&blk, u32::MAX).unwrap();
            replica.accept(&blk, u32::MAX).unwrap();
            net.chain.audit().unwrap();
        }
        println!("S per block: {:?}; S now {} anchor {} days read {}", used, net.chain.reading.s, net.chain.reading.anchor, net.chain.reading.days_read);
        assert_eq!(used[0], s0); assert_eq!(used[1], s0);          // S holds inside the day
        assert_eq!(net.chain.reading.days_read, 1, "the day was read");
        assert!(net.chain.reading.s > s0, "S moved toward the true value");
        assert!(net.chain.reading.s as f64 <= s0 as f64 * 1.1 + 6.0, "but by at most the day clip");
        assert_eq!(net.chain.reading.s, used[2]);                  // block 3 was built and accepted at the new S
        assert_eq!(replica.reading.s, net.chain.reading.s);
        assert_eq!(replica.reading.anchor, net.chain.reading.anchor);
        assert_eq!(replica.root(), net.chain.root());
        // a block that still uses the old S is rejected
        let parent = net.chain.clone();
        let tickets = dev::make_tickets(&parent, &net.keys[..4], 24);
        let mut blk = dev::build_block(&parent, net.keys[0].addr, tickets, &[], parent.tip_ntime + 150, &DevStampMaker).unwrap();
        blk.pubvalues[14] = s0; dev::reseal(&parent, &mut blk);
        assert!(err(parent.validate(&blk, u32::MAX)).contains("public values"));
    }

    #[test]
    fn chain_accepts_blocks_and_rejects_each_kind_of_bad_block() {
        let mut net = dev::Devnet::new(None, 8).unwrap();
        for _ in 0..3 { let b = net.next_block(24, 12).unwrap(); net.chain.accept(&b, u32::MAX).unwrap(); net.chain.audit().unwrap(); }
        // block 3 paid rewards of block 1; the credits were checked exactly
        let good = net.next_block(24, 12).unwrap();
        net.chain.validate(&good, u32::MAX).unwrap();
        let c = &net.chain;
        // encode / decode round trip
        let rt = Block::decode(&good.encode()).unwrap();
        assert_eq!(rt.encode(), good.encode());
        assert!(Block::decode(&good.encode()[..100]).is_err());
        // wrong previous block, wrong time
        let mut b = good.clone(); b.header.prev[0] ^= 1;
        assert!(err(c.validate(&b, u32::MAX)).contains("previous block"));
        let mut b = good.clone(); b.header.ntime = c.tip_ntime;
        assert!(err(c.validate(&b, u32::MAX)).contains("time not after"));
        let mut b = good.clone(); b.header.ntime = u32::MAX / 2;
        assert!(err(c.validate(&b, 1_700_000_000)).contains("too far ahead"));
        // a seal that does not meet the target
        let mut b = good.clone();
        loop { b.header.nonce = b.header.nonce.wrapping_add(1); if !seal::meets(&b.header.hash(), b.header.nbits) { break; } }
        assert!(err(c.validate(&b, u32::MAX)).contains("target"));
        // a body changed after sealing
        let mut b = good.clone(); b.stamp[0] ^= 1;
        assert!(err(c.validate(&b, u32::MAX)).contains("commitment"));
        // no tickets, too many tickets
        let mut b = good.clone(); b.tickets.clear(); dev::reseal(c, &mut b);
        assert!(err(c.validate(&b, u32::MAX)).contains("tickets"));
        // the same blow twice
        let mut b = good.clone(); let t0 = b.tickets[0].clone(); *b.tickets.last_mut().unwrap() = t0; dev::reseal(c, &mut b);
        assert!(err(c.validate(&b, u32::MAX)).contains("twice"));
        // a ticket from another block (its signature names the previous block)
        let mut b = good.clone(); b.tickets[1].nonce += 1; dev::reseal(c, &mut b);
        assert!(err(c.validate(&b, u32::MAX)).contains("signature"));
        // block data: one credit one unit too high
        let (slots, mut leaves) = blockdata::decode(&good.data).unwrap();
        let e = leaves.iter_mut().flat_map(|l| l.pays.iter_mut()).find(|e| e.credit).unwrap(); e.amt += 1;
        let mut b = good.clone(); b.data = blockdata::encode(slots, &leaves); dev::reseal(c, &mut b);
        assert!(err(c.validate(&b, u32::MAX)).contains("credits differ"));
        // block data changed but public values and stamp kept
        let mut b = good.clone(); let n = b.data.len(); b.data[n - 1] ^= 1; dev::reseal(c, &mut b);
        assert!(err(c.validate(&b, u32::MAX)).len() > 0 && !err(c.validate(&b, u32::MAX)).contains("ACCEPTED"));
        // public values changed (and a matching stamp): they differ from the node's own replay
        let mut b = good.clone(); b.pubvalues[9] += 1; b.stamp = DevStamp::make(&b.pubvalues); dev::reseal(c, &mut b);
        assert!(err(c.validate(&b, u32::MAX)).contains("public values differ"));
        // a stamp that does not prove the public values
        let mut b = good.clone(); b.stamp[3] ^= 1; dev::reseal(c, &mut b);
        assert!(err(c.validate(&b, u32::MAX)).contains("stamp"));
        // none of that changed the chain, and the good block still goes in
        net.chain.accept(&good, u32::MAX).unwrap();
        net.chain.audit().unwrap();
        assert_eq!(net.chain.height, 4);
    }

    #[test]
    fn restart_from_the_log_gives_the_same_chain() {
        let dir = std::env::temp_dir().join(format!("zen-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let mut net = dev::Devnet::new(Some(&dir), 6).unwrap();
        for _ in 0..3 { let b = net.next_block(24, 8).unwrap(); net.chain.accept(&b, u32::MAX).unwrap(); }
        let keys = &net.keys;
        let again = Chain::open(Params::devnet(), &dev::genesis_of(keys), Box::new(DevStamp), Some(&dir)).unwrap();
        assert_eq!((again.height, again.tip, again.root(), again.pool), (net.chain.height, net.chain.tip, net.chain.root(), net.chain.pool));
        assert_eq!(again.pending, net.chain.pending);
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn seal_difficulty_follows_the_window() {
        let p = Params { bits0: 0x1d00_ffff, ..Params::devnet() };
        let exp = p.window * p.block_secs;
        let tgt = |b: u32| seal::bits_to_target(b).unwrap();
        // on time: unchanged (within compact rounding)
        let b0 = 0x1c00_ffff;
        assert_eq!(retarget_bits(&p, b0, exp), b0);
        // twice as fast: target halves; ten times as fast: still only halves
        assert_eq!(tgt(retarget_bits(&p, b0, exp / 2)), tgt(b0) / 2u32);
        assert_eq!(retarget_bits(&p, b0, exp / 10), retarget_bits(&p, b0, exp / 2));
        // slower: target doubles, but never above the starting target
        assert_eq!(tgt(retarget_bits(&p, b0, exp * 2)), tgt(b0) * 2u32);
        assert_eq!(retarget_bits(&p, p.bits0, exp * 5), p.bits0);
    }
}
