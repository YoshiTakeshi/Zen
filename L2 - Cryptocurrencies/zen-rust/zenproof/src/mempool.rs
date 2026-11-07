// The mempool (stage 4, Justus L. Ludovic): signed payments waiting for a block, checked against the chain tip.
//
// Admission (all of them, in order of cost): the right size; amounts inside the consensus limits the block replay enforces
// (smallest payment and fee from S, fee between 0.01% and 6% of what leaves the account); the sender has an account; the
// signature; the nonce (the account's next nonce plus the sender's payments already waiting, so a sender queues up to
// MAX_PER_SENDER payments in order); the balance covers everything the sender has waiting; closing an account is not
// taken yet (the builder has no close). A payment with the nonce of one already waiting replaces it only if its fee is at
// least 10% higher (replace-by-fee); payments after it that no longer fit the balance are dropped.
// The pool holds at most `max` payments; when full, a payment is taken only if it pays a higher fee rate than the worst
// one, which leaves together with the later payments of the same sender.
// After each block `on_block` drops what was confirmed or can no longer apply. A payment that was confirmed is remembered
// for MAX_REORG blocks (at most ARCHIVE_MAX of them); if a reorg takes its block away and the account's nonce is back at
// the payment's, it goes back into the pool. (Blocks carry no signatures, so only payments this node has seen can come back.)
use crate::node::Chain;
use crate::tx::{addr_key, SignedPay};
use crate::F;
use anyhow::{bail, Result};
use std::collections::{BTreeMap, BinaryHeap, HashMap, VecDeque};

pub const MAX_PER_SENDER: usize = 16;
const ARCHIVE_MAX: usize = 20_000;

#[derive(Debug, PartialEq, Eq)]
pub enum Admit { New, Replaced }

#[derive(Clone)]
struct Entry { tx: SignedPay, from: [F; 4] }
pub struct Mempool {
    txs: HashMap<[u8; 32], Entry>,
    by_sender: HashMap<[u64; 4], BTreeMap<u64, [u8; 32]>>,
    pub max: usize,
    /// payments that were confirmed, with the height of the tip when they were seen confirmed
    archive: VecDeque<(u64, [F; 4], SignedPay)>,
}
fn rate(tx: &SignedPay) -> u128 { tx.fee as u128 * 1_000_000 / (tx.amt as u128 + tx.fee as u128).max(1) }

impl Mempool {
    pub fn new(max: usize) -> Mempool { Mempool { txs: HashMap::new(), by_sender: HashMap::new(), max, archive: VecDeque::new() } }
    pub fn len(&self) -> usize { self.txs.len() }
    pub fn get(&self, id: &[u8; 32]) -> Option<&SignedPay> { self.txs.get(id).map(|e| &e.tx) }
    pub fn contains(&self, id: &[u8; 32]) -> bool { self.txs.contains_key(id) }
    /// up to `max` waiting payments, best fee rate first, with their senders
    pub fn list(&self, max: usize) -> Vec<([u8; 32], SignedPay, [F; 4])> {
        let mut v: Vec<_> = self.txs.iter().map(|(id, e)| (*id, e.tx.clone(), e.from)).collect();
        v.sort_by(|a, b| rate(&b.1).cmp(&rate(&a.1)).then(a.0.cmp(&b.0)));
        v.truncate(max);
        v
    }
    /// how many payments of this sender wait, and the nonce its next one must carry
    pub fn next_nonce(&self, chain: &Chain, addr: &[F; 4]) -> Option<u64> {
        let (_, acct) = chain.account(addr)?;
        Some(acct.nonce + self.by_sender.get(&addr_key(addr)).map_or(0, |q| q.len() as u64))
    }
    pub fn pending_spend(&self, addr: &[F; 4]) -> u128 {
        self.by_sender.get(&addr_key(addr)).map_or(0, |q| q.values().map(|id| { let t = &self.txs[id].tx; t.amt as u128 + t.fee as u128 }).sum())
    }

    fn remove(&mut self, id: &[u8; 32]) {
        if let Some(e) = self.txs.remove(id) {
            let k = addr_key(&e.from);
            if let Some(q) = self.by_sender.get_mut(&k) { q.remove(&e.tx.nonce); if q.is_empty() { self.by_sender.remove(&k); } }
        }
    }
    /// drop the payments of `from` with nonce >= `n` (they follow a payment that went)
    fn drop_from(&mut self, from: &[F; 4], n: u64) {
        let ids: Vec<[u8; 32]> = self.by_sender.get(&addr_key(from)).map_or(vec![], |q| q.range(n..).map(|(_, id)| *id).collect());
        for id in ids { self.remove(&id); }
    }

    pub fn admit(&mut self, chain: &Chain, tx: SignedPay) -> Result<Admit> {
        let id = tx.id();
        if self.txs.contains_key(&id) { bail!("known"); }
        if tx.close { bail!("closing an account is not taken yet"); }
        // consensus limits, as Chain::validate's replay applies them
        let s = chain.reading.s as u128;
        if tx.amt >= 1 << 62 || tx.fee >= 1 << 62 { bail!("amount or fee out of range"); }
        let spend = tx.amt as u128 + tx.fee as u128;
        if tx.amt as u128 * 6 < s { bail!("below the smallest payment"); }
        if tx.fee as u128 * 100 < s { bail!("below the smallest fee"); }
        if (tx.fee as u128) * 10_000 < spend { bail!("fee below 0.01%"); }
        if (tx.fee as u128) * 100 > 6 * spend { bail!("fee above 6%"); }
        let (_, from) = tx.verify()?;
        if from == tx.to { bail!("payment to itself"); }
        let Some((_, acct)) = chain.account(&from) else { bail!("the sender has no account") };
        let fk = addr_key(&from);
        let q = self.by_sender.get(&fk);
        let waiting = q.map_or(0, |q| q.len() as u64);
        let replacing = q.and_then(|q| q.get(&tx.nonce)).copied();
        match replacing {
            Some(old_id) => {
                let old = &self.txs[&old_id].tx;
                if (tx.fee as u128) < old.fee as u128 + old.fee as u128 / 10 + 1 { bail!("replacement must pay at least 10% more fee"); }
            }
            None => {
                if tx.nonce != acct.nonce + waiting { bail!("nonce {} (the next is {})", tx.nonce, acct.nonce + waiting); }
                if waiting as usize >= MAX_PER_SENDER { bail!("too many payments waiting for this sender"); }
            }
        }
        // the balance must cover every payment of this sender that waits, this one included
        let others: u128 = q.map_or(0, |q| q.iter().filter(|(n, _)| **n != tx.nonce).map(|(_, id)| { let t = &self.txs[id].tx; t.amt as u128 + t.fee as u128 }).sum());
        if others + spend > acct.bal as u128 { bail!("balance {} does not cover {}", acct.bal, others + spend); }
        // room
        if replacing.is_none() && self.txs.len() >= self.max {
            let worst = self.txs.values().min_by_key(|e| rate(&e.tx)).map(|e| (e.tx.id(), e.from, e.tx.nonce, rate(&e.tx)));
            match worst { Some((wid, wfrom, wn, wr)) if rate(&tx) > wr => { let _ = wid; self.drop_from(&wfrom, wn); } _ => bail!("the pool is full of payments paying more") }
        }
        if let Some(old_id) = replacing { self.remove(&old_id); }
        self.by_sender.entry(fk).or_default().insert(tx.nonce, id);
        self.txs.insert(id, Entry { tx, from });
        if replacing.is_some() { self.revalidate(chain, &from); Ok(Admit::Replaced) } else { Ok(Admit::New) }
    }

    /// keep a sender's waiting payments only while they follow the account's nonce and fit its balance
    fn revalidate(&mut self, chain: &Chain, from: &[F; 4]) {
        let Some((_, acct)) = chain.account(from) else { self.drop_from(from, 0); return };
        let (bal, mut next, mut spent) = (acct.bal as u128, acct.nonce, 0u128);
        let entries: Vec<(u64, [u8; 32])> = self.by_sender.get(&addr_key(from)).map_or(vec![], |q| q.iter().map(|(n, id)| (*n, *id)).collect());
        for (n, id) in entries {
            if n < next {                                                       // already applied: confirmed
                if let Some(e) = self.txs.get(&id) { self.archive.push_back((chain.height, e.from, e.tx.clone())); if self.archive.len() > ARCHIVE_MAX { self.archive.pop_front(); } }
                self.remove(&id); continue;
            }
            let t = &self.txs[&id].tx;
            let sp = t.amt as u128 + t.fee as u128;
            if n != next || spent + sp > bal { self.drop_from(from, n); return; }
            spent += sp; next += 1;
        }
    }

    pub fn archived(&self) -> usize { self.archive.len() }
    /// after a block is committed: drop what it confirmed and what no longer applies; take back payments whose block was lost
    pub fn on_block(&mut self, chain: &Chain) {
        let senders: Vec<[F; 4]> = self.txs.values().map(|e| e.from).collect::<Vec<_>>();
        let mut seen = std::collections::HashSet::new();
        for f in senders { if seen.insert(addr_key(&f)) { self.revalidate(chain, &f); } }
        // forget old confirmations; a confirmed payment whose account is back at its nonce was reorganized away
        let keep_from = chain.height.saturating_sub(crate::node::MAX_REORG);
        self.archive.retain(|(h, _, _)| *h >= keep_from);
        let mut back: Vec<SignedPay> = vec![];
        for (_, from, t) in &self.archive {
            if chain.account(from).is_some_and(|(_, a)| t.nonce >= a.nonce) { back.push(t.clone()); }
        }
        if back.is_empty() { return; }
        back.sort_by_key(|t| t.nonce);                                        // each sender's payments in nonce order
        for t in back {
            let id = t.id();
            let _ = self.admit(chain, t);
            self.archive.retain(|(_, _, a)| a.id() != id);
        }
    }

    /// up to `max` payments for the next block: highest fee rate first, each sender's payments in nonce order
    pub fn select(&self, chain: &Chain, max: usize) -> Vec<SignedPay> {
        let mut heads: BinaryHeap<(u128, [u64; 4], u64)> = BinaryHeap::new();   // (rate, sender, nonce)
        let first = |k: &[u64; 4], q: &BTreeMap<u64, [u8; 32]>| -> Option<(u128, [u64; 4], u64)> {
            let addr = k.map(|x| plonky2::field::types::Field::from_canonical_u64(x));
            let (_, acct) = chain.account(&addr)?;
            let id = q.get(&acct.nonce)?;
            Some((rate(&self.txs[id].tx), *k, acct.nonce))
        };
        for (k, q) in &self.by_sender { if let Some(h) = first(k, q) { heads.push(h); } }
        let mut out = vec![];
        let mut spent: HashMap<[u64; 4], u128> = HashMap::new();
        while out.len() < max {
            let Some((_, k, n)) = heads.pop() else { break };
            let q = &self.by_sender[&k];
            let tx = &self.txs[&q[&n]].tx;
            let addr: [F; 4] = k.map(|x| plonky2::field::types::Field::from_canonical_u64(x));
            let bal = chain.account(&addr).map_or(0, |(_, a)| a.bal as u128);
            let sp = spent.entry(k).or_insert(0);
            if *sp + tx.amt as u128 + tx.fee as u128 > bal { continue; }
            *sp += tx.amt as u128 + tx.fee as u128;
            out.push(tx.clone());
            if let Some(id) = q.get(&(n + 1)) { heads.push((rate(&self.txs[id].tx), k, n + 1)); }
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::node::{dev, DevStamp, Params};
    use crate::tx::Wallet;
    use num_bigint::BigUint;

    fn setup() -> (Chain, Vec<Wallet>) {
        let ws: Vec<Wallet> = (0..4).map(|i| Wallet::from_secret(BigUint::from(1_000_003u64 + 7919 * i as u64))).collect();
        let genesis: Vec<([F; 4], u64)> = ws.iter().map(|w| (w.address(), 1_000_000_000)).collect();
        (Chain::open(Params::devnet(), &genesis, Box::new(DevStamp), None).unwrap(), ws)
    }
    fn err(r: Result<Admit>) -> String { match r { Ok(a) => format!("{a:?}"), Err(e) => e.to_string() } }

    #[test]
    fn admission_rules() {
        let (chain, ws) = setup();
        let mut mp = Mempool::new(100);
        let (a, b) = (&ws[0], &ws[1]);
        let pay = |n: u64, amt: u64| a.pay(b.address(), amt, Wallet::standard_fee(amt), n);
        assert_eq!(mp.admit(&chain, pay(0, 100_000)).unwrap(), Admit::New);
        assert_eq!(err(mp.admit(&chain, pay(0, 100_000))), "known");
        assert!(err(mp.admit(&chain, pay(5, 100_000))).contains("nonce 5 (the next is 1)"));
        assert_eq!(mp.admit(&chain, pay(1, 200_000)).unwrap(), Admit::New);
        assert_eq!(mp.next_nonce(&chain, &a.address()), Some(2));
        // replace-by-fee: needs 10% more
        let same = a.pay(b.address(), 100_000, 1_050, 0);
        assert!(err(mp.admit(&chain, a.pay(b.address(), 100_000, 1_050, 0))).contains("10% more"), "{:?}", same.fee);
        assert_eq!(mp.admit(&chain, a.pay(b.address(), 100_000, 1_200, 0)).unwrap(), Admit::Replaced);
        assert_eq!(mp.len(), 2);
        // overspending the balance, in total
        assert!(err(mp.admit(&chain, pay(2, 999_000_000))).contains("does not cover"));
        // limits of consensus
        assert!(err(mp.admit(&chain, a.pay(b.address(), 100_000, 1, 2))).contains("fee"));
        assert!(err(mp.admit(&chain, a.pay(b.address(), 1, 1_000, 2))).contains("smallest payment"));
        assert!(err(mp.admit(&chain, a.pay(b.address(), 100_000, 20_000, 2))).contains("fee above 6%"));
        // self payment, unknown sender, bad signature
        assert!(err(mp.admit(&chain, a.pay(a.address(), 100_000, 1_001, 2))).contains("itself"));
        let stranger = Wallet::from_secret(BigUint::from(5u64));
        assert!(err(mp.admit(&chain, stranger.pay(b.address(), 100_000, 1_001, 0))).contains("no account"));
        let mut bad = pay(2, 100_000); bad.amt += 1;
        assert!(err(mp.admit(&chain, bad)).contains("signature"));
        let mut c = pay(2, 100_000); c.close = true;
        assert!(err(mp.admit(&chain, c)).contains("closing"));
    }

    #[test]
    fn replacement_never_strands_later_payments() {
        let (chain, ws) = setup();
        let mut mp = Mempool::new(100);
        let (a, b) = (&ws[0], &ws[1]);
        mp.admit(&chain, a.pay(b.address(), 400_000_000, 4_000_000, 0)).unwrap();
        mp.admit(&chain, a.pay(b.address(), 500_000_000, 5_000_000, 1)).unwrap();
        assert_eq!(mp.len(), 2);
        // a replacement of nonce 0 that would leave nonce 1 without funds is refused
        assert!(err(mp.admit(&chain, a.pay(b.address(), 600_000_000, 6_000_000, 0))).contains("does not cover"));
        assert_eq!(mp.len(), 2);
        // one that fits (10% more fee) goes through and the later payment stays
        assert_eq!(mp.admit(&chain, a.pay(b.address(), 400_000_000, 4_500_000, 0)).unwrap(), Admit::Replaced);
        assert_eq!(mp.len(), 2);
    }

    #[test]
    fn full_pool_keeps_the_best_rates() {
        let (chain, ws) = setup();
        let mut mp = Mempool::new(3);
        let b = ws[3].address();
        for i in 0..3 { mp.admit(&chain, ws[i].pay(b, 100_000, 1_000 + 100 * i as u64, 0)).unwrap(); }
        // too cheap: refused; better: takes the place of the worst
        assert!(err(mp.admit(&chain, ws[0].pay(b, 100_000, 1_000, 1))).contains("full"));
        assert!(mp.admit(&chain, ws[0].pay(b, 100_000, 5_000, 1)).is_ok());
        assert_eq!(mp.len(), 3);
        assert!(mp.next_nonce(&chain, &ws[0].address()).is_some());
    }

    #[test]
    fn selection_orders_by_rate_and_nonce_and_blocks_clear_the_pool() {
        let (chain0, ws) = setup();
        let mut mp = Mempool::new(100);
        let b = ws[3].address();
        // sender 0: a cheap payment first, then a rich one that can only follow it
        mp.admit(&chain0, ws[0].pay(b, 100_000, 1_000, 0)).unwrap();
        mp.admit(&chain0, ws[0].pay(b, 100_000, 5_000, 1)).unwrap();
        mp.admit(&chain0, ws[1].pay(b, 100_000, 3_000, 0)).unwrap();
        mp.admit(&chain0, ws[2].pay(b, 100_000, 2_000, 0)).unwrap();
        let sel = mp.select(&chain0, 10);
        let fees: Vec<u64> = sel.iter().map(|t| t.fee).collect();
        assert_eq!(fees, vec![3_000, 2_000, 1_000, 5_000]);       // 5,000 waits behind its sender's first payment
        assert_eq!(mp.select(&chain0, 2).len(), 2);
        // a block with those payments (the builder takes them in this order)
        let mut net = dev::Devnet::new(None, 4).unwrap();
        assert_eq!(net.chain.root(), chain0.root(), "same genesis");
        let pays: Vec<dev::DevPay> = sel.iter().map(|t| dev::DevPay { from: t.verify().unwrap().1, to: t.to, amt: t.amt, fee: t.fee }).collect();
        let parent = net.chain.clone();
        let tickets = dev::make_tickets(&parent, &net.keys[..4], 24);
        let blk = dev::build_block(&parent, net.keys[0].addr, tickets, &pays, parent.tip_ntime + 150, &crate::node::DevStampMaker).unwrap();
        net.chain.accept(&blk, u32::MAX).unwrap();
        mp.on_block(&net.chain);
        assert_eq!(mp.len(), 0, "everything was confirmed");
        // the account nonces moved
        assert_eq!(net.chain.account(&ws[0].address()).unwrap().1.nonce, 2);
    }

    #[test]
    fn a_payment_comes_back_when_its_block_is_lost_in_a_reorg() {
        let mut net = dev::Devnet::new(None, 4).unwrap();
        let chain0 = net.chain.clone();
        let w0 = Wallet { key: net.keys[0].clone() };
        let amt = 100_000;
        let tx = w0.pay(net.keys[1].addr, amt, Wallet::standard_fee(amt), 0);
        let mut mp = Mempool::new(100);
        mp.admit(&chain0, tx.clone()).unwrap();
        let pays = [dev::DevPay { from: net.keys[0].addr, to: net.keys[1].addr, amt, fee: Wallet::standard_fee(amt) }];
        let build = |parent: &Chain, pays: &[dev::DevPay], net: &dev::Devnet| {
            let t = dev::make_tickets(parent, &net.keys[..4], 24);
            dev::build_block(parent, net.keys[0].addr, t, pays, parent.tip_ntime + 150, &crate::node::DevStampMaker).unwrap()
        };
        // branch A confirms the payment
        let a1 = build(&chain0, &pays, &net);
        let mut ca = chain0.clone(); ca.accept(&a1, u32::MAX).unwrap();
        mp.on_block(&ca);
        assert_eq!((mp.len(), mp.archived()), (0, 1), "confirmed: out of the pool, remembered");
        // branch B, two blocks, does not have it
        let other = [dev::DevPay { from: net.keys[2].addr, to: net.keys[3].addr, amt, fee: Wallet::standard_fee(amt) }];
        let b1 = build(&chain0, &other, &net);
        let mut cb = chain0.clone(); cb.accept(&b1, u32::MAX).unwrap();
        let other2 = [dev::DevPay { from: net.keys[3].addr, to: net.keys[2].addr, amt, fee: Wallet::standard_fee(amt) }];
        let b2 = build(&cb, &other2, &net); cb.accept(&b2, u32::MAX).unwrap();
        net.chain = cb.clone();
        mp.on_block(&cb);
        assert_eq!((mp.len(), mp.archived()), (1, 0), "the reorg took its block away: back in the pool");
        assert_eq!(mp.select(&cb, 10).len(), 1);
        // and when the payment is confirmed again it is remembered again, not duplicated
        let b3 = build(&cb, &pays, &net); cb.accept(&b3, u32::MAX).unwrap();
        mp.on_block(&cb);
        assert_eq!((mp.len(), mp.archived()), (0, 1));
        // old confirmations are forgotten after MAX_REORG blocks
        let mut far = cb.clone(); far.height += crate::node::MAX_REORG + 1;
        mp.on_block(&far);
        assert_eq!(mp.archived(), 0);
    }
}
