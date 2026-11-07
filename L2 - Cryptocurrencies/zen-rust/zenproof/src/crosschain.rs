// Following the other chains (SPEC 8.4). A chain's node keeps the headers of the other two chains and checks what a light client can check:
// the seal (proof of work at the difficulty the header chain itself dictates), the commitment that ties the header to the block's public values
// and stamp, the stamp, the height, and that every block starts from the state root the one before it ended with. It does not replay payments or
// check tickets; the stamp is what vouches for the state transition. With these headers a transaction on one chain can be shown to have happened
// on another without a bridge (the order claims of 8.2 will use `root_at` and `hash_at`).
// Block validity on a chain never reads this data except in transactions that say so (claims); everything else stays independent (SPEC 6.3).
use crate::node::{self, Block, Node, Params, StampVerifier, PUBVALUES};
use crate::seal;
use anyhow::{bail, Result};
use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

#[derive(Clone, Debug, PartialEq)]
pub struct Hdr { pub hash: [u8; 32], pub ntime: u32, pub root: [u64; 4], pub payments: u64, bits_after: u32, win_start_after: u32, win_n_after: u64, work_total: u128 }

/// the verified headers of one chain, from height 1
#[derive(Clone)]
pub struct HeaderChain {
    pub p: Params,
    genesis_root: [u64; 4],
    genesis_hash: [u8; 32],
    hdrs: Vec<Hdr>,
    verifier: Arc<dyn StampVerifier + Send + Sync>,
}
impl HeaderChain {
    pub fn new(p: Params, genesis_root: [u64; 4], verifier: Box<dyn StampVerifier + Send + Sync>) -> HeaderChain {
        let genesis_hash = node::genesis_hash(p.chain);
        HeaderChain { p, genesis_root, genesis_hash, hdrs: vec![], verifier: Arc::from(verifier) }
    }
    pub fn height(&self) -> u64 { self.hdrs.len() as u64 }
    /// the proof of work behind the tip: what "the best chain" means (a longer chain at an easier difficulty has less)
    pub fn work(&self) -> u128 { self.hdrs.last().map_or(0, |h| h.work_total) }
    fn tip_hash(&self) -> [u8; 32] { self.hdrs.last().map_or(self.genesis_hash, |h| h.hash) }
    fn state_after(&self) -> (u32, u32, u64, [u64; 4]) {
        match self.hdrs.last() { Some(h) => (h.bits_after, h.win_start_after, h.win_n_after, h.root), None => (self.p.bits0, self.p.genesis_time, 0, self.genesis_root) }
    }
    pub fn hash_at(&self, h: u64) -> Option<[u8; 32]> { if h == 0 { Some(self.genesis_hash) } else { self.hdrs.get(h as usize - 1).map(|x| x.hash) } }
    pub fn header(&self, h: u64) -> Option<&Hdr> { if h == 0 { None } else { self.hdrs.get(h as usize - 1) } }
    pub fn root_at(&self, h: u64) -> Option<[u64; 4]> { if h == 0 { Some(self.genesis_root) } else { self.hdrs.get(h as usize - 1).map(|x| x.root) } }
    /// the next block, checked as a light client can; changes nothing when it fails
    pub fn push(&mut self, blk: &Block) -> Result<()> {
        let h = self.height() + 1;
        let (bits, win_start, win_n, root) = self.state_after();
        if blk.pubvalues.len() != PUBVALUES { bail!("wrong number of public values"); }
        if blk.header.ntime <= self.hdrs.last().map_or(self.p.genesis_time, |x| x.ntime) { bail!("time not after the previous block"); }
        seal::check_seal(&blk.header, &blk.coinbase, self.p.chain, h, &self.tip_hash(), &blk.body_root(), bits)?;
        if blk.pubvalues[15] != h { bail!("the block says it is height {}, not {h}", blk.pubvalues[15]); }
        if blk.pubvalues[0..4] != root { bail!("the block does not start from the state the last one ended in"); }
        self.verifier.verify(&blk.pubvalues, &blk.stamp)?;
        let (mut nb, mut ws, mut wn) = (bits, win_start, win_n + 1);
        if wn == self.p.window { nb = node::retarget_bits(&self.p, bits, (blk.header.ntime - win_start) as u64); ws = blk.header.ntime; wn = 0; }
        self.hdrs.push(Hdr { hash: blk.hash(), ntime: blk.header.ntime, root: [blk.pubvalues[4], blk.pubvalues[5], blk.pubvalues[6], blk.pubvalues[7]],
                             payments: blk.pubvalues[9], bits_after: nb, win_start_after: ws, win_n_after: wn, work_total: self.work().saturating_add(node::work_of_bits(bits)) });
        Ok(())
    }
    /// our hashes from the tip back, thinning out, ending at the genesis (what a node needs to find where we agree with it)
    pub fn locator(&self) -> Vec<[u8; 32]> {
        let (mut out, mut step, mut h) = (vec![], 1u64, self.height());
        loop {
            out.push(self.hash_at(h).unwrap());
            if h == 0 { break; }
            h = h.saturating_sub(step);
            if out.len() >= 10 { step *= 2; }
        }
        out
    }
    /// catch up with a full node of this chain over the network. Nothing the node says is trusted: every block is checked as a light client can
    /// (seal at the difficulty the headers dictate, commitment, stamp, state chaining), and a reorg is followed only by blocks that pass the same checks.
    /// Returns how many headers were added. At most `max` blocks per call.
    pub fn follow(&mut self, addr: std::net::SocketAddr, network_id: [u8; 32], max: u64) -> Result<u64> {
        let mut probe = crate::p2p::Probe::connect(addr, network_id, self.genesis_hash)?;
        let mut added = 0;
        while added < max && self.tip_hash() != probe.tip {
            let Some(blk) = probe.next(&self.locator())? else { break };
            // where it attaches: our block it builds on (the node's best chain may have left ours behind)
            let Some(k) = (0..=self.height()).rev().find(|k| self.hash_at(*k) == Some(blk.header.prev)) else { bail!("a block that attaches to nothing we hold") };
            self.rollback_to(k);
            if let Err(e) = self.push(&blk) { bail!("block {} of chain {}: {e}", k + 1, self.p.chain); }
            added += 1;
        }
        Ok(added)
    }
    pub fn rollback_to(&mut self, h: u64) { self.hdrs.truncate(h as usize); }
    /// catch up with a node's best chain: step back to where the two agree, then take the new blocks. Returns how many headers were added.
    /// A block that fails the checks stops the sync there (and is reported); the headers before it stay.
    pub fn sync(&mut self, n: &Node) -> Result<u64> {
        let mut h = self.height().min(n.height());
        while h > 0 && n.hash_at(h) != self.hash_at(h) { h -= 1; }
        self.rollback_to(h);
        let from = h;
        while self.height() < n.height() {
            let next = self.height() + 1;
            let Some(hash) = n.hash_at(next) else { break };
            let Some(blk) = n.block(&hash) else { bail!("block {next} is not available") };
            self.push(&blk).map_err(|e| anyhow::anyhow!("block {next} of chain {}: {e}", self.p.chain))?;
        }
        Ok(self.height() - from)
    }
}

/// what one chain's node knows about the others: a header chain per other chain, kept up to date by a thread
pub struct Observer { pub me: u8, pub views: Arc<Mutex<BTreeMap<u8, HeaderChain>>>, pub last_error: Arc<Mutex<BTreeMap<u8, String>>> }
impl Observer {
    /// `others`: for each other chain, its Net (the in-process source of blocks), its parameters, genesis root and the verifier for its stamps
    pub fn spawn(me: u8, others: Vec<(crate::p2p::Net, HeaderChain)>, every: std::time::Duration) -> Observer {
        let views = Arc::new(Mutex::new(BTreeMap::new()));
        let last_error = Arc::new(Mutex::new(BTreeMap::new()));
        let mut srcs = vec![];
        for (net, hc) in others { let c = hc.p.chain; views.lock().unwrap().insert(c, hc); srcs.push((c, net)); }
        let (v2, e2) = (views.clone(), last_error.clone());
        std::thread::spawn(move || loop {
            for (c, net) in &srcs {
                // take a copy of what is needed under the node's lock, check outside it would be better; blocks are small and checks take about a millisecond
                let r = { let n = net.node.lock().unwrap(); v2.lock().unwrap().get_mut(c).map(|hc| hc.sync(&n)) };
                match r { Some(Err(e)) => { e2.lock().unwrap().insert(*c, e.to_string()); } _ => { e2.lock().unwrap().remove(c); } }
            }
            std::thread::sleep(every);
        });
        Observer { me, views, last_error }
    }
    /// for the API: what this node sees of each other chain
    pub fn json(&self) -> serde_json::Value {
        let v = self.views.lock().unwrap(); let e = self.last_error.lock().unwrap();
        serde_json::Value::Array(v.iter().map(|(c, hc)| {
            let tip = hc.hash_at(hc.height()).unwrap();
            serde_json::json!({"chain": c, "name": crate::netconf::chain_name(*c), "headers_checked": hc.height(), "tip": seal::hex(&tip), "problem": e.get(c)})
        }).collect())
    }
}

/// one other chain followed over the network: where its full nodes are, and what to check them against
pub struct Remote { pub hc: HeaderChain, pub peers: Vec<std::net::SocketAddr>, pub network_id: [u8; 32] }
impl Observer {
    /// follow the other chains through their full nodes' p2p ports (any machine). Several nodes per chain are followed side by side
    /// and the longest chain that checks out is the view, so one lying or stale node cannot hide the truth or fake a block.
    pub fn spawn_net(me: u8, others: Vec<Remote>, every: std::time::Duration) -> Observer {
        let views = Arc::new(Mutex::new(BTreeMap::new()));
        let last_error = Arc::new(Mutex::new(BTreeMap::new()));
        let (v2, e2) = (views.clone(), last_error.clone());
        for r in &others { views.lock().unwrap().insert(r.hc.p.chain, r.hc.clone()); }
        std::thread::spawn(move || {
            // one header chain per (chain, node), kept here; the best of each chain is published
            let mut cands: Vec<(u8, std::net::SocketAddr, HeaderChain, [u8; 32], Option<std::time::Instant>)> = vec![];
            for r in &others { for a in &r.peers { cands.push((r.hc.p.chain, *a, r.hc.clone(), r.network_id, None)); } }
            loop {
                for (chain, addr, hc, nid, bad_until) in cands.iter_mut() {
                    if bad_until.map_or(false, |t| t > std::time::Instant::now()) { continue; }
                    match hc.follow(*addr, *nid, 500) {
                        Ok(_) => { *bad_until = None; }
                        Err(e) => {
                            // a node that sends a block that fails the checks is left alone for a while; one that is merely unreachable is tried again soon
                            let wrong = !e.chain().any(|c| c.downcast_ref::<std::io::Error>().is_some());
                            *bad_until = Some(std::time::Instant::now() + std::time::Duration::from_secs(if wrong { 300 } else { 10 }));
                            e2.lock().unwrap().insert(*chain, format!("{addr}: {e}"));
                        }
                    }
                }
                for r in &others {
                    let c = r.hc.p.chain;
                    let best = cands.iter().filter(|x| x.0 == c).max_by_key(|x| (x.2.work(), x.2.height()));
                    if let Some(b) = best {
                        let mut v = v2.lock().unwrap();
                        let cur = v.get(&c).map(|x| (x.height(), x.hash_at(x.height())));
                        if cur != Some((b.2.height(), b.2.hash_at(b.2.height()))) { v.insert(c, b.2.clone()); }
                        drop(v);
                        if cands.iter().filter(|x| x.0 == c).any(|x| x.4.is_none()) { e2.lock().unwrap().remove(&c); }
                    }
                }
                std::thread::sleep(every);
            }
        });
        Observer { me, views, last_error }
    }
}

impl crate::locks::CrossHeaders for Observer {
    fn header(&self, chain: u8, height: u64) -> Option<([u8; 32], u32)> { self.views.lock().unwrap().get(&chain)?.header(height).map(|x| (x.hash, x.ntime)) }
    fn tip_height(&self, chain: u8) -> Option<u64> { self.views.lock().unwrap().get(&chain).map(|hc| hc.height()) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::node::{dev, DevStamp};
    fn follower(net: &dev::Devnet) -> HeaderChain {
        HeaderChain::new(net.chain.p.clone(), net.chain.root(), Box::new(DevStamp))
    }
    #[test]
    fn a_follower_checks_a_chain_header_by_header_and_follows_a_reorg() {
        let mut dn = dev::Devnet::new(None, 8).unwrap();
        let mut node = Node::open(dn.chain.p.clone(), &dev::genesis_of(&dn.keys), Box::new(DevStamp), None).unwrap();
        let genesis_root = dn.chain.root();
        let mut f = follower(&dn);
        assert_eq!(f.sync(&node).unwrap(), 0);
        let mut fork_base = None;
        for k in 1..=6 {
            let b = dn.next_block(24, 4).unwrap();
            if k == 3 { fork_base = Some(dn.chain.clone()); }
            dn.chain.accept(&b, u32::MAX).unwrap();
            node.add_block(&b, u32::MAX).unwrap();
        }
        assert_eq!(f.sync(&node).unwrap(), 6);
        assert_eq!(f.height(), 6);
        assert_eq!(f.root_at(6), Some(node.tip().root()));
        assert_eq!(f.hash_at(4), node.hash_at(4));
        assert_eq!(f.root_at(0), Some(genesis_root));
        // a longer branch from block 2 replaces blocks 3..6: the follower rolls back and takes the new ones
        let mut branch = fork_base.unwrap();
        for _ in 0..5 {
            let b = dn.block_on(&branch, 24, 2).unwrap();
            let ap = branch.validate(&b, u32::MAX).unwrap(); branch.commit(&b, ap);
            node.add_block(&b, u32::MAX).unwrap();
        }
        assert_eq!(node.height(), 7, "the node moved to the longer branch");
        assert_ne!(node.hash_at(4), f.hash_at(4));
        assert_eq!(f.sync(&node).unwrap(), 5, "back to 2, then 3..7");
        assert_eq!((f.hash_at(7), f.root_at(7)), (node.hash_at(7), Some(node.tip().root())));
    }
    #[test]
    fn a_follower_over_the_network_takes_blocks_from_a_node_checks_them_and_follows_a_reorg() {
        let mut dn = dev::Devnet::new(None, 8).unwrap();
        let node = Node::open(dn.chain.p.clone(), &dev::genesis_of(&dn.keys), Box::new(DevStamp), None).unwrap();
        let nid = node.network_id();
        let net = crate::p2p::Net::new(node);
        let addr = net.listen("127.0.0.1:0").unwrap();
        let g0 = dn.chain.root();
        let fresh = |dn: &dev::Devnet| HeaderChain::new(dn.chain.p.clone(), g0, Box::new(DevStamp));
        let mut f = fresh(&dn);
        assert_eq!(f.follow(addr, nid, 100).unwrap(), 0, "nothing to take yet");
        let mut fork_base = None;
        for k in 1..=6 {
            let b = dn.next_block(24, 4).unwrap();
            if k == 3 { fork_base = Some(dn.chain.clone()); }
            dn.chain.accept(&b, u32::MAX).unwrap();
            net.node.lock().unwrap().add_block(&b, u32::MAX).unwrap();
        }
        assert_eq!(f.follow(addr, nid, 100).unwrap(), 6);
        assert_eq!(f.hash_at(6), net.node.lock().unwrap().hash_at(6));
        assert_eq!(f.follow(addr, nid, 100).unwrap(), 0, "up to date");
        // at most `max` blocks per call
        let mut g = fresh(&dn);
        assert_eq!(g.follow(addr, nid, 4).unwrap(), 4);
        assert_eq!(g.follow(addr, nid, 4).unwrap(), 2);
        // a node of another network is refused (its hello names another network)
        let mut other = fresh(&dn);
        assert!(other.follow(addr, [9; 32], 10).is_err());
        // a longer branch from block 2 replaces blocks 3..6: the follower steps back and takes the new ones
        let mut branch = fork_base.unwrap();
        for _ in 0..5 {
            let b = dn.block_on(&branch, 24, 2).unwrap();
            let ap = branch.validate(&b, u32::MAX).unwrap(); branch.commit(&b, ap);
            net.node.lock().unwrap().add_block(&b, u32::MAX).unwrap();
        }
        assert_eq!(net.node.lock().unwrap().height(), 7);
        assert_eq!(f.follow(addr, nid, 100).unwrap(), 5);
        assert_eq!((f.height(), f.hash_at(7)), (7, net.node.lock().unwrap().hash_at(7)));
        // a node that is gone is an I/O error, not a verdict on its blocks
        drop(net);
        let e = f.follow("127.0.0.1:9".parse().unwrap(), nid, 10).unwrap_err();
        assert!(e.chain().any(|c| c.downcast_ref::<std::io::Error>().is_some()), "{e}");
    }
    #[test]
    fn the_observer_keeps_the_longest_valid_chain_among_the_nodes_it_follows_and_survives_a_dead_one() {
        let mut dn = dev::Devnet::new(None, 8).unwrap();
        let g0 = dn.chain.root();
        let mk = || Node::open(dn.chain.p.clone(), &dev::genesis_of(&dn.keys), Box::new(DevStamp), None).unwrap();
        let (n1, n2) = (mk(), mk());
        let nid = n1.network_id();
        let (a, b) = (crate::p2p::Net::new(n1), crate::p2p::Net::new(n2));
        let (aa, ba) = (a.listen("127.0.0.1:0").unwrap(), b.listen("127.0.0.1:0").unwrap());
        for _ in 0..4 {
            let blk = dn.next_block(24, 4).unwrap(); dn.chain.accept(&blk, u32::MAX).unwrap();
            a.node.lock().unwrap().add_block(&blk, u32::MAX).unwrap();
            if b.node.lock().unwrap().height() < 2 { b.node.lock().unwrap().add_block(&blk, u32::MAX).unwrap(); }   // the second node is stale at 2
        }
        let dead: std::net::SocketAddr = "127.0.0.1:9".parse().unwrap();
        let obs = Observer::spawn_net(1, vec![Remote { hc: HeaderChain::new(dn.chain.p.clone(), g0, Box::new(DevStamp)), peers: vec![dead, ba, aa], network_id: nid }], std::time::Duration::from_millis(50));
        let chain = dn.chain.p.chain;
        for _ in 0..100 { if obs.views.lock().unwrap().get(&chain).map_or(0, |x| x.height()) == 4 { break; } std::thread::sleep(std::time::Duration::from_millis(100)); }
        assert_eq!(obs.views.lock().unwrap().get(&chain).unwrap().height(), 4, "the view is the longest chain, whatever the stale and dead nodes say");
        { let v = obs.views.lock().unwrap(); let hc = v.get(&chain).unwrap(); assert_eq!(hc.work(), 4 * node::work_of_bits(hc.p.bits0), "the work of the view is the sum of its blocks' work (devnet keeps one difficulty here)"); }
        use crate::locks::CrossHeaders;
        assert_eq!(obs.tip_height(chain), Some(4));
        assert_eq!(obs.header(chain, 3).map(|x| x.0), a.node.lock().unwrap().hash_at(3));
    }
    #[test]
    fn a_follower_refuses_what_a_light_client_can_see_is_wrong() {
        let mut dn = dev::Devnet::new(None, 8).unwrap();
        let b1 = dn.next_block(24, 4).unwrap(); dn.chain.accept(&b1, u32::MAX).unwrap();
        let b2 = dn.next_block(24, 4).unwrap();
        let fresh = || follower(&dn_clone_of_genesis());
        fn dn_clone_of_genesis() -> dev::Devnet { dev::Devnet::new(None, 8).unwrap() }
        // the honest pair goes in
        let mut f = fresh(); f.push(&b1).unwrap(); f.push(&b2).unwrap();
        // block 2 first: wrong height and wrong previous block
        let mut f = fresh(); assert!(f.push(&b2).is_err(), "a block that does not follow");
        // a changed public value (so the commitment no longer matches), a changed stamp, another chain's block
        for (what, edit) in [("public value", 0usize), ("stamp", 1), ("state root", 2)] {
            let mut b = b1.clone();
            match edit { 0 => b.pubvalues[9] ^= 1, 1 => b.stamp[0] ^= 1, _ => b.pubvalues[0] ^= 1 }
            let mut f = fresh(); assert!(f.push(&b).is_err(), "{what} changed but the block was taken");
            assert_eq!(f.height(), 0, "a refused block changes nothing");
        }
        // a follower for another chain id refuses this chain's blocks
        let mut p = dn.chain.p.clone(); p.chain = 1;
        let mut other = HeaderChain::new(p, dn.chain.root(), Box::new(DevStamp));
        assert!(other.push(&b1).is_err(), "a block of one chain is not a block of another");
    }
}
