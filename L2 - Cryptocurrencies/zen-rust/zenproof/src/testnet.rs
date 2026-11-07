// The three-chain test network: Yen, Ken and Jen in one process, each with its own network file, log, pool and API, and each following the other
// two chains' headers (crosschain.rs). Stamps are the stand-in kind for now (rules first); real proofs come after the rules have settled.
//
//   zenproof net init all <dir> [minters] [wallets]     <dir>/{yen,ken,jen}/net.conf, and the same minter and wallet keys on all three chains
//   zenproof node serve-all <dir> [base port]           p2p base+0..2, Stratum base+10..12, API (loopback) base+20..22; Yen, Ken, Jen in that order
//   zenproof node mine <stratum addr> [blocks]          the CPU miner, one chain at a time
use anyhow::{anyhow, bail, Result};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use crate::crosschain::{HeaderChain, Observer};
use crate::netconf::{chain_name, NetConf};
use crate::node::{dev, DevStamp, DevStampMaker, Node, StampMaker};
use crate::p2p::{Net, Stratum};

const CHAINS: [u8; 3] = [1, 2, 3];
const DEFAULT_BASE: u16 = 18440;

pub fn init_all() -> Result<()> {
    let a: Vec<String> = std::env::args().collect();
    let usage = "usage: net init all <dir> [minters (default 4)] [wallets (default 4)]";
    let dir = PathBuf::from(a.get(4).ok_or_else(|| anyhow!(usage))?);
    let (nm, nw): (usize, usize) = (a.get(5).map(|s| s.parse()).transpose()?.unwrap_or(4), a.get(6).map(|s| s.parse()).transpose()?.unwrap_or(4));
    if nm == 0 || nm > 4 { bail!("minters: 1 to 4"); }
    if dir.join("yen").join("net.conf").exists() { bail!("{} already holds a test network; it is never overwritten", dir.display()); }
    for sub in ["minters", "wallets"] { std::fs::create_dir_all(dir.join(sub))?; }
    let mut alloc = vec![];
    for (sub, n) in [("minters", nm), ("wallets", nw)] {
        for i in 0..n {
            let w = crate::tx::Wallet::generate();
            w.save(&dir.join(sub).join(format!("{}{}.key", &sub[..1], i)))?;
            // a wallet needs more than the smallest Yen amount (0.4 YEN = 1.6 g) to open a Yen channel
            alloc.push((w.address(), if sub == "wallets" { 10_000_000_000u64 } else { 1_000_000_000u64 }));
        }
    }
    let t0 = crate::p2p::now();
    for c in CHAINS {
        let mut p = crate::node::Params::testnet(c);
        p.genesis_time = t0;
        let nc = NetConf { name: format!("zen-{}-testnet", chain_name(c)), params: p, alloc: alloc.clone(), seeds: vec![] };
        nc.check()?;
        std::fs::create_dir_all(dir.join(chain_name(c)))?;
        std::fs::write(dir.join(chain_name(c)).join("net.conf"), nc.to_text())?;
        println!("{:>4}: network id {}", chain_name(c), crate::seal::hex(&nc.network_id()));
    }
    println!("wrote {} ({} minter keys, {} test wallets with 10 g on each chain; the .key files are secrets, the net.conf files are not)", dir.display(), nm, nw);
    println!("run it:  zenproof node serve-all {}", dir.display());
    Ok(())
}

pub fn serve_all() -> Result<()> {
    let a: Vec<String> = std::env::args().collect();
    let dir = PathBuf::from(a.get(3).ok_or_else(|| anyhow!("usage: node serve-all <dir> [base port]"))?);
    let base: u16 = a.get(4).map(|s| s.parse()).transpose()?.unwrap_or(DEFAULT_BASE);
    if std::env::var("ZEN_REAL").is_ok() || std::env::var("ZEN_G16").is_ok() { bail!("serve-all runs with stand-in stamps for now (real proofs for three chains need three provers)"); }
    // 127.0.0.1 on a developer machine; 0.0.0.0 in a container (ZEN_BIND), the API with ZEN_API_BIND (+ ZEN_API_BIND_ANY=1, see api.rs)
    let bind = std::env::var("ZEN_BIND").unwrap_or_else(|_| "127.0.0.1".to_string());
    let api_bind = std::env::var("ZEN_API_BIND").unwrap_or_else(|_| "127.0.0.1".to_string());
    let confs: Vec<NetConf> = CHAINS.iter().map(|c| NetConf::load(&dir.join(chain_name(*c)).join("net.conf"))).collect::<Result<_>>()?;
    for (c, nc) in CHAINS.iter().zip(&confs) { if nc.params.chain != *c { bail!("{}/net.conf is for chain {}", chain_name(*c), nc.params.chain); } }
    let minters: Vec<crate::mint::Key> = crate::netconf::load_minters(&dir.join("minters"))?.into_iter().map(|w| w.key).collect();
    if minters.is_empty() || minters.len() > 4 { bail!("1 to 4 minter keys are needed in {}/minters", dir.display()); }
    for nc in &confs { for k in &minters { if !nc.alloc.iter().any(|(x, _)| *x == k.addr) { bail!("a minter key is not in the genesis allocation of {}", nc.name); } } }
    let maker: Arc<dyn StampMaker> = Arc::new(DevStampMaker);
    // 1. the three nodes
    let mut nets: Vec<Net> = vec![];
    for (i, nc) in confs.iter().enumerate() {
        let data = dir.join(chain_name(nc.params.chain)).join("data");
        let node = Node::open(nc.params.clone(), &nc.genesis(), Box::new(DevStamp), Some(&data))?;
        println!("{:>4}: height {} | {}", chain_name(nc.params.chain), node.height(), if node.from_snapshot > 0 { format!("from a snapshot at {}", node.from_snapshot) } else { "every block validated".to_string() });
        let net = Net::new(node);
        let p2p = net.listen(&format!("{bind}:{}", base + i as u16))?;
        let token = crate::api::load_or_create_token(Some(&data))?;
        let api = crate::api::start(net.clone(), &format!("{api_bind}:{}", base + 20 + i as u16), token)?;
        let pool = Stratum::new(net.clone(), Arc::new(dev::PoolSource { minters: minters.clone(), miner: minters[0].addr, maker: maker.clone(), pool: net.pool.clone(),
                                                                   store: None, max_pays: 2 * crate::node::SLOTS_PER_LEAF, wall_clock: true, ops: Some(net.ops.clone()) }));
        let st = pool.listen(&format!("{bind}:{}", base + 10 + i as u16))?;
        for seed in &nc.seeds { if let Some(sa) = std::net::ToSocketAddrs::to_socket_addrs(seed.as_str()).ok().and_then(|mut x| x.next()) { let _ = net.connect(sa); } }
        net.spawn_maintainer(std::time::Duration::from_secs(10));
        println!("{:>4}: p2p {p2p} | Stratum {st} | explorer http://{api}/ | token in {}", "", data.join("api.token").display());
        std::mem::forget(pool);
        nets.push(net);
    }
    // 2. each chain follows the other two
    let mut observers = vec![];
    for (i, nc) in confs.iter().enumerate() {
        let others: Vec<(Net, HeaderChain)> = (0..3).filter(|j| *j != i).map(|j| {
            let hc = HeaderChain::new(confs[j].params.clone(), nets[j].node.lock().unwrap().genesis_root(), Box::new(DevStamp));
            (nets[j].clone(), hc)
        }).collect();
        observers.push(Arc::new(Observer::spawn(nc.params.chain, others, std::time::Duration::from_millis(500))));
    }
    // a claim on one chain may read the other chains' headers, as these observers have checked them (nothing else crosses)
    for i in 0..3 { nets[i].node.lock().unwrap().set_cross(crate::locks::CrossMode::View(observers[i].clone())); }
    // 3. what each API says about the three chains (its own from the node, the others as this node has checked them)
    for i in 0..3 {
        let (net, obs, names, mine) = (nets[i].clone(), observers[i].clone(), CHAINS.map(chain_name), CHAINS[i]);
        let f: Arc<dyn Fn() -> serde_json::Value + Send + Sync> = Arc::new(move || {
            let seen = obs.json();
            let own = { let n = net.node.lock().unwrap(); (n.height(), crate::seal::hex(&n.best)) };
            serde_json::Value::Array((0..3).map(|j| {
                let c = CHAINS[j];
                if c == mine { serde_json::json!({"chain": c, "name": names[j], "self": true, "height": own.0, "tip": own.1, "api_port": base + 20 + j as u16}) }
                else {
                    let s = seen.as_array().and_then(|v| v.iter().find(|x| x["chain"] == c)).cloned().unwrap_or(serde_json::json!({}));
                    serde_json::json!({"chain": c, "name": names[j], "self": false, "height": s["headers_checked"], "tip": s["tip"], "problem": s["problem"], "api_port": base + 20 + j as u16})
                }
            }).collect())
        });
        *nets[i].chains.lock().unwrap() = Some(f);
    }
    println!("three chains running. Mine each with: zenproof node mine 127.0.0.1:{} <blocks>   (Yen {}, Ken {}, Jen {})", base + 10, base + 10, base + 11, base + 12);
    let mut last = [u64::MAX; 3];
    loop {
        std::thread::sleep(std::time::Duration::from_millis(500));
        for i in 0..3 {
            let h = nets[i].height();
            if h != last[i] {
                last[i] = h;
                let seen: Vec<String> = (0..3).filter(|j| *j != i).map(|j| { let v = observers[i].views.lock().unwrap(); format!("{} {}", chain_name(CHAINS[j]), v.get(&CHAINS[j]).map_or(0, |x| x.height())) }).collect();
                println!("{} height {h} | sees {}", chain_name(CHAINS[i]), seen.join(", "));
            }
        }
    }
}

/// `zenproof node serve-chain <net dir> <yen|ken|jen> [base port]`: ONE chain's node, with the other two followed over the network (stage 13).
/// The net dir holds each chain's net.conf (public). The other chains' full nodes are the `seed` lines of their net.conf (several are followed side
/// by side, the longest valid chain is the view), or the comma list in `ZEN_FOLLOW_YEN` / `ZEN_FOLLOW_KEN` / `ZEN_FOLLOW_JEN` (host:p2p port).
/// Ports are base + chain index (p2p), +10 (Stratum), +20 (API), as in serve-all, so three machines can use the same base.
pub fn serve_chain() -> Result<()> {
    let a: Vec<String> = std::env::args().collect();
    let dir = PathBuf::from(a.get(3).ok_or_else(|| anyhow!("usage: node serve-chain <dir> <yen|ken|jen> [base port]"))?);
    let me: u8 = match a.get(4).map(|s| s.to_ascii_lowercase()).as_deref() { Some("yen") | Some("1") => 1, Some("ken") | Some("2") => 2, Some("jen") | Some("3") => 3, _ => bail!("usage: node serve-chain <dir> <yen|ken|jen> [base port]") };
    let base: u16 = a.get(5).map(|s| s.parse()).transpose()?.unwrap_or(DEFAULT_BASE);
    if std::env::var("ZEN_REAL").is_ok() || std::env::var("ZEN_G16").is_ok() { bail!("serve-chain runs with stand-in stamps for now"); }
    let bind = std::env::var("ZEN_BIND").unwrap_or_else(|_| "127.0.0.1".to_string());
    let api_bind = std::env::var("ZEN_API_BIND").unwrap_or_else(|_| "127.0.0.1".to_string());
    let confs: Vec<NetConf> = CHAINS.iter().map(|c| NetConf::load(&dir.join(chain_name(*c)).join("net.conf"))).collect::<Result<_>>()?;
    for (c, nc) in CHAINS.iter().zip(&confs) { if nc.params.chain != *c { bail!("{}/net.conf is for chain {}", chain_name(*c), nc.params.chain); } }
    let minters: Vec<crate::mint::Key> = crate::netconf::load_minters(&dir.join("minters"))?.into_iter().map(|w| w.key).collect();
    if minters.is_empty() || minters.len() > 4 { bail!("1 to 4 minter keys are needed in {}/minters", dir.display()); }
    let i = CHAINS.iter().position(|c| *c == me).unwrap();
    let nc = &confs[i];
    let maker: Arc<dyn StampMaker> = Arc::new(DevStampMaker);
    let data = dir.join(chain_name(me)).join("data");
    let node = Node::open(nc.params.clone(), &nc.genesis(), Box::new(DevStamp), Some(&data))?;
    println!("{:>4}: height {} | {}", chain_name(me), node.height(), if node.from_snapshot > 0 { format!("from a snapshot at {}", node.from_snapshot) } else { "every block validated".to_string() });
    let net = Net::new(node);
    let p2p = net.listen(&format!("{bind}:{}", base + i as u16))?;
    let token = crate::api::load_or_create_token(Some(&data))?;
    let api = crate::api::start(net.clone(), &format!("{api_bind}:{}", base + 20 + i as u16), token)?;
    let pool = Stratum::new(net.clone(), Arc::new(dev::PoolSource { minters: minters.clone(), miner: minters[0].addr, maker: maker.clone(), pool: net.pool.clone(),
                                                               store: None, max_pays: 2 * crate::node::SLOTS_PER_LEAF, wall_clock: true, ops: Some(net.ops.clone()) }));
    let st = pool.listen(&format!("{bind}:{}", base + 10 + i as u16))?;
    for seed in &nc.seeds { if let Some(sa) = std::net::ToSocketAddrs::to_socket_addrs(seed.as_str()).ok().and_then(|mut x| x.next()) { if !(sa.port() == p2p.port() && (sa.ip() == p2p.ip() || sa.ip().is_loopback())) { let _ = net.connect(sa); } } }
    net.spawn_maintainer(std::time::Duration::from_secs(10));
    println!("{:>4}: p2p {p2p} | Stratum {st} | explorer http://{api}/ | token in {}", "", data.join("api.token").display());
    std::mem::forget(pool);
    // the other two chains, followed over the network
    let mut remotes = vec![];
    for (j, oc) in confs.iter().enumerate() {
        if j == i { continue; }
        let list: Vec<String> = match std::env::var(format!("ZEN_FOLLOW_{}", chain_name(CHAINS[j]).to_ascii_uppercase())) {
            Ok(v) if !v.trim().is_empty() => v.split(',').map(|x| x.trim().to_string()).filter(|x| !x.is_empty()).collect(),
            _ => oc.seeds.clone(),
        };
        let peers: Vec<std::net::SocketAddr> = list.iter().filter_map(|x| std::net::ToSocketAddrs::to_socket_addrs(x.as_str()).ok().and_then(|mut v| v.next())).collect();
        if peers.is_empty() { println!("warning: no node to follow {} (add `seed host:port` lines to {0}/net.conf or set ZEN_FOLLOW_{})", chain_name(CHAINS[j]), chain_name(CHAINS[j]).to_ascii_uppercase()); }
        // the other chain's genesis, from its public net.conf alone (no data directory needed)
        let g = Node::open(oc.params.clone(), &oc.genesis(), Box::new(DevStamp), None)?;
        remotes.push(crate::crosschain::Remote { hc: HeaderChain::new(oc.params.clone(), g.genesis_root(), Box::new(DevStamp)), peers, network_id: g.network_id() });
    }
    let obs = Arc::new(Observer::spawn_net(me, remotes, std::time::Duration::from_millis(1000)));
    net.node.lock().unwrap().set_cross(crate::locks::CrossMode::View(obs.clone()));
    {
        let (net2, obs, names) = (net.clone(), obs.clone(), CHAINS.map(chain_name));
        let f: Arc<dyn Fn() -> serde_json::Value + Send + Sync> = Arc::new(move || {
            let seen = obs.json();
            let own = { let n = net2.node.lock().unwrap(); (n.height(), crate::seal::hex(&n.best)) };
            serde_json::Value::Array((0..3).map(|j| {
                let c = CHAINS[j];
                if c == me { serde_json::json!({"chain": c, "name": names[j], "self": true, "height": own.0, "tip": own.1, "api_port": base + 20 + j as u16}) }
                else {
                    let s = seen.as_array().and_then(|v| v.iter().find(|x| x["chain"] == c)).cloned().unwrap_or(serde_json::json!({}));
                    serde_json::json!({"chain": c, "name": names[j], "self": false, "height": s["headers_checked"], "tip": s["tip"], "problem": s["problem"], "api_port": base + 20 + j as u16, "followed_over_network": true})
                }
            }).collect())
        });
        *net.chains.lock().unwrap() = Some(f);
    }
    println!("{} runs alone; the other two chains are followed over the network. Mine it with: zenproof node mine 127.0.0.1:{} <blocks>", chain_name(me), base + 10 + i as u16);
    let mut last = u64::MAX;
    loop {
        std::thread::sleep(std::time::Duration::from_millis(500));
        let h = net.height();
        if h != last {
            last = h;
            let seen: Vec<String> = (0..3).filter(|j| *j != i).map(|j| { let v = obs.views.lock().unwrap(); format!("{} {}", chain_name(CHAINS[j]), v.get(&CHAINS[j]).map_or(0, |x| x.height())) }).collect();
            println!("{} height {h} | sees {}", chain_name(me), seen.join(", "));
        }
    }
}
