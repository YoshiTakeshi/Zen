// A network configuration file: everything two nodes must agree on to be on the same chain, and nothing secret.
//
//   zenproof net init <yen|ken|jen> <dir> [minters] [wallets]    new network: <dir>/net.conf, key files for the pool's minters and some test wallets
//   zenproof net show <net.conf>                                  what the file says, and the network id (peers compare it)
//   ZEN_NET=<net.conf> zenproof node serve ...                    run a node on it (minter keys from ZEN_MINTERS, default <dir>/minters)
//
// The file is plain text, one `key value` per line, `#` starts a comment:
//   name <text>   chain <yen|ken|jen>   genesis_time <unix seconds>   s <n>   bits0 <hex>   blow_diff0 <n>   window <n>   block_secs <n>
//   maturity <n>   std_fee_pm <n>   cap_bp <n>   min_obs <n>   seed <host:port>   alloc <zen1 address> <base units>
// Anything not given takes the chain's default. The network id is a hash of the chain, every number above (except seeds and the name) and the
// genesis allocation, so a node refuses peers whose file differs in anything that would make their blocks invalid.
use anyhow::{anyhow, bail, Result};
use crate::F;
use std::path::{Path, PathBuf};
use crate::node::{Params, MATURITY_BLOCKS};

pub struct NetConf {
    pub name: String,
    pub params: Params,
    pub alloc: Vec<([F; 4], u64)>,
    pub seeds: Vec<String>,
}

pub fn chain_id(name: &str) -> Result<u8> {
    match name.to_ascii_lowercase().as_str() { "yen" => Ok(1), "ken" => Ok(2), "jen" => Ok(3), o => bail!("chain must be yen, ken or jen, not {o:?}") }
}
pub fn chain_name(id: u8) -> &'static str { match id { 1 => "yen", 2 => "ken", _ => "jen" } }

impl Params {
    /// a test network's defaults for one chain: the block time from the spec (Yen 15 min, Ken 5 min, Jen 2.5 min), the chain's standard fee,
    /// the real maturity, and an easy seal so CPU miners can find blocks
    pub fn testnet(chain: u8) -> Params {
        let (block_secs, std_fee_pm) = match chain { 1 => (900, 1), 2 => (300, 4), _ => (150, 10) };
        Params { chain, block_secs, maturity: MATURITY_BLOCKS, read: crate::reading::ReadParams { std_fee_pm, cap_bp: 0, min_obs: 5 }, ..Params::devnet() }
    }
}

fn num<T: std::str::FromStr>(v: &str, ln: usize, key: &str) -> Result<T> where T::Err: std::fmt::Display {
    v.parse::<T>().map_err(|e| anyhow!("line {ln}: {key} {v:?}: {e}"))
}

impl NetConf {
    pub fn parse(text: &str) -> Result<NetConf> {
        let mut chain: Option<u8> = None;
        let mut kv: Vec<(usize, String, String)> = vec![];
        for (i, line) in text.lines().enumerate() {
            let line = line.split('#').next().unwrap().trim();
            if line.is_empty() { continue; }
            let (k, v) = line.split_once(char::is_whitespace).ok_or_else(|| anyhow!("line {}: {:?} has no value", i + 1, line))?;
            let (k, v) = (k.to_string(), v.trim().to_string());
            if k == "chain" { if chain.is_some() { bail!("line {}: chain given twice", i + 1); } chain = Some(chain_id(&v).map_err(|e| anyhow!("line {}: {e}", i + 1))?); }
            kv.push((i + 1, k, v));
        }
        let chain = chain.ok_or_else(|| anyhow!("the file must say which chain it is for: chain yen|ken|jen"))?;
        let mut p = Params::testnet(chain);
        let (mut name, mut alloc, mut seeds) = (String::new(), vec![], vec![]);
        let mut seen: std::collections::HashSet<String> = Default::default();
        for (ln, k, v) in kv {
            if !matches!(k.as_str(), "alloc" | "seed") && !seen.insert(k.clone()) { bail!("line {ln}: {k} given twice"); }
            match k.as_str() {
                "name" => name = v,
                "chain" => {}
                "genesis_time" => p.genesis_time = num(&v, ln, &k)?,
                "s" => p.s = num(&v, ln, &k)?,
                "bits0" => p.bits0 = u32::from_str_radix(v.trim_start_matches("0x"), 16).map_err(|e| anyhow!("line {ln}: bits0 {v:?}: {e}"))?,
                "blow_diff0" => p.blow_diff0 = num(&v, ln, &k)?,
                "window" => p.window = num(&v, ln, &k)?,
                "block_secs" => p.block_secs = num(&v, ln, &k)?,
                "maturity" => p.maturity = num(&v, ln, &k)?,
                "std_fee_pm" => p.read.std_fee_pm = num(&v, ln, &k)?,
                "cap_bp" => p.read.cap_bp = num(&v, ln, &k)?,
                "min_obs" => p.read.min_obs = num(&v, ln, &k)?,
                "seed" => seeds.push(v),
                "alloc" => {
                    let (a, n) = v.split_once(char::is_whitespace).ok_or_else(|| anyhow!("line {ln}: alloc needs an address and an amount"))?;
                    let addr = crate::tx::parse_address(a).map_err(|e| anyhow!("line {ln}: {e}"))?;
                    let amt: u64 = num(n.trim(), ln, "alloc amount")?;
                    alloc.push((addr, amt));
                }
                o => bail!("line {ln}: unknown setting {o:?}"),
            }
        }
        let c = NetConf { name, params: p, alloc, seeds };
        c.check()?;
        Ok(c)
    }
    pub fn load(path: &Path) -> Result<NetConf> {
        NetConf::parse(&std::fs::read_to_string(path).map_err(|e| anyhow!("cannot read {}: {e}", path.display()))?)
    }
    /// what makes a file unusable, said in words
    pub fn check(&self) -> Result<()> {
        let p = &self.params;
        if p.window == 0 || p.window > 100_000 { bail!("window must be between 1 and 100000 blocks"); }
        if p.block_secs == 0 || p.block_secs > 86_400 { bail!("block_secs must be between 1 and 86400"); }
        if p.s == 0 || p.s >= 1 << 32 { bail!("s must be between 1 and 2^32"); }
        if p.blow_diff0 == 0 { bail!("blow_diff0 must be at least 1"); }
        if p.maturity > 100_000 { bail!("maturity is at most 100000 blocks"); }
        if p.read.std_fee_pm == 0 || p.read.std_fee_pm > 1000 { bail!("std_fee_pm must be between 1 and 1000"); }
        crate::seal::bits_to_target(p.bits0).map_err(|e| anyhow!("bits0 is not a valid difficulty: {e}"))?;
        if self.alloc.is_empty() { bail!("the file needs at least one alloc line, or nobody can ever mint or pay"); }
        let mut total: u128 = 0;
        let mut seen = std::collections::HashSet::new();
        for (a, n) in &self.alloc {
            if *n == 0 || *n >= 1 << 62 { bail!("an alloc amount must be between 1 and 2^62 base units"); }
            if !seen.insert(a.map(|x| plonky2::field::types::PrimeField64::to_canonical_u64(&x))) { bail!("the same address appears in two alloc lines"); }
            total += *n as u128;
        }
        if total >= 1 << 62 { bail!("the allocations add up to more than 2^62 base units"); }
        Ok(())
    }
    pub fn to_text(&self) -> String {
        let p = &self.params;
        let mut s = format!("# Zen test network. This file holds no secrets: give it to anyone who should join.\nname {}\nchain {}\ngenesis_time {}\n", self.name, chain_name(p.chain), p.genesis_time);
        s += &format!("s {}\nbits0 {:08x}\nblow_diff0 {}\nwindow {}\nblock_secs {}\nmaturity {}\nstd_fee_pm {}\ncap_bp {}\nmin_obs {}\n",
            p.s, p.bits0, p.blow_diff0, p.window, p.block_secs, p.maturity, p.read.std_fee_pm, p.read.cap_bp, p.read.min_obs);
        for sd in &self.seeds { s += &format!("seed {sd}\n"); }
        for (a, n) in &self.alloc { s += &format!("alloc {} {}\n", crate::tx::address_string(a), n); }
        s
    }
    pub fn genesis(&self) -> Vec<([F; 4], u64)> { self.alloc.clone() }
    /// the digest peers compare (the node computes the same from its own parameters and genesis)
    pub fn network_id(&self) -> [u8; 32] { crate::node::network_id_of(&self.params, &crate::node::genesis_digest(&self.alloc)) }
}

/// the pool's minter keys: every wallet file in the directory, in file-name order
pub fn load_minters(dir: &Path) -> Result<Vec<crate::tx::Wallet>> {
    let mut files: Vec<PathBuf> = std::fs::read_dir(dir).map_err(|e| anyhow!("cannot read the minter key directory {}: {e}", dir.display()))?
        .filter_map(|e| e.ok()).map(|e| e.path()).filter(|p| p.extension().is_some_and(|x| x == "key")).collect();
    files.sort();
    files.iter().map(|f| crate::tx::Wallet::load(f).map_err(|e| anyhow!("{}: {e}", f.display()))).collect()
}

/// `zenproof net init|show`
pub fn net_main() -> Result<()> {
    let a: Vec<String> = std::env::args().collect();
    match a.get(2).map(|s| s.as_str()) {
        Some("init") if a.get(3).map(|s| s.as_str()) == Some("all") => return crate::testnet::init_all(),
        Some("init") => {
            let usage = "usage: net init <yen|ken|jen> <dir> [minters (default 4)] [wallets (default 4)]";
            let chain = chain_id(a.get(3).ok_or_else(|| anyhow!(usage))?)?;
            let dir = PathBuf::from(a.get(4).ok_or_else(|| anyhow!(usage))?);
            let (nm, nw): (usize, usize) = (a.get(5).map(|s| s.parse()).transpose()?.unwrap_or(4), a.get(6).map(|s| s.parse()).transpose()?.unwrap_or(4));
            if nm == 0 || nm > 4 { bail!("minters: 1 to 4 (the pool draws tickets from at most four keys)"); }
            if dir.join("net.conf").exists() { bail!("{} already has a net.conf; it is never overwritten", dir.display()); }
            std::fs::create_dir_all(dir.join("minters"))?; std::fs::create_dir_all(dir.join("wallets"))?;
            let mut alloc = vec![];
            for (sub, n) in [("minters", nm), ("wallets", nw)] {
                for i in 0..n {
                    let w = crate::tx::Wallet::generate();
                    w.save(&dir.join(sub).join(format!("{}{}.key", &sub[..1], i)))?;
                    alloc.push((w.address(), 1_000_000_000u64));      // 1 gram each
                }
            }
            let mut p = Params::testnet(chain);
            p.genesis_time = crate::p2p::now();
            let c = NetConf { name: format!("zen-{}-testnet", chain_name(chain)), params: p, alloc, seeds: vec![] };
            c.check()?;
            std::fs::write(dir.join("net.conf"), c.to_text())?;
            println!("wrote {}/net.conf ({} minter keys in minters/, {} test wallets in wallets/; the .key files are secrets, net.conf is not)", dir.display(), nm, nw);
            println!("network id {}", crate::seal::hex(&c.network_id()));
            println!("run it:  ZEN_NET={0}/net.conf ZEN_DIR={0}/data zenproof node serve 0.0.0.0:18444 127.0.0.1:13333", dir.display());
        }
        Some("show") => {
            let c = NetConf::load(Path::new(a.get(3).ok_or_else(|| anyhow!("usage: net show <net.conf>"))?))?;
            let p = &c.params;
            println!("{} | chain {} ({}) | genesis time {} | {} s per block, retarget every {} blocks, first seal bits {:08x}", c.name, p.chain, chain_name(p.chain), p.genesis_time, p.block_secs, p.window, p.bits0);
            println!("S {} | maturity {} blocks | standard fee {} per thousand | {} allocations, {} base units | {} seed nodes", p.s, p.maturity, p.read.std_fee_pm, c.alloc.len(), c.alloc.iter().map(|x| x.1 as u128).sum::<u128>(), c.seeds.len());
            println!("network id {}", crate::seal::hex(&c.network_id()));
        }
        _ => bail!("usage: net <init|show> ..."),
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    fn wallet_addr(i: u64) -> String { crate::tx::Wallet::from_secret(num_bigint::BigUint::from(1000 + i)).address_string() }
    fn conf(extra: &str) -> String { format!("chain ken\nname t\nalloc {} 5000000\nalloc {} 7\n{extra}", wallet_addr(1), wallet_addr(2)) }

    #[test]
    fn a_file_reads_back_the_same_and_defaults_follow_the_chain() {
        let c = NetConf::parse(&conf("seed 10.0.0.1:18444\nblock_secs 60 # fast\n")).unwrap();
        assert_eq!((c.params.chain, c.params.block_secs, c.params.read.std_fee_pm, c.params.maturity), (2, 60, 4, MATURITY_BLOCKS));
        assert_eq!(c.seeds, vec!["10.0.0.1:18444"]);
        let again = NetConf::parse(&c.to_text()).unwrap();
        assert_eq!(again.network_id(), c.network_id());
        assert_eq!(again.alloc, c.alloc);
        // each chain has its own block time and fee
        for (n, secs, fee) in [("yen", 900, 1), ("ken", 300, 4), ("jen", 150, 10)] {
            let c = NetConf::parse(&format!("chain {n}\nalloc {} 5\n", wallet_addr(1))).unwrap();
            assert_eq!((c.params.block_secs, c.params.read.std_fee_pm), (secs, fee), "{n}");
        }
    }
    #[test]
    fn anything_that_changes_what_is_valid_changes_the_network_id() {
        let base = NetConf::parse(&conf("")).unwrap().network_id();
        for extra in ["s 999\n", "window 16\n", "bits0 1e00ffff\n", "maturity 5\n", "genesis_time 5\n", "std_fee_pm 3\n", "blow_diff0 2\n"] {
            assert_ne!(NetConf::parse(&conf(extra)).unwrap().network_id(), base, "{extra}");
        }
        // seeds and the name are only hints, not rules
        assert_eq!(NetConf::parse(&conf("seed 1.2.3.4:5\n")).unwrap().network_id(), base);
        assert_eq!(NetConf::parse(&conf("").replace("name t", "name other")).unwrap().network_id(), base);
        // another chain, another allocation
        assert_ne!(NetConf::parse(&conf("").replace("chain ken", "chain yen")).unwrap().network_id(), base);
        assert_ne!(NetConf::parse(&conf("").replace("5000000", "5000001")).unwrap().network_id(), base);
    }
    #[test]
    fn a_bad_file_is_refused_with_the_line_and_the_reason() {
        let bad = |t: String, want: &str| { let e = NetConf::parse(&t).err().unwrap_or_else(|| panic!("accepted: {t}")).to_string(); assert!(e.contains(want), "{e:?} lacks {want:?}"); };
        bad("alloc x 5\n".into(), "which chain");
        bad(conf("chain jen\n"), "chain given twice");
        bad(conf("window 0\n"), "window");
        bad(conf("window 4\nwindow 5\n"), "window given twice");
        bad(conf("bits0 zz\n"), "line");
        bad(conf("bits0 00000000\n"), "bits0");
        bad(conf("block_secs soon\n"), "block_secs");
        bad(conf("color blue\n"), "unknown setting");
        bad(conf("maturity\n"), "no value");
        bad("chain jen\n".into(), "alloc");
        bad(format!("chain jen\nalloc {0} 5\nalloc {0} 6\n", wallet_addr(1)), "two alloc lines");
        bad(format!("chain jen\nalloc {} {}\n", wallet_addr(1), 1u64 << 62), "alloc amount");
        bad(format!("chain jen\nalloc {} 0\n", wallet_addr(1)), "alloc amount");
        bad(format!("chain jen\nalloc {} 5\n", wallet_addr(1).replace("zen1", "zen2")), "zen1");
        let mut typo = wallet_addr(1).into_bytes(); let n = typo.len() - 1; typo[n] = if typo[n] == b'0' { b'1' } else { b'0' };
        bad(format!("chain jen\nalloc {} 5\n", String::from_utf8(typo).unwrap()), "checksum");
        bad(conf("").replace("chain ken", "chain bar"), "yen, ken or jen");
    }
    #[test]
    fn a_node_opens_on_the_file_and_peers_with_another_file_are_refused() {
        let c = NetConf::parse(&conf("")).unwrap();
        let open = |c: &NetConf| crate::node::Node::open(c.params.clone(), &c.genesis(), Box::new(crate::node::DevStamp), None).unwrap();
        let n = open(&c);
        assert_eq!(n.network_id(), c.network_id(), "the node and the file compute the same id");
        assert_eq!(n.tip().p.chain, 2);
        let net = crate::p2p::Net::new(n);
        let other = crate::p2p::Net::new(open(&NetConf::parse(&conf("window 16\n")).unwrap()));
        let a = net.listen("127.0.0.1:0").unwrap();
        let _ = other.connect(a);
        std::thread::sleep(std::time::Duration::from_millis(600));
        assert_eq!(net.peer_count(), 0, "another network file is not our peer");
        let same = crate::p2p::Net::new(open(&c));
        same.connect(a).unwrap();
        for _ in 0..50 { if net.peer_count() == 1 { break; } std::thread::sleep(std::time::Duration::from_millis(100)); }
        assert_eq!(net.peer_count(), 1, "the same file is");
    }
    #[test]
    fn init_writes_a_file_no_secret_and_keys_that_match() {
        let dir = std::env::temp_dir().join(format!("zen-netinit-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(dir.join("minters")).unwrap();
        for i in 0..2 { let w = crate::tx::Wallet::generate(); w.save(&dir.join("minters").join(format!("m{i}.key"))).unwrap(); }
        let ms = load_minters(&dir.join("minters")).unwrap();
        assert_eq!(ms.len(), 2);
        let c = NetConf { name: "x".into(), params: Params::testnet(1), alloc: ms.iter().map(|w| (w.address(), 9)).collect(), seeds: vec![] };
        let text = c.to_text();
        for w in &ms { assert!(!text.contains(&w.secret_hex()), "the file must not contain a secret"); assert!(text.contains(&w.address_string())); }
        assert!(load_minters(&dir.join("nope")).is_err());
        std::fs::remove_dir_all(&dir).unwrap();
    }
}
