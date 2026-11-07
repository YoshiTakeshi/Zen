// Stage P7 (Justus L. Ludovic): soundness tests of the operation circuits.
//
// The node's rules (`locks.rs`) are the specification; a circuit is sound if it proves nothing the node would refuse. For every operation of a life story
// (vault, channel, order, factory) the battery below takes the honest scenario and
//   1. TAMPERS: every touched leaf (sender, paid accounts, the lock) gets a changed balance, nonce, key, index or Merkle sibling; another signer, another
//      root before, other terms;
//   2. VARIES THE HEIGHT around the honest one: wherever the node refuses the operation (a window, a timeout, an expiry, a reservation), the circuit must too;
//   3. BREAKS A RULE: variants of the operation built by the story (a new lock whose terms break one rule of the node, a state with update number 0,
//      shares beyond the channel, a bad point lock, a close nobody signed, ...), each of which the node refuses.
// Each of them must NOT prove. The honest operation must prove and match the node's replay (root after, fee, data hash).
use crate::locks::{self, ChanSigs, ChanState, CrossMode, Ctx, Dest, FMember, Op, OpTrace, OrderState, PLock, SignedOp, SubState, Terms};
use crate::mint;
use crate::node::dev;
use crate::node::{Chain, DevStamp, Params};
use crate::opcirc::{self, OpLeaf};
use crate::{ec, Acct, Tree, F};
use plonky2::field::types::{Field, PrimeField64};
use plonky2::hash::hash_types::HashOut;
use plonky2::iop::witness::PartialWitness;
use std::collections::HashMap;
use std::sync::OnceLock;

const FEE: u64 = 10_000;
const S: u64 = 1_000_000;
const NT: u32 = 777_777;

struct Leaves { vault: OpLeaf, chan: crate::chancirc::ChanLeaf, order: crate::ordercirc::OrderLeaf, fact: crate::factorycirc::FactoryLeaf }
fn leaves() -> &'static Leaves {
    static L: OnceLock<Leaves> = OnceLock::new();
    L.get_or_init(|| { let (c, p) = (Params::devnet().chain as u64, ec::params());
        Leaves { vault: opcirc::build_op(c, &p, &[], 0), chan: crate::chancirc::build_chan(c, &p, &[], 0), order: crate::ordercirc::build_order(c, &p, &[], 0), fact: crate::factorycirc::build_factory(c, &p, &[], 0) } })
}
#[derive(Clone)]
struct World { state: HashMap<u64, Acct>, tree: Tree, locks: locks::LockTable, chain: u8, tmpl: Acct }
fn keys() -> Vec<mint::Key> { dev::devnet_keys(8) }
fn world() -> World {
    let ks = keys();
    let c = Chain::open(Params::devnet(), &dev::genesis_of(&ks), Box::new(DevStamp), None).unwrap();
    let tmpl = *c.state.values().next().unwrap();
    World { state: c.state.clone(), tree: c.tree.clone(), locks: c.locks.clone(), chain: c.p.chain, tmpl }
}
fn felts(h: HashOut<F>) -> Vec<u64> { h.elements.iter().map(|x| x.to_canonical_u64()).collect() }
impl World {
    fn idx(&self, k: &mint::Key) -> u32 { self.state.iter().find(|(_, a)| a.pk == k.addr).map(|(i, _)| *i as u32).unwrap() }
    fn nonce(&self, k: &mint::Key) -> u64 { self.state[&(self.idx(k) as u64)].nonce }
    fn dest(&self, k: &mint::Key) -> Dest { Dest { idx: self.idx(k), new: None } }
    fn terms(&self, at: u64) -> Terms { self.locks[&at].clone() }
    /// the node's rules: the trace of the operation, or why it is refused
    fn try_native(&mut self, op: &Op, height: u64) -> anyhow::Result<OpTrace> {
        let mut traces = vec![];
        let ctx = Ctx { chain: self.chain, ntime: NT, cross: &CrossMode::Trust };
        locks::apply_ops_traced(std::slice::from_ref(op), &mut self.state, &mut self.tree, &mut self.locks, S, height, &ctx, self.tmpl, Some(&mut traces))?;
        Ok(traces.remove(0))
    }
    /// the circuit of the operation's family; the pis of its proof, or None when it does not prove
    fn prove(&self, op: &Op, tr: &OpTrace, height: u64, root0: HashOut<F>, signer: &mint::Key) -> Option<Vec<u64>> {
        let req = opcirc::req_of(op, &self.state).ok()?;
        let nonce = tr.touches.first()?.old?.nonce;
        let (e, sv) = mint::sign(signer, SignedOp::message(self.chain, nonce, &req));
        let sender_sig = (e, sv);
        let kind = locks::leaf_kind(op)?;
        let l = leaves();
        let mut pw = PartialWitness::new();
        let (cd, wr) = match kind {
            0 => (&l.vault.data, opcirc::set_witness(&l.vault, &mut pw, &opcirc::OpInput { op, trace: tr, height, s: S, root0, chain: self.chain, sender_a: signer.a, sender_sig })),
            1 => (&l.chan.data, crate::chancirc::set_witness(&l.chan, &mut pw, &crate::chancirc::ChanInput { op, trace: tr, height, s: S, root0, chain: self.chain, sender_a: signer.a, sender_sig })),
            2 => (&l.order.data, crate::ordercirc::set_witness(&l.order, &mut pw, &crate::ordercirc::OrderInput { op, trace: tr, height, s: S, root0, ntime: NT, sender_a: signer.a, sender_sig })),
            _ => (&l.fact.data, crate::factorycirc::set_witness(&l.fact, &mut pw, &crate::factorycirc::FactoryInput { op, trace: tr, height, s: S, root0, chain: self.chain, sender_a: signer.a, sender_sig })),
        };
        if wr.is_err() { return None; }
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| cd.prove(pw)));
        let Ok(Ok(proof)) = r else { return None };
        let pis: Vec<u64> = proof.public_inputs.iter().map(|x| x.to_canonical_u64()).collect();
        cd.verify(proof).ok().map(|_| pis)
    }
}
fn data_hash(op: &Op) -> Vec<u64> { locks::proved_data_hash(op, NT).unwrap().iter().map(|x| x.to_canonical_u64()).collect() }

/// one operation of a story: the honest operation, who sends it, and variants that break one rule each
struct Step { op: Op, h: u64, signer: mint::Key, rules: Vec<(String, Op)> }
#[derive(Default)]
struct Tally { harmless: usize, mutations: usize, refused_heights: usize, ops: usize, failures: Vec<String> }

/// runs the battery on `op` in the world `w` (before it), then moves the world on
fn run(w: &mut World, st: Step, tally: &mut Tally) {
    let before = w.clone();
    let root0 = before.tree.root();
    let tr = w.try_native(&st.op, st.h).unwrap_or_else(|e| panic!("the node refuses the honest operation {:?}: {e}", std::mem::discriminant(&st.op)));
    let name = format!("{:?}", std::mem::discriminant(&st.op));
    tally.ops += 1;
    // the honest operation proves and matches the node's replay
    let pis = before.prove(&st.op, &tr, st.h, root0, &st.signer).unwrap_or_else(|| panic!("the circuit does not prove the honest {name} at {}", st.h));
    assert_eq!(&pis[0..4], &felts(root0)[..]); assert_eq!(&pis[4..8], &felts(w.tree.root())[..]);
    assert_eq!((pis[8], pis[9]), (st.op.fee(), 1)); assert_eq!(&pis[10..14], &data_hash(&st.op)[..]); assert_eq!((pis[14], pis[15]), (S, st.h));
    // a mutation is refused when it does not prove; when it does, the proof must be the honest statement (the mutated field changed nothing the proof speaks of),
    // and must never vouch for the refused operation itself: the block-data hash it carries is the one the node computes for that operation
    let honest = pis.clone();
    let honest_data = data_hash(&st.op);
    let mut must_fail = |tally: &mut Tally, what: String, got: Option<Vec<u64>>, vouches_for: &[u64], other_op_ok: bool| {
        tally.mutations += 1;
        let Some(p) = got else { return };
        if p == honest { tally.harmless += 1; return; }
        if p[10..14] == *vouches_for { tally.failures.push(format!("{name} at {}: {what}: the proof vouches for the refused operation", st.h)); return; }
        if !other_op_ok { tally.failures.push(format!("{name} at {}: {what}: a proof of a statement that is neither the honest one nor the refused one", st.h)); }
    };
    let ks = keys();
    // 1. tampering with the witness
    must_fail(tally, "another signer".into(), before.prove(&st.op, &tr, st.h, root0, &ks.iter().find(|k| k.addr != st.signer.addr).unwrap().clone()), &honest_data, false);
    let mut r2 = root0; r2.elements[0] += F::ONE;
    must_fail(tally, "another root before".into(), before.prove(&st.op, &tr, st.h, r2, &st.signer), &honest_data, false);
    if let Some(t) = &tr.terms { let mut t2 = tr.clone(); let mut tt = t.clone(); tt.set_salt(tt.salt() + 1); t2.terms = Some(tt); if !matches!(st.op, Op::Make { .. }) { must_fail(tally, "other terms than the lock's".into(), before.prove(&st.op, &t2, st.h, root0, &st.signer), &honest_data, false); } }
    let n = tr.touches.len();
    for ti in 0..n {
        let mut variants: Vec<(String, OpTrace)> = vec![];
        let base = tr.clone();
        let mut m = base.clone(); m.touches[ti].sibs[0] = HashOut { elements: [F::from_canonical_u64(5); 4] }; variants.push(("a changed Merkle sibling".into(), m));
        let mut m = base.clone(); m.touches[ti].idx ^= 1; variants.push(("a changed leaf index".into(), m));
        if let Some(a) = tr.touches[ti].old {
            let mut m = base.clone(); let mut x = a; x.bal += 1; m.touches[ti].old = Some(x); variants.push(("a changed balance".into(), m));
            let mut m = base.clone(); let mut x = a; x.nonce += 1; m.touches[ti].old = Some(x); variants.push(("a changed nonce".into(), m));
            if ti == 0 { let mut m = base.clone(); let mut x = a; x.pk[0] += F::ONE; m.touches[ti].old = Some(x); variants.push(("a changed key".into(), m)); }
        }
        for (what, m) in variants {
            // the slot of a new lock may move to another empty slot: a different operation, whose slot the data hash binds
            let moves = matches!(st.op, Op::Make { .. }) && ti == n - 1 && what.contains("index");
            must_fail(tally, format!("touch {ti} of {n}: {what}"), before.prove(&st.op, &m, st.h, root0, &st.signer), &honest_data, moves);
        }
    }
    // 2. other heights: wherever the node refuses, the circuit refuses
    for h2 in st.h.saturating_sub(6).max(1)..=st.h + 6 {
        if h2 == st.h { continue; }
        let mut v = before.clone();
        if v.try_native(&st.op, h2).is_err() { tally.refused_heights += 1; must_fail(tally, format!("the node refuses height {h2}, the circuit proves"), before.prove(&st.op, &tr, h2, root0, &st.signer), &honest_data, false); }
    }
    // 2b. the fee: below the floor, or out of range
    for (what, f) in [("a fee below the floor", S / 100 - 1), ("a fee out of range", 1u64 << 62)] {
        let var = with_fee(&st.op, f);
        let mut v = before.clone();
        assert!(v.try_native(&var, st.h).is_err(), "the node accepts {what}: the test is wrong");
        let vd = data_hash(&var);
        must_fail(tally, format!("rule broken: {what}"), before.prove(&var, &tr, st.h, root0, &st.signer), &vd, false);
    }
    // 3. the rules of the story
    for (what, var) in &st.rules {
        let mut v = before.clone();
        assert!(v.try_native(var, st.h).is_err(), "the node accepts the rule-breaking variant '{what}' of {name}: the test is wrong");
        let mut t2 = tr.clone();
        if let Op::Make { terms, .. } = var { t2.terms = Some(terms.clone()); }
        let vd = data_hash(var);
        must_fail(tally, format!("rule broken: {what}"), before.prove(var, &t2, st.h, root0, &st.signer), &vd, false);
    }
}
fn finish(name: &str, t: Tally) {
    println!("RESULT soundness {name}: {} operations, {} mutations ({} at heights the node refuses), {} harmless (the proof is the honest statement), {} provable that should not be", t.ops, t.mutations, t.refused_heights, t.harmless, t.failures.len());
    assert!(t.failures.is_empty(), "the circuit proves what the node refuses:\n{}", t.failures.join("\n"));
}
fn sign2(a: &mint::Key, b: &mint::Key, msg: [F; 4]) -> ChanSigs { let (ea, sa) = mint::sign(a, msg); let (eb, sb) = mint::sign(b, msg); ChanSigs { ea, sa: mint::s_bytes(&sa), eb, sb: mint::s_bytes(&sb) } }
fn plock(t: u32, amt: u64, to_b: bool, expiry: u64) -> (PLock, [u8; 40]) { let k = num_bigint::BigUint::from(t); (PLock { amt, to_b, point: mint::encode_point(ec::mul_g(&ec::params(), &k)), expiry }, mint::s_bytes(&k)) }
fn with_terms(op: &Op, f: &dyn Fn(&mut Terms)) -> Op { let mut o = op.clone(); if let Op::Make { terms, .. } = &mut o { f(terms); } o }
fn with_fee(op: &Op, f: u64) -> Op {
    let mut o = op.clone();
    match &mut o {
        Op::Make { fee, .. } | Op::VaultClaim { fee, .. } | Op::VaultRefund { fee, .. } | Op::Reserve { fee, .. } | Op::Bid { fee, .. } | Op::OrderClaim { fee, .. } | Op::Reopen { fee, .. } | Op::Return { fee, .. }
        | Op::ChanStart { fee, .. } | Op::ChanUpdate { fee, .. } | Op::ChanSettle { fee, .. } | Op::ChanClose { fee, .. } | Op::ChanFund { fee, .. }
        | Op::FactoryStart { fee, .. } | Op::FactoryPost { fee, .. } | Op::FactoryExit { fee, .. } | Op::FactoryExitNow { fee, .. } | Op::FactoryFund { fee, .. } => *fee = f,
    }
    o
}
fn with_amt(op: &Op, a: u64) -> Op { let mut o = op.clone(); if let Op::Make { amt, .. } = &mut o { *amt = a; } o }

// ---------------------------------------------------------------- vault
#[test]
fn the_vault_circuit_proves_nothing_the_node_refuses() {
    let ks = keys(); let mut w = world(); let mut t = Tally::default();
    let (owner, claimer, dest, other, anyone) = (ks[4].clone(), ks[5].clone(), ks[6].clone(), ks[3].clone(), ks[7].clone());
    let make = Op::Make { from: w.idx(&owner), fee: FEE, amt: 500_000_000, at: 5000, terms: Terms::Vault { key: mint::encode_point(claimer.a), owner: owner.addr, timeout: 20, salt: w.nonce(&owner) } };
    let rules = vec![
        ("the owner is not the sender".to_string(), with_terms(&make, &|t| if let Terms::Vault { owner, .. } = t { *owner = other.addr })),
        ("the timeout is not in the future".into(), with_terms(&make, &|t| if let Terms::Vault { timeout, .. } = t { *timeout = 5 })),
        ("the salt is not the sender's nonce".into(), with_terms(&make, &|t| t.set_salt(t.salt() + 1))),
        ("below the smallest amount".into(), with_amt(&make, S / 6 - 1)),
        ("the amount does not fit".into(), with_amt(&make, 1 << 62)),
    ];
    let hmake = 5;
    let b0 = w.clone();
    run(&mut w, Step { op: make, h: hmake, signer: owner.clone(), rules }, &mut t);
    let lock_addr = w.state[&5000].pk;
    let after_make = w.clone();
    let (e, sv) = mint::sign(&claimer, locks::vault_claim_msg(w.chain, &lock_addr, &dest.addr));
    let claim = Op::VaultClaim { from: w.idx(&anyone), fee: FEE, lock: 5000, to: w.dest(&dest), e, s: mint::s_bytes(&sv) };
    let (e2, s2) = mint::sign(&dest, locks::vault_claim_msg(w.chain, &lock_addr, &dest.addr));
    let rules = vec![
        ("signed by another key than the vault's".to_string(), Op::VaultClaim { from: w.idx(&anyone), fee: FEE, lock: 5000, to: w.dest(&dest), e: e2, s: mint::s_bytes(&s2) }),
        ("the money goes where the vault's key did not say".into(), Op::VaultClaim { from: w.idx(&anyone), fee: FEE, lock: 5000, to: w.dest(&anyone), e, s: mint::s_bytes(&sv) }),
        ("the signature is for another vault".into(), Op::VaultClaim { from: w.idx(&anyone), fee: FEE, lock: 5000, to: w.dest(&dest), e: e ^ 1, s: mint::s_bytes(&sv) }),
    ];
    run(&mut w, Step { op: claim, h: 6, signer: anyone.clone(), rules }, &mut t);
    // the refund, in the world with the vault
    let mut w2 = after_make;
    let refund = Op::VaultRefund { from: w2.idx(&anyone), fee: FEE, lock: 5000, to: w2.dest(&owner) };
    let rules = vec![("the money goes to someone else than the owner".to_string(), Op::VaultRefund { from: w2.idx(&anyone), fee: FEE, lock: 5000, to: w2.dest(&dest) })];
    run(&mut w2, Step { op: refund, h: 21, signer: anyone.clone(), rules }, &mut t);
    let _ = b0;
    finish("vault", t);
}

// ---------------------------------------------------------------- channel
#[test]
fn the_channel_circuit_proves_nothing_the_node_refuses() {
    let ks = keys(); let mut w = world(); let mut t = Tally::default();
    let (a, b, other, anyone) = (ks[4].clone(), ks[5].clone(), ks[3].clone(), ks[7].clone());
    let chan = |salt: u64| Terms::Channel { a: a.addr, b: b.addr, key_a: mint::encode_point(a.a), key_b: mint::encode_point(b.a), delay: 5, oneway: false, salt, state: ChanState::Open };
    let make = Op::Make { from: w.idx(&a), fee: FEE, amt: 600_000_000, at: 5000, terms: chan(w.nonce(&a)) };
    let rules = vec![
        ("the funder is not the sender".to_string(), with_terms(&make, &|t| if let Terms::Channel { a, .. } = t { *a = other.addr })),
        ("a channel joins two accounts".into(), with_terms(&make, &|t| if let Terms::Channel { b, .. } = t { *b = a.addr })),
        ("no dispute window".into(), with_terms(&make, &|t| if let Terms::Channel { delay, .. } = t { *delay = 0 })),
        ("the dispute window is too long".into(), with_terms(&make, &|t| if let Terms::Channel { delay, .. } = t { *delay = 100_001 })),
        ("a new channel is open".into(), with_terms(&make, &|t| if let Terms::Channel { state, .. } = t { *state = ChanState::OpenDual { base_a: 1 } })),
        ("the salt is not the sender's nonce".into(), with_terms(&make, &|t| t.set_salt(t.salt() + 1))),
        ("below the smallest amount".into(), with_amt(&make, S / 6 - 1)),
    ];
    run(&mut w, Step { op: make, h: 3, signer: a.clone(), rules }, &mut t);
    let fresh = w.clone();
    let fund = Op::ChanFund { from: w.idx(&b), fee: FEE, lock: 5000, amt: 200_000_000 };
    let rules = vec![
        ("only b funds the other side".to_string(), Op::ChanFund { from: w.idx(&anyone), fee: FEE, lock: 5000, amt: 200_000_000 }),
        ("nothing to add".into(), Op::ChanFund { from: w.idx(&b), fee: FEE, lock: 5000, amt: 0 }),
        ("the amount does not fit".into(), Op::ChanFund { from: w.idx(&b), fee: FEE, lock: 5000, amt: 1 << 62 }),
    ];
    run(&mut w, Step { op: fund, h: 4, signer: b.clone(), rules }, &mut t);
    let cap = 800_000_000u64;
    let (p1, t1) = plock(11, 100_000_000, true, 100);
    let (p2, _) = plock(12, 50_000_000, false, 8);
    let pl = vec![p1.clone(), p2.clone()];
    let id = w.terms(5000).channel_id().unwrap();
    let upd = |w: &World, seq: u64, bal_a: u64, pl: &Vec<PLock>| Op::ChanUpdate { from: w.idx(&anyone), fee: FEE, lock: 5000, seq, bal_a, locks: pl.clone(), sigs: sign2(&a, &b, locks::chan_state_msg(w.chain, &id, seq, bal_a, cap, pl)) };
    let mut bad_pl = |f: &dyn Fn(&mut PLock)| { let mut x = pl.clone(); f(&mut x[0]); x };
    let rules = vec![
        ("update number 0".to_string(), upd(&w, 0, 300_000_000, &pl)),
        ("update number 2^62".into(), upd(&w, 1 << 62, 300_000_000, &pl)),
        ("shares beyond the channel".into(), upd(&w, 1, 700_000_000, &pl)),
        ("a point lock without an amount".into(), upd(&w, 1, 300_000_000, &bad_pl(&|p| p.amt = 0))),
        ("a point lock that expired already".into(), upd(&w, 1, 300_000_000, &bad_pl(&|p| p.expiry = 5))),
        ("a point lock expiring after 2^62".into(), upd(&w, 1, 300_000_000, &bad_pl(&|p| p.expiry = 1 << 62))),
        ("b did not sign".into(), Op::ChanUpdate { from: w.idx(&anyone), fee: FEE, lock: 5000, seq: 1, bal_a: 300_000_000, locks: pl.clone(), sigs: sign2(&a, &other, locks::chan_state_msg(w.chain, &id, 1, 300_000_000, cap, &pl)) }),
        ("signed for other balances".into(), Op::ChanUpdate { from: w.idx(&anyone), fee: FEE, lock: 5000, seq: 1, bal_a: 300_000_000, locks: pl.clone(), sigs: sign2(&a, &b, locks::chan_state_msg(w.chain, &id, 1, 299_999_999, cap, &pl)) }),
    ];
    let u1 = upd(&w, 1, 300_000_000, &pl);
    run(&mut w, Step { op: u1, h: 5, signer: anyone.clone(), rules }, &mut t);
    let rules = vec![("not newer than the state waiting".to_string(), upd(&w, 1, 250_000_000, &pl))];
    let u2 = upd(&w, 2, 250_000_000, &pl);
    run(&mut w, Step { op: u2, h: 6, signer: anyone.clone(), rules }, &mut t);
    let settle = |w: &World, wits: Vec<Option<[u8; 40]>>| Op::ChanSettle { from: w.idx(&anyone), fee: FEE, lock: 5000, wits, to_a: w.dest(&a), to_b: w.dest(&b) };
    let rules = vec![
        ("a point lock neither opened nor expired".to_string(), settle(&w, vec![None, None])),
        ("a witness that does not open its lock".into(), settle(&w, vec![Some(mint::s_bytes(&num_bigint::BigUint::from(99u32))), None])),
        ("one witness entry per point lock".into(), settle(&w, vec![Some(t1)])),
        ("the payout goes to the wrong account".into(), Op::ChanSettle { from: w.idx(&anyone), fee: FEE, lock: 5000, wits: vec![Some(t1), None], to_a: w.dest(&b), to_b: w.dest(&b) }),
    ];
    let st = settle(&w, vec![Some(t1), None]);
    run(&mut w, Step { op: st, h: 12, signer: anyone.clone(), rules }, &mut t);
    // a start, then a close by agreement, each on the fresh channel
    let mut w2 = fresh.clone();
    let start = Op::ChanStart { from: w2.idx(&a), fee: FEE, lock: 5000 };
    let rules = vec![("only the channel's two sides start a close".to_string(), Op::ChanStart { from: w2.idx(&anyone), fee: FEE, lock: 5000 })];
    run(&mut w2, Step { op: start, h: 5, signer: a.clone(), rules }, &mut t);
    let mut w3 = fresh;
    let id = w3.terms(5000).channel_id().unwrap();
    let close = |w: &World, bal_a: u64, signer_b: &mint::Key| Op::ChanClose { from: w.idx(&anyone), fee: FEE, lock: 5000, bal_a, sigs: sign2(&a, signer_b, locks::chan_close_msg(w.chain, &id, bal_a, 600_000_000)), to_a: w.dest(&a), to_b: w.dest(&b) };
    let rules = vec![
        ("b did not sign".to_string(), close(&w3, 400_000_000, &other)),
        ("a's share is more than the channel holds".into(), close(&w3, 700_000_000, &b)),
        ("signed for other balances".into(), Op::ChanClose { from: w3.idx(&anyone), fee: FEE, lock: 5000, bal_a: 400_000_000, sigs: sign2(&a, &b, locks::chan_close_msg(w3.chain, &id, 399_999_999, 600_000_000)), to_a: w3.dest(&a), to_b: w3.dest(&b) }),
    ];
    let c = close(&w3, 400_000_000, &b);
    run(&mut w3, Step { op: c, h: 6, signer: anyone.clone(), rules }, &mut t);
    // a stream: only a signs, the state is the amount paid
    let mut w4 = world();
    let stream = Terms::Channel { a: a.addr, b: b.addr, key_a: mint::encode_point(a.a), key_b: mint::encode_point(b.a), delay: 5, oneway: true, salt: w4.nonce(&a), state: ChanState::Open };
    let mk = Op::Make { from: w4.idx(&a), fee: FEE, amt: 600_000_000, at: 5000, terms: stream };
    run(&mut w4, Step { op: mk, h: 3, signer: a.clone(), rules: vec![] }, &mut t);
    let sid = w4.terms(5000).channel_id().unwrap();
    let pay = |w: &World, paid: u64, bal_a: u64, pl: &Vec<PLock>| { let (ea, sa) = mint::sign(&a, locks::chan_state_msg(w.chain, &sid, paid, bal_a, 600_000_000, pl)); Op::ChanUpdate { from: w.idx(&anyone), fee: FEE, lock: 5000, seq: paid, bal_a, locks: pl.clone(), sigs: ChanSigs { ea, sa: mint::s_bytes(&sa), eb: 0, sb: [0; 40] } } };
    let rules = vec![
        ("a stream's state is the amount paid".to_string(), pay(&w4, 100_000_000, 499_999_999, &vec![])),
        ("a stream holds no point locks".into(), pay(&w4, 100_000_000, 400_000_000, &vec![p1.clone()])),
        ("a stream cannot have paid more than it holds".into(), pay(&w4, 700_000_000, 0, &vec![])),
    ];
    let up = pay(&w4, 100_000_000, 500_000_000, &vec![]);
    run(&mut w4, Step { op: up, h: 4, signer: anyone.clone(), rules }, &mut t);
    finish("channel", t);
}

// ---------------------------------------------------------------- order
#[test]
fn the_order_circuit_proves_nothing_the_node_refuses() {
    let ks = keys(); let mut w = world(); let mut t = Tally::default();
    let (maker, taker, taker2, payto, other, anyone) = (ks[4].clone(), ks[5].clone(), ks[6].clone(), ks[2].clone(), ks[3].clone(), ks[7].clone());
    let order = |salt: u64, state: OrderState| Terms::Order { maker: maker.addr, sell: 600_000_000, want_chain: 1, want_amt: 5_000, pay_to: payto.addr, expiry: 40, reserve_blocks: 5, deposit: 12_000_000, salt, state };
    let make = Op::Make { from: w.idx(&maker), fee: FEE, amt: 600_000_000, at: 5000, terms: order(w.nonce(&maker), OrderState::Open) };
    let chain = w.chain;
    let rules: Vec<(String, Op)> = vec![
        ("the maker is not the sender".to_string(), with_terms(&make, &|t| if let Terms::Order { maker, .. } = t { *maker = other.addr })),
        ("the order sells what the lock holds".into(), with_terms(&make, &|t| if let Terms::Order { sell, .. } = t { *sell += 1 })),
        ("no chain 0".into(), with_terms(&make, &|t| if let Terms::Order { want_chain, .. } = t { *want_chain = 0 })),
        ("no chain 4".into(), with_terms(&make, &|t| if let Terms::Order { want_chain, .. } = t { *want_chain = 4 })),
        ("this chain's own metal".into(), with_terms(&make, &|t| if let Terms::Order { want_chain, .. } = t { *want_chain = chain })),
        ("nothing asked".into(), with_terms(&make, &|t| if let Terms::Order { want_amt, .. } = t { *want_amt = 0 })),
        ("the asked amount is out of range".into(), with_terms(&make, &|t| if let Terms::Order { want_amt, .. } = t { *want_amt = 1 << 62 })),
        ("expired already".into(), with_terms(&make, &|t| if let Terms::Order { expiry, .. } = t { *expiry = 3 })),
        ("no reservation time".into(), with_terms(&make, &|t| if let Terms::Order { reserve_blocks, .. } = t { *reserve_blocks = 0 })),
        ("a reservation time that is too long".into(), with_terms(&make, &|t| if let Terms::Order { reserve_blocks, .. } = t { *reserve_blocks = 100_001 })),
        ("the deposit is below 1%".into(), with_terms(&make, &|t| if let Terms::Order { deposit, .. } = t { *deposit = 5_999_999 })),
        ("a new order is not reserved".into(), with_terms(&make, &|t| if let Terms::Order { state, .. } = t { *state = OrderState::Reserved { taker: taker.addr, until: 9, since: 1 } })),
        ("an auction window of 0".into(), with_terms(&make, &|t| if let Terms::Order { state, .. } = t { *state = OrderState::Auction { window: 0 } })),
        ("an auction window that is too long".into(), with_terms(&make, &|t| if let Terms::Order { state, .. } = t { *state = OrderState::Auction { window: 10_001 } })),
        ("the salt is not the sender's nonce".into(), with_terms(&make, &|t| t.set_salt(t.salt() + 1))),
        ("below the smallest amount".into(), with_amt(&with_terms(&make, &|t| if let Terms::Order { sell, deposit, .. } = t { *sell = 100; *deposit = 1 }), 100)),
    ];
    run(&mut w, Step { op: make, h: 3, signer: maker.clone(), rules }, &mut t);
    let open = w.clone();
    let rs = Op::Reserve { from: w.idx(&taker), fee: FEE, lock: 5000, taker: taker.addr };
    run(&mut w, Step { op: rs, h: 4, signer: taker.clone(), rules: vec![] }, &mut t);
    let reserved = w.clone();
    // a claim inside the reservation (until 9)
    let mut wc = reserved.clone();
    let claim = Op::OrderClaim { from: wc.idx(&anyone), fee: FEE, lock: 5000, to: wc.dest(&taker), proof: vec![1, 2, 3] };
    let rules = vec![("the money goes to someone else than the taker".to_string(), Op::OrderClaim { from: wc.idx(&anyone), fee: FEE, lock: 5000, to: wc.dest(&anyone), proof: vec![1, 2, 3] })];
    run(&mut wc, Step { op: claim, h: 9, signer: anyone.clone(), rules }, &mut t);
    // a reopen after the reservation, the escrow to the maker
    let mut wr = reserved.clone();
    let reopen = Op::Reopen { from: wr.idx(&anyone), fee: FEE, lock: 5000, to: wr.dest(&maker) };
    let rules = vec![("the escrow goes to someone else than the maker".to_string(), Op::Reopen { from: wr.idx(&anyone), fee: FEE, lock: 5000, to: wr.dest(&anyone) })];
    run(&mut wr, Step { op: reopen, h: 10, signer: anyone.clone(), rules }, &mut t);
    // a return after the expiry of the order that was never reserved
    let mut wo = open.clone();
    let ret = Op::Return { from: wo.idx(&anyone), fee: FEE, lock: 5000, to: wo.dest(&maker) };
    let rules = vec![("the sale goes to someone else than the maker".to_string(), Op::Return { from: wo.idx(&anyone), fee: FEE, lock: 5000, to: wo.dest(&anyone) })];
    run(&mut wo, Step { op: ret, h: 41, signer: anyone.clone(), rules }, &mut t);
    // the rules that need a borrowed shape: a return of a reserved order, a claim of an open one, a reopen of an open one
    {
        let mut v = reserved.clone();
        let reopen = Op::Reopen { from: v.idx(&anyone), fee: FEE, lock: 5000, to: v.dest(&maker) };
        let tr = v.try_native(&reopen, 41).unwrap();
        let ret = Op::Return { from: reserved.idx(&anyone), fee: FEE, lock: 5000, to: reserved.dest(&maker) };
        t.mutations += 1;
        if reserved.prove(&ret, &tr, 41, reserved.tree.root(), &anyone).is_some() { t.failures.push("a reserved order is returned".into()); }
        let mut v = open.clone();
        let ret = Op::Return { from: v.idx(&anyone), fee: FEE, lock: 5000, to: v.dest(&maker) };
        let tr = v.try_native(&ret, 41).unwrap();
        for (what, op) in [("an open order is claimed", Op::OrderClaim { from: open.idx(&anyone), fee: FEE, lock: 5000, to: open.dest(&maker), proof: vec![1] }), ("an open order is reopened", Op::Reopen { from: open.idx(&anyone), fee: FEE, lock: 5000, to: open.dest(&maker) })] {
            t.mutations += 1;
            if open.prove(&op, &tr, 41, open.tree.root(), &anyone).is_some() { t.failures.push(what.into()); }
        }
        let rs2 = Op::Reserve { from: reserved.idx(&anyone), fee: FEE, lock: 5000, taker: anyone.addr };
        let mut v = open.clone();
        let tr = v.try_native(&Op::Reserve { from: open.idx(&anyone), fee: FEE, lock: 5000, taker: anyone.addr }, 5).unwrap();
        t.mutations += 1;
        if reserved.prove(&rs2, &tr, 5, reserved.tree.root(), &anyone).is_some() { t.failures.push("a reserved order is reserved again".into()); }
    }
    // an auction
    let mut wa = world();
    let auc = Op::Make { from: wa.idx(&maker), fee: FEE, amt: 600_000_000, at: 5000, terms: order(wa.nonce(&maker), OrderState::Auction { window: 3 }) };
    run(&mut wa, Step { op: auc, h: 3, signer: maker.clone(), rules: vec![] }, &mut t);
    let bid = |w: &World, from: &mint::Key, bid: u64, refund: &mint::Key| Op::Bid { from: w.idx(from), fee: FEE, lock: 5000, taker: from.addr, bid, refund: w.dest(refund) };
    let rules = vec![("no bid".to_string(), bid(&wa, &taker, 0, &taker)), ("a bid below the deposit".into(), bid(&wa, &taker, 11_999_999, &taker)), ("a bid out of range".into(), bid(&wa, &taker, 1 << 62, &taker))];
    let b1 = bid(&wa, &taker, 15_000_000, &taker);
    run(&mut wa, Step { op: b1, h: 5, signer: taker.clone(), rules }, &mut t);
    let rules = vec![("a bid that is not higher".to_string(), bid(&wa, &taker2, 15_000_000, &taker)), ("the refund goes to someone else than the bidder".into(), bid(&wa, &taker2, 20_000_000, &anyone))];
    let b2 = bid(&wa, &taker2, 20_000_000, &taker);
    run(&mut wa, Step { op: b2, h: 6, signer: taker2.clone(), rules }, &mut t);
    let ro = Op::Reopen { from: wa.idx(&anyone), fee: FEE, lock: 5000, to: wa.dest(&maker) };
    run(&mut wa, Step { op: ro, h: 14, signer: anyone.clone(), rules: vec![] }, &mut t);
    finish("order", t);
}

// ---------------------------------------------------------------- factory
#[test]
fn the_factory_circuit_proves_nothing_the_node_refuses() {
    let ks = keys(); let mut w = world(); let mut t = Tally::default();
    let (coord, m0, m1, other, anyone) = (ks[4].clone(), ks[5].clone(), ks[6].clone(), ks[3].clone(), ks[7].clone());
    let fm = |k: &mint::Key, cap: u64| FMember { addr: k.addr, key: mint::encode_point(k.a), cap, base: cap, state: SubState::Open };
    let fact = |salt: u64| Terms::Factory { coord: coord.addr, key_c: mint::encode_point(coord.a), delay: 3, salt, members: vec![fm(&m0, 300_000_000), fm(&m1, 300_000_000)] };
    let make = Op::Make { from: w.idx(&coord), fee: FEE, amt: 600_000_000, at: 5000, terms: fact(w.nonce(&coord)) };
    let mem = |t: &mut Terms, i: usize, f: &dyn Fn(&mut FMember)| if let Terms::Factory { members, .. } = t { f(&mut members[i]) };
    let rules: Vec<(String, Op)> = vec![
        ("the coordinator is not the sender".to_string(), with_terms(&make, &|t| if let Terms::Factory { coord, .. } = t { *coord = other.addr })),
        ("no dispute window".into(), with_terms(&make, &|t| if let Terms::Factory { delay, .. } = t { *delay = 0 })),
        ("the dispute window is too long".into(), with_terms(&make, &|t| if let Terms::Factory { delay, .. } = t { *delay = 100_001 })),
        ("no members".into(), with_terms(&make, &|t| if let Terms::Factory { members, .. } = t { members.clear() })),
        ("the channels do not add up to the amount".into(), with_amt(&make, 600_000_001)),
        ("a channel with nothing in it".into(), with_terms(&make, &|t| { mem(t, 0, &|m| { m.cap = 0; m.base = 0 }); })),
        ("a channel whose base is not its size".into(), with_terms(&make, &|t| mem(t, 1, &|m| m.base = 1))),
        ("a member that has left already".into(), with_terms(&make, &|t| mem(t, 1, &|m| m.state = SubState::Exited))),
        ("a channel that is closing already".into(), with_terms(&make, &|t| mem(t, 0, &|m| m.state = SubState::Closing { seq: 1, bal_c: 1, until: 9, locks: vec![] }))),
        ("the salt is not the sender's nonce".into(), with_terms(&make, &|t| t.set_salt(t.salt() + 1))),
        ("below the smallest amount".into(), with_amt(&with_terms(&make, &|t| { mem(t, 0, &|m| { m.cap = 50; m.base = 50 }); mem(t, 1, &|m| { m.cap = 50; m.base = 50 }); }), 100)),
    ];
    run(&mut w, Step { op: make, h: 3, signer: coord.clone(), rules }, &mut t);
    let fund = Op::FactoryFund { from: w.idx(&m0), fee: FEE, lock: 5000, idx: 0, amt: 50_000_000 };
    let rules = vec![
        ("only the member funds its own channel".to_string(), Op::FactoryFund { from: w.idx(&anyone), fee: FEE, lock: 5000, idx: 0, amt: 50_000_000 }),
        ("nothing to add".into(), Op::FactoryFund { from: w.idx(&m0), fee: FEE, lock: 5000, idx: 0, amt: 0 }),
        ("the amount does not fit".into(), Op::FactoryFund { from: w.idx(&m0), fee: FEE, lock: 5000, idx: 0, amt: 1 << 62 }),
        ("a member that is not there".into(), Op::FactoryFund { from: w.idx(&m0), fee: FEE, lock: 5000, idx: 2, amt: 50_000_000 }),
    ];
    run(&mut w, Step { op: fund, h: 4, signer: m0.clone(), rules }, &mut t);
    let start = Op::FactoryStart { from: w.idx(&coord), fee: FEE, lock: 5000, idx: 0 };
    let rules = vec![("only the coordinator and the member start a close".to_string(), Op::FactoryStart { from: w.idx(&anyone), fee: FEE, lock: 5000, idx: 0 })];
    let before_start = w.clone();
    run(&mut w, Step { op: start, h: 5, signer: coord.clone(), rules }, &mut t);
    // member 0 closes by agreement while its window runs (until 8)
    let fid = w.terms(5000).factory_id().unwrap();
    let cap0 = 350_000_000u64;
    let now = |w: &World, bal_c: u64, signer: &mint::Key, cap: u64| Op::FactoryExitNow { from: w.idx(&anyone), fee: FEE, lock: 5000, idx: 0, bal_c, sigs: sign2(&coord, signer, locks::fact_close_msg(w.chain, &fid, 0, bal_c, cap)), to_c: w.dest(&coord), to_m: w.dest(&m0) };
    let rules = vec![
        ("the member did not sign".to_string(), now(&w, 100_000_000, &other, cap0)),
        ("the coordinator's share is more than the channel holds".into(), now(&w, 400_000_000, &m0, cap0)),
        ("signed for another size".into(), now(&w, 100_000_000, &m0, cap0 - 1)),
    ];
    let en = now(&w, 100_000_000, &m0, cap0);
    run(&mut w, Step { op: en, h: 6, signer: anyone.clone(), rules }, &mut t);
    // member 1 posts a state with point locks, then leaves after the window
    let (p1, t1) = plock(11, 100_000_000, true, 100);
    let (p2, _) = plock(12, 50_000_000, false, 8);
    let pl = vec![p1, p2];
    let fid = w.terms(5000).factory_id().unwrap();
    let post = |w: &World, seq: u64, bal_c: u64, pl: &Vec<PLock>, sb: &mint::Key| Op::FactoryPost { from: w.idx(&anyone), fee: FEE, lock: 5000, idx: 1, seq, bal_c, locks: pl.clone(), sigs: sign2(&coord, sb, locks::fact_state_msg(w.chain, &fid, 1, seq, bal_c, 300_000_000, pl)) };
    let bad_pl = |f: &dyn Fn(&mut PLock)| { let mut x = pl.clone(); f(&mut x[0]); x };
    let rules = vec![
        ("update number 0".to_string(), post(&w, 0, 100_000_000, &pl, &m1)),
        ("update number 2^62".into(), post(&w, 1 << 62, 100_000_000, &pl, &m1)),
        ("shares beyond the channel".into(), post(&w, 1, 300_000_000, &pl, &m1)),
        ("a point lock without an amount".into(), post(&w, 1, 100_000_000, &bad_pl(&|p| p.amt = 0), &m1)),
        ("a point lock that expired already".into(), post(&w, 1, 100_000_000, &bad_pl(&|p| p.expiry = 5), &m1)),
        ("a point lock expiring after 2^62".into(), post(&w, 1, 100_000_000, &bad_pl(&|p| p.expiry = 1 << 62), &m1)),
        ("the member did not sign".into(), post(&w, 1, 100_000_000, &pl, &other)),
        ("a member that has left".into(), Op::FactoryPost { from: w.idx(&anyone), fee: FEE, lock: 5000, idx: 0, seq: 1, bal_c: 100_000_000, locks: vec![], sigs: sign2(&coord, &m0, locks::fact_state_msg(w.chain, &fid, 0, 1, 100_000_000, cap0, &[])) }),
    ];
    let p = post(&w, 1, 100_000_000, &pl, &m1);
    run(&mut w, Step { op: p, h: 7, signer: anyone.clone(), rules }, &mut t);
    let exit = |w: &World, wits: Vec<Option<[u8; 40]>>| Op::FactoryExit { from: w.idx(&anyone), fee: FEE, lock: 5000, idx: 1, wits, to_c: w.dest(&coord), to_m: w.dest(&m1) };
    let rules = vec![
        ("a point lock neither opened nor expired".to_string(), exit(&w, vec![None, None])),
        ("a witness that does not open its lock".into(), exit(&w, vec![Some(mint::s_bytes(&num_bigint::BigUint::from(99u32))), None])),
        ("one witness entry per point lock".into(), exit(&w, vec![Some(t1)])),
        ("a member that is not closing".into(), Op::FactoryExit { from: w.idx(&anyone), fee: FEE, lock: 5000, idx: 0, wits: vec![], to_c: w.dest(&coord), to_m: w.dest(&m0) }),
    ];
    let ex = exit(&w, vec![Some(t1), None]);
    run(&mut w, Step { op: ex, h: 11, signer: anyone.clone(), rules }, &mut t);
    let _ = before_start;
    finish("factory", t);
}
