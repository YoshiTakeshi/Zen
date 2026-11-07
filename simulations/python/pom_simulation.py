"""
pom_simulation.py - Proof of concept of Proof of Minting (PoM) for Golden Yen.

    python3 pom_simulation.py            (about 1-2 minutes)

What is real and what is simulated
----------------------------------
REAL   : Ed25519 signatures on every transaction, SHA-256 blows (minter lottery),
         SHA-256 seals (miner race), fee rules, balances, fee split, block reward
         formula, difficulty adjustment, conservation of coins.
SIMULATED: the zero-knowledge proofs. A "proof" here is a record with exactly the
         claims a real proof would carry (pre-state root, post-state root, number
         of transactions, fees, credits root, prover). Verifying it re-executes the
         work instead of checking a succinct proof. The tree shape, the hand-over
         rule, who proves what and who gets paid are the same as with real proofs.
         Time is counted in ticks (1 tick ~ 1 second of a phone).

Roles
-----
users   : 1000 accounts sending signed payments
minters : 1000 (950 phones, 50 desktops/servers) - hash blows, prove strikes, share 75% of fees
miners  : 20 - race to seal each minted block, take the block reward + 25% of fees
"""

import hashlib, math, random, statistics as st, struct, time
from dataclasses import dataclass, field
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey, Ed25519PublicKey
from cryptography.hazmat.primitives import serialization
from cryptography.exceptions import InvalidSignature

H = lambda *parts: hashlib.sha256(b"".join(parts)).digest()
RNG = random.Random(42)

# ----------------------------------------------------------------------------- parameters
PICO = 10 ** 12
FEE_MIN, FEE_MAX = 0.0001, 0.025      # Golden Yen fineness limits
LEAF_SIZE = 16                        # transactions per leaf strike
MAX_TX = 512                          # block capacity (transactions)
N_MIN = 300                           # density target: transactions the stamp must cover
TARGET_MINT_TICKS = 90                # pace the network aims for
MINTER_SHARE = 0.75                   # fees to minters; rest to the sealing miner
STRIKE_TIMEOUT = 20                   # ticks before an undelivered strike is reassigned
BLOCKS = 30
TX_BYTES_COMPACT = 60                 # per-tx data in a minted block (no signature: the stamp covers it)
TX_BYTES_RAW = 124                    # same tx with its 64-byte signature (classic block)
STAMP_BYTES = 300                     # size of one succinct proof, independent of block size
HEADER_BYTES = 200


def raw_reward(n):                    # Zen page: 2520 * (1/2)^(log N / log phi)
    return 2520 * 0.5 ** (math.log(n) / math.log(1.6180339)) if n > 1 else 2520.0


# ----------------------------------------------------------------------------- accounts & txs
def addr_of(pub: Ed25519PublicKey) -> bytes:
    raw = pub.public_bytes(serialization.Encoding.Raw, serialization.PublicFormat.Raw)
    return H(raw)[:20]


@dataclass
class Tx:
    sender: bytes
    pubkey: bytes
    receiver: bytes
    amount: int
    fee: int
    nonce: int
    sig: bytes = b""

    def body(self):
        return self.sender + self.receiver + struct.pack(">QQI", self.amount, self.fee, self.nonce)

    @property
    def fee_rate(self):
        return self.fee / (self.amount + self.fee)


def sig_ok(tx: Tx) -> bool:
    try:
        Ed25519PublicKey.from_public_bytes(tx.pubkey).verify(tx.sig, tx.body())
        return addr_of(Ed25519PublicKey.from_public_bytes(tx.pubkey)) == tx.sender
    except InvalidSignature:
        return False


class State:
    def __init__(self):
        self.bal, self.nonce = {}, {}

    def copy(self):
        s = State(); s.bal = dict(self.bal); s.nonce = dict(self.nonce); return s

    def root(self):
        h = hashlib.sha256()
        for a in sorted(self.bal):
            h.update(a + struct.pack(">QI", self.bal[a], self.nonce.get(a, 0)))
        return h.digest()

    def check(self, tx: Tx):
        """The rules a leaf proof certifies. Returns None if valid, else the reason."""
        if not sig_ok(tx): return "bad signature"
        if not (FEE_MIN <= tx.fee_rate <= FEE_MAX): return "fee outside fineness limits"
        if self.nonce.get(tx.sender, 0) != tx.nonce: return "bad nonce"
        if self.bal.get(tx.sender, 0) < tx.amount + tx.fee: return "insufficient balance"
        return None

    def apply(self, tx: Tx):
        self.bal[tx.sender] -= tx.amount + tx.fee
        self.bal[tx.receiver] = self.bal.get(tx.receiver, 0) + tx.amount
        self.nonce[tx.sender] = tx.nonce + 1

    def credit(self, a, v):
        self.bal[a] = self.bal.get(a, 0) + v


# ----------------------------------------------------------------------------- proofs (simulated)
@dataclass
class Proof:
    kind: str                 # "leaf" or "merge"
    lo: int                   # first leaf index covered
    hi: int                   # last leaf index covered (inclusive)
    pre: bytes                # state root before
    post: bytes               # state root after
    n_tx: int
    fees: int
    credits_root: bytes       # commits to every prover below
    prover: bytes
    credits: list = field(default_factory=list)   # (prover, kind) list the root commits to

    def digest(self):
        return H(self.kind.encode(), struct.pack(">IIQQ", self.lo, self.hi, self.n_tx, self.fees),
                 self.pre, self.post, self.credits_root, self.prover)


def make_leaf(i, txs, snap: State, prover, cheat=False):
    s = snap.copy(); pre = s.root(); fees = 0
    for tx in txs:
        s.apply(tx); fees += tx.fee
    post = s.root()
    if cheat:                                  # a dishonest minter claims a wrong result
        post = H(b"forged", post)
    return Proof("leaf", i, i, pre, post, len(txs), fees, H(b"leaf", prover), prover, [(prover, "leaf")])


def verify_leaf(p: Proof, txs, snap: State):
    """Stand-in for SNARK verification: re-execute and compare every claim."""
    s = snap.copy()
    if s.root() != p.pre: return False
    fees = 0
    for tx in txs:
        if s.check(tx): return False
        s.apply(tx); fees += tx.fee
    return (s.root() == p.post and p.n_tx == len(txs) and p.fees == fees
            and p.credits_root == H(b"leaf", p.prover))


def make_merge(a: Proof, b: Proof, prover):
    return Proof("merge", a.lo, b.hi, a.pre, b.post, a.n_tx + b.n_tx, a.fees + b.fees,
                 H(b"merge", a.credits_root, b.credits_root, prover), prover,
                 a.credits + b.credits + [(prover, "merge")])


def verify_merge(p: Proof, a: Proof, b: Proof):
    return (a.post == b.pre and a.hi + 1 == b.lo and p.lo == a.lo and p.hi == b.hi
            and p.pre == a.pre and p.post == b.post and p.n_tx == a.n_tx + b.n_tx
            and p.fees == a.fees + b.fees
            and p.credits_root == H(b"merge", a.credits_root, b.credits_root, p.prover))


# ----------------------------------------------------------------------------- participants
@dataclass
class Minter:
    addr: bytes
    kind: str          # "phone" or "server"
    hashes_per_tick: int
    prove_ticks: int   # ticks to finish one strike
    drop_rate: float   # chance a strike is never delivered (phone goes offline)
    cheater: bool = False
    nonce: int = 0
    busy_until: int = -1


@dataclass
class Miner:
    addr: bytes
    hashes_per_tick: int


def blow_hash(prev, addr, nonce):
    return H(prev, addr, struct.pack(">Q", nonce))


def below(h, p):                       # hash interpreted as a number in [0,1)
    return int.from_bytes(h[:8], "big") < p * 2 ** 64


# ----------------------------------------------------------------------------- task tree
class Tree:
    """Leaves 0..L-1, merges built bottom-up by pairing adjacent finished proofs."""
    def __init__(self, n_leaves):
        self.levels = [[None] * n_leaves]
        n = n_leaves
        while n > 1:
            n = (n + 1) // 2
            self.levels.append([None] * n)

    def open_tasks(self, assigned):
        out = []
        for i, p in enumerate(self.levels[0]):
            if p is None and ("leaf", 0, i) not in assigned: out.append(("leaf", 0, i))
        for lv in range(1, len(self.levels)):
            below_ = self.levels[lv - 1]
            for j, p in enumerate(self.levels[lv]):
                if p is not None: continue
                a = below_[2 * j]
                b = below_[2 * j + 1] if 2 * j + 1 < len(below_) else None
                if 2 * j + 1 >= len(below_):          # odd one out: promoted without work
                    if a is not None: self.levels[lv][j] = a
                    continue
                if a is not None and b is not None and ("merge", lv, j) not in assigned:
                    out.append(("merge", lv, j))
        return out

    def root(self):
        return self.levels[-1][0]


# ----------------------------------------------------------------------------- the network
class Network:
    def __init__(self):
        self.state = State()
        self.users = []
        for _ in range(1000):
            k = Ed25519PrivateKey.generate()
            pub = k.public_key()
            a = addr_of(pub)
            self.users.append((k, pub.public_bytes(serialization.Encoding.Raw, serialization.PublicFormat.Raw), a))
            self.state.bal[a] = RNG.randint(5, 500) * PICO
        self.genesis_supply = sum(self.state.bal.values())

        self.minters = []
        for i in range(1000):
            a = H(b"minter", struct.pack(">I", i))[:20]
            if i < 950:
                m = Minter(a, "phone", RNG.randint(1, 3), RNG.randint(3, 6), 0.03)
            else:
                m = Minter(a, "server", RNG.randint(25, 60), 1, 0.0)
            self.minters.append(m)
        for i in RNG.sample(range(1000), 5):
            self.minters[i].cheater = True
        self.miners = [Miner(H(b"miner", struct.pack(">I", i))[:20], RNG.randint(50, 400)) for i in range(20)]

        self.blow_p = 1.5e-4
        self.seal_p = 2e-5
        self.prev = H(b"genesis")
        self.height = 0
        self.minted_reward_total = 0
        self.log = []
        self.events = {"forged proofs rejected": 0, "stolen blows rejected": 0, "strikes timed out": 0,
                       "invalid txs filtered": 0}
        self.earned = {m.addr: 0 for m in self.minters}
        self.mined = {m.addr: 0 for m in self.miners}
        self.minter_work_hashes = {m.addr: 0 for m in self.minters}

    # users -------------------------------------------------------------
    def make_mempool(self, n):
        pool = []
        senders = RNG.sample(self.users, n)
        for k, pub, a in senders:
            bal = self.state.bal.get(a, 0)
            amount = int(bal * RNG.uniform(0.01, 0.3))
            rate = math.exp(RNG.uniform(math.log(FEE_MIN * 1.05), math.log(FEE_MAX * 0.95)))
            fee = int(amount * rate / (1 - rate))
            r = RNG.random()
            if r < 0.02: fee = int(amount * 0.05)          # fee above the maximum fineness
            if r > 0.98: amount = bal * 2                   # overspend
            tx = Tx(a, pub, RNG.choice(self.users)[2], max(amount, 1), max(fee, 1), self.state.nonce.get(a, 0))
            tx.sig = k.sign(tx.body())
            if 0.97 < r <= 0.98: tx.sig = bytes(64)         # forged signature
            pool.append(tx)
        return pool

    # minting -----------------------------------------------------------
    def mint(self, mempool):
        # 1. canonical transaction list (every node computes the same one)
        s = self.state.copy(); txs = []
        for tx in sorted(mempool, key=lambda t: -t.fee_rate):
            if s.check(tx):
                self.events["invalid txs filtered"] += 1; continue
            s.apply(tx); txs.append(tx)
            if len(txs) == MAX_TX: break
        quiet = len(txs) < N_MIN
        leaves = [txs[i:i + LEAF_SIZE] for i in range(0, len(txs), LEAF_SIZE)]
        snaps, s = [], self.state.copy()             # state providers: snapshot at each leaf boundary
        for lt in leaves:
            snaps.append(s.copy())
            for tx in lt: s.apply(tx)

        tree = Tree(len(leaves))
        assigned = {}            # task -> (minter, due_tick, blow nonce)
        blow_queue = []          # winning blows waiting for an open task
        strikes = []             # (minter addr, kind) credited when the proof verifies
        tick, blows_won, hashes = 0, 0, 0
        prev = self.prev

        while tree.root() is None or tree.root().n_tx < len(txs) or tree.root().lo != 0:
            tick += 1
            # 2. blows: every minter hashes; winners are announced and verified by everyone
            for m in self.minters:
                for _ in range(m.hashes_per_tick):
                    h = blow_hash(prev, m.addr, m.nonce); m.nonce += 1; hashes += 1
                    self.minter_work_hashes[m.addr] += 1
                    if below(h, self.blow_p):
                        # a thief re-broadcasts someone else's winning nonce under his own address
                        if RNG.random() < 0.01:
                            thief = RNG.choice(self.minters)
                            if not below(blow_hash(prev, thief.addr, m.nonce - 1), self.blow_p):
                                self.events["stolen blows rejected"] += 1
                        blow_queue.append(m); blows_won += 1
            # 3. strikes: each queued blow takes the next open task
            for task in tree.open_tasks(assigned):
                if not blow_queue: break
                m = blow_queue.pop(0)
                assigned[task] = (m, tick + m.prove_ticks, tick + STRIKE_TIMEOUT, RNG.random() < m.drop_rate)
            # 4. deliveries
            for task, (m, done, timeout, dropped) in list(assigned.items()):
                kind, lv, j = task
                if tick < done: continue
                if dropped:
                    if tick >= timeout:
                        del assigned[task]; self.events["strikes timed out"] += 1
                    continue
                if kind == "leaf":
                    p = make_leaf(j, leaves[j], snaps[j], m.addr, cheat=m.cheater)
                    ok = verify_leaf(p, leaves[j], snaps[j])
                else:
                    a, b = tree.levels[lv - 1][2 * j], tree.levels[lv - 1][2 * j + 1]
                    p = make_merge(a, b, m.addr)
                    ok = verify_merge(p, a, b)
                del assigned[task]
                if ok:
                    tree.levels[lv][j] = p; strikes.append((m.addr, kind))
                else:
                    self.events["forged proofs rejected"] += 1
            tree.open_tasks(assigned)            # promote odd nodes
            if len(txs) == 0: break

        stamp = tree.root()
        minted_bytes = HEADER_BYTES + STAMP_BYTES + TX_BYTES_COMPACT * len(txs)
        return dict(txs=txs, stamp=stamp, ticks=tick, blows=blows_won, hashes=hashes, strikes=strikes,
                    quiet=quiet, minted_bytes=minted_bytes,
                    density=len(txs) / (minted_bytes / 1000),
                    density_raw=len(txs) / ((HEADER_BYTES + TX_BYTES_RAW * len(txs)) / 1000))

    # hand-over check (what every miner and node runs) -------------------
    def handover_ok(self, mb):
        st_ = mb["stamp"]
        if st_ is None: return False, "no stamp"
        if st_.pre != self.state.root(): return False, "stamp starts from wrong state"
        if st_.n_tx != len(mb["txs"]): return False, "stamp does not cover the block"
        if st_.fees != sum(t.fee for t in mb["txs"]): return False, "fee total mismatch"
        if len(mb["txs"]) < N_MIN and not mb["quiet"]: return False, "density below target"
        # final state must equal the stamp's post root
        s = self.state.copy()
        for t in mb["txs"]: s.apply(t)
        if s.root() != st_.post: return False, "post state mismatch"
        return True, "ok"

    # mining ------------------------------------------------------------
    def header(self, mb):
        txroot = H(*[t.body() for t in mb["txs"]]) if mb["txs"] else H(b"")
        return H(self.prev, mb["stamp"].digest(), txroot, struct.pack(">I", self.height + 1))

    def seal(self, mb):
        hdr = self.header(mb); tick = 0; nonces = {m.addr: 0 for m in self.miners}
        while True:
            tick += 1
            for m in self.miners:
                for _ in range(m.hashes_per_tick):
                    n = nonces[m.addr]; nonces[m.addr] += 1
                    if below(H(hdr, m.addr, struct.pack(">Q", n)), self.seal_p):
                        return m, n, tick, hdr

    def verify_seal(self, hdr, miner_addr, nonce):
        return below(H(hdr, miner_addr, struct.pack(">Q", nonce)), self.seal_p)

    # one full block ----------------------------------------------------
    def step(self):
        n_users_sending = RNG.randint(150, 650)       # some blocks busy, some quiet
        mb = self.mint(self.make_mempool(n_users_sending))
        ok, why = self.handover_ok(mb)
        assert ok, why
        miner, nonce, seal_ticks, hdr = self.seal(mb)

        # tamper test: a miner changes one transaction after minting -> header no longer matches
        if mb["txs"]:
            t0 = mb["txs"][0]; orig = t0.amount; t0.amount += 1
            tampered_ok = self.verify_seal(self.header(mb), miner.addr, nonce) and self.handover_ok(mb)[0]
            t0.amount = orig
            assert not tampered_ok
        assert self.verify_seal(hdr, miner.addr, nonce)

        # apply block, pay everyone
        for t in mb["txs"]: self.state.apply(t)
        fees = sum(t.fee for t in mb["txs"])
        pot = int(fees * MINTER_SHARE)
        weight = len(mb["strikes"])
        paid = 0
        for i, (a, kind) in enumerate(mb["strikes"]):
            share = pot // weight if i < weight - 1 else pot - paid
            self.state.credit(a, share); self.earned[a] += share; paid += share
        self.height += 1
        reward = int(raw_reward(self.height) * PICO)
        self.state.credit(miner.addr, reward + fees - pot)
        self.mined[miner.addr] += reward + fees - pot
        self.minted_reward_total += reward
        self.prev = H(hdr, miner.addr, struct.pack(">Q", nonce))

        # difficulty: keep minting near TARGET_MINT_TICKS
        f = min(max(mb["ticks"] / TARGET_MINT_TICKS, 0.5), 2.0)
        self.blow_p *= f
        self.log.append(dict(h=self.height, tx=len(mb["txs"]), quiet=mb["quiet"], leaves=math.ceil(len(mb["txs"]) / LEAF_SIZE),
                             strikes=len(mb["strikes"]), blows=mb["blows"], ticks=mb["ticks"], seal=seal_ticks,
                             dens=mb["density"], dens_raw=mb["density_raw"], fees=fees, reward=reward,
                             miner=miner.addr.hex()[:6]))

    def supply(self):
        return sum(self.state.bal.values())


# ----------------------------------------------------------------------------- run & report
def main():
    t0 = time.time()
    net = Network()
    print(f"Proof of Minting simulation: 1000 users, 1000 minters (950 phones, 50 servers, 5 cheaters), 20 miners\n")
    print(f"{'blk':>3} {'txs':>4} {'leaves':>6} {'strikes':>7} {'blows':>5} {'mint t':>6} {'seal t':>6} "
          f"{'density':>15} {'fees YEN':>9} {'reward':>8} miner")
    for _ in range(BLOCKS):
        net.step()
        r = net.log[-1]
        print(f"{r['h']:>3} {r['tx']:>4} {r['leaves']:>6} {r['strikes']:>7} {r['blows']:>5} {r['ticks']:>6} {r['seal']:>6} "
              f"{r['dens']:>6.1f} vs {r['dens_raw']:>4.1f}{' q' if r['quiet'] else '  '} {r['fees'] / PICO:>9.3f} "
              f"{r['reward'] / PICO:>8.2f} {r['miner']}")

    print("\n== Checks ==")
    expected = net.genesis_supply + net.minted_reward_total
    print(f"  coins conserved (supply = genesis + block rewards): {net.supply() == expected}")
    print("  every minted block passed the hand-over check, every seal verified,")
    print("  and a transaction changed after minting was rejected in every block")
    for k, v in net.events.items():
        print(f"  {k}: {v}")

    print("\n== Fairness: minters' fee income vs their share of blow hashing ==")
    tot_e = sum(net.earned.values()); tot_w = sum(net.minter_work_hashes.values())
    for kind in ("phone", "server"):
        ms = [m for m in net.minters if m.kind == kind]
        e = sum(net.earned[m.addr] for m in ms) / tot_e
        w = sum(net.minter_work_hashes[m.addr] for m in ms) / tot_w
        paid = sum(1 for m in ms if net.earned[m.addr] > 0)
        print(f"  {kind + 's':8s}: {w * 100:5.1f}% of blow hashes -> {e * 100:5.1f}% of minter fees; "
              f"{paid}/{len(ms)} got paid at least once in {BLOCKS} blocks")
    cheaters = [m for m in net.minters if m.cheater]
    print(f"  5 cheaters forge every leaf they prove: all forged leaves rejected, so their "
          f"{sum(net.earned[m.addr] for m in cheaters) / PICO:.3f} YEN came only from honest merge strikes")

    print("\n== Miners: block reward + 25% of fees vs hashrate ==")
    tot_m = sum(net.mined.values()); tot_hr = sum(m.hashes_per_tick for m in net.miners)
    for m in sorted(net.miners, key=lambda m: -m.hashes_per_tick)[:5]:
        print(f"  miner {m.addr.hex()[:6]}: {m.hashes_per_tick / tot_hr * 100:5.1f}% hashrate -> "
              f"{net.mined[m.addr] / tot_m * 100:5.1f}% of mining income")

    ticks = [r["ticks"] for r in net.log]
    print(f"\n== Pace ==\n  minting ticks per block: first 5 avg {st.mean(ticks[:5]):.0f}, last 10 avg {st.mean(ticks[-10:]):.0f} "
          f"(target {TARGET_MINT_TICKS})")
    print(f"  density: minted blocks carry {st.mean(r['dens'] for r in net.log):.1f} tx/KB vs "
          f"{st.mean(r['dens_raw'] for r in net.log):.1f} tx/KB for the same txs with signatures")
    print(f"\nran in {time.time() - t0:.0f} s")


if __name__ == "__main__":
    main()
