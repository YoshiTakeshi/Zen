"""
zen_minting.py - prototype of collaborative Block Minting for Golden Yen / Silver Ken / Bronze Jen.

Pure Python 3, standard library only.  Run:  python3 zen_minting.py

What is implemented
-------------------
1. Anti-prime generator (same algorithm as the Zen page) and fast "decentralize" /
   "centralize" of an integer into anti-prime terms.
2. The (increment-size, increment, multiplicator) bit encoding described on the page.
3. A toy transaction / block model.
4. Collaborative minting:
     - every minter works on the SAME current block
     - a "blow" = deterministic shuffle of the block's transactions, seeded by
       H(block_state || minter_address || nonce)  -> the minter's unique "hammer"
     - if the shuffled block encodes smaller than the current best by at least
       MIN_GAIN bytes, the blow is "lucky": the space made is recorded in the
       block's mint log (minter address, nonce, bytes saved) and refilled with
       mempool transactions (highest fee first)
     - the network keeps the densest candidate and everyone continues from it
     - stops when the block reaches the target density
5. Verifier: replays every blow from the mint proof, checks sizes, limits,
   fee rules and computes the fee split between minters and the miner.

Notes on the design choices (see the bottom of the file / the chat for details)
- Shuffling the list of anti-prime terms does not change their sum, so it cannot
  change the encoding.  What changes the number is the ORDER OF TRANSACTIONS
  in the block, so that is what a blow shuffles.
- Because the shuffle seed contains the minter's address, a lucky blow cannot
  be stolen: replaying it with another address gives a different shuffle.
  So the mint-log entry needs no signature, only (address, nonce).
"""

import hashlib
import math
import random
import struct
import zlib
from dataclasses import dataclass, field

H = lambda b: hashlib.sha256(b).digest()

# ---------------------------------------------------------------------------
# 1. Anti-primes
# ---------------------------------------------------------------------------
# The Zen generator multiplies the previous anti-prime by ONE prime each step,
# so A(k+1)/A(k) is always a prime.  We store those ratios; A(k) = product.
# 1, 2, 6, 12, 60, 120, 360, 2520, 5040, 55440, 720720, ...

_ratios = []
_primes = [2]
_exps = [0]


def _extend_ratios(count):
    while len(_ratios) < count:
        min_x, min_j = float("inf"), 0
        for j in range(len(_primes)):
            if j == 0 or _exps[j - 1] > _exps[j]:
                x = math.log(_primes[j]) / math.log(1.0 / (_exps[j] + 1.0) + 1.0)
                if x < min_x:
                    min_x, min_j = x, j
        _exps[min_j] += 1
        if min_j + 1 == len(_primes):
            _exps.append(0)
            n = _primes[-1] + 1
            while any(n % p == 0 for p in _primes if p * p <= n):
                n += 1
            _primes.append(n)
        _ratios.append(_primes[min_j])


def ratio(i):
    """A(i+2)/A(i+1) using 0-based i; the multiplicator of term index i+1 is < ratio(i)."""
    if i >= len(_ratios):
        _extend_ratios(i + 64)
    return _ratios[i]


def antiprimes(n):
    out, a = [1], 1
    for i in range(n - 1):
        a *= ratio(i)
        out.append(a)
    return out


def decentralize(N):
    """Integer -> multiplicators d[i] of A(i+1), with 0 <= d[i] < ratio(i).
    Same result as the greedy subtraction on the page, but done by chunked divmod
    so it runs on block-sized integers."""
    digits, i = [], 0
    while N:
        j, P = i, 1
        while P < (1 << 60):
            P *= ratio(j)
            j += 1
        N, rem = divmod(N, P)
        for k in range(i, j):
            rem, d = divmod(rem, ratio(k))
            digits.append(d)
        i = j
    while digits and digits[-1] == 0:
        digits.pop()
    return digits


def centralize(digits):
    N = 0
    i = len(digits)
    while i > 0:
        j, P, small = i, 1, 0
        while j > 0 and P < (1 << 60):
            j -= 1
            small = small * ratio(j) + digits[j]
            P *= ratio(j)
        N = N * P + small
        i = j
    return N


def as_term_list(digits):
    """The page's representation: list of anti-prime indices (1-based), largest first."""
    out = []
    for i in range(len(digits) - 1, -1, -1):
        out += [i + 1] * digits[i]
    return out


# ---------------------------------------------------------------------------
# 2. Anti-prime bit encoding (size(5 bits), increment, multiplicator)
# ---------------------------------------------------------------------------

def _mult_bits(r):
    choices = r - 1                      # multiplicator is 1 .. r-1
    return (choices - 1).bit_length() if choices > 1 else 0


def antiprime_encode(data: bytes) -> bytes:
    digits = decentralize(int.from_bytes(b"\x01" + data, "big"))  # 0x01 guard keeps leading zeros
    fields = []
    prev = 0
    entries = 0
    for i, d in enumerate(digits):
        if d == 0:
            continue
        idx = i + 1
        inc = idx - prev
        size = inc.bit_length()
        assert size < 32
        fields.append(format(size, "05b"))
        fields.append(format(inc, "0%db" % size))
        mb = _mult_bits(ratio(i))
        if mb:
            fields.append(format(d - 1, "0%db" % mb))
        prev = idx
        entries += 1
    bits = format(entries, "032b") + "".join(fields)
    bits += "0" * (-len(bits) % 8)
    return int(bits, 2).to_bytes(len(bits) // 8, "big")


def antiprime_decode(blob: bytes) -> bytes:
    bits = format(int.from_bytes(blob, "big"), "0%db" % (len(blob) * 8))
    pos = 0

    def take(n):
        nonlocal pos
        v = int(bits[pos:pos + n], 2) if n else 0
        pos += n
        return v

    entries = take(32)
    digits = []
    idx = 0
    for _ in range(entries):
        size = take(5)
        idx += take(size)
        i = idx - 1
        mb = _mult_bits(ratio(i))
        d = take(mb) + 1 if mb else 1
        digits += [0] * (i + 1 - len(digits))
        digits[i] = d
    N = centralize(digits)
    raw = N.to_bytes((N.bit_length() + 7) // 8, "big")
    assert raw[0] == 1
    return raw[1:]


# ---------------------------------------------------------------------------
# 3. Transactions and blocks
# ---------------------------------------------------------------------------

PICO = 10 ** 12
FEE_MIN, FEE_MAX = 0.0001, 0.025          # Golden Yen limits from the page


@dataclass(frozen=True)
class Tx:
    sender: bytes      # 20 bytes
    receiver: bytes    # 20 bytes
    amount: int        # picograms
    fee: int           # picograms
    sig: bytes         # 64 bytes (random stand-in for a real signature)

    def serialize(self):
        return self.sender + self.receiver + struct.pack(">QQ", self.amount, self.fee) + self.sig

    @property
    def txid(self):
        return H(self.serialize())[:8]

    @property
    def fee_rate(self):
        return self.fee / (self.amount + self.fee)


@dataclass(frozen=True)
class MintEntry:
    minter: bytes      # 20-byte address
    nonce: int
    saved: int         # bytes of space this blow made

    def serialize(self):
        return self.minter + struct.pack(">QI", self.nonce, self.saved)   # 32 bytes


@dataclass
class Block:
    prev_hash: bytes
    txs: list
    mint_log: list = field(default_factory=list)

    def serialize(self):
        return (b"\x01" + self.prev_hash
                + struct.pack(">II", len(self.txs), len(self.mint_log))
                + b"".join(m.serialize() for m in self.mint_log)
                + b"".join(t.serialize() for t in self.txs))

    def state_hash(self):
        return H(self.serialize())

    def copy(self):
        return Block(self.prev_hash, list(self.txs), list(self.mint_log))


# Encoders: "the size the network sees".  Both are deterministic and lossless.
ENCODERS = {
    "antiprime": lambda b: len(antiprime_encode(b)),
    "zlib": lambda b: len(zlib.compress(b, 9)),
}


def make_mempool(n, seed=7):
    rng = random.Random(seed)
    senders = [H(b"s%d" % i)[:20] for i in range(300)]
    merchants = [H(b"m%d" % i)[:20] for i in range(12)]      # popular receivers -> redundancy
    pool = []
    for _ in range(n):
        amount = rng.choice([1, 2, 5, 10, 12, 60, 120]) * rng.choice([PICO // 6, PICO // 2, PICO])
        rate = math.exp(rng.uniform(math.log(FEE_MIN * 1.01), math.log(FEE_MAX * 0.99)))
        fee = int(amount * rate / (1 - rate))
        recv = rng.choice(merchants) if rng.random() < 0.7 else rng.choice(senders)
        pool.append(Tx(rng.choice(senders), recv, amount, fee, rng.randbytes(64)))
    pool.sort(key=lambda t: t.fee_rate, reverse=True)       # miners/minters take best fees first
    return pool


# ---------------------------------------------------------------------------
# 4. Minting
# ---------------------------------------------------------------------------

MIN_GAIN = 32      # a blow must at least pay for its own mint-log entry (32 bytes)


def hash_shuffle(n, seed):
    order = list(range(n))
    for c, i in enumerate(range(n - 1, 0, -1)):
        j = int.from_bytes(H(seed + c.to_bytes(4, "big"))[:8], "big") % (i + 1)
        order[i], order[j] = order[j], order[i]
    return order


def blow(block, minter, nonce, enc):
    """One mint attempt with this minter's hammer. Returns (candidate block, encoded size)."""
    seed = H(block.state_hash() + minter + nonce.to_bytes(8, "big"))
    order = hash_shuffle(len(block.txs), seed)
    cand = Block(block.prev_hash, [block.txs[i] for i in order], list(block.mint_log))
    return cand, enc(cand.serialize())


def fill(block, mempool, enc, limit):
    """Append the largest prefix of the mempool that keeps the block within the limit."""
    lo, hi = 0, len(mempool)
    while lo < hi:                                   # binary search on prefix length
        mid = (lo + hi + 1) // 2
        trial = block.copy()
        trial.txs += mempool[:mid]
        if enc(trial.serialize()) <= limit:
            lo = mid
        else:
            hi = mid - 1
    added = mempool[:lo]
    block.txs += added
    del mempool[:lo]
    return added


def density(block, enc):
    raw = sum(len(t.serialize()) for t in block.txs)
    return raw / enc(block.serialize())


@dataclass
class MintStep:
    minter: bytes
    nonce: int
    size_before: int
    size_after: int
    added: list


def mint_block(mempool, minters, enc_name, limit, target_density, blows_per_round, max_rounds,
               prev_hash=b"\x00" * 32, log=print):
    enc = ENCODERS[enc_name]
    block = Block(prev_hash, [])
    fill(block, mempool, enc, limit)
    initial = block.copy()
    size = enc(block.serialize())
    steps, nonces = [], {m: 0 for m in minters}
    log(f"  initial block: {len(block.txs)} txs, encoded {size} B, density {density(block, enc):.3f}")

    for rnd in range(max_rounds):
        best = None
        for m in minters:                       # in reality these run in parallel
            for _ in range(blows_per_round):
                n = nonces[m]
                nonces[m] += 1
                cand, s = blow(block, m, n, enc)
                if size - s >= MIN_GAIN and (best is None or s < best[0]):
                    best = (s, m, n, cand)
        if best is None:
            continue
        s, m, n, cand = best                    # network keeps the densest block
        cand.mint_log.append(MintEntry(m, n, size - s))
        added = fill(cand, mempool, enc, limit)
        steps.append(MintStep(m, n, size, s, added))
        block, size = cand, enc(cand.serialize())
        d = density(block, enc)
        log(f"  round {rnd:3d}: lucky blow by {m.hex()[:8]} nonce {n}: "
            f"saved {steps[-1].size_before - s} B, +{len(added)} txs, density {d:.3f}")
        if d >= target_density:
            log("  target density reached -> block handed to miners")
            break
    return initial, steps, block


# ---------------------------------------------------------------------------
# 5. Verification and fee split
# ---------------------------------------------------------------------------

MINTER_SHARE = 0.5     # fraction of block fees paid to minters, by bytes saved


def verify(initial, steps, final, enc_name, limit, target_density):
    enc = ENCODERS[enc_name]
    for t in final.txs:
        assert FEE_MIN <= t.fee_rate <= FEE_MAX, "fee out of range"
    block, size = initial.copy(), enc(initial.serialize())
    assert size <= limit
    for st in steps:
        cand, s = blow(block, st.minter, st.nonce, enc)
        assert s == st.size_after and size - s >= MIN_GAIN, "blow does not reproduce"
        cand.mint_log.append(MintEntry(st.minter, st.nonce, size - s))
        cand.txs += st.added
        block, size = cand, enc(cand.serialize())
        assert size <= limit, "block over size limit"
    assert block.serialize() == final.serialize(), "final block mismatch"
    assert density(final, enc) >= target_density, "density target not met"

    fees = sum(t.fee for t in final.txs)
    total_saved = sum(e.saved for e in final.mint_log)
    payout = {}
    for e in final.mint_log:
        payout[e.minter] = payout.get(e.minter, 0) + fees * MINTER_SHARE * e.saved / total_saved
    return fees, payout


def retarget_density(target, actual_seconds, expected_seconds, damping=4):
    """Network rule: if blocks come too fast, ask for more density; too slow, less."""
    factor = (expected_seconds / actual_seconds) ** (1 / damping)
    return target * min(max(factor, 0.8), 1.25)


# ---------------------------------------------------------------------------
# Demo
# ---------------------------------------------------------------------------

def main():
    print("== 1. Anti-primes ==")
    print("  first 12:", antiprimes(12))

    print("\n== 2. 'Hello World!' decentralized (same list as the Zen page) ==")
    N = int.from_bytes(b"Hello World!", "big")
    terms = as_term_list(decentralize(N))
    print("  terms:", len(terms), " first ones:", terms[:12], "...")
    assert centralize(decentralize(N)) == N
    blob = antiprime_encode(b"Hello World!")
    assert antiprime_decode(blob) == b"Hello World!"
    print(f"  12 raw bytes -> {len(blob)} encoded bytes")

    print("\n== 3. How the anti-prime encoding sizes up ==")
    rng = random.Random(1)
    sample_tx = b"".join(t.serialize() for t in make_mempool(30, seed=3))
    for name, data in [("random 2 KB", rng.randbytes(2048)), ("30 transactions", sample_tx)]:
        e = antiprime_encode(data)
        assert antiprime_decode(e) == data
        print(f"  {name:16s} raw {len(data):5d} B | antiprime {len(e):5d} B | zlib {len(zlib.compress(data, 9)):5d} B")

    minters = [H(b"minter%d" % i)[:20] for i in range(8)]

    for enc_name, limit, target, blows, rounds in [("antiprime", 6000, 0.50, 3, 40),
                                                   ("zlib", 16000, 1.40, 25, 120)]:
        print(f"\n== 4. Collaborative minting, encoder = {enc_name}, size limit {limit} B ==")
        pool = make_mempool(3000)
        initial, steps, final = mint_block(pool, minters, enc_name, limit, target, blows, rounds)
        enc = ENCODERS[enc_name]
        reached = density(final, enc) >= target
        print(f"  final: {len(final.txs)} txs, {len(steps)} lucky blows, density {density(final, enc):.3f}"
              f" (target {target}, {'reached' if reached else 'NOT reached'})")
        if reached:
            fees, payout = verify(initial, steps, final, enc_name, limit, target)
            print(f"  verified by replay. block fees {fees / PICO:.4f} YEN; minter payouts:")
            for m, p in sorted(payout.items(), key=lambda kv: -kv[1]):
                print(f"    {m.hex()[:8]}  {p / PICO:.4f} YEN")
        else:
            verify(initial, steps, final, enc_name, limit, 0)
            print("  replay verified (density target not reached)")

        # Comparison: what a plain canonical ordering gets for free
        canon = final.copy()
        canon.txs.sort(key=lambda t: (t.receiver, t.amount))
        print(f"  for comparison, same txs simply sorted by receiver: density {density(canon, enc):.3f}")


if __name__ == "__main__":
    main()
