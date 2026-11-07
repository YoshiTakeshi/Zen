// Jen market model: does 1 JEN = 1 SEN hold as more people agree?
//
// Time: 1 h market steps, 24 Jen blocks per hour (150 s blocks).
// Units: value in SEN (the physical copper coin, 2 g, value S = 1);
//        Jen amounts in base units (bu).
//
// Pieces
//  - Supply Q: real Jen emission, 2520 x N^-a per block x E[V] (a = 0.58015).
//  - Coin weight W (bu per JEN): the protocol rule. Each block records the
//    mean and SD of payment sizes; Fibonacci-weighted window of 231 blocks;
//    Bronze average = mean - 0.5164 SD (floor mean/10); W moves at most
//    `step` per block toward it. Variants: follow (1%/block, the protocol),
//    slow (1%/day), freeze (follows until `freezeMonth`, then fixed).
//  - Payments: purchase values v ~ lognormal (median kMed SEN, sigma kSig).
//    Believers price in SEN and pay v JEN = v*W bu ("1 JEN = 1 SEN").
//    Everyone else pays the market value: v/P bu (P = SEN per bu).
//  - Market for Jen, cleared every hour:
//      others hold value Dn = (1-f) E e^s (E = economy, s = speculative mood,
//      a mean-reverting random walk with annual volatility `vol`);
//      believers defend the peg: they buy Jen when 1 JEN < 1 SEN and sell when
//      1 JEN > 1 SEN, with the cash they brought (cash x their share of E) and
//      the Jen they hold. When their cash or Jen runs out, the market price wins.
//  - 1 JEN in SEN: J = W x P.

const A = 0.58015443606796071376;
const EV = Math.exp(Math.pow(Math.log((3 + Math.sqrt(13)) / 2), 2) / 2); // E[r^Z] = 2.04
const Z = -0.5164;
const GROUPS = (() => { const g = []; let a = 1, b = 2, start = 0; for (let i = 0; i < 10; i++) { g.push({ start, end: start + a, w: 1 << (9 - i) }); start += a; [a, b] = [b, a + b]; } return g; })();
const WIN = 231, BPH = 24;

function rng(seed) { // mulberry32 + Box-Muller
  let t = seed >>> 0;
  const u = () => { t += 0x6D2B79F5; let r = Math.imul(t ^ (t >>> 15), 1 | t); r ^= r + Math.imul(r ^ (r >>> 7), 61 | r); return ((r ^ (r >>> 14)) >>> 0) / 4294967296; };
  return () => Math.sqrt(-2 * Math.log(u() + 1e-12)) * Math.cos(2 * Math.PI * u());
}

const DEFAULTS = {
  months: 24,
  schedule: [[0, 0], [3, 0.01], [6, 0.05], [9, 0.10], [12, 0.20], [15, 0.35], [18, 0.50], [21, 0.75]], // [month, share agreeing]
  rule: "follow",      // follow | slow | freeze
  freezeMonth: 3,
  kMed: 12,            // median purchase, in SEN (12 = a dozen minutes of labour)
  kSig: 1.0,           // spread of purchase sizes (lognormal sigma)
  vol: 1.0,            // speculative mood, annual volatility
  meanRevDays: 60,
  E0: 2e5,             // value people want to hold in Jen at start, SEN
  growth: 3,           // economy x growth per year
  cash: 1.0,           // believers' spare cash, x their share of E
  seed: 7,
};

function simulate(p0 = {}) {
  const p = { ...DEFAULTS, ...p0 };
  const hours = Math.round(p.months * 730);
  const gauss = rng(p.seed);
  const muV = p.kMed * Math.exp(p.kSig * p.kSig / 2), m2V = p.kMed * p.kMed * Math.exp(2 * p.kSig * p.kSig);
  const nb = hours * BPH + 1;
  const cumM = new Float64Array(nb + 1), cumS = new Float64Array(nb + 1);
  let blk = 0, N = 0, Q = 0, W = 2520, s = 0, E = p.E0, X = 0, R = 0, fPrev = 0;
  const stepBlock = p.rule === "slow" ? Math.pow(1.01, 1 / 576) - 1 : 0.01; // 576 blocks a day
  const dt = 1 / 8760, theta = 1 / (p.meanRevDays / 365);
  const fAt = (h) => { let f = 0; for (const [m, v] of p.schedule) if (h >= m * 730) f = v; return f; };
  const out = [];
  let pegHours = 0, firstPeg = -1, lostPeg = -1;
  for (let h = 0; h < hours; h++) {
    const f = fAt(h);
    const E1 = p.E0 * Math.pow(p.growth, h / 8760);
    R += Math.max(0, f - fPrev) * E1 * p.cash + f * (E1 - E) * p.cash; // new believers bring cash
    E = E1; fPrev = f;
    s += -theta * s * dt + p.vol * Math.sqrt(dt) * gauss();
    // supply grows through the hour's blocks; clear on the supply at the hour's start
    if (Q <= 0) { for (let i = 0; i < BPH; i++) { N++; Q += 2520 * Math.pow(N, -A) * EV; } }
    const Dn = (1 - f) * E * Math.exp(s);
    let P, Pstar = 1 / W, peg = false;
    if (f <= 0) { P = Dn / Math.max(Q - X, 1e-9); }
    else {
      const need = Q - Dn / Pstar - X; // bu believers must buy (+) or sell (-) to hold 1 JEN = 1 SEN
      if (need >= 0) {
        const cost = need * Pstar;
        if (cost <= R) { R -= cost; X += need; P = Pstar; peg = true; }
        else { P = (Dn + R) / (Q - X); X += R / P; R = 0; }
      } else if (-need <= X) { X += need; R += -need * Pstar; P = Pstar; peg = true; }
      else { R += X * Dn / Q; X = 0; P = Dn / Q; }
    }
    const J = W * P;
    // believers pay in JEN only while they hold some (else they use physical Sen)
    const want = 0.05 * f * E;
    const phi = f <= 0 ? 0 : f * Math.min(1, (X / W) / Math.max(want, 1e-9));
    // blocks of this hour
    for (let i = 0; i < BPH; i++) {
      if (h > 0 || i > 0) { N++; Q += 2520 * Math.pow(N, -A) * EV; }
      const a = W, b = 1 / P; // bu per SEN of purchase: believers, others
      const mean = muV * (phi * a + (1 - phi) * b);
      const m2 = m2V * (phi * a * a + (1 - phi) * b * b);
      const sd = Math.sqrt(Math.max(0, m2 - mean * mean));
      cumM[blk + 1] = cumM[blk] + mean; cumS[blk + 1] = cumS[blk] + sd; blk++;
      if (p.rule === "freeze" && h >= p.freezeMonth * 730) continue;
      let sw = 0, sm = 0, ss = 0;
      for (const g of GROUPS) {
        const hi = blk - g.start, lo = Math.max(0, blk - g.end);
        if (hi <= 0) break;
        if (hi > lo) { sw += g.w * (hi - lo); sm += g.w * (cumM[hi] - cumM[lo]); ss += g.w * (cumS[hi] - cumS[lo]); }
      }
      const avg = sm / sw, sdv = ss / sw;
      const target = Math.max(avg + Z * sdv, avg / 10);
      W = Math.min(W * (1 + stepBlock), Math.max(W * (1 - stepBlock), target));
    }
    if (peg) { pegHours++; if (firstPeg < 0) firstPeg = h; lostPeg = -1; } else if (firstPeg >= 0 && lostPeg < 0) lostPeg = h;
    if (h % 24 === 23) out.push({ day: (h + 1) / 24, f, J, W, P, Q, mood: Math.exp(s), cash: R / Math.max(f * E, 1e-9), heldShare: X / Q, phi, peg });
  }
  return { series: out, pegHours, hours };
}

if (typeof module !== "undefined") module.exports = { simulate, DEFAULTS };
