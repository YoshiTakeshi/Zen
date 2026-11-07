// Denomination payments and the ratio rule for W.
//
// Hourly market, 24 blocks an hour (150 s), individual payments in every block.
//  - Goods have a value v in SEN (lognormal around kMed).
//  - Denomination payers (share f): the shop prices in SEN (k = v rounded to
//    whole SEN, or to 1/6 below 1), the wallet pays k JEN split into the
//    denominations 2520 ... 1/6, each piece a whole multiple of W. The network
//    recognises these and reads the SEN count k.
//  - Market payers: pay the market value v x basket in base units (v x basket / P).
//    `basket` > 1 means they buy bigger things than denomination payers.
//  - Market for Jen as in model.js: others hold value (1-f) E e^mood, the
//    denomination payers hold f E JEN; P (SEN per base unit) clears supply Q.
//  - 1 JEN in SEN: J = W x P.
// W rules (Fibonacci window of 231 blocks, Bronze average, 1% step a block):
//  service  : typical size of all payments (the protocol now)
//  exclude  : typical size of market payments only (exact-JEN payments ignored)
//  ratio    : typical market payment (base units) / typical SEN count,
//             when denomination payments are at least `minShare` of payments
//             in the window; otherwise like `exclude`.
// Attacker (optional, from `attackMonth`): adds fake denomination payments of
// count 1 (pushing the typical count down, so W up), `attack` x the honest
// number of payments, paying a 1% fee on them.

const A3 = 0.58015443606796071376;
const EV3 = Math.exp(Math.pow(Math.log((3 + Math.sqrt(13)) / 2), 2) / 2);
const Z3 = -0.5164;
const GROUPS3 = (() => { const g = []; let a = 1, b = 2, start = 0; for (let i = 0; i < 10; i++) { g.push({ start, end: start + a, w: 1 << (9 - i) }); start += a; [a, b] = [b, a + b]; } return g; })();

function rng3(seed) {
  let t = seed >>> 0;
  const u = () => { t += 0x6D2B79F5; let r = Math.imul(t ^ (t >>> 15), 1 | t); r ^= r + Math.imul(r ^ (r >>> 7), 61 | r); return ((r ^ (r >>> 14)) >>> 0) / 4294967296; };
  return { u, n: () => Math.sqrt(-2 * Math.log(u() + 1e-12)) * Math.cos(2 * Math.PI * u()) };
}

const DEFAULTS3 = {
  months: 24,
  schedule: [[0, 0], [3, 0.01], [6, 0.05], [9, 0.10], [12, 0.20], [15, 0.35], [18, 0.50], [21, 0.75]],
  rule: "ratio",
  kMed: 12, kSig: 1.0,
  basket: 1.0,
  perBlock: 24,       // payments per block in the simulation (sampled)
  minShare: 0.02,
  vol: 1.0, meanRevDays: 60, E0: 2e5, growth: 3,
  attack: 0, attackMonth: 15,
  seed: 5,
};

function simulate3(p0 = {}) {
  const p = { ...DEFAULTS3, ...p0 };
  const R = rng3(p.seed);
  const hours = Math.round(p.months * 730), BPH = 24, nb = hours * BPH + 1;
  // per-block sums for the window: market sizes, denomination counts, all sizes
  const S = {};
  for (const k of ["mM", "mS", "mN", "dM", "dS", "dN", "aM", "aS"]) S[k] = new Float64Array(nb + 1);
  let blk = 0, N = 1, Q = 2520 * EV3, W = 2520, mood = 0, E = p.E0;
  const fAt = (h) => { let f = 0; for (const [m, v] of p.schedule) if (h >= m * 730) f = v; return f; };
  const dt = 1 / 8760, theta = 365 / p.meanRevDays;
  const out = [];
  let fakeFees = 0;
  const priceSen = (v) => v < 1 ? Math.max(1 / 6, Math.round(v * 6) / 6) : Math.round(v);
  const stat = (xs) => { let s = 0, s2 = 0; for (const x of xs) { s += x; s2 += x * x; } const m = s / xs.length; return [m, Math.sqrt(Math.max(0, s2 / xs.length - m * m))]; };
  function win(prefix) { // Fibonacci-weighted mean of per-block means and SDs
    let sw = 0, sm = 0, ss = 0, sn = 0;
    for (const g of GROUPS3) {
      const hi = blk - g.start, lo = Math.max(0, blk - g.end);
      if (hi <= 0) break;
      if (hi > lo) {
        const n = S[prefix + "N"] ? S[prefix + "N"][hi] - S[prefix + "N"][lo] : hi - lo;
        sw += g.w * (hi - lo); sm += g.w * (S[prefix + "M"][hi] - S[prefix + "M"][lo]); ss += g.w * (S[prefix + "S"][hi] - S[prefix + "S"][lo]); sn += n;
      }
    }
    if (!sw) return null;
    const avg = sm / sw, sd = ss / sw;
    return { b: Math.max(avg + Z3 * sd, avg / 10), n: sn };
  }
  for (let h = 0; h < hours; h++) {
    const f = fAt(h);
    E = p.E0 * Math.pow(p.growth, h / 8760);
    mood += -theta * mood * dt + p.vol * Math.sqrt(dt) * R.n();
    const believersBU = Math.min(f * E * W, 0.9 * Q);
    const P = (1 - f) * E * Math.exp(mood) / (Q - believersBU) + (f >= 1 ? 1 / W : 0);
    const J = W * P;
    const attacking = p.attack > 0 && h >= p.attackMonth * 730;
    for (let i = 0; i < BPH; i++) {
      N++; Q += 2520 * Math.pow(N, -A3) * EV3;
      const mk = [], dn = [], all = [];
      for (let j = 0; j < p.perBlock; j++) {
        const v = p.kMed * Math.exp(p.kSig * R.n());
        if (R.u() < f) { const k = priceSen(v); dn.push(k); all.push(k * W); }
        else { const x = v * p.basket / P; mk.push(x); all.push(x); }
      }
      if (attacking) { const nf = Math.round(p.attack * p.perBlock); for (let j = 0; j < nf; j++) { dn.push(1); all.push(W); fakeFees += 0.01; } }
      const put = (pre, xs) => { const [m, sd] = xs.length ? stat(xs) : [0, 0]; S[pre + "M"][blk + 1] = S[pre + "M"][blk] + (xs.length ? m : 0); S[pre + "S"][blk + 1] = S[pre + "S"][blk] + (xs.length ? sd : 0); if (S[pre + "N"]) S[pre + "N"][blk + 1] = S[pre + "N"][blk] + xs.length; };
      // blocks with no payments of a kind contribute nothing to that kind's average:
      // store the block's mean only when present, and count presence for the weights
      put("m", mk); put("d", dn); put("a", all);
      blk++;
      let target;
      if (p.rule === "service") { const a = winAll("a"); target = a; }
      else {
        const m = winKind("m"), d = winKind("d");
        if (p.rule === "ratio" && d && m && d.n >= p.minShare * (d.n + m.n)) target = m.b / d.b;
        else target = m ? m.b : W;
      }
      if (target > 0) W = Math.min(W * 1.01, Math.max(W * 0.99, target));
    }
    if (h % 24 === 23) out.push({ day: (h + 1) / 24, f, J, W, P });
  }
  return { series: out, fakeFees };

  function winAll(pre) { const r = win(pre); return r ? r.b : 0; }
  function winKind(pre) { // only blocks that had payments of this kind
    let sw = 0, sm = 0, ss = 0, sn = 0;
    for (const g of GROUPS3) {
      const hi = blk - g.start, lo = Math.max(0, blk - g.end);
      if (hi <= 0) break;
      if (hi > lo) {
        const present = countPresent(pre, lo, hi);
        sw += g.w * present; sm += g.w * (S[pre + "M"][hi] - S[pre + "M"][lo]); ss += g.w * (S[pre + "S"][hi] - S[pre + "S"][lo]); sn += S[pre + "N"][hi] - S[pre + "N"][lo];
      }
    }
    if (!sw || !sn) return null;
    const avg = sm / sw, sd = ss / sw;
    return { b: Math.max(avg + Z3 * sd, avg / 10), n: sn };
  }
  function countPresent(pre, lo, hi) { let c = 0; for (let i = lo + 1; i <= hi; i++) if (S[pre + "N"][i] > S[pre + "N"][i - 1]) c++; return c; }
}

if (typeof module !== "undefined") module.exports = { simulate3, DEFAULTS3 };
