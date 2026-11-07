// Three chains (Jen, Ken, Yen), each with its own Sen/Ten/Ren peg, plus an
// exchange between them, and a three-way brake.
//
// Units: every chain's W is in its own grams per unit; "1 JEN in Sen" = W x g / P
// where g is the market value of one chain-gram and P the value of the physical
// coin. Everything starts at the peg (all logs 0).
//
// Peg per chain (the Jen-0.12 design from pegdef2.js): middle-20% average,
// each payment counted once; floor at a quarter of the long-run typical;
// clip centres from long-run averages; speed by min(recent, long-run) Sen share;
// anchor moving at most 0.005% a block, band +-10%.
//
// Exchange: one market price per pair (log), fundamental + a deviation that
// arbitrageurs pull back with a half-life of 6 blocks. Holding the price away
// by x costs the attacker k x D x^2 per block (k = ln2/6, D = trade volume in
// $ that moves the price by a factor e).
//
// Three-way brake: for each pair the implied unit ratio
//   r_AB = logW_A + log p_AB - logW_B   (1 unit of A in units of B)
// is compared with its slow average (half-life ~3.5 days). If both pairs of one
// chain deviate by more than TAU while the other pair stays within TAU/2, that
// chain is the odd one out: its W and anchor stop moving until it is back.
//
// One step = 150 s (a Jen block); all three pegs use the same per-step rules
// here (a simplification: Ken and Yen have longer blocks).
'use strict';
function rngf(seed) { let s = seed >>> 0; return () => { s = (s + 0x6D2B79F5) >>> 0; let t = s; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; }; }
const DAY = 576, STEP = 0.01, ALPHA = 0.1, LONG = 1 - Math.pow(0.5, 1 / 2000);
const ANCHOR = 0.00005, BAND = Math.log(1.1), SHARE_FULL = 0.30, SHARE_MIN = 0.02;
const TAU = Math.log(1.05), BASE = 1 - Math.pow(0.5, 1 / 2000), KREV = Math.log(2) / 6;
const CH = ['J', 'K', 'Y'];
const PAY = { J: 100, K: 50, Y: 15 };            // honest payments per step
const PAIRS = [['K', 'J'], ['Y', 'K'], ['Y', 'J']];

function trimmed(L, q = 0.4) { // count-weighted middle of the values
  if (!L.length) return null;
  L.sort((a, b) => a - b); const n = L.length, lo = q * n, hi = (1 - q) * n; let s = 0, w = 0;
  for (let i = 0; i < n; i++) { const a = Math.max(i, lo), b = Math.min(i + 1, hi); if (b > a) { s += (b - a) * L[i]; w += b - a; } }
  return w > 0 ? s / w : L[n >> 1];
}

function run(o, seed = 1) {
  const R = rngf(seed);
  const gauss = () => Math.sqrt(-2 * Math.log(R() + 1e-12)) * Math.cos(2 * Math.PI * R());
  const steps = o.steps || 8000;
  // per chain state
  const S = {};
  for (const c of CH) S[c] = { w: 0, A: 0, nG: 0, dG: 0, nD: 0, dD: 0, lG: Math.log(2.6), lD: Math.log(2.6), sS: 0.3, sL: 0.3, frozen: false, frozenSteps: 0 };
  // true values: log P_c (physical coin, $) and log g_c ($ per chain-gram): start equal so the peg is W = 1
  const P = { J: 0, K: 0, Y: 0 }, g = { J: 0, K: 0, Y: 0 };
  const m = {}, base = {};
  for (const [a, b] of PAIRS) { m[a + b] = 0; base[a + b] = 0; }
  let marketCost = 0, fakeCount = 0;
  const out = { maxMove: { J: 0, K: 0, Y: 0 }, frozenFrac: { J: 0, K: 0, Y: 0 }, series: [], track: null, falseFreeze: 0 };
  for (let t = 0; t < steps; t++) {
    // genuine changes of the copper (Sen) value
    if (o.change === 'sudden' && t === 2000) P.J += Math.log(1.2);
    if (o.change === 'slow' && t >= 2000 && t < 2000 + 30 * DAY) P.J += Math.log(1.2) / (30 * DAY);
    const attacking = o.att && t >= 2000 && t < 2000 + 7 * DAY;
    // ---- each chain's peg
    for (const c of CH) {
      const s = S[c], LG = [], LD = [];
      const U = P[c] - g[c];                       // log of the true W (grams per coin)
      for (let i = 0; i < PAY[c]; i++) {
        const v = Math.log(2) + gauss();            // goods worth v coins (log)
        if (R() < 0.3) { const k = Math.exp(v) < 1 ? Math.max(1, Math.round(Math.exp(v) * 6)) / 6 : Math.round(Math.exp(v)); LD.push(Math.log(k)); }
        else LG.push(v + U + 0.005 * gauss());
      }
      if (attacking && o.att.chains.includes(c)) {
        const na = Math.round(PAY[c] * o.att.share / (1 - o.att.share));
        for (let i = 0; i < na; i++) { LD.push(s.lD + 0.7 * (o.att.dir === 'down' ? 1 : -1)); fakeCount++; }
      }
      const fl = (L, cen) => L.filter(x => x >= cen - Math.log(4));
      const LGf = fl(LG, s.lG), LDf = fl(LD, s.lD);
      const sh = LD.length / (LD.length + LG.length);
      s.sS += ALPHA * (sh - s.sS); s.sL += LONG * (sh - s.sL);
      const mG = trimmed(LGf), mD = trimmed(LDf);
      if (mG !== null) { s.nG = (1 - ALPHA) * s.nG + ALPHA * mG; s.dG = (1 - ALPHA) * s.dG + ALPHA; }
      if (mD !== null) { s.nD = (1 - ALPHA) * s.nD + ALPHA * mD; s.dD = (1 - ALPHA) * s.dD + ALPHA; }
      if (s.dG > 0 && s.dD > 0) {
        const gm = s.nG / s.dG, dm = s.nD / s.dD;
        s.lG += LONG * (gm - s.lG); s.lD += LONG * (dm - s.lD);
        if (!(o.brake && s.frozen)) {
          const share = Math.min(s.sS, s.sL);
          const step = share < SHARE_MIN ? 0 : STEP * Math.min(1, share / SHARE_FULL);
          s.w += Math.max(-step, Math.min(step, (gm - dm) - s.w));
          s.w = Math.max(s.A - BAND, Math.min(s.A + BAND, s.w));
          s.A += Math.max(-ANCHOR, Math.min(ANCHOR, s.w - s.A));
        }
      }
    }
    // ---- exchange: arbitrage pulls deviations back; the attacker may hold them
    for (const [a, b] of PAIRS) {
      const key = a + b;
      m[key] = m[key] * (1 - KREV) + 0.002 * gauss();
      if (attacking && o.att.market) {
        // keep the implied ratios of the attacked chain where they were
        const target = impliedTarget(a, b);
        if (target !== null) { marketCost += KREV * o.depth * target * target; m[key] = target; }
      }
    }
    function impliedTarget(a, b) {
      const hit = o.att.chains;
      if (hit.includes(a) === hit.includes(b)) return null;          // both or neither attacked
      // deviation the attacked W causes in r_ab, cancelled by moving the market the other way
      const dw = (S[a].w - (P[a] - g[a])) - (S[b].w - (P[b] - g[b]));
      return -dw;
    }
    // ---- brake: implied unit ratios against their slow average
    const dev = {};
    for (const [a, b] of PAIRS) {
      const key = a + b;
      const r = S[a].w + (g[a] - g[b] + m[key]) - S[b].w;        // log (1 unit a in units b), market price included
      if (t === 0) base[key] = r;
      base[key] += BASE * (r - base[key]);
      dev[key] = Math.abs(r - base[key]);
    }
    const d = (x, y) => dev[x + y] ?? dev[y + x];
    for (const c of CH) {
      const others = CH.filter(x => x !== c);
      const odd = d(c, others[0]) > TAU && d(c, others[1]) > TAU && d(others[0], others[1]) < TAU / 2;
      S[c].frozen = odd;
      if (odd) { S[c].frozenSteps++; if (!attacking && !o.change) out.falseFreeze++; }
    }
    // ---- measure 1 unit in coins = W x g / P
    for (const c of CH) {
      const ratio = S[c].w + g[c] - P[c];
      if (attacking || (o.change && t >= 2000)) out.maxMove[c] = Math.max(out.maxMove[c], Math.abs(ratio));
    }
    if (o.change && t >= 2000 && out.track === null && Math.abs(S.J.w + g.J - P.J) < Math.log(1.05)) out.track = t - 2000;
    if (t % 20 === 0) out.series.push(CH.map(c => +Math.exp(S[c].w + g[c] - P[c]).toFixed(4)));
  }
  for (const c of CH) out.frozenFrac[c] = S[c].frozenSteps / steps;
  out.marketCostPerDay = marketCost / (7 * DAY) * DAY;
  out.fakesPerStep = fakeCount / (7 * DAY);
  return out;
}

module.exports = { run };
if (require.main === module) {
  const pct = x => (100 * (Math.exp(x) - 1)).toFixed(0) + '%';
  const lines = [];
  const show = (label, o) => {
    const rs = [1, 2, 3].map(sd => run(o, sd));
    const avg = f => rs.reduce((a, r) => a + f(r), 0) / rs.length;
    const mv = c => avg(r => r.maxMove[c]);
    lines.push(`${label.padEnd(58)} JEN ${pct(mv('J')).padStart(5)}  KEN ${pct(mv('K')).padStart(5)}  YEN ${pct(mv('Y')).padStart(5)}` +
      `   frozen J/K/Y ${['J', 'K', 'Y'].map(c => (100 * avg(r => r.frozenFrac[c])).toFixed(0) + '%').join('/')}` +
      (o.att && o.att.market ? `   market cost $${(avg(r => r.marketCostPerDay) / 1e6).toFixed(2)}M/day` : '') +
      (o.change ? `   JEN within 5% after ${(avg(r => r.track ?? 99999) / DAY).toFixed(1)} days` : ''));
  };
  lines.push('Largest move of 1 unit in its coin (7-day attack, or after a genuine change), 3 seeds');
  lines.push('\nNo attack');
  show('  no brake', { brake: false });
  show('  brake', { brake: true });
  for (const share of [0.10, 0.25]) {
    lines.push(`\nAttack on Jen payments only (fakes = ${share * 100}% of Jen payments)`);
    show('  no brake', { brake: false, att: { chains: ['J'], share, dir: 'down' } });
    show('  brake', { brake: true, att: { chains: ['J'], share, dir: 'down' } });
  }
  for (const depth of [5e6, 1e8]) {
    lines.push(`\nAttack on Jen payments AND the exchange, holding the ratios steady (market depth $${depth / 1e6}M per factor e, i.e. ~$${(depth / 1e8).toFixed(2)}M moves a price 1%)`);
    show('  brake', { brake: true, depth, att: { chains: ['J'], share: 0.25, dir: 'down', market: true } });
  }
  lines.push('\nAttack on two pegs at once (Jen and Ken payments, 25% fakes each)');
  show('  no brake', { brake: false, att: { chains: ['J', 'K'], share: 0.25, dir: 'down' } });
  show('  brake', { brake: true, att: { chains: ['J', 'K'], share: 0.25, dir: 'down' } });
  lines.push('\nGenuine change: the Sen worth 1.2x (copper up against silver and gold)');
  show('  sudden, no brake', { brake: false, change: 'sudden', steps: 12000 });
  show('  sudden, brake', { brake: true, change: 'sudden', steps: 12000 });
  show('  over 30 days, no brake', { brake: false, change: 'slow', steps: 2000 + 40 * DAY });
  show('  over 30 days, brake', { brake: true, change: 'slow', steps: 2000 + 40 * DAY });
  require('fs').writeFileSync(__dirname + '/results/tri.txt', lines.join('\n') + '\n');
  console.log(lines.join('\n'));
}
