// Measure S by VOLUME, each gram counted at most once per rest period.
//   - An account's payment counts toward S only up to its rested balance (money held unmoved for
//     R days) not yet used; money that arrives is fresh and must rest R days before it counts again.
//   - The day reading is VALUE-weighted: the middle 20% of the day's counted value, sorted by log
//     price (Sen side) or log value (ordinary side), after the floor (1/4 of the typical).
//   - Day window (Fibonacci over days) + day clip +-10% + anchor (2.9%/day, band +-10%), as before.
//   - Option 'recv': receiver cap (each receiver at most 0.03% of the day's counted Sen value) and
//     the bond ($1,000 base, held 7 days) that grows 20%/day on receiver disagreement.
// Jen at 1M payments a day: 300,000 Sen-priced, about $2.47M of Sen-priced value a day.
// Honest money that is rested when spent: 85% (R = 1 day), 75% (3 days), 60% (7 days) (assumed).
// Attacker: holds C dollars of rested money, cycles it: counted on a day, rests R days at the
// receiver, counts again -> C / (R + 1) counted a day. All of it at an offset from the typical
// price, the direction that pushes hardest.
'use strict';
function rngf(seed) { let s = seed >>> 0; return () => { s = (s + 0x6D2B79F5) >>> 0; let t = s; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; }; }
const SEN_VALUE_DAY = 300000 * 5 * Math.exp(0.5), N_D = 12000, N_G = 12000, T0 = 40, HORIZON = 60;
const LONGD = 1 - Math.pow(0.5, 1 / 3.5), ANCHOR_DAY = 0.00005 * 576, BAND = Math.log(1.1), CLIP = Math.log(1.1);
const FIB = [1, 2, 3, 5, 8, 13, 21, 34, 55]; const WEIGHTS = []; FIB.forEach((n, k) => { for (let i = 0; i < n; i++) WEIGHTS.push(Math.pow(0.5, k)); });
const RESTED = { 1: 0.85, 3: 0.75, 7: 0.60 };
const HONEST_VOTERS = 730, CAPF = 0.0003, B0 = 1000;
// weighted middle 20% of [logv, weight] pairs
function wmid(L) {
  if (!L.length) return null; L.sort((a, b) => a[0] - b[0]);
  let T = 0; for (const x of L) T += x[1];
  const lo = 0.4 * T, hi = 0.6 * T; let acc = 0, s = 0, w = 0;
  for (const [v, wt] of L) { const a = Math.max(acc, lo), b = Math.min(acc + wt, hi); if (b > a) { s += (b - a) * v; w += b - a; } acc += wt; if (acc >= hi) break; }
  return w ? s / w : L[L.length >> 1][0];
}
function mid(L) { L.sort((a, b) => a - b); const n = L.length, lo = 0.4 * n, hi = 0.6 * n; let s = 0, w = 0; for (let i = 0; i < n; i++) { const a = Math.max(i, lo), b = Math.min(i + 1, hi); if (b > a) { s += (b - a) * L[i]; w += b - a; } } return s / w; }

function run(o, seed = 31) {
  const R = rngf(seed); const gauss = () => Math.sqrt(-2 * Math.log(R() + 1e-12)) * Math.cos(2 * Math.PI * R());
  const fr = RESTED[o.rest];
  let U = 0, mult = 1, base = null; const multHist = [];
  const hG = [], hD = []; let lG = Math.log(2), lD = Math.log(2), logS = 0, A = 0, cGp = null, cDp = null;
  const out = { maxDev: 0, follow: null, maxMult: 1, cutDays: 0 };
  for (let d = 0; d < T0 + HORIZON; d++) {
    if (o.copper && d === T0) U += Math.log(1.5);
    multHist.push(mult); if (multHist.length > 7) multHist.shift();
    const need = o.recv ? Math.max(...multHist) : 1;
    // honest payments in the sample: value in Sen exp(lp); counted share = rested share
    const D = [], G = [];
    let honestCounted = 0;
    for (let i = 0; i < N_D; i++) { const v = 2 * Math.exp(gauss()); const p = v < 1 ? Math.max(1, Math.round(v * 6)) / 6 : Math.round(v); if (R() < fr) { D.push([Math.log(p), p]); honestCounted += p; } }
    for (let i = 0; i < N_G; i++) { const v = 2 * Math.exp(gauss()); if (R() < fr) G.push([Math.log(v) + U, v]); }
    // the receiver bond also removes honest shops when it grows (shops below the bond stop counting)
    if (o.recv && need > 1) { const keep = Math.pow(need, -0.6); for (let i = D.length - 1; i >= 0; i--) if (R() > keep) { honestCounted -= D[i][1]; D.splice(i, 1); } }
    // attacker: counted value a day = C / (R + 1), scaled to the sample
    let att = 0;
    if (o.C && d >= T0 && d < T0 + o.dur) {
      let usd = o.C / (o.rest + 1);
      let K = 0;
      if (o.recv) {
        const capUsd = CAPF * SEN_VALUE_DAY * fr;          // each receiver at most 0.03% of the day's counted value
        K = Math.ceil(usd / capUsd);
        if (o.m * 1 < need) { usd = 0; out.cutDays++; }      // his bonds (m x base, placed ahead) no longer qualify
      }
      att = usd / (SEN_VALUE_DAY * fr) * honestCounted;      // same share of counted value as in the real chain
      if (att > 0) D.push([lD + o.sgn * o.off, att]);
      o._K = K;
    }
    const fl = (L, c) => L.filter(x => x[0] >= c - Math.log(4));
    const gRaw = wmid(fl(G, lG)), dRaw = wmid(fl(D, lD));
    let g = gRaw, dm = dRaw;
    if (cGp !== null) { g = Math.max(cGp - CLIP, Math.min(cGp + CLIP, g)); dm = Math.max(cDp - CLIP, Math.min(cDp + CLIP, dm)); }
    hG.unshift(g); hD.unshift(dm); if (hG.length > WEIGHTS.length) { hG.pop(); hD.pop(); }
    lG += LONGD * (g - lG); lD += LONGD * (dm - lD);
    let sw = 0, sg = 0, sd = 0; for (let i = 0; i < hG.length; i++) { sw += WEIGHTS[i]; sg += WEIGHTS[i] * hG[i]; sd += WEIGHTS[i] * hD[i]; }
    cGp = sg / sw; cDp = sd / sw;
    const target = cGp - cDp;
    if (d < 20) { logS = target; A = target; base = dRaw; continue; }
    logS = Math.max(A - BAND, Math.min(A + BAND, target)); A += Math.max(-ANCHOR_DAY, Math.min(ANCHOR_DAY, logS - A));
    if (o.recv) {
      // receiver disagreement: payment-weighted change vs the median receiver's own change
      const honestMid = wmid(fl(D.filter(x => x[1] !== att || att === 0), lD));
      const votes = []; for (let i = 0; i < HONEST_VOTERS; i++) votes.push((honestMid - base) + 0.13 * gauss());
      for (let i = 0; i < (att > 0 ? o._K : 0); i++) votes.push(o.sgn * o.off);
      const press = Math.abs((dRaw - base) - mid(votes)) > Math.log(1.03);
      mult = press ? Math.min(20, mult * 1.2) : Math.max(1, mult * 0.95);
      out.maxMult = Math.max(out.maxMult, mult);
      base += LONGD * (honestMid - base);
    }
    if (d >= T0) { const dev = logS - U; out.maxDev = Math.max(out.maxDev, Math.abs(dev)); if (o.copper && out.follow === null && Math.abs(dev) < Math.log(1.05)) out.follow = d - T0; }
  }
  return out;
}
module.exports = { run };

if (require.main === module) {
  const pct = x => (100 * (Math.exp(x) - 1)).toFixed(0) + '%';
  const usd = x => '$' + (x >= 1e6 ? (x / 1e6).toFixed(1) + 'M' : Math.round(x / 1e3) + 'k');
  const caps = [50e3, 100e3, 250e3, 500e3, 1e6, 2.5e6];
  const strategies = [{ sgn: 1, off: 0.3 }, { sgn: 1, off: 1 }, { sgn: -1, off: 0.3 }, { sgn: -1, off: 1 }];
  const CONFIGS = [['count once, rest 1 day', { rest: 1 }], ['count once, rest 3 days', { rest: 3 }], ['count once, rest 7 days', { rest: 7 }],
    ['+ receiver cap + bond on disagreement, rest 1 day', { rest: 1, recv: true, m: 2 }], ['+ receiver cap + bond on disagreement, rest 3 days', { rest: 3, recv: true, m: 2 }]];
  const L = ['Volume-weighted reading, each gram counted once per rest period. Jen at 1M payments a day ($2.47M Sen-priced value a day).',
    'Cell: largest move of S over 7 days / 30 days, for the attacker\'s rested money (the receiver variants also lock bonds, see the note).'];
  for (const [name, cfg] of CONFIGS) {
    const q = run({ ...cfg, C: 0, dur: 0, sgn: 1, off: 0 });
    L.push(`\n${name}  (no attack: S wanders ${pct(q.maxDev)})`);
    L.push('attacker money'.padEnd(16) + caps.map(c => usd(c).padStart(12)).join(''));
    const row7 = [], row30 = [], kRow = [];
    for (const C of caps) {
      let a = 0, b = 0, K = 0;
      for (const st of strategies) { const o1 = { ...cfg, C, dur: 7, ...st }; a = Math.max(a, run(o1).maxDev); K = o1._K || K; b = Math.max(b, run({ ...cfg, C, dur: 30, ...st }).maxDev); }
      row7.push(pct(a)); row30.push(pct(b)); kRow.push(K);
    }
    L.push('7 days'.padEnd(16) + row7.map(x => x.padStart(12)).join(''));
    L.push('30 days'.padEnd(16) + row30.map(x => x.padStart(12)).join(''));
    if (cfg.recv) L.push('accounts needed'.padEnd(16) + kRow.map(k => String(k).padStart(12)).join('') + '   (each with a bond: $2,000 placed ahead)');
  }
  L.push('\nGenuine change, a Sen worth 1.5x:');
  for (const [name, cfg] of CONFIGS) { const r = run({ ...cfg, C: 0, dur: 0, sgn: 1, off: 0, copper: true }); L.push(`  ${name.padEnd(52)} S within 5% after ${r.follow ?? '>60'} days, bond up to x${r.maxMult.toFixed(1)}`); }
  require('fs').writeFileSync(__dirname + '/results/volsim.txt', L.join('\n') + '\n');
  console.log(L.join('\n'));
}
