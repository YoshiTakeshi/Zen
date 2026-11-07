// Peg defences, round 2: robust block statistic + anchor + speed by share.
// Same model as pegdef.js (one block = 150 s on Jen, 576 a day; 100 honest
// payments a block; goods lognormal, median 2 Sen; JEN-mode prices in whole Sen
// or sixths below 1). The attacker adds a share of all payments, on either
// side of the ratio (JEN-mode counts or gram amounts), at the value that
// pushes hardest for each estimator (it tries 6 strategies; the worst counts).
'use strict';
function rngf(seed) { let s = seed >>> 0; return () => { s = (s + 0x6D2B79F5) >>> 0; let t = s; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; }; }

const BLOCKS = 8000, DAY = 576, N = 100, STEP = 0.01, CLIP = 1.5, ALPHA = 0.1;
const LONG = 1 - Math.pow(0.5, 1 / 2000);
const SHARE_FULL = 0.30, SHARE_MIN = 0.02;

// estimators of one block's typical log value
function clippedMean(L, c) { let w = 0, s = 0; for (const [l, x] of L) { w += x; s += x * Math.max(c - CLIP, Math.min(c + CLIP, l)); } return s / w; }
function trimmedMean(L) { // drop 25% of the weight at each end, average the middle half
  L.sort((a, b) => a[0] - b[0]);
  let t = 0; for (const x of L) t += x[1];
  const lo = 0.25 * t, hi = 0.75 * t; let acc = 0, s = 0, w = 0;
  for (const [l, x] of L) {
    const a = Math.max(acc, lo), b = Math.min(acc + x, hi);
    if (b > a) { s += (b - a) * l; w += b - a; }
    acc += x;
  }
  return w > 0 ? s / w : L[L.length >> 1][0];
}

function run(o, seed = 1) {
  const R = rngf(seed);
  const gauss = () => Math.sqrt(-2 * Math.log(R() + 1e-12)) * Math.cos(2 * Math.PI * R());
  const has = (k) => o.def.includes(k);
  const trim = has('trim'), anchor = has('anchor') || has('slowanchor'), shareOn = has('share');
  const anchorStep = has('slowanchor') ? 0.00002 : 0.0001, band = Math.log(1.1);
  let U = 1, logW = 0, A = 0;
  let nG = 0, dG = 0, nD = 0, dD = 0, bwG = 0, bwD = 0;
  let cG = Math.log(2.6), cD = Math.log(2.6), lG = cG, lD = cD;
  let sShort = o.share, sLong = o.share;
  const out = { maxDev: 0, track: null, series: [] };
  let attackSen = 0;
  for (let b = 0; b < BLOCKS; b++) {
    if (o.change && b === 2000) U *= 1.5;
    const attacking = o.att > 0 && b >= 2000 && b < 6000;
    const LG = [], LD = [];
    for (let i = 0; i < N; i++) {
      const v = 2 * Math.exp(gauss());
      if (R() < o.share) { const k = v < 1 ? Math.max(1, Math.round(v * 6)) / 6 : Math.round(v); LD.push([Math.log(k), trim ? 1 : k]); }
      else { const g = v * U * (1 + 0.005 * gauss()); LG.push([Math.log(g), trim ? 1 : g]); }
    }
    if (attacking) {
      const na = Math.round(N * o.att / (1 - o.att));
      // strategy: side (D or G) and offset from the long-run centre, sign set by the direction
      const sgn = (o.dir === 'down') === (o.side === 'D') ? 1 : -1; // down: D up or G down
      for (let i = 0; i < na; i++) {
        const c = o.side === 'D' ? lD : lG;
        const l = o.off === 'x' ? c + sgn * 8 : c + sgn * o.off;
        const val = Math.exp(l);
        (o.side === 'D' ? LD : LG).push([l, trim ? 1 : val]);
        attackSen += o.side === 'D' ? val : val / U;
      }
    }
    const nJ = LD.length, nT = LD.length + LG.length;
    const sh = nJ / nT; sShort += ALPHA * (sh - sShort); sLong += LONG * (sh - sLong);
    const blockMean = (L, c) => trim ? trimmedMean(L) : clippedMean(L, c);
    if (LG.length) { const m = blockMean(LG, cG); const bw = trim ? LG.length : LG.reduce((a, x) => a + x[1], 0); bwG = bwG ? bwG + ALPHA * (bw - bwG) : bw; const w = Math.min(bw, bwG); nG = (1 - ALPHA) * nG + ALPHA * w * m; dG = (1 - ALPHA) * dG + ALPHA * w; }
    if (LD.length) { const m = blockMean(LD, cD); const bw = trim ? LD.length : LD.reduce((a, x) => a + x[1], 0); bwD = bwD ? bwD + ALPHA * (bw - bwD) : bw; const w = Math.min(bw, bwD); nD = (1 - ALPHA) * nD + ALPHA * w * m; dD = (1 - ALPHA) * dD + ALPHA * w; }
    if (dG > 0 && dD > 0) {
      const fin = (x) => Math.max(-30, Math.min(30, x));
      const mG = fin(nG / dG), mD = fin(nD / dD);
      cG = mG; cD = mD; lG += LONG * (mG - lG); lD += LONG * (mD - lD);
      const s = shareOn ? Math.min(sShort, sLong) : sShort;
      let step = s < SHARE_MIN ? 0 : shareOn ? STEP * Math.min(1, s / SHARE_FULL) : STEP;
      logW += Math.max(-step, Math.min(step, (mG - mD) - logW));
      logW = Math.max(-10, Math.min(10, logW));
      if (anchor) { logW = Math.max(A - band, Math.min(A + band, logW)); A += Math.max(-anchorStep, Math.min(anchorStep, logW - A)); }
    }
    const ratio = Math.exp(logW) / U;
    if (attacking) out.maxDev = Math.max(out.maxDev, Math.abs(Math.log(ratio)));
    if (o.change && b >= 2000 && out.track === null && Math.abs(Math.log(ratio)) < Math.log(1.05)) out.track = b - 2000;
    if (b % 20 === 0) out.series.push(+ratio.toFixed(4));
  }
  out.costSenPerDay = Math.min(1e12, attackSen / 4000 * DAY * 0.01 * 0.5);
  out.honestSenPerDay = N * 2 * Math.exp(0.5) * DAY;
  return out;
}

const DEFS = {
  'Jen-0.11 (clipped mean)': [],
  'anchor only': ['anchor'],
  'trimmed mean': ['trim'],
  'trimmed + share': ['trim', 'share'],
  'trimmed + anchor': ['trim', 'anchor'],
  'trimmed+share+anchor': ['trim', 'share', 'anchor'],
  'trimmed+share+slow anchor': ['trim', 'share', 'slowanchor'],
};
const STRATS = [];
for (const side of ['D', 'G']) for (const off of [0.7, 1.5, 'x']) STRATS.push({ side, off });

module.exports = { run, DEFS };
if (require.main === module) {
  const shares = [0.05, 0.10, 0.30], atts = [0.02, 0.05, 0.10, 0.20];
  const res = { attack: [], change: [], series: {} };
  for (const [name, def] of Object.entries(DEFS)) {
    for (const sh of [0.05, 0.10, 0.30, 0.50]) {
      const ch = run({ def, share: sh, att: 0, change: true });
      res.change.push({ defence: name, share: sh, blocks_to_5pct: ch.track });
    }
    for (const sh of shares) for (const a of atts) for (const dir of ['down', 'up']) {
      let worst = null;
      for (const st of STRATS) { const r = run({ def, share: sh, att: a, dir, ...st }); if (!worst || r.maxDev > worst.maxDev) worst = { ...r, ...st }; }
      res.attack.push({ defence: name, share: sh, attacker: a, dir, side: worst.side, off: worst.off,
        max_move_pct: +Math.min(99999, 100 * (Math.exp(worst.maxDev) - 1)).toFixed(1),
        cost_pct_daily: +(100 * worst.costSenPerDay / worst.honestSenPerDay).toFixed(2) });
      if (sh === 0.30 && dir === 'down' && a === 0.10) res.series[name] = worst.series;
    }
  }
  require('fs').writeFileSync(__dirname + '/results/pegdef2.json', JSON.stringify(res));
  const lines = [];
  for (const sh of shares) {
    lines.push(`\nHonest Sen share ${sh * 100}%: largest move of 1 JEN in Sen during a 7-day attack (worst direction and strategy)`);
    lines.push('defence'.padEnd(28) + atts.map(a => (`att ${a * 100}%`).padStart(10)).join(''));
    for (const name of Object.keys(DEFS)) {
      const row = atts.map(a => Math.max(...res.attack.filter(r => r.defence === name && r.share === sh && r.attacker === a).map(r => r.max_move_pct)));
      lines.push(name.padEnd(28) + row.map(x => (x >= 99999 ? 'runaway' : x.toFixed(0) + '%').padStart(10)).join(''));
    }
  }
  lines.push('\nGenuine change (Sen worth 1.5x, no attack): blocks until 1 JEN is within 5% of 1 Sen (576 a day)');
  lines.push('defence'.padEnd(28) + [5, 10, 30, 50].map(s => (`share ${s}%`).padStart(11)).join(''));
  for (const name of Object.keys(DEFS)) lines.push(name.padEnd(28) + [0.05, 0.10, 0.30, 0.50].map(s => String(res.change.find(x => x.defence === name && x.share === s).blocks_to_5pct ?? '>6000').padStart(11)).join(''));
  require('fs').writeFileSync(__dirname + '/results/pegdef2.txt', lines.join('\n') + '\n');
  console.log(lines.join('\n'));
}
