// Peg defences against fake JEN-mode / gram-mode payments (Zen, Jen).
// Block-level model: every payment is simulated; the peg estimator follows
// Jen-0.11 with an exponential window (alpha 0.1, close to the Fibonacci
// window's recent weight) and four defences that can be switched on:
//   cap    capped value weighting: a payment weighs min(value, 4 x the typical value)
//   anchor a slow anchor (moves at most 0.01% a block) and a band of +-10% around
//          it; the clip centres come from long-run averages, not the last window
//   share  speed by Sen share: the step limit scales with min(recent, long-run)
//          JEN-mode share, full at 30%, none under 2%
// One block = 150 s (Jen); 576 blocks a day. Values in Sen; U = grams per Sen.
'use strict';

function rngf(seed) {
  let s = seed >>> 0;
  return () => { s = (s + 0x6D2B79F5) >>> 0; let t = s; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
}

const BLOCKS = 8000, DAY = 576, N = 100;
const STEP = 0.01, CLIP = 1.5, ALPHA = 0.1;
const LONG = 1 - Math.pow(0.5, 1 / 2000);      // long-run averages: half-life 2000 blocks (~3.5 days)
const ANCHOR_STEP = 0.0001, BAND = Math.log(1.1), CAPX = 4;
const SHARE_FULL = 0.30, SHARE_MIN = 0.02;

function run(o, seed = 1) {
  const R = rngf(seed);
  const gauss = () => Math.sqrt(-2 * Math.log(R() + 1e-12)) * Math.cos(2 * Math.PI * R());
  const cap = o.def.includes('cap'), anchor = o.def.includes('anchor'), shareOn = o.def.includes('share');
  let U = 1;                      // grams per Sen (true value)
  let logW = Math.log(o.w0 || 1); // grams per JEN, starts at the peg unless set
  // estimator state: window EMAs of (weight x mean) and weight, per side
  let nG = 0, dG = 0, nD = 0, dD = 0, bwG = 0, bwD = 0;
  let cG = Math.log(U * 2.6), cD = Math.log(2.6);          // clip centres (start at honest typical values)
  let lG = cG, lD = cD;                                     // long-run centres
  let A = logW;                                             // anchor
  let sShort = o.share, sLong = o.share;
  let first = true;
  const out = { maxDev: 0, devEnd: 0, track: null, series: [] };
  let attackSen = 0;
  for (let b = 0; b < BLOCKS; b++) {
    if (o.change && b === 2000) U *= 1.5;
    const attacking = o.att > 0 && b >= 2000 && b < 6000;
    // ---- payments
    let sGw = 0, sGl = 0, sDw = 0, sDl = 0, nJ = 0, nT = 0;
    const centreG = anchor ? lG : cG, centreD = anchor ? lD : cD;
    const add = (mode, val, lg) => {
      // val: weight basis (grams for G, JEN count for D); lg: log of it
      const c = mode === 'G' ? centreG : centreD;
      const l = Math.max(c - CLIP, Math.min(c + CLIP, lg));
      let w = val;
      if (cap) w = Math.min(val, CAPX * Math.exp(c));
      if (mode === 'G') { sGw += w; sGl += w * l; } else { sDw += w; sDl += w * l; nJ++; }
      nT++;
    };
    for (let i = 0; i < N; i++) {
      const v = 2 * Math.exp(gauss());                       // goods worth v Sen
      if (R() < o.share) {
        const k = v < 1 ? Math.max(1, Math.round(v * 6)) / 6 : Math.round(v); // priced in Sen, paid in JEN
        add('D', k, Math.log(k));
      } else {
        const g = v * U * (1 + 0.005 * gauss());
        add('G', g, Math.log(g));
      }
    }
    if (attacking) {
      const na = Math.round(N * o.att / (1 - o.att));
      for (let i = 0; i < na; i++) {
        let mode, val;
        if (o.dir === 'down') {
          // more JEN for the same goods: large JEN-mode counts
          mode = 'D'; val = o.strat === 'huge' ? 2520 : Math.exp(centreD + CLIP) * 1.001;
        } else if (o.strat === 'tiny') {
          mode = 'D'; val = 1 / 6;                             // fewer JEN: tiny JEN-mode counts
        } else {
          mode = 'G'; val = o.strat === 'huge' ? 2520 * U : Math.exp(centreG + CLIP) * 1.001; // larger gram amounts
        }
        add(mode, val, Math.log(val));
        attackSen += mode === 'D' ? val : val / U;
      }
    }
    // ---- shares
    const sh = nT ? nJ / nT : 0;
    sShort += ALPHA * (sh - sShort); sLong += LONG * (sh - sLong);
    // ---- window (block weight capped at the running typical block weight)
    if (sGw > 0) { const m = sGl / sGw; bwG = bwG ? bwG + ALPHA * (sGw - bwG) : sGw; const w = Math.min(sGw, bwG); nG = (1 - ALPHA) * nG + ALPHA * w * m; dG = (1 - ALPHA) * dG + ALPHA * w; }
    if (sDw > 0) { const m = sDl / sDw; bwD = bwD ? bwD + ALPHA * (sDw - bwD) : sDw; const w = Math.min(sDw, bwD); nD = (1 - ALPHA) * nD + ALPHA * w * m; dD = (1 - ALPHA) * dD + ALPHA * w; }
    if (dG > 0 && dD > 0) {
      const mG = nG / dG, mD = nD / dD;
      cG = mG; cD = mD;
      lG += LONG * (mG - lG); lD += LONG * (mD - lD);
      // ---- step
      const s = shareOn ? Math.min(sShort, sLong) : sShort;
      let step = STEP;
      if (s < SHARE_MIN) step = 0;
      else if (shareOn) step = STEP * Math.min(1, s / SHARE_FULL);
      const target = mG - mD;
      logW += Math.max(-step, Math.min(step, target - logW));
      if (anchor) {
        logW = Math.max(A - BAND, Math.min(A + BAND, logW));
        A += Math.max(-ANCHOR_STEP, Math.min(ANCHOR_STEP, logW - A));
      }
    }
    // ---- measure: 1 JEN in Sen = W / U
    const ratio = Math.exp(logW) / U;
    if (attacking) out.maxDev = Math.max(out.maxDev, Math.abs(Math.log(ratio)));
    if (b === 5999) out.devEnd = Math.log(ratio);
    if (o.change && b >= 2000 && out.track === null && Math.abs(Math.log(ratio)) < Math.log(1.05)) out.track = b - 2000;
    if (b % 20 === 0) out.series.push(+ratio.toFixed(4));
    first = false;
  }
  out.costSenPerDay = attackSen / 4000 * DAY * 0.01 * 0.5; // 1% fee on fake value, half not earned back
  out.honestSenPerDay = N * 2 * Math.exp(0.5) * DAY;
  out.final = Math.exp(logW) / U;
  return out;
}

const DEFS = {
  'Jen-0.11': [],
  'capped value': ['cap'],
  'anchor + band': ['anchor'],
  'speed by share': ['share'],
  'all three': ['cap', 'anchor', 'share'],
};
module.exports = { run, DEFS, BLOCKS, DAY };

if (require.main === module) {
  const shares = [0.02, 0.05, 0.10, 0.30, 0.50];
  const atts = [0.02, 0.05, 0.10, 0.20, 0.40];
  const res = { attack: [], change: [], series: {} };
  const pct = x => (100 * (Math.exp(x) - 1)).toFixed(0);
  for (const [name, def] of Object.entries(DEFS)) {
    for (const sh of shares) {
      // a genuine change of the Sen's value (x1.5), no attack
      const ch = run({ def, share: sh, att: 0, change: true });
      res.change.push({ defence: name, share: sh, blocks_to_5pct: ch.track, final: +ch.final.toFixed(3) });
      for (const a of atts) {
        for (const dir of ['down', 'up']) {
          let worst = null;
          for (const strat of dir === 'down' ? ['edge', 'huge'] : ['tiny', 'edge', 'huge']) {
            const r = run({ def, share: sh, att: a, dir, strat });
            if (!worst || r.maxDev > worst.maxDev) worst = { ...r, strat };
          }
          res.attack.push({ defence: name, share: sh, attacker: a, dir, strat: worst.strat,
            max_dev_pct: +(100 * (Math.exp(worst.maxDev) - 1)).toFixed(1),
            jen_in_sen_worst: +(dir === 'down' ? Math.exp(-worst.maxDev) : Math.exp(worst.maxDev)).toFixed(3),
            cost_pct_of_daily_volume: +(100 * worst.costSenPerDay / worst.honestSenPerDay).toFixed(2) });
          if (sh === 0.30 && dir === 'down' && (a === 0.10 || a === 0.40)) {
            const r = run({ def, share: sh, att: a, dir, strat: worst.strat });
            res.series[`${name}|${a}`] = r.series;
          }
        }
      }
    }
  }
  require('fs').writeFileSync(__dirname + '/results/pegdef.json', JSON.stringify(res));
  // text summary: worst case over directions, per defence, honest share 30% and 5%
  const lines = [];
  for (const sh of [0.30, 0.05]) {
    lines.push(`\nHonest Sen share ${sh * 100}%: worst move of 1 JEN in Sen during a 7-day attack (both directions)`);
    lines.push('defence'.padEnd(16) + atts.map(a => (`att ${a * 100}%`).padStart(11)).join(''));
    for (const name of Object.keys(DEFS)) {
      const row = atts.map(a => {
        const w = res.attack.filter(r => r.defence === name && r.share === sh && r.attacker === a);
        return Math.max(...w.map(r => r.max_dev_pct));
      });
      lines.push(name.padEnd(16) + row.map(x => (x.toFixed(0) + '%').padStart(11)).join(''));
    }
  }
  lines.push('\nGenuine change: the Sen worth 1.5x, blocks until 1 JEN is within 5% of 1 Sen (576 blocks a day)');
  lines.push('defence'.padEnd(16) + shares.map(s => (`share ${s * 100}%`).padStart(12)).join(''));
  for (const name of Object.keys(DEFS)) {
    lines.push(name.padEnd(16) + shares.map(s => { const r = res.change.find(x => x.defence === name && x.share === s); return String(r.blocks_to_5pct ?? '>6000').padStart(12); }).join(''));
  }
  lines.push('\nAttack cost (fees lost, % of a day\'s honest payment volume), honest share 30%, all three defences:');
  for (const a of atts) {
    const w = res.attack.filter(r => r.defence === 'all three' && r.share === 0.30 && r.attacker === a);
    lines.push(`  attacker ${a * 100}%: ` + w.map(r => `${r.dir} (${r.strat}) moves ${r.max_dev_pct}% for ${r.cost_pct_of_daily_volume}%/day`).join('; '));
  }
  require('fs').writeFileSync(__dirname + '/results/pegdef.txt', lines.join('\n') + '\n');
  console.log(lines.join('\n'));
}
