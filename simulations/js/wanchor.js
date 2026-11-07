// W (the typical ordinary payment, which sets the typical fee, the smallest fee
// W x 0.01% and the smallest payment W / 600) with and without a loose anchor.
// W: middle-20% average of ordinary payments, each counted once, window alpha 0.1,
// at most 1% a block (as in twounit.js). Anchor variants: W stays within +-BAND of
// an anchor that follows W by at most ASTEP a block.
// One block = 150 s, 576 a day, 100 honest payments a block, goods lognormal (sigma 1).
// Attack: the attacker adds a share of all payments (ordinary, at the size that pushes
// hardest, up or down) for 7 or 30 days.
'use strict';
function rngf(seed) { let s = seed >>> 0; return () => { s = (s + 0x6D2B79F5) >>> 0; let t = s; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; }; }
const DAY = 576, N = 100, STEP = 0.01, ALPHA = 0.1, LONG = 1 - Math.pow(0.5, 1 / 2000);
function mid(L) { if (!L.length) return null; L.sort((a, b) => a - b); const n = L.length, lo = 0.4 * n, hi = 0.6 * n; let s = 0, w = 0; for (let i = 0; i < n; i++) { const a = Math.max(i, lo), b = Math.min(i + 1, hi); if (b > a) { s += (b - a) * L[i]; w += b - a; } } return w ? s / w : L[n >> 1]; }

const VARIANTS = {
  'no anchor': null,
  '+-50%, 0.05%/blk': { band: Math.log(1.5), astep: 0.0005 },
  '+-50%, 0.02%/blk': { band: Math.log(1.5), astep: 0.0002 },
  '+-25%, 0.02%/blk': { band: Math.log(1.25), astep: 0.0002 },
  '+-25%, 0.01%/blk': { band: Math.log(1.25), astep: 0.0001 },
};

function run(o, seed = 1) {
  const R = rngf(seed);
  const gauss = () => Math.sqrt(-2 * Math.log(R() + 1e-12)) * Math.cos(2 * Math.PI * R());
  const v = VARIANTS[o.variant];
  const days = o.days || 7, start = 2000, end = start + days * DAY;
  const BLOCKS = o.habit ? start + 20 * DAY : end + 200;
  let size = 0, logW = 0.25, A = 0.25, nW = 0, dW = 0, lG = 0.25; // honest typical (middle-20% of lognormal) ~ size
  const out = { maxUp: 0, maxDown: 0, follow: null, attValue: 0, honValue: 0 };
  for (let b = 0; b < BLOCKS; b++) {
    if (o.habit && b === start) size += o.habit;           // genuine change in spending
    const att = o.att > 0 && b >= start && b < end;
    const L = [];
    for (let i = 0; i < N; i++) { const l = size + gauss(); L.push(l); if (att) out.honValue += Math.exp(l); }
    if (att) {
      const na = Math.round(N * o.att / (1 - o.att));
      const c = o.centre === 'long' ? lG : logW;
      for (let i = 0; i < na; i++) { const l = o.off === 'x' ? o.sgn * 8 : c + o.sgn * o.off; L.push(l); out.attValue += Math.exp(l); }
    }
    const m = mid(L);
    nW = (1 - ALPHA) * nW + ALPHA * m; dW = (1 - ALPHA) * dW + ALPHA;
    logW += Math.max(-STEP, Math.min(STEP, nW / dW - logW));
    if (v) { logW = Math.max(A - v.band, Math.min(A + v.band, logW)); A += Math.max(-v.astep, Math.min(v.astep, logW - A)); }
    lG += LONG * (logW - lG);
    const dev = logW - (size + 0.0);                          // against the honest typical payment (middle-20% of N(size,1) = size)
    if (att) { out.maxUp = Math.max(out.maxUp, dev); out.maxDown = Math.min(out.maxDown, dev); }
    if (o.habit && b >= start && out.follow === null && Math.abs(dev) < Math.log(1.05)) out.follow = b - start;
  }
  return out;
}
module.exports = { run, VARIANTS };

if (require.main === module) {
  const pct = x => Math.abs(x) >= 7 ? (x > 0 ? 'runaway' : '-100%') : (100 * (Math.exp(x) - 1)).toFixed(0) + '%';
  const strategies = [];
  for (const sgn of [1, -1]) for (const off of [0.3, 0.7, 1.5, 3, 'x']) for (const centre of ['now', 'long']) strategies.push({ sgn, off, centre });
  const lines = [];
  const atts = [0.05, 0.10, 0.20, 0.30, 0.40];
  // honest typical payment $5; 1M honest payments a day; fee 1% of value, half not earned back
  const COST = (r, att, days) => { const usdPerUnit = 5 / Math.exp(0.5); const perDay = 1e6 * (att / (1 - att)); const meanAtt = r.attValue / (r.attCount || 1); return null; };
  for (const days of [7, 30]) {
    lines.push(`\n${days}-day attack on ordinary payments: largest move of W up / down (W sets the typical fee, the smallest fee and the smallest payment)`);
    lines.push('variant'.padEnd(20) + atts.map(a => (`att ${a * 100}%`).padStart(18)).join(''));
    for (const name of Object.keys(VARIANTS)) {
      const row = atts.map(a => {
        let up = 0, down = 0;
        for (const st of strategies) { const r = run({ variant: name, att: a, days, ...st }); up = Math.max(up, r.maxUp); down = Math.min(down, r.maxDown); }
        return `+${pct(up)} / ${pct(down)}`.replace('+runaway', 'runaway');
      });
      lines.push(name.padEnd(20) + row.map(x => x.padStart(18)).join(''));
    }
  }
  lines.push('\nGenuine change in spending, no attack: blocks until W is within 5% of the new typical payment (576 blocks a day)');
  lines.push('variant'.padEnd(20) + ['x1.2', 'x2', 'x0.5', 'x4'].map(s => s.padStart(14)).join(''));
  for (const name of Object.keys(VARIANTS)) {
    const row = [1.2, 2, 0.5, 4].map(f => { const r = run({ variant: name, att: 0, habit: Math.log(f) }); return r.follow === null ? '>20 days' : `${r.follow} (${(r.follow / DAY).toFixed(1)}d)`; });
    lines.push(name.padEnd(20) + row.map(x => x.padStart(14)).join(''));
  }
  // attack cost: the hardest push up at 20% for 7 days, no anchor vs anchor; attacker value relative to honest value
  lines.push('\nAttack cost in fees (1% of the attacker\'s payment value, half not earned back), Jen at 1M honest payments a day, typical payment $5:');
  for (const a of [0.10, 0.20, 0.40]) {
    let best = null;
    for (const st of strategies.filter(s => s.sgn > 0)) { const r = run({ variant: '+-50%, 0.02%/blk', att: a, days: 7, ...st }); if (!best || r.maxUp > best.r.maxUp) best = { r, st }; }
    const ratio = best.r.attValue / best.r.honValue;                      // attacker value / honest value
    const honDaily = 1e6 * 5 * Math.exp(0.5) / Math.exp(0);              // honest $ a day (mean of lognormal vs typical $5)
    const usd = ratio * honDaily * 0.01 * 0.5 * 7;
    lines.push(`  attacker ${a * 100}% of payments, push up (offset ${best.st.off}): W +${pct(best.r.maxUp)} in a week for about $${Math.round(usd).toLocaleString('en-US')}`);
  }
  require('fs').writeFileSync(__dirname + '/results/wanchor.txt', lines.join('\n') + '\n');
  console.log(lines.join('\n'));
}
