// S (the SEN unit) read with a Fibonacci window counted in DAYS instead of blocks.
//   Per day d: G_d = middle-20% average of log(value) of ordinary payments,
//              D_d = middle-20% average of log(price in Sen) of Sen-priced payments,
//              both after the floor (drop payments under 1/4 of the long-run typical value).
//   Window: day weights 1 (the last full day), 1/2 for the 2 before, 1/4 for the 3 before,
//           1/8 for the next 5, ... (Fibonacci groups), each day's weight capped at the
//           window's median day weight (equal here, payments a day are steady).
//   S target = window(G) - window(D), set once a day; S moves to it at most
//           step x min(day share, long-run share) / 30% (none under 2%).
//   Optional anchor: S within +-10% of an anchor moving at most 0.005% a block (2.9% a day).
// Traffic: 5,760 honest payments a day in the model (each day's middle-20% is then read to
// about 1%; a real chain with more payments reads it more finely, the attack shares scale).
// 30% of honest payments priced in Sen. Goods lognormal, median 2 Sen, sigma 1.
// Attack: from day 40 the attacker adds a share of ALL payments for 1, 7 or 30 days, as
// Sen-priced payments at the offset and direction that pushes hardest. Measured: the largest
// move of S over the 60 days after the attack starts.
'use strict';
function rngf(seed) { let s = seed >>> 0; return () => { s = (s + 0x6D2B79F5) >>> 0; let t = s; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; }; }
const PER_DAY = 5760, SHARE = 0.30, T0 = 40, HORIZON = 60;
const LONGD = 1 - Math.pow(0.5, 1 / 3.5);               // long-run centres: half-life 3.5 days
const ANCHOR_DAY = 0.00005 * 576, BAND = Math.log(1.1), STEP_DAY = 0.01 * 576;
const FIB = [1, 2, 3, 5, 8, 13, 21, 34, 55, 89];
const WEIGHTS = []; FIB.forEach((n, k) => { for (let i = 0; i < n; i++) WEIGHTS.push(Math.pow(0.5, k)); });
const WLEN = 120;                                        // days kept (the weight beyond is < 0.5%)
function mid(L) { if (!L.length) return null; L.sort((a, b) => a - b); const n = L.length, lo = 0.4 * n, hi = 0.6 * n; let s = 0, w = 0; for (let i = 0; i < n; i++) { const a = Math.max(i, lo), b = Math.min(i + 1, hi); if (b > a) { s += (b - a) * L[i]; w += b - a; } } return w ? s / w : L[n >> 1]; }

function run(o, seed = 11) {
  const R = rngf(seed);
  const gauss = () => Math.sqrt(-2 * Math.log(R() + 1e-12)) * Math.cos(2 * Math.PI * R());
  const days = T0 + HORIZON;
  let U = 0;                                             // log true value of a Sen (in grams); S should equal it
  const hG = [], hD = [];                                // per-day values, newest first
  let lG = Math.log(2), lD = Math.log(2), sL = SHARE, logS = 0, A = 0;
  const out = { maxDev: 0, follow: null, cost: 0, path: [] };
  for (let d = 0; d < days; d++) {
    if (o.copper && d === T0) U += Math.log(1.5);      // genuine: a Sen worth 1.5x
    const att = o.att > 0 && d >= T0 && d < T0 + o.dur;
    const G = [], D = [];
    for (let i = 0; i < PER_DAY; i++) {
      const v = Math.exp(Math.log(2) + gauss());        // goods worth v Sen
      if (R() < SHARE) { const k = v < 1 ? Math.max(1, Math.round(v * 6)) / 6 : Math.round(v); D.push(Math.log(k)); }
      else G.push(Math.log(v) + U + 0.005 * gauss());
    }
    if (att) {
      const na = Math.round(PER_DAY * o.att / (1 - o.att));
      const l = o.off === 'x' ? lD + o.sgn * 8 : lD + o.sgn * o.off;
      for (let i = 0; i < na; i++) D.push(l);
      out.cost += na * Math.exp(l);                     // fake Sen value pushed through
    }
    const share = D.length / (D.length + G.length);
    sL += LONGD * (share - sL);
    const fl = (L, c) => L.filter(x => x >= c - Math.log(4));
    const g = mid(fl(G, lG + U * 0)), dm = mid(fl(D, lD));
    hG.unshift(g); hD.unshift(dm); if (hG.length > WLEN) { hG.pop(); hD.pop(); }
    lG += LONGD * (g - lG); lD += LONGD * (dm - lD);
    // window averages
    let sw = 0, sg = 0, sd = 0;
    for (let i = 0; i < hG.length; i++) { const w = WEIGHTS[i] || 0; sw += w; sg += w * hG[i]; sd += w * hD[i]; }
    const target = sg / sw - sd / sw;
    if (d < 20) { logS = target; A = target; continue; } // warm-up: start at the honest reading
    const s = Math.min(share, sL);
    const step = s < 0.02 ? 0 : STEP_DAY * Math.min(1, s / 0.30);
    logS += Math.max(-step, Math.min(step, target - logS));
    if (o.anchor) { logS = Math.max(A - BAND, Math.min(A + BAND, logS)); A += Math.max(-ANCHOR_DAY, Math.min(ANCHOR_DAY, logS - A)); }
    if (d >= T0) {
      const dev = logS - U;
      out.maxDev = Math.max(out.maxDev, Math.abs(dev));
      if (o.copper && out.follow === null && Math.abs(dev) < Math.log(1.05)) out.follow = d - T0;
      out.path.push(+Math.exp(dev).toFixed(3));
    }
  }
  return out;
}
module.exports = { run };

if (require.main === module) {
  const pct = x => x >= 5 ? 'runaway' : (100 * (Math.exp(x) - 1)).toFixed(0) + '%';
  const strategies = [];
  for (const sgn of [1, -1]) for (const off of [0.3, 0.7, 1.5, 3, 'x']) strategies.push({ sgn, off });
  const atts = [0.02, 0.05, 0.10, 0.20, 0.40];
  const L = [];
  L.push('Day-based Fibonacci window for S. Largest move of 1 SEN unit away from a true Sen, over 60 days from the attack start.');
  L.push('Attacker share = share of ALL payments (honest Sen-priced share 30%), all fake payments Sen-priced.');
  // honest noise
  const quiet = run({ att: 0, dur: 0 });
  L.push(`No attack: S wanders at most ${pct(quiet.maxDev)} over 60 days.`);
  const costRows = [];
  for (const anchor of [false, true]) {
    L.push(`\n${anchor ? 'With' : 'Without'} the anchor (+-10% band, 2.9% a day):`);
    L.push('attack length'.padEnd(15) + atts.map(a => (`att ${a * 100}%`).padStart(10)).join(''));
    for (const dur of [1, 7, 30]) {
      const row = atts.map(a => {
        let best = null;
        for (const st of strategies) { const r = run({ att: a, dur, anchor, ...st }); if (!best || r.maxDev > best.r.maxDev) best = { r, st }; }
        if (anchor && dur === 7) costRows.push([a, best]);
        return pct(best.r.maxDev);
      });
      L.push(`${dur} day${dur > 1 ? 's' : ''}`.padEnd(15) + row.map(x => x.padStart(10)).join(''));
    }
  }
  const c1 = run({ copper: true, att: 0, dur: 0 }), c2 = run({ copper: true, att: 0, dur: 0, anchor: true });
  L.push(`\nGenuine change, a Sen worth 1.5x: S within 5% of the new value after ${c1.follow ?? '>60'} days without the anchor, ${c2.follow ?? '>60'} days with it.`);
  L.push('\nCost of the 7-day attack with the anchor, Jen at 1M payments a day ($5 typical payment, scale x173 from the model),');
  L.push('fee 1% of the fake Sen value, half not earned back, Sen $0.0276:');
  for (const [a, b] of costRows) {
    const fakeSen = b.r.cost * (1e6 / PER_DAY) * (180 / 2);   // model goods median 2 Sen -> real typical 180 Sen
    L.push(`  attacker ${a * 100}%: moves S ${pct(b.r.maxDev)} (offset ${b.st.off}, ${b.st.sgn > 0 ? 'up' : 'down'}) for about $${Math.round(fakeSen * 0.0276 * 0.01 * 0.5).toLocaleString('en-US')}`);
  }
  require('fs').writeFileSync(__dirname + '/results/daywin.txt', L.join('\n') + '\n');
  console.log(L.join('\n'));
}
