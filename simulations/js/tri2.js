// Three chains (Jen, Ken, Yen) with the exchange feeding the weight.
// Day model. For each chain c: true weight U_c = V_c - g_c (log grams per coin), where V_c is the
// physical coin's value (copper / silver / gold, random walk 0.5%/day) and g_c the market value of
// one gram of the chain's money (random walk 0.5%/day).
// Readings of U_c each day:
//   payment reading  P_c = U_c + noise 1% + the attacker's push on payments
//   exchange-implied from pair (c, j): I_cj = S_j + (V_c - V_j) + (g_j - g_c) as seen in the day's
//     batch auctions: the coin ratio quoted by coin-priced traders (from metal prices, spread 2%) and
//     the gram rate of gram-priced trades (noise 0.5%), using the chain's current S_j.
//     An attacker who places coin-priced orders off by d with a share s of the pair's coin-priced
//     volume moves the auction's median; his orders are filled by others, so he loses d x his volume.
// Rule 'median3': the day's value for chain c = median(P_c, I_cj, I_ck); 'pay': P_c only.
// Then the Fibonacci day window, the day clip (10%), anchor (2.9%/day) and band (+-10%) as in 6.6.
'use strict';
function rngf(seed) { let s = seed >>> 0; return () => { s = (s + 0x6D2B79F5) >>> 0; let t = s; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; }; }
const DAYS = 120, T0 = 40, ANCHOR_DAY = 0.00005 * 576, BAND = Math.log(1.1), CLIP = Math.log(1.1);
const FIB = [1, 2, 3, 5, 8, 13, 21, 34, 55]; const WEIGHTS = []; FIB.forEach((n, k) => { for (let i = 0; i < n; i++) WEIGHTS.push(Math.pow(0.5, k)); });
const CH = ['Jen', 'Ken', 'Yen'];
function invPhi(p) { // Acklam approximation
  const a = [-39.69683028665376, 220.9460984245205, -275.9285104469687, 138.357751867269, -30.66479806614716, 2.506628277459239];
  const b = [-54.47609879822406, 161.5858368580409, -155.6989798598866, 66.80131188771972, -13.28068155288572];
  const c = [-0.007784894002430293, -0.3223964580411365, -2.400758277161838, -2.549732539343734, 4.374664141464968, 2.938163982698783];
  const d = [0.007784695709041462, 0.3224671290700398, 2.445134137142996, 3.754408661907416];
  const pl = 0.02425; let q, r;
  if (p < pl) { q = Math.sqrt(-2 * Math.log(p)); return (((((c[0] * q + c[1]) * q + c[2]) * q + c[3]) * q + c[4]) * q + c[5]) / ((((d[0] * q + d[1]) * q + d[2]) * q + d[3]) * q + 1); }
  if (p > 1 - pl) { q = Math.sqrt(-2 * Math.log(1 - p)); return -(((((c[0] * q + c[1]) * q + c[2]) * q + c[3]) * q + c[4]) * q + c[5]) / ((((d[0] * q + d[1]) * q + d[2]) * q + d[3]) * q + 1); }
  q = p - 0.5; r = q * q; return (((((a[0] * r + a[1]) * r + a[2]) * r + a[3]) * r + a[4]) * r + a[5]) * q / (((((b[0] * r + b[1]) * r + b[2]) * r + b[3]) * r + b[4]) * r + 1);
}
// shift of a weighted median when a share s of the volume sits at +d and the rest is honest with spread sd
function medShift(s, d, sd) { if (s <= 0 || d === 0) return 0; if (s >= 0.5) return d; const z = invPhi(0.5 / (1 - s)); return Math.sign(d) * Math.min(Math.abs(d), sd * z); }

function run(o, seed = 3) {
  const R = rngf(seed); const g = () => Math.sqrt(-2 * Math.log(R() + 1e-12)) * Math.cos(2 * Math.PI * R());
  const V = [0, 0, 0], G = [0, 0, 0];
  const S = [0, 0, 0], A = [0, 0, 0], hist = [[], [], []], prevW = [null, null, null];
  const out = { maxDev: [0, 0, 0], follow: null };
  for (let d = 0; d < DAYS; d++) {
    for (let c = 0; c < 3; c++) { V[c] += 0.005 * g(); G[c] += 0.005 * g(); }
    if (o.copper && d === T0) V[0] += Math.log(1.5);                      // copper jumps 50%
    const U = V.map((v, c) => v - G[c]);
    const att = d >= T0 && d < T0 + (o.dur || 30);
    const vals = [];
    for (let c = 0; c < 3; c++) {
      const P = U[c] + 0.01 * g() + (att && o.pay && o.pay[c] ? o.pay[c] : 0);
      if (o.rule === 'pay') { vals.push(P); continue; }
      const imp = [];
      for (let j = 0; j < 3; j++) {
        if (j === c) continue;
        const key = c < j ? `${c}${j}` : `${j}${c}`, ex = att && o.ex && o.ex[key];
        // attacker's coin-priced orders distort the pair's coin ratio; sign: pushing chain c's weight by ex.d
        let shift = ex ? medShift(ex.s, ex.d, 0.02) : 0;
        if (ex && ex.target !== c) shift = -shift;                          // the same distortion reads the other way for the partner chain
        imp.push(S[j] + (V[c] - V[j]) + (G[j] - G[c]) + 0.02 / Math.sqrt(20) * g() + 0.005 * g() + shift);
      }
      vals.push([P, ...imp].sort((a, b) => a - b)[1]);
    }
    for (let c = 0; c < 3; c++) {
      let v = vals[c];
      if (prevW[c] !== null) v = Math.max(prevW[c] - CLIP, Math.min(prevW[c] + CLIP, v));
      hist[c].unshift(v); if (hist[c].length > WEIGHTS.length) hist[c].pop();
      let sw = 0, s = 0; for (let i = 0; i < hist[c].length; i++) { sw += WEIGHTS[i]; s += WEIGHTS[i] * hist[c][i]; }
      prevW[c] = s / sw;
      if (d < 20) { S[c] = prevW[c]; A[c] = S[c]; continue; }
      S[c] = Math.max(A[c] - BAND, Math.min(A[c] + BAND, prevW[c])); A[c] += Math.max(-ANCHOR_DAY, Math.min(ANCHOR_DAY, S[c] - A[c]));
      if (d >= T0) out.maxDev[c] = Math.max(out.maxDev[c], Math.abs(S[c] - U[c]));
    }
    if (o.copper && d >= T0 && out.follow === null && Math.abs(S[0] - U[0]) < Math.log(1.05)) out.follow = d - T0;
  }
  return out;
}
module.exports = { run };

if (require.main === module) {
  const pct = x => (100 * (Math.exp(x) - 1)).toFixed(0) + '%';
  const L = ['Three chains, exchange trades in the weight. Largest move of each chain\'s S away from its true value in a 30-day attack (Jen / Ken / Yen).'];
  const P = 0.25; // a payment attack strong enough to move Jen's S about 18-20% a month on its own (the $5M case of 6.6)
  const rows = [
    ['no attack', {}],
    ['payment attack on Jen', { pay: [P, 0, 0] }],
    ['exchange attack on Jen-Ken, 30% of coin-priced volume, 13% off', { ex: { '01': { s: 0.3, d: 0.13, target: 0 } } }],
    ['exchange attack on Jen-Ken, 60% of volume, 13% off', { ex: { '01': { s: 0.6, d: 0.13, target: 0 } } }],
    ['payment on Jen + exchange Jen-Ken 60%', { pay: [P, 0, 0], ex: { '01': { s: 0.6, d: 0.13, target: 0 } } }],
    ['payment on Jen + exchange Jen-Ken and Jen-Yen 60%', { pay: [P, 0, 0], ex: { '01': { s: 0.6, d: 0.13, target: 0 }, '02': { s: 0.6, d: 0.13, target: 0 } } }],
    ['payment attack on Jen and Ken together, same push', { pay: [P, P, 0] }],
  ];
  L.push('scenario'.padEnd(62) + 'payments only'.padStart(20) + 'median of three'.padStart(22));
  for (const [name, o] of rows) {
    const a = run({ ...o, rule: 'pay' }), b = run({ ...o, rule: 'median3' });
    const f = r => r.maxDev.map(pct).join(' / ');
    L.push(name.padEnd(62) + f(a).padStart(20) + f(b).padStart(22));
  }
  const c1 = run({ rule: 'pay', copper: true }), c2 = run({ rule: 'median3', copper: true });
  L.push(`\nGenuine change (copper +50%): Jen's S within 5% after ${c1.follow ?? '>80'} days with payments only, ${c2.follow ?? '>80'} days with the median of three.`);
  require('fs').writeFileSync(__dirname + '/results/tri2.txt', L.join('\n') + '\n');
  console.log(L.join('\n'));
}
