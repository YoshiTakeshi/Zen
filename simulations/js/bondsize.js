// A bond that resizes with pressure, on top of the day window + anchor + day clip and the
// receiver cap. Jen at 1M payments a day, 300,000 Sen-priced, 50,000 shops (Zipf sizes).
//
// Who counts toward S on a day:
//   receiver: holds at least B for the last 7 days (its lowest balance over 7 days >= B today),
//             counts at most CAP = 0.03% of the day's Sen payments (90);
//   sender  : holds at least Bs for the last 7 days, counts at most Q = 10 payments a day
//             (only with rule 'pair').
// Bond resize (rule 'resize'): pressure = the day's raw reading differs from S by more than 5%.
//   Under pressure B and Bs grow 20% a day (at most x20 the base); without it they shrink 5% a
//   day back to the base. Base: B0 = $1,000, Bs0 = $50.
// Honest side: shop balance = 3 days of takings x lognormal(0, 0.5); customer balances
//   lognormal, median $200, sigma 1.2; a customer counts if it holds Bs.
// Attacker: K receiver accounts holding X each and enough sender accounts (K x 90 / Q) holding
//   Xs each, placed ahead of time; X and Xs are m times the base bonds. His counted fakes =
//   K x 90 while his accounts still qualify. Fakes placed where they push hardest.
'use strict';
function rngf(seed) { let s = seed >>> 0; return () => { s = (s + 0x6D2B79F5) >>> 0; let t = s; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; }; }
const SEN_DAY = 300000, SHOPS = 50000, CAP = 0.0003 * SEN_DAY, Q = 10, B0 = 1000, BS0 = 50;
const SAMPLE_D = 2000, SAMPLE_G = 4500, T0 = 40, HORIZON = 60;
const LONGD = 1 - Math.pow(0.5, 1 / 3.5), ANCHOR_DAY = 0.00005 * 576, BAND = Math.log(1.1), CLIP = Math.log(1.1);
const FIB = [1, 2, 3, 5, 8, 13, 21, 34, 55]; const WEIGHTS = []; FIB.forEach((n, k) => { for (let i = 0; i < n; i++) WEIGHTS.push(Math.pow(0.5, k)); });
function mid(L) { if (!L.length) return null; L.sort((a, b) => a - b); const n = L.length, lo = 0.4 * n, hi = 0.6 * n; let s = 0, w = 0; for (let i = 0; i < n; i++) { const a = Math.max(i, lo), b = Math.min(i + 1, hi); if (b > a) { s += (b - a) * L[i]; w += b - a; } } return w ? s / w : L[n >> 1]; }
// shops
const R0 = rngf(99); const g0 = () => Math.sqrt(-2 * Math.log(R0() + 1e-12)) * Math.cos(2 * Math.PI * R0());
const zs = (() => { let s = 0; for (let i = 1; i <= SHOPS; i++) s += 1 / i; return s; })();
const shops = []; for (let i = 1; i <= SHOPS; i++) { const n = SEN_DAY / i / zs; shops.push({ n, bal: n * 8.24 * 3 * Math.exp(0.5 * g0()) }); }
shops.sort((a, b) => b.bal - a.bal);
function erfc(x) { const t = 1 / (1 + 0.5 * Math.abs(x)); const y = t * Math.exp(-x * x - 1.26551223 + t * (1.00002368 + t * (0.37409196 + t * (0.09678418 + t * (-0.18628806 + t * (0.27886807 + t * (-1.13520398 + t * (1.48851587 + t * (-0.82215223 + t * 0.17087277))))))))); return x >= 0 ? y : 2 - y; }
const custFrac = bs => 0.5 * erfc((Math.log(bs) - Math.log(200)) / (1.2 * Math.SQRT2));
function honestCounted(B, Bs, pair) { let c = 0; for (const s of shops) { if (s.bal < B) break; c += Math.min(s.n, CAP); } return c * (pair ? custFrac(Bs) : 1); }
const H0 = { plain: honestCounted(B0, BS0, false), pair: honestCounted(B0, BS0, true) };

function run(o, seed = 21) {
  const R = rngf(seed); const gauss = () => Math.sqrt(-2 * Math.log(R() + 1e-12)) * Math.cos(2 * Math.PI * R());
  let U = 0, mult = 1; const multHist = [];
  const hG = [], hD = []; let lG = Math.log(2), lD = Math.log(2), logS = 0, A = 0, cGp = null, cDp = null;
  const out = { maxDev: 0, follow: null, minHonest: 1, maxMult: 1, attDays: 0 };
  for (let d = 0; d < T0 + HORIZON; d++) {
    if (o.copper && d === T0) U += Math.log(1.5);
    multHist.push(mult); if (multHist.length > 7) multHist.shift();
    const need = Math.max(...multHist);                         // held for 7 days at the highest level asked
    const B = B0 * (o.resize ? need : 1), Bs = BS0 * (o.resize ? need : 1);
    const H = honestCounted(B, Bs, o.pair);
    out.minHonest = Math.min(out.minHonest, H / H0[o.pair ? 'pair' : 'plain']);
    let Acnt = 0;
    if (o.K && d >= T0 && d < T0 + o.dur) {
      const qual = o.m * B0 >= B && (!o.pair || o.m * BS0 >= Bs);
      if (qual) { Acnt = o.K * CAP; out.attDays++; }
    }
    // the day's sample: honest counted payments, plus fakes in proportion
    const G = [], D = [];
    for (let i = 0; i < SAMPLE_G; i++) G.push(Math.log(2) + gauss() + U);
    for (let i = 0; i < SAMPLE_D; i++) { const v = 2 * Math.exp(gauss()); D.push(Math.log(v < 1 ? Math.max(1, Math.round(v * 6)) / 6 : Math.round(v))); }
    const nf = Math.round(SAMPLE_D * Acnt / H);
    for (let i = 0; i < nf; i++) D.push(lD + o.sgn * o.off);
    const fl = (L, c) => L.filter(x => x >= c - Math.log(4));
    const gRaw = mid(fl(G, lG)), dRaw = mid(fl(D, lD));
    let g = gRaw, dm = dRaw;
    if (cGp !== null) { g = Math.max(cGp - CLIP, Math.min(cGp + CLIP, g)); dm = Math.max(cDp - CLIP, Math.min(cDp + CLIP, dm)); }
    hG.unshift(g); hD.unshift(dm); if (hG.length > WEIGHTS.length) { hG.pop(); hD.pop(); }
    lG += LONGD * (g - lG); lD += LONGD * (dm - lD);
    let sw = 0, sg = 0, sd = 0; for (let i = 0; i < hG.length; i++) { sw += WEIGHTS[i]; sg += WEIGHTS[i] * hG[i]; sd += WEIGHTS[i] * hD[i]; }
    cGp = sg / sw; cDp = sd / sw;
    const target = cGp - cDp;
    if (d < 20) { logS = target; A = target; continue; }
    logS = target; logS = Math.max(A - BAND, Math.min(A + BAND, logS)); A += Math.max(-ANCHOR_DAY, Math.min(ANCHOR_DAY, logS - A));
    // pressure from the raw (unclipped) day reading
    const press = Math.abs((gRaw - dRaw) - logS) > Math.log(1.05);
    mult = press ? Math.min(20, mult * 1.2) : Math.max(1, mult * 0.95);
    out.maxMult = Math.max(out.maxMult, mult);
    if (d >= T0) { const dev = logS - U; out.maxDev = Math.max(out.maxDev, Math.abs(dev)); if (o.copper && out.follow === null && Math.abs(dev) < Math.log(1.05)) out.follow = d - T0; }
  }
  return out;
}
module.exports = { run };

if (require.main === module) {
  const pct = x => (100 * (Math.exp(x) - 1)).toFixed(0) + '%';
  const usd = x => '$' + (x >= 1e6 ? (x / 1e6).toFixed(1) + 'M' : Math.round(x / 1e3) + 'k');
  const strategies = [{ sgn: 1, off: 0.3 }, { sgn: 1, off: 0.7 }, { sgn: -1, off: 0.3 }, { sgn: -1, off: 0.7 }];
  const worst = o => { let b = null; for (const st of strategies) { const r = run({ ...o, ...st }); if (!b || r.maxDev > b.maxDev) b = r; } return b; };
  const RULES = [['fixed bond', {}], ['fixed bond + sender limit', { pair: true }], ['resizing bond', { resize: true }], ['resizing bond + sender limit', { resize: true, pair: true }]];
  const L = [];
  L.push(`Honest Sen payments counted at the base bonds: ${Math.round(H0.plain).toLocaleString('en-US')} (receiver rules), ${Math.round(H0.pair).toLocaleString('en-US')} (with sender rules), of 300,000 a day.`);
  L.push('No attack: S wanders at most ' + pct(run({ K: 0, dur: 0, sgn: 1, off: 0 }).maxDev) + '.');
  for (const [name, rule] of RULES) {
    L.push(`\n${name}: largest move of S in 7 / 30 days, and the capital the attacker locked`);
    L.push('accounts'.padEnd(10) + [1, 2, 4, 8].map(m => (`bonds x${m}`).padStart(24)).join(''));
    for (const K of [50, 100, 200, 500]) {
      const row = [1, 2, 4, 8].map(m => {
        const a = worst({ K, m, dur: 7, ...rule }), b = worst({ K, m, dur: 30, ...rule });
        const cap = K * m * B0 + (rule.pair ? (K * CAP / Q) * m * BS0 : 0);
        return `${pct(a.maxDev)} / ${pct(b.maxDev)} ${usd(cap)}`;
      });
      L.push(String(K).padEnd(10) + row.map(x => x.padStart(24)).join(''));
    }
  }
  L.push('\nGenuine change, a Sen worth 1.5x (no attack):');
  for (const [name, rule] of RULES) {
    const r = run({ K: 0, dur: 0, sgn: 1, off: 0, copper: true, ...rule });
    L.push(`  ${name.padEnd(30)} S within 5% after ${r.follow ?? '>60'} days; bond up to x${r.maxMult.toFixed(1)}; honest payments counted fell to ${(100 * r.minHonest).toFixed(0)}% of normal`);
  }
  require('fs').writeFileSync(__dirname + '/results/bondsize.txt', L.join('\n') + '\n');
  console.log(L.join('\n'));
}
