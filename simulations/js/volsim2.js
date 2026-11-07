// Coin-days and the bond penalty, on top of the full set (volsim.js: volume-weighted day reading,
// each gram counted once with a 3-day rest, day window + day clip + anchor/band, receiver cap
// 0.03%, bond that grows on receiver disagreement).
//
// Honest money: the age of the money a payment spends is exponential, mean 20 days (assumed).
//   Money younger than the 3-day rest does not count.
// Coin-days (cd): a counted payment weighs value x min(age, 30) / 30. An attacker who cycles his
//   money every H days (H >= 3) counts C/H a day at weight min(H,30)/30, i.e. C/30 a day for any
//   H <= 30; he picks H = 30 to pay the least fees. Without coin-days he counts C/4 a day.
// Bond penalty (pen): each receiver's 30-day price change is compared with the median receiver's;
//   a receiver more than 15% away loses 2% of its bond a day (burned). The attacker's accounts
//   show his offset as their 30-day change. He tops the bonds back up (that is his cost) or keeps
//   his offset under 15% to avoid it.
// Jen at 1M payments a day: $2.47M of Sen-priced value a day. Costs: interest 5% a year on what is
// locked, fees 1% of the value he moves (half not earned back), penalties.
'use strict';
function rngf(seed) { let s = seed >>> 0; return () => { s = (s + 0x6D2B79F5) >>> 0; let t = s; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; }; }
const V = 300000 * 5 * Math.exp(0.5), N_D = 12000, N_G = 12000, T0 = 40, HORIZON = 60, REST = 3, AGE_MEAN = 20;
const LONGD = 1 - Math.pow(0.5, 1 / 3.5), ANCHOR_DAY = 0.00005 * 576, BAND = Math.log(1.1), CLIP = Math.log(1.1);
const FIB = [1, 2, 3, 5, 8, 13, 21, 34, 55]; const WEIGHTS = []; FIB.forEach((n, k) => { for (let i = 0; i < n; i++) WEIGHTS.push(Math.pow(0.5, k)); });
const HONEST_VOTERS = 730, CAPF = 0.0003, B0 = 1000, M = 2, PEN_LIMIT = Math.log(1.15), PEN_RATE = 0.02;
function wmid(L) {
  if (!L.length) return null; L.sort((a, b) => a[0] - b[0]);
  let T = 0; for (const x of L) T += x[1];
  const lo = 0.4 * T, hi = 0.6 * T; let acc = 0, s = 0, w = 0;
  for (const [v, wt] of L) { const a = Math.max(acc, lo), b = Math.min(acc + wt, hi); if (b > a) { s += (b - a) * v; w += b - a; } acc += wt; if (acc >= hi) break; }
  return w ? s / w : L[L.length >> 1][0];
}
function mid(L) { L.sort((a, b) => a - b); const n = L.length, lo = 0.4 * n, hi = 0.6 * n; let s = 0, w = 0; for (let i = 0; i < n; i++) { const a = Math.max(i, lo), b = Math.min(i + 1, hi); if (b > a) { s += (b - a) * L[i]; w += b - a; } } return s / w; }

function run(o, seed = 41) {
  const R = rngf(seed); const gauss = () => Math.sqrt(-2 * Math.log(R() + 1e-12)) * Math.cos(2 * Math.PI * R());
  const age = () => -AGE_MEAN * Math.log(R() + 1e-12);
  const wAge = a => a < REST ? 0 : (o.cd ? Math.min(a, 30) / 30 : 1);
  let U = 0, mult = 1, base = null; const multHist = [];
  const hG = [], hD = []; let lG = Math.log(2), lD = Math.log(2), logS = 0, A = 0, cGp = null, cDp = null;
  const out = { maxDev: 0, follow: null, maxMult: 1, K: 0, penalty: 0, fees: 0, honestShare: 1, honestPen: 0 };
  let attDays = 0;
  for (let d = 0; d < T0 + HORIZON; d++) {
    if (o.copper && d === T0) U += Math.log(1.5);
    multHist.push(mult); if (multHist.length > 7) multHist.shift();
    const need = Math.max(...multHist);
    const D = [], G = [];
    let hW = 0, hAll = 0;
    for (let i = 0; i < N_D; i++) { const v = 2 * Math.exp(gauss()); const p = v < 1 ? Math.max(1, Math.round(v * 6)) / 6 : Math.round(v); hAll += p; const w = wAge(age()); if (w > 0) { D.push([Math.log(p), p * w]); hW += p * w; } }
    for (let i = 0; i < N_G; i++) { const v = 2 * Math.exp(gauss()); const w = wAge(age()); if (w > 0) G.push([Math.log(v) + U, v * w]); }
    if (need > 1) { const keep = Math.pow(need, -0.6); for (let i = D.length - 1; i >= 0; i--) if (R() > keep) { hW -= D[i][1]; D.splice(i, 1); } }
    const honestMid = wmid(D.filter(x => x[0] >= lD - Math.log(4)));
    let att = 0, K = 0;
    if (o.C && d >= T0 && d < T0 + o.dur) {
      const H = o.cd ? 30 : REST + 1;                        // days between two counts of the same money
      let usdW = o.cd ? o.C / 30 : o.C / H;                    // weighted counted value a day
      const capUsdW = CAPF * V * (hW / hAll);                  // each receiver: 0.03% of the day's weighted counted value
      K = Math.ceil(usdW / capUsdW); out.K = K;
      if (M < need) usdW = 0;                                  // his bonds no longer qualify
      if (usdW > 0) {
        att = usdW / V * hAll;                                 // in sample units
        D.push([lD + o.sgn * o.off, att]);
        out.fees += (o.C / H) * 0.01 * 0.5;                    // he moves C/H a day
        if (o.pen && Math.abs(o.off) > PEN_LIMIT) out.penalty += K * M * B0 * PEN_RATE;
        attDays++;
      }
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
    // receiver disagreement (bond growth), as in volsim.js
    const votes = []; for (let i = 0; i < HONEST_VOTERS; i++) votes.push((honestMid - base) + 0.13 * gauss());
    for (let i = 0; i < (att > 0 ? K : 0); i++) votes.push(o.sgn * o.off);
    const press = Math.abs((dRaw - base) - mid(votes)) > Math.log(1.03);
    mult = press ? Math.min(20, mult * 1.2) : Math.max(1, mult * 0.95);
    out.maxMult = Math.max(out.maxMult, mult);
    base += LONGD * (honestMid - base);
    // honest shops hit by the penalty: own 30-day change noise (a shop's 30-day middle, ~13%/sqrt(30))
    if (o.pen && d >= T0) { let hit = 0; for (let i = 0; i < HONEST_VOTERS; i++) if (Math.abs(0.13 / Math.sqrt(30) * gauss() + 0.03 * gauss()) > PEN_LIMIT) hit++; out.honestPen = Math.max(out.honestPen, hit / HONEST_VOTERS); }
    if (d >= T0) { const dev = logS - U; out.maxDev = Math.max(out.maxDev, Math.abs(dev)); if (o.copper && out.follow === null && Math.abs(dev) < Math.log(1.05)) out.follow = d - T0; }
  }
  out.attDays = attDays;
  return out;
}
module.exports = { run };

if (require.main === module) {
  const pct = x => (100 * (Math.exp(x) - 1)).toFixed(0) + '%';
  const usd = x => '$' + (x >= 1e6 ? (x / 1e6).toFixed(1) + 'M' : Math.round(x / 1e3) + 'k');
  const caps = [1e6, 2.5e6, 5e6, 10e6, 25e6];
  const strategies = [];
  for (const sgn of [1, -1]) for (const off of [0.1, 0.13, 0.3, 1]) strategies.push({ sgn, off });
  const CONFIGS = [['full set (3-day rest)', {}], ['+ coin-days', { cd: true }], ['+ bond penalty', { pen: true }], ['+ coin-days + bond penalty', { cd: true, pen: true }]];
  const L = ['Coin-days and bond penalty on top of the full set. Jen at 1M payments a day ($2.47M Sen-priced value a day).',
    'For each attacker money C: largest move of S in 30 days (worst strategy), money locked (C + bonds), spent in 30 days (fees + 5%/yr interest + penalties).'];
  for (const [name, cfg] of CONFIGS) {
    const q = run({ ...cfg, C: 0, dur: 0, sgn: 1, off: 0 });
    L.push(`\n${name}  (no attack: S wanders ${pct(q.maxDev)}${cfg.pen ? `; honest receivers penalised at worst ${(100 * q.honestPen).toFixed(1)}%` : ''})`);
    L.push('money'.padEnd(10) + 'move 7d'.padStart(9) + 'move 30d'.padStart(10) + 'accounts'.padStart(10) + 'locked'.padStart(10) + 'spent 30d'.padStart(11) + '  (of which penalties)   best offset');
    for (const C of caps) {
      let b7 = 0, best = null;
      for (const st of strategies) {
        b7 = Math.max(b7, run({ ...cfg, C, dur: 7, ...st }).maxDev);
        const r = run({ ...cfg, C, dur: 30, ...st });
        if (!best || r.maxDev > best.r.maxDev + 0.005 || (Math.abs(r.maxDev - best.r.maxDev) <= 0.005 && r.penalty < best.r.penalty)) best = { r, st };
      }
      const r = best.r, locked = C + r.K * M * B0, spent = r.fees + locked * 0.05 * 30 / 365 + r.penalty;
      L.push(usd(C).padEnd(10) + pct(b7).padStart(9) + pct(r.maxDev).padStart(10) + String(r.K).padStart(10) + usd(locked).padStart(10) + usd(spent).padStart(11) + `  (${usd(r.penalty)})`.padEnd(23) + `${best.st.sgn > 0 ? '+' : '-'}${best.st.off}`);
    }
  }
  L.push('\nGenuine change, a Sen worth 1.5x:');
  for (const [name, cfg] of CONFIGS) { const r = run({ ...cfg, C: 0, dur: 0, sgn: 1, off: 0, copper: true }); L.push(`  ${name.padEnd(30)} S within 5% after ${r.follow ?? '>60'} days, bond up to x${r.maxMult.toFixed(1)}`); }
  require('fs').writeFileSync(__dirname + '/results/volsim2.txt', L.join('\n') + '\n');
  console.log(L.join('\n'));
}
