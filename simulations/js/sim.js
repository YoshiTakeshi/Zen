// Zen collaborative-minting resize model (Jen parameters).
// Compares the resize rule in the spec today (OLD) with the balanced rule (NEW):
//   OLD: 1-day moving averages; grow 0.5%/block if nearly full and fees above standard,
//        shrink 0.5%/block if not nearly full; no per-minter limit; minters pick the
//        same high-fee payments independently (overlap).
//   NEW: recent-weighted averages (half-life 20 blocks); at most ~doubling per day
//        (0.12%/block); grow if full and fees high; HOLD if fees high but not full
//        (too few provers); shrink only if fees at standard and blocks under 75% full;
//        per-credential leaf quota = 1.25 x cap x its ticket share; mempool split so
//        minters prove different payments; half of each fee goes to a pool paid out
//        1/32 per block; credential window widens with the cap.
// One step = one Jen block (150 s); 576 blocks = 1 day. Amounts in Sen.
'use strict';

const BLOCKS = 5760, DAY = 576, EVENT = 3 * DAY, EVENT2 = 5 * DAY;
const B = 100;            // tickets (winning blows) per block
const W0 = 1000;          // credential window, blocks
const CAPMIN = 2, CAPMAX = 1024, CAP0 = 64;
const STD = 0.01, FEEMAX = 0.06;
const RMED = 0.015, RSIG = 0.8;   // users' maximum acceptable fee rate (lognormal)
const MEANV = 41;         // mean payment value, Sen (lognormal median 20, sigma 1.2)
const LEAF = 4;           // payments per leaf
const POWER = 2;          // leaves per block one ordinary minter can prove
const COST = 0.3;         // Sen per leaf proof (energy + hardware)
const PROVER = 0.75;      // prover share of fees

function rngf(seed) {
  let s = seed >>> 0;
  return () => {
    s = (s + 0x6D2B79F5) >>> 0; let t = s;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}
// inverse normal CDF (Acklam)
function qnorm(p) {
  const a = [-39.69683028665376, 220.9460984245205, -275.9285104469687, 138.357751867269, -30.66479806614716, 2.506628277459239];
  const b = [-54.47609879822406, 161.5858368580409, -155.6989798598866, 66.80131188771972, -13.28068155288572];
  const c = [-0.007784894002430293, -0.3223964580411365, -2.400758277161838, -2.549732539343734, 4.374664141464968, 2.938163982698783];
  const d = [0.007784695709041462, 0.3224671290700398, 2.445134137142996, 3.754408661907416];
  const pl = 0.02425;
  if (p <= 0) return -8; if (p >= 1) return 8;
  if (p < pl) { const q = Math.sqrt(-2 * Math.log(p)); return (((((c[0] * q + c[1]) * q + c[2]) * q + c[3]) * q + c[4]) * q + c[5]) / ((((d[0] * q + d[1]) * q + d[2]) * q + d[3]) * q + 1); }
  if (p > 1 - pl) { const q = Math.sqrt(-2 * Math.log(1 - p)); return -(((((c[0] * q + c[1]) * q + c[2]) * q + c[3]) * q + c[4]) * q + c[5]) / ((((d[0] * q + d[1]) * q + d[2]) * q + d[3]) * q + 1); }
  const q = p - 0.5, r = q * q;
  return (((((a[0] * r + a[1]) * r + a[2]) * r + a[3]) * r + a[4]) * r + a[5]) * q / (((((b[0] * r + b[1]) * r + b[2]) * r + b[3]) * r + b[4]) * r + 1);
}
// clearing fee rate when only a fraction f of the demand fits
function clearing(f) {
  if (f >= 1) return STD;
  const r = RMED * Math.exp(RSIG * qnorm(1 - f));
  return Math.min(FEEMAX, Math.max(STD, r));
}

function run(sc, rule, seed = 1) {
  const R = rngf(seed);
  const gauss = () => Math.sqrt(-2 * Math.log(R() + 1e-12)) * Math.cos(2 * Math.PI * R());
  const NEW = rule === 'new';
  // minters
  const M = [];
  const add = (power, hash, opts = {}) => M.push({ power, hash, last: -1e9, inc: 0, proofs: 0, leaves: 0, alive: true, ...opts });
  const n0 = sc.minters || 60;
  for (let i = 0; i < n0; i++) add(POWER, 1, { last: -Math.floor(R() * 300) });
  let big = null;
  if (sc.big) { add(sc.big.power, sc.big.hash, { big: true, last: 0 }); big = M[M.length - 1]; }

  let cap = CAP0, pool = 0;
  // OLD: ring buffers for 1-day averages
  const histF = new Float64Array(DAY), histU = new Float64Array(DAY);
  let sumF = 0, sumU = 0, nh = 0;
  // NEW: EMAs
  const alpha = 1 - Math.pow(0.5, 1 / 20);
  let emaF = Math.log(STD), emaU = 0.8;
  let mEma = 1.2; // minter margin
  const series = [];
  const acc = { served: 0, demand: 0, proofs: 0, unique: 0, attPaid: 0, attInc: 0, bigLeaves: 0, allLeaves: 0, bigInc: 0, allInc: 0, feeLog: 0, feeN: 0, capPost: [], servedPost: [], adapt: null };

  for (let t = 0; t < BLOCKS; t++) {
    // ---- scenario events
    if (sc.mintersX && t === EVENT) { const k = M.filter(m => m.alive && !m.big).length; for (let i = 0; i < k * (sc.mintersX - 1); i++) add(POWER, 1); }
    if (sc.halfLeave && t === EVENT) { let k = 0; for (const m of M) if (m.alive && !m.big && (k++ % 2 === 0)) { m.alive = false; m.left = true; } }
    if (sc.halfLeave && t === EVENT2) { for (const m of M) if (m.left) { m.alive = true; m.left = false; } }

    // ---- demand
    const mult = (sc.volX && t >= EVENT) ? sc.volX : 1;
    const D = Math.max(0, (sc.base || 200) * mult * (1 + 0.3 * Math.sin(2 * Math.PI * t / DAY)) * (1 + 0.05 * gauss()));
    const fakes = (sc.attack && t >= EVENT) ? sc.attack.fakes : 0;

    // ---- tickets (B per block, by hash), credentials
    const alive = M.filter(m => m.alive);
    let H = 0; for (const m of alive) H += m.hash;
    const cum = []; let c = 0; for (const m of alive) { c += m.hash; cum.push(c); }
    for (let k = 0; k < B; k++) {
      const x = R() * H; let lo = 0, hi = cum.length - 1;
      while (lo < hi) { const mid = (lo + hi) >> 1; if (cum[mid] < x) lo = mid + 1; else hi = mid; }
      alive[lo].last = t;
    }
    const W = NEW ? W0 * Math.max(1, cap / 256) : W0;
    const cred = alive.filter(m => t - m.last <= W);
    let Hc = 0; for (const m of cred) Hc += m.hash;

    // ---- proving
    const K = Math.max(0, Math.min((D + fakes) / LEAF, cap));
    let P = 0; for (const m of cred) { m.p = Math.min(m.power, K); P += m.p; }
    let unique;
    if (K <= 0 || P <= 0) unique = 0;
    else if (NEW) unique = Math.min(P, K);                 // split mempool: little overlap
    else unique = K * (1 - Math.exp(-P / K));              // independent picks: overlap
    const madeProofs = NEW ? Math.min(P, K * 1.05) : P;     // with a split, minters stop at their bucket
    for (const m of cred) { m.avail = P > 0 ? unique * m.p / P : 0; m.proofs += P > 0 ? madeProofs * m.p / P : 0; }

    // ---- block assembly
    let minerBig = false;
    if (big && big.alive && sc.big.seal && R() < sc.big.seal) minerBig = true;
    for (const m of cred) { m.q = NEW ? Math.max(1, Math.ceil(1.25 * cap * m.hash / Hc)) : Infinity; m.got = 0; }
    let room = cap;
    if (minerBig && cred.includes(big)) { big.got = Math.min(big.avail, big.q, room); room -= big.got; }
    // water-fill the rest in proportion to what each minter has, up to its quota
    for (let it = 0; it < 6 && room > 1e-9; it++) {
      let want = 0; for (const m of cred) want += Math.max(0, Math.min(m.avail, m.q) - m.got);
      if (want <= 1e-9) break;
      const f = Math.min(1, room / want);
      for (const m of cred) { const w = Math.max(0, Math.min(m.avail, m.q) - m.got); m.got += w * f; }
      room = cap; for (const m of cred) room -= m.got;
    }
    let L = 0; for (const m of cred) L += m.got;

    // ---- payments and fees
    const slots = L * LEAF;
    const fakeServed = Math.min(fakes, slots);
    const realServed = Math.min(D, slots - fakeServed);
    const r = D > 0 ? clearing(realServed / D) : STD;
    const fees = realServed * r * MEANV + fakeServed * FEEMAX * MEANV;
    const nTx = realServed + fakeServed;
    const feeMeasured = nTx > 0 ? (realServed * Math.log(r) + fakeServed * Math.log(FEEMAX)) / nTx : Math.log(STD);
    const full = cap > 0 ? L / cap : 0;

    // fee split; NEW sends half into a pool paid 1/32 per block
    let direct = fees;
    if (NEW) { pool += fees * 0.5; direct = fees * 0.5; const pay = pool / 32; pool -= pay; direct += pay; }
    const proverPart = direct * PROVER, minerPart = direct - proverPart;
    for (const m of cred) { const g = L > 0 ? proverPart * m.got / L : 0; m.inc += g; m.leaves += m.got; }
    if (big) {
      if (minerBig) big.inc += minerPart;
      if (sc.attack && t >= EVENT) acc.attPaid += fakeServed * FEEMAX * MEANV;
    }

    // ---- resize
    if (rule === 'old') {
      const i = t % DAY; if (nh >= DAY) { sumF -= histF[i]; sumU -= histU[i]; } else nh++;
      histF[i] = feeMeasured; histU[i] = full; sumF += feeMeasured; sumU += full;
      const fAvg = Math.exp(sumF / nh), uAvg = sumU / nh;
      if (uAvg > 0.9 && fAvg > STD * 1.02) cap *= 1.005;
      else if (uAvg < 0.9 || fAvg < STD) cap *= 0.995;
    } else {
      emaF += alpha * (feeMeasured - emaF); emaU += alpha * (full - emaU);
      const fAvg = Math.exp(emaF);
      if (emaU > 0.9 && fAvg > STD * 1.02) cap *= 1.0012;
      else if (fAvg > STD * 1.02) { /* fees high but not full: too few provers, hold */ }
      else if (emaU < 0.75) cap *= 0.9988;
    }
    cap = Math.min(CAPMAX, Math.max(CAPMIN, cap));

    // ---- minter entry and exit (profit-driven)
    if (sc.entry) {
      let inc = 0, cost = 0;
      for (const m of cred) if (!m.big) { inc += L > 0 ? proverPart * m.got / L : 0; cost += (P > 0 ? madeProofs * m.p / P : 0) * COST; }
      const small = alive.filter(m => !m.big).length;
      const marg = cost > 0 ? inc / cost : (inc > 0 ? 3 : 1);
      mEma += 0.02 * (Math.min(5, marg) - mEma);
      if (mEma > 1.3) { const k = Math.max(1, Math.round(0.003 * small)); for (let i = 0; i < k; i++) add(POWER, 1); }
      else if (mEma < 0.9 && small > 5) { const k = Math.max(1, Math.round(0.003 * small)); let d = 0; for (const m of M) if (m.alive && !m.big && d < k) { m.alive = false; d++; } }
    }

    // ---- bookkeeping
    if (t >= EVENT) {
      acc.served += realServed; acc.demand += D; acc.proofs += madeProofs; acc.unique += unique;
      acc.feeLog += Math.log(r) * realServed; acc.feeN += realServed;
      for (const m of cred) { acc.allLeaves += m.got; if (m.big) acc.bigLeaves += m.got; }
      if (acc.adapt === null && t > EVENT + 10 && D > 0 && realServed / D >= 0.9) acc.adapt = t - EVENT;
      if (t >= BLOCKS - 3 * DAY) { acc.capPost.push(cap); acc.servedPost.push(D > 0 ? realServed / D : 1); }
    }
    if (t % 6 === 0) series.push({ t, cap: +cap.toFixed(1), L: +L.toFixed(1), fee: +(r * 100).toFixed(2), served: D > 0 ? +(realServed / D).toFixed(3) : 1, minters: alive.length, cred: cred.length });
  }
  // results
  const capP = acc.capPost, mean = capP.reduce((a, b) => a + b, 0) / capP.length;
  const res = {
    servedPct: 100 * acc.served / acc.demand,
    medianFee: 100 * Math.exp(acc.feeLog / Math.max(1, acc.feeN)),
    capMean: mean, capSwing: 100 * (Math.max(...capP) - Math.min(...capP)) / mean,
    wastePct: acc.proofs > 0 ? 100 * (acc.proofs - acc.unique) / acc.proofs : 0,
    adaptBlocks: acc.adapt,
    minters: M.filter(m => m.alive).length,
  };
  if (big) {
    const all = M.filter(m => m.alive || m.left);
    let H = 0; for (const m of all) H += m.hash;
    res.bigHashPct = 100 * big.hash / H;
    res.bigLeafPct = 100 * acc.bigLeaves / Math.max(1, acc.allLeaves);
    let totInc = 0; for (const m of M) totInc += m.inc;
    res.bigIncPct = 100 * big.inc / totInc;
  }
  if (sc.attack) { res.attPaidPerDay = acc.attPaid / ((BLOCKS - EVENT) / DAY); res.attIncTotal = big.inc; }
  return { res, series };
}

const SCEN = {
  S0: { name: 'Baseline: daily cycle only', entry: true },
  S1: { name: 'Volume x10, same minters', volX: 10 },
  S1b: { name: 'Volume x10, minters may join', volX: 10, entry: true },
  S2: { name: 'Minters x10, same volume', mintersX: 10 },
  S3: { name: 'Half the minters leave (day 3), return (day 5)', halfLeave: true },
  S4: { name: 'One big prover: 50% of hashing, fills whole blocks, mines 50% and prefers its own leaves', entry: true, big: { power: 1024, hash: 60, seal: 0.5 } },
  S5: { name: 'Fake-fee attack: 30% miner-minter adds 400 fake 6%-fee payments per block', entry: true, big: { power: 300, hash: 26, seal: 0.3 }, attack: { fakes: 400 } },
  S5n: { name: 'Same 30% miner-minter, no attack (reference)', entry: true, big: { power: 300, hash: 26, seal: 0.3 } },
};

module.exports = { run, SCEN, DAY, EVENT, BLOCKS, W0, B };

if (require.main === module) {
  const out = {};
  const fmt = (x, d = 1) => (x === null || x === undefined) ? '-' : (typeof x === 'number' ? x.toFixed(d) : x);
  const lines = [];
  for (const [k, sc] of Object.entries(SCEN)) {
    out[k] = { name: sc.name };
    lines.push(`\n${k}: ${sc.name}`);
    for (const rule of ['old', 'new']) {
      // average results over seeds
      const runs = [1, 2, 3, 4, 5].map(s => run(sc, rule, s));
      const avg = {};
      for (const key of Object.keys(runs[0].res)) {
        const v = runs.map(r => r.res[key]).filter(x => x !== null && x !== undefined);
        avg[key] = v.length ? v.reduce((a, b) => a + b, 0) / v.length : null;
      }
      out[k][rule] = { res: avg, series: runs[0].series };
      const r = avg;
      lines.push(`  ${rule.toUpperCase()}: served ${fmt(r.servedPct)}%  fee ${fmt(r.medianFee, 2)}%  cap ${fmt(r.capMean, 0)} (swing ${fmt(r.capSwing, 0)}%)  waste ${fmt(r.wastePct)}%  adapt ${fmt(r.adaptBlocks, 0)} blk  minters ${fmt(r.minters, 0)}` +
        (r.bigLeafPct !== undefined ? `  big: hash ${fmt(r.bigHashPct)}% leaves ${fmt(r.bigLeafPct)}% income ${fmt(r.bigIncPct)}%` : '') +
        (r.attPaidPerDay !== undefined ? `  attacker fake fees ${fmt(r.attPaidPerDay, 0)} Sen/day` : ''));
    }
  }
  // attack cost: attacker income with attack minus without, minus fees paid
  for (const rule of ['old', 'new']) {
    const a = out.S5[rule].res, n = out.S5n[rule].res;
    const days = (BLOCKS - EVENT) / DAY;
    const net = (a.attPaidPerDay * days - (a.attIncTotal - n.attIncTotal)) / days;
    out.S5[rule].res.attNetCostPerDay = net;
    out.S5[rule].res.attRecoveredPct = 100 * (1 - net / a.attPaidPerDay);
    lines.push(`S5 ${rule.toUpperCase()}: attacker net cost ${net.toFixed(0)} Sen/day, recovers ${out.S5[rule].res.attRecoveredPct.toFixed(0)}% of fake fees`);
  }
  // credential entry: N equal minters
  lines.push('\nCredential entry, N equal minters, 100 tickets/block');
  out.entry = [];
  for (const N of [1e3, 1e4, 1e5, 1e6]) {
    const row = { N };
    for (const [lab, W] of [['w1000', 1000], ['w4000', 4000]]) row[lab] = 100 * (1 - Math.exp(-B * W / N));
    row.waitHours = N / B * 150 / 3600;
    out.entry.push(row);
    lines.push(`  N=${N}: credentialed ${row.w1000.toFixed(1)}% (window 1000) / ${row.w4000.toFixed(1)}% (window 4000); first ticket after ~${row.waitHours.toFixed(1)} h`);
  }
  require('fs').writeFileSync(__dirname + '/results.json', JSON.stringify(out));
  require('fs').writeFileSync(__dirname + '/results.txt', lines.join('\n') + '\n');
  console.log(lines.join('\n'));
}
