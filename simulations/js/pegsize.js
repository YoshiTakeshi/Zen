// Block resize that steers W (the typical on-chain payment, in Sen) toward the SEN unit.
// The gap g = log(W / S) is read every block. Resize rules:
//   base     Jen-0.10 style: grow 0.3% a block when blocks run full with a backlog, shrink
//            0.12% when they run under 60% full.
//   pegsize  base + a peg term: grow when W > S (admitting smaller payments lowers W),
//            shrink when W < S (pricing out the smallest raises W), up to 0.3% a block.
// How block size can move W: minters fill a block with the payments paying the largest fee
// per leaf. With percentage fees that is the largest payments, so a small block carries
// only large payments and a big block lets small ones in. A payment that waits more than 8
// blocks leaves the chain (paid in a channel or not at all).
// Units: values in physical Sen. S = the network's SEN unit (1 when read correctly).
// Demand: 200 payments a block, lognormal value, median Dm Sen, sigma 1.5.
'use strict';
function rngf(seed) { let s = seed >>> 0; return () => { s = (s + 0x6D2B79F5) >>> 0; let t = s; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; }; }
const DAY = 576, N = 200, ALPHA = 0.1, STEP = 0.01, SIG = 1.5, EXPIRE = 8;
const GROW = 0.003, SHRINK = 0.0012, PEG = 0.003, CMIN = 8, CMAX = 1 << 16;
function mid(L) { if (!L.length) return null; L.sort((a, b) => a - b); const n = L.length, lo = 0.4 * n, hi = 0.6 * n; let s = 0, w = 0; for (let i = 0; i < n; i++) { const a = Math.max(i, lo), b = Math.min(i + 1, hi); if (b > a) { s += (b - a) * L[i]; w += b - a; } } return w ? s / w : L[n >> 1]; }

function run(o, seed = 7) {
  const R = rngf(seed);
  const gauss = () => Math.sqrt(-2 * Math.log(R() + 1e-12)) * Math.cos(2 * Math.PI * R());
  const BLOCKS = o.blocks || 12 * DAY, T0 = 4 * DAY;              // events start on day 4
  let logDm = Math.log(o.dm), C = o.c0 || 256, logW = Math.log(o.dm), nW = 0, dW = 0, full = 0.5;
  let logS = 0;                                                     // S read correctly
  let pool = [];
  const st = { served: 0, arrived: 0, wait: 0, n: 0 };
  const out = { series: [], before: null, during: null, after: null };
  const win = () => ({ served: 0, arrived: 0, gap: 0, cap: 0, k: 0, maxGap: 0, minCap: Infinity, maxCap: 0 });
  const W = { before: win(), during: win(), after: win() };
  for (let b = 0; b < BLOCKS; b++) {
    const ev = b >= T0, evEnd = T0 + (o.evDays || 7) * DAY, during = ev && b < evEnd;
    // genuine changes
    if (o.event === 'copper' && b === T0) logDm -= Math.log(1.5);  // a Sen worth 1.5x: goods cost fewer Sen
    if (o.event === 'habit' && b === T0) logDm += Math.log(2);     // people pay twice as much each time
    // attacks
    let attS = 0;
    if (o.event === 'attackS' && during) attS = Math.min(Math.log(1.37), Math.log(1.37) * (b - T0) / (7 * DAY) * 3); // S pushed up to the band (+37%)
    if (o.event === 'attackSdown' && during) attS = -Math.min(Math.log(1.37), Math.log(1.37) * (b - T0) / (7 * DAY) * 3);
    const S = Math.exp(logS + attS);
    // arrivals
    const minPay = Math.exp(logW) / 600;
    for (let i = 0; i < N; i++) { const v = Math.exp(logDm + SIG * gauss()); if (v >= minPay) pool.push({ v, age: 0, h: 1 }); st.arrived++; if (during) W.during.arrived++; else if (ev) W.after.arrived++; else if (b >= T0 - 2 * DAY) W.before.arrived++; }
    if ((o.event === 'attackWup' || o.event === 'attackWdown') && during) {
      const na = Math.round(N * 0.2 / 0.8);                         // attacker = 20% of payments
      for (let i = 0; i < na; i++) pool.push({ v: Math.exp(logW + (o.event === 'attackWup' ? 1.5 : -1.5)), age: 0, h: 0 });
    }
    // fill the block: largest fee per leaf first
    pool.sort((a, b) => b.v - a.v);
    const k = Math.min(pool.length, Math.floor(C));
    const inc = pool.slice(0, k);
    let rest = pool.slice(k);
    const backlog = rest.length;
    for (const p of rest) p.age++;
    pool = rest.filter(p => p.age <= EXPIRE);
    const honestInc = inc.filter(p => p.h).length;
    const bucket = during ? W.during : ev ? W.after : (b >= T0 - 2 * DAY ? W.before : null);
    // W: middle-20% of the included payments, window, 1% step
    const m = mid(inc.map(p => Math.log(p.v)));
    if (m !== null) { nW = (1 - ALPHA) * nW + ALPHA * m; dW = (1 - ALPHA) * dW + ALPHA; logW += Math.max(-STEP, Math.min(STEP, nW / dW - logW)); }
    // resize
    full += 0.125 * (k / C - full);
    let step = 0;
    if (full > 0.9 && backlog > 0.05 * C) step = GROW; else if (full < 0.6) step = -SHRINK;
    const gap = logW - Math.log(S);
    if (o.rule === 'pegsize') step += PEG * Math.max(-1, Math.min(1, gap / Math.log(1.5)));
    C = Math.max(CMIN, Math.min(CMAX, C * Math.exp(step)));
    if (bucket) { bucket.served += honestInc; bucket.gap += gap; bucket.cap += C; bucket.k++; bucket.maxGap = Math.max(bucket.maxGap, Math.abs(gap)); bucket.minCap = Math.min(bucket.minCap, C); bucket.maxCap = Math.max(bucket.maxCap, C); }
    if (b % 24 === 0) out.series.push([b, +Math.exp(logW).toFixed(3), +S.toFixed(3), Math.round(C)]);
  }
  for (const key of ['before', 'during', 'after']) { const x = W[key]; out[key] = { served: x.arrived ? x.served / x.arrived : 0, ratio: Math.exp(x.gap / (x.k || 1)), cap: x.cap / (x.k || 1), maxGap: x.maxGap, minCap: x.minCap, maxCap: x.maxCap }; }
  out.final = { W: Math.exp(logW), S: Math.exp(logS), C };
  return out;
}
module.exports = { run };

if (require.main === module) {
  const f = (x, d = 2) => x.toFixed(d);
  const pc = x => (100 * x).toFixed(0) + '%';
  const L = [];
  L.push('1. Can resizing make 1 JEN (the typical on-chain payment) = 1 SEN unit? Steady state, no events (last 2 days of a quiet run).');
  L.push('   Demand median = typical payment people want to make, in Sen. W/S = JEN in Sen. served = honest payments that got on chain.');
  L.push('Dm (Sen)'.padEnd(10) + 'base: W/S   blocks   served'.padEnd(32) + 'pegsize: W/S   blocks   served');
  for (const dm of [0.3, 1, 3, 10, 180]) {
    const a = run({ dm, rule: 'base', event: 'none' }), p = run({ dm, rule: 'pegsize', event: 'none' });
    L.push(String(dm).padEnd(10) + `${f(a.before.ratio).padStart(9)} ${Math.round(a.before.cap).toString().padStart(8)} ${pc(a.before.served).padStart(8)}`.padEnd(32) + `${f(p.before.ratio).padStart(12)} ${Math.round(p.before.cap).toString().padStart(8)} ${pc(p.before.served).padStart(8)}`);
  }
  const evs = [
    ['habit', 'genuine: people pay twice as much (W should rise, S not)'],
    ['copper', 'genuine: copper up 50% (a Sen worth more, S fixed in Sen, goods fewer Sen)'],
    ['attackS', 'attack: S pushed up 37% (the band limit) for 7 days'],
    ['attackSdown', 'attack: S pushed down 27% for 7 days'],
    ['attackWup', 'attack: 20% fake large ordinary payments for 7 days'],
    ['attackWdown', 'attack: 20% fake small ordinary payments for 7 days'],
  ];
  for (const dm of [1, 180]) {
    L.push(`\n2. Events with demand median ${dm} Sen (7 days from day 4). Mean JEN in Sen (W/S) and honest payments served during the event; largest |gap|; block size range.`);
    L.push('event'.padEnd(14) + 'rule'.padEnd(9) + 'W/S before'.padStart(11) + 'W/S during'.padStart(11) + 'max gap'.padStart(9) + 'served before'.padStart(15) + 'served during'.padStart(15) + 'blocks during (min-max)'.padStart(26));
    for (const [ev] of evs) for (const rule of ['base', 'pegsize']) {
      const r = run({ dm, rule, event: ev });
      L.push(ev.padEnd(14) + rule.padEnd(9) + f(r.before.ratio).padStart(11) + f(r.during.ratio).padStart(11) + pc(Math.exp(r.during.maxGap) - 1).padStart(9) + pc(r.before.served).padStart(15) + pc(r.during.served).padStart(15) + `${Math.round(r.during.minCap)}-${Math.round(r.during.maxCap)}`.padStart(26));
    }
    L.push('  ' + evs.map(e => `${e[0]} = ${e[1]}`).join('\n  '));
  }
  require('fs').writeFileSync(__dirname + '/results/pegsize.txt', L.join('\n') + '\n');
  console.log(L.join('\n'));
}
