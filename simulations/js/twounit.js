// Two units on one chain (Jen): JEN = the typical ordinary payment (W, grams),
// SEN unit = grams per Sen (S), read from Sen-priced payments compared with
// ordinary ones. Balances stay in grams; 1 JEN = W / S Sen.
//
//   W: middle-20% average of the ordinary payments (each counted once), window
//      as in pegdef2, at most 1% a block. No anchor: JEN is a floating unit.
//   S: the Jen-0.12 peg design: typical ordinary value / typical Sen price,
//      middle-20% averages, floor, speed by Sen share, anchor 0.005% a block,
//      band +-10%.
// One block = 150 s; 100 honest payments a block; goods lognormal, median 2 Sen;
// a Sen is worth U grams. Attack: 7 days, the attacker's payments are a share
// of all payments, either Sen-priced (the SEN side) or ordinary (the gram side),
// at the size that pushes hardest.
'use strict';
function rngf(seed) { let s = seed >>> 0; return () => { s = (s + 0x6D2B79F5) >>> 0; let t = s; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; }; }
const BLOCKS = 8000, DAY = 576, N = 100, STEP = 0.01, ALPHA = 0.1, LONG = 1 - Math.pow(0.5, 1 / 2000);
const ANCHOR = 0.00005, BAND = Math.log(1.1), SHARE_FULL = 0.30, SHARE_MIN = 0.02;
function mid(L) { if (!L.length) return null; L.sort((a, b) => a - b); const n = L.length, lo = 0.4 * n, hi = 0.6 * n; let s = 0, w = 0; for (let i = 0; i < n; i++) { const a = Math.max(i, lo), b = Math.min(i + 1, hi); if (b > a) { s += (b - a) * L[i]; w += b - a; } } return w ? s / w : L[n >> 1]; }

function run(o, seed = 1) {
  const R = rngf(seed);
  const gauss = () => Math.sqrt(-2 * Math.log(R() + 1e-12)) * Math.cos(2 * Math.PI * R());
  let U = 0, size = Math.log(2);                  // log grams per Sen, log median goods (Sen)
  let logS = 0, A = 0, logW = Math.log(2.6);     // S starts at the peg, W at the honest typical payment
  let nG = 0, dG = 0, nD = 0, dD = 0, nW = 0, dW = 0;
  let lG = Math.log(2.6), lD = Math.log(2.6), sS = o.share, sL = o.share;
  const out = { maxS: 0, maxW: 0, wTrack: null };
  for (let b = 0; b < BLOCKS; b++) {
    if (o.habit && b === 2000) size += Math.log(2);   // people start buying twice as much per payment
    const att = o.att > 0 && b >= 2000 && b < 2000 + 7 * DAY;
    const LG = [], LD = [];
    for (let i = 0; i < N; i++) {
      const v = Math.exp(size + gauss());
      if (R() < o.share) { const k = v < 1 ? Math.max(1, Math.round(v * 6)) / 6 : Math.round(v); LD.push(Math.log(k)); }
      else LG.push(Math.log(v) + U + 0.005 * gauss());
    }
    if (att) {
      const na = Math.round(N * o.att / (1 - o.att));
      const c = o.side === 'D' ? lD : lG;
      for (let i = 0; i < na; i++) {
        const l = o.off === 'x' ? c + o.sgn * 8 : c + o.sgn * o.off;
        (o.side === 'D' ? LD : LG).push(l);
      }
    }
    const sh = LD.length / (LD.length + LG.length);
    sS += ALPHA * (sh - sS); sL += LONG * (sh - sL);
    // W: typical ordinary payment (no floor, no anchor)
    const mw = mid(LG.slice());
    if (mw !== null) { nW = (1 - ALPHA) * nW + ALPHA * mw; dW = (1 - ALPHA) * dW + ALPHA; logW += Math.max(-STEP, Math.min(STEP, nW / dW - logW)); }
    // S: the peg
    const fl = (L, cen) => L.filter(x => x >= cen - Math.log(4));
    const mG = mid(fl(LG, lG)), mD = mid(fl(LD, lD));
    if (mG !== null) { nG = (1 - ALPHA) * nG + ALPHA * mG; dG = (1 - ALPHA) * dG + ALPHA; }
    if (mD !== null) { nD = (1 - ALPHA) * nD + ALPHA * mD; dD = (1 - ALPHA) * dD + ALPHA; }
    if (dG > 0 && dD > 0) {
      const gm = nG / dG, dm = nD / dD;
      lG += LONG * (gm - lG); lD += LONG * (dm - lD);
      const s = Math.min(sS, sL);
      const step = s < SHARE_MIN ? 0 : STEP * Math.min(1, s / SHARE_FULL);
      logS += Math.max(-step, Math.min(step, (gm - dm) - logS));
      logS = Math.max(A - BAND, Math.min(A + BAND, logS));
      A += Math.max(-ANCHOR, Math.min(ANCHOR, logS - A));
    }
    // measures: 1 SEN unit in physical Sen = S / U; 1 JEN against the honest typical payment
    const honestTypical = size + 0.25 + U;           // log of the honest typical ordinary payment (median of exp(size+N(0,1)) ~ size; small rounding offset)
    if (att) { out.maxS = Math.max(out.maxS, Math.abs(logS - U)); out.maxW = Math.max(out.maxW, Math.abs(logW - (Math.log(2) + U))); }
    if (o.habit && b >= 2000 && out.wTrack === null && Math.abs(logW - (size + U)) < Math.log(1.05)) out.wTrack = b - 2000;
    if (o.habit && b >= 2000) out.maxS = Math.max(out.maxS, Math.abs(logS - U));
  }
  return out;
}

module.exports = { run };
if (require.main === module) {
  const pct = x => x >= 9 ? 'runaway' : (100 * (Math.exp(x) - 1)).toFixed(0) + '%';
  const lines = [];
  const strategies = [];
  for (const side of ['D', 'G']) for (const sgn of [1, -1]) for (const off of [0.3, 0.7, 1.5, 'x']) strategies.push({ side, sgn, off });
  for (const share of [0.30, 0.10]) {
    lines.push(`\nHonest Sen-priced share ${share * 100}%: largest move in a 7-day attack (worst strategy for each side)`);
    lines.push('attacker'.padEnd(10) + 'attacks Sen payments: SEN unit / JEN'.padEnd(40) + 'attacks ordinary payments: SEN unit / JEN');
    for (const a of [0.02, 0.05, 0.10, 0.20, 0.40]) {
      const worst = side => { let bs = 0, bw = 0; for (const st of strategies.filter(x => x.side === side)) { const r = run({ share, att: a, ...st }); bs = Math.max(bs, r.maxS); bw = Math.max(bw, r.maxW); } return [bs, bw]; };
      const [dS, dW] = worst('D'), [gS, gW] = worst('G');
      lines.push(`${(a * 100 + '%').padEnd(10)}${(pct(dS) + ' / ' + pct(dW)).padEnd(40)}${pct(gS) + ' / ' + pct(gW)}`);
    }
  }
  const h = run({ share: 0.30, att: 0, habit: true });
  lines.push(`\nSpending habits change (payments twice as large from block 2000), no attack:`);
  lines.push(`  JEN follows the new typical payment within 5% after ${h.wTrack} blocks (${(h.wTrack / DAY).toFixed(2)} days); the SEN unit moves at most ${pct(h.maxS)}`);
  require('fs').writeFileSync(__dirname + '/results/twounit.txt', lines.join('\n') + '\n');
  console.log(lines.join('\n'));
}
