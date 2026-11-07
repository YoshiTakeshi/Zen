// Receiver-based counting on top of the day window + anchor + day clip (daywin.js).
// Both sides sign, the receiver pays the fee. A Sen-priced payment counts toward S only if
//   - its receiver is bonded: has held at least BOND for 7 days, and
//   - the receiver has not passed its cap: at most CAP of the day's counted Sen payments.
// Honest receivers: SHOPS accounts, daily Sen-priced payments Zipf (exponent 1) over 300,000 a
// day (Jen at 1M payments a day, 30% priced in Sen). A shop is bonded if it takes at least
// BONDED_MIN payments a day (a shop that busy keeps the bond as working balance).
// Attacker: K bonded receivers of his own, each filled to the cap with fake payments every day.
'use strict';
const { run } = require('./daywin.js');
const SEN_DAY = 300000, SHOPS = 50000, BONDED_MIN = 20;
const pct = x => (100 * (Math.exp(x) - 1)).toFixed(0) + '%';
const usd = x => '$' + (x >= 1e6 ? (x / 1e6).toFixed(1) + 'M' : x >= 1e3 ? Math.round(x / 1e3) + 'k' : Math.round(x));
// honest receivers
let H = 0; const sizes = [];
for (let i = 1; i <= SHOPS; i++) sizes.push(1 / i);
const zs = sizes.reduce((a, b) => a + b);
const n = sizes.map(s => s / zs * SEN_DAY);
function honestCounted(cap) { let c = 0, bonded = 0; for (const x of n) if (x >= BONDED_MIN) { c += Math.min(x, cap); bonded++; } return { c, bonded }; }
const strategies = [];
for (const sgn of [1, -1]) for (const off of [0.3, 0.7, 1.3, 1.5, 3]) strategies.push({ sgn, off });
function worst(att, dur) {
  let best = null;
  for (const st of strategies) { const r = run({ att, dur, anchor: true, clip: true, ...st }); if (!best || r.maxDev > best.maxDev) best = r; }
  return best.maxDev;
}
const L = [];
L.push('Receiver cap + bond, with the day window + anchor + day clip. Jen at 1M payments a day, 300,000 Sen-priced.');
for (const CAPF of [0.001, 0.0003]) {
  const cap = CAPF * SEN_DAY;
  const h = honestCounted(cap);
  L.push(`\nCap ${CAPF * 100}% of a day's Sen payments (${cap} payments per receiver a day). Honest: ${h.bonded} of ${SHOPS} shops bonded, ${Math.round(h.c).toLocaleString('en-US')} of ${SEN_DAY.toLocaleString('en-US')} Sen payments counted (${(100 * h.c / SEN_DAY).toFixed(0)}%).`);
  L.push('attacker receivers'.padEnd(20) + 'share of counted'.padStart(18) + 'moves S 7d'.padStart(12) + 'moves S 30d'.padStart(13) + 'bonds ($1,000 each)'.padStart(21) + 'fees 7d'.padStart(10));
  for (const K of [5, 10, 25, 50, 100, 200, 500]) {
    const A = K * cap, r = A / h.c, e = A / (A + h.c);
    const att = 0.3 * r / (1 + 0.3 * r);                 // daywin attacker share giving the same fake / honest Sen ratio
    const m7 = worst(att, 7), m30 = worst(att, 30);
    const fees = A * 7 * 5 * 0.27 * 0.01 * 0.5;          // small fakes, about 1/4 of a $5 typical payment, 1% fee, half lost
    L.push(String(K).padEnd(20) + ((100 * e).toFixed(1) + '%').padStart(18) + pct(m7).padStart(12) + pct(m30).padStart(13) + usd(K * 1000).padStart(21) + usd(fees).padStart(10));
  }
}
L.push('\nWithout receiver counting (from daycost.txt): 5% of all payments moves S 13% in 7 days and 31% in 30 days, for about $3k and $10k in fees.');
require('fs').writeFileSync(__dirname + '/results/receivers.txt', L.join('\n') + '\n');
console.log(L.join('\n'));
