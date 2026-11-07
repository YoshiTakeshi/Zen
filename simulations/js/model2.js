// Two coins, one value: physical Sen and electronic Jen side by side.
//
// Unit of value: minutes of labour (the original page: 1 Sen ~ a minute).
// Daily steps over `years`.
//
// Jen:  the protocol sets 1 JEN = the Bronze-typical payment V, whatever the
//       supply or the speculation (measured in the block-level runs: within ~2%).
//       Here J = V x a small daily noise, and V may drift (`vDrift` per year).
// Sen:  N coins circulate; their value s = what people want to hold in Sen / N.
//       - Anyone can print a coin at cost c (copper + printing): when a coin is
//         worth more than c, printers add coins (up to `printCap` of the stock a day).
//       - When a coin is worth less than its copper m, coins are melted.
//       - Coins wear out slowly.
// People: a share f of commerce uses the 1:1 convention (prices in units, pay
//       with a Sen coin or 1 JEN). They split what they hold between Sen and Jen,
//       and switch toward Jen when they expect it to rise (mood) and back.
// Switch counters: shops of the convention swap 1 Sen <-> 1 JEN with what they
//       hold (`reserve` x their share of the economy, half in coins, half in Jen).
//       When a coin is worth less than 1 JEN, people bring coins and take Jen;
//       when it is worth more, they take coins for Jen. Printers and melters use
//       the counters too when it pays (print at c, swap for 1 JEN; buy a coin for
//       1 JEN, melt it for m).
// Question: does a Sen coin end up worth 1 JEN?

function rng2(seed) {
  let t = seed >>> 0;
  const u = () => { t += 0x6D2B79F5; let r = Math.imul(t ^ (t >>> 15), 1 | t); r ^= r + Math.imul(r ^ (r >>> 7), 61 | r); return ((r ^ (r >>> 14)) >>> 0) / 4294967296; };
  return () => Math.sqrt(-2 * Math.log(u() + 1e-12)) * Math.cos(2 * Math.PI * u());
}

const DEFAULTS2 = {
  years: 3,
  V: 1,            // typical payment, minutes of labour (so 1 JEN = V)
  vDrift: 0,       // change of V per year (e.g. 0.3 = +30%/year)
  m: 0.1,          // copper in a 2 g Sen, minutes of labour
  c: 2,            // cost to print one Sen, minutes of labour
  schedule: [[0, 0.02], [6, 0.05], [12, 0.10], [18, 0.20], [24, 0.35], [30, 0.50]], // [month, share using 1:1]
  swing: 0.3,      // how far switching moves holdings (share of their money moved by a strong mood)
  vol: 1.0,        // speculative mood volatility per year
  meanRevDays: 60,
  reserve: 0.2,    // counters' stock, x their share of the economy's money
  printCap: 0.01,  // printers can add at most 1% of the coins a day
  wear: 0.02,      // coins lost or worn out per year
  seed: 11,
};

function simulate2(p0 = {}) {
  const p = { ...DEFAULTS2, ...p0 };
  const days = Math.round(p.years * 365);
  const g = rng2(p.seed);
  const M0 = 1e6; // money people of the convention hold, minutes of labour, at f = 100%
  let mood = 0, V = p.V;
  const fAt = (d) => { let f = 0; for (const [mo, v] of p.schedule) if (d >= mo * 30.42) f = v; return f; };
  // start: coins in circulation worth their making cost, counters empty until people join
  let f = fAt(0);
  let N = f * M0 * 0.5 / p.c, Rs = 0, Rj = 0, fPrev = 0;
  const out = [];
  let printed = 0, melted = 0, swapsIn = 0, swapsOut = 0;
  for (let d = 0; d < days; d++) {
    f = fAt(d);
    V = p.V * Math.pow(1 + p.vDrift, d / 365);
    mood += -mood / p.meanRevDays + p.vol * Math.sqrt(1 / 365) * g();
    const J = V * Math.exp(0.007 * g()); // 1 JEN, from the protocol
    // counters get stock as people join (half coins at the going value, half Jen)
    if (f > fPrev) { const add = (f - fPrev) * M0 * p.reserve; Rj += add / 2; Rs += add / 2 / J; }
    fPrev = f;
    // what people of the convention want to hold in Sen (the rest in Jen)
    const jenShare = Math.min(0.95, Math.max(0.05, 0.5 + p.swing * Math.tanh(mood * 2)));
    const Ds = f * M0 * (1 - jenShare);
    N *= 1 - p.wear / 365;
    let s = Ds / Math.max(N, 1e-9);
    // 1) switch counters: 1 Sen <-> 1 JEN
    if (f > 0) {
      if (s < J) { // coin worth less than 1 JEN: bring coins, take Jen
        const want = N - Ds / J, k = Math.min(want, Rj / J);
        N -= k; Rs += k; Rj -= k * J; swapsIn += k;
      } else if (s > J) { // coin worth more: take coins for Jen
        const want = Ds / J - N, k = Math.min(want, Rs);
        N += k; Rs -= k; Rj += k * J; swapsOut += k;
      }
      s = Ds / Math.max(N, 1e-9);
    }
    // 2) printers: print at c when a coin is worth more than c, or when 1 JEN > c at a counter
    const cap = p.printCap * Math.max(N + Rs, 1);
    if (s > p.c) { const k = Math.min(cap, N - Ds / p.c < 0 ? Ds / p.c - N : 0); N += k; printed += k; s = Ds / N; }
    if (f > 0 && J > p.c && Rj > 0) { const k = Math.min(cap, Rj / J); Rs += k; Rj -= k * J; printed += k; }
    // 3) melters: melt when the copper is worth more than the coin
    if (s < p.m) { const k = Math.max(0, N - Ds / p.m); N -= k; melted += k; s = Ds / Math.max(N, 1e-9); }
    if (f > 0 && J < p.m && Rs > 0) { const k = Rs; Rs = 0; Rj += k * J; melted += k; }
    if (d % 1 === 0) out.push({ day: d + 1, f, J, s, ratio: s / J, Rs: Rs * J, Rj, mood, jenShare });
  }
  return { series: out, printed, melted, swapsIn, swapsOut };
}

if (typeof module !== "undefined") module.exports = { simulate2, DEFAULTS2 };
