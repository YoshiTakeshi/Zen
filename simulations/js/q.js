const { run, SCEN } = require('./sim.js');
const ks = process.argv.slice(2).length ? process.argv.slice(2) : ['S0', 'S1'];
for (const k of ks) for (const rule of ['old', 'new']) {
  const t0 = Date.now(); const r = run(SCEN[k], rule, 1);
  console.log(k, rule, Date.now() - t0, 'ms', JSON.stringify(r.res, (a, v) => typeof v === 'number' ? +v.toFixed(2) : v));
  const s = r.series; for (const i of [0, 280, 290, 330, 480, 600, 700, 900, s.length - 1]) if (s[i]) console.log('   ', JSON.stringify(s[i]));
}
