'use strict';
// The explorer page of a Zen node. It reads the node's own /api and builds the page with createElement and textContent only
// (nothing from the chain is ever parsed as markup).

const view = document.getElementById('view');
const alertBox = document.getElementById('alert');
const chipBox = document.getElementById('chain-chip');
const METALS = { 1: 'gold', 2: 'silver', 3: 'copper' };
// the metallic ratio of each chain (SPEC 5.4): golden, silver, bronze
const RATIO = { 1: (1 + Math.sqrt(5)) / 2, 2: 1 + Math.SQRT2, 3: (3 + Math.sqrt(13)) / 2 };
let known = { tip: null };           // the tip we last drew, to mark new blocks

function h(tag, attrs, ...kids) {
  const e = document.createElement(tag);
  for (const k in attrs || {}) {
    const v = attrs[k];
    if (v === false || v == null) continue;
    if (k === 'class') e.className = v; else e.setAttribute(k, v);
  }
  for (const kid of kids.flat()) { if (kid == null || kid === false) continue; e.append(kid.nodeType ? kid : document.createTextNode(String(kid))); }
  return e;
}
const show = (...kids) => view.replaceChildren(...kids.flat(Infinity).filter((k) => k != null && k !== false));
const svg = (tag, attrs, ...kids) => {
  const e = document.createElementNS('http://www.w3.org/2000/svg', tag);
  for (const k in attrs || {}) e.setAttribute(k, attrs[k]);
  for (const kid of kids) if (kid) e.append(kid);
  return e;
};
class NetErr extends Error {}
async function api(path) {
  let r;
  try { r = await fetch('/api/' + path, { cache: 'no-store' }); } catch (e) { throw new NetErr('offline'); }
  const j = await r.json().catch(() => ({}));
  if (!r.ok) throw new Error(j.error || ('The node answered ' + r.status));
  return j;
}
const n0 = (x) => Number(x).toLocaleString('en-US');
// grams: thousands separators, at most `dp` decimals, at least two
function grams(s, dp = 4) {
  const [i, f = ''] = String(s).split('.');
  let fr = f.slice(0, dp).replace(/0+$/, '');
  if (fr.length < 2) fr = fr.padEnd(2, '0');
  return Number(i).toLocaleString('en-US') + '.' + fr;
}
const when = (t) => new Date(t * 1000).toISOString().replace('T', ' ').slice(0, 16) + ' UTC';
const short = (hex) => hex.slice(0, 10) + '…' + hex.slice(-6);
const link = (href, text, cls) => h('a', { href, class: cls }, text);

function setChain(st) {
  document.documentElement.dataset.chain = String(st.chain.id);
  chipBox.textContent = st.chain.name + ', ' + st.chain.metal;
  document.title = st.chain.name + ' node, block ' + n0(st.height);
}
function showAlert(msg) { alertBox.hidden = !msg; alertBox.textContent = msg || ''; }

// ---- the plot: what the raw reward curve has paid out by block height
function issuance(chainId) {
  const r = RATIO[chainId] || RATIO[3], a = Math.LN2 / Math.log(r), K = 100000;
  const prefix = new Float64Array(K + 1);
  for (let n = 1; n <= K; n++) prefix[n] = prefix[n - 1] + 2520 * Math.pow(n, -a);
  const tail = (N) => 2520 * (Math.pow(N, 1 - a) - Math.pow(K, 1 - a)) / (1 - a);
  const at = (N) => (N <= K ? prefix[Math.max(1, Math.floor(N))] : prefix[K] + tail(N));
  const ceiling = a > 1 ? prefix[K] + 2520 * Math.pow(K, 1 - a) / (a - 1) : null;
  return { at, ceiling };
}
function plot(st) {
  const W = 540, H = 320, L = 62, R = 14, T = 14, B = 40;
  const x0 = 0, x1 = 7, y0 = 3, y1 = 7;                       // 1 to 10 million blocks; 1 kg to 10 t
  const px = (lx) => L + (lx - x0) / (x1 - x0) * (W - L - R);
  const py = (ly) => H - B - (ly - y0) / (y1 - y0) * (H - T - B);
  const { at, ceiling } = issuance(st.chain.id);
  const pts = [];
  for (let t = 0; t <= 7.001; t += 0.05) pts.push(px(t).toFixed(1) + ',' + py(Math.log10(at(Math.pow(10, t)))).toFixed(1));
  const g = svg('svg', { viewBox: `0 0 ${W} ${H}`, role: 'img',
    'aria-label': 'Grams of metal the raw reward curve has paid out by block height, on logarithmic axes. ' + (ceiling ? 'It levels off near ' + n0(Math.round(ceiling)) + ' grams.' : 'It keeps growing without a ceiling.') });
  const xl = ['1', '10', '100', '1 k', '10 k', '100 k', '1 M', '10 M'], yl = ['1 kg', '10 kg', '100 kg', '1 t', '10 t'];
  for (let i = 0; i <= 7; i++) { g.append(svg('line', { class: 'grid', x1: px(i), x2: px(i), y1: T, y2: H - B }));
    const t = svg('text', { class: 'tick', x: px(i), y: H - B + 16, 'text-anchor': 'middle' }); t.textContent = xl[i]; g.append(t); }
  for (let j = 0; j <= 4; j++) { g.append(svg('line', { class: 'grid', x1: L, x2: W - R, y1: py(3 + j), y2: py(3 + j) }));
    const t = svg('text', { class: 'tick', x: L - 8, y: py(3 + j) + 4, 'text-anchor': 'end' }); t.textContent = yl[j]; g.append(t); }
  const xt = svg('text', { class: 'tick', x: (L + W - R) / 2, y: H - 6, 'text-anchor': 'middle' }); xt.textContent = 'block height'; g.append(xt);
  if (ceiling) {
    g.append(svg('line', { class: 'ceiling', x1: L, x2: W - R, y1: py(Math.log10(ceiling)), y2: py(Math.log10(ceiling)) }));
    const t = svg('text', { class: 'tick', x: W - R, y: py(Math.log10(ceiling)) - 6, 'text-anchor': 'end' }); t.textContent = 'ceiling, about ' + n0(Math.round(ceiling)) + ' g'; g.append(t);
  }
  g.append(svg('polyline', { class: 'curve', points: pts.join(' ') }));
  const N = Math.max(1, st.height), lx = Math.log10(N), ly = Math.log10(at(N));
  g.append(svg('line', { class: 'here-line', x1: px(lx), x2: px(lx), y1: py(ly), y2: H - B }));
  g.append(svg('circle', { class: 'here', cx: px(lx), cy: py(ly), r: 6 }));
  const right = lx > 4.5;
  const note = svg('text', { class: 'note', x: px(lx) + (right ? -12 : 12), y: py(ly) - 12, 'text-anchor': right ? 'end' : 'start' });
  note.textContent = 'block ' + n0(st.height); g.append(note);
  return g;
}

// ---- views
async function home() {
  const [st, bl, mp, pe] = await Promise.all([api('status'), api('blocks?limit=15'), api('mempool?limit=8'), api('peers')]);
  setChain(st);
  const fresh = known.tip !== null && known.tip !== st.tip;
  known.tip = st.tip;
  const caption = st.chain.name + ' pays by a curve that falls with block height. This is the total that curve has paid out by each height, before the random factor' +
    (issuance(st.chain.id).ceiling ? '. It levels off, so this chain has a ceiling.' : '. It keeps growing, so this chain has no ceiling.');
  const hero = h('section', { class: 'hero', 'aria-labelledby': 'hh' },
    h('div', null,
      h('p', { class: 'label', id: 'hh' }, 'Chain height'),
      h('div', { class: 'height' }, n0(st.height)),
      h('p', { class: 'muted' }, st.height ? 'Last block ' + when(st.tip_time) : 'No blocks yet'),
      h('dl', { class: 'facts' },
        h('dt', null, 'Paid out so far'), h('dd', null, grams(st.supply.issued_g, 2) + ' g'),
        h('dt', null, 'Waiting to mature'), h('dd', null, grams(st.supply.held_rewards_g, 2) + ' g, after ' + n0(st.maturity_blocks) + ' blocks'),
        h('dt', null, 'Next block pays up to'), h('dd', null, grams(st.next_block_curve_reward_g, 2) + ' g'),
        h('dt', null, 'Fee pool'), h('dd', null, grams(st.fee_pool_g, 4) + ' g'),
        h('dt', null, 'S, base units per coin'), h('dd', null, n0(st.sen_units)),
        h('dt', null, 'Peers'), h('dd', null, n0(st.peers)),
        h('dt', null, 'Payments waiting'), h('dd', null, n0(st.mempool)))),
    h('figure', { class: 'plot' }, plot(st), h('figcaption', null, caption)));

  const rows = bl.blocks.map((b) => h('tr', { class: fresh && b.height === st.height ? 'fresh' : null },
    h('td', null, link('#/block/' + b.height, n0(b.height))),
    h('td', null, when(b.time)),
    h('td', { class: 'num' }, n0(b.payments)),
    h('td', { class: 'num opt' }, n0(b.tickets)),
    h('td', { class: 'num opt' }, n0(b.size_bytes)),
    h('td', { class: 'opt' }, link('#/block/' + b.hash, short(b.hash), 'hash'))));
  const blocks = h('section', { 'aria-labelledby': 'bh' }, h('h2', { id: 'bh' }, 'Latest blocks'),
    bl.blocks.length
      ? h('div', { class: 'wrap' }, h('table', null,
          h('thead', null, h('tr', null, h('th', null, 'Height'), h('th', null, 'Time'), h('th', { class: 'num' }, 'Payments'), h('th', { class: 'num opt' }, 'Blows'), h('th', { class: 'num opt' }, 'Bytes'), h('th', { class: 'opt' }, 'Hash'))),
          h('tbody', null, rows)))
      : h('p', { class: 'empty' }, 'No blocks yet. A miner connected to the pool’s Stratum port will produce the first one.'));

  const pays = h('section', { 'aria-labelledby': 'ph' }, h('h2', { id: 'ph' }, 'Payments waiting'),
    mp.payments.length
      ? h('div', { class: 'wrap' }, h('table', null,
          h('thead', null, h('tr', null, h('th', null, 'To'), h('th', { class: 'num' }, 'Grams'), h('th', { class: 'num' }, 'Fee'))),
          h('tbody', null, mp.payments.map((p) => h('tr', null,
            h('td', null, link('#/account/' + p.to, p.to.slice(0, 10) + '…' + p.to.slice(-6), 'addr')),
            h('td', { class: 'num' }, grams(p.amount_g, 4)), h('td', { class: 'num' }, grams(p.fee_g, 4)))))))
      : h('p', { class: 'empty' }, 'No payments waiting. Send one with the wallet and it shows here until a block takes it.'));
  const peers = h('section', { 'aria-labelledby': 'eh' }, h('h2', { id: 'eh' }, 'Peers'),
    pe.peers.length
      ? h('table', null, h('thead', null, h('tr', null, h('th', null, 'Address'), h('th', null, 'Direction'))),
          h('tbody', null, pe.peers.map((p) => h('tr', null, h('td', { class: 'addr' }, p.listens_on || p.ip), h('td', null, p.inbound ? 'connected to us' : 'we connected')))))
      : h('p', { class: 'empty' }, 'No peers connected. Start another node and give it this node’s p2p address as its peer.'));
  show(hero, h('section', { class: 'block' }, h('div', { class: 'cols' }, h('div', null, blocks), h('div', null, pays, peers))));
}

async function blockPage(id) {
  const [st, b] = await Promise.all([api('status'), api('block/' + encodeURIComponent(id))]);
  setChain(st);
  const dl = (k, v) => [h('dt', null, k), h('dd', null, v)];
  const pager = h('nav', { class: 'pager', 'aria-label': 'Neighbouring blocks' },
    b.height > 1 ? link('#/block/' + (b.height - 1), 'Previous block') : null,
    b.height < st.height ? link('#/block/' + (b.height + 1), 'Next block') : null);
  show(h('h1', null, 'Block ' + n0(b.height)),
    b.main_chain ? null : h('p', { class: 'muted' }, 'This block is on a side branch, not on the best chain.'),
    h('dl', { class: 'detail' },
      dl('Hash', h('span', { class: 'hash' }, b.hash)),
      dl('Parent', b.height > 1 ? link('#/block/' + b.prev, short(b.prev), 'hash') : h('span', { class: 'muted' }, 'the start of the chain')),
      dl('Time', when(b.time)),
      dl('Payments', n0(b.payments)),
      dl('Fees', grams(b.fees_g, 9) + ' g'),
      dl('Blows (tickets)', n0(b.tickets)),
      dl('S, base units per coin', n0(b.sen_units)),
      dl('Seal difficulty bits', h('span', { class: 'hash' }, b.bits)),
      dl('Seal nonce', n0(b.nonce)),
      dl('State root', h('span', { class: 'hash' }, b.state_root)),
      dl('Stamp', n0(b.stamp_bytes) + ' bytes'),
      dl('Block data', n0(b.data_bytes) + ' bytes'),
      dl('Whole block', n0(b.size_bytes) + ' bytes')),
    pager);
  document.title = 'Block ' + n0(b.height) + ', ' + st.chain.name + ' node';
}

async function accountPage(addr) {
  const [st, a] = await Promise.all([api('status'), api('account/' + encodeURIComponent(addr))]);
  setChain(st);
  show(h('h1', null, 'Account'), h('p', { class: 'addr' }, a.address),
    a.found
      ? [h('div', { class: 'bal' }, grams(a.balance_g, 9) + ' g'), h('p', { class: 'muted' }, 'at block ' + n0(a.height)),
         h('dl', { class: 'detail' }, h('dt', null, 'Payments sent'), h('dd', null, n0(a.nonce)), h('dt', null, 'Next payment number'), h('dd', null, n0(a.next_nonce)))]
      : h('p', { class: 'empty' }, 'No account has this address yet. It is created when someone sends it a payment.'));
  document.title = 'Account, ' + st.chain.name + ' node';
}

function notFound(msg) {
  show(h('h1', null, 'Not found'), h('p', { class: 'empty' }, msg), h('p', null, link('#/', 'Back to the latest blocks')));
}

// the other two chains, when this node runs beside them (serve-all): what this node has checked of each, and a link to that chain's page
async function chainsNav() {
  const nav = document.getElementById('chains');
  let list = [];
  try { list = await api('chains'); } catch (e) { /* a lone node has none */ }
  if (!Array.isArray(list) || list.length < 2) { nav.hidden = true; return; }
  nav.hidden = false;
  nav.replaceChildren(...list.map((c) => {
    const body = [h('strong', null, c.name), ' ', n0(c.height), c.self ? '' : ' checked'];
    if (c.problem) body.push(h('span', { class: 'bad' }, ' problem: ' + c.problem));
    return c.self ? h('span', { class: 'here-chain', 'aria-current': 'page' }, body)
                  : h('a', { href: location.protocol + '//' + location.hostname + ':' + c.api_port + '/' }, body);
  }));
}

async function render() {
  const parts = location.hash.replace(/^#\/?/, '').split('/');
  try {
    if (parts[0] === 'block' && parts[1]) await blockPage(parts[1]);
    else if (parts[0] === 'account' && parts[1]) await accountPage(decodeURIComponent(parts[1]));
    else await home();
    showAlert('');
    chainsNav();
  } catch (e) {
    if (e instanceof NetErr) { showAlert('Can’t reach the node. Is it still running? This page tries again every 5 seconds.'); return; }
    showAlert('');
    notFound(e.message);
  }
}

document.getElementById('search').addEventListener('submit', (ev) => {
  ev.preventDefault();
  const q = document.getElementById('q').value.trim();
  if (/^\d+$/.test(q)) location.hash = '#/block/' + q;
  else if (/^[0-9a-fA-F]{64}$/.test(q)) location.hash = '#/block/' + q.toLowerCase();
  else if (/^zen1[0-9a-f]{72}$/i.test(q)) location.hash = '#/account/' + q.toLowerCase();
  else { showAlert('Enter a block height, a 64-digit block hash, or an address that starts with zen1.'); return; }
  showAlert('');
});
window.addEventListener('hashchange', () => { known.tip = null; render(); window.scrollTo(0, 0); });
setInterval(() => { if (!document.hidden && !/^#\/(block|account)\//.test(location.hash)) render(); }, 5000);
render();
