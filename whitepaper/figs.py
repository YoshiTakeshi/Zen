import json, math
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

# Palette: reference dataviz slots (validated). Chains: Yen gold, Ken blue, Jen copper-orange.
BLUE, ORANGE, AQUA, YELLOW, VIOLET = '#2a78d6', '#eb6834', '#1baf7a', '#eda100', '#6250d6'
YEN, KEN, JEN = YELLOW, BLUE, ORANGE
INK, INK2, GRID, MUTED = '#0b0b0b', '#52514e', '#e4e3df', '#8a8984'

plt.rcParams.update({
    'font.family': 'FreeSans', 'font.size': 9, 'axes.titlesize': 10, 'axes.labelsize': 9,
    'axes.edgecolor': MUTED, 'axes.labelcolor': INK2, 'xtick.color': INK2, 'ytick.color': INK2,
    'axes.spines.top': False, 'axes.spines.right': False, 'axes.grid': True, 'grid.color': GRID,
    'grid.linewidth': 0.6, 'axes.axisbelow': True, 'legend.frameon': False, 'lines.linewidth': 2,
    'pdf.fonttype': 42, 'figure.dpi': 150,
})
W1, W2 = 3.3, 6.8  # single / double column widths, inches
D = '/home/claude/whitepaper/'
S = json.load(open(D + 'data/series.json'))
L = json.load(open(D + 'data/launch.json'))

def save(fig, name):
    fig.savefig(D + 'figs/' + name + '.pdf', bbox_inches='tight', pad_inches=0.02)
    plt.close(fig)

def bars(ax, x, h, color, **k):
    return ax.bar(x, h, color=color, edgecolor='white', linewidth=1.2, **k)

# 1. Supply with V = 1
fig, ax = plt.subplots(figsize=(W2, 2.6))
for name, a, bpd, col in [('Golden Yen', 1.440, 96, YEN), ('Silver Ken', 0.786, 288, KEN), ('Bronze Jen', 0.580, 576, JEN)]:
    years = np.logspace(-2, 2, 300)
    N = years * 365 * bpd
    # sum_{n=1}^{N} 2520 n^-a, via Euler-Maclaurin
    def supply(N):
        if abs(a - 1) < 1e-9: return 2520 * (math.log(N) + 0.5772)
        z = {1.440: 1.0 + 1/0.44 - 0.5 + 0.44/12, 0.786: None, 0.580: None}
        return 2520 * ((N ** (1 - a) - 1) / (1 - a) + 0.5 * (1 + N ** -a) + a / 12 * (1 - N ** (-a - 1)))
    ax.plot(years, [supply(n) for n in N], color=col)
    ax.text(100 * 1.08, supply(100 * 365 * bpd), name, color=INK, va='center', fontsize=8.5)
ax.set_xscale('log'); ax.set_yscale('log')
ax.set_xlabel('Years after the chain starts'); ax.set_ylabel('Coins issued (V = 1)')
ax.set_xlim(0.01, 100); ax.set_xticks([0.01, 0.1, 1, 10, 100]); ax.set_xticklabels(['4 days', '5 weeks', '1', '10', '100'])
save(fig, 'supply')

# 2. Metallic split: miner vs minters share of new coins
fig, ax = plt.subplots(figsize=(W1, 1.7))
ch = ['Yen (gold)', 'Ken (silver)', 'Jen (bronze)']; miner = [89, 65, 45]
y = np.arange(3)[::-1]
ax.barh(y, miner, color=BLUE, edgecolor='white', linewidth=1.2, height=0.6, label='Miner keeps')
ax.barh(y, [100 - m for m in miner], left=miner, color=ORANGE, edgecolor='white', linewidth=1.2, height=0.6, label='Minters share')
for yi, m in zip(y, miner):
    ax.text(m / 2, yi, f'{m}%', color='white', ha='center', va='center', fontsize=8, fontweight='bold')
    ax.text(m + (100 - m) / 2, yi, f'{100-m}%', color='white', ha='center', va='center', fontsize=8, fontweight='bold')
ax.set_yticks(y); ax.set_yticklabels(ch); ax.set_xlim(0, 100); ax.set_xlabel('Average share of new coins (%)')
ax.grid(axis='y', visible=False); ax.legend(loc='lower center', bbox_to_anchor=(0.5, 1.0), ncol=2, fontsize=8)
save(fig, 'split')

# 3. Blow benchmark (measured)
fig, ax = plt.subplots(figsize=(W1, 1.9))
lab = ['Phone, 1 core\n(4 GB Android)', 'Mac, 1 core', 'Mac, 5 cores']
val = [1000 / 196, 1000 / 125, 36]
b = bars(ax, range(3), val, [ORANGE, BLUE, BLUE], width=0.6)
for i, v in enumerate(val): ax.text(i, v + 0.8, f'{v:.0f}/s' if v > 9 else f'{v:.1f}/s', ha='center', fontsize=8, color=INK)
ax.set_xticks(range(3)); ax.set_xticklabels(lab, fontsize=7.5); ax.set_ylabel('Blows per second'); ax.set_ylim(0, 42)
ax.grid(axis='x', visible=False)
save(fig, 'blowbench')

# 4. Collaborative minting: leaves per block vs minters (devnet, Jen-0.8)
fig, ax = plt.subplots(figsize=(W1, 2.0))
m = [4, 8, 16, 24]; lv = [23, 44, 71, 89]
ax.plot(m, lv, color=ORANGE, marker='o', markersize=5)
for a_, b_ in zip(m, lv): ax.text(a_, b_ + 4, str(b_), ha='center', fontsize=8)
ax.set_xlabel('Minters on the devnet'); ax.set_ylabel('Leaves per block'); ax.set_ylim(0, 105); ax.set_xticks(m)
ax.text(23.5, 50, 'one 2-core test machine\nsaturates', fontsize=7.5, color=INK2, ha='right')
save(fig, 'capacity')

# 5. Jen-0.9 vs Jen-0.10 A/B
fig, axs = plt.subplots(1, 3, figsize=(W2, 1.9))
for ax, title, v, fmt in [(axs[0], 'Proofs thrown away as overlap', [78, 3], '{}%'),
                          (axs[1], 'Payments carried per block', [36, 208], '{}'),
                          (axs[2], 'Leaves taken by a 15x faster prover', [99, 23], '{}%')]:
    bars(ax, [0, 1], v, [MUTED, ORANGE], width=0.6)
    for i, x in enumerate(v): ax.text(i, x * 1.02 + max(v) * 0.02, fmt.format(x), ha='center', fontsize=8)
    ax.set_xticks([0, 1]); ax.set_xticklabels(['Jen-0.9', 'Jen-0.10']); ax.set_title(title, fontsize=8.5, color=INK)
    ax.set_ylim(0, max(v) * 1.2); ax.grid(axis='x', visible=False)
fig.tight_layout(w_pad=1.5)
save(fig, 'ab')

# 6. Hidden-chain attack
fig, ax = plt.subplots(figsize=(W1, 2.0))
x = np.arange(3); w = 0.36
seal = [99, 111, None]; two = [3, 57, 59]
labs = ['none', '30% of honest', '50% of honest']
two = [3, 57, 59]; seal = [np.nan, 99, 111]
bars(ax, x - w / 2, [0 if np.isnan(s) else s for s in seal], MUTED, width=w, label='Seal work only')
bars(ax, x + w / 2, two, ORANGE, width=w, label='Two-factor weight')
for i in range(3):
    if not np.isnan(seal[i]): ax.text(i - w / 2, seal[i] + 3, f'{seal[i]:.0f}%', ha='center', fontsize=7.5)
    ax.text(i + w / 2, two[i] + 3, f'{two[i]}%', ha='center', fontsize=7.5)
ax.axhline(100, color=INK, lw=1, ls='--'); ax.text(2.55, 102, 'attack wins above', fontsize=7, ha='right', color=INK2)
ax.set_xticks(x); ax.set_xticklabels(labs, fontsize=8); ax.set_xlabel("Attacker's minting power (3x the honest sealing)")
ax.set_ylabel('Hidden chain, % of honest weight'); ax.set_ylim(0, 128); ax.grid(axis='x', visible=False)
ax.legend(loc='upper left', fontsize=7.5)
save(fig, 'hidden')

# 7. Launch and hashrate-drop difficulty
fig, axs = plt.subplots(1, 2, figsize=(W2, 2.3), sharey=True)
for ax, key, title, lim in [(axs[0], 'launch', 'Launch: difficulty set for 50x the hashrate present', 200),
                            (axs[1], 'drop', '90% of hashrate leaves after 4 hours', 250)]:
    for runs, col, lab in [(L[key + '_pb'], MUTED, 'Per-block retarget (12.5% max step)'), (L[key + '_as'], ORANGE, 'Time-based difficulty (1-hour half-life)')]:
        for i, r in enumerate(runs):
            t = np.array(r) / 3600
            ax.plot(t, np.arange(1, len(t) + 1), color=col, lw=1.3, alpha=0.9 if i == 0 else 0.35, label=lab if i == 0 else None)
    tt = np.linspace(0, 30, 2)
    ax.plot(tt, tt * 24, color=INK, lw=1, ls='--', label='Target: 24 blocks an hour' if key == 'launch' else None)
    ax.set_xlim(0, 30); ax.set_ylim(0, lim); ax.set_title(title, fontsize=8.5, color=INK); ax.set_xlabel('Hours')
axs[0].set_ylabel('Blocks found (Jen, 2.5 min)')
axs[0].legend(fontsize=7, loc='upper left')
fig.tight_layout(w_pad=1.2)
save(fig, 'launch')

# 8. Purity and confirmation (Jen-0.6 devnet, busy)
fig, ax = plt.subplots(figsize=(W1, 1.8))
lab = ['940\n(6% fee)', '990\n(1% fee)', '9999\n(0.01% fee)']; v = [15, 25, 68]
bars(ax, range(3), v, [ORANGE, BLUE, MUTED], width=0.6)
for i, x in enumerate(v): ax.text(i, x + 2, f'{x} s', ha='center', fontsize=8)
ax.set_xticks(range(3)); ax.set_xticklabels(lab, fontsize=8); ax.set_ylabel('Median wait to a block (s)'); ax.set_ylim(0, 80)
ax.grid(axis='x', visible=False)
save(fig, 'purity')

# 9. Fibonacci day weights
fig, ax = plt.subplots(figsize=(W1, 1.7))
FIB = [1, 2, 3, 5, 8, 13, 21, 34, 55]; wts = []
for k, n in enumerate(FIB): wts += [0.5 ** k] * n
ax.bar(range(1, len(wts) + 1), wts, color=ORANGE, width=0.85, edgecolor='white', linewidth=0.4)
ax.set_xlabel('Days ago'); ax.set_ylabel('Weight'); ax.set_xlim(0, len(wts) + 1); ax.grid(axis='x', visible=False)
ax.text(60, 0.6, f'{len(wts)} days in the window\nhalf the weight in the last 8', fontsize=7.5, color=INK2)
save(fig, 'window')

def attack_axes(ax, n=60, att=(0, 30)):
    ax.axvspan(att[0], att[1], color='#f3efe8', zorder=0)
    ax.text((att[0] + att[1]) / 2, 0.02, 'attack', transform=ax.get_xaxis_transform(), ha='center', fontsize=7.5, color=INK2)
    ax.axhline(1, color=INK, lw=0.8)

# 10. Day window variants under a 30-day attack by 10% of payments
fig, ax = plt.subplots(figsize=(W2, 2.4))
attack_axes(ax)
d = np.arange(60)
for k, col, lab in [('dw_none', MUTED, 'Day window only'), ('dw_anchor', BLUE, '+ anchor and band'), ('dw_full', ORANGE, '+ anchor, band and 10% day clip')]:
    ax.plot(d, S[k], color=col, label=lab)
ax.set_xlabel('Days from the start of the attack'); ax.set_ylabel('1 JEN in physical Sen'); ax.set_xlim(0, 59); ax.set_ylim(0.4, 1.1)
ax.legend(fontsize=7.5, loc='lower right')
save(fig, 'daywin')

# 11. Genuine change: Sen worth 1.5x
fig, ax = plt.subplots(figsize=(W1, 2.0))
ax.axhline(1, color=INK, lw=0.8); ax.axhspan(0.95, 1.05, color='#eef4fb', zorder=0)
ax.plot(np.arange(60), S['dw_copper'], color=ORANGE)
ax.text(2, 0.965, 'within 5%', fontsize=7.5, color=INK2)
ax.set_xlabel('Days after copper rises 50%'); ax.set_ylabel('1 JEN in physical Sen'); ax.set_xlim(0, 59); ax.set_ylim(0.6, 1.08)
save(fig, 'copper')

# 12. Attacker vs defender
fig, ax = plt.subplots(figsize=(W1, 2.2))
attack_axes(ax)
for k, col, lab in [('att_alone', MUTED, 'Attacker alone ($5M)'), ('att_def5', BLUE, 'Defender $2.5M from day 5'), ('att_def2', ORANGE, 'Defender $2.5M from day 2')]:
    ax.plot(np.arange(60), S[k], color=col, label=lab, lw=1.6)
ax.set_xlabel('Days'); ax.set_ylabel('1 JEN in physical Sen'); ax.set_xlim(0, 59); ax.set_ylim(0.97, 1.22)
ax.legend(fontsize=7, loc='upper right')
save(fig, 'defender')

# 13. Convergence from a wrong genesis S
fig, axs = plt.subplots(1, 2, figsize=(W2, 2.4), sharey=True)
cols = {1: ORANGE, 0.7: BLUE, 0.5: AQUA, 0.3: MUTED}
for ax, s0, title in [(axs[0], 'third', 'Genesis S = 1/3 of the true Sen'), (axs[1], '3', 'Genesis S = 3x the true Sen')]:
    ax.axhspan(0.95, 1.05, color='#eef4fb', zorder=0); ax.axhline(1, color=INK, lw=0.8)
    for q in [1, 0.7, 0.5, 0.3]:
        p = S['conv'][f'q{q}_s{s0}'][:365]
        ax.plot(np.arange(len(p)), p, color=cols[q], lw=1.5, label=f'{int(q*100)}% priced from the coin')
    ax.set_yscale('log'); ax.set_yticks([1/3, 0.5, 1, 2, 3]); ax.set_yticklabels(['1/3', '1/2', '1', '2', '3'])
    ax.minorticks_off(); ax.set_xlim(0, 365); ax.set_title(title, fontsize=8.5, color=INK); ax.set_xlabel('Days after launch')
axs[0].set_ylabel('1 JEN in physical Sen'); axs[1].legend(fontsize=7, loc='upper right')
fig.tight_layout(w_pad=1.2)
save(fig, 'converge')

# 14. Cost of a 12% push held for a month, by defence level
fig, ax = plt.subplots(figsize=(W2, 2.2))
lv = ['Fees only (no defences)', 'Each gram once + receiver cap + bond', '+ coin-days + bond penalty', '+ exchange median of three\n(once Ken and Yen trade)']
lost = [3e3, 45e3, 0.5e6, 30e6]; locked = [0, 1.9e6, 6e6, 6e6]
y = np.arange(4)[::-1]
ax.barh(y, lost, color=[MUTED, BLUE, ORANGE, ORANGE], edgecolor='white', height=0.55)
fmt = lambda v: f'${v/1e6:.1f}M' if v >= 1e6 else f'${v/1e3:.0f}k'
for yi, v, lk in zip(y, lost, locked):
    ax.text(v * 1.25, yi, fmt(v) + ' lost a month' + (f'  ·  {fmt(lk)} locked' if lk else ''), va='center', fontsize=8)
ax.set_xscale('log'); ax.set_xlim(1e3, 1e9); ax.set_yticks(y); ax.set_yticklabels(lv, fontsize=8)
ax.set_xlabel('Attacker spending (US$, log scale), Jen at 1M payments a day'); ax.grid(axis='y', visible=False)
save(fig, 'costs')

# 15. Attacker money vs spending, full set vs + coin-days + penalty
fig, axs = plt.subplots(1, 2, figsize=(W2, 2.3))
money = [1, 2.5, 5, 10, 25]
full_move = [16, 17, 20, 12, 12]; both_move = [6, 11, 18, 21, 23]
full_spent = [27, 72, 177, 249, 622]; both_spent = [116, 247, 534, 981, 2700]
ax = axs[0]
ax.plot(money, full_move, color=BLUE, marker='o', ms=4, label='Full set'); ax.plot(money, both_move, color=ORANGE, marker='o', ms=4, label='+ coin-days + bond penalty')
ax.axhline(37, color=INK, ls='--', lw=0.8); ax.text(25, 34, 'band limit 37%/month', ha='right', fontsize=7, color=INK2)
ax.set_xscale('log'); ax.set_xticks(money); ax.set_xticklabels(['1', '2.5', '5', '10', '25']); ax.minorticks_off()
ax.set_xlabel("Attacker's money ($M)"); ax.set_ylabel('Largest move of S in 30 days (%)'); ax.set_ylim(0, 40); ax.legend(fontsize=7, loc='upper left')
ax = axs[1]
ax.plot(money, full_spent, color=BLUE, marker='o', ms=4); ax.plot(money, both_spent, color=ORANGE, marker='o', ms=4)
ax.set_xscale('log'); ax.set_yscale('log'); ax.set_xticks(money); ax.set_xticklabels(['1', '2.5', '5', '10', '25']); ax.minorticks_off()
ax.set_yticks([30, 100, 300, 1000, 3000]); ax.set_yticklabels(['$30k', '$100k', '$300k', '$1M', '$3M'])
ax.set_xlabel("Attacker's money ($M)"); ax.set_ylabel('Lost in 30 days')
fig.tight_layout(w_pad=1.5)
save(fig, 'coindays')

# 16. Exchange: median of three
fig, ax = plt.subplots(figsize=(W2, 2.2))
sc = ['Payment attack\non Jen', 'Exchange attack\non Jen–Ken (60%)', 'Payment on Jen\n+ exchange Jen–Ken', 'Payment attack on\nJen and Ken together']
po = [26, 4, 26, 26]; m3 = [4, 4, 14, 4]
x = np.arange(4); w = 0.36
bars(ax, x - w / 2, po, MUTED, width=w, label='Payments only'); bars(ax, x + w / 2, m3, ORANGE, width=w, label='Median of three readings')
for i in range(4):
    ax.text(i - w / 2, po[i] + 0.8, f'{po[i]}%', ha='center', fontsize=7.5); ax.text(i + w / 2, m3[i] + 0.8, f'{m3[i]}%', ha='center', fontsize=7.5)
ax.axhline(4, color=INK, ls=':', lw=0.8); ax.text(3.6, 4.6, 'normal noise', fontsize=7, ha='right', color=INK2)
ax.set_xticks(x); ax.set_xticklabels(sc, fontsize=7.5); ax.set_ylabel("Largest move of Jen's S, 30 days (%)"); ax.set_ylim(0, 31)
ax.grid(axis='x', visible=False); ax.legend(fontsize=7.5, loc='upper center', ncol=2)
save(fig, 'exchange')

# 17. Throughput levers
fig, ax = plt.subplots(figsize=(W1, 2.0))
lab = ['100 blows ×\n16 payments', 'Leaf ceiling\n1,024 × 16', 'With one\nstamp (2 MB)', 'Three chains\n(stamps)']
v = [11, 110, 830, 1700]
bars(ax, range(4), v, [MUTED, BLUE, ORANGE, ORANGE], width=0.6)
for i, x in enumerate(v): ax.text(i, x * 1.15, f'{x:,}/s', ha='center', fontsize=8)
ax.set_yscale('log'); ax.set_ylim(5, 5000); ax.set_xticks(range(4)); ax.set_xticklabels(lab, fontsize=7); ax.set_ylabel('Payments per second (log)')
ax.grid(axis='x', visible=False); ax.minorticks_off()
save(fig, 'throughput')
print('ok')
