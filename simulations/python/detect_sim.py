# Detection and attribution with 2 versus 3 linked currencies.
# Each chain i has a log deviation x_i(t) of its electronic coin from its physical coin.
# Observable each day: the electronic cross rate of each pair against the metal ratio,
#   r_ij(t) = x_i(t) - x_j(t) + noise   (noise sigma = 1% a day: auction prices, metal quotes)
# An attacker pushes chain A's S at a constant rate (at most 2.9%/day, the anchor limit).
# Detector: 7-day mean of each residual; alarm when |mean| exceeds a threshold set so that,
# with no attack, false alarms happen about once a year per pair.
# Attribution with 3 chains: the chain whose two residuals both deviate (sign-consistent),
# i.e. argmax_i |r_ij + r_ik| / 2. With 2 chains there is one residual and no attribution.
import numpy as np, json
rng = np.random.default_rng(7)
SIG, WIN, DAYS, RUNS = 0.01, 7, 60, 4000

def thresh():
    # false alarm about once per 365 days on a 7-day moving mean of white noise
    z = rng.normal(0, SIG, (2000, 365 + WIN))
    m = np.abs(np.convolve(np.ones(WIN) / WIN, np.zeros(1), 'full'))  # placeholder
    mm = np.array([np.abs(np.convolve(row, np.ones(WIN) / WIN, 'valid')).max() for row in z])
    return np.quantile(mm, 0.5)  # median yearly max -> ~1 false alarm a year
TH = thresh()

def run(n, rate, attacked=(0,), coord=False):
    det_days, correct = [], 0
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    for _ in range(RUNS):
        t = np.arange(DAYS)
        x = np.zeros((n, DAYS))
        for a in attacked: x[a] = rate * t
        r = {p: x[p[0]] - x[p[1]] + rng.normal(0, SIG, DAYS) for p in pairs}
        mean = {p: np.convolve(r[p], np.ones(WIN) / WIN, 'valid') for p in pairs}
        hit = None
        for d in range(len(next(iter(mean.values())))):
            if any(abs(mean[p][d]) > TH for p in pairs): hit = d + WIN - 1; break
        det_days.append(hit if hit is not None else DAYS)
        if n == 3 and hit is not None:
            d = hit - WIN + 1
            score = []
            for i in range(3):
                s = 0
                for (a, b) in pairs:
                    if a == i: s += mean[(a, b)][d]
                    elif b == i: s -= mean[(a, b)][d]
                score.append(abs(s) / 2)
            if int(np.argmax(score)) in attacked and len(attacked) == 1: correct += 1
            if len(attacked) == 2 and int(np.argmax(score)) not in attacked: correct += 0  # honest chain blamed
            if len(attacked) == 2 and int(np.argmax(score)) in attacked: correct += 1
    return float(np.median(det_days)), correct / RUNS

out = {'threshold_pct': TH * 100, 'rates': [], 'n2': [], 'n3': [], 'attr3': [], 'coord_attr': []}
for rate in [0.001, 0.002, 0.005, 0.01, 0.02, 0.029]:
    d2, _ = run(2, rate)
    d3, a3 = run(3, rate)
    _, ca = run(3, rate, attacked=(0, 1))
    out['rates'].append(rate * 100); out['n2'].append(d2); out['n3'].append(d3); out['attr3'].append(a3); out['coord_attr'].append(ca)
    print(f'push {rate*100:.1f}%/day: detect 2 chains {d2:.0f} d, 3 chains {d3:.0f} d, attribution {a3*100:.0f}%, coordinated two-chain attack attributed to an attacked chain {ca*100:.0f}%')
print('threshold (7-day mean) %.2f%%' % (TH * 100))
json.dump(out, open('/home/claude/whitepaper/data/detect.json', 'w'))
