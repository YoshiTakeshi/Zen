# Detection and attribution with what every Zen node sees on the public chains.
# For each chain i the truth is U_i = log grams of chain i's money that one physical coin is worth.
# Nine public readings, recomputed every hour from blocks and batch auctions:
#   P_i      chain i's own coin-priced payments                      = U_i + bP_i + noise (sigma_P)
#   I_i(j)   chain i read through the i-j exchange: S_j (public grams
#            per coin of chain j) x gram rate (on-chain trades) / coin
#            ratio (coin-priced quotes, set from metal prices)        = U_i + bX_ij + noise (sigma_I)
#   I_j(i)   the same pair read from chain j's side                   = U_j - bX_ij + noise
# An attacker biases components: bP_i (fake payments on chain i) or bX_ij (coin-priced orders at a
# wrong ratio on pair i-j, which shift the pair's reading for i one way and for j the other way).
# Detector: at each hour, for windows of the last 1, 3, 6, 12 and 24 hours, fit the readings with the
# smallest set of biased components (0, 1 or 2 of the 6) by least squares; alarm when a non-empty set
# explains the readings significantly better than none (threshold set for about one false alarm in
# five quiet years); the chosen set is the attribution.
import numpy as np, itertools, json, os
rng = np.random.default_rng(11)
SC = float(os.environ.get('SCALE', '1'))         # 1 = liquid; 3 = thin, young markets
SP, SI = 0.049 * SC, 0.033 * SC                   # hourly noise: 1%/day payments, 0.67%/day exchange, x sqrt(24)
COMP = ['P0', 'P1', 'P2', 'X01', 'X02', 'X12']   # chains 0 = Jen, 1 = Ken, 2 = Yen
# reading order: P0 P1 P2, I0(1) I1(0), I0(2) I2(0), I1(2) I2(1)
R_CH = [0, 1, 2, 0, 1, 0, 2, 1, 2]
SIG = np.array([SP] * 3 + [SI] * 6)
def design(cset):
    cols = []
    for c in range(3):  # U_c
        cols.append([1.0 if R_CH[r] == c else 0.0 for r in range(9)])
    for name in cset:
        v = np.zeros(9)
        if name[0] == 'P': v[int(name[1])] = 1
        else:
            i, j = int(name[1]), int(name[2])
            k = {(0, 1): 3, (0, 2): 5, (1, 2): 7}[(i, j)]
            v[k], v[k + 1] = 1, -1
        cols.append(v)
    return np.array(cols).T
SETS = [()] + [(c,) for c in COMP] + list(itertools.combinations(COMP, 2))
PROJ = {}
for s in SETS:
    A = design(s) / SIG[:, None]
    PROJ[s] = np.eye(9) - A @ np.linalg.pinv(A)
WINS = [1, 3, 6, 12, 24]
def rss(y, w):
    z = y / (SIG / np.sqrt(w))
    return {s: float(z @ PROJ[s] @ z) for s in SETS}
PEN = {0: 0.0}
def choose(r, th):
    # penalised fit: each component costs th/2 (BIC-like); pick the cheapest set
    best = min(SETS, key=lambda s: r[s] + len(s) * th)
    return best, r[()] - r[best] - len(best) * th
def readings(bias, H):
    y = rng.normal(0, 1, (H, 9)) * SIG
    for name, b in bias.items():
        if name[0] == 'P': y[:, int(name[1])] += b
        else:
            i, j = int(name[1]), int(name[2]); k = {(0, 1): 3, (0, 2): 5, (1, 2): 7}[(i, j)]
            y[:, k] += b; y[:, k + 1] -= b
    return y
def detect(y, th, H):
    for h in range(H):
        for w in WINS:
            if h + 1 < w: continue
            s, gain = choose(rss(y[h + 1 - w:h + 1].mean(0), w), th)
            if s: return h + 1, s
    return None, ()
def calibrate(years=5):
    # threshold so that a quiet stretch of `years` years raises about one false alarm; estimated on 60-day runs
    H = 24 * 60; runs = 60
    ys = [readings({}, H) for _ in range(runs)]
    lo, hi = 2.0, 40.0
    for _ in range(14):
        th = (lo + hi) / 2
        fa = sum(detect(y, th, H)[0] is not None for y in ys) / runs  # alarms per 60 days
        target = 60 / (365 * years)
        lo, hi = (th, hi) if fa > target else (lo, th)
    return hi
TH = calibrate()
print('threshold', round(TH, 2))
SCEN = [
    ('Payment attack on Jen', {'P0': 1}),
    ('Payment attack on Jen and Ken', {'P0': 1, 'P1': 1}),
    ('Exchange attack on Jen-Ken', {'X01': 1}),
    ('Payments on Jen + exchange Jen-Ken', {'P0': 1, 'X01': 1}),
    ('Counterfeit Ren (Yen payments shift)', {'P2': -1}),
]
out = {'scale': SC, 'threshold': TH, 'sizes': [], 'rows': {}}
SIZES = [0.02, 0.05, 0.10, 0.25]
H = 24 * 14; RUNS = 400
for name, pat in SCEN:
    out['rows'][name] = []
    for d in SIZES:
        hrs, ok = [], 0
        want = tuple(sorted(pat))
        for _ in range(RUNS):
            y = readings({k: v * d for k, v in pat.items()}, H)
            h, s = detect(y, TH, H)
            hrs.append(h if h else H)
            ok += tuple(sorted(s)) == want
        out['rows'][name].append({'size': d * 100, 'hours': float(np.median(hrs)), 'named': ok / RUNS * 100})
        print(f'{name:40s} {d*100:4.0f}%  detected after {np.median(hrs):5.1f} h  right components named {ok/RUNS*100:5.1f}%')
out['sizes'] = [s * 100 for s in SIZES]
json.dump(out, open('/home/claude/whitepaper/data/detect9_%g.json' % SC, 'w'))
