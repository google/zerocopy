#!/usr/bin/env python3
"""Interval / quantile scoring probe (TOY MODEL, standard library only).

Transcribes the weighted interval score (WIS) of Bracher et al. (2021) as
implemented in scoringutils (R/metrics-interval-range.R interval_score,
R/metrics-quantile.R wis and quantile_score) and checks:
  F1  WIS == mean of quantile scores (2 x pinball loss) for a symmetric set
  F2  count_median_twice changes the normaliser, not the ranking of one forecast
  F3  propriety for quantile forecasts: expected WIS under a known predictive
      law is minimised by the true quantiles (numerical integration)
  F4  missing-forecast handling: mean WIS over each model's own forecasts vs
      the scoringutils pairwise 'mean score ratio on the overlap' convention
  F5  quantile-set convention: the same two forecasters can swap rank between
      the 23-level and 7-level quantile sets
All distributions and forecasters are synthetic; nothing here is a property
of any real hub submission.
"""
import math, random

Q23 = [0.01, 0.025] + [round(0.05 * k, 2) for k in range(1, 20)] + [0.975, 0.99]
Q7 = [0.025, 0.1, 0.25, 0.5, 0.75, 0.9, 0.975]

def interval_score(y, lo, hi, alpha, weigh=True):
    disp = hi - lo
    over = (lo - y) if y < lo else 0.0
    under = (y - hi) if y > hi else 0.0
    if weigh:
        disp *= alpha / 2
    else:
        over = 2 / alpha * over if over else 0.0
        under = 2 / alpha * under if under else 0.0
    return disp + under + over

def wis(y, qs, levels, count_median_twice=False):
    d = dict(zip(levels, qs))
    rows = []
    for tau in levels:
        if tau < 0.5:
            alpha = 2 * tau
            rows.append((interval_score(y, d[tau], d[round(1 - tau, 3)], alpha), 1.0))
        elif tau == 0.5:
            rows.append((interval_score(y, d[0.5], d[0.5], 1.0), 1.0 if count_median_twice else 0.5))
    return sum(s * w for s, w in rows) / sum(w for _, w in rows)

def quantile_score_mean(y, qs, levels):
    return sum(2 * ((1.0 if y <= q else 0.0) - tau) * (q - y) for q, tau in zip(qs, levels)) / len(levels)

# normal law helpers
def ncdf(x, mu, s): return 0.5 * (1 + math.erf((x - mu) / (s * math.sqrt(2))))
def nppf(p, mu, s):
    lo, hi = mu - 20 * s, mu + 20 * s
    for _ in range(200):
        mid = (lo + hi) / 2
        if ncdf(mid, mu, s) < p: lo = mid
        else: hi = mid
    return (lo + hi) / 2
def npdf(x, mu, s): return math.exp(-0.5 * ((x - mu) / s) ** 2) / (s * math.sqrt(2 * math.pi))

def expected(score_fn, mu, s, n=4001):
    a, b = mu - 10 * s, mu + 10 * s
    h = (b - a) / (n - 1)
    tot = 0.0
    for i in range(n):
        y = a + i * h
        wgt = 0.5 if i in (0, n - 1) else 1.0
        tot += wgt * score_fn(y) * npdf(y, mu, s)
    return tot * h

random.seed(20261120)
# F1
maxdiff = 0.0
for _ in range(2000):
    mu, s = random.uniform(0, 100), random.uniform(1, 30)
    qs = [nppf(t, mu, s) for t in Q23]
    y = random.gauss(mu, 1.5 * s)
    maxdiff = max(maxdiff, abs(wis(y, qs, Q23) - quantile_score_mean(y, qs, Q23)))
print(f"F1: max |WIS - mean quantile score| over 2000 random cases (23 levels) = {maxdiff:.2e}")

# F2
y, qs = 7.0, [nppf(t, 10, 3) for t in Q23]
a, b = wis(y, qs, Q23), wis(y, qs, Q23, count_median_twice=True)
print(f"F2: WIS default={a:.6f}, count_median_twice={b:.6f} (normaliser K+1/2=11.5 vs K+1=12)")

# F3
mu0, s0 = 50.0, 10.0
truth = [nppf(t, mu0, s0) for t in Q23]
base = expected(lambda y: wis(y, truth, Q23), mu0, s0)
print(f"F3: E[WIS] true quantiles = {base:.4f}")
for label, f in [("shift +2", lambda t: nppf(t, mu0 + 2, s0)), ("shift -2", lambda t: nppf(t, mu0 - 2, s0)),
                 ("sd x0.8", lambda t: nppf(t, mu0, 0.8 * s0)), ("sd x1.25", lambda t: nppf(t, mu0, 1.25 * s0))]:
    qs = [f(t) for t in Q23]
    print(f"    {label:9s}: E[WIS] = {expected(lambda y: wis(y, qs, Q23), mu0, s0):.4f}")

# F4 missing forecasts
weeks = []
for wk in range(40):
    hard = wk % 5 == 0
    mu = 1000 if hard else 100
    weeks.append((mu, random.gauss(mu, 0.3 * mu if hard else 0.1 * mu)))
def model_forecast(mu, sdfrac):
    return [nppf(t, mu, sdfrac * mu) for t in Q23]
scA = {i: wis(y, model_forecast(mu, 0.2), Q23) for i, (mu, y) in enumerate(weeks)}
scB = {i: wis(y, model_forecast(mu * 1.1, 0.2), Q23) for i, (mu, y) in enumerate(weeks) if i % 5 != 0}
meanA = sum(scA.values()) / len(scA); meanB = sum(scB.values()) / len(scB)
overlap = sorted(set(scA) & set(scB))
ratio_BA = (sum(scB[i] for i in overlap) / len(overlap)) / (sum(scA[i] for i in overlap) / len(overlap))
print(f"F4: model A (40/40 weeks) mean WIS={meanA:.2f}; model B (32/40, skips high-count weeks, biased +10%) "
      f"mean WIS={meanB:.2f}; overlap mean-score ratio B/A={ratio_BA:.3f}")

# F5 quantile-set convention can flip rankings (constructed example)
# forecaster C: exact at every level except 0.01/0.99, which it collapses onto
# its 0.05/0.95 quantiles (tails too thin); D: sd inflated by 5% everywhere.
def fC(t):
    if t == 0.01: return nppf(0.05, mu0, s0)
    if t == 0.99: return nppf(0.95, mu0, s0)
    return nppf(t, mu0, s0)
def fD(t): return nppf(t, mu0, 1.05 * s0)
for name, lv in (("23-level", Q23), ("7-level", Q7)):
    cC = [fC(t) for t in lv]; cD = [fD(t) for t in lv]
    eC = expected(lambda y: wis(y, cC, lv), mu0, s0); eD = expected(lambda y: wis(y, cD, lv), mu0, s0)
    print(f"F5: {name}: E[WIS] C={eC:.4f} D={eD:.4f} -> better: {'C' if eC < eD else 'D'}")
