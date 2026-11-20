"""Exercise three OpenQuake hazardlib functions on small synthetic inputs.

Run with the pinned gem/oq-engine source tree on sys.path:
    python oq_stats_truncation_probe.py /path/to/oq-engine-<sha>

The inputs are synthetic (chosen by hand to make differences visible); the
functions are the real ones from openquake.hazardlib at the pinned revision:
  - stats.truncnorm_sf / stats.ndtr        (ground-motion truncation)
  - stats.mean_curve, calc.mean_rates.to_rates / to_probs
                                            (two definitions of "mean hazard")
  - stats.quantile_curve                    (logic-tree fractiles)
"""
import math
import sys

import numpy as np
from scipy.special import ndtr as sp_ndtr

sys.path.insert(0, sys.argv[1])
from openquake.hazardlib import stats  # noqa: E402
from openquake.hazardlib.calc.mean_rates import to_rates, to_probs  # noqa: E402

print("== 1. Truncation at n = 2 sigma: OQ truncnorm_sf vs one-sided form ==")
n = 2.0
phi_b = float(stats.ndtr(n))
eps = np.array([-2.5, -1.0, 0.0, 0.5, 1.0, 1.5, 1.9, 2.0, 2.1])
oq = stats.truncnorm_sf(phi_b, eps)
two_sided = np.clip((sp_ndtr(n) - sp_ndtr(eps)) / (2 * sp_ndtr(n) - 1), 0, 1)
upper_only = np.clip((sp_ndtr(n) - sp_ndtr(eps)) / sp_ndtr(n), 0, 1)
untrunc = 1 - sp_ndtr(eps)
print(f"{'eps':>5} {'OQ':>10} {'2-sided':>10} {'upper-only':>11} {'untrunc':>10} {'upper/2sided-1':>15}")
for e, a, b, c, d in zip(eps, oq, two_sided, upper_only, untrunc):
    ratio = (c / b - 1) if b > 0 else float('nan')
    print(f"{e:5.1f} {a:10.6f} {b:10.6f} {c:11.6f} {d:10.6f} {ratio:+15.3%}")
print("max |OQ - 2-sided| =", float(np.max(np.abs(oq - two_sided))))

print()
print("== 2. 'Mean hazard' over logic-tree branches: mean of PoEs vs PoE of mean rate ==")
# three branches with annual exceedance rates at four ground-motion levels
rates = np.array([[0.05, 5e-3, 5e-4, 5e-5],
                  [0.20, 2e-2, 2e-3, 2e-4],
                  [0.80, 8e-2, 8e-3, 8e-4]])
w = np.array([1 / 3, 1 / 3, 1 / 3])
poes = to_probs(rates, 1.0)            # per-branch Poisson PoE, 1-year
mean_of_poes = stats.mean_curve(poes, w)            # OQ default (use_rates=false)
poe_of_mean_rate = to_probs(stats.mean_curve(to_rates(poes.copy()), w))  # use_rates=true
for j in range(rates.shape[1]):
    print(f"level {j}: mean(PoE)={mean_of_poes[j]:.6e}  PoE(mean rate)={poe_of_mean_rate[j]:.6e}"
          f"  ratio-1={poe_of_mean_rate[j] / mean_of_poes[j] - 1:+.3%}")

print()
print("== 3. Fractiles of a 3-branch tree: OQ quantile_curve vs alternatives ==")
vals = np.array([1e-4, 4e-4, 1.6e-3])   # hazard at one level, sorted
wts = np.array([0.2, 0.6, 0.2])
cw = np.cumsum(wts)
for q in (0.1, 0.5, 0.9):
    oqq = float(stats.quantile_curve(q, vals, wts))
    loglin = float(np.exp(np.interp(q, cw, np.log(vals))))   # linear in weight, log in hazard
    first = float(vals[np.searchsorted(cw, q, side='left')])  # first cumulative weight >= q
    print(f"q={q}: OQ={oqq:.4e}  linear-weight/log-hazard={loglin:.4e}  first-exceeding={first:.4e}")
