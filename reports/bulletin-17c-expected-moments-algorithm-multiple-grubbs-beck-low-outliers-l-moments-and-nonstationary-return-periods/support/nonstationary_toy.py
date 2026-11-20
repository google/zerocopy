"""Toy model (NOT a fitted nonstationary model of any real river): how the
return-period and risk redefinitions of Olsen et al. (1998), Cooley (2013),
Salas & Obeysekera (2014), Rootzen & Katz (2013) and Read & Vogel (2015) change the
design quantity when annual exceedance probabilities drift.

Base distribution: GEV whose parameters are the L-moment fit (lmomco/lmom/lmoments3
agree to 1e-14) to the systematic annual peaks of USGS 08167000 bundled in lmomco.
Hypothetical drift: all flows scale by (1+g)^t (GEV location and scale both grow by a
factor (1+g) per year, shape fixed) -- a 'flood magnification' toy in the spirit of
Vogel, Yaindl and Walter (2011).
Usage: python nonstationary_toy.py <l1> <l2> <t3> [--loc-only]   (L-moments of the record)
--loc-only drifts only the GEV location (scale fixed), for comparison.
"""
import math
import sys

import numpy as np
from scipy import optimize, special, stats


def gev_from_lmoments(l1, l2, t3):
    # Hosking (1990) approximation, k in Hosking's sign convention (= scipy c)
    c = 2.0 / (3.0 + t3) - math.log(2) / math.log(3)
    k = 7.8590 * c + 2.9554 * c * c
    g = special.gamma(1 + k)
    alpha = l2 * k / ((1 - 2 ** (-k)) * g)
    xi = l1 - alpha * (1 - g) / k
    return xi, alpha, k


l1, l2, t3 = map(float, sys.argv[1:4])
LOC_ONLY = "--loc-only" in sys.argv[4:]
sc = (lambda g, t: alpha) if LOC_ONLY else (lambda g, t: alpha * (1 + g) ** t)
print("drift:", "location only" if LOC_ONLY else "location and scale (all flows scale by (1+g)^t)")
xi0, alpha, k = gev_from_lmoments(l1, l2, t3)
dist0 = stats.genextreme(c=k, loc=xi0, scale=alpha)
q100 = float(dist0.ppf(0.99))
print(f"stationary GEV(xi={xi0:.1f}, alpha={alpha:.1f}, k={k:.4f}); Q(AEP 0.01) = {q100:.0f}")
print("stationary: T = 1/p = 100 yr; risk over 50 yr = 1-(0.99)^50 = %.4f" % (1 - 0.99 ** 50))

H = 2000  # horizon long enough for the waiting-time sum to converge
for g in (0.0, 0.002, 0.005, 0.01):
    t = np.arange(1, H + 1)
    p = 1 - stats.genextreme.cdf(q100, c=k, loc=xi0 * (1 + g) ** t, scale=sc(g, t))
    surv = np.cumprod(1 - p)                       # P(no exceedance in years 1..x)
    T_ewt = 1 + surv[:-1].sum()                    # expected waiting time (Olsen; Salas-Obeysekera)
    risk50 = 1 - surv[49]                          # P(at least one exceedance in 50 yr)
    # design-life level: z with prod_{t<=50} F_t(z) = 0.99**50 (same 50-yr risk as stationary 1% design)
    target = 0.99 ** 50
    f = lambda z: np.sum(np.log(stats.genextreme.cdf(z, c=k, loc=xi0 * (1 + g) ** t[:50], scale=sc(g, t[:50])))) - math.log(target)
    dll = optimize.brentq(f, q100 * 0.5, q100 * 20)
    print(f"g={g:5.3f}/yr: p(year1)={p[0]:.5f} p(year50)={p[49]:.5f} | expected waiting time={T_ewt:7.1f} yr | "
          f"50-yr risk of exceeding Q100={risk50:.4f} | 50-yr design-life level at stationary risk={dll:.0f} ({dll / q100 - 1:+.1%})")
