#!/usr/bin/env python3
"""TOY Monte Carlo (not rpact) illustrating why adaptive sample-size
modification needs a combination test.  Two-stage, one-sided alpha = 0.025,
normal outcome with known variance, H0 true (effect 0).

Stage-wise z statistics z1, z2 are independent N(0,1) under H0 whatever the
stage-2 sample size, because stage 2 uses new patients.  The stage-2 sample
size n2 is chosen from z1 by a 'promising zone' rule:
    n2 = n1                      if z1 <= 0.5 or z1 >= 2.0
    n2 = 4 * n1 (cap)            if 0.5 < z1 < 2.0
Tests compared (no early stopping, to isolate the adaptation effect):
  naive pooled   Z = (sqrt(n1) z1 + sqrt(n2) z2) / sqrt(n1 + n2)  (actual n2)
  CHW / inverse normal with prespecified weights w1 = w2 = sqrt(1/2)
  Fisher product  p1 * p2 <= exp(-chi2_{4,1-alpha} / 2)
Also evaluates Bauer-Koehne (1994) two-stage Fisher design with early
efficacy stop alpha1 and binding futility alpha0:
  alpha = alpha1 + c * (ln alpha0 - ln alpha1)
Usage: python3 adaptive_ssr_toy.py [reps] [seed]   (requires numpy)
"""
import math
import sys
import numpy as np

SQ2 = math.sqrt(2.0)


def upper_p(z):
    return 0.5 * np.vectorize(math.erfc)(z / SQ2)


def norm_ppf_upper(p):
    lo, hi = -40.0, 40.0
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if 0.5 * math.erfc(mid / SQ2) > p:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def chi2_4_upper_quantile(alpha):
    # chi2 with 4 df: survival = exp(-x/2) (1 + x/2)
    lo, hi = 0.0, 200.0
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if math.exp(-mid / 2) * (1 + mid / 2) > alpha:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def main():
    reps = int(sys.argv[1]) if len(sys.argv) > 1 else 4000000
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 20261120
    alpha = 0.025
    rng = np.random.default_rng(seed)
    z1 = rng.standard_normal(reps)
    z2 = rng.standard_normal(reps)
    n1 = 1.0
    n2 = np.where((z1 > 0.5) & (z1 < 2.0), 4.0, 1.0)
    zc = norm_ppf_upper(alpha)
    naive = (math.sqrt(n1) * z1 + np.sqrt(n2) * z2) / np.sqrt(n1 + n2)
    chw = (z1 + z2) / SQ2
    # vectorised normal tail via numpy erfc substitute: use math.erfc through frompyfunc
    erfc = np.frompyfunc(math.erfc, 1, 1)
    p1 = (0.5 * erfc(z1 / SQ2)).astype(float)
    p2 = (0.5 * erfc(z2 / SQ2)).astype(float)
    c_fisher = math.exp(-chi2_4_upper_quantile(alpha) / 2)
    mcse = math.sqrt(alpha * (1 - alpha) / reps)
    print(f'reps={reps} seed={seed} alpha={alpha} z_crit={zc:.6f} fisher c={c_fisher:.6f} MCSE~{mcse:.5f}')
    print(f'P(promising zone, n2 increased) = {np.mean(n2 > 1):.4f}')
    print(f'[rule A: promising zone 0.5<z1<2.0 -> n2=4n1]')
    print(f'naive pooled test  type I error = {np.mean(naive > zc):.5f}')
    print(f'CHW inverse normal type I error = {np.mean(chw > zc):.5f}')
    # rule B: increase when interim is weak but positive
    n2b = np.where((z1 > 0.0) & (z1 < 1.2), 4.0, 1.0)
    naive_b = (z1 + np.sqrt(n2b) * z2) / np.sqrt(1.0 + n2b)
    print(f'[rule B: weak-positive zone 0<z1<1.2 -> n2=4n1] P(increase)={np.mean(n2b > 1):.4f}')
    print(f'naive pooled test  type I error = {np.mean(naive_b > zc):.5f}  (CHW unchanged: {np.mean(chw > zc):.5f})')
    # rule C: per z1, choose m in {1,4} maximising the naive conditional rejection probability
    erfc_ = np.frompyfunc(math.erfc, 1, 1)
    def cond_rej(m):
        thr = (zc * np.sqrt(1.0 + m) - z1) / np.sqrt(m)
        return (0.5 * erfc_(thr / SQ2)).astype(float)
    m_c = np.where(cond_rej(4.0) > cond_rej(1.0), 4.0, 1.0)
    naive_c = (z1 + np.sqrt(m_c) * z2) / np.sqrt(1.0 + m_c)
    print(f'[rule C: adversarial choice of n2 in {{n1, 4n1}} given z1] P(increase)={np.mean(m_c > 1):.4f}')
    print(f'naive pooled test  type I error = {np.mean(naive_c > zc):.5f}  (CHW unchanged: {np.mean(chw > zc):.5f})')
    print(f'Fisher product     type I error = {np.mean(p1 * p2 <= c_fisher):.5f}')
    # Bauer-Koehne with early stopping
    a1, a0 = 0.0102, 0.5
    c = (alpha - a1) / (math.log(a0) - math.log(a1))
    rej = (p1 <= a1) | ((p1 > a1) & (p1 <= a0) & (p1 * p2 <= c))
    print(f'Bauer-Koehne alpha1={a1} alpha0={a0}: c = {c:.6f}; '
          f'closed-form size = {a1 + c * (math.log(a0) - math.log(a1)):.6f}; simulated = {np.mean(rej):.5f}')
    rej_nb = (p1 <= a1) | ((p1 > a1) & (p1 * p2 <= c))
    print(f'  same c with futility ignored (non-binding use): simulated = {np.mean(rej_nb):.5f}')


if __name__ == '__main__':
    main()
