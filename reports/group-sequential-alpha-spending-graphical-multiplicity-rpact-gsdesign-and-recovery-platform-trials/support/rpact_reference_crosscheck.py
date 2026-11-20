#!/usr/bin/env python3
"""Cross-checks of reference values embedded in rpact's shipped smoke test
(inst/tests/testthat/test-rpact.R at the pinned revision) using independent
computations (NOT rpact):

1. getDesignInverseNormal() defaults (kMax = 3, O'Brien-Fleming, alpha = 0.025
   one-sided, equally spaced): criticalValues c(3.4710914, 2.4544323, 2.0040356),
   alphaSpent c(0.00025917372, 0.0071600594, 0.02499999).  Recomputed with the
   reference quadrature of gsd_numint.py.
2. getDesignFisher() defaults (kMax = 3, alpha = 0.025, no futility):
   criticalValues c(0.012308547, 0.0016635923, 0.00029106687) and alphaSpent
   c(0.012308547, 0.01962413, 0.025).  Checked by Monte Carlo of the
   product-of-p-values rule  p1 <= c1  or  p1 p2 <= c2  or  p1 p2 p3 <= c3
   under H0 (independent uniform p-values).
Usage: python3 rpact_reference_crosscheck.py [mc_reps] [seed]  (requires numpy;
imports gsd_numint.py from the same directory)
"""
import math
import os
import sys
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gsd_numint as g  # noqa: E402


def main():
    reps = int(sys.argv[1]) if len(sys.argv) > 1 else 20000000
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 20261120
    t = [1 / 3, 2 / 3, 1.0]
    C = g.classical_constant(t, lambda x: 1 / math.sqrt(x), 0.025)
    c = [C / math.sqrt(x) for x in t]
    # cumulative alpha spent at each stage with these boundaries
    spent = [g.attained_alpha(t[:k + 1], c[:k + 1]) for k in range(3)]
    rp_c = [3.4710914, 2.4544323, 2.0040356]
    rp_a = [0.00025917372, 0.0071600594, 0.02499999]
    print('== O\'Brien-Fleming kMax=3 alpha=0.025 (rpact getDesignInverseNormal defaults)')
    for k in range(3):
        print(f'   stage {k+1}: c={c[k]:.7f} (rpact test {rp_c[k]})  |d|={abs(c[k]-rp_c[k]):.1e}   '
              f'alphaSpent={spent[k]:.10f} (rpact test {rp_a[k]})  |d|={abs(spent[k]-rp_a[k]):.1e}')
    print('== Fisher combination kMax=3 (rpact getDesignFisher defaults), Monte Carlo')
    rng = np.random.default_rng(seed)
    cf = [0.012308547, 0.0016635923, 0.00029106687]
    rp_af = [0.012308547, 0.01962413, 0.025]
    batch = 5000000
    rej1 = rej2 = rej3 = 0
    done = 0
    while done < reps:
        b = min(batch, reps - done)
        p1 = rng.random(b)
        p2 = rng.random(b)
        p3 = rng.random(b)
        s1 = p1 <= cf[0]
        s2 = (~s1) & (p1 * p2 <= cf[1])
        s3 = (~s1) & (~s2) & (p1 * p2 * p3 <= cf[2])
        rej1 += int(s1.sum())
        rej2 += int(s2.sum())
        rej3 += int(s3.sum())
        done += b
    cum = [rej1 / reps, (rej1 + rej2) / reps, (rej1 + rej2 + rej3) / reps]
    for k in range(3):
        se = math.sqrt(cum[k] * (1 - cum[k]) / reps)
        print(f'   cumulative rejection by stage {k+1}: {cum[k]:.6f} +- {1.96*se:.6f} (95% MC) '
              f'vs rpact alphaSpent {rp_af[k]}')
    print(f'   reps={reps} seed={seed}')


if __name__ == '__main__':
    main()
