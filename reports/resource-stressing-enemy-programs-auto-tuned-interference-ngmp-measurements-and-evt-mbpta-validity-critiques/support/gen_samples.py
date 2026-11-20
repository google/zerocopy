#!/usr/bin/env python3
"""Generate synthetic execution-time samples for the chronovise driver, and
compute the exact exceedance of a given pWCET value under a mixture that the
"measurement campaign" did not exercise.

All data are synthetic (NumPy, fixed seeds).  They model *statistical* situations
discussed in the MBPTA literature (i.i.d. light tail; serial dependence; a rare
execution mode or interference scenario absent from the campaign); they are not
measurements of any processor.

Usage:
  python3 gen_samples.py gen            # writes s_iid.txt s_ar1.txt s_campaign.txt
  python3 gen_samples.py exceed <w>     # P(X > w) for the deployed mixture
"""
import sys
import numpy as np

N = 20000
Q_RARE = 1e-3          # probability of the rare mode in deployment
RARE_SHIFT = 200.0     # extra cycles in the rare mode (e.g. an unexercised co-runner)


def base(rng, n):
    return 1000.0 + rng.gamma(shape=4.0, scale=5.0, size=n)


def gen():
    rng = np.random.default_rng(1)
    np.savetxt("s_iid.txt", base(rng, N), fmt="%.6f")
    rng = np.random.default_rng(2)
    e = rng.gamma(shape=4.0, scale=5.0, size=N) - 20.0
    x = np.empty(N); x[0] = e[0]
    for i in range(1, N):
        x[i] = 0.8 * x[i - 1] + e[i]
    np.savetxt("s_ar1.txt", 1020.0 + x, fmt="%.6f")
    rng = np.random.default_rng(3)
    np.savetxt("s_campaign.txt", base(rng, N), fmt="%.6f")  # rare mode never exercised
    print("wrote s_iid.txt s_ar1.txt s_campaign.txt (n=%d each)" % N)


def exceed(w):
    rng = np.random.default_rng(4)
    m = 10_000_000
    x = base(rng, m)
    rare = rng.random(m) < Q_RARE
    x[rare] += RARE_SHIFT
    p_mix = float(np.mean(x > w))
    p_base = float(np.mean(x[~rare] > w))
    print(f"w={w:.6g}: P_deployed(X>w) = {p_mix:.3e} (Monte Carlo, m={m}); P_campaign(X>w) = {p_base:.3e}")


if __name__ == "__main__":
    if sys.argv[1] == "gen":
        gen()
    else:
        exceed(float(sys.argv[2]))
