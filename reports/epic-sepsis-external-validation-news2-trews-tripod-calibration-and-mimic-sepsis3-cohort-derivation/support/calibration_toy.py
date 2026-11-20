#!/usr/bin/env python3
"""TOY MODEL (synthetic data; not a property of any deployed sepsis model).

Shows three textbook facts used in REPORT.md:
  1. AUROC is invariant to a strictly monotone transform of the score, while
     calibration intercept and slope are not.
  2. At fixed sensitivity and specificity, PPV and alert burden move with
     prevalence (a pure case-mix shift).
  3. Logistic recalibration (fitting a + b*logit(p)) restores weak calibration
     without changing AUROC.
Requires numpy. Seeded for reproducibility.
"""
import time
import numpy as np

t0 = time.perf_counter()
rng = np.random.default_rng(20261120)
n = 200_000
x = rng.normal(size=n)
true_logit = -3.0 + 1.2 * x            # synthetic outcome model, prevalence ~7%
y = rng.random(n) < 1 / (1 + np.exp(-true_logit))

def auroc(score, y):
    order = np.argsort(score, kind="mergesort")
    ranks = np.empty(n); ranks[order] = np.arange(1, n + 1)
    # average ranks for ties are not needed for continuous scores
    n1 = y.sum(); n0 = n - n1
    return (ranks[y].sum() - n1 * (n1 + 1) / 2) / (n1 * n0)

def logistic_fit(z, y, iters=50):
    """Newton-Raphson fit of y ~ a + b*z. Returns (a, b)."""
    X = np.column_stack([np.ones_like(z), z]); w = np.zeros(2)
    for _ in range(iters):
        p = 1 / (1 + np.exp(-X @ w))
        g = X.T @ (y - p); H = (X * (p * (1 - p))[:, None]).T @ X
        w = w + np.linalg.solve(H, g)
    return w

def intercept_given_slope1(z, y, iters=50):
    a = 0.0
    for _ in range(iters):
        p = 1 / (1 + np.exp(-(a + z)))
        a += (y - p).sum() / (p * (1 - p)).sum()
    return a

def report(name, p):
    z = np.log(p / (1 - p))
    a, b = logistic_fit(z, y)
    citl = intercept_given_slope1(z, y)
    print(f"{name:<34} AUROC={auroc(p, y):.4f} mean_pred={p.mean():.4f} obs={y.mean():.4f} "
          f"cal_intercept(slope=1)={citl:+.3f} cal_slope={b:.3f}")

p_true = 1 / (1 + np.exp(-true_logit))
report("well calibrated", p_true)
report("overconfident (logit x 2)", 1 / (1 + np.exp(-(2 * true_logit))))
report("shifted (+1.5 on logit scale)", 1 / (1 + np.exp(-(true_logit + 1.5))))
bad = 1 / (1 + np.exp(-(2 * true_logit + 1.0)))
z = np.log(bad / (1 - bad)); a, b = logistic_fit(z, y)
report("recalibrated from overconfident", 1 / (1 + np.exp(-(a + b * z))))

print()
print("Fixed sensitivity 0.33 / specificity 0.83, varying prevalence:")
for prev in [0.02, 0.05, 0.066, 0.10, 0.20]:
    ppv = 0.33 * prev / (0.33 * prev + 0.17 * (1 - prev))
    print(f"  prevalence={prev:.3f}: PPV={ppv:.3f} alert_fraction={0.33*prev + 0.17*(1-prev):.3f} NNE={1/ppv:.1f}")
print(f"elapsed_s={time.perf_counter() - t0:.3f}")
