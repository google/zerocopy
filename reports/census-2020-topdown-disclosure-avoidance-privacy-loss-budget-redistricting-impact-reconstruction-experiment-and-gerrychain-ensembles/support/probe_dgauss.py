#!/usr/bin/env python3
"""Run the 2020 redistricting DAS release's exact discrete Gaussian sampler
(source/programs/engine/discrete_gaussian_utility.py, function
RationalSimpleDiscreteGaussian -> RationalScalarDiscreteGaussian ->
RationalScalarDiscreteLaplace / RationalScalarBernoulliExp) at three production
sigma^2 values, and compare the empirical moments and pmf with the exact
discrete Gaussian.

What is exercised: the unmodified upstream module, imported from an extracted
tarball of uscensusbureau/DAS_2020_Redistricting_Production_Code at
289ee463936a6f0efcf2e378abe410ec01d0e140.

What is substituted: the uniform-integer source. Production uses
rngs.RDRandLbitInts (RDRAND XOR /dev/urandom with OpenBSD rejection sampling);
for reproducibility this probe uses a seeded adapter exposing the same
.integers(low, high) interface over Python's random.Random.randrange (Mersenne
Twister). A second, unseeded pass uses the release's own rngs.RDRandLbitInts if
the 'randomgen' package and the RDRAND instruction are available.

What is not exercised: the Spark pipeline, the mechanism wrapper in
primitives.py (which adds the integer perturbations to numpy arrays), the
optimizer, and all I/O.

Usage: python3 probe_dgauss.py <path-to-source/programs/engine> [--rdrand]
"""
import math
import random
import sys
import time
from fractions import Fraction as Fr

ENGINE = sys.argv[1]
sys.path.insert(0, ENGINE)
import discrete_gaussian_utility as dgu  # noqa: E402  (stdlib-only upstream module)

GLOBAL_SCALE = Fr(339, 542)


def prod_sigma_sq(qprop, gprop):
    # engine_utils.py:490 inverse_scale = dpq_prop * geolevel_prop / global_scale**2 ; primitives.py:209 sigma_sq = 1/inverse_scale
    return 1 / (qprop * gprop / GLOBAL_SCALE ** 2)


CASES = [
    ("State total (q=3773/4097, g=1440/4099)", prod_sigma_sq(Fr(3773, 4097), Fr(1440, 4099)), 200_000, 20251121),
    ("Block detailed (q=3945/4097, g=165/4099)", prod_sigma_sq(Fr(3945, 4097), Fr(165, 4099)), 200_000, 20251122),
    ("Block total (q=5/4097, g=165/4099)", prod_sigma_sq(Fr(5, 4097), Fr(165, 4099)), 50_000, 20251123),
]


class SeededIntegers:
    """Stand-in for rngs.RDRandLbitInts: same .integers(low, high) contract, arbitrary-size ints."""

    def __init__(self, seed):
        self._r = random.Random(seed)

    def integers(self, low=0, high=0):
        return self._r.randrange(low, high)


def exact_moments(sigma_sq):
    s2 = float(sigma_sq)
    bound = int(math.ceil(40 * math.sqrt(s2))) + 10
    w = [math.exp(-(n * n) / (2 * s2)) for n in range(-bound, bound + 1)]
    z = math.fsum(w)
    var = math.fsum(((n - bound) ** 2) * wi for n, wi in enumerate(w)) / z
    m4 = math.fsum(((n - bound) ** 4) * wi for n, wi in enumerate(w)) / z
    pmf = {n - bound: wi / z for n, wi in enumerate(w)}
    return var, m4, pmf


def summarize(label, sigma_sq, xs, secs, gof=False):
    n = len(xs)
    mean = math.fsum(xs) / n
    var_hat = math.fsum((x - mean) ** 2 for x in xs) / (n - 1)
    var, m4, pmf = exact_moments(sigma_sq)
    se_var = math.sqrt((m4 - var * var) / n)
    se_mean = math.sqrt(var / n)
    line = (f"{label}: sigma_sq={sigma_sq} (~{float(sigma_sq):.4f}); N={n}; "
            f"mean={mean:+.4f} (z={mean / se_mean:+.2f}); var_hat={var_hat:.4f}; exact DG var={var:.4f}; "
            f"rel.dev={(var_hat - var) / var:+.4%} (z={(var_hat - var) / se_var:+.2f}); "
            f"min={min(xs)} max={max(xs)}; wall={secs:.2f}s; throughput={n / secs:,.0f} samples/s")
    print(line)
    if gof:
        counts = {}
        for x in xs:
            counts[x] = counts.get(x, 0) + 1
        sd = math.sqrt(var)
        cut = int(3 * sd)
        bins = list(range(-cut, cut + 1))
        obs = [counts.get(b, 0) for b in bins]
        exp_ = [n * pmf[b] for b in bins]
        tail_obs = n - sum(obs)
        tail_exp = n - sum(exp_)
        obs.append(tail_obs)
        exp_.append(tail_exp)
        chi2 = sum((o - e) ** 2 / e for o, e in zip(obs, exp_))
        dof = len(obs) - 1
        try:
            from scipy.stats import chi2 as chi2dist
            p = chi2dist.sf(chi2, dof)
            print(f"  chi-square GOF vs exact DG pmf: bins=|x|<={cut} plus pooled tail; chi2={chi2:.2f}, dof={dof}, p={p:.3f}")
        except ImportError:
            print(f"  chi-square GOF vs exact DG pmf: bins=|x|<={cut} plus pooled tail; chi2={chi2:.2f}, dof={dof} (scipy unavailable for p-value)")


def main():
    print(f"python {sys.version.split()[0]}; module {dgu.__file__}")
    for label, s2, n, seed in CASES:
        rng = SeededIntegers(seed)
        t0 = time.perf_counter()
        xs = dgu.RationalSimpleDiscreteGaussian(sigma_sq=s2, size=n, rng=rng)
        secs = time.perf_counter() - t0
        assert all(isinstance(x, int) for x in xs)
        summarize(f"[seed {seed}] {label}", s2, xs, secs, gof=True)
    if "--rdrand" in sys.argv:
        import rngs  # upstream module: needs numpy + randomgen
        prod_rng = rngs.DASRDRandIntegers()
        label, s2, _, _ = CASES[1]
        n = 20_000
        t0 = time.perf_counter()
        xs = dgu.RationalSimpleDiscreteGaussian(sigma_sq=s2, size=n, rng=prod_rng)
        secs = time.perf_counter() - t0
        summarize(f"[upstream rngs.RDRandLbitInts, unseeded] {label}", s2, xs, secs, gof=False)


if __name__ == "__main__":
    main()
