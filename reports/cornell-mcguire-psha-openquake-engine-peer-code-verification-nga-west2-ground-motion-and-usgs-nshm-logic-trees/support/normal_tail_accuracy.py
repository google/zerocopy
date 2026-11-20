"""Compare normal-tail (survival) functions used by two hazard codes against
an exact reference, at the epsilons exercised by PEER 2018/03 Test 2.5a.

- erf_as7126: line-for-line port of Maths.erf/erfBase/normalCcdf from
  usgs/nshmp-haz@35e140b8eb665e35d373dbd4a96d2204ce7f2592,
  src/gov/usgs/earthquake/nshmp/util/Maths.java lines 60-79 and 128-130
  (Abramowitz & Stegun 7.1.26 constants).
- oq: openquake.hazardlib.stats.truncnorm_sf imported from the pinned
  gem/oq-engine source tree (phi_b = ndtr(99) means effectively untruncated).
- reference: scipy.special.ndtr (Cephes), cross-checked with mpmath if present.
"""
import math, sys
from scipy.special import ndtr

P = 0.3275911; A1 = 0.254829592; A2 = -0.284496736; A3 = 1.421413741
A4 = -1.453152027; A5 = 1.061405429
SQRT_2 = math.sqrt(2.0)

def erf_base(x):
    t = 1 / (1 + P * x)
    tsq = t * t
    return 1 - (A1 * t + A2 * tsq + A3 * tsq * t + A4 * tsq * tsq + A5 * tsq * tsq * t) * math.exp(-x * x)

def erf_as(x):
    return -erf_base(-x) if x < 0.0 else erf_base(x)

def normal_ccdf_as(mu, sigma, x):
    return (1.0 + erf_as((mu - x) / (sigma * SQRT_2))) * 0.5

try:
    sys.path.insert(0, sys.argv[1])
    from openquake.hazardlib.stats import truncnorm_sf, ndtr as oq_ndtr
    phi_b = float(oq_ndtr(99.0))
    have_oq = True
except Exception as e:  # pragma: no cover
    print('OQ import failed:', e); have_oq = False

print(f"{'eps':>4} {'exact P(Z>eps)':>15} {'A&S7.1.26 port':>15} {'rel.err':>9} {'OQ truncnorm_sf':>16} {'rel.err':>9}")
for eps in [1, 2, 3, 4, 5, 6, 7, 7.5, 8, 8.5, 9]:
    exact = float(ndtr(-eps))
    a = normal_ccdf_as(0.0, 1.0, float(eps))
    row = f"{eps:>4} {exact:15.6e} {a:15.6e} {a/exact-1:+9.2%}"
    if have_oq:
        o = float(truncnorm_sf(phi_b, [float(eps)])[0])
        row += f" {o:16.6e} {o/exact-1 if exact else float('nan'):+9.2%}"
    print(row)
