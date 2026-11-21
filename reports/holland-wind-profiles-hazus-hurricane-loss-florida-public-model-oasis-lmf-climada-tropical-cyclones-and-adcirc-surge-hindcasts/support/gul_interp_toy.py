"""Toy transliteration of the in-bin damage sampling used by ktools and OasisLMF.

THIS IS A TOY: it re-implements, in numpy, the two inverse-CDF interpolation routines
  * ktools  gulcalc::getgul       (OasisLMF/ktools@4a7506c7..., src/gulcalc/gulcalc.cpp l.181-207)
  * OasisLMF pytools gul get_gul  (OasisLMF/OasisLMF@02aaf854..., oasislmf/pytools/gul/core.py l.11-60)
Both treat damage inside a bin as having a LINEAR density whose mean is the bin's
"interpolation" value; the sample is the root of a quadratic CDF. The real ktools binary
was exercised separately (ktools_probe.sh / gul_paired_shift.py).

Run: python3 gul_interp_toy.py
"""
import numpy as np


def ktools_getgul(bf, bt, bm, pf, pt, r):
    # quadratic branch only; ktools takes sqrt(bb*bb - 4*aa*cc) without a guard
    x = (bm - bf) / (bt - bf)
    w, h = bt - bf, pt - pf
    aa = 3 * h / (w * w) * (2 * x - 1)
    bb = 2 * h / w * (2 - 3 * x)
    cc = pf - r
    with np.errstate(invalid="ignore"):
        return bf + (np.sqrt(bb * bb - 4 * aa * cc) - bb) / (2 * aa)


def oasis_get_gul(bf, bt, bm, pf, pt, r):
    # quadratic branch only; OasisLMF clamps the discriminant at 0 (core.py: disc = max(..., 0.))
    x = (bm - bf) / (bt - bf)
    w, h = bt - bf, pt - pf
    aa = 3. * h / w ** 2 * (2. * x - 1.)
    bb = 2. * h / w * (2. - 3. * x)
    disc = np.maximum(bb ** 2 + 4. * aa * (r - pf), 0.)
    return bf + (np.sqrt(disc) - bb) / (2. * aa)


u = np.linspace(0, 1, 200001)
print("x = (interpolation-bin_from)/(bin_to-bin_from); sampled damage reported as fraction of bin width")
print("   x    mean_of_samples  max_sample  (mean should equal x if the declared mean is honoured)")
for x in [0.1, 0.2, 0.3, 1 / 3, 0.4, 0.6, 2 / 3, 0.7, 0.8, 0.9]:
    d = ktools_getgul(0.0, 1.0, x, 0.0, 1.0, u)
    print(f"{x:6.4f}  {np.nanmean(d):14.4f}  {np.nanmax(d):10.4f}")
print("closed form: discriminant at r = prob_to equals 4 h^2/w^2 (3x-1)^2; at r = prob_from it is bb^2")

# Rounding at the analytic zero of the discriminant (x = 1/3, r = prob_to), float32 inputs.
rng = np.random.default_rng(0)
n = 200000
bf = np.sort(rng.random((n, 2)).astype(np.float32), axis=1)
bt = bf[:, 1]; bf = bf[:, 0]
pf = np.sort(rng.random((n, 2)).astype(np.float32), axis=1)
pt = pf[:, 1]; pf = pf[:, 0]
bm = (bf.astype(np.float64) + (bt.astype(np.float64) - bf) / 3.0).astype(np.float32)
ok = (bt > bf) & (pt > pf)
args = [a[ok].astype(np.float64) for a in (bf, bt, bm, pf, pt)] + [pt[ok].astype(np.float64)]
k = ktools_getgul(*args)
o = oasis_get_gul(*args)
print(f"x=1/3, r=prob_to, {ok.sum()} random float32 bins: ktools-style NaN count = {np.isnan(k).sum()}, "
      f"OasisLMF-style NaN count = {np.isnan(o).sum()}")
