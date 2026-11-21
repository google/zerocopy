"""Executable comparison of default tolerance rules in widely used assertion helpers.

Run:  PYTHONPATH=<dir containing _pytest/approx.py and _pytest/warning_types.py> python3 helper_semantics.py

Each row is (actual, expected). For every helper we print PASS/FAIL using that
helper's *default* tolerances. `assert_allclose` and `assertAlmostEqual` are
called in try/except so the outcome is the helper's real verdict.
"""
import math
import sys
import unittest

import numpy as np
from numpy.testing import assert_allclose, assert_almost_equal

try:
    from _pytest.approx import approx
except Exception as e:  # pragma: no cover
    approx = None
    print("approx import failed:", e)

tc = unittest.TestCase()


def v_allclose(a, e):
    try:
        assert_allclose(a, e)
        return "PASS"
    except AssertionError:
        return "FAIL"


def v_almost(a, e):
    try:
        assert_almost_equal(a, e)
        return "PASS"
    except AssertionError:
        return "FAIL"


def v_isclose_np(a, e):
    return "PASS" if bool(np.isclose(a, e)) else "FAIL"


def v_isclose_math(a, e):
    return "PASS" if math.isclose(a, e) else "FAIL"


def v_unittest(a, e):
    try:
        tc.assertAlmostEqual(a, e)
        return "PASS"
    except AssertionError:
        return "FAIL"


def v_approx(a, e):
    if approx is None:
        return "n/a"
    return "PASS" if a == approx(e) else "FAIL"


HELPERS = [
    ("np.testing.assert_allclose", v_allclose),
    ("np.testing.assert_almost_equal", v_almost),
    ("np.isclose", v_isclose_np),
    ("math.isclose", v_isclose_math),
    ("unittest.assertAlmostEqual", v_unittest),
    ("pytest.approx", v_approx),
]

CASES = [
    ("rel err 5e-8 at scale 1", 1.0 + 5e-8, 1.0),
    ("rel err 5e-7 at scale 1", 1.0 + 5e-7, 1.0),
    ("rel err 5e-6 at scale 1", 1.0 + 5e-6, 1.0),
    ("rel err 1e-10 at scale 1e10", 1e10 + 1.0, 1e10),
    ("100% rel err at scale 1e-9", 2e-9, 1e-9),
    ("100% rel err at scale 1e-12", 2e-12, 1e-12),
    ("expected 0, actual 1e-13", 1e-13, 0.0),
    ("expected 0, actual 1e-9", 1e-9, 0.0),
    ("expected 0, actual 1e-300", 1e-300, 0.0),
    ("NaN vs NaN", float("nan"), float("nan")),
    ("inf vs inf", float("inf"), float("inf")),
    ("1e308 vs inf", 1e308, float("inf")),
]


def asymmetry_example():
    """Find a pair where np.isclose(a, b) != np.isclose(b, a) (rtol applies to |b| only)."""
    a = 1.0
    # |a-b| must exceed atol + rtol*|a| but not atol + rtol*|b|; with rtol=1e-5, atol=1e-8
    # that window is (1.001e-5, 1.001e-5 + 1e-5*d), roughly 1e-10 wide.
    b = 1.0 + 1e-8 + 1e-5 + 5e-11
    return a, b, bool(np.isclose(a, b)), bool(np.isclose(b, a)), math.isclose(a, b), math.isclose(b, a)


def main():
    print("python", sys.version.split()[0], "numpy", np.__version__)
    w = max(len(c[0]) for c in CASES)
    print("case".ljust(w), "|", " | ".join(h[0] for h in HELPERS))
    for name, a, e in CASES:
        print(name.ljust(w), "|", " | ".join(f(a, e).ljust(len(h)) for h, f in HELPERS))
    a, b, ab, ba, mab, mba = asymmetry_example()
    print(f"asymmetry: a={a!r} b={b!r} np.isclose(a,b)={ab} np.isclose(b,a)={ba} math.isclose(a,b)={mab} math.isclose(b,a)={mba}")
    # Effective absolute thresholds at a few scales, from each helper's documented rule.
    print("effective tolerance |actual-expected| allowed (expected=x):")
    for x in [0.0, 1e-12, 1e-6, 1.0, 1e6, 1e12]:
        allclose = 0 + 1e-7 * abs(x)
        npisclose = 1e-8 + 1e-5 * abs(x)
        mathisclose = 1e-9 * abs(x)  # max with |actual|*1e-9; shown for actual~expected
        appr = max(1e-6 * abs(x), 1e-12)
        almost = 1.5e-7
        print(f"  x={x:g}: assert_allclose {allclose:.3g}; np.isclose {npisclose:.3g}; math.isclose ~{mathisclose:.3g}; approx {appr:.3g}; assert_almost_equal <{almost:.3g}; assertAlmostEqual ~5e-8 (round to 7 places)")


if __name__ == "__main__":
    main()
