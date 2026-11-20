#!/usr/bin/env python3
"""Executable demonstrations of two test-harness defects discussed in REPORT.md.

1. numpy.testing.assert_allclose(actual, desired, rtol=1e-07, atol=0, ...) takes rtol as
   its third positional parameter. Passing a "number of decimals" there (as
   statsmodels' CheckRegressionResults.test_standarderrors passes DECIMAL_4 == 4) makes
   the check accept any value within 400 % relative error.
2. Comparing a float (or numpy float64) with a str: ProbFuzz's metrics/lr_smape.py reads
   its threshold as sys.argv[1] (a str) and evaluates `abs(smape) <= smape_thres`.
   Under Python 3 this raises; this script shows the exception types. (The Python 2
   behaviour, where mixed-type comparisons fall back to an arbitrary but consistent type
   ordering, is not executed here.)

Usage: python3 defect_demos.py
"""
import numpy as np

# 1. rtol passed positionally
for actual in (1.0001, 2.0, 4.9, 5.1):
    try:
        np.testing.assert_allclose([actual], [1.0], 4)
        print("assert_allclose([%g], [1.0], 4): passed" % actual)
    except AssertionError:
        print("assert_allclose([%g], [1.0], 4): FAILED" % actual)
try:
    np.testing.assert_allclose([1.0002], [1.0], rtol=10 ** -4)
    print("assert_allclose([1.0002], [1.0], rtol=1e-4): passed")
except AssertionError:
    print("assert_allclose([1.0002], [1.0], rtol=1e-4): FAILED (intended strictness)")

# 2. float vs str comparison
smape = abs(np.mean(np.array([0.01, 0.02, 0.03])))
for lhs in (smape, float(smape)):
    try:
        print(lhs <= "0.1")
    except Exception as e:  # noqa: BLE001
        print("%s <= '0.1' -> %s: %s" % (type(lhs).__name__, type(e).__name__, e))
print("numpy", np.__version__)
