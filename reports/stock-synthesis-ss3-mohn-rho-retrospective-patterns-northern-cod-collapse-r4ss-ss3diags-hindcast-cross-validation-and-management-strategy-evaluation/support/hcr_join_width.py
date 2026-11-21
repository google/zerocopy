#!/usr/bin/env python3
"""Width of the smooth switch used by Stock Synthesis' forecast control rule.

SS_benchfore.tpl (nmfs-ost/ss3-source-code @ 94cea415...) blends the
harvest-control-rule ramp with two logistic "join" functions:

    join1 = 1 / (1 + exp(100 * (SSB_current - H4010_bot * HCR_anchor)))
    join2 = 1 / (1 + exp(100 * (SSB_current - H4010_top * HCR_anchor)))

The slope constant 100 multiplies an absolute spawning-output difference, so the
10 %-90 % transition width is 2*ln(9)/100 spawning-output units whatever the
stock's scale.  This script prints that width and its size relative to an
example intercept B_bot = H4010_bot * HCR_anchor for several unit scales.
The examples are illustrative scales, not properties of any particular stock.
"""
import math

width = 2 * math.log(9) / 100.0
print(f"10-90 % transition width = {width:.5f} spawning-output units")
for b_bot in (0.1, 1.0, 10.0, 1000.0, 100000.0):
    for d in (-0.05, -0.01, 0.0, 0.01, 0.05):
        j = 1.0 / (1.0 + math.exp(100.0 * d))
        if b_bot == 1.0:
            print(f"  SSB - B_bot = {d:+.2f}: join1 = {j:.4f}")
    print(f"B_bot = {b_bot:>9}: width / B_bot = {width / b_bot:.2e}")
