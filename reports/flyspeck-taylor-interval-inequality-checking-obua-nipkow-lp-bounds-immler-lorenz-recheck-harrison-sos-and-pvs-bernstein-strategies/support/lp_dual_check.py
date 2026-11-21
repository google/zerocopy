#!/usr/bin/env python3
"""Exact re-check of the worked linear-programming infeasibility example in
Hales et al., "A formal proof of the Kepler conjecture" (Forum Math. Pi 5,
2017; arXiv:1501.02155v1, Section 9).

System to refute:   x - 1.42 y <= 3.15,  x + y <= 6,  5 <= x <= 10,  0 <= y <= 10.
Slack form (paper eq. (3)): minimize s1 + s2 subject to
    x - 1.42y <= 3.15 + s1,  x + y <= 6 + s2,  5 <= x <= 10,  0 <= y <= 10,
    0 <= s1, 0 <= s2.
The paper's "modified dual solution", one entry per constraint in that order:
    (0.704, 1, -1.705, 0.001, -0.00032, 0, 0.296, 0)
Sign convention used here: a positive multiplier scales the upper-bound form
(a.z <= u); a negative multiplier scales the lower-bound form (a.z >= l, i.e.
lambda*a.z <= lambda*l because lambda < 0). Slacks are set to zero, as in the
paper's description, so the two slack-bound rows (entries 7 and 8, whose
multipliers 0.296 and 0 belong to the slack columns of the dual LP) contribute
nothing to the combined inequality.

The check is exact rational arithmetic (fractions.Fraction); it confirms that
every variable coefficient cancels to exactly 0 and the right-hand side is
negative, which is the entire content of the in-logic check for one LP.
This is a re-execution of the paper's example data, not of the HOL Light
procedure (formal_lp/more_arith/prove_lp.hl), which uses formal integer
arithmetic after scaling by a power of ten.
"""
from fractions import Fraction as F
import time

# rows: (coeffs over (x, y), lower, upper)  -- None = unbounded side
rows = [
    ({"x": F(1), "y": F("-1.42")}, None, F("3.15")),   # x - 1.42y <= 3.15 (+ s1)
    ({"x": F(1), "y": F(1)}, None, F(6)),              # x + y <= 6 (+ s2)
    ({"x": F(1)}, F(5), None),                         # 5 <= x
    ({"x": F(1)}, None, F(10)),                        # x <= 10
    ({"y": F(1)}, F(0), None),                         # 0 <= y
    ({"y": F(1)}, None, F(10)),                        # y <= 10
    ({}, F(0), None),                                  # 0 <= s1 (slack set to 0)
    ({}, F(0), None),                                  # 0 <= s2 (slack set to 0)
]
dual = [F("0.704"), F(1), F("-1.705"), F("0.001"), F("-0.00032"), F(0), F("0.296"), F(0)]

t0 = time.perf_counter()
coef = {"x": F(0), "y": F(0)}
rhs = F(0)
for (a, lo, hi), lam in zip(rows, dual):
    if lam == 0 or not a:
        continue  # slack-bound rows contribute lam*0 = 0 once slacks are fixed at 0
    bound = hi if lam > 0 else lo
    assert bound is not None, "multiplier sign uses a missing bound"
    for v, c in a.items():
        coef[v] += lam * c
    rhs += lam * bound
t1 = time.perf_counter()

print("combined inequality: %s*x + %s*y <= %s" % (coef["x"], coef["y"], rhs))
print("as decimal rhs:", float(rhs))
ok = coef["x"] == 0 and coef["y"] == 0 and rhs < 0
print("INFEASIBILITY CERTIFIED" if ok else "CERTIFICATE REJECTED")
print("check time: %.1f microseconds" % ((t1 - t0) * 1e6))

# Mutation probe: perturb each nonzero multiplier by +/-1e-5 and re-run the same
# exact check. A perturbed vector is still a valid certificate only if every
# variable coefficient still cancels exactly and the rhs stays negative.
def check(d):
    cx, cy, r = F(0), F(0), F(0)
    for (a, lo, hi), lam in zip(rows, d):
        if lam == 0 or not a:
            continue
        b = hi if lam > 0 else lo
        if b is None:
            return False, "sign uses missing bound"
        cx += lam * a.get("x", 0); cy += lam * a.get("y", 0); r += lam * b
    if cx != 0 or cy != 0:
        return False, "residual coefficient x=%s y=%s" % (cx, cy)
    return (r < 0), "rhs=%s" % r

for i, lam in enumerate(dual):
    if lam == 0:
        continue
    for delta in (F(1, 100000), F(-1, 100000)):
        d2 = list(dual); d2[i] = lam + delta
        ok2, why = check(d2)
        print("mutant entry %d %+g: %s (%s)" % (i + 1, float(delta), "ACCEPTED" if ok2 else "rejected", why))
