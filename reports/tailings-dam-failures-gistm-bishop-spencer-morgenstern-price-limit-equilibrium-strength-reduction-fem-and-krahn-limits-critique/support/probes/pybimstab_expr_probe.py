#!/usr/bin/env python3
"""Evaluate, in plain CPython, the two Boolean expressions that pyBIMstab
(eamontoyaa/pyBIMstab @ ca13d23379c60453e1df53c6d3849902e3c600e0) uses for
convergence bookkeeping, copied verbatim:

  pybimstab/slopestabl.py:409 and :487
      if i > 5 and all((fs[-1] - fs[-2], fs[-2] - fs[-3])) <= self.tol:
  pybimstab/slopestabl.py:657
      idx2interp = np.where(tolM and tolF)

This exercises the expressions only, not pyBIMstab itself (which needs scipy,
matplotlib and shapely).
"""
tol = 1e-3
cases = {
    "converged to 1e-9 (diffs 1e-9, 2e-9)": [2.0, 2.0 + 2e-9, 2.0 + 1e-9],
    "diverging (diffs 0.5, 0.4)":          [1.0, 1.4, 1.9],
    "one exact repeat (diffs 0.0, 0.3)":   [1.0, 1.3, 1.3],
    "oscillating (diffs -0.2, +0.2)":      [1.2, 1.4, 1.2],
}
print("fs[-3:]  ->  all((d1, d2))  ->  all(...) <= tol")
for name, fs in cases.items():
    a = all((fs[-1] - fs[-2], fs[-2] - fs[-3]))
    print(f"{name:40s} all={a!s:5s}  flag={a <= tol}")

tolM = [True, False, False, True]
tolF = [False, True, True, True]
print()
print("tolM and tolF ->", tolM and tolF, "(Python 'and' on two non-empty lists returns the second list)")
print("element-wise AND would be ->", [m and f for m, f in zip(tolM, tolF)])
