#!/usr/bin/env python3
"""Micro-timings for the MOOSE python/mms helpers (pinned revision).
Usage: python3 timings_probe.py <dir containing the upstream mms/ package>
Host class used for the recorded output: x86_64 Linux workstation, Intel Xeon
@ 2.60GHz; Python 3.13, sympy 1.14.0, pandas 3.1.1, matplotlib 3.11.2, numpy 2.5.4.
mooseutils is stubbed (it is only needed to launch a MOOSE executable)."""
import sys
import time
import timeit
import types

sys.modules["mooseutils"] = types.ModuleType("mooseutils")
sys.path.insert(0, sys.argv[1])
t0 = time.perf_counter()
import mms  # noqa: E402
print("import mms (sympy, pandas, matplotlib): %.2f s" % (time.perf_counter() - t0))


def bench(label, *args, **kw):
    ts = []
    for _ in range(5):
        a = time.perf_counter()
        f, _s = mms.evaluate(*args, **kw)
        ts.append(time.perf_counter() - a)
    print("%s: min %.4f s median %.4f s (5 calls, one process; sympy caches)"
          % (label, min(ts), sorted(ts)[2]))
    return f


bench("evaluate() 1-D ADR", "-div(k*grad(u)) + c*diff(u, x) + r*u", "sin(3*x)*exp(x)",
      scalars=["c", "r"], k="1 + x/2")
f = bench("evaluate() 3-D transient ADR", "diff(u,t) + div(v*u) - div(k*grad(u))",
          "sin(x)*cos(y)*exp(z)*t**2", vectors=["v"], k="1 + x*y*z")
print("fparser length of the 3-D source term: %d chars" % len(mms.fparser(f)))
import numpy as np  # noqa: E402
x = np.array([0.05, 0.025, 0.0125])
y = 3 * x**2
n = 20000
t = timeit.timeit(lambda: np.polyfit(np.log10(x), np.log10(y), 1), number=n)
print("np.polyfit(log10 h, log10 e, 1) on 3 points: %.1f us per call" % (1e6 * t / n))
