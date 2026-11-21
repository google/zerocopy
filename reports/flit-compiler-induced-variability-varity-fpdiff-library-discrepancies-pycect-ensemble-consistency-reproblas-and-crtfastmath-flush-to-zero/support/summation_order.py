"""Summation-order sensitivity and a toy order-independent summation.

TOY MODEL. The "reproducible" summation below is a minimal NumPy re-implementation
of the pre-rounding idea (round every addend to a common grid derived from the
global maximum, so that all partial sums are exact and therefore order-independent).
It is NOT ReproBLAS and its timings are NOT ReproBLAS timings.

Run: python3 summation_order.py
"""
import math
import sys
import time

import numpy as np

rng = np.random.default_rng(20261121)
N = 1 << 20
x = rng.standard_normal(N) * 10.0 ** rng.uniform(-6, 6, N)
ref = math.fsum(x)  # correctly rounded sum of the binary64 inputs


def ulps(v):
    return abs(v - ref) / math.ulp(ref)


def seq(a):
    return float(np.add.accumulate(a)[-1])  # strictly left-to-right


def chunked(a, p):
    parts = np.array_split(a, p)
    return float(np.add.accumulate(np.array([seq(c) for c in parts]))[-1])


def preround(a, levels):
    """Toy K-level pre-rounding sum. Order-independent while n*max|a| < 2^(E-1) per level."""
    total = 0.0
    r = a.astype(np.float64).copy()
    n = len(r)
    for _ in range(levels):
        m = float(np.max(np.abs(r)))
        if m == 0.0:
            break
        e = math.frexp(m * n)[1] + 1  # 2^e > 2*n*m
        big = 1.5 * 2.0 ** e
        q = (r + big) - big  # each q_i is a multiple of ulp(big) = 2^(e-52); exact by Sterbenz-style argument
        r = r - q  # exact residual
        total += float(np.add.accumulate(q)[-1])  # exact: all partial sums are multiples of 2^(e-52) below 2^(e+1)
    return total


def preround_orders(a, levels, orders):
    out = set()
    for perm in orders:
        out.add(preround(a[perm], levels))
    return out


def best_time(fn, reps=5):
    t = []
    for _ in range(reps):
        t0 = time.perf_counter()
        fn()
        t.append(time.perf_counter() - t0)
    return min(t)


def main():
    print(f"python {sys.version.split()[0]} numpy {np.__version__} N={N}")
    print(f"reference math.fsum = {ref!r}")
    results = {}
    results["sequential"] = seq(x)
    results["numpy.sum (pairwise)"] = float(np.sum(x))
    for p in (2, 4, 8, 16, 64, 256, 1024):
        results[f"{p} chunks, then combine"] = chunked(x, p)
    perms = [rng.permutation(N) for _ in range(8)]
    for i, pm in enumerate(perms):
        results[f"random permutation {i}"] = seq(x[pm])
    for k, v in results.items():
        print(f"  {k:<28} {v!r:<26} err={ulps(v):8.1f} ulp")
    print(f"distinct results among {len(results)} orderings: {len(set(results.values()))}")
    print(f"max error {max(ulps(v) for v in results.values()):.1f} ulp; max/min spread {max(results.values()) - min(results.values()):.3e}")
    orders = [np.arange(N)] + perms[:4] + [np.arange(N)[::-1]]
    for lv in (1, 2, 3):
        vals = preround_orders(x, lv, orders)
        v = next(iter(vals))
        print(f"toy pre-rounding, {lv} level(s): distinct results over {len(orders)} orderings = {len(vals)}; err = {ulps(v):.3g} ulp")
    # chunked pre-rounding must agree with whole-array pre-rounding only if the grid is global:
    v_whole = preround(x, 2)
    v_chunks_local = sum(preround(c, 2) for c in np.array_split(x, 8))
    print(f"2-level, global grid: {v_whole!r}; 8 chunks each with its OWN local grid, then summed: {v_chunks_local!r}; equal={v_whole == v_chunks_local}")
    print("timings (best of 5 per variant; ratio against one best-of-20 numpy.sum baseline; single thread):")
    base = best_time(lambda: np.sum(x), reps=20)
    for name, fn in [("numpy.sum", lambda: np.sum(x)), ("sequential accumulate", lambda: seq(x)),
                     ("math.fsum", lambda: math.fsum(x)), ("toy pre-rounding K=1", lambda: preround(x, 1)),
                     ("toy pre-rounding K=2", lambda: preround(x, 2)), ("toy pre-rounding K=3", lambda: preround(x, 3))]:
        t = best_time(fn)
        print(f"  {name:<24} {t*1e3:9.3f} ms  ({t / base:6.1f}x numpy.sum)")


if __name__ == "__main__":
    main()
