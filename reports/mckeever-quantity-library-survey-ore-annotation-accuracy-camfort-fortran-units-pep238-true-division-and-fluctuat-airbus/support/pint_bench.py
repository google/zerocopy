"""pint overhead micro-benchmark (measures the real pint at the installed revision
against plain Python floats on the same host; single-threaded, wall clock).

Run: python3 pint_bench.py
Reports: import time, registry construction time, peak RSS after setup,
and per-operation cost for add / multiply / to() conversion.
"""
import resource
import sys
import time
import timeit

t0 = time.perf_counter()
import pint  # noqa: E402

t1 = time.perf_counter()
ureg = pint.UnitRegistry()
t2 = time.perf_counter()
Q_ = ureg.Quantity
a, b = Q_(1.5, "m"), Q_(2.5, "m")
c = Q_(3.0, "s")
f1, f2, f3 = 1.5, 2.5, 3.0
ft = Q_(1.0, "ft")
# Warm caches (pint caches parsed units and conversion factors).
for _ in range(1000):
    a + b; a * c; ft.to("m")

N = 200_000
REPEAT = 5


def best(stmt, g):
    return min(timeit.repeat(stmt, globals=g, number=N, repeat=REPEAT)) / N * 1e9


g = dict(a=a, b=b, c=c, f1=f1, f2=f2, f3=f3, ft=ft)
res = {
    "float add": best("f1 + f2", g),
    "pint add (same unit)": best("a + b", g),
    "float mul": best("f1 * f3", g),
    "pint mul (m*s)": best("a * c", g),
    "pint to('m') from ft": best("ft.to('m')", g),
}
rss_kib = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
print("python", sys.version.split()[0], "pint", pint.__version__)
print(f"import pint: {(t1 - t0) * 1e3:.1f} ms")
print(f"UnitRegistry(): {(t2 - t1) * 1e3:.1f} ms")
print(f"peak RSS after setup: {rss_kib / 1024:.1f} MiB")
for k, v in res.items():
    print(f"{k}: {v:.1f} ns/op")
print(f"ratio pint add / float add: {res['pint add (same unit)'] / res['float add']:.0f}x")
print(f"ratio pint mul / float mul: {res['pint mul (m*s)'] / res['float mul']:.0f}x")
