"""Timing probe: per-point cost and first-call (JIT) latency of heat-stress functions.

Run with an empty NUMBA_CACHE_DIR to include numba compilation in first-call latency:
  NUMBA_CACHE_DIR=$(mktemp -d) /usr/bin/time -v python perf_probe.py
Numbers are single-process wall-clock measurements on the machine where it runs.
"""
import time
import warnings
import numpy as np

warnings.filterwarnings("ignore")
t0 = time.perf_counter()
from pythermalcomfort.models import heat_index_rothfusz, heat_index_lu, utci
import thermofeel as tf
from metpy.calc import heat_index as metpy_hi
from metpy.units import units
print("import pythermalcomfort+thermofeel+metpy: %.2f s" % (time.perf_counter() - t0))

K = 273.15
rng = np.random.default_rng(0)


def first_call(name, fn):
    t = time.perf_counter(); fn(); a = time.perf_counter() - t
    t = time.perf_counter(); fn(); b = time.perf_counter() - t
    print("%-34s first call %.3f s, second call %.6f s" % (name, a, b))


def per_point(name, fn, n, reps=3):
    best = 1e9
    for _ in range(reps):
        t = time.perf_counter(); fn(); best = min(best, time.perf_counter() - t)
    print("%-34s n=%-8d best of %d: %.4f s  = %.0f ns/point" % (name, n, reps, best, best / n * 1e9))


first_call("ptc heat_index_rothfusz (scalar)", lambda: heat_index_rothfusz(30.0, 50.0))
first_call("ptc heat_index_lu (scalar)", lambda: heat_index_lu(30.0, 50.0))
first_call("ptc utci (scalar)", lambda: utci(30.0, 35.0, 1.0, 50.0))

N = 1_000_000
t = rng.uniform(27, 45, N); r = rng.uniform(5, 95, N)
per_point("ptc heat_index_rothfusz", lambda: heat_index_rothfusz(t, r, round_output=False), N)
per_point("thermofeel heat_index_simplified", lambda: tf.calculate_heat_index_simplified(t + K, r), N)
td = tf.calculate_dew_point_from_relative_humidity(r, t + K)
per_point("thermofeel heat_index_adjusted", lambda: tf.calculate_heat_index_adjusted(t + K, td), N)
per_point("metpy heat_index", lambda: metpy_hi(t * units.degC, r * units.percent, mask_undefined=False), N)
tr = t + rng.uniform(0, 30, N); v = rng.uniform(0.5, 10, N)
per_point("ptc utci", lambda: utci(t, tr, v, r, round_output=False), N)
e = tf.calculate_saturation_vapour_pressure(t + K) * r / 100
per_point("thermofeel calculate_utci", lambda: tf.calculate_utci(t + K, v, tr + K, ehPa=e), N)
n2 = 100_000
per_point("thermofeel wbgt_liljegren (sun)", lambda: tf.calculate_wbgt_liljegren(
    t[:n2] + K, r[:n2], np.full(n2, 1013.25), v[:n2], np.full(n2, 800.0), np.full(n2, 0.8), np.full(n2, 0.85)), n2)
n3 = 20_000
per_point("ptc heat_index_lu", lambda: heat_index_lu(t[:n3], r[:n3], round_output=False), n3)
