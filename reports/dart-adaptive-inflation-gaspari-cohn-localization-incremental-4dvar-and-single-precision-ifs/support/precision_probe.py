#!/usr/bin/env python3
"""Probe 3: precision and operation-order sensitivity in chaotic toy models.

Basis: execution (toy models Lorenz-63 / Lorenz-96 in numpy, NOT IFS/ectrans/WRF).
Shows (a) float32 vs float64 trajectory divergence time, (b) divergence caused by an
algebraically equivalent re-association of the tendency in float64 (a stand-in for a
compiler/optimization change), (c) statistical (climate) agreement despite trajectory
divergence, (d) the binary32 value of 0.4.
Run: python3 precision_probe.py
"""
import numpy as np


def l63_tend(x, dt_type, reassoc=False):
    s, r, b = dt_type(10.0), dt_type(28.0), dt_type(8.0) / dt_type(3.0)
    X, Y, Z = x[0], x[1], x[2]
    if not reassoc:
        return np.array([s * (Y - X), X * (r - Z) - Y, X * Y - b * Z], dtype=dt_type)
    return np.array([s * Y - s * X, X * r - X * Z - Y, Y * X - Z * b], dtype=dt_type)


def l96_tend(x, F, reassoc=False):
    xp1, xm1, xm2 = np.roll(x, -1), np.roll(x, 1), np.roll(x, 2)
    if not reassoc:
        return (xp1 - xm2) * xm1 - x + F
    return xp1 * xm1 - xm2 * xm1 + (F - x)


def rk4(f, x, dt):
    k1 = dt * f(x); k2 = dt * f(x + k1 / 2); k3 = dt * f(x + k2 / 2); k4 = dt * f(x + k3)
    return x + k1 / 6 + k2 / 3 + k3 / 3 + k4 / 6


def first_exceed(a, b, thr, dt, nsteps, fa, fb):
    first_nonzero = None
    for n in range(1, nsteps + 1):
        a = fa(a); b = fb(b)
        d = np.sqrt(np.mean((a.astype(np.float64) - b.astype(np.float64)) ** 2))
        if first_nonzero is None and d > 0:
            first_nonzero = n
        if d > thr:
            return round(n * dt, 6), first_nonzero
    return None, first_nonzero


def main():
    print("binary32(0.4) =", repr(float(np.float32(0.4))))
    print("binary32 eps =", np.finfo(np.float32).eps, " binary64 eps =", np.finfo(np.float64).eps)
    # Lorenz-63
    dt = 0.01
    x0 = np.array([1.0, 1.0, 1.0])
    for _ in range(1000):
        x0 = rk4(lambda x: l63_tend(x, np.float64), x0, dt)
    x0_32 = x0.astype(np.float32).astype(np.float64)  # same start representable in both
    f64 = lambda x: rk4(lambda y: l63_tend(y, np.float64), x, np.float64(dt))
    f64r = lambda x: rk4(lambda y: l63_tend(y, np.float64, True), x, np.float64(dt))
    f32 = lambda x: rk4(lambda y: l63_tend(y, np.float32), x, np.float32(dt))
    t, fn = first_exceed(x0_32.copy(), x0_32.astype(np.float32), 1.0, dt, 20000, f64, f32)
    print(f"L63 dt={dt}: float64 vs float32 RMS diff > 1.0 at t={t} (first nonzero diff at step {fn})")
    t, fn = first_exceed(x0_32.copy(), x0_32.copy(), 1.0, dt, 20000, f64, f64r)
    print(f"L63 dt={dt}: float64 vs float64-reassociated RMS diff > 1.0 at t={t} (first nonzero diff at step {fn})")
    # Lorenz-96
    N, F, dt = 40, 8.0, 0.05
    rng = np.random.default_rng(0)
    x = 8.0 + rng.standard_normal(N)
    g64 = lambda x: rk4(lambda y: l96_tend(y, np.float64(F)), x, np.float64(dt))
    for _ in range(2000):
        x = g64(x)
    x = x.astype(np.float32).astype(np.float64)
    g64r = lambda x: rk4(lambda y: l96_tend(y, np.float64(F), True), x, np.float64(dt))
    g32 = lambda x: rk4(lambda y: l96_tend(y, np.float32(F)), x, np.float32(dt))
    t, fn = first_exceed(x.copy(), x.astype(np.float32), 1.0, dt, 20000, g64, g32)
    print(f"L96 N=40 F=8 dt={dt}: float64 vs float32 RMS diff > 1.0 at t={t} (first nonzero diff at step {fn})")
    t, fn = first_exceed(x.copy(), x.copy(), 1.0, dt, 20000, g64, g64r)
    print(f"L96 N=40 F=8 dt={dt}: float64 vs float64-reassociated RMS diff > 1.0 at t={t} (first nonzero diff at step {fn})")
    # Climate statistics after trajectories have decorrelated
    a, b = x.copy(), x.astype(np.float32)
    sa, sb = [], []
    for n in range(60000):
        a = g64(a); b = g32(b)
        if n >= 10000:
            sa.append(a.copy()); sb.append(b.astype(np.float64))
    sa = np.array(sa); sb = np.array(sb)
    print(f"L96 climate over 50000 steps: float64 mean={sa.mean():.4f} sd={sa.std():.4f} | float32 mean={sb.mean():.4f} sd={sb.std():.4f}")
    # standard error of the mean using batch means (100 batches)
    bm_a = sa.reshape(100, -1, N).mean(axis=(1, 2)); bm_b = sb.reshape(100, -1, N).mean(axis=(1, 2))
    print(f"   batch-mean standard error of mean: float64 {bm_a.std(ddof=1)/10:.4f}  float32 {bm_b.std(ddof=1)/10:.4f}")


if __name__ == "__main__":
    main()
