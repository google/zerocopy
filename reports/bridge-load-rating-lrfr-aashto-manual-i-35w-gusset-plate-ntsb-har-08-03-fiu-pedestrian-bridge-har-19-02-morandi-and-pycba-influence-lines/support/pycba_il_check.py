#!/usr/bin/env python3
"""Check pycba (ccaprani/pycba, src/pycba) influence lines and moving-load envelopes
against closed-form beam theory.

Closed forms used (unit load P = 1 at global position x):
  Simple span length L, section at a:
    moment IL  eta_M(x) = x (L - a) / L  for x <= a;  a (L - x) / L  for x >= a
    left-reaction IL eta_RA(x) = 1 - x / L
  Two equal spans L (supports A, B, C at 0, L, 2L), constant EI (three-moment equation):
    interior-support moment M_B(x) = -x (L^2 - x^2) / (4 L^2)              for 0 <= x <= L
                            M_B(x) = -u (L^2 - u^2) / (4 L^2), u = 2L - x  for L <= x <= 2L
    moment at section a in span AB: M_a(x) = eta_M,simple(x; a, L) + M_B(x) * a / L
    (for x in span BC the simple-span term is zero)
  Absolute maximum moment of a simple span under a set of axles that stays on the span
  (resultant theorem): the critical axle and the resultant are placed symmetrically about
  midspan; computed here by exhaustive evaluation over critical axle candidates.
Usage: python3 pycba_il_check.py
"""
import time
import tracemalloc

import numpy as np
import pycba as cba

EI = 1.0e5  # irrelevant for statically determinate effects; any positive value


def il_simple_M(x, a, L):
    return np.where(x <= a, x * (L - a) / L, a * (L - x) / L)


def il_2span_MB(x, L):
    u = np.where(x <= L, x, 2 * L - x)
    return -u * (L * L - u * u) / (4 * L * L)


def il_2span_Ma(x, a, L):
    simple = np.where(x <= L, il_simple_M(np.minimum(x, L), a, L), 0.0)
    return simple + il_2span_MB(x, L) * a / L


def report(name, x, eta, ref):
    err = np.abs(eta - ref)
    i = int(err.argmax())
    print(f"{name}: n={len(x)} max|err|={err.max():.3e} at x={x[i]:.4f} "
          f"(pycba {eta[i]:.6f}, closed form {ref[i]:.6f}); max|ref|={np.abs(ref).max():.6f}")
    return err.max()


def main():
    L = 20.0
    print("pycba version:", cba.__version__)
    # 1. simple span, moment ILs at three sections, reaction IL
    ils = cba.InfluenceLines([L], EI, [-1, 0, -1, 0])
    t0 = time.perf_counter()
    ils.create_ils(step=0.1)
    t_il = time.perf_counter() - t0
    print(f"simple span L={L}: create_ils(step=0.1) wall {t_il:.3f} s for {len(ils.vResults)} analyses")
    for a in (10.0, 6.0, 7.33):
        x, eta = ils.get_il(a, "M")
        report(f"  simple M IL at a={a}", x, eta, il_simple_M(x, a, L))
    x, eta = ils.get_il(0.0, "R")
    report("  simple R IL at A", x, eta, 1 - x / L)
    # section snapping: which result abscissa is used for a=7.33?
    span_x = ils.vResults[0].vRes[0].x
    idx = np.abs(span_x[1:-1] - 7.33).argmin() + 1
    print(f"  section used for poi=7.33: x={span_x[idx]:.6f} (results grid spacing {span_x[2] - span_x[1]:.6f})")

    # 2. two equal spans
    il2 = cba.InfluenceLines([L, L], EI, [-1, 0, -1, 0, -1, 0])
    il2.create_ils(step=0.1)
    x, eta = il2.get_il(L, "M")
    report("two-span M IL at interior support B (poi=L)", x, eta, il_2span_MB(x, L))
    i = int(np.argmin(eta))
    print(f"  min ordinate pycba {eta[i]:.6f} at x={x[i]:.3f}; closed form -L/(6*sqrt(3)) = {-L / (6 * np.sqrt(3)):.6f} "
          f"at x=L/sqrt(3)={L / np.sqrt(3):.3f}")
    x, eta = il2.get_il(8.0, "M")
    report("two-span M IL at a=0.4L in span AB", x, eta, il_2span_Ma(x, 8.0, L))

    # 3. moving HL-93 design truck (35/145/145 kN, 4.3 m + 4.3 m) on a simple span
    veh = cba.VehicleLibrary.US.get_hl93_truck()
    P = veh.axw.astype(float)
    xc = veh.axle_coords.astype(float)  # front axle at 0, rear axles behind
    R = P.sum()
    xbar = (P * xc).sum() / R  # resultant distance behind front axle
    best = -1.0
    for k in range(len(P)):
        d = xbar - xc[k]
        xk = L / 2 + d / 2  # critical axle position measured from left support, vehicle moving +x
        front = xk + xc[k]
        pos = front - xc
        if np.all((pos >= 0) & (pos <= L)):
            M = sum(Pi * float(il_simple_M(np.array(pi), xk, L)) for Pi, pi in zip(P, pos))
            best = max(best, M)
    # brute force check of the absolute maximum on a fine grid (independent of pycba)
    secs = np.linspace(0, L, 4001)
    fronts = np.linspace(0, L + xc[-1], 4001)
    bf = 0.0
    for f in fronts:
        pos = f - xc
        on = (pos >= 0) & (pos <= L)
        if not on.any():
            continue
        M = np.zeros_like(secs)
        for Pi, pi in zip(P[on], pos[on]):
            M += Pi * np.where(secs <= pi, secs * (L - pi) / L, pi * (L - secs) / L)
        bf = max(bf, M.max())
    print(f"HL-93 truck on simple span L={L}: resultant {R:.1f} kN at {xbar:.4f} m behind front axle; "
          f"absolute max moment (resultant theorem) {best:.4f} kN.m; fine-grid brute force {bf:.4f} kN.m")
    bridge = cba.BridgeAnalysis(cba.BeamAnalysis([L], EI, [-1, 0, -1, 0]), veh)
    for step in (1.0, 0.5, 0.25, 0.1, 0.05):
        tracemalloc.start()
        t0 = time.perf_counter()
        env = bridge.run_vehicle(step)
        dt = time.perf_counter() - t0
        peak = tracemalloc.get_traced_memory()[1]
        tracemalloc.stop()
        mmax = float(np.max(env.Mmax))
        print(f"  run_vehicle(step={step}): {len(bridge.vResults)} positions, envelope max M {mmax:.4f} "
              f"(error {mmax - best:+.4f}, {100 * (mmax - best) / best:+.3f}%), wall {dt:.3f} s, "
              f"python peak traced alloc {peak / 1e6:.1f} MB")


if __name__ == "__main__":
    main()
