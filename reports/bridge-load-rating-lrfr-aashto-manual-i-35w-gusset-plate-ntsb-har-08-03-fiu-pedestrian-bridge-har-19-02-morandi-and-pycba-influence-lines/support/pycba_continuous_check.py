#!/usr/bin/env python3
"""Two-span continuous beam (2 x 20 m, constant EI) under the HL-93 design truck from
pycba.VehicleLibrary.US.get_hl93_truck(): pycba run_vehicle envelope extremes at the interior
support and at 0.4L versus an independent reference that sums axle loads times the closed-form
influence lines (three-moment equation) over a fine grid of truck positions, both directions
of the truck being covered by pycba only in the forward direction (as here).
Usage: python3 pycba_continuous_check.py
"""
import time

import numpy as np
import pycba as cba

L, EI = 20.0, 1.0e5


def il_simple_M(x, a, Ls):
    return np.where(x <= a, x * (Ls - a) / Ls, a * (Ls - x) / Ls)


def il_MB(x):
    u = np.where(x <= L, x, 2 * L - x)
    return np.where((x >= 0) & (x <= 2 * L), -u * (L * L - u * u) / (4 * L * L), 0.0)


def il_Ma(x, a):
    inside1 = (x >= 0) & (x <= L)
    return np.where(inside1, il_simple_M(np.clip(x, 0, L), a, L), 0.0) + il_MB(x) * a / L


veh = cba.VehicleLibrary.US.get_hl93_truck()
P, xc = veh.axw.astype(float), veh.axle_coords.astype(float)
fronts = np.linspace(0, 2 * L + xc[-1], 200001)
# add the exact truck positions that put an axle on an influence-line kink (section 0.4L, support B)
fronts = np.unique(np.concatenate([fronts, 0.4 * L + xc, L + xc]))
pos = fronts[:, None] - xc[None, :]
on = (pos >= 0) & (pos <= 2 * L)
MB = (np.where(on, il_MB(pos), 0.0) * P).sum(axis=1)
Ma = (np.where(on, il_Ma(pos, 0.4 * L), 0.0) * P).sum(axis=1)
print(f"reference (closed-form ILs, 200001 grid + kink truck positions): min M_B = {MB.min():.4f} kN.m at front={fronts[MB.argmin()]:.3f}; "
      f"max M(0.4L) = {Ma.max():.4f} kN.m at front={fronts[Ma.argmax()]:.3f}")
bridge = cba.BridgeAnalysis(cba.BeamAnalysis([L, L], EI, [-1, 0, -1, 0, -1, 0]), veh)
for step in (0.5, 0.1, 0.02):
    t0 = time.perf_counter()
    env = bridge.run_vehicle(step)
    dt = time.perf_counter() - t0
    x = env.x
    iB = int(np.argmin(np.abs(x - L)))
    ia = int(np.argmin(np.abs(x - 0.4 * L)))
    print(f"pycba run_vehicle(step={step}): {len(bridge.vResults)} positions in {dt:.3f} s; "
          f"Mmin at x={x[iB]:.3f}: {env.Mmin[iB]:.4f} (ref {MB.min():.4f}, err {env.Mmin[iB] - MB.min():+.4f}); "
          f"Mmax at x={x[ia]:.3f}: {env.Mmax[ia]:.4f} (ref {Ma.max():.4f}, err {env.Mmax[ia] - Ma.max():+.4f})")
