#!/usr/bin/env python3
"""Absolute maximum simple-span moment of the HL-93 design truck (truck only, no lane, no IM) in the
SI-edition values used by pycba.VehicleLibrary.US.get_hl93_truck() (35/145/145 kN at 4.3 m + 4.3 m)
versus the US-customary values (8/32/32 kip at 14 ft + 14 ft). Pure statics on a fine grid of truck
positions and sections; independent of pycba."""
import numpy as np


def absmax(P, xc, L):
    P = np.array(P, float); xc = np.array(xc, float)
    fronts = np.linspace(0, L + xc[-1], 20001); secs = np.linspace(0, L, 2001)
    best = 0.0
    for f in fronts:
        pos = f - xc; on = (pos >= 0) & (pos <= L)
        M = np.zeros_like(secs)
        for Pi, pi in zip(P[on], pos[on]):
            M += Pi * np.where(secs <= pi, secs * (L - pi) / L, pi * (L - secs) / L)
        best = max(best, M.max())
    return best


KIP, FT = 4.4482216, 0.3048
for L in (10.0, 20.0, 40.0):
    si = absmax([35, 145, 145], [0, 4.3, 8.6], L)
    us = absmax([8 * KIP, 32 * KIP, 32 * KIP], [0, 14 * FT, 28 * FT], L)
    print(f"L={L} m: SI-edition truck {si:.1f} kN.m, customary truck {us:.1f} kN.m, ratio {si / us:.4f}")
