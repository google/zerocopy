#!/usr/bin/env python3
"""Probe 1: Gaspari-Cohn localization, transcribed from DART cov_cutoff_mod.f90.

Toy check of the *formula* only (Python transcription), not an execution of DART.
Checks: Horner form (live code) == expanded form (commented reference lines);
value/derivative continuity at r=1 and r=2; float32 vs float64 evaluation error;
minimum eigenvalue of the localization matrix on a 40-point periodic 1-D grid
using the DART 1-D periodic distance (shortest arc on a unit-length circle).
Run: python3 gc_probe.py
"""
import numpy as np


def gc_horner(z, c, dtype=np.float64):
    """Transcription of cov_cutoff_mod.f90 (select_localization = 1)."""
    z = dtype(abs(z)); c = dtype(c)
    if z >= c * dtype(2.0):
        return dtype(0.0)
    r = z / c
    if z <= c:
        return ((((dtype(-0.25) * r + dtype(0.5)) * r + dtype(0.625)) * r
                 - dtype(5.0) / dtype(3.0)) * r ** 2 + dtype(1.0))
    return ((((r / dtype(12.0) - dtype(0.5)) * r + dtype(0.625)) * r
             + dtype(5.0) / dtype(3.0)) * r - dtype(5.0)) * r \
        + dtype(4.0) - dtype(2.0) / (dtype(3.0) * r)


def gc_expanded(z, c):
    """Expanded polynomial form (the commented-out lines in the same file)."""
    z = abs(z)
    if z >= 2 * c:
        return 0.0
    r = z / c
    if z <= c:
        return r**5 * (-0.25) + r**4 / 2.0 + r**3 * 5.0 / 8.0 - r**2 * 5.0 / 3.0 + 1.0
    return r**5 / 12.0 - r**4 / 2.0 + r**3 * 5.0 / 8.0 + r**2 * 5.0 / 3.0 - 5.0 * r + 4.0 - 2.0 / (3.0 * r)


def main():
    c = 0.2  # DART assim_tools_nml default 'cutoff' (half-width)
    zs = np.linspace(0.0, 2.2 * c, 200001)
    h = np.array([gc_horner(z, c) for z in zs])
    e = np.array([gc_expanded(z, c) for z in zs])
    print(f"max|horner-expanded| over [0,2.2c] = {np.max(np.abs(h - e)):.3e}")
    h32 = np.array([gc_horner(np.float32(z), np.float32(c), np.float32) for z in zs], dtype=np.float64)
    print(f"max|float32-float64| (horner) = {np.max(np.abs(h32 - h)):.3e}")
    eps = 1e-9
    for rr in (1.0, 2.0):
        zl, zr = rr * c - eps * c, rr * c + eps * c
        print(f"r={rr}: left={gc_horner(zl, c):.12f} right={gc_horner(zr, c):.12f}")
        d = 1e-6 * c
        dl = (gc_horner(zl, c) - gc_horner(zl - d, c)) / d
        dr = (gc_horner(zr + d, c) - gc_horner(zr, c)) / d
        print(f"r={rr}: dleft={dl:.6f} dright={dr:.6f}")
    print(f"value at r=1 exact 5/24 = {5/24:.12f}")
    # Localization matrix on a periodic 1-D grid with DART's 1-D distance.
    n = 40
    x = np.arange(n) / n
    for half in (0.05, 0.1, 0.2, 0.25, 0.3):
        L = np.empty((n, n))
        for i in range(n):
            for j in range(n):
                d = abs(x[i] - x[j])
                if d > 0.5:
                    d = 1.0 - d
                L[i, j] = gc_horner(d, half)
        w = np.linalg.eigvalsh(L)
        print(f"n=40 periodic, half-width={half}: min eig={w.min():+.3e}  max eig={w.max():.3f}")


if __name__ == "__main__":
    main()
