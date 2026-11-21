#!/usr/bin/env python3
"""Probe: empirical thermosphere (NRLMSISE-00 / NRLMSIS 2.0 / 2.1 via pymsis)
density response at Starlink insertion altitudes for 3-4 February 2022.

Inputs: observed 3-hourly ap and daily F10.7obs from the GFZ file
Kp_ap_Ap_SN_F107_since_1932.txt (path given as argv[1]). The comparison is
against a COUNTERFACTUAL quiet input (every ap = 6, the daily Ap of
1 February 2022) with identical solar flux, so the ratio isolates the model's
geomagnetic response; it is not a reconstruction of the true density.

    python3 probe_msis_starlink.py Kp_ap_Ap_SN_F107_since_1932.txt
"""
import sys
import time
from datetime import datetime, timedelta

import numpy as np
import pymsis

rows = {}
for line in open(sys.argv[1]):
    if line.startswith("#"):
        continue
    p = line.split()
    d = datetime(int(p[0]), int(p[1]), int(p[2]))
    rows[d] = dict(ap=[int(x) for x in p[15:23]], Ap=int(p[23]), f107=float(p[25]))


def ap_vector(t):
    """MSIS 7-element ap array for UTC time t (storm-time option)."""
    day = datetime(t.year, t.month, t.day)
    idx = t.hour // 3

    def ap_at(k):  # k-th 3-h interval back from current (0 = current)
        dd, ii = day, idx - k
        while ii < 0:
            dd -= timedelta(days=1)
            ii += 8
        return rows[dd]["ap"][ii]

    return [rows[day]["Ap"], ap_at(0), ap_at(1), ap_at(2), ap_at(3),
            np.mean([ap_at(k) for k in range(4, 12)]),
            np.mean([ap_at(k) for k in range(12, 20)])]


def f107_inputs(t):
    day = datetime(t.year, t.month, t.day)
    prev = rows[day - timedelta(days=1)]["f107"]
    window = [rows[day + timedelta(days=k)]["f107"] for k in range(-40, 41)]
    return prev, float(np.mean(window))


lats = np.arange(-52.5, 53, 5.0)  # band reachable from a 53 deg inclination orbit
lons = np.arange(0, 360, 10.0)
# pymsis.calculate evaluates the outer product of dates x lons x lats x alts
w = np.cos(np.deg2rad(lats))[np.newaxis, :] * np.ones((len(lons), 1))  # area weight (lon, lat)
print(f"pymsis {pymsis.__version__}")
for alt in (210.0, 350.0):
    print(f"== altitude {alt:.0f} km: area-weighted mean density, |lat|<=52.5 ==")
    print("  UTC               ap(3h)  ratio_storm/quiet: MSIS-00  MSIS2.0  MSIS2.1")
    for t in [datetime(2022, 2, 3, 1, 30) + timedelta(hours=3 * k) for k in range(16)]:
        f107, f107a = f107_inputs(t)
        ap = ap_vector(t)
        out = []
        for ver in (0, 2.0, 2.1):
            dens = {}
            for label, aps in (("storm", ap), ("quiet", [6] * 7)):
                r = pymsis.calculate(np.datetime64(t), lons, lats, alt,
                                     f107s=f107, f107as=f107a, aps=[aps], version=ver,
                                     geomagnetic_activity=-1)
                rho = r[..., pymsis.Variable.MASS_DENSITY].reshape(len(lons), len(lats))
                dens[label] = np.sum(rho * w) / np.sum(w)
            out.append(dens["storm"] / dens["quiet"])
        print(f"  {t:%Y-%m-%d %H:%M}   {ap[1]:4d}    {out[0]:.3f}   {out[1]:.3f}   {out[2]:.3f}")
t0 = time.perf_counter()
n = 100000
r = pymsis.calculate(np.full(n, np.datetime64("2022-02-04T12:00")), np.random.uniform(0, 360, n),
                     np.random.uniform(-53, 53, n), np.full(n, 210.0), f107s=np.full(n, 129.6), f107as=np.full(n, 110.0),
                     aps=np.full((n, 7), 32.0), version=2.1, geomagnetic_activity=-1)
print(f"timing: {n} MSIS 2.1 point evaluations in {time.perf_counter() - t0:.3f} s")
print("== absolute area-weighted mean mass density (kg/m^3), observed inputs ==")
for alt in (210.0, 350.0):
    t = datetime(2022, 2, 4, 19, 30)
    f107, f107a = f107_inputs(t)
    vals = []
    for ver in (0, 2.0, 2.1):
        r = pymsis.calculate(np.datetime64(t), lons, lats, alt, f107s=f107, f107as=f107a,
                             aps=[ap_vector(t)], version=ver, geomagnetic_activity=-1)
        rho = r[..., pymsis.Variable.MASS_DENSITY].reshape(len(lons), len(lats))
        vals.append(np.sum(rho * w) / np.sum(w))
    print(f"  {t:%Y-%m-%d %H:%M} {alt:.0f} km: MSIS-00 {vals[0]:.3e}  MSIS2.0 {vals[1]:.3e}  MSIS2.1 {vals[2]:.3e}; F10.7(prev day)={f107} F10.7a(81d)={f107a:.1f}")
