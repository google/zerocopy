#!/usr/bin/env python3
"""Time-step refinement companion to mf6_probe.py Probe B (TVD, DELR = 0.25 m).
Usage: mf6_probe_dt.py <mf6> <workdir>"""
import math, sys
import mf6_probe as P
for nstp in [400, 4000]:
    P.NSTP = nstp
    r = P.probe_b("tvd", 0.25)
    ncol = r["ncol"]; obs = int(round(50.0 / 0.25)) + 1
    h = r["heads"]; grad = (h[0] - h[-1]) / ((ncol - 1) * 0.25)
    v = P.K_B * grad / P.POR; D = P.ALH * v
    times = [t for t, _ in r["conc"]]; sim = [c[obs - 1] for _, c in r["conc"]]
    ana = [P.ogata_banks(50.0, t, v, D) for t in times]
    span = lambda s: next(t for t, c in zip(times, s) if c >= 0.9) - next(t for t, c in zip(times, s) if c >= 0.1)
    rmse = math.sqrt(sum((a - b) ** 2 for a, b in zip(sim, ana)) / len(sim))
    print(f"tvd DELR=0.25 NSTP={nstp} dt={P.PERLEN/nstp:g} d Courant={v*P.PERLEN/nstp/0.25:.3f} "
          f"rmse={rmse:.4f} t10-90_sim={span(sim):.1f} t10-90_ana={span(ana):.1f} "
          f"v^2*dt/2={v*v*P.PERLEN/nstp/2:.5f} D={D:.5f} wall={r['wall']:.3f}s maxrss_kB={r['rss_kb']}")
