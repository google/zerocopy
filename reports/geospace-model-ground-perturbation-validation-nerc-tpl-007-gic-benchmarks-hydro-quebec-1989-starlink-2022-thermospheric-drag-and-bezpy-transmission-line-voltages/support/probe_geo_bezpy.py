#!/usr/bin/env python3
"""Probe: bezpy TPL-007 scaling factors, waveform sensitivity of beta, EPRI-21
network GIC under uniform fields, and convolution cost.

Run from a neutral directory with bezpy installed from the pinned source tree:
    cd /tmp && python3 probe_geo_bezpy.py

The driving magnetic waveforms are SYNTHETIC band-limited random series (the
same construction bezpy's own test-suite uses as a stand-in for the NERC
reference waveform, which bezpy does not redistribute). Beta values computed
here are therefore NOT the TPL-007 Table 3 values; they show how beta moves
with the storm spectrum.
"""
import resource
import time
import warnings

import numpy as np
import pandas as pd

import bezpy
from bezpy.tpl007 import (ALPHA_TABLE, BETA_TABLE, QUEBEC_REFERENCE_MODEL,
                          alpha_factor, beta_factor)
from bezpy.tl.network import Network


def storm_like(seed, n=16384, dt=10.0, band=(100.0, 10000.0), exponent=1.0):
    """Copy of bezpy tests/test_tpl007.py::_storm_like (independent Bx, By)."""
    rng = np.random.default_rng(seed)
    freqs = np.fft.rfftfreq(n, d=dt)
    periods = np.divide(1.0, freqs, out=np.full_like(freqs, np.inf), where=freqs > 0)
    amp = np.zeros_like(freqs)
    inb = (freqs > 0) & (periods >= band[0]) & (periods <= band[1])
    amp[inb] = freqs[inb] ** -exponent

    def draw():
        s = np.fft.irfft(amp * np.exp(1j * rng.uniform(0, 2 * np.pi, len(freqs))), n)
        return 1000.0 * s / np.abs(s).max()

    return draw(), draw()


print("== P1: alpha, eq.3 formula vs Table 2 ==")
lat = ALPHA_TABLE["geomagnetic_latitude"].values
f = alpha_factor(lat, method="formula")
t = alpha_factor(lat, method="table")
for L, a1, a2 in zip(lat, f, t):
    print(f"  L={L:4.0f}  formula={a1:.4f}  table={a2:.2f}  diff={a1 - a2:+.4f}")
print(f"  max |formula-table| over Table 2 rows = {np.max(np.abs(f - t)):.4f}")

print("== P2: beta from shipped 1-D models under synthetic waveforms ==")
models = [m for m in BETA_TABLE.index if m in set(bezpy.mt.list_1d_sites())]
sites = [bezpy.mt.get_1d_site(m) for m in models]
rows = {}
configs = [(s, e) for e in (0.5, 1.0, 1.5) for s in (1989, 2003, 2024)]
for seed, expo in configs:
    bx, by = storm_like(seed, exponent=expo)
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        df = beta_factor(sites, bx, by, dt=10)
    rows[(seed, expo)] = df["beta"].values
B = pd.DataFrame(rows, index=models)
B.columns = [f"s{s}_e{e}" for s, e in B.columns]
pub = BETA_TABLE.loc[models, "beta_b"]
summary = pd.DataFrame({
    "table3_beta_b": pub,
    "synthetic_min": B.min(axis=1),
    "synthetic_median": B.median(axis=1),
    "synthetic_max": B.max(axis=1),
})
summary["max_over_min"] = summary["synthetic_max"] / summary["synthetic_min"]
pd.set_option("display.width", 160)
print(summary.round(3).to_string())
for col in B.columns:
    rho = pd.Series(B[col].values).corr(pd.Series(pub.values), method="spearman")
    mae = np.median(np.abs(B[col].values - pub.values))
    print(f"  {col}: spearman_vs_table3={rho:.3f} median_abs_err={mae:.3f}")
print(f"  models compared: {len(models)}")

print("== P3: EPRI 21-bus network, uniform 1 V/km field ==")
net = Network.epri21_benchmark()
print(" ", repr(net))
import json
from importlib.resources import files
raw = json.load(files("bezpy.tl").joinpath("data", "epri21_network.json").open())
bus = {b["id"]: (b["latitude"], b["longitude"]) for b in raw["buses"]}
from bezpy.tl.utils import haversine_dl
res = {}
for name, E in (("north_1Vkm", (1.0, 0.0)), ("east_1Vkm", (0.0, 1.0))):
    V = []
    for br in net.branches:
        la1, lo1 = bus[br["from_bus"]]
        la2, lo2 = bus[br["to_bus"]]
        dl = haversine_dl(np.array([lo1]), np.array([la1]), np.array([lo2]), np.array([la2]))[0]
        V.append(E[0] * dl[0] + E[1] * dl[1])  # (V/km)*(km) = V
    V = np.array(V)
    t0 = time.perf_counter()
    nv = net.solve(V)
    I = net.neutral_currents(nv)
    dt_solve = time.perf_counter() - t0
    res[name] = np.abs(I) / 3.0
    print(f"  {name}: max |I_neutral|/3 = {res[name].max():.3f} A per phase; solve+neutral {dt_solve*1e3:.2f} ms")
ids = [tr["id"] for tr in net.transformers]
tab = pd.DataFrame(res, index=ids).round(3)
print(tab.to_string())
# Line EMFs copied from bezpy tests/test_network.py (EPRI21_LINE_V) and the
# per-phase GSU currents that test compares against (PowerWorld data
# redistributed by PowerModelsGMD.jl, as cited in that test).
EPRI21_LINE_V = np.array([120.60003474069319, 131.6938150979946, 131.6938150979946,
    321.2612206582465, 190.9859010213294, -20.137238063195745, 160.17017349968367,
    -129.27518497259706, 191.1051972595808, 191.1051972595808, 1.4850062354159403,
    -155.55611343458276, 158.17375406876596, -93.15718079092285, 169.82073202204822])
published = {"xf-6-7-7": 59.090, "xf-6-8-8": 59.090, "xf-12-13-9": 22.373,
             "xf-12-14-10": 22.373, "xf-17-18-13": 31.548, "xf-17-19-14": 31.548}
I = net.neutral_currents(net.solve(EPRI21_LINE_V))
by_id = {t: i for i, t in enumerate(ids)}
for tid, ref in published.items():
    mine = abs(I[by_id[tid]]) / 3.0
    print(f"  {tid}: bezpy={mine:.3f} A/phase published={ref:.3f} rel_err={(mine-ref)/ref:+.2e}")

print("== P4: convolution cost (SiteCollection.convolve_fft) ==")
for nsites, ntimes in ((100, 8640), (1000, 8640), (1000, 86400)):
    coll = bezpy.mt.SiteCollection([sites[i % len(sites)] for i in range(nsites)])
    bx, by = storm_like(7, n=ntimes)
    t0 = time.perf_counter()
    Ex, Ey = coll.convolve_fft(bx, by, dt=10)
    el = time.perf_counter() - t0
    print(f"  nsites={nsites:5d} ntimes={ntimes:6d}: {el:.3f} s wall; output {Ex.nbytes/2**20:.1f} MiB per component")
print(f"  peak RSS of this process: {resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024:.0f} MiB")
