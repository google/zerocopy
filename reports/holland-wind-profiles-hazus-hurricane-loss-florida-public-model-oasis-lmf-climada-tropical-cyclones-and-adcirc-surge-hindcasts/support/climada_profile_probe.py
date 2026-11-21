"""Execute CLIMADA's own Holland wind-profile functions (unmodified bodies) under numpy.

Subject: CLIMADA-project/climada_python@cc0b21516a156384f718e328c59b60138dc1775c,
file climada/hazard/trop_cyclone/trop_cyclone_windfields.py.

The installed environment has numpy only (no xarray/pint/climada), so this script
extracts selected top-level function definitions from the pinned source with `ast`,
and executes them in a namespace that provides: numpy, a tiny dict-based stand-in for
the xarray Dataset (items expose `.values`), `xr.full_like`, and the module constants
(unit factors written numerically: MBAR_TO_PA=100, H_TO_S=3600, KM_TO_M=1000; DEF_* as
in the source). Function bodies are not edited. The stand-in only supports the
operations these functions use.

Usage: python3 climada_profile_probe.py [path/to/trop_cyclone_windfields.py]
(without a path the file is fetched from raw.githubusercontent.com at the pinned SHA).
Also runs the independent toy re-implementation in holland_toy.py on the same storm
as a differential check of that toy.
"""
import ast
import hashlib
import math
import os
import sys
import time
import types
import urllib.request

import numpy as np

sys.dont_write_bytecode = True  # keep the support directory free of __pycache__

SHA = "cc0b21516a156384f718e328c59b60138dc1775c"
REL = "climada/hazard/trop_cyclone/trop_cyclone_windfields.py"
if len(sys.argv) > 1:
    src = open(sys.argv[1]).read()
else:
    url = f"https://raw.githubusercontent.com/CLIMADA-project/climada_python/{SHA}/{REL}"
    req = urllib.request.Request(url, headers={"User-Agent": "research-bot"})
    src = urllib.request.urlopen(req, timeout=60).read().decode()
print("sha256(source) =", hashlib.sha256(src.encode()).hexdigest())

WANT = ["_vgrad", "_rho_air", "_bs_holland_2008", "_v_max_s_holland_2008",
        "_B_holland_1980", "_b_holland_clip_interval", "_stat_holland_1980",
        "_compute_angular_windspeeds_h1980", "_compute_angular_windspeeds_h08"]
tree = ast.parse(src)
defs = {n.name: n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name in WANT}
assert set(defs) == set(WANT), set(WANT) - set(defs)
for n in WANT:
    print(f"extracted {n}: source lines {defs[n].lineno}-{defs[n].end_lineno}")


class Arr(np.ndarray):
    @property
    def values(self):
        return np.asarray(self)


class Track(dict):
    def __getitem__(self, k):
        return np.asarray(dict.__getitem__(self, k), dtype=float).view(Arr)


xr = types.SimpleNamespace(Dataset=Track,
                           full_like=lambda a, v, dtype=float: np.full_like(np.asarray(a, dtype=dtype), v))
from typing import Optional, Tuple, Union  # noqa: E402

ns = dict(np=np, xr=xr, Optional=Optional, Tuple=Tuple, Union=Union,
          MBAR_TO_PA=100.0, H_TO_S=3600.0, KM_TO_M=1000.0,
          DEF_RHO_AIR=1.15, DEF_GRADIENT_TO_SURFACE_WINDS=0.9, T_ICE_K=273.16,
          LOGGER=None)
mod = ast.Module(body=[defs[n] for n in WANT], type_ignores=[])
exec(compile(mod, REL, "exec"), ns)

# Reference storm (illustrative; not fitted to any event).
VMAX = 50.0        # 1-min sustained 10-m wind, m/s (CLIMADA convention for "vmax")
PCEN, PENV = 950.0, 1010.0  # hPa
RMAX_KM, LAT, VT = 40.0, 25.0, 5.0
F_COR = 2 * 7.29e-5 * math.sin(math.radians(LAT))
radii_km = np.array([10, 20, 30, 40, 50, 60, 80, 120, 200, 300], dtype=float)


def make_track():
    t = Track()
    t["time"] = np.array([0.0, 1.0])
    t["lat"] = np.array([LAT, LAT])
    t["tstep"] = np.array([3600.0, 3600.0])
    t["cen"] = np.array([PCEN, PCEN]) * 100
    t["env"] = np.array([PENV, PENV]) * 100
    t["pdelta"] = (np.array([PENV, PENV]) - np.array([PCEN, PCEN])) * 100
    t["vmax"] = np.array([VMAX, VMAX])
    t["vtrans_norm"] = np.array([VT, VT])
    t["rad"] = np.array([RMAX_KM, RMAX_KM]) * 1000
    t["cp"] = np.array([F_COR, F_COR])
    return t


d = np.tile(radii_km * 1000, (2, 1))
m = np.ones_like(d, dtype=bool)
out = {}
for name, fn in [("H1980", ns["_compute_angular_windspeeds_h1980"]),
                 ("H08", ns["_compute_angular_windspeeds_h08"])]:
    tr = make_track()
    v = fn(tr, d.copy(), m)
    out[name] = v[1]
    print(f"{name}: hol_b={float(tr['hol_b'][1]):.5f} rho={float(tr['rho_air'][1]):.3f} "
          f"vgrad={float(tr['vgrad'][1]) if 'vgrad' in tr else float('nan'):.4f}")
print("r_km   " + " ".join(f"{r:7.0f}" for r in radii_km))
for k, v in out.items():
    print(f"{k:6s} " + " ".join(f"{x:7.3f}" for x in v))
print("(angular wind speed, m/s; translational vector not yet added; H1980 already x0.9)")
# _compute_windfields (l.1227-1242) subtracts vtrans_norm*min(1, rmax/r) from H08/H10 angular
# speeds before adding the translational vector back; replicate that one step here (own code).
corr = np.minimum(1.0, RMAX_KM / radii_km)
h08_ang = out["H08"] - VT * corr
print("H08-vt " + " ".join(f"{x:7.3f}" for x in h08_ang)
      + "   (H08 after the l.1240-1242 subtraction; comparable with H1980 row)")
print("ratio  " + " ".join(f"{x:7.4f}" for x in h08_ang / out["H1980"]))

# rho=None branch (Holland 2008 eq. 9 density) for H08
tr = make_track()
v = ns["_compute_angular_windspeeds_h08"](tr, d.copy(), m, rho_air_const=None)
print(f"H08 rho_air_const=None: rho={float(tr['rho_air'][1]):.4f} hol_b={float(tr['hol_b'][1]):.5f} "
      f"v(Rmax)={v[1][3]:.3f}")

# Differential check against the independent toy (holland_toy.py, same directory).
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import holland_toy as toy  # noqa: E402
toy_h80 = toy.climada_h1980_recipe(VMAX, PCEN, PENV, RMAX_KM, LAT, VT, radii_km)
toy_h08 = toy.climada_h08_recipe(VMAX, PCEN, PENV, RMAX_KM, LAT, VT, radii_km)
print("max|upstream-toy| H1980 = %.2e m/s, H08 = %.2e m/s"
      % (np.max(np.abs(out["H1980"] - toy_h80)), np.max(np.abs(out["H08"] - toy_h08))))

# Throughput of the upstream _stat_holland_1980 body on 1e6 node-centroid pairs.
n = 1_000_000
tr = make_track()
ns["_vgrad"](tr, 0.9)
ns["_rho_air"](tr, 1.15)
ns["_B_holland_1980"](tr)
dd = np.tile(np.linspace(2e3, 3e5, n // 2), (2, 1))
mm = np.ones_like(dd, dtype=bool)
best = 1e9
for _ in range(5):
    t0 = time.perf_counter()
    ns["_stat_holland_1980"](tr, dd, mm)
    best = min(best, time.perf_counter() - t0)
print(f"_stat_holland_1980: {dd.size} evaluations, best of 5 = {best*1e3:.1f} ms "
      f"({dd.size/best/1e6:.1f} M evals/s)")
