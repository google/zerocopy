#!/usr/bin/env python3
"""MODFLOW 6 probes, writing native MF6 input files directly (no FloPy).

Probe A (unconfined Dupuit flow with recharge, Newton-Raphson):
  1 layer x 1 row x 100 columns, DELR = 10 m, K = 10 m/d, bottom 0 m, top 50 m,
  recharge R = 1e-3 m/d, CHD h = 20 m in column 1 and h = 10 m in column 100.
  Sweeps OUTER_DVCLOSE and records outer iterations, PERCENT DISCREPANCY,
  max |h - h_ref| against a tightly converged run (closure error), and
  max |h - h_Dupuit| against the analytical Dupuit-Forchheimer solution between the
  two CHD cell centres (discretization + closure error).

Probe B (1-D advection-dispersion, Ogata-Banks):
  1 x 1 x 200 cells, DELR = 1 m, confined, K = 1 m/d, CHD 10 m / 0 m at the ends,
  porosity 0.25, ALH = 0.1 m (grid Peclet number DELR/ALH = 10), constant
  concentration 1 at column 1, 300 daily time steps.  Compares the breakthrough curve
  at 50 m downstream of the CNC cell centre for ADV schemes upstream/central/tvd/utvd
  with Ogata-Banks, and records min/max concentration (over/undershoot) and transport
  PERCENT DISCREPANCY.

Usage: mf6_probe.py <path-to-mf6-binary> <workdir>
"""
import math
import os
import re
import shutil
import struct
import subprocess
import sys
import time

MF6 = sys.argv[1]
WORK = sys.argv[2]


def w(path, text):
    with open(path, "w") as f:
        f.write(text.strip() + "\n")


def read_heads(path):
    """Read an MF6 binary head/concentration file; return list of (totim, values)."""
    out = []
    with open(path, "rb") as f:
        while True:
            hdr = f.read(4 + 4 + 8 + 8 + 16 + 4 + 4 + 4)
            if len(hdr) < 52:
                break
            kstp, kper, pertim, totim = struct.unpack("<iidd", hdr[:24])
            ncol, nrow, ilay = struct.unpack("<iii", hdr[40:52])
            n = ncol * nrow
            vals = struct.unpack("<%dd" % n, f.read(8 * n))
            out.append((totim, list(vals)))
    return out


def run(ws):
    t0 = time.perf_counter()
    p = subprocess.run(["/usr/bin/time", "-f", "MAXRSS_KB=%M", MF6], cwd=ws,
                       capture_output=True, text=True)
    wall = time.perf_counter() - t0
    rss = re.search(r"MAXRSS_KB=(\d+)", p.stderr)
    return p.returncode, wall, int(rss.group(1)) if rss else None, p.stdout


def lst_value(path, pattern):
    vals = []
    with open(path) as f:
        for line in f:
            m = re.search(pattern, line)
            if m:
                vals.append(float(m.group(1)))
    return vals


def common(ws, nper_block, models, exchanges, slns):
    os.makedirs(ws, exist_ok=True)
    w(os.path.join(ws, "mfsim.nam"), f"""
BEGIN options
END options
BEGIN timing
  TDIS6 sim.tdis
END timing
BEGIN models
{models}
END models
BEGIN exchanges
{exchanges}
END exchanges
BEGIN solutiongroup 1
{slns}
END solutiongroup
""")
    w(os.path.join(ws, "sim.tdis"), f"""
BEGIN options
  TIME_UNITS days
END options
BEGIN dimensions
  NPER 1
END dimensions
BEGIN perioddata
{nper_block}
END perioddata
""")


def ims(path, dvclose, rclose, complexity="simple", extra=""):
    w(path, f"""
BEGIN options
  PRINT_OPTION summary
  COMPLEXITY {complexity}
END options
BEGIN nonlinear
  OUTER_DVCLOSE {dvclose}
  OUTER_MAXIMUM 500
{extra}
END nonlinear
BEGIN linear
  INNER_MAXIMUM 500
  INNER_DVCLOSE {min(dvclose, 1e-3) * 0.1}
  INNER_RCLOSE {rclose}
  LINEAR_ACCELERATION bicgstab
END linear
""")


# ---------------------------------------------------------------- Probe A
NCOL_A, DELR_A, K_A, R_A, H1, H2 = 100, 10.0, 10.0, 1e-3, 20.0, 10.0


def probe_a(dvclose, tag):
    ws = os.path.join(WORK, f"A_{tag}")
    shutil.rmtree(ws, ignore_errors=True)
    common(ws, "  1.0 1 1.0", "  gwf6 gwf.nam gwf", "", "  ims6 gwf.ims gwf")
    ims(os.path.join(ws, "gwf.ims"), dvclose, 1e-6, extra="  UNDER_RELAXATION none")
    w(os.path.join(ws, "gwf.nam"), """
BEGIN options
  NEWTON
END options
BEGIN packages
  DIS6 gwf.dis dis
  NPF6 gwf.npf npf
  IC6 gwf.ic ic
  CHD6 gwf.chd chd
  RCH6 gwf.rch rch
  OC6 gwf.oc oc
END packages
""")
    w(os.path.join(ws, "gwf.dis"), f"""
BEGIN options
  LENGTH_UNITS meters
END options
BEGIN dimensions
  NLAY 1
  NROW 1
  NCOL {NCOL_A}
END dimensions
BEGIN griddata
  delr
    CONSTANT {DELR_A}
  delc
    CONSTANT 1.0
  top
    CONSTANT 50.0
  botm
    CONSTANT 0.0
END griddata
""")
    w(os.path.join(ws, "gwf.npf"), f"""
BEGIN options
END options
BEGIN griddata
  icelltype
    CONSTANT 1
  k
    CONSTANT {K_A}
END griddata
""")
    w(os.path.join(ws, "gwf.ic"), """
BEGIN griddata
  strt
    CONSTANT 30.0
END griddata
""")
    w(os.path.join(ws, "gwf.chd"), f"""
BEGIN dimensions
  MAXBOUND 2
END dimensions
BEGIN period 1
  1 1 1 {H1}
  1 1 {NCOL_A} {H2}
END period
""")
    w(os.path.join(ws, "gwf.rch"), f"""
BEGIN options
  READASARRAYS
END options
BEGIN period 1
  recharge
    CONSTANT {R_A}
END period
""")
    w(os.path.join(ws, "gwf.oc"), """
BEGIN options
  HEAD FILEOUT gwf.hds
  BUDGET FILEOUT gwf.cbc
END options
BEGIN period 1
  SAVE HEAD ALL
  PRINT BUDGET ALL
END period
""")
    rc, wall, rss, _ = run(ws)
    heads = read_heads(os.path.join(ws, "gwf.hds"))[-1][1]
    disc = lst_value(os.path.join(ws, "gwf.lst"), r"PERCENT DISCREPANCY\s*=\s*([-0-9.Ee+]+)")
    outer = lst_value(os.path.join(ws, "mfsim.lst"), r"(\d+) CALLS TO NUMERICAL SOLUTION")
    inner = lst_value(os.path.join(ws, "mfsim.lst"), r"^\s*(\d+) TOTAL ITERATIONS")
    tin = lst_value(os.path.join(ws, "gwf.lst"), r"TOTAL IN =\s*[-0-9.Ee+]+\s+TOTAL IN =\s*([-0-9.Ee+]+)")
    tout = lst_value(os.path.join(ws, "gwf.lst"), r"TOTAL OUT =\s*[-0-9.Ee+]+\s+TOTAL OUT =\s*([-0-9.Ee+]+)")
    calc = 100 * (tin[-1] - tout[-1]) / (0.5 * (tin[-1] + tout[-1])) if tin and tout else None
    return dict(rc=rc, wall=wall, rss_kb=rss, heads=heads, pct_disc=disc[-1] if disc else None,
                outer=int(outer[-1]) if outer else None, inner=int(inner[-1]) if inner else None,
                rate_in=tin[-1] if tin else None, rate_out=tout[-1] if tout else None, calc_disc=calc)


def dupuit(x):
    # x measured from the centre of column 1; L between the two CHD cell centres.
    L = (NCOL_A - 1) * DELR_A
    h2 = H1 ** 2 + (H2 ** 2 - H1 ** 2) * x / L + (R_A / K_A) * x * (L - x)
    return math.sqrt(h2)


# ---------------------------------------------------------------- Probe B
K_B, POR, ALH, NSTP, PERLEN, LEN_B = 1.0, 0.25, 0.1, 400, 400.0, 200.0


def probe_b(scheme, DELR_B):
    NCOL_B = int(round(LEN_B / DELR_B))
    ws = os.path.join(WORK, f"B_{scheme}_{DELR_B:g}")
    shutil.rmtree(ws, ignore_errors=True)
    common(ws, f"  {PERLEN} {NSTP} 1.0", "  gwf6 gwf.nam gwf\n  gwt6 gwt.nam gwt",
           "  GWF6-GWT6 gwfgwt.exg gwf gwt", "  ims6 gwf.ims gwf\n  ims6 gwt.ims gwt")
    w(os.path.join(ws, "gwfgwt.exg"), "BEGIN options\nEND options")
    ims(os.path.join(ws, "gwf.ims"), 1e-9, 1e-9)
    ims(os.path.join(ws, "gwt.ims"), 1e-9, 1e-9)
    dis = f"""
BEGIN options
  LENGTH_UNITS meters
END options
BEGIN dimensions
  NLAY 1
  NROW 1
  NCOL {NCOL_B}
END dimensions
BEGIN griddata
  delr
    CONSTANT {DELR_B}
  delc
    CONSTANT 1.0
  top
    CONSTANT 20.0
  botm
    CONSTANT 0.0
END griddata
"""
    w(os.path.join(ws, "gwf.dis"), dis)
    w(os.path.join(ws, "gwt.dis"), dis)
    w(os.path.join(ws, "gwf.nam"), """
BEGIN packages
  DIS6 gwf.dis dis
  NPF6 gwf.npf npf
  IC6 gwf.ic ic
  CHD6 gwf.chd chd
  OC6 gwf.oc oc
END packages
""")
    w(os.path.join(ws, "gwf.npf"), f"""
BEGIN options
  SAVE_SPECIFIC_DISCHARGE
  SAVE_FLOWS
END options
BEGIN griddata
  icelltype
    CONSTANT 0
  k
    CONSTANT {K_B}
END griddata
""")
    w(os.path.join(ws, "gwf.ic"), "BEGIN griddata\n  strt\n    CONSTANT 5.0\nEND griddata")
    w(os.path.join(ws, "gwf.chd"), f"""
BEGIN options
  SAVE_FLOWS
END options
BEGIN dimensions
  MAXBOUND 2
END dimensions
BEGIN period 1
  1 1 1 10.0
  1 1 {NCOL_B} 0.0
END period
""")
    w(os.path.join(ws, "gwf.oc"), """
BEGIN options
  HEAD FILEOUT gwf.hds
  BUDGET FILEOUT gwf.cbc
END options
BEGIN period 1
  SAVE HEAD LAST
  SAVE BUDGET LAST
END period
""")
    w(os.path.join(ws, "gwt.nam"), """
BEGIN packages
  DIS6 gwt.dis dis
  IC6 gwt.ic ic
  ADV6 gwt.adv adv
  DSP6 gwt.dsp dsp
  MST6 gwt.mst mst
  CNC6 gwt.cnc cnc
  SSM6 gwt.ssm ssm
  OC6 gwt.oc oc
END packages
""")
    w(os.path.join(ws, "gwt.ic"), "BEGIN griddata\n  strt\n    CONSTANT 0.0\nEND griddata")
    w(os.path.join(ws, "gwt.adv"), f"BEGIN options\n  SCHEME {scheme}\nEND options")
    w(os.path.join(ws, "gwt.dsp"), f"""
BEGIN options
  XT3D_OFF
END options
BEGIN griddata
  diffc
    CONSTANT 0.0
  alh
    CONSTANT {ALH}
  ath1
    CONSTANT {ALH / 10}
END griddata
""")
    w(os.path.join(ws, "gwt.mst"), f"""
BEGIN griddata
  porosity
    CONSTANT {POR}
END griddata
""")
    w(os.path.join(ws, "gwt.cnc"), """
BEGIN dimensions
  MAXBOUND 1
END dimensions
BEGIN period 1
  1 1 1 1.0
END period
""")
    w(os.path.join(ws, "gwt.ssm"), "BEGIN options\nEND options\nBEGIN sources\nEND sources")
    w(os.path.join(ws, "gwt.oc"), """
BEGIN options
  CONCENTRATION FILEOUT gwt.ucn
END options
BEGIN period 1
  SAVE CONCENTRATION ALL
  PRINT BUDGET LAST
END period
""")
    rc, wall, rss, _ = run(ws)
    conc = read_heads(os.path.join(ws, "gwt.ucn"))
    heads = read_heads(os.path.join(ws, "gwf.hds"))[-1][1]
    disc = lst_value(os.path.join(ws, "gwt.lst"), r"PERCENT DISCREPANCY\s*=\s*([-0-9.Ee+]+)")
    return dict(rc=rc, wall=wall, rss_kb=rss, conc=conc, heads=heads,
                pct_disc=disc[-1] if disc else None, ncol=NCOL_B)


def ogata_banks(x, t, v, D):
    if t <= 0:
        return 0.0
    a = (x - v * t) / (2 * math.sqrt(D * t))
    b = (x + v * t) / (2 * math.sqrt(D * t))
    term2 = 0.0
    ex = v * x / D
    if ex < 700:
        term2 = math.exp(ex) * math.erfc(b)
    return 0.5 * (math.erfc(a) + term2)


def main():
    os.makedirs(WORK, exist_ok=True)
    print("== Probe A: unconfined Dupuit flow with recharge (NEWTON)")
    ref = probe_a(1e-12, "ref")
    xs = [(j) * DELR_A for j in range(NCOL_A)]
    ana = [dupuit(x) for x in xs]
    print(f"reference dvclose=1e-12: rc={ref['rc']} outer={ref['outer']} inner={ref['inner']} pct_disc={ref['pct_disc']}"
          f" max|h_ref-h_dupuit|={max(abs(a - b) for a, b in zip(ref['heads'], ana)):.3e} m")
    print("dvclose | rc | outer_iters | inner_iters | lst_pct_discrepancy | rate_in | rate_out | recomputed_pct | max|h-h_ref| (m) | max|h-h_dupuit| (m) | wall_s | maxrss_kB")
    for dv in [1.0, 1e-1, 1e-2, 1e-3, 1e-4, 1e-6, 1e-8, 1e-10]:
        r = probe_a(dv, f"{dv:g}")
        e_ref = max(abs(a - b) for a, b in zip(r["heads"], ref["heads"]))
        e_ana = max(abs(a - b) for a, b in zip(r["heads"], ana))
        print(f"{dv:g} | {r['rc']} | {r['outer']} | {r['inner']} | {r['pct_disc']} | {r['rate_in']} | {r['rate_out']} | {r['calc_disc']:.4f} | {e_ref:.3e} | {e_ana:.3e} | {r['wall']:.3f} | {r['rss_kb']}")

    for DELR_B in [1.0, 0.25]:
        print("== Probe B: Ogata-Banks breakthrough at x = 50 m, DELR =", DELR_B, "grid Peclet = DELR/ALH =", DELR_B / ALH)
        for scheme in ["upstream", "central", "tvd", "utvd"]:
            r = probe_b(scheme, DELR_B)
            NCOL_B = r["ncol"]
            OBS_COL = int(round(50.0 / DELR_B)) + 1
            h = r["heads"]
            grad = (h[0] - h[-1]) / ((NCOL_B - 1) * DELR_B)
            v = K_B * grad / POR
            D = ALH * v
            times = [t for t, _ in r["conc"]]
            sim = [c[OBS_COL - 1] for _, c in r["conc"]]
            ana = [ogata_banks(50.0, t, v, D) for t in times]
            rmse = math.sqrt(sum((a - b) ** 2 for a, b in zip(sim, ana)) / len(sim))
            allc = [x for _, c in r["conc"] for x in c]
            # time at which C/C0 first reaches 0.5 at the observation cell
            def t50(series):
                for t, c in zip(times, series):
                    if c >= 0.5:
                        return t
                return None
            # spreading: time between C = 0.1 and C = 0.9
            def tspan(series):
                t1 = next((t for t, c in zip(times, series) if c >= 0.1), None)
                t9 = next((t for t, c in zip(times, series) if c >= 0.9), None)
                return None if t1 is None or t9 is None else t9 - t1
            print(f"{scheme} (DELR={DELR_B}, obs col {OBS_COL}): rc={r['rc']} v={v:.5f} m/d D={D:.5f} m2/d rmse={rmse:.4f} "
                  f"t50_sim={t50(sim)} t50_ana={t50(ana)} t10-90_sim={tspan(sim)} t10-90_ana={tspan(ana)} "
                  f"cmin={min(allc):.3e} cmax={max(allc):.6f} pct_disc={r['pct_disc']} wall={r['wall']:.3f}s maxrss_kB={r['rss_kb']}")


if __name__ == "__main__":
    main()
