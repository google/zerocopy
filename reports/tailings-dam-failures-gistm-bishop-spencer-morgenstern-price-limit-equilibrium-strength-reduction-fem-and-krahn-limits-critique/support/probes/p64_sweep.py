#!/usr/bin/env python3
"""Sweep the iteration ceiling, convergence tolerance and mesh density of the
Smith-Griffiths program 6.4 (viscoplastic strength reduction) on its published
example slope, recording the first trial SRF that fails to converge.

Usage: python3 p64_sweep.py /path/to/run_p64 /path/to/workdir
"""
import os, subprocess, sys, time, resource

RUN = sys.argv[1]
WD = sys.argv[2]
os.makedirs(WD, exist_ok=True)

GEOM = "20.0  20.0  20.0  10.0  5.0"         # w1 s1 w2 h1 h2 (m)
PROPS = "20.0  15.0  0.0  20.0  1.0e5  0.3"  # phi(deg) c(kPa) psi(deg) gamma(kN/m3) E(kPa) nu
SRFS = [1.0] + [round(1.50 + 0.01 * k, 2) for k in range(0, 16)]


def run(mesh, tol, limit, tag):
    dat = os.path.join(WD, f"{tag}.dat")
    res = os.path.join(WD, f"{tag}.res")
    with open(dat, "w") as f:
        f.write(GEOM + "\n")
        f.write(" ".join(str(m) for m in mesh) + "\n")
        f.write("1\n")
        f.write(PROPS + "\n")
        f.write(f"{tol} {limit}\n")
        f.write(f"{len(SRFS)}\n")
        f.write(" ".join(f"{s:.2f}" for s in SRFS) + "\n")
    t0 = time.perf_counter()
    r0 = resource.getrusage(resource.RUSAGE_CHILDREN)
    subprocess.run([RUN, dat, res], cwd=WD, stdout=subprocess.DEVNULL, check=True)
    r1 = resource.getrusage(resource.RUSAGE_CHILDREN)
    dt = time.perf_counter() - t0
    rows = []
    for line in open(res):
        p = line.split()
        if len(p) == 3:
            try:
                rows.append((float(p[0]), float(p[1]), int(p[2])))
            except ValueError:
                pass
    last_conv = max((s for s, d, it in rows if it < limit), default=None)
    first_fail = next((s for s, d, it in rows if it >= limit), None)
    return rows, last_conv, first_fail, dt, r1.ru_maxrss


print("mesh(nx1,nx2,ny1,ny2) tol limit last_converged_SRF first_nonconverged_SRF wall_s maxrss_kB iters_per_trial")
for mesh in [(20, 10, 10, 5), (40, 20, 20, 10)]:
    for tol in [1e-4, 1e-3]:
        for limit in [250, 500, 1000, 2000, 5000]:
            tag = f"m{mesh[0]}_t{tol:g}_l{limit}"
            rows, lc, ff, dt, rss = run(mesh, tol, limit, tag)
            its = ",".join(f"{s:.2f}:{it}" for s, d, it in rows)
            print(f"{mesh} {tol:g} {limit} {lc} {ff} {dt:.2f} {rss} {its}")
            sys.stdout.flush()
