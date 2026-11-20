#!/usr/bin/env python3
"""Fundamental-diagram measurement-method probe.

1. Generates trajectories with JuPedSim's CollisionFreeSpeedModel (raw pyjupedsim bindings)
   in a 100 m x 2 m corridor: N agents start on 4 lanes at initial density rho0 from x = 1 m and
   walk to an exit stage at x in [99.5, 100]; the measurement area is x in [60, 62] (4 m^2)
   and the measurement line is x = 61.  Optional bottleneck: for x in [70, 72] the corridor
   narrows symmetrically to the given width, so that congestion backs up through the
   measurement area.  Trajectories are sampled at 10 frames/s (dt = 0.01 s).
2. Applies four measurement methods, re-implemented here in numpy following the formulas
   documented in PedPy (density_calculator.py, speed_calculator.py, flow_calculator.py):
     A  line method: flow J over windows of 50 frames at x = 61 m (first-to-last crossing in
        each window, as in PedPy compute_flow), time-mean crossing speed v_A, rho_A = J/(v_A*b)
     B  passing method: per pedestrian, v = d/(t_out - t_in) over x in [60, 62] and
        rho = mean classic density over that pedestrian's [t_in, t_out)  (PedPy
        compute_passing_speed / compute_passing_density)
     C  classic: per frame rho = N/A(M), v = mean individual speed of pedestrians in M
     D  Voronoi: per frame rho = sum_i |V_i ∩ M|/|V_i| / |M|, v = sum_i v_i |V_i ∩ M| / |M|;
        Voronoi cells approximated by nearest-site assignment on a 0.05 m lattice clipped to
        the corridor (no cut-off), i.e. a discretised tessellation, not PedPy's exact polygons.
   Individual speed: centred difference over +/- 5 frames (PedPy frame_step = 5, BORDER_EXCLUDE).
3. Fits v = v0 * (1 - rho / rho_max) by least squares to each method's (rho, v) points.

This is execution of JuPedSim plus a re-implementation of the measurement formulas; it is not
an execution of PedPy itself.
Usage: PYTHONPATH=<pyjupedsim dir> fd_methods_probe.py
"""
import json
import math

import numpy as np
import pyjupedsim as jps

W, LEN = 2.0, 100.0
M_X0, M_X1 = 60.0, 62.0
LINE_X = 61.0
FPS = 10
DT = 0.01
STEP = 5


BN_X0, BN_X1 = 70.0, 72.0


def run_corridor(n, rho0, seed=0, bottleneck=None):
    rng = np.random.default_rng(seed)
    gb = jps.GeometryBuilder()
    if bottleneck is None:
        boundary = [(0, 0), (LEN, 0), (LEN, W), (0, W)]
    else:
        lo, hi = W / 2 - bottleneck / 2, W / 2 + bottleneck / 2
        boundary = [(0, 0), (BN_X0, 0), (BN_X0, lo), (BN_X1, lo), (BN_X1, 0), (LEN, 0),
                    (LEN, W), (BN_X1, W), (BN_X1, hi), (BN_X0, hi), (BN_X0, W), (0, W)]
    region = gb.add_region(boundary=boundary, height=0.0)
    sim = jps._Simulation(model=jps.CollisionFreeSpeedModel(), geometry=gb.build(), dt=DT,
                          floorfield_options=jps.FloorfieldOptions())
    ex = sim.add_exit_stage([([(LEN - 0.5, 0), (LEN, 0), (LEN, W), (LEN - 0.5, W)], region)])
    j = sim.add_journey({ex: jps.Transition.create_none_transition()})
    # 4 lanes (y = 0.25, 0.75, 1.25, 1.75); longitudinal spacing sx gives initial density rho0
    lanes = [0.25, 0.75, 1.25, 1.75]
    sx = len(lanes) / (rho0 * W)
    pos = []
    x = 1.0
    while len(pos) < n:
        for y in lanes:
            if len(pos) < n:
                pos.append((x + rng.uniform(-0.02, 0.02), y + rng.uniform(-0.02, 0.02)))
        x += sx
    for p in pos:
        sim.add_agent(journey_id=j, stage_id=ex, position=p,
                      state=jps.CollisionFreeSpeedModelState(desired_speed=1.34, radius=0.2,
                                                             time_gap=1.0), region_id=region)
    traj = {}  # id -> list of (frame, x, y)
    frame = 0
    it = 0
    while sim.agent_count() > 0 and sim.elapsed_time() < 400:
        sim.iterate()
        it += 1
        if it % int(1 / (FPS * DT)) == 0:
            frame += 1
            for a in sim.agents():
                traj.setdefault(a.id, []).append((frame, a.position[0], a.position[1]))
    return traj


def speeds(traj):
    out = {}
    for pid, rows in traj.items():
        arr = np.array(rows)
        f = arr[:, 0].astype(int)
        for k in range(STEP, len(arr) - STEP):
            if f[k + STEP] - f[k - STEP] != 2 * STEP:
                continue
            d = arr[k + STEP, 1:] - arr[k - STEP, 1:]
            out[(pid, f[k])] = (np.linalg.norm(d) / (2 * STEP / FPS), arr[k, 1], arr[k, 2])
    return out


def methods(traj):
    sp = speeds(traj)
    frames = {}
    for (pid, f), (v, x, y) in sp.items():
        frames.setdefault(f, []).append((pid, x, y, v))
    A_M = (M_X1 - M_X0) * W
    C, D = [], []
    gx = np.arange(M_X0 - 4 + 0.025, M_X1 + 4, 0.05)
    gy = np.arange(0.025, W, 0.05)
    GX, GY = np.meshgrid(gx, gy)
    G = np.stack([GX.ravel(), GY.ravel()], 1)
    in_m = (G[:, 0] >= M_X0) & (G[:, 0] < M_X1)
    cell = 0.05 * 0.05
    for f, peds in sorted(frames.items()):
        inside = [p for p in peds if M_X0 <= p[1] < M_X1]
        if inside:
            C.append((len(inside) / A_M, float(np.mean([p[3] for p in inside]))))
        near = [p for p in peds if M_X0 - 4 <= p[1] < M_X1 + 4]
        if not near:
            continue
        P = np.array([[p[1], p[2]] for p in near])
        owner = np.argmin(((G[:, None, :] - P[None, :, :]) ** 2).sum(-1), axis=1)
        area = np.bincount(owner, minlength=len(near)) * cell
        inter = np.bincount(owner[in_m], minlength=len(near)) * cell
        # cells of pedestrians at the window edge are truncated by the window; only peds whose
        # cells intersect M matter and they lie well inside the +/- 4 m window at these densities
        mask = inter > 0
        if mask.any():
            rho = float((inter[mask] / area[mask]).sum() / A_M)
            v = float((np.array([p[3] for p in near])[mask] * inter[mask]).sum() / A_M)
            D.append((rho, v))
    # Method A: line crossings
    cross = []
    for pid, rows in traj.items():
        for (f0, x0, _), (f1, x1, _) in zip(rows, rows[1:]):
            if x0 < LINE_X <= x1:
                cross.append((f1, pid))
                break
    cross.sort()
    A = []
    if cross:
        cf = np.array([c[0] for c in cross])
        start = cf[0]
        prev_n, prev_f = 0, start
        for wend in range(start + 50, cf[-1] + 51, 50):
            n_cum = int((cf <= wend).sum())
            if n_cum > prev_n:
                last_f = int(cf[cf <= wend].max()) + 1
                J = (n_cum - prev_n) / ((last_f - prev_f) / FPS)
                vs = [sp[(pid, f)][0] for f, pid in cross[prev_n:n_cum] if (pid, f) in sp]
                if vs:
                    vA = float(np.mean(vs))
                    A.append((J / (vA * W), vA))
                prev_n, prev_f = n_cum, last_f
    # Method B: passing
    dens_by_frame = {f: len([p for p in peds if M_X0 <= p[1] < M_X1]) / A_M
                     for f, peds in frames.items()}
    B = []
    for pid, rows in traj.items():
        fin = next((f for f, x, _ in rows if x >= M_X0), None)
        fout = next((f for f, x, _ in rows if x >= M_X1), None)
        if fin is None or fout is None or fout <= fin:
            continue
        v = (M_X1 - M_X0) / ((fout - fin) / FPS)
        ds = [dens_by_frame.get(f, 0.0) for f in range(fin, fout)]
        B.append((float(np.mean(ds)), v))
    return {"A": A, "B": B, "C": C, "D": D}


def fit(points):
    if len(points) < 3:
        return None
    r = np.array([p[0] for p in points]); v = np.array([p[1] for p in points])
    b, a = np.polyfit(r, v, 1)
    return {"n": len(points), "v0": float(a), "rho_max": float(-a / b) if b < 0 else None,
            "rho_range": [float(r.min()), float(r.max())], "v_range": [float(v.min()), float(v.max())],
            "rho_mean": float(r.mean()), "v_mean": float(v.mean())}


CONFIGS = [(80, 1.0, None), (240, 2.0, 1.2), (240, 2.0, 0.9), (240, 2.0, 0.7), (240, 2.0, 0.5)]

if __name__ == "__main__":
    import sys
    if len(sys.argv) > 1 and sys.argv[1] == "one":
        # run a single configuration and dump raw (rho, v) points: fd_methods_probe.py one <idx> <out.json>
        n, rho0, bn = CONFIGS[int(sys.argv[2])]
        pts = methods(run_corridor(n, rho0, bottleneck=bn))
        json.dump({"N": n, "rho0": rho0, "bottleneck_width": bn, "points": pts}, open(sys.argv[3], "w"))
        sys.exit(0)
    if len(sys.argv) > 1 and sys.argv[1] == "pool":
        # pool previously dumped configurations: fd_methods_probe.py pool <in1.json> ...
        allpts = {"A": [], "B": [], "C": [], "D": []}
        for fn in sys.argv[2:]:
            d = json.load(open(fn))
            for k in allpts:
                allpts[k] += [tuple(p) for p in d["points"][k]]
            print(json.dumps({"N": d["N"], "rho0": d["rho0"], "bottleneck_width": d["bottleneck_width"],
                              **{k: fit(v) for k, v in d["points"].items()}}))
        CONFIGS = []
    else:
        allpts = {"A": [], "B": [], "C": [], "D": []}
    for n, rho0, bn in CONFIGS:
        traj = run_corridor(n, rho0, bottleneck=bn)
        pts = methods(traj)
        for k in allpts:
            allpts[k] += pts[k]
        print(json.dumps({"N": n, "rho0": rho0, "bottleneck_width": bn, **{k: fit(v) for k, v in pts.items()}}), flush=True)
    print(json.dumps({"POOLED": {k: fit(v) for k, v in allpts.items()}}), flush=True)
    # density-binned mean speed per method (0.25 /m^2 bins) for direct comparison
    bins = np.arange(0, 4.01, 0.25)
    for k, pts in allpts.items():
        r = np.array([p[0] for p in pts]); v = np.array([p[1] for p in pts])
        row = []
        for lo, hi in zip(bins, bins[1:]):
            m = (r >= lo) & (r < hi)
            row.append(f"{lo:.2f}-{hi:.2f}:{v[m].mean():.3f}(n={m.sum()})" if m.sum() >= 3 else f"{lo:.2f}-{hi:.2f}:-")
        print(k, " ".join(row))
