#!/usr/bin/env python3
"""Single-line leak and operational-transient probe driven by TSNet's own MOC kernels.

What this is:
  A harness that time-steps a straight liquid line
      sump + pump (source_pump) -> pipe 1 -> junction J (add_leakage) -> pipe 2 -> delivery orifice (dead_end)
  using functions loaded verbatim from TSNet at a pinned revision:
      tsnet/simulation/solver.py   : inner_node_steady, source_pump, add_leakage, dead_end
      tsnet/network/control.py     : burstsetting (linear leak opening)
      tsnet/postprocessing/detect_cusum.py : detect_cusum (TSNet's modified CUSUM)
  Network bookkeeping, steady-state initialisation (TSNet normally uses WNTR), sensor
  noise, SCADA sampling, the volume-balance detector, the classical CUSUM used for
  comparison and all scenario definitions are written here and are NOT TSNet.

What this is not:
  Not a model of any real pipeline, not a CPM product and not crude-oil physics
  (TSNet carries pressure as metres of fluid, hard-codes water viscosity for its
  non-steady friction models, and has no vapour-cavity / column-separation model).
  Every number this prints is a property of this toy configuration only.

Usage:
  git clone https://github.com/glorialulu/TSNet /tmp/TSNet
  git -C /tmp/TSNet checkout 27e616a8e2048a431eed27b00a08322d49035a52
  python3 tsnet_leak_probe.py --tsnet-root /tmp/TSNet > out.json
Requires: Python 3.10+ and numpy. matplotlib is not required (a stub is injected
because detect_cusum.py imports matplotlib.dates at module level).
"""
import argparse, importlib.util, json, math, resource, sys, time, types, warnings

import numpy as np

G = 9.81


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


class Node:
    def __init__(self, demand_coeff=0.0):
        self.demand_coeff, self.emitter_coeff = demand_coeff, 0.0


class Pipe:  # only the attributes solver.py reads
    def __init__(self, D, a, f, end_node=None, KD=1e-4):
        self.diameter, self.wavev, self.roughness = D, a, f
        self.theta, self.roughness_height = 0.0, KD
        self.start_node, self.end_node = Node(), end_node or Node()


def line_params():
    # Toy line: 40 km, D = 0.762 m, a = 1000 m/s, Darcy f = 0.015, flat, dx = 500 m (dt = 0.5 s).
    P = dict(D=0.762, a=1000.0, f=0.015, dx=500.0, L=40000.0, T=1800.0, scan=2.0, t_event=300.0,
             H_sump=10.0, pump_c=200.0, pump_a=-147.4, elev_J=0.0, elev_deliv=100.0, k_deliv=0.0594)
    return P


def steady_Q(P, k_deliv):
    """Solve sump + pump = delivery head + orifice loss + friction for Q (written here)."""
    A = math.pi * P['D'] ** 2 / 4
    r = P['f'] * P['L'] / (P['D'] * 2 * G * A * A)
    return math.sqrt((P['H_sump'] + P['pump_c'] - P['elev_deliv']) / (-P['pump_a'] + 1 / k_deliv ** 2 + r))


def simulate(S, P, K):
    sol = K['solver']
    D, a, f, dx = P['D'], P['a'], P['f'], P['dx']
    dt = dx / a
    A = math.pi * D * D / 4
    xL = S.get('x_leak', 20000.0)
    n1, n2 = int(round(xL / dx)), int(round((P['L'] - xL) / dx))
    deliv = Node(P['k_deliv'])
    p1, p2 = Pipe(D, a, f), Pipe(D, a, f, end_node=deliv)
    Q0 = steady_Q(P, P['k_deliv']); V0 = Q0 / A
    hf = lambda x: f * x / D * V0 ** 2 / (2 * G)
    H_dn0 = P['elev_deliv'] + (Q0 / P['k_deliv']) ** 2
    H_up0 = H_dn0 + hf(P['L'])
    H1 = H_up0 - hf(np.arange(n1 + 1) * dx)
    H2 = H1[-1] - hf(np.arange(n2 + 1) * dx)
    V1, V2 = np.full(n1 + 1, V0), np.full(n2 + 1, V0)
    tn = int(P['T'] / dt)
    kleak = K['control'].burstsetting(dt, P['T'], S.get('t_leak', 1e9), S.get('tc', 0.0), S.get('k_leak', 0.0))
    every = int(round(P['scan'] / dt))
    out = {k: [] for k in ('t', 'H_up', 'H_dn', 'Q_in', 'Q_out', 'Q_leak')}
    for ts in range(tn):
        t = ts * dt
        ramp = lambda t0, tc: min(1.0, max(0.0, (t - t0) / tc))
        pc = P['pump_c'] * (1 - S.get('pump_drop', 0.0) * ramp(P['t_event'], 10.0)) if 'pump_drop' in S else P['pump_c']
        deliv.demand_coeff = P['k_deliv'] * (1 - S.get('valve_close', 0.0) * ramp(P['t_event'], 10.0)) if 'valve_close' in S else P['k_deliv']
        N1H, N1V, N2H, N2V = (np.empty_like(z) for z in (H1, V1, H2, V2))
        N1H[1:-1], N1V[1:-1] = sol.inner_node_steady(p1, H1, V1, dt, G)
        N2H[1:-1], N2V[1:-1] = sol.inner_node_steady(p2, H2, V2, dt, G)
        N1H[0], N1V[0] = sol.source_pump([P['H_sump'], (P['pump_a'], 0.0, pc)], p1, H1[1], V1[1], dt, G, [-1], 'steady', 0, 0)
        N2H[n2], N2V[n2] = sol.dead_end(p2, H2[n2 - 1], V2[n2 - 1], P['elev_deliv'], n2, a, G, f, D, dt, p2.roughness_height, 'steady', 0, 0)
        k = float(kleak[ts]) if ts < len(kleak) else 0.0
        hj, ve = sol.add_leakage(k, 0, p1, p2, P['elev_J'], H1[n1 - 1], V1[n1 - 1], H2[1], V2[1], dt, G, n1, [1], [-1], 'steady')
        _, vs = sol.add_leakage(k, 0, p1, p2, P['elev_J'], H1[n1 - 1], V1[n1 - 1], H2[1], V2[1], dt, G, 0, [1], [-1], 'steady')
        N1H[n1], N1V[n1], N2H[0], N2V[0] = hj, float(np.squeeze(ve)), hj, float(np.squeeze(vs))
        H1, V1, H2, V2 = N1H, N1V, N2H, N2V
        if ts % every == 0:
            out['t'].append(t); out['H_up'].append(H1[0]); out['H_dn'].append(H2[n2])
            out['Q_in'].append(V1[0] * A); out['Q_out'].append(V2[n2] * A); out['Q_leak'].append((V1[n1] - V2[0]) * A)
    return {k_: np.asarray(v) for k_, v in out.items()}, dict(dt=dt, Q0=Q0, H_up0=H_up0, H_dn0=H_dn0, HJ0=float(H1[-1]) if False else None)


def classical_cusum(x, threshold, drift):
    """Page/Gustafsson two-sided CUSUM (the commented-out block in detect_cusum.py), written here. Returns alarm indices."""
    gp = gn = 0.0; alarms = []
    for i in range(1, len(x)):
        s = x[i] - x[i - 1]
        gp = max(0.0, gp + s - drift); gn = max(0.0, gn - s - drift)
        if gp > threshold or gn > threshold:
            alarms.append(i); gp = gn = 0.0
    return alarms


def tsnet_alarm_indices(det, t, x, threshold, drift):
    """detect_cusum(ending=False) returns change-START indices only. Because its forward pass is causal,
    the alarm index of the k-th alarm is the smallest prefix length m whose result has >= k entries; found by bisection."""
    full = len(det(t, x, threshold, drift, False, ending=False)[0])
    alarms, lo_start = [], 2
    for k in range(1, full + 1):
        lo, hi = lo_start, len(x)
        while lo < hi:
            mid = (lo + hi) // 2
            if len(det(t[:mid], x[:mid], threshold, drift, False, ending=False)[0]) >= k:
                hi = mid
            else:
                lo = mid + 1
        alarms.append(lo - 1); lo_start = lo
    return alarms


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--tsnet-root', required=True)
    ap.add_argument('--seeds', type=int, default=20)
    args = ap.parse_args()
    sys.modules.setdefault('matplotlib', types.ModuleType('matplotlib'))
    sys.modules.setdefault('matplotlib.dates', types.ModuleType('matplotlib.dates'))
    K = {'solver': load('ts_solver', f'{args.tsnet_root}/tsnet/simulation/solver.py'),
         'control': load('ts_control', f'{args.tsnet_root}/tsnet/network/control.py'),
         'cusum': load('ts_cusum', f'{args.tsnet_root}/tsnet/postprocessing/detect_cusum.py')}
    det = K['cusum'].detect_cusum
    warnings.simplefilter('ignore')
    P = line_params()
    sig_H, sig_Q, bias_Q = 0.2, 0.0025, 0.001   # toy: 0.2 m head noise; flow noise 0.25 % and per-meter bias sd 0.1 % of Q0
    base, meta = simulate({}, P, K)
    Q0 = meta['Q0']
    A = math.pi * P['D'] ** 2 / 4
    HJ0 = meta['H_up0'] - P['f'] * 20000.0 / P['D'] * (Q0 / A) ** 2 / (2 * G)
    kfor = lambda r, HJ=HJ0: r * Q0 / math.sqrt(HJ - P['elev_J'])
    HJ10 = meta['H_up0'] - P['f'] * 10000.0 / P['D'] * (Q0 / A) ** 2 / (2 * G)
    te = P['t_event']
    scen = {
        'S0_no_event': {},
        'S1_leak_5pct_at20km_abrupt': dict(x_leak=20000.0, t_leak=te, tc=0.0, k_leak=kfor(0.05)),
        'S2_leak_1pct_at20km_abrupt': dict(x_leak=20000.0, t_leak=te, tc=0.0, k_leak=kfor(0.01)),
        'S3_leak_0p5pct_at20km_ramp60s': dict(x_leak=20000.0, t_leak=te, tc=60.0, k_leak=kfor(0.005)),
        'S4_rupture_25pct_at10km_abrupt': dict(x_leak=10000.0, t_leak=te, tc=0.0, k_leak=kfor(0.25, HJ10)),
        'S7_rupture_60pct_at10km_abrupt': dict(x_leak=10000.0, t_leak=te, tc=0.0, k_leak=kfor(0.60, HJ10)),
        'S5_pump_head_drop_10pct_10s': dict(pump_drop=0.10),
        'S6_delivery_valve_close_20pct_10s': dict(valve_close=0.20),
    }
    t0w = time.perf_counter()
    sims = {nm: simulate(s, P, K)[0] for nm, s in scen.items()}
    wall = time.perf_counter() - t0w
    t = sims['S0_no_event']['t']
    L, a = P['L'], P['a']
    thr_list = [0.6, 0.8, 1.0, 1.5]; drift = 0.05
    res = {'meta': {'Q0_m3s': Q0, 'H_up0_m': meta['H_up0'], 'H_dn0_m': meta['H_dn0'], 'dt_s': meta['dt'],
                    'sig_H_m': sig_H, 'sig_Q_rel': sig_Q, 'bias_Q_rel_sd': bias_Q, 'seeds': args.seeds,
                    'P': P, 'sim_wall_s_all_scenarios': round(wall, 2)}}
    # (1) false-alarm calibration on pure noise (S0): TSNet modified CUSUM vs classical CUSUM
    fa = {}
    for thr in thr_list:
        n_ts = n_cl = 0
        for seed in range(args.seeds):
            rng = np.random.default_rng(1000 + seed)
            for key in ('H_up', 'H_dn'):
                x = sims['S0_no_event'][key] + rng.normal(0, sig_H, len(t))
                n_ts += len(det(t, x, thr, drift, False, ending=False)[0])
                n_cl += len(classical_cusum(x, thr, drift))
        hours = args.seeds * 2 * P['T'] / 3600
        fa[str(thr)] = {'tsnet_alarms_per_sensor_hour': n_ts / hours, 'classical_alarms_per_sensor_hour': n_cl / hours}
    res['cusum_false_alarm_rate_S0_drift0.05'] = fa
    thr = 1.0
    res['meta']['cusum_threshold_used_m'] = thr
    # (2) per-scenario metrics
    for nm, o in sims.items():
        r = {}
        pre = t < te
        r['true_final_Q_leak_m3s'] = float(o['Q_leak'][-1])
        r['true_final_Qin_minus_Qout_m3s'] = float(o['Q_in'][-1] - o['Q_out'][-1])
        for key in ('H_up', 'H_dn'):
            h0 = float(o[key][pre][-1])
            w15 = (t >= te) & (t <= te + 900)
            r[f'true_{key}_min_change_within_15min_m'] = float(np.min(o[key][w15]) - h0)
            r[f'true_{key}_min_change_within_15min_pct'] = 100 * (float(np.min(o[key][w15])) - h0) / h0  # pipe elevation is 0, so H is pressure head
            r[f'true_{key}_max_change_within_15min_m'] = float(np.max(o[key][w15]) - h0)
        def arrival(h):
            ref = h[pre][-1]; idx = np.where((t >= te) & (np.abs(h - ref) > 0.05))[0]
            return float(t[idx[0]]) if len(idx) else None
        tu, td = arrival(o['H_up']), arrival(o['H_dn'])
        r['noise_free_arrival_up_s'], r['noise_free_arrival_dn_s'] = tu, td
        if tu is not None and td is not None:
            r['noise_free_npw_location_est_m'] = (L + a * (tu - td)) / 2
        m = (t >= te) & (t <= te + 300)
        r['true_max_abs_Qin_minus_Qout_0_300s_m3s'] = float(np.max(np.abs(o['Q_in'][m] - o['Q_out'][m])))
        both, loc, delays_bal = [], [], {60: [], 300: [], 1200: []}
        fa_bal = {60: 0, 300: 0, 1200: 0}
        for seed in range(args.seeds):
            rng = np.random.default_rng(seed)
            hu = o['H_up'] + rng.normal(0, sig_H, len(t)); hd = o['H_dn'] + rng.normal(0, sig_H, len(t))
            au = [i for i in tsnet_alarm_indices(det, t, hu, thr, drift) if t[i] >= te]
            ad = [i for i in tsnet_alarm_indices(det, t, hd, thr, drift) if t[i] >= te]
            tai_u = [i for i in det(t, hu, thr, drift, False, ending=False)[0] if t[i] >= te - 10]
            tai_d = [i for i in det(t, hd, thr, drift, False, ending=False)[0] if t[i] >= te - 10]
            # "both ends dropped" rule: first post-event alarm at each end whose change is a decrease
            du = [i for i in au if hu[i] < hu[max(0, i - 10)]]; dd = [i for i in ad if hd[i] < hd[max(0, i - 10)]]
            both.append(max(t[du[0]], t[dd[0]]) - te if (du and dd) else None)
            if tai_u and tai_d:
                loc.append((L + a * (t[tai_u[0]] - t[tai_d[0]])) / 2)
            bi, bo = rng.normal(0, bias_Q * Q0), rng.normal(0, bias_Q * Q0)
            qi = o['Q_in'] + bi + rng.normal(0, sig_Q * Q0, len(t)); qo = o['Q_out'] + bo + rng.normal(0, sig_Q * Q0, len(t))
            imb = qi - qo
            for w in (60, 300, 1200):
                nw = int(w / P['scan'])
                # threshold: 4 x the steady-state sd of the windowed mean (white noise + both biases), derived analytically
                sd = math.sqrt(2 * (sig_Q * Q0) ** 2 / nw + 2 * (bias_Q * Q0) ** 2)
                cs = np.convolve(imb, np.ones(nw) / nw, mode='valid'); tw = t[nw - 1:]
                hit = np.where((tw >= te) & (cs > 4 * sd))[0]
                delays_bal[w].append(float(tw[hit[0]] - te) if len(hit) else None)
                fa_bal[w] += int(np.any((tw < te) & (cs > 4 * sd)))
        d = [x for x in both if x is not None]
        r['pressure_both_ends_drop_detect_fraction'] = len(d) / args.seeds
        r['pressure_both_ends_drop_median_delay_s'] = float(np.median(d)) if d else None
        r['npw_location_from_cusum_starts_median_m'] = float(np.median(loc)) if loc else None
        r['npw_location_from_cusum_starts_iqr_m'] = [float(np.percentile(loc, 25)), float(np.percentile(loc, 75))] if loc else None
        for w in (60, 300, 1200):
            dd_ = [x for x in delays_bal[w] if x is not None]
            r[f'balance_{w}s_detect_fraction'] = len(dd_) / args.seeds
            r[f'balance_{w}s_median_delay_s'] = float(np.median(dd_)) if dd_ else None
            r[f'balance_{w}s_runs_with_pre_event_alarm'] = fa_bal[w]
        res[nm] = r
    res['meta']['peak_rss_kib'] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    print(json.dumps(res, indent=1, default=float))


if __name__ == '__main__':
    main()
