#!/usr/bin/env python3
"""Probe 2: toy serial EAKF on Lorenz-96 with/without Gaspari-Cohn localization and
prior inflation (fixed, or spatially varying adaptive per Anderson 2009).

Basis: execution (toy model of the DART update equations, NOT DART itself).
The observation increment, regression update, localization function, linear_bayes
inflation-mean update, damping, and deflation step are transcribed from DART
(assim_tools_mod.f90 obs_increment_eakf / update_from_obs_inc; cov_cutoff_mod.f90
comp_cov_factor; adaptive_inflate_mod.f90 linear_bayes / solve_quadratic /
update_varying_state_space_inflation; filter_mod.f90 inf_damping). Everything else
(model integration, observation network, bookkeeping) is a simplification.

Setup: 40 variables, F=8, RK4 dt=0.05 (DART lorenz_96 model_nml defaults), every
variable observed every step with error variance 1.0, 20 members, 3000 cycles,
statistics over cycles 500-2999. Location of variable i is i/40 on a unit circle.
Run: python3 l96_eakf_probe.py [--nens K] [stream ...]
"""
import sys
import time
import numpy as np

N, F, DT = 40, 8.0, 0.05
NENS, NCYC, SPIN = 20, 3000, 500  # NENS may be overridden with --nens
OBS_VAR = 1.0


def tend(x):
    return (np.roll(x, -1, -1) - np.roll(x, 2, -1)) * np.roll(x, 1, -1) - x + F


def rk4(x):
    k1 = DT * tend(x); k2 = DT * tend(x + k1 / 2); k3 = DT * tend(x + k2 / 2); k4 = DT * tend(x + k3)
    return x + k1 / 6 + k2 / 3 + k3 / 3 + k4 / 6


def gc(z, c):
    z = np.abs(z); r = z / c; out = np.zeros_like(z)
    m1 = z <= c; m2 = (z > c) & (z < 2 * c)
    r1 = r[m1]; r2 = r[m2]
    out[m1] = ((((-0.25 * r1 + 0.5) * r1 + 0.625) * r1 - 5.0 / 3.0) * r1 ** 2 + 1.0)
    out[m2] = ((((r2 / 12.0 - 0.5) * r2 + 0.625) * r2 + 5.0 / 3.0) * r2 - 5.0) * r2 + 4.0 - 2.0 / (3.0 * r2)
    return out


LOC = np.arange(N) / N
D = np.abs(LOC[:, None] - LOC[None, :]); D = np.where(D > 0.5, 1.0 - D, D)


def solve_quadratic(a, b, c):
    s = np.maximum(np.maximum(np.abs(a), np.abs(b)), np.abs(c))
    a_, b_, c_ = a / s, b / s, c / s
    disc = np.sqrt(b_ ** 2 - 4.0 * a_ * c_)
    r1 = np.where(b_ > 0, (-b_ - disc) / (2 * a_), (-b_ + disc) / (2 * a_))
    return r1, (c_ / a_) / r1


def linear_bayes(dist_2, sp2, so2, lam, lam_sd2, g):
    """Vectorized transcription of adaptive_inflate_mod.f90 linear_bayes."""
    tb2 = (1.0 + g * (np.sqrt(lam) - 1.0)) ** 2 * sp2 + so2
    tb = np.sqrt(tb2)
    u = 1.0 / (np.sqrt(2.0 * np.pi) * tb)
    v = np.exp(dist_2 / (-2.0 * tb2))
    like = u * v
    dth = 0.5 * sp2 * g * (1.0 - g + g * np.sqrt(lam)) / (tb * np.sqrt(lam))
    likep = (u * v * dth / tb) * (dist_2 / tb2 - 1.0)
    ok = (like > 0) & (likep != 0)
    likep_s = np.where(ok, likep, 1.0)
    b = like / likep_s - 2.0 * lam
    c = lam ** 2 - lam_sd2 - like * lam / likep_s
    p, m = solve_quadratic(np.ones_like(b), b, c)
    new = np.where(np.abs(m - lam) < np.abs(p - lam), m, p)
    return np.where(ok, new, lam)


def run(mode, stream, cutoff=0.2, fixed_inf=1.05, inf_sd=0.6, damping=0.9):
    rng = np.random.default_rng(stream)
    xt = 8.0 + rng.standard_normal(N)
    for _ in range(1000):
        xt = rk4(xt)
    ens = xt + rng.standard_normal((NENS, N)) * 2.0
    obs_rng = np.random.default_rng(stream + 1000)
    loc = gc(D, cutoff) if mode["loc"] else np.ones((N, N))
    lam = np.ones(N)
    rmse, sprd = [], []
    for k in range(NCYC):
        xt = rk4(xt); ens = rk4(ens)
        y = xt + obs_rng.standard_normal(N) * np.sqrt(OBS_VAR)
        # prior inflation
        if mode["inf"] == "fixed":
            lam_apply = np.full(N, fixed_inf)
        elif mode["inf"] == "adaptive":
            lam = 1.0 + damping * (lam - 1.0)
            lam_apply = lam.copy()
        else:
            lam_apply = np.ones(N)
        mean = ens.mean(0); s = np.sqrt(lam_apply)
        ens = ens * s + mean * (1.0 - s)
        orig_mean = ens.mean(0); orig_var = ens.var(0, ddof=1)
        lam_base = lam_apply.copy()
        for i in range(N):
            hx = ens[:, i].copy()
            pm = hx.mean(); pv = hx.var(ddof=1)
            vr = OBS_VAR / (pv + OBS_VAR)
            nm = vr * (pm + pv * y[i] / OBS_VAR)
            a = np.sqrt(vr)
            inc = a * (hx - pm) + nm - hx
            xm = ens.mean(0)
            cov = ((ens - xm) * (hx - pm)[:, None]).sum(0) / (NENS - 1)
            reg = cov / pv
            if mode["inf"] == "adaptive":
                sv = ens.var(0, ddof=1)
                corr = np.clip(cov / np.sqrt(pv * np.maximum(sv, 1e-300)), -1, 1)
                g = loc[i] * np.abs(corr)
                gm = g > 1e-12
                defl = np.where(gm, orig_var[i] / (1.0 + g * (np.sqrt(lam_base) - 1.0)) ** 2, orig_var[i])
                newlam = linear_bayes((y[i] - orig_mean[i]) ** 2, defl, OBS_VAR, lam, inf_sd ** 2, np.maximum(g, 1e-12))
                newlam = np.maximum(newlam, 1.0)  # inf_lower_bound = 1.0
                lam = np.where(gm, newlam, lam)
            ens = ens + (loc[i] * reg)[None, :] * inc[:, None]
        if k >= SPIN:
            rmse.append(np.sqrt(np.mean((ens.mean(0) - xt) ** 2)))
            sprd.append(np.sqrt(np.mean(ens.var(0, ddof=1))))
    return float(np.mean(rmse)), float(np.mean(sprd)), float(np.mean(lam))


MODES = [
    ("A no-loc, no-inf", {"loc": False, "inf": None}),
    ("B GC c=0.2, no-inf", {"loc": True, "inf": None}),
    ("C GC c=0.2, fixed 1.05", {"loc": True, "inf": "fixed"}),
    ("D GC c=0.2, adaptive", {"loc": True, "inf": "adaptive"}),
    ("E no-loc, fixed 1.05", {"loc": False, "inf": "fixed"}),
]


def main():
    global NENS
    args = sys.argv[1:]
    if args[:1] == ["--nens"]:
        NENS = int(args[1]); args = args[2:]
    streams = [int(s) for s in args] or [1, 2, 3]
    print(f"L96 N={N} F={F} dt={DT} ens={NENS} cycles={NCYC} spin={SPIN} obs_var={OBS_VAR}")
    for name, mode in MODES:
        for stream in streams:
            t0 = time.time()
            r, s, l = run(mode, stream)
            print(f"{name:26s} stream={stream}  rmse={r:7.3f}  spread={s:7.3f}  mean_inflation={l:6.3f}  ({time.time()-t0:.1f}s)")


if __name__ == "__main__":
    main()
