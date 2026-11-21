#!/usr/bin/env python3
"""Toy-model simulations for laboratory error-detection rules. Requires Python 3.10+ and numpy.

Everything here is a TOY MODEL with synthetic parameters. Results characterise the rule
definitions as written (published forms, and a transliteration of the rule forms read from one
open-source LIS), not any laboratory, analyser or deployed system.

Usage: python3 lab_qc_sim.py [seed]
"""
import math, sys, time
import numpy as np

SEED = int(sys.argv[1]) if len(sys.argv) > 1 else 20261121
rng = np.random.default_rng(SEED)
Phi = lambda x: 0.5 * (1 + math.erf(x / math.sqrt(2)))

def section(t):
    print(f"\n## {t}")

# ---------------------------------------------------------------- A. reference change values
section("A. Reference change value (derived; CV_A = 2%, CV_I = 5% are synthetic example inputs)")
cva, cvi = 0.02, 0.05
for z, lab in [(1.96, "two-sided 95%"), (2.58, "two-sided 99%"), (1.645, "one-sided 95%")]:
    rcv = math.sqrt(2) * z * math.sqrt(cva ** 2 + cvi ** 2)
    s = math.sqrt(math.log(1 + cva ** 2) + math.log(1 + cvi ** 2))
    up, down = math.exp(math.sqrt(2) * z * s) - 1, math.exp(-math.sqrt(2) * z * s) - 1
    print(f"Z={z} ({lab}): symmetric RCV = {100 * rcv:.2f}%; log-normal RCV = +{100 * up:.2f}% / {100 * down:.2f}%")

# ---------------------------------------------------------------- B. delta checks
section("B. Delta check toy model: same-patient pairs vs specimen mix-ups (n = 200000 pairs each)")
print("Set points ~ lognormal(CV_G); results = set point x (1 + N(0, sqrt(CV_I^2 + CV_A^2))). Mix-up: 2nd result from another patient.")
print("II = CV_I/CV_G; threshold = symmetric RCV at Z (percent change, |delta| > RCV flags).")
n = 200_000
cvi, cva = 0.05, 0.02
sd_w = math.sqrt(cvi ** 2 + cva ** 2)
print("II, CV_G, Z, RCV%, false-flag rate (true pairs), sensitivity (mix-ups), PPV@0.1% prev, PPV@1% prev, detect 10% shift, detect 20% shift")
for ii in (0.2, 0.5, 1.0):
    cvg = cvi / ii
    sg = math.sqrt(math.log(1 + cvg ** 2))
    sp1 = np.exp(rng.normal(0, sg, n)); sp2 = np.exp(rng.normal(0, sg, n))
    x1 = sp1 * (1 + rng.normal(0, sd_w, n))
    same = sp1 * (1 + rng.normal(0, sd_w, n))
    mix = sp2 * (1 + rng.normal(0, sd_w, n))
    sh10 = same * 1.10; sh20 = same * 1.20
    for z in (1.96, 2.58, 3.29):
        rcv = math.sqrt(2) * z * sd_w
        fp = np.mean(np.abs(same / x1 - 1) > rcv); se = np.mean(np.abs(mix / x1 - 1) > rcv)
        d10 = np.mean(np.abs(sh10 / x1 - 1) > rcv); d20 = np.mean(np.abs(sh20 / x1 - 1) > rcv)
        ppv = lambda p: (se * p) / (se * p + fp * (1 - p)) if (se * p + fp * (1 - p)) > 0 else float('nan')
        print(f"{ii}, {cvg:.2f}, {z}, {100 * rcv:.1f}, {fp:.4f}, {se:.4f}, {ppv(0.001):.3f}, {ppv(0.01):.3f}, {d10:.4f}, {d20:.4f}")

# ---------------------------------------------------------------- C. multirule QC
section("C. Statistical QC rules: 2 control levels per run, z ~ N(SE, 1) per observation (toy model)")
print("Analytic checks: P(1_2s reject | N=2, in control) = %.4f; P(1_3s reject | N=2) = %.4f"
      % (1 - (1 - 2 * (1 - Phi(2))) ** 2, 1 - (1 - 2 * (1 - Phi(3))) ** 2))
print("Analytic R4s, iid N(0,1) pair: Westgard within-run form P(one>+2 & other<-2) = %.5f;"
      " range form P(|z1-z2|>=4) = %.5f" % (2 * (1 - Phi(2)) ** 2, 2 * (1 - Phi(4 / math.sqrt(2)))))

def westgard_run(hist, z, gate):
    """Published multirule on one run of 2 levels; hist = list of earlier observations (oldest first, level-interleaved)."""
    a, b = z
    obs = hist + [a, b]
    warn = abs(a) > 2 or abs(b) > 2
    if gate and not warn:
        return False
    if abs(a) > 3 or abs(b) > 3: return True                                   # 1_3s
    if (a > 2 and b > 2) or (a < -2 and b < -2): return True                  # 2_2s within run (across levels)
    if (a > 2 and b < -2) or (a < -2 and b > 2): return True                  # R4s within run only
    if len(obs) >= 4 and (all(o > 1 for o in obs[-4:]) or all(o < -1 for o in obs[-4:])): return True   # 4_1s
    if len(obs) >= 10 and (all(o > 0 for o in obs[-10:]) or all(o < 0 for o in obs[-10:])): return True # 10x
    return False

def lis_variant_run(hl, z):
    """Transliteration of rule forms read from one open LIS: per control series (level), each new value is
    checked against that series' own history; thresholds use >=; R4s = |z_t - z_(t-1)| >= 4 on the same series;
    10x treats z == 0 as the negative side; no 1_2s gating."""
    rej = False
    for lv in (0, 1):
        h = hl[lv]; c = z[lv]
        if abs(c) >= 3: rej = True
        if h and abs(c) >= 2 and abs(h[-1]) >= 2 and ((c > 0 and h[-1] > 0) or (c < 0 and h[-1] < 0)): rej = True
        if h and abs(c - h[-1]) >= 4: rej = True
        if len(h) >= 3 and all(abs(x) >= 1 for x in h[-3:] + [c]) and (all(x > 0 for x in h[-3:] + [c]) or all(x < 0 for x in h[-3:] + [c])): rej = True
        if len(h) >= 9 and all((x > 0) == (c > 0) for x in h[-9:]): rej = True
    return rej

def run_length(proc, se, max_runs=200, burn=10):
    hist = list(rng.normal(0, 1, 2 * burn)); hl = [list(rng.normal(0, 1, burn)), list(rng.normal(0, 1, burn))]
    for t in range(1, max_runs + 1):
        z = rng.normal(se, 1, 2)
        r = proc(hist, hl, z)
        hist += list(z); hl[0].append(z[0]); hl[1].append(z[1])
        if r: return t
    return max_runs

procs = {
    "1_3s only": lambda h, hl, z: abs(z[0]) > 3 or abs(z[1]) > 3,
    "1_2s only": lambda h, hl, z: abs(z[0]) > 2 or abs(z[1]) > 2,
    "multirule, 1_2s-gated (classic)": lambda h, hl, z: westgard_run(h, z, True),
    "multirule, ungated (modern)": lambda h, hl, z: westgard_run(h, z, False),
    "LIS-variant rule forms": lambda h, hl, z: lis_variant_run(hl, z),
}
reps = 4000
print("procedure, P(reject first run) at SE=0 / 1 / 2 / 3 (n=%d runs each); mean run length to rejection at SE=0 (capped 200) / 1 / 2" % reps)
t0 = time.time()
for name, pr in procs.items():
    p_first = []
    for se in (0, 1, 2, 3):
        cnt = 0
        for _ in range(reps):
            hist = list(rng.normal(0, 1, 20)); hl = [list(rng.normal(0, 1, 10)), list(rng.normal(0, 1, 10))]
            z = rng.normal(se, 1, 2)
            cnt += pr(hist, hl, z)
        p_first.append(cnt / reps)
    arl = [np.mean([run_length(pr, se) for _ in range(600)]) for se in (0, 1, 2)]
    print(f"{name}: {p_first[0]:.4f} / {p_first[1]:.4f} / {p_first[2]:.4f} / {p_first[3]:.4f}; ARL {arl[0]:.1f} / {arl[1]:.2f} / {arl[2]:.2f}")
print(f"(section C elapsed {time.time() - t0:.1f} s)")

# ---------------------------------------------------------------- D. rolling statistics absorption
section("D. Rolling-window statistics absorb a persistent shift (toy model of a rolling calculator)")
print("One control series, true SD 1. 20 in-control runs establish stats. Persistent shift SE from run 1.")
print("FIXED: mean/SD frozen after establishment. ROLLING: mean/SD recomputed over the last 20 results (all")
print("results, including rejected ones) after each insert; each result's z uses the statistics in force before it.")
print("Rules: 1_3s, 2_2s, 4_1s, 10x in the LIS-variant forms (>=, per series). Report P(detected by run k), 3000 reps.")

def simulate(mode, se, horizon=40, win=20):
    est = list(rng.normal(0, 1, win))
    mean, sd = np.mean(est), np.std(est, ddof=1)
    zs = []; vals = est[:]
    for t in range(1, horizon + 1):
        v = rng.normal(se, 1)
        z = (v - mean) / sd if sd > 0 else 0.0
        zs.append(z); vals.append(v)
        h = zs[:-1]; c = z
        hit = abs(c) >= 3
        hit |= bool(h) and abs(c) >= 2 and abs(h[-1]) >= 2 and (c > 0) == (h[-1] > 0)
        hit |= len(h) >= 3 and all(abs(x) >= 1 for x in h[-3:] + [c]) and len({x > 0 for x in h[-3:] + [c]}) == 1
        hit |= len(h) >= 9 and all((x > 0) == (c > 0) for x in h[-9:])
        if hit: return t, zs
        if mode == "ROLLING":
            w = vals[-win:]; mean, sd = np.mean(w), np.std(w, ddof=1)
    return None, zs

for se in (0.0, 1.0, 1.5, 2.0):
    for mode in ("FIXED", "ROLLING"):
        det = []; zlate = []
        for _ in range(3000):
            t, zs = simulate(mode, se)
            det.append(t)
            if len(zs) >= 30: zlate.append(np.mean(zs[25:30]))
        det = np.array([d if d is not None else 10 ** 9 for d in det])
        zl = f"{np.mean(zlate):+.2f}" if zlate else "n/a (all detected before run 30)"
        print(f"SE={se} {mode:7s}: P(by run 5) {np.mean(det <= 5):.3f}, by 10 {np.mean(det <= 10):.3f}, by 40 {np.mean(det <= 40):.3f};"
              f" mean z over runs 26-30 when undetected: {zl}")

# ---------------------------------------------------------------- E. moving average PBRTQC
section("E. Moving-average patient-based QC toy model (bias detection curve)")
print("Synthetic patient stream: 90% N(140, 2.5), 10% N(133, 6) (a sodium-like mixture; synthetic).")
print("Truncation 130-150; simple moving average of block N over retained results; symmetric control limits")
print("calibrated on 400000 in-control results to ~1 false alarm per 10000 results. Bias added from result 1.")

def stream(k, bias=0.0):
    m = rng.random(k) < 0.9
    return np.where(m, rng.normal(140, 2.5, k), rng.normal(133, 6, k)) + bias

def ma_series(x, nblk, lo=130, hi=150):
    x = x[(x >= lo) & (x <= hi)]
    c = np.cumsum(np.insert(x, 0, 0.0))
    return (c[nblk:] - c[:-nblk]) / nblk, x.size

t0 = time.time()
for nblk in (20, 50, 100):
    ma0, _ = ma_series(stream(400_000), nblk)
    center = np.median(ma0)
    lim = np.quantile(np.abs(ma0 - center), 1 - 1e-4)
    out = []
    for bias in (0.5, 1.0, 2.0, 3.0):
        nres = []
        for _ in range(400):
            raw = stream(6000, bias)
            keep = (raw >= 130) & (raw <= 150)
            idx_keep = np.flatnonzero(keep)
            ma, _ = ma_series(raw, nblk)
            hits = np.flatnonzero(np.abs(ma - center) > lim)
            nres.append(idx_keep[hits[0] + nblk - 1] + 1 if hits.size else 6000)
        nres = np.array(nres)
        out.append(f"bias {bias}: median {int(np.median(nres))}, p95 {int(np.quantile(nres, 0.95))}")
    print(f"N={nblk}, limit +/-{lim:.2f} around {center:.2f}: " + "; ".join(out) + " (patient results to detection, censored at 6000)")
print(f"(section E elapsed {time.time() - t0:.1f} s)")
