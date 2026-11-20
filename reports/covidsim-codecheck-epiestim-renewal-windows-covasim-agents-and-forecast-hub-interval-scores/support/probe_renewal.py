#!/usr/bin/env python3
"""Renewal-equation (Cori et al. 2013) estimator probe.

Part A is a differential check: a pure-Python transcription of the EpiEstim
`parametric_si` code path (discr_si, overall_infectivity,
posterior_from_si_distr) is run on the incidence vector printed in EpiEstim's
own test snapshot (tests/testthat/_snaps/estimate_R.md, "Example 3") and its
posterior mean/sd are compared with the snapshot values.

Parts B-E are a TOY MODEL: deterministic expected-value renewal epidemics,
fed to the same transcription, to illustrate generation-interval
misspecification, window lag, reporting delay and right truncation.
They characterise the estimator formula, not any real outbreak or EpiEstim's
R runtime.  Standard library only (Python 3.10+).
"""
import math

# ---------- regularized lower incomplete gamma P(a, x) -----------------
def gammp(a, x):
    if x <= 0:
        return 0.0
    gln = math.lgamma(a)
    if x < a + 1.0:  # series
        ap, s = a, 1.0 / a
        d = s
        for _ in range(10000):
            ap += 1.0
            d *= x / ap
            s += d
            if abs(d) < abs(s) * 1e-16:
                break
        return s * math.exp(-x + a * math.log(x) - gln)
    # continued fraction (Lentz)
    b = x + 1.0 - a
    c = 1.0 / 1e-300
    d = 1.0 / b
    h = d
    for i in range(1, 10000):
        an = -i * (i - a)
        b += 2.0
        d = an * d + b
        if abs(d) < 1e-300: d = 1e-300
        c = b + an / c
        if abs(c) < 1e-300: c = 1e-300
        d = 1.0 / d
        de = d * c
        h *= de
        if abs(de - 1.0) < 1e-16:
            break
    return 1.0 - math.exp(-x + a * math.log(x) - gln) * h

def pgamma(k, shape, scale):
    return gammp(shape, k / scale) if k > 0 else 0.0

# ---------- EpiEstim transcription (R/discr_si.R, R/overall_infectivity.R,
# ---------- R/estimate_R.R posterior_from_si_distr) ---------------------
def discr_si(ks, mu, sigma):
    a = ((mu - 1) / sigma) ** 2
    b = sigma ** 2 / (mu - 1)
    out = []
    for k in ks:
        r = (k * pgamma(k, a, b) + (k - 2) * pgamma(k - 2, a, b)
             - 2 * (k - 1) * pgamma(k - 1, a, b))
        r += a * b * (2 * pgamma(k - 1, a + 1, b) - pgamma(k - 2, a + 1, b)
                      - pgamma(k, a + 1, b))
        out.append(max(0.0, r))
    return out

def overall_infectivity(I, w):
    # lambda[t] = sum_{s=1..t} w[s-1] * I[t-s+1]   (1-based, w[0] = P(SI=0) = 0)
    T = len(I)
    lam = [float('nan')]
    for t in range(2, T + 1):
        lam.append(sum(w[s - 1] * I[t - s] for s in range(1, t + 1) if s - 1 < len(w)))
    return lam

def cori(I_local, I_total, w, t_start, t_end, mean_prior=5.0, std_prior=5.0):
    a_prior = (mean_prior / std_prior) ** 2
    b_prior = std_prior ** 2 / mean_prior
    lam = overall_infectivity(I_total, w)
    mean_si = sum(i * p for i, p in enumerate(w))
    res = []
    for ts, te in zip(t_start, t_end):
        if te > mean_si:
            a = a_prior + sum(I_local[ts - 1:te])
            b = 1.0 / (1.0 / b_prior + sum(lam[ts - 1:te]))
            res.append((ts, te, a * b, math.sqrt(a) * b))
        else:
            res.append((ts, te, float('nan'), float('nan')))
    return res

# ---------- Part A: differential check against EpiEstim snapshot ------
I_tot = [1, 1, 0, 2, 5, 3, 3, 3, 6, 2, 5, 9, 13, 12, 13, 11, 12, 6, 6, 6, 3, 1, 0, 2, 0,
         0, 0, 0, 2, 0, 2, 0]
I_loc = [0] + I_tot[1:]          # first case is imported (snapshot $I_imported)
SNAP_MEAN = [1.7357977, 1.7491678, 1.5370581, 1.4318389, 1.4227247, 1.6353733, 1.6639845,
             1.6161467, 1.4344239, 1.4087217, 1.2479472, 1.0821477, 0.9371671, 0.8196564,
             0.6910352, 0.5896765, 0.4992206, 0.4729631, 0.4176319, 0.2978682, 0.2400880,
             0.4573477, 0.6734382, 0.8591897, 0.9975352]
SNAP_STD = [0.40913143, 0.36472669, 0.30741163, 0.27059213, 0.25150457, 0.25234358,
            0.23300443, 0.20692639, 0.17656537, 0.16159146, 0.14221678, 0.12579711,
            0.11449319, 0.10762616, 0.10188759, 0.09967353, 0.09984413, 0.10850519,
            0.11583024, 0.11258359, 0.12004401, 0.20453212, 0.30117074, 0.38424130,
            0.44611130]
T = len(I_tot)
w = discr_si(range(T), 2.6, 1.5) + [0.0]       # padded to T+1 as in estimate_R.R
m = sum(i * p for i, p in enumerate(w))
sd = math.sqrt(sum(i * i * p for i, p in enumerate(w)) - m * m)
print(f"A: discretised SI moments mean={m:.6f} sd={sd:.6f} (snapshot: 2.6, 1.55488); "
      f"w[1..3]={w[1]:.7f},{w[2]:.7f},{w[3]:.7f} (snapshot 2.331721e-01,3.585794e-01,1.981108e-01)")
res = cori(I_loc, I_tot, w, list(range(2, 27)), list(range(8, 33)))
dm = max(abs(r[2] - s) for r, s in zip(res, SNAP_MEAN))
ds = max(abs(r[3] - s) for r, s in zip(res, SNAP_STD))
print(f"A: 25 windows, max|mean-snapshot|={dm:.2e}, max|sd-snapshot|={ds:.2e} "
      f"(snapshot printed to 7-8 significant digits)")

# ---------- toy renewal epidemic -----------------------------------------
def gamma_gi(mean, sd, n=40):
    # discretised gamma GI via the same offset-gamma discretisation
    return discr_si(range(n), mean, sd)

def renewal(R_of_t, w, T, I0=10.0, seed_days=1):
    I = [I0] * seed_days
    for t in range(seed_days, T):
        lam = sum(w[s] * I[t - s] for s in range(1, min(t, len(w) - 1) + 1))
        I.append(R_of_t(t + 1) * lam)
    return I

def R_true(t):  # 1-based day index
    return 2.0 if t <= 40 else (0.8 if t <= 90 else 1.15)

TT = 120
w_true = gamma_gi(6.5, 4.0)
I = renewal(R_true, w_true, TT)
win = 7
ts = list(range(2, TT - win + 2)); te = [s + win - 1 for s in ts]

def est(Iobs, wassumed, ts=ts, te=te):
    return {r[1]: r[2] for r in cori(Iobs, Iobs, wassumed, ts, te)}

# ---------- Part B: generation-interval mean misspecification ------------
print("B: GI misspecification (true GI discretised gamma mean 6.5 sd 4.0; window 7; "
      "estimate reported at window end)")
for label, mu in [("assumed mean 4.5", 4.5), ("assumed mean 6.5 (true)", 6.5), ("assumed mean 8.5", 8.5)]:
    e = est(I, gamma_gi(mu, 4.0))
    print(f"   {label:24s} R_hat(t_end=35, true 2.0)={e[35]:.3f}  "
          f"R_hat(t_end=80, true 0.8)={e[80]:.3f}  R_hat(t_end=115, true 1.15)={e[115]:.3f}")

# ---------- Part C: window length -> lag of the end-of-window estimate ----
print("C: first t_end with R_hat < 1 after the true drop at day 41 (true GI, no delay)")
for win_c in (1, 7, 14, 21):
    tsc = list(range(2, TT - win_c + 2)); tec = [s + win_c - 1 for s in tsc]
    e = est(I, w_true, tsc, tec)
    first = min(t for t in tec if t > 40 and e[t] < 1.0)
    print(f"   window {win_c:2d}: first t_end with R_hat<1 = {first}  (lag {first - 41} d)")

# ---------- Part D: reporting delay without deconvolution ---------------
delay = gamma_gi(8.0, 4.0)  # infection -> report delay pmf (index = days)
rep = [sum(delay[d] * I[t - d] for d in range(0, min(t, len(delay) - 1) + 1)) for t in range(TT)]
e_rep = est(rep, w_true)
first_rep = min(t for t in te if t > 40 and e_rep[t] < 1.0)
print(f"D: counts by report date (delay mean 8 d), window 7: first t_end with R_hat<1 = "
      f"{first_rep} vs {min(t for t in te if t > 40 and est(I, w_true)[t] < 1.0)} by infection date")

# ---------- Part E: right truncation at analysis day -----------------------
cdf = [sum(delay[:k + 1]) for k in range(len(delay))]
for T_an in (60, 100):
    Itr = [I[t] * (cdf[min(T_an - 1 - t, len(cdf) - 1)]) for t in range(T_an)]
    tse = list(range(2, T_an - win + 2)); tee = [s + win - 1 for s in tse]
    e_full = est(I[:T_an], w_true, tse, tee)
    e_tr = est(Itr, w_true, tse, tee)
    print(f"E: analysis day {T_an}: last-window R_hat infection-date complete={e_full[T_an]:.3f} "
          f"vs right-truncated (only infections already reported)={e_tr[T_an]:.3f} "
          f"(true R={R_true(T_an)})")
