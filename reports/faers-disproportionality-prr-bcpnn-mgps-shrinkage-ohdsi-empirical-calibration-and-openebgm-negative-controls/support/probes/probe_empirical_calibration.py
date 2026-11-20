#!/usr/bin/env python3
"""Toy re-implementation of EmpiricalCalibration 3.1.4 (OHDSI/EmpiricalCalibration@03d4747f...)
run on the datasets shipped in that package's data/ directory.

Basis: execution (toy re-implementation of EmpiricalCalibration, not EmpiricalCalibration itself).

Mirrors, at the pinned revision:
  fitNull()                    R/EmpiricalCalibrationUsingAsymptotics.R:48-86 + src/RcppWrapper.cpp:152-171
                               (parameters (mean, precision), start c(0, 1), Nelder-Mead, |logRr| > log(100) dropped)
  calibrateP()                 R/EmpiricalCalibrationUsingAsymptotics.R:139-163
  fitSystematicErrorModel()    R/ConfidenceIntervalCalibration.R:47-111 and R/Likelihoods.R:53-83
                               (default: sd = c + d*|trueLogRr|; legacy: sd = exp(c + d*trueLogRr))
  calibrateConfidenceInterval  R/ConfidenceIntervalCalibration.R:138-310
  computeExpectedAbsoluteSystematicError  R/ExpectedSystematicError.R:19-65

Usage: python3 probe_empirical_calibration.py DATA_DIR
DATA_DIR must contain sccs.rda caseControl.rda cohortMethod.rda southworthReplication.rda grahamReplication.rda
from https://raw.githubusercontent.com/OHDSI/EmpiricalCalibration/03d4747fd805e92744d0bcaf603f4c2d0b13370b/data/
"""
import math
import os
import sys

import numpy as np

from rda_reader import as_columns, read_rda
from smath import minimize_restarts, nelder_mead, pnorm, qnorm


def gaussian_product(mu1, mu2, sd1, sd2):
    v = sd1 ** 2 + sd2 ** 2
    return (2 * math.pi) ** -0.5 * v ** -0.5 * np.exp(-(mu1 - mu2) ** 2 / (2 * v))


def ll_null(theta, y, se):
    mu, prec = theta
    if prec <= 0:
        return math.inf
    sd = 1 / math.sqrt(prec)
    if sd < 1e-6:
        return float(-np.sum(-0.5 * np.log(2 * math.pi * se ** 2) - (mu - y) ** 2 / (2 * se ** 2)))
    return float(-np.sum(np.log(gaussian_product(y, mu, se, sd))))


def fit_null(y, se):
    y, se = np.asarray(y, float), np.asarray(se, float)
    keep = np.isfinite(y) & np.isfinite(se) & (np.abs(y) <= math.log(100))
    y, se = y[keep], se[keep]
    best = None
    x = np.array([0.0, 1.0])
    for step in (0.5, 0.1, 0.02):
        x, v, _ = nelder_mead(lambda t: ll_null(t, y, se), x, step=step)
        best = (x, v)
    mu, prec = best[0]
    return mu, 1 / math.sqrt(prec)


def calibrate_p(null, y, se):
    mu, sd = null
    d = math.sqrt(sd ** 2 + se ** 2)
    up = float(pnorm((mu - y) / d))
    lo = float(pnorm((y - mu) / d))
    return 2 * min(up, lo)


def traditional_p(y, se):
    z = y / se
    return 2 * min(float(pnorm(z)), 1 - float(pnorm(z)))


def ease(mu, sd):
    # closed form of E|X|, X ~ N(mu, sd^2), as in closedFormIntegeralAbsolute()
    if mu == 0 and sd == 0:
        return 0.0
    phi0 = math.exp(-mu ** 2 / (2 * sd ** 2)) / (sd * math.sqrt(2 * math.pi))
    Phi0 = float(pnorm((0 - mu) / sd))
    return mu * (1 - 2 * Phi0) + 2 * sd ** 2 * phi0


def ease_numeric(mu, sd, n=200001):
    x = np.linspace(mu - 12 * sd, mu + 12 * sd, n)
    f = np.abs(x) * np.exp(-(x - mu) ** 2 / (2 * sd ** 2)) / (sd * math.sqrt(2 * math.pi))
    return float(np.sum((f[1:] + f[:-1]) * np.diff(x)) / 2)


def err_model_nll(theta, y, se, t, legacy):
    a, b, c, d = theta
    mean = a + b * t
    sd = np.exp(c + d * t) if legacy else c + d * np.abs(t)
    if not legacy and np.any(sd < 0):
        return 99999.0
    sd = np.where(sd < 1e-6, 0.0, sd)
    v = se ** 2 + sd ** 2
    r = -np.sum(-0.5 * np.log(2 * math.pi * v) - (y - mean) ** 2 / (2 * v))
    return float(r) if np.isfinite(r) else 99999.0


def fit_error_model(y, se, t, legacy=False):
    x0 = np.array([0, 1, -2, 0.0]) if legacy else np.array([0, 1, 0.1, 0.0])
    x, v = minimize_restarts(lambda th: err_model_nll(th, y, se, t, legacy), x0, step=0.2)
    return x


def calibrate_ci(model, y, se, width=0.95, legacy=False):
    a, b, c, d = model

    def opt(x, z):
        mean = a + b * x
        sd = math.exp(c + d * x) if legacy else c + d * abs(x)
        return z + (mean - y) / math.sqrt(sd ** 2 + se ** 2)

    def root(z):
        lo, hi = -100.0, 100.0
        flo = opt(lo, z)
        for _ in range(200):
            mid = 0.5 * (lo + hi)
            fm = opt(mid, z)
            if (fm < 0) == (flo < 0):
                lo, flo = mid, fm
            else:
                hi = mid
        return 0.5 * (lo + hi)

    zq = qnorm((1 - width) / 2)
    return root(0.0), root(-zq), root(zq)


def load(dirpath, name):
    return as_columns(read_rda(os.path.join(dirpath, name + ".rda"))[name])


def main(d):
    print("== Null fits on the Schuemie et al. 2014 datasets shipped with the package")
    for name, paper in (("sccs", (0.79, 0.28)), ("caseControl", (0.90, 0.35)), ("cohortMethod", (-0.05, 0.54))):
        c = load(d, name)
        gt = np.array([float(g) for g in c["groundTruth"]])
        y, se = np.array(c["logRr"], float), np.array(c["seLogRr"], float)
        neg = gt == 0
        null = fit_null(y[neg], se[neg])
        pos = np.where(gt == 1)[0][0]
        trad = [traditional_p(a, b) < 0.05 for a, b in zip(y[neg], se[neg])]
        # leave-one-out calibrated p for each negative control (as in plotCalibration)
        loo = []
        idx = np.where(neg)[0]
        for i in idx:
            others = [j for j in idx if j != i]
            loo.append(calibrate_p(fit_null(y[others], se[others]), y[i], se[i]) < 0.05)
        print(f"{name}: negatives={neg.sum()} toy null mean={null[0]:.4f} sd={null[1]:.4f}"
              f"  (paper Table 1: {paper[0]}, {paper[1]})")
        print(f"   drug of interest {c['drugName'][pos]}: RR={math.exp(y[pos]):.2f} traditional p={traditional_p(y[pos], se[pos]):.2e}"
              f" calibrated p={calibrate_p(null, y[pos], se[pos]):.4f}")
        print(f"   negatives with traditional p<0.05: {sum(trad)}/{len(trad)};"
              f" leave-one-out calibrated p<0.05: {sum(loo)}/{len(loo)}")
        e = ease(*null)
        print(f"   EASE closed form={e:.4f} numeric={ease_numeric(*null):.4f} null mean={null[0]:.4f}"
              f" |EASE-mean|/|mean|={abs(e - null[0]) / abs(null[0]):.2e}")
    print("   vignette (EmpiricalPCalibrationVignette.pdf, sccs): Mean 0.7922 SD 0.2834; calibrateP 0.8389142")

    print("\n== Schuemie 2014 derived check from rounded published numbers (Results 3, Table 1, section 3.2)")
    cases = (("isoniazid cohort", 4.0, 2.7, 6.0, -0.05, 0.54, 0.01),
             ("sertraline case-control", 2.2, 1.9, 2.5, 0.90, 0.35, 0.71),
             ("sertraline SCCS", 2.1, 1.8, 2.4, 0.79, 0.28, 0.84))
    for lbl, rr, lb, ub, mu, s, paper_p in cases:
        y = math.log(rr)
        se = (math.log(ub) - math.log(lb)) / (2 * 1.959964)
        p_sd = calibrate_p((mu, s), y, se)
        p_var = calibrate_p((mu, math.sqrt(s)), y, se)
        print(f"{lbl}: column read as SD -> p={p_sd:.3f}; read as variance -> p={p_var:.3f}; paper reports {paper_p}")

    print("\n== Systematic error model on southworthReplication / grahamReplication")
    for name in ("southworthReplication", "grahamReplication"):
        c = load(d, name)
        t = np.array(c["trueLogRr"], float)
        y, se = np.array(c["logRr"], float), np.array(c["seLogRr"], float)
        ctl = np.isfinite(t)
        m_new = fit_error_model(y[ctl], se[ctl], t[ctl], legacy=False)
        m_leg = fit_error_model(y[ctl], se[ctl], t[ctl], legacy=True)
        print(f"{name}: controls={ctl.sum()} (negatives={np.sum(t[ctl] == 0)})")
        print("   default model (mean a+b*t, sd c+d*|t|):", np.round(m_new, 6))
        print("   legacy model  (mean a+b*t, sd exp(c+d*t)):", np.round(m_leg, 4))
        oi = np.where(~ctl)[0][0]
        est = calibrate_ci(m_new, y[oi], se[oi])
        print(f"   outcome of interest uncalibrated RR {math.exp(y[oi]):.3f} ({math.exp(y[oi]-1.959964*se[oi]):.3f}-{math.exp(y[oi]+1.959964*se[oi]):.3f});"
              f" calibrated logRr={est[0]:.4f} [{est[1]:.4f}, {est[2]:.4f}] -> RR {math.exp(est[0]):.3f} ({math.exp(est[1]):.3f}-{math.exp(est[2]):.3f})")
        # coverage of the true effect by 95% CI: uncalibrated vs leave-one-negative-control-group-out calibrated
        groups = {}
        names = c["outcomeName"]
        for i in np.where(ctl)[0]:
            groups.setdefault(names[i], []).append(i)
        cov_u, cov_c, n = 0, 0, 0
        for g, members in groups.items():
            train = [j for j in np.where(ctl)[0] if names[j] != g]
            m = fit_error_model(y[train], se[train], t[train], legacy=False)
            for i in members:
                lbu, ubu = y[i] - 1.959964 * se[i], y[i] + 1.959964 * se[i]
                cov_u += lbu < t[i] < ubu
                _, lbc, ubc = calibrate_ci(m, y[i], se[i])
                cov_c += lbc < t[i] < ubc
                n += 1
        print(f"   95% CI coverage of true effect over {n} controls: uncalibrated {cov_u/n:.3f}; leave-one-out calibrated {cov_c/n:.3f}")
    print("   vignette (EmpiricalCiCalibrationVignette.pdf, southworth): meanIntercept -0.066550795 meanSlope 0.933292141"
          " sdIntercept 0.187468405 sdSlope 0.002979502; calibrated logRr -0.3117702 [-0.733957, 0.1067054]")
    print("   PNAS 2018 Table 1 (legacy parameterization): Southworth -0.07 0.93 -1.67 0.02; Graham -0.03 0.99 -2.92 0.29")


if __name__ == "__main__":
    main(sys.argv[1])
