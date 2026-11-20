#!/usr/bin/env python3
"""Run NIST StRD univariate, ANOVA and linear-regression datasets through numpy, CPython's
statistics module, and textbook formulas; report log relative error (LRE) against the
certified values, and independently recompute the certified values in exact rationals.

Inputs: a directory containing the StRD .dat files, obtained from
  univariate: https://www.itl.nist.gov/div898/strd/univ/data/<Name>.dat
  linear LS : https://www.itl.nist.gov/div898/strd/lls/data/LINKS/DATA/<Name>.dat
  ANOVA     : scipy/scipy (pinned revision in REPORT.json), scipy/stats/tests/data/nist_anova/
The SHA-256 of every file read is printed so a later run can confirm identical inputs.

LRE(x, c) = -log10(|x - c| / |c|) (or -log10|x - c| when c == 0), capped at 15 and floored at 0.
"Toy" rows are re-implementations of formulas written for this probe, not any package's code.

Usage: python3 strd_probe.py <data_dir>
"""
import hashlib
import math
import os
import re
import statistics
import sys
from fractions import Fraction

import numpy as np


def lre(x, c):
    x, c = Fraction(x), Fraction(c)
    if x == c:
        return 15.0
    d = abs(x - c) if c == 0 else abs(x - c) / abs(c)
    v = -math.log10(d)
    return max(0.0, min(15.0, v))


def read(path):
    raw = open(path, "rb").read()
    return raw.decode("ascii", "replace").replace("\r", ""), hashlib.sha256(raw).hexdigest()[:16]


def data_rows(text, start_marker_line):
    lines = text.split("\n")
    return [l.split() for l in lines[start_marker_line - 1:] if l.strip()]


def header_range(text, label):
    m = re.search(label + r"\s*:?\s*\(?lines\s+(\d+)\s+to\s+(\d+)", text)
    return int(m.group(1)), int(m.group(2))


# ---------------------------------------------------------------- univariate
def univariate(d):
    print("\n## Univariate summary statistics (LRE; mean / sd / r1)")
    print("%-9s %-24s %-24s %-24s %-24s" % ("dataset", "numpy(mean,std ddof=1)", "statistics(mean,stdev)",
                                             "toy one-pass sd", "toy two-pass r1"))
    for name in ("PiDigits", "Lottery", "Lew", "Mavro", "Michelso", "NumAcc1", "NumAcc2", "NumAcc3", "NumAcc4"):
        p = os.path.join(d, name + ".dat")
        if not os.path.exists(p):
            continue
        text, h = read(p)
        a, b = header_range(text, "Data")
        lines = text.split("\n")
        ystr = [l.split()[0] for l in lines[a - 1:b] if l.strip()]
        cert = {}
        for key, pat in (("mean", r"ybar:\s*([-0-9.E+]+)"), ("sd", r"\s s:\s*([-0-9.E+]+)"), ("r1", r"r\(1\):\s*([-0-9.E+]+)")):
            m = re.search(pat, text)
            cert[key] = Fraction(m.group(1))
        y = np.array([float(s) for s in ystr])
        yf = [Fraction(s) for s in ystr]  # exact decimal data
        n = len(yf)
        # exact recomputation of the certified values (checks the reference itself)
        mu = sum(yf) / n
        ss = sum((v - mu) ** 2 for v in yf)
        r1x = sum((yf[i] - mu) * (yf[i - 1] - mu) for i in range(1, n)) / ss
        sdx = math.sqrt(ss / (n - 1))
        ok = (lre(float(mu), cert["mean"]) >= 14.5, lre(sdx, cert["sd"]) >= 14.5, lre(float(r1x), cert["r1"]) >= 14.5)
        npm, nps = float(np.mean(y)), float(np.std(y, ddof=1))
        stm, sts = statistics.mean([float(s) for s in ystr]), statistics.stdev([float(s) for s in ystr])
        # toy one-pass "calculator" variance: (sum y^2 - n*ybar^2)/(n-1), in binary64
        s1 = 0.0
        s2 = 0.0
        for v in y:
            s1 += v
            s2 += v * v
        var1 = (s2 - s1 * s1 / n) / (n - 1)
        sd1 = math.sqrt(var1) if var1 > 0 else 0.0
        ybar = float(np.mean(y))
        dev = y - ybar
        r1t = float(np.dot(dev[1:], dev[:-1]) / np.dot(dev, dev))
        # representation limit: exact sd of the binary64-converted data (no rounding in the
        # algorithm at all); no binary64 algorithm can be expected to beat this LRE
        yb = [Fraction(float(s)) for s in ystr]
        mub = sum(yb) / n
        sdb = math.sqrt(sum((v - mub) ** 2 for v in yb) / (n - 1))
        print("%-9s %5.1f %5.1f %s %-10s %5.1f %5.1f %-12s %5.1f %-17s %5.1f   [repr-limit sd LRE %4.1f; sha256 %s; exact-recompute-matches=%s]" % (
            name, lre(npm, cert["mean"]), lre(nps, cert["sd"]), "", "",
            lre(stm, cert["mean"]), lre(sts, cert["sd"]), "",
            lre(sd1, cert["sd"]), "", lre(r1t, cert["r1"]), lre(sdb, cert["sd"]), h, all(ok)))


# ---------------------------------------------------------------- ANOVA
def anova(d):
    print("\n## One-way ANOVA F statistic (LRE)")
    print("%-8s %-10s %-10s %-10s %s" % ("dataset", "toy 2-pass", "toy 1-pass", "exact", "notes"))
    for name in ("SiRstv", "SmLs01", "SmLs02", "SmLs03", "AtmWtAg", "SmLs04", "SmLs05", "SmLs06", "SmLs07", "SmLs08", "SmLs09"):
        p = os.path.join(d, name + ".dat")
        if not os.path.exists(p):
            continue
        text, h = read(p)
        m = re.search(r"Between \w+\s+\d+\s+\S+\s+\S+\s+(\S+)", text)
        fcert = Fraction(m.group(1))
        a, b = header_range(text, "Data")
        lines = text.split("\n")
        rows = [l.split() for l in lines[a - 1:b] if l.strip()]
        groups = {}
        for g, v in rows:
            groups.setdefault(g, []).append(v)
        k = len(groups)
        N = sum(len(v) for v in groups.values())
        # exact
        gm = {g: sum(Fraction(x) for x in v) / len(v) for g, v in groups.items()}
        grand = sum(sum(Fraction(x) for x in v) for v in groups.values()) / N
        ssb = sum(len(v) * (gm[g] - grand) ** 2 for g, v in groups.items())
        ssw = sum(sum((Fraction(x) - gm[g]) ** 2 for x in v) for g, v in groups.items())
        fx = (ssb / (k - 1)) / (ssw / (N - k))
        # toy two-pass (centered) in binary64
        gv = {g: np.array([float(x) for x in v]) for g, v in groups.items()}
        allv = np.concatenate(list(gv.values()))
        gr = float(np.mean(allv))
        ssb2 = sum(len(v) * (float(np.mean(v)) - gr) ** 2 for v in gv.values())
        ssw2 = sum(float(np.sum((v - np.mean(v)) ** 2)) for v in gv.values())
        f2 = (ssb2 / (k - 1)) / (ssw2 / (N - k))
        # toy one-pass (raw sums of squares) in binary64
        tot = 0.0
        tot2 = 0.0
        ssb1_terms = 0.0
        for v in gv.values():
            s = 0.0
            for x in v:
                s += x
                tot2 += x * x
            tot += s
            ssb1_terms += s * s / len(v)
        ssb1 = ssb1_terms - tot * tot / N
        ssw1 = tot2 - ssb1_terms
        f1 = (ssb1 / (k - 1)) / (ssw1 / (N - k)) if ssw1 != 0 else float("inf")
        # representation limit: exact F of the binary64-converted data
        gb = {g: [Fraction(float(x)) for x in v] for g, v in groups.items()}
        gmb = {g: sum(v) / len(v) for g, v in gb.items()}
        grandb = sum(sum(v) for v in gb.values()) / N
        ssbb = sum(len(v) * (gmb[g] - grandb) ** 2 for g, v in gb.items())
        sswb = sum(sum((x - gmb[g]) ** 2 for x in v) for g, v in gb.items())
        fb = (ssbb / (k - 1)) / (sswb / (N - k))
        print("%-8s %-10.1f %-10.1f %-10.1f repr-limit %4.1f k=%d N=%d sha256=%s" % (
            name, lre(f2, fcert), lre(f1, fcert) if math.isfinite(f1) else 0.0, lre(float(fx), fcert),
            lre(float(fb), fcert), k, N, h))


# ---------------------------------------------------------------- linear LS
POLY = {"Pontius": 2, "Filip": 10, "Wampler1": 5, "Wampler2": 5, "Wampler3": 5, "Wampler4": 5, "Wampler5": 5}


def design(name, rows):
    y = [r[0] for r in rows]
    if name == "Longley":
        X = [["1"] + r[1:] for r in rows]
        return X, y, True
    xs = [r[1] for r in rows]
    if name in ("NoInt1", "NoInt2"):
        return [[x] for x in xs], y, False
    deg = POLY.get(name, 1)
    return [[x] for x in xs], y, deg


def exact_ls(Xf, yf):
    p = len(Xf[0])
    A = [[sum(r[i] * r[j] for r in Xf) for j in range(p)] for i in range(p)]
    bvec = [sum(r[i] * yy for r, yy in zip(Xf, yf)) for i in range(p)]
    # Gauss-Jordan in rationals
    M = [A[i] + [bvec[i]] for i in range(p)]
    for c in range(p):
        piv = next(r for r in range(c, p) if M[r][c] != 0)
        M[c], M[piv] = M[piv], M[c]
        for r in range(p):
            if r != c and M[r][c] != 0:
                f = M[r][c] / M[c][c]
                M[r] = [a - f * bb for a, bb in zip(M[r], M[c])]
    return [M[i][p] / M[i][i] for i in range(p)]


def linreg(d):
    print("\n## Linear least squares: minimum LRE over coefficients")
    print("%-9s %-16s %-14s %-12s %-12s %s" % ("dataset", "numpy lstsq", "toy normal-eq", "toy QR", "exact", "notes"))
    for name in ("Norris", "Pontius", "NoInt1", "NoInt2", "Filip", "Longley", "Wampler1", "Wampler2", "Wampler3", "Wampler4", "Wampler5"):
        p = os.path.join(d, name + ".dat")
        if not os.path.exists(p):
            continue
        text, h = read(p)
        a, b = header_range(text, "Data")
        lines = text.split("\n")
        rows = [l.split() for l in lines[a - 1:b] if l.strip()]
        # NIST lls files list the response first only for some datasets; normalize: y is first column except Longley
        if name != "Longley":
            rows = [[r[0], r[1]] for r in rows]
        else:
            rows = [[r[0]] + r[1:] for r in rows]
        certs = re.findall(r"^\s+B\d+\s+(\S+)\s+\S+", text, re.M)
        cert = [Fraction(c.replace("E", "e")) for c in certs]
        if name == "Longley":
            yv = [r[0] for r in rows]
            Xs = [["1"] + r[1:] for r in rows]
            Xf = [[Fraction(v) for v in r] for r in Xs]
        elif name in ("NoInt1", "NoInt2"):
            yv = [r[0] for r in rows]
            Xf = [[Fraction(r[1])] for r in rows]
        else:
            yv = [r[0] for r in rows]
            deg = POLY.get(name, 1)
            Xf = [[Fraction(r[1]) ** k for k in range(deg + 1)] for r in rows]
        yf = [Fraction(v) for v in yv]
        bx = exact_ls(Xf, yf)
        X = np.array([[float(v) for v in r] for r in Xf])
        y = np.array([float(v) for v in yf])
        bl, _, rank, _ = np.linalg.lstsq(X, y, rcond=None)
        bl0, _, rank0, _ = np.linalg.lstsq(X, y, rcond=0.0)
        bxb = exact_ls([[Fraction(float(v)) for v in r] for r in Xf], [Fraction(float(v)) for v in yf])
        try:
            bn = np.linalg.solve(X.T @ X, X.T @ y)
        except np.linalg.LinAlgError:
            bn = np.full(X.shape[1], np.nan)
        Q, R = np.linalg.qr(X)
        bq = np.linalg.solve(R, Q.T @ y)

        def mlre(bs):
            if any(not math.isfinite(v) for v in bs):
                return 0.0
            return min(lre(float(v), c) for v, c in zip(bs, cert))
        print("%-9s %4.1f(rank %2d) %-14.1f %-12.1f %-12.1f lstsq(rcond=0) %4.1f(rank %2d) repr-limit %4.1f p=%d cond2(X)=%.1e sha256=%s" % (
            name, mlre(bl), rank, mlre(bn), mlre(bq), min(lre(float(v), c) for v, c in zip(bx, cert)),
            mlre(bl0), rank0, min(lre(float(v), c) for v, c in zip(bxb, cert)),
            X.shape[1], np.linalg.cond(X), h))


def main():
    d = sys.argv[1]
    print("# numpy", np.__version__, "| python", sys.version.split()[0])
    univariate(d)
    anova(d)
    linreg(d)


if __name__ == "__main__":
    main()
