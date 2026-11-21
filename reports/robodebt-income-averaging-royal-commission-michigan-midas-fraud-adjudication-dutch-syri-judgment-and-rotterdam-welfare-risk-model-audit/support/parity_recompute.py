#!/usr/bin/env python3
"""Recompute the published pairwise t-test p-values of one statistical parity experiment
(Lighthouse-Reports/suspicion_machine, results/statistical_parity/single_feature/
sf_persoon_geslacht_vrouw) from the published per-group n / mean / sd, and summarise the
published synthetic data file (data/01_raw/synth_data.csv).

The upstream analysis (notebooks/analyze.R) calls rstatix::pairwise_t_test(Ja ~ IV) with
its defaults; for two groups that is a two-sample t-test with pooled SD (Student). Means and
SDs are published rounded to 3 decimals, so the recomputation reports the p-value at the
rounded values and the range implied by +-0.0005 rounding of each mean.
Usage: python3 parity_recompute.py <sum_stats.csv> <t_test.csv> <synth_data.csv>
"""
import csv
import json
import math
import sys


def betacf(a, b, x, itmax=400, eps=3e-16):
    qab, qap, qam = a + b, a + 1.0, a - 1.0
    c, d = 1.0, 1.0 - qab * x / qap
    d = 1.0 / (d if abs(d) > 1e-300 else 1e-300)
    h = d
    for m in range(1, itmax + 1):
        m2 = 2 * m
        aa = m * (b - m) * x / ((qam + m2) * (a + m2))
        d = 1.0 + aa * d
        d = 1.0 / (d if abs(d) > 1e-300 else 1e-300)
        c = 1.0 + aa / c
        c = c if abs(c) > 1e-300 else 1e-300
        h *= d * c
        aa = -(a + m) * (qab + m) * x / ((a + m2) * (qap + m2))
        d = 1.0 + aa * d
        d = 1.0 / (d if abs(d) > 1e-300 else 1e-300)
        c = 1.0 + aa / c
        c = c if abs(c) > 1e-300 else 1e-300
        delta = d * c
        h *= delta
        if abs(delta - 1.0) < eps:
            break
    return h


def betai(a, b, x):
    if x <= 0:
        return 0.0
    if x >= 1:
        return 1.0
    lbt = math.lgamma(a + b) - math.lgamma(a) - math.lgamma(b) + a * math.log(x) + b * math.log(1 - x)
    if x < (a + 1) / (a + b + 2):
        return math.exp(lbt) * betacf(a, b, x) / a
    return 1.0 - math.exp(lbt) * betacf(b, a, 1 - x) / b


def two_sided_p(t, df):
    return betai(df / 2.0, 0.5, df / (df + t * t))


def pooled_t(n1, m1, s1, n2, m2, s2):
    df = n1 + n2 - 2
    sp2 = ((n1 - 1) * s1 ** 2 + (n2 - 1) * s2 ** 2) / df
    t = (m2 - m1) / math.sqrt(sp2 * (1.0 / n1 + 1.0 / n2))
    return t, df


def main(sum_path, tt_path, synth_path):
    groups = {}
    for r in csv.DictReader(open(sum_path, newline="")):
        level = r["IV"].strip().splitlines()[-1].strip()
        groups.setdefault(r["data_type"], []).append(
            (level, int(r["n"]), float(r["mean"]), float(r["sd"]) if r["sd"] != "NA" else None,
             float(r["share_above_td_threshold"])))
    published = {r["data_type"]: float(r["p"]) for r in csv.DictReader(open(tt_path, newline=""))}
    out = {}
    for dt, g in groups.items():
        (l1, n1, m1, s1, sh1), (l2, n2, m2, s2, sh2) = g
        t, df = pooled_t(n1, m1, s1, n2, m2, s2)
        lo_t, _ = pooled_t(n1, m1 + 0.0005, s1, n2, m2 - 0.0005, s2)
        hi_t, _ = pooled_t(n1, m1 - 0.0005, s1, n2, m2 + 0.0005, s2)
        out[dt] = {
            "groups": [l1, l2], "n": [n1, n2], "mean": [m1, m2], "sd": [s1, s2],
            "share_above_threshold": [round(sh1, 4), round(sh2, 4)],
            "t_at_rounded_values": round(t, 3), "df": df,
            "p_at_rounded_values": float("%.3g" % two_sided_p(t, df)),
            "p_range_from_mean_rounding": [float("%.3g" % two_sided_p(hi_t, df)), float("%.3g" % two_sided_p(lo_t, df))],
            "p_published": published.get(dt),
        }
    with open(synth_path, newline="") as fh:
        rd = csv.reader(fh)
        hdr = next(rd)
        rows = list(rd)
    gi = hdr.index("persoon_geslacht_vrouw")
    ai = hdr.index("persoon_leeftijd_bij_onderzoek")
    ages = [float(x[ai]) for x in rows]
    out["synth_data_csv"] = {
        "rows": len(rows), "columns": len(hdr),
        "persoon_geslacht_vrouw_counts": {v: sum(1 for x in rows if x[gi] == v) for v in sorted({x[gi] for x in rows})},
        "persoon_leeftijd_bij_onderzoek_min_mean_max": [min(ages), round(sum(ages) / len(ages), 2), max(ages)],
    }
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main(*sys.argv[1:4])
