#!/usr/bin/env python3
"""Toy probe: how method choices change time in therapeutic range (TTR).

Synthetic INR series only (no patient data). Implements:
  * Rosendaal-style linear interpolation between consecutive INR measurements,
    evaluated exactly (piecewise-linear crossing times) and on a daily grid;
  * fraction of INR tests in range;
  * variants: target range bounds (2.0-3.0 vs 1.8-3.2), observation window start
    (day 0 vs day 4), window end (stop at last INR vs carry last value to day 28),
    and refusing to interpolate across gaps longer than a threshold.
Deterministic: random cohort uses random.Random(20261121).
Usage: python3 ttr_probe.py
"""
import json
import random


def interp_time_in_range(points, lo, hi, start, end, carry_forward=False, max_gap=None):
    """Exact time (days) in [lo, hi] for piecewise-linear INR between measurements.

    points: list of (day, inr), sorted by day. Only the portion of each segment
    inside [start, end] counts. If carry_forward, the last INR is held constant to `end`.
    Segments longer than max_gap (days) are excluded from numerator and denominator.
    Returns (days_in_range, days_observed).
    """
    pts = sorted(points)
    if carry_forward and pts[-1][0] < end:
        pts = pts + [(end, pts[-1][1])]
    in_range = observed = 0.0
    for (t0, y0), (t1, y1) in zip(pts, pts[1:]):
        if t1 <= t0:
            continue
        if max_gap is not None and (t1 - t0) > max_gap:
            continue
        a, b = max(t0, start), min(t1, end)
        if b <= a:
            continue
        observed += b - a
        # INR(t) = y0 + (y1-y0)*(t-t0)/(t1-t0); find sub-interval of [a,b] where lo<=INR<=hi
        slope = (y1 - y0) / (t1 - t0)

        def inr(t):
            return y0 + slope * (t - t0)

        if slope == 0:
            in_range += (b - a) if lo <= y0 <= hi else 0.0
            continue
        ta = t0 + (lo - y0) / slope
        tb = t0 + (hi - y0) / slope
        s_lo, s_hi = min(ta, tb), max(ta, tb)
        u, v = max(a, s_lo), min(b, s_hi)
        if v > u:
            in_range += v - u
    return in_range, observed


def daily_grid_ttr(points, lo, hi, start, end):
    """Daily-grid variant: INR interpolated at integer days start..end-1 inclusive of start."""
    pts = sorted(points)
    days_in = days = 0
    for d in range(int(start), int(end)):
        for (t0, y0), (t1, y1) in zip(pts, pts[1:]):
            if t0 <= d <= t1 and t1 > t0:
                y = y0 + (y1 - y0) * (d - t0) / (t1 - t0)
                days += 1
                days_in += 1 if (lo <= round(y, 1) <= hi) else 0
                break
    return days_in, days


def fraction_tests_in_range(points, lo, hi, start, end):
    vals = [y for t, y in points if start <= t <= end]
    return sum(lo <= y <= hi for y in vals), len(vals)


PATIENTS = {
    "A_overshoot": [(0, 1.2), (3, 1.6), (5, 2.4), (8, 3.6), (12, 2.8), (19, 2.2), (26, 2.6)],
    "B_oscillating": [(0, 1.0), (4, 2.1), (7, 1.7), (11, 2.9), (14, 3.4), (21, 2.5), (28, 2.0)],
    "C_sparse_gap": [(0, 1.1), (4, 1.9), (6, 2.5), (35, 2.6)],
    "D_borderline": [(0, 1.0), (4, 1.9), (7, 1.95), (11, 3.1), (14, 3.15), (21, 1.85), (28, 2.05)],
}

VARIANTS = [
    # name, lo, hi, start, end, carry_forward, max_gap
    ("rosendaal_2-3_d0-28", 2.0, 3.0, 0, 28, False, None),
    ("rosendaal_2-3_d4-28", 2.0, 3.0, 4, 28, False, None),
    ("rosendaal_2-3_d4-28_carry", 2.0, 3.0, 4, 28, True, None),
    ("rosendaal_2-3_d4-28_gap>14_excluded", 2.0, 3.0, 4, 28, False, 14),
    ("rosendaal_1.8-3.2_d4-28", 1.8, 3.2, 4, 28, False, None),
]


def pct(n, d):
    return None if d == 0 else round(100.0 * n / d, 1)


def per_patient():
    out = {}
    for name, pts in PATIENTS.items():
        row = {}
        for vname, lo, hi, s, e, cf, mg in VARIANTS:
            n, d = interp_time_in_range(pts, lo, hi, s, e, cf, mg)
            row[vname] = pct(n, d)
        n, d = daily_grid_ttr(pts, 2.0, 3.0, 4, 28)
        row["daily_grid_rounded_2-3_d4-28"] = pct(n, d)
        n, d = fraction_tests_in_range(pts, 2.0, 3.0, 4, 28)
        row["fraction_of_tests_2-3_d4-28"] = pct(n, d)
        out[name] = row
    return out


def simulate_cohort(n=500, seed=20261121):
    """Toy INR trajectories: INR rises toward a patient-specific plateau with noise."""
    rng = random.Random(seed)
    schedule = [0, 3, 5, 7, 10, 14, 21, 28]
    cohort = []
    for _ in range(n):
        plateau = rng.gauss(2.5, 0.6)
        rate = rng.uniform(0.15, 0.45)
        pts = []
        for d in schedule:
            if d not in (0, 28) and rng.random() < 0.25:
                continue  # missed visit
            mean = 1.0 + (plateau - 1.0) * (1 - (1 - rate) ** d)
            pts.append((d, max(0.8, round(mean + rng.gauss(0, 0.35), 1))))
        cohort.append(pts)
    return cohort


def cohort_summary():
    cohort = simulate_cohort()
    names = [v[0] for v in VARIANTS] + ["fraction_of_tests_2-3_d4-28"]
    vals = {k: [] for k in names}
    for pts in cohort:
        for vname, lo, hi, s, e, cf, mg in VARIANTS:
            nn, dd = interp_time_in_range(pts, lo, hi, s, e, cf, mg)
            vals[vname].append(100.0 * nn / dd if dd else float("nan"))
        nn, dd = fraction_tests_in_range(pts, 2.0, 3.0, 4, 28)
        vals["fraction_of_tests_2-3_d4-28"].append(100.0 * nn / dd if dd else float("nan"))
    ref = vals["rosendaal_2-3_d4-28"]
    summ = {}
    for k, v in vals.items():
        good = [x for x in v if x == x]
        diffs = [abs(a - b) for a, b in zip(v, ref) if a == a and b == b]
        summ[k] = {
            "cohort_mean_ttr_pct": round(sum(good) / len(good), 2),
            "mean_abs_diff_vs_rosendaal_2-3_d4-28_pp": round(sum(diffs) / len(diffs), 2),
            "share_patients_diff_gt_10pp": round(100.0 * sum(d > 10 for d in diffs) / len(diffs), 1),
        }
    return summ


if __name__ == "__main__":
    print(json.dumps({"per_patient": per_patient(), "cohort_n500_seed20261121": cohort_summary()}, indent=1))
