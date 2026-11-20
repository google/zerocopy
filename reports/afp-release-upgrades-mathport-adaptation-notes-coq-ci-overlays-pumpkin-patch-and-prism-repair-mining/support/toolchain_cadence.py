#!/usr/bin/env python3
"""Cadence statistics for Mathlib `lean-toolchain` bumps listed in history_counts.out.

Usage: python3 toolchain_cadence.py history_counts.out
"""
import datetime, re, statistics, sys

lines = [l for l in open(sys.argv[1]) if "bump toolchain" in l]
ds = sorted(datetime.datetime.fromisoformat(l.split()[1].replace("Z", "+00:00")) for l in lines)
iv = [(b - a).total_seconds() / 86400 for a, b in zip(ds, ds[1:])]
print("bumps", len(lines), "span_days", round((ds[-1] - ds[0]).total_seconds() / 86400, 1),
      "mean_interval_days", round(statistics.mean(iv), 1), "median_interval_days", round(statistics.median(iv), 1),
      "max_interval_days", round(max(iv), 1), "min_interval_days", round(min(iv), 2))
finals = [re.search(r"v4\.\d+\.0", l).group(0) for l in lines if re.search(r"v4\.\d+\.0[ `)]", l) and "-rc" not in l]
print("final_release_bumps", len(finals), sorted(finals, key=lambda v: int(v.split(".")[1])))
print("rc_bumps", len(lines) - len(finals))
rc1, fin = {}, {}
for l in lines:
    d = datetime.datetime.fromisoformat(l.split()[1].replace("Z", "+00:00"))
    m = re.search(r"v4\.(\d+)\.0(-rc(\d+))?", l)
    if m.group(2) and m.group(3) == "1":
        rc1[int(m.group(1))] = d
    elif not m.group(2):
        fin[int(m.group(1))] = d
for k in sorted(set(rc1) & set(fin)):
    print("v4.%d rc1_to_final_on_master_days" % k, round((fin[k] - rc1[k]).total_seconds() / 86400, 1))
