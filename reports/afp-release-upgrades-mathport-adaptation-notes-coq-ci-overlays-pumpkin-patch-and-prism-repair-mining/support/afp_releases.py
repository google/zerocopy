#!/usr/bin/env python3
"""Summarize AFP release continuity from metadata/releases.toml and metadata/release-dates.

Usage: python3 afp_releases.py <releases.toml> <release-dates> [<entries-dir-listing.txt>]
releases.toml maps [Entry] -> { <AFP release date> = "<Isabelle version>" }.
"""
import collections, re, sys
rel = collections.defaultdict(list); cur = None
for line in open(sys.argv[1], encoding="utf-8"):
    line = line.strip()
    m = re.match(r"^\[(.+)\]$", line)
    if m: cur = m.group(1).strip('"'); continue
    m = re.match(r'^(\d{4}-\d{2}-\d{2})\s*=\s*"([^"]+)"', line)
    if m and cur: rel[cur].append((m.group(1), m.group(2)))
order = [l.split("=")[0].strip() for l in open(sys.argv[2]) if "=" in l]
per_ver = collections.Counter(); first = collections.Counter(); last = collections.Counter()
for e, rs in rel.items():
    vs = {v for _, v in rs}
    for v in vs: per_ver[v] += 1
    vo = sorted(vs, key=lambda v: order.index(v) if v in order else -1)
    first[vo[0]] += 1; last[vo[-1]] += 1
print("entries_in_releases_toml", len(rel))
print("isabelle_releases_in_release_dates", len(order), order[0], "...", order[-1])
latest = order[-1]
print(f"entries_released_for_latest({latest})", per_ver[latest])
print("entries_whose_last_release_is_not_latest", sum(c for v, c in last.items() if v != latest))
print("last_release_histogram_excluding_latest", {v: last[v] for v in order if last[v] and v != latest})
gaps = []
for e, rs in rel.items():
    idx = sorted({order.index(v) for _, v in rs if v in order})
    if idx and idx[-1] - idx[0] + 1 != len(idx): gaps.append(e)
print("entries_with_a_skipped_isabelle_release_between_first_and_last", len(gaps), gaps)
print("entries_not_released_for_latest", [e for e, rs in rel.items() if latest not in {v for _, v in rs}])
print("per_release_entry_counts", {v: per_ver[v] for v in order})
multi = sum(1 for e, rs in rel.items() if len(rs) != len({v for _, v in rs}))
print("entries_with_multiple_tarball_dates_for_one_release", multi)
if len(sys.argv) > 3:
    ents = {l.strip().split("/")[-1][:-5] for l in open(sys.argv[3]) if l.startswith("metadata/entries/")}
    print("metadata_entries", len(ents), "not_in_releases_toml", len(ents - set(rel)))
