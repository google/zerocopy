#!/usr/bin/env python3
"""Summarize Rocq CI overlay files (dev/ci/user-overlays/*.sh) and the CI project list.

Usage: python3 rocq_overlays.py <dir-with-overlay-.sh-files> <ci-basic-overlay.sh>
Counts `overlay <project> <giturl> <ref> <prnumber> [<prbranch>]` calls.
"""
import collections, pathlib, re, sys
d = pathlib.Path(sys.argv[1]); files = sorted(p for p in d.glob("*.sh"))
calls = collections.Counter(); per_file = collections.Counter(); prs = []
for f in files:
    m = re.match(r"(\d{5})-", f.name)
    if m: prs.append(int(m.group(1)))
    n = 0
    for line in f.read_text(errors="replace").splitlines():
        mm = re.match(r"\s*overlay\s+(\S+)", line)
        if mm: calls[mm.group(1)] += 1; n += 1
    per_file[n] += 1
basic = pathlib.Path(sys.argv[2]).read_text()
projects = re.findall(r"^project\s+(\S+)", basic, re.M)
subprojects = re.findall(r"^subproject\s+(\S+)", basic, re.M)
print("overlay_files", len(files))
print("pr_number_range", min(prs), max(prs))
print("overlay_calls", sum(calls.values()))
print("distinct_projects_overlaid", len(calls))
print("overlay_calls_per_file_histogram", dict(sorted(per_file.items())))
print("top_projects", calls.most_common(12))
print("ci_basic_overlay_project_declarations", len(projects), "subproject_declarations", len(subprojects))
print("overlaid_projects_not_declared_in_ci_basic_overlay", sorted(set(calls) - set(projects) - set(subprojects)))
