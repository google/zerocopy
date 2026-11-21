#!/usr/bin/env python3
"""Run the IOOS compliance-checker (cf:1.8) on each probe file and summarise.

For each file prints exit code, scored/possible points, and the failure messages
that mention the probe variable or the edge case, plus any check errors.
Usage: run_cases.py <compliance-checker executable> <dir with .nc files>
"""
import json, subprocess, sys, pathlib, time

exe, d = sys.argv[1], pathlib.Path(sys.argv[2])
for nc in sorted(d.glob('*.nc')):
    t0 = time.perf_counter()
    r = subprocess.run([exe, '--test', 'cf:1.8', '--format', 'json_new', '-o', '-', str(nc)],
                       capture_output=True, text=True)
    el = time.perf_counter() - t0
    try:
        j = json.loads(r.stdout[r.stdout.find('{'):])
    except Exception:
        print(f'## {nc.name}: exit={r.returncode} UNPARSEABLE OUTPUT; stderr tail: {r.stderr[-400:]!r}')
        continue
    res = next(iter(j.values()))['cf:1.8']
    scored, possible = res.get('scored_points'), res.get('possible_points')
    msgs = []
    for prio in ('high_priorities', 'medium_priorities', 'low_priorities'):
        for item in res.get(prio, []):
            for m in item.get('msgs', []):
                msgs.append(f"[{prio.split('_')[0]}] {item.get('name')}: {m}")
    errors = res.get('errors') or {}
    print(f'## {nc.name}: exit={r.returncode} scored={scored}/{possible} wall={el:.2f}s errors={len(errors)}')
    for k, v in errors.items():
        print(f'   ERROR in {k}: {str(v)[:300]}')
    for m in msgs:
        print('   ', m[:260])
