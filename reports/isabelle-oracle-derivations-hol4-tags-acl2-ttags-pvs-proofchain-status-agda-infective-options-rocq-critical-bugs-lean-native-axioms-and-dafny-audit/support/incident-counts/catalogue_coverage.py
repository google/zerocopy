#!/usr/bin/env python3
"""Measure how many rocq-prover/rocq issues labelled 'kind: inconsistency' are
referenced by number in dev/doc/critical-bugs.md.
Usage: catalogue_coverage.py path/to/critical-bugs.md
Requires an authenticated `gh` CLI (read-only search API)."""
import json, re, subprocess, sys, datetime
md = open(sys.argv[1], encoding='utf-8').read()
refs = set(int(n) for n in re.findall(r'(?:#|issues/)(\d{3,6})\b', md))
items = []
for page in (1, 2):
    out = subprocess.run(['gh', 'api', '-X', 'GET', 'search/issues', '-f',
                          'q=repo:rocq-prover/rocq label:"kind: inconsistency" is:issue',
                          '-f', 'per_page=100', '-f', f'page={page}'],
                         capture_output=True, text=True, check=True).stdout
    d = json.loads(out)
    items += d['items']
    if len(items) >= d['total_count']:
        break
print('observed_utc', datetime.datetime.now(datetime.timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ'))
print('labelled issues fetched', len(items))
hit = [i for i in items if i['number'] in refs]
print('referenced by number in catalogue', len(hit))
for st in ('open', 'closed'):
    s = [i for i in items if i['state'] == st]
    print(f'  {st}: {len(s)} labelled, {sum(1 for i in s if i["number"] in refs)} referenced')
years = {}
for i in items:
    y = i['created_at'][:4]
    years.setdefault(y, [0, 0]); years[y][0] += 1; years[y][1] += i['number'] in refs
print('by creation year (labelled, referenced):', dict(sorted(years.items())))
