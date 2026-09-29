#!/usr/bin/env python3
"""Read-only validation of the I054–I106 row and cited-package review."""
import csv
import hashlib
import json
from pathlib import Path
import re

here = Path(__file__).resolve().parent
root = here.parent
reports = root.parent
v22 = reports / 'anneal-3730-3731-final-coverage-audit-2026-09-29-v22/support'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
meta = json.loads((root / 'REPORT.json').read_text())
assert sha(v22 / 'investigation-final-v22.csv') == meta['subjects'][0]['identity']['investigation_csv_sha256']
assert sha(v22 / 'row-challenge-v22.json') == meta['subjects'][0]['identity']['row_challenge_sha256']
assert sha(v22 / 'issue-scope-snapshot.json') == meta['subjects'][1]['identity']['sha256']

with (v22 / 'investigation-final-v22.csv').open() as f:
    source = {r['id']: r for r in csv.DictReader(f)}
with (here / 'row-review.csv').open() as f:
    rows = list(csv.DictReader(f))
expected_ids = [f'I{i:03}' for i in range(54,107)]
assert [r['id'] for r in rows] == expected_ids
assert sum(r['review_status']=='partial' for r in rows)==51
assert sum(r['review_status']=='not-run' for r in rows)==1
assert sum(r['review_status']=='conditional' for r in rows)==1
changed_prereqs = {'I065','I071','I077','I089','I094','I101','I103'}
for r in rows:
    old = source[r['id']]
    assert r['title']==old['title'] and r['requested_scope']==old['requested_scope']
    assert r['review_status']==old['v22_status']
    assert r['gate_categories']==old['v22_gate_categories']
    assert (r['next_prerequisite']!=old['v22_next_prerequisite']) == (r['id'] in changed_prereqs)
    if r['id'] in changed_prereqs:
        assert 'OCaml/Dune/opam' not in r['next_prerequisite']
    if r['id']=='I080':
        assert r['new_local_experiment']=='I080 shared-target two-process'
        assert 'anneal-3731-i080-shared-cargo-target-two-process-2026-09-29' in r['cited_packages'].split(';')
        assert r['specific_remaining_delta'] != old['v22_specific_remaining_delta']
    else:
        assert not r['new_local_experiment']
        assert r['specific_remaining_delta']==old['v22_specific_remaining_delta']
    assert all((reports / p / 'REPORT.md').exists() for p in r['cited_packages'].split(';'))

with (here / 'package-inventory.csv').open() as f:
    packages = list(csv.DictReader(f))
assert len(packages)==85
assert len({r['package'] for r in packages})==85
assert sum(int(r['file_count']) for r in packages)==3044
assert sum(r['checker_status']=='none' for r in packages)==56
assert sum(r['checker_status']=='passed_read_only' for r in packages)==24
assert sum(r['checker_status']=='initially_skipped' for r in packages)==5
for item in packages:
    package = reports / item['package']
    assert sha(package/'REPORT.md')==item['report_md_sha256']
    assert sha(package/'REPORT.json')==item['report_json_sha256']
    assert sum(p.is_file() for p in package.rglob('*'))==int(item['file_count'])
    if item['checker_status']!='none':
        assert (package/'support/check.py').exists()

links=0
for item in packages:
    package=reports/item['package']
    for url in re.findall(r'\]\((support/[^)]+)\)',(package/'REPORT.md').read_text()):
        url=url.split('#')[0]
        if any(c in url for c in '*{$'): continue
        links+=1
        assert (package/url).exists(),(item['package'],url)
assert links==86
new=reports/'anneal-3731-i080-shared-cargo-target-two-process-2026-09-29'
assert sha(new/'support/probe-observed.py')==meta['subjects'][2]['identity']['observed_probe_sha256']
md=(root/'REPORT.md').read_text()
assert all(f'| {id} |' in md for id in expected_ids)
print('PASS: 53 unchanged statuses, seven exact gate corrections, I080 evidence, 85 cited packages and 86 links')
