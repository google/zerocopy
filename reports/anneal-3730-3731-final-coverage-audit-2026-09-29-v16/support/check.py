#!/usr/bin/env python3
"""Verify the v16 issue ledger, new packages and deterministic regeneration."""
import csv
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def generated_hashes():
    names=('investigation-final-v16.csv','3730-crosswalk-final-v16.csv',
           'new-package-review-v16.csv','new-file-inventory-v16.csv','validation-v16.json')
    return {name:sha(HERE/name) for name in names}
before=generated_hashes()
for _ in range(2):
    run=subprocess.run([sys.executable,str(HERE/'build_audit.py')],cwd=ROOT,text=True,capture_output=True,timeout=60)
    assert run.returncode==0,(run.stdout,run.stderr)
    assert generated_hashes()==before,'audit build changed frozen outputs'
v=json.loads((HERE/'validation-v16.json').read_text())
assert v['issue_3730_heading_count']==174 and v['issue_3731_id_count']==159
assert v['reviewed_noncomplete_rows']==318
assert v['status_counts']['investigations']=={'complete':2,'partial':153,'not-run':1,'conditional':3}
assert v['status_counts']['suggestions']=={'complete':4,'partial':161,'not-run':5,'conditional':4}
for filename,count,key in [('investigation-final-v16.csv',159,'id'),('3730-crosswalk-final-v16.csv',174,'3730_id')]:
    with (HERE/filename).open(newline='') as file:rows=list(csv.DictReader(file))
    assert len(rows)==count and len({r[key] for r in rows})==count
    assert all(r['v16_specific_remaining_delta'] and r['v16_disposition'] for r in rows)
for package in v['new_packages']:
    script=ROOT/'reports'/package/'support'/'check.py'
    assert script.is_file(),package
    result=subprocess.run([sys.executable,str(script)],cwd=ROOT,capture_output=True,text=True,timeout=60)
    assert result.returncode==0,(package,result.stdout,result.stderr)
print(f"v16 deterministic audit passed: 159/174 rows, {v['new_package_count']} package checkers")
