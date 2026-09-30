#!/usr/bin/env python3
"""Offline validation of every frozen cohort row and its exact claim excerpt.

Run from a checkout containing the frozen reference commit. This deliberately
does not claim to validate the remote 4.34.1 source pages offline.
"""
import csv
import hashlib
import json
import subprocess
import sys
from pathlib import Path

BASE = Path(__file__).resolve().parent
FROZEN = '3c82f8819d4f4ce0ad1f043e7771e2f0ebce0d73'
OLD_LEAN = '3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc'
NEW_LEAN = '5045d0056413266e57c625dcd7c365b10e377c52'
OLD_MATHLIB = '5450b53e5ddc75d46418fabb605edbf36bd0beb6'
NEW_MATHLIB = 'd13f23b723b8a846827a245b89c10fc7d3f11612'
SPECIAL = {'R414': 'cache_mapping_read_delta', 'R421': 'config_cache_location_delta', 'R422': 'config_cache_location_delta'}

def blob(ref, path):
    return subprocess.check_output(['git', 'show', f'{ref}:{path}'], stderr=subprocess.DEVNULL)

def require(ok, message):
    if not ok:
        raise AssertionError(message)

def main():
    doc = json.loads((BASE / 'matrix.json').read_text())
    require(doc['frozen_reference_commit'] == FROZEN, 'frozen commit changed')
    rows = doc['rows']
    selected = list(csv.DictReader((BASE / 'frozen-cohort.csv').open()))
    require(len(rows) == len(selected) == 161, 'cohort count mismatch')
    require(len({x['inventory_id'] for x in rows}) == 161, 'duplicate row ID')
    require(len({x['report_md'] for x in rows}) == 161, 'duplicate report path')
    require(len({x['report_json'] for x in rows}) == 161, 'duplicate metadata path')
    require({(r['inventory_id'], r['report_md'], r['report_json']) for r in rows} ==
            {(r['inventory_id'], r['report_md'], r['report_json']) for r in selected},
            'matrix does not match frozen cohort selector')
    require(all(r['cohort'] == 'Lean/Lake v4.30.0-rc2' for r in selected), 'mixed cohort')
    reviewed = 0
    paired = 0
    for row in rows:
        iid = row['inventory_id']
        md_bytes = blob(FROZEN, row['report_md'])
        json_bytes = blob(FROZEN, row['report_json'])
        require(hashlib.sha256(md_bytes).hexdigest() == row['frozen_md_sha256'], f'{iid}: md hash')
        require(hashlib.sha256(json_bytes).hexdigest() == row['frozen_json_sha256'], f'{iid}: metadata hash')
        md = md_bytes.decode('utf-8')
        lines = md.splitlines()
        claim = row['claim_excerpt_exact']
        line = row['locator']['line']
        require(1 <= line <= len(lines) and md.count(claim) == 1, f'{iid}: excerpt absent/ambiguous')
        require('\n'.join(lines[line-1:]).startswith(claim) or claim in lines[line-1], f'{iid}: line locator')
        heading = next((s.strip() for s in reversed(lines[:line-1]) if s.startswith('#')), lines[0])
        require(heading == row['locator']['heading'], f'{iid}: heading locator')
        meta = json.loads(json_bytes)
        require(row['frozen_subjects'] == meta['subjects'], f'{iid}: exact subject identities')
        lean_subjects = [s for s in meta['subjects'] if s['identity'].get('repository') == 'leanprover/lean4']
        require(all(s['identity'].get('revision') in (None, OLD_LEAN) and s['identity'].get('version') in (None, 'v4.30.0-rc2') for s in lean_subjects), f'{iid}: Lean pin')
        mathlib_subjects = [s for s in meta['subjects'] if s['identity'].get('repository') == 'leanprover-community/mathlib4']
        require(all(s['identity'].get('revision') == OLD_MATHLIB for s in mathlib_subjects), f'{iid}: Mathlib pin')
        require(row['old_lean'] == {'tag':'v4.30.0-rc2','commit':OLD_LEAN}, f'{iid}: old Lean')
        require(row['new_lean'] == {'tag':'v4.34.1','commit':NEW_LEAN}, f'{iid}: new Lean')
        old_ml = {'tag':'v4.30.0-rc2','commit':OLD_MATHLIB} if mathlib_subjects else None
        new_ml = {'tag':'v4.34.1','commit':NEW_MATHLIB} if mathlib_subjects else None
        require(row['old_mathlib'] == old_ml and row['new_mathlib'] == new_ml, f'{iid}: Mathlib pair')
        paired += bool(mathlib_subjects)
        require(row['new_runtime'] == 'unexecuted', f'{iid}: runtime label')
        result = row['comparison']
        require(result == SPECIAL.get(iid, 'unresolved'), f'{iid}: comparison label')
        reviewed += result != 'unresolved'
    require(reviewed == 3 and paired == 3, 'reviewed/paired totals')
    print(f'OK: {len(rows)} frozen excerpts and metadata verified; {reviewed} narrow source deltas; {len(rows)-reviewed} unresolved; {paired} paired Mathlib pins; 161 runtime-unexecuted')

if __name__ == '__main__':
    try:
        main()
    except Exception as exc:
        print(f'FAIL: {exc}', file=sys.stderr)
        raise
