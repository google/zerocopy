#!/usr/bin/env python3
"""Offline checks of the retained direct Lean macro-position result."""
import json
from pathlib import Path

data = json.loads((Path(__file__).resolve().parent / 'results.json').read_text())
rows = data['cases']
assert [r['label'] for r in rows] == ['unsolved-v1', 'solved-v2', 'unsolved-v3']
assert [r['version'] for r in rows] == [1, 2, 3]
assert [r['fresh_batch']['rc'] == 0 for r in rows] == [False, True, False]
assert all(r['wait'].get('result') == {} for r in rows)
assert all(len(r['positions']) == 8 for r in rows)
assert all('unsolved goals' in r['fresh_batch']['stdout'] for r in (rows[0], rows[2]))
for r in (rows[0], rows[2]):
    start = next(p['reply']['result'] for p in r['positions'] if p['line'] == 3 and p['character'] == 0)
    assert 'h : True' in str(start) and '⊢ True' in str(start)
    assert r['diagnostics'] and r['diagnostics']['uri']
solved = next(p['reply']['result'] for p in rows[1]['positions'] if p['line'] == 3 and p['character'] == 8)
assert not solved.get('goals')
print('I043 macro tactic retained result checks passed')
