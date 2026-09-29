#!/usr/bin/env python3
"""Reconcile retained J02 raw inventory and probe assertions without rerunning Lean."""
import csv
import json
from collections import defaultdict
from pathlib import Path
import probe

root = Path(__file__).parent
data = json.loads((root / 'results.json').read_text())
rows = defaultdict(list)
for r in csv.DictReader((root / 'inventory.csv').open(newline='')):
    for k in ('logical_bytes', 'allocated_charge_bytes', 'device', 'inode', 'nlink'):
        r[k] = int(r[k])
    case = r.pop('case')
    rows[case].append(r)
assert set(rows) == set(data['cases']) == {
    'cold-1', 'cold-2', 'warm-1', 'warm-2', 'hardlink-1', 'clone-1'}
assert data['filesystem'] == 'APFS'
assert data['lean_sha256'] == 'b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997'
hashes = None
proof_hashes = set()
for case, result in data['cases'].items():
    assert probe.summarize(rows[case]) == result['summary'], case
    assert result['dependency_build']['exit'] == 0
    assert len(result['worker_runs']) == result['workers']
    assert all(x['build']['exit'] == x['fresh_check']['exit'] == 0
               for x in result['worker_runs'])
    assert all(x['build']['stdout'] == x['fresh_check']['stdout'] == ''
               for x in result['worker_runs'])
    if hashes is None:
        hashes = result['dependency_hashes']
    else:
        assert result['dependency_hashes'] == hashes
    names = [r['path'] for r in rows[case]]
    assert len(names) == len(set(names))
    assert all(r['role'] for r in rows[case])
    proof_hashes.update(r['sha256'] for r in rows[case] if r['path'].endswith('Proof.olean'))
    identities = result['worker_dependency_identity']
    assert len(identities) == result['workers']
    if result['mode'] in ('symlink', 'hardlink'):
        assert all(x['dep_source_inode'] == x['shared_source_inode'] for x in identities)
    else:
        assert all(x['dep_source_inode'] != x['shared_source_inode'] for x in identities)
    if result['mode'] == 'symlink':
        assert result['summary']['worker_copied_dependency_payload_bytes'] == 0
    if result['mode'] == 'copy':
        assert result['summary']['worker_copied_dependency_payload_bytes'] == 6189 * result['workers']
assert data['cases']['cold-2']['summary']['regular_payload_bytes'] - data['cases']['warm-2']['summary']['regular_payload_bytes'] == 12378
assert proof_hashes == {'0167443fca001f19617fd0734b02d3f965448348e5a70c02fadc1cf2829d8305'}
assert data['cases']['hardlink-1']['summary']['unique_inode_allocated_charge_bytes'] == data['cases']['warm-1']['summary']['unique_inode_allocated_charge_bytes']
print('PASS: six cases, all entries and summaries, hashes, exits, inode identities, and 1/2-worker accounting')
