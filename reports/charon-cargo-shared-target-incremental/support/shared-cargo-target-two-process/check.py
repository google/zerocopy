#!/usr/bin/env python3
"""Read-only checks for the bounded I080 shared Cargo-target observation."""
import hashlib
import json
from pathlib import Path

here = Path(__file__).resolve().parent
root = here.parent
meta = json.loads((root / 'REPORT.json').read_text())
data = json.loads((here / 'results.json').read_text())
cleanup = json.loads((here / 'cleanup.json').read_text())
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()

assert sha(here / 'probe-observed.py') == meta['subjects'][2]['identity']['observed_probe_sha256']
assert (here / 'probe.py').read_text().replace("SRC = ROOT / 'fixture-origin'",
    "SRC = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/scratch/20260927-reference-experiments/reference-publish/reports/anneal-3730-charon-warm-target-controls-2026-09-29/support/fixture/origin')") == (here / 'probe-observed.py').read_text()
prior = root.parent / 'anneal-3730-charon-warm-target-controls-2026-09-29/support/fixture/origin'
for file in (here / 'fixture-origin').rglob('*'):
    if file.is_file():
        assert sha(file) == sha(prior / file.relative_to(here / 'fixture-origin'))
assert data['preflight']['charon_sha256'] == meta['subjects'][0]['identity']['sha256']
assert data['preflight']['cargo_sha256'] == meta['subjects'][1]['identity']['cargo_sha256']
assert data['preflight']['free_disk_bytes'] > 10 * 1024**3
assert data['preflight']['rss_guard_kib_each'] == 1536 * 1024
assert data['preflight']['disk_guard_kib_total'] == 4 * 1024 * 1024
assert data['preflight']['timeout_seconds'] == 25

runs = {r['label']: r for r in data['runs']}
assert list(runs) == ['complete', 'cancel']
for run in runs.values():
    assert run['guard'] is None and run['samples']
    assert set(run['results']) == {'A', 'B'}
    assert any(s['processes']['A']['members'] and s['processes']['B']['members']
               for s in run['samples'])
    assert max(s['work_kib'] for s in run['samples']) < data['preflight']['disk_guard_kib_total']
    for name in ('A', 'B'):
        assert max(s['processes'][name]['rss_sum_kib'] for s in run['samples']) < data['preflight']['rss_guard_kib_each']
        assert run['results'][name]['pid'] == run['samples'][0]['processes'][name]['pid']
    assert 'Blocking waiting for file lock on build directory' in run['results']['B']['stderr']

complete = runs['complete']
assert not complete['cancelled']
assert [complete['results'][x]['exit'] for x in ('A','B')] == [0,0]
cancel = runs['cancel']
assert cancel['cancelled']
assert [cancel['results'][x]['exit'] for x in ('A','B')] == [-15,0]
assert cancel['results']['A']['dest_sha256'] is None
assert any(s['processes']['A']['exit'] == -15 and s['processes']['B']['members']
           for s in cancel['samples'])
assert cancel['samples'][-1]['at'] > complete['samples'][-1]['at']

for label, name in (('complete','A'),('complete','B'),('cancel','B')):
    r = runs[label]['results'][name]
    artifact = here / 'artifacts' / f'{label}-{name}.llbc'
    assert sha(artifact) == r['dest_sha256']
    assert artifact.stat().st_size == r['dest_bytes']
    llbc = json.loads(artifact.read_text())
    assert llbc['has_errors'] is False
    assert llbc['translated']['crate_name'] == 'warm_probe'

assert cleanup['time_monotonic'] > cancel['samples'][-1]['at']
assert set(cleanup['process_groups']) == {'complete-A','complete-B','cancel-A','cancel-B'}
for label, run in runs.items():
    for name in ('A','B'):
        group = cleanup['process_groups'][f'{label}-{name}']
        assert group['pgid'] == run['results'][name]['pid']
        assert group['members'] == []
    assert cleanup['target_trees'][label]['file_count'] > 0
    assert cleanup['target_trees'][label]['total_file_bytes'] > 0
assert cleanup['cleanup']['work_tree_exists_after_removal'] is False
print('PASS: two private shared-target pairs, overlap, Cargo lock, bounded resources, cancellation/peer completion, LLBCs and cleanup')
