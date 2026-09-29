#!/usr/bin/env python3
"""Offline consistency checker for the retained matched Lake writer run."""
import hashlib
import json
from pathlib import Path

S = Path(__file__).resolve().parent
data = json.loads((S / 'results.json').read_text())
assert data['schema'] == 'i151-matched-lake-writer-isolation-v1'
assert data['subject'] == {
    'lean_revision': '3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc',
    'lake_sha256': '9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb',
    'lean_sha256': 'b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997',
}
cells = {c['cell']: c for c in data['cells']}
assert len(data['cells']) == len(cells) == 4
assert set(cells) == {'shared-kill-A', 'isolated-kill-A', 'shared-kill-B', 'isolated-kill-B'}
for name, c in cells.items():
    shared, victim = name.split('-kill-')
    assert c['preflight']['disk_free_bytes'] > 10 * 1024**3
    assert c['preflight']['memory_free_percent'] >= 35
    assert 0 < c['peak_sampled_rss_kib'] < 4_000_000
    assert c['events'][0] == 'A_entered_7'
    assert c['events'][-3:] == ['B_entered_9', 'killed_' + victim,
                                 'released_' + ('B' if victim == 'A' else 'A')]
    assert ('shared_source_changed_to_9' in c['events']) == (shared == 'shared')
    rec = {r['label']: r for r in c['records']}
    assert rec['killed_' + victim]['exit'] == -9
    assert rec['survivor']['exit'] == 0 and 'Built Dep' in rec['survivor']['stdout']
    assert rec['prime_A']['exit'] == 0
    assert ('prime_B' in rec) == (shared == 'isolated')
    for kind, suffix, digest in [('olean', '.olean', 'artifact_sha256'),
                                 ('trace', '.trace', 'trace_sha256')]:
        p = S / 'artifacts' / (name + suffix)
        assert p.is_file(), (name, kind)
        assert hashlib.sha256(p.read_bytes()).hexdigest() == c[digest]
    assert c['trace_after_no_build_sha256'] == c['trace_sha256']
    if victim == 'A':
        assert c['survivor_root'] == 'B'
        assert rec['no_build']['exit'] == 0
        assert rec['fresh_7']['exit'] != 0 and '\n9\n' in rec['fresh_7']['stdout']
        assert rec['fresh_9']['exit'] == 0 and rec['fresh_9']['stdout'].strip() == '9'
    else:
        assert c['survivor_root'] == 'A'
        assert rec['fresh_7']['exit'] == 0 and rec['fresh_7']['stdout'].strip() == '7'
        assert rec['fresh_9']['exit'] != 0 and '\n7\n' in rec['fresh_9']['stdout']
        assert rec['no_build']['exit'] == (3 if shared == 'shared' else 0)
        if shared == 'shared':
            assert 'out-of-date' in rec['no_build']['stdout']
            assert c['no_build_trace_sha256'] is not None
        else:
            assert c['no_build_trace_sha256'] is None
assert cells['shared-kill-A']['artifact_sha256'] == cells['isolated-kill-A']['artifact_sha256']
assert cells['shared-kill-B']['artifact_sha256'] == cells['isolated-kill-B']['artifact_sha256']
assert cells['shared-kill-A']['artifact_sha256'] != cells['shared-kill-B']['artifact_sha256']
print('OK: four matched gate/kill cells, proof controls, no-build distinction, and saved artifact/trace hashes')
