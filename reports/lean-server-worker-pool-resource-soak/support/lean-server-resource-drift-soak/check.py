#!/usr/bin/env python3
"""Offline checks for the retained direct Lean J10 resource soak."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).parent
data = json.loads((root / 'results.json').read_text())
assert data['lean_sha256'] == 'b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997'
assert data['host_ram_bytes'] == 8 * (1 << 30)
assert data['preflight_free_percent'] >= 35
assert data['dependency_build']['exit'] == 0
assert len(data['segments']) == 3
assert 330 <= data['total_seconds'] < data['guards']['max_seconds']

def check_disk(d):
    rows = d['rows']
    files = [r for r in rows if r['kind'] == 'file']
    assert len(rows) == d['entries']
    assert len(files) == d['files']
    assert len({r['path'] for r in rows}) == len(rows)
    assert sum(r['logical_bytes'] for r in files) == d['payload_bytes']
    assert sum(r['blocks_bytes'] for r in files) == d['blocks_bytes']
    assert len({(r['device'], r['inode']) for r in rows}) == d['distinct_inodes']

all_pids = set()
last_elapsed = -1
last_saved_sha256 = None
for expected, segment in enumerate(data['segments'], 1):
    assert segment['id'] == expected
    assert segment['server_pid'] not in all_pids
    all_pids.add(segment['server_pid'])
    assert segment['initial']['wait']['result'] == {}
    assert '⊢ depValue = 7' in str(segment['initial']['goal']['result'])
    if last_saved_sha256 is not None:
        assert segment['initial']['disk_source_sha256'] == last_saved_sha256
    assert len(segment['rounds']) >= 18
    assert [r['version'] for r in segment['rounds']] == list(range(2, 2 + len(segment['rounds'])))
    for r in segment['rounds']:
        assert r['wait']['result'] == {}
        assert '⊢ depValue = 7' in str(r['goal']['result'])
    assert segment['final_buffer_sha256'] == segment['saved_disk_sha256']
    last_saved_sha256 = segment['saved_disk_sha256']
    assert segment['shutdown']['exit'] == 0 and not segment['shutdown']['forced']
    assert segment['tree_after_shutdown']['processes'] == 0
    assert 110 <= segment['elapsed_seconds'] < 125
    assert len(segment['samples']) >= 8
    assert segment['samples'][0]['label'] == 'segment-start'
    assert segment['samples'][-1]['label'] == 'segment-end'
    for sample in segment['samples']:
        assert sample['elapsed_seconds'] > last_elapsed
        last_elapsed = sample['elapsed_seconds']
        tree = sample['tree']
        assert 1 <= tree['processes'] <= data['guards']['max_tree_processes']
        assert tree['rss_sum_bytes'] <= data['guards']['max_rss_or_footprint_bytes']
        assert sample['free_percent'] >= data['guards']['min_free_percent']
        check_disk(sample['disk'])
        assert next(r['sha256'] for r in sample['disk']['rows'] if r['path'] == 'Dep.olean') == data['dep_olean_sha256']
        assert sample['disk']['blocks_bytes'] <= data['guards']['max_disk_bytes']
        fp = sample['footprint']
        assert fp and fp['exit'] == 0 and fp['summary_bytes'] is not None
        assert fp['summary_bytes'] <= data['guards']['max_rss_or_footprint_bytes']
        assert len(fp['per_pid_phys_footprint_bytes']) == tree['processes']
        assert abs(fp['summary_bytes'] - sum(fp['per_pid_phys_footprint_bytes'])) < 10 * (1 << 20)
    check_disk(segment['disk_after_shutdown'])
check_disk(data['initial_disk'])
check_disk(data['final_disk'])
assert data['dep_olean_sha256'] == next(r['sha256'] for r in data['final_disk']['rows'] if r['path'] == 'Dep.olean')
assert data['segments'][-1]['saved_disk_sha256'] == next(r['sha256'] for r in data['final_disk']['rows'] if r['path'] == 'Proof.lean')
print('PASS: three timed segments, all goals/edits, periodic footprint/tree/disk ledgers, clean restarts')
