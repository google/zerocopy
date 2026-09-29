#!/usr/bin/env python3
"""Verify retained J05 matrix, disk ledger, admission, goals, memory, cleanup."""
import json
from pathlib import Path

x = json.loads((Path(__file__).parent / 'results.json').read_text())
assert x['lean_sha256'] == 'b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997'
assert x['host_ram_bytes'] == 8 * (1 << 30)
assert x['cap_bytes'] == int(4.5 * (1 << 30))
assert not x['skipped']
assert set(x['cells']) == {f'{mode}-{n}' for mode in ('cold', 'warm') for n in (1, 2, 4, 8)}

def disk_reconcile(d):
    rows = d['rows']
    files = [r for r in rows if r['kind'] == 'file']
    assert len(rows) == d['entries']
    assert len(files) == d['files']
    assert len({r['path'] for r in rows}) == len(rows)
    assert sum(r['logical_bytes'] for r in files) == d['payload_bytes']
    assert sum(r['blocks_bytes'] for r in files) == d['allocated_charge_bytes']
    assert len({(r['device'], r['inode']) for r in rows}) == d['distinct_inodes']

for n in (1, 2, 4, 8):
    admission = x['admissions'][str(n)]
    assert admission['allowed']
    assert admission['estimated_bytes'] <= x['cap_bytes']
    assert admission['estimated_bytes'] + admission['reserve_bytes'] <= admission['free_estimated_bytes']
    for mode in ('cold', 'warm'):
        c = x['cells'][f'{mode}-{n}']
        assert c['mode'] == mode and c['workers'] == n
        assert c['dep_build']['exit'] == 0
        assert c['dep_build']['seconds'] > 0
        assert len(c['worker_preparation']) == n
        assert all(p['method'] == ('local-source-build' if mode == 'cold' else 'symlink-prebuilt')
                   and p['seconds'] >= 0 and
                   (p['compile']['exit'] == 0 if mode == 'cold' else p['compile'] is None)
                   for p in c['worker_preparation'])
        assert len(c['wait1']) == len(c['goal1']) == len(c['wait2']) == len(c['goal2']) == n
        assert all(v.get('result') == {} for v in c['wait1'] + c['wait2'])
        assert all('⊢ depValue = 7' in str(v.get('result')) for v in c['goal1'])
        assert all(v.get('result') is None for v in c['goal2'])
        assert len(c['cleanup']) == n
        assert all(v['exit'] == 0 and not v['forced'] for v in c['cleanup'])
        for phase in ('memory_open', 'memory_edited'):
            m = c[phase]
            assert m['footprint']['exit'] == 0
            assert len(m['pids']) == len(m['rss_rows']) == len(m['per_pid_phys_footprint_bytes']) == 2 * n
            assert m['parsed_footprint_bytes'] <= x['cap_bytes']
            assert m['summed_phys_footprint_bytes'] == sum(m['per_pid_phys_footprint_bytes'])
            assert abs(m['parsed_footprint_bytes'] - m['summed_phys_footprint_bytes']) < 15 * (1 << 20)
        for phase in ('disk_before', 'disk_live', 'disk_after', 'disk_reclaimed'):
            disk_reconcile(c[phase])
        live = c['disk_live']
        assert live['files'] == (5 + 9 * n if mode == 'cold' else 5 + 4 * n)
        assert live['payload_bytes'] == (6189 + 6470 * n if mode == 'cold' else 6189 + 281 * n)
        assert live['distinct_inodes'] == (6 + 11 * n if mode == 'cold' else 6 + 6 * n)
        assert live['payload_bytes'] == c['disk_after']['payload_bytes']
        assert c['disk_reclaimed']['files'] == 5
        assert c['disk_reclaimed']['payload_bytes'] == 6189
        assert c['disk_reclaimed']['distinct_inodes'] == 6
        assert all(not r['path'].startswith('worker-') for r in c['disk_reclaimed']['rows'])
print('PASS: 8 cells, 1/2/4/8 admissions, goals, physical-memory samples, disk/inode attribution, worker cleanup')
