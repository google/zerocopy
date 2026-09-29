#!/usr/bin/env python3
"""Check the retained one-worker full-chain inventory against original evidence."""
import hashlib
import json
import os
from pathlib import Path

here=Path(__file__).resolve().parent
reports=here.parents[1]
source=reports/'anneal-3730-full-lake-server-chain-2026-09-29'/'support'
d=json.loads((here/'results.json').read_text())
assert d['source_results_sha256']==hashlib.sha256((source/'results.json').read_bytes()).hexdigest()
root=source/'work'/'one'/'u0'
for row in d['rows']:
    path=root/row['path']
    stat=path.lstat()
    assert stat.st_size==row['logical_bytes']
    assert stat.st_blocks*512==row['allocated_bytes']
    if row['mode']=='symlink':assert path.is_symlink() and os.readlink(path)==row['link_target']
    else:assert path.is_file() and hashlib.sha256(path.read_bytes()).hexdigest()==row['sha256']
assert d['totals']=={'allocated_bytes':4698112,'files':54,'logical_bytes':4524103,'symlinks':1,'unique_inodes':55}
assert sorted(x['logical_bytes_each'] for x in d['duplicate_content_groups'])==[20,542,1120]
assert sum(x['extra_logical_bytes'] for x in d['duplicate_content_groups'])==3364
t=d['timing']
assert [t['one_worker_wall_seconds'],t['direct_rust_through_lean_seconds'],t['lake_build_seconds'],t['fresh_batch_seconds']]==[54.754,17.068,12.045,7.256]
assert t['unattributed_or_overlapping_wall_seconds']==18.385
print('I113/I118 retained one-chain byte and timing inventory passed')
