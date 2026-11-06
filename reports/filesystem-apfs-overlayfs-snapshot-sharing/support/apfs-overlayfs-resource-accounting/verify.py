#!/usr/bin/env python3
"""Validate retained APFS/overlayfs file and counter observations."""
import hashlib,json
from pathlib import Path

HERE=Path(__file__).resolve().parent
x=json.loads((HERE/'results.json').read_text())
for name,h in x['fixture_sha256'].items():
 assert hashlib.sha256((HERE/'fixture'/name).read_bytes()).hexdigest()==h
assert x['fixture_blob_count']==8 and x['fixture_blob_bytes']==262144
a=x['host']['apfs'];o=x['container']['overlayfs']
assert x['host']['diskutil_apfs'].lower()=='apfs' and o['filesystem']=='overlayfs'
assert x['container']['image'].startswith('sha256:224a1869083a311ef3f13648a154ba79832fbef6364d31493642ca03082da254')
base=a['base']['logical_bytes'];assert base==o['base']['logical_bytes']==2147019
assert a['base']['file_count']==o['base']['file_count']==11
for d in (a,o):
 assert d['empty']['logical_bytes']==0
 assert d['full_copy']['logical_bytes']==2*base
 assert d['clone_copy']['logical_bytes']==3*base
 assert d['hardlink']['logical_bytes']==3*base+x['fixture_blob_bytes']*0+4552
 assert d['clone_mutated']['logical_bytes']==d['hardlink']['logical_bytes']
 assert d['clone_copy']['allocated_file_bytes']>d['full_copy']['allocated_file_bytes']
 files={f['path']:f for f in d['hardlink']['files']}
 assert files['base/Dep.olean']['inode']==files['read_only_link/Dep.olean']['inode']
 assert files['base/Dep.olean']['links']==files['read_only_link/Dep.olean']['links']==2
 assert files['base/cache/unit-00.bin']['inode']!=files['clone/cache/unit-00.bin']['inode']
assert all(isinstance(a[phase]['volume_available_bytes'],int) and a[phase]['volume_available_bytes']>0
           for phase in ('empty','base','full_copy','clone_copy','hardlink','clone_mutated'))
assert a['baseline_blob_sha256']==next(f['sha256'] for f in a['hardlink']['files'] if f['path']=='base/cache/unit-00.bin')
assert a['baseline_blob_sha256']==next(f['sha256'] for f in a['clone_mutated']['files'] if f['path']=='base/cache/unit-00.bin')
assert a['baseline_blob_sha256']!=next(f['sha256'] for f in a['clone_mutated']['files'] if f['path']=='clone/cache/unit-00.bin')
assert o['reflink_attempt']['exit']==0
assert o['clone_copy']['docker_size_rw_bytes']-o['full_copy']['docker_size_rw_bytes']>2_000_000
assert o['hardlink']['docker_size_rw_bytes']==o['clone_copy']['docker_size_rw_bytes']
assert o['clone_mutated']['docker_size_rw_bytes']==o['hardlink']['docker_size_rw_bytes']
assert o['mutation']['kind']=='reflink'
before=[z.split()[0] for z in o['mutation']['before_sha256sum'].splitlines()]
after=[z.split()[0] for z in o['mutation']['after_sha256sum'].splitlines()]
assert before[0]==before[1]==after[0]!=after[1]
runs=[r for r in x['commands'] if 'run' in r['argv'][:2] and '--pull=never' in r['argv']]
assert len(runs)==1 and '--network=none' in runs[0]['argv'] and '--memory=512m' in runs[0]['argv']
assert x['commands'][-1]['argv'][1:3]==['rm','-f'] and x['commands'][-1]['exit']==0
print('PASS: APFS and cached overlayfs counters, clone/hardlink identity, mutation isolation and cleanup')
