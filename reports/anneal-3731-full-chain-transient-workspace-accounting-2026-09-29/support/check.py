#!/usr/bin/env python3
"""Offline arithmetic and outcome checks for the preserved one-chain snapshots."""
import gzip, json
from pathlib import Path
x=json.loads(gzip.decompress((Path(__file__).resolve().parent/'observations.json.gz').read_bytes()))
assert x['preflight']['memory_free_percent']>=25
assert x['preflight']['disk_free_bytes']>=10*1024**3
assert x['runtime']['abort'] is None and x['runtime']['error'] is None
assert x['runtime']['snapshot_failures']==[] and x['runtime']['cleanup_processes']==[]
assert x['runtime']['minimum_free_percent']>=25
assert len(x['boundaries'])==24 and len(x['samples'])>0
assert len(x['outcome']['direct_exit'])==6 and all(q==0 for q in x['outcome']['direct_exit'])
assert x['outcome']['lake_exit']==x['outcome']['fresh_exit']==0
assert len(x['outcome']['live_goal'])==1 and 'pipeline_workload.inc 0#u32' in x['outcome']['live_goal'][0]
assert x['outcome']['live_wait']=={}
for b in x['boundaries']:
    assert b['errors']==[]
    f=b['families']; t=b['totals']; rows=b['rows']
    assert t['files']==sum(v['files'] for v in f.values())
    assert t['symlinks']==sum(v['symlinks'] for v in f.values())
    assert t['logical_bytes']==sum(v['logical_bytes'] for v in f.values())
    assert t['allocated_bytes']==sum(v['allocated_bytes'] for v in f.values())
    assert len(rows)==t['files']+t['symlinks']
    assert sum(v['size'] for v in rows.values() if v['kind']=='file')==t['logical_bytes']
    assert sum(v['allocated'] for v in rows.values())==t['allocated_bytes']
for s in x['samples']:
    assert s['errors']==[] and s['disk_free_bytes']>=10*1024**3
    assert s['total']['allocated_bytes']==sum(v['allocated_bytes'] for v in s['families'].values())
def stage(label,phase='after'):
    rows=[b for b in x['boundaries'] if b['label']==label and b['phase']==phase]
    assert len(rows)==1,(label,phase,len(rows))
    return rows[0]
charon=stage('u0:charon'); lake=stage('u0:lake-build'); pre=stage('pre-target-cleanup'); post=stage('target-cleanup')
assert charon['families']['rust_target']=={'files':12,'symlinks':0,'logical_bytes':5838,'allocated_bytes':28672}
assert lake['families']['lake_build']['allocated_bytes']==4567040
assert pre['totals']['allocated_bytes']==4825088
assert post['totals']['allocated_bytes']==4796416
lost=set(pre['rows'])-set(post['rows'])
assert len(lost)==12 and all(p.startswith('work/one/u0/target/') for p in lost)
assert sum(pre['rows'][p]['allocated'] for p in lost)==28672
assert max([b['totals']['allocated_bytes'] for b in x['boundaries']]+[s['total']['allocated_bytes'] for s in x['samples']])==4825088
for name,before in x['outside_before'].items():
    after=x['outside_after'][name]
    assert before['du_exit']==after['du_exit']==0
    assert before['du_kib']==after['du_kib']
    assert before['root_mtime_ns']==after['root_mtime_ns']
baseline=json.loads((Path(__file__).resolve().parent/'baseline-retained.json').read_text())['rows']
current={p.removeprefix('work/one/u0/'):v for p,v in post['rows'].items() if p.startswith('work/one/u0/')}
assert set(baseline)==set(current) and len(current)==55
assert sum(v['size'] for v in baseline.values())==4524103
assert sum(v['size'] for v in current.values())==4520848
assert sum(v['allocated'] for v in baseline.values())==4698112
assert sum(v['allocated'] for v in current.values())==4681728
changed={p for p in current if baseline[p]['size']!=current[p]['size'] or baseline[p]['allocated']!=current[p]['allocated']}
assert changed=={'current.llbc','lake/.lake/build/ir/Current.setup.json',
    'lake/.lake/build/ir/Current/Funs.setup.json','lake/.lake/build/ir/Proof.setup.json',
    'lake/.lake/build/lib/lean/Current.trace','lake/.lake/build/lib/lean/Current/Funs.trace',
    'lake/.lake/build/lib/lean/Current/Types.trace','lake/.lake/build/lib/lean/Proof.trace'}
print('PASS: one admitted full chain, stage sums, retained and deleted file accounting, sampled bound, selected outside-root net deltas')
