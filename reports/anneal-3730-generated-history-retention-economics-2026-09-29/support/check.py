#!/usr/bin/env python3
"""Validate retained Aeneas generation bytes, historical goals, and tier sums offline."""
import hashlib,json
from pathlib import Path

s=Path(__file__).resolve().parent
r=json.loads((s/'results.json').read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert r['schema']=='anneal-generated-history-retention-v1'
assert list(r['generations'])==['g0-base','g1-body','g2-signature','g3-move']
assert list(r['retention'])==['1','2','4']
for label,g in r['generations'].items():
 root=s/'work'/label
 for name,meta in g['files'].items():
  p=root/name
  assert p.stat().st_size==meta['bytes'] and p.stat().st_blocks*512==meta['allocated'] and sha(p)==meta['sha256']
 assert g['rust_source_bytes']==g['files']['provenance/fixture.rs']['bytes']
 assert g['llbc_bytes']==g['files']['provenance/fixture.llbc']['bytes']
 assert g['source_bytes']==g['rust_source_bytes']+g['llbc_bytes']
 assert g['generated_bytes']==sum(v['bytes'] for k,v in g['files'].items() if k.endswith('.lean'))
 assert g['compiled_bytes']==sum(v['bytes'] for k,v in g['files'].items() if k.endswith('.olean'))
for n,t in r['retention'].items():
 labels=t['generations'];assert len(labels)==int(n)
 assert t['rust_only_bytes']==sum(r['generations'][x]['rust_source_bytes'] for x in labels)
 assert t['source_bytes']==sum(r['generations'][x]['source_bytes'] for x in labels)
 assert t['source_plus_generated_bytes']==sum(r['generations'][x]['source_bytes']+r['generations'][x]['generated_bytes'] for x in labels)
 assert t['source_generated_compiled_bytes']==sum(r['generations'][x]['source_bytes']+r['generations'][x]['generated_bytes']+r['generations'][x]['compiled_bytes'] for x in labels)
assert len(r['sessions'])==7
goals={
 'g0-base':'trait_reuse.core.use_step 1#u32 = Aeneas.Std.Result.ok 2#u32',
 'g1-body':'trait_reuse.core.use_step 1#u32 = Aeneas.Std.Result.ok 3#u32',
 'g2-signature':'trait_reuse.core.use_step 1#u32 = Aeneas.Std.Result.ok 2#u32',
 'g3-move':'move_probe.moved.core.use_step 1#u32 = Aeneas.Std.Result.ok 2#u32',
}
for x in r['sessions']:
 label=x['label'].replace('restart-','').replace('recomputed-','')
 assert x['server_exit']==0 and x['sampled_tree_rss_kib']<3300000
 assert 0<=x['startup_seconds']<=x['ready_seconds']<=x['goal_seconds']
 assert x['wait'].get('result')=={}
 assert x['goal']['result']['goals']==['⊢ '+goals[label]]
 assert x['source_sha256']==sha(s/'work'/('recompute-g0-base' if x['label']=='recomputed-g0-base' else label)/'Historical.lean')
proofs=[c for c in r['commands'] if c['label'].endswith(':fresh-proof')]
assert len(proofs)==4 and all(c['exit']==0 and 'sorryAx' not in c['stdout'] for c in proofs)
recomp=[c for c in r['commands'] if c['label'].startswith('recompute:')]
assert len(recomp)==4 and all(c['exit']==0 for c in recomp)
for mod,h in r['recompute']['generated_olean_sha256'].items():assert sha(s/'work/recompute-g0-base'/(mod+'.olean'))==h
assert r['recompute']['compile_seconds']>0
assert r['peak_sampled_rss_kib']<3300000
print('PASS: four real generated generations, 1/2/4 tier bytes, seven historical sessions and old recompilation')
