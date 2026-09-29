#!/usr/bin/env python3
"""Validate E10 retained component results without rerunning Lean/Aeneas."""
import hashlib,json
from pathlib import Path
here=Path(__file__).resolve().parent;work=here/'work'
r=json.loads((here/'results.json').read_text());assert r['schema']==1 and len(r['commands'])==24
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for path,digest in r['tools'].items():assert sha(path)==digest
assert sha(work/'source.rs')==r['source_sha256'] and sha(work/'source.llbc')==r['llbc_sha256']
assert r['generated']==r['regenerated']
for name,m in r['generated'].items():
    assert sha(work/'generated'/name)==m['sha256']
    assert sha(work/'generated-again'/name)==m['sha256']
v=r['variants'];assert set(v)=={'concrete','wrong','axiom','missing'}
assert len({x['model_sha256'] for x in v.values()})==4
for kind,x in v.items():
    d=work/'variants'/kind
    assert sha(d/'Source/FunsExternal.lean')==x['model_sha256']
    assert x['generated_sha256']['Source/Funs.lean']==r['generated']['Funs.lean']['sha256']
    assert x['generated_sha256']['Source/Types.lean']==r['generated']['Types.lean']['sha256']
    assert x['generated_sha256']['Source.lean']==r['generated']['Source.lean']['sha256']
    for name,digest in x['olean'].items():assert sha(d/name)==digest
assert v['concrete']['compile_rcs']==[0,0,0,0] and v['concrete']['check_rc']==0
assert 'does not depend on any axioms' in v['concrete']['check_stdout']
assert v['wrong']['compile_rcs']==[0,0,0,0] and v['wrong']['check_rc']!=0
assert v['axiom']['compile_rcs']==[0,0,0,0] and v['axiom']['check_rc']!=0
assert 'depends on axioms: [external_double]' in v['axiom']['check_stdout']
assert v['missing']['compile_rcs'][-1]!=0 and v['missing']['check_rc'] is None
assert v['concrete']['olean']['Source/Funs.olean']!=v['wrong']['olean']['Source/Funs.olean']
c=r['cache_negative_control']
assert c['candidate_external_model_sha256']==v['wrong']['model_sha256']
assert c['loaded_external_olean_sha256']==v['concrete']['olean']['Source/FunsExternal.olean']
assert c['wrong_fresh_check_rc']!=0 and c['stale_reuse_check_rc']==0
assert c['generated_only_acceptance_invalid']
l=r['live_workers'];assert l['old_pid']!=l['new_pid']
assert l['external_model_sha256']==v['wrong']['model_sha256']
assert l['before_olean']!=l['after_olean']
for tree,pid in [(l['old_tree_initial'],l['old_pid']),
                 (l['old_tree_after_rebuild'],l['old_pid']),
                 (l['new_tree'],l['new_pid'])]:
    assert len(tree)>=2 and any(x['pid']==pid for x in tree)
    assert any(x['ppid']==pid for x in tree)
old_children={x['pid'] for x in l['old_tree_initial'] if x['ppid']==l['old_pid']}
assert old_children=={x['pid'] for x in l['old_tree_after_rebuild'] if x['ppid']==l['old_pid']}
assert old_children.isdisjoint({x['pid'] for x in l['new_tree']})
assert all(x['severity']!=1 for x in l['old_initial_diagnostics']['diagnostics'])
assert all(x['severity']!=1 for x in l['old_after_diagnostics']['diagnostics'])
assert any(x['severity']==1 for x in l['new_diagnostics']['diagnostics'])
assert 'does not depend on any axioms' in str(l['old_after_diagnostics'])
assert 'depends on axioms' in str(l['new_diagnostics'])
assert r['external_kind'].startswith('separate Lean source')
print('E10 retained-result checks passed')
