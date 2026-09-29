#!/usr/bin/env python3
"""Check retained I023 component outputs and experiment-side freshness policies."""
import hashlib,json
from pathlib import Path
here=Path(__file__).resolve().parent;work=here/'work'
r=json.loads((here/'results.json').read_text())
assert r['schema']==1 and len(r['commands'])==11
assert r['policy_origin'].startswith('experiment-side')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for path,digest in r['tools'].items():assert sha(path)==digest
for kind,folder in [('source_snapshots','snapshots'),('proof_snapshots','proof-snapshots')]:
    for name,meta in r[kind].items():
        p=work/folder/name
        assert p.stat().st_size==meta['bytes'] and sha(p)==meta['sha256']
a=r['baseline'];b=r['syntax_failure'];c=r['unsupported_extraction']
assert a['freshness']=='current' and a['current_verified'] and a['proof']['lean_rc']==0
assert a['rust_sha256']==sha(work/'snapshots/A-good.rs')
assert a['llbc_sha256']==sha(work/'current.llbc')==b['retained_llbc_sha256']
for name,meta in a['generated'].items():assert sha(work/'generated-A'/name)==meta['sha256']
assert b['charon_rc']!=0 and b['llbc_path_still_exists']
assert b['rust_sha256']==sha(work/'snapshots/B-syntax.rs')!=a['rust_sha256']
assert c['rust_sha256']==sha(work/'snapshots/C-unsupported.rs')!=a['rust_sha256']
assert c['aeneas_rc']!=0 and c['candidate_llbc_sha256']==sha(work/'candidate.llbc')
assert c['partial_contains_sorry'] and 'sorry' in (work/'generated-C-partial/Funs.lean').read_text()
assert 'wrapping_add x 2#u32' in (work/'generated-C-partial/Funs.lean').read_text()
for case,version in ((b,'v2'),(c,'v3')):
    stop=case['policies']['stop'];old=case['policies']['last_good']
    assert stop['mode']=='stop-interaction' and not stop['query_performed'] and not stop['current_verified']
    assert old['mode']=='explicit-last-good' and old['query_performed']
    assert old['freshness']=='stale' and not old['current_verified']
    assert old['model_id']==a['model_id'] and old['model_rust_sha256']==a['rust_sha256']
    assert old['requested_rust_sha256']==case['rust_sha256']!=old['model_rust_sha256']
    assert old['query']['proof_version']==version and old['query']['lean_rc']==0
    assert old['query']['proof_sha256']==sha(work/'proof-snapshots'/f'{version}.lean')
    assert case['policies']['naive_exit_zero_would_mislabel_current']
assert [x['rc'] for x in r['commands'] if x['label'] in ('B:charon-syntax-error','C:aeneas-unsupported')]==[2,1]
print('I023 retained-result checks passed')
