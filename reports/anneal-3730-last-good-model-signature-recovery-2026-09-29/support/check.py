#!/usr/bin/env python3
"""Validate retained R25 CLI outputs and experiment-side model routing."""
import hashlib,json
from pathlib import Path
here=Path(__file__).resolve().parent;work=here/'work'
r=json.loads((here/'results.json').read_text());assert r['schema']==1 and len(r['commands'])==16
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for path,digest in r['tools'].items():assert sha(path)==digest
for k,folder in [('source_snapshots','source-snapshots'),('proof_snapshots','proof-snapshots')]:
    for name,m in r[k].items():
        p=work/folder/name
        assert p.stat().st_size==m['bytes'] and sha(p)==m['sha256']
a=r['A'];f=r['failure'];b=r['B']
assert a['rust_sha256']==sha(work/'source-snapshots/A.rs')
assert f['rust_sha256']==sha(work/'source-snapshots/failed.rs')
assert b['rust_sha256']==sha(work/'source-snapshots/B.rs')==sha(work/'source.rs')
assert len({a['rust_sha256'],f['rust_sha256'],b['rust_sha256']})==3
assert a['llbc_sha256']==f['retained_llbc_sha256']==sha(work/'current.llbc')
assert b['llbc_sha256']==sha(work/'recovery.llbc') and b['llbc_sha256']!=a['llbc_sha256']
assert a['signature']['input']==a['signature']['output']=='Std.U32'
assert b['signature']['input']==b['signature']['output']=='Std.U64'
assert a['signature']['line'] in (work/'generated-A/Funs.lean').read_text()
assert b['signature']['line'] in (work/'generated-B/Funs.lean').read_text()
for case,path in ((a,work/'generated-A'),(b,work/'generated-B')):
    for name,m in case['generated'].items():assert sha(path/name)==m['sha256']
assert a['model_id']!=b['model_id']
assert a['initial_proof']['rc']==0 and f['charon_rc']!=0
p=f['policies'];assert not p['stop']['query_performed'] and not p['stop']['current_verified']
q=p['last_good'];assert q['query_performed'] and q['freshness']=='stale' and not q['current_verified']
assert q['requested_rust_sha256']==f['rust_sha256'] and q['model_rust_sha256']==a['rust_sha256']
assert q['model_id']==a['model_id'] and q['query']['rc']==0
assert b['old_assumptions']['rc']!=0 and 'U32' in b['old_assumptions']['stdout'] and 'U64' in b['old_assumptions']['stdout']
assert b['adapted']['rc']==0 and b['freshness']=='current' and b['current_model_proof_accepted']
assert b['late_A']['query']['rc']==0 and not b['late_A']['current_verified']
assert b['late_A']['actual_model_id']==a['model_id'] and b['late_A']['current_model_id']==b['model_id']
events=[e['name'] for e in r['events']]
assert events==['publish-A-current','current-rust-failed','old-model-query-provisional',
               'publish-B-current-stop-provisional','B-current-proof-accepted',
               'late-A-result-rejected-as-current']
assert b['provisional_stopped_at']==events[3]
print('R25 retained-result checks passed')
