#!/usr/bin/env python3
"""Validate retained module-move bytes and fresh Lean outcomes offline."""
import hashlib
import json
from pathlib import Path

s=Path(__file__).resolve().parent
r=json.loads((s/'raw-results.json').read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert r['schema']=='anneal-aeneas-namespace-move-v1'
assert set(r['cases'])=={'base','moved'}
for name,v in r['cases'].items():
    d=s/'work'/name
    assert sha(d/'fixture.rs')==v['source_sha256']
    assert sha(d/'fixture.llbc')==v['llbc_sha256']
    for f,m in v['generated'].items():
        p=d/'generated'/f
        assert p.stat().st_size==m['size'] and sha(p)==m['sha256']
    assert sha(d/'Proof.lean')==v['proof_sha256']
    assert len(v['commands'])==6 and all(c['exit']==0 for c in v['commands'])
    assert 'sorryAx' not in v['commands'][-1]['stdout']
    assert "'caller' depends on axioms:" in v['commands'][-1]['stdout']
    assert "'helper' depends on axioms:" in v['commands'][-1]['stdout']
base=(s/'work/base/generated/Funs.lean').read_text()
moved=(s/'work/moved/generated/Funs.lean').read_text()
assert 'def core.use_step ' in base and 'def moved.core.use_step ' in moved
assert 'def caller ' in base and 'def caller ' in moved
assert r['cases']['base']['generated']['Funs.lean']['sha256']!=r['cases']['moved']['generated']['Funs.lean']['sha256']
neg=r['old_name_negative']
assert neg['exit']!=0 and 'Unknown identifier `move_probe.core.use_step`' in neg['stdout']
assert '#check move_probe.core.use_step' in (s/'work/moved/OldProof.lean').read_text()
print('PASS: pinned module-move output, two fresh proofs, and old-name rejection')
