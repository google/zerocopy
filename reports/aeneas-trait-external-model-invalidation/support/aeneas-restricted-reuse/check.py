#!/usr/bin/env python3
"""Validate retained E11 oracle-guided reuse results without invoking toolchains."""
import hashlib
import json
from pathlib import Path

here=Path(__file__).parent
r=json.loads((here/'results.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
expected={'Fixture/Types':[],'Fixture/Funs':['Fixture/Types'],'Fixture':['Fixture/Funs']}
assert len(r['commands'])==28
for case in ['base','body','signature']:
    v=r['variants'][case]
    assert sha(here/f'source-{case}.rs')==v['rust_sha256']
    assert sha(here/'inputs'/case/'fixture.rs')==v['rust_sha256']
    assert sha(here/'inputs'/case/'fixture.llbc')==v['llbc_sha256']
    for name,meta in v['generated'].items():
        p=here/'outputs'/case/name
        assert sha(p)==meta['sha256'] and p.stat().st_size==meta['bytes']
    assert r['generated_import_graph'][case]==expected
    assert v['fresh_lean']['compile']['exits']==[0,0,0]
    assert v['fresh_lean']['proof']['exit']==0
    assert v['fresh_lean']['proof']['stdout'].count("'caller'")==1
    assert 'sorryAx' not in v['fresh_lean']['proof']['stdout']
assert r['policy']['body']['artifact_reuse']=={'Fixture/Types':True,'Fixture/Funs':False,'Fixture':False}
assert r['policy']['signature']['artifact_reuse']=={'Fixture/Types':False,'Fixture/Funs':False,'Fixture':False}
for case in ['body','signature']:
    h=r['policy'][case]['hybrid']
    assert h['proof']['exit']==0 and 'sorryAx' not in h['proof']['stdout']
    assert all(x==0 for x in h['compile']['exits'])
assert r['policy']['body']['hybrid']['copied_olean']==['Fixture/Types']
assert r['policy']['signature']['hybrid']['copied_olean']==[]
assert r['controls']['stale_funs']['compile']['exits']==[0]
assert r['controls']['stale_funs']['proof']['exit']!=0
assert r['controls']['stale_types']['compile']['exits'][0]!=0
print('PASS: three whole-crate variants, dependency graph, hybrid policy and stale controls')
