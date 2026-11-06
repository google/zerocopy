#!/usr/bin/env python3
"""Offline invariants for the retained eight-proof live stale-oracle fanout."""
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent
d=json.loads((ROOT/'results.json').read_text())
sha=lambda x:hashlib.sha256(x).hexdigest()
assert d['schema']==1
assert '4.30.0-rc2' in d['tools']['lean_version'] and '4.30.0-rc2' in d['tools']['lake_version']
assert d['tools']['lean_sha256']=='b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997'
assert d['tools']['lake_sha256']=='9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb'
events=d['events']
assert [e['seq'] for e in events]==list(range(len(events)))
assert len(d['waves'])==4 and [w['mode'] for w in d['waves']]==['direct','direct','lake','lake']
assert [w['proofs'] for w in d['waves']]==[[0,1],[2,3],[4,5],[6,7]]
assert len(d['batch'])==16
assert sorted((r['stage'],r['proof']) for r in d['batch'])==sorted((stage,i) for stage in ('base','edited') for i in range(8))
for name,expected in d['sources'].items():
    assert sha((ROOT/'work'/name).read_bytes())==expected
assert (ROOT/'work/Model.lean').read_text()=='def model : Nat := 7\n'
assert (ROOT/'work/Helper.lean').read_text()=='import Model\ndef helper : Nat := model\n'
for i in range(8):
    source=(ROOT/'work'/f'Proof{i}.lean').read_text()
    assert source==f'import Helper\n#eval helper\ntheorem proof_{i} : helper = 8 := by\n  rfl\n'

for stage,rc,value in [('base',0,'8'),('edited',1,'7')]:
    for row in (x for x in d['batch'] if x['stage']==stage):
        assert row['rc']==rc and not row['stderr']
        messages=[json.loads(line) for line in row['stdout'].splitlines() if line.strip()]
        assert any(m['data']==value and m['severity']=='information' for m in messages)
        if rc:
            assert any('Tactic `rfl` failed' in m['data'] and m['severity']=='error' for m in messages)
        else:assert not any(m['severity']=='error' for m in messages)

base_hash=d['initial_artifacts']
assert base_hash['Model']!=d['waves'][0]['edited_artifacts']['Model']
assert base_hash['Helper']!=d['waves'][0]['edited_artifacts']['Helper']
edited_hash=d['waves'][0]['edited_artifacts']
assert d['final_artifacts']==edited_hash
for value,expected in [('8',base_hash),('7',edited_hash)]:
    for name,digest in expected.items():
        assert sha((ROOT/'artifacts'/value/(name+'.olean')).read_bytes())==digest
for name,digest in edited_hash.items():
    assert sha((ROOT/'work/.lake/build/lib/lean'/(name+'.olean')).read_bytes())==digest

def diags(label):
    return [x['message']['params'] for x in events if x['kind']=='server' and x.get('label')==label
        and x['message'].get('method')=='textDocument/publishDiagnostics']
for j,w in enumerate(d['waves']):
    assert w['index']==j and w['base_artifacts']==base_hash and w['edited_artifacts']==edited_hash
    proof_keys={str(i) for i in w['proofs']}
    for key in ('base_waits','base_goals','old_waits','old_goals','fresh_waits','fresh_goals'):
        assert set(w[key])==proof_keys
    for i in proof_keys:
        assert w['base_waits'][i]['result']==w['old_waits'][i]['result']==w['fresh_waits'][i]['result']=={}
        assert w['base_goals'][i]['result']['goals']==[]
        assert w['old_goals'][i]['result']['goals']==[]
        assert w['fresh_goals'][i]['result']['goals']==['⊢ helper = 8']
    for phase in ('base_tree','old_tree','fresh_tree'):
        tree=w[phase]
        assert tree['count']<=4 and tree['rss_bytes']<d['tools']['rss_cap_bytes']
    old=diags(f'wave-{j}-old');fresh=diags(f'wave-{j}-fresh')
    assert any(x.get('version')==2 and any(z['message']=='8' for z in x['diagnostics']) for x in old)
    assert any(any(z['message']=='7' for z in x['diagnostics']) for x in fresh)
    assert any(any('Tactic `rfl` failed' in z['message'] for z in x['diagnostics']) for x in fresh)
    if w['mode']=='lake':
        assert any(any('Imports are out of date' in z['message'] for z in x['diagnostics']) for x in old)
    else:
        assert not any(any('Imports are out of date' in z['message'] for z in x['diagnostics']) for x in old)
stops=[e for e in events if e['kind']=='stop']
assert len(stops)==8 and all(x['rc']==0 for x in stops)
assert not [x for x in events if x['kind']=='fatal']
print('PASS: 8 fresh batch oracles per generation, four two-worker direct/Lake stale-versus-fresh waves, artifacts, diagnostics and cleanup')
