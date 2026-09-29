#!/usr/bin/env python3
"""Check retained bounded Lean observations without rerunning Lean."""
import hashlib
import json
from pathlib import Path

here=Path(__file__).resolve().parent
x=json.loads((here/'results.json').read_text())
assert x['subject']['lean_sha256']=='b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997'
assert x['subject']['free_percent']>=25
source=here.parents[1]/'anneal-3730-lean-launch-refresh-matrix-v4-30-0-rc2'/'support'/'probe.py'
assert hashlib.sha256(source.read_bytes()).hexdigest()==x['subject']['source_harness_sha256']
cases=x['uri']['cases']
assert len(cases)==8
assert {(r['mode'],r['case']) for r in cases}=={(m,c) for m in ('direct','lake-serve') for c in ('shell','file-absent','custom','untitled')}
for r in cases:
    assert r['wait']['result']=={}
    assert r['goal']['result']['goals']==['⊢ selected = 7']
    assert r['source_sha256']==hashlib.sha256(b'import Dep\ntheorem q : selected = 7 := by\n  exact ?_\n').hexdigest()
    assert r['diagnostics'] is not None
    if r['case']=='file-absent': assert r['physical_exists'] is False
    if r['case']=='shell': assert r['physical_exists'] is True
setup={r['label']:r for r in x['uri']['setup']}
assert setup['setup-Shell.lean']['rc']==0
assert setup['setup-Absent.lean']['rc']!=0
h=x['history']
for key,goal in [('initial','⊢ 1 = 1'),('oldgoal','⊢ 1 = 1'),('latest','⊢ 3 = 3'),('stillold','⊢ 1 = 1'),('reopened_goal','⊢ 1 = 1'),('fresh_goal','⊢ 1 = 1')]:
    assert h[key]['result']['goals']==[goal]
for key in ('first','oldwait','wait2','wait3','reopened_wait','fresh_wait'): assert h[key]['result']=={}
assert h['afterclose']['error']['code']==-32801
assert h['rss_before']['count'] and h['rss_after']['count']
assert h['fresh_rss']['count'] and h['resident_old_goal_ms']>=0
assert h['reopened_old_wait_and_goal_ms']>=0 and h['fresh_start_wait_goal_ms']>=0
rows=x['imports']['rows']
assert [r['label'] for r in rows]==['base','proof-body','statement','helper-change','model-change','updated-obligations']
assert [(r['proof']['rc'],r['proof2']['rc']) for r in rows]==[(0,0),(0,0),(1,0),(1,1),(1,1),(0,0)]
assert rows[0]['artifact_hashes']==rows[1]['artifact_hashes']==rows[2]['artifact_hashes']
assert rows[2]['artifact_hashes']['Helper.olean']!=rows[3]['artifact_hashes']['Helper.olean']
assert rows[3]['artifact_hashes']['Model.olean']==rows[0]['artifact_hashes']['Model.olean']
assert rows[4]['artifact_hashes']['Model.olean']!=rows[0]['artifact_hashes']['Model.olean']
assert rows[4]['artifact_hashes']['Helper.olean']!=rows[3]['artifact_hashes']['Helper.olean']
assert rows[5]['artifact_hashes']==rows[4]['artifact_hashes']
for r in rows:
    if r['build']:assert r['build']['rc']==0
for r in rows[2:5]: assert 'Tactic `rfl` failed' in r['proof']['stdout']
fan=x['imports']['fanout']
assert [r['label'] for r in fan]==['eight-current','eight-stale','eight-updated']
assert all(len(r['checks'])==8 for r in fan)
assert [[c['rc'] for c in r['checks']] for r in fan]==[[0]*8,[1]*8,[0]*8]
assert fan[0]['model_olean_sha256']!=fan[1]['model_olean_sha256']
assert fan[0]['helper_olean_sha256']!=fan[1]['helper_olean_sha256']
assert fan[1]['model_olean_sha256']==fan[2]['model_olean_sha256']
assert all('Tactic `rfl` failed' in c['stdout'] for c in fan[1]['checks'])
print('PASS URI/Lake, historical same-versus-separate URI, and imported proof/model ablations')
