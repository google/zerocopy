#!/usr/bin/env python3
"""Check retained two-project router evidence and fixture without launching Lean."""
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent
data=json.loads((ROOT/'results.json').read_text())
sha=lambda path:hashlib.sha256(path.read_bytes()).hexdigest()
assert '4.30.0-rc2' in data['lean_version']
assert '3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc' in data['lean_version']

for label,value in [('A',11),('B',22)]:
    folder=ROOT/'fixture'/label
    record=data['projects'][label]
    assert record['value']==value and record['build_returncode']==0
    assert sha(folder/'Dep.lean')==record['dependency_source_sha256']
    assert sha(folder/'Dep.olean')==record['dependency_artifact_sha256']
    assert sha(folder/'Proof.lean')==record['proof_source_sha256']
    assert (folder/'Dep.lean').read_text()==f'def selected : Nat := {value}\n'
    assert f'theorem expected : selected = {value}' in (folder/'Proof.lean').read_text()
assert data['projects']['A']['dependency_artifact_sha256']!=data['projects']['B']['dependency_artifact_sha256']

route=data['route']
assert [(r['project'],r['reused']) for r in route]==[
    ('A',False),('B',False),('A',True),('A',False),('B',True)]
assert route[0]['pid']==route[2]['pid']==data['A_initial']['pid']==data['A_resumed']['pid']
assert route[1]['pid']==route[4]['pid']==data['B_initial']['pid']==data['B_resumed']['pid']
assert route[3]['pid']==data['A_cold']['pid']!=route[0]['pid']

def messages(section):
    return [d['message'] for d in section['diagnostics']]
def no_goals(result):
    return result['result']=={'goals':[],'rendered':'no goals'}

assert no_goals(data['A_initial']['goal']) and no_goals(data['B_initial']['goal'])
assert no_goals(data['A_cold']['goal']) and no_goals(data['B_resumed']['goal'])
assert data['A_unsaved']['buffer_sha256']!=data['A_unsaved']['disk_sha256']
assert data['A_unsaved']['disk_sha256']==data['projects']['A']['proof_source_sha256']
assert data['A_unsaved']['goal']['result']['goals']==['⊢ selected = 99']
assert data['A_resumed']['goal']['result']['goals']==['⊢ selected = 99']
assert any('Tactic `rfl` failed' in m for m in messages(data['A_unsaved']['edit']))
assert data['A_unsaved']['edit']['diagnostics']==data['A_resumed']['wait']['diagnostics']
assert all('Tactic `rfl` failed' not in m for m in messages(data['A_initial']['open']))
assert all('Tactic `rfl` failed' not in m for m in messages(data['A_cold']['open']))
assert all('Tactic `rfl` failed' not in m for m in messages(data['B_initial']['open']))
assert any(m=='11' for m in messages(data['A_initial']['open']))
assert any(m=='22' for m in messages(data['B_initial']['open']))

for label in ('A','B'):
    rows=data['two_server_processes'][label]
    assert len(rows)==2
    assert any(r['pid']==data[f'{label}_initial']['pid'] for r in rows)
    assert len({r['pid'] for r in rows})==2
assert data['A_first_stop']['returncode']==0
assert data['A_first_stop']['tracked_pids_after']==[]
assert len(data['final_stops'])==2
assert all(s['returncode']==0 and s['tracked_pids_after']==[] for s in data['final_stops'])
assert [e['project'] for e in data['events'] if e['kind']=='switch']==[r['project'] for r in route]
print('PASS: A→B→A route, import/unsaved-buffer isolation, cold-restart contrast, process trees, cleanup')
