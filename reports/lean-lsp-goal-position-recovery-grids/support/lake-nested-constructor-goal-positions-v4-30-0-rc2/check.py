#!/usr/bin/env python3
"""Read-only validation of one Lake nested-goal plain/rich position run."""
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent
r=json.loads((ROOT/'results.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert r['tools']=={
 'lake_sha256':'9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb',
 'lean_sha256':'b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997'}
assert r['preflight']['memory_free_percent']>=20
assert r['preflight']['disk_free_bytes']>=10*1024**3
assert 0<r['resources']['peak_process_group_rss_kib']<=1536*1024
assert 0<r['resources']['elapsed_seconds']<=300 and r['resources']['samples']>=10
for name in ('Dep.lean','Proof.lean'):
 p=ROOT/'fixture'/name
 assert p.read_text()==r['source'][name]
 assert sha(p)==r['source']['sha256'][name]
assert r['source']['variants']=={'nested':r['source']['Proof.lean']}
assert r['build']['exit']==r['setup']['exit']==r['batches']['nested']['exit']==0
assert 'Built Dep' in r['build']['stdout'] and 'Built Proof' in r['build']['stdout']
assert '$WORK/dep/.lake/build/lib/lean/Dep.olean' in r['setup']['stdout']
assert all(r['artifacts'].values()) and r['artifacts']['Dep.olean']!=r['artifacts']['Proof.olean']
batch=[json.loads(line) for line in r['batches']['nested']['stdout'].splitlines() if line.strip()]
assert len(batch)==2 and all(x['severity']=='information' for x in batch)
assert any("'nested' does not depend on any axioms" in x['data'] for x in batch)
assert any(x['data']=='7' for x in batch)
assert r['waits']['nested']['result']=={} and r['stop']=={'exit':0,'stderr':''}
assert r['connect']['result']['sessionId']
expected={
 'before_constructor':((3,2),['h : depValue = 7\n⊢ depValue = 7 ∧ True'],[None],['depValue = 7 ∧ True'],[['h']]),
 'after_constructor':((3,13),['case left\nh : depValue = 7\n⊢ depValue = 7','case right\nh : depValue = 7\n⊢ True'],['left','right'],['depValue = 7','True'],[['h'],['h']]),
 'first_bullet':((4,2),['case left\nh : depValue = 7\n⊢ depValue = 7','case right\nh : depValue = 7\n⊢ True'],['left','right'],['depValue = 7','True'],[['h'],['h']]),
 'have_start':((4,4),['case left\nh : depValue = 7\n⊢ depValue = 7'],['left'],['depValue = 7'],[['h']]),
 'inner_by':((4,30),['h : depValue = 7\n⊢ depValue = 7'],[None],['depValue = 7'],[['h']]),
 'inner_exact_start':((5,6),['h : depValue = 7\n⊢ depValue = 7'],[None],['depValue = 7'],[['h']]),
 'inner_exact_end':((5,13),[],[],[],[]),
 'outer_exact_start':((6,4),['case left\nh hz : depValue = 7\n⊢ depValue = 7'],['left'],['depValue = 7'],[['h','hz']]),
 'outer_exact_end':((6,12),[],[],[],[]),
 'second_bullet':((7,2),['case right\nh : depValue = 7\n⊢ True'],['right'],['True'],[['h']]),
 'trivial_start':((7,4),['case right\nh : depValue = 7\n⊢ True'],['right'],['True'],[['h']]),
 'trivial_end':((7,11),[],[],[],[]),
 'eof':((10,0),None,None,None,None)}

def render(x):
 if isinstance(x,str):return x
 if isinstance(x,list):return ''.join(map(render,x))
 if isinstance(x,dict):
  if 'info' in x and 'subexprPos' in x:return ''
  for k in ('text','append','tag'):
   if k in x:return render(x[k])
 raise AssertionError(x)

assert list(r['live']['nested'])==list(expected)
for name,(coords,plain_expected,users,targets,names) in expected.items():
 pair=r['live']['nested'][name]
 assert pair['position']=={'line':coords[0],'character':coords[1]}
 assert r['positions'][name]==list(coords)
 assert 'error' not in pair['plain'] and 'error' not in pair['rich']
 p=pair['plain']['result'];q=pair['rich']['result']
 if plain_expected is None:
  assert p is None and q is None
  continue
 assert p['goals']==plain_expected and len(q['goals'])==len(plain_expected)
 for rich,user,target,hyp_names in zip(q['goals'],users,targets,names):
  assert rich.get('userName')==user
  assert render(rich['type'])==target
  assert [n for h in rich['hyps'] for n in h['names']]==hyp_names
  assert all(render(h['type'])=='depValue = 7' for h in rich['hyps'])
assert r['diagnostics']['nested']
assert not any(d['severity']==1 for ds in r['diagnostics']['nested'] for d in ds)
assert any("'nested' does not depend on any axioms" in d['message'] for ds in r['diagnostics']['nested'] for d in ds)
requests=[e['message'] for e in r['events'] if e['direction']=='client' and e['message'].get('method') in ('$/lean/plainGoal','$/lean/rpc/call')]
assert len(requests)==26
assert len([m for m in requests if m['method']=='$/lean/plainGoal'])==13
assert len([m for m in requests if m['method']=='$/lean/rpc/call'])==13
ids={m['id'] for m in requests}
replies=[e['message'] for e in r['events'] if e['direction']=='server' and e['message'].get('id') in ids]
assert len(replies)==26 and {m['id'] for m in replies}==ids
assert len([e for e in r['events'] if e['direction']=='client' and e['message'].get('method')=='$/lean/rpc/connect'])==1
assert not [e for e in r['events'] if e['direction']=='client' and e['message'].get('method')=='textDocument/didChange']
print('PASS: one Lake nested fixture, batch/import controls, 13 plain/rich pairs, diagnostics, resources, shutdown')
