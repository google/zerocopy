#!/usr/bin/env python3
"""Offline check of one Lake term-proof plain/rich/plainTermGoal position run."""
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
assert r['source']['variants']=={'term_proof':r['source']['Proof.lean']}
assert r['build']['exit']==r['setup']['exit']==r['batches']['term_proof']['exit']==0
assert 'Built Dep' in r['build']['stdout'] and 'Built Proof' in r['build']['stdout']
assert '$WORK/dep/.lake/build/lib/lean/Dep.olean' in r['setup']['stdout']
assert all(r['artifacts'].values()) and r['artifacts']['Dep.olean']!=r['artifacts']['Proof.olean']
batch=[json.loads(line) for line in r['batches']['term_proof']['stdout'].splitlines() if line.strip()]
assert len(batch)==2 and all(x['severity']=='information' for x in batch)
assert any("'term_proof' does not depend on any axioms" in x['data'] for x in batch)
assert any(x['data']=='7' for x in batch)
assert r['waits']['term_proof']['result']=={} and r['stop']=={'exit':0,'stderr':''}
assert r['connect']['result']['sessionId']
expected={
 'exact_start':((3,2),['⊢ depValue = depValue'],1,None),
 'exact_inside':((3,5),[],0,None),
 'term_start':((3,8),[],0,('⊢ depValue = depValue',8,24)),
 'term_inside':((3,11),[],0,('⊢ depValue = depValue',8,24)),
 'argument_start':((3,16),[],0,('⊢ Nat',16,24)),
 'argument_inside':((3,20),[],0,('⊢ Nat',16,24)),
 'term_end':((3,24),[],0,('⊢ Nat',16,24)),
 'next_line':((4,0),None,None,None),
 'eof':((6,0),None,None,None)}

def render(x):
 if isinstance(x,str):return x
 if isinstance(x,list):return ''.join(map(render,x))
 if isinstance(x,dict):
  if 'info' in x and 'subexprPos' in x:return ''
  for key in ('text','append','tag'):
   if key in x:return render(x[key])
 raise AssertionError(x)

assert list(r['live']['term_proof'])==list(expected)
for name,(coords,plain_expected,rich_count,term_expected) in expected.items():
 pair=r['live']['term_proof'][name]
 assert pair['position']=={'line':coords[0],'character':coords[1]}
 assert r['positions'][name]==list(coords)
 assert all('error' not in pair[api] for api in ('plain','rich','term'))
 p=pair['plain']['result'];q=pair['rich']['result'];t=pair['term']['result']
 if plain_expected is None:assert p is None and q is None
 else:
  assert p['goals']==plain_expected and len(q['goals'])==rich_count
  if rich_count:
   assert q['goals'][0]['hyps']==[]
   assert render(q['goals'][0]['type'])=='depValue = depValue'
 if term_expected is None:assert t is None
 else:
  goal,start,end=term_expected
  assert t=={'goal':goal,'range':{'start':{'line':3,'character':start},'end':{'line':3,'character':end}}}
assert r['diagnostics']['term_proof']
assert not any(d['severity']==1 for ds in r['diagnostics']['term_proof'] for d in ds)
assert any("'term_proof' does not depend on any axioms" in d['message'] for ds in r['diagnostics']['term_proof'] for d in ds)
requests=[e['message'] for e in r['events'] if e['direction']=='client' and e['message'].get('method') in ('$/lean/plainGoal','$/lean/rpc/call','$/lean/plainTermGoal')]
assert len(requests)==27
assert all(len([m for m in requests if m['method']==method])==9 for method in ('$/lean/plainGoal','$/lean/rpc/call','$/lean/plainTermGoal'))
ids={m['id'] for m in requests}
replies=[e['message'] for e in r['events'] if e['direction']=='server' and e['message'].get('id') in ids]
assert len(replies)==27 and {m['id'] for m in replies}==ids
assert len([e for e in r['events'] if e['direction']=='client' and e['message'].get('method')=='$/lean/rpc/connect'])==1
assert not [e for e in r['events'] if e['direction']=='client' and e['message'].get('method')=='textDocument/didChange']
print('PASS: one Lake reflexive term proof, 9 plain/rich/term triples, batch/import controls, diagnostics, resources, shutdown')
