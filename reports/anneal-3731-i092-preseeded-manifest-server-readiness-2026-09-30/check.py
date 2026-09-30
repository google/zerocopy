#!/usr/bin/env python3
"""Offline check of retained I092 retry evidence."""
import hashlib, json, re
from pathlib import Path
P=Path(__file__).resolve().parent
sha=lambda b: hashlib.sha256(b).hexdigest()

def frames(raw):
 out=[]
 while raw:
  head,sep,rest=raw.partition(b'\r\n\r\n'); assert sep
  n=int(re.search(rb'(?i)Content-Length:\s*(\d+)',head).group(1))
  out.append(json.loads(rest[:n]));raw=rest[n:]
 return out

def main():
 x=json.loads((P/'results.json').read_text()); seed=json.loads((P/'preseed.json').read_text())
 meta=json.loads((P/'REPORT.json').read_text())
 assert x['schema']==2 and x['status']=='completed'
 assert meta['subjects'][0]['identity']['results_sha256']==sha((P/'results.json').read_bytes())
 assert x['preseed_sha256']==sha((P/'preseed.json').read_bytes())
 found={str(f.relative_to(P/'work')):sha(f.read_bytes()) for f in (P/'work').rglob('*') if f.is_file() and not f.is_symlink()}
 assert len(found)==36 and found==seed['work_sha256']
 assert x['restored_manifest_sha256']==x['manifest_sha256']['valid']==sha((P/'work/consumer/lake-manifest.json').read_bytes())
 assert x['producer_source_sha256']==sha((P/'work/producer/Dep.lean').read_bytes())
 assert x['consumer_source_sha256']==sha((P/'work/consumer/Generated.lean').read_bytes())
 assert [r['label'] for r in x['runs']]==['valid-server','malformed-server','semantic-no-dependency-server']
 for name in ('valid','malformed','semantic-no-dependency'):
  assert x['manifest_sha256'][name]==sha((P/'fixtures'/f'{name}-lake-manifest.json').read_bytes())
  p=x['phases'][name]
  assert p['manifest_sha256']==x['manifest_sha256'][name]
  assert p['producer_before']==p['producer_after'] and p['cache_before']==p['cache_after']
 assert (P/'fixtures/malformed-lake-manifest.json').read_bytes()==b'{\n'
 assert json.loads((P/'fixtures/semantic-no-dependency-lake-manifest.json').read_text())['packages']==[]
 assert 'require probe_dep' in (P/'work/consumer/lakefile.lean').read_text()
 for r in x['runs']:
  name=r['label'].removesuffix('-server'); admit=x['server_admissions'][r['label']]
  assert admit['memory']['fraction']>.30 and admit['disk_free']>10*1024**3
  assert r['exit']==0 and r['abort'] is None and not r['client_errors']
  assert r['opened'] and r['first_diagnostic_observed'] and r['elapsed']<30 and r['before']==r['after']
  assert r['env_overrides']['LAKE_NO_NET']=='1' and r['env_overrides']['LEAN_PATH'] is None
  assert r['argv'][-3:]==['--no-build','--no-cache','serve']
  assert min(z['reclaimable'] for z in r['resource_samples'])>=.20
  assert max(z['group_rss_kib'] for z in r['resource_samples'])<1200*1024
  raw=(P/'raw'/f"{r['label']}.stdout").read_bytes();err=(P/'raw'/f"{r['label']}.stderr").read_bytes()
  assert sha(raw)==r['stdout_sha256'] and sha(err)==r['stderr_sha256']
  msgs=frames(raw);assert msgs==r['decoded_messages']==[e['message'] for e in r['received_events']]
  sends=[e['message'] for e in r['sent_events']]
  assert [m['method'] for m in sends]==['initialize','initialized','textDocument/didOpen','$/lean/plainGoal','shutdown','exit']
  assert sends[3]['params']['position']=={'line':1,'character':40}
  assert sends[2]['params']['textDocument']['text']==(P/'work/consumer/Generated.lean').read_text()
  replies={m['id']:m for m in msgs if isinstance(m.get('id'),int) and 'result' in m}
  assert 'result' in replies[1] and 'result' in replies[3] and replies[2]==r['goal_response']
  progs=[m['params']['processing'] for m in msgs if m.get('method')=='$/lean/fileProgress']
  diags=[d['message'] for m in msgs if m.get('method')=='textDocument/publishDiagnostics' for d in m['params']['diagnostics']]
  if name=='valid':
   assert r['readiness_quiescent'] and progs[-1]==[] and 6<r['diagnostic_wait_seconds']<8
   assert r['goal_response']['result']['goals']==['⊢ depValue = 7'] and '7' in diags and err==b''
  else:
   assert not r['readiness_quiescent'] and r['goal_response']['result'] is None
   assert 8<=r['diagnostic_wait_seconds']<8.1 and progs[-1]!=[] and progs[-1][0]['kind']==2
   joined='\n'.join(diags);assert 'Failed to configure the Lake workspace' in joined and 'lake setup-file' in joined
   assert b'falling back to plain `lean --server`' in err
   assert ('invalid JSON: offset 2' if name=='malformed' else 'missing manifest; use `lake update`') in joined
 print('PASS: I092 preseeded manifest server readiness evidence')
if __name__=='__main__': main()
