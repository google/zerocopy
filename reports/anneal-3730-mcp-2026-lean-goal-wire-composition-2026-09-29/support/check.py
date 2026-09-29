#!/usr/bin/env python3
"""Offline consistency check for current-wire test bridge over real Lean goal."""
import hashlib,json
from pathlib import Path
R=Path(__file__).resolve().parent
x=json.loads((R/'results.json').read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert x['preflight']['free_memory_percent']>=30
assert x['preflight']['free_disk_bytes']>=2*1024**3
for name,path in [('source_sha256',R/'Proof.lean'),('bridge_sha256',R/'bridge.py'),('probe_sha256',R/'probe.py'),('slow_source_sha256',R/'Slow.lean')]:
 assert sha(path)==x['pins'][name],name
assert x['pins']['lean_sha256']==hashlib.sha256(Path(x['pins']['lean']).read_bytes()).hexdigest()
c=x['cases']
assert c['wrong_version']['error']['code']==-32022
assert c['discover']['result']['supportedVersions']==['2026-07-28']
assert 'io.modelcontextprotocol/tasks' in c['discover']['result']['capabilities']['extensions']
assert c['stale']['error']['code']==-32602
assert c['stale']['error']['data']['current_sha256']==x['pins']['source_sha256']
assert c['sync']['result']['resultType']=='complete' and c['sync']['result']['content']==[{'type':'text','text':'⊢ True'}]
assert c['start']['result']['resultType']=='task'
assert c['initial']['result']['status']=='working'
assert c['old_result_method']['error']['code']==-32601
final=c['completed']['result'];assert final['status']=='completed'
assert final['result']['resultType']=='complete' and final['result']['content']==[{'type':'text','text':'⊢ True'}]
assert final['result']['_meta']['sourceSha256']==x['pins']['source_sha256']
assert final['result']['_meta']['lspExit']==0 and final['result']['_meta']['trackedAfter']==[]
assert c['cancel_ack']['result']=={'resultType':'complete'}
assert c['cancelled']['result']['status']=='cancelled'
assert c['before_slow_stats']['result']['queryCount']==2
assert c['slow_start']['result']['resultType']=='task'
assert c['slow_inflight']['result']['status']=='working'
assert c['slow_inflight']['result']['statusMessage']=='Lean waitForDiagnostics in flight'
assert c['slow_cancel_ack']['result']=={'resultType':'complete'}
assert c['slow_cancelled']['result']['status']=='cancelled'
assert c['slow_cancelled']['result']['statusMessage']=='result suppressed after in-flight cancellation'
assert 'result' not in c['slow_cancelled']['result']
assert c['stats']['result']['queryCount']==3 and len(c['stats']['result']['queries'])==3
assert c['stats']['result']['activeQueries']==0
for i,q in enumerate(c['stats']['result']['queries']):
 assert q['source_sha256']==(x['pins']['source_sha256'] if i<2 else x['pins']['slow_source_sha256'])
 assert q['goal']['result']['goals']==['⊢ True']
 if i<2:
  assert q['upstream_cancel_sent'] is False and q['wait']['result']=={}
 else:
  assert q['upstream_cancel_sent'] is True and q['wait']['error']['code']==-32800
 assert q['cleanup']['exit']==0 and q['cleanup']['tracked_after']==[]
 assert len(q['cleanup']['before'])>=2
assert x['bridge_process']['exit']==0 and x['bridge_process']['stderr']==''
assert x['batch']['exit']==0 and '⊢ True' in x['batch']['stdout']
assert "'target' does not depend on any axioms" in x['batch']['stdout']
assert 'sorryAx' not in x['batch']['stdout']
assert x['slow_batch']['exit']==0 and '⊢ True' in x['slow_batch']['stdout']
assert "'target' does not depend on any axioms" in x['slow_batch']['stdout']
assert len(x['transcript'])>=44 and len(x['transcript'])%2==0
assert all(row['message'].get('method')!='notifications/progress' for row in x['transcript'] if row['direction']=='server')
assert any(row['direction']=='client' and row['message'].get('method')=='tasks/cancel' for row in x['transcript'])
print('PASS: current-wire toy Tasks over real Lean goal, stale/pre-start/forwarded in-flight cancel and fresh batch oracles')
