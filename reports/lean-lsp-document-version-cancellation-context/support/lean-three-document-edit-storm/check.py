#!/usr/bin/env python3
"""Offline check of saved edit-burst wire trace and guarded overlap."""
import hashlib,json
from pathlib import Path

s=Path(__file__).resolve().parent
a=json.loads((s/'transcript.json').read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
subject=next(x for x in a if x['kind']=='subject')
assert set(subject['source_sha256'])=={'Slow.lean','FastA.lean','Batch.lean'}
for name,h in subject['source_sha256'].items():assert sha(s/'work'/name)==h
assert (s/'work/slow.entered').read_text()=='entered'
assert (s/'work/batch.entered').read_text()=='entered'
def one(kind):
 rows=[x for x in a if x['kind']==kind]
 assert len(rows)==1,(kind,len(rows))
 return rows[0]
gate=one('slow_gate_entered');batch_gate=one('batch_gate_entered');burst=one('burst_complete')
waits=one('fast_final_waits');goals=one('fast_final_goals');batch_end=one('batch_end')
release=one('slow_gate_released');slow_end=one('slow_wait_end');stop=one('server_stop')
assert gate['ms']<batch_gate['ms']<burst['ms']<waits['ms']<goals['ms']<batch_end['ms']<release['ms']<slow_end['ms']
assert batch_end['exit']==0 and stop['exit']==0
assert 0<waits['elapsed_since_burst_ms']<30000
assert 0<goals['elapsed_since_burst_ms']<30000
assert one('peak_sampled_rss_kib')['value']<4600000
changes=[x['message']['params']['textDocument']['version'] for x in a
 if x['kind']=='client' and x['message'].get('method')=='textDocument/didChange']
assert changes==[2,4,4,3,5],changes
assert len(waits['responses'])==1 and all('error' not in v for v in waits['responses'].values())
assert len(goals['responses'])==1
goal=next(iter(goals['responses'].values()))
assert goal['result']['goals']==['⊢ 5 = 5']
diags=[x for x in a if x['kind']=='server' and x['message'].get('method')=='textDocument/publishDiagnostics']
assert any(x['message']['params'].get('version')==5 and x['message']['params']['uri'].endswith('/FastA.lean')
 for x in diags if x['ms']>=burst['ms'] and x['ms']<=waits['ms'])
assert slow_end['response'].get('result')=={} and 'error' not in slow_end['response']
print('PASS: gated slow worker, active batch overlap, 2/4/4/3/5 burst, final v5 goal and bounded tail')
