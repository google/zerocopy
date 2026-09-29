#!/usr/bin/env python3
"""Validate retained plugin reversal and restart wire/byte evidence offline."""
import hashlib,json
from pathlib import Path

s=Path(__file__).resolve().parent
a=json.loads((s/'transcript.json').read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
subject=next(x for x in a if x['kind']=='subject')
v1=subject['v1_plugin_sha256'];v2=subject['v2_plugin_sha256']
assert v1!=v2
assert sha(s/'artifacts/plugin-v1.dylib')==v1
assert sha(s/'artifacts/plugin-v2.dylib')==v2
assert sha(s/'work/live/.lake/build/lib/lean/plugin__probe_Plugin.dylib')==v1
assert sha(s/'work/live/.lake/build/lib/lean/Dep.olean')==subject['dep_olean_sha256']
assert sha(s/'work/live/P0.lean')==subject['proof_sha256']
starts=[x for x in a if x['kind']=='server_start']
stops=[x for x in a if x['kind']=='server_stop']
assert [x['label'] for x in starts]==['retained','fresh']
assert [x['label'] for x in stops]==['retained','fresh']
assert stops[0]['seq']<starts[1]['seq'] and all(x['exit']==0 for x in stops)
assert starts[0]['plugin_sha256']==starts[1]['plugin_sha256']==v1
replacements=[x for x in a if x['kind']=='replace']
assert [(x['label'],x['old_sha256'],x['new_sha256']) for x in replacements]==[
 ('v1-to-v2',v1,v2),('v2-to-v1',v2,v1)]
phases=[x for x in a if x['kind']=='phase']
assert [(x['label'],x['marker'],x['plugin_sha256']) for x in phases]==[
 ('v1-first','plugin-v1',v1),('v2-second','plugin-v2',v2),
 ('v1-third','plugin-v1',v1),('v1-after-restart','plugin-v1',v1)]
for x in phases:
 assert x['wait'].get('result')=={}
 assert x['goal'].get('result',{}).get('rendered')=='no goals'
 assert x['goal'].get('result',{}).get('goals')==[]
olds=[x for x in a if x['kind'].startswith('old_goal_')]
assert [x['marker'] for x in olds]==['plugin-v1','plugin-v2']
assert all(x['goal'].get('result',{}).get('rendered')=='no goals' for x in olds)
assert a[-1]['kind']=='final_artifact' and a[-1]['plugin_sha256']==v1
print('PASS: v1→v2→v1 marker order, retained old goals, fresh restart and exact plugin bytes')
