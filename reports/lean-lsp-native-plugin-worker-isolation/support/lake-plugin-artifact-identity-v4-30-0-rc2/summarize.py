#!/usr/bin/env python3
"""Assert the acquired result without rerunning the compilers or server."""
import hashlib, json
from pathlib import Path
H=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
rows=json.loads((H/'transcript.json').read_text())
assert [x['seq'] for x in rows]==list(range(len(rows)))
cmd={x['label']:x for x in rows if x['kind']=='command'}
phase={x['label']:x for x in rows if x['kind']=='phase'}
def rc(label,n):assert cmd[label]['rc']==n,(label,cmd[label]['rc'])
def no_goals(label):
    x=phase[label]
    assert x['wait']['result']=={} and x['goal']['result']['rendered']=='no goals',label
for f in ['olean','ilean','c','dynlib']:
    rc('no-build-'+f,3)
    rc('setup-'+f,0)
    rc('batch-after-setup-'+f,0 if f!='dynlib' else 1)
rc('batch-before-setup-olean',1)
for f in ['ilean','c']:rc('batch-before-setup-'+f,0)
rc('batch-before-setup-dynlib',1)
rc('batch-without-plugin-after-prune-dynlib',0)
for f in ['invalid-dylib','missing-dylib']:rc('batch-'+f,1)
rc('batch-fresh-after-replace',0);rc('batch-fresh-bad-abi',1)
assert 'initializer not found' in cmd['batch-fresh-bad-abi']['stderr']
assert 'valid mach-o' in cmd['batch-invalid-dylib']['stderr']
for label in ['old-before','old-process-new-worker','fresh','bad-abi-before']:no_goals(label)
assert phase['old-before']['marker']=='plugin-v1'
assert phase['old-process-new-worker']['marker']=='plugin-v2'
assert phase['fresh']['marker']=='plugin-v2'
assert phase['bad-abi-new-worker']['wait']['error']['code']==-32901
assert phase['bad-abi-new-worker']['goal'] is None
assert all(x['rc']==0 for x in rows if x['kind']=='server_stop')
events={x['kind']:[] for x in rows}
for x in rows:events[x['kind']].append(x)
assert events['old-goal-after'][0]['goal']['result']['rendered']=='no goals'
assert events['old-goal-after'][0]['marker']=='plugin-v1'
assert events['bad-abi-old-goal-after'][0]['goal']['result']['rendered']=='no goals'
assert events['replace-plugin'][0]['old_sha256']!=events['replace-plugin'][0]['new_sha256']
assert events['replace-bad-abi'][0]['old_sha256']!=events['replace-bad-abi'][0]['new_sha256']
restored={x['family']:x['restored'] for x in events['after-prune']}
assert restored=={'olean':True,'ilean':True,'c':True,'dynlib':False},restored
subject=events['subject'][0]
summary=dict(status='bounded assertions passed',event_count=len(rows),probe_sha256=sha(H/'probe.py'),transcript_sha256=sha(H/'transcript.json'),
             lean_sha256=subject['lean_sha256'],lake_sha256=subject['lake_sha256'],
             baseline_artifacts=events['built'][0]['artifacts'],
             plugin_v1_sha256=events['replace-plugin'][0]['old_sha256'],plugin_v2_sha256=events['replace-plugin'][0]['new_sha256'],
             wrong_initializer_sha256=events['replace-bad-abi'][0]['new_sha256'],
             command_rc={k:v['rc'] for k,v in cmd.items() if k not in ('memory-pressure','lean-version','uname')},
             phase_marker={k:v['marker'] for k,v in phase.items()},restored=restored,
             max_event_ms=max(x['time_ms'] for x in rows))
(H/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
