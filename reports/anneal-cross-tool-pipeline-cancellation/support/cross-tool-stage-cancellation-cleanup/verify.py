#!/usr/bin/env python3
"""Verify retained cancellation, retry, artifact and synthetic fence evidence."""
import hashlib,json
from pathlib import Path

HERE=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
raw=json.loads((HERE/'results.json').read_text())
stages=raw['stages']
assert [x['stage'] for x in stages]==['cargo','charon','aeneas','lake','lean','cargo-active','charon-active','lake-active']
for stage in stages:
    cancel=stage['cancel'];retry=stage['retry']
    assert cancel['signal']=='SIGSTOP then SIGKILL' and cancel['exit']==-9
    assert cancel['stopped_group'] and not cancel['remaining_group'] and not cancel['surviving_recorded_pids']
    assert all('T' in x['stat'] for x in cancel['stopped_group'])
    assert retry['exit']==0
assert {'cargo','rustc'}=={x['comm'].split('/')[-1] for x in stages[5]['cancel']['stopped_group']}
assert {'charon','cargo'}.issubset({x['comm'].split('/')[-1] for x in stages[6]['cancel']['stopped_group']})
assert len(stages[6]['cancel']['stopped_group'])>=3
assert len(stages[5]['cancel']['output_after'])>0 and len(stages[7]['cancel']['output_after'])>0
for name,digest in raw['artifacts_sha256'].items():
    assert sha(HERE/'artifacts'/name)==digest
charon=json.loads((HERE/'artifacts/charon-app.llbc').read_text())
assert charon['translated']['crate_name']=='app_closure' and not charon['has_errors']
assert (HERE/'artifacts/aeneas-Funs.lean').read_text().strip()
assert (HERE/'artifacts/lake-Probe.olean').stat().st_size>0
fence=json.loads((HERE/'fence-results.json').read_text())
assert fence['model_only'] and fence['input_results_sha256']==sha(HERE/'results.json')
assert len(fence['events'])==len(stages)
assert all(x['late_rejected'] and x['pointer_unchanged_after_late'] and x['fresh_accepted'] for x in fence['events'])
print('verified 8 cancellation/retry groups, retained artifacts, and 8 synthetic fence rejects')
