#!/usr/bin/env python3
"""Check retained R20 claims from raw results and captured files, without rerunning CLIs."""
import hashlib,json
from pathlib import Path
here=Path(__file__).resolve().parent
r=json.loads((here/'results.json').read_text());x=r['results']
assert r['schema']==1 and len(r['commands'])>=19
for path,digest in r['tools'].items():
    assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==digest
for path,digest in [(here/'work/charon/base.rs',r['fixture_hashes']['rust_base']),
                    (here/'work/new/current.rs',r['fixture_hashes']['rust_new']),
                    (here/'work/lake/Cancel/B.lean',r['fixture_hashes']['lake_B']),
                    (here/'gated_stage.py',r['fixture_hashes']['gated_stage'])]:
    assert hashlib.sha256(path.read_bytes()).hexdigest()==digest
for key in ['pre_exec','charon_cancel','aeneas_cancel','lake_cancel']:
    c=x[key]
    assert c['barrier']['alive'] and c['rc']==-9 and c['signal']=='SIGKILL'
    assert c['members_before'] and not c['members_after']
assert x['pre_exec']['cli_started'] is False
assert len(x['charon_cancel']['members_before'])>=2
assert x['charon_retry']['json_valid'] and x['charon_retry']['postcard_parse_rc']==0
assert set(x['aeneas_cancel']['partial'])=={'Types.lean'}
assert x['lake_cancel']['A_olean_exists'] and not x['lake_cancel']['B_olean_exists']
assert len(x['lake_cancel']['members_before'])>=2 and x['lake_retry']['consumer_rc']==0
for k in ['aeneas_retry','new_complete']:
    assert 'Funs.lean' in x[k]['generated'] and x[k]['lean']['oracle_stdout'].find('sorryAx')<0
assert x['old_wait']['alive'] and x['late_fence']['wrapper_rc']==0
assert x['late_fence']['decision']=={'job_generation':1,'authority_generation':2,'publish':False,'aeneas_rc':0}
assert x['late_fence']['authority']=={'generation':2,'accepted':'current'}
assert len(x['late_fence']['old_generated'])>=3
assert all(row['rc']==0 for row in r['commands'] if row['label'] not in
           {'pre-exec-wrapper','charon-after-json-before-postcard',
            'aeneas-after-types-before-funs','lake-lean-in-tactic-after-A-olean'})
print('R20 retained-result checks passed')
