#!/usr/bin/env python3
"""Validate the retained R22 observation without re-executing the toolchains."""
import gzip,hashlib,json,re
from pathlib import Path
here=Path(__file__).resolve().parent
with gzip.open(here/'results.json.gz','rt') as f:r=json.load(f)
x=r['results']
assert r['schema']==1 and len(r['commands'])>=31
for path,digest in r['tool_hashes'].items():
    assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==digest
assert hashlib.sha256((here/'work/input.rs').read_bytes()).hexdigest()==r['fixture_sha256']
assert set(x)=={'charon','aeneas','lake'}
assert set(x['charon'])=={'graceful','kill-control'}
assert set(x['aeneas'])=={'graceful','kill-control','escalation-control'}
assert set(x['lake'])=={'graceful','kill-control'}
for stage,cases in x.items():
    for label,case in cases.items():
        c=case['cancel'];assert c['rc']!=0 and c['entered_ms']<30000
        assert c['before']['members'] and not c['after']['members']
        assert c['before']['flock']['exclusive_flock_obtained'] is True
        assert c['after']['flock']['exclusive_flock_obtained'] is True
        assert all(fd['rc']==0 for fd in c['before']['lsof'])
        raw='\n'.join(fd['stdout'] for fd in c['before']['lsof'])
        assert re.search(r'\bPIPE\b',raw),stage
        assert case['retry_rc']==0
        if label=='kill-control':assert [e['signal'] for e in c['timeline']]==['SIGKILL']
        if stage=='charon':
            assert case['postcard_parse_rc']==0 and 'input.llbc.postcard' in case['complete']
            assert len(c['before']['members'])==2 and c['partial_json_sha256']
        elif stage=='aeneas':
            assert case['oracle']['oracle_rc']==0 and 'Funs.lean' in case['oracle']['generated']
            assert 'Types.lean' in c['before']['output_at_gate'] and c['partial_types_sha256']
        else:
            assert case['consumer_rc']==0 and c['A_olean_exists'] and not c['B_olean_exists']
            assert len(c['before']['members'])==2 and case['B_olean_sha256']
assert [e['signal'] for e in x['charon']['graceful']['cancel']['timeline']]==['SIGINT']
assert [e['signal'] for e in x['aeneas']['graceful']['cancel']['timeline']]==['SIGTERM']
assert [e['signal'] for e in x['lake']['graceful']['cancel']['timeline']]==['SIGINT']
assert [e['signal'] for e in x['aeneas']['escalation-control']['cancel']['timeline']]==['SIGINT','SIGTERM']
assert len([m for m in x['aeneas']['escalation-control']['cancel']['timeline'][0]['members_after_grace']
            if not m['stat'].startswith('Z')])==2
print('R22 retained-result checks passed')
