#!/usr/bin/env python3
"""Validate retained combined-pipeline cells without launching heavy tools."""
import json
from pathlib import Path

base=Path(__file__).parent
for mode,filename in [('on','results-instrumented.json'),('off','results-uninstrumented.json')]:
    x=json.loads((base/filename).read_text())
    assert x['preflight']['ram_bytes']==8589934592
    assert x['guards']['rss_cap_kib']==4_000_000
    assert x['cells'][0]['label']=='serial-2'
    assert x['cells'][1]['label']=='parallel-2'
    assert x['cells'][2]['label']=='parallel-2-lean1'
    assert x['cells'][3]['label']=='parallel-4' and not x['cells'][3]['admission']['allowed']
    assert len(x['tools'])==5
    outputs=[]
    for c in x['cells'][:3]:
        assert c['admission']['allowed'] and c['abort'] is None and not c['errors']
        assert len(c['units'])==2 and c['cleanup_tree']['count']==0
        assert c['sampled_peak_rss_kib']<4_000_000 and c['sampled_peak_processes']<=40
        for u in c['units']:
            assert [cmd['exit'] for cmd in u['commands']]==[0]*6
            assert [cmd['label'].split(':',1)[1] for cmd in u['commands']]==[
                'charon','aeneas','lean:Current/Types','lean:Current/Funs','lean:Current','lean:proof']
            assert u['axiom_stdout'].count("'obl_")==3
            assert 'sorryAx' not in u['axiom_stdout']
            outputs.append(u['hashes'])
        if mode=='on':
            assert c['group_footprint_samples']
            assert any(z['complete'] and z['sum_phys_footprint_bytes'] for z in c['group_footprint_samples'])
        else:assert not c['group_footprint_samples']
    for key in ['rust','types','funs','entry','proof','funs_olean']:
        assert len({u[key] for u in outputs})==1,key
    assert len({u['llbc'] for u in outputs})==6
    assert all(x['output_comparison'].values())
print('PASS: two retained complete workflow runs, resource gates and output identities')
