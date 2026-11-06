#!/usr/bin/env python3
"""Self-check of acquired fixture and compiler/Charon evidence."""
import hashlib,json,re
from pathlib import Path
H=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
raw=json.loads((H/'raw-results.json').read_text())
assert [x['seq'] for x in raw]==list(range(len(raw)))
commands={x['label']:x for x in raw if x['kind']=='command'}
loc={x['variant']:x for x in raw if x['kind']=='locator'}
charon={x['label']:x for x in raw if x['kind']=='charon_result'}
def marker(label,name):
    p=charon[label]['projection']
    return [f for f in p['functions'] if 'proof-id: '+name in f['markers']]
def rc(label,n):assert commands[label]['rc']==n,(label,commands[label]['rc'])
for v in ['baseline','moved','duplicated','proof-edit']:
    rc('rustc-'+v,0);rc('lean-'+v,0)
rc('rustc-malformed',1);rc('rustc-unfinished',0)
assert 'unclosed delimiter' in commands['rustc-malformed']['stderr']
assert [(b['id'],b['status']) for b in loc['malformed']['blocks']]==[(b['id'],b['status']) for b in loc['baseline']['blocks']]
assert ('orphan','incomplete') in [(b['id'],b['status']) for b in loc['unfinished']['blocks']]
assert sum(b['id']=='claim-a' for b in loc['duplicated']['blocks'])==2
assert len([b for b in loc['baseline']['blocks'] if b['status']=='complete'])==5
for v in ['baseline-lib','baseline-selected','baseline-tests','moved-lib','duplicated-lib']:
    rc('charon-'+v,0)
    assert charon[v]['projection'] and not charon[v]['projection']['has_errors']
rc('charon-malformed-lib',101)
assert charon['malformed-lib']['projection'] is None
assert len(marker('baseline-lib','claim-a'))==1
assert len(marker('baseline-lib','selected'))==0
assert len(marker('baseline-selected','selected'))==1
assert len(marker('baseline-lib','test-only'))==0
assert len(marker('baseline-tests','test-only'))==1
assert len(marker('duplicated-lib','claim-a'))==2
assert marker('baseline-lib','claim-a')[0]['name']=='annotation_boundary_probe::left::alpha'
assert marker('moved-lib','claim-a')[0]['name']=='annotation_boundary_probe::relocated::alpha'
assert charon['baseline-lib']['source_sha256']==charon['baseline-selected']['source_sha256']==charon['baseline-tests']['source_sha256']
for v in ['baseline','proof-edit']:rc('cargo-observe-'+v,0)
def observation(v):
    m=re.fullmatch(r'len=(\d+) stamp=(\d+)\n',commands['cargo-observe-'+v]['stdout'])
    assert m,commands['cargo-observe-'+v]['stdout']
    return tuple(map(int,m.groups()))
a,b=observation('baseline'),observation('proof-edit')
assert a[0]!=b[0] and a[1]!=b[1]
assert sha(H/'artifacts/baseline.rmeta')!=sha(H/'artifacts/proof-edit.rmeta')
def verdict(label,id):
    xs=marker(label,id)
    return {'status':'missing' if len(xs)==0 else 'unique' if len(xs)==1 else 'ambiguous',
            'candidates':[{'def_id':x['id'],'name':x['name'],'span':x['span']} for x in xs]}
attachment={label:{id:verdict(label,id) for id in ['claim-a','claim-b','selected','test-only']}
            for label in ['baseline-lib','baseline-selected','baseline-tests','moved-lib','duplicated-lib']}
assert attachment['baseline-lib']['selected']['status']=='missing'
assert attachment['duplicated-lib']['claim-a']['status']=='ambiguous'
(H/'attachment-manifest.json').write_text(json.dumps(attachment,indent=2)+'\n')
subject=next(x for x in raw if x['kind']=='subject')
result={'status':'bounded assertions passed','events':len(raw),'raw_sha256':sha(H/'raw-results.json'),
        'probe_sha256':sha(H/'probe.py'),'tool_hashes':{k:v['sha256'] for k,v in subject['tools'].items()},
        'variant_hashes':subject['fixture_hashes'],'observation':{'baseline':a,'proof_edit':b},
        'rmeta_hashes':{v:sha(H/'artifacts'/f'{v}.rmeta') for v in ['baseline','proof-edit']},
        'charon_function_counts':{k:len(v['projection']['functions']) for k,v in charon.items() if v['projection']},
        'attachment_manifest_sha256':sha(H/'attachment-manifest.json')}
(H/'summary.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
