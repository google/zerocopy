#!/usr/bin/env python3
"""Read-only replay of ASCII-local Charon span/source-text intervals."""
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
META=json.loads((HERE.parent/'REPORT.json').read_text())
RECORD=json.loads((HERE/'comparison.json').read_text())
RESULTS=json.loads((HERE/'source-results.json').read_text())
def sha(raw):return hashlib.sha256(raw).hexdigest()
def file_sha(path):return sha(path.read_bytes())
source_id=META['subjects'][0]['identity'];compare_id=META['subjects'][1]['identity']
assert source_id['reference_revision']=='974c035a2a32b8b873ad560b572eeda7a69679bb'
for field,path in (('source_report_sha256','source-report.md'),('source_probe_sha256','source-probe.py'),
                   ('source_results_sha256','source-results.json'),('baseline_source_sha256','source-states/baseline.rs'),
                   ('edited_source_sha256','source-states/edited.rs')):
    assert source_id[field]==file_sha(HERE/path)
source_meta=json.loads((HERE/'source-report.json').read_text())
assert source_meta['subjects'][2]['identity']['probe_sha256']==file_sha(HERE/'source-probe.py')
assert source_id['source_results_sha256']=='e1f8ac94a2bda6f93ca21d11c8fae4c6030bd2f9a9ac5491d2e4b36f981e1d4a'
assert compare_id['compare_sha256']==file_sha(HERE/'compare.py')
assert compare_id['comparison_sha256']==file_sha(HERE/'comparison.json')
assert compare_id['source_results_sha256']==RECORD['source_results_sha256']==file_sha(HERE/'source-results.json')
assert RECORD['status']=='completed'
assert RECORD['limits']=={'max_rss_bytes':64*1024**2,'max_seconds':5.0,'min_reclaimable_percent':20.0}
assert RECORD['elapsed_seconds']<=5 and RECORD['peak_rss_bytes']<=64*1024**2
assert len(RECORD['samples'])==34 and RECORD['samples'][0]['label']=='preflight-before-input'
assert all(s['reclaimable_percent']>20 and s['max_rss_bytes']<=64*1024**2 and s['elapsed_seconds']<=5 for s in RECORD['samples'])
assert 'underdetermined' in RECORD['span_interpretation']['column_unit']
base=(HERE/'source-states/baseline.rs').read_bytes();edited=(HERE/'source-states/edited.rs').read_bytes()
assert base.isascii() and edited.isascii()
assert base.count(b'x.wrapping_add(1)')==1 and edited==base.replace(b'x.wrapping_add(1)',b'x.wrapping_add(2)')
states={sha(base):base,sha(edited):edited}
assert RECORD['source_state_sha256']=={'baseline':sha(base),'edited':sha(edited)}
expected={}
for c in RESULTS['cells']:
    assert c['incremental'] in (0,1) and c['baseline_sha256']==sha(base) and c['edited_sha256']==sha(edited)
    for state,run in c['oracle'].items():
        assert state in ('baseline','edited')
        expected[run['label']]=run
    for ph in c['phases']:
        for root,run in ph['runs'].items():
            assert root in ('A','B') and run['source_sha256']==ph['source_hashes'][root]
            expected[run['label']]=run
assert len(expected)==16 and set(RECORD['artifacts'])==set(expected)
assert {p.stem for p in (HERE/'artifacts').glob('*.llbc')}==set(expected)
matched=excluded=0
for label,run in expected.items():
    raw=(HERE/'artifacts'/f'{label}.llbc').read_bytes()
    record=RECORD['artifacts'][label]
    assert sha(raw)==record['llbc_sha256']==run['output']['sha256'] and len(raw)==run['output']['bytes']
    source=states[run['source_sha256']]
    assert record['source_state_sha256']==sha(source)
    doc=json.loads(raw)
    assert doc['translated']['crate_name']=='warm_probe' and doc['has_errors'] is False
    files={f['id']:f for f in doc['translated']['files']}
    assert files[0]['name']=={'Local':'app/src/lib.rs'} and files[0]['contents'].encode('utf-8')==source
    observed=[];skipped=[]
    for category in ('type_decls','fun_decls','global_decls','trait_decls','trait_impls'):
        for decl in doc['translated'][category]:
            meta=decl.get('item_meta') or {}
            span=(meta.get('span') or {}).get('data')
            if not meta.get('is_local') or span is None:continue
            name='::'.join(part['Ident'][0] for part in meta['name'] if 'Ident' in part)
            if span['file_id']!=0:
                skipped.append({'category':category,'name':name,'file_id':span['file_id'],
                    'reason':'no independent retained generated Rust state for this file'})
                continue
            assert category=='fun_decls' and span['beg']['line']==span['end']['line']
            line=source.splitlines(keepends=True)[span['beg']['line']-1]
            start,end=span['beg']['col'],span['end']['col']
            assert 0<=start<end<=len(line)
            selected=line[start:end]
            assert selected.isascii() and selected.decode('utf-8')==meta['source_text']
            observed.append({'category':category,'name':name,'def_id':decl['def_id'],
                'span':span,'source_text_sha256':sha(selected),'source_text':meta['source_text'],
                'source_state_sha256':run['source_sha256']})
    assert observed==record['local_ascii_items'] and skipped==record['excluded_generated_local_items']
    assert len(observed)==4 and len(skipped)==2
    matched+=len(observed);excluded+=len(skipped)
    step=next(x for x in observed if x['name']=='warm_probe::step')['source_text']
    assert ('wrapping_add(2)' in step)==(run['source_sha256']==sha(edited))
assert (matched,excluded)==(64,32)
for inc in (0,1):
    assert RECORD['artifacts'][f'inc{inc}-edited-A']['source_state_sha256']==sha(edited)
    for phase in ('baseline','reverted'):
        assert RECORD['artifacts'][f'inc{inc}-{phase}-A']['source_state_sha256']==sha(base)
    for phase in ('baseline','edited','reverted'):
        assert RECORD['artifacts'][f'inc{inc}-{phase}-B']['source_state_sha256']==sha(base)
control=RECORD['negative_controls']
assert all(control.values())
item=RECORD['artifacts']['inc0-baseline-A']['local_ascii_items'][0]
line=base.splitlines(keepends=True)[item['span']['beg']['line']-1]
a=item['span']['beg']['col'];b=item['span']['end']['col'];target=item['source_text'].encode()
assert line[a:b]==target and line[a+1:b]!=target and line[a:b+1]!=target
print('PASS: 16 raw hashes, two source states, 64 ASCII-local span matches, 32 explicit exclusions and offset controls')
