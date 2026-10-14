#!/usr/bin/env python3
"""Exact selected artifact admission, with explicit projection/unit/operation inventory.
It is a pinned specimen decoder, not a general Charon parser or Rust semantics proof.
"""
import copy, hashlib, json, pathlib
HERE=pathlib.Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((HERE/'capture-identities.json').read_text())
for n,record in manifest['generated_files'].items():
    assert sha(HERE/n)==record['preserved_sha256']
assert sha(HERE/'probe.rs')==manifest['source_sha256']
def admit(path,expected):
    assert sha(path)==expected, 'consumer-selected full specimen identity differs'
    return json.loads(path.read_text())
raw=admit(HERE/'selected-update.ullbc.json',manifest['selected_raw_decl_sha256'])
final=admit(HERE/'selected-update.llbc.json',manifest['selected_final_decl_sha256'])
assert final['def_id']==1 and final['item_meta']['name'][-1]=={'Ident':['update_second',0]}
assert final['signature']['is_unsafe'] is False and final['signature']['abi']=='Rust'
assert final['src']=='TopLevel' and final['is_global_initializer'] is None
b=final['body']['Structured'];assert b['bound_body_regions']==2 and b['locals']['arg_count']==2
assert len(b['locals']['locals'])==4 and [l['index'] for l in b['locals']['locals']]==list(range(4))
ss=b['body']['statements'];assert len(ss)==7
assert ss[1]['kind']=={'StorageLive':3} and ss[4]['kind']=={'StorageDead':3} and ss[6]['kind']=='Return'
unit=ss[0]['kind']['Assign'];assert ss[5]['kind']['Assign']==unit
assert unit[0]['kind']=={'Local':0} and unit[1]['Aggregate'][1]==[]
assert unit[1]['Aggregate'][0]['Adt'][0]['id']=='Tuple'
assert unit[1]['Aggregate'][0]['Adt'][0]['generics']['types']==[]
copyop=ss[2]['kind']['Assign'];assert copyop[0]['kind']=={'Local':3}
assert copyop[1]['Use'][1]=='Yes' and copyop[1]['Use'][0]['Copy']['kind']=={'Local':2}
write=ss[3]['kind']['Assign'];projection=write[0]['kind']['Projection']
assert projection[1]=={'Field':[{'Tuple':2},1]}
deref=projection[0]['kind']['Projection'];assert deref[1]=='Deref' and deref[0]['kind']=={'Local':1}
assert write[1]['Use'][1]=='Yes' and write[1]['Use'][0]['Move']['kind']=={'Local':3}
rawss=raw['body']['Unstructured']['body'][0]['statements']
assert len(raw['body']['Unstructured']['body'])==1 and len(rawss)==6
assert rawss[0]['kind']==ss[0]['kind'] # raw serialized export already has entry unit.
assert [x['kind'] for x in rawss[1:5]]==[x['kind'] for x in ss[1:5]]
assert rawss[5]['kind']['Assign'][1]['Use'][0]['Const']['kind']=={'Adt':[None,[]]}
assert raw['body']['Unstructured']['body'][0]['terminator']['kind']=='Return'
text=(HERE/'CapturedFuns.lean').read_text()
for name,record in manifest['definition_bodies'].items(): assert record['text'] in text
# Changed field is still syntactically plausible, but differs from the selected data.
mut=copy.deepcopy(final);mut['body']['Structured']['body']['statements'][3]['kind']['Assign'][0]['kind']['Projection'][1]['Field'][1]=0
assert mut!=final
(HERE/'wrong-field.llbc.json').write_text(json.dumps(mut,indent=2)+'\n')
try: admit(HERE/'wrong-field.llbc.json',manifest['selected_final_decl_sha256'])
except AssertionError: pass
else: raise AssertionError('wrong field admitted')
print(json.dumps({'accepted':True,'exact_specimens':True,'operation_order':['unit:0','live:3','copy:2:3','write:deref-1:field-1:move-3','dead:3','unit:0','return:0'],'wrong_field_fingerprint_rejected':True,'trust':'Python exact-data/definition capture; Rust import and exclusive permission remain assumed'}))
