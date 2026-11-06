"""Meaningful pure-data controls. Never invokes a compiler, observer or fixture.
Synthetic ABI values are invented parser/comparison inputs, not rustc results.
"""
from pathlib import Path
import copy,contextlib,hashlib,io,json,sys
import e33_data as D
import e33_consumer as K
B=Path(__file__).resolve().parent
R=B/'pure-data-controls'
assert not R.exists();R.mkdir()
rows=[];attempted_capture_calls=[]
def blocked_capture(*args,**kwargs):
 attempted_capture_calls.append(True);raise RuntimeError('test must never invoke capture')
K.C.run_owned=blocked_capture
encode=lambda v:json.dumps(v,sort_keys=True,separators=(',',':')).encode()
def save(n,data):
 p=R/n;p.write_bytes(data);return D.sha(data)
def result(name,expected,fn,kind):
 try:value=fn();observed='pass';why=None
 except D.Reject as e:observed='reject';why=str(e)
 except SystemExit as e:observed='CLI-reject' if e.code==2 else 'unexpected-exit';why=str(e)
 row={'id':name,'kind':kind,'expected':expected,'observed':observed,'reason':why};rows.append(row)
 assert observed==expected,row

def arg():
 return {'type':'SYNTHETIC','type_debug':'SYNTHETIC','layout':{'size_bytes':1,'abi_align_bytes':1,'unadjusted_abi_align_bytes':1,'max_repr_align_bytes':None,'uninhabited':False,'backend_repr':{'kind':'scalar','scalar':{'kind':'initialized','primitive':{'kind':'integer','integer':'I8','signed':False},'valid_range_start':'0','valid_range_end':'255'}},'field_offsets_bytes':[],'fields_debug':'SYNTHETIC','variants_debug':'SYNTHETIC','largest_niche_debug':'SYNTHETIC','full_layout_debug':'SYNTHETIC'},'mode':{'kind':'direct','attrs':{'regular_bits':0,'regular_debug':'SYNTHETIC','extension':'None','pointee_size_bytes':0,'pointee_align_bytes':None}}}
def packet(r):
 p=r['profile'];selected=[]
 for s in r['selections']:
  identity={'instance_kind':'Item(SYNTHETIC)','arguments_debug':'SYNTHETIC','declared_signature_debug':'SYNTHETIC'} if s['query']=='instance' else {'function_pointer_type':'SYNTHETIC'}
  selected.append({'selection':copy.deepcopy(s),'resolved_definition':s['path'],'definition_kind':'Fn' if s['query']=='instance' else 'TyAlias','identity':identity,'fn_abi':{'args':[arg()],'ret':arg(),'c_variadic':False,'fixed_count':1,'canonical_convention':'SYNTHETIC','can_unwind':False}})
 return {'schema':'e33-proposed-observation-v1','crate_name':p['crate_name'],'target_spec_debug':'SYNTHETIC; NO ACTUAL TARGET QUERY','target_triple_debug':'TargetTuple('+json.dumps(p['target'])+')','target_cpu':'Some('+json.dumps(p['target_cpu'])+')','target_features':p['target_features'],'opt_level':{0:'No',2:'More'}[p['optimization']],'incremental_enabled':False,'effective_cfg':[],'source_files':[{'name':str(r['root']/p['source']['path']),'compiler_source':r['source']}],'external_crates':[],'selected':selected,'trust_frontier':'SYNTHETIC TEST DATA; NOT AN ACTUAL COMPILER OBSERVATION'}
requests={p:D.load_request(B,p) for p in ['host-subjects-opt0','host-subjects-opt2','host-vectors-opt0','host-vectors-opt2']}
for key,r in requests.items():
 v=packet(r);raw=encode(v);save('synthetic-'+key+'.json',raw)
 result('synthetic-equality-'+key,'pass',lambda raw=raw,r=r:D.compare_data(raw,raw,r),'synthetic grammar/equality only')
r=requests['host-subjects-opt0'];base=packet(r);reference=encode(base)
def mutate(name,fn):
 v=copy.deepcopy(base);fn(v);data=encode(v);digest=save('mutant-'+name+'.json',data)
 result(name,'reject',lambda:D.compare_data(data,reference,r),'synthetic candidate mutation');rows[-1]['candidate_sha256']=digest
mutate('producer-request-substitution',lambda v:v.update(request={'target':'different'}))
mutate('wrong-target',lambda v:v.update(target_triple_debug='TargetTuple("x86_64-pc-windows-msvc")'))
mutate('wrong-CPU',lambda v:v.update(target_cpu='Some("other")'))
mutate('wrong-options',lambda v:v.update(opt_level='More'))
mutate('source-byte-substitution',lambda v:v['source_files'][0].update(compiler_source=v['source_files'][0]['compiler_source']+'\n//changed\n'))
mutate('source-path-substitution',lambda v:v['source_files'][0].update(name='different.rs'))
mutate('omitted-selection',lambda v:v['selected'].pop())
mutate('reordered-root',lambda v:v['selected'].reverse())
mutate('wrong-instance',lambda v:v['selected'][20]['selection'].update(type_args=['u64']))
mutate('wrong-resolved-root',lambda v:v['selected'][0].update(resolved_definition='abi_subjects::decoy'))
mutate('wrong-attribute-bits',lambda v:v['selected'][0]['fn_abi']['args'][0]['mode']['attrs'].update(regular_bits=8))
mutate('wrong-pointee-size',lambda v:v['selected'][0]['fn_abi']['args'][0]['mode']['attrs'].update(pointee_size_bytes=8))
mutate('wrong-extension',lambda v:v['selected'][0]['fn_abi']['args'][0]['mode']['attrs'].update(extension='Sext'))
mutate('wrong-return-mode',lambda v:v['selected'][0]['fn_abi']['ret'].update(mode={'kind':'ignore'}))
mutate('omitted-argument',lambda v:v['selected'][0]['fn_abi'].update(args=[]))
mutate('wrong-fixed-count',lambda v:v['selected'][0]['fn_abi'].update(fixed_count=0))
mutate('wrong-unwind',lambda v:v['selected'][0]['fn_abi'].update(can_unwind=True))
mutate('opaque-layout-difference',lambda v:v['selected'][0]['fn_abi']['ret']['layout'].update(full_layout_debug='DIFFERENT'))
mutate('unknown-nested-key',lambda v:v['selected'][0]['fn_abi']['ret']['layout'].update(ignored=True))
mutate('unknown-mode',lambda v:v['selected'][0]['fn_abi']['ret'].update(mode={'kind':'trusted-bypass'}))
mutate('bool-as-integer',lambda v:v['selected'][0]['fn_abi']['ret']['layout'].update(size_bytes=True))
mutate('wrong-alignment-grammar',lambda v:v['selected'][0]['fn_abi']['ret']['layout'].update(abi_align_bytes=3))
mutate('u128-range-overflow',lambda v:v['selected'][0]['fn_abi']['ret']['layout']['backend_repr']['scalar'].update(valid_range_end=str(2**128)))
mutate('non-ASCII-range',lambda v:v['selected'][0]['fn_abi']['ret']['layout']['backend_repr']['scalar'].update(valid_range_end='١'))
mutate('leading-zero-range',lambda v:v['selected'][0]['fn_abi']['ret']['layout']['backend_repr']['scalar'].update(valid_range_end='01'))
raw_cases={'duplicate-key':b'{"x":0,"x":1}','nested-duplicate':b'{"x":{"a":1,"a":2}}','invalid-UTF8':b'\xff','depth-limit':b'['*65+b'0'+b']'*65,'byte-limit':b' '* (D.MAX_BYTES+1),'integer-token-limit':b'1'*41,'float-token':b'0.0','NaN-token':b'NaN','infinity-token':b'Infinity','truncated':b'{"x":','suffix':b'{}garbage','empty':b'','UTF8-BOM':b'\xef\xbb\xbf{}'}
for name,data in raw_cases.items():
 result(name,'reject',lambda data=data:D.parse(data),'strict parser');rows[-1]['input_sha256']=D.sha(data)
result('unknown-consumer-profile','reject',lambda:D.load_request(B,'producer-chosen-root'),'fixed caller preflight')
for kind in ['authority','catalog','source','selectors']:
 root=R/('substitution-'+kind);root.mkdir()
 if kind=='authority':
  a=json.loads((B/'consumer-authority.json').read_text());a['profile_ids'].append('producer-chosen-root');(root/'consumer-authority.json').write_text(json.dumps(a))
 else:
  names=[x['path'] for x in json.loads((B/'prepared-manifest.json').read_text())['files']]+['prepared-manifest.json','consumer-authority.json']
  for name in names:(root/name).write_bytes((B/name).read_bytes())
  target={'catalog':'requests.json','source':'subjects.rs','selectors':'selectors-subjects.json'}[kind]
  (root/target).write_bytes((root/target).read_bytes()+b'\n ')
 result('modified-'+kind+'-preflight','reject',lambda root=root:D.load_request(root,'host-subjects-opt0'),'fixed caller preflight')
# Grammar branches only: both sides are deliberately synthetic and changed alike.
variants=[{'kind':'ignore'},{'kind':'pair','first':arg()['mode']['attrs'],'second':arg()['mode']['attrs']},{'kind':'indirect','attrs':arg()['mode']['attrs'],'meta_attrs':arg()['mode']['attrs'],'on_stack':False},{'kind':'cast','pad_i32':False,'prefix':[None]*8,'rest_offset_bytes':None,'rest_unit':{'kind':'Integer','size_bytes':8},'rest_total_bytes':16,'rest_is_consecutive':True,'attrs':arg()['mode']['attrs']}]
for i,mode in enumerate(variants):
 v=copy.deepcopy(base);v['selected'][0]['fn_abi']['ret']['mode']=mode;data=encode(v)
 result('synthetic-mode-grammar-'+str(i),'pass',lambda data=data:D.compare_data(data,data,r),'synthetic grammar branch only')
# Query source preserves nonvariadic track_caller hidden count: allow the shape,
# with no assertion that this invented packet is the real tracked-function ABI.
v=copy.deepcopy(base);v['selected'][0]['fn_abi']['args'].append(arg());data=encode(v)
result('synthetic-nonvariadic-extra-hidden-shape','pass',lambda:D.compare_data(data,data,r),'synthetic grammar branch only')
old=sys.argv
try:
 sys.argv=['e33_consumer.py','preflight','--toolchain','unused','--profile','host-subjects-opt0','--producer-request','bad']
 with contextlib.redirect_stderr(io.StringIO()):result('unknown-CLI-flag','CLI-reject',K.main,'CLI grammar; no observer call')
 sys.argv=['e33_consumer.py','preflight','--toolchain','unused','--profile','host-subjects-opt0','--pro','bad']
 with contextlib.redirect_stderr(io.StringIO()):result('abbreviated-CLI-flag','CLI-reject',K.main,'CLI grammar; no observer call')
finally:sys.argv=old
assert not attempted_capture_calls
summary={'status':'PASS','case_count':len(rows),'outcomes':{x:sum(row['observed']==x for row in rows) for x in ['pass','reject','CLI-reject']},'observer_or_compiler_invocations':0,'meaning':'Synthetic schema/comparison and immutable preflight controls only. No invented ABI data was claimed as actual captured or accepted compiler evidence. Fresh-capture consumer mode remains unexecuted.','sources_sha256':{n:D.sha((B/n).read_bytes()) for n in ['e33_data.py','e33_consumer.py','test_pure_data.py']},'results':rows}
(R/'results.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps({k:v for k,v in summary.items() if k!='results'},indent=2))
