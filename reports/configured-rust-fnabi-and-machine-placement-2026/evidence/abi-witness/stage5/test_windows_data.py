"""Windows closed bindings/grammar controls only; no observer/compiler/fixture call.
Every positive packet below is SYNTHETIC, never a Windows FnAbi observation.
"""
from pathlib import Path
import copy,contextlib,io,json,sys
from unittest.mock import patch
import e33_data_windows as D
import e33_consumer_windows as K
S=Path(__file__).resolve().parent;B=S.parent
T=B.parent/'toolchains/rustup/toolchains/nightly-2026-05-01-aarch64-apple-darwin'
R=S/'windows-pure-data-controls';assert not R.exists();R.mkdir()
rows=[];calls=[]
def forbidden(*args,**kwargs):calls.append(True);raise RuntimeError('test forbidden compiler/observer invocation')
K.C.run_owned=forbidden
encode=lambda v:json.dumps(v,sort_keys=True,separators=(',',':')).encode()
def result(name,expected,fn,kind):
 try:fn();observed='pass';why=None
 except D.Reject as e:observed='reject';why=str(e)
 except SystemExit as e:observed='CLI-reject' if e.code==2 else 'unexpected-exit';why=str(e)
 row={'id':name,'kind':kind,'expected':expected,'observed':observed,'reason':why};rows.append(row)
 assert expected==observed,row

def arg():
 return {'type':'SYNTHETIC','type_debug':'SYNTHETIC','layout':{'size_bytes':1,'abi_align_bytes':1,'unadjusted_abi_align_bytes':1,'max_repr_align_bytes':None,'uninhabited':False,'backend_repr':{'kind':'scalar','scalar':{'kind':'initialized','primitive':{'kind':'integer','integer':'I8','signed':False},'valid_range_start':'0','valid_range_end':'255'}},'field_offsets_bytes':[],'fields_debug':'SYNTHETIC','variants_debug':'SYNTHETIC','largest_niche_debug':'SYNTHETIC','full_layout_debug':'SYNTHETIC'},'mode':{'kind':'direct','attrs':{'regular_bits':0,'regular_debug':'SYNTHETIC','extension':'None','pointee_size_bytes':0,'pointee_align_bytes':None}}}
def packet(r):
 p=r['profile'];selected=[]
 for s in r['selections']:
  identity={'instance_kind':'Item(SYNTHETIC)','arguments_debug':'SYNTHETIC','declared_signature_debug':'SYNTHETIC'} if s['query']=='instance' else {'function_pointer_type':'SYNTHETIC'}
  selected.append({'selection':copy.deepcopy(s),'resolved_definition':s['path'],'definition_kind':'Fn' if s['query']=='instance' else 'TyAlias','identity':identity,'fn_abi':{'args':[arg()],'ret':arg(),'c_variadic':False,'fixed_count':1,'canonical_convention':'SYNTHETIC','can_unwind':False}})
 return {'schema':'e33-proposed-observation-v1','crate_name':p['crate_name'],'target_spec_debug':'SYNTHETIC; NO ACTUAL TARGET QUERY','target_triple_debug':'TargetTuple('+json.dumps(p['target'])+')','target_cpu':'Some('+json.dumps(p['target_cpu'])+')','target_features':p['target_features'],'opt_level':'More','incremental_enabled':False,'effective_cfg':[],'source_files':[{'name':str(r['root']/p['source']['path']),'compiler_source':r['source']}],'external_crates':[],'selected':selected,'trust_frontier':'SYNTHETIC PARSER DATA; NOT ACTUAL WINDOWS COMPILER OUTPUT'}
r=D.load_request(B,'windows-subjects-opt2');base=packet(r);reference=encode(base)
(R/'synthetic-only.json').write_bytes(reference)
result('synthetic-equality','pass',lambda:D.compare_data(reference,reference,r),'synthetic grammar/equality')
result('readonly-actual-installed-tool-preflight','pass',lambda:K.preflight(T,'windows-subjects-opt2'),'hash reads only; no compiler query')
def mutate(name,fn):
 v=copy.deepcopy(base);fn(v);data=encode(v);(R/('mutant-'+name+'.json')).write_bytes(data)
 result(name,'reject',lambda:D.compare_data(data,reference,r),'synthetic candidate mutation');rows[-1]['input_sha256']=D.sha(data)
mutate('producer-request',lambda v:v.update(request={'target':'other'}))
mutate('host-target',lambda v:v.update(target_triple_debug='TargetTuple("aarch64-apple-darwin")'))
mutate('host-CPU',lambda v:v.update(target_cpu='Some("apple-m1")'))
mutate('stale-optimization',lambda v:v.update(opt_level='No'))
mutate('extra-target-features',lambda v:v.update(target_features='+avx'))
mutate('changed-source',lambda v:v['source_files'][0].update(compiler_source=v['source_files'][0]['compiler_source']+'//changed'))
mutate('changed-source-path',lambda v:v['source_files'][0].update(name='other.rs'))
mutate('omitted-selection',lambda v:v['selected'].pop())
mutate('reordered-selection',lambda v:v['selected'].reverse())
mutate('unqualified-name',lambda v:v['selected'][0]['selection'].update(path='abi_c_narrow'))
mutate('wrong-generic-instance',lambda v:v['selected'][20]['selection'].update(type_args=['u64']))
mutate('changed-attribute',lambda v:v['selected'][0]['fn_abi']['args'][0]['mode']['attrs'].update(regular_bits=8))
mutate('changed-extension',lambda v:v['selected'][0]['fn_abi']['args'][0]['mode']['attrs'].update(extension='Sext'))
mutate('changed-opaque-layout',lambda v:v['selected'][0]['fn_abi']['ret']['layout'].update(full_layout_debug='OTHER'))
mutate('changed-range',lambda v:v['selected'][0]['fn_abi']['ret']['layout']['backend_repr']['scalar'].update(valid_range_end='254'))
mutate('unknown-nested-key',lambda v:v['selected'][0]['fn_abi']['ret']['layout'].update(ignored=True))
mutate('unknown-mode',lambda v:v['selected'][0]['fn_abi']['ret'].update(mode={'kind':'trusted-bypass'}))
mutate('bool-integer',lambda v:v['selected'][0]['fn_abi']['ret']['layout'].update(size_bytes=True))
mutate('bad-alignment',lambda v:v['selected'][0]['fn_abi']['ret']['layout'].update(abi_align_bytes=3))
mutate('oversized-u128',lambda v:v['selected'][0]['fn_abi']['ret']['layout']['backend_repr']['scalar'].update(valid_range_end=str(2**128)))
mutate('unicode-u128',lambda v:v['selected'][0]['fn_abi']['ret']['layout']['backend_repr']['scalar'].update(valid_range_end='١'))
mutate('leading-zero-u128',lambda v:v['selected'][0]['fn_abi']['ret']['layout']['backend_repr']['scalar'].update(valid_range_end='01'))
mutate('omitted-argument',lambda v:v['selected'][0]['fn_abi'].update(args=[]))
mutate('wrong-hidden-count',lambda v:v['selected'][0]['fn_abi'].update(fixed_count=0))
mutate('wrong-unwind',lambda v:v['selected'][0]['fn_abi'].update(can_unwind=True))
raws={'duplicate':b'{"x":0,"x":1}','nested-duplicate':b'{"x":{"x":0,"x":1}}','invalidUTF8':b'\xff','depth':b'['*65+b'0'+b']'*65,'bytes':b' '*(D.MAX_BYTES+1),'integer-token':b'1'*41,'float':b'0.0','NaN':b'NaN','infinity':b'Infinity','truncated':b'{"x":','suffix':b'{}garbage','empty':b'','BOM':b'\xef\xbb\xbf{}'}
for name,data in raws.items():
 result(name,'reject',lambda data=data:D.parse(data),'strict parser');rows[-1]['input_sha256']=D.sha(data)
for profile in ['host-subjects-opt0','host-subjects-opt2','host-vectors-opt0','host-vectors-opt2','producer-root']:
 result('reject-profile-'+profile,'reject',lambda profile=profile:D.load_request(B,profile),'closed caller catalog')
# Read substitution is test-only. The production modules/inputs are unchanged.
original=D.read
for name,p in [('authority',S/'consumer-authority-windows.json'),('Windows-catalog',S/'requests-windows.json'),('historical-catalog',B/'requests.json'),('source',B/'subjects.rs'),('selectors',B/'selectors-subjects.json'),('target-identities',S/'windows-target-identities.json'),('observer-source',B/'observer_v3.rs'),('observer-binary',B/'observer-v3')]:
 changed=original(p)+b' '
 def altered(path,p=p,changed=changed):return changed if Path(path)==p else original(path)
 with patch.object(D,'read',altered):result('reject-replaced-'+name,'reject',lambda:D.load_request(B,'windows-subjects-opt2'),'fixed digest preflight; test read substitution only')
# Same scalar/mode branches as host grammar; invented data on both sides.
variants=[{'kind':'ignore'},{'kind':'pair','first':arg()['mode']['attrs'],'second':arg()['mode']['attrs']},{'kind':'indirect','attrs':arg()['mode']['attrs'],'meta_attrs':arg()['mode']['attrs'],'on_stack':False},{'kind':'cast','pad_i32':False,'prefix':[None]*8,'rest_offset_bytes':None,'rest_unit':{'kind':'Integer','size_bytes':8},'rest_total_bytes':16,'rest_is_consecutive':True,'attrs':arg()['mode']['attrs']}]
for i,mode in enumerate(variants):
 v=copy.deepcopy(base);v['selected'][0]['fn_abi']['ret']['mode']=mode;data=encode(v)
 result('synthetic-mode-'+str(i),'pass',lambda data=data:D.compare_data(data,data,r),'synthetic grammar branch')
v=copy.deepcopy(base);v['selected'][0]['fn_abi']['args'].append(arg());data=encode(v)
result('synthetic-nonvariadic-hidden-shape','pass',lambda:D.compare_data(data,data,r),'synthetic grammar branch')
actual_host=B/'stage4/runs/capture-subjects-o2/reference.json'
result('actual-host-packet-not-Windows-root','reject',lambda:D.validate_observation(D.parse(actual_host.read_bytes()),r),'actual old host DATA rejected; no new observation')
old=sys.argv
try:
 for tail in [['--producer-request','bad'],['--pro','bad'],['--reference','bad']]:
  sys.argv=['e33_consumer_windows.py','preflight','--toolchain',str(T),'--profile','windows-subjects-opt2']+tail
  with contextlib.redirect_stderr(io.StringIO()):result('CLI-'+tail[0],'CLI-reject',K.main,'closed CLI; no observer')
 sys.argv=['e33_consumer_windows.py','preflight','--toolchain',str(T),'--profile','host-subjects-opt2']
 with contextlib.redirect_stderr(io.StringIO()):result('CLI-host-profile','CLI-reject',K.main,'closed CLI; no observer')
finally:sys.argv=old
assert not calls
summary={'status':'PASS','case_count':len(rows),'outcomes':{x:sum(z['observed']==x for z in rows) for x in ['pass','reject','CLI-reject']},'compiler_or_observer_invocations':0,'fixture_execution_count':0,'effective_request_sha256':r['effective_request_sha256'],'scope':'Synthetic grammar/comparison + readonly actual installed-file preflight only. NO actual Windows FnAbi, IR, assembly or COFF result.','sources_sha256':{x:D.sha((S/x).read_bytes()) for x in ['e33_data_windows.py','e33_consumer_windows.py','test_windows_data.py']},'results':rows}
with (R/'results.json').open('x') as f:json.dump(summary,f,indent=2);f.write('\n')
print(json.dumps({k:v for k,v in summary.items() if k!='results'},indent=2))
