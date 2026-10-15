"""Closed finite ABI data grammar and caller-bound comparison, not ABI semantics.
A reference argument is a trusted consumer-owned observation premise. Only the
separate consumer obtains that reference by a fresh reviewed observer invocation.
Synthetic tests below this boundary do not establish any actual FnAbi result.
"""
from pathlib import Path
import hashlib,json
AUTHORITY_SHA256='d9b0b86788625c0d9f23c4662a39708c587fa6a34ea21e8790e5f26532700078'
MAX_BYTES=4*1024*1024
MAX_DEPTH=64
class Reject(ValueError):pass
def require(test,why):
 if not test:raise Reject(why)
def sha(data):return hashlib.sha256(data).hexdigest()
def read(path):
 p=Path(path);require(p.is_file() and not p.is_symlink(),'regular nonsymlink input required')
 require(p.stat().st_size<=MAX_BYTES,'input byte limit');return p.read_bytes()
def pairs(ps):
 d={}
 for k,v in ps:
  require(k not in d,'duplicate key');d[k]=v
 return d
def parse(data):
 require(type(data) is bytes and len(data)<=MAX_BYTES,'input byte limit/type')
 try:s=data.decode('utf-8')
 except UnicodeDecodeError as e:raise Reject('invalid UTF8') from e
 # Bound nesting before handing data to recursive JSON parsing. Strings/escapes
 # are scanned, but grammar correctness remains the strict JSON decoder's job.
 depth=0;inside=False;escaped=False
 for c in s:
  if inside:
   if escaped:escaped=False
   elif c=='\\':escaped=True
   elif c=='"':inside=False
  elif c=='"':inside=True
  elif c in '[{':depth+=1;require(depth<=MAX_DEPTH,'nesting limit')
  elif c in ']}':depth-=1
 def integer(x):require(len(x)<=40,'integer token limit');return int(x)
 def no_float(x):raise Reject('floating/NaN/infinite JSON tokens outside grammar')
 try:return json.loads(s,object_pairs_hook=pairs,parse_int=integer,parse_float=no_float,parse_constant=no_float)
 except (json.JSONDecodeError,RecursionError) as e:raise Reject('malformed JSON') from e
def obj(v,keys):require(type(v) is dict and set(v)==set(keys),'object closed keys: '+str(keys))
def string(v,n=65536):require(type(v) is str and len(v)<=n,'bounded string')
def boolean(v):require(type(v) is bool,'boolean')
def integer(v,hi=65536):require(type(v) is int and 0<=v<=hi,'bounded unsigned integer')
def array(v,n=64):require(type(v) is list and len(v)<=n,'bounded array')
def align(v,nullable=False):
 if v is None and nullable:return
 integer(v,1048576);require(v>0 and v&(v-1)==0,'power-of-two alignment')
def uint128_string(v):
 string(v,39);require(v=='0' or (v.isascii() and v.isdigit() and not v.startswith('0')),'canonical unsigned decimal')
 require(int(v)<2**128,'u128 bound')
def primitive(v):
 require(type(v) is dict and 'kind' in v,'primitive tag')
 if v['kind']=='integer':
  obj(v,['kind','integer','signed']);require(v['integer'] in ['I8','I16','I32','I64','I128'],'integer kind');boolean(v['signed'])
 elif v['kind']=='float':
  obj(v,['kind','float']);require(v['float'] in ['F16','F32','F64','F128'],'float kind')
 elif v['kind']=='pointer':obj(v,['kind','address_space']);string(v['address_space'],256)
 else:raise Reject('primitive tag')
def scalar(v):
 require(type(v) is dict and 'kind' in v,'scalar tag')
 if v['kind']=='initialized':
  obj(v,['kind','primitive','valid_range_start','valid_range_end']);primitive(v['primitive']);uint128_string(v['valid_range_start']);uint128_string(v['valid_range_end'])
 elif v['kind']=='union':obj(v,['kind','primitive','valid_range']);primitive(v['primitive']);require(v['valid_range'] is None,'union range must be null')
 else:raise Reject('scalar tag')
def representation(v):
 require(type(v) is dict and 'kind' in v,'representation tag')
 if v['kind']=='scalar':obj(v,['kind','scalar']);scalar(v['scalar'])
 elif v['kind']=='scalar_pair':obj(v,['kind','first','second']);scalar(v['first']);scalar(v['second'])
 elif v['kind']=='simd_vector':obj(v,['kind','element','count']);scalar(v['element']);integer(v['count'],64);require(v['count']>0,'positive vector count')
 elif v['kind']=='memory':obj(v,['kind','sized']);boolean(v['sized'])
 else:raise Reject('representation tag outside fixed grammar')
def attrs(v):
 obj(v,['regular_bits','regular_debug','extension','pointee_size_bytes','pointee_align_bytes'])
 integer(v['regular_bits'],511);string(v['regular_debug'],2048);require(v['extension'] in ['None','Zext','Sext'],'extension');integer(v['pointee_size_bytes']);align(v['pointee_align_bytes'],True)
def reg(v):obj(v,['kind','size_bytes']);string(v['kind'],2048);integer(v['size_bytes'],256);require(v['size_bytes']>0,'positive register size')
def mode(v):
 require(type(v) is dict and 'kind' in v,'passing mode tag')
 if v['kind']=='ignore':obj(v,['kind'])
 elif v['kind']=='direct':obj(v,['kind','attrs']);attrs(v['attrs'])
 elif v['kind']=='pair':obj(v,['kind','first','second']);attrs(v['first']);attrs(v['second'])
 elif v['kind']=='indirect':
  obj(v,['kind','attrs','meta_attrs','on_stack']);attrs(v['attrs']);boolean(v['on_stack'])
  if v['meta_attrs'] is not None:attrs(v['meta_attrs'])
 elif v['kind']=='cast':
  obj(v,['kind','pad_i32','prefix','rest_offset_bytes','rest_unit','rest_total_bytes','rest_is_consecutive','attrs'])
  boolean(v['pad_i32']);array(v['prefix'],8);require(len(v['prefix'])==8,'eight cast prefix slots')
  for x in v['prefix']:
   if x is not None:reg(x)
  if v['rest_offset_bytes'] is not None:integer(v['rest_offset_bytes'])
  reg(v['rest_unit']);integer(v['rest_total_bytes']);boolean(v['rest_is_consecutive']);attrs(v['attrs'])
 else:raise Reject('passing mode outside grammar')
def argument(v):
 obj(v,['type','type_debug','layout','mode']);string(v['type']);string(v['type_debug']);mode(v['mode'])
 z=v['layout'];obj(z,['size_bytes','abi_align_bytes','unadjusted_abi_align_bytes','max_repr_align_bytes','uninhabited','backend_repr','field_offsets_bytes','fields_debug','variants_debug','largest_niche_debug','full_layout_debug'])
 integer(z['size_bytes']);align(z['abi_align_bytes']);align(z['unadjusted_abi_align_bytes']);align(z['max_repr_align_bytes'],True);boolean(z['uninhabited']);representation(z['backend_repr'])
 array(z['field_offsets_bytes'])
 for x in z['field_offsets_bytes']:integer(x)
 for k in ['fields_debug','variants_debug','largest_niche_debug','full_layout_debug']:string(z[k])
def abi(v):
 obj(v,['args','ret','c_variadic','fixed_count','canonical_convention','can_unwind']);array(v['args'],16)
 for x in v['args']:argument(x)
 argument(v['ret']);boolean(v['c_variadic']);integer(v['fixed_count'],16);require(v['fixed_count']<=len(v['args']),'fixed count cannot exceed emitted ABI arguments');string(v['canonical_convention'],1024);boolean(v['can_unwind'])
 # Do not require equal fixed_count/len for nonvariadic track_caller instances:
 # source construction appends caller_location after the fixed source inputs.
def selector(v):
 obj(v,['path','query','type_args','extra_args']);string(v['path'],1024);require(v['query'] in ['instance','fn_ptr'],'query mode');array(v['type_args'],1);array(v['extra_args'],3)
 for x in v['type_args']+v['extra_args']:require(x in ['u8','u32','u64','i32','f64','*const u8'],'finite type selector')
 require(v['query']!='instance' or v['extra_args']==[],'instance extras outside selection')
def load_request(root,request_id):
 root=Path(root).resolve();a=parse(read(root/'consumer-authority-v3.json'));require(sha(read(root/'consumer-authority-v3.json'))==AUTHORITY_SHA256,'consumer authority digest')
 require(request_id in a['profile_ids'],'unknown consumer request')
 mbytes=read(root/'prepared-manifest.json');require(sha(mbytes)==a['preparation_manifest_sha256'],'historical preparation digest')
 for f in parse(mbytes)['files']:
  p=root/f['path'];require(sha(read(p))==f['sha256'] and p.stat().st_size==f['bytes'],'historical input changed')
 cb=read(root/'requests.json');require(sha(cb)==a['historical_catalog_sha256'],'catalog digest');catalog=parse(cb)
 ps=[x for x in catalog['profiles'] if x['id']==request_id];require(len(ps)==1,'request uniqueness');p=ps[0]
 require(p['extra_flags']==[] and p['target']=='aarch64-apple-darwin' and p['edition']=='2021' and p['optimization'] in [0,2] and not p['incremental'] and p['panic']=='abort' and p['target_cpu']=='apple-m1' and p['target_features']=='' and p['compiler_threads']==p['codegen_units']==1,'finite fixed caller profile')
 for k in ['source','selectors']:require(sha(read(root/p[k]['path']))==p[k]['sha256'],'fixed selected input changed')
 selections=parse(read(root/p['selectors']['path']));obj(selections,['schema','selections']);require(selections['schema']=='e33-proposed-selectors-v1','selector schema');array(selections['selections'],32);require(len(selections['selections'])>0,'selection nonempty')
 for s in selections['selections']:selector(s)
 for k in ['corrected_observer_source','corrected_observer_binary']:
  q=a[k];require(sha(read(root/q['path']))==q['sha256'],'corrected observer binding')
 effective={'schema':'e33-effective-consumer-request-v2','authority_sha256':AUTHORITY_SHA256,'historical_catalog_sha256':a['historical_catalog_sha256'],'profile':p,'observer_source':a['corrected_observer_source'],'observer_binary':a['corrected_observer_binary']}
 return {'root':root,'authority':a,'profile':p,'selections':selections['selections'],'source':read(root/p['source']['path']).decode('utf-8'),'effective_request':effective,'effective_request_sha256':sha(json.dumps(effective,sort_keys=True,separators=(',',':')).encode())}
def validate_observation(v,request):
 obj(v,['schema','crate_name','target_spec_debug','target_triple_debug','target_cpu','target_features','opt_level','incremental_enabled','effective_cfg','source_files','external_crates','selected','trust_frontier'])
 require(v['schema']=='e33-proposed-observation-v1','observation schema');p=request['profile'];require(v['crate_name']==p['crate_name'],'selected crate')
 string(v['target_spec_debug']);require(v['target_triple_debug']=='TargetTuple('+json.dumps(p['target'])+')','selected built-in target');require(v['target_cpu']=='Some('+json.dumps(p['target_cpu'])+')','selected CPU');require(v['target_features']==p['target_features'],'selected target features');require(v['opt_level']=={0:'No',2:'More'}[p['optimization']],'selected optimization');require(v['incremental_enabled'] is False,'incremental disabled')
 array(v['effective_cfg'],128)
 for x in v['effective_cfg']:string(x,4096)
 require(v['effective_cfg']==sorted(set(v['effective_cfg'])),'canonical cfg census')
 array(v['source_files'],1);require(len(v['source_files'])==1,'complete selected fixture local source set')
 s=v['source_files'][0];obj(s,['name','compiler_source']);string(s['name'],4096);require(s['name']==str(request['root']/p['source']['path']),'compiler source path binding');require(s['compiler_source']==request['source'],'compiler source content binding')
 array(v['external_crates'],16)
 for e in v['external_crates']:obj(e,['crate','crate_hash']);string(e['crate'],1024);string(e['crate_hash'],1024)
 array(v['selected'],32);require(len(v['selected'])==len(request['selections']),'complete selected request set')
 for x,expected in zip(v['selected'],request['selections']):
  obj(x,['selection','resolved_definition','definition_kind','identity','fn_abi']);selector(x['selection']);require(x['selection']==expected,'consumer selected root/instance/extras');require(x['resolved_definition']==expected['path'],'resolved definition binding')
  identity=x['identity']
  if expected['query']=='instance':
   require(x['definition_kind']=='Fn','ordinary local function');obj(identity,['instance_kind','arguments_debug','declared_signature_debug'])
  else:require(x['definition_kind']=='TyAlias','function pointer type alias');obj(identity,['function_pointer_type'])
  for y in identity.values():string(y)
  abi(x['fn_abi'])
 string(v['trust_frontier'])
 return v
def compare_data(candidate_bytes,reference_bytes,request):
 candidate=validate_observation(parse(candidate_bytes),request);reference=validate_observation(parse(reference_bytes),request)
 require(candidate==reference,'complete observation mismatch')
 return {'status':'equal_to_consumer_reference','effective_request_sha256':request['effective_request_sha256'],'candidate_sha256':sha(candidate_bytes),'reference_sha256':sha(reference_bytes),'meaning':'Complete parsed data equality under a consumer-fixed request. Actual fresh reference provenance is a separate mandatory consumer premise; synthetic calls prove no FnAbi semantics.'}
