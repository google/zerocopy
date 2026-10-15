"""24 authorized candidate-DATA controls. Never changes or executes source/image.
Each schema-admissible candidate invokes unchanged consumer with fresh reference.
"""
from pathlib import Path
import copy,hashlib,json,subprocess,sys,time
import e33_data_v3 as D
B=Path(__file__).resolve().parent
S=B/'stage4';R=S/'actual-controls'
T=B.parent/'toolchains/rustup/toolchains/nightly-2026-05-01-aarch64-apple-darwin'
PROFILE='host-subjects-opt2'
BASE=B/'stage4/runs/capture-subjects-o2/reference.json'
BASE_SHA='befdf851863832f050eb65f4b86552372ad2606d2ed9482a23bf530be096a1d9'
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def entry(v,name,type_args=None,extras=None):
 xs=[x for x in v['selected'] if x['selection']['path']=='abi_subjects::'+name and (type_args is None or x['selection']['type_args']==type_args) and (extras is None or x['selection']['extra_args']==extras)]
 assert len(xs)==1;return xs[0]
def abi(v,name,**kw):return entry(v,name,**kw)['fn_abi']
def attrs(v,name,index=0):return abi(v,name)['args'][index]['mode']['attrs']
def remove_attr(v,name,tag,bit):
 a=attrs(v,name);parts=a['regular_debug'].split(' | ');assert tag in parts and a['regular_bits']&bit;a['regular_bits']^=bit;parts.remove(tag);a['regular_debug']=' | '.join(parts)
def prepare():
 assert not R.exists();R.mkdir();(R/'candidates').mkdir();(R/'jobs').mkdir();(R/'runs').mkdir()
 assert h(BASE)==BASE_SHA
 base=D.parse(BASE.read_bytes());request=D.load_request(B,PROFILE);D.validate_observation(base,request)
 controls=[]
 def add(name,fn=None,raw=None):
  v=copy.deepcopy(base)
  if fn:fn(v)
  data=raw if raw is not None else json.dumps(v,sort_keys=True,separators=(',',':')).encode()
  p=R/'candidates'/(name+'.json');p.write_bytes(data)
  try:D.validate_observation(D.parse(data),request);admissible=True;reason='complete observation mismatch'
  except D.Reject as e:admissible=False;reason=str(e)
  controls.append({'id':name,'profile':PROFILE,'candidate':str(p.relative_to(R)),'bytes':len(data),'sha256':h(p),'schema_admissible':admissible,'expected_observer_calls':int(admissible),'expected_consumer_exit':64,'expected_reason':reason})
 add('01-stale-target',lambda v:v.update(target_triple_debug='TargetTuple("x86_64-pc-windows-msvc")'))
 add('02-stale-opt-profile',raw=(B/'capture-v3-host-subjects-opt0-01/reference.json').read_bytes())
 add('03-wrong-CPU',lambda v:v.update(target_cpu='Some("other")'))
 add('04-unqualified-name',lambda v:entry(v,'abi_c_narrow')['selection'].update(path='abi_c_narrow'))
 add('05-wrong-root',lambda v:entry(v,'abi_c_narrow')['selection'].update(path='abi_subjects::abi_system_narrow'))
 add('06-wrong-generic-instance',lambda v:entry(v,'generic_id',type_args=['u8'])['selection'].update(type_args=['u64']))
 add('07-omitted-selection',lambda v:v['selected'].pop())
 add('08-reordered-selection',lambda v:v['selected'].reverse())
 add('09-omitted-selected-vararg-extra',lambda v:entry(v,'VarC',extras=['i32','f64','*const u8'])['selection']['extra_args'].pop())
 add('10-omitted-hidden-location',lambda v:abi(v,'abi_track')['args'].pop())
 add('11-omitted-vararg-ABI-argument',lambda v:abi(v,'VarC',extras=['i32','f64','*const u8'])['args'].pop())
 add('12-wrong-result-mode',lambda v:abi(v,'abi_c_big')['ret'].update(mode={'kind':'direct','attrs':abi(v,'abi_c_big')['ret']['mode']['attrs']}))
 add('13-wrong-indirect-on-stack',lambda v:abi(v,'abi_c_big')['args'][0]['mode'].update(on_stack=True))
 add('14-wrong-extension',lambda v:attrs(v,'abi_c_narrow').update(extension='None'))
 add('15-removed-NoAlias',lambda v:remove_attr(v,'abi_shared','NoAlias',8))
 add('16-wrong-pointee-size',lambda v:attrs(v,'abi_shared').update(pointee_size_bytes=0))
 add('17-wrong-pointee-alignment',lambda v:attrs(v,'abi_shared').update(pointee_align_bytes=1))
 add('18-wrong-cast-coverage',lambda v:abi(v,'abi_c_pair')['args'][0]['mode'].update(rest_total_bytes=8))
 add('19-wrong-HFA-consecutiveness',lambda v:abi(v,'abi_c_hfa')['args'][0]['mode'].update(rest_is_consecutive=False))
 add('20-widened-bool-range',lambda v:abi(v,'abi_c_narrow')['args'][2]['layout']['backend_repr']['scalar'].update(valid_range_end='2'))
 add('21-wrong-generic-return-size',lambda v:abi(v,'generic_id',type_args=['u8'])['ret']['layout'].update(size_bytes=8))
 add('22-opaque-layout-change',lambda v:abi(v,'abi_c_pair')['ret']['layout'].update(full_layout_debug='changed producer opaque layout'))
 add('23-removed-NoUndef',lambda v:remove_attr(v,'abi_c_narrow','NoUndef',128))
 add('24-false-unwind-permission',lambda v:abi(v,'abi_c_narrow').update(can_unwind=True))
 assert len(controls)==24 and sum(x['schema_admissible'] for x in controls)==15
 manifest={'scope':'24 candidate-only actual captured-packet mutations; no source/image mutation or execution','base_packet_sha256':BASE_SHA,'effective_request_sha256':request['effective_request_sha256'],'helper_sha256':h(Path(__file__)),'consumer_sha256':h(B/'e33_consumer_v3.py'),'grammar_sha256':h(B/'e33_data_v3.py'),'controls':controls}
 (R/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps({'prepared':24,'schema_admissible':15,'schema_rejected':9,'manifest_sha256':h(R/'manifest.json')},indent=2))
def execute():
 assert not (R/'STOP.json').exists() and not (S/'RESUMED_STOP.json').exists()
 m=json.loads((R/'manifest.json').read_text());assert m['helper_sha256']==h(Path(__file__)) and m['base_packet_sha256']==h(BASE)==BASE_SHA
 assert m['consumer_sha256']==h(B/'e33_consumer_v3.py')=='c0c476f3fe9e1497f4484b4de4c493194cd82d2fd93f5853fbfd7241f7aeb6da'
 assert m['grammar_sha256']==h(B/'e33_data_v3.py')=='b9246631d37955add31da62f891eb9d0e0ec201a8a532ca3ccf385f8bced6018'
 rows=[]
 for c in m['controls']:
  candidate=R/c['candidate'];assert candidate.stat().st_size==c['bytes'] and h(candidate)==c['sha256'];job=R/'jobs'/c['id'];run=R/'runs'/c['id'];assert not job.exists() and not run.exists();job.mkdir();(job/'tmp').mkdir()
  argv=[sys.executable,'-B',str(B/'e33_consumer_v3.py'),'check','--toolchain',str(T),'--profile',PROFILE,'--candidate',str(candidate),'--run-dir',str(run)]
  env={'PATH':'/usr/bin:/bin:/usr/sbin:/sbin','LANG':'C','LC_ALL':'C','TMPDIR':str(job/'tmp'),'PYTHONDONTWRITEBYTECODE':'1'}
  (job/'invocation.json').write_text(json.dumps({'argv':argv,'env_exact':env,'helper_sha256':h(Path(__file__)),'candidate_sha256':h(candidate)},indent=2)+'\n')
  started=time.monotonic();p=subprocess.run(argv,env=env,capture_output=True,timeout=90);(job/'stdout').write_bytes(p.stdout);(job/'stderr').write_bytes(p.stderr)
  stop=None
  try:value=json.loads(p.stdout)
  except Exception:stop='malformed consumer CLI output';value=None
  if p.returncode!=64 or p.stderr or not value or value.get('status')!='rejected_data' or value.get('reason')!=c['expected_reason']:stop=stop or 'unexpected candidate result/diagnostic'
  fresh=None
  if c['schema_admissible']:
   if not (run/'result.json').is_file():stop=stop or 'missing fresh observer'
   else:
    fresh=json.loads((run/'result.json').read_text())
    if fresh['exit_code']!=0 or fresh['controller_failure'] or fresh['stop_reason'] or fresh['remaining_group_after_parent_wait'] or (run/'stdout').stat().st_size or (run/'stderr').stat().st_size:stop=stop or 'fresh observer operational/diagnostic issue'
    if not (run/'reference.json').is_file() or h(run/'reference.json')!=BASE_SHA:stop=stop or 'unexpected fresh reference content'
  elif run.exists():stop=stop or 'schema rejection launched capture'
  size=sum(x.stat().st_size for x in S.rglob('*') if x.is_file())
  if size>=268435456:stop=stop or 'additional output budget'
  row={'id':c['id'],'schema_admissible':c['schema_admissible'],'observer_calls':int(fresh is not None),'consumer_exit':p.returncode,'CLI_json':value,'seconds':time.monotonic()-started,'fresh_observer':fresh,'candidate_sha256':h(candidate),'stdout_sha256':h(job/'stdout'),'stderr_sha256':h(job/'stderr'),'stop':stop}
  (job/'result.json').write_text(json.dumps(row,indent=2)+'\n');rows.append(row)
  if stop:(R/'STOP.json').write_text(json.dumps(row,indent=2)+'\n');break
 summary={'status':'PASS' if len(rows)==24 and not any(x['stop'] for x in rows) else 'STOPPED','completed':len(rows),'expected_rejections':sum(x['consumer_exit']==64 and not x['stop'] for x in rows),'observer_calls':sum(x['observer_calls'] for x in rows),'zero-observer_schema_rejections':sum(not x['schema_admissible'] and not x['observer_calls'] for x in rows),'manifest_sha256':h(R/'manifest.json'),'rows':rows,'scope':'Actual candidate data only; same consumer-chosen hostO2 source/target/options. No source/image/invalid-native execution.'}
 (R/'results.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps({k:v for k,v in summary.items() if k!='rows'},indent=2));return 0 if summary['status']=='PASS' else 70
if __name__=='__main__':
 if sys.argv[1:]==['prepare']:prepare()
 elif sys.argv[1:]==['execute']:raise SystemExit(execute())
 else:raise SystemExit('prepare or execute; only fixed data-control matrix')
