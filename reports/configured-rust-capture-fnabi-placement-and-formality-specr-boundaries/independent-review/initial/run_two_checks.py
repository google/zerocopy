from pathlib import Path
import json,hashlib,subprocess,time,sys
OWN=Path(__file__).resolve().parent
P=json.loads((OWN/'NEXT-REPLAY-PLAN.json').read_bytes());BASE=Path(P['cwd']);R=BASE/'work/execution/abi-witness';T=BASE/'work/execution/toolchains/rustup/toolchains/nightly-2026-05-01-aarch64-apple-darwin';PK=BASE/'work/execution/abi-package/reports/configured-rust-fnabi-and-machine-placement-2026'
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(name,x):
 with (OWN/name).open('x') as f:json.dump(x,f,indent=2);f.write('\n')
def require(v,why):
 if not v:raise RuntimeError(why)
def frozen():
 require(h(PK/'MANIFEST.json')=='49219fcca8820d9d5f864d569e3b52c5156fb53110d05f8232b590e5f4fec5ea','original frozen manifest')
 m=json.loads((PK/'MANIFEST.json').read_bytes())
 for n,x in m['files'].items():
  p=PK/n;require(p.is_file() and not p.is_symlink() and p.stat().st_size==x['bytes'] and h(p)==x['sha256'],'frozen public artifact '+n)
 require({str(p.relative_to(PK)) for p in PK.rglob('*') if p.is_file()}==set(m['files'])|{'MANIFEST.json'},'original frozen census')
 pr=json.loads((PK/'PROJECTION.json').read_bytes())
 for x in pr['files']:
  p=BASE/'work/execution'/x['raw_label'];require(p.is_file() and not p.is_symlink() and p.stat().st_size==x['raw_bytes'] and h(p)==x['raw_sha256'],'original raw artifact '+x['raw_label'])
 for x in json.loads((R/'source-identities.json').read_bytes())['readonly_tools']:
  p=T/x['toolchain_relative_path'];require(p.is_file() and not p.is_symlink() and p.stat().st_size==x['bytes'] and h(p)==x['sha256'],'tool '+str(p))
 a=json.loads((R/'stage5/consumer-authority-windows.json').read_bytes());q=a['installed_target_identities'];p=R/q['path'];require(h(p)==q['sha256'],'target receipt')
 ids=json.loads(p.read_bytes());require(len(ids['files'])==45,'target45')
 for x in ids['files']:
  p=T/x['toolchain_relative_path'];require(p.is_file() and not p.is_symlink() and p.stat().st_size==x['bytes'] and h(p)==x['sha256'],'target '+str(p))
 require(h(R/'observer-v3')=='f1d0404e6c9cfca353376653c1ea9464c328d358851447e12af65953d368172b','observer binary')
 actual=R.parent/'toolchains/rustup/toolchains/nightly-2026-05-01-aarch64-apple-darwin/lib/rustlib/aarch64-apple-darwin/lib/librustc_driver-16d1e96e5b674978.dylib'
 require(h(actual)=='dcaea7cc1884046940eb55fcb783e6a86272cf4743600925431022332fa9d69d','loader-resolved driver')
 return {'original_public_manifest_sha256':h(PK/'MANIFEST.json'),'raw_projected_file_bindings':len(pr['files']),'public_file_bindings':len(m['files']),'windows_target_files':len(ids['files']),'observer_sha256':h(R/'observer-v3'),'actual_driver_sha256':h(actual)}
summary={'status':'INCOMPLETE','max_observer_invocations':2,'separate_captures':0,'codegen_link_native_reader_invocations':0,'rows':[],'amendment':'Parent granted -B immediately after /usr/bin/python3; no other argv/env/source changes','trust':'Existing consumer/compiler/observer/controller, Python runtime and OS/shared cache remain trusted; sampled operational limits are not hard isolation or peak bounds.'}
try:
 for row in P['sequence']:
  rp=Path(row['run_path_must_not_exist']);require(not rp.exists() and not any(x.name.casefold()==rp.name.casefold() for x in rp.parent.iterdir()),'fresh noncolliding run path '+str(rp))
 before=frozen();write('fresh-preflight.json',{'status':'PASS','bindings':before,'python':{'path':'/usr/bin/python3','resolved':str(Path('/usr/bin/python3').resolve()),'sha256':h(Path('/usr/bin/python3'))},'settings':'Requested gpt-6.1-sol/medium; effective settings not exposed','source_helpers_executed':'Exact private originals, no edits/copies'})
 for row in P['sequence']:
  require(h(Path(row['argv'][1]))==row['consumer_sha256'],'consumer binding')
  candidate=Path(row['argv'][row['argv'].index('--candidate')+1]);require(h(candidate)==row['candidate_raw_sha256'],'candidate binding')
  argv=row['argv'][:1]+['-B']+row['argv'][1:];write(row['name']+'-command.json',{'argv':argv,'env_exact':P['environment'],'cwd':P['cwd'],'consumer_sha256':row['consumer_sha256'],'candidate_sha256':row['candidate_raw_sha256'],'run_path':row['run_path_must_not_exist']})
  start=time.monotonic();pre=frozen();prefix=Path(row['parent_cli_stream_prefix'])
  with Path(str(prefix)+'.stdout').open('xb') as out,Path(str(prefix)+'.stderr').open('xb') as err:
   p=subprocess.Popen(argv,cwd=P['cwd'],env=P['environment'],stdout=out,stderr=err)
   write(row['name']+'-consumer-child.json',{'pid':p.pid,'argv':argv,'started_unix_ns':time.time_ns()});exitcode=p.wait()
  cli={'exit_code':exitcode,'seconds':time.monotonic()-start,'waited_and_reaped':True,'stdout_sha256':h(Path(str(prefix)+'.stdout')),'stderr_sha256':h(Path(str(prefix)+'.stderr')),'stderr_bytes':Path(str(prefix)+'.stderr').stat().st_size};write(row['name']+'-consumer-status.json',cli)
  require(exitcode==0,'consumer exit failure '+row['name']);require(cli['stderr_bytes']==0,'unexpected consumer stderr '+row['name'])
  stdout=json.loads(Path(str(prefix)+'.stdout').read_bytes());require(stdout['status']==row['expected_comparison_status'],'consumer CLI status')
  rp=Path(row['run_path_must_not_exist']);result=json.loads((rp/'result.json').read_bytes());comparison=json.loads((rp/'comparison.json').read_bytes());child=json.loads((rp/'child.json').read_bytes());inv=json.loads((rp/'invocation.json').read_bytes())
  require(result['spawned'] and result['exit_code']==0 and result['controller_failure'] is None and result['stop_reason'] is None and result['remaining_group_after_parent_wait']==[],'observer lifecycle failure '+row['name'])
  require((rp/'stdout').stat().st_size==0 and (rp/'stderr').stat().st_size==0,'unexpected ordinary observer diagnostic '+row['name'])
  require(result['child_pid']==child['pid']==child['pgid'] and inv['argv']==child['argv'] and inv['argv'][0]==str(R/'observer-v3'),'observer child binding')
  require(h(rp/'reference.json')==row['expected_fresh_reference_sha256'] and h(candidate)==row['candidate_raw_sha256'],'fresh/candidate packet binding')
  require(comparison['status']==row['expected_comparison_status'] and comparison['candidate_sha256']==h(candidate) and comparison['reference_sha256']==h(rp/'reference.json'),'comparison receipt binding')
  post=frozen();require(pre==post,'before/after bindings')
  summary['rows'].append({'name':row['name'],'status':'PASS','observer_invocations':1,'consumer':cli,'observer_pid':result['child_pid'],'observer_exit':result['exit_code'],'observer_waited_in_controller_finally':True,'remaining_group_after_parent_wait':result['remaining_group_after_parent_wait'],'reference_sha256':h(rp/'reference.json'),'comparison_sha256':h(rp/'comparison.json'),'effective_request_sha256':comparison['effective_request_sha256'],'observer_seconds':result['seconds'],'rss_samples':len(json.loads((rp/'rss-samples.json').read_bytes())),'max_observed_group_rss_bytes':result['max_observed_group_rss_bytes'],'bindings_unchanged':post,'run_dir':str(rp)})
 summary['status']='PASS';summary['actual_observer_invocations']=2
except BaseException as e:
 summary['status']='STOP';summary['error_type']=type(e).__name__;summary['error']=str(e);summary['retry_or_repair']=False
finally:
 write('fresh-two-checks-result.json',summary)
print(json.dumps(summary,indent=2));sys.exit(0 if summary['status']=='PASS' else 70)
