#!/usr/bin/env python3
"""Pinned Lake config/mtime/trace/setup identity experiment in tiny private roots."""
from __future__ import annotations
import argparse,hashlib,json,os,pathlib,platform,select,shutil,signal,subprocess,time
HERE=pathlib.Path(__file__).resolve().parent
BIN=pathlib.Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin')
LAKE=BIN/'lake';LEAN=BIN/'lean';PIN='leanprover/lean4:v4.30.0-rc2'
R={'environment':{},'commands':[],'cases':{},'limits':[]}
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def snapshot(root,cache):
 root=pathlib.Path(root);prod=root/'producer';con=root/'consumer'
 names={'source':prod/'Dep.lean','lean_config':prod/'lakefile.lean','toml_config':prod/'lakefile.toml',
 'trace':prod/'.lake/build/lib/lean/Dep.trace','setup':prod/'.lake/build/ir/Dep.setup.json',
 'olean':prod/'.lake/build/lib/lean/Dep.olean','ilean':prod/'.lake/build/lib/lean/Dep.ilean',
 'c':prod/'.lake/build/ir/Dep.c','consumer_manifest':con/'lake-manifest.json'}
 files={k:({'sha256':sha(p),'bytes':p.stat().st_size,'mtime_ns':p.stat().st_mtime_ns} if p.exists() else None) for k,p in names.items()}
 m=cache/'outputs/probe_dep';maps={p.name:sha(p) for p in sorted(m.glob('*.json'))} if m.exists() else {}
 return {'files':files,'cache_maps':maps}
def env(work,cache,choice=None,leanpath=None,enabled=True):
 e=dict(os.environ);e.update({'ELAN_TOOLCHAIN':PIN,'LEAN_NUM_THREADS':'1','MATHLIB_NO_CACHE_ON_UPDATE':'1',
 'HOME':str(work/'home'),'PATH':str(BIN)+os.pathsep+e.get('PATH',''),
 'LAKE_CACHE_DIR':str(cache),'LAKE_ARTIFACT_CACHE':'true' if enabled else 'false'})
 if choice:e['PROBE_CONFIG_VALUE']=choice
 else:e.pop('PROBE_CONFIG_VALUE',None)
 if leanpath:e['LEAN_PATH']=str(leanpath)
 return e
def run(label,args,cwd,work,cache,choice=None,leanpath=None,timeout=25,enabled=True):
 process_env=env(work,cache,choice,leanpath,enabled)
 producer_source=cwd.parent/'producer/Dep.lean'
 if producer_source.is_file():process_env['PROBE_SOURCE_PATH']=str(producer_source)
 p=subprocess.run([str(x) for x in args],cwd=cwd,env=process_env,capture_output=True,text=True,timeout=timeout)
 r={'label':label,'argv':[str(x).replace(str(work),'$WORK') for x in args],
 'cwd':str(cwd).replace(str(work),'$WORK'),'choice':choice,'artifact_cache_enabled':enabled,'exit':p.returncode,
 'stdout':p.stdout.replace(str(work),'$WORK'),'stderr':p.stderr.replace(str(work),'$WORK')}
 R['commands'].append(r);return r
def make(root,config='lean-dynamic',value=7):
 prod=root/'producer';con=root/'consumer';prod.mkdir(parents=True);con.mkdir()
 if config=='lean-dynamic':
  (prod/'lakefile.lean').write_text('import Lake\nopen Lake DSL\nrun_cmd do\n  let v ← IO.getEnv "PROBE_CONFIG_VALUE"\n  let some p ← IO.getEnv "PROBE_SOURCE_PATH" | throwError "missing private source path"\n  let n := if v == some "B" then "9" else "7"\n  IO.FS.writeFile p s!"def depValue : Nat := {n}\\n"\npackage probe_dep\n@[default_target]\nlean_lib Dep\n')
  (prod/'Dep.lean').write_text('-- placeholder; overwritten when Lean lakefile is compiled\n')
  cfg='lakefile.lean'
 elif config=='lean-option':
  (prod/'lakefile.lean').write_text('import Lake\nopen Lake DSL\npackage probe_dep where\n  leanOptions := #[⟨`pp.unicode.fun, true⟩]\n@[default_target]\nlean_lib Dep\n')
  (prod/'Dep.lean').write_text(f'def depValue : Nat := {value}\n');cfg='lakefile.lean'
 elif config=='toml':
  (prod/'lakefile.toml').write_text('name = "probe_dep"\ndefaultTargets = ["Dep"]\n[[lean_lib]]\nname = "Dep"\n')
  (prod/'Dep.lean').write_text(f'def depValue : Nat := {value}\n');cfg='lakefile.toml'
 else:raise AssertionError(config)
 (prod/'lean-toolchain').write_text(PIN+'\n')
 (con/'lakefile.lean').write_text('import Lake\nopen Lake DSL\nrequire probe_dep from "../producer"\npackage probe_consumer\n@[default_target]\nlean_lib Generated\n')
 (con/'lean-toolchain').write_text(PIN+'\n')
 (con/'Generated.lean').write_text('import Dep\ntheorem generatedEq : depValue + 1 = 8 := by decide\n#eval depValue + 1\n')
 manifest={'version':'1.2.0','packagesDir':'.lake/packages','packages':[{'type':'path','scope':'','name':'probe_dep','manifestFile':'lake-manifest.json','inherited':False,'dir':'../producer','configFile':cfg}],
 'name':'probe_consumer','lakeDir':'.lake','fixedToolchain':False}
 (con/'lake-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
 return prod,con
def build(label,root,work,cache,choice):
 con=root/'consumer'
 a=run(label+'-local',[LAKE,'--keep-toolchain','--no-cache','build','Dep'],con,work,cache,choice,enabled=False)
 b=run(label+'-cache',[LAKE,'--keep-toolchain','build','Dep'],con,work,cache,choice)
 assert a['exit']==b['exit']==0,(label,a,b)
def batch(label,root,work,cache,choice,setup=False):
 con=root/'consumer';prod=root/'producer'
 if not setup:
  return run(label,[LEAN,'--json','Generated.lean'],con,work,cache,choice,prod/'.lake/build/lib/lean')
 st=run(label+'-setup',[LAKE,'--keep-toolchain','--no-build','setup-file','Generated.lean'],con,work,cache,choice)
 if st['exit']!=0:return {'exit':None,'setup_exit':st['exit'],'setup_import_sha256':None}
 data=json.loads(st['stdout']);art=pathlib.Path(data['importArts']['Dep'][0].replace('$WORK',str(work)))
 assert art.is_file()
 isolated=work/('setup-'+label);isolated.mkdir();shutil.copyfile(con/'Generated.lean',isolated/'Generated.lean')
 (isolated/'Dep.olean').symlink_to(art)
 p=run(label+'-via-setup',[LEAN,'--json','Generated.lean'],isolated,work,cache,choice,isolated)
 return {'exit':p['exit'],'setup_exit':st['exit'],'setup_import_sha256':sha(art),'setup_import_path':str(art).replace(str(work),'$WORK')}
def server(label,root,work,cache,choice):
 prod=root/'producer';server_root=work/('server-'+label);server_root.mkdir();source=server_root/'Generated.lean';shutil.copyfile(root/'consumer/Generated.lean',source)
 uri=source.as_uri();buf=b'';seen=[]
 p=subprocess.Popen([str(LEAN),'--server'],cwd=server_root,env=env(work,cache,choice,prod/'.lake/build/lib/lean'),stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0,start_new_session=True)
 def send(m):
  data=json.dumps(m,separators=(',',':')).encode();p.stdin.write(b'Content-Length: '+str(len(data)).encode()+b'\r\n\r\n'+data);p.stdin.flush()
 def get(seconds=12):
  nonlocal buf
  end=time.monotonic()+seconds
  while time.monotonic()<end:
   if b'\r\n\r\n' in buf:
    h,b=buf.split(b'\r\n\r\n',1);lengths=[int(x.split(b':',1)[1]) for x in h.split(b'\r\n') if x.lower().startswith(b'content-length:')]
    if lengths and len(b)>=lengths[0]:
     raw,buf=b[:lengths[0]],b[lengths[0]:];m=json.loads(raw);seen.append(m)
     if m.get('method')=='client/registerCapability' and 'id' in m:send({'jsonrpc':'2.0','id':m['id'],'result':None})
     return m
   ready,_,_=select.select([p.stdout],[],[],min(.1,max(0,end-time.monotonic())))
   if ready:
    chunk=os.read(p.stdout.fileno(),65536)
    if not chunk:break
    buf+=chunk
  raise TimeoutError(label)
 def until(i,seconds=12):
  end=time.monotonic()+seconds
  while time.monotonic()<end:
   m=get(max(.1,end-time.monotonic()))
   if m.get('id')==i:return m
  raise TimeoutError(label)
 try:
  send({'jsonrpc':'2.0','id':1,'method':'initialize','params':{'processId':os.getpid(),'rootUri':server_root.as_uri(),'capabilities':{},'initializationOptions':{'hasWidgets':False}}});until(1)
  send({'jsonrpc':'2.0','method':'initialized','params':{}})
  send({'jsonrpc':'2.0','method':'textDocument/didOpen','params':{'textDocument':{'uri':uri,'languageId':'lean','version':1,'text':source.read_text()}}})
  send({'jsonrpc':'2.0','id':2,'method':'textDocument/waitForDiagnostics','params':{'uri':uri,'version':1}});until(2)
  diags=[m['params'] for m in seen if m.get('method')=='textDocument/publishDiagnostics' and m['params'].get('uri')==uri]
  out={'label':label,'diagnostics':diags,'wait_completed':True,'source_sha256':sha(source),'olean_sha256':sha(prod/'.lake/build/lib/lean/Dep.olean')}
  send({'jsonrpc':'2.0','method':'textDocument/didClose','params':{'textDocument':{'uri':uri}}})
  send({'jsonrpc':'2.0','id':3,'method':'shutdown','params':None});until(3,5);send({'jsonrpc':'2.0','method':'exit','params':{}})
  try:p.wait(timeout=2)
  except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);p.wait(timeout=5)
 except Exception as ex:out={'label':label,'error':repr(ex),'messages':seen}
 finally:
  if p.poll() is None:os.killpg(p.pid,signal.SIGKILL);p.wait(timeout=5)
  out['process_exit']=p.returncode;out['stderr']=p.stderr.read().decode(errors='replace').replace(str(work),'$WORK')
 R['commands'].append({'label':label,'server':out});return out

def main():
 a=argparse.ArgumentParser();a.add_argument('--work',type=pathlib.Path,required=True);x=a.parse_args();work=x.work.resolve()
 if work.exists():raise SystemExit('--work must be absent and owned')
 if shutil.disk_usage(work.parent).free<15*(1<<30):raise SystemExit('15 GiB free disk guard')
 mp=subprocess.run(['/usr/bin/memory_pressure','-Q'],capture_output=True,text=True,timeout=5)
 pct=int(mp.stdout.rsplit('System-wide memory free percentage:',1)[1].split('%',1)[0].strip())
 if pct<35:raise SystemExit(f'free memory {pct}% below 35% guard')
 work.mkdir();(work/'home').mkdir();cache=work/'cache'
 R['environment']={'platform':platform.platform(),'lake_sha256':sha(LAKE),'lean_sha256':sha(LEAN),'free_memory_preflight_percent':pct,
 'cache_root':'$WORK/cache','toolchain':PIN,'max_concurrent_commands':1,'per_command_timeout_seconds':25}
 art=HERE/'artifacts'
 if art.exists():shutil.rmtree(art)
 art.mkdir()
 for label,config,value,choice in [('dynamic-a','lean-dynamic',7,'A'),('dynamic-b','lean-dynamic',9,'B'),('toml-seven','toml',7,None),('toml-nine','toml',9,None),('lean-option','lean-option',7,None)]:
  root=work/label;make(root,config,value);build(label,root,work,cache,choice)
  bs=batch(label+'-local-batch',root,work,cache,choice)
  via=batch(label+'-setup-batch',root,work,cache,choice,setup=True)
  R['cases'][label]={'snapshot':snapshot(root,cache),'local_batch_exit':bs['exit'],'setup_batch':via,
   'server':server(label+'-server',root,work,cache,choice) if label in ('dynamic-a','dynamic-b','toml-seven') else None}
  d=art/label;d.mkdir()
  for key,path in {'source':root/'producer/Dep.lean','config_lean':root/'producer/lakefile.lean','config_toml':root/'producer/lakefile.toml',
   'trace':root/'producer/.lake/build/lib/lean/Dep.trace','setup':root/'producer/.lake/build/ir/Dep.setup.json',
   'olean':root/'producer/.lake/build/lib/lean/Dep.olean','consumer':root/'consumer/Generated.lean'}.items():
   if path.is_file():shutil.copyfile(path,d/key)
 # Change only the dynamic configuration environment on the already built A root.
 root=work/'dynamic-a';prod=root/'producer';con=root/'consumer'
 nb=run('env-b-stale-no-build',[LAKE,'--keep-toolchain','--no-build','build','Dep'],con,work,cache,'B')
 via=batch('env-b-stale-setup-batch',root,work,cache,'B',setup=True)
 local=batch('env-b-stale-local-batch',root,work,cache,'B')
 R['cases']['env-b-stale']={'no_build_exit':nb['exit'],'snapshot':snapshot(root,cache),'setup_batch':via,'local_batch_exit':local['exit'],'server':server('env-b-stale-server',root,work,cache,'B')}
 # Copy original bytes and times before perturbing metadata or traces.
 golden={k:(prod/p) for k,p in {'source':'Dep.lean','config':'lakefile.lean','trace':'.lake/build/lib/lean/Dep.trace','setup':'.lake/build/ir/Dep.setup.json','olean':'.lake/build/lib/lean/Dep.olean','ilean':'.lake/build/lib/lean/Dep.ilean','c':'.lake/build/ir/Dep.c'}.items()}
 orig_mtimes={k:v.stat().st_mtime_ns for k,v in golden.items()}
 for k,p in golden.items():shutil.copyfile(p,art/('golden-'+k))
 def restore_golden():
  for key,p in golden.items():
   if p.exists():p.chmod(p.stat().st_mode|0o200)
   p.parent.mkdir(parents=True,exist_ok=True)
   shutil.copyfile(art/('golden-'+key),p)
   os.utime(p,ns=(orig_mtimes[key],orig_mtimes[key]))
 for label,key,delta in [('source-older','source',-86_400_000_000_000),('source-newer','source',86_400_000_000_000),('trace-newer','trace',86_400_000_000_000)]:
  p=golden[key];os.utime(p,ns=(orig_mtimes[key]+delta,orig_mtimes[key]+delta))
  nb=run(label+'-no-build',[LAKE,'--keep-toolchain','--no-build','build','Dep'],con,work,cache,'B')
  via=batch(label+'-setup-batch',root,work,cache,'B',setup=True)
  local=batch(label+'-local-batch',root,work,cache,'B')
  R['cases'][label]={'no_build_exit':nb['exit'],'snapshot':snapshot(root,cache),'setup_batch':via,'local_batch_exit':local['exit']}
  os.utime(p,ns=(orig_mtimes[key],orig_mtimes[key]))
 # Replace whole trace with a valid trace from a different source generation.
 trace=golden['trace'];trace.chmod(trace.stat().st_mode|0o200)
 shutil.copyfile(work/'dynamic-b'/'producer'/'.lake/build/lib/lean/Dep.trace',trace)
 nb=run('wrong-trace-no-build',[LAKE,'--keep-toolchain','--no-build','build','Dep'],con,work,cache,'B')
 via=batch('wrong-trace-setup-batch',root,work,cache,'B',setup=True)
 local=batch('wrong-trace-local-batch',root,work,cache,'B')
 R['cases']['wrong-trace']={'no_build_exit':nb['exit'],'snapshot':snapshot(root,cache),'setup_batch':via,'local_batch_exit':local['exit']}
 restore_golden()
 # Replace only setup JSON with a valid option-generation file.
 setup=golden['setup'];setup.chmod(setup.stat().st_mode|0o200)
 shutil.copyfile(work/'lean-option'/'producer'/'.lake/build/ir/Dep.setup.json',setup)
 nb=run('wrong-setup-no-build',[LAKE,'--keep-toolchain','--no-build','build','Dep'],con,work,cache,'B')
 via=batch('wrong-setup-setup-batch',root,work,cache,'B',setup=True)
 local=batch('wrong-setup-local-batch',root,work,cache,'B')
 R['cases']['wrong-setup']={'no_build_exit':nb['exit'],'snapshot':snapshot(root,cache),'setup_batch':via,'local_batch_exit':local['exit']}
 restore_golden()
 # Same mtime, changed source; the B cache entry is already present.
 src=golden['source'];src.write_text('def depValue : Nat := 9\n');os.utime(src,ns=(orig_mtimes['source'],orig_mtimes['source']))
 nb=run('same-mtime-source-edit-no-build',[LAKE,'--keep-toolchain','--no-build','build','Dep'],con,work,cache,'B')
 via=batch('same-mtime-source-edit-setup-batch',root,work,cache,'B',setup=True)
 local=batch('same-mtime-source-edit-local-batch',root,work,cache,'B')
 R['cases']['same-mtime-source-edit']={'no_build_exit':nb['exit'],'snapshot':snapshot(root,cache),'setup_batch':via,'local_batch_exit':local['exit']}
 R['retained_inventory']={p.relative_to(art).as_posix():{'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(art.rglob('*')) if p.is_file()}
 R['limits']=['One pinned Lake/Lean host with tiny local packages; no Anneal archive, Mathlib or cross-version claim.',
 'The dynamic Lean run_cmd source writer is deliberately adversarial config-time I/O; TOML cells are static.',
 'No network syscall trace or power-loss durability test.',
 'Direct Lean server imports use explicit local LEAN_PATH; Lake setup may return a different cache object.']
 (HERE/'results.json').write_text(json.dumps(R,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'cases':list(R['cases']),'commands':len(R['commands'])}))
if __name__=='__main__':main()
