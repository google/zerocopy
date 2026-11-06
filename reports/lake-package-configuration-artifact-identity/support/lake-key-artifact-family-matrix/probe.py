#!/usr/bin/env python3
"""Small pinned Lake key and cross-generation artifact-family matrix."""
from __future__ import annotations
import argparse,hashlib,json,os,pathlib,platform,shutil,subprocess,sys,time,select,signal
HERE=pathlib.Path(__file__).resolve().parent
PKG=HERE.parent
TOOLS=pathlib.Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools')
BIN=TOOLS/'elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin'
LAKE=BIN/'lake';LEAN=BIN/'lean'
TOOLCHAIN='leanprover/lean4:v4.30.0-rc2'
PRIOR=pathlib.Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/scratch/20260927-reference-experiments/reference-publish/reports/anneal-3730-lake-plugin-artifact-identity-v4-30-0-rc2/support/work')
R={'environment':{},'commands':[],'cases':{},'limits':[]}
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def inv(root):
 root=pathlib.Path(root)
 return {p.relative_to(root).as_posix():{'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(root.rglob('*')) if p.is_file()}
def env(work,cache=None,leanpath=None):
 e=dict(os.environ);e.update({'ELAN_TOOLCHAIN':TOOLCHAIN,'LEAN_NUM_THREADS':'1','MATHLIB_NO_CACHE_ON_UPDATE':'1',
 'HOME':str(work/'home'),'PATH':str(BIN)+os.pathsep+e.get('PATH',''),
 'LAKE_ARTIFACT_CACHE':'true','LAKE_CACHE_DIR':str(cache or work/'cache')})
 if leanpath:e['LEAN_PATH']=str(leanpath)
 return e
def run(label,argv,cwd,work,cache=None,leanpath=None,timeout=30,extraenv=None):
 process_env=env(work,cache,leanpath)
 if extraenv:process_env.update(extraenv)
 p=subprocess.run([str(x) for x in argv],cwd=cwd,env=process_env,text=True,capture_output=True,timeout=timeout)
 rec={'label':label,'argv':[str(x).replace(str(work),'$WORK') for x in argv],
 'cwd':str(cwd).replace(str(work),'$WORK'),'exit':p.returncode,
 'stdout':p.stdout.replace(str(work),'$WORK'),'stderr':p.stderr.replace(str(work),'$WORK')}
 R['commands'].append(rec);return rec
def make(root,value,option=False,manifest='probe_consumer',extra=False):
 prod=root/'producer';con=root/'consumer';prod.mkdir(parents=True);con.mkdir()
 (prod/'Dep.lean').write_text(f'def depValue : Nat := {value}\n'+('def extraValue : Nat := 44\n' if extra else ''))
 pconf='import Lake\nopen Lake DSL\npackage probe_dep'+(' where\n  leanOptions := #[⟨`pp.unicode.fun, true⟩]' if option else '')+'\n@[default_target]\nlean_lib Dep\n'
 (prod/'lakefile.lean').write_text(pconf)
 (prod/'lean-toolchain').write_text(TOOLCHAIN+'\n')
 (con/'Generated.lean').write_text('import Dep\ntheorem generatedEq : depValue + 1 = 8 := by decide\n#eval depValue + 1\n')
 (con/'lakefile.lean').write_text(f'import Lake\nopen Lake DSL\nrequire probe_dep from "../producer"\npackage {manifest}\n@[default_target]\nlean_lib Generated\n')
 (con/'lean-toolchain').write_text(TOOLCHAIN+'\n')
 m={'version':'1.2.0','packagesDir':'.lake/packages','packages':[{'type':'path','scope':'','name':'probe_dep','manifestFile':'lake-manifest.json','inherited':False,'dir':'../producer','configFile':'lakefile.lean'}],
 'name':manifest,'lakeDir':'.lake','fixedToolchain':False}
 (con/'lake-manifest.json').write_text(json.dumps(m,indent=2)+'\n')
 return prod,con
def maps(cache):
 p=cache/'outputs/probe_dep';return {x.name:json.loads(x.read_text()) for x in sorted(p.glob('*.json'))} if p.exists() else {}
def artifact_paths(prod):
 build=prod/'.lake/build'
 return {'olean':build/'lib/lean/Dep.olean','ilean':build/'lib/lean/Dep.ilean','c':build/'ir/Dep.c','setup':build/'ir/Dep.setup.json'}
def batch(label,prod,con,work):
 return run(label,[LEAN,'--json','Generated.lean'],con,work,leanpath=prod/'.lake/build/lib/lean')
def server(label,prod,con,work):
 path=con/'Generated.lean';source=path.read_text();e=env(work,leanpath=prod/'.lake/build/lib/lean')
 p=subprocess.Popen([str(LEAN),'--server'],cwd=con,env=e,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0,start_new_session=True)
 buf=b'';seen=[]
 def send(msg):
  raw=json.dumps(msg,separators=(',',':')).encode();p.stdin.write(b'Content-Length: '+str(len(raw)).encode()+b'\r\n\r\n'+raw);p.stdin.flush()
 def receive(deadline):
  nonlocal buf
  while time.monotonic()<deadline:
   if b'\r\n\r\n' in buf:
    head,body=buf.split(b'\r\n\r\n',1)
    lengths=[int(x.split(b':',1)[1]) for x in head.split(b'\r\n') if x.lower().startswith(b'content-length:')]
    if lengths and len(body)>=lengths[0]:
     raw,buf=body[:lengths[0]],body[lengths[0]:]
     msg=json.loads(raw);seen.append(msg)
     if msg.get('method')=='client/registerCapability' and 'id' in msg:send({'jsonrpc':'2.0','id':msg['id'],'result':None})
     return msg
   ready,_,_=select.select([p.stdout],[],[],min(.1,max(0,deadline-time.monotonic())))
   if ready:
    chunk=os.read(p.stdout.fileno(),65536)
    if not chunk:break
    buf+=chunk
  raise TimeoutError(label)
 def until(rid,seconds=15):
  end=time.monotonic()+seconds
  while time.monotonic()<end:
   m=receive(end)
   if m.get('id')==rid:return m
  raise TimeoutError(label)
 try:
  uri=path.as_uri();send({'jsonrpc':'2.0','id':1,'method':'initialize','params':{'processId':os.getpid(),'rootUri':con.as_uri(),'capabilities':{},'initializationOptions':{'hasWidgets':False}}});init=until(1)
  send({'jsonrpc':'2.0','method':'initialized','params':{}})
  send({'jsonrpc':'2.0','method':'textDocument/didOpen','params':{'textDocument':{'uri':uri,'languageId':'lean','version':1,'text':source}}})
  send({'jsonrpc':'2.0','id':2,'method':'textDocument/waitForDiagnostics','params':{'uri':uri,'version':1}});wait=until(2)
  diags=[m['params'] for m in seen if m.get('method')=='textDocument/publishDiagnostics' and m['params'].get('uri')==uri]
  send({'jsonrpc':'2.0','method':'textDocument/didClose','params':{'textDocument':{'uri':uri}}})
  send({'jsonrpc':'2.0','id':3,'method':'shutdown','params':None});until(3,5);send({'jsonrpc':'2.0','method':'exit','params':{}})
  try:p.wait(timeout=2)
  except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);p.wait(timeout=5)
  out={'label':label,'exit':p.returncode,'initialize':init,'wait':wait,'diagnostics':diags,'message_count':len(seen),'source_sha256':sha(path),'olean_sha256':sha(artifact_paths(prod)['olean'])}
 except Exception as exc:
  out={'label':label,'error':repr(exc),'messages':seen}
 finally:
  if p.poll() is None:os.killpg(p.pid,signal.SIGKILL);p.wait(timeout=5)
  out['process_exit']=p.returncode;out['stderr']=p.stderr.read().decode(errors='replace').replace(str(work),'$WORK')
 R['commands'].append({'label':label,'server':out});return out

def main():
 a=argparse.ArgumentParser();a.add_argument('--work',type=pathlib.Path,required=True);x=a.parse_args();work=x.work.resolve()
 if work.exists():raise SystemExit('--work must be absent and owned')
 if shutil.disk_usage(work.parent).free<15*(1<<30):raise SystemExit('15 GiB disk guard')
 mp=subprocess.run(['/usr/bin/memory_pressure','-Q'],capture_output=True,text=True,timeout=5)
 pct=int(mp.stdout.rsplit('System-wide memory free percentage:',1)[1].split('%',1)[0].strip())
 if pct<35:raise SystemExit(f'memory free {pct}% below 35% guard')
 assert LAKE.is_file() and LEAN.is_file()
 work.mkdir();(work/'home').mkdir();cache=work/'cache'
 R['environment']={'platform':platform.platform(),'lake_sha256':sha(LAKE),'lean_sha256':sha(LEAN),'free_percent_preflight':pct,
 'cache_root':'$WORK/cache','toolchain':TOOLCHAIN,'max_concurrent_commands':1,'command_timeout_seconds':30}
 for case,value,opt,manifest,extra in [('base',7,False,'probe_consumer',False),('path-copy',7,False,'probe_consumer',False),('source-nine',9,False,'probe_consumer',False),('source-extra',7,False,'probe_consumer',True),('option',7,True,'probe_consumer',False),('manifest',7,False,'probe_consumer_alt',False)]:
  prod,con=make(work/case,value,opt,manifest,extra)
  b=run(case+'-build',[LAKE,'--keep-toolchain','build','Dep'],con,work,cache)
  assert b['exit']==0,(case,b)
  setup=run(case+'-setup',[LAKE,'--keep-toolchain','--no-build','setup-file','Generated.lean'],con,work,cache)
  assert setup['exit']==0,(case,setup)
  paths=artifact_paths(prod);got={k:({'sha256':sha(v),'bytes':v.stat().st_size} if v.exists() else None) for k,v in paths.items()}
  R['cases'][case]={'source_sha256':sha(prod/'Dep.lean'),'producer_config_sha256':sha(prod/'lakefile.lean'),
   'consumer_manifest_sha256':sha(con/'lake-manifest.json'),'cache_maps':maps(cache),
   'artifacts':got,'batch':batch(case+'-batch',prod,con,work)['exit'],'setup_exit':setup['exit']}
 base=work/'base';nine=work/'source-nine';pa,pb=artifact_paths(base/'producer'),artifact_paths(nine/'producer')
 family_sources={'olean':pb['olean'],'ilean':artifact_paths(work/'source-extra'/'producer')['ilean'],
                 'c':pb['c'],'setup':artifact_paths(work/'option'/'producer')['setup']}
 assert all(pa[k].exists() and pb[k].exists() for k in ('olean','ilean','c','setup'))
 assert all(family_sources[k].exists() and sha(family_sources[k])!=sha(pa[k]) for k in family_sources)
 for family in ('olean','ilean','c','setup'):
  root=work/('mixed-'+family);shutil.copytree(base,root)
  prod,con=root/'producer',root/'consumer';dest=artifact_paths(prod)[family]
  dest.chmod(dest.stat().st_mode | 0o200);shutil.copyfile(family_sources[family],dest)
  before={k:sha(v) for k,v in artifact_paths(prod).items() if v.exists()}
  no=run('mixed-'+family+'-no-build',[LAKE,'--keep-toolchain','--no-build','build','Dep'],con,work,cache)
  st=run('mixed-'+family+'-setup',[LAKE,'--keep-toolchain','--no-build','setup-file','Generated.lean'],con,work,cache)
  setup_art=pathlib.Path(json.loads(st['stdout'])['importArts']['Dep'][0].replace('$WORK',str(work))) if st['exit']==0 else None
  if setup_art and setup_art.is_file():
   setup_root=work/('setup-import-'+family);setup_root.mkdir();shutil.copyfile(con/'Generated.lean',setup_root/'Generated.lean')
   (setup_root/'Dep.olean').symlink_to(setup_art)
   setup_batch=run('mixed-'+family+'-setup-import-batch',[LEAN,'--json','Generated.lean'],setup_root,work,leanpath=setup_root)
  else:setup_batch=None
  bt=batch('mixed-'+family+'-batch',prod,con,work)
  if family in ('olean','ilean','c'):
   isolated=work/('isolated-'+family);isolated.mkdir();shutil.copyfile(con/'Generated.lean',isolated/'Generated.lean')
   sv=server('mixed-'+family+'-server',prod,isolated,work)
  else:sv=None
  after={k:sha(v) for k,v in artifact_paths(prod).items() if v.exists()}
  R['cases']['mixed-'+family]={'before_artifact_sha256':before,'after_artifact_sha256':after,
   'no_build_exit':no['exit'],'setup_exit':st['exit'],'setup_import_olean_sha256':sha(setup_art) if setup_art and setup_art.is_file() else None,
   'setup_import_batch_exit':setup_batch['exit'] if setup_batch else None,'batch_exit':bt['exit'],'server':sv}
 # Existing valid native plug-in generations are copied into this package's evidence tree.
 plugin_dir=PKG/'support/artifacts'
 if plugin_dir.exists():shutil.rmtree(plugin_dir)
 plugin_dir.mkdir()
 plugins={}
 for version in ('v1','v2'):
  candidate=PRIOR/f'seed-{version}'/'.lake/build/lib/lean/plugin__probe_Plugin.dylib'
  assert candidate.is_file(),candidate
  target=plugin_dir/version/'plugin__probe_Plugin.dylib';target.parent.mkdir(exist_ok=True);shutil.copyfile(candidate,target)
  shutil.copyfile(PRIOR/f'seed-{version}'/'Plugin.lean',target.parent/'Plugin.lean')
  plugins[version]={'sha256':sha(target),'bytes':target.stat().st_size,'source_report_relative':str(candidate).split('/reports/',1)[-1]}
 # Explicit plugin loads use the archived source from the same prior fixture.
 proof=PRIOR/'seed-v1'/'Proof.lean';dep=PRIOR/'seed-v1'/'Dep.olean'
 if not dep.exists():dep=PRIOR/'seed-v1'/'.lake/build/lib/lean/Dep.olean'
 assert proof.is_file() and dep.is_file()
 plugroot=work/'plugin';plugroot.mkdir();shutil.copyfile(proof,plugroot/'Proof.lean');shutil.copyfile(dep,plugroot/'Dep.olean')
 shutil.copyfile(proof,plugin_dir/'Proof.lean');shutil.copyfile(dep,plugin_dir/'Dep.olean')
 plugin_results={}
 for version in ('v1','v2'):
  plug=plugin_dir/version/'plugin__probe_Plugin.dylib'
  marker=plugroot/f'marker-{version}.txt'
  p=run('plugin-'+version+'-batch',[LEAN,'--plugin='+str(plug),'--json','Proof.lean'],plugroot,work,leanpath=plugroot,extraenv={'PLUGIN_MARKER':str(marker)})
  plugin_results[version]={'exit':p['exit'],'stdout':p['stdout'],'stderr':p['stderr'],'dylib_sha256':sha(plug),
   'marker':marker.read_text() if marker.exists() else None,'marker_sha256':sha(marker) if marker.exists() else None}
 R['cases']['plugin']={'prebuilt_artifacts':plugins,'proof_sha256':sha(plugroot/'Proof.lean'),'dep_olean_sha256':sha(plugroot/'Dep.olean'),'fresh_batch':plugin_results}
 retained=plugin_dir/'retained'
 for case in ('base','path-copy','source-nine','source-extra','option','manifest'):
  root=work/case;d=retained/case;d.mkdir(parents=True)
  for src in (root/'producer/Dep.lean',root/'producer/lakefile.lean',root/'consumer/lakefile.lean',root/'consumer/lake-manifest.json'):
   shutil.copyfile(src,d/(src.parent.name+'-'+src.name))
  for kind,path in artifact_paths(root/'producer').items():
   if path.is_file():shutil.copyfile(path,d/('Dep.'+kind))
 for family in ('olean','ilean','c','setup'):
  d=retained/('mixed-'+family);d.mkdir(parents=True)
  p=artifact_paths(work/('mixed-'+family)/'producer')[family]
  shutil.copyfile(p,d/('Dep.'+family))
 R['retained_inventory']=inv(plugin_dir)
 R['limits']=['No power loss, native Linux/Windows filesystem, Mathlib, Anneal archive or generation manager.',
 'One pinned Lake/Lean revision; separate valid artifact generations are deliberately mixed under unchanged source.',
 'Server checks operate directly on Lean with LEAN_PATH; they do not attest an Anneal worker environment.',
 'Plugin dylibs are reused from the earlier pinned native-plugin report rather than rebuilt here.']
 (HERE/'results.json').write_text(json.dumps(R,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'cases':list(R['cases']),'commands':len(R['commands']),'cache_maps':{k:list(R['cases'][k]['cache_maps']) for k in ('base','path-copy','source-nine','source-extra','option','manifest')}}))
if __name__=='__main__':main()
