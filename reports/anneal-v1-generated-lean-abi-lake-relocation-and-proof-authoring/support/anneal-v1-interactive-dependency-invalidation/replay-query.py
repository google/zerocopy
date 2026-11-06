import argparse, hashlib, json, os, pathlib, select, subprocess, time
ARGS=argparse.ArgumentParser()
ARGS.add_argument('--workspace',required=True)
ARGS.add_argument('--evidence-dir',required=True)
ARGS=ARGS.parse_args()
ROOT=pathlib.Path(ARGS.workspace).resolve()
FILE=ROOT/'user/Probe.lean'; FUNS=ROOT/'generated/RelocateProbeRelocateProbe93d79f43b0c543cb/Funs.lean'
V1='''import Generated\n\ntheorem identity_pair (x : Aeneas.Std.U32) : (relocate_probe.identity x = Aeneas.Std.Result.ok x) ∧ True := by\n  apply And.intro\n'''
V2=V1.replace('  apply And.intro','  exact ⟨rfl, trivial⟩')
OUT=pathlib.Path(ARGS.evidence_dir).resolve();OUT.mkdir(parents=True,exist_ok=True);LOGDIR=OUT/'server-logs';LOGDIR.mkdir(exist_ok=True)
EVENTS=[];T0=time.monotonic();proc=None;buf=b'';reqid=0;COMPLETE=set()

def record(kind,data): EVENTS.append({'elapsed_ms':round((time.monotonic()-T0)*1000),'kind':kind,'data':data})
def send(m):
 raw=json.dumps(m,separators=(',',':')).encode();proc.stdin.write(b'Content-Length: '+str(len(raw)).encode()+b'\r\n\r\n'+raw);proc.stdin.flush();record('client',m)
def recv(pred,timeout=45):
 global buf
 end=time.monotonic()+timeout
 while time.monotonic()<end:
  while b'\r\n\r\n' in buf:
   h,rest=buf.split(b'\r\n\r\n',1);ls=[int(z.split(b':',1)[1]) for z in h.split(b'\r\n') if z.lower().startswith(b'content-length:')]
   if not ls or len(rest)<ls[0]:break
   raw,buf=rest[:ls[0]],rest[ls[0]:];m=json.loads(raw);record('server',m)
   if m.get('method')=='$/lean/fileProgress':
    p=m.get('params',{});td=p.get('textDocument',{})
    if td.get('uri')==FILE.as_uri() and not p.get('processing'): COMPLETE.add(td.get('version'))
   if m.get('method')=='client/registerCapability' and 'id' in m:send({'jsonrpc':'2.0','id':m['id'],'result':None})
   if pred(m):return m
  rd,_,_=select.select([proc.stdout],[],[],min(.1,max(0,end-time.monotonic())))
  if rd:
   c=os.read(proc.stdout.fileno(),65536)
   if not c:break
   buf+=c
 raise TimeoutError('LSP response timeout')
def request(method,params):
 global reqid
 reqid+=1;rid=reqid;send({'jsonrpc':'2.0','id':rid,'method':method,'params':params});return recv(lambda m:m.get('id')==rid)
def await_diagnostics(version):
 request('textDocument/waitForDiagnostics',{'uri':FILE.as_uri(),'version':version})
 if version not in COMPLETE: recv(lambda m:m.get('method')=='$/lean/fileProgress' and m.get('params',{}).get('textDocument',{}).get('uri')==FILE.as_uri() and m.get('params',{}).get('textDocument',{}).get('version')==version and not m.get('params',{}).get('processing'),timeout=90)
def cursor(label,char):
 m=request('$/lean/plainGoal',{'textDocument':{'uri':FILE.as_uri()},'position':{'line':3,'character':char}})
 record('goal_observation',{'label':label,'character':char,'result':m.get('result'),'error':m.get('error')});return m
def open_server(label,source):
 global proc,buf
 proc=subprocess.Popen(['lake','--offline','env','lean','--server'],cwd=ROOT,env=dict(os.environ,LEAN_SERVER_LOG_DIR=str(LOGDIR)),stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0);buf=b''
 record('server_start',{'label':label,'pid':proc.pid,'cwd':str(ROOT)})
 request('initialize',{'processId':os.getpid(),'rootUri':ROOT.as_uri(),'capabilities':{},'initializationOptions':{'hasWidgets':False,'logCfg':{'logDir':str(LOGDIR)}}})
 send({'jsonrpc':'2.0','method':'initialized','params':{}});FILE.parent.mkdir(parents=True,exist_ok=True);FILE.write_text(source)
 record('source_snapshot',{'label':label,'sha256':hashlib.sha256(source.encode()).hexdigest(),'text':source})
 send({'jsonrpc':'2.0','method':'textDocument/didOpen','params':{'textDocument':{'uri':FILE.as_uri(),'languageId':'lean','version':1,'text':source}}})
 await_diagnostics(1)
def edit(source,version,label):
 FILE.write_text(source);send({'jsonrpc':'2.0','method':'textDocument/didChange','params':{'textDocument':{'uri':FILE.as_uri(),'version':version},'contentChanges':[{'text':source}]}})
 await_diagnostics(version)
 cursor(label+'-before-tactic',2);cursor(label+'-after-tactic',len(source.splitlines()[3]))
def stop(label):
 global proc
 if proc and proc.poll() is None:request('shutdown',None);send({'jsonrpc':'2.0','method':'exit'});proc.wait(timeout=10)
 err=proc.stderr.read().decode(errors='replace') if proc else ''
 record('server_stop',{'label':label,'exit_code':proc.returncode if proc else None,'stderr':err});proc=None
def main():
 base=FUNS.read_text();needle='def identity (x : Std.U32) : Result Std.U32 := do\n  ok (U32.ofNat 0)';replacement='def identity (x : Std.U32) : Result Std.U32 := do\n  ok x'
 if needle in base:FUNS.write_text(base.replace(needle,replacement,1))
 initial=subprocess.run(['lake','--offline','build','Generated'],cwd=ROOT,capture_output=True,text=True,timeout=180)
 record('baseline_generated_build',{'exit_code':initial.returncode,'stdout':initial.stdout,'stderr':initial.stderr})
 if initial.returncode:raise RuntimeError('baseline Generated target failed')
 FILE.parent.mkdir(parents=True,exist_ok=True)
 for label,source in [('batch-v1-open-subgoals',V1),('batch-v2-proved',V2)]:
  FILE.write_text(source);p=subprocess.run(['lake','--offline','env','lean',str(FILE.relative_to(ROOT)),'--json'],cwd=ROOT,capture_output=True,text=True,timeout=60)
  record(label,{'exit_code':p.returncode,'stdout':p.stdout,'stderr':p.stderr,'source_sha256':hashlib.sha256(source.encode()).hexdigest()})
 open_server('initial',V1);cursor('initial-before-tactic',2);cursor('initial-after-tactic',len(V1.splitlines()[3]))
 edit(V2,2,'edited-v2')
 original=FUNS.read_text();old='def identity (x : Std.U32) : Result Std.U32 := do\n  ok x';new='def identity (x : Std.U32) : Result Std.U32 := do\n  ok (U32.ofNat 0)'
 if old not in original:raise RuntimeError('expected identity source not found')
 FUNS.write_text(original.replace(old,new,1));record('dependency_source_edit',{'path':str(FUNS.relative_to(ROOT)),'before_sha256':hashlib.sha256(original.encode()).hexdigest(),'after_sha256':hashlib.sha256(FUNS.read_bytes()).hexdigest()})
 build=subprocess.run(['lake','--offline','build','Generated'],cwd=ROOT,capture_output=True,text=True,timeout=180)
 record('dependency_rebuild',{'exit_code':build.returncode,'stdout':build.stdout,'stderr':build.stderr})
 if build.returncode:raise RuntimeError('edited Generated target failed to build')
 send({'jsonrpc':'2.0','method':'workspace/didChangeWatchedFiles','params':{'changes':[{'uri':(ROOT/'generated/RelocateProbeRelocateProbe93d79f43b0c543cb/Funs.lean').as_uri(),'type':2}]}})
 record('notify_dependency_change',{'uri':(ROOT/'generated/RelocateProbeRelocateProbe93d79f43b0c543cb/Funs.lean').as_uri()})
 edit(V2,3,'same-server-after-dependency-rebuild')
 stop('same-server-after-dependency-rebuild')
 open_server('fresh-process-after-dependency-rebuild',V2)
 cursor('fresh-after-change-before-tactic',2);cursor('fresh-after-change-after-tactic',len(V2.splitlines()[3]))
 stop('fresh-process-after-dependency-rebuild')
 for label,source in [('Probe-v1.lean',V1),('Probe-v2.lean',V2)]: (OUT/label).write_text(source)
 (OUT/'interactive-transcript.json').write_text(json.dumps(EVENTS,indent=2)+'\n')
 print(json.dumps({'events':len(EVENTS),'goals':[e['data'] for e in EVENTS if e['kind']=='goal_observation'],'batch_exit_codes':{e['kind']:e['data']['exit_code'] for e in EVENTS if e['kind'].startswith('batch-')},'build_exit_codes':{e['kind']:e['data']['exit_code'] for e in EVENTS if e['kind'].endswith('build')},'transcript':str(OUT/'interactive-transcript.json')},indent=2))
try:main()
except Exception as e:
 record('fatal',{'error':repr(e)})
 if proc and proc.poll() is None:proc.kill();proc.wait()
 (OUT/'interactive-transcript.json').write_text(json.dumps(EVENTS,indent=2)+'\n');raise
