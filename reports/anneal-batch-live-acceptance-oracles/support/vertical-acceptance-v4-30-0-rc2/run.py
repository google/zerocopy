#!/usr/bin/env python3
"""Small illustrative Rust-comment -> Lean batch/live acceptance engine.

This is a prototype, not Charon, Aeneas, Lake, or current Anneal CLI code.
"""
import hashlib,json,os,re,select,subprocess,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
WORK=ROOT/'work';WORK.mkdir(exist_ok=True)
LEAN=Path(os.environ['LEAN_BIN']).resolve()
EVENTS=[];START=time.monotonic();SERVERS=[]
HOST_INITIAL='pub const MODEL_VALUE: u8 = 3;\n// anneal: theorem claim : modelValue = 3 := by\n// anneal:   exact ?_\n'
HOST_A='pub const MODEL_VALUE: u8 = 3;\n// anneal: theorem claim : modelValue = 3 := by\n// anneal:   rfl\n'
HOST_B='pub const MODEL_VALUE: u8 = 4;\n// anneal: theorem claim : modelValue = 4 := by\n// anneal:   rfl\n'
HOST_FAIL='pub const MODEL_VALUE: u8 = 5;\n// anneal: theorem claim : modelValue = 5 := by\n// anneal:   rfl\n'
def sha(x):return hashlib.sha256(x if isinstance(x,bytes) else x.encode()).hexdigest()
def rec(kind,**kw):EVENTS.append({'seq':len(EVENTS),'ms':round((time.monotonic()-START)*1000),'kind':kind,**kw})
def source_parts(rust):
 m=re.search(r'pub const MODEL_VALUE: u8 = (\d+);',rust)
 if not m:raise ValueError('unsupported Rust source shape')
 proof='import Generated\n'+''.join(line.removeprefix('// anneal: ')+'\n' for line in rust.splitlines() if line.startswith('// anneal: '))
 return int(m.group(1)),proof

def write_snapshot(name,rust,generated_override=None):
 d=WORK/name;d.mkdir(exist_ok=True)
 n,proof=source_parts(rust)
 generated=generated_override if generated_override is not None else f'import Lean\ndef modelValue : Nat := {n}\n'
 (d/'RustHost.rs').write_text(rust)
 (d/'Generated.lean').write_text(generated)
 (d/'Proof.lean').write_text(proof)
 rec('snapshot',name=name,rust_sha256=sha(rust),generated_sha256=sha(generated),proof_sha256=sha(proof),model_value=n)
 return d,proof

def run(label,argv,cwd,extra_env=None,timeout=20):
 env=dict(os.environ,LEAN_NUM_THREADS='1',**(extra_env or {}))
 p=subprocess.run(argv,cwd=cwd,env=env,capture_output=True,text=True,timeout=timeout)
 rec('command',label=label,argv=argv,cwd=str(cwd),rc=p.returncode,stdout=p.stdout,stderr=p.stderr)
 return p

def build_generated(name,d):
 (d/'Generated.olean').unlink(missing_ok=True)
 p=run(name+'-generated',[str(LEAN),'--json','-o','Generated.olean','Generated.lean'],d)
 path=d/'Generated.olean'
 rec('generated_build',name=name,rc=p.returncode,artifact_sha256=sha(path.read_bytes()) if path.exists() else None)
 return p.returncode==0

def check_proof(name,d,proof_text,expected):
 # Use captured source bytes for batch, then compile an importable proof artifact.
 (d/'Proof.lean').write_text(proof_text)
 (d/'Proof.olean').unlink(missing_ok=True)
 env={'LEAN_PATH':str(d)}
 batch=run(name+'-proof-batch',[str(LEAN),'--json','Proof.lean'],d,env)
 compiled=run(name+'-proof-olean',[str(LEAN),'--json','-o','Proof.olean','Proof.lean'],d,env) if batch.returncode==0 else None
 oracle='import Proof\nexample : modelValue = '+str(expected)+' := claim\n#print axioms claim\n'
 (d/'Oracle.lean').write_text(oracle)
 oracle_run=run(name+'-claim-oracle',[str(LEAN),'--json','Oracle.lean'],d,env) if compiled and compiled.returncode==0 else None
 rec('claim_comparison',name=name,expected=expected,proof_sha256=sha(proof_text),oracle_sha256=sha(oracle),batch_rc=batch.returncode,compiled_rc=compiled.returncode if compiled else None,oracle_rc=oracle_run.returncode if oracle_run else None,reported_sorry_ax=('sorryAx' in oracle_run.stdout) if oracle_run else None,proof_artifact_sha256=sha((d/'Proof.olean').read_bytes()) if (d/'Proof.olean').exists() else None)
 return batch.returncode, oracle_run.returncode if oracle_run else None

class Server:
 def __init__(self,label,d):
  self.label=label;self.d=d;self.buf=b'';self.nextid=2
  self.p=subprocess.Popen([str(LEAN),'--server'],cwd=d,env=dict(os.environ,LEAN_NUM_THREADS='1',LEAN_PATH=str(d)),stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0)
  SERVERS.append(self);rec('server_start',label=label,pid=self.p.pid,cwd=str(d))
  self.send({'jsonrpc':'2.0','id':1,'method':'initialize','params':{'processId':os.getpid(),'rootUri':d.as_uri(),'capabilities':{},'initializationOptions':{'hasWidgets':False}}})
  self.until(lambda m:m.get('id')==1)
  self.send({'jsonrpc':'2.0','method':'initialized','params':{}})
 def send(self,m):
  b=json.dumps(m,separators=(',',':')).encode();self.p.stdin.write(b'Content-Length: '+str(len(b)).encode()+b'\r\n\r\n'+b);self.p.stdin.flush();rec('client',label=self.label,message=m)
 def read(self,timeout=12):
  end=time.monotonic()+timeout
  while time.monotonic()<end:
   if b'\r\n\r\n' in self.buf:
    h,body=self.buf.split(b'\r\n\r\n',1);ls=[int(x.split(b':',1)[1]) for x in h.split(b'\r\n') if x.lower().startswith(b'content-length:')]
    if ls and len(body)>=ls[0]:
     raw,self.buf=body[:ls[0]],body[ls[0]:];m=json.loads(raw);rec('server',label=self.label,message=m)
     if m.get('method')=='client/registerCapability' and 'id' in m:self.send({'jsonrpc':'2.0','id':m['id'],'result':None})
     return m
   r,_,_=select.select([self.p.stdout],[],[],min(.1,max(0,end-time.monotonic())))
   if r:
    b=os.read(self.p.stdout.fileno(),65536)
    if not b:break
    self.buf+=b
  raise TimeoutError('read '+self.label)
 def until(self,pred,timeout=12):
  end=time.monotonic()+timeout
  while time.monotonic()<end:
   m=self.read(max(.1,end-time.monotonic()))
   if pred(m):return m
  raise TimeoutError('until '+self.label)
 def req(self,method,params):
  rid=self.nextid;self.nextid+=1;self.send({'jsonrpc':'2.0','id':rid,'method':method,'params':params});return self.until(lambda m:m.get('id')==rid)
 def open(self,name,text,version):
  uri=(self.d/name).as_uri();self.send({'jsonrpc':'2.0','method':'textDocument/didOpen','params':{'textDocument':{'uri':uri,'languageId':'lean','version':version,'text':text}}});return uri
 def edit(self,uri,text,version):self.send({'jsonrpc':'2.0','method':'textDocument/didChange','params':{'textDocument':{'uri':uri,'version':version},'contentChanges':[{'text':text}]}})
 def wait(self,uri,version):return self.req('textDocument/waitForDiagnostics',{'uri':uri,'version':version})
 def goal(self,uri,proof_text):return self.req('$/lean/plainGoal',{'textDocument':{'uri':uri},'position':{'line':2,'character':len(proof_text.splitlines()[2])}})
 def stop(self):
  if self.p.poll() is not None:return
  try:
   self.req('shutdown',None);self.send({'jsonrpc':'2.0','method':'exit'});self.p.wait(timeout=3)
  except Exception as e:rec('shutdown_failure',label=self.label,error=repr(e));self.p.kill();self.p.wait()
  rec('server_exit',label=self.label,rc=self.p.returncode,stderr=self.p.stderr.read().decode(errors='replace'))

CURRENT=WORK/'current.json'
HOST_AUTHORITY={'text':HOST_INITIAL,'revision':0}
def cas_host(expected_sha256,new_text):
 current_sha256=sha(HOST_AUTHORITY['text'])
 if current_sha256!=expected_sha256:
  rec('host_cas_rejected',expected_sha256=expected_sha256,actual_sha256=current_sha256,new_sha256=sha(new_text),revision=HOST_AUTHORITY['revision'])
  return False
 HOST_AUTHORITY['text']=new_text;HOST_AUTHORITY['revision']+=1
 rec('host_cas_accepted',expected_sha256=expected_sha256,new_sha256=sha(new_text),revision=HOST_AUTHORITY['revision'])
 return True
def publish(rev,name,d):
 old=json.loads(CURRENT.read_text()) if CURRENT.exists() else None
 if old and rev<=old['revision']:
  rec('publication_rejected_stale',candidate=name,candidate_revision=rev,current=old)
  return False
 if not (d/'Generated.olean').exists() or not (d/'Proof.olean').exists():
  rec('publication_rejected_incomplete',candidate=name,candidate_revision=rev,current=old)
  return False
 state={'revision':rev,'name':name,'rust_sha256':sha((d/'RustHost.rs').read_bytes()),'generated_sha256':sha((d/'Generated.lean').read_bytes()),'generated_olean_sha256':sha((d/'Generated.olean').read_bytes()),'proof_sha256':sha((d/'Proof.lean').read_bytes()),'proof_olean_sha256':sha((d/'Proof.olean').read_bytes())}
 temp=CURRENT.with_suffix('.tmp');temp.write_text(json.dumps(state,sort_keys=True)+'\n');temp.replace(CURRENT)
 rec('published',state=state)
 return True

try:
 CURRENT.unlink(missing_ok=True)
 rec('subject',lean_version=subprocess.check_output([str(LEAN),'--version'],text=True).strip(),lean_sha256=sha(LEAN.read_bytes()),engine='illustrative regex projection, no Charon/Aeneas/Lake')
 a0,p0=write_snapshot('A-initial',HOST_INITIAL)
 a,pa=write_snapshot('A',HOST_A)
 b,pb=write_snapshot('B',HOST_B)
 f,pf=write_snapshot('F-invalid',HOST_FAIL,'import Lean\ndef modelValue : Nat :=\n')
 assert build_generated('A',a)
 # The disk proof remains the unfinished annotation while the client owns unsaved A text.
 (a/'Proof.lean').write_text(p0)
 s=Server('A-live',a);u=s.open('Proof.lean',p0,1);s.wait(u,1);rec('A_initial_goal',response=s.goal(u,p0),disk_proof_sha256=sha((a/'Proof.lean').read_bytes()))
 # Application-level compare-and-swap from the exact captured host source.
 assert sha(HOST_INITIAL)==sha((a0/'RustHost.rs').read_bytes())
 assert cas_host(sha(HOST_INITIAL),HOST_A)
 s.edit(u,pa,2);s.wait(u,2);rec('A_edited_goal',response=s.goal(u,pa),disk_proof_sha256=sha((a/'Proof.lean').read_bytes()))
 s.stop()
 assert check_proof('A',a,pa,3)==(0,0)
 assert publish(1,'A',a)
 # Controlled obsolete build: a separate old-generation output waits at a Lean tactic gate.
 gate='import Lean\ndef modelValue : Nat := 3\ntheorem delayGate : True := by\n  run_tac do\n    IO.FS.writeFile "gate.entered" "1"\n    while !(← (System.FilePath.mk "gate.release").pathExists) do\n      IO.sleep 10\n  trivial\n'
 late,lateproof=write_snapshot('A-late',HOST_A,gate)
 for marker in ('gate.entered','gate.release','Generated.olean','Proof.olean'):(late/marker).unlink(missing_ok=True)
 late_proc=subprocess.Popen([str(LEAN),'--json','-o','Generated.olean','Generated.lean'],cwd=late,env=dict(os.environ,LEAN_NUM_THREADS='1'),stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
 rec('late_build_started',pid=late_proc.pid,argv=[str(LEAN),'--json','-o','Generated.olean','Generated.lean'])
 deadline=time.monotonic()+12
 while not (late/'gate.entered').exists() and time.monotonic()<deadline:time.sleep(.01)
 if not (late/'gate.entered').exists():raise TimeoutError('late build never entered gate')
 rec('late_build_entered_gate',pid=late_proc.pid)
 # The authoritative Rust source advances while the checked model remains A.
 assert cas_host(sha(HOST_A),HOST_FAIL)
 # Failed intermediate generated output cannot become current.
 assert not build_generated('F-invalid',f)
 assert not publish(2,'F-invalid',f)
 rec('provisional_failure',host_revision=HOST_AUTHORITY['revision'],host_sha256=sha(HOST_AUTHORITY['text']),last_good=json.loads(CURRENT.read_text()))
 assert cas_host(sha(HOST_FAIL),HOST_B)
 assert not cas_host(sha(HOST_A),HOST_INITIAL)
 # B has a changed Rust source, generated model, and matching proof.
 assert build_generated('B',b)
 assert check_proof('B',b,pb,4)==(0,0)
 assert publish(3,'B',b)
 # Late A completes only after B has published and cannot move current backward.
 (late/'gate.release').write_text('release')
 rec('late_build_gate_released',after_published_revision=json.loads(CURRENT.read_text())['revision'])
 out,err=late_proc.communicate(timeout=12)
 rec('late_build_finished',rc=late_proc.returncode,stdout=out,stderr=err,artifact_sha256=sha((late/'Generated.olean').read_bytes()) if (late/'Generated.olean').exists() else None)
 assert late_proc.returncode==0
 assert check_proof('A-late',late,lateproof,3)==(0,0)
 assert not publish(1,'A-late',late)
 # Fresh batch oracle negatives on B's immutable import artifact.
 stale='import Generated\ntheorem claim : modelValue = 3 := by\n  rfl\n'
 weak='import Generated\ntheorem claim : True := by\n  trivial\n'
 sd=WORK/'stale-on-B';sd.mkdir(exist_ok=True);(sd/'Stale.lean').write_text(stale)
 p=run('stale-proof-batch',[str(LEAN),'--json','Stale.lean'],sd,{'LEAN_PATH':str(b)})
 rec('stale_proof_comparison',rc=p.returncode,proof_sha256=sha(stale),model_artifact_sha256=sha((b/'Generated.olean').read_bytes()))
 assert p.returncode!=0
 wd=WORK/'weak-on-B';wd.mkdir(exist_ok=True)
 # The proof compiles, but the fixed proposition consumer rejects it.
 (wd/'Generated.olean').write_bytes((b/'Generated.olean').read_bytes())
 assert check_proof('weak-on-B',wd,weak,4)==(0,1)
 admitted='import Generated\ntheorem claim : modelValue = 4 := by\n  sorry\n'
 ad=WORK/'admitted-on-B';ad.mkdir(exist_ok=True)
 (ad/'Generated.olean').write_bytes((b/'Generated.olean').read_bytes())
 assert check_proof('admitted-on-B',ad,admitted,4)==(0,0)
 # Fresh interactive checks against the same B artifact and captured source.
 t=Server('B-live',b);v=t.open('Proof.lean',pb,1);t.wait(v,1);rec('B_goal',response=t.goal(v,pb));t.stop()
 z=Server('B-stale-proof',b);w=z.open('StaleProof.lean',stale,1);z.wait(w,1);rec('B_stale_goal',response=z.goal(w,stale));z.stop()
 rec('final_current',state=json.loads(CURRENT.read_text()),host_revision=HOST_AUTHORITY['revision'],host_sha256=sha(HOST_AUTHORITY['text']))
except Exception as e:rec('fatal',error=repr(e));raise
finally:
 for obj in SERVERS:
  if obj.p.poll() is None:obj.p.kill();obj.p.wait();rec('forced_server_exit',label=obj.label)
 if 'late_proc' in locals() and late_proc.poll() is None:
  (late/'gate.release').write_text('release');late_proc.kill();late_proc.wait();rec('forced_late_exit',pid=late_proc.pid)
 raw=json.dumps(EVENTS,indent=2)+'\n'
 raw=raw.replace(str(WORK),'$WORK').replace(str(LEAN),'$LEAN_BIN').replace(str(LEAN.parent.parent),'$LEAN_HOME')
 (ROOT/'transcript.json').write_text(raw)
