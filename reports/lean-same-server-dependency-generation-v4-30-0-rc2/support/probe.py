#!/usr/bin/env python3
"""Probe old/new dependent workers in one direct Lean --server process."""
import hashlib, json, os, select, subprocess, time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
FIXTURE=ROOT/'fixture'
FIXTURE.mkdir(exist_ok=True)
LEAN=Path(os.environ['LEAN_BIN']).resolve()
EVENTS=[]
def digest(data): return hashlib.sha256(data if isinstance(data,bytes) else data.encode()).hexdigest()
def record(kind,**kw): EVENTS.append({'kind':kind,'time_monotonic':time.monotonic(),**kw})

def build_dep(value):
 src=f'def sharedValue : Nat := {value}\n'
 dep=FIXTURE/'Dep.lean'; dep.write_text(src)
 cmd=[str(LEAN),'-o','Dep.olean','Dep.lean']
 p=subprocess.run(cmd,cwd=FIXTURE,env=dict(os.environ,LEAN_NUM_THREADS='1'),capture_output=True,text=True,timeout=30)
 record('build_dependency',value=value,argv=cmd,returncode=p.returncode,stdout=p.stdout,stderr=p.stderr,source_sha256=digest(src),olean_sha256=digest((FIXTURE/'Dep.olean').read_bytes()) if (FIXTURE/'Dep.olean').exists() else None)
 if p.returncode: raise RuntimeError(f'Dep build failed: {p.stderr}')
 return src

class Server:
 def __init__(self):
  self.buf=b''; self.seq=1
  self.p=subprocess.Popen([str(LEAN),'--server'],cwd=FIXTURE,env=dict(os.environ,LEAN_NUM_THREADS='1',LEAN_PATH=str(FIXTURE)),stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0)
  record('server_start',pid=self.p.pid,argv=[str(LEAN),'--server'],cwd=str(FIXTURE),LEAN_PATH=str(FIXTURE))
  r=self.req('initialize',{'processId':os.getpid(),'rootUri':FIXTURE.as_uri(),'capabilities':{},'initializationOptions':{'hasWidgets':False}})
  self.send({'jsonrpc':'2.0','method':'initialized','params':{}})
 def send(self,msg):
  b=json.dumps(msg,separators=(',',':')).encode()
  self.p.stdin.write(b'Content-Length: '+str(len(b)).encode()+b'\r\n\r\n'+b); self.p.stdin.flush()
  record('client_message',message=msg)
 def recv(self,timeout=15):
  deadline=time.monotonic()+timeout
  while time.monotonic()<deadline:
   while b'\r\n\r\n' in self.buf:
    head,body=self.buf.split(b'\r\n\r\n',1)
    sizes=[int(x.split(b':',1)[1]) for x in head.split(b'\r\n') if x.lower().startswith(b'content-length:')]
    if not sizes or len(body)<sizes[0]: break
    raw,self.buf=body[:sizes[0]],body[sizes[0]:]
    msg=json.loads(raw); record('server_message',message=msg)
    if 'method' in msg and 'id' in msg:
     self.send({'jsonrpc':'2.0','id':msg['id'],'result':None})
    return msg
   ready,_,_=select.select([self.p.stdout],[],[],min(.2,max(0,deadline-time.monotonic())))
   if ready:
    chunk=os.read(self.p.stdout.fileno(),65536)
    if not chunk: break
    self.buf+=chunk
  raise TimeoutError('Lean server response timeout')
 def req(self,method,params,timeout=15):
  rid=self.seq; self.seq+=1; self.send({'jsonrpc':'2.0','id':rid,'method':method,'params':params})
  deadline=time.monotonic()+timeout
  while time.monotonic()<deadline:
   msg=self.recv(max(.1,deadline-time.monotonic()))
   if 'method' not in msg and msg.get('id')==rid: return msg
  raise TimeoutError(f'No result for {method} id={rid}')
 def open_doc(self,name,text,version=1):
  path=FIXTURE/name; path.write_text(text)
  uri=path.as_uri()
  self.send({'jsonrpc':'2.0','method':'textDocument/didOpen','params':{'textDocument':{'uri':uri,'languageId':'lean','version':version,'text':text}}})
  barrier=self.req('textDocument/waitForDiagnostics',{'uri':uri,'version':version})
  return path,uri,barrier
 def close_doc(self,uri):
  self.send({'jsonrpc':'2.0','method':'textDocument/didClose','params':{'textDocument':{'uri':uri}}})
 def goal(self,uri,version):
  line='  rfl'
  return self.req('$/lean/plainGoal',{'textDocument':{'uri':uri,'version':version},'position':{'line':2,'character':len(line)}})
 def stop(self):
  try:
   self.req('shutdown',None,timeout=5); self.send({'jsonrpc':'2.0','method':'exit'}); self.p.wait(timeout=5)
  except Exception as e:
   record('shutdown_failure',error=repr(e)); self.p.kill(); self.p.wait()
  record('server_exit',pid=self.p.pid,returncode=self.p.returncode,stderr=self.p.stderr.read().decode(errors='replace'))

try:
 build_dep(3)
 proof='import Dep\ntheorem current : sharedValue = 3 := by\n  rfl\n'
 srv=Server()
 old_path,old_uri,old_barrier=srv.open_doc('OldOpen.lean',proof)
 old_before=srv.goal(old_uri,1)
 record('old_worker_before_change',barrier=old_barrier,goal=old_before,source_sha256=digest(proof))
 old_olean=(FIXTURE/'Dep.olean').read_bytes(); old_olean_hash=digest(old_olean)
 build_dep(4)
 new_olean_hash=digest((FIXTURE/'Dep.olean').read_bytes())
 record('artifact_changed',old_olean_sha256=old_olean_hash,new_olean_sha256=new_olean_hash,changed=old_olean_hash!=new_olean_hash)
 # The old open worker has the original imported environment. A source watcher
 # is sent to exercise the documented refresh path without assuming success.
 srv.send({'jsonrpc':'2.0','method':'workspace/didChangeWatchedFiles','params':{'changes':[{'uri':(FIXTURE/'Dep.lean').as_uri(),'type':2}]}})
 old_after=srv.goal(old_uri,1)
 record('old_worker_after_dependency_rebuild',goal=old_after)
 new_path,new_uri,new_barrier=srv.open_doc('NewOpen.lean',proof)
 new_goal=srv.goal(new_uri,1)
 record('new_worker_same_server_after_dependency_rebuild',barrier=new_barrier,goal=new_goal,source_sha256=digest(proof))
 srv.close_doc(old_uri)
 reopened_path,reopened_uri,reopen_barrier=srv.open_doc('OldOpen.lean',proof,version=2)
 reopened_goal=srv.goal(reopened_uri,2)
 record('closed_reopened_worker_after_dependency_rebuild',barrier=reopen_barrier,goal=reopened_goal,source_sha256=digest(proof))
 batch=subprocess.run([str(LEAN),'--json',str(new_path)],cwd=FIXTURE,env=dict(os.environ,LEAN_NUM_THREADS='1',LEAN_PATH=str(FIXTURE)),capture_output=True,text=True,timeout=30)
 record('fresh_batch_after_dependency_rebuild',returncode=batch.returncode,stdout=batch.stdout,stderr=batch.stderr,source_sha256=digest(proof))
 srv.stop()
 diagnostics=[e['message']['params'] for e in EVENTS if e.get('kind')=='server_message' and e['message'].get('method')=='textDocument/publishDiagnostics']
 result={'lean_version':subprocess.check_output([str(LEAN),'--version'],text=True).strip(),'old_olean_sha256':old_olean_hash,'new_olean_sha256':new_olean_hash,'old_worker_goal_before':old_before,'old_worker_goal_after':old_after,'new_worker_goal_same_server':new_goal,'reopened_worker_goal_same_server':reopened_goal,'fresh_batch_returncode':batch.returncode,'diagnostics':diagnostics,'events':EVENTS}
 raw=json.dumps(result,indent=2)+'\n'
 raw=raw.replace(str(FIXTURE),'$FIXTURE').replace(str(LEAN),'$LEAN_BIN')
 (ROOT/'transcript.json').write_text(raw)
 print(json.dumps({k:v for k,v in result.items() if k!='events'},indent=2))
except Exception as e:
 record('fatal',error=repr(e))
 (ROOT/'transcript.json').write_text(json.dumps({'events':EVENTS},indent=2)+'\n')
 raise
