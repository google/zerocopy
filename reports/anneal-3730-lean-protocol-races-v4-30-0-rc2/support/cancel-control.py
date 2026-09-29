#!/usr/bin/env python3
"""Version/cancellation race with a tactic-file handshake; direct Lean server."""
import hashlib, json, os, select, subprocess, time
from pathlib import Path
ROOT = Path(__file__).resolve().parent
WORK = ROOT / 'work'
WORK.mkdir(exist_ok=True)
LEAN = Path(os.environ['LEAN_BIN']).resolve()
FILE = WORK / 'Proof.lean'
V1 = '''import Lean

theorem demo : True := by
  run_tac do
    IO.FS.writeFile "gate.entered" "1"
    while !(← (System.FilePath.mk "gate.release").pathExists) do
      IO.sleep 10
  trivial
'''
V2 = '''import Lean

theorem demo : False := by
  exact ?_
'''
EV=[]; START=time.monotonic()
def sha(x): return hashlib.sha256(x if isinstance(x,bytes) else x.encode()).hexdigest()
def log(kind, **kw): EV.append(dict(ms=round((time.monotonic()-START)*1000),kind=kind,**kw))
class Server:
  def __init__(self,label):
    self.label=label;self.buf=b''
    self.p=subprocess.Popen([str(LEAN),'--server'],cwd=WORK,env=dict(os.environ,LEAN_NUM_THREADS='1'),stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0)
    log('server_start',server=label,pid=self.p.pid)
    self.send(dict(jsonrpc='2.0',id=1,method='initialize',params=dict(processId=os.getpid(),rootUri=WORK.as_uri(),capabilities={},initializationOptions={'hasWidgets':False})))
    self.until(lambda m:m.get('id')==1)
    self.send(dict(jsonrpc='2.0',method='initialized',params={}))
  def send(self,m):
    b=json.dumps(m,separators=(',',':')).encode();self.p.stdin.write(b'Content-Length: '+str(len(b)).encode()+b'\r\n\r\n'+b);self.p.stdin.flush()
    log('client',server=self.label,message=m)
  def read(self,limit=15):
    end=time.monotonic()+limit
    while time.monotonic()<end:
      if b'\r\n\r\n' in self.buf:
        h,body=self.buf.split(b'\r\n\r\n',1)
        sizes=[int(x.split(b':',1)[1]) for x in h.split(b'\r\n') if x.lower().startswith(b'content-length:')]
        if sizes and len(body)>=sizes[0]:
          raw,self.buf=body[:sizes[0]],body[sizes[0]:]
          m=json.loads(raw);log('server',server=self.label,message=m)
          if m.get('method')=='client/registerCapability' and 'id' in m:self.send(dict(jsonrpc='2.0',id=m['id'],result=None))
          return m
      ready,_,_=select.select([self.p.stdout],[],[],min(.1,max(0,end-time.monotonic())))
      if ready:
        b=os.read(self.p.stdout.fileno(),65536)
        if not b:break
        self.buf+=b
    raise TimeoutError('server read: '+self.label)
  def until(self,pred,limit=15):
    end=time.monotonic()+limit
    while time.monotonic()<end:
      m=self.read(max(.1,end-time.monotonic()))
      if pred(m):return m
    raise TimeoutError('server until: '+self.label)
  def stop(self):
    try:
      self.send(dict(jsonrpc='2.0',id=99,method='shutdown',params=None));self.until(lambda m:m.get('id')==99,5)
      self.send(dict(jsonrpc='2.0',method='exit'));self.p.wait(timeout=5)
    except Exception as e:
      log('shutdown_error',server=self.label,error=repr(e));self.p.kill();self.p.wait()
    log('server_exit',server=self.label,pid=self.p.pid,rc=self.p.returncode,stderr=self.p.stderr.read().decode(errors='replace'))

def batch(label,text):
  FILE.write_text(text)
  p=subprocess.run([str(LEAN),'--json',str(FILE)],cwd=WORK,capture_output=True,text=True,timeout=20)
  log('batch',label=label,source_sha256=sha(text),rc=p.returncode,stdout=p.stdout,stderr=p.stderr)

def open_doc(s,txt,version):
  s.send(dict(jsonrpc='2.0',method='textDocument/didOpen',params={'textDocument':dict(uri=FILE.as_uri(),languageId='lean',version=version,text=txt)}))
def wait_req(s,rid,version):
  s.send(dict(jsonrpc='2.0',id=rid,method='textDocument/waitForDiagnostics',params={'uri':FILE.as_uri(),'version':version}))
def goal_req(s,rid,version):
  s.send(dict(jsonrpc='2.0',id=rid,method='$/lean/plainGoal',params={'textDocument':{'uri':FILE.as_uri(),'version':version},'position':{'line':3,'character':9}}))

try:
  log('subject',lean_version=subprocess.check_output([str(LEAN),'--version'],text=True).strip(),lean_sha256=sha(LEAN.read_bytes()),v1_sha256=sha(V1),v2_sha256=sha(V2))
  (WORK/'gate.release').write_text('release')
  batch('v1',V1);batch('v2',V2)
  (WORK/'gate.release').unlink();(WORK/'gate.entered').unlink(missing_ok=True)
  FILE.write_text(V1)
  s=Server('race')
  open_doc(s,V1,1);wait_req(s,10,1)
  deadline=time.monotonic()+12
  while not (WORK/'gate.entered').exists() and time.monotonic()<deadline:time.sleep(.01)
  if not (WORK/'gate.entered').exists():raise TimeoutError('tactic did not enter gate')
  log('tactic_entered',gate_sha256=sha((WORK/'gate.entered').read_bytes()))
  s.send(dict(jsonrpc='2.0',id=23,method='$/lean/plainGoal',params={'textDocument':{'uri':FILE.as_uri(),'version':1},'position':{'line':7,'character':9}}))
  s.send(dict(jsonrpc='2.0',method='$/cancelRequest',params={'id':23}))
  (WORK/'gate.release').write_text('release');log('gate_released_for_cancel')
  s.until(lambda m:m.get('id')==23,5)
  log('explicit_cancel_completed_before_edit')
  goal_req(s,20,1)
  s.send(dict(jsonrpc='2.0',method='textDocument/didChange',params={'textDocument':{'uri':FILE.as_uri(),'version':2},'contentChanges':[{'text':V2}]}))
  log('edit_sent_after_enter_and_goal_request')
  (WORK/'gate.release').write_text('release');log('gate_released')
  wait_req(s,11,2)
  pending={10,11,20};deadline=time.monotonic()+20
  while pending and time.monotonic()<deadline:
    m=s.read(max(.1,deadline-time.monotonic()))
    if m.get('id') in pending:pending.remove(m['id'])
  log('pending_after_barrier',ids=sorted(pending))
  wait_req(s,12,1)
  s.until(lambda m:m.get('id')==12)
  goal_req(s,21,1)
  s.until(lambda m:m.get('id')==21)
  goal_req(s,22,2)
  s.until(lambda m:m.get('id')==22)
  s.stop()
  # New transport and worker; reuse URI, document version, and request IDs.
  FILE.write_text(V2)
  fresh=Server('fresh-v2')
  open_doc(fresh,V2,1);wait_req(fresh,10,1)
  fresh.until(lambda m:m.get('id')==10)
  goal_req(fresh,20,1)
  fresh.until(lambda m:m.get('id')==20)
  fresh.stop()
except Exception as e:
  log('fatal',error=repr(e))
  raise
finally:
  for obj in (locals().get('s'),locals().get('fresh')):
    if obj is not None and obj.p.poll() is None:obj.p.kill();obj.p.wait();log('forced_exit',server=obj.label)
  raw=json.dumps(EV,indent=2)+'\n'
  raw=raw.replace(str(WORK),'$WORK').replace(str(LEAN),'$LEAN_BIN')
  (ROOT/'transcript.json').write_text(raw)
