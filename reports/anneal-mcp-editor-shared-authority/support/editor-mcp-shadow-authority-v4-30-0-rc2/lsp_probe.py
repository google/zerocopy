#!/usr/bin/env python3
"""Direct Lean LSP probe of two documents, stale disk mirror, and process replay."""
import hashlib,json,os,select,subprocess,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
WORK=ROOT/'work';WORK.mkdir(exist_ok=True)
LEAN=Path(os.environ['LEAN_BIN']).resolve()
SHADOW=WORK/'Shadow.lean';OTHER=WORK/'Other.lean';MISSING=WORK/'Missing.lean'
GOOD='theorem demo : True := by\n  trivial\n'
BAD='theorem demo : False := by\n  exact ?_\n'
OTHER_TEXT='#check nonexistentName\n'
EVENTS=[];START=time.monotonic()
def digest(x):return hashlib.sha256(x if isinstance(x,bytes) else x.encode()).hexdigest()
def rec(kind,**x):EVENTS.append({'seq':len(EVENTS),'ms':round((time.monotonic()-START)*1000),'kind':kind,**x})
class Server:
 def __init__(self,label):
  self.label=label;self.buf=b'';self.nextid=2
  self.p=subprocess.Popen([str(LEAN),'--server'],cwd=WORK,env=dict(os.environ,LEAN_NUM_THREADS='1'),stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0)
  rec('start',server=label,pid=self.p.pid)
  self.send({'jsonrpc':'2.0','id':1,'method':'initialize','params':{'processId':os.getpid(),'rootUri':WORK.as_uri(),'capabilities':{},'initializationOptions':{'hasWidgets':False}}})
  self.until(lambda m:m.get('id')==1)
  self.send({'jsonrpc':'2.0','method':'initialized','params':{}})
 def send(self,m):
  b=json.dumps(m,separators=(',',':')).encode();self.p.stdin.write(b'Content-Length: '+str(len(b)).encode()+b'\r\n\r\n'+b);self.p.stdin.flush();rec('client',server=self.label,message=m)
 def read(self,timeout=12):
  end=time.monotonic()+timeout
  while time.monotonic()<end:
   if b'\r\n\r\n' in self.buf:
    h,body=self.buf.split(b'\r\n\r\n',1);ls=[int(x.split(b':',1)[1]) for x in h.split(b'\r\n') if x.lower().startswith(b'content-length:')]
    if ls and len(body)>=ls[0]:
     raw,self.buf=body[:ls[0]],body[ls[0]:];m=json.loads(raw);rec('server',server=self.label,message=m)
     if m.get('method')=='client/registerCapability' and 'id' in m:self.send({'jsonrpc':'2.0','id':m['id'],'result':None})
     return m
   ready,_,_=select.select([self.p.stdout],[],[],min(.1,max(0,end-time.monotonic())))
   if ready:
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
 def request(self,method,params):
  rid=self.nextid;self.nextid+=1;self.send({'jsonrpc':'2.0','id':rid,'method':method,'params':params});return self.until(lambda m:m.get('id')==rid)
 def open(self,path,text,version):self.send({'jsonrpc':'2.0','method':'textDocument/didOpen','params':{'textDocument':{'uri':path.as_uri(),'languageId':'lean','version':version,'text':text}}})
 def edit(self,path,text,version):self.send({'jsonrpc':'2.0','method':'textDocument/didChange','params':{'textDocument':{'uri':path.as_uri(),'version':version},'contentChanges':[{'text':text}]}})
 def close(self,path):self.send({'jsonrpc':'2.0','method':'textDocument/didClose','params':{'textDocument':{'uri':path.as_uri()}}})
 def wait(self,path,version):return self.request('textDocument/waitForDiagnostics',{'uri':path.as_uri(),'version':version})
 def goal(self,path):return self.request('$/lean/plainGoal',{'textDocument':{'uri':path.as_uri()},'position':{'line':1,'character':len('  exact ?_')}})
 def stop(self):
  if self.p.poll() is not None:return
  try:
   self.request('shutdown',None);self.send({'jsonrpc':'2.0','method':'exit'});self.p.wait(timeout=3)
  except Exception as e:rec('shutdown_error',server=self.label,error=repr(e));self.p.kill();self.p.wait()
  rec('exit',server=self.label,rc=self.p.returncode,stderr=self.p.stderr.read().decode(errors='replace'))

try:
 rec('subject',lean_version=subprocess.check_output([str(LEAN),'--version'],text=True).strip(),lean_sha256=digest(LEAN.read_bytes()),good_sha256=digest(GOOD),bad_sha256=digest(BAD),other_sha256=digest(OTHER_TEXT))
 SHADOW.write_text(BAD);OTHER.write_text(OTHER_TEXT);MISSING.unlink(missing_ok=True)
 rec('disk_start',shadow_sha256=digest(SHADOW.read_bytes()),other_sha256=digest(OTHER.read_bytes()))
 batch=subprocess.run([str(LEAN),'--json',str(SHADOW)],cwd=WORK,capture_output=True,text=True,timeout=20)
 rec('batch_shadow_bad',rc=batch.returncode,stdout=batch.stdout,stderr=batch.stderr)
 s=Server('initial')
 s.open(SHADOW,GOOD,1);s.open(OTHER,OTHER_TEXT,1)
 s.wait(SHADOW,1);s.wait(OTHER,1)
 rec('good_unsaved_goal',response=s.goal(SHADOW),disk_sha256=digest(SHADOW.read_bytes()))
 s.edit(SHADOW,BAD,2);s.wait(SHADOW,2)
 rec('bad_unsaved_goal',response=s.goal(SHADOW))
 s.edit(SHADOW,GOOD,3);s.wait(SHADOW,3)
 rec('good_unsaved_again',response=s.goal(SHADOW),disk_sha256=digest(SHADOW.read_bytes()))
 # The independent document remains open while Shadow diagnostics change twice.
 rec('other_still_open_goal',response=s.goal(OTHER))
 s.close(SHADOW)
 s.open(SHADOW,SHADOW.read_text(),4);s.wait(SHADOW,4)
 rec('reopen_from_disk_goal',response=s.goal(SHADOW))
 s.close(SHADOW)
 s.open(SHADOW,GOOD,5);s.wait(SHADOW,5)
 rec('reopen_from_authoritative_unsaved_text',response=s.goal(SHADOW),disk_sha256=digest(SHADOW.read_bytes()))
 s.p.kill();s.p.wait(timeout=3);rec('forced_watchdog_loss',pid=s.p.pid,rc=s.p.returncode)
 fresh=Server('replayed')
 fresh.open(SHADOW,GOOD,1);fresh.open(OTHER,OTHER_TEXT,1)
 fresh.wait(SHADOW,1);fresh.wait(OTHER,1)
 rec('replayed_shadow_goal',response=fresh.goal(SHADOW),disk_sha256=digest(SHADOW.read_bytes()))
 rec('replayed_other_goal',response=fresh.goal(OTHER))
 fresh.open(MISSING,GOOD,1);fresh.wait(MISSING,1)
 rec('missing_file_uri_unsaved_goal',response=fresh.goal(MISSING),disk_exists=MISSING.exists())
 fresh.close(MISSING)
 fresh.stop()
 custom=Server('custom-uri')
 custom_uri='untitled:AnnealProof.lean'
 custom.send({'jsonrpc':'2.0','method':'textDocument/didOpen','params':{'textDocument':{'uri':custom_uri,'languageId':'lean','version':1,'text':GOOD}}})
 try:
  wait_result=custom.request('textDocument/waitForDiagnostics',{'uri':custom_uri,'version':1})
  goal_result=custom.request('$/lean/plainGoal',{'textDocument':{'uri':custom_uri},'position':{'line':1,'character':9}})
  rec('custom_uri_result',wait=wait_result,goal=goal_result)
 except Exception as exc:rec('custom_uri_error',error=repr(exc))
 custom.stop()
except Exception as e:rec('fatal',error=repr(e));raise
finally:
 for obj in (locals().get('s'),locals().get('fresh'),locals().get('custom')):
  if obj is not None and obj.p.poll() is None:obj.p.kill();obj.p.wait();rec('forced_exit',server=obj.label)
 raw=json.dumps(EVENTS,indent=2)+'\n'
 raw=raw.replace(str(WORK),'$WORK').replace(str(LEAN),'$LEAN_BIN').replace(str(LEAN.parent.parent),'$LEAN_HOME')
 (ROOT/'transcript.json').write_text(raw)
