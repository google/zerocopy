#!/usr/bin/env python3
"""Direct Lean imported-proof state probe; no Anneal/editor integration."""
import argparse,hashlib,json,os,select,shutil,subprocess,time
from pathlib import Path

HERE=Path(__file__).resolve().parent
LEAN=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean')
A0='theorem helper (n : Nat) : n + 0 = n := by\n  simp\n'
A1='theorem helper (n : Nat) : n + 1 = n + 1 := by\n  rfl\n'
A_UNSAVED=A1+'theorem unsavedOnly : True := by\n  trivial\n'
B='import A\ntheorem consumer (n : Nat) : n + 0 = n := by\n  exact helper n\n'
B_UNSAVED='import A\ntheorem consumer : True := by\n  exact unsavedOnly\n'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def textsha(s):return hashlib.sha256(s.encode()).hexdigest()

class Server:
 def __init__(self,work,path):
  self.work=work;self.path=path;self.buf=b'';self.seq=0;self.messages=[]
  self.p=subprocess.Popen([str(LEAN),'--server'],cwd=work,env=dict(os.environ,LEAN_PATH=str(path),LEAN_NUM_THREADS='1'),stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0)
  self.req('initialize',{'processId':os.getpid(),'rootUri':work.as_uri(),'capabilities':{},'initializationOptions':{'hasWidgets':False}})
  self.send({'jsonrpc':'2.0','method':'initialized','params':{}})
 def send(self,m):
  raw=json.dumps(m,separators=(',',':')).encode();self.p.stdin.write(b'Content-Length: '+str(len(raw)).encode()+b'\r\n\r\n'+raw);self.p.stdin.flush()
  self.messages.append({'side':'client','message':m})
 def recv(self,pred,timeout=20):
  deadline=time.monotonic()+timeout
  while time.monotonic()<deadline:
   while b'\r\n\r\n' in self.buf:
    header,body=self.buf.split(b'\r\n\r\n',1)
    lens=[int(x.split(b':',1)[1]) for x in header.split(b'\r\n') if x.lower().startswith(b'content-length:')]
    if not lens or len(body)<lens[0]:break
    raw,self.buf=body[:lens[0]],body[lens[0]:];m=json.loads(raw)
    self.messages.append({'side':'server','message':m})
    if m.get('method')=='client/registerCapability' and 'id' in m:self.send({'jsonrpc':'2.0','id':m['id'],'result':None})
    if pred(m):return m
   ready,_,_=select.select([self.p.stdout],[],[],max(0,deadline-time.monotonic()))
   if not ready:break
   raw=os.read(self.p.stdout.fileno(),65536)
   if not raw:break
   self.buf+=raw
  raise TimeoutError('server response')
 def req(self,method,params):
  self.seq+=1;id_=self.seq;self.send({'jsonrpc':'2.0','id':id_,'method':method,'params':params})
  return self.recv(lambda m:m.get('id')==id_)
 def notify(self,method,params):self.send({'jsonrpc':'2.0','method':method,'params':params})
 def open(self,name,text,version=1):
  uri=(self.work/name).as_uri();self.notify('textDocument/didOpen',{'textDocument':{'uri':uri,'languageId':'lean','version':version,'text':text}})
  barrier=self.req('textDocument/waitForDiagnostics',{'uri':uri,'version':version})
  return {'uri':uri,'version':version,'barrier':barrier,'diagnostics':self.diag(uri,version)}
 def change(self,name,text,version):
  uri=(self.work/name).as_uri();self.notify('textDocument/didChange',{'textDocument':{'uri':uri,'version':version},'contentChanges':[{'text':text}]})
  barrier=self.req('textDocument/waitForDiagnostics',{'uri':uri,'version':version})
  return {'uri':uri,'version':version,'barrier':barrier,'diagnostics':self.diag(uri,version)}
 def diag(self,uri,version):
  pub=[e['message']['params'] for e in self.messages if e['side']=='server' and e['message'].get('method')=='textDocument/publishDiagnostics']
  got=[p['diagnostics'] for p in pub if p.get('uri')==uri and p.get('version')==version]
  return got[-1] if got else None
 def goal(self,name,version,line=2,char=2):
  return self.req('$/lean/plainGoal',{'textDocument':{'uri':(self.work/name).as_uri(),'version':version},'position':{'line':line,'character':char}})
 def hover(self,name,version):
  return self.req('textDocument/hover',{'textDocument':{'uri':(self.work/name).as_uri(),'version':version},'position':{'line':2,'character':10}})
 def close(self,name):self.notify('textDocument/didClose',{'textDocument':{'uri':(self.work/name).as_uri()}})
 def stop(self):
  self.req('shutdown',None);self.notify('exit',None);self.p.wait(timeout=5)
  assert self.p.returncode==0
  return {'exit':self.p.returncode,'stderr':self.p.stderr.read().decode(errors='replace')}

def batch(work,name,path=None,build=False):
 cmd=[str(LEAN)]+(['-o',str(work/'A.olean')] if build else ['--json'])+[name]
 p=subprocess.run(cmd,cwd=work,env=dict(os.environ,LEAN_PATH=str(path or work),LEAN_NUM_THREADS='1'),capture_output=True,text=True,timeout=30)
 return {'argv':[str(LEAN),'…',name],'exit':p.returncode,'stdout':p.stdout.replace(str(work),'$WORK'),'stderr':p.stderr.replace(str(work),'$WORK'),
         'lean_path':str(path or work).replace(str(work),'$WORK')}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--work',type=Path,required=True);args=ap.parse_args();work=args.work.resolve()
 assert not work.exists();assert shutil.disk_usage(work.parent).free>15*(1<<30)
 work.mkdir();(work/'A.lean').write_text(A0);(work/'B.lean').write_text(B)
 artifacts=HERE/'artifacts';artifacts.mkdir(exist_ok=True)
 events=[]
 def row(step,**kw):events.append({'step':step,**kw})
 initial=batch(work,'A.lean',build=True);assert initial['exit']==0
 o0=sha(work/'A.olean');b0=batch(work,'B.lean');assert b0['exit']==0
 (artifacts/'A0.lean').write_text(A0);shutil.copyfile(work/'A.olean',artifacts/'A0.olean')
 row('saved_initial',a_source_sha256=sha(work/'A.lean'),a_olean_sha256=o0,b_batch=b0)
 srv=Server(work,work)
 open_a=srv.open('A.lean',A0);open_b=srv.open('B.lean',B)
 row('open_both',a=open_a,b=open_b,b_goal=srv.goal('B.lean',1),b_hover=srv.hover('B.lean',1),a_disk_sha256=sha(work/'A.lean'),a_olean_sha256=sha(work/'A.olean'))
 dirty_a=srv.change('A.lean',A_UNSAVED,2);assert sha(work/'A.lean')==textsha(A0)
 row('dirty_unsaved_a',a=dirty_a,a_disk_sha256=sha(work/'A.lean'),a_olean_sha256=sha(work/'A.olean'),b_goal=srv.goal('B.lean',1))
 (work/'BUnsaved.lean').write_text(B_UNSAVED)
 b_unsaved=srv.open('BUnsaved.lean',B_UNSAVED)
 row('b_imports_unsaved_only',b=b_unsaved,b_batch=batch(work,'BUnsaved.lean'),a_disk_sha256=sha(work/'A.lean'),a_olean_sha256=sha(work/'A.olean'))
 (work/'A.lean').write_text(A1)
 row('saved_a_without_rebuild',a_disk_sha256=sha(work/'A.lean'),a_olean_sha256=sha(work/'A.olean'),b_batch=batch(work,'B.lean'),b_goal=srv.goal('B.lean',1))
 rebuild=batch(work,'A.lean',build=True);assert rebuild['exit']==0
 o1=sha(work/'A.olean');assert o1!=o0
 (artifacts/'A1.lean').write_text(A1);shutil.copyfile(work/'A.olean',artifacts/'A1.olean')
 row('rebuilt_a',a_disk_sha256=sha(work/'A.lean'),a_olean_sha256=o1,rebuild=rebuild,b_batch=batch(work,'B.lean'),old_b_goal=srv.goal('B.lean',1),old_b_hover=srv.hover('B.lean',1))
 (work/'BNew.lean').write_text(B)
 new_b=srv.open('BNew.lean',B)
 row('new_b_same_server',b=new_b,b_goal=srv.goal('BNew.lean',1),b_hover=srv.hover('BNew.lean',1),a_olean_sha256=sha(work/'A.olean'))
 srv.close('B.lean');reopened=srv.open('B.lean',B,2)
 row('reopened_b_same_server',b=reopened,b_goal=srv.goal('B.lean',2),a_olean_sha256=sha(work/'A.olean'))
 end=srv.stop()
 fresh=Server(work,work);fresh_b=fresh.open('B.lean',B,1)
 row('fresh_server',b=fresh_b,b_goal=fresh.goal('B.lean',1),a_olean_sha256=sha(work/'A.olean'))
 fresh_end=fresh.stop()
 missing=work/'missing-import-dir';missing.mkdir()
 row('wrong_import_context',b_batch=batch(work,'B.lean',path=missing),correct_a_olean_sha256=sha(work/'A.olean'))
 # A minimal cyclic import graph has no compiled artifacts and cannot serve as
 # a source-only substitute for an importable environment.
 cycle=work/'cycle';cycle.mkdir();(cycle/'CycleA.lean').write_text('import CycleB\ntheorem ca : True := by trivial\n')
 (cycle/'CycleB.lean').write_text('import CycleA\ntheorem cb : True := by trivial\n')
 ca=batch(cycle,'CycleA.lean',path=cycle,build=False);cb=batch(cycle,'CycleB.lean',path=cycle,build=False)
 row('unbuilt_import_cycle',a=ca,b=cb)
 cyclic=Server(cycle,cycle);cycle_a=cyclic.open('CycleA.lean',(cycle/'CycleA.lean').read_text());cycle_b=cyclic.open('CycleB.lean',(cycle/'CycleB.lean').read_text())
 row('live_unbuilt_import_cycle',a=cycle_a,b=cycle_b,server_exit=cyclic.stop())
 result={'lean_sha256':sha(LEAN),'lean_version':subprocess.check_output([str(LEAN),'--version'],text=True).strip(),
         'sources':{'A0':A0,'A1':A1,'A_unsaved':A_UNSAVED,'B':B,'B_unsaved':B_UNSAVED},
         'artifact_sha256':{p.name:sha(p) for p in artifacts.iterdir() if p.is_file()},
         'events':events,'first_server':srv.messages,'first_server_exit':end,'fresh_server':fresh.messages,'fresh_server_exit':fresh_end,'cycle_server':cyclic.messages}
 raw=json.dumps(result,indent=2,ensure_ascii=False).replace(str(work),'$WORK')
 (HERE/'transcript.json').write_text(raw+'\n')
 print(json.dumps([{'step':e['step'],'a_olean':e.get('a_olean_sha256','')[:12],
                    'b_diagnostics':len((e.get('b') or {}).get('diagnostics') or []),
                    'b_batch_exit':(e.get('b_batch') or {}).get('exit')} for e in events],indent=2))
if __name__=='__main__':main()
