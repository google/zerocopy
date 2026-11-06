#!/usr/bin/env python3
import hashlib,json,os,pathlib,select,shutil,subprocess,time
ROOT=pathlib.Path(__file__).resolve().parent/'server-memory';ROOT.mkdir(parents=True,exist_ok=True)
LEAN=pathlib.Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean')
MON=pathlib.Path(__file__).resolve().parent/'proc-tree'
SOURCES={
 'v1':'import Dep\ntheorem demo (n : Nat) (h : n = 1) : n + sharedValue = 1 + sharedValue := by\n  exact ?_\n',
 'v2':'import Dep\ntheorem demo (n : Nat) (h : n = 1) : n + sharedValue = 1 + sharedValue := by\n  exact congrArg (fun x => x + sharedValue) h\n'}
EVENTS=[];START=time.monotonic();SERVERS=[];STOP=1_500_000_000

def record(kind,**d): EVENTS.append({'elapsed_ms':round((time.monotonic()-START)*1000), 'kind':kind,**d})
def sha(s): return hashlib.sha256(s.encode()).hexdigest()
def resources():
 p=subprocess.run(['memory_pressure','-Q'],capture_output=True,text=True,timeout=5)
 v=None
 for line in p.stdout.splitlines():
  if line.startswith('System-wide memory free percentage:'):v=int(line.rsplit(' ',1)[-1].rstrip('%'))
 free=shutil.disk_usage(ROOT).free
 return v,free

def sample(label):
 total=0;procs=[]
 for s in SERVERS:
  if s.p.poll() is None:
   r=subprocess.run([str(MON),str(s.p.pid)],capture_output=True,text=True,timeout=3)
   if r.returncode: raise RuntimeError(f'process monitor failed for {s.label}: {r.stderr}')
   rows=[x.split('\t') for x in r.stdout.splitlines() if '\t' in x and x.split('\t')[0]!='TOTAL']
   sumline=next(x for x in r.stdout.splitlines() if x.startswith('TOTAL\t'))
   rss=int(sumline.split('\t')[1]);total+=rss
   procs.append({'server':s.label,'pid':s.p.pid,'descendant_count':len(rows),'tree_rss_bytes':rss,'processes':[{'pid':int(x[0]),'name':x[1],'rss_bytes':int(x[2])} for x in rows]})
 free,dis=resources()
 record('memory_sample',label=label,active_servers=len(procs),aggregate_tree_rss_bytes=total,servers=procs,memory_free_percent=free,disk_free_bytes=dis)
 if total>STOP: raise RuntimeError(f'aggregate RSS exceeded 1.5GB: {total}')
 if free is not None and free<20: raise RuntimeError(f'system free memory below 20%: {free}%')
 if dis<5*(1<<30): raise RuntimeError(f'disk free below 5GiB: {dis}')

def send(p,msg):
 raw=json.dumps(msg,separators=(',',':')).encode();p.stdin.write(b'Content-Length: '+str(len(raw)).encode()+b'\r\n\r\n'+raw);p.stdin.flush()

def recv(p,buf,predicate,limit=15):
 deadline=time.monotonic()+limit
 while time.monotonic()<deadline:
  if b'\r\n\r\n' in buf:
   header,rest=buf.split(b'\r\n\r\n',1);lengths=[int(x.split(b':',1)[1]) for x in header.split(b'\r\n') if x.lower().startswith(b'content-length:')]
   if lengths and len(rest)>=lengths[0]:
    raw,buf=rest[:lengths[0]],rest[lengths[0]:];msg=json.loads(raw)
    if msg.get('method')=='client/registerCapability' and 'id' in msg:send(p,{'jsonrpc':'2.0','id':msg['id'],'result':None})
    if predicate(msg):return msg,buf
  ready,_,_=select.select([p.stdout],[],[],min(0.1,deadline-time.monotonic()))
  if ready:
   chunk=os.read(p.stdout.fileno(),65536)
   if not chunk:break
   buf+=chunk
 raise TimeoutError('LSP response deadline')

class Server:
 def __init__(self,label):
  self.label=label;self.root=ROOT/label;self.root.mkdir(exist_ok=True);self.file=self.root/'Proof.lean';self.file.write_text(SOURCES['v1']);self.buf=b'';self.seq=1
  self.p=subprocess.Popen([str(LEAN),'--server'],cwd=self.root,env=dict(os.environ,LEAN_NUM_THREADS='1',LEAN_PATH=str(ROOT/'shared')),stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0)
  SERVERS.append(self);record('start',server=label,pid=self.p.pid,cwd=str(self.root),source_sha256=sha(SOURCES['v1']))
  self.request('initialize',{'processId':os.getpid(),'rootUri':self.root.as_uri(),'capabilities':{},'initializationOptions':{'hasWidgets':False}})
  send(self.p,{'jsonrpc':'2.0','method':'initialized','params':{}})
  send(self.p,{'jsonrpc':'2.0','method':'textDocument/didOpen','params':{'textDocument':{'uri':self.file.as_uri(),'languageId':'lean','version':1,'text':SOURCES['v1']}}})
  self.request('textDocument/waitForDiagnostics',{'uri':self.file.as_uri(),'version':1})
  self.goal()
 def request(self,method,params):
  rid=self.seq;self.seq+=1;send(self.p,{'jsonrpc':'2.0','id':rid,'method':method,'params':params});m,self.buf=recv(self.p,self.buf,lambda x:x.get('id')==rid);return m
 def goal(self):return self.request('$/lean/plainGoal',{'textDocument':{'uri':self.file.as_uri()},'position':{'line':2,'character':2}})
 def edit(self):
  send(self.p,{'jsonrpc':'2.0','method':'textDocument/didChange','params':{'textDocument':{'uri':self.file.as_uri(),'version':2},'contentChanges':[{'text':SOURCES['v2']}]}})
  self.request('textDocument/waitForDiagnostics',{'uri':self.file.as_uri(),'version':2});return self.goal()
 def stop(self):
  if self.p.poll() is None:
   try:self.request('shutdown',None);send(self.p,{'jsonrpc':'2.0','method':'exit'});self.p.wait(timeout=3)
   except Exception:self.p.kill();self.p.wait(timeout=3)
  record('exit',server=self.label,status=self.p.returncode,stderr=self.p.stderr.read().decode(errors='replace'))

def main():
 shared=ROOT/'shared';shared.mkdir(exist_ok=True);dep=shared/'Dep.lean';dep.write_text('def sharedValue : Nat := 3\n');olean=shared/'Dep.olean'
 b=subprocess.run([str(LEAN),'-o',str(olean),str(dep)],cwd=shared,env=dict(os.environ,LEAN_NUM_THREADS='1'),capture_output=True,text=True,timeout=20)
 record('build_dep',exit=b.returncode,stdout=b.stdout,stderr=b.stderr,olean_bytes=olean.stat().st_size)
 if b.returncode:raise RuntimeError('Lean dependency failed')
 olean.chmod(0o444);record('dependency',sha256=hashlib.sha256(olean.read_bytes()).hexdigest(),mode=oct(olean.stat().st_mode&0o777))
 sample('baseline-no-servers')
 for n in range(1,5):
  s=Server(f'job{n}');sample(f'{n}-concurrent-server(s)-loaded')
 for i in range(10):
  for s in SERVERS:s.edit()
  if i in (0,4,9):sample(f'after-{i+1}-edit-rounds')
 for i in range(8):
  sample(f'idle-{i}');time.sleep(0.25)
 for s in SERVERS:s.stop()
 sample('after-stop')
 record('summary',samples=[e for e in EVENTS if e['kind']=='memory_sample'],disk_used_bytes=sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()))

try:main()
except Exception as e:record('abort',error=repr(e))
finally:
 for s in SERVERS:
  if s.p.poll() is None:s.p.kill();s.p.wait(timeout=3);record('forced_stop',server=s.label,status=s.p.returncode)
 (ROOT/'transcript.json').write_text(json.dumps(EVENTS,indent=2)+'\n')
 print(json.dumps({'events':len(EVENTS),'samples':[e for e in EVENTS if e['kind']=='memory_sample'],'abort':[e for e in EVENTS if e['kind']=='abort'],'disk_bytes':sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file())},indent=2))
