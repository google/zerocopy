#!/usr/bin/env python3
"""Two bounded offline Lake fresh consumers of one seeded read-only artifact cache."""
import argparse, concurrent.futures, hashlib, json, os, re, select, shutil, signal, subprocess, threading, time
from pathlib import Path
BIN=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin')
LAKE=BIN/'lake';LEAN=BIN/'lean';TOOLCHAIN='leanprover/lean4:v4.30.0-rc2'
SOURCE='import Dep\ntheorem generatedEq : depValue + 1 = 8 := by\n  trace_state\n  decide\n#print axioms generatedEq\n#eval depValue + 1\n'
PROFILE='(version 1) (allow default) (deny network*)'
LIMITS={'disk_bytes':15*1024**3,'start_free_percent':23,'runtime_free_percent':12,'rss_kib':4500000,'cell_seconds':75,'call_seconds':30}

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def inv(root):return {str(p.relative_to(root)):{'sha256':sha(p),'size':p.stat().st_size,'mtime_ns':p.stat().st_mtime_ns} for p in sorted(root.rglob('*')) if p.is_file()}
def free_percent():
 s=subprocess.check_output(['vm_stat'],text=True);page=int(re.search(r'page size of (\d+) bytes',s).group(1))
 n=sum(int(re.search(rf'^{k}:\s+(\d+)',s,re.M).group(1)) for k in ('Pages free','Pages inactive','Pages speculative','Pages purgeable'))
 return round(100*n*page/int(subprocess.check_output(['sysctl','-n','hw.memsize'],text=True)),2)
def fixture(root):
 dep,consumer=root/'producer',root/'consumer';dep.mkdir(parents=True);consumer.mkdir()
 (dep/'lakefile.lean').write_text('import Lake\nopen Lake DSL\npackage probe_dep\n@[default_target]\nlean_lib Dep\n')
 (dep/'Dep.lean').write_text('def depValue : Nat := 7\n');(dep/'lean-toolchain').write_text(TOOLCHAIN+'\n')
 (consumer/'lakefile.lean').write_text('import Lake\nopen Lake DSL\nrequire probe_dep from "../producer"\npackage probe_consumer\n@[default_target]\nlean_lib Generated\n')
 (consumer/'Generated.lean').write_text(SOURCE);(consumer/'lean-toolchain').write_text(TOOLCHAIN+'\n')
 m={'version':'1.2.0','packagesDir':'.lake/packages','packages':[{'type':'path','scope':'','name':'probe_dep','manifestFile':'lake-manifest.json','inherited':False,'dir':'../producer','configFile':'lakefile.lean'}],'name':'probe_consumer','lakeDir':'.lake','fixedToolchain':False}
 (consumer/'lake-manifest.json').write_text(json.dumps(m,indent=2)+'\n')
 return dep,consumer
def environment(work,cache,label,write):
 e=dict(os.environ);home=work/('home-'+label);home.mkdir();xdg=work/('xdg-'+label);xdg.mkdir()
 e.update(HOME=str(home),XDG_CACHE_HOME=str(xdg),ELAN_TOOLCHAIN=TOOLCHAIN,LEAN_NUM_THREADS='1',LAKE_NO_NET='1',LAKE_CACHE_DIR=str(cache),PATH=str(BIN)+os.pathsep+e.get('PATH',''))
 e.pop('LAKE_ARTIFACT_CACHE',None)
 if write:e['LAKE_ARTIFACT_CACHE']='true'
 return e
class Guard:
 def __init__(self):
  self.lock=threading.Lock();self.pids=set();self.stop=threading.Event();self.abort=None;self.samples=0;self.peak=0;self.min_free=100;self.max_processes=0
 def add(self,p):
  with self.lock:self.pids.add(p.pid)
 def remove(self,p):
  with self.lock:self.pids.discard(p.pid)
 def kill(self):
  with self.lock:pids=list(self.pids)
  for pid in pids:
   try:os.killpg(pid,signal.SIGKILL)
   except ProcessLookupError:pass
 def monitor(self):
  start=time.monotonic()
  while not self.stop.is_set():
   try:
    with self.lock:roots=set(self.pids)
    out=subprocess.check_output(['ps','-axo','pid=,ppid=,rss='],text=True,timeout=3)
    rows=[tuple(map(int,line.split())) for line in out.splitlines() if len(line.split())==3]
    children={}
    for pid,ppid,rss in rows:children.setdefault(ppid,[]).append(pid)
    descendants=set(roots);todo=list(roots)
    while todo:
     for p in children.get(todo.pop(),[]):
      if p not in descendants:descendants.add(p);todo.append(p)
    rss=sum(r for pid,_,r in rows if pid in descendants);free=free_percent()
    self.samples+=1;self.peak=max(self.peak,rss);self.min_free=min(self.min_free,free);self.max_processes=max(self.max_processes,len(descendants))
    reason=('cell timeout' if time.monotonic()-start>LIMITS['cell_seconds'] else
            'sampled RSS cap' if rss>LIMITS['rss_kib'] else
            'system free-memory floor' if free<LIMITS['runtime_free_percent'] else None)
    if reason:self.abort=reason;self.kill();return
   except Exception as x:self.abort='monitor error: '+repr(x);self.kill();return
   self.stop.wait(.08)
def norm(obj,work):
 return json.loads(json.dumps(obj,ensure_ascii=False).replace(work.as_uri(),'$WORK_URI').replace(str(work),'$WORK').replace(str(BIN.parent),'$TOOLCHAIN'))
def launch(guard,cmd,cwd,e):
 p=subprocess.Popen(cmd,cwd=cwd,env=e,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0,start_new_session=True)
 guard.add(p);return p
def call(guard,label,cwd,args,e,profile,work):
 cmd=['/usr/bin/sandbox-exec','-p',profile,str(LAKE),'--keep-toolchain',*args];start=time.monotonic()
 p=launch(guard,cmd,cwd,e)
 try:out,err=p.communicate(timeout=LIMITS['call_seconds'])
 except subprocess.TimeoutExpired:
  os.killpg(p.pid,signal.SIGKILL);out,err=p.communicate();guard.abort=guard.abort or label+' timeout'
 finally:guard.remove(p)
 return {'label':label,'args':args,'start':start,'end':time.monotonic(),'exit':p.returncode,'stdout':out.decode(errors='replace'),'stderr':err.decode(errors='replace')}
class Server:
 def __init__(self,guard,cwd,e,profile):
  self.guard=guard;self.p=launch(guard,['/usr/bin/sandbox-exec','-p',profile,str(LAKE),'--keep-toolchain','--no-cache','serve'],cwd,e)
  self.buf=b'';self.id=0;self.messages=[];self.request('initialize',{'processId':os.getpid(),'rootUri':cwd.as_uri(),'capabilities':{},'initializationOptions':{'hasWidgets':False}},20)
  self.send({'jsonrpc':'2.0','method':'initialized','params':{}})
 def send(self,m):
  raw=json.dumps(m,separators=(',',':')).encode();self.p.stdin.write(b'Content-Length: '+str(len(raw)).encode()+b'\r\n\r\n'+raw);self.p.stdin.flush();self.messages.append({'direction':'client','message':m})
 def receive(self,rid,timeout):
  end=time.monotonic()+timeout
  while time.monotonic()<end:
   if self.guard.abort:raise RuntimeError(self.guard.abort)
   while b'\r\n\r\n' in self.buf:
    h,b=self.buf.split(b'\r\n\r\n',1);n=int(re.search(rb'Content-Length:\s*(\d+)',h,re.I).group(1))
    if len(b)<n:break
    m=json.loads(b[:n]);self.buf=b[n:];self.messages.append({'direction':'server','message':m})
    if 'method' in m and 'id' in m:self.send({'jsonrpc':'2.0','id':m['id'],'result':None})
    if 'method' not in m and m.get('id')==rid:return m
   ready,_,_=select.select([self.p.stdout],[],[],min(.1,max(0,end-time.monotonic())))
   if ready:
    part=os.read(self.p.stdout.fileno(),65536)
    if not part:raise RuntimeError('server closed')
    self.buf+=part
  raise TimeoutError('server response')
 def request(self,method,params,timeout=30):
  self.id+=1;rid=self.id;self.send({'jsonrpc':'2.0','id':rid,'method':method,'params':params});return self.receive(rid,timeout)
 def stop(self):
  try:
   if self.p.poll() is None:
    self.request('shutdown',None,5);self.send({'jsonrpc':'2.0','method':'exit'});self.p.wait(timeout=5)
  except Exception:
   if self.p.poll() is None:os.killpg(self.p.pid,signal.SIGKILL);self.p.wait(timeout=5)
  self.guard.remove(self.p);return {'exit':self.p.returncode,'stderr':self.p.stderr.read().decode(errors='replace')}
def goal(guard,label,cwd,e,profile,barrier):
 barrier.wait(timeout=10);start=time.monotonic();s=None
 try:
  s=Server(guard,cwd,e,profile);uri=(cwd/'Generated.lean').as_uri()
  s.send({'jsonrpc':'2.0','method':'textDocument/didOpen','params':{'textDocument':{'uri':uri,'languageId':'lean','version':1,'text':SOURCE}}})
  wait=s.request('textDocument/waitForDiagnostics',{'uri':uri,'version':1})
  answer=s.request('$/lean/plainGoal',{'textDocument':{'uri':uri,'version':1},'position':{'line':2,'character':3}})
  error=None
 except Exception as x:wait=None;answer=None;error=repr(x)
 finally:stop=s.stop() if s else None
 notices=[m['message'] for m in s.messages if m['direction']=='server' and m['message'].get('method')=='textDocument/publishDiagnostics'] if s else []
 return {'label':label,'start':start,'end':time.monotonic(),'error':error,'wait':wait,'goal':answer,'stop':stop,'diagnostics':notices}
def worker(label,root,e,profile,guard,build_barrier,goal_barrier,work):
 dep,cwd=root/'producer',root/'consumer'
 build_barrier.wait(timeout=10)
 build=call(guard,label+'-no-build',cwd,['-v','--no-build','build','Generated'],e,profile,work)
 batch=call(guard,label+'-batch',cwd,['--no-cache','env','lean','--json','Generated.lean'],e,profile,work)
 first=goal(guard,label+'-first-goal',cwd,e,profile,goal_barrier)
 return {'build':build,'batch':batch,'goal':first,'producer_after':inv(dep),'consumer_after':inv(cwd)}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--work',type=Path,required=True);ap.add_argument('--output',type=Path,required=True)
 a=ap.parse_args();work=a.work.resolve()
 if work.exists():raise SystemExit('work must be absent')
 disk=shutil.disk_usage(work.parent).free;mem=free_percent()
 if disk<LIMITS['disk_bytes'] or mem<LIMITS['start_free_percent']:raise SystemExit(f'preflight denied: disk={disk}, free_memory={mem}')
 if not LAKE.is_file() or not LEAN.is_file():raise SystemExit('local pinned tools absent')
 work.mkdir();seed=work/'seed';seed_dep,seed_consumer=fixture(seed);cache=work/'cache'
 seed_env=environment(work,cache,'seed',True);seed_guard=Guard()
 seed_build=call(seed_guard,'seed-build',seed_consumer,['-v','build','Generated'],seed_env,PROFILE,work)
 if seed_build['exit']!=0:raise SystemExit('seed build failed: '+seed_build['stderr'][-400:])
 seed_product={'Dep.olean':sha(seed_dep/'.lake/build/lib/lean/Dep.olean'),'Generated.olean':sha(seed_consumer/'.lake/build/lib/lean/Generated.olean')}
 for p in sorted(cache.rglob('*'),reverse=True):
  if p.is_file():p.chmod(0o444)
  elif p.is_dir():p.chmod(0o555)
 cache.chmod(0o555)
 cache_before=inv(cache);seed_before=inv(seed)
 roots={};envs={}
 for label in ('a','b'):
  root=work/label;fixture(root);roots[label]=root;envs[label]=environment(work,cache,label,False)
 private_before={label:inv(root) for label,root in roots.items()}
 profile=PROFILE+f' (deny file-write* (subpath "{cache}"))'
 guard=Guard();monitor=threading.Thread(target=guard.monitor,daemon=True);monitor.start()
 build_barrier=threading.Barrier(2);goal_barrier=threading.Barrier(2);results={}
 try:
  with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
   futs={label:pool.submit(worker,label,roots[label],envs[label],profile,guard,build_barrier,goal_barrier,work) for label in roots}
   for label,f in futs.items():results[label]=f.result(timeout=LIMITS['cell_seconds']+10)
 finally:
  guard.stop.set();monitor.join(timeout=5);guard.kill()
 result={'preflight':{'disk_free_bytes':disk,'memory_free_percent':mem},'limits':LIMITS,'tools':{'lake_sha256':sha(LAKE),'lean_sha256':sha(LEAN)},
         'seed_build':seed_build,'seed_product':seed_product,'seed_before':seed_before,'seed_after':inv(seed),
         'cache_before':cache_before,'cache_after':inv(cache),'private_before':private_before,
         'guard':{'abort':guard.abort,'samples':guard.samples,'peak_rss_kib':guard.peak,'min_free_percent':guard.min_free,'max_processes':guard.max_processes},
         'consumers':results,'source':SOURCE}
 a.output.write_text(json.dumps(norm(result,work),indent=2,ensure_ascii=False)+'\n')
 print(json.dumps({'preflight':result['preflight'],'guard':result['guard'],'cache_unchanged':cache_before==result['cache_after'],
                   'seed_unchanged':seed_before==result['seed_after'],
                   'exits':{x:{k:results[x][k]['exit'] if k!='goal' else (results[x][k]['stop'] or {}).get('exit') for k in ('build','batch','goal')} for x in results},
                   'actions':{x:[l for l in results[x]['build']['stdout'].splitlines() if 'Fetched ' in l or 'Replayed ' in l or 'Built ' in l] for x in results}},indent=2))
if __name__=='__main__':main()
