#!/usr/bin/env python3
"""One Lean watchdog, gated slow document, two edit bursts, and one batch checker."""
import hashlib,json,os,re,select,shutil,signal,subprocess,time
from pathlib import Path

S=Path(__file__).resolve().parent;W=S/'work'
LEAN=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean')
T0=time.monotonic();EV=[];P=[];PEAK=0
def ms():return round((time.monotonic()-T0)*1000,2)
def ev(kind,**kw):EV.append(dict(ms=ms(),kind=kind,**kw))
def sha(x):return hashlib.sha256(x if isinstance(x,bytes) else Path(x).read_bytes()).hexdigest()
def fast(n):return f'import Lean\ntheorem demo : {n} = {n} := by\n  exact ?_\n'
SLOW='''import Lean
theorem slow : True := by
  run_tac do
    IO.FS.writeFile "slow.entered" "entered"
    while !(← (System.FilePath.mk "slow.release").pathExists) do
      IO.sleep 10
  exact ?_
'''
def tree_rss():
 global PEAK
 ps=subprocess.run(['ps','-axo','pid=,ppid=,rss='],capture_output=True,text=True)
 rows=[]
 for line in ps.stdout.splitlines():
  try:rows.append(tuple(map(int,line.split()[:3])))
  except ValueError:pass
 live={p.pid for p in P if p.poll() is None}
 for _ in range(8):live.update(pid for pid,parent,_ in rows if parent in live)
 total=sum(rss for pid,_,rss in rows if pid in live)
 PEAK=max(PEAK,total)
 if total>4600000:raise RuntimeError('sampled summed RSS over 4,600,000 KiB guard')
 return total
class Server:
 def __init__(self):
  self.buf=b'';self.next=10
  self.p=subprocess.Popen([str(LEAN),'--server'],cwd=W,env=dict(os.environ,LEAN_NUM_THREADS='1'),
   stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0,start_new_session=True)
  P.append(self.p);ev('server_start',pid=self.p.pid)
  self.send(dict(jsonrpc='2.0',id=1,method='initialize',params=dict(processId=os.getpid(),rootUri=W.as_uri(),capabilities={},initializationOptions={'hasWidgets':False})))
  self.until({1},20);self.send(dict(jsonrpc='2.0',method='initialized',params={}))
 def send(self,m):
  raw=json.dumps(m,separators=(',',':')).encode();self.p.stdin.write(b'Content-Length: '+str(len(raw)).encode()+b'\r\n\r\n'+raw);self.p.stdin.flush()
  ev('client',message=m)
 def read(self,timeout=25):
  end=time.monotonic()+timeout
  while time.monotonic()<end:
   tree_rss()
   if b'\r\n\r\n' in self.buf:
    h,b=self.buf.split(b'\r\n\r\n',1)
    n=[int(x.split(b':',1)[1]) for x in h.split(b'\r\n') if x.lower().startswith(b'content-length:')]
    if n and len(b)>=n[0]:
     raw,self.buf=b[:n[0]],b[n[0]:];m=json.loads(raw);ev('server',message=m)
     if 'method' in m and 'id' in m:self.send(dict(jsonrpc='2.0',id=m['id'],result=None))
     return m
   rd,_,_=select.select([self.p.stdout],[],[],min(.1,max(0,end-time.monotonic())))
   if rd:
    x=os.read(self.p.stdout.fileno(),65536)
    if not x:break
    self.buf+=x
  raise TimeoutError('server read')
 def until(self,ids,timeout=25):
  pending=set(ids);out={};end=time.monotonic()+timeout
  while pending and time.monotonic()<end:
   m=self.read(max(.1,end-time.monotonic()))
   if m.get('id') in pending and 'method' not in m:
    out[m['id']]=m;pending.remove(m['id'])
  if pending:raise TimeoutError('pending '+str(pending))
  return out
 def open(self,name,text):
  u=(W/name).as_uri();self.send(dict(jsonrpc='2.0',method='textDocument/didOpen',params={'textDocument':dict(uri=u,languageId='lean',version=1,text=text)}))
 def change(self,name,version,text):
  u=(W/name).as_uri();self.send(dict(jsonrpc='2.0',method='textDocument/didChange',params={'textDocument':dict(uri=u,version=version),'contentChanges':[{'text':text}]}))
 def wait(self,name,version):
  rid=self.next;self.next+=1;self.send(dict(jsonrpc='2.0',id=rid,method='textDocument/waitForDiagnostics',params=dict(uri=(W/name).as_uri(),version=version)));return rid
 def goal(self,name):
  rid=self.next;self.next+=1;self.send(dict(jsonrpc='2.0',id=rid,method='$/lean/plainGoal',params=dict(textDocument=dict(uri=(W/name).as_uri()),position=dict(line=2,character=8))));return rid
 def stop(self):
  if self.p.poll() is None:
   try:
    self.send(dict(jsonrpc='2.0',id=99,method='shutdown',params=None));self.until({99},6)
    self.send(dict(jsonrpc='2.0',method='exit'));self.p.wait(timeout=6)
   except Exception:os.killpg(self.p.pid,signal.SIGKILL);self.p.wait()
  ev('server_stop',exit=self.p.returncode,stderr=self.p.stderr.read().decode(errors='replace'))
def main():
 assert LEAN.is_file()
 assert shutil.disk_usage(S).free>2*1024**3
 mp=subprocess.run(['memory_pressure','-Q'],capture_output=True,text=True,timeout=5)
 m=re.search(r'System-wide memory free percentage: (\d+)%',mp.stdout)
 if m and int(m.group(1))<35:raise RuntimeError('less than 35 percent free memory')
 if W.exists():shutil.rmtree(W)
 W.mkdir()
 batch_src='import Lean\nrun_cmd do\n  IO.FS.writeFile "batch.entered" "entered"\n  IO.sleep 500\ntheorem batch_ok : True := by trivial\n'
 for name,src in [('Slow.lean',SLOW),('FastA.lean',fast(1)),('Batch.lean',batch_src)]:
  (W/name).write_text(src)
 ev('subject',lean_sha256=sha(LEAN),source_sha256={p.name:sha(p) for p in W.glob('*.lean')},free_memory_percent=int(m.group(1)) if m else None)
 s=None;batch=None
 try:
  s=Server();s.open('Slow.lean',SLOW);slow_wait=s.wait('Slow.lean',1)
  deadline=time.monotonic()+12
  while not (W/'slow.entered').exists() and time.monotonic()<deadline:tree_rss();time.sleep(.02)
  assert (W/'slow.entered').exists(),'slow gate missing'
  ev('slow_gate_entered')
  s.open('FastA.lean',fast(1))
  initial=[s.wait('FastA.lean',1)]
  out=s.until(initial,20);assert all('error' not in x for x in out.values()),out
  ev('fast_initial_ready')
  batch=subprocess.Popen([str(LEAN),'--json','Batch.lean'],cwd=W,env=dict(os.environ,LEAN_NUM_THREADS='1'),
   stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,start_new_session=True);P.append(batch)
  ev('batch_start',pid=batch.pid)
  deadline=time.monotonic()+12
  while not (W/'batch.entered').exists() and time.monotonic()<deadline:tree_rss();time.sleep(.02)
  assert (W/'batch.entered').exists(),'batch gate missing'
  ev('batch_gate_entered')
  # FastA deliberately skips 3, duplicates 4 with different bytes, then sends late 3.
  for version,n in [(2,2),(4,4),(4,40),(3,3),(5,5)]:s.change('FastA.lean',version,fast(n))
  final_sent=ms();ev('burst_complete',fastA_final_version=5)
  wa=s.wait('FastA.lean',5)
  waits=s.until([wa],30);ev('fast_final_waits',responses=waits,elapsed_since_burst_ms=round(ms()-final_sent,2))
  ga=s.goal('FastA.lean')
  goals=s.until([ga],20);ev('fast_final_goals',responses=goals,elapsed_since_burst_ms=round(ms()-final_sent,2))
  bout,berr=batch.communicate(timeout=25);ev('batch_end',exit=batch.returncode,stdout=bout,stderr=berr)
  (W/'slow.release').write_text('release');ev('slow_gate_released')
  slow=s.until({slow_wait},15);ev('slow_wait_end',response=slow[slow_wait])
  assert batch.returncode==0 and all('error' not in x for x in waits.values())
  assert '5 = 5' in str(goals[ga]),goals
 finally:
  if batch is not None and batch.poll() is None:os.killpg(batch.pid,signal.SIGKILL);batch.wait()
  if s is not None:s.stop()
  ev('peak_sampled_rss_kib',value=PEAK)
  (S/'transcript.json').write_text(json.dumps(EV,indent=2)+'\n')
 waits=next(x for x in EV if x['kind']=='fast_final_waits')
 print(json.dumps({'fast_wait_tail_ms':waits['elapsed_since_burst_ms'],'peak_sampled_rss_kib':PEAK}))
if __name__=='__main__':main()
