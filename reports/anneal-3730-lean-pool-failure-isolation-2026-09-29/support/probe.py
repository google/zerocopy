#!/usr/bin/env python3
"""Guarded four/eight direct Lean server pool with injected fault and crash."""
import argparse,hashlib,json,os,re,select,shutil,signal,subprocess,threading,time
from pathlib import Path

HERE=Path(__file__).resolve().parent;LEAN=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean')
OUT=HERE/'transcript.json';RSS_CAP=2400*1024*1024;DISK_CAP=25*1024*1024;FREE_FLOOR=30;DURATION_CAP=90
START=time.monotonic();WORK=None;SERVERS=[];ABORT=[];MONITOR_STOP=threading.Event();EVENTS=[]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def source(i):return f'theorem peer_{i} : True := by\n  trivial\n'
def malformed(i):return f'theorem peer_{i} : True := by\n  exact 0\n'
def free_pct():
 p=subprocess.run(['memory_pressure','-Q'],capture_output=True,text=True,timeout=5)
 m=re.search(r'System-wide memory free percentage: (\d+)%',p.stdout)
 return int(m.group(1)) if m else None
def prows():
 p=subprocess.run(['ps','-axo','pid=,ppid=,pgid=,rss=,comm='],capture_output=True,text=True,timeout=5)
 rows=[]
 for line in p.stdout.splitlines():
  v=line.strip().split(maxsplit=4)
  if len(v)<5:continue
  try:pid,ppid,pgid,rss=map(int,v[:4])
  except ValueError:continue
  rows.append({'pid':pid,'ppid':ppid,'pgid':pgid,'rss_bytes':rss*1024,'comm':v[4]})
 return rows
def resources():
 gids={s.p.pid for s in SERVERS if s.p.poll() is None};rows=[r for r in prows() if r['pgid'] in gids]
 files=[p for p in WORK.rglob('*') if p.is_file()] if WORK else []
 return {'free_percent':free_pct(),'rss_bytes':sum(r['rss_bytes'] for r in rows),'process_count':len(rows),
         'processes':rows,'disk_blocks_bytes':sum(p.stat().st_blocks*512 for p in files),
         'elapsed_seconds':round(time.monotonic()-START,3)}
def check(label):
 r=resources();bad=[]
 if r['free_percent'] is None or r['free_percent']<FREE_FLOOR:bad.append('free-memory')
 if r['rss_bytes']>RSS_CAP:bad.append('rss')
 if r['disk_blocks_bytes']>DISK_CAP:bad.append('disk')
 if r['elapsed_seconds']>DURATION_CAP:bad.append('duration')
 EVENTS.append({'kind':'resource','label':label,'value':r,'violations':bad})
 if bad:ABORT.extend(bad);raise RuntimeError('resource cap: '+','.join(bad))
 return r
def monitor():
 while not MONITOR_STOP.wait(.4):
  try:
   r=resources();bad=[]
   if r['free_percent'] is None or r['free_percent']<FREE_FLOOR:bad.append('free-memory')
   if r['rss_bytes']>RSS_CAP:bad.append('rss')
   if r['disk_blocks_bytes']>DISK_CAP:bad.append('disk')
   if r['elapsed_seconds']>DURATION_CAP:bad.append('duration')
   if bad:
    ABORT.extend(bad);EVENTS.append({'kind':'watchdog_abort','value':r,'violations':bad})
    for s in SERVERS:
     if s.p.poll() is None:
      try:os.killpg(s.p.pid,signal.SIGKILL)
      except ProcessLookupError:pass
    return
  except Exception as exc:
   ABORT.append(repr(exc));return
def log(side,label,message):EVENTS.append({'kind':'rpc','side':side,'label':label,'message':message})
class Server:
 def __init__(self,root,label):
  self.root=root;self.label=label;self.file=root/'Proof.lean';self.uri=self.file.as_uri();self.buf=b'';self.n=0;self.diag={}
  self.file.write_text(source(label))
  self.p=subprocess.Popen([str(LEAN),'--server'],cwd=root,env=dict(os.environ,LEAN_NUM_THREADS='1',LEAN_PATH=str(root)),
   stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0,start_new_session=True)
  SERVERS.append(self)
  self.req('initialize',{'processId':os.getpid(),'rootUri':root.as_uri(),'capabilities':{},'initializationOptions':{'hasWidgets':False}})
  self.send({'jsonrpc':'2.0','method':'initialized','params':{}})
 def send(self,m):
  raw=json.dumps(m,separators=(',',':')).encode();self.p.stdin.write(b'Content-Length: '+str(len(raw)).encode()+b'\r\n\r\n'+raw);self.p.stdin.flush();log('client',self.label,m)
 def receive(self,pred,timeout=10):
  end=time.monotonic()+timeout
  while time.monotonic()<end:
   if ABORT:raise RuntimeError('watchdog aborted: '+repr(ABORT))
   while b'\r\n\r\n' in self.buf:
    head,body=self.buf.split(b'\r\n\r\n',1)
    lengths=[int(q.split(b':',1)[1]) for q in head.split(b'\r\n') if q.lower().startswith(b'content-length:')]
    if not lengths or len(body)<lengths[0]:break
    raw,self.buf=body[:lengths[0]],body[lengths[0]:];m=json.loads(raw);log('server',self.label,m)
    if m.get('method')=='textDocument/publishDiagnostics':self.diag[m['params']['version']]=m['params']['diagnostics']
    if m.get('method') in ('client/registerCapability','workspace/inlayHint/refresh') and 'id' in m:self.send({'jsonrpc':'2.0','id':m['id'],'result':None})
    if pred(m):return m
   ready,_,_=select.select([self.p.stdout],[],[],min(.2,max(0,end-time.monotonic())))
   if ready:
    raw=os.read(self.p.stdout.fileno(),65536)
    if not raw:break
    self.buf+=raw
  raise TimeoutError(self.label)
 def req(self,method,params):
  self.n+=1;id_=self.n;self.send({'jsonrpc':'2.0','id':id_,'method':method,'params':params})
  return self.receive(lambda m:m.get('id')==id_ and 'method' not in m)
 def open(self):
  self.send({'jsonrpc':'2.0','method':'textDocument/didOpen','params':{'textDocument':{'uri':self.uri,'languageId':'lean','version':1,'text':source(self.label)}}})
  barrier=self.req('textDocument/waitForDiagnostics',{'uri':self.uri,'version':1})
  if 1 not in self.diag:self.receive(lambda m:m.get('method')=='textDocument/publishDiagnostics' and m['params'].get('version')==1)
  return barrier
 def change(self,text,version):
  self.send({'jsonrpc':'2.0','method':'textDocument/didChange','params':{'textDocument':{'uri':self.uri,'version':version},'contentChanges':[{'text':text}]}})
  barrier=self.req('textDocument/waitForDiagnostics',{'uri':self.uri,'version':version})
  if version not in self.diag:self.receive(lambda m:m.get('method')=='textDocument/publishDiagnostics' and m['params'].get('version')==version)
  return barrier
 def goal(self,version):return self.req('$/lean/plainGoal',{'textDocument':{'uri':self.uri,'version':version},'position':{'line':1,'character':2}})
 def stop(self):
  if self.p.poll() is None:
   try:self.req('shutdown',None);self.send({'jsonrpc':'2.0','method':'exit'});self.p.wait(timeout=3)
   except Exception:
    if self.p.poll() is None:os.killpg(self.p.pid,signal.SIGKILL);self.p.wait(timeout=3)
  return {'pid':self.p.pid,'exit':self.p.returncode,'stderr':self.p.stderr.read().decode(errors='replace')}

def fence(candidate,current):
 return candidate['worker_epoch']==current['worker_epoch'] and candidate['document_version']==current['document_version'] and candidate['source_sha256']==current['source_sha256']
def run_cell(work,n):
 roots=[work/f'pool{n}-w{i}' for i in range(n)]
 for r in roots:r.mkdir()
 cell={'workers':n,'started':[],'peer_checks':[]}
 pool=[]
 try:
  for i,r in enumerate(roots):
   s=Server(r,i);pool.append(s);barrier=s.open();goal=s.goal(1)
   assert s.diag.get(1)==[] and '⊢ True' in json.dumps(goal,ensure_ascii=False)
   cell['started'].append({'index':i,'pid':s.p.pid,'barrier':barrier,'goal':goal,'diagnostics':s.diag[1],
                           'source_sha256':sha(s.file),'resources':check(f'pool{n}-start-{i}')})
  bad=pool[0];barrier=bad.change(malformed(0),2);bad_d=bad.diag.get(2)
  assert bad_d and any(d.get('severity')==1 for d in bad_d)
  cell['malformed']={'index':0,'barrier':barrier,'diagnostics':bad_d,'disk_sha256':sha(bad.file),
                      'buffer_sha256':hashlib.sha256(malformed(0).encode()).hexdigest()}
  for i,s in enumerate(pool[1:],1):
   b=s.req('textDocument/waitForDiagnostics',{'uri':s.uri,'version':1});g=s.goal(1)
   assert s.diag.get(1)==[] and '⊢ True' in json.dumps(g,ensure_ascii=False),(n,i,s.diag,g)
   cell['peer_checks'].append({'index':i,'barrier':b,'goal':g,'diagnostics':s.diag[1]})
  check(f'pool{n}-after-malformed')
  victim=pool[1];before=resources();victim.send({'jsonrpc':'2.0','method':'textDocument/didChange',
   'params':{'textDocument':{'uri':victim.uri,'version':2},'contentChanges':[{'text':source(1)+'-- request before crash\n'}]}})
  victim.n+=1;pending_id=victim.n
  victim.send({'jsonrpc':'2.0','id':pending_id,'method':'textDocument/waitForDiagnostics','params':{'uri':victim.uri,'version':2}})
  victim.send({'jsonrpc':'2.0','method':'$/cancelRequest','params':{'id':pending_id}})
  os.killpg(victim.p.pid,signal.SIGKILL);victim.p.wait(timeout=4)
  time.sleep(.2);after_rows=[r for r in prows() if r['pgid']==victim.p.pid]
  assert victim.p.returncode==-9 and not after_rows
  cell['crash']={'index':1,'pid':victim.p.pid,'pending_request_id':pending_id,'cancel_sent':True,
                 'exit':victim.p.returncode,'process_group_after':after_rows,'resources_before':before}
  old={'worker_epoch':1,'document_version':2,'source_sha256':hashlib.sha256((source(1)+'-- request before crash\n').encode()).hexdigest()}
  current={'worker_epoch':2,'document_version':1,'source_sha256':sha(victim.file)}
  assert not fence(old,current) and fence(current,current)
  cell['model_fence']={'old_candidate':old,'restart_current':current,'old_accepted':fence(old,current),
                       'fresh_accepted':fence(current,current)}
  restarted=Server(roots[1],1);b=restarted.open();g=restarted.goal(1)
  assert restarted.diag.get(1)==[] and '⊢ True' in json.dumps(g,ensure_ascii=False)
  cell['restart']={'old_pid':victim.p.pid,'new_pid':restarted.p.pid,'barrier':b,'goal':g,
                   'diagnostics':restarted.diag[1],'resources':check(f'pool{n}-restart')}
  for i,s in enumerate(pool):
   if i==1:continue
   g=s.goal(2 if i==0 else 1)
   cell['peer_checks'].append({'index':i,'after_crash':True,'goal':g,'diagnostics':s.diag.get(2 if i==0 else 1)})
  cell['final_resources']=check(f'pool{n}-final')
  return cell
 finally:
  for s in SERVERS:
   if s.p.poll() is None:s.stop()
  time.sleep(.1)
  cell['post_cleanup']={'process_rows':[r for r in prows() if r['pgid'] in {s.p.pid for s in SERVERS}],
                        'resources':resources()}
  assert not cell['post_cleanup']['process_rows']

def main():
 global WORK
 ap=argparse.ArgumentParser();ap.add_argument('--work',type=Path,required=True);ap.add_argument('--max-workers',type=int,choices=(4,8),default=8);args=ap.parse_args();WORK=args.work.resolve()
 assert not WORK.exists() and shutil.disk_usage(WORK.parent).free>=15*(1<<30)
 pre={'free_percent':free_pct(),'physical_bytes':int(subprocess.check_output(['sysctl','-n','hw.memsize'],text=True).strip()),
      'free_disk_bytes':shutil.disk_usage(WORK.parent).free}
 assert pre['free_percent'] is not None and pre['free_percent']>=40,'preflight memory floor'
 WORK.mkdir();thread=threading.Thread(target=monitor,daemon=True);thread.start();cells=[]
 try:
  cells.append(run_cell(WORK,4))
  admission={'free_percent':free_pct(),'prior_peak_rss_bytes':max(e['value']['rss_bytes'] for e in EVENTS if e['kind']=='resource')}
  if args.max_workers==8 and not ABORT and admission['free_percent']>=45 and admission['prior_peak_rss_bytes']<1500*1024*1024:
   cells.append(run_cell(WORK,8));admission['eight_admitted']=True
  else:admission['eight_admitted']=False
 finally:
  MONITOR_STOP.set();thread.join(timeout=2)
  for s in SERVERS:
   if s.p.poll() is None:s.stop()
 result={'lean_sha256':sha(LEAN),'preflight':pre,'admission':admission if 'admission' in locals() else None,
         'limits':{'rss_bytes':RSS_CAP,'disk_blocks_bytes':DISK_CAP,'free_percent_floor':FREE_FLOOR,'duration_seconds':DURATION_CAP},
         'abort':ABORT,'cells':cells,'events':EVENTS,'final_live_groups':[r for r in prows() if r['pgid'] in {s.p.pid for s in SERVERS}]}
 OUT.write_text(json.dumps(result,indent=2,ensure_ascii=False).replace(str(WORK),'$WORK')+'\n')
 assert not ABORT and not result['final_live_groups']
 print(json.dumps({'preflight':pre,'admission':admission,'cells':[
  {'workers':c['workers'],'malformed_diagnostics':len(c['malformed']['diagnostics']),
   'peer_checks':len(c['peer_checks']),'crash_exit':c['crash']['exit'],'restart_pid':c['restart']['new_pid'],
   'post_cleanup':len(c['post_cleanup']['process_rows'])} for c in cells]},indent=2))
if __name__=='__main__':main()
