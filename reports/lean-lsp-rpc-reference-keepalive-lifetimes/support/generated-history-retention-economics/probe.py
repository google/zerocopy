#!/usr/bin/env python3
"""Four cached Aeneas generations: tier bytes, fresh/restarted Lean goals, one rebuild."""
import hashlib,json,os,re,select,shutil,signal,subprocess,time
from pathlib import Path

S=Path(__file__).resolve().parent;W=S/'work'
REPO=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/scratch/20260927-reference-experiments/reference-publish')
R09=REPO/'reports/anneal-3730-aeneas-restricted-reuse-2026-09-29/support'
MOVE=REPO/'reports/anneal-3730-aeneas-namespace-move-proof-context-2026-09-29/support/work/moved'
T=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools')
ROOT=T/'elan/toolchains/leanprover--lean4---v4.30.0-rc2';LEAN=ROOT/'bin/lean'
BACKEND=T/'aeneas-release/backends/lean'
PKGS=['Cli','batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient','plausible','mathlib']
RESULT={'schema':'anneal-generated-history-retention-v1','tools':{},'generations':{},'retention':{},'sessions':[],'recompute':{},'commands':[]}
LIVE=[];PEAK=0
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def env(root):
 libs=[BACKEND/'.lake/packages'/p/'.lake/build/lib/lean' for p in PKGS]
 libs += [BACKEND/'.lake/build/lib/lean',ROOT/'lib/lean']
 e=dict(os.environ,LEAN_NUM_THREADS='1');e['LEAN_PATH']=os.pathsep.join(map(str,[root,*(p for p in libs if p.is_dir())]));return e
def inv(root):
 return {str(p.relative_to(root)):dict(bytes=p.stat().st_size,allocated=p.stat().st_blocks*512,sha256=sha(p))
  for p in sorted(root.rglob('*')) if p.is_file()}
def call(label,args,cwd,envv=None,timeout=60):
 t=time.monotonic();p=subprocess.run([str(x) for x in args],cwd=cwd,env=envv or env(cwd),capture_output=True,text=True,timeout=timeout)
 row=dict(label=label,argv=[str(x) for x in args],cwd=str(cwd),exit=p.returncode,seconds=round(time.monotonic()-t,3),stdout=p.stdout,stderr=p.stderr)
 RESULT['commands'].append(row);return row
def rss():
 global PEAK
 ps=subprocess.run(['ps','-axo','pid=,ppid=,rss='],capture_output=True,text=True)
 rows=[]
 for l in ps.stdout.splitlines():
  try:rows.append(tuple(map(int,l.split()[:3])))
  except ValueError:pass
 live={p.pid for p in LIVE if p.poll() is None}
 for _ in range(8):live.update(pid for pid,parent,_ in rows if parent in live)
 total=sum(r for pid,_,r in rows if pid in live);PEAK=max(PEAK,total)
 if total>3300000:raise RuntimeError('summed RSS over 3,300,000 KiB guard')
 return total
class Server:
 def __init__(self,root):
  self.root=root;self.buf=b'';self.n=10
  self.p=subprocess.Popen([str(LEAN),'--server'],cwd=root,env=env(root),stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0,start_new_session=True)
  LIVE.append(self.p);self.send(dict(jsonrpc='2.0',id=1,method='initialize',params=dict(processId=os.getpid(),rootUri=root.as_uri(),capabilities={},initializationOptions={'hasWidgets':False})))
  self.until(1,20);self.send(dict(jsonrpc='2.0',method='initialized',params={}))
 def send(self,m):
  raw=json.dumps(m,separators=(',',':')).encode();self.p.stdin.write(b'Content-Length: '+str(len(raw)).encode()+b'\r\n\r\n'+raw);self.p.stdin.flush()
 def read(self,timeout=20):
  end=time.monotonic()+timeout
  while time.monotonic()<end:
   rss()
   if b'\r\n\r\n' in self.buf:
    h,b=self.buf.split(b'\r\n\r\n',1)
    n=[int(x.split(b':',1)[1]) for x in h.split(b'\r\n') if x.lower().startswith(b'content-length:')]
    if n and len(b)>=n[0]:
     raw,self.buf=b[:n[0]],b[n[0]:];m=json.loads(raw)
     if 'method' in m and 'id' in m:self.send(dict(jsonrpc='2.0',id=m['id'],result=None))
     return m
   rd,_,_=select.select([self.p.stdout],[],[],min(.1,max(0,end-time.monotonic())))
   if rd:
    x=os.read(self.p.stdout.fileno(),65536)
    if not x:break
    self.buf+=x
  raise TimeoutError('server read')
 def until(self,rid,timeout=20):
  end=time.monotonic()+timeout
  while time.monotonic()<end:
   m=self.read(max(.1,end-time.monotonic()))
   if m.get('id')==rid and 'method' not in m:return m
  raise TimeoutError('request '+str(rid))
 def req(self,method,params):
  rid=self.n;self.n+=1;self.send(dict(jsonrpc='2.0',id=rid,method=method,params=params));return self.until(rid)
 def stop(self):
  if self.p.poll() is None:
   try:
    self.send(dict(jsonrpc='2.0',id=99,method='shutdown',params=None));self.until(99,6)
    self.send(dict(jsonrpc='2.0',method='exit'));self.p.wait(timeout=6)
   except Exception:os.killpg(self.p.pid,signal.SIGKILL);self.p.wait()
  return self.p.returncode
def session(label,root):
 t=time.monotonic();s=Server(root);start=round(time.monotonic()-t,3)
 try:
  uri=(root/'Historical.lean').as_uri();source=(root/'Historical.lean').read_text()
  s.send(dict(jsonrpc='2.0',method='textDocument/didOpen',params={'textDocument':dict(uri=uri,languageId='lean',version=1,text=source)}))
  wait=s.req('textDocument/waitForDiagnostics',dict(uri=uri,version=1));ready=round(time.monotonic()-t,3)
  goal=s.req('$/lean/plainGoal',dict(textDocument=dict(uri=uri),position=dict(line=2,character=8)))
  done=round(time.monotonic()-t,3);mem=rss()
  row=dict(label=label,source_sha256=sha(root/'Historical.lean'),import_olean_sha256=sha(root/'Fixture/Funs.olean'),
   startup_seconds=start,ready_seconds=ready,goal_seconds=done,sampled_tree_rss_kib=mem,
   wait=wait,goal=goal)
 finally:
  row_exit=s.stop()
 row['server_exit']=row_exit;RESULT['sessions'].append(row)
 assert row_exit==0 and 'error' not in wait and 'error' not in goal,row
 return row
def main():
 assert LEAN.is_file() and (BACKEND/'.lake/build/lib/lean/Aeneas.olean').is_file()
 assert shutil.disk_usage(S).free>2*1024**3
 mp=subprocess.run(['memory_pressure','-Q'],capture_output=True,text=True,timeout=5)
 m=re.search(r'System-wide memory free percentage: (\d+)%',mp.stdout)
 if m and int(m.group(1))<35:raise RuntimeError('less than 35 percent free memory')
 if W.exists():shutil.rmtree(W)
 W.mkdir();RESULT['tools']={'lean_sha256':sha(LEAN),'aeneas_olean_sha256':sha(BACKEND/'.lake/build/lib/lean/Aeneas.olean'),
  'free_memory_percent':int(m.group(1)) if m else None}
 cases=[('g0-base',R09/'work/full-base',R09/'inputs/base',
   'trait_reuse.core.use_step 1#u32 = .ok 2#u32'),
  ('g1-body',R09/'work/full-body',R09/'inputs/body',
   'trait_reuse.core.use_step 1#u32 = .ok 3#u32'),
  ('g2-signature',R09/'work/full-signature',R09/'inputs/signature',
   'trait_reuse.core.use_step 1#u32 = .ok 2#u32'),
  ('g3-move',MOVE,MOVE,'move_probe.moved.core.use_step 1#u32 = .ok 2#u32')]
 for label,src,inputs,claim in cases:
  dest=W/label;dest.mkdir();(dest/'Fixture').mkdir();(dest/'provenance').mkdir()
  for p in [src/'Fixture.lean',src/'Fixture.olean',src/'Fixture/Funs.lean',src/'Fixture/Funs.olean',src/'Fixture/Types.lean',src/'Fixture/Types.olean',src/'Proof.lean']:
   shutil.copy2(p,dest/p.relative_to(src))
  (dest/'provenance/fixture.rs').write_bytes((inputs/'fixture.rs').read_bytes())
  (dest/'provenance/fixture.llbc').write_bytes((inputs/'fixture.llbc').read_bytes())
  (dest/'Historical.lean').write_text(f'import Fixture\ntheorem historical : {claim} := by\n  exact ?_\n')
  inventory=inv(dest)
  RESULT['generations'][label]=dict(claim=claim,files=inventory,
   rust_source_bytes=sum(v['bytes'] for k,v in inventory.items() if k.endswith('.rs')),
   llbc_bytes=sum(v['bytes'] for k,v in inventory.items() if k.endswith('.llbc')),
   source_bytes=sum(v['bytes'] for k,v in inventory.items() if k.startswith('provenance/')),
   generated_bytes=sum(v['bytes'] for k,v in inventory.items() if k.endswith('.lean')),
   compiled_bytes=sum(v['bytes'] for k,v in inventory.items() if k.endswith('.olean')))
  proof=call(label+':fresh-proof',[LEAN,'--json','Proof.lean'],dest)
  assert proof['exit']==0,proof
 for n in [1,2,4]:
  labels=[x[0] for x in cases[-n:]]
  RESULT['retention'][str(n)]={'generations':labels,
   'rust_only_bytes':sum(RESULT['generations'][x]['rust_source_bytes'] for x in labels),
   'source_bytes':sum(RESULT['generations'][x]['source_bytes'] for x in labels),
   'source_plus_generated_bytes':sum(RESULT['generations'][x]['source_bytes']+RESULT['generations'][x]['generated_bytes'] for x in labels),
   'source_generated_compiled_bytes':sum(RESULT['generations'][x]['source_bytes']+RESULT['generations'][x]['generated_bytes']+RESULT['generations'][x]['compiled_bytes'] for x in labels)}
 for label,*_ in cases:session(label,W/label)
 session('restart-g0-base',W/'g0-base');session('restart-g3-move',W/'g3-move')
 # Generated-source-only reconstruction of one historical generation, no Charon/Aeneas rerun.
 src=W/'g0-base';reb=W/'recompute-g0-base';reb.mkdir();(reb/'Fixture').mkdir()
 for p in [src/'Fixture.lean',src/'Fixture/Funs.lean',src/'Fixture/Types.lean',src/'Proof.lean',src/'Historical.lean']:
  shutil.copy2(p,reb/p.relative_to(src))
 rows=[];t=time.monotonic()
 for mod in ['Fixture/Types','Fixture/Funs','Fixture']:
  r=call('recompute:'+mod,[LEAN,'-o',mod+'.olean',mod+'.lean'],reb);rows.append(r);assert r['exit']==0,r
 RESULT['recompute']['compile_seconds']=round(time.monotonic()-t,3)
 r=call('recompute:proof',[LEAN,'--json','Proof.lean'],reb);assert r['exit']==0,r
 RESULT['recompute']['proof_seconds']=r['seconds']
 RESULT['recompute']['generated_olean_sha256']={x:sha(reb/(x+'.olean')) for x in ['Fixture/Types','Fixture/Funs','Fixture']}
 RESULT['recompute']['historical_goal']=session('recomputed-g0-base',reb)['goal']
 RESULT['peak_sampled_rss_kib']=PEAK
 (S/'results.json').write_text(json.dumps(RESULT,indent=2)+'\n')
 print(json.dumps({'retention':RESULT['retention'],'sessions':len(RESULT['sessions']),
  'recompile_seconds':RESULT['recompute']['compile_seconds'],'peak_sampled_rss_kib':PEAK}))
if __name__=='__main__':main()
