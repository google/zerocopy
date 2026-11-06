#!/usr/bin/env python3
"""Pinned native plugin v1→v2→v1 path replacement across one Lean watchdog."""
import hashlib,json,os,re,select,shutil,subprocess,time
from pathlib import Path

S=Path(__file__).resolve().parent
WORK=S/'work'
SOURCE=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/scratch/20260927-reference-experiments/reference-publish/reports/anneal-3730-lake-plugin-artifact-identity-v4-30-0-rc2/support/work')
BIN=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean')
PLUGIN='plugin__probe_Plugin.dylib'
LOG=[]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ev(kind,**kw):LOG.append(dict(seq=len(LOG),kind=kind,**kw))
def plugin(root):return root/'.lake/build/lib/lean'/PLUGIN
class Server:
 def __init__(self,label,root):
  self.label=label;self.root=root;self.buf=b'';self.n=10
  env=dict(os.environ,LEAN_NUM_THREADS='1',LEAN_PATH=str(root/'.lake/build/lib/lean'),PLUGIN_MARKER=str(root/'marker.txt'))
  self.p=subprocess.Popen([str(BIN),'--plugin='+str(plugin(root)),'--server'],cwd=root,env=env,
      stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0)
  ev('server_start',label=label,pid=self.p.pid,plugin_sha256=sha(plugin(root)))
  self.send(dict(jsonrpc='2.0',id=1,method='initialize',params=dict(processId=os.getpid(),rootUri=root.as_uri(),capabilities={},initializationOptions={'hasWidgets':False})))
  self.until(1,20);self.send(dict(jsonrpc='2.0',method='initialized',params={}))
 def send(self,m):
  raw=json.dumps(m,separators=(',',':')).encode();self.p.stdin.write(b'Content-Length: '+str(len(raw)).encode()+b'\r\n\r\n'+raw);self.p.stdin.flush()
  ev('client',label=self.label,message=m)
 def read(self,timeout=20):
  end=time.monotonic()+timeout
  while time.monotonic()<end:
   if b'\r\n\r\n' in self.buf:
    h,b=self.buf.split(b'\r\n\r\n',1)
    n=[int(x.split(b':',1)[1]) for x in h.split(b'\r\n') if x.lower().startswith(b'content-length:')]
    if n and len(b)>=n[0]:
     raw,self.buf=b[:n[0]],b[n[0]:];m=json.loads(raw);ev('server',label=self.label,message=m)
     if 'method' in m and 'id' in m:self.send(dict(jsonrpc='2.0',id=m['id'],result=None))
     return m
   rd,_,_=select.select([self.p.stdout],[],[],min(.1,max(0,end-time.monotonic())))
   if rd:
    x=os.read(self.p.stdout.fileno(),65536)
    if not x:break
    self.buf+=x
  raise TimeoutError('server read '+self.label)
 def until(self,rid,timeout=20):
  end=time.monotonic()+timeout
  while time.monotonic()<end:
   m=self.read(max(.1,end-time.monotonic()))
   if m.get('id')==rid and 'method' not in m:return m
  raise TimeoutError('server response '+str(rid))
 def req(self,method,params):
  rid=self.n;self.n+=1;self.send(dict(jsonrpc='2.0',id=rid,method=method,params=params));return self.until(rid)
 def open(self,name):
  uri=(self.root/name).as_uri();self.send(dict(jsonrpc='2.0',method='textDocument/didOpen',params={'textDocument':dict(uri=uri,languageId='lean',version=1,text=(self.root/name).read_text())}))
  wait=self.req('textDocument/waitForDiagnostics',dict(uri=uri,version=1))
  goal=self.goal(name)
  return dict(wait=wait,goal=goal)
 def goal(self,name):
  return self.req('$/lean/plainGoal',dict(textDocument=dict(uri=(self.root/name).as_uri()),position=dict(line=2,character=4)))
 def stop(self):
  if self.p.poll() is None:
   try:
    self.send(dict(jsonrpc='2.0',id=99,method='shutdown',params=None));self.until(99,6)
    self.send(dict(jsonrpc='2.0',method='exit'));self.p.wait(timeout=6)
   except Exception:self.p.kill();self.p.wait()
  ev('server_stop',label=self.label,exit=self.p.returncode,stderr=self.p.stderr.read().decode(errors='replace'))
def phase(s,label,name):
 r=s.open(name);marker=s.root/'marker.txt'
 ev('phase',label=label,file=name,plugin_sha256=sha(plugin(s.root)),
    marker=marker.read_text() if marker.exists() else None,wait=r['wait'],goal=r['goal'])
 assert 'error' not in r['wait'] and 'error' not in r['goal'],r
def replace(root,src,label):
 target=plugin(root);old=sha(target);tmp=target.with_suffix('.replacement');shutil.copy2(src,tmp);os.replace(tmp,target)
 ev('replace',label=label,old_sha256=old,new_sha256=sha(target),marker=(root/'marker.txt').read_text())
def main():
 assert BIN.is_file() and (SOURCE/'seed-v1').is_dir()
 assert shutil.disk_usage(S).free>2*1024**3
 mp=subprocess.run(['memory_pressure','-Q'],capture_output=True,text=True,timeout=5)
 m=re.search(r'System-wide memory free percentage: (\d+)%',mp.stdout)
 if m and int(m.group(1))<20:raise RuntimeError('less than 20 percent free memory')
 if WORK.exists():shutil.rmtree(WORK)
 WORK.mkdir();live=WORK/'live';shutil.copytree(SOURCE/'seed-v1',live)
 artifacts=S/'artifacts';artifacts.mkdir(exist_ok=True)
 p1=artifacts/'plugin-v1.dylib';p2=artifacts/'plugin-v2.dylib'
 if not p1.exists():shutil.copy2(plugin(SOURCE/'seed-v1'),p1)
 if not p2.exists():shutil.copy2(plugin(SOURCE/'seed-v2'),p2)
 proof=(live/'Proof.lean').read_text()
 for name in ['P0.lean','P1.lean','P2.lean','P3.lean']:(live/name).write_text(proof)
 (live/'marker.txt').unlink(missing_ok=True)
 ev('subject',lean_sha256=sha(BIN),v1_plugin_sha256=sha(p1),v2_plugin_sha256=sha(p2),
    dep_olean_sha256=sha(live/'.lake/build/lib/lean/Dep.olean'),proof_sha256=sha(live/'P0.lean'),
    free_memory_percent=int(m.group(1)) if m else None)
 s=Server('retained',live)
 try:
  phase(s,'v1-first','P0.lean')
  replace(live,p2,'v1-to-v2')
  ev('old_goal_v1_after_v2',goal=s.goal('P0.lean'),marker=(live/'marker.txt').read_text())
  phase(s,'v2-second','P1.lean')
  replace(live,p1,'v2-to-v1')
  ev('old_goal_v2_after_v1',goal=s.goal('P1.lean'),marker=(live/'marker.txt').read_text())
  phase(s,'v1-third','P2.lean')
 finally:s.stop()
 # Exactly one server at a time: fresh process after the retained watchdog exits.
 (live/'marker.txt').unlink(missing_ok=True)
 fresh=Server('fresh',live)
 try:phase(fresh,'v1-after-restart','P3.lean')
 finally:fresh.stop()
 ev('final_artifact',plugin_sha256=sha(plugin(live)),dep_olean_sha256=sha(live/'.lake/build/lib/lean/Dep.olean'))
 (S/'transcript.json').write_text(json.dumps(LOG,indent=2)+'\n')
 print(json.dumps({'phases':[(x['label'],x['marker']) for x in LOG if x['kind']=='phase']}))
if __name__=='__main__':main()
