#!/usr/bin/env python3
"""Inspect real plugin mappings across Lean file-worker path transitions."""
import gzip,hashlib,json,os,re,select,shutil,signal,subprocess,threading,time
from pathlib import Path

S=Path(__file__).resolve().parent
WORK=S/'run'
SOURCE=S/'seed'
BIN=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean')
PLUGIN='plugin__probe_Plugin.dylib'
LOG=[]
PEAK_RSS_KIB=0
SAMPLES=0
ACTIVE_SERVER_PID=None
MONITOR_STOP=threading.Event()
CAP_KIB=1536*1024
GUARD_ABORT_PATH=S/'guard-abort.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ev(kind,**kw):LOG.append(dict(seq=len(LOG),kind=kind,**kw))
def plugin(root):return root/'.lake/build/lib/lean'/PLUGIN
def process_rows():
 raw=subprocess.check_output(['/bin/ps','-axo','pid=,ppid=,pgid=,rss=,command='],text=True)
 rows=[]
 for line in raw.splitlines():
  parts=line.split(None,4)
  if len(parts)==5:
   try:rows.append({'pid':int(parts[0]),'ppid':int(parts[1]),'pgid':int(parts[2]),'rss_kib':int(parts[3]),'command':parts[4]})
   except ValueError:pass
 return rows
def process_tree(root,rows):
 children={}
 for row in rows:children.setdefault(row['ppid'],[]).append(row['pid'])
 pending=[root];seen=set()
 while pending:
  pid=pending.pop()
  if pid in seen:continue
  seen.add(pid);pending.extend(children.get(pid,[]))
 return [row for row in rows if row['pid'] in seen]
def kill_tree(root):
 for row in reversed(process_tree(root,process_rows())):
  try:os.kill(row['pid'],signal.SIGKILL)
  except ProcessLookupError:pass
def monitor():
 global PEAK_RSS_KIB,SAMPLES
 while not MONITOR_STOP.is_set():
  rows=process_rows()
  tree=process_tree(ACTIVE_SERVER_PID,rows) if ACTIVE_SERVER_PID is not None else []
  included={r['pid'] for r in tree}
  own=[r for r in rows if (r['pid']==os.getpid() or r['ppid']==os.getpid()) and r['pid'] not in included]
  total=sum(r['rss_kib'] for r in tree)+sum(r['rss_kib'] for r in own)
  PEAK_RSS_KIB=max(PEAK_RSS_KIB,total);SAMPLES+=1
  if total>CAP_KIB:
   GUARD_ABORT_PATH.write_text(json.dumps({'reason':'process-tree RSS cap exceeded',
       'total_kib':total,'cap_kib':CAP_KIB,'active_server_pid':ACTIVE_SERVER_PID,
       'tree':process_tree(ACTIVE_SERVER_PID,rows) if ACTIVE_SERVER_PID is not None else []},indent=2)+'\n')
   if ACTIVE_SERVER_PID is not None:kill_tree(ACTIVE_SERVER_PID)
   MONITOR_STOP.set();return
  MONITOR_STOP.wait(.05)
def mapping(label,server):
 rows=[r for r in process_tree(server.p.pid,process_rows()) if 'lean' in r['command']]
 out=[];logdir=S/'mapping-logs';logdir.mkdir(exist_ok=True)
 for row in rows:
  observed={'process':row,'tools':{}}
  for tool,path,args in [('lsof','/usr/sbin/lsof',['-nP','-p',str(row['pid'])]),
                         ('vmmap','/usr/bin/vmmap',[str(row['pid'])])]:
   p=subprocess.run([path,*args],capture_output=True,text=True,timeout=12)
   raw=p.stdout+p.stderr
   archive=logdir/f'{label}-{row["pid"]}-{tool}.txt.gz'
   with gzip.open(archive,'wt',encoding='utf-8') as f:f.write(raw)
   lines=[line for line in raw.splitlines() if 'plugin-v1.dylib' in line or 'plugin-v2.dylib' in line or PLUGIN in line]
   observed['tools'][tool]={'exit':p.returncode,'raw_sha256':hashlib.sha256(raw.encode()).hexdigest(),
                            'archive':archive.name,'matching_lines':lines}
  out.append(observed)
 ev('mapping',label=label,server_pid=server.p.pid,processes=out)
 return out
class Server:
 def __init__(self,label,root):
  global ACTIVE_SERVER_PID
  self.label=label;self.root=root;self.buf=b'';self.n=10
  env=dict(os.environ,LEAN_NUM_THREADS='1',LEAN_PATH=str(root/'.lake/build/lib/lean'),PLUGIN_MARKER=str(root/'marker.txt'))
  self.p=subprocess.Popen([str(BIN),'--plugin='+str(plugin(root)),'--server'],cwd=root,env=env,
      stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0,start_new_session=True)
  ACTIVE_SERVER_PID=self.p.pid
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
 def close(self,name):
  self.send(dict(jsonrpc='2.0',method='textDocument/didClose',params={'textDocument':{'uri':(self.root/name).as_uri()}}))
 def stop(self):
  if self.p.poll() is None:
   try:
    self.send(dict(jsonrpc='2.0',id=99,method='shutdown',params=None));self.until(99,6)
    self.send(dict(jsonrpc='2.0',method='exit'));self.p.wait(timeout=6)
   except Exception:kill_tree(self.p.pid);self.p.wait()
  ev('server_stop',label=self.label,exit=self.p.returncode,stderr=self.p.stderr.read().decode(errors='replace'))
def phase(s,label,name):
 r=s.open(name);marker=s.root/'marker.txt'
 ev('phase',label=label,file=name,plugin_sha256=sha(plugin(s.root)),
    marker=marker.read_text() if marker.exists() else None,wait=r['wait'],goal=r['goal'])
 assert 'error' not in r['wait'] and 'error' not in r['goal'],r
def replace(root,version,label):
 target=plugin(root);old=sha(target);tmp=target.with_suffix('.next')
 tmp.unlink(missing_ok=True);tmp.symlink_to(f'{version}/{PLUGIN}');os.replace(tmp,target)
 ev('replace',label=label,old_sha256=old,new_sha256=sha(target),
    link_target=os.readlink(target),marker=(root/'marker.txt').read_text() if (root/'marker.txt').exists() else None)
def main():
 global ACTIVE_SERVER_PID
 assert BIN.is_file() and SOURCE.is_dir()
 assert shutil.disk_usage(S).free>10*1024**3
 mp=subprocess.run(['memory_pressure','-Q'],capture_output=True,text=True,timeout=5)
 m=re.search(r'System-wide memory free percentage: (\d+)%',mp.stdout)
 if not m or int(m.group(1))<30:raise RuntimeError('less than 30 percent free memory')
 if WORK.exists() or (S/'transcript.json').exists() or (S/'guard-abort.json').exists():raise RuntimeError('fresh absent run/results required')
 WORK.mkdir();live=WORK/'live';shutil.copytree(SOURCE,live,symlinks=True)
 artifacts=S/'artifacts'
 p1=artifacts/'plugin-v1.dylib';p2=artifacts/'plugin-v2.dylib'
 assert p1.is_file() and p2.is_file()
 target=plugin(live);target.unlink()
 for version,source in [('v1',p1),('v2',p2)]:
  directory=target.parent/version;directory.mkdir()
  shutil.copy2(source,directory/PLUGIN)
 target.symlink_to(f'v1/{PLUGIN}')
 proof=(live/'Proof.lean').read_text()
 for name in ['P0.lean','P1.lean','P2.lean','P3.lean']:(live/name).write_text(proof)
 (live/'marker.txt').unlink(missing_ok=True)
 ev('subject',lean_sha256=sha(BIN),v1_plugin_sha256=sha(p1),v2_plugin_sha256=sha(p2),
    dep_olean_sha256=sha(live/'.lake/build/lib/lean/Dep.olean'),proof_sha256=sha(live/'P0.lean'),
    free_memory_percent=int(m.group(1)),free_disk_bytes=shutil.disk_usage(S).free,
    rss_cap_kib=CAP_KIB,plugin_link=os.readlink(target))
 watcher=threading.Thread(target=monitor,daemon=True);watcher.start()
 s=Server('retained',live);ACTIVE_SERVER_PID=s.p.pid
 try:
  phase(s,'v1-first','P0.lean')
  mapping('v1-first',s)
  s.close('P0.lean');time.sleep(.5)
  mapping('v1-after-close',s)
  replace(live,'v2','v1-to-v2')
  phase(s,'v2-second','P1.lean')
  mapping('v2-open',s)
  s.close('P1.lean');time.sleep(.5)
  mapping('v2-after-close',s)
  replace(live,'v1','v2-to-v1')
  phase(s,'v1-third','P2.lean')
  mapping('v1-reopened',s)
 finally:
  retained_pids=[r['pid'] for r in process_tree(s.p.pid,process_rows())]
  s.stop();ACTIVE_SERVER_PID=None
 ev('after_retained_shutdown',remaining_processes=[r for r in process_rows() if r['pid'] in retained_pids])
 # Exactly one server at a time: fresh process after the retained watchdog exits.
 (live/'marker.txt').unlink(missing_ok=True)
 fresh=Server('fresh',live);ACTIVE_SERVER_PID=fresh.p.pid
 try:
  phase(fresh,'v1-after-restart','P3.lean')
  mapping('fresh-v1',fresh)
 finally:
  fresh_pids=[r['pid'] for r in process_tree(fresh.p.pid,process_rows())]
  fresh.stop();ACTIVE_SERVER_PID=None
 ev('after_fresh_shutdown',remaining_processes=[r for r in process_rows() if r['pid'] in fresh_pids])
 MONITOR_STOP.set();watcher.join(timeout=2)
 ev('resources',peak_process_tree_rss_kib=PEAK_RSS_KIB,samples=SAMPLES,cap_kib=CAP_KIB)
 ev('final_artifact',plugin_sha256=sha(plugin(live)),dep_olean_sha256=sha(live/'.lake/build/lib/lean/Dep.olean'))
 (S/'transcript.json').write_text(json.dumps(LOG,indent=2)+'\n')
 shutil.rmtree(WORK)
 print(json.dumps({'phases':[(x['label'],x['marker']) for x in LOG if x['kind']=='phase']}))
if __name__=='__main__':main()
