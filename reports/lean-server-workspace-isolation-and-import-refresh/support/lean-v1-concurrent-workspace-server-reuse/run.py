import hashlib,json,os,pathlib,select,shutil,subprocess,time
import argparse
ARGS=argparse.ArgumentParser(description='Run two independent generated-project Lean servers with shared dependencies.')
ARGS.add_argument('--workspace-root',required=True,help='directory containing worker-a and worker-b')
ARGS.add_argument('--evidence-dir',required=True,help='directory for the JSON-RPC/resource transcript')
ARGS.add_argument('--monitor',required=True,help='path to proc-tree compiled from proc-tree.c')
ARGS.add_argument('--lean',default=shutil.which('lean'),help='Lean executable; defaults to lean found on PATH')
ARGS=ARGS.parse_args()
BASE=pathlib.Path(ARGS.workspace_root).resolve()
LEAN=pathlib.Path(ARGS.lean).resolve() if ARGS.lean else None
MON=pathlib.Path(ARGS.monitor).resolve(); OUT=pathlib.Path(ARGS.evidence_dir).resolve();OUT.mkdir(parents=True,exist_ok=True)
if LEAN is None: raise SystemExit('lean not found on PATH; pass --lean')
SOURCES={'v1':lambda label:f'import Generated\n\ntheorem {label}_ok : True := by\n  trivial\n','v2':lambda label:f'import Generated\n\ntheorem {label}_ok : True := by\n  exact True.intro\n'}
EVENTS=[];START=time.monotonic();SERVERS=[];DONE=set();MAX_RSS=3_500_000_000;MIN_FREE=20;MIN_DISK=5*(1<<30)
def record(kind,**d):EVENTS.append({'elapsed_ms':round((time.monotonic()-START)*1000),'kind':kind,**d})
def parse_env(cwd):
 p=subprocess.run(['lake','--offline','env','printenv'],cwd=cwd,capture_output=True,text=True,timeout=30)
 if p.returncode:raise RuntimeError(f'lake env printenv exit {p.returncode}: {p.stderr}')
 e=dict(os.environ)
 for line in p.stdout.splitlines():
  k,sep,v=line.partition('=')
  if sep:e[k]=v
 record('lake_env',cwd=str(cwd),returncode=p.returncode,lean_path_sha256=hashlib.sha256(e.get('LEAN_PATH','').encode()).hexdigest())
 return e
def resources(label):
 sample={'label':label,'disk_free_bytes':shutil.disk_usage(BASE).free}
 m=subprocess.run(['memory_pressure','-Q'],capture_output=True,text=True,timeout=5)
 sample['memory_pressure_exit']=m.returncode;sample['memory_pressure_stdout']=m.stdout;sample['memory_pressure_stderr']=m.stderr
 for line in m.stdout.splitlines():
  if line.startswith('System-wide memory free percentage:'):
   try:sample['memory_free_percent']=int(line.rsplit(' ',1)[-1].rstrip('%'))
   except ValueError:pass
 total=0;details=[]
 for s in SERVERS:
  if s['proc'].poll() is None:
   q=subprocess.run([str(MON),str(s['proc'].pid)],capture_output=True,text=True,timeout=4)
   if q.returncode:raise RuntimeError(f'process monitor failed: {q.stderr}')
   totalrow=next(x for x in q.stdout.splitlines() if x.startswith('TOTAL\t'));rss=int(totalrow.split('\t')[1]);total+=rss
   details.append({'label':s['label'],'pid':s['proc'].pid,'tree_rss_bytes':rss,'processes':[x.split('\t') for x in q.stdout.splitlines() if '\t' in x and not x.startswith('TOTAL\t')]})
 sample.update(active_servers=len(details),aggregate_tree_rss_bytes=total,servers=details);record('resource_sample',**sample)
 if total>MAX_RSS:raise RuntimeError(f'aggregate resident-size guard exceeded ({total} > {MAX_RSS})')
 if sample.get('memory_free_percent') is not None and sample['memory_free_percent']<MIN_FREE:raise RuntimeError(f'memory floor violated ({sample["memory_free_percent"]}%)')
 if sample['disk_free_bytes']<MIN_DISK:raise RuntimeError('disk floor violated')
def write_msg(p,msg):
 raw=json.dumps(msg,separators=(',',':')).encode();p['proc'].stdin.write(b'Content-Length: '+str(len(raw)).encode()+b'\r\n\r\n'+raw);p['proc'].stdin.flush();record('client',server=p['label'],message=msg)
def recv(p,pred,timeout=45):
 end=time.monotonic()+timeout
 while time.monotonic()<end:
  while b'\r\n\r\n' in p['buf']:
   h,rest=p['buf'].split(b'\r\n\r\n',1);ls=[int(z.split(b':',1)[1]) for z in h.split(b'\r\n') if z.lower().startswith(b'content-length:')]
   if not ls or len(rest)<ls[0]:break
   raw,p['buf']=rest[:ls[0]],rest[ls[0]:];m=json.loads(raw);record('server',server=p['label'],message=m)
   if m.get('method')=='client/registerCapability' and 'id' in m:write_msg(p,{'jsonrpc':'2.0','id':m['id'],'result':None})
   if m.get('method')=='$/lean/fileProgress':
    z=m.get('params',{});td=z.get('textDocument',{})
    if td.get('uri')==p['file'].as_uri() and not z.get('processing'):DONE.add((p['label'],td.get('version')))
   if pred(m):return m
  rd,_,_=select.select([p['proc'].stdout],[],[],min(.1,max(0,end-time.monotonic())))
  if rd:
   chunk=os.read(p['proc'].stdout.fileno(),65536)
   if not chunk:break
   p['buf']+=chunk
 raise TimeoutError(f'{p["label"]}: LSP timeout')
def send_request(p,method,params):
 p['seq']+=1;rid=p['seq'];write_msg(p,{'jsonrpc':'2.0','id':rid,'method':method,'params':params});return recv(p,lambda m:m.get('id')==rid)
def await_doc(p,ver):
 send_request(p,'textDocument/waitForDiagnostics',{'uri':p['file'].as_uri(),'version':ver})
 if (p['label'],ver) not in DONE:recv(p,lambda m:m.get('method')=='$/lean/fileProgress' and m.get('params',{}).get('textDocument',{}).get('uri')==p['file'].as_uri() and m.get('params',{}).get('textDocument',{}).get('version')==ver and not m.get('params',{}).get('processing'),timeout=90)
def query(p,label,char):
 m=send_request(p,'$/lean/plainGoal',{'textDocument':{'uri':p['file'].as_uri()},'position':{'line':3,'character':char}})
 record('goal_query',server=p['label'],label=label,character=char,result=m.get('result'),error=m.get('error'));return m
def start(label,source):
 DONE.discard((label,1))
 cwd=BASE/label;f=cwd/'Probe.lean';env=parse_env(cwd);env['LEAN_NUM_THREADS']='1'
 p={'label':label,'cwd':cwd,'file':f,'buf':b'','seq':0,'proc':None}
 p['proc']=subprocess.Popen([str(LEAN),'--server'],cwd=cwd,env=env,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0);SERVERS.append(p)
 record('server_start',server=label,pid=p['proc'].pid,cwd=str(cwd),source_sha256=hashlib.sha256(source.encode()).hexdigest())
 send_request(p,'initialize',{'processId':os.getpid(),'rootUri':cwd.as_uri(),'capabilities':{},'initializationOptions':{'hasWidgets':False}})
 write_msg(p,{'jsonrpc':'2.0','method':'initialized','params':{}});f.write_text(source)
 write_msg(p,{'jsonrpc':'2.0','method':'textDocument/didOpen','params':{'textDocument':{'uri':f.as_uri(),'languageId':'lean','version':1,'text':source}}});await_doc(p,1)
 query(p,'before-tactic',2);query(p,'after-tactic',len(source.splitlines()[3]));return p
def edit(p,source,ver):
 p['file'].write_text(source);write_msg(p,{'jsonrpc':'2.0','method':'textDocument/didChange','params':{'textDocument':{'uri':p['file'].as_uri(),'version':ver},'contentChanges':[{'text':source}]}});await_doc(p,ver)
 query(p,'edit-before-tactic',2);query(p,'edit-after-tactic',len(source.splitlines()[3]))
def stop(p,why):
 if p['proc'].poll() is None:
  try:send_request(p,'shutdown',None);write_msg(p,{'jsonrpc':'2.0','method':'exit'});p['proc'].wait(timeout=10)
  except Exception:p['proc'].kill();p['proc'].wait(timeout=4)
 record('server_stop',server=p['label'],reason=why,exit_code=p['proc'].returncode,stderr=p['proc'].stderr.read().decode(errors='replace'))
def main():
 (BASE/'worker-a/Probe.lean').write_text(SOURCES['v1']('worker_a_ok'))
 (BASE/'worker-b/Probe.lean').write_text(SOURCES['v1']('worker_b_ok'))
 resources('baseline');a=start('worker-a',SOURCES['v1']('worker_a_ok'));resources('one-loaded-generated-project-server')
 b=start('worker-b',SOURCES['v1']('worker_b_ok'));resources('two-loaded-independent-generated-project-servers')
 edit(a,SOURCES['v2']('worker_a_ok'),2);edit(b,SOURCES['v2']('worker_b_ok'),2);resources('two-servers-after-independent-edits')
 stop(a,'graceful-stop-for-reconstruction');fresh=start('worker-a',SOURCES['v2']('worker_a_ok'));resources('restarted-worker-a-while-worker-b-remains-live')
 stop(fresh,'graceful-shutdown');stop(b,'graceful-shutdown');resources('after-stop')
 (OUT/'transcript.json').write_text(json.dumps(EVENTS,indent=2)+'\n')
 print(json.dumps({'resource_samples':[e for e in EVENTS if e['kind']=='resource_sample'],'goal_results':[e for e in EVENTS if e['kind']=='goal_query'],'transcript':str(OUT/'transcript.json')},indent=2))
try:main()
except Exception as e:
 record('abort',error=repr(e))
 for p in SERVERS:
  if p['proc'].poll() is None:p['proc'].kill();p['proc'].wait();record('forced_stop',server=p['label'])
 (OUT/'transcript.json').write_text(json.dumps(EVENTS,indent=2)+'\n');raise
