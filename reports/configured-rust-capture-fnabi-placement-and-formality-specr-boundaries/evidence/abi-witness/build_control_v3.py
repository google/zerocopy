"""One reviewed observer build, or harmless lifecycle regression. No observer run."""
from pathlib import Path
import hashlib,json,os,signal,subprocess,sys,time,traceback
B=Path(__file__).resolve().parent
T=B.parent/'toolchains/rustup/toolchains/nightly-2026-05-01-aarch64-apple-darwin'
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,z):p.write_text(json.dumps(z,indent=2)+'\n')
class ScopedMonitor:
 def command(self,argv,empty_ok=False):
  p=subprocess.run(argv,capture_output=True,text=True,timeout=5)
  if p.returncode==0:return p.stdout
  if empty_ok and p.returncode==1 and not p.stdout.strip() and not p.stderr.strip():return ''
  raise RuntimeError('monitor command failed: '+repr((argv,p.returncode,p.stderr)))
 def preflight(self):
  self.command(['/bin/ps','-o','pid=,ppid=,rss=','-p',str(os.getpid())])
  self.command(['/usr/bin/pgrep','-P',str(os.getpid())],empty_ok=True)
 def sample(self,pid):
  # Process-group scope belongs to the child created with start_new_session=True.
  text=self.command(['/usr/bin/pgrep','-g',str(pid)],empty_ok=True)
  pids={int(x) for x in text.split()}
  if not pids:return {'pids':[],'rss_tree_bytes':0}
  text=self.command(['/bin/ps','-o','pid=,ppid=,rss=','-p',','.join(str(p) for p in sorted(pids))],empty_ok=True)
  rows=[tuple(map(int,line.split())) for line in text.splitlines()]
  return {'pids':[x[0] for x in rows],'rss_tree_bytes':sum(x[2]*1024 for x in rows)}
 def remaining(self,pid):return [int(x) for x in self.command(['/usr/bin/pgrep','-g',str(pid)],empty_ok=True).split()]
class DenyPreflight:
 def preflight(self):raise PermissionError(1,'simulated monitor denial before launch')
class DenyAfterLaunch:
 def preflight(self):pass
 def sample(self,pid):raise PermissionError(1,'simulated monitor denial after PID receipt')
 def remaining(self,pid):return []
def run_owned(R,argv,env,monitor,extra_output=None,seconds=600):
 assert not R.exists();R.mkdir();(R/'tmp').mkdir()
 started=time.monotonic();launch_start=time.time_ns();p=None;samples=[];failure=None;stop=None;code=None;remaining=[]
 def output_bytes():
  return sum(x.stat().st_size for x in R.rglob('*') if x.is_file())+(extra_output.stat().st_size if extra_output and extra_output.is_file() else 0)
 save(R/'invocation.json',{'argv':argv,'env_exact':env,'cwd':str(B),'controller_sha256':h(Path(__file__))})
 try:
  monitor.preflight()  # MUST succeed before Popen.
  with (R/'stdout').open('xb') as out,(R/'stderr').open('xb') as err:
   try:
    p=subprocess.Popen(argv,cwd=B,env=env,stdout=out,stderr=err,start_new_session=True)
    save(R/'child.json',{'pid':p.pid,'pgid':p.pid,'launch_start_unix_ns':launch_start,'pid_persisted_unix_ns':time.time_ns(),'argv':argv})
    while p.poll() is None:
     row=monitor.sample(p.pid);row.update(seconds=time.monotonic()-started,output_bytes=output_bytes());samples.append(row)
     if row['rss_tree_bytes']>=1073741824:stop='observed process-group RSS >=1GiB'
     elif row['output_bytes']>=134217728:stop='observed output >=128MiB'
     elif row['seconds']>=seconds:stop='wall deadline'
     if stop:break
     time.sleep(0.1)
   finally:
    # Covers ps/pgrep failure, PID receipt failure, KeyboardInterrupt and budgets.
    if p is not None:
     if p.poll() is None:
      os.killpg(p.pid,signal.SIGTERM)
      try:p.wait(timeout=2)
      except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);p.wait()
     code=p.wait()
 except BaseException as e:
  failure={'type':type(e).__name__,'message':str(e),'traceback':traceback.format_exc()}
 finally:
  if p is not None:
   try:
    remaining=monitor.remaining(p.pid)
    if remaining:
     os.killpg(p.pid,signal.SIGTERM)
     failure=failure or {'type':'RemainingChildGroup','message':'Terminated remaining owned group after parent wait'}
   except BaseException as e:failure=failure or {'type':type(e).__name__,'message':'post-wait monitor: '+str(e)}
  save(R/'rss-samples.json',samples)
  result={'exit_code':code,'spawned':p is not None,'child_pid':p.pid if p else None,'seconds':time.monotonic()-started,'stop_reason':stop,'controller_failure':failure,'remaining_group_after_parent_wait':remaining,'max_observed_group_rss_bytes':max((s['rss_tree_bytes'] for s in samples),default=None),'rss_scope':'Periodic scoped ps KiB converted to bytes; not hardAS/isolation or unsampled peak proof.','output_bytes':output_bytes(),'stdout_sha256':h(R/'stdout') if (R/'stdout').exists() else None,'stderr_sha256':h(R/'stderr') if (R/'stderr').exists() else None}
  save(R/'result.json',result)
 return result

def regression():
 R=B/'controller-regression-v3';assert not R.exists();R.mkdir()
 argv=[sys.executable,'-B','-c','import time; time.sleep(30)']
 a=run_owned(R/'denied-before-launch',argv,{},DenyPreflight(),seconds=3)
 assert not a['spawned'] and a['exit_code'] is None and a['controller_failure']['type']=='PermissionError'
 b=run_owned(R/'denied-after-launch',argv,{},DenyAfterLaunch(),seconds=3)
 assert b['spawned'] and b['exit_code']==-signal.SIGTERM and b['controller_failure']['type']=='PermissionError'
 # wait() owns/reaped this exact child: a second waitpid cannot recover a live child.
 try:os.waitpid(b['child_pid'],os.WNOHANG)
 except ChildProcessError:reaped=True
 else:reaped=False
 assert reaped and (R/'denied-after-launch/child.json').exists()
 result={'status':'PASS','meaning':'Harmless owned Python child only; injected monitor denial retained PID/status, terminated and reaped child. No compiler or observer run.','controller_sha256':h(Path(__file__)),'before_spawned':a['spawned'],'after_PID':b['child_pid'],'after_exit_code':b['exit_code'],'child_reaped':reaped}
 save(R/'regression.json',result);print(json.dumps(result,indent=2))
def build():
 assert h(B/'prepared-manifest.json')=='f43a6306944d5ee5c2e1984f1bafd20fe95706e6217e0c6c3ec1640547ca26b8'
 for f in json.loads((B/'prepared-manifest.json').read_text())['files']:
  p=B/f['path'];assert p.stat().st_size==f['bytes'] and h(p)==f['sha256']
 assert h(B/'observer_v3.rs')=='e6c50e7c4ce7bc9ff5eb5515cc4f5973fd2fc182d53bce38dbfeb09afc398ba1'
 assert json.loads((B/'controller-regression-v3/regression.json').read_text())['status']=='PASS'
 assert h(Path(__file__))==json.loads((B/'controller-regression-v3/regression.json').read_text())['controller_sha256']
 ident=json.loads((B/'source-identities.json').read_text())
 def tools():
  for f in ident['readonly_tools']:
   p=T/f['toolchain_relative_path'];assert p.stat().st_size==f['bytes'] and h(p)==f['sha256']
 tools();R=B/'build-03';O=B/'observer-v3';assert not O.exists()
 argv=[str(T/'bin/rustc'),str(B/'observer_v3.rs'),'--sysroot',str(T),'--edition=2021','-C','opt-level=0','-C','debuginfo=0','-C','rpath','-Zthreads=1','-Ccodegen-units=1','-o',str(O)]
 env={'PATH':'/usr/bin:/bin:/usr/sbin:/sbin','TMPDIR':str(R/'tmp'),'LC_ALL':'C','LANG':'C'}
 save(B/'build-03-plan.json',{'argv':argv,'source_sha256':h(B/'observer_v3.rs'),'original_preparation_manifest_sha256':h(B/'prepared-manifest.json'),'historical_request_catalog_sha256':h(B/'requests.json'),'new_profile_status':'Planned corrected observer source only; historical request/catalog not rewritten.','controller_sha256':h(Path(__file__))})
 result=run_owned(R,argv,env,ScopedMonitor(),O)
 tools();assert h(B/'observer_v3.rs')=='e6c50e7c4ce7bc9ff5eb5515cc4f5973fd2fc182d53bce38dbfeb09afc398ba1'
 result['tools_before_after']='All5 frozen tool hashes/sizes unchanged';result['observer_sha256']=h(O) if O.is_file() else None;result['observer_bytes']=O.stat().st_size if O.is_file() else None;result['observer_or_fixture_invocations']=0
 save(R/'result.json',result);print(json.dumps(result,indent=2))
if __name__=='__main__':
 if sys.argv[1:]==['--regression']:regression()
 elif sys.argv[1:]==['--build']:build()
 else:raise SystemExit('choose --regression or --build; observer is never run')
