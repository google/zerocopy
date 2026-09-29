#!/usr/bin/env python3
"""Two pinned Lake writers, one writable package tree, changed definition, one kill."""
import hashlib,json,os,signal,shutil,subprocess,time
from pathlib import Path

S=Path(__file__).resolve().parent
T=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools')
ROOT=T/'elan/toolchains/leanprover--lean4---v4.30.0-rc2'
LAKE=ROOT/'bin/lake';LEAN=ROOT/'bin/lean'
MODE=os.environ.get('PROBE_KILL','A')
assert MODE in ('A','B')
W=S/('work' if MODE=='A' else 'work-kill-B');P=W/'probe'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def inv(root):return {str(p.relative_to(root)):{'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(root.rglob('*')) if p.is_file()}
def src(n):return f'''import Lean
run_cmd do
  let marker ← IO.getEnv "WRITER_MARKER"
  let release ← IO.getEnv "WRITER_RELEASE"
  if let some marker := marker then
    IO.FS.writeFile marker "entered"
    if let some release := release then
      while !(← (System.FilePath.mk release).pathExists) do
        IO.sleep 10
def depValue : Nat := {n}
'''
def env(marker=None,release=None):
 e=dict(os.environ,LEAN_NUM_THREADS='1',LAKE_NO_NET='1',LAKE_ARTIFACT_CACHE='false',HOME=str(W/'home'))
 for k,v in [('WRITER_MARKER',marker),('WRITER_RELEASE',release)]:
  if v is None:e.pop(k,None)
  else:e[k]=str(v)
 return e
def run(label,args,cwd=P,envv=None,timeout=40):
 p=subprocess.run([str(x) for x in args],cwd=cwd,env=envv or env(),capture_output=True,text=True,timeout=timeout)
 return dict(label=label,argv=[str(x) for x in args],cwd=str(cwd),exit=p.returncode,stdout=p.stdout,stderr=p.stderr)
def tree_rss(pids):
 ps=subprocess.run(['ps','-axo','pid=,ppid=,rss='],capture_output=True,text=True)
 rows=[]
 for l in ps.stdout.splitlines():
  try:rows.append(tuple(map(int,l.split()[:3])))
  except ValueError:pass
 live=set(pids)
 for _ in range(8):live.update(pid for pid,parent,_ in rows if parent in live)
 return sum(rss for pid,_,rss in rows if pid in live),sorted(live)
def await_marker(marker,procs,limit=25):
 start=time.monotonic();peak=0;members=[]
 while not marker.exists():
  rss,pids=tree_rss([p.pid for p in procs]);peak=max(peak,rss);members=pids
  if rss>4400000:raise RuntimeError('sampled summed RSS over 4.4 GiB guard')
  if time.monotonic()-start>limit:raise TimeoutError('marker '+str(marker))
  if any(p.poll() is not None for p in procs):raise RuntimeError('writer exited before marker')
  time.sleep(.05)
 return dict(peak_sampled_rss_kib=peak,pids_at_marker=members)
def finish(p,label):
 try:out,err=p.communicate(timeout=45)
 except subprocess.TimeoutExpired:
  os.killpg(p.pid,signal.SIGKILL);out,err=p.communicate();raise
 return dict(label=label,exit=p.returncode,stdout=out,stderr=err)
def main():
 assert LAKE.is_file() and LEAN.is_file()
 assert shutil.disk_usage(S).free>10*1024**3
 if W.exists():shutil.rmtree(W)
 P.mkdir(parents=True);(W/'home').mkdir()
 (P/'lean-toolchain').write_text('leanprover/lean4:v4.30.0-rc2\n')
 (P/'lakefile.lean').write_text('import Lake\nopen Lake DSL\npackage probe\n@[default_target]\nlean_lib Dep\n')
 (P/'Dep.lean').write_text(src(7))
 out={'schema':'anneal-shared-lake-tree-conflict-v1','tools':{'lake_sha256':sha(LAKE),'lean_sha256':sha(LEAN)},
      'source_a_sha256':sha(P/'Dep.lean'),'records':[],'events':[]}
 mA,mB=W/'A.entered',W/'B.entered';rA,rB=W/'A.release',W/'B.release'
 procs=[]
 try:
  a=subprocess.Popen([str(LAKE),'build','Dep'],cwd=P,env=env(mA,rA),stdout=subprocess.PIPE,
                     stderr=subprocess.PIPE,text=True,start_new_session=True);procs.append(a)
  out['events'].append(dict(kind='launch_A',pid=a.pid))
  out['A_gate']=await_marker(mA,[a]);out['events'].append(dict(kind='A_entered'))
  (P/'Dep.lean').write_text(src(9));out['source_b_sha256']=sha(P/'Dep.lean')
  out['events'].append(dict(kind='source_changed_to_9'))
  b=subprocess.Popen([str(LAKE),'build','Dep'],cwd=P,env=env(mB,rB),stdout=subprocess.PIPE,
                     stderr=subprocess.PIPE,text=True,start_new_session=True);procs.append(b)
  out['events'].append(dict(kind='launch_B',pid=b.pid))
  try:
   out['B_gate']=await_marker(mB,[a,b]);out['events'].append(dict(kind='B_entered'))
  except (TimeoutError,RuntimeError) as e:
   out['events'].append(dict(kind='B_gate_unavailable',detail=str(e)))
  victim,survivor=(a,b) if MODE=='A' else (b,a)
  os.killpg(victim.pid,signal.SIGKILL);out['events'].append(dict(kind='kill_'+MODE))
  out['records'].append(finish(victim,MODE))
  release=rB if MODE=='A' else rA
  release.write_text('release');out['events'].append(dict(kind='release_'+('B' if MODE=='A' else 'A')))
  out['records'].append(finish(survivor,'B' if MODE=='A' else 'A'))
  out['after_writers']=inv(P)
  out['records'].append(run('fresh_no_build',[LAKE,'--no-build','build','Dep']))
  (P/'Check9.lean').write_text('import Dep\ntheorem expected : depValue = 9 := by rfl\n#eval depValue\n')
  (P/'Check7.lean').write_text('import Dep\ntheorem stale : depValue = 7 := by rfl\n#eval depValue\n')
  e=env();e['LEAN_PATH']=str(P/'.lake/build/lib/lean')
  out['records'].append(run('pre_retry_lean_9',[LEAN,'Check9.lean'],envv=e))
  out['records'].append(run('pre_retry_lean_7',[LEAN,'Check7.lean'],envv=e))
  out['records'].append(run('ordinary_retry',[LAKE,'build','Dep']))
  out['records'].append(run('post_retry_no_build',[LAKE,'--no-build','build','Dep']))
  out['records'].append(run('fresh_lean_9',[LEAN,'Check9.lean'],envv=e))
  out['records'].append(run('fresh_lean_7_negative',[LEAN,'Check7.lean'],envv=e))
  out['final_inventory']=inv(P)
  out['source_final_sha256']=sha(P/'Dep.lean')
  assert out['records'][-2]['exit']==0 and out['records'][-1]['exit']!=0,out['records'][-2:]
  assert out['records'][-3]['exit']==0 and out['records'][-4]['exit']==0,out['records'][-4:]
 finally:
  for p in procs:
   if p.poll() is None:os.killpg(p.pid,signal.SIGKILL);p.wait()
  (S/('results.json' if MODE=='A' else 'results-kill-B.json')).write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps({'A':out['records'][0]['exit'],'B':out['records'][1]['exit'],
                  'no_build':out['records'][2]['exit'],'pre9':out['records'][3]['exit'],
                  'pre7':out['records'][4]['exit'],'retry':out['records'][5]['exit'],
                  'fresh9':out['records'][-2]['exit'],'fresh7':out['records'][-1]['exit']}))
if __name__=='__main__':main()
