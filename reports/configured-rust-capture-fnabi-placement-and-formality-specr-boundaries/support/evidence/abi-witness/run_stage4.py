"""One authorized fixed job at a time; consumer/source/flags remain unchanged.
Stops on any diagnostic, unexpected verdict or resource/controller issue.
"""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
B=Path(__file__).resolve().parent
S=B/'stage4'
T=B.parent/'toolchains/rustup/toolchains/nightly-2026-05-01-aarch64-apple-darwin'
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
JOBS={
 'check-subjects-o0':('check','host-subjects-opt0',B/'capture-v3-host-subjects-opt0-01/reference.json'),
 'capture-subjects-o2':('capture','host-subjects-opt2',None),
 'check-subjects-o2':('check','host-subjects-opt2',S/'runs/capture-subjects-o2/reference.json'),
 'capture-vectors-o0':('capture','host-vectors-opt0',None),
 'check-vectors-o0':('check','host-vectors-opt0',S/'runs/capture-vectors-o0/reference.json'),
 'capture-vectors-o2':('capture','host-vectors-opt2',None),
 'check-vectors-o2':('check','host-vectors-opt2',S/'runs/capture-vectors-o2/reference.json'),
}
def output_bytes():return sum(p.stat().st_size for p in S.rglob('*') if p.is_file())
def known_internal_warning(data,profile):
 if not profile.startswith('host-vectors-') or len(data)>8192:return False
 try:lines=data.decode('utf-8').splitlines()
 except UnicodeDecodeError:return False
 headlines=[x for x in lines if x.startswith('warning: the feature ')]
 if not 1<=len(headlines)<=2:return False
 for x in lines:
  if not x:continue
  if x in ['warning: the feature `repr_simd` is internal to the compiler or standard library','warning: the feature `simd_ffi` is internal to the compiler or standard library','  = note: using it is strongly discouraged','  = note: `#[warn(internal_features)]` on by default']:continue
  if re.fullmatch(r'\s*--> '+re.escape(str(B/'vectors.rs'))+r':\d+:\d+',x):continue
  if re.fullmatch(r'\s*(?:\d+ )?\|.*',x):continue
  if x=='warning: '+str(len(headlines))+(' warning emitted' if len(headlines)==1 else ' warnings emitted'):continue
  return False
 return '  = note: using it is strongly discouraged' in lines and '  = note: `#[warn(internal_features)]` on by default' in lines
def job(name):
 assert name in JOBS and not (S/'STOP.json').exists()
 assert h(B/'e33_consumer_v3.py')=='c0c476f3fe9e1497f4484b4de4c493194cd82d2fd93f5853fbfd7241f7aeb6da'
 assert h(B/'e33_data_v3.py')=='b9246631d37955add31da62f891eb9d0e0ec201a8a532ca3ccf385f8bced6018'
 assert h(B/'observer-v3')=='f1d0404e6c9cfca353376653c1ea9464c328d358851447e12af65953d368172b'
 if not S.exists():S.mkdir();(S/'jobs').mkdir();(S/'runs').mkdir()
 assert output_bytes()<268435456
 R=S/'jobs'/name;assert not R.exists();R.mkdir();(R/'tmp').mkdir()
 mode,profile,candidate=JOBS[name];run=S/'runs'/name;assert not run.exists()
 argv=[sys.executable,'-B',str(B/'e33_consumer_v3.py'),mode,'--toolchain',str(T),'--profile',profile,'--run-dir',str(run)]
 if candidate is not None:assert candidate.is_file();argv+=['--candidate',str(candidate)]
 env={'PATH':'/usr/bin:/bin:/usr/sbin:/sbin','LANG':'C','LC_ALL':'C','TMPDIR':str(R/'tmp'),'PYTHONDONTWRITEBYTECODE':'1'}
 (R/'invocation.json').write_text(json.dumps({'argv':argv,'env_exact':env,'wrapper_sha256':h(Path(__file__)),'consumer_sha256':h(B/'e33_consumer_v3.py'),'candidate_sha256':h(candidate) if candidate else None},indent=2)+'\n')
 started=time.monotonic()
 p=subprocess.run(argv,env=env,capture_output=True,timeout=90)
 (R/'stdout').write_bytes(p.stdout);(R/'stderr').write_bytes(p.stderr)
 stop=None;anticipated_diagnostic=False
 if p.returncode!=0:stop='unexpected consumer nonzero status'
 elif p.stderr:stop='consumer CLI diagnostic'
 elif not (run/'result.json').is_file():stop='missing fresh observer result'
 else:
  raw=json.loads((run/'result.json').read_text())
  if raw['exit_code']!=0 or raw['controller_failure'] or raw['stop_reason'] or raw['remaining_group_after_parent_wait']:stop='observer/controller issue'
  elif (run/'stdout').stat().st_size:stop='new observer stdout diagnostic'
  elif (run/'stderr').stat().st_size:
   anticipated_diagnostic=known_internal_warning((run/'stderr').read_bytes(),profile)
   if not anticipated_diagnostic:stop='new observer/compiler diagnostic: stop before extension'
 if output_bytes()>=268435456:stop='stage output budget'
 result={'job':name,'mode':mode,'profile':profile,'consumer_exit':p.returncode,'seconds':time.monotonic()-started,'stop':stop,'anticipated_internal_features_warning':anticipated_diagnostic,'stdout_sha256':h(R/'stdout'),'stderr_sha256':h(R/'stderr'),'fresh_reference_sha256':h(run/'reference.json') if (run/'reference.json').is_file() else None,'fresh_observer_result':json.loads((run/'result.json').read_text()) if (run/'result.json').is_file() else None,'CLI_json':json.loads(p.stdout) if p.stdout else None,'additional_output_bytes':output_bytes()}
 (R/'result.json').write_text(json.dumps(result,indent=2)+'\n')
 if stop:(S/'STOP.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))
 return 70 if stop else 0
if __name__=='__main__':
 if len(sys.argv)!=2 or sys.argv[1] not in JOBS:raise SystemExit('one fixed job ID required')
 raise SystemExit(job(sys.argv[1]))
