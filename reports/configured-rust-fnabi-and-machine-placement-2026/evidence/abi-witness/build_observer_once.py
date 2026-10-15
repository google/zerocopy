"""Authorized observer build only. Never launches the built observer or fixtures."""
from pathlib import Path
import hashlib,json,os,signal,subprocess,time
B=Path(__file__).resolve().parent
T=B.parent/'toolchains/rustup/toolchains/nightly-2026-05-01-aarch64-apple-darwin'
R=B/'build-01'
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert B.resolve()==B and not B.is_symlink()
assert h(B/'prepared-manifest.json')=='f43a6306944d5ee5c2e1984f1bafd20fe95706e6217e0c6c3ec1640547ca26b8'
manifest=json.loads((B/'prepared-manifest.json').read_text())
for f in manifest['files']:
 p=B/f['path'];assert p.is_file() and not p.is_symlink() and p.stat().st_size==f['bytes'] and h(p)==f['sha256']
ident=json.loads((B/'source-identities.json').read_text())
def tools():
 result=[]
 for f in ident['readonly_tools']:
  p=T/f['toolchain_relative_path'];digest=h(p);assert p.stat().st_size==f['bytes'] and digest==f['sha256'];result.append(dict(f))
 return result
before=tools();source_before=h(B/'proposed_observer.rs')
assert not R.exists() and not (B/'observer').exists()
R.mkdir();(R/'tmp').mkdir()
argv=[x.replace('${TOOLCHAIN}',str(T)).replace('${E33_ROOT}',str(B)) for x in json.loads((B/'commands.json').read_text())['commands'][0]['argv']]
env={'PATH':'/usr/bin:/bin:/usr/sbin:/sbin','TMPDIR':str(R/'tmp'),'LC_ALL':'C','LANG':'C'}
(R/'invocation.json').write_text(json.dumps({'argv':argv,'cwd':str(B),'env_exact':env,'source_sha256':source_before,'tools_before':before,'harness_sha256':h(Path(__file__))},indent=2)+'\n')
def output_bytes():
 return sum(p.stat().st_size for p in R.rglob('*') if p.is_file())+((B/'observer').stat().st_size if (B/'observer').is_file() else 0)
started=time.monotonic();samples=[];stop=None
with (R/'stdout').open('xb') as out,(R/'stderr').open('xb') as err:
 p=subprocess.Popen(argv,cwd=B,env=env,stdout=out,stderr=err,start_new_session=True)
 while p.poll() is None:
  rows=subprocess.run(['/bin/ps','-axo','pid=,ppid=,rss='],capture_output=True,check=True,text=True).stdout.splitlines()
  nodes={}
  for row in rows:
   cols=row.split()
   if len(cols)==3:nodes[int(cols[0])]=(int(cols[1]),int(cols[2])*1024)
  wanted={p.pid};old=set()
  while old!=wanted:
   old=set(wanted);wanted|={pid for pid,(parent,rss) in nodes.items() if parent in wanted}
  rss=sum(nodes[pid][1] for pid in wanted if pid in nodes)
  elapsed=time.monotonic()-started;size=output_bytes()
  samples.append({'seconds':elapsed,'rss_tree_bytes':rss,'pids':sorted(pid for pid in wanted if pid in nodes),'output_bytes':size})
  if rss>=1073741824:stop='observed aggregate compiler-tree RSS >=1GiB'
  elif size>=134217728:stop='observed output bytes >=128MiB'
  elif elapsed>=600:stop='600-second wall limit'
  if stop:
   os.killpg(p.pid,signal.SIGTERM)
   try:p.wait(timeout=2)
   except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);p.wait()
   break
  time.sleep(0.1)
 code=p.wait()
(R/'rss-samples.json').write_text(json.dumps(samples,indent=2)+'\n')
after=tools();assert source_before==h(B/'proposed_observer.rs')
receipt={'exit_code':code,'seconds':time.monotonic()-started,'stop_reason':stop,'max_observed_tree_rss_bytes':max((x['rss_tree_bytes'] for x in samples),default=0),'monitor':'Periodic ps RSS in KiB converted to bytes, aggregate descendants; not a hard address-space cap, OS isolation, or proof of unsampled peak.','output_bytes':output_bytes(),'stdout_sha256':h(R/'stdout'),'stderr_sha256':h(R/'stderr'),'stderr_bytes':(R/'stderr').stat().st_size,'source_before_after_sha256':source_before,'tools_after':after,'observer':{'sha256':h(B/'observer'),'bytes':(B/'observer').stat().st_size} if (B/'observer').is_file() else None,'observer_or_fixture_invocations':0}
(R/'result.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
