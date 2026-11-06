from pathlib import Path
import sys,json,hashlib,shutil,subprocess,os,time,resource
s=json.load(sys.stdin);p=Path('/home/opam/anneal-sail-output/controls-parent-1');p.mkdir();(p/'Controls.lean').write_text(s['control']);(p/'Proof.lean').write_text(s['proof'])
f=Path('/home/opam/anneal-sail-output/proof-development/check-05/Proof.olean')
if hashlib.sha256(f.read_bytes()).hexdigest()!='a37ef2b0d8f2ed3613a85ae666e89771464e2453df0929f9f80fb44397faa3bf':raise SystemExit('STOP accepted proof import changed')
shutil.copyfile(f,p/'Proof.olean');env=os.environ.copy();env['LEAN_PATH']='/home/opam/anneal-sail-output/serial-build-integration/olean:'+str(p)
argv=['timeout','--signal=TERM','--kill-after=5','120','/home/opam/anneal-sail-tools/lean-4.29.0-linux_aarch64/bin/lean','-j1','-M4500','--tstack=400000','-t0','-R',str(p),'-o',str(p/'Controls.olean'),str(p/'Controls.lean')];t=time.monotonic()
with (p/'controls.stdout').open('xb') as so,(p/'controls.stderr').open('xb') as se:r=subprocess.run(argv,cwd=p,env=env,stdout=so,stderr=se)
u=resource.getrusage(resource.RUSAGE_CHILDREN);row={'status':r.returncode,'seconds':time.monotonic()-t,'maxrss_kib':u.ru_maxrss,'argv':argv,'lean_path':env['LEAN_PATH'],'files':{}}
for name in ['Controls.lean','Controls.olean','Proof.lean','Proof.olean','controls.stdout','controls.stderr']:
 f=p/name
 if f.exists():
  b=f.read_bytes();row['files'][name]={'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
(p/'controls-result.json').write_text(json.dumps(row,indent=2)+'\n');print(json.dumps({'result':row,'stdout':(p/'controls.stdout').read_text(),'stderr':(p/'controls.stderr').read_text()},indent=2))
