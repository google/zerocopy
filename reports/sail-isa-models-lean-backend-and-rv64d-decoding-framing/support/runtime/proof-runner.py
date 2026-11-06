from pathlib import Path
import subprocess,sys,json,time,resource,hashlib,os
s=json.load(sys.stdin);root=Path(s['root']);env=os.environ.copy();env['LEAN_PATH']='/home/opam/anneal-sail-output/serial-build-integration/olean:'+str(root);t=time.monotonic()
with (root/'proof.stdout').open('xb') as so,(root/'proof.stderr').open('xb') as se:r=subprocess.run(s['argv'],cwd=root,env=env,stdout=so,stderr=se)
u=resource.getrusage(resource.RUSAGE_CHILDREN);row={'status':r.returncode,'seconds':time.monotonic()-t,'child_maxrss_kib':u.ru_maxrss,'child_user_seconds':u.ru_utime,'child_system_seconds':u.ru_stime,'argv':s['argv'],'lean_path':env['LEAN_PATH']}
for name in ['proof.stdout','proof.stderr','Proof.lean','Proof.olean']:
 p=root/name
 if p.exists():
  b=p.read_bytes();row[name]={'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
(root/'proof-result.json').write_text(json.dumps(row,indent=2)+'\n');print(json.dumps(row),flush=True)
