from pathlib import Path
import sys,json,subprocess,time,resource,hashlib
s=json.load(sys.stdin);root=Path(s['output_root']);run=root/'run';run.mkdir()
(root/'run'/'generation-spec.json').write_text(json.dumps(s,indent=2)+'\n')
t=time.monotonic()
with (run/'generation.stdout').open('xb') as so,(run/'generation.stderr').open('xb') as se:
 r=subprocess.run(s['argv'],cwd=s['cwd'],stdout=so,stderr=se)
u=resource.getrusage(resource.RUSAGE_CHILDREN)
row={'status':r.returncode,'seconds':time.monotonic()-t,'child_user_seconds':u.ru_utime,'child_system_seconds':u.ru_stime,'child_maxrss_kib':u.ru_maxrss,'argv':s['argv'],'cwd':s['cwd']}
for n in ['stdout','stderr']:
 b=(run/('generation.'+n)).read_bytes();row[n]={'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
(run/'generation-result.json').write_text(json.dumps(row,indent=2)+'\n');print(json.dumps(row),flush=True)
