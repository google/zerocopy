"""Assigned source tree/container only. All host writes stay beside this script."""
from pathlib import Path
import json,subprocess,time,sys,hashlib,shutil
R=Path(__file__).resolve().parent;L=R/'logs';L.mkdir(exist_ok=True)
PLAN=R.parent/'simuliris-plan';N='anneal-simuliris-20261014';C='/home/opam/anneal-simuliris-sources/simuliris'
ID='d46d5503dc34302f8be823d721b398aec61ac6028f154f8ce7654a995aa7786d'
def exe(args,stdin=False):return ['docker','exec']+(['-i'] if stdin else [])+['--workdir',C,N,'opam','exec','--switch=4.14','--']+args
def run(label,argv,seconds=60,data=None,allowed=(0,)):
 t=time.monotonic()
 out=L/(label+'.stdout');err=L/(label+'.stderr')
 with out.open('wb') as o,err.open('wb') as e:
  try:
   p=subprocess.run(argv,input=data,stdout=o,stderr=e,timeout=seconds)
   code=p.returncode;status='finished'
  except subprocess.TimeoutExpired:
   code=None;status='host timeout; stop and diagnose container process state'
 b=out.read_bytes();d=err.read_bytes();x={'label':label,'argv':argv,'exit_code':code,'status':status,'elapsed_seconds':round(time.monotonic()-t,3),'stdout_bytes':len(b),'stderr_bytes':len(d),'stdout_sha256':hashlib.sha256(b).hexdigest(),'stderr_sha256':hashlib.sha256(d).hexdigest(),'allowed_exit_codes':list(allowed)}
 (L/(label+'.json')).write_text(json.dumps(x,indent=2)+'\n');print(json.dumps({k:x[k] for k in ['label','exit_code','status','elapsed_seconds','stdout_bytes','stderr_bytes']}),flush=True)
 if code not in allowed:raise SystemExit('Stop: '+label)
 return b
act=sys.argv[1]
if act=='identity':
 b=run('container-identity',['docker','inspect','--format','{{.Id}}|{{.Name}}|{{.State.Status}}|{{.HostConfig.Memory}}|{{.HostConfig.NanoCpus}}|{{.HostConfig.PidsLimit}}|{{json .Mounts}}',N])
 if b.decode().strip().split('|')!=[ID,'/'+N,'running','3221225472','2000000000','512','[]']:raise SystemExit('Container identity mismatch')
 for label,args,codes in [('rocq-version',['rocq','--version'],(0,)),('rocqchk-version',['rocqchk','--version'],(0,)),('ocaml-version',['ocamlc','-version'],(0,)),('dune-version',['dune','--version'],(0,)),('rocq-help',['rocq','--help'],(0,1)),('checker-help',['rocq','check','--help'],(0,1))]:run(label,exe(args),allowed=codes)
 run('tool-identities',exe(['/bin/sh','-c','for n in rocq rocqchk rocqtop rocqc rocqmakefile rocqdep coqc coqchk ocamlc dune; do p=$(command -v "$n") || continue; printf "%s %s\\n" "$n" "$p"; sha256sum "$p"; done']))
 run('installed-switch-state',exe(['cat','/home/opam/.opam/4.14/.opam-switch/switch-state']))
 run('original-project-flags',exe(['cat','_RocqProject']))
 run('source-directory-identity',exe(['/bin/sh','-c','id; stat -c "%u %g %a %n" .; du -sb .']))
 inv=json.loads((PLAN/'archive-inventory.json').read_text());prefix='simuliris-e3abfcdc301f92250d4227fc03c00463bf57b982/'
 data=''.join(x['sha256']+'  '+C+'/'+x['path'][len(prefix):]+'\n' for x in inv['files']).encode();(R/'source-check-input.sha256').write_bytes(data)
 run('initial-source-check',exe(['sha256sum','--check','--strict'],True),data=data)
 run('initial-proof-absence',exe(['/bin/sh','-c',"find . -type f \\( -name '*.vo' -o -name '*.vos' -o -name '*.vok' -o -name '*.vio' \\) -print"]))
elif act=='copy-audits':
 for name in ['PlannedAuditFramework.v','PlannedAuditResources.v','PlannedAuditExamples.v']:
  shutil.copyfile(PLAN/name,R/name)
  run('copy-'+name,['docker','cp',str(R/name),N+':'+C+'/'+name])
 run('copied-audit-hashes',exe(['sha256sum','PlannedAuditFramework.v','PlannedAuditResources.v','PlannedAuditExamples.v']))
elif act=='phase':
 label=sys.argv[2];cap=int(sys.argv[3]);command=sys.argv[4:]
 wrapper='''limit=$1
shift
start=$(du -sb . | cut -f1)
peak=$start
stop=none
begin=$(date +%s)
timeout --signal=TERM --kill-after=5 "$limit" "$@" &
pid=$!
while kill -0 "$pid" 2>/dev/null; do
 size=$(du -sb . | cut -f1)
 if [ "$size" -gt "$peak" ]; then peak=$size; fi
 if [ "$peak" -gt 1076927915 ]; then
  stop=disk-cap
  kill -TERM "$pid"
  break
 fi
 sleep 2
done
wait "$pid"
result=$?
end=$(date +%s)
final=$(du -sb . | cut -f1)
printf 'ANNEAL_PHASE_RESULT returncode=%s stop=%s elapsed_seconds=%s start_bytes=%s peak_bytes=%s final_bytes=%s\\n' "$result" "$stop" "$((end-begin))" "$start" "$peak" "$final"
exit "$result"
'''
 run(label,exe(['/bin/sh','-c',wrapper,'anneal-phase',str(cap)]+command),seconds=cap+30)
elif act=='source-final':run('final-source-check',exe(['sha256sum','--check','--strict'],True),data=(R/'source-check-input.sha256').read_bytes())
elif act=='inventory':
 run('final-file-hashes',exe(['find','.','-type','f','-exec','sha256sum','{}','+']))
 run('final-file-sizes',exe(['find','.','-type','f','-printf','%s %p\n']))
else:raise SystemExit('Unknown action')
