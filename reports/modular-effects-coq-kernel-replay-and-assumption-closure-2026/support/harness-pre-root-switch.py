#!/usr/bin/env python3
"""Host controller: assigned container only; logs confined to this directory."""
from pathlib import Path
import subprocess,json,sys,time,hashlib
R=Path(__file__).resolve().parent
LOG=R/'logs'; LOG.mkdir(exist_ok=True)
NAME='anneal-formal-experiments-20261014'
CWD='/home/opam/anneal-itree/iris-itree'
PREFIX='/home/opam/.opam/4.14'
ENV=['--env','PATH='+PREFIX+'/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin','--env','OPAMROOT=/home/opam/.opam','--env','OPAM_SWITCH_PREFIX='+PREFIX]

def run(label,argv,timeout=120,input_bytes=None):
    t=time.monotonic()
    try:
        p=subprocess.run(argv,input=input_bytes,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=timeout)
        code=p.returncode; out=p.stdout; err=p.stderr; status='finished'
    except subprocess.TimeoutExpired as e:
        code=None; out=e.stdout or b''; err=e.stderr or b''; status='host-controller-timeout'
    (LOG/(label+'.stdout')).write_bytes(out)
    (LOG/(label+'.stderr')).write_bytes(err)
    rec={'label':label,'argv':argv,'status':status,'exit_code':code,'elapsed_seconds':round(time.monotonic()-t,3),'stdout_bytes':len(out),'stderr_bytes':len(err),'stdout_sha256':hashlib.sha256(out).hexdigest(),'stderr_sha256':hashlib.sha256(err).hexdigest()}
    (LOG/(label+'.json')).write_text(json.dumps(rec,indent=2)+'\n')
    print(json.dumps(rec),flush=True)
    if code!=0: sys.exit(1)

def ex(args): return ['docker','exec','--user','opam','--workdir',CWD]+ENV+[NAME]+args

if sys.argv[1]=='preflight-shell':
    run('identity-coqc',ex(['coqc','--version']))
    run('identity-coqwhere',ex(['coqc','-where']))
    run('identity-ocaml',ex(['ocamlc','-version']))
    run('identity-coqcore',ex(['ocamlfind','query','coq-core']))
    run('coqchk-help',ex(['coqchk','--help']))
elif sys.argv[1]=='preflight-rest':
    run('identity-tools',ex(['/bin/sh','-c','for n in coqc coqchk coq_makefile coqdep ocamlc timeout du sha256sum find setsid ps awk stat; do command -v "$n"; done']))
    run('tool-hashes',ex(['/bin/sh','-c','for n in coqc coqchk coq_makefile coqdep ocamlc; do sha256sum "$(command -v "$n")"; done']))
    x=json.loads((R/'source-identity-proposal.json').read_text())
    manifest=''.join(v['sha256']+'  /home/opam/anneal-itree/'+v['path']+'\n' for v in x['file_manifest']).encode()
    (R/'source-check-input.sha256').write_bytes(manifest)
    argv=['docker','exec','-i','--user','opam',NAME,'sha256sum','--check','--strict']
    run('exact-source-check',argv,input_bytes=manifest)
    run('prebuild-objects',ex(['find','.','-type','f','-name','*.vo']))
elif sys.argv[1]=='copy':
    for f in ['AuditCore.v','AuditHeapLang.v','AuditIslaris.v']:
        run('copy-'+f,['docker','cp',str(R/f),NAME+':'+CWD+'/'+f])
    run('copied-audits',ex(['sha256sum','AuditCore.v','AuditHeapLang.v','AuditIslaris.v']))
elif sys.argv[1]=='phase':
    label=sys.argv[2]; seconds=int(sys.argv[3]); command=sys.argv[4:]
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
 if [ "$peak" -gt 1074516112 ]; then
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
printf 'ANNEAL_PHASE_RESULT returncode=%s stop=%s elapsed_seconds=%s start_bytes=%s peak_bytes=%s final_bytes=%s\n' "$result" "$stop" "$((end-begin))" "$start" "$peak" "$final"
exit "$result"
'''
    run(label,ex(['/bin/sh','-c',wrapper,'anneal-phase',str(seconds)]+command),seconds+30)
elif sys.argv[1]=='inventory':
    run('post-hashes',ex(['find','.','-type','f','-exec','sha256sum','{}','+']))
    run('post-sizes',ex(['find','.','-type','f','-printf','%s %p\n']))
else:raise SystemExit('unknown action')
