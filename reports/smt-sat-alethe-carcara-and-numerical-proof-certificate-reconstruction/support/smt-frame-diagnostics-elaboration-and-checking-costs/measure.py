"""Small exact-verdict consumer; neither elaboration nor process zero grants proof authority."""
from pathlib import Path
import subprocess,json,time,hashlib,sys

def proof_payload(status, raw):
    if status!=0 or not raw.startswith(b'valid\n') or len(raw)==6:
        raise ValueError('not a complete valid elaboration')
    return raw[6:]

p=Path(__file__).resolve().parent;binary=Path(sys.argv[1]).resolve();cvc=Path(sys.argv[2]).resolve();out=Path(sys.argv[3]).resolve();out.mkdir(exist_ok=False)
proof=p/'frame-not-equality.alethe';problem=p/'frame-not-equality.smt2';rows=[]
# Regression for the actual first-attempt parser failure: verdict-prefixed output must be split.
raw=(p/'elaborated0.alethe').read_bytes();assert proof_payload(0,raw).startswith(b'(assume')
for status,raw in [(0,b'holey\n'),(1,b'valid\n(proof)'),(0,b'valid\n'),(0,b'unknown\n(proof)')]:
    try:proof_payload(status,raw)
    except ValueError:pass
    else:raise RuntimeError('verdict admission failed')
for i in range(3):
 for name,args,want in [('generate',[str(cvc),'--proof-format-mode=alethe','--proof-granularity=theory-rewrite',str(problem)],b'unsat\n'),('check',[str(binary),'--no-color','check',str(proof),str(problem)],b'valid\n'),('elaborate',[str(binary),'--no-color','elaborate',str(proof),str(problem)],b'valid\n')]:
  start=time.monotonic_ns();r=subprocess.run(args,capture_output=True,timeout=20);ns=time.monotonic_ns()-start
  (out/(name+str(i)+'.stdout')).write_bytes(r.stdout);(out/(name+str(i)+'.stderr')).write_bytes(r.stderr)
  rows.append({'phase':name,'sample':i,'exit':r.returncode,'elapsed_ns':ns,'stdout_bytes':len(r.stdout)})
  if r.returncode or not r.stdout.startswith(want):raise RuntimeError(rows[-1])
  if name=='elaborate':
   elaborated=out/('elaborated'+str(i)+'.alethe');elaborated.write_bytes(proof_payload(r.returncode,r.stdout))
   start=time.monotonic_ns();r=subprocess.run([str(binary),'--no-color','check','--check-granularity','elaborated',str(elaborated),str(problem)],capture_output=True,timeout=20)
   rows.append({'phase':'recheck-elaborated','sample':i,'exit':r.returncode,'elapsed_ns':time.monotonic_ns()-start,'stdout_bytes':len(r.stdout)})
   (out/('recheck'+str(i)+'.stdout')).write_bytes(r.stdout);(out/('recheck'+str(i)+'.stderr')).write_bytes(r.stderr)
   if r.returncode or r.stdout!=b'valid\n':raise RuntimeError(rows[-1])
mutant=out/'wrong-rule.alethe';mutant.write_text(proof.read_text().replace(':rule arrays_row',':rule refl'))
r=subprocess.run([str(binary),'--no-color','check',str(mutant),str(problem)],capture_output=True,timeout=20)
(out/'wrong-rule.stdout').write_bytes(r.stdout);(out/'wrong-rule.stderr').write_bytes(r.stderr)
if r.returncode==0 or r.stdout!=b'invalid\n':raise RuntimeError('semantic mutant accepted')
(out/'measurements.json').write_text(json.dumps({'samples':rows,'semantic_mutant_exit':r.returncode,'proof_bytes':proof.stat().st_size,'elaborated_bytes':(out/'elaborated0.alethe').stat().st_size,'cvc5_sha256':hashlib.sha256(cvc.read_bytes()).hexdigest(),'carcara_sha256':hashlib.sha256(binary.read_bytes()).hexdigest(),'scope':'Three process-start-inclusive samples, one small array obligation, uncontrolled caches/load. Elaborator and checker share implementation.'},indent=2)+'\n')
print(json.dumps({'runs':len(rows),'all_valid':True,'semantic_mutant_rejected':True,'proof_bytes':proof.stat().st_size,'elaborated_bytes':(out/'elaborated0.alethe').stat().st_size}))
