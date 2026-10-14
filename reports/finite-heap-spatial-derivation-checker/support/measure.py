#!/usr/bin/env python3
import hashlib,json,os,statistics,subprocess,time
from pathlib import Path
HERE=Path(__file__).resolve().parent
LEAN=Path(os.environ['LEAN_BINARY']).resolve()
env={**os.environ,'LEAN_PATH':str(HERE)}
statement='Join (write (meaning owned) 1 12) (meaning framed) (meaning after) ∧ Unchanged (meaning before) (meaning after) 1'
routes={'data':'step_sound good (by decide)','direct':'by constructor <;> decide'}
result={}
for name,proof in routes.items():
    source='import Heap\nopen FiniteHeap\n'+''.join('theorem probe'+str(i)+' : '+statement+' := '+proof+'\n' for i in range(100))+'#print axioms probe99\n'
    path=HERE/(name+'-cost.lean');path.write_text(source);samples=[]
    for i in range(5):
        start=time.perf_counter();r=subprocess.run([str(LEAN),path.name],cwd=HERE,env=env,capture_output=True,text=True)
        elapsed=1000*(time.perf_counter()-start);assert r.returncode==0 and 'sorryAx' not in r.stdout
        samples.append(elapsed)
    result[name]={'source_bytes':len(source.encode()),'source_sha256':hashlib.sha256(source.encode()).hexdigest(),'samples_ms':samples,'median_ms':statistics.median(samples),'stdout':r.stdout,'stderr':r.stderr}
(HERE/'matched-costs.json').write_text(json.dumps({'same_statement':statement,'repetitions_per_process':100,'fresh_process_samples':5,'included':'startup/import/elaboration/kernel checking of repeated declarations; warm filesystem; precompiled Heap import; no proof generation or Rust frontend cost','routes':result},indent=2)+'\n')
print(json.dumps(result,indent=2))
