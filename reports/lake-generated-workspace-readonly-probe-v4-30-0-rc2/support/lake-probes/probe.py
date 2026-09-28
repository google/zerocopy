from pathlib import Path
import os, subprocess, json, hashlib, shutil, stat, time
ROOT=Path('$CHECKOUT/.anneal-local-tools/scratch/lake-probes')
TC='leanprover/lean4:v4.30.0-rc2'
BIN=Path('$CHECKOUT/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin')
base=os.environ.copy(); base['ELAN_TOOLCHAIN']=TC; base['PATH']=str(BIN)+':'+base.get('PATH',''); base['LAKE_CACHE_DIR']=str(ROOT/'system-cache'); base['LAKE_ARTIFACT_CACHE']='false'; base['LEAN_NUM_THREADS']='1'; base['LAKE_JOBS']='1'
records=[]
def run(name,cwd,args,env=None):
    e=base.copy(); e.update(env or {})
    t=time.monotonic()
    try:
        p=subprocess.run([str(BIN/'lake'),*args],cwd=cwd,env=e,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=30)
        rec={'name':name,'cwd':str(cwd),'argv':[str(BIN/'lake'),*args],'environment':{k:e.get(k) for k in ['ELAN_TOOLCHAIN','LAKE_CACHE_DIR','LAKE_ARTIFACT_CACHE','LEAN_NUM_THREADS','LAKE_JOBS']},'exit':p.returncode,'seconds':round(time.monotonic()-t,3),'stdout':p.stdout[-8000:],'stderr':p.stderr[-8000:]}
    except subprocess.TimeoutExpired as ex:
        rec={'name':name,'cwd':str(cwd),'argv':[str(BIN/'lake'),*args],'timeout':30,'seconds':round(time.monotonic()-t,3),'stdout':str(ex.stdout)[-8000:],'stderr':str(ex.stderr)[-8000:]}
    records.append(rec); (ROOT/'runs.json').write_text(json.dumps(records,indent=2)+'\n')
    print(name,rec.get('exit','TIMEOUT'),rec['seconds'],(rec.get('stdout','')+' '+rec.get('stderr',''))[-400:].replace('\n',' | '),flush=True)
    return rec

def write(path,s):
    path.parent.mkdir(parents=True,exist_ok=True); path.write_text(s)
def hash(path): return hashlib.sha256(path.read_bytes()).hexdigest() if path.exists() else None
layout=ROOT/'layout-a'; prod=layout/'producer'; cons=layout/'consumer'; prod.mkdir(parents=True,exist_ok=True); cons.mkdir(parents=True,exist_ok=True)
write(prod/'lean-toolchain',TC+'\n')
write(prod/'lakefile.lean','import Lake\nopen Lake DSL\npackage probe_dep\n@[default_target]\nlean_lib Dep\n')
write(prod/'Dep.lean','def depValue : Nat := 7\n')
write(cons/'lean-toolchain',TC+'\n')
write(cons/'lakefile.lean','import Lake\nopen Lake DSL\nrequire probe_dep from "../producer"\npackage probe_consumer\n@[default_target]\nlean_lib Generated\n')
write(cons/'Generated.lean','import Dep\n#eval depValue\n')
run('producer-build',prod,['--keep-toolchain','--no-cache','--old','build','Dep'])
run('consumer-first-build',cons,['--keep-toolchain','--no-cache','--old','build','Generated'])
print('hashes',json.dumps({'producer_olean':hash(prod/'.lake/build/lib/lean/Dep.olean'),'consumer_olean':hash(cons/'.lake/build/lib/lean/Generated.olean')}),flush=True)
