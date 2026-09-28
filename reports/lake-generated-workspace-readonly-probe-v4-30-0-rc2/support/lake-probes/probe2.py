from pathlib import Path
import os, subprocess, json, hashlib, shutil, time, stat
ROOT=Path('$CHECKOUT/.anneal-local-tools/scratch/lake-probes')
BIN=Path('$CHECKOUT/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin')
TC='leanprover/lean4:v4.30.0-rc2'
records=json.loads((ROOT/'runs.json').read_text())
base=os.environ.copy();base.update({'ELAN_TOOLCHAIN':TC,'PATH':str(BIN)+':'+base.get('PATH',''),'LAKE_CACHE_DIR':str(ROOT/'system-cache'),'LAKE_ARTIFACT_CACHE':'false','LEAN_NUM_THREADS':'1','LAKE_JOBS':'1'})
def run(name,cwd,args,env=None):
 e=base.copy();e.update(env or {});t=time.monotonic()
 try:
  p=subprocess.run([str(BIN/'lake'),*args],cwd=cwd,env=e,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=30)
  rec={'name':name,'cwd':str(cwd),'argv':[str(BIN/'lake'),*args],'environment':{k:e.get(k) for k in ['ELAN_TOOLCHAIN','LAKE_CACHE_DIR','LAKE_ARTIFACT_CACHE','LEAN_NUM_THREADS','LAKE_JOBS']},'exit':p.returncode,'seconds':round(time.monotonic()-t,3),'stdout':p.stdout[-8000:],'stderr':p.stderr[-8000:]}
 except subprocess.TimeoutExpired as ex: rec={'name':name,'cwd':str(cwd),'argv':[str(BIN/'lake'),*args],'timeout':30,'seconds':round(time.monotonic()-t,3),'stdout':str(ex.stdout)[-8000:],'stderr':str(ex.stderr)[-8000:]}
 records.append(rec);(ROOT/'runs.json').write_text(json.dumps(records,indent=2)+'\n');print(name,rec.get('exit','TIMEOUT'),rec['seconds'],(rec.get('stdout','')+' '+rec.get('stderr',''))[-400:].replace('\n',' | '),flush=True)
def hash(p):return hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else None
def treehash(p):
 h=hashlib.sha256()
 for f in sorted(x for x in p.rglob('*') if x.is_file()):h.update(str(f.relative_to(p)).encode());h.update(hashlib.sha256(f.read_bytes()).digest())
 return h.hexdigest()
def write_cons(path):
 path.mkdir(parents=True,exist_ok=True)
 (path/'lean-toolchain').write_text(TC+'\n')
 (path/'lakefile.lean').write_text('import Lake\nopen Lake DSL\nrequire probe_dep from "../producer"\npackage probe_consumer\n@[default_target]\nlean_lib Generated\n')
 (path/'Generated.lean').write_text('import Dep\n#eval depValue\n')
layout=ROOT/'layout-b';shutil.copytree(ROOT/'layout-a/producer',layout/'producer');prod=layout/'producer'
for p in sorted(prod.rglob('*'),reverse=True):
 if not p.is_symlink():p.chmod(0o555 if p.is_dir() else 0o444)
prod.chmod(0o555)
before=treehash(prod)
cons=layout/'consumer';write_cons(cons)
run('relocated-readonly-no-build',cons,['--keep-toolchain','--no-cache','--old','--no-build','build','Dep'])
run('relocated-readonly-build',cons,['--keep-toolchain','--no-cache','--old','build','Generated'])
run('server-setup-file',cons,['--keep-toolchain','--no-cache','setup-file','Generated.lean'])
run('consumer-repeat-no-build',cons,['--keep-toolchain','--no-cache','--old','--no-build','build','Generated'])
run('consumer-lean-json',cons,['--keep-toolchain','--no-cache','env','lean','--json','Generated.lean'])
layoutc=ROOT/'layout-c';shutil.copytree(ROOT/'layout-a/producer',layoutc/'producer');consc=layoutc/'consumer';write_cons(consc)
run('cache-true-build',consc,['--keep-toolchain','--no-cache','--old','build','Generated'],{'LAKE_ARTIFACT_CACHE':'true','LAKE_CACHE_DIR':str(ROOT/'cache-true')})
layoutd=ROOT/'layout-d';shutil.copytree(ROOT/'layout-a/producer',layoutd/'producer');consd=layoutd/'consumer';write_cons(consd)
run('empty-cache-dir-build',consd,['--keep-toolchain','--no-cache','--old','build','Generated'],{'LAKE_CACHE_DIR':''})
# A source-only dependency checks whether the producer build state matters for --no-build.
layoute=ROOT/'layout-e';shutil.copytree(ROOT/'layout-a/producer',layoute/'producer',ignore=shutil.ignore_patterns('.lake'));conse=layoute/'consumer';write_cons(conse)
run('source-only-no-build',conse,['--keep-toolchain','--no-cache','--old','--no-build','build','Dep'])
run('source-only-build',conse,['--keep-toolchain','--no-cache','--old','build','Generated'])
summary={'producer_before':before,'producer_after':treehash(prod),'producer_olean_a':hash(ROOT/'layout-a/producer/.lake/build/lib/lean/Dep.olean'),'producer_olean_b':hash(prod/'.lake/build/lib/lean/Dep.olean'),'consumer_oleans':{n:hash(ROOT/n/'consumer/.lake/build/lib/lean/Generated.olean') for n in ['layout-a','layout-b','layout-c','layout-d','layout-e']},'size_bytes':sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file())}
(ROOT/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2),flush=True)
