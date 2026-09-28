from pathlib import Path
import os,subprocess,json,hashlib,time
R=Path('$CHECKOUT/.anneal-local-tools/scratch/lake-probes'); B=Path('$CHECKOUT/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin')
records=json.loads((R/'runs.json').read_text());e=os.environ.copy();e.update({'ELAN_TOOLCHAIN':'leanprover/lean4:v4.30.0-rc2','PATH':str(B)+':'+e.get('PATH',''),'LAKE_CACHE_DIR':str(R/'system-cache'),'LAKE_ARTIFACT_CACHE':'false','LEAN_NUM_THREADS':'1','LAKE_JOBS':'1'})
def run(name,cwd,args):
 t=time.monotonic()
 try:
  p=subprocess.run([str(B/'lake'),*args],cwd=cwd,env=e,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,timeout=30)
  rec={'name':name,'cwd':str(cwd),'argv':[str(B/'lake'),*args],'environment':{k:e.get(k) for k in ['ELAN_TOOLCHAIN','LAKE_CACHE_DIR','LAKE_ARTIFACT_CACHE','LEAN_NUM_THREADS','LAKE_JOBS']},'exit':p.returncode,'seconds':round(time.monotonic()-t,3),'stdout':p.stdout[-8000:],'stderr':p.stderr[-8000:]}
 except subprocess.TimeoutExpired as x:rec={'name':name,'cwd':str(cwd),'argv':[str(B/'lake'),*args],'timeout':30,'seconds':round(time.monotonic()-t,3),'stdout':str(x.stdout)[-8000:],'stderr':str(x.stderr)[-8000:]}
 records.append(rec);(R/'runs.json').write_text(json.dumps(records,indent=2)+'\n');print(name,rec.get('exit','TIMEOUT'),rec['seconds'],(rec.get('stdout','')+' '+rec.get('stderr',''))[-500:].replace('\n',' | '),flush=True)
def treehash(p):
 h=hashlib.sha256()
 for f in sorted(x for x in p.rglob('*') if x.is_file()):h.update(str(f.relative_to(p)).encode());h.update(hashlib.sha256(f.read_bytes()).digest())
 return h.hexdigest()
p=R/'layout-b/producer';c=R/'layout-b/consumer'
for f in p.rglob('*'):
 if not f.is_symlink():f.chmod(0o755 if f.is_dir() else 0o644)
p.chmod(0o755)
run('relocated-writable-primer',c,['--keep-toolchain','--no-cache','--old','build','Generated'])
run('relocated-writable-server',c,['--keep-toolchain','--no-cache','setup-file','Generated.lean'])
for f in sorted(p.rglob('*'),reverse=True):
 if not f.is_symlink():f.chmod(0o555 if f.is_dir() else 0o444)
p.chmod(0o555)
before=treehash(p)
run('primed-readonly-no-build',c,['--keep-toolchain','--no-cache','--old','--no-build','build','Generated'])
run('primed-readonly-server',c,['--keep-toolchain','--no-cache','setup-file','Generated.lean'])
run('primed-readonly-lean-json',c,['--keep-toolchain','--no-cache','env','lean','--json','Generated.lean'])
run('primed-readonly-offline-build',c,['--keep-toolchain','--offline','--no-cache','--old','build','Generated'])
print(json.dumps({'producer_before':before,'producer_after':treehash(p),'consumer_olean':hashlib.sha256((c/'.lake/build/lib/lean/Generated.olean').read_bytes()).hexdigest(),'cache_true_olean_build_path_exists':(R/'layout-c/consumer/.lake/build/lib/lean/Generated.olean').exists(),'cache_true_file_count':sum(1 for f in (R/'cache-true').rglob('*') if f.is_file())},indent=2),flush=True)
