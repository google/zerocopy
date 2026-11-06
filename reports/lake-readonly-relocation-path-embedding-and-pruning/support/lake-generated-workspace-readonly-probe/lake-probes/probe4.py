from pathlib import Path
import os,subprocess,json,hashlib,shutil,time
R=Path('$CHECKOUT/.anneal-local-tools/scratch/lake-probes');B=Path('$CHECKOUT/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin');rec=json.loads((R/'runs.json').read_text());e=os.environ.copy();e.update({'ELAN_TOOLCHAIN':'leanprover/lean4:v4.30.0-rc2','PATH':str(B)+':'+e.get('PATH',''),'LAKE_CACHE_DIR':str(R/'system-cache'),'LAKE_ARTIFACT_CACHE':'false','LEAN_NUM_THREADS':'1','LAKE_JOBS':'1'})
def run(n,c,a):
 t=time.monotonic();p=subprocess.run([str(B/'lake'),*a],cwd=c,env=e,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,timeout=30);x={'name':n,'cwd':str(c),'argv':[str(B/'lake'),*a],'environment':{k:e.get(k) for k in ['ELAN_TOOLCHAIN','LAKE_CACHE_DIR','LAKE_ARTIFACT_CACHE','LEAN_NUM_THREADS','LAKE_JOBS']},'exit':p.returncode,'seconds':round(time.monotonic()-t,3),'stdout':p.stdout[-8000:],'stderr':p.stderr[-8000:]};rec.append(x);(R/'runs.json').write_text(json.dumps(rec,indent=2)+'\n');print(n,p.returncode,x['seconds'],(p.stdout+p.stderr)[-350:].replace('\n',' | '),flush=True)
def th(p):
 h=hashlib.sha256()
 for f in sorted(x for x in p.rglob('*') if x.is_file()):h.update(str(f.relative_to(p)).encode());h.update(hashlib.sha256(f.read_bytes()).digest())
 return h.hexdigest()
f=R/'layout-f';shutil.copytree(R/'layout-a/producer',f/'producer');p=f/'producer';run('producer-only-relocation-prime',p,['--keep-toolchain','--no-cache','--old','build','Dep'])
for x in sorted(p.rglob('*'),reverse=True):
 if not x.is_symlink():x.chmod(0o555 if x.is_dir() else 0o444)
p.chmod(0o555);before=th(p)
c=f/'consumer';c.mkdir();(c/'lean-toolchain').write_text('leanprover/lean4:v4.30.0-rc2\n');(c/'lakefile.lean').write_text('import Lake\nopen Lake DSL\nrequire probe_dep from "../producer"\npackage probe_consumer\n@[default_target]\nlean_lib Generated\n');(c/'Generated.lean').write_text('import Dep\n#eval depValue\n')
run('fresh-consumer-primed-dep-no-build',c,['--keep-toolchain','--no-cache','--old','--no-build','build','Dep'])
run('fresh-consumer-primed-dep-build',c,['--keep-toolchain','--no-cache','--old','build','Generated'])
run('fresh-consumer-primed-dep-server',c,['--keep-toolchain','--no-cache','setup-file','Generated.lean'])
print('treehash_before_after',before,th(p),flush=True)
