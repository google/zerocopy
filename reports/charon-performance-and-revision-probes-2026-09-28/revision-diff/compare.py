#!/usr/bin/env python3
import hashlib, json, os, pathlib, subprocess, time
ROOT=pathlib.Path(__file__).resolve().parent
REPO=pathlib.Path('/Users/josh/Codex/Projects/zerocopy')
TOOLS=REPO/'.anneal-local-tools'
SOURCE=REPO/'.anneal-local-tools/scratch/20260927-reference-experiments/aeneas_charon/cases/baseline/baseline.rs'
OLD=ROOT/'old'
BASE={**os.environ,'CHARON_TOOLCHAIN_IS_IN_PATH':'1','CARGO_BUILD_JOBS':'1','RAYON_NUM_THREADS':'1','CARGO_INCREMENTAL':'0'}
VERSIONS={'nightly-2026.06.02':ROOT/'old', 'nightly-2026.06.03':TOOLS/'bin'}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
records={'source':{'path':str(SOURCE),'bytes':SOURCE.stat().st_size,'sha256':sha(SOURCE)},'runs':{}}
for tag,bindir in VERSIONS.items():
 env=BASE.copy(); tc='nightly-2026-05-31'; env['RUSTUP_TOOLCHAIN']=tc
 env['PATH']=str(bindir)+os.pathsep+str(TOOLS/'cargo/bin')+os.pathsep+str(TOOLS/'elan/bin')+os.pathsep+env['PATH']
 troot=TOOLS/f'rustup/toolchains/{tc}-aarch64-apple-darwin'
 env['DYLD_LIBRARY_PATH']=str(troot/'lib')+os.pathsep+str(troot/'lib/rustlib/aarch64-apple-darwin/lib')+os.pathsep+env.get('DYLD_LIBRARY_PATH','')
 out=ROOT/tag
 out.mkdir(exist_ok=True)
 dest=out/'baseline.llbc'
 argv=['charon','rustc','--preset','aeneas','--dest-file',str(dest),'--',str(SOURCE),'--crate-type','lib','--crate-name','baseline','--edition','2021']
 started=time.monotonic(); proc=subprocess.run(argv,cwd=ROOT,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=45)
 (out/'stdout.txt').write_bytes(proc.stdout); (out/'stderr.txt').write_bytes(proc.stderr)
 record={'argv':argv,'cwd':str(ROOT),'exit':proc.returncode,'wall_seconds':round(time.monotonic()-started,3),'binary':str(bindir/'charon'),'binary_sha256':sha(bindir/'charon'),'driver':str(bindir/'charon-driver'),'driver_sha256':sha(bindir/'charon-driver'),'stdout_sha256':hashlib.sha256(proc.stdout).hexdigest(),'stderr_sha256':hashlib.sha256(proc.stderr).hexdigest()}
 if dest.exists():
  x=json.loads(dest.read_text()); t=x['translated']; record.update(llbc_bytes=dest.stat().st_size,llbc_sha256=sha(dest),has_errors=x['has_errors'],ordered_decls=len(t['ordered_decls']),local_functions=len(t['fun_decls']))
 else: record['llbc_missing']=True
 records['runs'][tag]=record
 (ROOT/'comparison.json').write_text(json.dumps(records,indent=2)+'\n')
 if proc.returncode: raise SystemExit(f'{tag} failed; see {out}/stderr.txt')
print(json.dumps(records,indent=2))
