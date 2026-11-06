#!/usr/bin/env python3
import hashlib, json, os, pathlib, resource, shutil, subprocess, time
ROOT=pathlib.Path(__file__).resolve().parent
REPO=pathlib.Path('/Users/josh/Codex/Projects/zerocopy')
TOOLS=REPO/'.anneal-local-tools'
SOURCE=REPO/'.anneal-local-tools/scratch/20260927-reference-experiments/charon_scaling/functions_1000.rs'
ENV={**os.environ,'CHARON_TOOLCHAIN_IS_IN_PATH':'1','CARGO_BUILD_JOBS':'1','RAYON_NUM_THREADS':'1','CARGO_INCREMENTAL':'0'}
ENV['DYLD_LIBRARY_PATH']=str(TOOLS/'rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/lib')+os.pathsep+str(TOOLS/'rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/lib/rustlib/aarch64-apple-darwin/lib')+os.pathsep+ENV.get('DYLD_LIBRARY_PATH','')
records=[]
for roots in (1,10,100,1000):
 dest=ROOT/f'roots-{roots}.llbc'
 argv=['charon','rustc','--preset','aeneas','--dest-file',str(dest)]
 for i in range(roots): argv += ['--start-from',f'crate::f{i:04d}']
 argv += ['--',str(SOURCE),'--crate-type','lib','--crate-name','functions_1000','--edition','2021']
 env=ENV.copy(); env['PATH']=str(TOOLS/'bin')+os.pathsep+str(TOOLS/'cargo/bin')+os.pathsep+str(TOOLS/'elan/bin')+os.pathsep+env['PATH']
 if shutil.disk_usage(ROOT).free < 5*(1<<30): raise SystemExit('disk guard <5GiB')
 t=time.monotonic(); p=subprocess.run(argv,cwd=ROOT,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=60)
 (ROOT/f'roots-{roots}.stdout').write_bytes(p.stdout); (ROOT/f'roots-{roots}.stderr').write_bytes(p.stderr)
 rec={'requested_roots':roots,'argv':argv,'exit':p.returncode,'wall_seconds':round(time.monotonic()-t,6),'child_maxrss_bytes':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,'source_bytes':SOURCE.stat().st_size,'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest()}
 if dest.exists():
  j=json.loads(dest.read_text()); tr=j['translated']; rec.update(has_errors=j['has_errors'],llbc_bytes=dest.stat().st_size,llbc_sha256=hashlib.sha256(dest.read_bytes()).hexdigest(),ordered_decls=len(tr['ordered_decls']),local_fun_decls=sum(1 for x in tr['fun_decls'] if x['item_meta'].get('is_local')))
 records.append(rec); (ROOT/'root-matrix.json').write_text(json.dumps(records,indent=2)+'\n')
 if p.returncode or not dest.exists() or rec.get('has_errors') or rec.get('local_fun_decls') != roots: raise SystemExit(f'failed/coverage mismatch at {roots}: {rec}')
 print(json.dumps(rec))
