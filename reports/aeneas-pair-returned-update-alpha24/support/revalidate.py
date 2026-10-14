#!/usr/bin/env python3
import argparse, json, os, pathlib, shutil, subprocess, time
p=argparse.ArgumentParser();p.add_argument('--legacy-runtime',required=True);p.add_argument('--out',required=True);a=p.parse_args()
src=pathlib.Path(__file__).resolve().parent;out=pathlib.Path(a.out).resolve();assert not out.exists(), 'use a new scratch directory'
support=out/'support';shutil.copytree(src,support);build=out/'build';build.mkdir();rt=pathlib.Path(a.legacy_runtime).resolve()
backend=rt/'aeneas/backends/lean';packages=rt/'aeneas/packages'
paths=[build,backend/'.lake/build/lib/lean']+[q/'.lake/build/lib/lean' for q in sorted(packages.iterdir()) if (q/'.lake/build/lib/lean').is_dir()]
env=os.environ.copy();env['LEAN_PATH']=':'.join(str(q) for q in paths);results=[]
commands=[('capture',['python3','-B','check_capture.py'],0)]
commands += [(m,[str(rt/'lean/bin/lean'),'-o',str(build/(m+'.olean')),m+'.lean'],0) for m in ['CapturedTypes','CapturedFuns','UpdateCertificate','ConcreteCounterexamples']]
commands += [(m,[str(rt/'lean/bin/lean'),m+'.lean'],1) for m in ['WrongChoose','WrongUpdate']]
commands += [('native-compile',[str(rt/'rust/bin/rustc'),'--sysroot',str(rt/'rust'),'--edition=2021','-O','native_control.rs','-o',str(build/'control')],0),('native-run',[str(build/'control')],0)]
for name,argv,expected in commands:
 t=time.monotonic();r=subprocess.run(argv,cwd=support,env=env,text=True,capture_output=True)
 (out/f'{name}.stdout').write_text(r.stdout);(out/f'{name}.stderr').write_text(r.stderr);results.append({'stage':name,'exit':r.returncode,'seconds':time.monotonic()-t})
 assert r.returncode==expected,(name,r.stdout,r.stderr)
 if expected==0: assert 'sorryAx' not in r.stdout
(out/'results.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps(results))
