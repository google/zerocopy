#!/usr/bin/env python3
import argparse, json, os, pathlib, shutil, subprocess, time
p=argparse.ArgumentParser();p.add_argument('--lean-root',required=True);p.add_argument('--out',required=True);a=p.parse_args()
src=pathlib.Path(__file__).resolve().parent;out=pathlib.Path(a.out).resolve();assert not out.exists(), 'use a new scratch directory'
support=out/'support';shutil.copytree(src,support);build=out/'build';build.mkdir();rt=pathlib.Path(a.lean_root).resolve();env=os.environ.copy();env['LEAN_PATH']=str(build);results=[]
commands=[(m,[str(rt/'bin/lean'),'-o',str(build/(m+'.olean')),'-c',str(build/(m+'.c')),m+'.lean']) for m in ['ArithmeticModel','CheckerMain']]
commands += [('kernel',[str(rt/'bin/lean'),'KernelReplay.lean']),('one-kernel',[str(rt/'bin/lean'),'SingleReplay.lean']),('link',[str(rt/'bin/leanc'),'-O2','-o',str(build/'checker'),str(build/'ArithmeticModel.c'),str(build/'CheckerMain.c')])]
for name,argv in commands:
 t=time.monotonic();r=subprocess.run(argv,cwd=support,env=env,text=True,capture_output=True)
 (out/f'{name}.stdout').write_text(r.stdout);(out/f'{name}.stderr').write_text(r.stderr);results.append({'stage':name,'exit':r.returncode,'seconds':time.monotonic()-t})
 assert r.returncode==0 and 'sorryAx' not in r.stdout,(r.stdout,r.stderr)
t=time.monotonic();r=subprocess.run([str(build/'checker')],input=(support/'fixture-inputs.jsonl').read_text(),text=True,capture_output=True)
(out/'native.stdout').write_text(r.stdout);(out/'native.stderr').write_text(r.stderr)
expected=json.loads((support/'fixture-expectations.json').read_text());actual=[json.loads(l) for l in r.stdout.splitlines()]
assert r.returncode==0 and len(actual)==len(expected) and all(x['accepted']==y['accepted'] for x,y in zip(actual,expected))
results.append({'stage':'native-fixtures','exit':r.returncode,'seconds':time.monotonic()-t,'cases':len(actual)})
(out/'results.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps(results))
