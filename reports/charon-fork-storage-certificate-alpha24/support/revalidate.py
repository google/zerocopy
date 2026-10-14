#!/usr/bin/env python3
import argparse, json, os, pathlib, shutil, subprocess, time
p=argparse.ArgumentParser();p.add_argument('--lean-bin',required=True);p.add_argument('--out',required=True);a=p.parse_args()
src=pathlib.Path(__file__).resolve().parent;out=pathlib.Path(a.out).resolve();assert not out.exists(), 'use a new scratch directory'
support=out/'support';shutil.copytree(src,support);build=out/'build';build.mkdir();env=os.environ.copy();env['LEAN_PATH']=str(build);results=[]
commands=[['python3','-B','check_capture.py']]+[[a.lean_bin,'-o',str(build/(m+'.olean')),m+'.lean'] for m in ['ForkModel','CapturedCertificate']]
for i,argv in enumerate(commands):
 t=time.monotonic();r=subprocess.run(argv,cwd=support,env=env,text=True,capture_output=True)
 (out/f'{i}.stdout').write_text(r.stdout);(out/f'{i}.stderr').write_text(r.stderr);results.append({'stage':i,'exit':r.returncode,'seconds':time.monotonic()-t})
 assert r.returncode==0 and 'sorryAx' not in r.stdout,(r.stdout,r.stderr)
(out/'results.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps(results))
