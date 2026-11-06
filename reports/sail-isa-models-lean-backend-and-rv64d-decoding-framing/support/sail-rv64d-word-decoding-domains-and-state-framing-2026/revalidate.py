#!/usr/bin/env python3
"""Portable replay proposal; not executed during report assembly."""
from pathlib import Path
import argparse, hashlib, json, os, shutil, subprocess, time
ap=argparse.ArgumentParser()
for x in ['lean','imports','base','output']: ap.add_argument('--'+x, required=True, type=Path)
a=ap.parse_args(); package=Path(__file__).resolve().parent
sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(a.lean)=='e215cbe9eab0914b49761e9e486d388e2e701cf876d1079d1ba733c48edb2d7b'
rows=json.loads((package/'support/import-identity-preflight.json').read_text())['verified_imports']
assert len(rows)==143
expected=set()
for r in rows:
 rel=Path(*r['module'].split('.')).with_suffix('.olean');p=a.imports/rel
 assert r['status']==0 and p.stat().st_size==r['olean_bytes'] and sha(p)==r['olean_sha256']
 expected.add(rel.as_posix())
assert {p.relative_to(a.imports).as_posix() for p in a.imports.rglob('*.olean')}==expected
inputs=[
 (a.base/'Proof.lean','Proof.lean','f62057489d30152c39dcfab87c5b7ecbb43dd2e6bbe14d0368c4cbc832b6f2d4'),
 (a.base/'support/proof/Proof.olean','Proof.olean','a37ef2b0d8f2ed3613a85ae666e89771464e2453df0929f9f80fb44397faa3bf'),
 (a.base/'Controls.lean','Controls.lean','7c9301d8c6080cd8cd1cf1a4ae356532b92de8378e416fd7ed48f35945d5635b'),
 (a.base/'support/independent/controls-v4-review/Controls.olean','Controls.olean','b2fbb76b44f7eb0ad57ca724d959a62dc0ddd7594df0db0a4b26b129fe9aa0b7'),
 (package/'ByteDiagnostic5.lean','ByteDiagnostic5.lean','5a71c58874e82df4788df8e1f9489567f70e38d14d8b6dde112dfd5f0ae16446'),
 (package/'MachineDecodeFinal2.lean','MachineDecodeFinal2.lean','fe89f0f6f1bf36db7877a9848e9c68d81d8ed130c354a9f6f7e2c7dee6c96965')]
for src,_,h in inputs: assert sha(src)==h
assert a.output.is_absolute() and a.lean.is_absolute() and a.imports.is_absolute() and a.base.is_absolute()
a.output.mkdir()
for src,name,h in inputs: shutil.copyfile(src,a.output/name); assert sha(a.output/name)==h
env=os.environ.copy();env['LEAN_PATH']=str(a.imports)+':'+str(a.output);env['LEAN_NUM_THREADS']='1'
for stem in ['ByteDiagnostic5','MachineDecodeFinal2']:
 argv=['timeout','--signal=TERM','--kill-after=5','120',str(a.lean),'-j1','-M4500','--tstack=400000','-t0','-R',str(a.output),'-o',str(a.output/(stem+'.olean')),str(a.output/(stem+'.lean'))]
 start=time.monotonic()
 with (a.output/(stem+'.stdout')).open('xb') as so,(a.output/(stem+'.stderr')).open('xb') as se:
  result=subprocess.run(argv,cwd=a.output,env=env,stdout=so,stderr=se)
 files={p.name:{'bytes':p.stat().st_size,'sha256':sha(p)} for p in [a.output/(stem+ext) for ext in ['.lean','.olean','.stdout','.stderr']] if p.exists()}
 receipt={'argv':argv,'lean_path':env['LEAN_PATH'],'status':result.returncode,'seconds':time.monotonic()-start,'files':files}
 (a.output/(stem+'-result.json')).write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(receipt))
 if result.returncode: raise SystemExit(result.returncode)
 if 'sorryAx' in (a.output/(stem+'.stdout')).read_text(): raise SystemExit('unexpected admission in accepted output')
