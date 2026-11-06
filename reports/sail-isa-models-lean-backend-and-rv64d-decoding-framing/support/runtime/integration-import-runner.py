from pathlib import Path
import json,sys,hashlib,shutil,subprocess
s=json.load(sys.stdin);out=Path('/home/opam/anneal-sail-output');source=out/'integration-source'
want={x['path']:x for x in s['source']['files']};got={p.relative_to(source).as_posix():p for p in source.rglob('*') if p.is_file()}
if set(got)!=set(want):raise SystemExit('STOP source path membership')
for k,p in got.items():
 if p.is_symlink() or hashlib.sha256(p.read_bytes()).hexdigest()!=want[k]['sha256']:raise SystemExit('STOP source identity '+k)
base=out/'termination-generated/Lean_RV64D';target=out/'integration-generated/Lean_RV64D'
if target.parent.exists() or target.parent.is_symlink():raise SystemExit('STOP generated destination exists')
old={x['path']:x for x in s['project']['files']};actual={p.relative_to(base).as_posix():p for p in base.rglob('*') if p.is_file()}
if set(actual)!=set(old):raise SystemExit('STOP baseline generated membership')
for k,p in actual.items():
 if p.is_symlink() or hashlib.sha256(p.read_bytes()).hexdigest()!=old[k]['sha256']:raise SystemExit('STOP baseline generated identity '+k)
target.parent.mkdir();shutil.copytree(base,target)
inp=source/'handwritten_support/RiscvExtras.lean';dest=target/'LeanRV64D/RiscvExtras.lean';argv=['sed','s/THE_MODULE_NAME/LeanRV64D/g',str(inp)]
with dest.open('wb') as f:r=subprocess.run(argv,stdout=f,stderr=subprocess.PIPE)
(out/'integration-import.stderr').write_bytes(r.stderr)
if r.returncode:raise SystemExit('STOP native import-copy failed')
expected=inp.read_bytes().replace(b'THE_MODULE_NAME',b'LeanRV64D')
if dest.read_bytes()!=expected:raise SystemExit('STOP native copy bytes differ')
new={p.relative_to(target).as_posix():p for p in target.rglob('*') if p.is_file()}
if set(new)!=set(old):raise SystemExit('STOP integration generated membership')
rows=[];changed=[]
for k,p in sorted(new.items()):
 b=p.read_bytes();h=hashlib.sha256(b).hexdigest();rows.append({'path':k,'bytes':len(b),'sha256':h})
 if h!=old[k]['sha256']:changed.append(k)
if changed!=['LeanRV64D/RiscvExtras.lean']:raise SystemExit('STOP integration delta scope')
result={'status':0,'argv':argv,'changed':changed,'source_sha256':hashlib.sha256(inp.read_bytes()).hexdigest(),'output_sha256':hashlib.sha256(expected).hexdigest(),'files':rows}
(out/'integration-import-result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
