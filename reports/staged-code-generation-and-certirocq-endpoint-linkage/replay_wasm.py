"""Replay original sources in a caller-selected fresh scratch; no installs or upstream builds."""
from pathlib import Path
import argparse,ast,hashlib,json,os,re,shutil,statistics,subprocess,time
arg=argparse.ArgumentParser();arg.add_argument('--out',required=True);arg.add_argument('--lean',required=True);arg.add_argument('--node',required=True);a=arg.parse_args()
src=Path(__file__).resolve().parent;out=Path(a.out).resolve()
if out.exists():raise SystemExit('Use a new output directory, preserving prior observations')
out.mkdir(parents=True)
files=['WasmValidator.lean','WasmArtifact.lean','KernelBase.lean','KernelBench.lean','execute_wasm.mjs','module-bytes.json','mutations.json']
for f in files:shutil.copyfile(src/f,out/f)
env=dict(os.environ);env['LEAN_PATH']=str(out)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
results=[]
def call(cmd,label):
    t=time.perf_counter();r=subprocess.run(cmd,cwd=out,env=env,capture_output=True,text=True);dt=time.perf_counter()-t
    (out/(label+'.stdout')).write_text(r.stdout);(out/(label+'.stderr')).write_text(r.stderr)
    row=dict(label=label,command=cmd,exit=r.returncode,seconds=dt,stdout=r.stdout,stderr=r.stderr);results.append(row)
    if r.returncode or 'sorryAx' in r.stdout:raise RuntimeError(str(row))
    return row
r=call([a.lean,'-o',str(out/'WasmValidator.olean'),str(out/'WasmValidator.lean')],'compiler')
bs=ast.literal_eval(re.search(r'\[0, 97, 115, 109,.*?\]',r['stdout'],re.S).group())
assert bs==json.loads((src/'module-bytes.json').read_text())
assert bytes(bs)==(src/'boolean4.wasm').read_bytes()
(out/'boolean4.wasm').write_bytes(bytes(bs))
call([a.lean,str(out/'WasmArtifact.lean')],'artifact')
for k in range(5):
    for f in ['KernelBase.lean','KernelBench.lean','WasmArtifact.lean']:call([a.lean,str(out/f)],f+'.trial'+str(k))
call([a.node,str(out/'execute_wasm.mjs')],'node')
root=Path(a.lean).parent.parent
ident=[Path(a.lean),root/'lib/lean/Init.olean',root/'lib/lean/libleanshared.dylib']
report=dict(status='pass',results=results,lean_version=subprocess.run([a.lean,'--version'],capture_output=True,text=True).stdout.strip(),
            identities=[dict(path=str(p),sha256=sha(p)) for p in ident],
            sources={f:sha(out/f) for f in files},module_sha256=sha(out/'boolean4.wasm'),
            boundary='Restricted compiler/parser proof and observed engine execution; normative specification correspondence, engine, filesystem/transcription, OS and hardware remain trusted.')
(out/'replay.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(dict(status='pass',out=str(out),module_sha256=report['module_sha256'],runs=len(results))))
