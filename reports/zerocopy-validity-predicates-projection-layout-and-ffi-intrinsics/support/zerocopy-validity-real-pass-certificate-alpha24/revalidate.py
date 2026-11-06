import argparse,hashlib,json,pathlib,shutil,subprocess,os
p=argparse.ArgumentParser();p.add_argument('--legacy-runtime',required=True);p.add_argument('--out',required=True);a=p.parse_args()
src=pathlib.Path(__file__).resolve().parent;out=pathlib.Path(a.out).resolve();rt=pathlib.Path(a.legacy_runtime).resolve()
if out.exists():raise SystemExit('Use a fresh scratch directory')
expected={'validity.rs': 'b13d798f9bd7fc10f72256f5467d14deeaccd7e3dcb9247ee3f13944804eca76', 'selected-bool-raw.ullbc.json': 'f7774eb41222de9042ccc931754ad986ff08125252af8b4c2b2bae04758c8d4d', 'selected-bool-aeneas.llbc.json': 'aa2358f390021a96b18b545ac756ac258301e3a5c8de17a974338830523a2568', 'CapturedModule.lean': '36a4b559404e74ac3e5ccbb8eab522c52278dbb802dd561dd80d4e31832ba5dd', 'CapturedProofs.lean': '5cfc6454f4fd8610fffd9551b733d5a7067e570d82a1ae6e2f5527fd92b415f9', 'ImportedBool.lean': 'eff8d9014c7e98ae6fd74120b076fcb7f43151000eb3d0bdd451630515c11470'}
for n,digest in expected.items():
 if hashlib.sha256((src/n).read_bytes()).hexdigest()!=digest:raise SystemExit('Selected artifact changed: '+n)
raw=json.loads((src/'selected-bool-raw.ullbc.json').read_text());final=json.loads((src/'selected-bool-aeneas.llbc.json').read_text())
rb=raw['body']['Unstructured']['body'];ss=final['body']['Structured']['body']['statements']
if len(rb)!=1 or rb[0]['terminator']['kind']!='Return' or [s['kind'] for s in rb[0]['statements']]!=[s['kind'] for s in ss[:-1]] or ss[-1]['kind']!='Return':raise SystemExit('Selected complete operation sequences differ')
shutil.copytree(src,out);build=out/'build';build.mkdir()
paths=[build,rt/'aeneas/backends/lean/.lake/build/lib/lean']+[q/'.lake/build/lib/lean' for q in sorted((rt/'aeneas/packages').iterdir()) if (q/'.lake/build/lib/lean').is_dir()]
env=os.environ.copy();env['LEAN_PATH']=':'.join(map(str,paths));rows=[]
for name in ['CapturedModule','CapturedProofs','ImportedBool']:
 r=subprocess.run([str(rt/'lean/bin/lean'),'-o',str(build/(name+'.olean')),name+'.lean'],cwd=out,env=env,capture_output=True,text=True)
 (out/(name+'.stdout')).write_text(r.stdout);(out/(name+'.stderr')).write_text(r.stderr)
 rows.append(dict(module=name,exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr))
 if r.returncode or r.stderr or 'sorryAx' in r.stdout:raise SystemExit('Rejected proof phase: '+name)
(out/'fresh-revalidation.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(rows))
