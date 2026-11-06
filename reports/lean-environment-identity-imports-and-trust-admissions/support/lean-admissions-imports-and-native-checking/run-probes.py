from pathlib import Path
import os,stat,subprocess,json,hashlib,time,re
import argparse
parser=argparse.ArgumentParser()
parser.add_argument('--lean',required=True)
args=parser.parse_args()
PKG=Path(__file__).resolve().parent.parent
D=PKG/'support/probes';D.mkdir(parents=True,exist_ok=True)
LEAN=Path(args.lean).resolve()
if not LEAN.is_file():raise RuntimeError('missing selected Lean binary')
specs={
 'logical-and-assumed':'''import Lean\ntheorem ordinary : 1 + 1 = 2 := by decide\ntheorem localHyp (h : False) : False := h\naxiom assumedFalse : False\nprivate def concealedFalse : False := assumedFalse\ntheorem viaHelper : False := concealedFalse\n#print axioms ordinary\n#print axioms localHyp\n#print axioms viaHelper\n''',
 'native-implementation':'''import Lean\ndef nativeTrue : Bool := true\n@[implemented_by nativeTrue]\ndef logicalFalse : Bool := false\ntheorem logicalResult : logicalFalse = false := rfl\ntheorem nativeResult : logicalFalse = true := by native_decide\n#print axioms logicalResult\n#print axioms nativeResult\n''',
 'checked-rejection':'''import Lean\nrun_cmd Lean.Elab.Command.liftCoreM do\n  Lean.addDecl <| Lean.Declaration.thmDecl {\n    name := `forged, levelParams := [],\n    type := Lean.mkConst ``False,\n    value := Lean.mkConst ``True.intro\n  }\n''',
 'kernel-bypass':'''import Lean\nset_option debug.skipKernelTC true\nrun_cmd Lean.Elab.Command.liftCoreM do\n  Lean.addDecl <| Lean.Declaration.thmDecl {\n    name := `forged, levelParams := [],\n    type := Lean.mkConst ``False,\n    value := Lean.mkConst ``True.intro\n  }\n#print axioms forged\n#print forged\n'''
}
results=[]
def run(label,args,expected):
 start=time.monotonic();env=os.environ.copy();env['LEAN_PATH']=str(D);env['PYTHONDONTWRITEBYTECODE']='1'
 p=subprocess.run([str(LEAN),*args],cwd=D,env=env,capture_output=True,text=True,timeout=30)
 (D/(label+'.stdout')).write_text(p.stdout);(D/(label+'.stderr')).write_text(p.stderr)
 results.append(dict(label=label,args=args,exit=p.returncode,expected_exit=expected,seconds=round(time.monotonic()-start,4),stdout=p.stdout,stderr=p.stderr))
for label,source in specs.items():
 f=D/(label+'.lean');f.write_text(source);run(label,[f.name],1 if label=='checked-rejection' else 0)
v1='axiom oldAssumption : False\ntheorem exportedFalse : False := oldAssumption\n'
v2='axiom newAssumption : False\ntheorem exportedFalse : False := newAssumption\n'
(D/'Producer-v1.lean').write_text(v1);(D/'Producer-v2.lean').write_text(v2)
(D/'Producer.lean').write_text(v1)
run('compile-producer',['-o','Producer.olean','Producer.lean'],0)
(D/'Producer.lean').write_text(v2)
(D/'Consumer.lean').write_text('import Producer\n#print axioms exportedFalse\n')
run('stale-source-import',['Consumer.lean'],0)
selected_version=subprocess.check_output([str(LEAN),'--version'],text=True).strip()
revision_match=re.search(r'commit ([0-9a-f]+)',selected_version)
result=dict(toolchain=dict(version=selected_version,revision=revision_match.group(1) if revision_match else 'not reported',binary_sha256=hashlib.sha256(LEAN.read_bytes()).hexdigest()),environment=dict(platform=os.uname().sysname,machine=os.uname().machine,release=os.uname().release,lean_path='support/probes',cwd='support/probes',timeout_seconds=30),results=results,files={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in D.iterdir() if p.is_file()})
(PKG/'support/observations.json').write_text(json.dumps(result,indent=2)+'\n')
for r in results:print(r['label'],r['exit'],r['stdout'].strip(),r['stderr'].strip())
