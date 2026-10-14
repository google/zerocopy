#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,subprocess,time,platform,statistics,os
BASE=Path(__file__).resolve().parent
EXP=BASE/"experiments"
LEAN=Path(os.environ["LEAN_BINARY"]) if "LEAN_BINARY" in os.environ else BASE.parents[1]/"toolchains/lean431/lean-4.31.0-darwin_aarch64/bin/lean"
EXP.mkdir(exist_ok=True)
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2)+"\n")
source="""fn scale(v: u8) -> u8 { v.wrapping_mul(5) }
pub fn subject(x: u8) -> u8 {
    let a = x.wrapping_add(3);
    let b = scale(a);
    b.wrapping_add(7)
}
"""
(EXP/"subject.rs").write_text(source)
pattern=r"\s*fn scale\(v: u8\) -> u8 \{ v\.wrapping_mul\((\d+)\) \}\s*pub fn subject\(x: u8\) -> u8 \{\s*let a = x\.wrapping_add\((\d+)\);\s*let b = scale\(a\);\s*b\.wrapping_add\((\d+)\)\s*\}\s*"
def capture(text):
 m=re.fullmatch(pattern,text)
 if not m:raise ValueError("outside trusted captured grammar")
 mul,add,last=map(int,m.groups())
 if any(n>255 for n in [mul,add,last]):raise ValueError("byte literal")
 def lit(n):return {"tag":"literal","value":n}
 return {"tag":"wrappingAdd","a":{"tag":"wrappingMul","a":{"tag":"wrappingAdd","a":{"tag":"input"},"b":lit(add)},"b":lit(mul)},"b":lit(last)}
ast=capture(source)
def construct(a):
 tag=a["tag"]
 if tag=="input":return {"tag":"parameter"}
 if tag=="literal":return {"tag":"immediate","value":a["value"]}
 return {"tag":{"wrappingAdd":"addByte","wrappingMul":"mulByte"}[tag],"a":construct(a["a"]),"b":construct(a["b"])}
ir=construct(ast)
rustc=Path(subprocess.check_output(["rustup","which","rustc"],text=True).strip())
versions={"lean":subprocess.check_output([str(LEAN),"--version"],text=True).strip(),"rust":subprocess.check_output([str(rustc),"--version","--verbose"],text=True).strip()}
identity={"lean_binary_sha256":sha(LEAN.read_bytes()),"rustc_binary_sha256":sha(rustc.read_bytes()),"versions":versions,"host":{"system":platform.system(),"release":platform.release(),"machine":platform.machine()},"rust_stdlib_and_shared_runtime":"not fully hashed"}
dump(EXP/"toolchain-identities.json",identity)
challenge={"schema":"arithmetic-challenge-v1","program":"subject","source_sha256":sha(source.encode()),"captured_source":ast,"domain":{"kind":"u8","bits":8,"inputs":256},"property":"all-u8-source-ir-output-equality","semantics":"wrapping-byte-tree-v1","callee":{"scale":{"body":"wrapping_mul","constant":5}},"generic_instance":"concrete-u8-scale5","target":"aarch64-apple-darwin","rust_flags":["--edition=2024","-C","opt-level=0"],"lean_revision":"68218e876d2a38b1985b8590fff244a83c321783","rust_revision":"b940084d7eb6a299eb4bfeb8e34901bc051e7ac4","generation":"consumer-generation-001","policy":{"allowed_axioms":["propext","Classical.choice","Quot.sound"],"native_proof_assumptions":False,"producer_data_only":True}}
challenge["model_sha256"]=sha((EXP/"ArithmeticModel.lean").read_bytes())
challenge["lean_binary_sha256"]=identity["lean_binary_sha256"]
dump(EXP/"challenge.json",challenge)
tracefn="""pub fn subject_trace(x: u8) -> (u8,u8,u8) {
    let a = x.wrapping_add(3);
    let b = scale(a);
    (a,b,b.wrapping_add(7))
}
"""
(EXP/"instrumented.rs").write_text(source+tracefn)
harness="""#[path="instrumented.rs"] mod captured;
fn main() {
 for n in 0u16..256 {
  let x=n as u8;
  let (a,b,out)=captured::subject_trace(x);
  assert_eq!(captured::subject(x),out);
  println!("{},{},{},{}",n,a,b,out);
 }
}
"""
(EXP/"arithmetic_native.rs").write_text(harness)
t=time.perf_counter()
r=subprocess.run([str(rustc),"--edition=2024","-C","opt-level=0","arithmetic_native.rs","-o","arithmetic-native"],cwd=EXP,capture_output=True,text=True)
compile_seconds=time.perf_counter()-t
(EXP/"arithmetic_compile.stdout").write_text(r.stdout);(EXP/"arithmetic_compile.stderr").write_text(r.stderr)
assert r.returncode==0,r.stderr
times=[]
for _ in range(3):
 t=time.perf_counter();run=subprocess.run([str(EXP/"arithmetic-native")],capture_output=True,text=True);times.append(time.perf_counter()-t)
 assert run.returncode==0
(EXP/"arithmetic_native.stdout").write_text(run.stdout);(EXP/"arithmetic_native.stderr").write_text(run.stderr)
rows=[list(map(int,line.split(","))) for line in run.stdout.splitlines()]
assert len(rows)==256 and [a[0] for a in rows]==list(range(256))
assert all(a==(x+3)%256 and b==(a*5)%256 and out==(b+7)%256 for x,a,b,out in rows)
dump(EXP/"native-rows.json",rows)
dump(EXP/"native-observation.json",{"compile_exit":r.returncode,"compile_seconds":compile_seconds,"run_exit":run.returncode,"inputs":256,"rows_sha256":sha((EXP/"native-rows.json").read_bytes()),"binary_sha256":sha((EXP/"arithmetic-native").read_bytes()),"run_seconds_samples":times,"scope":"All u8 inputs, fixed source; native trace agrees with uninstrumented subject and mathematical byte formula. This does not prove Rust import or compiler correspondence."})
def lean_expr(a,source=True):
 tag=a["tag"]
 if tag in ["input","parameter"]:return ".input" if source else ".parameter"
 if tag in ["literal","immediate"]:return f".{tag} {a['value']}"
 return f".{tag} ({lean_expr(a['a'],source)}) ({lean_expr(a['b'],source)})"
common=(EXP/"ArithmeticModel.lean").read_text()+"\nopen ArithmeticPrototype\nset_option maxRecDepth 4096\nset_option maxHeartbeats 1000000\n"
common+=f'def expectedSourceHash : String := "{challenge["source_sha256"]}"\ndef actualSourceHash : String := "{challenge["source_sha256"]}"\n'
common+=f"def capturedSource : Source := {lean_expr(ast)}\ndef proposedIR : IR := {lean_expr(ir,False)}\n"
rowdata="#["+ ", ".join(f"⟨{x}, {a}, {v}, {out}⟩" for x,a,v,out in rows)+"]"
routes={
"instrumented":f"def rows : Array Row := {rowdata}\ntheorem acceptance : checkInstrumented capturedSource proposedIR rows = true := by decide +kernel\ntheorem consumerAccepted : Claim expectedSourceHash actualSourceHash capturedSource proposedIR := ⟨rfl, instrumented_sound _ _ rows acceptance⟩\n",
"posthoc":"theorem acceptance : checkPosthoc capturedSource proposedIR = true := by decide +kernel\ntheorem consumerAccepted : Claim expectedSourceHash actualSourceHash capturedSource proposedIR := ⟨rfl, posthoc_sound _ _ acceptance⟩\n#eval checkPosthoc capturedSource proposedIR\n",
"constructive":"theorem translationWitness : proposedIR = construct capturedSource := by rfl\ntheorem consumerAccepted : Claim expectedSourceHash actualSourceHash capturedSource proposedIR := by\n constructor\n · rfl\n · intro x; rw [translationWitness]; exact construct_eval _ _\n"
}
for name,body in routes.items():
 (EXP/f"Arithmetic-{name}.lean").write_text(common+body+"#print consumerAccepted\n#print axioms consumerAccepted\n#print axioms posthoc_sound\n#print axioms construct_eval\n#print axioms instrumented_sound\n")
dump(EXP/"baseline-candidate.json",{"schema":"arithmetic-candidate-v1","binding":{k:challenge[k] for k in ["program","source_sha256","domain","property","semantics","callee","generic_instance","target","rust_flags","lean_revision","rust_revision","generation","policy","model_sha256","lean_binary_sha256"]},"ir":ir,"rows":rows,"route":"posthoc","proof_stage":"kernel-checked","producer_status":"success","stages":{"capture":"success","translate":"success","proof":"success"},"source_artifact":"subject.rs"})
print(json.dumps({"source_sha256":challenge["source_sha256"],"native_compile_seconds":compile_seconds,"native_run_seconds":times,"lean_routes":list(routes)},indent=2))

