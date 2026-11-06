#!/usr/bin/env python3
"""Consumer-owned prototype wrapper; no OS isolation or proof of Rust import."""
from __future__ import annotations
from pathlib import Path
import hashlib,json,re,subprocess,time,os
BASE=Path(__file__).resolve().parent
EXP=BASE/"experiments"
LEAN=Path(os.environ["LEAN_BINARY"]) if "LEAN_BINARY" in os.environ else BASE.parents[1]/"toolchains/lean431/lean-4.31.0-darwin_aarch64/bin/lean"
BINDING_FIELDS=["program","source_sha256","domain","property","semantics","callee","generic_instance","target","rust_flags","lean_revision","rust_revision","generation","policy","model_sha256","lean_binary_sha256"]
def sha(data):return hashlib.sha256(data).hexdigest()
def strict_json(data):
 def pairs(items):
  out={}
  for k,v in items:
   if k in out:raise ValueError("conflicting identifier/key")
   out[k]=v
  return out
 return json.loads(data,object_pairs_hook=pairs,parse_constant=lambda _: (_ for _ in ()).throw(ValueError("constant")))
def validate_ir(a,depth=0):
 if depth>32 or type(a) is not dict:raise ValueError("invalid IR tree")
 tag=a.get("tag")
 if tag=="parameter":
  if set(a)!={"tag"}:raise ValueError("parameter fields")
 elif tag=="immediate":
  if set(a)!={"tag","value"} or type(a["value"]) is not int or not 0<=a["value"]<256:raise ValueError("byte literal")
 elif tag in ["addByte","mulByte"]:
  if set(a)!={"tag","a","b"}:raise ValueError("binary operation fields")
  validate_ir(a["a"],depth+1);validate_ir(a["b"],depth+1)
 else:raise ValueError("invalid operation/reference")
def lean_ir(a):
 tag=a["tag"]
 if tag=="parameter":return ".parameter"
 if tag=="immediate":return f".immediate {a['value']}"
 return f".{tag} ({lean_ir(a['a'])}) ({lean_ir(a['b'])})"
def lean_source(a):
 tag=a["tag"]
 if tag=="input":return ".input"
 if tag=="literal":return f".literal {a['value']}"
 return f".{tag} ({lean_source(a['a'])}) ({lean_source(a['b'])})"
def capture(source):
 pattern=r"\s*fn scale\(v: u8\) -> u8 \{ v\.wrapping_mul\((\d+)\) \}\s*pub fn subject\(x: u8\) -> u8 \{\s*let a = x\.wrapping_add\((\d+)\);\s*let b = scale\(a\);\s*b\.wrapping_add\((\d+)\)\s*\}\s*"
 m=re.fullmatch(pattern,source)
 if not m:raise ValueError("unsupported capture grammar")
 mul,add,last=map(int,m.groups())
 if max(mul,add,last)>255:raise ValueError("source byte literal")
 return {"tag":"wrappingAdd","a":{"tag":"wrappingMul","a":{"tag":"wrappingAdd","a":{"tag":"input"},"b":{"tag":"literal","value":add}},"b":{"tag":"literal","value":mul}},"b":{"tag":"literal","value":last}}
def axioms(stdout,theorem="consumerAccepted"):
 no=f"'{theorem}' does not depend on any axioms"
 if no in stdout:return []
 m=re.search(re.escape("'"+theorem+"' depends on axioms:")+"\\s*\\[([^]]*)\\]",stdout,re.S)
 if not m:raise ValueError("missing actual theorem dependency output")
 return [a.strip() for a in m.group(1).replace("\n"," ").split(",") if a.strip()]
def proof_policy(exit_code,stdout,allowed):
 if exit_code!=0:return False,"kernel-rejected"
 try:actual=axioms(stdout)
 except ValueError:return False,"missing-dependency-record"
 bad=[a for a in actual if a not in allowed]
 if bad:return False,"disallowed-assumptions:"+",".join(bad)
 return True,"kernel-and-policy-pass"
def accepted_predicate(bindings_ok,producer_ok,stages_ok,kernel_ok,policy_ok,bytes_stable):
 return bindings_ok and producer_ok and stages_ok and kernel_ok and policy_ok and bytes_stable
def make_proof(challenge,candidate,model_bytes):
 common=model_bytes.decode()+"\nopen ArithmeticPrototype\nset_option maxRecDepth 4096\nset_option maxHeartbeats 1000000\n"
 common+=f'def expectedSourceHash : String := "{challenge["source_sha256"]}"\ndef actualSourceHash : String := "{candidate["binding"]["source_sha256"]}"\n'
 common+=f"def capturedSource : Source := {lean_source(challenge['captured_source'])}\ndef proposedIR : IR := {lean_ir(candidate['ir'])}\n"
 route=candidate["route"]
 if route=="posthoc":
  body="theorem acceptance : checkPosthoc capturedSource proposedIR = true := by decide +kernel\ntheorem consumerAccepted : Claim expectedSourceHash actualSourceHash capturedSource proposedIR := ⟨rfl, posthoc_sound _ _ acceptance⟩\n"
 elif route=="constructive":
  body="theorem witness : proposedIR = construct capturedSource := by rfl\ntheorem consumerAccepted : Claim expectedSourceHash actualSourceHash capturedSource proposedIR := by\n constructor\n · rfl\n · intro x; rw [witness]; exact construct_eval _ _\n"
 elif route=="instrumented":
  rows="#["+ ", ".join(f"⟨{x}, {a}, {v}, {out}⟩" for x,a,v,out in candidate["rows"])+"]"
  body=f"def rows : Array Row := {rows}\ntheorem acceptance : checkInstrumented capturedSource proposedIR rows = true := by decide +kernel\ntheorem consumerAccepted : Claim expectedSourceHash actualSourceHash capturedSource proposedIR := ⟨rfl, instrumented_sound _ _ rows acceptance⟩\n"
 else:raise ValueError("unknown route")
 return common+body+"#print consumerAccepted\n#print axioms consumerAccepted\n"
def check(challenge_bytes,candidate_bytes,expected_challenge_sha,label,producer_returncode=0,model_bytes_override=None):
 verdict={"label":label,"accepted":False,"reason":"uninitialized","candidate_sha256":sha(candidate_bytes),"challenge_sha256":sha(challenge_bytes)}
 try:
  if not re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*",label):raise ValueError("invalid-consumer-label")
  if sha(challenge_bytes)!=expected_challenge_sha:raise ValueError("changed-consumer-challenge")
  challenge=strict_json(challenge_bytes);candidate=strict_json(candidate_bytes)
  supported={"schema":"arithmetic-challenge-v1","program":"subject","domain":{"kind":"u8","bits":8,"inputs":256},"property":"all-u8-source-ir-output-equality","semantics":"wrapping-byte-tree-v1","callee":{"scale":{"body":"wrapping_mul","constant":5}},"generic_instance":"concrete-u8-scale5","target":"aarch64-apple-darwin","rust_flags":["--edition=2024","-C","opt-level=0"],"lean_revision":"68218e876d2a38b1985b8590fff244a83c321783","rust_revision":"b940084d7eb6a299eb4bfeb8e34901bc051e7ac4","policy":{"allowed_axioms":["propext","Classical.choice","Quot.sound"],"native_proof_assumptions":False,"producer_data_only":True}}
  if set(challenge)!=set(BINDING_FIELDS)|{"schema","captured_source"}:raise ValueError("unsupported-challenge-schema")
  if any(challenge[k]!=v for k,v in supported.items()):raise ValueError("unsupported-consumer-profile")
  required={"schema","binding","ir","rows","route","proof_stage","producer_status","stages","source_artifact"}
  if set(candidate)!=required or candidate["schema"]!="arithmetic-candidate-v1":raise ValueError("malformed-or-incomplete-export")
  if type(candidate["binding"]) is not dict or set(candidate["binding"])!=set(BINDING_FIELDS):raise ValueError("missing-or-extra-binding")
  mismatches=[k for k in BINDING_FIELDS if candidate["binding"][k]!=challenge[k]]
  if mismatches:raise ValueError("binding-mismatch:"+",".join(mismatches))
  if producer_returncode!=0 or candidate["producer_status"]!="success":raise ValueError("producer-failed-or-cancelled")
  if candidate["stages"]!={"capture":"success","translate":"success","proof":"success"} or candidate["proof_stage"]!="kernel-checked":raise ValueError("missing-or-partial-stage")
  if candidate["source_artifact"]!="subject.rs":raise ValueError("invalid-source-path")
  source=(EXP/"subject.rs").read_bytes()
  if sha(source)!=challenge["source_sha256"] or capture(source.decode())!=challenge["captured_source"]:raise ValueError("source-capture-mismatch")
  validate_ir(candidate["ir"])
  rows=candidate["rows"]
  if type(rows) is not list or len(rows)!=256:raise ValueError("missing-domain-cases")
  if any(type(row) is not list or len(row)!=4 or any(type(n) is not int for n in row) or row[0]!=i or any(not 0<=n<256 for n in row) for i,row in enumerate(rows)):raise ValueError("invalid-domain-row")
  model_bytes=(EXP/"ArithmeticModel.lean").read_bytes() if model_bytes_override is None else model_bytes_override
  if sha(model_bytes)!=challenge["model_sha256"]:raise ValueError("consumer-model-mismatch")
  if sha(LEAN.read_bytes())!=challenge["lean_binary_sha256"]:raise ValueError("checker-binary-mismatch")
  # Validated data enter an independently selected model snapshot/template.
  proof=make_proof(challenge,candidate,model_bytes)
  p=EXP/"protocol-proofs"/(label+".lean");p.parent.mkdir(exist_ok=True)
  p.write_text(proof)
  t=time.perf_counter();r=subprocess.run([str(LEAN),p.name],cwd=p.parent,capture_output=True,text=True,timeout=30);elapsed=time.perf_counter()-t
  p.with_suffix(".stdout").write_text(r.stdout);p.with_suffix(".stderr").write_text(r.stderr)
  kernel_ok=r.returncode==0
  policy_ok,reason=proof_policy(r.returncode,r.stdout,challenge["policy"]["allowed_axioms"])
  # Read-only byte snapshots above, compared to the original selected inputs.
  stable=sha(candidate_bytes)==verdict["candidate_sha256"] and sha(challenge_bytes)==expected_challenge_sha
  verdict.update({"kernel_exit":r.returncode,"proof_seconds":elapsed,"actual_axioms":axioms(r.stdout) if r.returncode==0 else None,"generated_proof_sha256":sha(p.read_bytes()),"reason":reason,"accepted":accepted_predicate(True,True,True,kernel_ok,policy_ok,stable)})
 except (ValueError,KeyError,TypeError,subprocess.TimeoutExpired) as e:
  verdict["reason"]=str(e)
 return verdict

