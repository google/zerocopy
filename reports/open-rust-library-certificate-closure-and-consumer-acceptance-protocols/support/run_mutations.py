#!/usr/bin/env python3
from pathlib import Path
import copy,hashlib,json,os,subprocess,time
import checker
B=Path(__file__).resolve().parent;E=B/"experiments";M=E/"mutations";M.mkdir(exist_ok=True)
def raw(x):return (json.dumps(x,indent=2)+"\n").encode()
def sha(b):return hashlib.sha256(b).hexdigest()
cb=(E/"challenge.json").read_bytes();expected=sha(cb);baseline=json.loads((E/"baseline-candidate.json").read_bytes())
results=[]
def test(name,candidate=None,challenge=cb,expect=False,**kwargs):
 p=raw(baseline if candidate is None else candidate)
 (M/(name+".candidate.json")).write_bytes(p);(M/(name+".challenge.json")).write_bytes(challenge)
 v=checker.check(challenge,p,expected,name,**kwargs);v["expected_acceptance"]=expect
 assert v["accepted"]==expect,(name,v)
 results.append(v)
def mutate(name,f,**kwargs):
 c=copy.deepcopy(baseline);f(c);test(name,c,**kwargs)
for route in ["posthoc","instrumented","constructive"]:
 c=copy.deepcopy(baseline);c["route"]=route;test("baseline-"+route,c,expect=True)
for key,value in [
 ("source_sha256","0"*64),("program","other-subject"),("property","True"),
 ("domain",{"kind":"u8","bits":8,"inputs":255}),("semantics","predicate-is-true"),
 ("target","x86_64-unknown-linux-gnu"),("rust_flags",["--edition=2024","-C","opt-level=3"]),
 ("generation","consumer-generation-000"),("generic_instance","concrete-u16-scale5"),
 ("callee",{}),("lean_revision","5045d0056413266e57c625dcd7c365b10e377c52"),
 ("model_sha256","1"*64),("lean_binary_sha256","2"*64)]:
 mutate("wrong-"+key.replace("_","-"),lambda c,k=key,v=value:c["binding"].__setitem__(k,v))
mutate("wrong-policy",lambda c:c["binding"]["policy"].__setitem__("native_proof_assumptions",True))
mutate("corrupt-model-and-goal",lambda c:(c["binding"].__setitem__("semantics","predicate-is-true"),c["binding"].__setitem__("property","True"),c.__setitem__("ir",{"tag":"immediate","value":0})))
mutate("invalid-ir-reference",lambda c:c.__setitem__("ir",{"tag":"register","index":999}))
mutate("invalid-byte-literal",lambda c:c.__setitem__("ir",{"tag":"immediate","value":256}))
mutate("missing-row",lambda c:(c.__setitem__("route","instrumented"),c["rows"].pop()))
mutate("duplicate-row",lambda c:(c.__setitem__("route","instrumented"),c["rows"].__setitem__(7,c["rows"][6])))
mutate("impossible-precondition",lambda c:c["binding"].__setitem__("domain",{"kind":"empty","inputs":0}))
mutate("restrictive-decoder",lambda c:c["binding"].__setitem__("domain",{"kind":"even-u8","inputs":128}))
mutate("missing-proof-stage",lambda c:c.pop("proof_stage"))
mutate("aggregate-partial",lambda c:c["stages"].__setitem__("proof","pending"))
mutate("producer-final-record-injection",lambda c:c.__setitem__("accepted",True))
mutate("producer-proof-code-injection",lambda c:c.__setitem__("proof_code","axiom pass : False"))
mutate("wrong-ir-operation",lambda c:c["ir"]["a"]["b"].__setitem__("value",6))
mutate("wrong-native-row",lambda c:(c.__setitem__("route","instrumented"),c["rows"][9].__setitem__(3,(c["rows"][9][3]+1)%256)))
altered=json.loads(cb);altered["policy"]["native_proof_assumptions"]=True
test("changed-consumer-challenge",challenge=raw(altered))
model=(E/"ArithmeticModel.lean").read_bytes()
badmodel=model.replace(b"expected = actual",b"True")
(M/"corrupted-consumer-model.lean").write_bytes(badmodel)
test("consumer-model-file-substitution",model_bytes_override=badmodel)
failure=subprocess.run(["python3","-B","-c","raise SystemExit(7)"],capture_output=True,text=True)
test("producer-crash",producer_returncode=failure.returncode)
try:
 subprocess.run(["python3","-B","-c","import time; time.sleep(0.2)"],timeout=0.02,capture_output=True,text=True)
 raise AssertionError("did not cancel")
except subprocess.TimeoutExpired:
 test("producer-cancelled",producer_returncode=-1)
# Truncated/conflicting JSON are parser cases, not theorem failures.
for name,payload in [("truncated-export",b'{"schema":'),("conflicting-identifiers",b'{"schema":"arithmetic-candidate-v1","schema":"other"}')]:
 (M/(name+".candidate.json")).write_bytes(payload)
 v=checker.check(cb,payload,expected,name);v["expected_acceptance"]=False;assert not v["accepted"];results.append(v)

# Actual kernel/dependency controls, separate from the production data-only gate.
P=E/"assumption-controls";P.mkdir(exist_ok=True)
common=(E/"Arithmetic-posthoc.lean").read_text().split("theorem acceptance")[0]
goodbody="theorem acceptance : checkPosthoc capturedSource proposedIR = true := by decide +kernel\ntheorem consumerAccepted : Claim expectedSourceHash actualSourceHash capturedSource proposedIR := ⟨rfl, posthoc_sound _ _ acceptance⟩\n"
controls={
 "hidden-axiom":common+"axiom hidden : Claim expectedSourceHash actualSourceHash capturedSource proposedIR\ntheorem consumerAccepted : Claim expectedSourceHash actualSourceHash capturedSource proposedIR := hidden\n",
 "native-assumption":common+goodbody.replace("decide +kernel","native_decide"),
 "malformed-proof":common+goodbody.replace("⟨rfl, posthoc_sound _ _ acceptance⟩","False.elim (by decide)"),
 "missing-proof":common+"#check consumerAccepted\n",
}
helper="import Lean\nnamespace HiddenHelper\naxiom assumedFalse : False\nend HiddenHelper\n"
(P/"HiddenHelper.lean").write_text(helper)
env=dict(os.environ);env["LEAN_PATH"]=str(P)
r=subprocess.run([str(checker.LEAN),"-o","HiddenHelper.olean","HiddenHelper.lean"],cwd=P,env=env,capture_output=True,text=True);assert r.returncode==0,r.stdout
controls["imported-hidden-axiom"]="import HiddenHelper\n"+common+"theorem consumerAccepted : Claim expectedSourceHash actualSourceHash capturedSource proposedIR := False.elim HiddenHelper.assumedFalse\n"
policy_results=[]
for name,text in controls.items():
 p=P/(name+".lean");p.write_text(text+"#print axioms consumerAccepted\n")
 t=time.perf_counter();r=subprocess.run([str(checker.LEAN),p.name],cwd=P,env=env,capture_output=True,text=True,timeout=30);elapsed=time.perf_counter()-t
 p.with_suffix(".stdout").write_text(r.stdout);p.with_suffix(".stderr").write_text(r.stderr)
 accepted,reason=checker.proof_policy(r.returncode,r.stdout,json.loads(cb)["policy"]["allowed_axioms"])
 assert not accepted,(name,r.stdout)
 policy_results.append({"label":name,"kernel_exit":r.returncode,"accepted":accepted,"reason":reason,"seconds":elapsed,"actual_axioms":checker.axioms(r.stdout) if r.returncode==0 else None,"fixture_sha256":sha(p.read_bytes())})
# Cached data are hints, never cached acceptance authority; changed bindings get rechecked.
cache={"challenge_sha256":expected,"candidate_sha256":sha(raw(baseline)),"generation":"consumer-generation-001","candidate":baseline}
(M/"cache-baseline.json").write_bytes(raw(cache))
newchallenge=json.loads(cb);newchallenge["generation"]="consumer-generation-002"
old_candidate=raw(cache["candidate"])
(M/"stale-cache-generation.challenge.json").write_bytes(raw(newchallenge));(M/"stale-cache-generation.candidate.json").write_bytes(old_candidate)
v=checker.check(raw(newchallenge),old_candidate,sha(raw(newchallenge)),"stale-cache-generation")
v["expected_acceptance"]=False;assert not v["accepted"];results.append(v)
newcandidate=copy.deepcopy(baseline);newcandidate["binding"]["generation"]="consumer-generation-002"
(M/"current-generation-rechecked.challenge.json").write_bytes(raw(newchallenge));(M/"current-generation-rechecked.candidate.json").write_bytes(raw(newcandidate))
v=checker.check(raw(newchallenge),raw(newcandidate),sha(raw(newchallenge)),"current-generation-rechecked")
v["expected_acceptance"]=True;assert v["accepted"];results.append(v)

summary={"schema":"mutation-results-v1","challenge_sha256":expected,"protocol_cases":results,"assumption_controls":policy_results,"producer_process_controls":{"crash_exit":failure.returncode,"cancel_timeout_seconds":0.02},"cache_policy":"Store candidate data only; always rebind and kernel-check for the current challenge. No cached acceptance authority.","observed_at":"2026-10-14"}
(E/"mutation-results.json").write_bytes(raw(summary))
print(json.dumps({"protocol_cases":len(results),"protocol_acceptances":sum(r["accepted"] for r in results),"protocol_rejections":sum(not r["accepted"] for r in results),"assumption_controls":policy_results},indent=2))

