#!/usr/bin/env python3
"""Finite quantifier, extraction, and UB-erasure controls; owned models only."""
from pathlib import Path
from fractions import Fraction
import itertools,json,platform,sys
def demonic(xs,ok): return all(ok(x) for x in xs)
def angelic(xs,ok): return any(ok(x) for x in xs)
def checked_demonic_certificate(allowed,cert,ok):
    return set(allowed)<=set(cert) and all(ok(x) for x in cert)
def checked_angelic_certificate(allowed,witness,ok):
    return witness in allowed and ok(witness)
# Faithful control-flow transcription of filter_specr_lang in source.rs.
def exact_fences(s):
    out=""
    while "\n```rust\n" in s:
        s=s.split("\n```rust\n",1)[1]
        if "\n```\n" not in s: return {"status":"unclosed"}
        code,s=s.split("\n```\n",1);out+=code+"\n\n"
    return {"status":"ok","code":out}
# Independent line-based collector for the stated normal fenced subset.
def line_fences(s):
    blocks=[];inside=False;cur=[]
    for line in s.splitlines():
        if line=="```rust": inside=True;cur=[]
        elif line=="```" and inside:
            blocks.append("\n".join(cur));inside=False
        elif inside:cur.append(line)
    return "\n\n".join(blocks)+("\n\n" if blocks else "")
normal="# Code\n\n```rust\nfn f() -> i32 { 7 }\n```\n"
ignored="# Code\n\n```rust,ignore\nfn hidden() {}\n```\n"
at_start="```rust\nfn f() -> i32 { 7 }\n```\n"
at_end="# Code\n```rust\nfn f() -> i32 { 7 }\n```"
# Do not exercise the subject's panic. The owned result classifies it.
fences={name:{"exact":exact_fences(s),"independent":line_fences(s)}
        for name,s in [("normal",normal),("ignored",ignored),("at_start",at_start),("no_final_newline",at_end)]}
# All 16 relations over two choices: the quantifier swap is checked exhaustively.
tables=[]
for bits in itertools.product([False,True],repeat=4):
    r=lambda a,p:bits[2*a+p]
    tables.append({"bits":bits,
      "forall_exists":all(any(r(a,p) for p in range(2)) for a in range(2)),
      "exists_forall":any(all(r(a,p) for a in range(2)) for p in range(2))})
# A legal deterministic stream can miss the one valid candidate 50 times.
stream=[0]*50
rare={"domain":4096,"valid_candidate":4095,"sample_budget":50,
      "legal_miss_stream":stream,"budget_exhausted":not any(x==4095 for x in stream),
      "semantic_allowed_set_nonempty":True,
      "uniform_failure_probability":float(Fraction(4095,4096)**50)}
# Source/model behavior domains include UB, rather than conditioning it away.
def source_run(ops):
    for op in ops:
        if op=="bad_bool_load":return "UB"
    return "Return"
def faulty_erase_discarded(ops):return [op for op in ops if op!="bad_bool_load"]
programs=[["return"],["bad_bool_load","return"],["bad_bool_load","unreachable","return"]]
erasure=[{"source":p,"source_outcome":source_run(p),
          "imported":faulty_erase_discarded(p),
          "imported_outcome":source_run(faulty_erase_discarded(p))} for p in programs]
checks={
 "empty_demonic_no_behavior":demonic([],lambda _:False),
 "empty_angelic_no_witness":not angelic([],lambda _:True),
 "one_run_does_not_prove_all":angelic([0,1],lambda x:x==0) and not demonic([0,1],lambda x:x==0),
 "incomplete_demonic_certificate_rejected":not checked_demonic_certificate([0,1],[0],lambda x:x==0),
 "invalid_angelic_witness_rejected":not checked_angelic_certificate(["A"],"B",lambda _:True),
 "normal_fence_routes_agree":fences["normal"]["exact"]["code"]==fences["normal"]["independent"],
 "fence_boundary_mutants_discriminate":fences["at_start"]["exact"]["code"]!=fences["at_start"]["independent"],
 "rare_valid_choice_sampler_miss":rare["budget_exhausted"],
 "quantifier_order_differs":any(t["forall_exists"]!=t["exists_forall"] for t in tables),
 "bad_execution_erasure_detected":any(t["source_outcome"]=="UB" and t["imported_outcome"]=="Return" for t in erasure)
}
out={"kind":"owned-model","python":sys.version.split()[0],"platform":platform.platform(),
     "checks":checks,"fences":fences,"quantifier_tables":tables,"rare_choice":rare,
     "erasure_control":erasure,"status":"pass" if all(checks.values()) else "fail"}
Path("results.json").write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps({"checks":checks,"rare_failure_probability":rare["uniform_failure_probability"],"status":out["status"]},indent=2))
sys.exit(0 if out["status"]=="pass" else 1)

