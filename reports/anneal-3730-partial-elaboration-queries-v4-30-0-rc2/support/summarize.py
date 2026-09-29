#!/usr/bin/env python3
"""Assert the bounded partial-elaboration matrix and write a compact digest."""
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent
events=json.loads((ROOT/"transcript.json").read_text())
def one(kind,case=None):
    xs=[x for x in events if x["kind"]==kind and (case is None or x.get("case")==case)]
    assert len(xs)==1,(kind,case,len(xs))
    return xs[0]
def goals(msg):
    result=msg.get("result")
    return None if result is None else result.get("goals")
def messages(uri_suffix,version):
    return [x["message"]["params"]["diagnostics"] for x in events if x["kind"]=="server"
        and x["message"].get("method")=="textDocument/publishDiagnostics"
        and x["message"]["params"]["uri"].endswith(uri_suffix)
        and x["message"]["params"].get("version")==version]

expected={"unfinished":"placeholder","unknown_tactic":"unknown tactic",
          "heartbeat":"(deterministic) timeout","syntax":"unexpected token"}
matrix={}
for name,needle in expected.items():
    b=one("batch",name);c=one("case",name)
    assert hashlib.sha256((ROOT/"work"/(name+".lean")).read_bytes()).hexdigest()==b["source_sha256"]
    assert b["rc"]==1
    ds=[json.loads(line) for line in b["stdout"].splitlines() if line.strip()]
    raw="\n".join(d.get("data","") for d in ds)
    assert needle in raw
    assert "'before' does not depend on any axioms" in raw
    assert "'after' does not depend on any axioms" in raw
    assert any(d.get("severity")=="error" for d in ds)
    assert goals(c["samples"]["before_start"])==["⊢ True"]
    assert goals(c["samples"]["after_start"])==["⊢ True"]
    assert goals(c["samples"]["before_inside"])==[]
    assert goals(c["samples"]["after_inside"])==[]
    if name in ("unfinished","unknown_tactic"):
        assert goals(c["samples"]["failure"])==["⊢ True"]
    else:
        assert goals(c["samples"]["failure"]) is None
    diags=messages(name+".lean",1)
    final_nonempty=next((d for d in reversed(diags) if d),None)
    assert final_nonempty and any(needle in d.get("message","") for d in final_nonempty)
    assert any("'before' does not depend on any axioms" in d.get("message","") for d in final_nonempty)
    assert any("'after' does not depend on any axioms" in d.get("message","") for d in final_nonempty)
    matrix[name]={"batch_diagnostics":len(ds),"final_lsp_diagnostics":len(final_nonempty),
                  "failure_goal":goals(c["samples"]["failure"]),
                  "before_goal":goals(c["samples"]["before_start"]),
                  "after_goal":goals(c["samples"]["after_start"]),
                  "batch_ms":b["wall_ms"],"source_sha256":b["source_sha256"]}

edit=one("edit_case")
assert hashlib.sha256((ROOT/"work"/"Edit.lean").read_bytes()).hexdigest()==edit["v1_sha256"]
assert goals(edit["old"])==["⊢ True"]
assert goals(edit["immediate"])==["⊢ False"]
assert goals(edit["late_v1"])==goals(edit["late_v2"])==["⊢ False"]
assert edit["ready"]["result"]==edit["oldwait"]["result"]=={}
ed2=messages("Edit.lean",2)
ed2_nonempty=next((d for d in reversed(ed2) if d),None)
assert ed2_nonempty and any("unknown tactic" in d.get("message","") for d in ed2_nonempty)
assert any("⊢ False" in d.get("message","") for d in ed2_nonempty)
assert one("completed")["seq"]<one("stop")["seq"]
assert one("stop")["rc"]==0
assert not [x for x in events if x["kind"]=="fatal"]
subject=one("subject")
summary=dict(status="bounded matrix passed",events=len(events),
    transcript_sha256=hashlib.sha256((ROOT/"transcript.json").read_bytes()).hexdigest(),
    probe_sha256=hashlib.sha256((ROOT/"probe.py").read_bytes()).hexdigest(),
    lean_version=subject["lean_version"],binary_sha256=subject["binary_sha256"],
    matrix=matrix,edit_case={"old_goal":goals(edit["old"]),
      "immediate_goal":goals(edit["immediate"]),"late_version_1_goal":goals(edit["late_v1"]),
      "late_version_2_goal":goals(edit["late_v2"]),"v1_sha256":edit["v1_sha256"],
      "v2_sha256":edit["v2_sha256"]})
(ROOT/"summary.json").write_text(json.dumps(summary,indent=2)+"\n")
print(json.dumps(summary,indent=2))
