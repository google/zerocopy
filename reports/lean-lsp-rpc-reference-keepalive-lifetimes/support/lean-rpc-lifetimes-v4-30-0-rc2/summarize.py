#!/usr/bin/env python3
"""Check only the bounded observations claimed in REPORT.md."""
import hashlib
import json
from pathlib import Path

root=Path(__file__).resolve().parent
events=json.loads((root/"transcript.json").read_text())
def one(kind):
    found=[x for x in events if x["kind"]==kind]
    assert len(found)==1,(kind,len(found))
    return found[0]
def goal(x):
    return "\n".join(x["result"]["goals"])
def rich_target(x):
    def collect(v):
        if isinstance(v,dict):
            return [v["text"]] if "text" in v and isinstance(v["text"],str) else sum((collect(y) for y in v.values()),[])
        if isinstance(v,list):
            return sum((collect(y) for y in v),[])
        return []
    return "".join(collect(x["result"]["goals"][0]["type"]))

assert one("completed")["seq"]==len(events)-1
assert "= 9" in rich_target(one("after_edit")["old_session_result"])
assert one("after_reopen")["old"]["error"]["code"]==-32900
assert "= 10" in rich_target(one("after_reopen")["new"])
assert "= 8" in goal(one("historical")["historical"])
assert "= 10" in goal(one("historical")["current"])
assert one("fresh_session")["cross"]["error"]["code"]==-32900
assert "= 10" in rich_target(one("fresh_session")["fresh"])
late=one("late_reply")
assert late["old_response"]["id"]==late["new_response"]["id"]==50
assert "True" in goal(late["old_response"])
assert "False" in goal(late["new_response"])
assert one("rpc_cancel")["response"]["error"]["code"]==-32800
assert "True" in rich_target(one("rpc_cancel")["session_after"])
assert one("clean_after")["watchdog_rc"]==0
assert one("clean_after")["live_prior_pids"]==[]
assert one("forced_after")["watchdog_rc"]==-9
assert one("forced_after")["live_prior_pids"]==[]
assert one("worker_crash_recovery")["children"]
old_crash=[x for x in events if x["kind"]=="server" and x.get("server")=="fresh"
           and x.get("message",{}).get("id")==12]
assert len(old_crash)==1 and old_crash[0]["message"]["error"]["code"]==-32801
assert old_crash[0]["seq"]>one("worker_crash_unresolved")["seq"]

result={"status":"bounded observations passed","events":len(events),
        "transcript_sha256":hashlib.sha256((root/"transcript.json").read_bytes()).hexdigest(),
        "probe_sha256":hashlib.sha256((root/"probe.py").read_bytes()).hexdigest(),
        "lean":one("subject")["lean_version"],
        "binary_sha256":one("subject")["lean_sha256"],
        "source_sha256":one("subject")["source_sha256"],
        "historical_open_ms":one("historical")["open_ms"],
        "historical_source_bytes":one("historical")["source_bytes"],
        "historical_workers":one("historical")["children"],
        "worker_crash_old_error":-32801,
        "cancellation_error":-32800,
        "stale_session_error":-32900}
(root/"summary.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result,indent=2))
