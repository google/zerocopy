#!/usr/bin/env python3
"""Offline validation of the bounded direct Lean cancellation transcript."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
events = json.loads((HERE/"transcript.json").read_text())
sha = lambda b: hashlib.sha256(b).hexdigest()
assert [x["seq"] for x in events] == list(range(len(events)))
assert not [x for x in events if x["kind"] == "fatal"]
one = lambda kind: next(x for x in events if x["kind"] == kind)
subject = one("subject")
assert "4.30.0-rc2" in subject["lean_version"]
assert subject["binary_sha256"] == "b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997"
assert subject["free_disk_bytes"] >= 1_000_000_000
for number in (1,2,3):
    assert subject["source_sha256"][str(number)] == sha((HERE/"work"/f"V{number}.lean").read_bytes())
assert (HERE/"work"/"Active.lean").read_bytes() == (HERE/"work"/"V1.lean").read_bytes()
assert len([x for x in events if x["kind"] == "server_start"]) == 1

batches = {x["version"]:x for x in events if x["kind"] == "batch"}
assert sorted(batches) == [1,3]
assert all(batches[v]["returncode"] == 0 and batches[v]["stdout"] == batches[v]["stderr"] == "" for v in (1,3))
assert batches[1]["markers"] == ["A","B1","C1"]
assert batches[3]["markers"] == ["A","B1","C1","A","B3","C3"]
base = ["A","B1","C1"]
final = base + ["B3","C3"]
assert one("ready")["version"] == 1 and one("ready")["response"]["result"] == {}
assert one("ready")["markers"] == base
for kind in ("gate_entered","edit_and_cancel_sent","gate_released"):
    assert one(kind)["markers"] == base
assert one("gate_entered")["gate_sha256"] == sha((HERE/"work"/"gate.entered").read_bytes())
assert [one(k)["seq"] for k in ("gate_entered","edit_and_cancel_sent","gate_released","wait_replies","final_goal","completed","server_stop")] == sorted(
       one(k)["seq"] for k in ("gate_entered","edit_and_cancel_sent","gate_released","wait_replies","final_goal","completed","server_stop"))

sent = [x["message"] for x in events if x["kind"] == "send"]
edits = [x for x in sent if x.get("method") == "textDocument/didChange"]
assert [x["params"]["textDocument"]["version"] for x in edits] == [2,3]
assert [sha(x["params"]["contentChanges"][0]["text"].encode()) for x in edits] == [
    subject["source_sha256"]["2"], subject["source_sha256"]["3"]]
cancel = [x for x in sent if x.get("method") == "$/cancelRequest"]
assert len(cancel) == 1 and cancel[0]["params"] == {"id":20}
assert one("edit_and_cancel_sent")["seq"] < one("gate_released")["seq"]
assert one("wait_replies")["pending"] == []
replies = one("wait_replies")["responses"]
assert replies["20"]["error"]["code"] == -32800
assert replies["21"]["result"] == {}
assert one("wait_replies")["markers"] == final
goal = one("final_goal")
assert goal["response"]["result"]["goals"] == ["⊢ generated = 3"]
assert goal["markers"] == one("completed")["markers"] == final
assert (HERE/"work"/"markers.txt").read_text().splitlines() == final
assert all("B2" not in x["markers"] and "C2" not in x["markers"]
           for x in events if "markers" in x and x["seq"] >= one("ready")["seq"])

diags = [x["message"]["params"] for x in events if x["kind"] == "recv"
         and x["message"].get("method") == "textDocument/publishDiagnostics"]
assert diags and any(x.get("version") == 3 and x["diagnostics"] == [] for x in diags)
stop = one("server_stop")
assert stop["returncode"] == 0 and stop["stderr"] == ""
assert 0 < stop["peak_sampled_rss_bytes"] < stop["rss_cap_bytes"] == 1_500_000_000
print("PASS: gated early-prefix edit, canceled V2 wait, V3 suffix only, exact goal, resource bound, clean exit")
