#!/usr/bin/env python3
"""Offline checker for the retained I051 real-artifact publication run."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
R = json.loads((HERE / "results.json").read_text())
FILES = ["current.llbc", "Current/Types.lean", "Current/Types.olean", "Current/Funs.lean", "Current/Funs.olean", "Current.lean", "Current.olean"]

def inventory(root):
    return {p.relative_to(root).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest() for p in root.rglob("*") if p.is_file()}

for name in "AB":
    actual = inventory(HERE / "inputs" / name)
    assert set(actual) == set(FILES)
    assert actual == R["expected"][name]
    gid = hashlib.sha256(json.dumps(actual, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    assert gid == R["generation_ids"][name]

assert R["expected"]["A"]["Current.olean"] == R["expected"]["B"]["Current.olean"]
assert R["expected"]["A"]["Current/Funs.olean"] != R["expected"]["B"]["Current/Funs.olean"]
old = json.loads((HERE / "inputs/model-manifest.json").read_text())
new = json.loads((HERE / "inputs/new-model-manifest.json").read_text())
assert old["llbc_sha256"] == R["expected"]["A"]["current.llbc"]
assert new["llbc_sha256"] == R["expected"]["B"]["current.llbc"]
assert old["files"] == {k:v for k,v in R["expected"]["A"].items() if k != "current.llbc"}
assert new["files_sha256"] == {k:v for k,v in R["expected"]["B"].items() if k != "current.llbc"}

def checked_snapshot(s):
    if s["classification"] in "AB":
        assert s["generation_id"] == R["generation_ids"][s["classification"]]
        assert s["files"] == R["expected"][s["classification"]]
    else:
        assert s["classification"] == "mixed" and s["generation_id"] is None
        assert set(s["files"]) == set(FILES)
        assert s["files"] not in R["expected"].values()

for case in ("staged", "inplace", "kill_before", "kill_after"):
    item = R[case]
    gates = item["gates"]
    assert [g["gate"] for g in gates[:7]] == [f"write-{i}" for i in range(7)]
    for g in gates:
        checked_snapshot(g["selected"])
        for q in g["reader_oracles"]:
            assert q["generation_path"] == g["selected"]["resolved"]
            assert q["generation_id"] == g["selected"]["generation_id"]
            assert q["generation_classification"] == g["selected"]["classification"]
            assert q["proof_value"] in (1,2)
            if g["selected"]["classification"] == "A": assert (q["rc"] == 0) == (q["proof_value"] == 1)
            if g["selected"]["classification"] == "B": assert (q["rc"] == 0) == (q["proof_value"] == 2)
            if q["rc"] == 0:
                assert "sorryAx" not in q["stdout"]
                assert "'obl_inc' depends on axioms: [propext, Classical.choice, Quot.sound]" in q["stdout"]
    checked_snapshot(item["readback"])

staged = R["staged"]
assert [g["gate"] for g in staged["gates"][7:]] == ["validated", "generation-moved", "before-publish", "after-publish"]
assert all(g["selected"]["classification"] == "A" for g in staged["gates"][:-1])
assert staged["gates"][-1]["selected"]["classification"] == "B"
assert staged["readback"]["classification"] == "B"
assert staged["old_server_initial_goal"]["response"]["result"] == {"goals": [], "rendered": "no goals"}
assert staged["old_server_after_goal"]["response"]["result"] == {"goals": [], "rendered": "no goals"}
assert staged["old_server_initial_goal"]["generation_id"] == R["generation_ids"]["A"]
assert staged["old_server_after_goal"]["generation_id"] == R["generation_ids"]["A"]
assert staged["old_server_initial_goal"]["current_for_selected"] is True
assert staged["old_server_after_goal"]["current_for_selected"] is False
assert staged["old_server"]["pinned_generation_id"] == R["generation_ids"]["A"]
assert staged["old_server"]["exit"] == 0
assert staged["validation"]["generation_id"] == R["generation_ids"]["B"]
assert staged["validation"]["exact_files"] == R["expected"]["B"]
assert staged["validation"]["old_proof"]["rc"] != 0
assert staged["validation"]["new_proof"]["rc"] == 0
for key in ("old_proof", "new_proof"):
    assert staged["validation"][key]["generation_id"] == R["generation_ids"]["B"]
    assert staged["validation"][key]["generation_classification"] == "B"

inplace = R["inplace"]
assert [g["selected"]["classification"] for g in inplace["gates"]] == ["mixed"]*4 + ["B"]*3
for n,g in enumerate(inplace["gates"]):
    expected = {rel: R["expected"]["B" if i <= n else "A"][rel] for i,rel in enumerate(FILES)}
    assert g["selected"]["files"] == expected
    assert [(q["proof_value"], q["rc"] == 0) for q in g["reader_oracles"]] == ([(1,True),(2,False)] if n < 4 else [(1,False),(2,True)])
assert inplace["readback"]["classification"] == "B"
assert R["kill_before"]["kill_at"] == "before-publish"
assert R["kill_before"]["readback"]["classification"] == "A"
assert R["kill_after"]["kill_at"] == "after-publish"
assert R["kill_after"]["readback"]["classification"] == "B"
assert R["kill_before"]["kill_rc"] < 0 and R["kill_after"]["kill_rc"] < 0
print("I051 real-artifact publication evidence checked")
