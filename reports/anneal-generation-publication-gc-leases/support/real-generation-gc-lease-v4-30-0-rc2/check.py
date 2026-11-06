#!/usr/bin/env python3
"""Offline evidence check for the retained real-generation GC run."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
FILES = ("current.llbc", "Current/Types.lean", "Current/Types.olean", "Current/Funs.lean", "Current/Funs.olean", "Current.lean", "Current.olean")


def sha(data):
    return hashlib.sha256(data).hexdigest()


def proof_source(value):
    name = "full-model-change-old-Proof.lean" if value == 1 else "full-model-change-new-Proof.lean"
    return (HERE / "inputs" / name).read_text() + f"example : golden_vertical.inc 0#u32 = .ok {value}#u32 := obl_inc\n#print axioms obl_inc\n"


def oracle(o, value, ok, id_, absent=False):
    assert o["proof_value"] == value
    assert o["source_sha256"] == sha(proof_source(value).encode())
    assert (o["rc"] == 0) == ok
    if ok:
        assert "'obl_inc' depends on axioms: [propext, Classical.choice, Quot.sound]" in o["stdout"]
        assert "sorryAx" not in o["stdout"]
    if absent:
        assert "unknown module prefix 'Current'" in o["stdout"]
    assert o["generation_id"] == id_


def exact(snap, expected, label, id_):
    assert snap["classification"] == label
    assert snap["generation_id"] == id_
    assert snap["files"] == expected


def main():
    d = json.loads((HERE / "results.json").read_text())
    expected = {g: {rel: sha((HERE / "inputs" / g / rel).read_bytes()) for rel in FILES} for g in "AB"}
    a_logical_bytes = sum((HERE / "inputs" / "A" / rel).stat().st_size for rel in FILES)
    ids = {g: sha(json.dumps(expected[g], sort_keys=True, separators=(",", ":")).encode()) for g in "AB"}
    assert d["expected"] == expected and d["generation_ids"] == ids
    assert ids["A"] != ids["B"]
    for label, leased in (("leased", True), ("unleased", False)):
        c = d[label]
        assert c["case"] == label
        exact(c["initial"]["selected"], expected["A"], "A", ids["A"])
        oracle(c["initial"]["old"], 1, True, ids["A"])
        oracle(c["initial"]["new"], 2, False, ids["A"])
        assert c["lease"]["acquired_shared"] == leased
        assert c["lease"]["released_after_server_exit"] == leased
        assert c["lease"]["holder_pid"] > 0
        assert c["gated_reader"]["status"] == "before Lean start"
        assert c["gated_reader"]["wrapper_pid"] == c["late_a_reader"]["wrapper_pid"] == c["late_a_reader"]["pid"]
        exact(c["publication"]["before"], expected["A"], "A", ids["A"])
        exact(c["publication"]["after"], expected["B"], "B", ids["B"])
        assert c["publication"]["pointer"] == "generations/B"
        oracle(c["fresh_b_before_gc"]["old"], 1, False, ids["B"])
        oracle(c["fresh_b_before_gc"]["new"], 2, True, ids["B"])
        first = c["first_gc"]
        assert first["gc_pid"] > 0 and first["gc_pid"] != c["lease"]["holder_pid"]
        assert first["selected_before"]["generation_id"] == ids["B"]
        assert first["logical_bytes_before"] == a_logical_bytes
        assert first["exclusive_lock_acquired"] == (not leased)
        assert first["outcome"] == ("deferred-lease-held" if leased else "removed")
        assert first["logical_bytes_after"] == (a_logical_bytes if leased else 0)
        assert first["logical_bytes_reclaimed"] == (0 if leased else a_logical_bytes)
        assert first["target_exists_after"] == leased
        late = c["late_a_reader"]
        assert late["rc"] == 0 and late["selected_generation_at_release"] == ids["B"]
        assert late["current_for_selected"] is False
        assert late["generation_path"].endswith("/generations/A")
        assert [o["proof_value"] for o in late["oracles"]] == [1, 2]
        if leased:
            exact(late["observed_family"], expected["A"], "A", ids["A"])
            oracle(late["oracles"][0], 1, True, ids["A"])
            oracle(late["oracles"][1], 2, False, ids["A"])
        else:
            assert late["observed_family"]["classification"] == "missing-or-mixed"
            assert late["observed_family"]["generation_id"] is None
            assert late["observed_family"]["files"] == {}
            oracle(late["oracles"][0], 1, False, None, absent=True)
            oracle(late["oracles"][1], 2, False, None, absent=True)
        server = c["open_server"]
        assert server["pid"] > 0 and server["exit"] == 0
        assert server["pinned_generation_id"] == ids["A"]
        assert server["current_for_selected_after_publication"] is False
        for goal in (c["open_server_initial_goal"], c["open_server_after_publication_and_gc"]["response"]):
            assert goal["result"] == {"goals": [], "rendered": "no goals"}
            assert any(m["direction"] == "server" and m["message"] == goal for m in server["messages"])
        assert c["open_server_after_publication_and_gc"]["error"] is None
        if leased:
            second = c["second_gc"]
            assert second["gc_pid"] > 0 and second["outcome"] == "removed"
            assert second["exclusive_lock_acquired"] is True
            assert second["logical_bytes_before"] == a_logical_bytes
            assert second["logical_bytes_after"] == 0 and second["logical_bytes_reclaimed"] == a_logical_bytes
        else:
            assert c["second_gc"] is None
        assert c["after"]["a_exists"] is False
        exact(c["after"]["selected"], expected["B"], "B", ids["B"])
        oracle(c["after"]["fresh_a_old"], 1, False, None, absent=True)
        oracle(c["after"]["fresh_b_new"], 2, True, ids["B"])
    print(json.dumps({"status": "ok", "generation_ids": ids, "cases": ["leased", "unleased"]}))


if __name__ == "__main__":
    main()
