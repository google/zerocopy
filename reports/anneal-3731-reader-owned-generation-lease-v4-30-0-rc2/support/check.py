#!/usr/bin/env python3
"""Offline check of the independent-reader lease and GC transcript."""
import hashlib
import json
import signal
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent.parent / "anneal-3731-real-generation-gc-lease-v4-30-0-rc2" / "support" / "inputs"
FILES = ("current.llbc", "Current/Types.lean", "Current/Types.olean", "Current/Funs.lean", "Current/Funs.olean", "Current.lean", "Current.olean")


def sha(data):
    return hashlib.sha256(data).hexdigest()


def exact(snapshot, expected, label, ids):
    assert snapshot["classification"] == label
    assert snapshot["generation_id"] == ids[label]
    assert snapshot["files"] == expected[label]


def proof_source(value):
    name = "full-model-change-old-Proof.lean" if value == 1 else "full-model-change-new-Proof.lean"
    return (SOURCE / name).read_text() + f"example : golden_vertical.inc 0#u32 = .ok {value}#u32 := obl_inc\n#print axioms obl_inc\n"


def proof(record, value, passes, generation):
    assert record["proof_value"] == value
    assert record["source_sha256"] == sha(proof_source(value).encode())
    assert (record["rc"] == 0) == passes
    assert record["generation_id"] == generation
    if passes:
        assert "'obl_inc' depends on axioms: [propext, Classical.choice, Quot.sound]" in record["stdout"]
        assert "sorryAx" not in record["stdout"]
    else:
        assert "Tactic `rfl` failed" in record["stdout"]
        assert "sorryAx" in record["stdout"]


def main():
    d = json.loads((HERE / "results.json").read_text())
    metadata = json.loads((HERE.parent / "REPORT.json").read_text())
    assert set(metadata) == {"topics", "subjects", "observed_at"}
    assert metadata["observed_at"] == "2026-09-29"
    assert len(metadata["topics"]) == len(set(metadata["topics"])) > 0
    families, lean, fixture = metadata["subjects"]
    assert families["identity"]["source_reference_package"] == SOURCE.parent.parent.name
    assert families["identity"]["old_origin_reference_commit"] == "b1787210c0143a705f6bbbf2da3b2fba30cc5718"
    assert lean["identity"]["repository"] == "leanprover/lean4"
    assert lean["identity"]["revision"] == "3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc"
    assert lean["identity"]["version"] == "v4.30.0-rc2"
    assert fixture["identity"]["source"] == "support/probe.py"
    assert fixture["identity"]["sha256"] == sha((HERE / "probe.py").read_bytes())
    assert fixture["identity"]["reference_checkout"] == d["reference_head"]
    expected = {g: {rel: sha((SOURCE / g / rel).read_bytes()) for rel in FILES} for g in "AB"}
    ids = {g: sha(json.dumps(expected[g], sort_keys=True, separators=(",", ":")).encode()) for g in "AB"}
    assert d["reference_head"] == "c89f1410d4f1cfbd9b654ea5268b38f5c81e115e"
    assert d["expected"] == expected and d["generation_ids"] == ids and ids["A"] != ids["B"]
    assert d["tool"]["lean_sha256"] == "b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997"
    assert lean["identity"]["binary_sha256"] == d["tool"]["lean_sha256"]
    assert families["identity"]["old_generation_id"] == ids["A"]
    assert families["identity"]["new_generation_id"] == ids["B"]
    exact(d["initial"], expected, "A", ids)
    exact(d["selected_b"], expected, "B", ids)
    one = d["acquired"]["reader-one"]
    two = d["acquired"]["reader-two"]
    for name, record in (("reader-one", one), ("reader-two", two)):
        assert record["name"] == name and record["shared_lock_acquired"] is True
        assert record["lease_path"].endswith("/generations/A/lease.lock")
        exact(record["family"], expected, "A", ids)
        assert record["time_ns"] < d["published_time_ns"]
    assert one["reader_pid"] != two["reader_pid"]
    assert d["killed_reader"]["pid"] == one["reader_pid"]
    assert d["killed_reader"]["rc"] == -signal.SIGKILL
    assert d["killed_reader"]["stdout"] == "" and d["killed_reader"]["stderr"] == ""
    assert d["reader_two_exit"]["pid"] == two["reader_pid"] and d["reader_two_exit"]["rc"] == 0
    done = d["reader_two_done"]
    assert done["reader_pid"] == two["reader_pid"] and done["name"] == "reader-two"
    assert done["shared_lock_acquired"] is True
    exact(done["family"], expected, "A", ids)
    exact(done["selected_after_publish"], expected, "B", ids)
    assert json.loads(d["reader_two_exit"]["stdout"]) == {k: v for k, v in done.items() if k != "time_ns"}
    assert d["reader_two_exit"]["stderr"] == ""
    proof(done["oracles"][0], 1, True, ids["A"])
    proof(done["oracles"][1], 2, False, ids["A"])
    stages = ("gc_both", "gc_after_kill", "gc_after_import", "gc_after_exit")
    times = [d[k]["time_ns"] for k in stages]
    assert d["published_time_ns"] < times[0] < d["killed_reader"]["completed_time_ns"] < times[1] < done["time_ns"] < times[2] < times[3]
    logical_bytes = sum((SOURCE / "A" / rel).stat().st_size for rel in FILES)
    pids = {one["reader_pid"], two["reader_pid"]}
    for k in stages:
        g = d[k]
        assert g["rc"] == 0 and g["stderr"] == ""
        assert g["gc_pid"] not in pids
        assert json.loads(g["stdout"])["gc_pid"] == g["gc_pid"]
        exact(g["selected"], expected, "B", ids)
        assert g["bytes_before"] == logical_bytes
        if k != "gc_after_exit":
            assert g["outcome"] == "deferred-reader-lease" and g["exclusive_lock_acquired"] is False
            assert g["bytes_after"] == logical_bytes and g["a_exists"] is True
        else:
            assert g["outcome"] == "removed" and g["exclusive_lock_acquired"] is True
            assert g["bytes_after"] == 0 and g["a_exists"] is False
    assert d["a_exists_after_gc"] is False
    proof(d["b_proof_after_gc"], 2, True, ids["B"])
    print(json.dumps({"status": "ok", "generation_ids": ids, "gc_outcomes": [d[k]["outcome"] for k in stages]}))


if __name__ == "__main__":
    main()
