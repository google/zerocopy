#!/usr/bin/env python3
"""Derive and assert the narrow results from the raw topology transcript."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
events = json.loads((ROOT / "transcript.json").read_text())


def one(kind, **where):
    matches = [x for x in events if x["kind"] == kind and all(x.get(k) == v for k, v in where.items())]
    assert len(matches) == 1, (kind, where, len(matches))
    return matches[0]


def docs(label):
    return [x for x in events if x["kind"] == "document_sample" and x["label"] == label]


def diagnostic_text(x):
    return [d["message"] for d in x["diagnostics"]["diagnostics"]]


shared_a, shared_b = docs("shared-A")
separate_a = docs("separate-A")[0]
separate_b = docs("separate-B")[0]
assert "11" in diagnostic_text(shared_a)
assert "11" in diagnostic_text(shared_b)
assert any("rfl` failed" in d for d in diagnostic_text(shared_b))
assert "11" in diagnostic_text(separate_a)
assert "22" in diagnostic_text(separate_b)
assert not any("rfl` failed" in d for d in diagnostic_text(separate_b))

shared = one("process_snapshot", label="shared-two-files")
separate = one("process_snapshot", label="separate-two-servers")
first = one("process_snapshot", label="scratch-first-worker")
reopened = one("process_snapshot", label="scratch-reopened-worker")
assert shared["count"] == 3 and separate["count"] == 4
assert all(row["rss_bytes"] > 0 for row in shared["processes"] + separate["processes"])
old_worker = [p["pid"] for p in first["processes"] if p["pid"] not in first["root_pids"]]
new_worker = [p["pid"] for p in reopened["processes"] if p["pid"] not in reopened["root_pids"]]
assert len(old_worker) == len(new_worker) == 1 and old_worker != new_worker
assert all(one("process_snapshot", label=name)["summed_rss_bytes"] == 0 for name in
           ("shared-after-stop", "separate-after-stop", "scratch-after-stop", "fresh-after-stop"))

reuse = one("scratch_reused_worker")
replacement = one("scratch_new_worker")
assert reuse["initial_goal"]["result"]["goals"]
assert reuse["solved_goal"]["result"]["goals"] == []
assert reuse["rpc_goal"]["result"]["goals"][0]["ctx"]
assert replacement["old_rpc"]["error"]["code"] == -32900
assert replacement["fresh_rpc"]["result"]["goals"]
assert replacement["old_session_id"] != replacement["new_session_id"]

init = [x for x in events if x["kind"] == "server_initialized"]
ready = [x for x in events if x["kind"] == "document_ready"]
goals = [x for x in events if x["kind"] == "request_latency" and x["method"] == "$/lean/plainGoal"]
fixtures = {x["name"]: {k: x[k] for k in ("dep_sha256", "proof_sha256", "olean_sha256")}
            for x in events if x["kind"] == "fixture"}
summary = {
    "shared_two_files": {"process_count": shared["count"], "summed_rss_bytes": shared["summed_rss_bytes"],
                         "per_process": shared["processes"], "A_eval": "11", "B_eval": "11",
                         "B_claim_rfl_failed": True},
    "separate_two_servers": {"process_count": separate["count"],
                             "summed_rss_bytes": separate["summed_rss_bytes"],
                             "per_process": separate["processes"], "A_eval": "11", "B_eval": "22",
                             "B_claim_rfl_failed": False},
    "rss_difference_bytes": separate["summed_rss_bytes"] - shared["summed_rss_bytes"],
    "scratch": {"old_worker_pid": old_worker[0], "new_worker_pid": new_worker[0],
                "old_rpc_session": replacement["old_session_id"],
                "new_rpc_session": replacement["new_session_id"],
                "old_rpc_error_code": replacement["old_rpc"]["error"]["code"],
                "reused_worker_solved_goal": reuse["solved_goal"]["result"]["goals"],
                "reopened_worker_goal": replacement["reopened_goal"]["result"]["goals"],
                "fresh_server_goal": one("scratch_fresh_server")["goal"]["result"]["goals"]},
    "latencies_ms": {"initialize": {x["label"]: x["wall_ms"] for x in init},
                     "open_wait": [{"label": x["label"], "wall_ms": x["wall_ms"],
                                    "version": x["version"]} for x in ready],
                     "plain_goal": [{"label": x["label"], "wall_ms": x["wall_ms"],
                                     "request_id": x["request_id"]} for x in goals]},
    "fixtures": fixtures,
    "clean_exit_zero_observed_rss": True,
}
(ROOT / "summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
print(json.dumps({"shared_rss": shared["summed_rss_bytes"],
                  "separate_rss": separate["summed_rss_bytes"],
                  "old_rpc_error_code": replacement["old_rpc"]["error"]["code"]}))
