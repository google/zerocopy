#!/usr/bin/env python3
"""Check retained frozen-index result; no Lake invocation is needed."""
import json
from pathlib import Path

data = json.loads((Path(__file__).parent / "results.json").read_text())
assert data["lake_sha256"] == "9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb"
assert data["lean_sha256"] == "b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997"
runs = {r["label"]: r for r in data["runs"]}
assert len(runs) == len(data["runs"]) == 4
assert [runs[k]["exit"] for k in (
    "prime-index-1", "frozen-matching-index-1", "frozen-shifted-index-2",
    "writable-shifted-index-2")] == [0, 0, 1, 0]
assert "Built Dep" in runs["prime-index-1"]["stdout"]
assert "Replayed Dep" in runs["frozen-matching-index-1"]["stdout"]
assert "Replayed Dep" in runs["writable-shifted-index-2"]["stdout"]
assert "info: Generated.lean:3:0: 7" in runs["frozen-matching-index-1"]["stdout"]
assert "info: Generated.lean:3:0: 7" in runs["writable-shifted-index-2"]["stdout"]
assert "permission denied" in runs["frozen-shifted-index-2"]["stderr"]
assert "$WORK/producer/.lake/config/probe_dep/lakefile.olean.lock" in runs["frozen-shifted-index-2"]["stderr"]
assert [data[k]["idx"] for k in (
    "producer_prime_trace", "producer_shift_trace", "producer_writable_trace")] == [1, 1, 2]
assert data["producer_before"] == data["producer_after_match"] == data["producer_after_shift"]
path = ".lake/config/probe_dep/lakefile.olean"
trace = path + ".trace"
for p in (path, trace):
    assert data["producer_before"][p][0] != data["producer_after_writable_shift"][p][0]
print("frozen-index retained result: ok")
