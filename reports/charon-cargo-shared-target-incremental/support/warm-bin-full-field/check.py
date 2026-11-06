#!/usr/bin/env python3
"""Read-only verification of every retained warm-bin decoded difference."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
META = json.loads((HERE.parent / "REPORT.json").read_text())
RECORD = json.loads((HERE / "comparison.json").read_text())
SOURCE = json.loads((HERE / "source-results.json").read_text())

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def ptr(path, key): return path + "/" + str(key).replace("~", "~0").replace("/", "~1")

def diff(a, b, path=""):
    if type(a) is not type(b): return [{"path": path or "/", "left": a, "right": b}]
    if isinstance(a, dict):
        out = []
        for key in sorted(set(a) | set(b)):
            p = ptr(path, key)
            if key not in a: out.append({"path": p, "left_missing": True, "right": b[key]})
            elif key not in b: out.append({"path": p, "left": a[key], "right_missing": True})
            else: out.extend(diff(a[key], b[key], p))
        return out
    if isinstance(a, list):
        out = []
        for i in range(max(len(a), len(b))):
            p = ptr(path, i)
            if i >= len(a): out.append({"path": p, "left_missing": True, "right": b[i]})
            elif i >= len(b): out.append({"path": p, "left": a[i], "right_missing": True})
            else: out.extend(diff(a[i], b[i], p))
        return out
    return [] if a == b else [{"path": path or "/", "left": a, "right": b}]

def order_diff(a, b, path=""):
    if type(a) is not type(b): return []
    if isinstance(a, dict):
        out = ([{"path": path or "/", "left_keys": list(a), "right_keys": list(b)}]
               if list(a) != list(b) else [])
        for key in a.keys() & b.keys(): out.extend(order_diff(a[key], b[key], ptr(path, key)))
        return out
    if isinstance(a, list):
        out = []
        for i in range(min(len(a), len(b))): out.extend(order_diff(a[i], b[i], ptr(path, i)))
        return out
    return []

def keyed(doc):
    out = {}
    for entry in doc["translated"]["short_names"]:
        key = json.dumps(entry["key"], sort_keys=True, separators=(",", ":"))
        assert key not in out
        out[key] = entry["value"]
    return out

assert RECORD["status"] == "completed"
identity = META["subjects"][1]["identity"]
assert identity["source_results_sha256"] == RECORD["source_results_sha256"] == sha(HERE / "source-results.json")
assert identity["compare_sha256"] == sha(HERE / "compare.py")
assert identity["comparison_sha256"] == sha(HERE / "comparison.json")
assert RECORD["limits"] == {"max_rss_bytes": 64 * 1024**2, "max_seconds": 5.0,
                            "min_reclaimable_percent": 20.0}
assert RECORD["elapsed_seconds"] <= 5 and RECORD["peak_rss_bytes"] <= 64 * 1024**2
assert len(RECORD["samples"]) == 4 and RECORD["samples"][0]["label"] == "preflight-before-input"
assert all(s["reclaimable_percent"] >= 20 and s["physical_bytes"] == 8 * 1024**3 and
           s["max_rss_bytes"] <= 64 * 1024**2 and s["elapsed_seconds"] <= 5 for s in RECORD["samples"])
runs = {r["label"]: r for r in SOURCE["runs"]}
assert set(runs) == {"baseline", "warm_repeat"}
assert set(RECORD["artifact_sha256"]) == set(runs)
docs = {}
for label in runs:
    path = HERE / "artifacts" / f"{label}.llbc"
    assert sha(path) == runs[label]["dest_sha256"] == RECORD["artifact_sha256"][label]
    raw = path.read_bytes()
    docs[label] = json.loads(raw)
    assert json.dumps(docs[label], separators=(",", ":"), ensure_ascii=False).encode() == raw
    assert RECORD["roundtrip_exact"][label] is True
    assert docs[label]["translated"]["crate_name"] == "subject_matrix_cli"
    assert docs[label]["has_errors"] is False
a, b = docs["baseline"], docs["warm_repeat"]
differences = diff(a, b)
assert RECORD["differences"] == differences and RECORD["difference_count"] == len(differences) == 30
paths = [d["path"] for d in differences]
assert paths.count("/translated/options/dest_file") == 1
assert sum(p.startswith("/translated/short_names/") for p in paths) == 29
assert all(p == "/translated/options/dest_file" or p.startswith("/translated/short_names/") for p in paths)
assert RECORD["object_key_order_differences"] == order_diff(a, b)
assert len(RECORD["object_key_order_differences"]) == 7
assert all(x["path"].startswith("/translated/short_names/") for x in RECORD["object_key_order_differences"])
assert RECORD["short_names_keyed_maps_equal"] is True and keyed(a) == keyed(b)
left, right = a["translated"]["short_names"], b["translated"]["short_names"]
assert len(left) == len(right) == 15
assert [i for i, (x, y) in enumerate(zip(left, right)) if x != y] == [3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14]
print("PASS: two source hashes, exact JSON round trips, 30 exhaustive differences, keyed names and guards")
