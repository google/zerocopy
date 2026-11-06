#!/usr/bin/env python3
"""Read-only check of every retained LLBC, pairwise leaf and negative control."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
META = json.loads((HERE.parent / "REPORT.json").read_text())
RECORD = json.loads((HERE / "comparison.json").read_text())
SOURCE = json.loads((HERE / "source-results.json").read_text())

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def pointer(path, segment):
    return path + "/" + str(segment).replace("~", "~0").replace("/", "~1")

def diff(left, right, path=""):
    if type(left) is not type(right):
        return [{"path": path or "/", "left": left, "right": right}]
    if isinstance(left, dict):
        out = []
        for key in sorted(set(left) | set(right)):
            p = pointer(path, key)
            if key not in left: out.append({"path": p, "left_missing": True, "right": right[key]})
            elif key not in right: out.append({"path": p, "left": left[key], "right_missing": True})
            else: out.extend(diff(left[key], right[key], p))
        return out
    if isinstance(left, list):
        out = []
        for i in range(max(len(left), len(right))):
            p = pointer(path, i)
            if i >= len(left): out.append({"path": p, "left_missing": True, "right": right[i]})
            elif i >= len(right): out.append({"path": p, "left": left[i], "right_missing": True})
            else: out.extend(diff(left[i], right[i], p))
        return out
    return [] if left == right else [{"path": path or "/", "left": left, "right": right}]

def keyed_short_names(document):
    out = {}
    for entry in document["translated"]["short_names"]:
        key = json.dumps(entry["key"], sort_keys=True, separators=(",", ":"))
        assert key not in out
        out[key] = entry["value"]
    return out

assert RECORD["status"] == "completed"
identity = META["subjects"][1]["identity"]
assert identity["source_results_sha256"] == RECORD["source_results_sha256"] == sha(HERE / "source-results.json")
assert identity["compare_sha256"] == sha(HERE / "compare.py")
assert identity["comparison_sha256"] == sha(HERE / "comparison.json")
limits = RECORD["limits"]
assert limits == {"max_rss_bytes": 64 * 1024**2, "max_seconds": 5.0, "min_reclaimable_percent": 20.0}
assert RECORD["elapsed_seconds"] <= 5.0 and RECORD["peak_rss_bytes"] <= 64 * 1024**2
assert len(RECORD["samples"]) == 31
assert RECORD["samples"][0]["label"] == "preflight-before-input"
assert all(s["reclaimable_percent"] >= 20.0 and s["max_rss_bytes"] <= 64 * 1024**2 and
           s["elapsed_seconds"] <= 5.0 and s["physical_bytes"] == 8 * 1024**3 for s in RECORD["samples"])
expected = {}
for cell in SOURCE["cells"]:
    inc = cell["incremental"]
    assert inc in (0, 1)
    for state, run in cell["oracle"].items():
        label = f"inc{inc}-oracle-{state}"
        assert run["label"] == label
        expected[label] = run["output"]["sha256"]
    for phase in cell["phases"]:
        for name, run in phase["runs"].items():
            label = f"inc{inc}-{phase['name']}-{name}"
            assert run["label"] == label
            expected[label] = run["output"]["sha256"]
assert len(expected) == 16 and expected == RECORD["artifact_sha256"]
assert {p.stem for p in (HERE / "artifacts").glob("*.llbc")} == set(expected)
documents = {}
for label, digest in expected.items():
    path = HERE / "artifacts" / f"{label}.llbc"
    assert sha(path) == digest
    documents[label] = json.loads(path.read_text())
    assert documents[label]["has_errors"] is False
    assert documents[label]["translated"]["crate_name"] == "warm_probe"

pairs = RECORD["pairs"]
assert len(pairs) == 12
for inc in (0, 1):
    for state in ("baseline", "edited", "reverted"):
        for name in ("A", "B"):
            left = f"inc{inc}-{state}-{name}"
            right = f"inc{inc}-oracle-{'edited' if state == 'edited' and name == 'A' else 'baseline'}"
            pair = next(p for p in pairs if p["left"] == left)
            assert pair["right"] == right and pair["left_sha256"] == expected[left]
            assert pair["right_sha256"] == expected[right]
            differences = diff(documents[left], documents[right])
            assert pair["differences"] == differences and pair["difference_count"] == len(differences)
            assert len(differences) > 2
            for item in differences:
                path = item["path"]
                assert path in ("/translated/options/dest_file", "/translated/files/1/name/Local") or path.startswith("/translated/short_names/")
            assert {"/translated/options/dest_file", "/translated/files/1/name/Local"} <= {x["path"] for x in differences}
            assert keyed_short_names(documents[left]) == keyed_short_names(documents[right])
assert len({p["left"] for p in pairs}) == 12

negatives = RECORD["negative_controls"]
assert len(negatives) == 2
literal = "/translated/fun_decls/0/body/Structured/body/statements/2/kind/Call/args/1/Const/kind/Literal/Scalar/Unsigned/1"
for inc in (0, 1):
    left, right = f"inc{inc}-oracle-edited", f"inc{inc}-oracle-baseline"
    item = next(n for n in negatives if n["left"] == left)
    assert item["right"] == right and item["left_sha256"] == expected[left]
    assert item["right_sha256"] == expected[right]
    differences = diff(documents[left], documents[right])
    assert item["differences"] == differences and item["difference_count"] == len(differences)
    by_path = {d["path"]: d for d in differences}
    assert by_path[literal]["left"] == "2" and by_path[literal]["right"] == "1"
    assert "wrapping_add(2)" in by_path["/translated/files/0/contents"]["left"]
    assert "wrapping_add(1)" in by_path["/translated/files/0/contents"]["right"]
print("PASS: 16 source hashes, 12 exhaustive oracle pairs, keyed names, two edit controls and resource gates")
