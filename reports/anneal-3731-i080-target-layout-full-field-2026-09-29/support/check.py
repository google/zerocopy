#!/usr/bin/env python3
"""Read-only verification of the 16-artifact, 24-pair decoded-field matrix."""
import copy
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

def label(layout, inc, phase, root):
    return f"{layout.ljust(7, '_')}-inc{inc}/{phase}-{root}.llbc"

def keyed_names(doc):
    out = {}
    for entry in doc["translated"]["short_names"]:
        key = json.dumps(entry["key"], sort_keys=True, separators=(",", ":"))
        assert key not in out
        out[key] = entry["value"]
    return out

identity = META["subjects"][1]["identity"]
assert RECORD["status"] == "completed"
assert identity["source_results_sha256"] == RECORD["source_results_sha256"] == sha(HERE / "source-results.json")
assert identity["compare_sha256"] == sha(HERE / "compare.py")
assert identity["comparison_sha256"] == sha(HERE / "comparison.json")
assert RECORD["limits"] == {"max_rss_bytes": 64 * 1024**2, "max_seconds": 5.0,
                            "min_reclaimable_percent": 20.0}
assert RECORD["elapsed_seconds"] <= 5.0 and RECORD["peak_rss_bytes"] <= 64 * 1024**2
assert len(RECORD["samples"]) == 44
assert RECORD["samples"][0]["label"] == "preflight-before-input"
assert all(s["reclaimable_percent"] > 20.0 and s["physical_bytes"] == 8 * 1024**3 and
           s["max_rss_bytes"] <= 64 * 1024**2 and s["elapsed_seconds"] <= 5.0 for s in RECORD["samples"])
assert [(c["layout"], c["incremental"]) for c in SOURCE["cells"]] == [
    ("private", 0), ("private", 1), ("shared", 0), ("shared", 1)]
expected = {}
for cell in SOURCE["cells"]:
    layout, inc = cell["layout"], cell["incremental"]
    assert [p["phase"] for p in cell["phases"]] == ["cold", "warm"]
    for phase in cell["phases"]:
        for root, run in phase["results"].items():
            assert root in ("A", "B")
            expected[label(layout, inc, phase["phase"], root)] = run["output"]["sha256"]
assert len(expected) == 16 and RECORD["artifact_sha256"] == expected
assert {p.relative_to(HERE / "artifacts").as_posix() for p in (HERE / "artifacts").rglob("*.llbc")} == set(expected)
docs = {}
for name, digest in expected.items():
    p = HERE / "artifacts" / name
    assert sha(p) == digest
    docs[name] = json.loads(p.read_text())
    assert docs[name]["translated"]["crate_name"] == "warm_probe"
    assert docs[name]["has_errors"] is False

specs = []
for layout in ("private", "shared"):
    for inc in (0, 1):
        for root in ("A", "B"):
            specs.append(("warm_vs_cold", label(layout, inc, "warm", root), label(layout, inc, "cold", root)))
for inc in (0, 1):
    for phase in ("cold", "warm"):
        for root in ("A", "B"):
            specs.append(("shared_vs_private", label("shared", inc, phase, root),
                          label("private", inc, phase, root)))
for layout in ("private", "shared"):
    for phase in ("cold", "warm"):
        for root in ("A", "B"):
            specs.append(("inc1_vs_inc0", label(layout, 1, phase, root),
                          label(layout, 0, phase, root)))
assert len(specs) == len(RECORD["pairs"]) == 24
families = {
    "warm_vs_cold": {"/translated/options/dest_file"},
    "shared_vs_private": {"/translated/options/dest_file", "/translated/files/1/name/Local"},
    "inc1_vs_inc0": {"/translated/options/dest_file", "/translated/files/1/name/Local"}}
for record, (axis, left, right) in zip(RECORD["pairs"], specs):
    assert (record["axis"], record["left"], record["right"]) == (axis, left, right)
    assert (record["left_sha256"], record["right_sha256"]) == (expected[left], expected[right])
    differences = diff(docs[left], docs[right])
    assert record["differences"] == differences and record["difference_count"] == len(differences)
    paths = {x["path"] for x in differences}
    assert families[axis] <= paths
    assert all(p in families[axis] or p.startswith("/translated/short_names/") for p in paths)
    assert record["short_names_keyed_maps_equal"] is True
    assert keyed_names(docs[left]) == keyed_names(docs[right])
assert {axis: sum(p["difference_count"] for p in RECORD["pairs"] if p["axis"] == axis)
        for axis in families} == {"warm_vs_cold": 154, "shared_vs_private": 167, "inc1_vs_inc0": 158}

basis = docs[label("private", 0, "cold", "A")]
controls = RECORD["synthetic_negative_controls"]
assert [x["kind"] for x in controls] == ["crate_name", "function_body", "short_names_order"]
for control in controls:
    mutant = copy.deepcopy(basis)
    kind = control["kind"]
    if kind == "crate_name":
        mutant["translated"]["crate_name"] = "synthetic_other_crate"
        prefix = "/translated/crate_name"
    elif kind == "function_body":
        mutant["translated"]["fun_decls"][0]["body"] = "synthetic_changed_body"
        prefix = "/translated/fun_decls/0/body"
    else:
        names = mutant["translated"]["short_names"]
        names[0], names[1] = names[1], names[0]
        prefix = "/translated/short_names/"
    differences = diff(basis, mutant)
    assert control["differences"] == differences and control["difference_count"] == len(differences)
    assert any(x["path"].startswith(prefix) for x in differences)
print("PASS: 16 source hashes, 24 exhaustive matrix pairs, keyed names, three synthetic controls and guards")
