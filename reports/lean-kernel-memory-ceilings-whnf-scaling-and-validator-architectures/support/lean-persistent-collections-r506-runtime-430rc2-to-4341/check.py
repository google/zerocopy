#!/usr/bin/env python3
"""Offline evidence check; optional exact-source recheck needs two source roots."""
import argparse
import difflib
import hashlib
import json
from pathlib import Path
import statistics

ROOT = Path(__file__).resolve().parent.parent
R = json.loads((ROOT / "results.json").read_text())
S = json.loads((ROOT / "source-observation.json").read_text())
MODES = ("array-retained", "array-discarded", "map-retained", "map-discarded")

def sha(data): return hashlib.sha256(data).hexdigest()
def blob(data): return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
def cell(v, m, n, r):
    x = [c for c in R["cells"] if (c["version"], c["mode"], c["n"], c["repeat"]) == (v,m,n,r)]
    assert len(x) == 1
    return x[0]

assert sha((ROOT / "fixture" / "Probe.lean").read_bytes()) == R["fixture_sha256"]
assert sha((ROOT / "source-diff.patch").read_bytes()) == S["patch_sha256"]
assert S["PersistentArray.lean"]["old_blob"] == "516fb0ce50651c1ef39cccdca48663335dac7790"
assert S["PersistentHashMap.lean"]["old_blob"] == "f963f3a3f3cfc8c262e14bfcf56d21fc3a55442d"
assert S["PersistentArray.lean"]["new_blob"] == "e252526851a5eb4bb988d67dd8854b90a2cf970c"
assert S["PersistentHashMap.lean"]["new_blob"] == "e4d81c5cc33ac8d6e67ad217402ec8688b11486e"
assert len(R["cells"]) == 48
assert {(c["version"],c["mode"],c["n"],c["repeat"]) for c in R["cells"]} == {
    (v,m,n,r) for v in ("old","new") for m in MODES for n in (8192,65536) for r in range(3)}
assert R["tools"]["old"]["lean_version"] == (
    "Lean (version 4.30.0-rc2, arm64-apple-darwin24.6.0, "
    "commit 3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc, Release)")
assert R["tools"]["new"]["lean_version"] == (
    "Lean (version 4.34.1, arm64-apple-darwin24.6.0, "
    "commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)")
assert R["tools"]["old"]["lean_sha256"] == "b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997"
assert R["tools"]["new"]["lean_sha256"] == "1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554"
for c in R["cells"]:
    assert c["version"] in ("old", "new")
    assert c["command"] == [R["tools"][c["version"]]["executable"], "--run", c["command"][2], c["mode"], str(c["n"])]
    assert Path(c["command"][2]).name == "Probe.lean"
    assert c["exit_code"] == 0 and c["terminated"] is None and c["elapsed_s"] < 30
    assert 0 < c["peak_sampled_rss_bytes"] < 1_073_741_824 and c["rss_polls"] > 0
    a = c["admission"]
    assert a["reclaimable_percent"] > 20 and a["disk_free_bytes"] > 1_073_741_824 and a["owned_raw_bytes"] < 100_000_000
    stem = f"{c['version']}--{c['mode']}--n{c['n']}--r{c['repeat']}"
    for stream in ("stdout","stderr"):
        data = (ROOT / "raw" / f"{stem}.{stream}").read_bytes()
        assert sha(data) == c[stream+"_sha256"] and len(data) == c[stream+"_bytes"]
    n = c["n"]
    expected = {
        "array-retained": f"array-retained (0, {n-1}, {n}, {2*n-1})\n",
        "array-discarded": f"array-discarded ({n}, {2*n-1})\n",
        "map-retained": f"map-retained (some 0, some {n-1}, some {n}, some {2*n-1})\n",
        "map-discarded": f"map-discarded (some {n}, some {2*n-1})\n",
    }[c["mode"]]
    assert (ROOT / "raw" / f"{stem}.stdout").read_text() == expected
    assert (ROOT / "raw" / f"{stem}.stderr").read_bytes() == b""

p = argparse.ArgumentParser()
p.add_argument("--old-source-root", type=Path)
p.add_argument("--new-source-root", type=Path)
args = p.parse_args()
assert bool(args.old_source_root) == bool(args.new_source_root)
if args.old_source_root:
    diff = []
    def source_file(root, name):
        # Git trees use src/Lean; release toolchains bundle the same bytes under src/lean/Lean.
        candidates = (root / "src/Lean/Data" / name, root / "src/lean/Lean/Data" / name)
        found = [p for p in candidates if p.is_file()]
        assert len(found) == 1, (root, name, found)
        return found[0]
    for name in ("PersistentArray.lean","PersistentHashMap.lean"):
        x = source_file(args.old_source_root, name).read_bytes()
        y = source_file(args.new_source_root, name).read_bytes()
        assert sha(x) == S[name]["old_sha256"] and blob(x) == S[name]["old_blob"]
        assert sha(y) == S[name]["new_sha256"] and blob(y) == S[name]["new_blob"]
        diff.extend(difflib.unified_diff(x.decode().splitlines(keepends=True),y.decode().splitlines(keepends=True),
                    fromfile=f"v4.30.0-rc2/Lean/Data/{name}",tofile=f"v4.34.1/Lean/Data/{name}"))
    assert "".join(diff).encode() == (ROOT / "source-diff.patch").read_bytes()

for n in (8192,65536):
    for v in ("old","new"):
        med = {m: statistics.median(cell(v,m,n,r)["peak_sampled_rss_bytes"] for r in range(3)) for m in MODES}
        assert med["map-retained"] > 0 and med["map-discarded"] > 0
print("PASS: 48 batch cells, retained/discarded semantics, source-diff hash, RSS/resource bounds" + (", exact source blobs" if args.old_source_root else ""))
