#!/usr/bin/env python3
"""Offline evidence check for the R491 helper probe; does not execute leantar."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
x = json.loads((ROOT / "results.json").read_text())
assert x["schema"] == 1 and x["status"] == "completed"
assert len(x["calls"]) == 19 and len(x["extractions"]) == 9
assert {p: sha(ROOT / "fixture" / p) for p in ("build.trace", "artifact.txt")} == x["fixture_sha256"]
assert (ROOT / "fixture/build.trace").read_bytes() == b"123456789"
assert (ROOT / "fixture/artifact.txt").read_bytes() == b"Anneal R491 helper comparison\n"
versions = ("0.1.16", "0.1.19", "0.1.20")
labels = {"0.1.16": "016", "0.1.19": "019", "0.1.20": "020"}
for version in versions:
    row = next(y for y in x["calls"] if y["label"] == f"version-{labels[version]}")
    assert row["returncode"] == 0 and row["stdout_utf8"].strip() == f"leantar {version}"
for producer in versions:
    archive = ROOT / "work" / f"by-{labels[producer]}.ltar"
    info = x["archives"][producer]
    assert info == {"sha256": sha(archive), "size": archive.stat().st_size, "magic": "LTAR"}
    assert info["sha256"] == "be5e94042c7f4c245ffeb92c4266c6e15f136539dbd5d3451906e4dd03f94f16"
    for consumer in versions:
        row = next(y for y in x["extractions"] if y["producer"] == producer and y["consumer"] == consumer)
        assert row["returncode"] == 0 and row["files_sha256"] == x["fixture_sha256"]
        dest = ROOT / "work" / f"unpack-{labels[producer]}-with-{labels[consumer]}" / "fixture"
        assert {p: sha(dest / p) for p in ("build.trace", "artifact.txt")} == x["fixture_sha256"]
stripped = ROOT / "work/stripped-020.ltar"
assert stripped.read_bytes()[:4] == b"LTR4"
assert x["stripped"]["archive"] == {"sha256": sha(stripped), "size": stripped.stat().st_size, "magic": "LTR4"}
assert x["stripped"]["archive"]["sha256"] == "f95e6fe5f7a351259f87af14838bebecc33fbd2789bbbb94d4e42971f1f1cd52"
assert next(y for y in x["calls"] if y["label"] == "pack-stripped-020")["returncode"] == 0
for consumer in ("0.1.16", "0.1.19"):
    assert x["stripped"][consumer] == {"returncode": 1, "output_files": []}
    dest = ROOT / "work" / f"unpack-stripped-with-{labels[consumer]}"
    assert not list(dest.rglob("*"))
    call = next(y for y in x["calls"] if y["label"] == f"unpack-stripped-{labels[consumer]}")
    assert call["returncode"] == 1 and "bad .ltar file" in call["stderr_utf8"]
new = x["stripped"]["0.1.20"]
assert new["returncode"] == 0 and new["artifact_sha256"] == x["fixture_sha256"]["artifact.txt"]
assert next(y for y in x["calls"] if y["label"] == "unpack-stripped-020")["returncode"] == 0
assert new["trace_utf8"] == '{"depHash":"00000000075bcd15","schemaVersion":"2025-09-10"}'
dest = ROOT / "work/unpack-stripped-with-020/fixture"
assert sha(dest / "artifact.txt") == new["artifact_sha256"]
assert sha(dest / "build.trace") == new["trace_sha256"]
assert all(c["admission"]["reclaimable_fraction"] > .20 and c["admission"]["disk_free_bytes"] > 10*1024**3 for c in x["calls"])
assert round(100 * min(c["admission"]["reclaimable_fraction"] for c in x["calls"]), 2) == 25.37
assert min(c["admission"]["disk_free_bytes"] for c in x["calls"]) == 15403745280
print("PASS: exact archived bytes, 3x3 extracts, stripped-format contrast, and admission records")
