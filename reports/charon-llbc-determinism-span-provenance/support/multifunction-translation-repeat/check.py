#!/usr/bin/env python3
"""Read-only consistency check of the retained I148 corpus run."""
import hashlib
import json
from pathlib import Path
import re

from probe import ROOT, FIX, ART, LOG, normalized

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    r = json.loads((ROOT / "results.json").read_text())
    meta = json.loads((ROOT.parent / "REPORT.json").read_text())
    assert r["schema"] == 1
    assert meta["observed_at"] == "2026-09-29"
    subjects = {x["name"]: x["identity"] for x in meta["subjects"]}
    assert len(subjects) == len(meta["subjects"]) == 5
    corpus = subjects["I148 five-function Rust corpus"]
    assert corpus == {"fixture_source_sha256": sha(FIX / "src/lib.rs"),
                      "fixture_manifest_sha256": sha(FIX / "Cargo.toml"),
                      "fixture_lock_sha256": sha(FIX / "Cargo.lock")}
    assert subjects["Five retained extraction and generation runs"] == {
        "probe_sha256": sha(ROOT / "probe.py"), "checker_sha256": sha(ROOT / "check.py"),
        "results_sha256": sha(ROOT / "results.json")}
    tool_subjects = ("Pinned Charon/Cargo/rustc toolchain", "Pinned Aeneas CLI", "Lean v4.30.0-rc2")
    assert all(name in subjects for name in tool_subjects)
    assert subjects[tool_subjects[0]]["charon_binary_sha256"] == r["tools"]["charon"]
    assert subjects[tool_subjects[0]]["cargo_binary_sha256"] == r["tools"]["cargo"]
    assert subjects[tool_subjects[0]]["rustc_binary_sha256"] == r["tools"]["rustc"]
    assert subjects[tool_subjects[1]]["executable_sha256"] == r["tools"]["aeneas"]
    assert subjects[tool_subjects[2]]["executable_sha256"] == r["tools"]["lean"]
    assert {str(p.relative_to(FIX)): sha(p) for p in FIX.rglob("*") if p.is_file()} == r["source"]
    runs = {x["label"]: x for x in r["runs"]}
    expected_labels = ({f"charon-seq-{n}" for n in (1, 2, 3)} |
                       {f"charon-par-{n}" for n in (1, 2)} |
                       {f"aeneas-{n}" for n in range(1, 6)} |
                       {"lean-Probe-Types", "lean-Probe-Funs", "lean-Probe", "lean-check"})
    assert len(r["runs"]) == len(runs) == 14 and set(runs) == expected_labels
    assert all(x["exit"] == 0 for x in runs.values())
    for x in runs.values():
        label = x["label"]
        assert sha(LOG / (label + ".stdout")) == x["stdout_sha256"]
        assert sha(LOG / (label + ".stderr")) == x["stderr_sha256"]
        assert x["end_monotonic"] > x["start_monotonic"]
    for n in (1, 2, 3):
        x = runs[f"charon-seq-{n}"]
        assert x["argv"][5].endswith("/artifacts/same.llbc")
    for n in (1, 2):
        x = runs[f"charon-par-{n}"]
        assert x["argv"][5].endswith(f"/artifacts/par-{n}.llbc")
    for label in (*[f"charon-seq-{n}" for n in (1, 2, 3)],
                  *[f"charon-par-{n}" for n in (1, 2)]):
        x = runs[label]
        assert x["argv"][1:5] == ["cargo", "--preset", "aeneas", "--dest-file"]
        assert x["argv"][6:] == ["--", "--manifest-path", x["cwd"] + "/Cargo.toml",
                                 "--lib", "--offline", "--locked", "-j", "1"]
    for n in range(1, 6):
        x = runs[f"aeneas-{n}"]
        assert x["argv"][1:7] == ["-backend", "lean", "-no-progress-bar",
                                   "-sequential", "-split-files", "-gen-lib-entry"]
        assert x["argv"][-1].endswith(f"/artifacts/input-{n}/probe.llbc")
        assert x["argv"][-2].endswith(f"/artifacts/gen-{n}")
    a, b = runs["charon-par-1"], runs["charon-par-2"]
    assert max(a["start_monotonic"], b["start_monotonic"]) < min(a["end_monotonic"], b["end_monotonic"])
    paths = [ART / f"seq-{n}.llbc" for n in (1, 2, 3)] + [ART / f"par-{n}.llbc" for n in (1, 2)]
    docs = []
    for p, row in zip(paths, r["llbc"]):
        assert p.name == row["file"] and p.stat().st_size == row["bytes"] and sha(p) == row["sha256"]
        doc = json.loads(p.read_bytes())
        assert doc["has_errors"] is False
        names = doc["translated"]["short_names"]
        assert len(names) == row["short_names_count"] and [x["key"] for x in names] == row["short_names_order"]
        assert len({json.dumps(x["key"], sort_keys=True) for x in names}) == len(names)
        docs.append(doc)
    assert len({sha(p) for p in paths}) == 5
    assert all(normalized(d) == normalized(docs[0]) for d in docs)
    assert r["all_core_llbc_equal_after_only_dest_and_short_name_order"] is True
    inventories = []
    for n, p in enumerate(paths, 1):
        assert sha(ART / f"input-{n}/probe.llbc") == sha(p)
        d = ART / f"gen-{n}"
        inventories.append({str(x.relative_to(d)): sha(x) for x in d.rglob("*") if x.is_file()})
    assert all(x == inventories[0] for x in inventories)
    assert inventories[0] == r["generated_inventory"]
    assert set(inventories[0]) == {"Types.lean", "Funs.lean", "Probe.lean"}
    lean = (ART / "gen-1/Funs.lean").read_text()
    decls = [s.strip() for s in lean.splitlines() if re.match(r"^\s*(?:def|theorem|axiom|opaque|partial def)\s", s)]
    assert decls == r["lean_declarations"] and len(decls) == 5
    assert r["lean_obligation_markers"] == {s: lean.count(s) for s in ("sorry", "axiom", "theorem", "decreasing_by")}
    check = (LOG / "lean-check.stdout").read_text()
    assert all(f"i148_corpus.{name}" in check for name in ("add_one", "choose", "pair_sum", "make_pair", "combine"))
    assert "[propext, Classical.choice, Quot.sound]" in check
    print("PASS: five error-free LLBC runs; recorded invocation overlap; core JSON and generated Lean equality; direct Lean acceptance")

if __name__ == "__main__":
    main()
