#!/usr/bin/env python3
"""Offline validation of R43's retained commands, inputs, outputs, and Lake trace oracle."""
import hashlib
import json
from pathlib import Path

here = Path(__file__).resolve().parent
work = here / "work"
r42 = here.parents[2] / "reports/anneal-3730-charon-warm-noop-byte-diff-2026-09-29/support"
r = json.loads((here / "results.json").read_text())
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert r["schema"] == 1 and len(r["commands"]) == 40
assert set(r["cases"]) == {f"run-{i}" for i in range(1, 6)}
assert len(r["incremental"]) == 5
assert r["r42_report_sha256"] == sha(r42.parent / "REPORT.md")
for path, digest in r["tools"].items():
    assert sha(path) == digest
for command in r["commands"]:
    assert command["exit"] == 0 and command["elapsed_ms"] > 0
    assert sha(here / command["stdout"]) == command["stdout_sha256"]
    assert sha(here / command["stderr"]) == command["stderr_sha256"]

generated_names = ("Types.lean", "FunsExternal_Template.lean", "Funs.lean", "Probe.lean")
for i in range(1, 6):
    label = f"run-{i}"
    cell = r["cases"][label]
    base = work / label
    assert cell["r42_llbc_sha256"] == sha(r42 / "artifacts" / f"{label}.llbc")
    assert cell["copied_llbc_sha256"] == sha(base / "probe.llbc")
    assert cell["r42_llbc_sha256"] == cell["copied_llbc_sha256"]
    for name in generated_names:
        assert cell["generated"][name]["sha256"] == sha(base / "generated" / name)
        assert cell["generated"][name]["bytes"] == (base / "generated" / name).stat().st_size
    direct = cell["direct"]
    assert len(direct["commands"]) == 5
    for name, rec in direct["source"].items():
        assert rec["sha256"] == sha(base / "direct-consumer" / name)
    for name, rec in direct["olean"].items():
        assert rec["sha256"] == sha(base / "direct-consumer" / name)
    assert "r37u0.combined (x : Aeneas.Std.U32)" in direct["proof_output"]
    assert "depends on axioms: [dep_a.dep_a, dep_b.dep_b]" in direct["proof_output"]
    assert "sorryAx" not in direct["proof_output"]
    lake = cell["lake_fresh"]
    assert len(lake["own_job_lines"]) == 4
    assert all("Built Probe" in line for line in lake["own_job_lines"])
    for name, rec in lake["artifacts"].items():
        assert rec["sha256"] == sha(base / "lake-consumer/.lake/build" / name)
    assert not (base / "lake-consumer/.lake/packages").exists()

assert r["comparison"]["raw_llbc_distinct"] == 5
assert all(len(groups) == 1 for groups in r["comparison"]["generated_hash_groups"].values())
assert all(len(groups) == 1 for groups in r["comparison"]["decl_groups"].values())
for name in generated_names:
    assert {cell["generated"][name]["sha256"] for cell in r["cases"].values()} == \
        set(r["comparison"]["generated_hash_groups"][name])
for name in r["cases"]["run-1"]["direct"]["olean"]:
    assert len({cell["direct"]["olean"][name]["sha256"] for cell in r["cases"].values()}) == 1

base_artifacts = r["cases"]["run-1"]["lake_fresh"]["artifacts"]
for idx, item in enumerate(r["incremental"]):
    assert item["input"] == ("no-write" if idx == 0 else f"run-{idx+1}")
    assert len(item["lake"]["own_job_lines"]) == 4
    assert all("Replayed Probe" in line for line in item["lake"]["own_job_lines"])
    assert item["lake"]["artifacts"] == base_artifacts
    if idx:
        for name, rec in item["source_hashes"].items():
            assert rec["sha256"] == sha(work / f"run-{idx+1}/lake-consumer" / name)

print("R43 retained-result checks passed: five Aeneas/Lean/Lake variants and five Lake replay controls")
