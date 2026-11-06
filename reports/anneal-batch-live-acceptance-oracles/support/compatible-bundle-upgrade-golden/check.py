#!/usr/bin/env python3
"""Validate retained two-bundle Rust→Charon→Aeneas→Lean results offline."""
from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
WORK = HERE / "work"
R = json.loads((HERE / "results.json").read_text())
PINS = json.loads((HERE / "local-pin-inventory.json").read_text())


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inv(root: Path) -> dict:
    return {p.relative_to(root).as_posix(): {"bytes": p.stat().st_size, "sha256": sha(p)}
            for p in sorted(root.rglob("*")) if p.is_file()}


assert R["schema"] == 1
assert set(R["bundles"]) == set(PINS["bundles"]) == {"june1", "june3"}
assert set(R["cases"]) == {f"{b}-{v}" for b in R["bundles"] for v in ("base", "changed")}
assert PINS["f03_later_than_4_30_available"] is False
assert len(R["commands"]) == 52
assert sum(c["exit"] != 0 for c in R["commands"]) == 6
assert all(c["exit"] == 0 for c in R["commands"] if not
           (c["label"].endswith(":wrong-claim") or c["label"] in R["cross_pair"]))

for bundle, pin in PINS["bundles"].items():
    subject = R["bundles"][bundle]
    assert subject["aeneas_commit"] == pin["aeneas_source_commit"]
    assert subject["charon_pin"] == pin["charon_source_pin"]
    assert subject["rust_toolchain"] == pin["rust_toolchain"]
    for name in ("aeneas", "charon"):
        assert subject["binary_sha256"][name] == pin[name]["sha256"]
    assert subject["binary_sha256"]["charon-driver"] == pin["charon_driver"]["sha256"]
    assert subject["rustc_sha256"] == pin["rustc"]["sha256"]
    assert subject["cargo_sha256"] == pin["cargo"]["sha256"]
    assert subject["aeneas_olean_sha256"] == pin["aeneas_olean"]["sha256"]
    assert subject["lean_sha256"] == PINS["lean_pins"]["leanprover--lean4---v4.30.0-rc2"]["lean"]["sha256"]

for key, case in R["cases"].items():
    base = WORK / key
    crate = base / "crate"
    expected_version = "0.1.208" if case["bundle"] == "june1" else "0.1.210"
    assert case["charon_version"] == expected_version
    assert sha(crate / "src/lib.rs") == case["source_sha256"]
    assert sha(base / "current.llbc") == case["llbc_sha256"]
    assert json.loads((base / "current.llbc").read_text())["has_errors"] is False
    assert {"inc", "twice", "choose"} <= set(case["llbc_function_names"])
    assert inv(base / "generated") == case["generated"]
    assert inv(base / "consumer") == case["consumer"]
    assert set(case["generated"]) == {"Current.lean", "Types.lean", "Funs.lean"}
    assert case["proof_exit"] == 0 and case["wrong_claim_exit"] != 0
    assert case["missing_obligations_exit"] == 0
    assert case["admitted_exit"] == 0 and case["admitted_has_sorryAx"] is True
    proof_lines = [json.loads(line) for line in case["proof_stdout"].splitlines()]
    assert len(proof_lines) == 3
    for name, diagnostic in zip(("obl_inc", "obl_twice", "obl_choose"), proof_lines):
        assert diagnostic["severity"] == "information"
        assert diagnostic["data"] == f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
    assert len(re.findall(r"^theorem\s+obl_", (base / "consumer/Proof.lean").read_text(), re.M)) == 3
    assert len(re.findall(r"^theorem\s+obl_", (base / "consumer/Missing.lean").read_text(), re.M)) == 1
    assert "sorry" in (base / "consumer/Admitted.lean").read_text()
    assert not (base / "target").exists()
    assert 0 < case["target_bytes_before_cleanup"] < 50_000_000

for variant in ("base", "changed"):
    old = R["cases"]["june1-" + variant]
    new = R["cases"]["june3-" + variant]
    compare = R["comparisons"][variant]
    assert compare["same_rust_source_sha256"] is True
    assert old["source_sha256"] == new["source_sha256"]
    assert compare["raw_llbc_equal"] is False and old["llbc_sha256"] != new["llbc_sha256"]
    assert compare["generated_file_names_equal"] is True
    assert compare["generated_file_sha256_equal"] is True
    assert old["generated"] == new["generated"]
for bundle in ("june1", "june3"):
    base = R["cases"][bundle + "-base"]
    changed = R["cases"][bundle + "-changed"]
    assert base["source_sha256"] != changed["source_sha256"]
    assert base["generated"]["Funs.lean"]["sha256"] != changed["generated"]["Funs.lean"]["sha256"]
    stale = R["freshness_controls"][bundle]
    assert stale["stale_batch_exit"] == 0 and stale["source_identity_gate_rejects"] is True
    assert stale["old_import_source_sha256"] == base["source_sha256"]
    assert stale["current_source_sha256"] == changed["source_sha256"]
    default = R["parallel_option"][bundle]
    assert default["two_defaults_equal"] is True and default["default_equals_sequential"] is True
    assert len(default["default_runs"]) == 2
    for index, output in enumerate(default["default_runs"], 1):
        assert output == base["generated"]
        assert inv(WORK / f"{bundle}-default-parallel-{index}") == output

assert set(R["cross_pair"]) == {"june1-on-june3-llbc", "june3-on-june1-llbc"}
for key, cell in R["cross_pair"].items():
    assert cell["exit"] != 0 and cell["inventory"] == {}
    message = (cell["stdout"] + cell["stderr"]).lower()
    assert "incompatible version of charon" in message
    assert "0.1.208" in message and "0.1.210" in message
    assert inv(WORK / key) == {}

summary = {"case_count": len(R["cases"]), "command_count": len(R["commands"]),
           "cross_pair_rejections": len(R["cross_pair"]),
           "paired_generated_bytes_equal": {v: R["comparisons"][v]["generated_file_sha256_equal"]
                                            for v in ("base", "changed")},
           "raw_llbc_equal": {v: R["comparisons"][v]["raw_llbc_equal"] for v in ("base", "changed")},
           "default_parallel_equals_sequential": {b: R["parallel_option"][b]["default_equals_sequential"]
                                                  for b in ("june1", "june3")},
           "stale_old_import_batch_passes": {b: R["freshness_controls"][b]["stale_batch_exit"] == 0
                                             for b in ("june1", "june3")},
           "accepted_axioms": ["propext", "Classical.choice", "Quot.sound"],
           "f03_later_than_4_30_available": False}
(HERE / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
print("PASS: two cached compatible bundles, four fresh goldens, six negative commands, two cross-pair rejections")
