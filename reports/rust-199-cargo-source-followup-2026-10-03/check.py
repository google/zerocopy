#!/usr/bin/env python3
"""Offline narrow checks for the Rust 1.98.1 → 1.99 Cargo source supplement."""
import argparse
import json
import csv
import hashlib
import io
import subprocess
from pathlib import Path

args_parser = argparse.ArgumentParser(description=__doc__)
args_parser.add_argument(
    "--reference-root", required=True, type=Path,
    help="Git checkout containing the pinned reference commit",
)
args = args_parser.parse_args()
root = Path(__file__).resolve().parent
metadata = json.loads((root / "REPORT.json").read_text())
assert set(metadata) == {"topics", "subjects", "observed_at"}
assert metadata["observed_at"] == "2026-10-03"
assert len(metadata["topics"]) == len(set(metadata["topics"])) and metadata["topics"]
assert metadata["subjects"]
assert all(set(subject) == {"name", "identity"} for subject in metadata["subjects"])
provenance = json.loads((root / "support" / "provenance.json").read_text())
assert provenance["source_result"] == "two_narrow_exact_source_deltas"
assert provenance["runtime_result"] == "unexecuted"
assert provenance["matrix_effect"] == "applied_by_integrated_v91_coverage_matrix"
for name, digest in provenance["evidence_sha256"].items():
    assert hashlib.sha256((root / name).read_bytes()).hexdigest() == digest, name
tags = (root / "rust-199-tags.txt").read_text()
assert "daa8d75bc715f77869fa06d80b6ea1a3fe52d38e\trefs/tags/1.99.0\n" in tags
assert "b940084d7eb6a299eb4bfeb8e34901bc051e7ac4\trefs/tags/1.99.0^{}\n" in tags
release_tree = json.loads((root / "rust-199-root-tree.json").read_text())
src_tree = json.loads((root / "rust-199-src-tree.json").read_text())
tools_tree = json.loads((root / "rust-199-tools-tree.json").read_text())
assert release_tree["sha"] == "b940084d7eb6a299eb4bfeb8e34901bc051e7ac4"
assert next(x for x in release_tree["tree"] if x["path"] == "src")["sha"] == src_tree["sha"]
assert next(x for x in src_tree["tree"] if x["path"] == "tools")["sha"] == tools_tree["sha"]
assert next(x for x in tools_tree["tree"] if x["path"] == "cargo")["sha"] == "5f94df4789f005f9a352888e8355ffc645b7ed0e"
old_parser = (root / "cargo-1981-parser.rs").read_text()
new_parser = (root / "cargo-199-parser.rs").read_text()
old_profiles = (root / "cargo-1981-profiles.rs").read_text()
new_profiles = (root / "cargo-199-profiles.rs").read_text()

assert 'if Edition::Edition2024 <= edition' in old_parser
assert 'anyhow::bail!("`default-features = false` cannot override workspace' in old_parser
assert 'if edition >= Edition::Edition2024 {' in new_parser
assert 'merged_dep.default_features = default_features.or(merged_dep.default_features);' in new_parser
assert 'deprecated_ws_default_features(name, Some(true), warnings);' in new_parser
assert 'None => gctx.build_config()?.incremental,' in old_profiles
assert '.or_else(|| is_ci().then_some(false)),' in new_profiles
assert 'use cargo_util::is_ci;' in new_profiles

compare = json.loads((root / "cargo-1981-to-199-compare.json").read_text())
assert compare["base_commit"]["sha"] == "797e8a9bca276c1c9f9f738d2a20f484fa4eea9d"
assert compare["status"] == "diverged"
assert compare["ahead_by"] == 369 and compare["behind_by"] == 18
assert len(compare["files"]) == 300  # GitHub endpoint cap; not a full path census.

delta = json.loads((root / "matrix-delta.json").read_text())
assert delta["integration"]["status"] == "applied_by_integrated_v91_coverage_matrix"
assert delta["integration"]["basis"] == "exact_v90_base_delta"
assert delta["integrated_report_path"] == "reports/rust-199-cargo-source-followup-2026-10-03/REPORT.md"
checkout = args.reference_root
raw_matrix = subprocess.check_output([
    "git", "-C", str(checkout), "show",
    f'{delta["base_reference"]}:{delta["base_matrix_path"]}',
])
assert hashlib.sha256(raw_matrix).hexdigest() == delta["base_matrix_sha256"]
rows = list(csv.DictReader(io.StringIO(raw_matrix.decode())))
assert len(rows) == 651
release_change, r349_change, r351_change = delta["changes"]
matches = [r for r in rows if r["newer_target"] == release_change["old_value"]]
assert len(matches) == release_change["expected_row_count"] == 55
assert [r["inventory_id"] for r in matches] == release_change["inventory_ids"]
by_id = {r["inventory_id"]: r for r in rows}
for change, row_id in ((r349_change, "R349"), (r351_change, "R351")):
    assert change["inventory_id"] == row_id
    row = by_id[row_id]
    assert row["report_path"] == change["report_path"]
    assert row["source_coverage"] == change["old_source_coverage"]
    assert row["source_evidence_path"] == change["old_source_evidence_path"]
    if "old_newer_target" in change:
        assert row["newer_target"] == change["old_newer_target"]
assert set(release_change["set"]) == {"newer_target"}
assert set(r349_change["set"]) == {"source_coverage", "source_evidence_path"}
assert set(r351_change["set"]) == {"newer_target", "source_coverage", "source_evidence_path"}
assert delta["release_evidence"]["source_commit"] == release_tree["sha"]
assert delta["release_evidence"]["cargo_gitlink"] == "5f94df4789f005f9a352888e8355ffc645b7ed0e"
print("passed_source_only: Cargo exact source; 651-row v90 Git-object delta; 55 target rows; R349/R351 integrated source deltas; no runtime")
