#!/usr/bin/env python3
"""Offline check of the integrated v91 index."""
import argparse
import json
from pathlib import Path

from build_delta import (BASE, INPUT, LEAN, MATRIX, PACKAGE, R414_EVIDENCE,
                         R414_SOURCE, R578_EVIDENCE, R578_SOURCE, RUST, SUPPORT,
                         build, digest, obj, rows)
from freeze_package_hashes import inventory

EXPECTED_INPUTS = {
    "lean-REPORT.md": "93a63b22a67d7f5cc734e433cefab314edca5df963dad3051f69a260bf48542f",
    "lean-REPORT.json": "ed7196afbf2e825624df0a7ac5b11b01a0447350920ed6129bb94057d82ac42a",
    "lean-verification-manifest.json": "e513a00b9d2a3673e66740896210a24012a0d23067b6652ef5110b8f3a49103c",
    "rust-REPORT.md": "2aa0c68d965dc5e295f5f9d8b3c4f1479c0220b7b2fb059cc449dedcc0ebd055",
    "rust-REPORT.json": "d9ed3f74ede5c4a93c92828f946d53c395ec63868f2d71e97763c7cc98ef1b45",
    "rust-provenance.json": "67a241294043d6261cc783b554173d858bdbc319e0f2bd28e605450d27d6d9c8",
    "rust-matrix-delta.json": "cdffcba6f0ab77f82c3bbfceedd16056704e69399eb01c370bdda25d287d8941",
}


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--reference-root", required=True, type=Path)
    p.add_argument("--lean-package-dir", type=Path)
    p.add_argument("--rust-package-dir", type=Path)
    p.add_argument("--staged-reports-root", type=Path)
    a = p.parse_args()
    assert not a.staged_reports_root or not (a.lean_package_dir or a.rust_package_dir)
    assert bool(a.lean_package_dir) == bool(a.rust_package_dir)
    for name, expected in EXPECTED_INPUTS.items():
        assert digest((INPUT / name).read_bytes()) == expected, name
    matrix, addition, delta = build(a.reference_root)
    actual = (SUPPORT / "version-coverage-matrix-20261003-v91.csv").read_bytes()
    assert actual == matrix
    assert json.loads((SUPPORT / "catalog-addition.json").read_text()) == addition
    assert json.loads((SUPPORT / "delta.json").read_text()) == delta
    assert delta["base_commit"] == BASE and delta["next_matrix_sha256"] == digest(actual)
    assert delta["base_matrix_rows"] == 651 and delta["next_matrix_rows"] == 654
    assert delta["base_catalog_entries"] == 652 and delta["next_catalog_entries"] == 655
    assert len(delta["changed_existing_rows"]) == 58
    changed = {r["inventory_id"]: r for r in delta["changed_existing_rows"]}
    assert len(changed) == 58
    assert set(changed["R578"]["changed_fields"]) == {"source_coverage", "source_evidence_path"}
    assert set(changed["R414"]["changed_fields"]) == {"source_coverage", "source_evidence_path"}
    assert set(changed["R351"]["changed_fields"]) == {"newer_target", "source_coverage", "source_evidence_path"}
    assert set(changed["R349"]["changed_fields"]) == {"newer_target", "source_coverage", "source_evidence_path"}
    old_bytes = obj(a.reference_root, MATRIX)
    old_lines, next_lines = old_bytes.splitlines(keepends=True), actual.splitlines(keepends=True)
    assert len(old_lines) == 652 and len(next_lines) == 655
    assert sum(x != y for x, y in zip(old_lines, next_lines)) == 58
    old_rows, final = rows(old_bytes), rows(actual)
    assert all(old_rows[i] == final[i] for i in range(651) if old_lines[i + 1] == next_lines[i + 1])
    ids = {r["inventory_id"]: r for r in final if r["inventory_id"].startswith("R")}
    assert len(ids) == 581 and ids["R578"]["classification"] == "no_newer_release"
    assert ids["R578"]["source_coverage"] == R578_SOURCE and ids["R578"]["source_evidence_path"] == R578_EVIDENCE
    assert ids["R414"]["source_coverage"] == R414_SOURCE and ids["R414"]["source_evidence_path"] == R414_EVIDENCE
    assert [r["report_path"] for r in final[-3:]] == delta["newly_indexed_reports"]
    assert final[-2]["report_path"] == f"{LEAN}/REPORT.md" and final[-1]["report_path"] == f"{RUST}/REPORT.md"
    assert set(addition["additions"]) == {LEAN.split("/")[1], RUST.split("/")[1], PACKAGE.name}
    package_hashes = json.loads((SUPPORT / "source-package-hashes.json").read_text())
    assert digest((SUPPORT / "source-package-hashes.json").read_bytes()) == delta["source_package_hashes_sha256"]
    for package, prefix in ((LEAN, "lean"), (RUST, "rust")):
        name = package.split("/")[1]
        assert json.loads((INPUT / f"{prefix}-REPORT.json").read_text()) == addition["additions"][name]
        assert package_hashes[name]["REPORT.json"]["sha256"] == digest((INPUT / f"{prefix}-REPORT.json").read_bytes())
    assert json.loads((PACKAGE / "REPORT.json").read_text()) == addition["additions"][PACKAGE.name]
    if a.staged_reports_root:
        roots = {name: a.staged_reports_root / name for name in addition["additions"]}
    elif a.lean_package_dir:
        roots = {LEAN.split("/")[1]: a.lean_package_dir,
                 RUST.split("/")[1]: a.rust_package_dir,
                 PACKAGE.name: PACKAGE}
    else:
        roots = {}
    for name, root in roots.items():
        assert json.loads((root / "REPORT.json").read_text()) == addition["additions"][name], name
        if name in package_hashes:
            assert inventory(root) == package_hashes[name], name
    assert f"reports/{PACKAGE.name}/REPORT.md" not in {r["report_path"] for r in final}
    report = (PACKAGE / "REPORT.md").read_text()
    for heading in ("# ", "## Summary", "## Applicability", "## Findings", "## Boundaries", "## Evidence", "## Revalidation"):
        assert heading in report
    for phrase in ("R578", "R414", "R349", "R351", "55", "58", "654", "655", "source-only", "unexecuted"):
        assert phrase in report
    print("PASS integrated v91: exact frozen inputs, 58 changed baseline rows, 654-row matrix, three catalog additions")


if __name__ == "__main__":
    main()
