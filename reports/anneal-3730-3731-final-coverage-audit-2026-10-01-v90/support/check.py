#!/usr/bin/env python3
"""Offline integrity and scoped-delta check for the v90 draft."""
import argparse
import csv
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
DRAFT = HERE.parent
M = json.loads((HERE / "delta.json").read_text())


def sha(data):
    return hashlib.sha256(data).hexdigest()


def git(root, *args):
    return subprocess.check_output(
        ["git", *args], cwd=root, env=dict(os.environ, GIT_NO_LAZY_FETCH="1")
    ).decode().strip()


def committed(root, revision, path):
    return subprocess.check_output(
        ["git", "show", f"{revision}:{path}"],
        cwd=root, env=dict(os.environ, GIT_NO_LAZY_FETCH="1")
    )


def rows(data):
    return list(csv.DictReader(io.StringIO(data.decode())))


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--reference-root", type=Path,
                   default=Path(os.environ["REFERENCE_ROOT"]) if os.environ.get("REFERENCE_ROOT") else None)
    a = p.parse_args()
    if a.reference_root is None:
        p.error("pass --reference-root or set REFERENCE_ROOT")
    root = a.reference_root.resolve()
    v89 = root / "reports/anneal-3730-3731-final-coverage-audit-2026-10-01-v89"
    observed = M["reference_head"]
    assert M["schema"] == 1 and M["observed_at"] == "2026-10-01"
    assert observed == "0dc78ac0ca00516fe75ac58c63f2d60b91a148de"
    assert git(root, "rev-parse", f"{observed}^{{tree}}") == M["reference_tree"]
    assert subprocess.run(["git", "merge-base", "--is-ancestor", observed, "HEAD"],
                          cwd=root, capture_output=True).returncode == 0
    assert M["v89_reference_head"] == "604a61e3bafe184b09587a4d0cfde5477977f638"
    assert sha((v89 / "support/delta.json").read_bytes()) == M["v89_local_delta_sha256"]
    assert sha((v89 / "support/check.py").read_bytes()) == M["v89_local_checker_sha256"]
    subprocess.run([sys.executable, "-B", str(v89 / "support/check.py"),
                    "--reference-root", str(root)], check=True)

    catalog_bytes = committed(root, observed, "CATALOG.json")
    assert sha(catalog_bytes) == M["catalog_sha256"]
    assert git(root, "rev-parse", f"{observed}:CATALOG.json") == M["catalog_blob"]
    catalog = json.loads(catalog_bytes)["reports"]
    names = set(git(root, "ls-tree", "-d", "--name-only", f"{observed}:reports").splitlines())
    assert len(catalog) == M["catalog_entries"] == 649
    assert len(names) == M["report_directories"] == 651
    assert names - set(catalog) == set(M["catalog_missing_new_reports"])

    packages = M["packages"]
    expected = {
        "v89": "anneal-3730-3731-final-coverage-audit-2026-10-01-v89",
        "lean_lsp": "lean-incremental-diagnostics-lsp-runtime-ab-430rc2-to-4341-2026-10-01",
        "i094_lake": "i094-lake-readonly-consumer-server-430rc2-to-4341-2026-10-01",
    }
    assert set(packages) == set(expected)
    assert packages["v89"]["publication_revision"] == M["v89_publication_revision"]
    for key, name in expected.items():
        item = packages[key]
        assert item["package"] == name
        revision = item["publication_revision"]
        assert subprocess.run(["git", "merge-base", "--is-ancestor", revision, observed],
                              cwd=root, capture_output=True).returncode == 0
        path = f"reports/{name}"
        assert git(root, "rev-parse", f"{revision}:{path}") == item["tree"]
        assert sha(committed(root, revision, f"{path}/REPORT.md")) == item["report_sha256"]
        metadata_bytes = committed(root, revision, f"{path}/REPORT.json")
        assert sha(metadata_bytes) == item["metadata_sha256"]
        assert json.loads(metadata_bytes)["subjects"]
        if key == "v89":
            assert catalog[name] == json.loads(metadata_bytes)
        else:
            assert name not in catalog

    additions_bytes = (HERE / "catalog-additions.json").read_bytes()
    assert sha(additions_bytes) == M["catalog_additions_sha256"]
    additions = json.loads(additions_bytes)
    v90_name = "anneal-3730-3731-final-coverage-audit-2026-10-01-v90"
    assert additions["baseline_catalog_entries"] == 649
    assert set(additions["additions"]) == set(M["catalog_missing_new_reports"]) | {v90_name}
    for key in ("lean_lsp", "i094_lake"):
        name = expected[key]
        assert additions["additions"][name] == json.loads(committed(
            root, packages[key]["publication_revision"], f"reports/{name}/REPORT.json"))
    assert additions["additions"][v90_name] == json.loads((DRAFT / "REPORT.json").read_text())

    old_data = (v89 / "support/version-coverage-matrix-20261001-v89.csv").read_bytes()
    new_data = (HERE / "version-coverage-matrix-20261001-v90.csv").read_bytes()
    info = M["version_matrix"]
    assert sha(new_data) == info["sha256"]
    old_rows, new_rows = rows(old_data), rows(new_data)
    assert len(old_rows) == 648 and len(new_rows) == info["rows"] == 651
    assert info["frozen_inventory_rows"] == 581
    assert info["post_frozen_report_rows"] == 70
    assert [r["report_path"] for r in old_rows] == [r["report_path"] for r in new_rows[:648]]
    changed = [a["report_path"] for a, b in zip(old_rows, new_rows) if a != b]
    lean_source = "reports/lean-incremental-diagnostics-430rc2-to-4341-source-delta-2026-10-01/REPORT.md"
    lake_original = "reports/lake-generated-workspace-readonly-probe-v4-30-0-rc2/REPORT.md"
    assert set(changed) == {lean_source, lake_original}
    for before, after in zip(old_rows, new_rows):
        if before != after:
            assert {k: v for k, v in before.items() if k not in ("runtime_coverage", "local_feasibility_or_blocker")} == {
                k: v for k, v in after.items() if k not in ("runtime_coverage", "local_feasibility_or_blocker")}
    assert [r["report_path"] for r in new_rows[648:]] == [
        f"reports/{expected[k]}/REPORT.md" for k in ("v89", "lean_lsp", "i094_lake")]
    assert {r["report_path"] for r in new_rows} == {f"reports/{n}/REPORT.md" for n in names}
    assert sum(r["inventory_id"] == "post581" for r in new_rows) == 70
    bypath = {r["report_path"]: r for r in new_rows}
    assert bypath[lake_original]["inventory_id"] == "R425"
    assert expected["i094_lake"] in bypath[lake_original]["runtime_coverage"]
    assert "actual Anneal/Aeneas/Mathlib archive" in bypath[lake_original]["local_feasibility_or_blocker"]
    assert bypath[lean_source]["inventory_id"] == "post581"
    assert expected["lean_lsp"] in bypath[lean_source]["runtime_coverage"]
    assert "isIncremental:true append path not observed" in bypath[lean_source]["runtime_coverage"]
    assert M["new_direct_original_inventory_ids"] == ["R425"]
    assert M["new_contextual_original_inventory_ids"] == []
    assert M["direct_original_inventory_ids_total"] == 19
    assert M["contextual_original_inventory_ids_total"] == 1

    cross_bytes = (HERE / "affected-crosswalk.json").read_bytes()
    assert sha(cross_bytes) == M["affected_crosswalk_sha256"]
    cross = json.loads(cross_bytes)
    assert cross["frozen_v80_rows_unchanged"] is True
    assert [(x["id"], x["frozen_v80_status"], x["v90_assessment"])
            for x in cross["investigation"] + cross["suggestions"]] == [
                ("I094", "partial", "partial"),
                ("F03", "not-run", "partial"),
                ("M01", "partial", "partial")]
    assert M["lean_lsp_append_observed"] is False
    assert M["i094_full_archive_tested"] is False
    assert M["issue_observation"]["mutations"] == 0
    assert [(x["number"], x["status"]) for x in M["issue_observation"]["issues"]] == [
        (3731, "Open"), (3730, "Closed as not planned")]
    assert M["inherited_counts"] == json.loads((v89 / "support/delta.json").read_text())["inherited_counts"]
    assert M["inherited_investigation_statuses"] == json.loads((v89 / "support/delta.json").read_text())["inherited_investigation_statuses"]

    report = (DRAFT / "REPORT.md").read_text()
    for name in expected.values():
        assert f"../{name}/REPORT.md" in report
    assert "No `isIncremental: true` append publication was observed" in report
    assert "**I094 partial**" in report and "**F03 as partial at this v90 assessment**" in report
    assert "**649 entries for 651 report directories**" in report
    assert "public issue pages were rechecked read-only on 2026-10-01" in report
    for key in ("lean_lsp", "i094_lake"):
        package_dir = root / "reports" / expected[key]
        subprocess.run([sys.executable, "-B", str(package_dir / "support/check.py")],
                       cwd=package_dir, check=True)
    print("PASS: v90 scoped delta, 651-row matrix, catalog gap/additions, frozen v89 ledger, and two offline evidence checkers")


if __name__ == "__main__":
    main()
