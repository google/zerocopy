#!/usr/bin/env python3
"""Read-only offline checker for the post-publication I001-I053 audit."""
import csv
import hashlib
import json
from pathlib import Path

import i005_models

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
V23 = ROOT / "reports/anneal-3730-3731-final-coverage-audit-2026-09-29-v23/support/investigation-final-v23.csv"
PRIOR = ROOT / "reports/anneal-3731-i001-i053-residual-reaudit-2026-09-29/REPORT.md"
SNAPSHOT = ROOT / "reports/anneal-3730-3731-coverage-audit-2026-09-29/support/source-snapshot/manifest.json"
PIN_SOURCE = ROOT / "reports/anneal-3730-3731-final-coverage-audit-2026-09-29-v21/support/resource-recheck.json"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def records(path):
    with path.open(newline="") as f:
        return list(csv.DictReader(f))


def main():
    facts = json.loads((HERE / "validation.json").read_text())
    assert sha(V23) == facts["v23_ledger_sha256"]
    assert sha(PRIOR) == facts["prior_review_sha256"]
    for filename, field in (("row-review.csv", "row_review_sha256"),
                            ("package-inventory.csv", "package_inventory_sha256"),
                            ("i005-results.json", "i005_results_sha256"),
                            ("i005_models.py", "i005_probe_sha256"),
                            ("live-issue-summary.json", "live_issue_summary_sha256"),
                            ("resource-summary.json", "resource_summary_sha256")):
        assert sha(HERE / filename) == facts[field], filename

    source = [r for r in records(V23) if "I001" <= r["id"] <= "I053"]
    review = records(HERE / "row-review.csv")
    assert len(source) == len(review) == facts["row_count"] == 53
    assert [r["id"] for r in review] == [f"I{i:03d}" for i in range(1, 54)]
    assert sum(r["postpublication_status"] == "complete" for r in review) == facts["complete_count"] == 2
    assert sum(r["postpublication_status"] == "partial" for r in review) == facts["partial_count"] == 51
    assert {r["id"] for r in review if r["postpublication_status"] == "complete"} == {"I046", "I049"}
    for old, new in zip(source, review):
        for field in ("id", "title"):
            assert new[field] == old[field]
        assert new["exact_requested_scope"] == old["requested_scope"]
        assert new["v23_status"] == new["postpublication_status"] == old["v23_status"]
        assert new["next_prerequisite"] == old["v23_next_prerequisite"]
        assert new["v23_review_package"] == old["v23_review_package"]
        assert new["remaining_gate"] and new["evidence_assessment"]
        if new["id"] != "I005":
            assert new["remaining_gate"] == old["v23_specific_remaining_delta"]
            assert new["cached_only_decision"] == "no further distinct bounded local cell found"
        else:
            assert "executed" in new["cached_only_decision"]

    names = set()
    evidence = set()
    for row in source:
        for key, value in row.items():
            if key.endswith("_packages"):
                names.update(item for item in value.split(";") if item)
            if key.endswith("_evidence_files"):
                evidence.update(item for item in value.split(";") if item)
    inventory = records(HERE / "package-inventory.csv")
    assert len(inventory) == facts["cited_package_count"] == 70
    assert [r["package"] for r in inventory] == sorted(names)
    for record in inventory:
        base = ROOT / "reports" / record["package"]
        for name, field in (("REPORT.md", "report_md_sha256"),
                            ("REPORT.json", "report_json_sha256"),
                            ("support/check.py", "checker_sha256")):
            path = base / name
            assert (sha(path) if path.is_file() else "") == record[field], str(path)
    missing = sorted(item for item in evidence
                     if not (ROOT / (item if item.startswith("reports/") else "reports/" + item)).exists())
    assert len(evidence) == facts["cited_evidence_file_count"] == 147
    assert missing == facts["missing_cited_evidence_files"] == []

    live = json.loads((HERE / "live-issue-summary.json").read_text())
    frozen = json.loads(SNAPSHOT.read_text())["files"]
    assert live["number"] == 3731 and live["state"] == "open"
    assert live["body_sha256"] == frozen["issue3731.txt"]["sha256"]
    assert len(live["comments"]) == 1 and live["comments"][0]["id"] == 5884299718
    assert live["comments"][0]["body_sha256"] == frozen["comment3731.txt"]["sha256"]
    resources = json.loads((HERE / "resource-summary.json").read_text())
    original = json.loads(PIN_SOURCE.read_text())["pins_rechecked"]
    assert set(resources["pins"]) == set(original)
    for name, item in resources["pins"].items():
        assert item["exists"] is True
        if "sha256" in original[name]:
            assert item["matches_v21"] is True
            assert item["sha256"] == original[name]["sha256"]
    assert all(resources["path_tools"][tool] is None for tool in ("ocaml", "dune", "opam", "lean", "lake", "charon", "aeneas"))

    retained = json.loads((HERE / "i005-results.json").read_text())
    assert retained == i005_models.build()
    assert set(retained["cases"]) == set(i005_models.VARIANTS)
    for variant, case in retained["cases"].items():
        assert len(case["schedules"]) == 12
        assert case["unfenced_stale_schedule_count"] == 3
        assert case["snapshot_calls"] == {"translation": 2, "proof": 2}
        assert case["scheduler_calls"] == {"translation": 2 if variant in ("source_edit", "model_change") else 1, "proof": 2}
        for schedule in case["schedules"]:
            assert schedule["snapshot"]["order"] == schedule["scheduler"]["order"] == schedule["unfenced"]["order"]
            assert all(event["current_safe"] for event in schedule["snapshot"]["events"])
            assert all(event["current_safe"] for event in schedule["scheduler"]["events"])
    assert retained["summary"]["matched_edit_schedules"] == 48
    assert retained["summary"]["unfenced_stale_schedules"] == 12
    assert len(retained["shared_cancel"]) == 2
    print("PASS: 53 rows (2 complete, 51 partial), 70 package hashes, 147 cited files, live scope, pins, and I005 48/12 + cancellation replay")


if __name__ == "__main__":
    main()
