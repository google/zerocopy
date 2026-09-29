#!/usr/bin/env python3
"""Build only this supplemental package from immutable, local source reports."""
import csv
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
V23 = ROOT / "reports/anneal-3730-3731-final-coverage-audit-2026-09-29-v23/support/investigation-final-v23.csv"
PRIOR = ROOT / "reports/anneal-3731-i001-i053-residual-reaudit-2026-09-29/REPORT.md"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_csv(path, rows, fields):
    with path.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)


def main():
    rows = [r for r in csv.DictReader(V23.open(newline="")) if "I001" <= r["id"] <= "I053"]
    assert len(rows) == 53 and [r["id"] for r in rows] == [f"I{i:03d}" for i in range(1, 54)]
    prior = {}
    for line in PRIOR.read_text().splitlines():
        match = re.fullmatch(r"\| (I\d{3}) \| ([PA]) \| (.*?) \|", line)
        if match:
            prior[match[1]] = (match[2], match[3])
    assert set(prior) == {r["id"] for r in rows}

    packages = set()
    evidence_files = set()
    review = []
    for row in rows:
        rid = row["id"]
        old_code, old_note = prior[rid]
        assert old_code == ("A" if row["v23_status"] == "complete" else "P")
        if rid == "I010":
            old_note = old_note.replace("[ABA double-collect evidence](support/aba-double-collect-results.json)",
                                        "ABA double-collect evidence in the cited I001-I053 review")
        if rid == "I005":
            assessment = ("The earlier finite/fake-stage schedules lacked a matched two-model comparison. "
                          "The retained matched replay now covers identical proof/source/model/import edits, "
                          "completion order, and cancellation for snapshot and versioned-scheduler models. "
                          "Each fenced model preserves latest selection in 48 valid edit schedules and a "
                          "surviving subscriber in 2 cancellation orders; an unfenced control selects stale A "
                          "in 12/48 orders. These are abstract fake backends, not Anneal product behavior.")
            cached = "executed: matched finite fake-backend comparison (support/i005-results.json)"
        else:
            assessment = old_note
            cached = "no further distinct bounded local cell found"
        for key, value in row.items():
            if key.endswith("_packages"):
                packages.update(s for s in value.split(";") if s)
            if key.endswith("_evidence_files"):
                evidence_files.update(s for s in value.split(";") if s)
        review.append({
            "id": rid,
            "title": row["title"],
            "exact_requested_scope": row["requested_scope"],
            "v23_status": row["v23_status"],
            "postpublication_status": row["v23_status"],
            "evidence_assessment": assessment,
            "remaining_gate": row["v23_specific_remaining_delta"] if rid != "I005" else
                "Actual Anneal dependency graph, repeated workloads, and real stage costs remain. The fake-backend comparison does not choose an architecture.",
            "next_prerequisite": row["v23_next_prerequisite"],
            "v23_review_package": row["v23_review_package"],
            "cached_only_decision": cached,
        })
    assert sum(r["postpublication_status"] == "complete" for r in review) == 2
    write_csv(HERE / "row-review.csv", review, list(review[0]))

    inventory = []
    for name in sorted(packages):
        package = ROOT / "reports" / name
        assert package.is_dir(), name
        paths = [package / "REPORT.md", package / "REPORT.json", package / "support/check.py"]
        record = {"package": name}
        for path, field in zip(paths, ("report_md", "report_json", "checker")):
            record[field + "_sha256"] = sha(path) if path.is_file() else ""
        assert record["report_md_sha256"], name
        inventory.append(record)
    write_csv(HERE / "package-inventory.csv", inventory, list(inventory[0]))
    missing = sorted(p for p in evidence_files if not (ROOT / (p if p.startswith("reports/") else "reports/" + p)).exists())
    assert not missing, missing
    facts = {
        "v23_ledger_sha256": sha(V23),
        "prior_review_sha256": sha(PRIOR),
        "row_count": len(review),
        "complete_count": 2,
        "partial_count": 51,
        "cited_package_count": len(inventory),
        "cited_evidence_file_count": len(evidence_files),
        "missing_cited_evidence_files": missing,
        "new_cached_only_experiment_ids": ["I005"],
        "row_review_sha256": sha(HERE / "row-review.csv"),
        "package_inventory_sha256": sha(HERE / "package-inventory.csv"),
        "i005_results_sha256": sha(HERE / "i005-results.json"),
        "i005_probe_sha256": sha(HERE / "i005_models.py"),
        "live_issue_summary_sha256": sha(HERE / "live-issue-summary.json"),
        "resource_summary_sha256": sha(HERE / "resource-summary.json"),
    }
    (HERE / "validation.json").write_text(json.dumps(facts, indent=2) + "\n")
    print(json.dumps({k: facts[k] for k in ("row_count", "complete_count", "partial_count", "cited_package_count", "cited_evidence_file_count")}))


if __name__ == "__main__":
    main()
