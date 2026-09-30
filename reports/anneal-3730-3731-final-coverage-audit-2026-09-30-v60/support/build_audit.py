#!/usr/bin/env python3
"""Derive v60 from published v59 and one stepwise Lean LSP version cell."""

import csv
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V59_NAME = "anneal-3730-3731-final-coverage-audit-2026-09-30-v59"
V59 = REPORTS / V59_NAME / "support"
PACKAGE = "anneal-3731-i112-stepwise-lsp-versions-2026-09-30"
PACKAGES = (V59_NAME, PACKAGE)
DIRECT = {"I112": PACKAGE}
CONTEXT = {}
EVIDENCE = tuple(path.relative_to(REPORTS / PACKAGE).as_posix()
                 for path in sorted((REPORTS / PACKAGE).rglob("*"))
                 if path.is_file() and "__pycache__" not in path.parts and path.suffix != ".pyc")
NEW_FIELDS = (
    "v60_status", "v60_gate_categories", "v60_specific_remaining_delta",
    "v60_scope_assessment", "v60_review_package", "v60_new_evidence_packages",
    "v60_evidence_files", "v60_next_prerequisite", "v60_evidence_relation",
)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_csv(path):
    with path.open(newline="") as stream:
        return list(csv.DictReader(stream))


def write_csv(path, rows):
    with path.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]), lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)


def updated_residual(item, previous):
    if item == "I112":
        assert "does not reveal each intermediate handling" in previous
        return previous + (
            " A stepwise direct Lean 4.30.0-rc2 run now awaited a unique"
            " versioned diagnostic marker before each plainGoal query and"
            " observed source-specific goals 1, 2, 4, 40, 3, 5 across"
            " v1/v2/v4/duplicate-v4/lower-v3/v5 notifications. A separate"
            " monotonic v1-v5 server control returned 1, 2, 3, 4, 5; both"
            " remained at 5 after a short quiet interval. Duplicate/lower"
            " versions deliberately violate the client's monotonic-update"
            " contract. Actual lost watcher/transport/MCP delivery, reconnect"
            " and Anneal authoritative-state reconciliation remain untested.")
    return previous


def main():
    live = json.loads((HERE / "live-issue-snapshot-v60.json").read_text())
    earlier = json.loads((V59 / "live-issue-snapshot-v59.json").read_text())
    assert live["issues"] == earlier["issues"]
    assert live["fetched_at_utc"] != earlier["fetched_at_utc"]
    assert live["source"] == "public GitHub REST issue and comments endpoints"
    assert live["issues"]["3730"]["state"] == "closed"
    assert live["issues"]["3731"]["state"] == "open"
    old_rows = json.loads((V59 / "row-challenge-v59.json").read_text())
    assert len(old_rows) == 333 and len({row["id"] for row in old_rows}) == 333
    assert all((REPORTS / PACKAGE / name).is_file() for name in EVIDENCE)
    out = []
    for old in old_rows:
        row = dict(old)
        item = row["id"]
        if item in DIRECT:
            residual = updated_residual(item, old["v59_specific_remaining_delta"])
            assessment = (
                "Direct bounded Lean LSP intermediate version/diagnostic/goal"
                " evidence; actual delivery loss and Anneal reconciliation"
                " remain at the inherited product gate.")
            relation = "direct bounded I112 stepwise Lean LSP version evidence"
            review = HERE.parent.name
            files = [f"reports/{PACKAGE}/{name}" for name in EVIDENCE]
            packages = [PACKAGE]
        elif item in CONTEXT:
            residual = old["v59_specific_remaining_delta"]
            assessment = (
                "No bounded context row is mapped to this direct Lean version"
                " cell; the inherited residual and prerequisite remain unchanged.")
            relation = "bounded context evidence"
            review = HERE.parent.name
            files = [f"reports/{PACKAGE}/{name}" for name in EVIDENCE]
            packages = [PACKAGE]
        else:
            residual = old["v59_specific_remaining_delta"]
            assessment = (
                f"The stepwise Lean LSP version package does not directly exercise {item}"
                f" ({row['title']}); the v59 residual and prerequisite remain.")
            relation = "no direct v60 evidence"
            review = old["v59_review_package"]
            files = []
            packages = []
        row.update({
            "v60_status": old["v59_status"],
            "v60_gate_categories": old["v59_gate_categories"],
            "v60_specific_remaining_delta": residual,
            "v60_scope_assessment": assessment,
            "v60_review_package": review,
            "v60_new_evidence_packages": packages,
            "v60_evidence_files": files,
            "v60_next_prerequisite": old["v59_next_prerequisite"],
            "v60_evidence_relation": relation,
        })
        out.append(row)
    assert {row["id"] for row in out if row["v60_specific_remaining_delta"] != row["v59_specific_remaining_delta"]} == set(DIRECT)
    assert all(row["v60_status"] == row["v59_status"] and
               row["v60_gate_categories"] == row["v59_gate_categories"] and
               row["v60_next_prerequisite"] == row["v59_next_prerequisite"] for row in out)
    (HERE / "row-challenge-v60.json").write_text(json.dumps(out, indent=2, sort_keys=True, ensure_ascii=False) + "\n")
    by_id = {row["id"]: row for row in out}

    def extend(old_name, key, new_name):
        rows = []
        for old in read_csv(V59 / old_name):
            row = dict(old)
            source = by_id[row[key]]
            for field in NEW_FIELDS:
                value = source[field]
                row[field] = ";".join(value) if isinstance(value, list) else value
            rows.append(row)
        write_csv(HERE / new_name, rows)
        return rows

    investigations = extend("investigation-final-v59.csv", "id", "investigation-final-v60.csv")
    suggestions = extend("3730-crosswalk-final-v59.csv", "3730_id", "3730-crosswalk-final-v60.csv")
    assert len(investigations) == 159 and len(suggestions) == 174
    body = live["issues"]["3731"]["body"]
    comment = live["issues"]["3731"]["comments"][0]["body"]
    titles = {item: re.sub(r"\s*\[[^]]+\]\.?$", "", title).strip()
              for source in (body, comment)
              for item, title in re.findall(r"(?m)^\*\*(I\d{3})\s+[—.]\s+([^\n]*?)\*\*", source)}
    cross = {item: (title.strip(), set(re.findall(r"I\d{3}", destinations)))
             for item, title, destinations in re.findall(r"(?m)^\| ([A-O]\d{2}) \| ([^|]+) \| ([^|]+) \|", comment)}
    assert len(titles) == 159 and len(cross) == 174
    assert all(row["title"] == titles[row["id"]] for row in investigations)
    assert all(row["suggestion"] == cross[row["3730_id"]][0] and
               set(row["3731_destinations"].split(";")) == cross[row["3730_id"]][1]
               for row in suggestions)
    links = sum(len(value[1]) for value in cross.values())
    assert links == 345

    inventory = []
    for package in PACKAGES:
        for path in sorted((REPORTS / package).rglob("*")):
            if path.is_file() and "__pycache__" not in path.parts and path.suffix != ".pyc":
                inventory.append({"path": path.relative_to(ROOT).as_posix(), "sha256": sha(path)})
    write_csv(HERE / "source-package-inventory-v60.csv", inventory)
    generated = (
        "row-challenge-v60.json", "investigation-final-v60.csv",
        "3730-crosswalk-final-v60.csv", "source-package-inventory-v60.csv",
    )
    inputs = {
        "v59/row-challenge-v59.json": V59 / "row-challenge-v59.json",
        "v59/investigation-final-v59.csv": V59 / "investigation-final-v59.csv",
        "v59/3730-crosswalk-final-v59.csv": V59 / "3730-crosswalk-final-v59.csv",
        "live-issue-snapshot-v60.json": HERE / "live-issue-snapshot-v60.json",
    }
    validation = {
        "reference_tip_at_start": "2cec790eeec883e83ac66dcfa021c51ad65ad4f1",
        "source_reference_package": V59_NAME,
        "source_anneal_revision": "bd0956be95c5f798f0c0484921b9b9d1fc6e9988",
        "issue_snapshot_relation": "fresh public REST fetch; issue fields unchanged from v59",
        "row_count": len(out), "investigation_count": len(investigations),
        "suggestion_count": len(suggestions), "suggestion_destination_links": links,
        "status_counts": {
            "investigations": dict(Counter(row["status"] for row in investigations)),
            "suggestions": dict(Counter(row["status"] for row in suggestions)),
        },
        "changed_status_ids": [], "changed_gate_ids": [], "changed_prerequisite_ids": [],
        "changed_residual_ids": sorted(DIRECT), "direct_evidence_ids": sorted(DIRECT),
        "bounded_context_ids": sorted(CONTEXT), "source_packages": list(PACKAGES),
        "inventory_files": len(inventory),
        "input_sha256": {name: sha(path) for name, path in inputs.items()},
        "generated_sha256": {name: sha(HERE / name) for name in generated},
    }
    (HERE / "validation-v60.json").write_text(json.dumps(validation, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: validation[key] for key in (
        "row_count", "suggestion_destination_links", "changed_residual_ids", "inventory_files")}, sort_keys=True))


if __name__ == "__main__":
    main()
