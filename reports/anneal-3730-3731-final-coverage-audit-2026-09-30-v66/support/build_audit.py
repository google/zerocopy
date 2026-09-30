#!/usr/bin/env python3
"""Derive v66 from published v65 and one three-manifest preseeded server retry."""

import csv
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V65_NAME = "anneal-3730-3731-final-coverage-audit-2026-09-30-v65"
V65 = REPORTS / V65_NAME / "support"
PACKAGE = "anneal-3731-i092-preseeded-manifest-server-readiness-2026-09-30"
PACKAGES = (V65_NAME, PACKAGE)
DIRECT = {"I092": PACKAGE}
CONTEXT = {"F07": PACKAGE, "F08": PACKAGE}
EVIDENCE = tuple(path.relative_to(REPORTS / PACKAGE).as_posix()
                 for path in sorted((REPORTS / PACKAGE).rglob("*"))
                 if path.is_file() and "__pycache__" not in path.parts and path.suffix != ".pyc")
NEW_FIELDS = (
    "v66_status", "v66_gate_categories", "v66_specific_remaining_delta",
    "v66_scope_assessment", "v66_review_package", "v66_new_evidence_packages",
    "v66_evidence_files", "v66_next_prerequisite", "v66_evidence_relation",
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
    if item == "I092":
        return previous + (
            " A subsequent fresh-admitted three-manifest retry opened the same"
            " preseeded Generated.lean with valid, malformed-JSON, and parseable"
            " no-dependency consumer manifests under Lake --no-build --no-cache"
            " serve. The valid cell reached final processing-empty quiescence and"
            " returned the live goal depValue = 7. Both invalid cells published"
            " Lake setup-file failures and fallback warnings, never met the"
            " probe's final quiescence rule, and returned null plainGoal after"
            " bounded eight-second waits; each process still exited 0. These"
            " bounded null replies do not prove unbounded goal absence. Producer,"
            " cache, and per-command work inventories were unchanged. The actual"
            " Anneal prepared archive, broader artifact families, and enforced"
            " read-only product path remain at the inherited gate.")
    return previous


def main():
    live = json.loads((HERE / "live-issue-snapshot-v66.json").read_text())
    earlier = json.loads((V65 / "live-issue-snapshot-v65.json").read_text())
    assert live["issues"] == earlier["issues"]
    assert live == earlier
    assert live["source"] == "public GitHub REST issue and comments endpoints"
    assert live["issues"]["3730"]["state"] == "closed"
    assert live["issues"]["3731"]["state"] == "open"
    old_rows = json.loads((V65 / "row-challenge-v65.json").read_text())
    assert len(old_rows) == 333 and len({row["id"] for row in old_rows}) == 333
    assert all((REPORTS / PACKAGE / name).is_file() for name in EVIDENCE)
    out = []
    for old in old_rows:
        row = dict(old)
        item = row["id"]
        if item in DIRECT:
            residual = updated_residual(item, old["v65_specific_remaining_delta"])
            assessment = (
                "Direct bounded three-manifest server observation; invalid"
                " cells had setup diagnostics and null goals without quiescence."
                " The actual Anneal archive remains at the inherited product gate.")
            relation = "direct bounded I092 three-manifest server evidence"
            review = HERE.parent.name
            files = [f"reports/{PACKAGE}/{name}" for name in EVIDENCE]
            packages = [PACKAGE]
        elif item in CONTEXT:
            residual = old["v65_specific_remaining_delta"]
            assessment = (
                "F07/F08 gain bounded server setup and goal context through I092;"
                " their product residuals remain unchanged.")
            relation = "bounded context evidence"
            review = HERE.parent.name
            files = [f"reports/{PACKAGE}/{name}" for name in EVIDENCE]
            packages = [PACKAGE]
        else:
            residual = old["v65_specific_remaining_delta"]
            assessment = (
                f"The three-manifest server package does not directly exercise {item}"
                f" ({row['title']}); the v65 residual and prerequisite remain.")
            relation = "no direct v66 evidence"
            review = old["v65_review_package"]
            files = []
            packages = []
        row.update({
            "v66_status": old["v65_status"],
            "v66_gate_categories": old["v65_gate_categories"],
            "v66_specific_remaining_delta": residual,
            "v66_scope_assessment": assessment,
            "v66_review_package": review,
            "v66_new_evidence_packages": packages,
            "v66_evidence_files": files,
            "v66_next_prerequisite": old["v65_next_prerequisite"],
            "v66_evidence_relation": relation,
        })
        out.append(row)
    assert {row["id"] for row in out if row["v66_specific_remaining_delta"] != row["v65_specific_remaining_delta"]} == set(DIRECT)
    assert all(row["v66_status"] == row["v65_status"] and
               row["v66_gate_categories"] == row["v65_gate_categories"] and
               row["v66_next_prerequisite"] == row["v65_next_prerequisite"] for row in out)
    (HERE / "row-challenge-v66.json").write_text(json.dumps(out, indent=2, sort_keys=True, ensure_ascii=False) + "\n")
    by_id = {row["id"]: row for row in out}

    def extend(old_name, key, new_name):
        rows = []
        for old in read_csv(V65 / old_name):
            row = dict(old)
            source = by_id[row[key]]
            for field in NEW_FIELDS:
                value = source[field]
                row[field] = ";".join(value) if isinstance(value, list) else value
            rows.append(row)
        write_csv(HERE / new_name, rows)
        return rows

    investigations = extend("investigation-final-v65.csv", "id", "investigation-final-v66.csv")
    suggestions = extend("3730-crosswalk-final-v65.csv", "3730_id", "3730-crosswalk-final-v66.csv")
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
    write_csv(HERE / "source-package-inventory-v66.csv", inventory)
    generated = (
        "row-challenge-v66.json", "investigation-final-v66.csv",
        "3730-crosswalk-final-v66.csv", "source-package-inventory-v66.csv",
    )
    inputs = {
        "v65/row-challenge-v65.json": V65 / "row-challenge-v65.json",
        "v65/investigation-final-v65.csv": V65 / "investigation-final-v65.csv",
        "v65/3730-crosswalk-final-v65.csv": V65 / "3730-crosswalk-final-v65.csv",
        "live-issue-snapshot-v66.json": HERE / "live-issue-snapshot-v66.json",
    }
    validation = {
        "reference_tip_at_start": "57155f6541e478f201ae47d8a27da2f3d448df5e",
        "source_reference_package": V65_NAME,
        "source_anneal_revision": "bd0956be95c5f798f0c0484921b9b9d1fc6e9988",
        "issue_snapshot_relation": "v65 public REST snapshot reused unchanged; no fresh issue read",
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
    (HERE / "validation-v66.json").write_text(json.dumps(validation, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: validation[key] for key in (
        "row_count", "suggestion_destination_links", "changed_residual_ids", "inventory_files")}, sort_keys=True))


if __name__ == "__main__":
    main()
