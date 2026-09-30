#!/usr/bin/env python3
"""Derive v49 from published v48 and the generated-file Charon span oracle."""

import csv
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V48_NAME = "anneal-3730-3731-final-coverage-audit-2026-09-30-v48"
V48 = REPORTS / V48_NAME / "support"
PACKAGE = "anneal-3731-i079-generated-file-charon-spans-2026-09-30"
PACKAGES = (V48_NAME, PACKAGE)
DIRECT = {"I079": PACKAGE}
CONTEXT = {}
EVIDENCE = (
    "REPORT.md", "REPORT.json", "probe.py", "check.py", "results.json",
    "comparison.json", "fixture/generated_template.rs", "fixture/build.rs",
    "generated.rs", "generated.llbc", "raw/charon.stderr",
)
NEW_FIELDS = (
    "v49_status", "v49_gate_categories", "v49_specific_remaining_delta",
    "v49_scope_assessment", "v49_review_package", "v49_new_evidence_packages",
    "v49_evidence_files", "v49_next_prerequisite", "v49_evidence_relation",
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
    if item == "I079":
        return previous + (
            " A new offline `build.rs`/`include!` fixture retained the actual generated.rs bytes"
            " independently of LLBC. Seven local generated file-ID-1 item records have exact"
            " source_text slices and fixture display-cell span endpoints against those bytes;"
            " the UTF-8-byte, scalar and UTF-16 hypotheses each mismatch some records."
            " This does not retroactively validate the earlier 32 generated-file records,"
            " establish a general Unicode contract or provide a Rust-to-Lean/Anneal map.")
    return previous


def main():
    live = json.loads((HERE / "live-issue-snapshot-v49.json").read_text())
    assert live == json.loads((V48 / "live-issue-snapshot-v48.json").read_text())
    assert live["issues"]["3730"]["state"] == "closed"
    assert live["issues"]["3731"]["state"] == "open"
    old_rows = json.loads((V48 / "row-challenge-v48.json").read_text())
    assert len(old_rows) == 333 and len({row["id"] for row in old_rows}) == 333
    assert all((REPORTS / PACKAGE / name).is_file() for name in EVIDENCE)
    out = []
    for old in old_rows:
        row = dict(old)
        item = row["id"]
        if item in DIRECT:
            residual = updated_residual(item, old["v48_specific_remaining_delta"])
            assessment = (
                "Direct bounded generated-file Charon item-span evidence with independently"
                " retained source bytes; general provenance and Anneal mapping remain at the"
                " inherited product gate.")
            relation = "direct bounded generated-file Charon span evidence"
            review = HERE.parent.name
            files = [f"reports/{PACKAGE}/{name}" for name in EVIDENCE]
            packages = [PACKAGE]
        else:
            residual = old["v48_specific_remaining_delta"]
            assessment = (
                f"The generated-file Charon span package does not directly exercise {item}"
                f" ({row['title']}); the v48 residual and prerequisite remain.")
            relation = "no direct v49 evidence"
            review = old["v48_review_package"]
            files = []
            packages = []
        row.update({
            "v49_status": old["v48_status"],
            "v49_gate_categories": old["v48_gate_categories"],
            "v49_specific_remaining_delta": residual,
            "v49_scope_assessment": assessment,
            "v49_review_package": review,
            "v49_new_evidence_packages": packages,
            "v49_evidence_files": files,
            "v49_next_prerequisite": old["v48_next_prerequisite"],
            "v49_evidence_relation": relation,
        })
        out.append(row)
    assert {row["id"] for row in out if row["v49_specific_remaining_delta"] != row["v48_specific_remaining_delta"]} == set(DIRECT)
    assert all(row["v49_status"] == row["v48_status"] and
               row["v49_gate_categories"] == row["v48_gate_categories"] and
               row["v49_next_prerequisite"] == row["v48_next_prerequisite"] for row in out)
    (HERE / "row-challenge-v49.json").write_text(json.dumps(out, indent=2, sort_keys=True, ensure_ascii=False) + "\n")
    by_id = {row["id"]: row for row in out}

    def extend(old_name, key, new_name):
        rows = []
        for old in read_csv(V48 / old_name):
            row = dict(old)
            source = by_id[row[key]]
            for field in NEW_FIELDS:
                value = source[field]
                row[field] = ";".join(value) if isinstance(value, list) else value
            rows.append(row)
        write_csv(HERE / new_name, rows)
        return rows

    investigations = extend("investigation-final-v48.csv", "id", "investigation-final-v49.csv")
    suggestions = extend("3730-crosswalk-final-v48.csv", "3730_id", "3730-crosswalk-final-v49.csv")
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
    write_csv(HERE / "source-package-inventory-v49.csv", inventory)
    generated = (
        "row-challenge-v49.json", "investigation-final-v49.csv",
        "3730-crosswalk-final-v49.csv", "source-package-inventory-v49.csv",
    )
    inputs = {
        "v48/row-challenge-v48.json": V48 / "row-challenge-v48.json",
        "v48/investigation-final-v48.csv": V48 / "investigation-final-v48.csv",
        "v48/3730-crosswalk-final-v48.csv": V48 / "3730-crosswalk-final-v48.csv",
        "live-issue-snapshot-v49.json": HERE / "live-issue-snapshot-v49.json",
    }
    validation = {
        "reference_tip_at_start": "ff9f5253bd129da0ab4b20e05103ac56993eac0d",
        "source_reference_package": V48_NAME,
        "source_anneal_revision": "bd0956be95c5f798f0c0484921b9b9d1fc6e9988",
        "issue_snapshot_relation": "exact inherited v48 snapshot; no fresh fetch",
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
    (HERE / "validation-v49.json").write_text(json.dumps(validation, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: validation[key] for key in (
        "row_count", "suggestion_destination_links", "changed_residual_ids", "inventory_files")}, sort_keys=True))


if __name__ == "__main__":
    main()
