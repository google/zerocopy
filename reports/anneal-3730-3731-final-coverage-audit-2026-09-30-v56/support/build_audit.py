#!/usr/bin/env python3
"""Derive v56 from published v55 and corrected cfg_attr(path) Charon controls."""

import csv
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V55_NAME = "anneal-3730-3731-final-coverage-audit-2026-09-30-v55"
V55 = REPORTS / V55_NAME / "support"
PACKAGE = "anneal-3731-i079-cfg-attr-module-2026-09-30"
PACKAGES = (V55_NAME, PACKAGE)
DIRECT = {"I079": PACKAGE}
CONTEXT = {"I031": PACKAGE}
EVIDENCE = tuple(path.relative_to(REPORTS / PACKAGE).as_posix()
                 for path in sorted((REPORTS / PACKAGE).rglob("*"))
                 if path.is_file() and "__pycache__" not in path.parts and path.suffix != ".pyc")
NEW_FIELDS = (
    "v56_status", "v56_gate_categories", "v56_specific_remaining_delta",
    "v56_scope_assessment", "v56_review_package", "v56_new_evidence_packages",
    "v56_evidence_files", "v56_next_prerequisite", "v56_evidence_relation",
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
        assert "General producer normalization, source association, Rust-to-Lean mapping and Anneal editor conversion remain open." in previous
        return previous + (
            " A corrected two-cell cfg_attr(path) Charon run holds the logical"
            " selected::marker item name, file ID 1 and span fixed while toggling"
            " only Cargo feature alternate with --no-default-features in both cells."
            " Serialized LLBC selects src/default.rs with literal 17 or"
            " src/alternate.rs with literal 29; the unselected file is absent."
            " Full decoded trees differ at selected path/content, marker MIR"
            " literal/source_text and requested dest_file only. A preliminary"
            " two-feature run is retained but excluded. This one-crate result"
            " does not establish a general cfg_attr normalizer, stable numeric"
            " file identity, Anneal source association or cache-key policy.")
    return previous


def main():
    live = json.loads((HERE / "live-issue-snapshot-v56.json").read_text())
    earlier = json.loads((V55 / "live-issue-snapshot-v55.json").read_text())
    assert live["issues"] == earlier["issues"]
    assert live["fetched_at_utc"] != earlier["fetched_at_utc"]
    assert live["source"] == "public GitHub REST issue and comments endpoints"
    assert live["issues"]["3730"]["state"] == "closed"
    assert live["issues"]["3731"]["state"] == "open"
    old_rows = json.loads((V55 / "row-challenge-v55.json").read_text())
    assert len(old_rows) == 333 and len({row["id"] for row in old_rows}) == 333
    assert all((REPORTS / PACKAGE / name).is_file() for name in EVIDENCE)
    out = []
    for old in old_rows:
        row = dict(old)
        item = row["id"]
        if item in DIRECT:
            residual = updated_residual(item, old["v55_specific_remaining_delta"])
            assessment = (
                "Direct bounded cfg_attr(path) physical module-source selection in"
                " Charon LLBC; general normalization and Anneal source association"
                " remain at the inherited product gate.")
            relation = "direct bounded I079 cfg_attr module-source evidence"
            review = HERE.parent.name
            files = [f"reports/{PACKAGE}/{name}" for name in EVIDENCE]
            packages = [PACKAGE]
        elif item in CONTEXT:
            residual = old["v55_specific_remaining_delta"]
            assessment = (
                "The conditional Charon file table adds source-provenance context to this"
                " diagnostics row; its Anneal residual, product gate and"
                " next prerequisite remain unchanged.")
            relation = "bounded I031 conditional-source context"
            review = HERE.parent.name
            files = [f"reports/{PACKAGE}/{name}" for name in EVIDENCE]
            packages = [PACKAGE]
        else:
            residual = old["v55_specific_remaining_delta"]
            assessment = (
                f"The cfg_attr(path) module-source package does not directly exercise {item}"
                f" ({row['title']}); the v55 residual and prerequisite remain.")
            relation = "no direct v56 evidence"
            review = old["v55_review_package"]
            files = []
            packages = []
        row.update({
            "v56_status": old["v55_status"],
            "v56_gate_categories": old["v55_gate_categories"],
            "v56_specific_remaining_delta": residual,
            "v56_scope_assessment": assessment,
            "v56_review_package": review,
            "v56_new_evidence_packages": packages,
            "v56_evidence_files": files,
            "v56_next_prerequisite": old["v55_next_prerequisite"],
            "v56_evidence_relation": relation,
        })
        out.append(row)
    assert {row["id"] for row in out if row["v56_specific_remaining_delta"] != row["v55_specific_remaining_delta"]} == set(DIRECT)
    assert all(row["v56_status"] == row["v55_status"] and
               row["v56_gate_categories"] == row["v55_gate_categories"] and
               row["v56_next_prerequisite"] == row["v55_next_prerequisite"] for row in out)
    (HERE / "row-challenge-v56.json").write_text(json.dumps(out, indent=2, sort_keys=True, ensure_ascii=False) + "\n")
    by_id = {row["id"]: row for row in out}

    def extend(old_name, key, new_name):
        rows = []
        for old in read_csv(V55 / old_name):
            row = dict(old)
            source = by_id[row[key]]
            for field in NEW_FIELDS:
                value = source[field]
                row[field] = ";".join(value) if isinstance(value, list) else value
            rows.append(row)
        write_csv(HERE / new_name, rows)
        return rows

    investigations = extend("investigation-final-v55.csv", "id", "investigation-final-v56.csv")
    suggestions = extend("3730-crosswalk-final-v55.csv", "3730_id", "3730-crosswalk-final-v56.csv")
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
    write_csv(HERE / "source-package-inventory-v56.csv", inventory)
    generated = (
        "row-challenge-v56.json", "investigation-final-v56.csv",
        "3730-crosswalk-final-v56.csv", "source-package-inventory-v56.csv",
    )
    inputs = {
        "v55/row-challenge-v55.json": V55 / "row-challenge-v55.json",
        "v55/investigation-final-v55.csv": V55 / "investigation-final-v55.csv",
        "v55/3730-crosswalk-final-v55.csv": V55 / "3730-crosswalk-final-v55.csv",
        "live-issue-snapshot-v56.json": HERE / "live-issue-snapshot-v56.json",
    }
    validation = {
        "reference_tip_at_start": "1018438e175202747f052dc1c0734d331b656f01",
        "source_reference_package": V55_NAME,
        "source_anneal_revision": "bd0956be95c5f798f0c0484921b9b9d1fc6e9988",
        "issue_snapshot_relation": "fresh public REST fetch; issue fields unchanged from v55",
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
    (HERE / "validation-v56.json").write_text(json.dumps(validation, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: validation[key] for key in (
        "row_count", "suggestion_destination_links", "changed_residual_ids", "inventory_files")}, sort_keys=True))


if __name__ == "__main__":
    main()
