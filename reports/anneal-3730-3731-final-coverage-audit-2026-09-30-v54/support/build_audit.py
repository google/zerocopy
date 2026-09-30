#!/usr/bin/env python3
"""Derive v54 from published v53 and matched Charon symlink/copy controls."""

import csv
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V53_NAME = "anneal-3730-3731-final-coverage-audit-2026-09-30-v53"
V53 = REPORTS / V53_NAME / "support"
PACKAGE = "anneal-3731-i079-symlink-module-identity-2026-09-30"
PACKAGES = (V53_NAME, PACKAGE)
DIRECT = {"I079": PACKAGE}
CONTEXT = {"I031": PACKAGE}
EVIDENCE = tuple(path.relative_to(REPORTS / PACKAGE).as_posix()
                 for path in sorted((REPORTS / PACKAGE).rglob("*"))
                 if path.is_file() and "__pycache__" not in path.parts and path.suffix != ".pyc")
NEW_FIELDS = (
    "v54_status", "v54_gate_categories", "v54_specific_remaining_delta",
    "v54_scope_assessment", "v54_review_package", "v54_new_evidence_packages",
    "v54_evidence_files", "v54_next_prerequisite", "v54_evidence_relation",
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
            " A matched APFS same-inode symlink-alias versus distinct-inode physical-copy"
            " crate now shows two lexical #[path] module filenames kept as separate Charon"
            " LLBC local file IDs 1/2 in both layouts, with identical embedded source bytes"
            " and left/right item file associations. The two decoded LLBC trees differ at"
            " requested dest_file and six positional short_names leaves across three"
            " entries; typed-key/name maps agree. This one-pair observation does not"
            " establish cross-filesystem identity, causal attribution for short_names"
            " ordering, a general normalizer, semantic equivalence, or Anneal cache policy.")
    return previous


def main():
    live = json.loads((HERE / "live-issue-snapshot-v54.json").read_text())
    earlier = json.loads((V53 / "live-issue-snapshot-v53.json").read_text())
    assert live["issues"] == earlier["issues"]
    assert live["fetched_at_utc"] != earlier["fetched_at_utc"]
    assert live["source"] == "public GitHub REST issue and comments endpoints"
    assert live["issues"]["3730"]["state"] == "closed"
    assert live["issues"]["3731"]["state"] == "open"
    old_rows = json.loads((V53 / "row-challenge-v53.json").read_text())
    assert len(old_rows) == 333 and len({row["id"] for row in old_rows}) == 333
    assert all((REPORTS / PACKAGE / name).is_file() for name in EVIDENCE)
    out = []
    for old in old_rows:
        row = dict(old)
        item = row["id"]
        if item in DIRECT:
            residual = updated_residual(item, old["v53_specific_remaining_delta"])
            assessment = (
                "Direct bounded Charon same-inode symlink-alias versus physical-copy file"
                " identity evidence; general normalization and Anneal source association"
                " remain at the inherited product gate.")
            relation = "direct bounded I079 LLBC lexical-alias file-identity evidence"
            review = HERE.parent.name
            files = [f"reports/{PACKAGE}/{name}" for name in EVIDENCE]
            packages = [PACKAGE]
        elif item in CONTEXT:
            residual = old["v53_specific_remaining_delta"]
            assessment = (
                "The same-inode Charon file table adds source-provenance context to this"
                " diagnostics row; its Anneal residual, product gate and"
                " next prerequisite remain unchanged.")
            relation = "bounded I031 Charon lexical-source context"
            review = HERE.parent.name
            files = [f"reports/{PACKAGE}/{name}" for name in EVIDENCE]
            packages = [PACKAGE]
        else:
            residual = old["v53_specific_remaining_delta"]
            assessment = (
                f"The Charon symlink-alias package does not directly exercise {item}"
                f" ({row['title']}); the v53 residual and prerequisite remain.")
            relation = "no direct v54 evidence"
            review = old["v53_review_package"]
            files = []
            packages = []
        row.update({
            "v54_status": old["v53_status"],
            "v54_gate_categories": old["v53_gate_categories"],
            "v54_specific_remaining_delta": residual,
            "v54_scope_assessment": assessment,
            "v54_review_package": review,
            "v54_new_evidence_packages": packages,
            "v54_evidence_files": files,
            "v54_next_prerequisite": old["v53_next_prerequisite"],
            "v54_evidence_relation": relation,
        })
        out.append(row)
    assert {row["id"] for row in out if row["v54_specific_remaining_delta"] != row["v53_specific_remaining_delta"]} == set(DIRECT)
    assert all(row["v54_status"] == row["v53_status"] and
               row["v54_gate_categories"] == row["v53_gate_categories"] and
               row["v54_next_prerequisite"] == row["v53_next_prerequisite"] for row in out)
    (HERE / "row-challenge-v54.json").write_text(json.dumps(out, indent=2, sort_keys=True, ensure_ascii=False) + "\n")
    by_id = {row["id"]: row for row in out}

    def extend(old_name, key, new_name):
        rows = []
        for old in read_csv(V53 / old_name):
            row = dict(old)
            source = by_id[row[key]]
            for field in NEW_FIELDS:
                value = source[field]
                row[field] = ";".join(value) if isinstance(value, list) else value
            rows.append(row)
        write_csv(HERE / new_name, rows)
        return rows

    investigations = extend("investigation-final-v53.csv", "id", "investigation-final-v54.csv")
    suggestions = extend("3730-crosswalk-final-v53.csv", "3730_id", "3730-crosswalk-final-v54.csv")
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
    write_csv(HERE / "source-package-inventory-v54.csv", inventory)
    generated = (
        "row-challenge-v54.json", "investigation-final-v54.csv",
        "3730-crosswalk-final-v54.csv", "source-package-inventory-v54.csv",
    )
    inputs = {
        "v53/row-challenge-v53.json": V53 / "row-challenge-v53.json",
        "v53/investigation-final-v53.csv": V53 / "investigation-final-v53.csv",
        "v53/3730-crosswalk-final-v53.csv": V53 / "3730-crosswalk-final-v53.csv",
        "live-issue-snapshot-v54.json": HERE / "live-issue-snapshot-v54.json",
    }
    validation = {
        "reference_tip_at_start": "6b0acaee13124bc17bef31c764693836a93ff25a",
        "source_reference_package": V53_NAME,
        "source_anneal_revision": "bd0956be95c5f798f0c0484921b9b9d1fc6e9988",
        "issue_snapshot_relation": "fresh public REST fetch; issue fields unchanged from v53",
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
    (HERE / "validation-v54.json").write_text(json.dumps(validation, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: validation[key] for key in (
        "row_count", "suggestion_destination_links", "changed_residual_ids", "inventory_files")}, sort_keys=True))


if __name__ == "__main__":
    main()
