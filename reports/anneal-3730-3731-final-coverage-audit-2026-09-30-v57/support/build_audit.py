#!/usr/bin/env python3
"""Derive v57 from published v56 and a bounded Lean UTF-32-only LSP cell."""

import csv
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V56_NAME = "anneal-3730-3731-final-coverage-audit-2026-09-30-v56"
V56 = REPORTS / V56_NAME / "support"
PACKAGE = "anneal-3731-i062-utf32-only-unicode-lsp-2026-09-30"
PACKAGES = (V56_NAME, PACKAGE)
DIRECT = {"I062": PACKAGE}
CONTEXT = {"I025": PACKAGE}
EVIDENCE = tuple(path.relative_to(REPORTS / PACKAGE).as_posix()
                 for path in sorted((REPORTS / PACKAGE).rglob("*"))
                 if path.is_file() and "__pycache__" not in path.parts and path.suffix != ".pyc")
NEW_FIELDS = (
    "v57_status", "v57_gate_categories", "v57_specific_remaining_delta",
    "v57_scope_assessment", "v57_review_package", "v57_new_evidence_packages",
    "v57_evidence_files", "v57_next_prerequisite", "v57_evidence_relation",
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
    if item == "I062":
        assert "real-editor or Anneal projection result." in previous
        return previous + (
            " A direct Lean 4.30.0-rc2 UTF-32-only offer on the same Unicode fixture"
            " also omitted explicit positionEncoding and emitted the initial"
            " unknownName range at UTF-16 columns 16-27 rather than scalar 15-26."
            " Sending a version-2 scalar-range edit produced an Unknown constant"
            " Nat.zeroe diagnostic, while fresh original/intended-patch batch checks"
            " exited 1/0. The complete post-edit buffer was not returned. Under"
            " LSP 3.17, UTF-16 remains mandatory for clients and an omitted server"
            " choice defaults to UTF-16, so the offer does not prove selected"
            " UTF-32 or a protocol violation. Real editor, Anneal projection and"
            " cross-version outcomes remain open.")
    return previous


def main():
    live = json.loads((HERE / "live-issue-snapshot-v57.json").read_text())
    earlier = json.loads((V56 / "live-issue-snapshot-v56.json").read_text())
    assert live["issues"] == earlier["issues"]
    assert live["fetched_at_utc"] != earlier["fetched_at_utc"]
    assert live["source"] == "public GitHub REST issue and comments endpoints"
    assert live["issues"]["3730"]["state"] == "closed"
    assert live["issues"]["3731"]["state"] == "open"
    old_rows = json.loads((V56 / "row-challenge-v56.json").read_text())
    assert len(old_rows) == 333 and len({row["id"] for row in old_rows}) == 333
    assert all((REPORTS / PACKAGE / name).is_file() for name in EVIDENCE)
    out = []
    for old in old_rows:
        row = dict(old)
        item = row["id"]
        if item in DIRECT:
            residual = updated_residual(item, old["v56_specific_remaining_delta"])
            assessment = (
                "Direct bounded Lean UTF-32-only capability-offer and Unicode edit"
                " evidence; client/Anneal position conversion"
                " remain at the inherited product gate.")
            relation = "direct bounded I062 UTF-32-only Lean LSP evidence"
            review = HERE.parent.name
            files = [f"reports/{PACKAGE}/{name}" for name in EVIDENCE]
            packages = [PACKAGE]
        elif item in CONTEXT:
            residual = old["v56_specific_remaining_delta"]
            assessment = (
                "The scalar versus UTF-16 coordinate contrast adds context to this"
                " projection row; its Anneal residual, product gate and"
                " next prerequisite remain unchanged.")
            relation = "bounded I025 coordinate-context evidence"
            review = HERE.parent.name
            files = [f"reports/{PACKAGE}/{name}" for name in EVIDENCE]
            packages = [PACKAGE]
        else:
            residual = old["v56_specific_remaining_delta"]
            assessment = (
                f"The UTF-32-only Lean LSP package does not directly exercise {item}"
                f" ({row['title']}); the v56 residual and prerequisite remain.")
            relation = "no direct v57 evidence"
            review = old["v56_review_package"]
            files = []
            packages = []
        row.update({
            "v57_status": old["v56_status"],
            "v57_gate_categories": old["v56_gate_categories"],
            "v57_specific_remaining_delta": residual,
            "v57_scope_assessment": assessment,
            "v57_review_package": review,
            "v57_new_evidence_packages": packages,
            "v57_evidence_files": files,
            "v57_next_prerequisite": old["v56_next_prerequisite"],
            "v57_evidence_relation": relation,
        })
        out.append(row)
    assert {row["id"] for row in out if row["v57_specific_remaining_delta"] != row["v56_specific_remaining_delta"]} == set(DIRECT)
    assert all(row["v57_status"] == row["v56_status"] and
               row["v57_gate_categories"] == row["v56_gate_categories"] and
               row["v57_next_prerequisite"] == row["v56_next_prerequisite"] for row in out)
    (HERE / "row-challenge-v57.json").write_text(json.dumps(out, indent=2, sort_keys=True, ensure_ascii=False) + "\n")
    by_id = {row["id"]: row for row in out}

    def extend(old_name, key, new_name):
        rows = []
        for old in read_csv(V56 / old_name):
            row = dict(old)
            source = by_id[row[key]]
            for field in NEW_FIELDS:
                value = source[field]
                row[field] = ";".join(value) if isinstance(value, list) else value
            rows.append(row)
        write_csv(HERE / new_name, rows)
        return rows

    investigations = extend("investigation-final-v56.csv", "id", "investigation-final-v57.csv")
    suggestions = extend("3730-crosswalk-final-v56.csv", "3730_id", "3730-crosswalk-final-v57.csv")
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
    write_csv(HERE / "source-package-inventory-v57.csv", inventory)
    generated = (
        "row-challenge-v57.json", "investigation-final-v57.csv",
        "3730-crosswalk-final-v57.csv", "source-package-inventory-v57.csv",
    )
    inputs = {
        "v56/row-challenge-v56.json": V56 / "row-challenge-v56.json",
        "v56/investigation-final-v56.csv": V56 / "investigation-final-v56.csv",
        "v56/3730-crosswalk-final-v56.csv": V56 / "3730-crosswalk-final-v56.csv",
        "live-issue-snapshot-v57.json": HERE / "live-issue-snapshot-v57.json",
    }
    validation = {
        "reference_tip_at_start": "a5ecd5bde3d2b33457b5a13b4b435d79515f4012",
        "source_reference_package": V56_NAME,
        "source_anneal_revision": "bd0956be95c5f798f0c0484921b9b9d1fc6e9988",
        "issue_snapshot_relation": "fresh public REST fetch; issue fields unchanged from v56",
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
    (HERE / "validation-v57.json").write_text(json.dumps(validation, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: validation[key] for key in (
        "row_count", "suggestion_destination_links", "changed_residual_ids", "inventory_files")}, sort_keys=True))


if __name__ == "__main__":
    main()
