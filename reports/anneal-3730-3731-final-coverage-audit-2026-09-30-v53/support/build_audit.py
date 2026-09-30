#!/usr/bin/env python3
"""Derive v53 from published v52 and the copied empty-line v2 bridge."""

import csv
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V52_NAME = "anneal-3730-3731-final-coverage-audit-2026-09-30-v52"
V52 = REPORTS / V52_NAME / "support"
PACKAGE = "anneal-3731-i025-empty-owned-v2-bridge-2026-09-30"
PACKAGES = (V52_NAME, PACKAGE)
DIRECT = {"I025": PACKAGE}
CONTEXT = {"I026": PACKAGE}
EVIDENCE = tuple(path.relative_to(REPORTS / PACKAGE).as_posix()
                 for path in sorted((REPORTS / PACKAGE).rglob("*"))
                 if path.is_file() and "__pycache__" not in path.parts and path.suffix != ".pyc")
NEW_FIELDS = (
    "v53_status", "v53_gate_categories", "v53_specific_remaining_delta",
    "v53_scope_assessment", "v53_review_package", "v53_new_evidence_packages",
    "v53_evidence_files", "v53_next_prerequisite", "v53_evidence_relation",
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
    if item == "I025":
        assert "Empty-line/display-width cases, negotiated editor encoding, unsaved revisions, production annotation grammar and generated obligations remain untested." in previous
        previous = previous.replace(
            "Empty-line/display-width cases, negotiated editor encoding, unsaved revisions, production annotation grammar and generated obligations remain untested.",
            "Production empty-line policy, display-width mapping, negotiated editor encoding, source identity across unsaved revisions, production annotation grammar and generated obligations remain untested.")
        return previous + (
            " A second hand-authored component fixture maps one explicitly owned zero-length"
            " Rust doc payload at host byte 58 to projected byte 33. A direct Lean 4.30-rc2"
            " version-2 unsaved insertion there yielded an unknown-name diagnostic at"
            " zero-based UTF-16 line 3 columns 16-28; fresh batch on exact v2 bytes gave"
            " one-based scalar line 4 columns 15-27. The disk retained v1 bytes. Five"
            " synthetic/CRLF/version/surrogate controls were rejected by the local map."
            " The first harness attempt had a response-ID bug and is retained but excluded."
            " This tests only one declared empty-line owner, not Anneal mapping or client behavior.")
    return previous


def main():
    live = json.loads((HERE / "live-issue-snapshot-v53.json").read_text())
    assert live == json.loads((V52 / "live-issue-snapshot-v52.json").read_text())
    assert live["issues"]["3730"]["state"] == "closed"
    assert live["issues"]["3731"]["state"] == "open"
    old_rows = json.loads((V52 / "row-challenge-v52.json").read_text())
    assert len(old_rows) == 333 and len({row["id"] for row in old_rows}) == 333
    assert all((REPORTS / PACKAGE / name).is_file() for name in EVIDENCE)
    out = []
    for old in old_rows:
        row = dict(old)
        item = row["id"]
        if item in DIRECT:
            residual = updated_residual(item, old["v52_specific_remaining_delta"])
            assessment = (
                "Direct bounded compiler-backed, hand-authored empty-line source anchor and"
                " Lean v2 unsaved diagnostic evidence; actual Anneal projection/editor"
                " remain at the inherited product gate.")
            relation = "direct bounded I025 copied-empty-line v2 bridge evidence"
            review = HERE.parent.name
            files = [f"reports/{PACKAGE}/{name}" for name in EVIDENCE]
            packages = [PACKAGE]
        elif item in CONTEXT:
            residual = old["v52_specific_remaining_delta"]
            assessment = (
                "The declared empty-line insertion owner adds border-policy context to this"
                " projection-invertibility row; its Anneal residual, product gate and"
                " next prerequisite remain unchanged.")
            relation = "bounded I026 empty-segment border-policy context"
            review = HERE.parent.name
            files = [f"reports/{PACKAGE}/{name}" for name in EVIDENCE]
            packages = [PACKAGE]
        else:
            residual = old["v52_specific_remaining_delta"]
            assessment = (
                f"The copied empty-line v2 bridge does not directly exercise {item}"
                f" ({row['title']}); the v52 residual and prerequisite remain.")
            relation = "no direct v53 evidence"
            review = old["v52_review_package"]
            files = []
            packages = []
        row.update({
            "v53_status": old["v52_status"],
            "v53_gate_categories": old["v52_gate_categories"],
            "v53_specific_remaining_delta": residual,
            "v53_scope_assessment": assessment,
            "v53_review_package": review,
            "v53_new_evidence_packages": packages,
            "v53_evidence_files": files,
            "v53_next_prerequisite": old["v52_next_prerequisite"],
            "v53_evidence_relation": relation,
        })
        out.append(row)
    assert {row["id"] for row in out if row["v53_specific_remaining_delta"] != row["v52_specific_remaining_delta"]} == set(DIRECT)
    assert all(row["v53_status"] == row["v52_status"] and
               row["v53_gate_categories"] == row["v52_gate_categories"] and
               row["v53_next_prerequisite"] == row["v52_next_prerequisite"] for row in out)
    (HERE / "row-challenge-v53.json").write_text(json.dumps(out, indent=2, sort_keys=True, ensure_ascii=False) + "\n")
    by_id = {row["id"]: row for row in out}

    def extend(old_name, key, new_name):
        rows = []
        for old in read_csv(V52 / old_name):
            row = dict(old)
            source = by_id[row[key]]
            for field in NEW_FIELDS:
                value = source[field]
                row[field] = ";".join(value) if isinstance(value, list) else value
            rows.append(row)
        write_csv(HERE / new_name, rows)
        return rows

    investigations = extend("investigation-final-v52.csv", "id", "investigation-final-v53.csv")
    suggestions = extend("3730-crosswalk-final-v52.csv", "3730_id", "3730-crosswalk-final-v53.csv")
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
    write_csv(HERE / "source-package-inventory-v53.csv", inventory)
    generated = (
        "row-challenge-v53.json", "investigation-final-v53.csv",
        "3730-crosswalk-final-v53.csv", "source-package-inventory-v53.csv",
    )
    inputs = {
        "v52/row-challenge-v52.json": V52 / "row-challenge-v52.json",
        "v52/investigation-final-v52.csv": V52 / "investigation-final-v52.csv",
        "v52/3730-crosswalk-final-v52.csv": V52 / "3730-crosswalk-final-v52.csv",
        "live-issue-snapshot-v53.json": HERE / "live-issue-snapshot-v53.json",
    }
    validation = {
        "reference_tip_at_start": "e1c4cf18da52136936eec8d6361607a9036adcb9",
        "source_reference_package": V52_NAME,
        "source_anneal_revision": "bd0956be95c5f798f0c0484921b9b9d1fc6e9988",
        "issue_snapshot_relation": "exact inherited v52 snapshot; no fresh fetch",
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
    (HERE / "validation-v53.json").write_text(json.dumps(validation, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: validation[key] for key in (
        "row_count", "suggestion_destination_links", "changed_residual_ids", "inventory_files")}, sort_keys=True))


if __name__ == "__main__":
    main()
