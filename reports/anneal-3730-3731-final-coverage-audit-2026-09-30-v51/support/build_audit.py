#!/usr/bin/env python3
"""Derive v51 from published v50 and the Unicode Lean LSP encoding probe."""

import csv
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V50_NAME = "anneal-3730-3731-final-coverage-audit-2026-09-30-v50"
V50 = REPORTS / V50_NAME / "support"
PACKAGE = "anneal-3731-i062-utf8-only-unicode-lsp-2026-09-30"
PACKAGES = (V50_NAME, PACKAGE)
DIRECT = {"I062": PACKAGE}
CONTEXT = {"B03": PACKAGE, "I025": PACKAGE}
EVIDENCE = (
    "REPORT.md", "REPORT.json", "probe.py", "oracle.py", "oracle.json",
    "check.py", "results.json", "comparison.json", "fixture/Encoding.lean",
    "fixture/EncodingPatched.lean", "raw/utf8_only.client-wire",
    "raw/utf8_only.server-wire", "raw/utf16_only.client-wire",
    "raw/utf16_only.server-wire", "raw/batch-original.stdout",
    "raw/batch-patched.stdout",
)
NEW_FIELDS = (
    "v51_status", "v51_gate_categories", "v51_specific_remaining_delta",
    "v51_scope_assessment", "v51_review_package", "v51_new_evidence_packages",
    "v51_evidence_files", "v51_next_prerequisite", "v51_evidence_relation",
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
        return previous + (
            " A new direct Lean 4.30.0-rc2 Unicode LSP pair offered UTF-8 alone and UTF-16"
            " alone in sequential servers. Both initialize responses omitted an explicit"
            " positionEncoding; both initial unknownName ranges were UTF-16 columns 16-27"
            " versus independent UTF-8 byte columns 19-30. A UTF-16-ranged incremental"
            " replacement cleared the error, while the UTF-8-byte-ranged replacement under"
            " the UTF-8-only offer produced an unexpected-end error. Fresh original/patched"
            " batch checks exited 1/0. This proves neither a negotiated UTF-8 selection nor"
            " a protocol violation; real editor clients, Anneal projection, source mapping,"
            " fallback and cross-version behavior remain untested.")
    return previous


def main():
    live = json.loads((HERE / "live-issue-snapshot-v51.json").read_text())
    assert live == json.loads((V50 / "live-issue-snapshot-v50.json").read_text())
    assert live["issues"]["3730"]["state"] == "closed"
    assert live["issues"]["3731"]["state"] == "open"
    old_rows = json.loads((V50 / "row-challenge-v50.json").read_text())
    assert len(old_rows) == 333 and len({row["id"] for row in old_rows}) == 333
    assert all((REPORTS / PACKAGE / name).is_file() for name in EVIDENCE)
    out = []
    for old in old_rows:
        row = dict(old)
        item = row["id"]
        if item in DIRECT:
            residual = updated_residual(item, old["v50_specific_remaining_delta"])
            assessment = (
                "Direct bounded Lean LSP Unicode capability/range/edit evidence; actual"
                " editor and Anneal projection remain at the inherited product gate.")
            relation = "direct bounded Unicode Lean LSP encoding evidence"
            review = HERE.parent.name
            files = [f"reports/{PACKAGE}/{name}" for name in EVIDENCE]
            packages = [PACKAGE]
        elif item in CONTEXT:
            residual = old["v50_specific_remaining_delta"]
            assessment = (
                "The direct Unicode Lean LSP result adds component context to this"
                " coordinate/UTF-16 row; its Anneal/editor residual, product gate and"
                " next prerequisite remain unchanged.")
            relation = "bounded Unicode Lean LSP encoding context"
            review = HERE.parent.name
            files = [f"reports/{PACKAGE}/{name}" for name in EVIDENCE]
            packages = [PACKAGE]
        else:
            residual = old["v50_specific_remaining_delta"]
            assessment = (
                f"The Unicode Lean LSP encoding package does not directly exercise {item}"
                f" ({row['title']}); the v50 residual and prerequisite remain.")
            relation = "no direct v51 evidence"
            review = old["v50_review_package"]
            files = []
            packages = []
        row.update({
            "v51_status": old["v50_status"],
            "v51_gate_categories": old["v50_gate_categories"],
            "v51_specific_remaining_delta": residual,
            "v51_scope_assessment": assessment,
            "v51_review_package": review,
            "v51_new_evidence_packages": packages,
            "v51_evidence_files": files,
            "v51_next_prerequisite": old["v50_next_prerequisite"],
            "v51_evidence_relation": relation,
        })
        out.append(row)
    assert {row["id"] for row in out if row["v51_specific_remaining_delta"] != row["v50_specific_remaining_delta"]} == set(DIRECT)
    assert all(row["v51_status"] == row["v50_status"] and
               row["v51_gate_categories"] == row["v50_gate_categories"] and
               row["v51_next_prerequisite"] == row["v50_next_prerequisite"] for row in out)
    (HERE / "row-challenge-v51.json").write_text(json.dumps(out, indent=2, sort_keys=True, ensure_ascii=False) + "\n")
    by_id = {row["id"]: row for row in out}

    def extend(old_name, key, new_name):
        rows = []
        for old in read_csv(V50 / old_name):
            row = dict(old)
            source = by_id[row[key]]
            for field in NEW_FIELDS:
                value = source[field]
                row[field] = ";".join(value) if isinstance(value, list) else value
            rows.append(row)
        write_csv(HERE / new_name, rows)
        return rows

    investigations = extend("investigation-final-v50.csv", "id", "investigation-final-v51.csv")
    suggestions = extend("3730-crosswalk-final-v50.csv", "3730_id", "3730-crosswalk-final-v51.csv")
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
    write_csv(HERE / "source-package-inventory-v51.csv", inventory)
    generated = (
        "row-challenge-v51.json", "investigation-final-v51.csv",
        "3730-crosswalk-final-v51.csv", "source-package-inventory-v51.csv",
    )
    inputs = {
        "v50/row-challenge-v50.json": V50 / "row-challenge-v50.json",
        "v50/investigation-final-v50.csv": V50 / "investigation-final-v50.csv",
        "v50/3730-crosswalk-final-v50.csv": V50 / "3730-crosswalk-final-v50.csv",
        "live-issue-snapshot-v51.json": HERE / "live-issue-snapshot-v51.json",
    }
    validation = {
        "reference_tip_at_start": "ebfeac694e945da0b52e09c6a185d857f982f4f3",
        "source_reference_package": V50_NAME,
        "source_anneal_revision": "bd0956be95c5f798f0c0484921b9b9d1fc6e9988",
        "issue_snapshot_relation": "exact inherited v50 snapshot; no fresh fetch",
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
    (HERE / "validation-v51.json").write_text(json.dumps(validation, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: validation[key] for key in (
        "row_count", "suggestion_destination_links", "changed_residual_ids", "inventory_files")}, sort_keys=True))


if __name__ == "__main__":
    main()
