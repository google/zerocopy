#!/usr/bin/env python3
"""Derive v62 from published v61 and one package-local OLean interruption."""

import csv
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V61_NAME = "anneal-3730-3731-final-coverage-audit-2026-09-30-v61"
V61 = REPORTS / V61_NAME / "support"
PACKAGE = "anneal-3731-i151-package-local-interrupted-olean-2026-09-30"
PACKAGES = (V61_NAME, PACKAGE)
DIRECT = {"I151": PACKAGE}
CONTEXT = {"F12": PACKAGE}
EVIDENCE = tuple(path.relative_to(REPORTS / PACKAGE).as_posix()
                 for path in sorted((REPORTS / PACKAGE).rglob("*"))
                 if path.is_file() and "__pycache__" not in path.parts and path.suffix != ".pyc")
NEW_FIELDS = (
    "v62_status", "v62_gate_categories", "v62_specific_remaining_delta",
    "v62_scope_assessment", "v62_review_package", "v62_new_evidence_packages",
    "v62_evidence_files", "v62_next_prerequisite", "v62_evidence_relation",
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
    if item == "I151":
        assert "Kills occurred before artifact output" in previous
        return previous + (
            " A sequential package-local Lake 4.30.0-rc2 file-size-limit"
            " update from Dep value 7 to 9 now left no final Dep.olean and"
            " one 2,308-byte partial Dep.olean.tmp file while the old trace"
            " and hash sidecar remained. Fresh no-build rejected the state"
            " (exit 3) and direct Lean could not import Dep (exit 1). An"
            " uncapped rebuild produced the value-9 OLean; no-build and"
            " fresh Lean then passed, but the partial temp persisted."
            " This is one interrupted writer, not a simultaneous shared-writer"
            " schedule; interruption during trace/hash writes, competing"
            " publishers and Anneal ownership remain untested.")
    return previous


def main():
    live = json.loads((HERE / "live-issue-snapshot-v62.json").read_text())
    earlier = json.loads((V61 / "live-issue-snapshot-v61.json").read_text())
    assert live["issues"] == earlier["issues"]
    assert live["fetched_at_utc"] != earlier["fetched_at_utc"]
    assert live["source"] == "public GitHub REST issue and comments endpoints"
    assert live["issues"]["3730"]["state"] == "closed"
    assert live["issues"]["3731"]["state"] == "open"
    old_rows = json.loads((V61 / "row-challenge-v61.json").read_text())
    assert len(old_rows) == 333 and len({row["id"] for row in old_rows}) == 333
    assert all((REPORTS / PACKAGE / name).is_file() for name in EVIDENCE)
    out = []
    for old in old_rows:
        row = dict(old)
        item = row["id"]
        if item in DIRECT:
            residual = updated_residual(item, old["v61_specific_remaining_delta"])
            assessment = (
                "Direct bounded package-local OLean-write failure and repair"
                " evidence; competing writers and actual Anneal ownership"
                " remain at the inherited product gate.")
            relation = "direct bounded I151 package-local interrupted OLean evidence"
            review = HERE.parent.name
            files = [f"reports/{PACKAGE}/{name}" for name in EVIDENCE]
            packages = [PACKAGE]
        elif item in CONTEXT:
            residual = old["v61_specific_remaining_delta"]
            assessment = (
                "F12 gains bounded one-writer interruption context; its"
                " shared-writer and product residual remain unchanged.")
            relation = "bounded context evidence"
            review = HERE.parent.name
            files = [f"reports/{PACKAGE}/{name}" for name in EVIDENCE]
            packages = [PACKAGE]
        else:
            residual = old["v61_specific_remaining_delta"]
            assessment = (
                f"The package-local OLean interruption package does not directly exercise {item}"
                f" ({row['title']}); the v61 residual and prerequisite remain.")
            relation = "no direct v62 evidence"
            review = old["v61_review_package"]
            files = []
            packages = []
        row.update({
            "v62_status": old["v61_status"],
            "v62_gate_categories": old["v61_gate_categories"],
            "v62_specific_remaining_delta": residual,
            "v62_scope_assessment": assessment,
            "v62_review_package": review,
            "v62_new_evidence_packages": packages,
            "v62_evidence_files": files,
            "v62_next_prerequisite": old["v61_next_prerequisite"],
            "v62_evidence_relation": relation,
        })
        out.append(row)
    assert {row["id"] for row in out if row["v62_specific_remaining_delta"] != row["v61_specific_remaining_delta"]} == set(DIRECT)
    assert all(row["v62_status"] == row["v61_status"] and
               row["v62_gate_categories"] == row["v61_gate_categories"] and
               row["v62_next_prerequisite"] == row["v61_next_prerequisite"] for row in out)
    (HERE / "row-challenge-v62.json").write_text(json.dumps(out, indent=2, sort_keys=True, ensure_ascii=False) + "\n")
    by_id = {row["id"]: row for row in out}

    def extend(old_name, key, new_name):
        rows = []
        for old in read_csv(V61 / old_name):
            row = dict(old)
            source = by_id[row[key]]
            for field in NEW_FIELDS:
                value = source[field]
                row[field] = ";".join(value) if isinstance(value, list) else value
            rows.append(row)
        write_csv(HERE / new_name, rows)
        return rows

    investigations = extend("investigation-final-v61.csv", "id", "investigation-final-v62.csv")
    suggestions = extend("3730-crosswalk-final-v61.csv", "3730_id", "3730-crosswalk-final-v62.csv")
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
    write_csv(HERE / "source-package-inventory-v62.csv", inventory)
    generated = (
        "row-challenge-v62.json", "investigation-final-v62.csv",
        "3730-crosswalk-final-v62.csv", "source-package-inventory-v62.csv",
    )
    inputs = {
        "v61/row-challenge-v61.json": V61 / "row-challenge-v61.json",
        "v61/investigation-final-v61.csv": V61 / "investigation-final-v61.csv",
        "v61/3730-crosswalk-final-v61.csv": V61 / "3730-crosswalk-final-v61.csv",
        "live-issue-snapshot-v62.json": HERE / "live-issue-snapshot-v62.json",
    }
    validation = {
        "reference_tip_at_start": "60ac83369bb7355bd6c729bc2b7256e479489987",
        "source_reference_package": V61_NAME,
        "source_anneal_revision": "bd0956be95c5f798f0c0484921b9b9d1fc6e9988",
        "issue_snapshot_relation": "fresh public REST fetch; issue fields unchanged from v61",
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
    (HERE / "validation-v62.json").write_text(json.dumps(validation, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: validation[key] for key in (
        "row_count", "suggestion_destination_links", "changed_residual_ids", "inventory_files")}, sort_keys=True))


if __name__ == "__main__":
    main()
