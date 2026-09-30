#!/usr/bin/env python3
"""Derive v61 from published v60 and one Lake package-version ablation."""

import csv
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V60_NAME = "anneal-3730-3731-final-coverage-audit-2026-09-30-v60"
V60 = REPORTS / V60_NAME / "support"
PACKAGE = "anneal-3731-i090-lake-version-only-identity-2026-09-30"
PACKAGES = (V60_NAME, PACKAGE)
DIRECT = {"I090": PACKAGE}
CONTEXT = {"F05": PACKAGE}
EVIDENCE = tuple(path.relative_to(REPORTS / PACKAGE).as_posix()
                 for path in sorted((REPORTS / PACKAGE).rglob("*"))
                 if path.is_file() and "__pycache__" not in path.parts and path.suffix != ".pyc")
NEW_FIELDS = (
    "v61_status", "v61_gate_categories", "v61_specific_remaining_delta",
    "v61_scope_assessment", "v61_review_package", "v61_new_evidence_packages",
    "v61_evidence_files", "v61_next_prerequisite", "v61_evidence_relation",
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
    if item == "I090":
        assert "Frozen index collision control already ran" in previous
        return previous + (
            " A fixed-path, assigned-name/index Lake 4.30.0-rc2 ablation"
            " varied only the producer package version 1.0.0→2.0.0→1.0.0"
            " with Dep.lean value 7 fixed. Producer config OLean and trace"
            " hashes changed and reverted, while Dep.olean and consumer"
            " Generated.olean bytes and fresh eval 7 stayed fixed; Lake"
            " logged Replayed Dep. A separate fixed-version Dep value 7→9"
            " control rebuilt Dep.olean and fresh eval returned 9. This"
            " bounds this version-line edit's observed config artifacts; a complete"
            " multi-identity preparation key and real archive still need"
            " Anneal producer/consumer evidence.")
    return previous


def main():
    live = json.loads((HERE / "live-issue-snapshot-v61.json").read_text())
    earlier = json.loads((V60 / "live-issue-snapshot-v60.json").read_text())
    assert live["issues"] == earlier["issues"]
    assert live["fetched_at_utc"] != earlier["fetched_at_utc"]
    assert live["source"] == "public GitHub REST issue and comments endpoints"
    assert live["issues"]["3730"]["state"] == "closed"
    assert live["issues"]["3731"]["state"] == "open"
    old_rows = json.loads((V60 / "row-challenge-v60.json").read_text())
    assert len(old_rows) == 333 and len({row["id"] for row in old_rows}) == 333
    assert all((REPORTS / PACKAGE / name).is_file() for name in EVIDENCE)
    out = []
    for old in old_rows:
        row = dict(old)
        item = row["id"]
        if item in DIRECT:
            residual = updated_residual(item, old["v60_specific_remaining_delta"])
            assessment = (
                "Direct bounded Lake package-version configuration and module"
                " artifact evidence; complete preparation identity and real"
                " archive remain at the inherited product gate.")
            relation = "direct bounded I090 Lake package-version identity evidence"
            review = HERE.parent.name
            files = [f"reports/{PACKAGE}/{name}" for name in EVIDENCE]
            packages = [PACKAGE]
        elif item in CONTEXT:
            residual = old["v60_specific_remaining_delta"]
            assessment = (
                "F05 gains bounded context from the Lake version-only control;"
                " its broader collisions and product residual remain unchanged.")
            relation = "bounded context evidence"
            review = HERE.parent.name
            files = [f"reports/{PACKAGE}/{name}" for name in EVIDENCE]
            packages = [PACKAGE]
        else:
            residual = old["v60_specific_remaining_delta"]
            assessment = (
                f"The Lake package-version identity package does not directly exercise {item}"
                f" ({row['title']}); the v60 residual and prerequisite remain.")
            relation = "no direct v61 evidence"
            review = old["v60_review_package"]
            files = []
            packages = []
        row.update({
            "v61_status": old["v60_status"],
            "v61_gate_categories": old["v60_gate_categories"],
            "v61_specific_remaining_delta": residual,
            "v61_scope_assessment": assessment,
            "v61_review_package": review,
            "v61_new_evidence_packages": packages,
            "v61_evidence_files": files,
            "v61_next_prerequisite": old["v60_next_prerequisite"],
            "v61_evidence_relation": relation,
        })
        out.append(row)
    assert {row["id"] for row in out if row["v61_specific_remaining_delta"] != row["v60_specific_remaining_delta"]} == set(DIRECT)
    assert all(row["v61_status"] == row["v60_status"] and
               row["v61_gate_categories"] == row["v60_gate_categories"] and
               row["v61_next_prerequisite"] == row["v60_next_prerequisite"] for row in out)
    (HERE / "row-challenge-v61.json").write_text(json.dumps(out, indent=2, sort_keys=True, ensure_ascii=False) + "\n")
    by_id = {row["id"]: row for row in out}

    def extend(old_name, key, new_name):
        rows = []
        for old in read_csv(V60 / old_name):
            row = dict(old)
            source = by_id[row[key]]
            for field in NEW_FIELDS:
                value = source[field]
                row[field] = ";".join(value) if isinstance(value, list) else value
            rows.append(row)
        write_csv(HERE / new_name, rows)
        return rows

    investigations = extend("investigation-final-v60.csv", "id", "investigation-final-v61.csv")
    suggestions = extend("3730-crosswalk-final-v60.csv", "3730_id", "3730-crosswalk-final-v61.csv")
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
    write_csv(HERE / "source-package-inventory-v61.csv", inventory)
    generated = (
        "row-challenge-v61.json", "investigation-final-v61.csv",
        "3730-crosswalk-final-v61.csv", "source-package-inventory-v61.csv",
    )
    inputs = {
        "v60/row-challenge-v60.json": V60 / "row-challenge-v60.json",
        "v60/investigation-final-v60.csv": V60 / "investigation-final-v60.csv",
        "v60/3730-crosswalk-final-v60.csv": V60 / "3730-crosswalk-final-v60.csv",
        "live-issue-snapshot-v61.json": HERE / "live-issue-snapshot-v61.json",
    }
    validation = {
        "reference_tip_at_start": "97677918e2120591c57486a353ee1b75e2f0bd6f",
        "source_reference_package": V60_NAME,
        "source_anneal_revision": "bd0956be95c5f798f0c0484921b9b9d1fc6e9988",
        "issue_snapshot_relation": "fresh public REST fetch; issue fields unchanged from v60",
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
    (HERE / "validation-v61.json").write_text(json.dumps(validation, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: validation[key] for key in (
        "row_count", "suggestion_destination_links", "changed_residual_ids", "inventory_files")}, sort_keys=True))


if __name__ == "__main__":
    main()
