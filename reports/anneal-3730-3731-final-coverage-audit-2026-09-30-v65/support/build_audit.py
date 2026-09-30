#!/usr/bin/env python3
"""Derive v65 from published v64 and one preseeded valid Lake server goal."""

import csv
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V64_NAME = "anneal-3730-3731-final-coverage-audit-2026-09-30-v64"
V64 = REPORTS / V64_NAME / "support"
PACKAGE = "anneal-3731-i092-preseeded-valid-server-goal-2026-09-30"
PACKAGES = (V64_NAME, PACKAGE)
DIRECT = {"I092": PACKAGE}
CONTEXT = {"F07": PACKAGE}
EVIDENCE = tuple(path.relative_to(REPORTS / PACKAGE).as_posix()
                 for path in sorted((REPORTS / PACKAGE).rglob("*"))
                 if path.is_file() and "__pycache__" not in path.parts and path.suffix != ".pyc")
NEW_FIELDS = (
    "v65_status", "v65_gate_categories", "v65_specific_remaining_delta",
    "v65_scope_assessment", "v65_review_package", "v65_new_evidence_packages",
    "v65_evidence_files", "v65_next_prerequisite", "v65_evidence_relation",
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
        stale = ("no document was opened, so import and goal behavior in that"
                 " fallback remain untested.")
        historical = ("no document was opened in that earlier malformed-fallback"
                      " cell, so import and goal behavior in that fallback"
                      " remain untested.")
        assert previous.count(stale) == 1
        return previous.replace(stale, historical) + (
            " A later byte-exact preseeded copy of the valid producer/consumer"
            " tree at a new private path launched only Lake --no-build"
            " --no-cache serve. It opened Generated.lean, reported #eval 7,"
            " reached a processing-empty quiescent state, and returned the"
            " live goal depValue = 7; producer/cache and work inventories"
            " were unchanged. The planned malformed server was denied before"
            " launch at 29.8279% reclaimable RAM, and the semantic"
            " no-dependency server did not run. This is a valid relocated"
            " positive control, not a malformed-manifest fallback test or"
            " an actual Anneal prepared archive.")
    return previous


def main():
    live = json.loads((HERE / "live-issue-snapshot-v65.json").read_text())
    earlier = json.loads((V64 / "live-issue-snapshot-v64.json").read_text())
    assert live["issues"] == earlier["issues"]
    assert live["fetched_at_utc"] != earlier["fetched_at_utc"]
    assert live["source"] == "public GitHub REST issue and comments endpoints"
    assert live["issues"]["3730"]["state"] == "closed"
    assert live["issues"]["3731"]["state"] == "open"
    old_rows = json.loads((V64 / "row-challenge-v64.json").read_text())
    assert len(old_rows) == 333 and len({row["id"] for row in old_rows}) == 333
    assert all((REPORTS / PACKAGE / name).is_file() for name in EVIDENCE)
    out = []
    for old in old_rows:
        row = dict(old)
        item = row["id"]
        if item in DIRECT:
            residual = updated_residual(item, old["v64_specific_remaining_delta"])
            assessment = (
                "Direct bounded valid preseeded Lake server goal evidence;"
                " malformed fallback and actual Anneal archive remain at the"
                " inherited product gate.")
            relation = "direct bounded I092 preseeded valid-server goal evidence"
            review = HERE.parent.name
            files = [f"reports/{PACKAGE}/{name}" for name in EVIDENCE]
            packages = [PACKAGE]
        elif item in CONTEXT:
            residual = old["v64_specific_remaining_delta"]
            assessment = (
                "F07 gains a valid relocated no-build server control through"
                " I092; its malformed/product residual remains unchanged.")
            relation = "bounded context evidence"
            review = HERE.parent.name
            files = [f"reports/{PACKAGE}/{name}" for name in EVIDENCE]
            packages = [PACKAGE]
        else:
            residual = old["v64_specific_remaining_delta"]
            assessment = (
                f"The preseeded valid-server package does not directly exercise {item}"
                f" ({row['title']}); the v64 residual and prerequisite remain.")
            relation = "no direct v65 evidence"
            review = old["v64_review_package"]
            files = []
            packages = []
        row.update({
            "v65_status": old["v64_status"],
            "v65_gate_categories": old["v64_gate_categories"],
            "v65_specific_remaining_delta": residual,
            "v65_scope_assessment": assessment,
            "v65_review_package": review,
            "v65_new_evidence_packages": packages,
            "v65_evidence_files": files,
            "v65_next_prerequisite": old["v64_next_prerequisite"],
            "v65_evidence_relation": relation,
        })
        out.append(row)
    assert {row["id"] for row in out if row["v65_specific_remaining_delta"] != row["v64_specific_remaining_delta"]} == set(DIRECT)
    assert all(row["v65_status"] == row["v64_status"] and
               row["v65_gate_categories"] == row["v64_gate_categories"] and
               row["v65_next_prerequisite"] == row["v64_next_prerequisite"] for row in out)
    (HERE / "row-challenge-v65.json").write_text(json.dumps(out, indent=2, sort_keys=True, ensure_ascii=False) + "\n")
    by_id = {row["id"]: row for row in out}

    def extend(old_name, key, new_name):
        rows = []
        for old in read_csv(V64 / old_name):
            row = dict(old)
            source = by_id[row[key]]
            for field in NEW_FIELDS:
                value = source[field]
                row[field] = ";".join(value) if isinstance(value, list) else value
            rows.append(row)
        write_csv(HERE / new_name, rows)
        return rows

    investigations = extend("investigation-final-v64.csv", "id", "investigation-final-v65.csv")
    suggestions = extend("3730-crosswalk-final-v64.csv", "3730_id", "3730-crosswalk-final-v65.csv")
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
    write_csv(HERE / "source-package-inventory-v65.csv", inventory)
    generated = (
        "row-challenge-v65.json", "investigation-final-v65.csv",
        "3730-crosswalk-final-v65.csv", "source-package-inventory-v65.csv",
    )
    inputs = {
        "v64/row-challenge-v64.json": V64 / "row-challenge-v64.json",
        "v64/investigation-final-v64.csv": V64 / "investigation-final-v64.csv",
        "v64/3730-crosswalk-final-v64.csv": V64 / "3730-crosswalk-final-v64.csv",
        "live-issue-snapshot-v65.json": HERE / "live-issue-snapshot-v65.json",
    }
    validation = {
        "reference_tip_at_start": "e2692485db6b8417bf415c83223cfc5a99e73e4f",
        "source_reference_package": V64_NAME,
        "source_anneal_revision": "bd0956be95c5f798f0c0484921b9b9d1fc6e9988",
        "issue_snapshot_relation": "fresh public REST fetch; issue fields unchanged from v64",
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
    (HERE / "validation-v65.json").write_text(json.dumps(validation, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: validation[key] for key in (
        "row_count", "suggestion_destination_links", "changed_residual_ids", "inventory_files")}, sort_keys=True))


if __name__ == "__main__":
    main()
