#!/usr/bin/env python3
"""Derive v64 from published v63 and two staggered Charon reader/collision pairs."""

import csv
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V63_NAME = "anneal-3730-3731-final-coverage-audit-2026-09-30-v63"
V63 = REPORTS / V63_NAME / "support"
PACKAGE = "anneal-3731-i076-live-reader-shared-destination-2026-09-30"
PACKAGES = (V63_NAME, PACKAGE)
DIRECT = {"I020": PACKAGE, "I076": PACKAGE}
CONTEXT = {"D07": PACKAGE}
EVIDENCE = tuple(path.relative_to(REPORTS / PACKAGE).as_posix()
                 for path in sorted((REPORTS / PACKAGE).rglob("*"))
                 if path.is_file() and "__pycache__" not in path.parts and path.suffix != ".pyc")
NEW_FIELDS = (
    "v64_status", "v64_gate_categories", "v64_specific_remaining_delta",
    "v64_scope_assessment", "v64_review_package", "v64_new_evidence_packages",
    "v64_evidence_files", "v64_next_prerequisite", "v64_evidence_relation",
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
    if item == "I020":
        assert "One guarded concurrent release/cfg Charon pair" in previous
        return previous + (
            " Two further staggered Charon release/cfg pairs with the same"
            " unchanged source and private targets each had two exit-0"
            " processes at one initially absent destination. Release-first"
            " ended with a 5,520-byte nonparseable LLBC: a complete cfg model"
            " (7/29) followed by literal e}. Cfg-first reader snapshots"
            " moved from a complete cfg model to a complete release model"
            " (11/23), the final file. This is direct component collision"
            " evidence, not an Anneal selector or proof-context mismatch.")
    if item == "I076":
        stale = ("The file was inspected only after both settled; in-flight"
                 " write order, atomicity, repeated schedules, collision"
                 " rejection and Anneal output ownership remain untested.")
        historical = ("That earlier file was inspected only after both settled;"
                      " no reader sampled it during that pair. Low-level write"
                      " order, atomicity, statistical repeatability, collision"
                      " rejection and Anneal output ownership remain untested.")
        assert previous.count(stale) == 1
        return previous.replace(stale, historical) + (
            " Two additional staggered release/cfg pairs now retained a"
            " read-only poller transcript. All four writers exited 0; one"
            " pair's final 5,520-byte shared LLBC failed strict JSON parse"
            " after a complete cfg model prefix and literal e} suffix. The"
            " opposite order exposed complete cfg then release byte states"
            " and ended with the release model. Matching double reads and"
            " sampled simultaneous process residency do not establish"
            " atomic publication, syscall order or a general winner rule."
            " Actual Anneal output ownership remains at the product gate.")
    return previous


def main():
    live = json.loads((HERE / "live-issue-snapshot-v64.json").read_text())
    earlier = json.loads((V63 / "live-issue-snapshot-v63.json").read_text())
    assert live["issues"] == earlier["issues"]
    assert live["fetched_at_utc"] != earlier["fetched_at_utc"]
    assert live["source"] == "public GitHub REST issue and comments endpoints"
    assert live["issues"]["3730"]["state"] == "closed"
    assert live["issues"]["3731"]["state"] == "open"
    old_rows = json.loads((V63 / "row-challenge-v63.json").read_text())
    assert len(old_rows) == 333 and len({row["id"] for row in old_rows}) == 333
    assert all((REPORTS / PACKAGE / name).is_file() for name in EVIDENCE)
    out = []
    for old in old_rows:
        row = dict(old)
        item = row["id"]
        if item in DIRECT:
            residual = updated_residual(item, old["v63_specific_remaining_delta"])
            assessment = (
                "Direct bounded staggered shared-destination Charon evidence;"
                " actual Anneal selector/publisher remain at the inherited"
                " product gate.")
            relation = "direct bounded I020/I076 shared-destination reader evidence"
            review = HERE.parent.name
            files = [f"reports/{PACKAGE}/{name}" for name in EVIDENCE]
            packages = [PACKAGE]
        elif item in CONTEXT:
            residual = old["v63_specific_remaining_delta"]
            assessment = (
                "D07 gains bounded Charon collision and reader context through"
                " I020/I076; its product residual remains unchanged.")
            relation = "bounded context evidence"
            review = HERE.parent.name
            files = [f"reports/{PACKAGE}/{name}" for name in EVIDENCE]
            packages = [PACKAGE]
        else:
            residual = old["v63_specific_remaining_delta"]
            assessment = (
                f"The staggered Charon reader package does not directly exercise {item}"
                f" ({row['title']}); the v63 residual and prerequisite remain.")
            relation = "no direct v64 evidence"
            review = old["v63_review_package"]
            files = []
            packages = []
        row.update({
            "v64_status": old["v63_status"],
            "v64_gate_categories": old["v63_gate_categories"],
            "v64_specific_remaining_delta": residual,
            "v64_scope_assessment": assessment,
            "v64_review_package": review,
            "v64_new_evidence_packages": packages,
            "v64_evidence_files": files,
            "v64_next_prerequisite": old["v63_next_prerequisite"],
            "v64_evidence_relation": relation,
        })
        out.append(row)
    assert {row["id"] for row in out if row["v64_specific_remaining_delta"] != row["v63_specific_remaining_delta"]} == set(DIRECT)
    assert all(row["v64_status"] == row["v63_status"] and
               row["v64_gate_categories"] == row["v63_gate_categories"] and
               row["v64_next_prerequisite"] == row["v63_next_prerequisite"] for row in out)
    (HERE / "row-challenge-v64.json").write_text(json.dumps(out, indent=2, sort_keys=True, ensure_ascii=False) + "\n")
    by_id = {row["id"]: row for row in out}

    def extend(old_name, key, new_name):
        rows = []
        for old in read_csv(V63 / old_name):
            row = dict(old)
            source = by_id[row[key]]
            for field in NEW_FIELDS:
                value = source[field]
                row[field] = ";".join(value) if isinstance(value, list) else value
            rows.append(row)
        write_csv(HERE / new_name, rows)
        return rows

    investigations = extend("investigation-final-v63.csv", "id", "investigation-final-v64.csv")
    suggestions = extend("3730-crosswalk-final-v63.csv", "3730_id", "3730-crosswalk-final-v64.csv")
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
    write_csv(HERE / "source-package-inventory-v64.csv", inventory)
    generated = (
        "row-challenge-v64.json", "investigation-final-v64.csv",
        "3730-crosswalk-final-v64.csv", "source-package-inventory-v64.csv",
    )
    inputs = {
        "v63/row-challenge-v63.json": V63 / "row-challenge-v63.json",
        "v63/investigation-final-v63.csv": V63 / "investigation-final-v63.csv",
        "v63/3730-crosswalk-final-v63.csv": V63 / "3730-crosswalk-final-v63.csv",
        "live-issue-snapshot-v64.json": HERE / "live-issue-snapshot-v64.json",
    }
    validation = {
        "reference_tip_at_start": "6318115869e612a771ffceb26f10d7bd3a15f257",
        "source_reference_package": V63_NAME,
        "source_anneal_revision": "bd0956be95c5f798f0c0484921b9b9d1fc6e9988",
        "issue_snapshot_relation": "fresh public REST fetch; issue fields unchanged from v63",
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
    (HERE / "validation-v64.json").write_text(json.dumps(validation, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: validation[key] for key in (
        "row_count", "suggestion_destination_links", "changed_residual_ids", "inventory_files")}, sort_keys=True))


if __name__ == "__main__":
    main()
