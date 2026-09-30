#!/usr/bin/env python3
"""Derive v47 from published v46 and the sequential Charon destination report."""

import csv
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V46_NAME = "anneal-3730-3731-final-coverage-audit-2026-09-30-v46"
V46 = REPORTS / V46_NAME / "support"
PACKAGE = "anneal-3731-i076-sequential-shared-destination-2026-09-30"
PACKAGES = (V46_NAME, PACKAGE)
DIRECT = {"I020": PACKAGE, "I076": PACKAGE}
CONTEXT = {"D07": PACKAGE}
EVIDENCE = (
    "REPORT.md", "REPORT.json", "support/results.json", "support/check.py",
    "support/probe.py", "support/acquisition-probe.py.txt",
    "support/artifacts/control-release.llbc", "support/artifacts/control-cfg_alt.llbc",
    "support/artifacts/release_then_cfg-step1.llbc",
    "support/artifacts/release_then_cfg-step2.llbc",
    "support/artifacts/cfg_then_release-step1.llbc",
    "support/artifacts/cfg_then_release-step2.llbc",
)
NEW_FIELDS = (
    "v47_status", "v47_gate_categories", "v47_specific_remaining_delta",
    "v47_scope_assessment", "v47_review_package", "v47_new_evidence_packages",
    "v47_evidence_files", "v47_next_prerequisite", "v47_evidence_relation",
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
        previous = previous.replace(
            "not a V2 CLI invocation, observed overwrite, proof-context selection or cross-stage mismatch rejection.",
            "not a V2 CLI invocation, proof-context selection or cross-stage mismatch rejection.")
        assert "observed overwrite" not in previous
        return previous + (
            " A new guarded sequential Charon probe used two initially absent shared destinations."
            " Release→cfg and cfg→release each exited 0 twice; immediate LLBC snapshots matched"
            " the later compilation subject's selected literals (11/23 or 7/29) after the second"
            " write. This observes Charon's serial shared-path outcome for one fixture, not Anneal"
            " publication, integrated subject selection or a proof mismatch.")
    if item == "I076":
        previous = previous.replace("writer ordering, collision rejection",
                                    "concurrent writer ordering, collision rejection")
        assert "concurrent writer ordering" in previous
        return previous + (
            " A new two-order serial Charon cell shows both profile/cfg writers succeed at one"
            " initially absent path and the second selected model occupies that path in each order."
            " This narrows sequential destination ownership only; it does not cover concurrent"
            " writers, complete compilation-unit identity or Anneal's publisher.")
    return previous


def main():
    live = json.loads((HERE / "live-issue-snapshot-v47.json").read_text())
    assert live == json.loads((V46 / "live-issue-snapshot-v46.json").read_text())
    assert live["issues"]["3730"]["state"] == "closed"
    assert live["issues"]["3731"]["state"] == "open"
    old_rows = json.loads((V46 / "row-challenge-v46.json").read_text())
    assert len(old_rows) == 333 and len({row["id"] for row in old_rows}) == 333
    assert all((REPORTS / PACKAGE / name).is_file() for name in EVIDENCE)
    out = []
    for old in old_rows:
        row = dict(old)
        item = row["id"]
        if item in DIRECT:
            residual = updated_residual(item, old["v46_specific_remaining_delta"])
            assessment = (
                "Direct bounded sequential Charon shared-destination evidence for profile/cfg"
                " subjects; Anneal publication, invalidation and proof-consumer behavior remain"
                " at the inherited product gate.")
            relation = "direct bounded sequential Charon destination evidence"
            review = HERE.parent.name
            files = [f"reports/{PACKAGE}/{name}" for name in EVIDENCE]
            packages = [PACKAGE]
        elif item in CONTEXT:
            residual = old["v46_specific_remaining_delta"]
            assessment = (
                "The sequential Charon shared-destination result adds bounded component context"
                " to D07's compilation-subject matrix; the Anneal invalidation residual, product"
                " gate and next prerequisite remain unchanged.")
            relation = "bounded sequential Charon destination context"
            review = HERE.parent.name
            files = [f"reports/{PACKAGE}/{name}" for name in EVIDENCE]
            packages = [PACKAGE]
        else:
            residual = old["v46_specific_remaining_delta"]
            assessment = (
                f"The sequential Charon destination package does not directly exercise {item}"
                f" ({row['title']}); the v46 residual and prerequisite remain.")
            relation = "no direct v47 evidence"
            review = old["v46_review_package"]
            files = []
            packages = []
        row.update({
            "v47_status": old["v46_status"],
            "v47_gate_categories": old["v46_gate_categories"],
            "v47_specific_remaining_delta": residual,
            "v47_scope_assessment": assessment,
            "v47_review_package": review,
            "v47_new_evidence_packages": packages,
            "v47_evidence_files": files,
            "v47_next_prerequisite": old["v46_next_prerequisite"],
            "v47_evidence_relation": relation,
        })
        out.append(row)
    assert {row["id"] for row in out if row["v47_specific_remaining_delta"] != row["v46_specific_remaining_delta"]} == set(DIRECT)
    assert all(row["v47_status"] == row["v46_status"] and
               row["v47_gate_categories"] == row["v46_gate_categories"] and
               row["v47_next_prerequisite"] == row["v46_next_prerequisite"] for row in out)
    (HERE / "row-challenge-v47.json").write_text(json.dumps(out, indent=2, sort_keys=True, ensure_ascii=False) + "\n")
    by_id = {row["id"]: row for row in out}

    def extend(old_name, key, new_name):
        rows = []
        for old in read_csv(V46 / old_name):
            row = dict(old)
            source = by_id[row[key]]
            for field in NEW_FIELDS:
                value = source[field]
                row[field] = ";".join(value) if isinstance(value, list) else value
            rows.append(row)
        write_csv(HERE / new_name, rows)
        return rows

    investigations = extend("investigation-final-v46.csv", "id", "investigation-final-v47.csv")
    suggestions = extend("3730-crosswalk-final-v46.csv", "3730_id", "3730-crosswalk-final-v47.csv")
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
    write_csv(HERE / "source-package-inventory-v47.csv", inventory)
    generated = (
        "row-challenge-v47.json", "investigation-final-v47.csv",
        "3730-crosswalk-final-v47.csv", "source-package-inventory-v47.csv",
    )
    inputs = {
        "v46/row-challenge-v46.json": V46 / "row-challenge-v46.json",
        "v46/investigation-final-v46.csv": V46 / "investigation-final-v46.csv",
        "v46/3730-crosswalk-final-v46.csv": V46 / "3730-crosswalk-final-v46.csv",
        "live-issue-snapshot-v47.json": HERE / "live-issue-snapshot-v47.json",
    }
    validation = {
        "reference_tip_at_start": "24eb9c0b5896c54d24884755f68dfe5b8b077d20",
        "source_reference_package": V46_NAME,
        "source_anneal_revision": "bd0956be95c5f798f0c0484921b9b9d1fc6e9988",
        "issue_snapshot_relation": "exact inherited v46 snapshot; no fresh fetch",
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
    (HERE / "validation-v47.json").write_text(json.dumps(validation, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: validation[key] for key in (
        "row_count", "suggestion_destination_links", "changed_residual_ids", "inventory_files")}, sort_keys=True))


if __name__ == "__main__":
    main()
