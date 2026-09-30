#!/usr/bin/env python3
"""Derive v63 from published v62 and one malformed-manifest preflight probe."""

import csv
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V62_NAME = "anneal-3730-3731-final-coverage-audit-2026-09-30-v62"
V62 = REPORTS / V62_NAME / "support"
PACKAGE = "anneal-3731-i092-malformed-manifest-preflight-2026-09-30"
PACKAGES = (V62_NAME, PACKAGE)
DIRECT = {"I092": PACKAGE}
CONTEXT = {"F07": PACKAGE}
EVIDENCE = tuple(path.relative_to(REPORTS / PACKAGE).as_posix()
                 for path in sorted((REPORTS / PACKAGE).rglob("*"))
                 if path.is_file() and "__pycache__" not in path.parts and path.suffix != ".pyc")
NEW_FIELDS = (
    "v63_status", "v63_gate_categories", "v63_specific_remaining_delta",
    "v63_scope_assessment", "v63_review_package", "v63_new_evidence_packages",
    "v63_evidence_files", "v63_next_prerequisite", "v63_evidence_relation",
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
        stale = ("These are net producer/cache inventories, not syscall traces;"
                 " malformed manifests, native/plugin families, actual Anneal"
                 " archive, exact server no-build launcher and full read-only"
                 " policy remain untested.")
        historical = ("These earlier observations are net producer/cache"
                      " inventories, not syscall traces; that earlier cell did"
                      " not test malformed manifests, native/plugin families,"
                      " the actual Anneal archive, the exact server no-build"
                      " launcher or full read-only policy.")
        assert previous.count(stale) == 1
        return previous.replace(stale, historical) + (
            " In a separate pinned two-package fixture, replacing only the"
            " consumer manifest with an opening brace plus LF made offline"
            " --no-build/--no-cache Lake setup-file and Lake-mediated batch"
            " exit 1 with invalid JSON. Lake serve instead reported fallback"
            " to plain lean --server and completed initialize/shutdown; no"
            " document was opened, so import and goal behavior in that"
            " fallback remain untested. Direct Lean with explicit LEAN_PATH"
            " still imported the retained producer OLean, and restoring the"
            " exact valid manifest restored all three Lake controls."
            " Other malformed inputs, native/plugin families, actual Anneal"
            " archive, enforced read-only policy and exact product launcher"
            " remain at the inherited gate.")
    return previous


def main():
    live = json.loads((HERE / "live-issue-snapshot-v63.json").read_text())
    earlier = json.loads((V62 / "live-issue-snapshot-v62.json").read_text())
    assert live["issues"] == earlier["issues"]
    assert live["fetched_at_utc"] != earlier["fetched_at_utc"]
    assert live["source"] == "public GitHub REST issue and comments endpoints"
    assert live["issues"]["3730"]["state"] == "closed"
    assert live["issues"]["3731"]["state"] == "open"
    old_rows = json.loads((V62 / "row-challenge-v62.json").read_text())
    assert len(old_rows) == 333 and len({row["id"] for row in old_rows}) == 333
    assert all((REPORTS / PACKAGE / name).is_file() for name in EVIDENCE)
    out = []
    for old in old_rows:
        row = dict(old)
        item = row["id"]
        if item in DIRECT:
            residual = updated_residual(item, old["v62_specific_remaining_delta"])
            assessment = (
                "Direct bounded malformed-manifest setup, batch and server"
                " fallback evidence; actual Anneal launcher and archive"
                " remain at the inherited product gate.")
            relation = "direct bounded I092 malformed-manifest preflight evidence"
            review = HERE.parent.name
            files = [f"reports/{PACKAGE}/{name}" for name in EVIDENCE]
            packages = [PACKAGE]
        elif item in CONTEXT:
            residual = old["v62_specific_remaining_delta"]
            assessment = (
                "F07 gains bounded malformed-manifest context through I092;"
                " its actual-product residual remains unchanged.")
            relation = "bounded context evidence"
            review = HERE.parent.name
            files = [f"reports/{PACKAGE}/{name}" for name in EVIDENCE]
            packages = [PACKAGE]
        else:
            residual = old["v62_specific_remaining_delta"]
            assessment = (
                f"The malformed-manifest package does not directly exercise {item}"
                f" ({row['title']}); the v62 residual and prerequisite remain.")
            relation = "no direct v63 evidence"
            review = old["v62_review_package"]
            files = []
            packages = []
        row.update({
            "v63_status": old["v62_status"],
            "v63_gate_categories": old["v62_gate_categories"],
            "v63_specific_remaining_delta": residual,
            "v63_scope_assessment": assessment,
            "v63_review_package": review,
            "v63_new_evidence_packages": packages,
            "v63_evidence_files": files,
            "v63_next_prerequisite": old["v62_next_prerequisite"],
            "v63_evidence_relation": relation,
        })
        out.append(row)
    assert {row["id"] for row in out if row["v63_specific_remaining_delta"] != row["v62_specific_remaining_delta"]} == set(DIRECT)
    assert all(row["v63_status"] == row["v62_status"] and
               row["v63_gate_categories"] == row["v62_gate_categories"] and
               row["v63_next_prerequisite"] == row["v62_next_prerequisite"] for row in out)
    (HERE / "row-challenge-v63.json").write_text(json.dumps(out, indent=2, sort_keys=True, ensure_ascii=False) + "\n")
    by_id = {row["id"]: row for row in out}

    def extend(old_name, key, new_name):
        rows = []
        for old in read_csv(V62 / old_name):
            row = dict(old)
            source = by_id[row[key]]
            for field in NEW_FIELDS:
                value = source[field]
                row[field] = ";".join(value) if isinstance(value, list) else value
            rows.append(row)
        write_csv(HERE / new_name, rows)
        return rows

    investigations = extend("investigation-final-v62.csv", "id", "investigation-final-v63.csv")
    suggestions = extend("3730-crosswalk-final-v62.csv", "3730_id", "3730-crosswalk-final-v63.csv")
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
    write_csv(HERE / "source-package-inventory-v63.csv", inventory)
    generated = (
        "row-challenge-v63.json", "investigation-final-v63.csv",
        "3730-crosswalk-final-v63.csv", "source-package-inventory-v63.csv",
    )
    inputs = {
        "v62/row-challenge-v62.json": V62 / "row-challenge-v62.json",
        "v62/investigation-final-v62.csv": V62 / "investigation-final-v62.csv",
        "v62/3730-crosswalk-final-v62.csv": V62 / "3730-crosswalk-final-v62.csv",
        "live-issue-snapshot-v63.json": HERE / "live-issue-snapshot-v63.json",
    }
    validation = {
        "reference_tip_at_start": "249263d6b8c2aed57a3d2757947458e636f126c0",
        "source_reference_package": V62_NAME,
        "source_anneal_revision": "bd0956be95c5f798f0c0484921b9b9d1fc6e9988",
        "issue_snapshot_relation": "fresh public REST fetch; issue fields unchanged from v62",
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
    (HERE / "validation-v63.json").write_text(json.dumps(validation, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: validation[key] for key in (
        "row_count", "suggestion_destination_links", "changed_residual_ids", "inventory_files")}, sort_keys=True))


if __name__ == "__main__":
    main()
