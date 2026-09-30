#!/usr/bin/env python3
"""Derive v58 from published v57 and one direct Lean RPC keep-alive cell."""

import csv
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V57_NAME = "anneal-3730-3731-final-coverage-audit-2026-09-30-v57"
V57 = REPORTS / V57_NAME / "support"
PACKAGE = "anneal-3731-i044-rpc-keepalive-positive-2026-09-30"
PACKAGES = (V57_NAME, PACKAGE)
DIRECT = {"I044": PACKAGE}
CONTEXT = {"C08": PACKAGE}
EVIDENCE = tuple(path.relative_to(REPORTS / PACKAGE).as_posix()
                 for path in sorted((REPORTS / PACKAGE).rglob("*"))
                 if path.is_file() and "__pycache__" not in path.parts and path.suffix != ".pyc")
NEW_FIELDS = (
    "v58_status", "v58_gate_categories", "v58_specific_remaining_delta",
    "v58_scope_assessment", "v58_review_package", "v58_new_evidence_packages",
    "v58_evidence_files", "v58_next_prerequisite", "v58_evidence_relation",
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
    if item == "I044":
        assert "42-second no-keep-alive run" in previous
        return previous + (
            " A separate direct Lean 4.30.0-rc2 positive control sent five"
            " $/lean/rpc/keepAlive notifications at roughly eight-second"
            " intervals, then successfully dereferenced the same InfoWithCtx"
            " reference and session after 43.1137 seconds with no edit, reopen,"
            " restart, or release. The prior no-message 42.01-second control expired"
            " with -32900. This is one reference and one bounded schedule;"
            " retention across many references and Anneal generation-specific"
            " policy remain.")
    return previous


def main():
    live = json.loads((HERE / "live-issue-snapshot-v58.json").read_text())
    earlier = json.loads((V57 / "live-issue-snapshot-v57.json").read_text())
    assert live["issues"] == earlier["issues"]
    assert live["fetched_at_utc"] != earlier["fetched_at_utc"]
    assert live["source"] == "public GitHub REST issue and comments endpoints"
    assert live["issues"]["3730"]["state"] == "closed"
    assert live["issues"]["3731"]["state"] == "open"
    old_rows = json.loads((V57 / "row-challenge-v57.json").read_text())
    assert len(old_rows) == 333 and len({row["id"] for row in old_rows}) == 333
    assert all((REPORTS / PACKAGE / name).is_file() for name in EVIDENCE)
    out = []
    for old in old_rows:
        row = dict(old)
        item = row["id"]
        if item in DIRECT:
            residual = updated_residual(item, old["v57_specific_remaining_delta"])
            assessment = (
                "Direct bounded Lean RPC keep-alive positive control on a real"
                " InfoWithCtx reference; many-reference and Anneal generation"
                " policy remain at the inherited product gate.")
            relation = "direct bounded I044 Lean RPC keep-alive evidence"
            review = HERE.parent.name
            files = [f"reports/{PACKAGE}/{name}" for name in EVIDENCE]
            packages = [PACKAGE]
        elif item in CONTEXT:
            residual = old["v57_specific_remaining_delta"]
            assessment = (
                "The positive RPC keep-alive control adds context to this handle"
                " lifetime row; its Anneal residual, product gate and next"
                " prerequisite remain unchanged.")
            relation = "bounded C08 RPC-handle context evidence"
            review = HERE.parent.name
            files = [f"reports/{PACKAGE}/{name}" for name in EVIDENCE]
            packages = [PACKAGE]
        else:
            residual = old["v57_specific_remaining_delta"]
            assessment = (
                f"The Lean RPC keep-alive package does not directly exercise {item}"
                f" ({row['title']}); the v57 residual and prerequisite remain.")
            relation = "no direct v58 evidence"
            review = old["v57_review_package"]
            files = []
            packages = []
        row.update({
            "v58_status": old["v57_status"],
            "v58_gate_categories": old["v57_gate_categories"],
            "v58_specific_remaining_delta": residual,
            "v58_scope_assessment": assessment,
            "v58_review_package": review,
            "v58_new_evidence_packages": packages,
            "v58_evidence_files": files,
            "v58_next_prerequisite": old["v57_next_prerequisite"],
            "v58_evidence_relation": relation,
        })
        out.append(row)
    assert {row["id"] for row in out if row["v58_specific_remaining_delta"] != row["v57_specific_remaining_delta"]} == set(DIRECT)
    assert all(row["v58_status"] == row["v57_status"] and
               row["v58_gate_categories"] == row["v57_gate_categories"] and
               row["v58_next_prerequisite"] == row["v57_next_prerequisite"] for row in out)
    (HERE / "row-challenge-v58.json").write_text(json.dumps(out, indent=2, sort_keys=True, ensure_ascii=False) + "\n")
    by_id = {row["id"]: row for row in out}

    def extend(old_name, key, new_name):
        rows = []
        for old in read_csv(V57 / old_name):
            row = dict(old)
            source = by_id[row[key]]
            for field in NEW_FIELDS:
                value = source[field]
                row[field] = ";".join(value) if isinstance(value, list) else value
            rows.append(row)
        write_csv(HERE / new_name, rows)
        return rows

    investigations = extend("investigation-final-v57.csv", "id", "investigation-final-v58.csv")
    suggestions = extend("3730-crosswalk-final-v57.csv", "3730_id", "3730-crosswalk-final-v58.csv")
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
    write_csv(HERE / "source-package-inventory-v58.csv", inventory)
    generated = (
        "row-challenge-v58.json", "investigation-final-v58.csv",
        "3730-crosswalk-final-v58.csv", "source-package-inventory-v58.csv",
    )
    inputs = {
        "v57/row-challenge-v57.json": V57 / "row-challenge-v57.json",
        "v57/investigation-final-v57.csv": V57 / "investigation-final-v57.csv",
        "v57/3730-crosswalk-final-v57.csv": V57 / "3730-crosswalk-final-v57.csv",
        "live-issue-snapshot-v58.json": HERE / "live-issue-snapshot-v58.json",
    }
    validation = {
        "reference_tip_at_start": "30b9d5749aed6049d949f4f582dd64c70088d07a",
        "source_reference_package": V57_NAME,
        "source_anneal_revision": "bd0956be95c5f798f0c0484921b9b9d1fc6e9988",
        "issue_snapshot_relation": "fresh public REST fetch; issue fields unchanged from v57",
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
    (HERE / "validation-v58.json").write_text(json.dumps(validation, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: validation[key] for key in (
        "row_count", "suggestion_destination_links", "changed_residual_ids", "inventory_files")}, sort_keys=True))


if __name__ == "__main__":
    main()
