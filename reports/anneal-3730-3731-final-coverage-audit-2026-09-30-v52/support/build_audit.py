#!/usr/bin/env python3
"""Derive v52 from published v51 and the Lean 4.29 encoding comparison."""

import csv
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V51_NAME = "anneal-3730-3731-final-coverage-audit-2026-09-30-v51"
V51 = REPORTS / V51_NAME / "support"
PACKAGE = "anneal-3731-i062-lean429-version-diff-2026-09-30"
PACKAGES = (V51_NAME, PACKAGE)
DIRECT = {"I062": PACKAGE}
CONTEXT = {"B03": PACKAGE, "I025": PACKAGE}
EVIDENCE = (
    "REPORT.md", "REPORT.json", "probe.py", "oracle.py", "oracle.json",
    "check.py", "results.json", "comparison.json", "fixture/Encoding.lean",
    "fixture/EncodingPatched.lean", "baseline-v430-results.json",
    "baseline-v430-batch-original.stdout", "baseline-v430-batch-patched.stdout",
    "raw/utf8_only.client-wire",
    "raw/utf8_only.server-wire", "raw/utf16_only.client-wire",
    "raw/utf16_only.server-wire", "raw/batch-original.stdout",
    "raw/batch-patched.stdout",
)
NEW_FIELDS = (
    "v52_status", "v52_gate_categories", "v52_specific_remaining_delta",
    "v52_scope_assessment", "v52_review_package", "v52_new_evidence_packages",
    "v52_evidence_files", "v52_next_prerequisite", "v52_evidence_relation",
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
        assert "fallback and cross-version behavior remain untested." in previous
        previous = previous.replace(
            "fallback and cross-version behavior remain untested.",
            "fallback and behavior in later releases remain untested.")
        return previous + (
            " One exact-fixture replay under locally installed Lean 4.29.0 produced the same"
            " Unicode diagnostic 16-27 range, UTF-8-only-offer failed edit, UTF-16-only"
            " repaired edit and original/patched batch 1/0 exits as 4.30.0-rc2. Both pins"
            " omitted explicit positionEncoding. Their initialize capability objects differed"
            " at exactly experimental.rpcProvider.rpcWireFormat, absent in 4.29.0 and `v1`"
            " in 4.30.0-rc2; no RPC call tested the effect. The batch JSON messages match"
            " after removing absolute fileName paths. This is one older-pin comparison on"
            " one host, not a later-release, real-editor or Anneal projection result.")
    return previous


def main():
    live = json.loads((HERE / "live-issue-snapshot-v52.json").read_text())
    assert live == json.loads((V51 / "live-issue-snapshot-v51.json").read_text())
    assert live["issues"]["3730"]["state"] == "closed"
    assert live["issues"]["3731"]["state"] == "open"
    old_rows = json.loads((V51 / "row-challenge-v51.json").read_text())
    assert len(old_rows) == 333 and len({row["id"] for row in old_rows}) == 333
    assert all((REPORTS / PACKAGE / name).is_file() for name in EVIDENCE)
    out = []
    for old in old_rows:
        row = dict(old)
        item = row["id"]
        if item in DIRECT:
            residual = updated_residual(item, old["v51_specific_remaining_delta"])
            assessment = (
                "Direct bounded Lean 4.29 versus 4.30-rc2 Unicode LSP comparison with"
                " one capability delta; actual editor, later release and Anneal projection"
                " remain at the inherited product gate.")
            relation = "direct bounded Lean LSP version-boundary evidence"
            review = HERE.parent.name
            files = [f"reports/{PACKAGE}/{name}" for name in EVIDENCE]
            packages = [PACKAGE]
        elif item in CONTEXT:
            residual = old["v51_specific_remaining_delta"]
            assessment = (
                "The older-pin Unicode Lean LSP comparison adds component context to this"
                " coordinate/UTF-16 row; its Anneal/editor residual, product gate and"
                " next prerequisite remain unchanged.")
            relation = "bounded Lean LSP version-boundary context"
            review = HERE.parent.name
            files = [f"reports/{PACKAGE}/{name}" for name in EVIDENCE]
            packages = [PACKAGE]
        else:
            residual = old["v51_specific_remaining_delta"]
            assessment = (
                f"The Lean LSP version-boundary package does not directly exercise {item}"
                f" ({row['title']}); the v51 residual and prerequisite remain.")
            relation = "no direct v52 evidence"
            review = old["v51_review_package"]
            files = []
            packages = []
        row.update({
            "v52_status": old["v51_status"],
            "v52_gate_categories": old["v51_gate_categories"],
            "v52_specific_remaining_delta": residual,
            "v52_scope_assessment": assessment,
            "v52_review_package": review,
            "v52_new_evidence_packages": packages,
            "v52_evidence_files": files,
            "v52_next_prerequisite": old["v51_next_prerequisite"],
            "v52_evidence_relation": relation,
        })
        out.append(row)
    assert {row["id"] for row in out if row["v52_specific_remaining_delta"] != row["v51_specific_remaining_delta"]} == set(DIRECT)
    assert all(row["v52_status"] == row["v51_status"] and
               row["v52_gate_categories"] == row["v51_gate_categories"] and
               row["v52_next_prerequisite"] == row["v51_next_prerequisite"] for row in out)
    (HERE / "row-challenge-v52.json").write_text(json.dumps(out, indent=2, sort_keys=True, ensure_ascii=False) + "\n")
    by_id = {row["id"]: row for row in out}

    def extend(old_name, key, new_name):
        rows = []
        for old in read_csv(V51 / old_name):
            row = dict(old)
            source = by_id[row[key]]
            for field in NEW_FIELDS:
                value = source[field]
                row[field] = ";".join(value) if isinstance(value, list) else value
            rows.append(row)
        write_csv(HERE / new_name, rows)
        return rows

    investigations = extend("investigation-final-v51.csv", "id", "investigation-final-v52.csv")
    suggestions = extend("3730-crosswalk-final-v51.csv", "3730_id", "3730-crosswalk-final-v52.csv")
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
    write_csv(HERE / "source-package-inventory-v52.csv", inventory)
    generated = (
        "row-challenge-v52.json", "investigation-final-v52.csv",
        "3730-crosswalk-final-v52.csv", "source-package-inventory-v52.csv",
    )
    inputs = {
        "v51/row-challenge-v51.json": V51 / "row-challenge-v51.json",
        "v51/investigation-final-v51.csv": V51 / "investigation-final-v51.csv",
        "v51/3730-crosswalk-final-v51.csv": V51 / "3730-crosswalk-final-v51.csv",
        "live-issue-snapshot-v52.json": HERE / "live-issue-snapshot-v52.json",
    }
    validation = {
        "reference_tip_at_start": "badec4d90493d883e5e6886f6695239fbfb7ac74",
        "source_reference_package": V51_NAME,
        "source_anneal_revision": "bd0956be95c5f798f0c0484921b9b9d1fc6e9988",
        "issue_snapshot_relation": "exact inherited v51 snapshot; no fresh fetch",
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
    (HERE / "validation-v52.json").write_text(json.dumps(validation, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: validation[key] for key in (
        "row_count", "suggestion_destination_links", "changed_residual_ids", "inventory_files")}, sort_keys=True))


if __name__ == "__main__":
    main()
