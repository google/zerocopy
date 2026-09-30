#!/usr/bin/env python3
"""Append a source-only v67 audit to the published v66 ledger and crosswalk."""
import csv
import hashlib
import json
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
REPORTS = ROOT / "reports"
V66 = REPORTS / "anneal-3730-3731-final-coverage-audit-2026-09-30-v66" / "support"
SOURCE_NAME = "anneal-3731-source-spec-synthesis-2026-09-30"
SOURCE = REPORTS / SOURCE_NAME
PARENT = "ebcdcadb63fefd1e6c0f46cb2030270ae3232837"
V66_PUBLISHED_PARENT = "0c504d98f5abafcbbd1460738e6d753378a6460e"
FIELDS = ("v67_status", "v67_gate_categories", "v67_specific_remaining_delta",
          "v67_scope_assessment", "v67_review_package", "v67_new_evidence_packages",
          "v67_evidence_files", "v67_next_prerequisite", "v67_evidence_relation",
          "v67_linked_source_ids")

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def csv_rows(path):
    with path.open(newline="") as f:
        return list(csv.DictReader(f))

def write_csv(path, rows):
    with path.open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0]), lineterminator="\n")
        w.writeheader(); w.writerows(rows)

def main():
    mapping = json.loads((SOURCE / "support/id-map.json").read_text())
    assert len(mapping) == 23 and sum(bool(x) for x in mapping.values()) == 19
    cross = csv_rows(V66 / "3730-crosswalk-final-v66.csv")
    destinations = {row["3730_id"]: row["3731_destinations"].split(";") for row in cross}
    assert len(cross) == len(destinations) == 174 and sum(len(v) for v in destinations.values()) == 345
    old = json.loads((V66 / "row-challenge-v66.json").read_text())
    assert len(old) == 333 and len({r["id"] for r in old}) == 333
    out = []
    for prior in old:
        row = dict(prior); item = row["id"]
        linked = ([item] if item in mapping and mapping[item] else
                  [x for x in destinations.get(item, []) if mapping.get(x)])
        if item in mapping and not mapping[item]:
            assessment = "No new ID-specific evidence in the 41 source/spec packages; inherited product residual remains."
            relation = "no new ID-specific source evidence"
        elif prior["kind"] == "investigation" and linked:
            assessment = "Bounded source/spec design context only; no Anneal product execution or gate change."
            relation = "source/spec design context"
        elif prior["kind"] == "suggestion" and linked:
            assessment = "Bounded source/spec context through exact inherited #3731 destinations " + ", ".join(linked) + "; no direct suggestion execution."
            relation = "source/spec context via exact destination links"
        else:
            assessment = "The 41 source/spec packages add no mapped v67 evidence for this inherited row."
            relation = "no mapped v67 source evidence"
        has_context = bool(linked)
        row.update({
            "v67_status": prior["v66_status"],
            "v67_gate_categories": prior["v66_gate_categories"],
            "v67_specific_remaining_delta": prior["v66_specific_remaining_delta"],
            "v67_scope_assessment": assessment,
            "v67_review_package": HERE.parent.name if has_context else prior["v66_review_package"],
            "v67_new_evidence_packages": [SOURCE_NAME] if has_context else [],
            "v67_evidence_files": [f"reports/{SOURCE_NAME}/REPORT.md", f"reports/{SOURCE_NAME}/support/id-map.json"] if has_context else [],
            "v67_next_prerequisite": prior["v66_next_prerequisite"],
            "v67_evidence_relation": relation,
            "v67_linked_source_ids": linked,
        })
        out.append(row)
    (HERE / "row-challenge-v67.json").write_text(json.dumps(out, indent=2, sort_keys=True, ensure_ascii=False) + "\n")
    by_id = {row["id"]: row for row in out}
    def extend(old_name, new_name, key):
        rows = csv_rows(V66 / old_name)
        for row in rows:
            source = by_id[row[key]]
            for field in FIELDS:
                value = source[field]
                row[field] = ";".join(value) if isinstance(value, list) else value
            assert row["status"] == source["v67_status"]
        write_csv(HERE / new_name, rows)
        return rows
    investigations = extend("investigation-final-v66.csv", "investigation-final-v67.csv", "id")
    suggestions = extend("3730-crosswalk-final-v66.csv", "3730-crosswalk-final-v67.csv", "3730_id")
    assert len(investigations) == 159 and len(suggestions) == 174
    census = json.loads((SOURCE / "support/source-census.json").read_text())
    assert len(census) == 41
    inventory = []
    for package in (V66.parent.name, SOURCE_NAME):
        for path in sorted((REPORTS / package).rglob("*")):
            if path.is_file() and "__pycache__" not in path.parts and path.suffix != ".pyc":
                inventory.append({"path": path.relative_to(ROOT).as_posix(), "sha256": sha(path), "size": path.stat().st_size})
    write_csv(HERE / "source-package-inventory-v67.csv", inventory)
    context_suggestions = [r["id"] for r in out if r["kind"] == "suggestion" and r["v67_linked_source_ids"]]
    validation = {
        "reference_tip_at_start": PARENT,
        "v66_published_git_parent": V66_PUBLISHED_PARENT,
        "v66_ledger_source_commit": "57155f6541e478f201ae47d8a27da2f3d448df5e",
        "v65_issue_snapshot_reused": True,
        "source_reference_package": V66.parent.name,
        "source_synthesis_package": SOURCE_NAME,
        "source_report_count": len(census),
        "row_count": len(out), "investigation_count": len(investigations), "suggestion_count": len(suggestions),
        "suggestion_destination_links": sum(len(v) for v in destinations.values()),
        "mapped_investigation_ids": sorted(x for x,v in mapping.items() if v),
        "no_new_id_specific_evidence_ids": sorted(x for x,v in mapping.items() if not v),
        "context_suggestion_ids": context_suggestions,
        "changed_status_ids": [], "changed_gate_ids": [], "changed_prerequisite_ids": [], "changed_residual_ids": [],
        "status_counts": {"investigations": dict(Counter(r["status"] for r in investigations)),
                          "suggestions": dict(Counter(r["status"] for r in suggestions))},
        "inventory_files": len(inventory),
        "input_sha256": {
            "v66/row-challenge-v66.json": sha(V66 / "row-challenge-v66.json"),
            "v66/investigation-final-v66.csv": sha(V66 / "investigation-final-v66.csv"),
            "v66/3730-crosswalk-final-v66.csv": sha(V66 / "3730-crosswalk-final-v66.csv"),
            "v66/live-issue-snapshot-v66.json": sha(V66 / "live-issue-snapshot-v66.json"),
            "source/id-map.json": sha(SOURCE / "support/id-map.json"),
            "source/source-census.json": sha(SOURCE / "support/source-census.json"),
        },
        "generated_sha256": {name: sha(HERE / name) for name in (
            "row-challenge-v67.json", "investigation-final-v67.csv", "3730-crosswalk-final-v67.csv",
            "source-package-inventory-v67.csv", "live-issue-snapshot-v67.json")},
    }
    (HERE / "validation-v67.json").write_text(json.dumps(validation, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"rows":len(out), "mapped_investigations":len(validation["mapped_investigation_ids"]),
                      "context_suggestions":len(context_suggestions), "inventory_files":len(inventory)}, sort_keys=True))

if __name__ == "__main__":
    main()
