#!/usr/bin/env python3
"""Derive v46 from published v45 and the retained mapped-worker package."""
import csv
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V45_NAME = "anneal-3730-3731-final-coverage-audit-2026-09-30-v45"
V45 = REPORTS / V45_NAME / "support"
PLUGIN = "anneal-3731-i125-i154-native-plugin-mapped-workers-2026-09-30"
PACKAGES = (V45_NAME, PLUGIN)
DIRECT = {"I125": PLUGIN, "I154": PLUGIN}
CONTEXT = {"J08": PLUGIN, "J12": PLUGIN}
EVIDENCE = {
    PLUGIN: ("REPORT.md", "REPORT.json", "support/check.py", "support/probe.py",
             "support/restart.py", "support/guard-abort.json", "support/restart-transcript.json",
             "support/artifacts/plugin-v1.dylib", "support/artifacts/plugin-v2.dylib",
             "support/mapping-logs/v1-first-93511-lsof.txt.gz",
             "support/mapping-logs/v1-first-93518-vmmap.txt.gz",
             "support/mapping-logs/v1-after-close-93511-lsof.txt.gz",
             "support/mapping-logs/v2-open-93511-vmmap.txt.gz",
             "support/mapping-logs/v2-open-93706-lsof.txt.gz",
             "support/mapping-logs/forced-restart-v1-93910-lsof.txt.gz",
             "support/mapping-logs/forced-restart-v1-93911-vmmap.txt.gz"),
}
NEW_FIELDS = ("v46_status", "v46_gate_categories", "v46_specific_remaining_delta",
              "v46_scope_assessment", "v46_review_package", "v46_new_evidence_packages",
              "v46_evidence_files", "v46_next_prerequisite", "v46_evidence_relation")

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def sha_text(text): return hashlib.sha256(text.encode()).hexdigest()
def read_csv(path):
    with path.open(newline="") as stream: return list(csv.DictReader(stream))
def write_csv(path, rows):
    with path.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]), lineterminator="\n")
        writer.writeheader(); writer.writerows(rows)

def verify_live(live):
    prior = json.loads((V45 / "live-issue-snapshot-v45.json").read_text())
    for number, state in ((3730, "closed"), (3731, "open")):
        x, old = live["issues"][str(number)], prior["issues"][str(number)]
        assert x["number"] == number and x["state"] == old["state"] == state
        assert x["body"] == old["body"] and x["body_sha256"] == old["body_sha256"] == sha_text(x["body"])
        assert len(x["comments"]) == len(old["comments"]) == 1
        assert x["comments"][0]["id"] == old["comments"][0]["id"]
        assert x["comments"][0]["body"] == old["comments"][0]["body"]
        assert x["comments"][0]["body_sha256"] == old["comments"][0]["body_sha256"] == sha_text(x["comments"][0]["body"])

def updated_residual(item, previous):
    if item == "I125":
        return previous + (" A new same-basename v1/v2 native-plugin probe retained `lsof` and `vmmap` output "
                           "for the actual watchdog and file-worker mappings. The first watchdog/worker pair "
                           "mapped v1; after `didClose` the first worker was absent while the watchdog still "
                           "mapped v1; a new file worker mapped v2 while that watchdog retained v1. A "
                           "1.5 GiB summed-RSS guard stopped the server before an in-one-watchdog reverse "
                           "v1 worker could be opened. A separate forced restart mapped v1 in a fresh watchdog "
                           "and worker and returned a clean goal result. The same-run v2 initializer marker "
                           "was not retained. Path mappings do not attest resident bytes or ABI compatibility. "
                           "Canonical plugin-path/content and worker-generation ownership, multiple native "
                           "dependencies, GC/identity policy and Anneal routing remain untested.")
    if item == "I154":
        return previous + (" A new retained mapping check directly shows v1 in the initial watchdog and "
                           "worker, v2 in a later worker under the same v1-mapped watchdog, first-worker "
                           "absence after close, and v1 in a separate forced-restart watchdog/worker. The "
                           "1.5 GiB summed-RSS guard stopped the live tree before the in-one-watchdog "
                           "v1→v2→v1 mapped transition; its same-run v2 marker was not retained. This "
                           "narrows a native-plugin contamination sentinel but does not establish fixture "
                           "reuse granularity, cleanup or isolation for representative imported models and "
                           "the Anneal test runner.")
    return previous

def main():
    live = json.loads((HERE / "live-issue-snapshot-v46.json").read_text())
    verify_live(live)
    old_rows = json.loads((V45 / "row-challenge-v45.json").read_text())
    assert len(old_rows) == 333 and len({r["id"] for r in old_rows}) == 333
    for package, names in EVIDENCE.items():
        assert all((REPORTS / package / name).is_file() for name in names)
    out = []
    for old in old_rows:
        row = dict(old); item = row["id"]
        package = DIRECT.get(item) or CONTEXT.get(item)
        if item in DIRECT:
            residual = updated_residual(item, old["v45_specific_remaining_delta"])
            assessment = ("Direct bounded native-plugin mapping and forced-restart evidence; "
                          "the reverse transition stopped at the memory guard. Partial product gate and inherited prerequisite remain.")
            relation = "direct bounded native-plugin mapping evidence"
            review = HERE.parent.name
        elif item in CONTEXT:
            residual = old["v45_specific_remaining_delta"]
            assessment = ("The I154 native-plugin worker mapping supplies bounded fixture-contamination context "
                          f"for mapped suggestion {item}; its residual and product prerequisite remain unchanged.")
            relation = "bounded mapped-worker context"
            review = HERE.parent.name
        else:
            residual = old["v45_specific_remaining_delta"]
            assessment = f"The new mapped-worker package does not directly exercise {item} ({row['title']}); the v45 residual and prerequisite remain."
            relation = "no direct v46 evidence"
            review = old["v45_review_package"]
        files = [f"reports/{package}/{name}" for name in EVIDENCE[package]] if package else []
        row.update({"v46_status": old["v45_status"], "v46_gate_categories": old["v45_gate_categories"],
                    "v46_specific_remaining_delta": residual, "v46_scope_assessment": assessment,
                    "v46_review_package": review, "v46_new_evidence_packages": [package] if package else [],
                    "v46_evidence_files": files, "v46_next_prerequisite": old["v45_next_prerequisite"],
                    "v46_evidence_relation": relation})
        out.append(row)
    assert {r["id"] for r in out if r["v46_specific_remaining_delta"] != r["v45_specific_remaining_delta"]} == set(DIRECT)
    assert all(r["v46_status"] == r["v45_status"] and r["v46_gate_categories"] == r["v45_gate_categories"] and
               r["v46_next_prerequisite"] == r["v45_next_prerequisite"] for r in out)
    (HERE / "row-challenge-v46.json").write_text(json.dumps(out, indent=2, sort_keys=True, ensure_ascii=False) + "\n")
    by_id = {r["id"]: r for r in out}
    def extend(old_name, key, new_name):
        rows = []
        for old in read_csv(V45 / old_name):
            row = dict(old); source = by_id[row[key]]
            for field in NEW_FIELDS:
                value = source[field]
                row[field] = ";".join(value) if isinstance(value, list) else value
            rows.append(row)
        write_csv(HERE / new_name, rows)
        return rows
    investigations = extend("investigation-final-v45.csv", "id", "investigation-final-v46.csv")
    suggestions = extend("3730-crosswalk-final-v45.csv", "3730_id", "3730-crosswalk-final-v46.csv")
    assert len(investigations) == 159 and len(suggestions) == 174
    body, comment = live["issues"]["3731"]["body"], live["issues"]["3731"]["comments"][0]["body"]
    titles = {item: re.sub(r"\s*\[[^]]+\]\.?$", "", title).strip() for source in (body, comment)
              for item, title in re.findall(r"(?m)^\*\*(I\d{3})\s+[—.]\s+([^\n]*?)\*\*", source)}
    cross = {item: (title.strip(), set(re.findall(r"I\d{3}", destinations)))
             for item, title, destinations in re.findall(r"(?m)^\| ([A-O]\d{2}) \| ([^|]+) \| ([^|]+) \|", comment)}
    assert len(titles) == 159 and len(cross) == 174
    assert all(r["title"] == titles[r["id"]] for r in investigations)
    assert all(r["suggestion"] == cross[r["3730_id"]][0] and
               set(r["3731_destinations"].split(";")) == cross[r["3730_id"]][1] for r in suggestions)
    links = sum(len(v[1]) for v in cross.values()); assert links == 345
    inventory = []
    for package in PACKAGES:
        for path in sorted((REPORTS / package).rglob("*")):
            if path.is_file() and "__pycache__" not in path.parts and path.suffix != ".pyc":
                inventory.append({"path": path.relative_to(ROOT).as_posix(), "sha256": sha(path)})
    write_csv(HERE / "source-package-inventory-v46.csv", inventory)
    generated = ("row-challenge-v46.json", "investigation-final-v46.csv", "3730-crosswalk-final-v46.csv",
                 "source-package-inventory-v46.csv")
    inputs = {"v45/row-challenge-v45.json": V45 / "row-challenge-v45.json",
              "v45/investigation-final-v45.csv": V45 / "investigation-final-v45.csv",
              "v45/3730-crosswalk-final-v45.csv": V45 / "3730-crosswalk-final-v45.csv",
              "live-issue-snapshot-v46.json": HERE / "live-issue-snapshot-v46.json"}
    validation = {"reference_tip_at_start": "22c27b3d8ba12ab9708cb7cd8f13eb29217ec71a",
                  "source_reference_package": V45_NAME,
                  "source_anneal_revision": "bd0956be95c5f798f0c0484921b9b9d1fc6e9988",
                  "row_count": len(out), "investigation_count": len(investigations),
                  "suggestion_count": len(suggestions), "suggestion_destination_links": links,
                  "status_counts": {"investigations": dict(Counter(r["status"] for r in investigations)),
                                    "suggestions": dict(Counter(r["status"] for r in suggestions))},
                  "changed_status_ids": [], "changed_gate_ids": [], "changed_prerequisite_ids": [],
                  "changed_residual_ids": sorted(DIRECT), "direct_evidence_ids": sorted(DIRECT),
                  "bounded_context_ids": sorted(CONTEXT), "source_packages": list(PACKAGES),
                  "inventory_files": len(inventory),
                  "input_sha256": {name: sha(path) for name, path in inputs.items()},
                  "generated_sha256": {name: sha(HERE / name) for name in generated}}
    (HERE / "validation-v46.json").write_text(json.dumps(validation, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: validation[key] for key in ("row_count", "suggestion_destination_links",
                                                     "changed_residual_ids", "bounded_context_ids", "inventory_files")}, sort_keys=True))

if __name__ == "__main__": main()
