#!/usr/bin/env python3
"""Deterministically build the v17 ledgers from frozen issue text and row decisions."""
import csv
import hashlib
import json
from collections import Counter
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
REPORTS = ROOT / "reports"
V16 = REPORTS / "anneal-3730-3731-final-coverage-audit-2026-09-29-v16" / "support"
sys.path.insert(0, str(ROOT / "tools"))
import reference


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read_json(path):
    return json.loads(Path(path).read_text())


def read_csv(path):
    with Path(path).open(newline="") as stream:
        return list(csv.DictReader(stream))


def write_csv(path, rows, fields):
    with path.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=fields, lineterminator="\n", extrasaction="raise")
        writer.writeheader()
        writer.writerows(rows)


snapshot = read_json(HERE / "issue-scope-snapshot.json")
live = read_json(HERE / "live-issue-hashes.json")
audit = read_json(HERE / "audit-snapshot.json")
inventory = read_json(HERE / "local-tool-inventory.json")
assert audit["reference_commit"] == "2c45d74f7176d15a417f9a78a60afaf66eb2fdf2"
assert len(audit["post_v16_packages"]) == 2
assert inventory["pins"]["nix"]["version"] == "nix (Nix) 2.35.2"
assert all(value is None for value in inventory["ocaml_family_path_lookup"].values())
assert not inventory["ocaml_family_local_root_matches"]
assert not inventory["ocaml_family_nix_store_matches"]
for number in (3730, 3731):
    old = snapshot[str(number)]
    new = live["issues"][str(number)]
    assert old["state"] == new["state"]
    assert hashlib.sha256(old["body"].encode()).hexdigest() == new["body_sha256"]
    assert len(old["comments"]) == len(new["comments"]) == 1
    for comment, metadata in zip(old["comments"], new["comments"]):
        assert comment["id"] == metadata["id"]
        assert hashlib.sha256(comment["body"].encode()).hexdigest() == metadata["body_sha256"]
issue_3730 = set(re.findall(r"(?m)^### ([A-O]\d{2})\.", snapshot["3730"]["body"]))
issue_3731 = set(re.findall(r"\bI\d{3}\b", snapshot["3731"]["body"] + "\n" + snapshot["3731"]["comments"][0]["body"]))
assert len(issue_3730) == 174
assert issue_3731 == {f"I{i:03d}" for i in range(1, 160)}

review_rows = read_json(HERE / "row-challenge-v17.json")
reviews = {row["id"]: row for row in review_rows}
assert len(review_rows) == len(reviews) == 333
assert {row["id"] for row in review_rows if row["kind"] == "investigation"} == issue_3731
assert {row["id"] for row in review_rows if row["kind"] == "suggestion"} == issue_3730
assert sum(not row["new_distinct_cached_only_experiment_available"] for row in review_rows) == 333

append_fields = [
    "v17_status", "v17_gate_categories", "v17_specific_remaining_delta",
    "v17_post_v16_scope_assessment", "v17_new_evidence_packages",
    "v17_evidence_files", "v17_next_prerequisite",
    "v17_new_distinct_cached_only_experiment_available",
]
outputs = []
for source, target, key, kind, expected in (
    ("investigation-final-v16.csv", "investigation-final-v17.csv", "id", "investigation", 159),
    ("3730-crosswalk-final-v16.csv", "3730-crosswalk-final-v17.csv", "3730_id", "suggestion", 174),
):
    rows = read_csv(V16 / source)
    assert len(rows) == expected
    for row in rows:
        decision = reviews[row[key]]
        assert decision["kind"] == kind
        assert decision["title"] == (row["title"] if kind == "investigation" else row["suggestion"])
        assert decision["v16_status"] == row["status"]
        assert decision["v16_disposition"] == row["v16_disposition"]
        assert decision["v17_status"] == row["status"]
        assert decision["v17_specific_remaining_delta"]
        assert decision["next_prerequisite"]
        packages = decision["new_evidence_packages"]
        assert set(packages) <= set(audit["post_v16_packages"])
        evidence = []
        for package in packages:
            evidence.extend((f"reports/{package}/REPORT.md", f"reports/{package}/support/check.py"))
            if package.endswith("file-event-observability-2026-09-29"):
                evidence.extend((f"reports/{package}/support/results.json", f"reports/{package}/support/observe.c"))
            else:
                evidence.append(f"reports/{package}/support/review.json")
        row["v17_status"] = decision["v17_status"]
        row["v17_gate_categories"] = ";".join(decision["v17_gate_categories"])
        row["v17_specific_remaining_delta"] = decision["v17_specific_remaining_delta"]
        row["v17_post_v16_scope_assessment"] = decision["v17_post_v16_scope_assessment"]
        row["v17_new_evidence_packages"] = ";".join(packages)
        row["v17_evidence_files"] = ";".join(evidence)
        row["v17_next_prerequisite"] = decision["next_prerequisite"]
        row["v17_new_distinct_cached_only_experiment_available"] = str(decision["new_distinct_cached_only_experiment_available"])
    fields = list(rows[0])
    assert fields[-len(append_fields):] == append_fields
    write_csv(HERE / target, rows, fields)
    outputs.append((kind, rows))

for name in audit["post_v16_packages"]:
    report, problems = reference._load_report(REPORTS / name)
    assert report is not None and not problems, (name, problems)
package_rows = []
file_rows = []
for name in audit["post_v16_packages"]:
    base = REPORTS / name
    files = sorted(path for path in base.rglob("*") if path.is_file())
    package_rows.append({"package": name, "files": len(files), "report_sha256": sha(base / "REPORT.md"), "metadata_sha256": sha(base / "REPORT.json"), "offline_checker": str((base / "support/check.py").is_file())})
    for path in files:
        file_rows.append({"package": name, "relative_path": str(path.relative_to(base)), "bytes": path.stat().st_size, "sha256": sha(path)})
write_csv(HERE / "post-v16-package-review.csv", package_rows, list(package_rows[0]))
write_csv(HERE / "post-v16-file-inventory.csv", file_rows, list(file_rows[0]))

counts = {kind: dict(Counter(row["v17_status"] for row in rows)) for kind, rows in outputs}
assert counts["investigation"] == {"complete": 2, "partial": 153, "not-run": 1, "conditional": 3}
assert counts["suggestion"] == {"complete": 4, "partial": 161, "not-run": 5, "conditional": 4}
assert all(not row["new_distinct_cached_only_experiment_available"] for row in review_rows)
assert {row["id"] for row in review_rows if "anneal-3730-lake-unprivileged-file-event-observability-2026-09-29" in row["new_evidence_packages"]} == {"I095", "I104", "F10", "F16"}

inputs = ("issue-scope-snapshot.json", "live-issue-hashes.json", "local-tool-inventory.json", "audit-snapshot.json", "row-challenge-v17.json")
generated = ("investigation-final-v17.csv", "3730-crosswalk-final-v17.csv", "post-v16-package-review.csv", "post-v16-file-inventory.csv")
validation = {
    "reference_commit": audit["reference_commit"],
    "issue_fetched_at_utc": live["fetched_at_utc"],
    "issue_hashes": live["issues"],
    "issue_3730_heading_count": len(issue_3730),
    "issue_3731_id_count": len(issue_3731),
    "row_challenge_count": len(review_rows),
    "status_counts": counts,
    "post_v16_packages": audit["post_v16_packages"],
    "post_v16_file_count": len(file_rows),
    "observer_row_ids": ["I095", "I104", "F10", "F16"],
    "new_distinct_cached_only_experiment_count": 0,
    "input_sha256": {name: sha(HERE / name) for name in inputs},
    "generated_sha256": {name: sha(HERE / name) for name in generated},
}
(HERE / "validation-v17.json").write_text(json.dumps(validation, indent=2, sort_keys=True) + "\n")
print(json.dumps({"rows": len(review_rows), "counts": counts, "packages": len(package_rows), "files": len(file_rows)}, sort_keys=True))
