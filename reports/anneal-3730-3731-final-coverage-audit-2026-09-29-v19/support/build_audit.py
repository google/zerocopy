#!/usr/bin/env python3
"""Rebuild v19 ledgers from frozen issue text, v18 rows and v19 judgments."""
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
V18 = REPORTS / "anneal-3730-3731-final-coverage-audit-2026-09-29-v18" / "support"
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
resource = read_json(HERE / "resource-recheck.json")
assert audit["reference_commit"] == "5f4c846fa5dddc19b649305d86d612bf142ce606"
assert audit["new_packages"] == ["anneal-3731-real-generation-publication-v4-30-0-rc2"]
assert all(item["matches_v18"] for item in resource["pins_rechecked"].values())
assert all(value is None for value in resource["ocaml_family_path_lookup"].values())
for number in (3730, 3731):
    old, new = snapshot[str(number)], live["issues"][str(number)]
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

judgments = read_json(HERE / "row-challenge-v19.json")
by_id = {item["id"]: item for item in judgments}
assert len(judgments) == len(by_id) == 333
assert {x["id"] for x in judgments if x["kind"] == "investigation"} == issue_3731
assert {x["id"] for x in judgments if x["kind"] == "suggestion"} == issue_3730
assert all(not x["v19_new_distinct_cached_only_experiment_available"] for x in judgments)
assert not {x["id"] for x in judgments if x["v19_status"] != x["v18_status"]}

fields_v19 = [
    "v19_status", "v19_gate_categories", "v19_specific_remaining_delta",
    "v19_post_v18_scope_assessment", "v19_new_evidence_packages",
    "v19_evidence_files", "v19_next_prerequisite",
    "v19_new_distinct_cached_only_experiment_available",
]
source = read_csv(V18 / "investigation-final-v18.csv")
assert len(source) == 159
investigations = []
for row in source:
    decision = by_id[row["id"]]
    assert decision["kind"] == "investigation" and decision["title"] == row["title"]
    assert decision["v18_status"] == row["status"] == row["v18_status"]
    assert decision["v16_disposition"] == row["v16_disposition"]
    assert decision["v19_status"] in ("complete", "partial", "not-run", "conditional")
    assert decision["v19_specific_remaining_delta"] and decision["v19_next_prerequisite"]
    packages = decision["v19_new_evidence_packages"]
    assert set(packages) <= set(audit["new_packages"])
    row["status"] = decision["v19_status"]
    row["v19_status"] = decision["v19_status"]
    row["v19_gate_categories"] = ";".join(decision["v19_gate_categories"])
    row["v19_specific_remaining_delta"] = decision["v19_specific_remaining_delta"]
    row["v19_post_v18_scope_assessment"] = decision["v19_post_v18_scope_assessment"]
    row["v19_new_evidence_packages"] = ";".join(packages)
    row["v19_evidence_files"] = ";".join(f"reports/{p}/{f}" for p in packages for f in ("REPORT.md", "support/check.py", "support/results.json", "support/inputs/A/current.llbc", "support/inputs/B/current.llbc"))
    row["v19_next_prerequisite"] = decision["v19_next_prerequisite"]
    row["v19_new_distinct_cached_only_experiment_available"] = str(decision["v19_new_distinct_cached_only_experiment_available"])
    investigations.append(row)
assert list(investigations[0])[-len(fields_v19):] == fields_v19
write_csv(HERE / "investigation-final-v19.csv", investigations, list(investigations[0]))
status_by_id = {row["id"]: row["status"] for row in investigations}

source = read_csv(V18 / "3730-crosswalk-final-v18.csv")
assert len(source) == 174
suggestions = []
for row in source:
    decision = by_id[row["3730_id"]]
    assert decision["kind"] == "suggestion" and decision["title"] == row["suggestion"]
    assert decision["v18_status"] == row["status"] == row["v18_status"]
    assert decision["v16_disposition"] == row["v16_disposition"]
    assert decision["v19_status"] == row["status"]
    assert decision["v19_specific_remaining_delta"] and decision["v19_next_prerequisite"]
    packages = decision["v19_new_evidence_packages"]
    assert set(packages) <= set(audit["new_packages"])
    destinations = [item for item in row["3731_destinations"].split(";") if item]
    assert set(destinations) <= issue_3731
    row["destination_statuses"] = ";".join(status_by_id[item] for item in destinations)
    row["v19_status"] = decision["v19_status"]
    row["v19_gate_categories"] = ";".join(decision["v19_gate_categories"])
    row["v19_specific_remaining_delta"] = decision["v19_specific_remaining_delta"]
    row["v19_post_v18_scope_assessment"] = decision["v19_post_v18_scope_assessment"]
    row["v19_new_evidence_packages"] = ";".join(packages)
    row["v19_evidence_files"] = ";".join(f"reports/{p}/{f}" for p in packages for f in ("REPORT.md", "support/check.py", "support/results.json", "support/inputs/A/current.llbc", "support/inputs/B/current.llbc"))
    row["v19_next_prerequisite"] = decision["v19_next_prerequisite"]
    row["v19_new_distinct_cached_only_experiment_available"] = str(decision["v19_new_distinct_cached_only_experiment_available"])
    suggestions.append(row)
assert list(suggestions[0])[-len(fields_v19):] == fields_v19
write_csv(HERE / "3730-crosswalk-final-v19.csv", suggestions, list(suggestions[0]))

package_rows = []
file_rows = []
for name in audit["new_packages"]:
    base = REPORTS / name
    report, problems = reference._load_report(base)
    assert report and not problems, (name, problems)
    files = sorted(path for path in base.rglob("*") if path.is_file())
    package_rows.append({"package": name, "files": len(files), "report_sha256": sha(base / "REPORT.md"), "metadata_sha256": sha(base / "REPORT.json"), "offline_checker": str((base / "support/check.py").is_file())})
    for path in files:
        file_rows.append({"package": name, "relative_path": str(path.relative_to(base)), "bytes": path.stat().st_size, "sha256": sha(path)})
write_csv(HERE / "new-package-review-v19.csv", package_rows, list(package_rows[0]))
write_csv(HERE / "new-file-inventory-v19.csv", file_rows, list(file_rows[0]))

unrun_conditional = []
for item in judgments:
    if item["v19_status"] in ("not-run", "conditional"):
        unrun_conditional.append({"id": item["id"], "kind": item["kind"], "status": item["v19_status"], "exact_blocker_or_input": item["v19_next_prerequisite"], "specific_remaining_delta": item["v19_specific_remaining_delta"]})
assert len(unrun_conditional) == 13
write_csv(HERE / "unrun-conditional-inputs-v19.csv", unrun_conditional, list(unrun_conditional[0]))

counts = {"investigations": dict(Counter(row["status"] for row in investigations)), "suggestions": dict(Counter(row["status"] for row in suggestions))}
assert counts["investigations"] == {"complete": 4, "partial": 151, "not-run": 1, "conditional": 3}
assert counts["suggestions"] == {"complete": 4, "partial": 161, "not-run": 5, "conditional": 4}
inputs = ("issue-scope-snapshot.json", "live-issue-hashes.json", "resource-recheck.json", "audit-snapshot.json", "row-challenge-v19.json")
generated = ("investigation-final-v19.csv", "3730-crosswalk-final-v19.csv", "new-package-review-v19.csv", "new-file-inventory-v19.csv", "unrun-conditional-inputs-v19.csv")
validation = {
    "reference_commit": audit["reference_commit"],
    "issue_fetched_at_utc": live["fetched_at_utc"],
    "issue_hashes": live["issues"],
    "issue_3730_heading_count": len(issue_3730),
    "issue_3731_id_count": len(issue_3731),
    "row_challenge_count": len(judgments),
    "status_counts": counts,
    "new_complete_ids": audit["new_complete_ids"],
    "new_packages": audit["new_packages"],
    "new_package_file_count": len(file_rows),
    "unrun_conditional_count": len(unrun_conditional),
    "new_distinct_cached_only_experiment_count": 0,
    "input_sha256": {name: sha(HERE / name) for name in inputs},
    "generated_sha256": {name: sha(HERE / name) for name in generated},
}
(HERE / "validation-v19.json").write_text(json.dumps(validation, indent=2, sort_keys=True) + "\n")
print(json.dumps({"rows": len(judgments), "counts": counts, "packages": len(package_rows), "files": len(file_rows), "unrun_conditional": len(unrun_conditional)}, sort_keys=True))
