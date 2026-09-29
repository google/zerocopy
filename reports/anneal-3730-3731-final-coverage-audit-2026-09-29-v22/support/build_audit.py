#!/usr/bin/env python3
"""Rebuild the v22 ledger from frozen v21 decisions and the current V2 source map."""
import csv
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
REPORTS = ROOT / "reports"
V21 = REPORTS / "anneal-3730-3731-final-coverage-audit-2026-09-29-v21" / "support"
SOURCE = "anneal-v2-current-source-surface-main-bd0956b-2026-09-29"
REFERENCE_HEAD = "a5b4d034aa65aa44d85afc943c3caec26a5229ba"
SOURCE_REVISION = "bd0956be95c5f798f0c0484921b9b9d1fc6e9988"


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read_json(path):
    return json.loads(Path(path).read_text())


def read_csv(path):
    with Path(path).open(newline="") as stream:
        return list(csv.DictReader(stream))


def write_csv(path, rows):
    with path.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]), lineterminator="\n", extrasaction="raise")
        writer.writeheader()
        writer.writerows(rows)


# A source observation belongs to a requested investigation only when the source
# report explicitly maps the relevant V2 surface to it. These groups do not imply
# that any component experiment has become an Anneal product acceptance test.
groups = {
    "selection": "I020 I075 I076 D07",
    "locks": "I078 I080 I107 I108 D03 D06 F12 H09 J13",
    "prepared": "I089 I090 I091 I092 I096 I150 F01 F02 F04 F05 F06 F07 F08",
    "locators": "I009 I079 I103 I123 I145 A01 A02 A08",
    "verification": "I129 I130 I137 I138 I149 I157 I159 I05 I06 I07 I08 E08 K02 L07 L08 N01 N02 N03 N04 N05 N06 N07 N08 N09 N10 N11 N12",
    "adapter": "I072",
}
assessment = {
    "selection": "Current V2 source defines package/target/kind enumeration and an LLBC filename helper, but the CLI does not call them or attest the Charon-producing compilation unit. Source presence narrows the implementation gap; no selected end-to-end run was observed.",
    "locks": "Current V2 source has a run-directory file-lock primitive and LockedRoots path accessor. The CLI does not invoke that path, the Cargo target directory is separate, and no publication, ownership, cancellation, or lock-order protocol is wired.",
    "prepared": "Current V2 exposes setup and contains a feature-gated read-only Lake archive fixture. The fixture was not executed here; no real prepared archive, first-goal server result, or operation-specific consumer contract was established.",
    "locators": "Current V2 computes workspace/run and LLBC locators. They are not authenticated source, translation, model, prepared environment, worker, RPC, or trust generations, and no end-to-end producer consumes them.",
    "verification": "Current V2 CLI exposes setup only. Its Lake fixture is not a generated proof; source has no reachable verification, claim/obligation acceptance, live proof query, or Rust-hosted annotation path. Existing complete disposable-prototype classifications retain their narrow scope.",
    "adapter": "Current V2 source contains no MCP adapter. The existing-adapter experiment remains unrun under its exact two-client Anneal conditions.",
}
by_group = {item: group for group, ids in groups.items() for item in ids.split()}
assert sum(len(ids.split()) for ids in groups.values()) == len(by_group)

# Retain the precise v21 residual except where the source map now makes its
# wording overbroad. These corrections still require the original product gate.
residual_corrections = {
    "I020": "The bounded default/feature/test and wrong-unit fixtures remain; V2 has unconnected target enumeration, but needs a complete compilation-unit key, selected Charon invocation, and cross-stage model/proof rejection.",
    "I075": "Selected Cargo unit graphs exist and V2 has unconnected target enumeration; extraction attestation for warm skip and alternate target invocations still needs an invoked wrapper policy.",
    "I076": "The wrong binary-unit negative exists; V2's target/kind enumeration and LLBC filename helper do not supply a complete compilation-unit key or collision-rejecting produced output selection.",
    "I078": "Private LLBC and interruption controls exist; V2's run-root lock primitive is not a schema-validated transactional Charon set publisher with a producer owner.",
    "I089": "V2 exposes setup and a feature-gated Lake archive fixture, but the scoped inventory found no actual prepared Anneal archive; the fixture was not executed and cannot substitute for a fresh consumer first-goal run.",
    "I096": "One Lake plugin/server discovery path ran; V2 setup resolves toolchain paths, while actual editor/MCP/CI launchers and their configuration discovery remain unexercised.",
    "I157": "V2 currently exposes setup and unconnected helpers, but no verify command or shared Anneal engine. The existing batch CLI and Python live prototypes do not share one product engine.",
    "L07": "V2 currently exposes setup and unconnected helpers, but no verify command or shared Anneal engine for a batch shell; Python shells remain illustrative.",
    "L08": "V2 currently exposes setup and unconnected helpers, but no shared Anneal engine for a transport-free live shell; Python shells remain illustrative.",
}

snapshot = read_json(HERE / "issue-scope-snapshot.json")
live = read_json(HERE / "live-issue-hashes.json")
audit = read_json(HERE / "audit-snapshot.json")
assert audit["reference_commit"] == REFERENCE_HEAD
assert audit["source_revision"] == SOURCE_REVISION
assert audit["new_packages"] == [SOURCE]
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

prior = read_json(V21 / "row-challenge-v21.json")
assert len(prior) == 333 and len({x["id"] for x in prior}) == 333
assert set(by_group) <= {x["id"] for x in prior}
assert all(x["v21_status"] in ("complete", "partial", "not-run", "conditional") for x in prior)
assert all(not x["v21_new_distinct_cached_only_experiment_available"] for x in prior)
judgments = []
for original in prior:
    row = dict(original)
    group = by_group.get(row["id"])
    row.update({
        "v22_status": row["v21_status"],
        "v22_gate_categories": row["v21_gate_categories"],
        "v22_specific_remaining_delta": residual_corrections.get(row["id"], row["v21_specific_remaining_delta"]),
        "v22_post_v21_scope_assessment": assessment[group] if group else "The present-source map does not execute this row's exact residual. Its v21 status, residual, and prerequisite remain in force.",
        "v22_new_evidence_packages": [SOURCE] if group else [],
        "v22_next_prerequisite": row["v21_next_prerequisite"],
        "v22_new_distinct_cached_only_experiment_available": False,
    })
    judgments.append(row)
(HERE / "row-challenge-v22.json").write_text(json.dumps(judgments, indent=2, sort_keys=True) + "\n")
by_id = {x["id"]: x for x in judgments}
assert {x["id"] for x in judgments if x["kind"] == "investigation"} == issue_3731
assert {x["id"] for x in judgments if x["kind"] == "suggestion"} == issue_3730

fields = ["v22_status", "v22_gate_categories", "v22_specific_remaining_delta", "v22_post_v21_scope_assessment", "v22_new_evidence_packages", "v22_evidence_files", "v22_next_prerequisite", "v22_new_distinct_cached_only_experiment_available"]
def extend(source_rows, id_key):
    rows = []
    for prior_row in source_rows:
        row = dict(prior_row)
        decision = by_id[row[id_key]]
        assert row["status"] == row["v21_status"] == decision["v21_status"] == decision["v22_status"]
        assert row["title" if id_key == "id" else "suggestion"] == decision["title"]
        row["v22_status"] = decision["v22_status"]
        row["v22_gate_categories"] = ";".join(decision["v22_gate_categories"])
        row["v22_specific_remaining_delta"] = decision["v22_specific_remaining_delta"]
        row["v22_post_v21_scope_assessment"] = decision["v22_post_v21_scope_assessment"]
        row["v22_new_evidence_packages"] = ";".join(decision["v22_new_evidence_packages"])
        row["v22_evidence_files"] = ";".join(f"reports/{p}/{f}" for p in decision["v22_new_evidence_packages"] for f in ("REPORT.md", "REPORT.json"))
        row["v22_next_prerequisite"] = decision["v22_next_prerequisite"]
        row["v22_new_distinct_cached_only_experiment_available"] = "False"
        rows.append(row)
    assert list(rows[0])[-len(fields):] == fields
    return rows

investigations = extend(read_csv(V21 / "investigation-final-v21.csv"), "id")
suggestions = extend(read_csv(V21 / "3730-crosswalk-final-v21.csv"), "3730_id")
assert len(investigations) == 159 and len(suggestions) == 174
write_csv(HERE / "investigation-final-v22.csv", investigations)
write_csv(HERE / "3730-crosswalk-final-v22.csv", suggestions)

package_rows, file_rows = [], []
for name in audit["new_packages"]:
    base = REPORTS / name
    metadata = read_json(base / "REPORT.json")
    assert metadata["subjects"][0]["identity"]["revision"] == SOURCE_REVISION
    files = sorted(path for path in base.rglob("*") if path.is_file())
    package_rows.append({"package": name, "files": len(files), "report_sha256": sha(base / "REPORT.md"), "metadata_sha256": sha(base / "REPORT.json"), "offline_checker": str((base / "support/check.py").is_file())})
    for path in files:
        file_rows.append({"package": name, "relative_path": str(path.relative_to(base)), "bytes": path.stat().st_size, "sha256": sha(path)})
write_csv(HERE / "new-package-review-v22.csv", package_rows)
write_csv(HERE / "new-file-inventory-v22.csv", file_rows)

gates = [{"id": x["id"], "kind": x["kind"], "status": x["v22_status"], "exact_blocker_or_input": x["v22_next_prerequisite"], "specific_remaining_delta": x["v22_specific_remaining_delta"]} for x in judgments if x["v22_status"] in ("not-run", "conditional")]
assert len(gates) == 13
write_csv(HERE / "unrun-conditional-inputs-v22.csv", gates)
counts = {"investigations": dict(Counter(row["status"] for row in investigations)), "suggestions": dict(Counter(row["status"] for row in suggestions))}
assert counts == {"investigations": {"complete": 4, "partial": 151, "not-run": 1, "conditional": 3}, "suggestions": {"complete": 4, "partial": 161, "not-run": 5, "conditional": 4}}
inputs = ("issue-scope-snapshot.json", "live-issue-hashes.json", "audit-snapshot.json")
generated = ("row-challenge-v22.json", "investigation-final-v22.csv", "3730-crosswalk-final-v22.csv", "new-package-review-v22.csv", "new-file-inventory-v22.csv", "unrun-conditional-inputs-v22.csv")
validation = {"reference_commit": REFERENCE_HEAD, "source_revision": SOURCE_REVISION, "issue_fetched_at_utc": live["fetched_at_utc"], "issue_hashes": live["issues"], "issue_3730_heading_count": len(issue_3730), "issue_3731_id_count": len(issue_3731), "row_challenge_count": len(judgments), "source_mapped_rows": len(by_group), "residual_corrections": sorted(residual_corrections), "status_counts": counts, "new_complete_ids": [], "new_packages": audit["new_packages"], "new_package_file_count": len(file_rows), "unrun_conditional_count": len(gates), "new_distinct_cached_only_experiment_count": 0, "input_sha256": {name: sha(HERE / name) for name in inputs}, "prior_sha256": {name: sha(V21 / name) for name in ("row-challenge-v21.json", "investigation-final-v21.csv", "3730-crosswalk-final-v21.csv")}, "generated_sha256": {name: sha(HERE / name) for name in generated}}
(HERE / "validation-v22.json").write_text(json.dumps(validation, indent=2, sort_keys=True) + "\n")
print(json.dumps({"rows": len(judgments), "mapped": len(by_group), "counts": counts, "files": len(file_rows), "gates": len(gates)}, sort_keys=True))
