#!/usr/bin/env python3
"""Build v23 from frozen v22 rows and explicit independent-review overlays."""
import csv
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

here = Path(__file__).resolve().parent
reports = here.parents[1]
v22 = reports / "anneal-3730-3731-final-coverage-audit-2026-09-29-v22/support"
r1 = "anneal-3731-i001-i053-residual-reaudit-2026-09-29"
r2 = "anneal-3731-i054-i106-independent-rereview-2026-09-29"
r3 = "anneal-3731-i107-i159-independent-rereview-2026-09-29"
rc = "anneal-3730-174-row-crosswalk-reaudit-2026-09-29"
rv = "anneal-3730-3731-v22-independent-rereview-2026-09-29"
c03 = "anneal-3730-c03-proof-resend-refresh-2026-09-29"
f15 = "anneal-3730-f15-final-versus-moved-lake-2026-09-29"
i080 = "anneal-3731-i080-shared-cargo-target-two-process-2026-09-29"
new_packages = (r1, r2, r3, rc, rv, c03, f15, i080)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def csv_rows(path):
    with path.open(newline="") as stream:
        return list(csv.DictReader(stream))

def write_csv(path, rows):
    with path.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]), lineterminator="\n", extrasaction="raise")
        writer.writeheader()
        writer.writerows(rows)

base = json.loads((v22 / "row-challenge-v22.json").read_text())
assert len(base) == 333 and len({row["id"] for row in base}) == 333
early = {}
for item, verdict, finding in re.findall(
    r"(?m)^\| (I\d{3}) \| ([PA]) \| (.+) \|$",
    (reports / r1 / "REPORT.md").read_text(),
):
    early[item] = (verdict, finding)
assert set(early) == {f"I{i:03}" for i in range(1, 54)}
mid = {row["id"]: row for row in csv_rows(reports / r2 / "support/row-review.csv")}
late = {row["id"]: row for row in csv_rows(reports / r3 / "support/row-review.csv")}
assert set(mid) == {f"I{i:03}" for i in range(54, 107)}
assert set(late) == {f"I{i:03}" for i in range(107, 160)}
cross = {row["id"]: row for row in json.loads((reports / rc / "support/audit.json").read_text())["rows"]}
assert len(cross) == 174 and {row["id"] for row in base if row["kind"] == "suggestion"} == set(cross)
challenged = {item for item, row in cross.items() if row["audit_finding"] != "no_further_discrepancy_found"}
assert len(challenged) == 23

investigation_residuals = {
    "I010": "A 256-source capture covered renames, symlink retargeting and mutable output; a new two-full-collection ABA schedule accepted an impossible mixed A/B pair when selection was unfenced. Coherent arbitrary live-tree capture still needs an immutable selection, owner epoch or protected snapshot and complete dependency closure.",
    "I011": "Finite identity/alias/version-reset controls and the new two-full-collection filesystem ABA schedule exist. Actual Anneal document, workspace, model, worker and request identities through restart and publication remain untested.",
    "I052": "A new paired tiny Lake project built at final path versus built at staging then renamed to that same final path; setup, server, batch and no-build agreed, but Dep.trace retained seven staging paths. A real Anneal archive/generated consumer with native paths, setup and retained workers remains untested.",
}
investigation_prerequisites = {
    "I129": "Implement the Anneal claim-relative machine status lattice across stale models, admissions, obligations and Rust coverage; then freeze its user/agent presentation and run a controlled interpretation evaluation.",
}
suggestion_residuals = {
    "C03": "Watched import replacement plus identical-text and changed-text didChange left the pinned direct Lean worker stale; close/reopen, fresh server and batch saw the new import. The explicit file-worker supervisor reset, new workspace/server generation and full three-launch-mode refresh comparison remain open.",
    "F15": "A paired tiny Lake project built at final path versus staging then rename gave matching setup, server, batch and no-build observations, while Dep.trace retained staging paths. Real prepared Anneal archive, generated consumer, native paths and retained workers remain untested.",
    "F19": "Selected clean/prepared tiny controls exist; an independently constructed clean-build oracle for the actual prepared Anneal interface/archive and its assumptions, imports, goals and artifacts remains untested. Human participants are not required by this exact suggestion.",
    "I01": "Selected batch/fresh/warm/live controls and the disposable embedded-proof/generated-model vertical exist. Same-subject equivalence over the actual Anneal interface, archive, obligations, imports and assumptions remains untested; independent operator/machine confirmation follows a runnable product oracle.",
    "I03": "Fresh batch checked captured proofs and old/new import combinations after live queries. Actual Anneal acceptance followed by an independently constructed fresh verification oracle remains untested; human participants are not required by this suggestion.",
}
suggestion_prerequisites = {
    "C03": "Exercise explicit file-worker supervisor restart and new workspace/server generation under matched imported-artifact transitions across the supported Lean/Lake launch modes, then compare each with fresh batch.",
    "D01": "Implemented Anneal unsaved-Rust overlay/shadow consumer and selected Charon compilation route with matched saved/private source identities.",
    "F02": "Built real Anneal prepared archive and clean read-only consumer with first server goal and complete producer/write observations.",
    "F14": "Built producer-removed Anneal prepared archive and consumer; separately relocate toolchain and consumer while checking setup, native imports and retained workers.",
    "F15": "Built Anneal prepared archive and generated consumer for matched final-path versus moved-path setup, server, native import and retained-worker checks.",
    "F19": "Frozen Anneal prepared interface/archive and a runnable clean-build consumer for an independently constructed oracle.",
    "I01": "Frozen Anneal interface, actual prepared archive and same-subject batch/live paths; then independently compare fresh, warm, edited and restarted results.",
    "I03": "Runnable Anneal live-acceptance path, exact captured subject and independently constructed fresh batch verification oracle.",
    "I04": "Built Anneal prepared archive and cold interactive consumer after a matched batch-accepted subject.",
    "I08": "Frozen Anneal protocol and rendered running interface before consenting independent participants evaluate partial-result taint and failure states.",
}
suggestion_categories = {
    "C03": ["product"],
    "D01": ["product"], "F02": ["product", "dependency"],
    "F14": ["product", "dependency"], "F19": ["product"],
    "I01": ["product"], "I03": ["product"], "I04": ["product", "dependency"],
    "I08": ["human", "product"],
}
resource_ids = {"J01", "J02", "J03", "J04", "J05", "J06", "J07", "J08", "J09", "J10", "J12", "J14"}
new_evidence = {
    "I010": [r1], "I011": [r1], "I052": [f15], "I080": [i080],
    "I147": [r3], "C03": [c03], "F15": [f15],
    "I01": ["anneal-3731-embedded-proof-generated-model-vertical-v4-30-0-rc2"],
}
extra_evidence_files = {
    c03: ["support/results.json", "support/check.py"],
    f15: ["support/results.json", "support/check.py"],
    i080: ["support/results.json", "support/check.py"],
    r1: ["support/aba-double-collect-results.json", "support/check_aba_double_collect.py"],
    r3: ["support/i147-same-mtime/transcript.json", "support/i147-comment-equivalence/transcript.json", "support/check.py"],
}

judgments = []
for old in base:
    row = dict(old)
    item = row["id"]
    status = row["v22_status"]
    gates = list(row["v22_gate_categories"])
    residual = row["v22_specific_remaining_delta"]
    next_step = row["v22_next_prerequisite"]
    evidence = new_evidence.get(item, [])
    if row["kind"] == "investigation":
        if item in early:
            verdict, finding = early[item]
            assert (verdict == "A") == (status == "complete"), item
            assessment = finding
            review_package = r1
        elif item in mid:
            source = mid[item]
            assert source["review_status"] == status
            assert source["requested_scope"]
            gates = source["gate_categories"].split(";") if source["gate_categories"] else []
            residual, next_step = source["specific_remaining_delta"], source["next_prerequisite"]
            assessment = "Independent exact-scope review retained this status; see the per-ID row-review record."
            review_package = r2
        else:
            source = late[item]
            assert source["review_status"] == status
            gates = source["review_gate_categories"].split(";") if source["review_gate_categories"] else []
            residual, next_step = source["review_remaining_delta"], source["next_prerequisite"]
            assessment = "Independent exact-scope review retained this status; see the per-ID row-review record."
            review_package = r3
        residual = investigation_residuals.get(item, residual)
        next_step = investigation_prerequisites.get(item, next_step)
    else:
        source = cross[item]
        assert source["v22_status"] == status
        assert source["recommended_status"] in ("complete", "partial", "not-run", "conditional")
        status = source["recommended_status"]
        assessment = source["audit_note"]
        review_package = rc
        residual = suggestion_residuals.get(item, residual)
        if item in suggestion_prerequisites:
            next_step = suggestion_prerequisites[item]
        if item in suggestion_categories:
            gates = suggestion_categories[item]
        if item in resource_ids:
            gates = sorted(set(gates) | {"product"})
            next_step = "Representative prepared Anneal workload and scheduler/consumer, plus the resource or platform controls already named in v22: " + next_step
        if item == "F12":
            # v22 already names the two-writer reverse-kill result; the challenge
            # note is a prompt to preserve that narrower current residual.
            assert "two-writer" in residual and "reverse-kill" in residual
            assessment = "The crosswalk challenge's two-writer cell is already explicit in v22; retain it. Artifact/trace syscall interruption and Anneal ownership remain."
    evidence_files = []
    for package in evidence:
        evidence_files.extend([f"reports/{package}/REPORT.md", f"reports/{package}/REPORT.json"])
        evidence_files.extend(f"reports/{package}/{path}" for path in extra_evidence_files.get(package, []))
    row.update({
        "v23_status": status,
        "v23_gate_categories": gates,
        "v23_specific_remaining_delta": residual,
        "v23_post_v22_scope_assessment": assessment,
        "v23_review_package": review_package,
        "v23_new_evidence_packages": evidence,
        "v23_evidence_files": evidence_files,
        "v23_next_prerequisite": next_step,
    })
    assert residual and next_step
    judgments.append(row)
by_id = {row["id"]: row for row in judgments}
assert len(by_id) == 333
assert {row["id"] for row in judgments if row["v23_status"] != row["v22_status"]} == {"C03"}
(here / "row-challenge-v23.json").write_text(json.dumps(judgments, indent=2, sort_keys=True) + "\n")

fields = ("v23_status", "v23_gate_categories", "v23_specific_remaining_delta", "v23_post_v22_scope_assessment", "v23_review_package", "v23_new_evidence_packages", "v23_evidence_files", "v23_next_prerequisite")
def extend(source, key):
    out = []
    for old in csv_rows(v22 / source):
        row = dict(old)
        decision = by_id[row[key]]
        row["status"] = decision["v23_status"]
        for field in fields:
            value = decision[field]
            row[field] = ";".join(value) if isinstance(value, list) else value
        out.append(row)
    assert len(out) == (159 if key == "id" else 174)
    return out

investigations = extend("investigation-final-v22.csv", "id")
suggestions = extend("3730-crosswalk-final-v22.csv", "3730_id")
write_csv(here / "investigation-final-v23.csv", investigations)
write_csv(here / "3730-crosswalk-final-v23.csv", suggestions)

package_rows = []
for name in new_packages:
    directory = reports / name
    assert (directory / "REPORT.md").is_file() and (directory / "REPORT.json").is_file()
    checker = directory / "support/check.py"
    package_rows.append({"package": name, "report_sha256": sha(directory / "REPORT.md"), "metadata_sha256": sha(directory / "REPORT.json"), "checker_sha256": sha(checker) if checker.is_file() else ""})
write_csv(here / "review-package-inventory-v23.csv", package_rows)

counts = {"investigations": dict(Counter(row["status"] for row in investigations)), "suggestions": dict(Counter(row["status"] for row in suggestions))}
assert counts == {"investigations": {"partial": 151, "complete": 4, "not-run": 1, "conditional": 3}, "suggestions": {"partial": 162, "complete": 3, "not-run": 5, "conditional": 4}}
inputs = {"v22/row-challenge-v22.json": v22 / "row-challenge-v22.json", "v22/investigation-final-v22.csv": v22 / "investigation-final-v22.csv", "v22/3730-crosswalk-final-v22.csv": v22 / "3730-crosswalk-final-v22.csv", "v22/issue-scope-snapshot.json": v22 / "issue-scope-snapshot.json", f"{r1}/REPORT.md": reports / r1 / "REPORT.md", f"{r2}/support/row-review.csv": reports / r2 / "support/row-review.csv", f"{r3}/support/row-review.csv": reports / r3 / "support/row-review.csv", f"{rc}/support/audit.json": reports / rc / "support/audit.json", f"{rv}/support/review.json": reports / rv / "support/review.json"}
generated = ("row-challenge-v23.json", "investigation-final-v23.csv", "3730-crosswalk-final-v23.csv", "review-package-inventory-v23.csv")
validation = {"baseline_reference_head": "75fa78c1b623ab8db9d9acb4f31ec7958bfb9110", "row_count": 333, "suggestion_destination_links": 345, "status_counts": counts, "changed_status_ids": ["C03"], "changed_investigation_residual_ids": sorted(row["id"] for row, old in zip(judgments, base) if row["kind"] == "investigation" and row["v23_specific_remaining_delta"] != old["v22_specific_remaining_delta"]), "changed_suggestion_residual_ids": sorted(row["id"] for row, old in zip(judgments, base) if row["kind"] == "suggestion" and row["v23_specific_remaining_delta"] != old["v22_specific_remaining_delta"]), "changed_prerequisite_ids": sorted(row["id"] for row, old in zip(judgments, base) if row["v23_next_prerequisite"] != old["v22_next_prerequisite"]), "challenged_suggestion_ids": sorted(challenged), "new_packages": list(new_packages), "input_sha256": {name: sha(path) for name, path in inputs.items()}, "generated_sha256": {name: sha(here / name) for name in generated}}
(here / "validation-v23.json").write_text(json.dumps(validation, indent=2, sort_keys=True) + "\n")
print(json.dumps({"rows": 333, "counts": counts, "changed_prerequisites": len(validation["changed_prerequisite_ids"]), "challenged_suggestions": len(challenged)}, sort_keys=True))
