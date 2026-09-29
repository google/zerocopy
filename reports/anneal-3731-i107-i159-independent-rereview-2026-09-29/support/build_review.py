#!/usr/bin/env python3
"""Rebuild this dated I107–I159 review from the retained v22 ledger."""
import csv
import hashlib
import json
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
REPORTS = ROOT / "reports"
V22 = REPORTS / "anneal-3730-3731-final-coverage-audit-2026-09-29-v22" / "support"
SOURCE = V22 / "investigation-final-v22.csv"
BASELINE = "75fa78c1b623ab8db9d9acb4f31ec7958bfb9110"

# These are corrections to the residual account, not promotions of item status.
RESIDUALS = {
    "I126": (
        "The retained trust-boundary fixture already distinguishes source hashing/Cargo metadata from execution: Cargo build scripts and proc macros, and Lean run_cmd, wrote owned out-of-workspace markers, spawned a child, and used owned loopback. R44 separately covers selected cross-tool proof/trust controls. Lake configuration, native-extension execution, enforced containment/resource limits, and Anneal trust-entry policy remain."
    ),
    "I129": (
        "The prototype labels old-selected guidance stale during failed and pending generations, then distinguishes a newly selected proof and cross-model failures. A complete Anneal machine status lattice across admissions, obligations and covered Rust claims remains; the requested user/agent interpretation also needs controlled evaluation."
    ),
    "I147": (
        "The cited three-launch-mode matrix already changed a valid OLean while source stayed fixed; E10 already changed an external Lean model while Aeneas output stayed byte-identical. This review adds a direct same-nanosecond-mtime OLean replacement with old/new/reopened/fresh consumers and a comment-only source change whose rebuilt OLean is byte-identical. Broader timestamp schedules, semantic-equivalent noncomment changes, options/native/setup identities, and Anneal freshness policy remain."
    ),
    "I148": (
        "Pinned Charon and Aeneas repeat/concurrent process controls, CLI flag/file-set variants, and paired bundle outputs exist. The current V2 producing flags and representative workload are not established; harmless textual instability's downstream Lake/Lean cost and semantic comparator remain. Arbitrary unselected flags or releases are not an item-completion requirement."
    ),
    "I151": (
        "The cited shared-tree report already ran two conflicting Lake processes in one writable package/build tree, with reverse killed-writer schedules, fresh Lean, no-build, and repair checks. Separate same-key artifact-cache pairs and selected generated-tree in-place mixes cover different surfaces. A matched isolated-versus-shared comparison, interruption during shared build-tree artifact/trace writes, a general ownership contract, and Anneal policy remain."
    ),
}
GATES = {"I129": "human;product"}
LOCAL = {
    "I147": "Same-mtime valid OLean replacement and byte-identical comment-only rebuild executed in this report; repeat under other launch modes or broader source/options only if a product decision needs it.",
    "I151": "A more exact shared-tree artifact/trace write interruption is locally possible with cached Lake, but earlier two-writer runs sampled 3.6 GiB RSS and already establish a bounded conflict/crash cell; no additional run was needed to preserve partial status.",
}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def write_csv(path, fields, rows):
    with path.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=fields, lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)

def main():
    rows = list(csv.DictReader(SOURCE.open(newline="")))[106:159]
    assert [r["id"] for r in rows] == [f"I{i:03}" for i in range(107, 160)]
    package_fields = [name for name in rows[0]
                      if name.endswith(("_experiment_packages", "_evidence_packages"))
                      or name == "prior_evidence_packages"]
    evidence_fields = [name for name in rows[0] if name.endswith("_evidence_files")]
    package_ids = defaultdict(set)
    evidence_ids = defaultdict(set)
    reviewed = []
    for row in rows:
        item = row["id"]
        for field in package_fields:
            for slug in row[field].split(";"):
                if slug.strip():
                    package_ids[slug.strip()].add(item)
        for field in evidence_fields:
            for pointer in row[field].split(";"):
                if pointer.strip():
                    evidence_ids[pointer.strip()].add(item)
        reviewed.append({
            "id": item,
            "title": row["title"],
            "exact_requested_scope": row["requested_scope"],
            "review_status": row["v22_status"],
            "review_gate_categories": GATES.get(item, row["v22_gate_categories"]),
            "review_remaining_delta": RESIDUALS.get(item, row["v22_specific_remaining_delta"]),
            "next_prerequisite": row["v22_next_prerequisite"],
            "new_cached_local_cell": LOCAL.get(item, "No distinct cached-only cell identified beyond cited component evidence and stated prerequisite."),
            "v22_status_changed": "false",
        })
    write_csv(HERE / "row-review.csv", list(reviewed[0]), reviewed)

    packages = []
    for slug, ids in sorted(package_ids.items()):
        directory = REPORTS / slug
        report = directory / "REPORT.md"
        metadata = directory / "REPORT.json"
        assert report.is_file() and metadata.is_file(), slug
        json.loads(metadata.read_text())
        checker = directory / "support/check.py"
        packages.append({
            "package": slug,
            "ids": ";".join(sorted(ids)),
            "report_md_sha256": sha(report),
            "report_json_sha256": sha(metadata),
            "checker_sha256": sha(checker) if checker.is_file() else "",
        })
    write_csv(HERE / "cited-package-inventory.csv", list(packages[0]), packages)

    evidence = []
    for pointer, ids in sorted(evidence_ids.items()):
        path = ROOT / pointer if pointer.startswith("reports/") else REPORTS / pointer
        assert path.is_file(), pointer
        evidence.append({"pointer": pointer, "ids": ";".join(sorted(ids)), "sha256": sha(path)})
    write_csv(HERE / "cited-evidence-inventory.csv", list(evidence[0]), evidence)

    probe_files = sorted(p for p in HERE.glob("i147-*/*") if p.is_file())
    record = {
        "baseline_reference_head": BASELINE,
        "v22_ledger_sha256": sha(SOURCE),
        "v22_row_challenge_sha256": sha(V22 / "row-challenge-v22.json"),
        "v22_issue_snapshot_sha256": sha(V22 / "issue-scope-snapshot.json"),
        "counts": {
            "rows": len(reviewed),
            "status": {s: sum(r["review_status"] == s for r in reviewed) for s in ("complete", "partial", "conditional")},
            "packages": len(packages),
            "package_checkers": sum(bool(r["checker_sha256"]) for r in packages),
            "evidence_files": len(evidence),
        },
        "generated_sha256": {name: sha(HERE / name) for name in (
            "row-review.csv", "cited-package-inventory.csv", "cited-evidence-inventory.csv")},
        "i147_probe_files_sha256": {str(p.relative_to(HERE)): sha(p) for p in probe_files},
    }
    (HERE / "validation.json").write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")

if __name__ == "__main__":
    main()
