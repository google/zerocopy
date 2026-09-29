#!/usr/bin/env python3
"""Derive v26 from the frozen v25 ledger and six retained experiments.

This builder is offline and writes only files in its own support directory.
"""

import csv
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORT = HERE.parent
REPORTS = REPORT.parent
ROOT = REPORTS.parent
V25 = REPORTS / "anneal-3730-3731-final-coverage-audit-2026-09-29-v25" / "support"
V22 = REPORTS / "anneal-3730-3731-final-coverage-audit-2026-09-29-v22" / "support"
PACKAGES = (
    "anneal-v2-cargo-root-selection-multipackage-2026-09-29",
    "anneal-v2-feature-subject-slug-collision-2026-09-29",
    "anneal-3731-i080-incremental-target-layout-matrix-2026-09-29",
    "charon-zerocopy-library-repeat-order-nightly-2026-05-31",
    "anneal-3731-full-chain-transient-workspace-accounting-2026-09-29",
    "anneal-3731-i125-plugin-cwd-path-alias-v4-30-0-rc2",
)
HERE_NAME = REPORT.name


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def csv_rows(path):
    with path.open(newline="") as stream:
        return list(csv.DictReader(stream))


def write_csv(path, rows):
    with path.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]), lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)


def evidence(package, *names):
    paths = [f"reports/{package}/{name}" for name in names]
    assert all((ROOT / path).is_file() for path in paths), paths
    return paths


ROOT_SELECTION = PACKAGES[0]
FEATURE_SLUG = PACKAGES[1]
INCREMENTAL = PACKAGES[2]
REPEAT_ORDER = PACKAGES[3]
TRANSIENT = PACKAGES[4]
PLUGIN_ALIAS = PACKAGES[5]

# The report names its own exact claim and its remaining boundary. These are
# additions to the v25 row, not a replacement for its historical evidence.
UPDATES = {
    "I020": {
        "residual": (
            "The checked-in V2 resolver includes a non-default virtual-workspace member and a binary whose required feature is disabled, unlike matched Cargo check selections. "
            "A separate checked-in V2 slug helper gives default and selected-feature library compilations one LLBC filename although Charon emits different 7/11 bodies. "
            "Both harnesses bypass the V2 CLI. A complete subject key, selected Charon invocation, interactive proof-context choice, visible mismatch, and cross-stage model/proof rejection remain untested."
        ),
        "prerequisite": (
            "Connect the checked-in root selector and a complete compilation-unit key to an Anneal Charon invocation and proof-query subject selector; reject wrong-subject model/proof results in a generated consumer."
        ),
        "assessment": "Resolver root-selection and feature-locator counterexamples are direct bounded components; neither is an Anneal extraction or proof query.",
        "packages": [ROOT_SELECTION, FEATURE_SLUG],
        "files": evidence(ROOT_SELECTION, "REPORT.md", "REPORT.json", "support/check.py", "support/commands.json", "support/raw/root_default.stdout", "support/raw/cargo_default.stdout", "support/raw/alpha_bins.stdout", "support/raw/cargo_alpha_bins.stdout")
        + evidence(FEATURE_SLUG, "REPORT.md", "REPORT.json", "support/check.py", "support/results.json", "support/raw/slug.stdout", "support/artifacts/default.llbc", "support/artifacts/selected.llbc"),
        "relation": "new direct V2 resolver and slug-helper component evidence",
    },
    "I076": {
        "residual": (
            "Earlier sibling libraries shared serialized crate/function names but had different 11/29 bodies. The checked-in V2 LLBC slug now also aliases default and selected-feature compilations of one library whose Charon bodies are 7/11. "
            "The feature result is a locator collision, not an observed overwrite. A complete Cargo compilation-unit key, host/target/profile/cfg/tool matrix, output ownership, concurrent arbitration, invalidation, and collision-rejecting Anneal publication remain untested."
        ),
        "prerequisite": (
            "Implement Anneal compilation-unit identity and produced-output ownership, then run sibling-name and feature collisions plus host/target/profile/cfg/tool and concurrent producer controls through the real extraction publisher."
        ),
        "assessment": "One checked-in V2 filename helper demonstrably aliases two feature-selected Charon bodies; publication and invalidation are still product gates.",
        "packages": [FEATURE_SLUG],
        "files": evidence(FEATURE_SLUG, "REPORT.md", "REPORT.json", "support/check.py", "support/harness/src/scanner.rs", "support/results.json", "support/raw/slug.stdout", "support/artifacts/default.llbc", "support/artifacts/selected.llbc"),
        "relation": "new direct V2 feature-locator collision component evidence",
    },
    "I080": {
        "residual": (
            "A new four-cell private/shared Cargo-target by incremental-off/on matrix ran cold and warm pairs: all 16 Charon requests produced parseable LLBC with equal selected local body projections. Shared cells logged build-directory lock waits; incremental-on targets retained more files and bytes. "
            "The fixture held equal-length source roots and made no edits or cancellations. Representative sustained load, path-sensitive source changes, incremental-on cancellation/restart, many-worker cleanup and physical resource economics remain untested."
        ),
        "prerequisite": (
            "Use a guarded representative Charon workload and measured RAM/disk headroom to compare incremental-on source changes, cancellation/restart, many-worker cleanup and shared versus private target ownership; connect the result to Anneal scheduling policy."
        ),
        "assessment": "The complete 2-by-2 cold/warm target-layout component adds incremental-on resource evidence; it makes no cancellation or production reuse claim.",
        "packages": [INCREMENTAL],
        "files": evidence(INCREMENTAL, "REPORT.md", "REPORT.json", "support/check.py", "support/results.json", "support/probe.py"),
        "relation": "new direct incremental target-layout component evidence",
    },
    "I148": {
        "residual": (
            "Three serial Charon runs on the real zerocopy library changed raw LLBC only in the destination path and ordering of 17,903 short_names entries; the field-aware comparison found identical remaining bytes and the pinned Aeneas importer clears short_names. "
            "Every LLBC nevertheless had has_errors: true and 13 warnings despite process exit 0. Aeneas and Lean were not run, so successful larger-corpus translation, downstream cost/comparator and actual V2 workload determinism remain untested."
        ),
        "prerequisite": (
            "Obtain a larger matched corpus whose selected Charon outputs are error-free, or an actual Anneal product workload, under a protected resource budget; compare generated Aeneas/Lean output and relevant semantic equivalence."
        ),
        "assessment": "A real library narrows Charon textual repeatability only; the error-bearing output cannot support downstream translation or proof claims.",
        "packages": [REPEAT_ORDER],
        "files": evidence(REPEAT_ORDER, "REPORT.md", "REPORT.json", "support/check.py", "support/observations.json", "support/comparison.json", "support/replay-comparison.json", "support/first-order-differences.json"),
        "relation": "new direct error-bearing Charon repeat-order component evidence",
    },
    "I113": {
        "residual": (
            "A one-worker full Rust-to-Lake-to-server replay now records 24 stage boundaries and 331 interval samples. The largest observed worker-tree regular-file allocation was 4,825,088 bytes; 12 Cargo target files totaling 28,672 allocated bytes were recorded before harness cleanup and absent afterward. "
            "Four selected external roots showed zero net du change at 1 KiB resolution, not zero writes. Cumulative bytes written, sub-sample temporary peaks, all outside-workspace operations, APFS exclusive extents, dependencies and worker-scaling terms remain unmeasured."
        ),
        "prerequisite": (
            "Run a guarded representative Anneal consumer with validated process-tree file-event and byte accounting across worker and outside-workspace paths, true transient peak capture, shared dependency attribution and multiple-worker scaling."
        ),
        "assessment": "One successful tiny full-chain replay adds observed stage-by-stage allocation and a deleted Cargo target term, not a complete write trace or real-project disk bill.",
        "packages": [TRANSIENT],
        "files": evidence(TRANSIENT, "REPORT.md", "REPORT.json", "support/check.py", "support/observations.json.gz", "support/baseline-retained.json", "support/probe.py"),
        "relation": "new direct one-worker transient workspace accounting component evidence",
    },
    "I125": {
        "residual": (
            "Pinned Lean --plugin=file resolves a bare plugin basename relative to cwd through realPath; LEAN_PATH did not supply that file. A same-basename symlink target change selected v1 then v2 initializer markers in newly opened file workers while the old file kept answering, and a fresh server selected v2. "
            "The marker is an execution witness, not loaded-binary attestation. ABI compatibility, multiple native dependencies, process mappings, Anneal worker routing and GC/identity policy remain untested."
        ),
        "prerequisite": (
            "Define and implement Anneal's canonical plugin-path/content and worker-generation ownership, then test compatible-looking ABI replacements, multiple dependencies, loaded mappings and restart/GC behavior through actual consumers."
        ),
        "assessment": "The pinned loader source and cwd/symlink execution close one path-resolution ambiguity and add a new-worker identity witness; they do not establish a general ABI or product rule.",
        "packages": [PLUGIN_ALIAS],
        "files": evidence(PLUGIN_ALIAS, "REPORT.md", "REPORT.json", "support/check.py", "support/transcript.json", "support/probe.py"),
        "relation": "new direct Lean plugin cwd and path-alias component evidence",
    },
    "D03": {
        "residual": (
            "The new cold/warm private/shared by incremental-off/on Charon matrix produced 16 parseable LLBCs with equal selected bodies, observed shared Cargo lock waits and measured a larger incremental-on target footprint. "
            "It did not mutate materialized source, cancel a job, attest the actual Charon-producing Cargo unit, or measure representative parallel resource economics; Anneal invocation and ownership policy remain open."
        ),
        "prerequisite": (
            "Implement producing-unit attestation and target ownership for materialized Anneal snapshots, then compare guarded representative warm/changed-source parallel runs with explicit resource bounds."
        ),
        "assessment": "I080's matrix directly strengthens Cargo target reuse economics for D03 only; it does not satisfy snapshot or producer attestation scope.",
        "packages": [INCREMENTAL],
        "files": evidence(INCREMENTAL, "REPORT.md", "REPORT.json", "support/check.py", "support/results.json"),
        "relation": "new direct I080 target-layout component evidence for D03",
    },
    "D07": {
        "residual": (
            "Alongside the prior same-name sibling LLBC witness, the checked-in V2 slug helper assigns one LLBC filename to default and selected-feature library compilations whose Charon bodies are 7/11. "
            "This is a feature-locator collision, not an Anneal overwrite. Complete compilation-unit identity, invalidation and collision-safe publication across target kind, host/target triple, profile, features, cfg/build output and tool settings remain open."
        ),
        "prerequisite": (
            "Implement Anneal compilation-unit keys, output ownership and dependency invalidation; run the feature collision and sibling-name controls plus host/target/profile/cfg/tool variants through actual concurrent producers and proof consumers."
        ),
        "assessment": "The feature-specific V2 locator witness narrows D07's feature dimension; no end-to-end invalidation matrix ran.",
        "packages": [FEATURE_SLUG],
        "files": evidence(FEATURE_SLUG, "REPORT.md", "REPORT.json", "support/check.py", "support/harness/src/scanner.rs", "support/results.json", "support/artifacts/default.llbc", "support/artifacts/selected.llbc"),
        "relation": "new direct I020/I076 feature-locator component evidence for D07",
    },
    "E07": {
        "residual": (
            "Three real zerocopy library Charon runs changed raw LLBC through one output path and keyed short_names entry order; after those exact fields were normalized or omitted, all other bytes matched. The pinned Aeneas CLI importer clears short_names, giving a source-backed reason this one textual difference is harmless to that importer if the LLBC loads. "
            "All outputs were has_errors: true with 13 warnings, so no successful Aeneas/Lean semantic-sameness oracle or authenticated Anneal obligation comparator ran. Broader moves, signatures and cross-tool mutants remain open."
        ),
        "prerequisite": (
            "Use an error-free matched larger corpus or actual Anneal workload to compare generated declarations, imported Lean meaning and obligations under controlled textual changes, then define an authenticated semantic comparator."
        ),
        "assessment": "The keyed-multiset and Aeneas-source controls directly inform one harmless textual-instability case; no successful semantic equivalence is claimed.",
        "packages": [REPEAT_ORDER],
        "files": evidence(REPEAT_ORDER, "REPORT.md", "REPORT.json", "support/check.py", "support/observations.json", "support/comparison.json", "support/first-order-differences.json"),
        "relation": "new field-specific textual-instability component evidence for E07",
    },
    "J01": {
        "residual": (
            "A one-worker tiny Rust/Charon/Aeneas/Lean/Lake/server replay now gives stage-boundary file, inode and allocated-byte counts, an observed 4,825,088-byte workspace maximum and a deleted Cargo-target term. "
            "It is not a scaling sweep: representative generated projects, multiple workers, archive/shared dependency attribution, true temporary peak, cumulative/outside writes, scheduler/GC and guarded capacity remain unmeasured."
        ),
        "prerequisite": (
            "Use representative prepared Anneal generated projects with a bounded multiworker scheduler/consumer and validated per-stage, temporary, outside-root and physical resource accounting."
        ),
        "assessment": "The I113 replay supplies one tiny baseline for stage allocation, not the requested real generated-project scaling economics.",
        "packages": [TRANSIENT],
        "files": evidence(TRANSIENT, "REPORT.md", "REPORT.json", "support/check.py", "support/observations.json.gz", "support/baseline-retained.json"),
        "relation": "new one-worker stage-accounting component evidence for J01",
    },
    "J02": {
        "residual": (
            "The new full-chain replay classifies observed worker-local files and allocated blocks at 24 boundaries, including 12 Cargo-target files and 28,672 allocated bytes deleted by cleanup; 331 samples give a lower bound on temporary allocation. "
            "Every copied or written byte is still not classified: sub-sample peaks, cumulative writes, outside-workspace operations, shared dependency extents, archive products and worker scaling remain open."
        ),
        "prerequisite": (
            "Trace all file writes and byte counts for a representative prepared Anneal worker and shared inputs through build, query and cleanup, with complete temporary/outside-root and multiworker attribution."
        ),
        "assessment": "The I113 replay adds a previously deleted Cargo target and stage allocation, while the suggestion's every-byte standard remains unmet.",
        "packages": [TRANSIENT],
        "files": evidence(TRANSIENT, "REPORT.md", "REPORT.json", "support/check.py", "support/observations.json.gz", "support/baseline-retained.json"),
        "relation": "new transient worker-local classification component evidence for J02",
    },
    "L02": {
        "residual": (
            "The one-chain I113 replay records worker-local stage allocations and a deleted Cargo target. Four selected external roots had unchanged before/after du totals at 1 KiB resolution and unchanged root metadata; this is zero observed net change, not proof of no outside writes. "
            "Actual adapter-wide filesystem effects, all outside paths, create/delete cycles, cumulative bytes written and injected failure behavior remain untraced."
        ),
        "prerequisite": (
            "Instrument the actual Charon/Aeneas/Lake/Lean adapters and Anneal workspace with validated process-tree filesystem tracing, including outside roots, writes that later disappear and failure/cancellation cases."
        ),
        "assessment": "The I113 replay adds a bounded positive worker-tree inventory and selected net-root controls, not a complete backend effects inventory.",
        "packages": [TRANSIENT],
        "files": evidence(TRANSIENT, "REPORT.md", "REPORT.json", "support/check.py", "support/observations.json.gz", "support/probe.py"),
        "relation": "new stage-boundary and selected net-root component evidence for L02",
    },
}


def verify_live_scope(live, frozen):
    old = json.loads((V25 / "live-issue-hashes.json").read_text())["issues"]
    for number, state in ((3730, "closed"), (3731, "open")):
        key = str(number)
        item = live["issues"][key]
        assert item["number"] == number and item["state"] == state
        assert item["body_sha256"] == sha_bytes(item["body"].encode()) == old[key]["body_sha256"]
        assert item["body"] == frozen[key]["body"]
        assert len(item["comments"]) == len(old[key]["comments"]) == len(frozen[key]["comments"]) == 1
        comment = item["comments"][0]
        assert comment["id"] == old[key]["comments"][0]["id"]
        assert comment["body_sha256"] == sha_bytes(comment["body"].encode()) == old[key]["comments"][0]["body_sha256"]
        assert comment["body"] == frozen[key]["comments"][0]["body"]


def sha_bytes(data):
    return hashlib.sha256(data).hexdigest()


def main():
    previous = json.loads((V25 / "row-challenge-v25.json").read_text())
    frozen = json.loads((V22 / "issue-scope-snapshot.json").read_text())
    live = json.loads((HERE / "live-issue-snapshot-v26.json").read_text())
    verify_live_scope(live, frozen)
    assert len(previous) == 333 and len({row["id"] for row in previous}) == 333
    assert set(UPDATES) == {"I020", "I076", "I080", "I113", "I125", "I148", "D03", "D07", "E07", "J01", "J02", "L02"}

    out = []
    for before in previous:
        row = dict(before)
        update = UPDATES.get(row["id"])
        row.update({
            "v26_status": row["v25_status"],
            "v26_gate_categories": row["v25_gate_categories"],
            "v26_specific_remaining_delta": update["residual"] if update else row["v25_specific_remaining_delta"],
            "v26_post_v25_scope_assessment": update["assessment"] if update else "No new v26 evidence changes this row.",
            "v26_review_package": HERE_NAME if update else row["v25_review_package"],
            "v26_new_evidence_packages": update["packages"] if update else [],
            "v26_evidence_files": update["files"] if update else [],
            "v26_next_prerequisite": update["prerequisite"] if update else row["v25_next_prerequisite"],
            "v26_evidence_relation": update["relation"] if update else "No v26 change.",
        })
        assert row["v26_specific_remaining_delta"] and row["v26_next_prerequisite"]
        out.append(row)
    assert {row["id"] for row in out if row["v26_specific_remaining_delta"] != row["v25_specific_remaining_delta"]} == set(UPDATES)
    assert not any(row["v26_status"] != row["v25_status"] for row in out)
    (HERE / "row-challenge-v26.json").write_text(json.dumps(out, indent=2, sort_keys=True, ensure_ascii=False) + "\n")

    by_id = {row["id"]: row for row in out}
    fields = ("v26_status", "v26_gate_categories", "v26_specific_remaining_delta", "v26_post_v25_scope_assessment",
              "v26_review_package", "v26_new_evidence_packages", "v26_evidence_files", "v26_next_prerequisite", "v26_evidence_relation")

    def extend(filename, key):
        rows = []
        for before in csv_rows(V25 / filename):
            row = dict(before)
            choice = by_id[row[key]]
            assert before["status"] == choice["v26_status"]
            for field in fields:
                value = choice[field]
                row[field] = ";".join(value) if isinstance(value, list) else value
            rows.append(row)
        return rows

    investigations = extend("investigation-final-v25.csv", "id")
    suggestions = extend("3730-crosswalk-final-v25.csv", "3730_id")
    assert len(investigations) == 159 and len(suggestions) == 174
    write_csv(HERE / "investigation-final-v26.csv", investigations)
    write_csv(HERE / "3730-crosswalk-final-v26.csv", suggestions)

    issue_body = live["issues"]["3731"]["body"]
    issue_comment = live["issues"]["3731"]["comments"][0]["body"]
    titles = {item: re.sub(r"\s*\[[^]]+\]\.?$", "", title).strip()
              for source in (issue_body, issue_comment)
              for item, title in re.findall(r"(?m)^\*\*(I\d{3})\s+[—.]\s+([^\n]*?)\*\*", source)}
    cross = {item: (title.strip(), set(re.findall(r"I\d{3}", destinations)))
             for item, title, destinations in re.findall(r"(?m)^\| ([A-O]\d{2}) \| ([^|]+) \| ([^|]+) \|", issue_comment)}
    assert len(titles) == 159 and len(cross) == 174
    assert all(row["title"] == titles[row["id"]] for row in investigations)
    assert all(row["suggestion"] == cross[row["3730_id"]][0] and
               set(row["3731_destinations"].split(";")) == cross[row["3730_id"]][1]
               for row in suggestions)
    links = sum(len(destination) for _, destination in cross.values())
    assert links == 345

    inventory = []
    for package in PACKAGES:
        for path in sorted((REPORTS / package).rglob("*")):
            if path.is_file() and "__pycache__" not in path.parts and path.suffix != ".pyc":
                inventory.append({"path": path.relative_to(ROOT).as_posix(), "sha256": sha(path)})
    write_csv(HERE / "source-package-inventory-v26.csv", inventory)

    generated = ("row-challenge-v26.json", "investigation-final-v26.csv", "3730-crosswalk-final-v26.csv", "source-package-inventory-v26.csv")
    inputs = {"v25/row-challenge-v25.json": V25 / "row-challenge-v25.json",
              "v25/investigation-final-v25.csv": V25 / "investigation-final-v25.csv",
              "v25/3730-crosswalk-final-v25.csv": V25 / "3730-crosswalk-final-v25.csv",
              "v22/issue-scope-snapshot.json": V22 / "issue-scope-snapshot.json",
              "live-issue-snapshot-v26.json": HERE / "live-issue-snapshot-v26.json"}
    validation = {
        "source_reference_package": "anneal-3730-3731-final-coverage-audit-2026-09-29-v25",
        "source_anneal_revision": "bd0956be95c5f798f0c0484921b9b9d1fc6e9988",
        "row_count": len(out), "investigation_count": len(investigations), "suggestion_count": len(suggestions),
        "suggestion_destination_links": links,
        "status_counts": {"investigations": dict(Counter(row["status"] for row in investigations)),
                          "suggestions": dict(Counter(row["status"] for row in suggestions))},
        "changed_status_ids": [],
        "changed_residual_ids": sorted(UPDATES),
        "changed_prerequisite_ids": sorted(UPDATES),
        "new_evidence_ids": sorted(UPDATES),
        "source_packages": list(PACKAGES),
        "inventory_files": len(inventory),
        "input_sha256": {key: sha(path) for key, path in inputs.items()},
        "generated_sha256": {key: sha(HERE / key) for key in generated},
    }
    (HERE / "validation-v26.json").write_text(json.dumps(validation, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: validation[key] for key in ("row_count", "suggestion_destination_links", "changed_residual_ids", "inventory_files", "status_counts")}, sort_keys=True))


if __name__ == "__main__":
    main()
