#!/usr/bin/env python3
"""Derive the append-only v27 ledger from v26 and four retained reports.

Offline; writes only derived files inside this package's support directory.
"""

import csv
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V26 = REPORTS / "anneal-3730-3731-final-coverage-audit-2026-09-29-v26" / "support"
V22 = REPORTS / "anneal-3730-3731-final-coverage-audit-2026-09-29-v22" / "support"
SOURCE_PACKAGES = (
    "anneal-3730-3731-final-coverage-audit-2026-09-29-v26",
    "anneal-3731-charon-relocation-comment-provenance-2026-09-29",
    "anneal-3731-rich-goal-unsaved-recovery-v4-30-0-rc2",
    "anneal-3731-i151-matched-lake-writer-isolation-2026-09-29",
    "anneal-3731-compiler-backed-coordinate-bridge-2026-09-29",
)
V26_NAME, CHARON, RICH_GOAL, LAKE_WRITERS, COORDINATES = SOURCE_PACKAGES


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
    result = [f"reports/{package}/{name}" for name in names]
    assert all((ROOT / path).is_file() for path in result), result
    return result


# Each entry is limited to the exact stage and output exercised by its source.
UPDATES = {
    "I025": {
        "residual": (
            "A pinned rustc/Lean fixture now bridges exact copied Rust doc-comment bytes to a projected Lean file with CRLF, emoji, combining mark and a Rust-side tab. Real rustc JSON, Lean batch and Lean LSP error spans map through the recorded 31-byte interval; 28 valid scalar boundaries round-trip through byte/scalar/UTF-16 coordinates and seven invalid or unowned cases are rejected. "
            "The bridge is a hand-authored exact-copy harness, not Anneal's source map. Empty-line/display-width cases, negotiated editor encoding, unsaved revisions, production annotation grammar and generated obligations remain untested."
        ),
        "prerequisite": (
            "Implement Anneal's Rust-hosted projection and source map, then rerun the retained Unicode/CRLF/boundary corpus through real batch/live output and negotiated editor encodings, including empty lines, display-width loss and unsaved revisions."
        ),
        "assessment": "Compiler-backed byte/scalar/UTF-16 specimens and inverse-domain negatives add a direct I025 component; production map and editor negotiation remain absent.",
        "packages": [COORDINATES],
        "files": evidence(COORDINATES, "REPORT.md", "REPORT.json", "support/check.py", "support/Host.rs", "support/Projected.lean", "support/results.json", "support/transcript.json"),
        "relation": "direct pinned Rustc/Lean coordinate bridge evidence for I025 only",
    },
    "I043": {
        "residual": (
            "A pinned direct Lean server now gives matched plainGoal and getInteractiveGoals availability at 24 cursor/version pairs across valid, unsaved syntax-error, unknown-tactic and recovered nested proofs: 17 goals, two empty lists and five null results. At each goal pair the rich rendered target matches the plain target after presentation tags are stripped; fresh batch rejects both error variants. "
            "This does not test rich reference dereference/expiration, tactic macros, generated imports, projected Rust coordinates, concurrent requests or an Anneal exact-version fence."
        ),
        "prerequisite": (
            "Run plain and rich goal queries through Anneal's version-fenced projected document and generated imports, then test richer references, macro positions, cancellation and worker restart against fresh batch controls."
        ),
        "assessment": "The 24 direct Lean pairs close a bounded plain-versus-rich selection cell, not the adapter or reference-lifecycle question.",
        "packages": [RICH_GOAL],
        "files": evidence(RICH_GOAL, "REPORT.md", "REPORT.json", "support/check.py", "support/results.json", "support/transcript.json"),
        "relation": "direct rich/plain unsaved-goal selection evidence",
    },
    "I079": {
        "residual": (
            "With pinned Charon/Aeneas on one safe function, relocating identical Rust bytes changed only the LLBC local source path after exact destination/name-map normalization, and generated Lean changed only its source-path comment line. An appended comment after the function changed LLBC embedded file contents while generated Lean stayed byte-identical at the same path; restored A output matched normalized A. "
            "This demonstrates model-text reuse and provenance identity can diverge in that fixture. General LLBC normalization, annotation association under moved/edited code, path-sensitive builds, tool/flag revisions and Anneal cache-key policy remain open."
        ),
        "prerequisite": (
            "Define a provenance-preserving Anneal cache key and source association policy, then exercise multi-file, path-sensitive, moved/declaration edits and tool/flag variants through actual Charon/Aeneas consumers and diagnostics."
        ),
        "assessment": "Four successful source states add field-level path/comment provenance contrasts; only this single-function schema slice is established.",
        "packages": [CHARON],
        "files": evidence(CHARON, "REPORT.md", "REPORT.json", "support/check.py", "support/results.json", "support/artifacts/origin/probe.llbc", "support/artifacts/relocated/probe.llbc", "support/artifacts/comment/probe.llbc", "support/artifacts/repeat/probe.llbc", "support/artifacts/origin/lean/Probe.lean", "support/artifacts/relocated/lean/Probe.lean", "support/artifacts/comment/lean/Probe.lean"),
        "relation": "direct Charon/Aeneas relocation and inert-comment provenance evidence",
    },
    "I148": {
        "residual": (
            "The prior real zerocopy Charon repeat remains error-bearing and cannot support downstream translation. A new error-free one-function Charon/Aeneas A-to-comment-to-A/relocation sequence gives equal generated Lean at the same source path despite an appended comment changing embedded LLBC source bytes; relocation changes only the generated source-path comment after narrow LLBC normalization, and restored A matches. "
            "Only sequential tiny generation was run. Intended V2 flags/split layout, concurrent successful larger corpus, generated-obligation equivalence, Lake/Lean reuse cost and general semantic comparator remain untested."
        ),
        "prerequisite": (
            "Use a larger error-free matched corpus or actual Anneal workload at intended flags and split layout, including concurrent repeats, then compare generated declarations/obligations and measure downstream Lake/Lean cost under provenance-safe keys."
        ),
        "assessment": "A successful small Charon-to-Aeneas control complements the error-bearing real-library repeat without generalizing its determinism.",
        "packages": [CHARON],
        "files": evidence(CHARON, "REPORT.md", "REPORT.json", "support/check.py", "support/results.json", "support/artifacts/origin/probe.llbc", "support/artifacts/comment/probe.llbc", "support/artifacts/repeat/probe.llbc", "support/artifacts/origin/lean/Probe.lean", "support/artifacts/comment/lean/Probe.lean", "support/artifacts/repeat/lean/Probe.lean"),
        "relation": "direct small successful Charon/Aeneas textual-repeatability evidence",
    },
    "I151": {
        "residual": (
            "A matched four-cell Lake experiment now compares shared and isolated writable package/build trees under both reverse killed-writer schedules. When the newer writer is killed, the surviving old writer exits 0 and both topologies produce identical old OLean; no-build rejects the shared tree's changed source (exit 3) but accepts the isolated tree's unchanged source (exit 0). When the older writer is killed, both newer artifacts agree and no-build passes. Fresh Lean proof controls agree with each artifact. "
            "Kills occurred before artifact output, so interruption during OLean/trace/hash writes, repair after partial files, general shared-writer ownership and actual Anneal policy remain open."
        ),
        "prerequisite": (
            "Instrument controlled interruption during shared OLean, trace and hash publication in an owned disposable tree; compare immediate reads, retries and isolation under an implemented Anneal build-tree ownership contract."
        ),
        "assessment": "The matched shared/isolated reverse-kill controls isolate one source-ownership hazard, while artifact-write interruption remains untested.",
        "packages": [LAKE_WRITERS],
        "files": evidence(LAKE_WRITERS, "REPORT.md", "REPORT.json", "support/check.py", "support/results.json", "support/probe.py"),
        "relation": "direct matched Lake shared-versus-isolated writer evidence",
    },
    "C02": {
        "residual": (
            "The direct Lean rich-goal probe compares getInteractiveGoals with plainGoal at 24 matched cursor/version pairs across valid, unsaved syntax-error, unknown-tactic and recovered nested proofs; availability categories agree and all 17 nonempty rendered targets match after presentation-tag removal. "
            "Rich object dereference/expiration, generated proofs, source mapping, exact Anneal version fencing and transport integration remain untested."
        ),
        "prerequisite": (
            "Exercise plain and rich goals on actual Anneal-generated/projected proofs with exact-version fencing, worker/reference lifecycle and fresh batch comparisons."
        ),
        "assessment": "The previously missing rich-versus-plain direct Lean cell is executed; projected/generated and RPC lifecycle scope remains.",
        "packages": [RICH_GOAL],
        "files": evidence(RICH_GOAL, "REPORT.md", "REPORT.json", "support/check.py", "support/results.json", "support/transcript.json"),
        "relation": "direct rich/plain nested unsaved-goal evidence for C02",
    },
    "E06": {
        "residual": (
            "A successful one-function Charon/Aeneas A-to-comment-to-A sequence produced byte-identical generated Lean at the same source path even though the appended inert comment changed LLBC embedded source contents; relocating identical Rust bytes changed only the Lean source-path documentation line, and restored A matched. "
            "This one sequential file does not establish generated-source determinism across intended Anneal split layout, features, concurrent runs, broader source edits or tool revisions; Lake trace and proof effects were not measured."
        ),
        "prerequisite": (
            "Run error-free matched generated-source repeats at Anneal's intended flags and split-file layout, including concurrent and path/feature variants, then measure Lake/Lean reuse and proof interpretation."
        ),
        "assessment": "The relocation/comment fixture adds successful generated-Lean byte comparisons; it is one safe function and one backend invocation mode.",
        "packages": [CHARON],
        "files": evidence(CHARON, "REPORT.md", "REPORT.json", "support/check.py", "support/results.json", "support/artifacts/origin/lean/Probe.lean", "support/artifacts/relocated/lean/Probe.lean", "support/artifacts/comment/lean/Probe.lean", "support/artifacts/repeat/lean/Probe.lean"),
        "relation": "direct small successful generated-source repeat evidence for E06",
    },
    "E07": {
        "residual": (
            "The prior error-bearing real-library short_names ordering result remains a field-specific importer control. A separate error-free safe-function sequence now has different LLBC embedded source bytes after an inert trailing comment but byte-identical generated Lean at the same path; relocation changes only a generated source-path comment. "
            "No Lean theorem, obligation identity or semantic-equivalence oracle was run. Broader moves/signatures, path-sensitive inputs, cross-tool mutants and an authenticated Anneal comparator remain open."
        ),
        "prerequisite": (
            "Compare generated obligations and Lean interpretations for a larger error-free corpus and controlled textual mutants under provenance-preserving Anneal identities, then define an authenticated semantic comparator."
        ),
        "assessment": "Successful generated-text equality adds one stronger textual-instability control, without establishing semantic sameness of obligations.",
        "packages": [CHARON],
        "files": evidence(CHARON, "REPORT.md", "REPORT.json", "support/check.py", "support/results.json", "support/artifacts/origin/probe.llbc", "support/artifacts/comment/probe.llbc", "support/artifacts/origin/lean/Probe.lean", "support/artifacts/comment/lean/Probe.lean"),
        "relation": "direct small generated-text equality evidence for E07",
    },
    "F12": {
        "residual": (
            "A new matched shared-versus-isolated Lake writer study runs both reverse killed-writer schedules. If the newer writer is killed, an older successful build leaves a 7 artifact in both topologies, but no-build rejects the changed shared source and accepts the unchanged isolated source; if the older writer is killed, both newer 9 artifacts pass. Fresh Lean controls confirm the selected definitions. "
            "The kill gates were before artifact output. Shared OLean/trace/hash syscall interruption, partial-file recovery, actual Anneal preparation lock graph and general ownership policy remain untested."
        ),
        "prerequisite": (
            "Test controlled interruption during shared build-tree artifact and trace publication, then validate recovery and ownership under Anneal's actual preparation/cache lock protocol."
        ),
        "assessment": "The missing matched topology control now isolates shared source ownership, but not artifact-write crash consistency.",
        "packages": [LAKE_WRITERS],
        "files": evidence(LAKE_WRITERS, "REPORT.md", "REPORT.json", "support/check.py", "support/results.json"),
        "relation": "direct matched shared-writer crash-schedule evidence for F12",
    },
}

# I046 was already complete at its explicitly narrow direct-Lean scope in v26.
# This corroborates that scope without manufacturing a new residual or status.
EVIDENCE_ONLY = {
    "I046": {
        "assessment": "The 24 matched plain/rich queries corroborate useful local goal state before and after syntax and tactic failures while fresh batch rejects both erroneous whole files; the narrow v26 completion remains unchanged.",
        "packages": [RICH_GOAL],
        "files": evidence(RICH_GOAL, "REPORT.md", "REPORT.json", "support/check.py", "support/results.json", "support/transcript.json"),
        "relation": "direct corroborating rich/plain failed-elaboration evidence; no status or residual change",
    },
}

CONTEXT_ONLY = {
    "B02": "The compiler-backed bridge round-trips its own exact copied interval, not the actual Anneal annotation grammar or incremental source map.",
    "B03": "The bridge includes UTF-16 and supplementary-character controls but no negotiated real editor client through Anneal projection.",
    "K01": "The bridge records an illustrative source interval, not an authenticated producer-owned pre-compiler proof-range sidecar.",
    "I009": "Relocation/comment was one rustc file, not the Cargo/config/model/toolchain input closure requested by this row.",
    "I074": "The path move omitted Cargo workspace, path dependencies, build scripts, proc macros and generated files needed to assess shadow fidelity.",
    "I044": "The rich-goal probe did not dereference or release opaque RPC references, or test expiry and worker restarts.",
    "I108": "The Lake fixture killed writers before artifact output and did not construct the preparation/cache/GC lock graph.",
    "I080": "The tiny Lake writer RSS observations are not Rust-side Cargo target economics or cancellation cleanup.",
    "I113": "The tiny Lake writer artifacts do not add to the full-chain per-consumer byte/write accounting gate.",
    "J01": "The two-writer Lake fixture retained only small OLean/trace specimens, not whole-tree byte measurements or representative generated-project scaling.",
    "J02": "The Lake fixture did not trace every copied or written byte across the full chain.",
    "A02": "The path/comment contrast is a single Charon/Aeneas component, not cross-layer Anneal locator-to-generation policy.",
    "A08": "A-to-comment-to-A is a bounded content-revert example, not an Anneal revision-versus-hash consumer contract.",
    "D05": "The Charon relocation/comment sequence was serial and did not test concurrent deterministic extraction.",
    "D07": "The source-path contrast did not vary compilation-subject selection or collision-safe output publication.",
    "D06": "The Lake interruption is a build-tree writer result, not Charon cancellation cleanup.",
}


def verify_live(live):
    frozen = json.loads((V22 / "issue-scope-snapshot.json").read_text())
    prior = json.loads((V26 / "live-issue-snapshot-v26.json").read_text())["issues"]
    for number, state in ((3730, "closed"), (3731, "open")):
        key = str(number)
        item = live["issues"][key]
        assert item["number"] == number and item["state"] == state
        assert item["body"] == frozen[key]["body"] == prior[key]["body"]
        assert item["body_sha256"] == hashlib.sha256(item["body"].encode()).hexdigest() == prior[key]["body_sha256"]
        assert len(item["comments"]) == len(prior[key]["comments"]) == 1
        comment = item["comments"][0]
        assert comment["id"] == prior[key]["comments"][0]["id"]
        assert comment["body"] == frozen[key]["comments"][0]["body"] == prior[key]["comments"][0]["body"]
        assert comment["body_sha256"] == hashlib.sha256(comment["body"].encode()).hexdigest() == prior[key]["comments"][0]["body_sha256"]


def main():
    prior = json.loads((V26 / "row-challenge-v26.json").read_text())
    live = json.loads((HERE / "live-issue-snapshot-v27.json").read_text())
    verify_live(live)
    assert len(prior) == 333 and len({row["id"] for row in prior}) == 333
    assert set(UPDATES) == {"I025", "I043", "I079", "I148", "I151", "C02", "E06", "E07", "F12"}
    assert set(EVIDENCE_ONLY) == {"I046"}
    assert not ((set(UPDATES) | set(EVIDENCE_ONLY)) & set(CONTEXT_ONLY))

    out = []
    for before in prior:
        row = dict(before)
        item = row["id"]
        update = UPDATES.get(item) or EVIDENCE_ONLY.get(item)
        if update:
            assessment = update["assessment"]
        elif item in CONTEXT_ONLY:
            assessment = CONTEXT_ONLY[item] + " The v26 residual and prerequisite remain."
        else:
            gate = ";".join(row["v26_gate_categories"]) or "already resolved or conditional"
            assessment = f"None of the four new reports directly exercises {item} ({row['title']}) at its remaining {gate} gate; the v26 residual and prerequisite remain."
        row.update({
            "v27_status": row["v26_status"],
            "v27_gate_categories": row["v26_gate_categories"],
            "v27_specific_remaining_delta": update.get("residual", row["v26_specific_remaining_delta"]) if update else row["v26_specific_remaining_delta"],
            "v27_scope_assessment": assessment,
            "v27_review_package": HERE.parent.name if update else row["v26_review_package"],
            "v27_new_evidence_packages": update["packages"] if update else [],
            "v27_evidence_files": update["files"] if update else [],
            "v27_next_prerequisite": update.get("prerequisite", row["v26_next_prerequisite"]) if update else row["v26_next_prerequisite"],
            "v27_evidence_relation": update["relation"] if update else "bounded context only" if item in CONTEXT_ONLY else "no direct v27 evidence",
        })
        assert row["v27_specific_remaining_delta"] and row["v27_next_prerequisite"] and row["v27_scope_assessment"]
        out.append(row)
    assert {row["id"] for row in out if row["v27_specific_remaining_delta"] != row["v26_specific_remaining_delta"]} == set(UPDATES)
    assert not any(row["v27_status"] != row["v26_status"] for row in out)
    (HERE / "row-challenge-v27.json").write_text(json.dumps(out, indent=2, sort_keys=True, ensure_ascii=False) + "\n")

    by_id = {row["id"]: row for row in out}
    fields = ("v27_status", "v27_gate_categories", "v27_specific_remaining_delta", "v27_scope_assessment", "v27_review_package", "v27_new_evidence_packages", "v27_evidence_files", "v27_next_prerequisite", "v27_evidence_relation")
    def extend(name, key):
        rows = []
        for before in csv_rows(V26 / name):
            row = dict(before)
            choice = by_id[row[key]]
            assert row["status"] == choice["v27_status"]
            for field in fields:
                value = choice[field]
                row[field] = ";".join(value) if isinstance(value, list) else value
            rows.append(row)
        return rows
    investigations = extend("investigation-final-v26.csv", "id")
    suggestions = extend("3730-crosswalk-final-v26.csv", "3730_id")
    assert len(investigations) == 159 and len(suggestions) == 174
    write_csv(HERE / "investigation-final-v27.csv", investigations)
    write_csv(HERE / "3730-crosswalk-final-v27.csv", suggestions)

    issue_body = live["issues"]["3731"]["body"]
    issue_comment = live["issues"]["3731"]["comments"][0]["body"]
    titles = {item: re.sub(r"\s*\[[^]]+\]\.?$", "", title).strip()
              for source in (issue_body, issue_comment)
              for item, title in re.findall(r"(?m)^\*\*(I\d{3})\s+[—.]\s+([^\n]*?)\*\*", source)}
    cross = {item: (title.strip(), set(re.findall(r"I\d{3}", destinations)))
             for item, title, destinations in re.findall(r"(?m)^\| ([A-O]\d{2}) \| ([^|]+) \| ([^|]+) \|", issue_comment)}
    assert len(titles) == 159 and len(cross) == 174
    assert all(row["title"] == titles[row["id"]] for row in investigations)
    assert all(row["suggestion"] == cross[row["3730_id"]][0] and set(row["3731_destinations"].split(";")) == cross[row["3730_id"]][1] for row in suggestions)
    links = sum(len(destinations) for _, destinations in cross.values())
    assert links == 345

    inventory = []
    for package in SOURCE_PACKAGES:
        for path in sorted((REPORTS / package).rglob("*")):
            if path.is_file() and "__pycache__" not in path.parts and path.suffix != ".pyc":
                inventory.append({"path": path.relative_to(ROOT).as_posix(), "sha256": sha(path)})
    write_csv(HERE / "source-package-inventory-v27.csv", inventory)

    generated = ("row-challenge-v27.json", "investigation-final-v27.csv", "3730-crosswalk-final-v27.csv", "source-package-inventory-v27.csv")
    inputs = {"v26/row-challenge-v26.json": V26 / "row-challenge-v26.json",
              "v26/investigation-final-v26.csv": V26 / "investigation-final-v26.csv",
              "v26/3730-crosswalk-final-v26.csv": V26 / "3730-crosswalk-final-v26.csv",
              "v22/issue-scope-snapshot.json": V22 / "issue-scope-snapshot.json",
              "live-issue-snapshot-v27.json": HERE / "live-issue-snapshot-v27.json"}
    validation = {
        "reference_tip_at_start": "087760fd8bccaa8852390f189d8daf01f0958b19",
        "source_reference_package": V26_NAME,
        "source_anneal_revision": "bd0956be95c5f798f0c0484921b9b9d1fc6e9988",
        "row_count": len(out), "investigation_count": len(investigations), "suggestion_count": len(suggestions),
        "suggestion_destination_links": links,
        "status_counts": {"investigations": dict(Counter(row["status"] for row in investigations)), "suggestions": dict(Counter(row["status"] for row in suggestions))},
        "changed_status_ids": [], "changed_gate_ids": [],
        "changed_residual_ids": sorted(UPDATES), "changed_prerequisite_ids": sorted(UPDATES),
        "direct_evidence_ids": sorted(set(UPDATES) | set(EVIDENCE_ONLY)),
        "evidence_only_ids": sorted(EVIDENCE_ONLY), "bounded_context_ids": sorted(CONTEXT_ONLY),
        "source_packages": list(SOURCE_PACKAGES), "inventory_files": len(inventory),
        "input_sha256": {key: sha(path) for key, path in inputs.items()},
        "generated_sha256": {key: sha(HERE / key) for key in generated},
    }
    (HERE / "validation-v27.json").write_text(json.dumps(validation, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: validation[key] for key in ("row_count", "suggestion_destination_links", "changed_residual_ids", "inventory_files", "status_counts")}, sort_keys=True))


if __name__ == "__main__":
    main()
