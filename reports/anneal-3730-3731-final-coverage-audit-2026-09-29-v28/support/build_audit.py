#!/usr/bin/env python3
"""Derive the append-only v28 ledger from v27 and four final source reports."""
import csv
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V27_NAME = "anneal-3730-3731-final-coverage-audit-2026-09-29-v27"
V27 = REPORTS / V27_NAME / "support"
V22 = REPORTS / "anneal-3730-3731-final-coverage-audit-2026-09-29-v22" / "support"
DIRECT = "lean-unsaved-cross-module-import-v4-30-0-rc2"
LAKE = "lean-lake-unsaved-cross-module-import-v4-30-0-rc2"
RACE = "lean-lsp-cross-version-goal-completion-v4-30-0-rc2"
CACHE = "anneal-3731-lake-fresh-cache-consumer-matrix-2026-09-29"
PATH_LOSS = "lean-lsp-open-buffer-path-disappearance-v4-30-0-rc2"
SOURCE_PACKAGES = (V27_NAME, DIRECT, LAKE, RACE, CACHE, PATH_LOSS)

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

def files(*packages):
    out = []
    for package in packages:
        names = ["REPORT.md", "REPORT.json", "support/check.py"]
        if package in (RACE, PATH_LOSS):
            names += ["support/transcript-run1.json", "support/transcript-run2.json", "support/transcript-run3.json", "support/work/V1.lean", "support/work/V2.lean"]
            if package == PATH_LOSS:
                names = ["REPORT.md", "REPORT.json", "support/check.py", "support/probe.py", "support/transcript-run1.json", "support/transcript-run2.json", "support/transcript-run3.json"]
                names += [p.relative_to(REPORTS / package).as_posix() for p in sorted((REPORTS / package / "support/work").glob("*.lean"))]
        elif package == CACHE:
            names += ["support/results.json", "support/probe.py"]
        else:
            names += ["support/transcript.json", "support/probe.py"]
        out += [f"reports/{package}/{name}" for name in names]
    assert all((ROOT / name).is_file() for name in out)
    return out

# Direct means a measured component slice of the named row, not full product completion.
# All eleven rows retain their inherited partial status and original gate categories.
UPDATES = {
    "I012": (PATH_LOSS,
        "Three pinned direct Lean server runs keep an unsaved B goal queryable after external disk overwrite C, an explicit save of B, and rename of the original open URI; an open renamed URI remains queryable after its disk path is deleted. Closing either URI makes queries fail with -32801, and recreating C then reopening returns C's goal. The harness itself writes B before didSave, sends watched-file events and supplies C on reopen. Real editor conflict handling, watcher delivery, Anneal buffer/disk authority and generated/imported proof behavior remain untested.",
        "Implement and test an Anneal editor-host buffer/disk authority contract across dirty save, external overwrite, rename, deletion and reopen, including conflict handling and generated/imported proofs.",
        "Three complete path-disappearance transcripts directly narrow Lean open-buffer ownership, while product conflict handling remains unexecuted."),
    "I038": (DIRECT, LAKE,
        "Two pinned Lean 4.30.0-rc2 server modes now distinguish an unsaved open producer from its compiled import. In direct lean --server and lake serve, a resident and newly opened consumer still prove sharedValue = 3 while the producer buffer says 4 and its OLean says 3. Rebuilding the producer changes fresh/reopened consumers to a remaining goal and fresh batch failure; the resident consumer remains stale. The direct-server open-buffer-only producer cannot be imported. Anneal's supported live-proof import/materialization contract, generated proof graph, fanout, refresh policy and production adapter remain untested.",
        "Implement an Anneal two-open-proof import and materialization policy; compare saved, unsaved, rebuilt, fresh/reopened and resident consumers across supported launch modes, including generated proofs and explicit dependency refresh.",
        "Two matched launch-mode executions directly narrow the unsaved cross-module import question; they do not implement Anneal semantics."),
    "I041": (RACE,
        "Three direct Lean server runs show version 2 tactic execution, waitForDiagnostics(version=2) completion and its False goal reply before older version-1 wait and True goal replies arrive. A later waitForDiagnostics(version=1) also succeeds; an extra textDocument.version on plainGoal did not pin that query. Client-visible arrival order and successful waits cannot justify a latest-version attribution. Internal computation time of the old reply, a production Anneal source/import envelope, version fence, cancellation and broader schedules remain untested.",
        "Implement and exercise an Anneal request envelope binding process incarnation, URI, version, source hash, position and import generation; reject or explicitly archive late replies after actual concurrent edits and worker replacement.",
        "Three causal-barrier transcripts sharpen the exact-version hazard, without proving a product fence."),
    "I089": (CACHE,
        "A tiny fresh Lake consumer with empty local build state fetched Dep and Generated from a seeded artifact cache under --no-build; selected OLean/ILEAN/C bytes, batch axiom/value output and first goal matched an independent clean build. Removing Dep.lean made no-build preparation fail while direct batch accepted retained OLean and a fresh server returned no goal. The actual content-identified Anneal omnibus archive, complete manifest, enforced read-only dependency, first-goal write trace and production generated consumer remain absent.",
        "Supply the real built Anneal prepared archive and matching generated consumer; repeat the frozen-manifest, empty-home/cache, read-only first-goal probe with complete producer and write tracing.",
        "A genuinely fresh tiny consumer and missing-source contrast execute a component of the archive question; the required real archive is still absent."),
    "I092": (CACHE,
        "In a pinned two-package Lake fixture, a new consumer with a seeded cache passes --no-build, reconstructing missing traces or compiled config and replaying missing hash sidecars; removing Dep.lean fails no-build even while direct batch imports the retained OLean. Removing one setup JSON did not force recreation in this selected path. These are net producer/cache inventories, not syscall traces; malformed manifests, native/plugin families, actual Anneal archive, exact server no-build launcher and full read-only policy remain untested.",
        "Exercise missing/stale imports, malformed manifests, setup/config/trace/hash/native/plugin families and all writes under the actual Anneal server no-build/no-cache consumer path with enforced read-only producer state.",
        "Fresh-consumer ablations directly distinguish selected no-build prerequisites and local replay; the full consumer contract remains open."),
    "I099": (CACHE,
        "Independent clean and freshly cache-fetched tiny Lake builds agree on Dep OLean/ILEAN/C hashes, one theorem's axiom result, evaluated value 8 and a live first goal. A missing-source cell shows direct batch acceptance can coexist with a failed Lake preparation and null live goal. This is one dependency and theorem; actual same-platform Anneal archive, representative generated graph, declarations, navigation, plugins, obligation provenance and source-level verification remain untested.",
        "Compare actual prepared Anneal generated projects with independently clean reconstructed builds across declarations, assumptions, relevant artifacts, navigation, tactic state and source-level verification, keeping each oracle distinct.",
        "A paired tiny clean/cache execution narrows the equivalence dimensions but cannot substitute for the actual generated project."),
    "C09": (RACE,
        "Three direct Lean runs overlap old and new goal requests for one URI. The version-2 wait and False goal complete before version-1 wait and True goal replies arrive; a later old-version wait also succeeds. These are client-visible causal barriers, not internal computation timestamps. An Anneal request/worker fence, current-result classification, cancellation and generated-import concurrency remain unimplemented.",
        "Run the same overlapping goal schedule through an Anneal version and worker-incarnation envelope, then test cancellation, restart and generated-import races against a current-version oracle.",
        "The new three-run overlap is direct single-document concurrent-query evidence, not a product wrapper."),
    "C11": (DIRECT, LAKE,
        "Both direct Lean and lake serve two-open-document fixtures import the old compiled producer, not its unsaved edited buffer; fresh consumers stay at the old proof until source write and OLean rebuild, after which new/reopened consumers expose a goal while resident consumers stay old. The direct-server open-buffer-only module is unresolved. Anneal live proof import semantics, graph cycles, generated declaration order and refresh protocol remain undefined.",
        "Implement Anneal live-proof import/materialization and dependency-refresh policy; test generated proof consumers through unsaved edits, rebuild, close/reopen, fanout and cycles.",
        "Two launch modes directly exercise the live producer/consumer contrast; the Anneal contract remains open."),
    "F07": (CACHE,
        "A selected no-build Lake consumer fails on missing producer source even with retained OLean, while fresh cache fetch succeeds with empty local build state and missing traces/config/hash sidecars take distinct fetch/replay paths. Hash inventories reveal local metadata writes after successful no-build reads. This tiny fixture does not cover malformed manifests, plugins/native outputs, actual Anneal archive, or syscall-level read-only fail-closed behavior.",
        "Run the exact Anneal no-build/no-cache server path over actual prepared archive with malformed/missing/stale manifest, source, OLean, traces, hash, setup and native/plugin controls under enforced read-only dependencies.",
        "A direct missing-source failure and metadata-replay matrix narrows fail-closed behavior in a tiny Lake component."),
    "F08": (CACHE,
        "In a fresh Lake consumer with producer source removed, direct batch Lean imports retained OLean and accepts the theorem, but no-build Lake preparation fails and a new Lake server returns a null first goal with missing-source diagnostics after a successful diagnostics wait. Thus batch artifact acceptance and wait completion do not imply this fixture's interactive readiness. Causal Anneal parse/import/elaboration/async status, actual archive and current-position readiness remain untested.",
        "Build the Anneal readiness protocol and repeat matched batch, Lake preparation, diagnostics wait and first-goal controls on the real prepared archive and generated consumer.",
        "The missing-source cell is a direct batch-versus-live readiness counterexample, with no production readiness state machine."),
    "F19": (CACHE,
        "An independently clean tiny Lake build and a new cache-fetched consumer match selected Dep OLean/ILEAN/C hashes, theorem axiom output and first goal. The missing-source cell further separates direct batch success from server goal availability. This does not construct an independent clean oracle for actual Anneal generated proofs, loaded imports, navigation, all declarations or source-level obligations.",
        "Build an independently reconstructed clean consumer for the actual prepared Anneal interface/archive and compare assumptions, declarations, diagnostics, goals, navigation and artifacts against the prepared path.",
        "A bounded clean-versus-cache oracle runs for one theorem and first goal; production generated scope remains."),
    "I04": (CACHE,
        "A freshly created Lake consumer with missing producer source has a direct batch command that accepts retained OLean and the theorem, yet Lake no-build preparation fails and a fresh server returns null for the first goal with missing-source diagnostics. A complete-source fresh cache consumer gives a first goal matching an independent clean build. These are tiny fixture contrasts; no actual Anneal archive, generated proof or batch-accepted product subject was consumed cold.",
        "After batch acceptance of a content-identified actual Anneal prepared archive, launch a genuinely cold generated interactive consumer and compare first goal, imports, diagnostics and write behavior with an independent clean oracle.",
        "The tiny missing-source and full-source cells directly test batch-to-cold-interactive divergence, not an actual Anneal archive."),
}

CONTEXT = {
    "B15": "The path-disappearance probe used a harness-controlled Lean buffer and physical file writes, not an Anneal editor host deciding proof authority or save conflicts.",
    "C01": "The late-reply transcripts motivate a version-bound wrapper but neither implement a wrapper nor attest loaded import identity.",
    "I042": "The missing-source null goal adds a readiness failure control, but no causal Anneal parse/import/elaboration/async status protocol was exercised.",
    "I045": "The goal overlap uses one server process and no worker-incarnation replacement or request-ID reuse.",
    "I039": "The two-module import probes did not construct a dependency cycle or generated declaration order.",
    "I091": "The Lake cache matrix uses saved source and does not attest unsaved current-document imports or setup.",
    "I131": "The independent clean control is on the same pinned host and trusts prebuilt toolchain components; it is not an independent operator/host oracle.",
    "I132": "The one-theorem equality checks do not calibrate a general semantic/diagnostic comparator.",
    "I134": "The direct Lean goal race is not a parallel Anneal publisher, reader or generated-model race.",
    "F02": "The cache consumer is a tiny fixture with writable producer copies, not the real read-only Anneal archive/server probe.",
    "F04": "The missing-source control removes one file from a tiny producer; no real archive manifest was available or removed.",
    "F13": "Fresh consumers ran sequentially with writable copied producers; no read-only producer with many concurrent consumers was tested.",
    "F20": "A tiny generated module was fetched, but actual generated-module rebuild isolation and whole-chain byte accounting were not measured.",
    "I02": "Selected artifacts and batch/live outputs were compared without worker-reported actual loaded import identity.",
}

def verify_live(live):
    frozen = json.loads((V22 / "issue-scope-snapshot.json").read_text())
    prior = json.loads((V27 / "live-issue-snapshot-v27.json").read_text())["issues"]
    for number, state in ((3730, "closed"), (3731, "open")):
        key = str(number)
        item = live["issues"][key]
        assert item["number"] == number and item["state"] == state
        assert item["body"] == frozen[key]["body"] == prior[key]["body"]
        assert item["body_sha256"] == sha_text(item["body"]) == prior[key]["body_sha256"]
        assert len(item["comments"]) == len(prior[key]["comments"]) == 1
        for comment, old, orig in zip(item["comments"], prior[key]["comments"], frozen[key]["comments"]):
            assert comment["id"] == old["id"] and comment["body"] == old["body"] == orig["body"]
            assert comment["body_sha256"] == sha_text(comment["body"]) == old["body_sha256"]

def sha_text(text):
    return hashlib.sha256(text.encode()).hexdigest()

def main():
    prior = json.loads((V27 / "row-challenge-v27.json").read_text())
    live = json.loads((HERE / "live-issue-snapshot-v28.json").read_text())
    verify_live(live)
    assert len(prior) == 333 and len({row["id"] for row in prior}) == 333
    assert len(UPDATES) == 12 and not set(UPDATES) & set(CONTEXT)
    out = []
    for before in prior:
        row = dict(before)
        item = row["id"]
        if item in UPDATES:
            *packages, residual, prerequisite, assessment = UPDATES[item]
            assert row["v27_status"] == "partial"
            evidence = files(*packages)
            relation = "direct bounded component evidence"
        elif item in CONTEXT:
            packages, evidence, residual, prerequisite = [], [], row["v27_specific_remaining_delta"], row["v27_next_prerequisite"]
            assessment = CONTEXT[item] + " The v27 residual and prerequisite remain."
            relation = "bounded context only"
        else:
            packages, evidence, residual, prerequisite = [], [], row["v27_specific_remaining_delta"], row["v27_next_prerequisite"]
            gate = ";".join(row["v27_gate_categories"]) or "already resolved or conditional"
            assessment = f"None of the four new reports directly exercises {item} ({row['title']}) at its remaining {gate} gate; the v27 residual and prerequisite remain."
            relation = "no direct v28 evidence"
        row.update({
            "v28_status": row["v27_status"],
            "v28_gate_categories": row["v27_gate_categories"],
            "v28_specific_remaining_delta": residual,
            "v28_scope_assessment": assessment,
            "v28_review_package": HERE.parent.name if item in UPDATES else row["v27_review_package"],
            "v28_new_evidence_packages": packages,
            "v28_evidence_files": evidence,
            "v28_next_prerequisite": prerequisite,
            "v28_evidence_relation": relation,
        })
        out.append(row)
    changed = {row["id"] for row in out if row["v28_specific_remaining_delta"] != row["v27_specific_remaining_delta"]}
    assert changed == set(UPDATES)
    assert all(row["v28_status"] == row["v27_status"] and row["v28_gate_categories"] == row["v27_gate_categories"] for row in out)
    (HERE / "row-challenge-v28.json").write_text(json.dumps(out, indent=2, sort_keys=True, ensure_ascii=False) + "\n")

    by_id = {row["id"]: row for row in out}
    fields = ("v28_status", "v28_gate_categories", "v28_specific_remaining_delta", "v28_scope_assessment", "v28_review_package", "v28_new_evidence_packages", "v28_evidence_files", "v28_next_prerequisite", "v28_evidence_relation")
    def extend(name, key):
        rows = []
        for before in csv_rows(V27 / name):
            row = dict(before)
            choice = by_id[row[key]]
            for field in fields:
                value = choice[field]
                row[field] = ";".join(value) if isinstance(value, list) else value
            rows.append(row)
        return rows
    investigations = extend("investigation-final-v27.csv", "id")
    suggestions = extend("3730-crosswalk-final-v27.csv", "3730_id")
    assert len(investigations) == 159 and len(suggestions) == 174
    write_csv(HERE / "investigation-final-v28.csv", investigations)
    write_csv(HERE / "3730-crosswalk-final-v28.csv", suggestions)

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
    write_csv(HERE / "source-package-inventory-v28.csv", inventory)

    generated = ("row-challenge-v28.json", "investigation-final-v28.csv", "3730-crosswalk-final-v28.csv", "source-package-inventory-v28.csv")
    inputs = {"v27/row-challenge-v27.json": V27 / "row-challenge-v27.json",
              "v27/investigation-final-v27.csv": V27 / "investigation-final-v27.csv",
              "v27/3730-crosswalk-final-v27.csv": V27 / "3730-crosswalk-final-v27.csv",
              "v22/issue-scope-snapshot.json": V22 / "issue-scope-snapshot.json",
              "live-issue-snapshot-v28.json": HERE / "live-issue-snapshot-v28.json"}
    validation = {
        "reference_tip_at_start": "1b67b6b87b3266f1f798cd825de9988e297b5822",
        "source_reference_package": V27_NAME,
        "source_anneal_revision": "bd0956be95c5f798f0c0484921b9b9d1fc6e9988",
        "row_count": len(out), "investigation_count": len(investigations), "suggestion_count": len(suggestions),
        "suggestion_destination_links": links,
        "status_counts": {"investigations": dict(Counter(row["status"] for row in investigations)), "suggestions": dict(Counter(row["status"] for row in suggestions))},
        "changed_status_ids": [], "changed_gate_ids": [],
        "changed_residual_ids": sorted(UPDATES), "changed_prerequisite_ids": sorted(UPDATES),
        "direct_evidence_ids": sorted(UPDATES), "bounded_context_ids": sorted(CONTEXT),
        "source_packages": list(SOURCE_PACKAGES), "inventory_files": len(inventory),
        "input_sha256": {key: sha(path) for key, path in inputs.items()},
        "generated_sha256": {key: sha(HERE / key) for key in generated},
    }
    (HERE / "validation-v28.json").write_text(json.dumps(validation, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: validation[key] for key in ("row_count", "suggestion_destination_links", "changed_residual_ids", "inventory_files", "status_counts")}, sort_keys=True))

if __name__ == "__main__":
    main()
