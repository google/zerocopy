#!/usr/bin/env python3
"""Deterministically derive v24 from v23 and three post-publication audits.

Writes only files beside this script. Never fetches or alters source packages.
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
V23 = REPORTS / "anneal-3730-3731-final-coverage-audit-2026-09-29-v23/support"
V22 = REPORTS / "anneal-3730-3731-final-coverage-audit-2026-09-29-v22/support"
R1 = "anneal-3731-i001-i053-postpublication-residual-review-2026-09-29"
R2 = "anneal-3731-i054-i106-postpublication-residual-audit-2026-09-29"
R3 = "anneal-3731-i107-i159-postpublication-residual-audit-2026-09-29"
PACKAGES = (R1, R2, R3)
ACTUAL_NEW_CELL = {"I005", "I076", "I126"}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_csv(path):
    with path.open(newline="") as f:
        return list(csv.DictReader(f))


def write_csv(path, rows):
    with path.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]), lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)


def audit_for(item):
    number = int(item[1:])
    return R1 if number <= 53 else R2 if number <= 106 else R3


def evidence(package, extra=()):
    paths = [f"reports/{package}/REPORT.md", f"reports/{package}/REPORT.json",
             f"reports/{package}/support/check.py"]
    paths.extend(f"reports/{package}/{item}" for item in extra)
    assert all((ROOT / item).is_file() for item in paths)
    return paths


INV_DELTA = {
    "I005": "A matched fake-backend snapshot/scheduler replay now covers four proof/source/model/import changes and 48 valid edit/cancellation/completion schedules. Both models with a current-request publication fence select B; the unfenced control selects stale A in 12 schedules. Two shared-reader cancellation orders preserve the survivor only with per-subscriber ownership. Actual Anneal dependency discovery, real stage costs, and a production generation engine remain untested.",
    "I076": "Two offline sibling Cargo libraries share serialized Charon crate/function names but produce distinct LLBC bodies (11 versus 29); the earlier lib/bin/test control also found a wrong final unit. A complete Cargo compilation-unit key, host/target/feature matrix, concurrent output arbitration, and collision-rejecting Anneal publication remain untested.",
    "I126": "Pinned Lake configuration run_cmd wrote an owned outside-workspace marker when permitted; a targeted macOS sandbox denial blocked that write and static configuration still built. Prior Cargo build-script, proc-macro, and Lean run_cmd controls remain. Native-extension execution, comprehensive containment and resource limits, inspection-before-execution, and Anneal trust-entry authorization remain untested.",
    "I127": "The new Lake denial diagnostic included an absolute owned marker path; the retained transcript normalizes that scratch root. This is one path-exposure control, not representative private-source, credential, environment, generated-file, or product-log leakage testing.",
    "I145": "The existing seven-file manifest and entry-OLean ablation cover selected identities. The new I076 sibling-Cargo fixture demonstrates that serialized crate/function names alone conflate distinct compilation subjects. Complete Cargo→Charon→Aeneas→Lake→Lean→MCP identity ablation, causality/content distinction, and product freshness routing remain untested.",
}
INV_NEXT = {
    "I005": "Implement the Anneal generation engine and dependency graph, then compare snapshot and versioned scheduling under matched real edits, cancellations, dependency changes, and stage costs.",
    "I076": "Implement Anneal's compilation-unit identity and produced-output ownership; run same-name sibling libraries, feature/host/target variants, and concurrent collision controls through it.",
    "I126": "Define Anneal's trust-entry authorization and run representative Cargo/Lake/Lean/native execution through enforced containment and resource limits, with inspection-before-execution controls.",
    "I127": "Run the real Anneal evidence pipeline on an authorized private fixture; compare local full and shareable minimized diagnostics, transcripts, paths, environment, and generated files.",
    "I145": "Implement the full cross-layer Anneal identity tuple and response envelope, then ablate each dimension under controlled A→B→A and same-locator/different-payload histories.",
}
INV_ASSESS = {
    "I005": "Post-publication I001–I053 review fills the previously missing identical fake-backend two-model comparison; it does not select a production architecture.",
    "I076": "Post-publication I054–I106 audit adds two actual Charon LLBCs with equal serialized names and different bodies; name-only selection is insufficient.",
    "I126": "Post-publication I107–I159 audit adds actual Lake configuration execution and a targeted sandbox denial; this is one trust-boundary cell.",
    "I127": "The I126 sandbox-denial stream also supplies one owned absolute-path diagnostic; product evidence hygiene remains open.",
    "I145": "The I076 same-name sibling witness is a cross-slice identity counterexample, not the requested full tuple ablation.",
}

SUGGESTION_DIRECT = {"D07": R2, "G09": R3}
I145_DESTINATIONS = {"A01", "A02", "A08", "C01", "F05", "G01", "G02", "G12", "L01", "O03"}
SUGGESTION_DIRECT.update({item: R2 for item in I145_DESTINATIONS})
SUGGESTION_DELTA = {
    "D07": "The new I076 sibling libraries produce different LLBC bodies behind equal serialized crate/function names, supplementing the wrong-final-unit control. Complete compilation-unit identity, invalidation, and collision rejection through Anneal remain open.",
    "G09": "The new I126 Lake configuration control wrote outside its workspace when allowed, and targeted sandbox denial blocked that write while static configuration built. Anneal MCP access tiers, user trust authorization, broad containment/resource limits, and generated-to-authored edit authority remain open.",
}
SUGGESTION_NEXT = {
    "D07": "Implement Anneal compilation-unit keys, output ownership, and dependency invalidation; exercise same-named sibling libraries, feature/host/target units, and concurrent producers.",
    "G09": "Implement actual Anneal MCP read/mutate tiers and untrusted-workspace authorization; enforce and test Cargo/Lake/Lean/native execution containment and resource limits.",
}


def main():
    old = json.loads((V23 / "row-challenge-v23.json").read_text())
    assert len(old) == 333 and len({row["id"] for row in old}) == 333
    early = {row["id"]: row for row in read_csv(REPORTS / R1 / "support/row-review.csv")}
    mid = {row["id"]: row for row in read_csv(REPORTS / R2 / "support/row-decisions.csv")}
    late = {row["id"]: row for row in read_csv(REPORTS / R3 / "support/row-decisions.csv")}
    assert [len(early), len(mid), len(late)] == [53, 53, 53]
    requested = {row["id"]: row["requested_scope"] for row in read_csv(V23 / "investigation-final-v23.csv")}
    for item, row in early.items():
        assert row["postpublication_status"] == next(x for x in old if x["id"] == item)["v23_status"]
    for source in (mid, late):
        for item, row in source.items():
            assert row["post_status"] == next(x for x in old if x["id"] == item)["v23_status"]

    live = json.loads((HERE / "live-issue-hashes.json").read_text())
    frozen = json.loads((V22 / "issue-scope-snapshot.json").read_text())
    original_manifest = json.loads((REPORTS / "anneal-3730-3731-coverage-audit-2026-09-29/support/source-snapshot/manifest.json").read_text())["files"]
    for number in (3730, 3731):
        item = live["issues"][str(number)]
        assert item["body_sha256"] == original_manifest[f"issue{number}.txt"]["sha256"]
        assert len(item["comments"]) == 1
        assert item["comments"][0]["body_sha256"] == original_manifest[f"comment{number}.txt"]["sha256"]
        assert hashlib.sha256(frozen[str(number)]["body"].encode()).hexdigest() == item["body_sha256"]
        assert hashlib.sha256(frozen[str(number)]["comments"][0]["body"].encode()).hexdigest() == item["comments"][0]["body_sha256"]

    out = []
    for previous in old:
        row = dict(previous)
        item = row["id"]
        status = row["v23_status"]
        assert status in ("complete", "partial", "not-run", "conditional")
        delta = row["v23_specific_remaining_delta"]
        next_step = row["v23_next_prerequisite"]
        gates = list(row["v23_gate_categories"])
        package = row["v23_review_package"]
        new_packages = []
        files = []
        if row["kind"] == "investigation":
            package = audit_for(item)
            source = early.get(item) or mid.get(item) or late.get(item)
            assert source and source.get("requested_scope", source.get("exact_requested_scope")) == requested[item]
            if item in INV_DELTA:
                delta, next_step = INV_DELTA[item], INV_NEXT[item]
                assessment = INV_ASSESS[item]
                new_packages = [package]
                extras = ["support/row-review.csv"] if package == R1 else ["support/row-decisions.csv"]
                extras += ["support/i005-results.json", "support/i005_models.py"] if item == "I005" else []
                extras += ["support/results.json"] if item in ("I076", "I126", "I127") else []
                if item == "I145":
                    new_packages = [R2, R3]
                    files = evidence(R2, ("support/results.json", "support/artifacts/left.llbc", "support/artifacts/right.llbc"))
                    files += evidence(R3, ("support/row-decisions.csv",))
                else:
                    files = evidence(package, extras)
            else:
                assessment = "Post-publication per-ID residual audit retained the v23 exact-scope status and gate."
                files = evidence(package, ("support/row-review.csv",) if package == R1 else ("support/row-decisions.csv",))
        else:
            if item in SUGGESTION_DIRECT:
                package = SUGGESTION_DIRECT[item]
                new_packages = [package]
                if item in SUGGESTION_DELTA:
                    delta = SUGGESTION_DELTA[item]
                    next_step = SUGGESTION_NEXT[item]
                else:
                    delta = row["v23_specific_remaining_delta"] + " The I076 same-name sibling-crate LLBC witness independently rejects serialized crate/function names as a sufficient compilation-subject key; complete cross-layer product identity remains open."
                assessment = "New I076/I145 name-only identity witness is a bounded component for this linked suggestion." if package == R2 else "New I126 Lake configuration and targeted-denial controls are bounded trust evidence for this linked suggestion."
                files = evidence(package, ("support/results.json", "support/row-decisions.csv"))
            else:
                assessment = "No directly linked new component changes the v23 suggestion assessment or remaining gate."
        row.update({
            "v24_status": status,
            "v24_gate_categories": gates,
            "v24_specific_remaining_delta": delta,
            "v24_post_v23_scope_assessment": assessment,
            "v24_review_package": package,
            "v24_new_evidence_packages": new_packages,
            "v24_evidence_files": files,
            "v24_next_prerequisite": next_step,
            "v24_new_distinct_cached_only_experiment_executed": item in ACTUAL_NEW_CELL,
        })
        assert delta and next_step
        out.append(row)
    assert {r["id"] for r in out if r["v24_specific_remaining_delta"] != r["v23_specific_remaining_delta"]} == set(INV_DELTA) | set(SUGGESTION_DIRECT)
    assert not any(r["v24_status"] != r["v23_status"] for r in out)
    (HERE / "row-challenge-v24.json").write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")

    by_id = {r["id"]: r for r in out}
    fields = ("v24_status", "v24_gate_categories", "v24_specific_remaining_delta", "v24_post_v23_scope_assessment", "v24_review_package", "v24_new_evidence_packages", "v24_evidence_files", "v24_next_prerequisite", "v24_new_distinct_cached_only_experiment_executed")
    def extend(filename, key):
        rows = []
        for before in read_csv(V23 / filename):
            row = dict(before)
            decision = by_id[row[key]]
            row["status"] = decision["v24_status"]
            for field in fields:
                value = decision[field]
                row[field] = ";".join(value) if isinstance(value, list) else (str(value) if isinstance(value, bool) else value)
            rows.append(row)
        return rows
    inv = extend("investigation-final-v23.csv", "id")
    sug = extend("3730-crosswalk-final-v23.csv", "3730_id")
    assert len(inv) == 159 and len(sug) == 174
    write_csv(HERE / "investigation-final-v24.csv", inv)
    write_csv(HERE / "3730-crosswalk-final-v24.csv", sug)

    titles = {item: re.sub(r"\s*\[[^]]+\]\.?$", "", title).strip()
              for source in (frozen["3731"]["body"], frozen["3731"]["comments"][0]["body"])
              for item, title in re.findall(r"(?m)^\*\*(I\d{3})\s+[—.]\s+([^\n]*?)\*\*", source)}
    cross = {item: (title.strip(), set(re.findall(r"I\d{3}", destinations)))
             for item, title, destinations in re.findall(r"(?m)^\| ([A-O]\d{2}) \| ([^|]+) \| ([^|]+) \|", frozen["3731"]["comments"][0]["body"])}
    assert len(titles) == 159 and len(cross) == 174
    assert all(row["title"] == titles[row["id"]] for row in inv)
    assert all(row["suggestion"] == cross[row["3730_id"]][0] and
               set(re.findall(r"I\d{3}", row["3731_destinations"])) == cross[row["3730_id"]][1]
               for row in sug)
    links = sum(len(value[1]) for value in cross.values())
    assert links == 345
    assert {row["3730_id"] for row in sug if set(row["3731_destinations"].split(";")) & set(INV_DELTA)} == set(SUGGESTION_DIRECT)

    inventory = []
    for name in PACKAGES:
        for file in sorted((REPORTS / name).rglob("*")):
            if file.is_file() and "__pycache__" not in file.parts and file.suffix != ".pyc":
                inventory.append({"path": file.relative_to(ROOT).as_posix(), "sha256": sha(file)})
    write_csv(HERE / "source-package-inventory-v24.csv", inventory)
    generated = ("row-challenge-v24.json", "investigation-final-v24.csv", "3730-crosswalk-final-v24.csv", "source-package-inventory-v24.csv")
    inputs = {"v23/row-challenge-v23.json": V23 / "row-challenge-v23.json",
              "v23/investigation-final-v23.csv": V23 / "investigation-final-v23.csv",
              "v23/3730-crosswalk-final-v23.csv": V23 / "3730-crosswalk-final-v23.csv",
              "v22/issue-scope-snapshot.json": V22 / "issue-scope-snapshot.json",
              "live-issue-hashes.json": HERE / "live-issue-hashes.json"}
    validation = {
        "baseline_reference_head": "9d2426519c7eaaf58b13b109a2f4c16d84c51616",
        "row_count": len(out),
        "investigation_count": len(inv),
        "suggestion_count": len(sug),
        "suggestion_destination_links": links,
        "status_counts": {"investigations": dict(Counter(x["status"] for x in inv)), "suggestions": dict(Counter(x["status"] for x in sug))},
        "changed_status_ids": [],
        "changed_residual_ids": sorted(set(INV_DELTA) | set(SUGGESTION_DIRECT)),
        "changed_prerequisite_ids": sorted(set(INV_NEXT) | set(SUGGESTION_NEXT)),
        "new_bounded_experiment_ids": sorted(ACTUAL_NEW_CELL),
        "linked_suggestion_ids": sorted(SUGGESTION_DIRECT),
        "source_packages": list(PACKAGES),
        "inventory_files": len(inventory),
        "input_sha256": {key: sha(path) for key, path in inputs.items()},
        "generated_sha256": {name: sha(HERE / name) for name in generated},
    }
    (HERE / "validation-v24.json").write_text(json.dumps(validation, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: validation[key] for key in ("row_count", "investigation_count", "suggestion_count", "suggestion_destination_links", "inventory_files", "changed_residual_ids")}, sort_keys=True))


if __name__ == "__main__":
    main()
