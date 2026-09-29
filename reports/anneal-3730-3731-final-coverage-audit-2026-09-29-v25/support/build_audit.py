#!/usr/bin/env python3
"""Deterministically derive v25 from v24 and the 174-suggestion audit.

Writes only this package's support files; does not fetch or alter source reports.
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
V24 = REPORTS / "anneal-3730-3731-final-coverage-audit-2026-09-29-v24/support"
V22 = REPORTS / "anneal-3730-3731-final-coverage-audit-2026-09-29-v22/support"
SUGGESTION_AUDIT = "anneal-3730-174-suggestion-postpublication-native-trust-audit-2026-09-29"
SOURCE_PACKAGES = (
    "anneal-3730-3731-final-coverage-audit-2026-09-29-v24",
    "anneal-3731-i001-i053-postpublication-residual-review-2026-09-29",
    "anneal-3731-i054-i106-postpublication-residual-audit-2026-09-29",
    "anneal-3731-i107-i159-postpublication-residual-audit-2026-09-29",
    SUGGESTION_AUDIT,
)
NATIVE = REPORTS / SUGGESTION_AUDIT


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


def new_files(extra=()):
    paths = [f"reports/{SUGGESTION_AUDIT}/REPORT.md",
             f"reports/{SUGGESTION_AUDIT}/REPORT.json",
             f"reports/{SUGGESTION_AUDIT}/support/row-decisions.csv",
             f"reports/{SUGGESTION_AUDIT}/support/check.py"]
    paths.extend(f"reports/{SUGGESTION_AUDIT}/{item}" for item in extra)
    assert all((ROOT / item).is_file() for item in paths)
    return paths


def main():
    old = json.loads((V24 / "row-challenge-v24.json").read_text())
    assert len(old) == 333 and len({item["id"] for item in old}) == 333
    reviewed = {row["id"]: row for row in read_csv(NATIVE / "support/row-decisions.csv")}
    prior_suggestions = {row["3730_id"]: row for row in read_csv(V24 / "3730-crosswalk-final-v24.csv")}
    assert len(reviewed) == len(prior_suggestions) == 174 and set(reviewed) == set(prior_suggestions)
    for item, row in reviewed.items():
        before = prior_suggestions[item]
        assert row["v24_status"] == row["audit_status"] == before["v24_status"]
        assert row["consolidation_title"] == before["suggestion"]
        assert row["destinations"] == before["3731_destinations"]
        assert row["next_prerequisite"] == before["v24_next_prerequisite"]
        assert row["requested_text_sha256"] == hashlib.sha256(row["requested_text"].encode()).hexdigest()
        assert bool(row["entire_requested_scope_supported"] == "true") == (item in {"C04", "C13", "N11"})
        if item != "G09":
            assert row["remaining_gate"] == before["v24_specific_remaining_delta"], item

    live = json.loads((HERE / "live-issue-hashes.json").read_text())
    previous_live = json.loads((V24 / "live-issue-hashes.json").read_text())
    frozen = json.loads((V22 / "issue-scope-snapshot.json").read_text())
    for n, state in ((3730, "closed"), (3731, "open")):
        now, before = live["issues"][str(n)], previous_live["issues"][str(n)]
        assert now["state"] == state and now["number"] == n
        assert now["body_sha256"] == before["body_sha256"] == hashlib.sha256(frozen[str(n)]["body"].encode()).hexdigest()
        assert now["comments"] == before["comments"]
        assert now["comments"][0]["body_sha256"] == hashlib.sha256(frozen[str(n)]["comments"][0]["body"].encode()).hexdigest()

    out = []
    for previous in old:
        row = dict(previous)
        item = row["id"]
        status = row["v24_status"]
        gate_categories = list(row["v24_gate_categories"])
        residual = row["v24_specific_remaining_delta"]
        prerequisite = row["v24_next_prerequisite"]
        assessment = "No new component directly changes this investigation beyond the v24 range-audit evidence."
        review_package = row["v24_review_package"]
        new_packages = []
        files = []
        original_request_sha256 = ""
        full_scope = ""
        evidence_relation = ""
        cached_only = "See the linked v24 range-audit decision."
        cited_packages = ""
        if row["kind"] == "suggestion":
            source = reviewed[item]
            residual = source["remaining_gate"]
            prerequisite = source["next_prerequisite"]
            assessment = source["scope_assessment"]
            review_package = SUGGESTION_AUDIT
            files = new_files(("support/results.json", "support/raw-streams/plugin-deny.stderr") if item == "G09" else ())
            if item == "G09":
                new_packages = [SUGGESTION_AUDIT]
            original_request_sha256 = source["requested_text_sha256"]
            full_scope = source["entire_requested_scope_supported"]
            evidence_relation = source["new_evidence_relation"]
            cached_only = source["cached_only_decision"]
            cited_packages = source["cited_packages"]
        elif item == "I126":
            residual = ("Cargo build-script, proc-macro, Lean run_cmd and Lake configuration callbacks had bounded execution controls. "
                        "A retained native Lean plugin initializer now also wrote an owned outside-workspace marker when allowed; "
                        "targeted macOS denial blocked it while a no-plugin proof passed. Full native/Cargo/Lake/Lean containment, "
                        "resource limits, inspection-before-execution, and Anneal trust-entry authorization remain untested.")
            assessment = "Native-plugin execution and targeted denial close one more I126 inventory cell; no broad untrusted-project safety follows."
            review_package = SUGGESTION_AUDIT
            new_packages = [SUGGESTION_AUDIT]
            files = new_files(("support/results.json", "support/inputs/Plugin.lean", "support/inputs/plugin__probe_Plugin.dylib"))
            cached_only = "New bounded native-plugin execution/denial control executed; full scope remains gated."
        elif item == "I127":
            residual = ("The Lake denial and new native-plugin denial each exposed an absolute owned scratch path in raw diagnostics; "
                        "their retained summaries normalize that root. Private-source, credential, environment, generated-file and "
                        "product-log leakage controls through an Anneal evidence pipeline remain untested.")
            assessment = "The plugin-denial path corroborates the prior I127 owned-path observation, without a private-source leakage test."
            review_package = SUGGESTION_AUDIT
            new_packages = [SUGGESTION_AUDIT]
            files = new_files(("support/results.json", "support/raw-streams/plugin-deny.stderr"))
            cached_only = "Cross-slice native denial corroborates an owned-path exposure; no distinct private-source trial executed."
        row.update({
            "v25_status": status,
            "v25_gate_categories": gate_categories,
            "v25_specific_remaining_delta": residual,
            "v25_post_v24_scope_assessment": assessment,
            "v25_review_package": review_package,
            "v25_new_evidence_packages": new_packages,
            "v25_evidence_files": files,
            "v25_next_prerequisite": prerequisite,
            "v25_original_request_sha256": original_request_sha256,
            "v25_entire_requested_scope_supported": full_scope,
            "v25_new_evidence_relation": evidence_relation,
            "v25_cached_only_decision": cached_only,
            "v25_cited_packages": cited_packages,
        })
        assert residual and prerequisite and cached_only
        out.append(row)
    assert not any(item["v25_status"] != item["v24_status"] for item in out)
    assert {item["id"] for item in out if item["v25_specific_remaining_delta"] != item["v24_specific_remaining_delta"]} == {"G09", "I126", "I127"}
    (HERE / "row-challenge-v25.json").write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")

    decisions = {row["id"]: row for row in out}
    fields = ("v25_status", "v25_gate_categories", "v25_specific_remaining_delta", "v25_post_v24_scope_assessment",
              "v25_review_package", "v25_new_evidence_packages", "v25_evidence_files", "v25_next_prerequisite",
              "v25_original_request_sha256", "v25_entire_requested_scope_supported", "v25_new_evidence_relation",
              "v25_cached_only_decision", "v25_cited_packages")
    def extend(filename, key):
        rows = []
        for before in read_csv(V24 / filename):
            row = dict(before)
            choice = decisions[row[key]]
            row["status"] = choice["v25_status"]
            for field in fields:
                value = choice[field]
                row[field] = ";".join(value) if isinstance(value, list) else value
            rows.append(row)
        return rows
    investigations = extend("investigation-final-v24.csv", "id")
    suggestions = extend("3730-crosswalk-final-v24.csv", "3730_id")
    assert len(investigations) == 159 and len(suggestions) == 174
    write_csv(HERE / "investigation-final-v25.csv", investigations)
    write_csv(HERE / "3730-crosswalk-final-v25.csv", suggestions)

    titles = {item: re.sub(r"\s*\[[^]]+\]\.?$", "", title).strip()
              for source in (frozen["3731"]["body"], frozen["3731"]["comments"][0]["body"])
              for item, title in re.findall(r"(?m)^\*\*(I\d{3})\s+[—.]\s+([^\n]*?)\*\*", source)}
    cross = {item: (title.strip(), set(re.findall(r"I\d{3}", destinations)))
             for item, title, destinations in re.findall(r"(?m)^\| ([A-O]\d{2}) \| ([^|]+) \| ([^|]+) \|", frozen["3731"]["comments"][0]["body"])}
    assert len(titles) == 159 and len(cross) == 174
    assert all(x["title"] == titles[x["id"]] for x in investigations)
    assert all(x["suggestion"] == cross[x["3730_id"]][0] and
               set(x["3731_destinations"].split(";")) == cross[x["3730_id"]][1]
               for x in suggestions)
    links = sum(len(destinations) for _, destinations in cross.values())
    assert links == 345

    inventory = []
    for name in SOURCE_PACKAGES:
        for file in sorted((REPORTS / name).rglob("*")):
            if file.is_file() and "__pycache__" not in file.parts and file.suffix != ".pyc":
                inventory.append({"path": file.relative_to(ROOT).as_posix(), "sha256": sha(file)})
    write_csv(HERE / "source-package-inventory-v25.csv", inventory)
    generated = ("row-challenge-v25.json", "investigation-final-v25.csv", "3730-crosswalk-final-v25.csv", "source-package-inventory-v25.csv")
    inputs = {"v24/row-challenge-v24.json": V24 / "row-challenge-v24.json",
              "v24/investigation-final-v24.csv": V24 / "investigation-final-v24.csv",
              "v24/3730-crosswalk-final-v24.csv": V24 / "3730-crosswalk-final-v24.csv",
              "v22/issue-scope-snapshot.json": V22 / "issue-scope-snapshot.json",
              "live-issue-hashes.json": HERE / "live-issue-hashes.json",
              f"{SUGGESTION_AUDIT}/support/row-decisions.csv": NATIVE / "support/row-decisions.csv"}
    validation = {
        "baseline_reference_head": "9d2426519c7eaaf58b13b109a2f4c16d84c51616",
        "row_count": len(out), "investigation_count": len(investigations), "suggestion_count": len(suggestions),
        "suggestion_destination_links": links,
        "status_counts": {"investigations": dict(Counter(x["status"] for x in investigations)),
                          "suggestions": dict(Counter(x["status"] for x in suggestions))},
        "changed_status_ids": [], "changed_residual_ids": ["G09", "I126", "I127"],
        "changed_prerequisite_ids": [],
        "new_bounded_experiment_ids": ["I126"],
        "cross_slice_observation_ids": ["I127"],
        "direct_suggestion_evidence_ids": ["G09"],
        "source_packages": list(SOURCE_PACKAGES),
        "inventory_files": len(inventory),
        "input_sha256": {key: sha(path) for key, path in inputs.items()},
        "generated_sha256": {key: sha(HERE / key) for key in generated},
    }
    (HERE / "validation-v25.json").write_text(json.dumps(validation, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: validation[key] for key in ("row_count", "suggestion_destination_links", "changed_residual_ids", "inventory_files", "status_counts")}, sort_keys=True))


if __name__ == "__main__":
    main()
