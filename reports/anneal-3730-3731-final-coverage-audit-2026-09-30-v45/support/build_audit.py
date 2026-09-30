#!/usr/bin/env python3
"""Derive v45 from published v44 and three retained component/model packages."""
import csv
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V44_NAME = "anneal-3730-3731-final-coverage-audit-2026-09-29-v44"
V44 = REPORTS / V44_NAME / "support"
LAKE = "anneal-3731-lake-rich-term-goal-nested-2026-09-30"
UNICODE = "anneal-3731-i079-unicode-charon-spans-2026-09-30"
MODEL = "anneal-3731-i145-cross-layer-identity-ablation-model-2026-09-30"
PACKAGES = (V44_NAME, LAKE, UNICODE, MODEL)
DIRECT = {"I043": LAKE, "C02": LAKE, "I079": UNICODE, "I145": MODEL}
CONTEXT = {"D05": UNICODE, "A02": UNICODE, "A08": UNICODE}
EVIDENCE = {
    LAKE: ("REPORT.md", "REPORT.json", "support/check.py", "support/probe.py",
           "support/results.json", "support/fixture/Dep.lean", "support/fixture/Proof.lean"),
    UNICODE: ("REPORT.md", "REPORT.json", "check.py", "probe.py", "results.json",
              "comparison.json", "unicode.llbc", "fixture/src/lib.rs"),
    MODEL: ("REPORT.md", "REPORT.json", "check.py", "results.json"),
}
NEW_FIELDS = ("v45_status", "v45_gate_categories", "v45_specific_remaining_delta",
              "v45_scope_assessment", "v45_review_package", "v45_new_evidence_packages",
              "v45_evidence_files", "v45_next_prerequisite", "v45_evidence_relation")

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def sha_text(text): return hashlib.sha256(text.encode()).hexdigest()
def read_csv(path):
    with path.open(newline="") as stream: return list(csv.DictReader(stream))
def write_csv(path, rows):
    with path.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]), lineterminator="\n")
        writer.writeheader(); writer.writerows(rows)

def verify_live(live):
    prior = json.loads((V44 / "live-issue-snapshot-v44.json").read_text())
    for number, state in ((3730, "closed"), (3731, "open")):
        x, old = live["issues"][str(number)], prior["issues"][str(number)]
        assert x["number"] == number and x["state"] == old["state"] == state
        assert x["body"] == old["body"] and x["body_sha256"] == old["body_sha256"] == sha_text(x["body"])
        assert len(x["comments"]) == len(old["comments"]) == 1
        assert x["comments"][0]["id"] == old["comments"][0]["id"]
        assert x["comments"][0]["body"] == old["comments"][0]["body"]
        assert x["comments"][0]["body_sha256"] == old["comments"][0]["body_sha256"] == sha_text(x["comments"][0]["body"])

def updated_residual(item, previous):
    if item == "I043":
        return ("Published v44's nine-position reflexive proof is supplemented by a pinned Lake-launched nested "
                "`by exact Eq.trans (Eq.refl depValue) (Eq.refl depValue)` proof. Eleven sequential positions "
                "paired `plainGoal`, `getInteractiveGoals`, `plainTermGoal`, and `getInteractiveTermGoal` in one opened version. "
                "At (3,2) the two tactic APIs returned one equality goal and both term APIs returned null; at eight inner "
                "positions tactic lists were empty while both term APIs returned matching equality or `Nat` targets and "
                "ranges; next line and EOF were null. Fresh same-text batch, clean Lake build/setup, no-axiom and "
                "imported-value controls succeeded. Rich `ctx`/`term` references were observed but not dereferenced. "
                "This one nested Eq.trans shape does not define general selection at whitespace, combinator branches, "
                "unsaved/error states or arbitrary proof terms. Worker/RPC reconnect, reference lifetime, stale "
                "responses, exact-version/import fences, Anneal generated/projected proofs, Rust source map and "
                "complete-obligation batch comparison remain open.")
    if item == "C02":
        return ("Published v44 compared plain and rich tactic goals beside plain term goals. The new nested imported "
                "Eq.trans proof adds 11 exact four-API positions and directly compares `plainTermGoal` with "
                "`Lean.Widget.getInteractiveTermGoal`: both were non-null at eight inner positions, with matching "
                "target text and ranges; both were null at the start of `exact`, next line and EOF. Plain/rich tactic "
                "goal counts also matched: one at `exact`, empty at the eight term positions, null afterward. The "
                "rich term response contained tagged text and opaque `ctx`/`term` RPC references. Fresh same-text "
                "batch and no-axiom/import controls succeeded. Reference dereference/expiry, protocol lifecycle, "
                "unsaved/error variants of this nested term, worker/RPC reconnect, generated/projected Anneal proof "
                "transport and complete-obligation verification remain open.")
    if item == "I079":
        corrected = previous.replace("All tested source bytes are ASCII, so byte versus Unicode-scalar versus UTF-16 column units remain undetermined.",
                                     "The earlier 16-file span fixture was ASCII-only, so its column units were undetermined.")
        assert corrected != previous
        return corrected + (" A new independent three-line Unicode Rust fixture and retained error-free Charon LLBC "
                            "match exact source_text slices for seven local item records (five unique items). "
                            "An emoji and a combining mark distinguish coordinate hypotheses: mismatch counts are "
                            "7 UTF-8 byte, 6 scalar, 4 UTF-16 unit, and 0 fixture display-cell calculations. "
                            "The display-cell rule is a fixture-specific oracle, not a general Charon Unicode contract. "
                            "One nonlocal record and the earlier 32 generated-file records remain unverified. "
                            "No Rust-to-Lean declaration mapping, annotation attachment, cache policy or Anneal "
                            "source-map product behavior follows from these item spans.")
    if item == "I145":
        return previous + (" A new bounded symbolic model exhaustively checked 65,536 independent binary "
                           "cross-stage states and one-field omission scenarios for three declared policies. "
                           "Within those policy oracles, elaboration content needs 3 modeled fields, strict "
                           "lineage 12, and current-request admission 16; 31 present-field removals yield "
                           "counterexamples, while 17 absent-field controls leave the respective key unchanged. "
                           "Named controls include constant locators, A→B→A, equal outputs from distinct histories, "
                           "unchanged proof with changed imports, and reused worker/RPC numbers. These are "
                           "policy-model implications, not Anneal runs or a globally minimum schema. A complete "
                           "actual Cargo→Charon→Aeneas→Lake→Lean→MCP identity chain and product routing remain open.")
    return previous

def main():
    live = json.loads((HERE / "live-issue-snapshot-v45.json").read_text())
    verify_live(live)
    old_rows = json.loads((V44 / "row-challenge-v44.json").read_text())
    assert len(old_rows) == 333 and len({r["id"] for r in old_rows}) == 333
    for package, names in EVIDENCE.items():
        assert all((REPORTS / package / name).is_file() for name in names)
    out = []
    for old in old_rows:
        row = dict(old); item = row["id"]
        package = DIRECT.get(item) or CONTEXT.get(item)
        if item in DIRECT:
            residual = updated_residual(item, old["v44_specific_remaining_delta"])
            assessment = f"Direct bounded {'Lake rich term-goal' if package == LAKE else 'Unicode Charon span' if package == UNICODE else 'symbolic identity-model'} evidence; partial product gate and inherited prerequisite remain."
            relation = "direct bounded component/model evidence"
            review = HERE.parent.name
        elif item in CONTEXT:
            residual = old["v44_specific_remaining_delta"]
            assessment = ("The Unicode LLBC item-span fixture bounds a source-coordinate distinction relevant to "
                          f"{item}; it does not exercise this row's remaining product or concurrency contract.")
            relation = "bounded source-coordinate context"
            review = HERE.parent.name
        else:
            residual = old["v44_specific_remaining_delta"]
            assessment = f"The three new packages do not directly exercise {item} ({row['title']}); the v44 residual and prerequisite remain."
            relation = "no direct v45 evidence"
            review = old["v44_review_package"]
        files = [f"reports/{package}/{name}" for name in EVIDENCE[package]] if package else []
        row.update({"v45_status": old["v44_status"], "v45_gate_categories": old["v44_gate_categories"],
                    "v45_specific_remaining_delta": residual, "v45_scope_assessment": assessment,
                    "v45_review_package": review, "v45_new_evidence_packages": [package] if package else [],
                    "v45_evidence_files": files, "v45_next_prerequisite": old["v44_next_prerequisite"],
                    "v45_evidence_relation": relation})
        out.append(row)
    assert {r["id"] for r in out if r["v45_specific_remaining_delta"] != r["v44_specific_remaining_delta"]} == set(DIRECT)
    assert all(r["v45_status"] == r["v44_status"] and r["v45_gate_categories"] == r["v44_gate_categories"] and
               r["v45_next_prerequisite"] == r["v44_next_prerequisite"] for r in out)
    (HERE / "row-challenge-v45.json").write_text(json.dumps(out, indent=2, sort_keys=True, ensure_ascii=False) + "\n")
    by_id = {r["id"]: r for r in out}
    def extend(old_name, key, new_name):
        rows = []
        for old in read_csv(V44 / old_name):
            row = dict(old); source = by_id[row[key]]
            for field in NEW_FIELDS:
                value = source[field]
                row[field] = ";".join(value) if isinstance(value, list) else value
            rows.append(row)
        write_csv(HERE / new_name, rows)
        return rows
    investigations = extend("investigation-final-v44.csv", "id", "investigation-final-v45.csv")
    suggestions = extend("3730-crosswalk-final-v44.csv", "3730_id", "3730-crosswalk-final-v45.csv")
    assert len(investigations) == 159 and len(suggestions) == 174
    body, comment = live["issues"]["3731"]["body"], live["issues"]["3731"]["comments"][0]["body"]
    titles = {item: re.sub(r"\s*\[[^]]+\]\.?$", "", title).strip() for source in (body, comment)
              for item, title in re.findall(r"(?m)^\*\*(I\d{3})\s+[—.]\s+([^\n]*?)\*\*", source)}
    cross = {item: (title.strip(), set(re.findall(r"I\d{3}", destinations)))
             for item, title, destinations in re.findall(r"(?m)^\| ([A-O]\d{2}) \| ([^|]+) \| ([^|]+) \|", comment)}
    assert len(titles) == 159 and len(cross) == 174
    assert all(r["title"] == titles[r["id"]] for r in investigations)
    assert all(r["suggestion"] == cross[r["3730_id"]][0] and
               set(r["3731_destinations"].split(";")) == cross[r["3730_id"]][1] for r in suggestions)
    links = sum(len(v[1]) for v in cross.values()); assert links == 345
    inventory = []
    for package in PACKAGES:
        for path in sorted((REPORTS / package).rglob("*")):
            if path.is_file() and "__pycache__" not in path.parts and path.suffix != ".pyc":
                inventory.append({"path": path.relative_to(ROOT).as_posix(), "sha256": sha(path)})
    write_csv(HERE / "source-package-inventory-v45.csv", inventory)
    generated = ("row-challenge-v45.json", "investigation-final-v45.csv", "3730-crosswalk-final-v45.csv",
                 "source-package-inventory-v45.csv")
    inputs = {"v44/row-challenge-v44.json": V44 / "row-challenge-v44.json",
              "v44/investigation-final-v44.csv": V44 / "investigation-final-v44.csv",
              "v44/3730-crosswalk-final-v44.csv": V44 / "3730-crosswalk-final-v44.csv",
              "live-issue-snapshot-v45.json": HERE / "live-issue-snapshot-v45.json"}
    validation = {"reference_tip_at_start": "d8a86362f68d2f84c6f1165e4fe3bffa35529ee2",
                  "source_reference_package": V44_NAME,
                  "source_anneal_revision": "bd0956be95c5f798f0c0484921b9b9d1fc6e9988",
                  "row_count": len(out), "investigation_count": len(investigations),
                  "suggestion_count": len(suggestions), "suggestion_destination_links": links,
                  "status_counts": {"investigations": dict(Counter(r["status"] for r in investigations)),
                                    "suggestions": dict(Counter(r["status"] for r in suggestions))},
                  "changed_status_ids": [], "changed_gate_ids": [], "changed_prerequisite_ids": [],
                  "changed_residual_ids": sorted(DIRECT), "direct_evidence_ids": sorted(DIRECT),
                  "bounded_context_ids": sorted(CONTEXT), "source_packages": list(PACKAGES),
                  "inventory_files": len(inventory),
                  "input_sha256": {name: sha(path) for name, path in inputs.items()},
                  "generated_sha256": {name: sha(HERE / name) for name in generated}}
    (HERE / "validation-v45.json").write_text(json.dumps(validation, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: validation[key] for key in ("row_count", "suggestion_destination_links",
                                                     "changed_residual_ids", "bounded_context_ids", "inventory_files")}, sort_keys=True))

if __name__ == "__main__": main()
