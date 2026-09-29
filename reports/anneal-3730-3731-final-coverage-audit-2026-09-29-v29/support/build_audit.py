#!/usr/bin/env python3
"""Derive v29's append-only ledger from published v28 and three reviewed reports."""
import csv
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V28_NAME = "anneal-3730-3731-final-coverage-audit-2026-09-29-v28"
V28 = REPORTS / V28_NAME / "support"
V22 = REPORTS / "anneal-3730-3731-final-coverage-audit-2026-09-29-v22" / "support"
EDIT = "anneal-3731-i080-source-edit-revert-incremental-cache-2026-09-29"
POSITION = "anneal-3731-lake-launched-position-context-v4-30-0-rc2"
REPEAT = "anneal-3731-i148-multifunction-translation-repeat-2026-09-29"
SOURCE_PACKAGES = (V28_NAME, EDIT, POSITION, REPEAT)

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def sha_text(value): return hashlib.sha256(value.encode()).hexdigest()
def csv_rows(path):
    with path.open(newline="") as stream: return list(csv.DictReader(stream))
def write_csv(path, rows):
    with path.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]), lineterminator="\n")
        writer.writeheader(); writer.writerows(rows)
def evidence(package, *names):
    out=[f"reports/{package}/{name}" for name in names]
    assert all((ROOT / name).is_file() for name in out), out
    return out

# Tuple: source package, residual, prerequisite, scope assessment, exact evidence.
UPDATES = {
    "I043": (POSITION,
        "A new fresh lake --no-cache serve fixture with a compiled local import compares plainGoal and getInteractiveGoals at seven exact nested-proof positions: four matching one-goal contexts, two matching empty lists and one matching EOF null. The inner simpa line changes target between columns, and the outer exact sees new hz; clean Lake build, setup-file Dep OLean and separate batch success/no-axiom/value controls agree for this disk-identical file. The prior 24-pair direct Lean unsaved/error/recovery grid remains distinct. Anneal-generated imports, Rust annotation projection, rich reference lifecycle, unsaved Lake edits, macro/error combinations, concurrency and exact-version adapter fencing remain untested.",
        "Run paired plain/rich position queries through Anneal's version-fenced generated/projected document and actual import graph, adding unsaved/error/macro and reference-lifecycle controls with fresh batch oracles.",
        "Seven imported Lake-server position pairs add direct nested-context evidence without satisfying Anneal source mapping or version fencing.",
        ("REPORT.md","REPORT.json","support/check.py","support/results.json","support/fixture/Dep.lean","support/fixture/Proof.lean")),
    "I080": (EDIT,
        "A pinned tiny two-crate Charon/Cargo fixture now edits only A's step body from wrapping_add(1) to wrapping_add(2), then reverts its exact source bytes, while B remains unchanged and equal-length roots sequentially share one writable target. Under CARGO_INCREMENTAL=0 and 1, all 16 requests exit 0 with parseable error-free LLBC; selected five local bodies match independent cold oracles at baseline, edited and reverted states, and B stays baseline. Incremental-on shared files rise from 55 to 70 and allocation after B from 2668 to 2988 KiB; off retains zero incremental files. The path-sensitive longer-root counterexample remains; no dirty concurrent pair, cancellation, representative load, full LLBC identity or Anneal ownership policy ran.",
        "Use guarded representative Charon snapshots to test dirty shared/private target concurrency, path-sensitive inputs, incremental-on cancellation/restart, many-worker cleanup and full output/resource ownership under Anneal scheduling.",
        "Sequential source edit/revert directly narrows the previously missing incremental-on dirty-target cell, but not concurrency or product resource policy.",
        ("REPORT.md","REPORT.json","support/check.py","support/results.json","support/probe.py","support/artifacts/inc0-edited-A.llbc","support/artifacts/inc1-edited-A.llbc","support/artifacts/inc1-reverted-B.llbc")),
    "I148": (REPEAT,
        "A new error-free five-function, one-struct Charon corpus ran three sequential same-target and two overlapping private-target extractions under one pinned preset. Five raw LLBC hashes differ only in destination path and six short_names ordering after two narrow normalizations; all five Aeneas split-file generations produce byte-identical Types/Funs/Probe Lean files. One set compiles with direct Lean; five definitions #check and combine reports axioms [propext, Classical.choice, Quot.sound]. This strengthens the prior safe single-function repeat, but does not authenticate arbitrary short-name reorder, Rust refinement, Anneal's intended V2 flags/publisher, representative large workload, provenance-safe identity or Lake invalidation cost.",
        "Repeat an error-free representative Anneal generation workload at intended flags and publication paths, then compare full obligation/provenance identity and downstream Lake/Lean invalidation under sequential and parallel producers.",
        "Five successful multi-function Charon/Aeneas translations add a concurrent and split-file repeat control; full product determinism and semantic provenance remain open.",
        ("REPORT.md","REPORT.json","support/check.py","support/results.json","support/artifacts/gen-1/Funs.lean","support/artifacts/gen-5/Funs.lean","support/artifacts/consumer/Check.lean")),
    "C02": (POSITION,
        "The new Lake-launched imported proof gives matching plain/rich categories and rendered local context at seven positions: four goals, two empty lists and one null, including a within-simpa target change and post-have hz. The earlier direct Lean 24-pair unsaved/error/recovery control remains separate. Anneal projected/generated proofs, exact-version fences, rich object dereference/expiry, tactic macros and transport integration remain untested.",
        "Run both goal APIs over actual Anneal generated/projected proofs with current-version/import fences, reference lifecycle and fresh batch comparisons.",
        "A seven-position prepared-import Lake complement directly narrows rich-versus-plain selection, not the Anneal adapter.",
        ("REPORT.md","REPORT.json","support/check.py","support/results.json","support/fixture/Proof.lean")),
    "D03": (EDIT,
        "The prior private/shared cold/warm incremental matrix now has a sequential shared-target source edit/revert complement: in both incremental modes, 16 error-free Charon LLBCs match selected cold-oracle local bodies for baseline, edited and reverted A while unchanged B remains baseline. Equal-length roots avoid the known build-script path-length counterexample; no source change was concurrent, no job was canceled, and the complete Charon-producing Cargo unit or representative Anneal target policy was not attested.",
        "Attest the producing Cargo unit and target ownership in Anneal materialized snapshots, then compare representative dirty concurrent and cancellation schedules under memory/disk guards and full output checks.",
        "A source transition now directly exercises shared Cargo reuse, while concurrency, cancellation and Anneal ownership remain open.",
        ("REPORT.md","REPORT.json","support/check.py","support/results.json","support/artifacts/inc1-edited-A.llbc")),
    "D05": (REPEAT,
        "A five-function error-free fixture now includes two overlapping Charon calls with private targets in addition to three same-target serial repeats. Raw LLBC differs only by destination and typed short_names order after narrow normalization; all five Aeneas split-file outputs are byte-identical. This is one pinned preset and tiny source, with subprocess intervals rather than instrumented OS start/exit times; arbitrary flags/revisions, shared concurrent targets and Anneal publication identity remain untested.",
        "Repeat representative error-free Charon generation under Anneal's intended flags, source identities and publication contract with matched parallel and sequential producers, then validate full obligations and downstream imports.",
        "The new concurrent successful Charon pair directly narrows D05's schedule evidence, but cannot establish general extraction determinism.",
        ("REPORT.md","REPORT.json","support/check.py","support/results.json","support/artifacts/par-1.llbc","support/artifacts/par-2.llbc")),
    "E06": (REPEAT,
        "Five Aeneas translations of narrowly equivalent error-free multi-function LLBC, including two overlapping Charon producers, generated identical split Types/Funs/Probe Lean bytes and the same five definitions; one generated set compiled and passed direct Lean #check. This extends the prior one-function serial source-repeat control, but not intended Anneal V2 generation flags, representative split layout, path/feature variants, Lake trace reuse or proof interpretation.",
        "Run matched representative generated-source repeats at Anneal's intended flags, split-file layout and path/feature variants; then measure Lake/Lean reuse and obligation provenance.",
        "A successful multi-function split-file repeat directly narrows generated-source determinism but not product or downstream reuse.",
        ("REPORT.md","REPORT.json","support/check.py","support/results.json","support/artifacts/gen-1/Funs.lean","support/artifacts/gen-5/Funs.lean","support/artifacts/consumer/Check.lean")),
    "E07": (REPEAT,
        "Five raw multi-function LLBC files have distinct bytes from destination and six typed short_names ordering, yet after only those two narrow normalizations parsed LLBC matches and five Aeneas generated Lean inventories are byte-identical; one generated set compiles with five checked definitions and combine's stated axiom inventory. This is a field-specific importer/textual-instability control, not a general semantic-equivalence oracle or Rust refinement proof. Arbitrary LLBC mutants, changed obligations, provenance-safe comparator and Anneal policy remain open.",
        "Compare actual generated obligations and Lean interpretations across controlled textual mutants and representative error-free Anneal runs under authenticated provenance keys; define a semantic comparator with explicit failure cases.",
        "A larger successful order/destination-only instability control directly narrows E07, while semantic sameness beyond this equivalence class remains unproved.",
        ("REPORT.md","REPORT.json","support/check.py","support/results.json","support/artifacts/seq-1.llbc","support/artifacts/par-1.llbc","support/artifacts/consumer/Check.lean")),
}

CONTEXT = {
    "D06": "The edit/revert and translation repeats completed without process cancellation, lock tracing or crash cleanup.",
    "F20": "The Charon shared target and generated Lean repeats did not measure full-chain generated-module rebuild isolation, archive state or byte accounting.",
    "I079": "The multi-function repeat varies output destination and short_names order but does not add a source-relocation or provenance-association contrast.",
    "I084": "The multi-function compiler check does not prove cross-language obligation equivalence or Rust refinement.",
    "I132": "The narrow LLBC normalization is not a calibrated semantic/diagnostic comparator matrix.",
    "I044": "Seven rich goal objects were rendered but opaque references were not dereferenced, expired or restarted.",
    "I046": "The Lake proof is successful and disk-identical; the row's already-complete narrow failed-elaboration control is unchanged.",
    "I075": "A source edit in one target does not authenticate Anneal's Cargo compilation-unit selection or all workspace inputs.",
    "I105": "All Charon processes finished successfully; interrupted production and transactional recovery were not exercised.",
}

def verify_live(live):
    frozen=json.loads((V22/"issue-scope-snapshot.json").read_text())
    prior=json.loads((V28/"live-issue-snapshot-v28.json").read_text())["issues"]
    for number,state in ((3730,"closed"),(3731,"open")):
        key=str(number);item=live["issues"][key]
        assert item["number"]==number and item["state"]==state
        assert item["body"]==prior[key]["body"]==frozen[key]["body"]
        assert item["body_sha256"]==sha_text(item["body"])==prior[key]["body_sha256"]
        assert len(item["comments"])==len(prior[key]["comments"])==1
        for comment,old,orig in zip(item["comments"],prior[key]["comments"],frozen[key]["comments"]):
            assert comment["id"]==old["id"] and comment["body"]==old["body"]==orig["body"]
            assert comment["body_sha256"]==sha_text(comment["body"])==old["body_sha256"]

def main():
    prior=json.loads((V28/"row-challenge-v28.json").read_text())
    live=json.loads((HERE/"live-issue-snapshot-v29.json").read_text())
    verify_live(live)
    assert len(prior)==333 and len({r["id"] for r in prior})==333
    assert len(UPDATES)==8 and not set(UPDATES)&set(CONTEXT)
    out=[]
    for old in prior:
        row=dict(old);item=row["id"]
        if item in UPDATES:
            package,residual,prerequisite,assessment,names=UPDATES[item]
            packages=[package];files=evidence(package,*names);relation="direct bounded component evidence"
            assert row["v28_status"]=="partial"
        elif item in CONTEXT:
            packages=[];files=[];residual=row["v28_specific_remaining_delta"];prerequisite=row["v28_next_prerequisite"]
            assessment=CONTEXT[item]+" The v28 residual and prerequisite remain.";relation="bounded context only"
        else:
            packages=[];files=[];residual=row["v28_specific_remaining_delta"];prerequisite=row["v28_next_prerequisite"]
            gate=";".join(row["v28_gate_categories"]) or "already resolved or conditional"
            assessment=f"None of the three new reports directly exercises {item} ({row['title']}) at its remaining {gate} gate; the v28 residual and prerequisite remain."
            relation="no direct v29 evidence"
        row.update({"v29_status":row["v28_status"],"v29_gate_categories":row["v28_gate_categories"],
                    "v29_specific_remaining_delta":residual,"v29_scope_assessment":assessment,
                    "v29_review_package":HERE.parent.name if item in UPDATES else row["v28_review_package"],
                    "v29_new_evidence_packages":packages,"v29_evidence_files":files,
                    "v29_next_prerequisite":prerequisite,"v29_evidence_relation":relation})
        out.append(row)
    assert {r["id"] for r in out if r["v29_specific_remaining_delta"]!=r["v28_specific_remaining_delta"]}==set(UPDATES)
    assert all(r["v29_status"]==r["v28_status"] and r["v29_gate_categories"]==r["v28_gate_categories"] for r in out)
    (HERE/"row-challenge-v29.json").write_text(json.dumps(out,indent=2,sort_keys=True,ensure_ascii=False)+"\n")
    by_id={r["id"]:r for r in out}
    fields=("v29_status","v29_gate_categories","v29_specific_remaining_delta","v29_scope_assessment","v29_review_package","v29_new_evidence_packages","v29_evidence_files","v29_next_prerequisite","v29_evidence_relation")
    def extend(name,key):
        rows=[]
        for before in csv_rows(V28/name):
            row=dict(before);choice=by_id[row[key]]
            for field in fields:
                value=choice[field];row[field]=";".join(value) if isinstance(value,list) else value
            rows.append(row)
        return rows
    investigations=extend("investigation-final-v28.csv","id")
    suggestions=extend("3730-crosswalk-final-v28.csv","3730_id")
    assert len(investigations)==159 and len(suggestions)==174
    write_csv(HERE/"investigation-final-v29.csv",investigations)
    write_csv(HERE/"3730-crosswalk-final-v29.csv",suggestions)
    body=live["issues"]["3731"]["body"];comment=live["issues"]["3731"]["comments"][0]["body"]
    titles={item:re.sub(r"\s*\[[^]]+\]\.?$","",title).strip() for source in (body,comment)
            for item,title in re.findall(r"(?m)^\*\*(I\d{3})\s+[—.]\s+([^\n]*?)\*\*",source)}
    cross={item:(title.strip(),set(re.findall(r"I\d{3}",destinations))) for item,title,destinations in
           re.findall(r"(?m)^\| ([A-O]\d{2}) \| ([^|]+) \| ([^|]+) \|",comment)}
    assert len(titles)==159 and len(cross)==174
    assert all(r["title"]==titles[r["id"]] for r in investigations)
    assert all(r["suggestion"]==cross[r["3730_id"]][0] and set(r["3731_destinations"].split(";"))==cross[r["3730_id"]][1] for r in suggestions)
    links=sum(len(destinations) for _,destinations in cross.values());assert links==345
    inventory=[]
    for package in SOURCE_PACKAGES:
        for path in sorted((REPORTS/package).rglob("*")):
            if path.is_file() and "__pycache__" not in path.parts and path.suffix!=".pyc":
                inventory.append({"path":path.relative_to(ROOT).as_posix(),"sha256":sha(path)})
    write_csv(HERE/"source-package-inventory-v29.csv",inventory)
    generated=("row-challenge-v29.json","investigation-final-v29.csv","3730-crosswalk-final-v29.csv","source-package-inventory-v29.csv")
    inputs={"v28/row-challenge-v28.json":V28/"row-challenge-v28.json",
            "v28/investigation-final-v28.csv":V28/"investigation-final-v28.csv",
            "v28/3730-crosswalk-final-v28.csv":V28/"3730-crosswalk-final-v28.csv",
            "v22/issue-scope-snapshot.json":V22/"issue-scope-snapshot.json",
            "live-issue-snapshot-v29.json":HERE/"live-issue-snapshot-v29.json"}
    validation={"reference_tip_at_start":"baa5c11b71289c5bf124a3f0fdc4194cf758c527",
                "source_reference_package":V28_NAME,"source_anneal_revision":"bd0956be95c5f798f0c0484921b9b9d1fc6e9988",
                "row_count":len(out),"investigation_count":len(investigations),"suggestion_count":len(suggestions),
                "suggestion_destination_links":links,
                "status_counts":{"investigations":dict(Counter(r["status"] for r in investigations)),"suggestions":dict(Counter(r["status"] for r in suggestions))},
                "changed_status_ids":[],"changed_gate_ids":[],"changed_residual_ids":sorted(UPDATES),"changed_prerequisite_ids":sorted(UPDATES),
                "direct_evidence_ids":sorted(UPDATES),"bounded_context_ids":sorted(CONTEXT),
                "source_packages":list(SOURCE_PACKAGES),"inventory_files":len(inventory),
                "input_sha256":{name:sha(path) for name,path in inputs.items()},
                "generated_sha256":{name:sha(HERE/name) for name in generated}}
    (HERE/"validation-v29.json").write_text(json.dumps(validation,indent=2,sort_keys=True)+"\n")
    print(json.dumps({key:validation[key] for key in ("row_count","suggestion_destination_links","changed_residual_ids","inventory_files","status_counts")},sort_keys=True))

if __name__=="__main__":main()
