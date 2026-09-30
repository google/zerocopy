#!/usr/bin/env python3
"""Derive v31's append-only ledger from published v30 and three reviewed reports."""
import csv
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V30_NAME = "anneal-3730-3731-final-coverage-audit-2026-09-29-v30"
V30 = REPORTS / V30_NAME / "support"
V22 = REPORTS / "anneal-3730-3731-final-coverage-audit-2026-09-29-v22" / "support"
ENVELOPE = "lean-goal-envelope-replay-2026-09-29"
LAKE_REPLAY = "anneal-3731-i148-five-function-lake-replay-2026-09-29"
REFUSAL = "anneal-3731-lake-malformed-manifest-preflight-refusal-2026-09-29"
SOURCE_PACKAGES = (V30_NAME, ENVELOPE, LAKE_REPLAY, REFUSAL)

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
    "I041": (ENVELOPE,
        "A deterministic Python client envelope now replays each of the three retained direct-Lean V1/V2 late-goal traces. Binding request ID to client-assigned process incarnation, URI, document version, source SHA-256 and position admits the V2 False goal as current and rejects the later V1 True goal for a latest-state caller; an explicit historical caller can retain V1. Seven synthetic controls per run cover arrival reorder, source/position/URI mutation and restart with ID reuse. This executes a proposed attribution policy over recorded payloads, not a new Lean run or Anneal adapter; the tuple lacks import generation, true worker replacement routing, multiple positions and product verification status.",
        "Implement the envelope in Anneal with source/import generation and transport-incarnation routing, then test live edits, worker replacement, cancellation, multiple positions and historical queries against current-state and batch oracles.",
        "Three real wire traces plus synthetic adversarial decisions directly exercise a client-side latest-result fence, while production causality and imports remain open.",
        ("REPORT.md","REPORT.json","support/check.py","support/replay.py","support/scenarios.json","support/expected.json","support/transcripts/transcript-run1.json","support/transcripts/transcript-run2.json","support/transcripts/transcript-run3.json")),
    "C01": (ENVELOPE,
        "A small offline client state machine now binds plainGoal requests to incarnation/URI/version/source-hash/position and classifies late V1 replies as stale or historical while keeping the V2 reply current in three retained Lean races. Synthetic restart with the same request ID and snapshot rejects the old incarnation. This is a runnable component wrapper policy, not an Anneal version-bound goal API; no imported-environment identity, trusted worker attestation, real restart callback or product transport was exercised.",
        "Implement and validate an Anneal goal wrapper carrying exact source/import and worker-incarnation identity through real edits, restart callbacks, response routing and fresh batch controls.",
        "The client-side envelope decision is directly executed against real late-reply payloads; product wrapper and loaded-import attestation remain absent.",
        ("REPORT.md","REPORT.json","support/check.py","support/replay.py","support/scenarios.json","support/expected.json")),
    "C09": (ENVELOPE,
        "The replay correlates two overlapping same-position goal requests in one document by request ID and submission envelope, accepting V2 False as current and rejecting the later V1 True in three retained wire traces. Adversarial reorder cases produce the expected latest-state decisions. This is same-position overlap and serialized model replay, not many-position concurrent Lean queries, cancellation, import changes or an Anneal request/worker fence.",
        "Run live many-position and cancellation schedules through an implemented Anneal envelope with worker/import generations, checking current and historical result classification after real replies.",
        "A concrete same-position overlap attribution control directly narrows C09, while broader concurrency and product routing remain open.",
        ("REPORT.md","REPORT.json","support/check.py","support/replay.py","support/scenarios.json","support/expected.json")),
    "I148": (LAKE_REPLAY,
        "The retained five-function Aeneas variants now have a fixed-path Lake consumer with four local modules. After a fresh build, warm no-write and four byte-identical source replacements all replayed the four modules with unchanged local trace/OLean hashes and mtimes. A real add_one x+1 to x+2 Rust/Charon/Aeneas mutant changed exactly one Funs.lean line; Lake replayed Types but rebuilt Funs, Probe and Consumer, changing their traces while some downstream OLean bytes stayed equal. A changed no-write build replayed all four, and selected equality-to-self theorems compiled with combine_self axioms [propext, Classical.choice, Quot.sound]. This is one sequential pinned consumer and trivial proof oracle, not Anneal publication, obligation provenance, Rust refinement, general semantic sameness or representative workload.",
        "Repeat representative Anneal generation through its actual publication and proof attachment path, compare full source/obligation provenance under concurrent producers, and measure Lake/Lean behavior with nontrivial verification oracles.",
        "Eight bounded Lake builds directly measure same-path replay and one function-change invalidation for the five-function corpus; product semantics remain open.",
        ("REPORT.md","REPORT.json","support/check.py","support/results.json","support/summary.json","support/theorem-output.txt","support/work/mutant-generated/Funs.lean","support/work/consumer/Consumer.lean")),
}

CONTEXT = {
    "I092": "The malformed-manifest cell was refused at 25.09% estimated free memory against its 30% minimum, so no Lake behavior was observed.",
    "F07": "The malformed-manifest fail-closed control did not run because its 30% free-memory admission gate rejected a 25.09% reading.",
    "F08": "The refused manifest cell made no server or first-goal query; it adds no readiness behavior evidence.",
    "E06": "The Lake replay measures downstream behavior after byte-identical generated source, but adds no new Aeneas source-determinism contrast beyond the prior five-function report.",
    "E07": "The changed-function control alters generated Lean and checks equality-to-self theorems; it does not compare semantic sameness under textual LLBC instability or authenticate obligations.",
    "F20": "The four-module Lake invalidation cell lacks the actual prepared Anneal archive, generated consumer ownership and whole-chain byte accounting requested here.",
    "I045": "The incarnation collision is synthetic replay, not a delayed real Lean reply across internal worker replacement on one transport.",
    "I048": "A client-assigned process token and source hash do not attest the complete loaded Lean import environment.",
    "I145": "The offline envelope does not ablate complete Cargo-to-Lean cross-layer product identity or authenticated import generation.",
    "I134": "Reordered model decisions do not add a real many-position or publisher/worker concurrency transcript.",
    "I079": "The same-path Lake replay does not test source relocation, annotation association or general LLBC normalization policy.",
    "I084": "The equality-to-self theorem is not a Rust refinement or generated obligation equivalence oracle.",
    "I132": "One function-change invalidation control is not a calibrated semantic/diagnostic comparator matrix.",
    "I044": "The replay uses plainGoal text, not rich RPC references or their lifetime.",
}

def verify_live(live):
    frozen=json.loads((V22/"issue-scope-snapshot.json").read_text())
    prior=json.loads((V30/"live-issue-snapshot-v30.json").read_text())["issues"]
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
    prior=json.loads((V30/"row-challenge-v30.json").read_text())
    live=json.loads((HERE/"live-issue-snapshot-v31.json").read_text())
    verify_live(live)
    assert len(prior)==333 and len({r["id"] for r in prior})==333
    assert len(UPDATES)==4 and not set(UPDATES)&set(CONTEXT)
    out=[]
    for old in prior:
        row=dict(old);item=row["id"]
        if item in UPDATES:
            package,residual,prerequisite,assessment,names=UPDATES[item]
            packages=[package];files=evidence(package,*names);relation="direct bounded component evidence"
            assert row["v30_status"]=="partial"
        elif item in CONTEXT:
            packages=[];files=[];residual=row["v30_specific_remaining_delta"];prerequisite=row["v30_next_prerequisite"]
            assessment=CONTEXT[item]+" The v30 residual and prerequisite remain.";relation="bounded context only"
        else:
            packages=[];files=[];residual=row["v30_specific_remaining_delta"];prerequisite=row["v30_next_prerequisite"]
            gate=";".join(row["v30_gate_categories"]) or "already resolved or conditional"
            assessment=f"None of the three new reports directly exercises {item} ({row['title']}) at its remaining {gate} gate; the v30 residual and prerequisite remain."
            relation="no direct v31 evidence"
        row.update({"v31_status":row["v30_status"],"v31_gate_categories":row["v30_gate_categories"],
                    "v31_specific_remaining_delta":residual,"v31_scope_assessment":assessment,
                    "v31_review_package":HERE.parent.name if item in UPDATES else row["v30_review_package"],
                    "v31_new_evidence_packages":packages,"v31_evidence_files":files,
                    "v31_next_prerequisite":prerequisite,"v31_evidence_relation":relation})
        out.append(row)
    assert {r["id"] for r in out if r["v31_specific_remaining_delta"]!=r["v30_specific_remaining_delta"]}==set(UPDATES)
    assert all(r["v31_status"]==r["v30_status"] and r["v31_gate_categories"]==r["v30_gate_categories"] for r in out)
    (HERE/"row-challenge-v31.json").write_text(json.dumps(out,indent=2,sort_keys=True,ensure_ascii=False)+"\n")
    by_id={r["id"]:r for r in out}
    fields=("v31_status","v31_gate_categories","v31_specific_remaining_delta","v31_scope_assessment","v31_review_package","v31_new_evidence_packages","v31_evidence_files","v31_next_prerequisite","v31_evidence_relation")
    def extend(name,key):
        rows=[]
        for before in csv_rows(V30/name):
            row=dict(before);choice=by_id[row[key]]
            for field in fields:
                value=choice[field];row[field]=";".join(value) if isinstance(value,list) else value
            rows.append(row)
        return rows
    investigations=extend("investigation-final-v30.csv","id")
    suggestions=extend("3730-crosswalk-final-v30.csv","3730_id")
    assert len(investigations)==159 and len(suggestions)==174
    write_csv(HERE/"investigation-final-v31.csv",investigations)
    write_csv(HERE/"3730-crosswalk-final-v31.csv",suggestions)
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
    write_csv(HERE/"source-package-inventory-v31.csv",inventory)
    generated=("row-challenge-v31.json","investigation-final-v31.csv","3730-crosswalk-final-v31.csv","source-package-inventory-v31.csv")
    inputs={"v30/row-challenge-v30.json":V30/"row-challenge-v30.json",
            "v30/investigation-final-v30.csv":V30/"investigation-final-v30.csv",
            "v30/3730-crosswalk-final-v30.csv":V30/"3730-crosswalk-final-v30.csv",
            "v22/issue-scope-snapshot.json":V22/"issue-scope-snapshot.json",
            "live-issue-snapshot-v31.json":HERE/"live-issue-snapshot-v31.json"}
    validation={"reference_tip_at_start":"3b549cb1eddebc54896a106c5c94ede6c2c134e5",
                "source_reference_package":V30_NAME,"source_anneal_revision":"bd0956be95c5f798f0c0484921b9b9d1fc6e9988",
                "row_count":len(out),"investigation_count":len(investigations),"suggestion_count":len(suggestions),
                "suggestion_destination_links":links,
                "status_counts":{"investigations":dict(Counter(r["status"] for r in investigations)),"suggestions":dict(Counter(r["status"] for r in suggestions))},
                "changed_status_ids":[],"changed_gate_ids":[],"changed_residual_ids":sorted(UPDATES),"changed_prerequisite_ids":sorted(UPDATES),
                "direct_evidence_ids":sorted(UPDATES),"bounded_context_ids":sorted(CONTEXT),
                "source_packages":list(SOURCE_PACKAGES),"inventory_files":len(inventory),
                "input_sha256":{name:sha(path) for name,path in inputs.items()},
                "generated_sha256":{name:sha(HERE/name) for name in generated}}
    (HERE/"validation-v31.json").write_text(json.dumps(validation,indent=2,sort_keys=True)+"\n")
    print(json.dumps({key:validation[key] for key in ("row_count","suggestion_destination_links","changed_residual_ids","inventory_files","status_counts")},sort_keys=True))

if __name__=="__main__":main()
