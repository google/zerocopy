#!/usr/bin/env python3
"""Derive v44 directly from published v43 and the reviewed reflexive Lake tactic/term-position report."""
import csv
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V43_NAME = "anneal-3730-3731-final-coverage-audit-2026-09-29-v43"
V43 = REPORTS / V43_NAME / "support"
SOURCE = "anneal-3731-lake-reflexive-term-goal-positions-v4-30-0-rc2"
PACKAGES = (V43_NAME, SOURCE)
DIRECT = {"I043", "C02"}
EVIDENCE_NAMES = ("REPORT.md", "REPORT.json", "support/check.py", "support/probe.py",
                  "support/results.json", "support/fixture/Dep.lean", "support/fixture/Proof.lean")

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def sha_text(value): return hashlib.sha256(value.encode()).hexdigest()
def read_csv(path):
    with path.open(newline="") as stream: return list(csv.DictReader(stream))
def write_csv(path, rows):
    with path.open("w", newline="") as stream:
        writer=csv.DictWriter(stream,fieldnames=list(rows[0]),lineterminator="\n")
        writer.writeheader();writer.writerows(rows)

def verify_live(live):
    prior=json.loads((V43/"live-issue-snapshot-v43.json").read_text())
    for n,state in ((3730,"closed"),(3731,"open")):
        x=live["issues"][str(n)];old=prior["issues"][str(n)]
        assert x["number"]==n and x["state"]==state
        assert x["body"]==old["body"] and x["body_sha256"]==sha_text(x["body"])==old["body_sha256"]
        assert len(x["comments"])==len(old["comments"])==1
        assert x["comments"][0]["id"]==old["comments"][0]["id"]
        assert x["comments"][0]["body"]==old["comments"][0]["body"]
        assert x["comments"][0]["body_sha256"]==sha_text(x["comments"][0]["body"])

def main():
    live=json.loads((HERE/"live-issue-snapshot-v44.json").read_text());verify_live(live)
    prior=json.loads((V43/"row-challenge-v43.json").read_text())
    assert len(prior)==333 and len({r["id"] for r in prior})==333
    evidence=[f"reports/{SOURCE}/{name}" for name in EVIDENCE_NAMES]
    assert all((ROOT/name).is_file() for name in evidence)
    updates={
      "I043": (
        "Earlier separate Lake fixtures retained 20 paired plain/rich unsaved macro/error positions and 13 paired nested constructor/inner-have positions. A new pinned Lake-launched local-import reflexive proof `depValue = depValue := by exact Eq.refl depValue` adds nine exact plainGoal/getInteractiveGoals/plainTermGoal triples. At (3,2) plain/rich show the tactic goal `⊢ depValue = depValue` while plainTermGoal is null. At (3,8) and (3,11) both tactic APIs show empty lists while plainTermGoal shows `⊢ depValue = depValue` over range (3,8)-(3,24); at (3,16), (3,20) and (3,24) it shows `⊢ Nat` over (3,16)-(3,24), again with empty tactic goals. The next line and EOF return null. Clean Lake build/setup, fresh same-text batch, no-axiom and imported-value controls succeeded with no error diagnostics. This one reflexive theorem and local goal guidance do not establish general term-proof selection or proof correctness beyond the fresh batch result for this exact file. Still open: broader/non-reflexive term proofs, combinator branches, whitespace changes, unsaved nested/error combinations, worker restart/reconnect, RPC reconnect, rich reference dereference/expiry, full protocol transcript/lifecycle coverage, late or stale responses and exact-version/import fencing. Actual Anneal launcher, generated/projected proof, Rust source map and editor/MCP integration with complete-obligation batch verification remain untested.",
        "Direct bounded Lake tactic-versus-term position evidence in one reflexive imported proof; v43 partial product gate and Anneal integration prerequisite remain."),
      "C02": (
        "Earlier Lake fixtures recorded 20 matched plain/rich unsaved macro/error pairs and 13 matched nested constructor/inner-have pairs. A separate pinned reflexive imported proof adds nine exact plainGoal/getInteractiveGoals/plainTermGoal triples. At the start of `exact` (3,2), both tactic APIs display `⊢ depValue = depValue`; inside `Eq.refl` (3,8)/(3,11), both tactic APIs are empty while plainTermGoal returns the equality goal over (3,8)-(3,24). Inside the argument (3,16)/(3,20) and at (3,24), the tactic APIs remain empty while plainTermGoal returns `⊢ Nat` over (3,16)-(3,24). Next line and EOF are null. Fresh same-text batch and no-axiom/import controls succeeded. Rich getInteractiveGoals was compared only for tactic goals; term goals came from plainTermGoal, and this reflexive toy does not establish general proof correctness or term selection. Still open: broader/non-reflexive term proofs, combinator/whitespace changes, unsaved nested/error combinations, worker restart/reconnect, RPC reconnect, rich object dereference/expiry, full protocol transcript/lifecycle coverage, late or stale responses and exact-version/import fencing. Anneal generated/projected proof, Rust source map, actual launcher and editor/MCP transport with complete-obligation batch verification remain untested.",
        "Direct bounded plain/rich tactic-goal comparison beside plainTermGoal in one reflexive Lake proof; v43 partial product gate and generated/projection prerequisite remain.")}
    out=[]
    for old in prior:
        row=dict(old);item=row["id"]
        if item in DIRECT:
            residual,assessment=updates[item]
            files=evidence;packages=[SOURCE];relation="direct bounded Lake tactic/term-position evidence"
            review=HERE.parent.name
            assert row["v43_status"]=="partial"
        else:
            residual=row["v43_specific_remaining_delta"]
            assessment=f"The reflexive Lake term-position report does not directly exercise {item} ({row['title']}); the v43 residual and prerequisite remain."
            files=[];packages=[];relation="no direct v44 evidence";review=row["v43_review_package"]
        row.update({"v44_status":row["v43_status"],"v44_gate_categories":row["v43_gate_categories"],
                    "v44_specific_remaining_delta":residual,"v44_scope_assessment":assessment,
                    "v44_review_package":review,"v44_new_evidence_packages":packages,
                    "v44_evidence_files":files,"v44_next_prerequisite":row["v43_next_prerequisite"],
                    "v44_evidence_relation":relation})
        out.append(row)
    assert {r["id"] for r in out if r["v44_specific_remaining_delta"]!=r["v43_specific_remaining_delta"]}==DIRECT
    assert all(r["v44_status"]==r["v43_status"] and r["v44_gate_categories"]==r["v43_gate_categories"] and r["v44_next_prerequisite"]==r["v43_next_prerequisite"] for r in out)
    (HERE/"row-challenge-v44.json").write_text(json.dumps(out,indent=2,sort_keys=True,ensure_ascii=False)+"\n")
    by_id={r["id"]:r for r in out}
    fields=("v44_status","v44_gate_categories","v44_specific_remaining_delta","v44_scope_assessment","v44_review_package","v44_new_evidence_packages","v44_evidence_files","v44_next_prerequisite","v44_evidence_relation")
    def extend(old_name,key,new_name):
        rows=[]
        for old in read_csv(V43/old_name):
            row=dict(old);source=by_id[row[key]]
            for field in fields:
                value=source[field];row[field]=";".join(value) if isinstance(value,list) else value
            rows.append(row)
        write_csv(HERE/new_name,rows)
        return rows
    investigations=extend("investigation-final-v43.csv","id","investigation-final-v44.csv")
    suggestions=extend("3730-crosswalk-final-v43.csv","3730_id","3730-crosswalk-final-v44.csv")
    assert len(investigations)==159 and len(suggestions)==174
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
    for package in PACKAGES:
        for path in sorted((REPORTS/package).rglob("*")):
            if path.is_file() and "__pycache__" not in path.parts and path.suffix!=".pyc":
                inventory.append({"path":path.relative_to(ROOT).as_posix(),"sha256":sha(path)})
    write_csv(HERE/"source-package-inventory-v44.csv",inventory)
    generated=("row-challenge-v44.json","investigation-final-v44.csv","3730-crosswalk-final-v44.csv","source-package-inventory-v44.csv")
    inputs={"v43/row-challenge-v43.json":V43/"row-challenge-v43.json",
            "v43/investigation-final-v43.csv":V43/"investigation-final-v43.csv",
            "v43/3730-crosswalk-final-v43.csv":V43/"3730-crosswalk-final-v43.csv",
            "live-issue-snapshot-v44.json":HERE/"live-issue-snapshot-v44.json"}
    validation={"reference_tip_at_start":"3d88b2c31d6c0774066ff581cf5d2bc27547b948",
                "source_reference_package":V43_NAME,"source_anneal_revision":"bd0956be95c5f798f0c0484921b9b9d1fc6e9988",
                "row_count":len(out),"investigation_count":len(investigations),"suggestion_count":len(suggestions),
                "suggestion_destination_links":links,
                "status_counts":{"investigations":dict(Counter(r["status"] for r in investigations)),"suggestions":dict(Counter(r["status"] for r in suggestions))},
                "changed_status_ids":[],"changed_gate_ids":[],"changed_residual_ids":sorted(DIRECT),"changed_prerequisite_ids":[],
                "direct_evidence_ids":sorted(DIRECT),"bounded_context_ids":[],"source_packages":list(PACKAGES),
                "inventory_files":len(inventory),"input_sha256":{name:sha(path) for name,path in inputs.items()},
                "generated_sha256":{name:sha(HERE/name) for name in generated}}
    (HERE/"validation-v44.json").write_text(json.dumps(validation,indent=2,sort_keys=True)+"\n")
    print(json.dumps({key:validation[key] for key in ("row_count","suggestion_destination_links","changed_residual_ids","inventory_files")},sort_keys=True))

if __name__=="__main__":main()
