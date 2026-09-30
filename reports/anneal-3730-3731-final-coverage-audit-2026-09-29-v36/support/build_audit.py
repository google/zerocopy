#!/usr/bin/env python3
"""Derive v36 directly from published v35 and one reviewed source report."""
import csv
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V35_NAME = "anneal-3730-3731-final-coverage-audit-2026-09-29-v35"
V35 = REPORTS / V35_NAME / "support"
SOURCE = "anneal-3731-lake-unsaved-macro-error-positions-v4-30-0-rc2"
PACKAGES = (V35_NAME, SOURCE)
DIRECT = {"I043", "C02"}
EVIDENCE_NAMES = ("REPORT.md", "REPORT.json", "support/check.py", "support/results.json",
                  "support/probe.py", "support/fixture/Dep.lean", "support/fixture/Proof.lean")

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def sha_text(value): return hashlib.sha256(value.encode()).hexdigest()
def read_csv(path):
    with path.open(newline="") as stream: return list(csv.DictReader(stream))
def write_csv(path, rows):
    with path.open("w", newline="") as stream:
        writer=csv.DictWriter(stream,fieldnames=list(rows[0]),lineterminator="\n")
        writer.writeheader();writer.writerows(rows)

def verify_live(live):
    prior=json.loads((V35/"live-issue-snapshot-v35.json").read_text())
    for n,state in ((3730,"closed"),(3731,"open")):
        x=live["issues"][str(n)];old=prior["issues"][str(n)]
        assert x["number"]==n and x["state"]==state
        assert x["body"]==old["body"] and x["body_sha256"]==sha_text(x["body"])==old["body_sha256"]
        assert len(x["comments"])==len(old["comments"])==1
        assert x["comments"][0]["id"]==old["comments"][0]["id"]
        assert x["comments"][0]["body"]==old["comments"][0]["body"]
        assert x["comments"][0]["body_sha256"]==sha_text(x["comments"][0]["body"])

def main():
    live=json.loads((HERE/"live-issue-snapshot-v36.json").read_text());verify_live(live)
    prior=json.loads((V35/"row-challenge-v35.json").read_text())
    assert len(prior)==333 and len({r["id"] for r in prior})==333
    evidence=[f"reports/{SOURCE}/{name}" for name in EVIDENCE_NAMES]
    assert all((ROOT/name).is_file() for name in evidence)
    updates={
      "I043": (
        "A pinned Lake-launched server with one compiled local import queried the same URI at five positions across solved macro, unresolved macro, syntax-error and restored unsaved full-text versions. All 20 paired plainGoal/getInteractiveGoals categories matched: seven one-goal, seven empty and six null; displayed rich hypothesis/target text matched every nonempty plain goal. Fresh batch controls on the exact variant text exited 0/1/1 and live error counts were 0/2/1/0. The syntax-error macro body at (4,8) returned no goals despite failing batch compilation. Prior valid-only nested Lake and direct unsaved grids remain separate. This combined cell does not test nested goals/tactics, combinators, whitespace changes, term proofs/plainTermGoal, worker restart/reconnect, RPC reconnect or rich reference lifetime. Anneal launcher, generated/projected proof, Rust source map, exact-version/import fence and editor/MCP integration remain untested.",
        "Direct bounded Lake-imported unsaved macro/error plain/rich position evidence; the v35 partial product gate and Anneal integration prerequisite remain."),
      "C02": (
        "The pinned Lake-launched imported proof adds 20 matched plainGoal/getInteractiveGoals pairs across solved, unresolved, syntax-error and restored unsaved macro versions: seven one-goal, seven empty and six null, with matching displayed hypothesis/target text in nonempty pairs. Fresh batch exits were 0/1/1 and live errors 0/2/1/0; the syntax-error macro body returned no goals while the same source text failed batch. The earlier seven-pair valid-only Lake context and 24-pair direct Lean unsaved/error controls remain separate. This cell does not test nested goals/tactics, combinators, whitespace changes, term proofs/plainTermGoal, worker restart/reconnect, RPC reconnect or rich object dereference/expiry. Anneal generated/projected proof, Rust source map, actual launcher, exact-version/import fence and editor/MCP transport remain untested.",
        "Direct bounded rich-versus-plain comparison through Lake under unsaved macro/error versions; the v35 partial product gate and generated/projection prerequisite remain.")}
    out=[]
    for old in prior:
        row=dict(old);item=row["id"]
        if item in DIRECT:
            residual,assessment=updates[item]
            files=evidence;packages=[SOURCE];relation="direct bounded component evidence"
            review=HERE.parent.name
            assert row["v35_status"]=="partial"
        else:
            residual=row["v35_specific_remaining_delta"]
            assessment=f"The Lake unsaved macro/error report does not directly exercise {item} ({row['title']}); the v35 residual and prerequisite remain."
            files=[];packages=[];relation="no direct v36 evidence";review=row["v35_review_package"]
        row.update({"v36_status":row["v35_status"],"v36_gate_categories":row["v35_gate_categories"],
                    "v36_specific_remaining_delta":residual,"v36_scope_assessment":assessment,
                    "v36_review_package":review,"v36_new_evidence_packages":packages,
                    "v36_evidence_files":files,"v36_next_prerequisite":row["v35_next_prerequisite"],
                    "v36_evidence_relation":relation})
        out.append(row)
    assert {r["id"] for r in out if r["v36_specific_remaining_delta"]!=r["v35_specific_remaining_delta"]}==DIRECT
    assert all(r["v36_status"]==r["v35_status"] and r["v36_gate_categories"]==r["v35_gate_categories"] and r["v36_next_prerequisite"]==r["v35_next_prerequisite"] for r in out)
    (HERE/"row-challenge-v36.json").write_text(json.dumps(out,indent=2,sort_keys=True,ensure_ascii=False)+"\n")
    by_id={r["id"]:r for r in out}
    fields=("v36_status","v36_gate_categories","v36_specific_remaining_delta","v36_scope_assessment","v36_review_package","v36_new_evidence_packages","v36_evidence_files","v36_next_prerequisite","v36_evidence_relation")
    def extend(old_name,key,new_name):
        rows=[]
        for old in read_csv(V35/old_name):
            row=dict(old);source=by_id[row[key]]
            for field in fields:
                value=source[field];row[field]=";".join(value) if isinstance(value,list) else value
            rows.append(row)
        write_csv(HERE/new_name,rows)
        return rows
    investigations=extend("investigation-final-v35.csv","id","investigation-final-v36.csv")
    suggestions=extend("3730-crosswalk-final-v35.csv","3730_id","3730-crosswalk-final-v36.csv")
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
    write_csv(HERE/"source-package-inventory-v36.csv",inventory)
    generated=("row-challenge-v36.json","investigation-final-v36.csv","3730-crosswalk-final-v36.csv","source-package-inventory-v36.csv")
    inputs={"v35/row-challenge-v35.json":V35/"row-challenge-v35.json",
            "v35/investigation-final-v35.csv":V35/"investigation-final-v35.csv",
            "v35/3730-crosswalk-final-v35.csv":V35/"3730-crosswalk-final-v35.csv",
            "live-issue-snapshot-v36.json":HERE/"live-issue-snapshot-v36.json"}
    validation={"reference_tip_at_start":"db2686d050caf5870e60118c80df713638cdd42d",
                "source_reference_package":V35_NAME,"source_anneal_revision":"bd0956be95c5f798f0c0484921b9b9d1fc6e9988",
                "row_count":len(out),"investigation_count":len(investigations),"suggestion_count":len(suggestions),
                "suggestion_destination_links":links,
                "status_counts":{"investigations":dict(Counter(r["status"] for r in investigations)),"suggestions":dict(Counter(r["status"] for r in suggestions))},
                "changed_status_ids":[],"changed_gate_ids":[],"changed_residual_ids":sorted(DIRECT),"changed_prerequisite_ids":[],
                "direct_evidence_ids":sorted(DIRECT),"bounded_context_ids":[],"source_packages":list(PACKAGES),
                "inventory_files":len(inventory),"input_sha256":{name:sha(path) for name,path in inputs.items()},
                "generated_sha256":{name:sha(HERE/name) for name in generated}}
    (HERE/"validation-v36.json").write_text(json.dumps(validation,indent=2,sort_keys=True)+"\n")
    print(json.dumps({key:validation[key] for key in ("row_count","suggestion_destination_links","changed_residual_ids","inventory_files")},sort_keys=True))

if __name__=="__main__":main()
