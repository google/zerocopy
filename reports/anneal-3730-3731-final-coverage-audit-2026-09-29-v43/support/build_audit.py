#!/usr/bin/env python3
"""Derive v43 directly from published v42 and the reviewed nested Lake tactic-position report."""
import csv
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V42_NAME = "anneal-3730-3731-final-coverage-audit-2026-09-29-v42"
V42 = REPORTS / V42_NAME / "support"
SOURCE = "anneal-3731-lake-nested-constructor-goal-positions-v4-30-0-rc2"
PACKAGES = (V42_NAME, SOURCE)
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
    prior=json.loads((V42/"live-issue-snapshot-v42.json").read_text())
    for n,state in ((3730,"closed"),(3731,"open")):
        x=live["issues"][str(n)];old=prior["issues"][str(n)]
        assert x["number"]==n and x["state"]==state
        assert x["body"]==old["body"] and x["body_sha256"]==sha_text(x["body"])==old["body_sha256"]
        assert len(x["comments"])==len(old["comments"])==1
        assert x["comments"][0]["id"]==old["comments"][0]["id"]
        assert x["comments"][0]["body"]==old["comments"][0]["body"]
        assert x["comments"][0]["body_sha256"]==sha_text(x["comments"][0]["body"])

def main():
    live=json.loads((HERE/"live-issue-snapshot-v43.json").read_text());verify_live(live)
    prior=json.loads((V42/"row-challenge-v42.json").read_text())
    assert len(prior)==333 and len({r["id"] for r in prior})==333
    evidence=[f"reports/{SOURCE}/{name}" for name in EVIDENCE_NAMES]
    assert all((ROOT/name).is_file() for name in evidence)
    updates={
      "I043": (
        "The prior separate Lake unsaved macro/error fixture compared 20 paired plain/rich positions across four buffer versions and retained batch and diagnostic controls. A new pinned Lake-launched imported nested constructor/two-bullet/inner-have proof adds 13 exact plainGoal/getInteractiveGoals pairs: the conjunction before constructor, two left/right goals after it, the inner equality goal, the resumed outer left goal with new hz, the right True goal, three empty lists and EOF null. All categories and displayed goal contexts matched; clean Lake build/setup and fresh same-text batch succeeded with no theorem axioms and imported value 7. This is one successful, disk-identical nested proofstate grid, not full protocol transcript or lifecycle coverage. Still open: combinator branches, whitespace changes, term-proof positions/plainTermGoal, unsaved nested/error combinations, worker restart/reconnect, RPC reconnect, rich reference dereference/expiry, late or stale responses and exact-version/import fencing. The actual Anneal launcher, generated/projected proof, Rust source map and editor/MCP integration with complete-obligation batch verification remain untested.",
        "Direct bounded nested Lake proofstate position evidence with two-goal selection and an inner have; v42 partial product gate and Anneal integration prerequisite remain."),
      "C02": (
        "The earlier Lake unsaved macro/error matrix recorded 20 matched plainGoal/getInteractiveGoals pairs. A separate pinned imported nested constructor/two-bullet/inner-have proof now adds 13 paired positions: nine nonempty positions (including two with both left/right goals), three empty lists and EOF null. Rich displayed goal targets, case names and hypothesis names/types matched the corresponding plain goals; the fresh same-text batch succeeded with no theorem axioms and imported value 7. These are local proofstate responses in one successful nested fixture, not full protocol transcript or lifecycle coverage. Still open: combinator/whitespace changes, term-proof positions/plainTermGoal, unsaved nested/error combinations, worker restart/reconnect, RPC reconnect, rich object dereference/expiry, late or stale responses and exact-version/import fencing. Anneal generated/projected proof, Rust source map, actual launcher and editor/MCP transport with complete-obligation batch verification remain untested.",
        "Direct bounded rich-versus-plain comparison at 13 nested Lake positions; v42 partial product gate and generated/projection prerequisite remain.")}
    out=[]
    for old in prior:
        row=dict(old);item=row["id"]
        if item in DIRECT:
            residual,assessment=updates[item]
            files=evidence;packages=[SOURCE];relation="direct bounded Lake proofstate evidence"
            review=HERE.parent.name
            assert row["v42_status"]=="partial"
        else:
            residual=row["v42_specific_remaining_delta"]
            assessment=f"The nested Lake proofstate report does not directly exercise {item} ({row['title']}); the v42 residual and prerequisite remain."
            files=[];packages=[];relation="no direct v43 evidence";review=row["v42_review_package"]
        row.update({"v43_status":row["v42_status"],"v43_gate_categories":row["v42_gate_categories"],
                    "v43_specific_remaining_delta":residual,"v43_scope_assessment":assessment,
                    "v43_review_package":review,"v43_new_evidence_packages":packages,
                    "v43_evidence_files":files,"v43_next_prerequisite":row["v42_next_prerequisite"],
                    "v43_evidence_relation":relation})
        out.append(row)
    assert {r["id"] for r in out if r["v43_specific_remaining_delta"]!=r["v42_specific_remaining_delta"]}==DIRECT
    assert all(r["v43_status"]==r["v42_status"] and r["v43_gate_categories"]==r["v42_gate_categories"] and r["v43_next_prerequisite"]==r["v42_next_prerequisite"] for r in out)
    (HERE/"row-challenge-v43.json").write_text(json.dumps(out,indent=2,sort_keys=True,ensure_ascii=False)+"\n")
    by_id={r["id"]:r for r in out}
    fields=("v43_status","v43_gate_categories","v43_specific_remaining_delta","v43_scope_assessment","v43_review_package","v43_new_evidence_packages","v43_evidence_files","v43_next_prerequisite","v43_evidence_relation")
    def extend(old_name,key,new_name):
        rows=[]
        for old in read_csv(V42/old_name):
            row=dict(old);source=by_id[row[key]]
            for field in fields:
                value=source[field];row[field]=";".join(value) if isinstance(value,list) else value
            rows.append(row)
        write_csv(HERE/new_name,rows)
        return rows
    investigations=extend("investigation-final-v42.csv","id","investigation-final-v43.csv")
    suggestions=extend("3730-crosswalk-final-v42.csv","3730_id","3730-crosswalk-final-v43.csv")
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
    write_csv(HERE/"source-package-inventory-v43.csv",inventory)
    generated=("row-challenge-v43.json","investigation-final-v43.csv","3730-crosswalk-final-v43.csv","source-package-inventory-v43.csv")
    inputs={"v42/row-challenge-v42.json":V42/"row-challenge-v42.json",
            "v42/investigation-final-v42.csv":V42/"investigation-final-v42.csv",
            "v42/3730-crosswalk-final-v42.csv":V42/"3730-crosswalk-final-v42.csv",
            "live-issue-snapshot-v43.json":HERE/"live-issue-snapshot-v43.json"}
    validation={"reference_tip_at_start":"29ea19d9dccef4f046d0b53eed0e8dc20b9c9ae7",
                "source_reference_package":V42_NAME,"source_anneal_revision":"bd0956be95c5f798f0c0484921b9b9d1fc6e9988",
                "row_count":len(out),"investigation_count":len(investigations),"suggestion_count":len(suggestions),
                "suggestion_destination_links":links,
                "status_counts":{"investigations":dict(Counter(r["status"] for r in investigations)),"suggestions":dict(Counter(r["status"] for r in suggestions))},
                "changed_status_ids":[],"changed_gate_ids":[],"changed_residual_ids":sorted(DIRECT),"changed_prerequisite_ids":[],
                "direct_evidence_ids":sorted(DIRECT),"bounded_context_ids":[],"source_packages":list(PACKAGES),
                "inventory_files":len(inventory),"input_sha256":{name:sha(path) for name,path in inputs.items()},
                "generated_sha256":{name:sha(HERE/name) for name in generated}}
    (HERE/"validation-v43.json").write_text(json.dumps(validation,indent=2,sort_keys=True)+"\n")
    print(json.dumps({key:validation[key] for key in ("row_count","suggestion_destination_links","changed_residual_ids","inventory_files")},sort_keys=True))

if __name__=="__main__":main()
