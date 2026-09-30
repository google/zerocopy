#!/usr/bin/env python3
"""Derive v38 directly from published v37 and the reviewed sequential I080 full-field report."""
import csv
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V37_NAME = "anneal-3730-3731-final-coverage-audit-2026-09-29-v37"
V37 = REPORTS / V37_NAME / "support"
SOURCE = "anneal-3731-i080-full-field-edit-revert-oracles-2026-09-29"
PACKAGES = (V37_NAME, SOURCE)
DIRECT = {"I080", "D03"}
EVIDENCE_NAMES = ("REPORT.md", "REPORT.json", "support/check.py", "support/comparison.json",
                  "support/compare.py", "support/source-results.json")

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def sha_text(value): return hashlib.sha256(value.encode()).hexdigest()
def read_csv(path):
    with path.open(newline="") as stream: return list(csv.DictReader(stream))
def write_csv(path, rows):
    with path.open("w", newline="") as stream:
        writer=csv.DictWriter(stream,fieldnames=list(rows[0]),lineterminator="\n")
        writer.writeheader();writer.writerows(rows)

def verify_live(live):
    prior=json.loads((V37/"live-issue-snapshot-v37.json").read_text())
    for n,state in ((3730,"closed"),(3731,"open")):
        x=live["issues"][str(n)];old=prior["issues"][str(n)]
        assert x["number"]==n and x["state"]==state
        assert x["body"]==old["body"] and x["body_sha256"]==sha_text(x["body"])==old["body_sha256"]
        assert len(x["comments"])==len(old["comments"])==1
        assert x["comments"][0]["id"]==old["comments"][0]["id"]
        assert x["comments"][0]["body"]==old["comments"][0]["body"]
        assert x["comments"][0]["body_sha256"]==sha_text(x["comments"][0]["body"])

def main():
    live=json.loads((HERE/"live-issue-snapshot-v38.json").read_text());verify_live(live)
    prior=json.loads((V37/"row-challenge-v37.json").read_text())
    assert len(prior)==333 and len({r["id"] for r in prior})==333
    evidence=[f"reports/{SOURCE}/{name}" for name in EVIDENCE_NAMES]
    assert all((ROOT/name).is_file() for name in evidence)
    updates={
      "I080": (
        " In a separate sequential source edit/revert corpus with CARGO_INCREMENTAL=0 and 1, all 12 shared-target completed LLBCs now have full decoded-field comparisons with same source-state cold oracles. Every pair differs only in requested destination path, generated-file local path and positional short_names order; typed-key/name maps agree. Two edited-versus-baseline cold-oracle controls detect changed embedded source and the serialized step literal 2 versus 1. This does not add concurrency, cancellation, lock tracing, representative load, path-sensitive provenance or Anneal-owned publication evidence.",
        "Direct sequential edit/revert full-field evidence extends selected-body checks across both incremental settings; the distinct v37 cancellation comparison and inherited resource/product limits remain."),
      "D03": (
        " Separately, the sequential shared-target edit/revert corpus under CARGO_INCREMENTAL=0 and 1 has full decoded comparisons of all 12 completed shared outputs against same source-state cold oracles: only destination path, generated-file local path and positional short_names order differ, while typed-key/name maps agree. Edited-versus-baseline cold controls detect embedded source and step literal 2 versus 1. This does not attest a complete producing Cargo unit, concurrent dirty-target behavior, path-insensitive keys, representative resources, Anneal target ownership or publication.",
        "Direct sequential edit/revert full-field evidence strengthens the D03 reuse component; the distinct v37 cancellation result and inherited product/resource gates remain.")}
    out=[]
    for old in prior:
        row=dict(old);item=row["id"]
        if item in DIRECT:
            addition,assessment=updates[item]
            residual=row["v37_specific_remaining_delta"]+addition
            files=evidence;packages=[SOURCE];relation="direct bounded sequential retained-output evidence"
            review=HERE.parent.name
            assert row["v37_status"]=="partial"
        else:
            residual=row["v37_specific_remaining_delta"]
            assessment=f"The I080 sequential edit/revert comparison does not directly exercise {item} ({row['title']}); the v37 residual and prerequisite remain."
            files=[];packages=[];relation="no direct v38 evidence";review=row["v37_review_package"]
        row.update({"v38_status":row["v37_status"],"v38_gate_categories":row["v37_gate_categories"],
                    "v38_specific_remaining_delta":residual,"v38_scope_assessment":assessment,
                    "v38_review_package":review,"v38_new_evidence_packages":packages,
                    "v38_evidence_files":files,"v38_next_prerequisite":row["v37_next_prerequisite"],
                    "v38_evidence_relation":relation})
        out.append(row)
    assert {r["id"] for r in out if r["v38_specific_remaining_delta"]!=r["v37_specific_remaining_delta"]}==DIRECT
    assert all(r["v38_status"]==r["v37_status"] and r["v38_gate_categories"]==r["v37_gate_categories"] and r["v38_next_prerequisite"]==r["v37_next_prerequisite"] for r in out)
    (HERE/"row-challenge-v38.json").write_text(json.dumps(out,indent=2,sort_keys=True,ensure_ascii=False)+"\n")
    by_id={r["id"]:r for r in out}
    fields=("v38_status","v38_gate_categories","v38_specific_remaining_delta","v38_scope_assessment","v38_review_package","v38_new_evidence_packages","v38_evidence_files","v38_next_prerequisite","v38_evidence_relation")
    def extend(old_name,key,new_name):
        rows=[]
        for old in read_csv(V37/old_name):
            row=dict(old);source=by_id[row[key]]
            for field in fields:
                value=source[field];row[field]=";".join(value) if isinstance(value,list) else value
            rows.append(row)
        write_csv(HERE/new_name,rows)
        return rows
    investigations=extend("investigation-final-v37.csv","id","investigation-final-v38.csv")
    suggestions=extend("3730-crosswalk-final-v37.csv","3730_id","3730-crosswalk-final-v38.csv")
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
    write_csv(HERE/"source-package-inventory-v38.csv",inventory)
    generated=("row-challenge-v38.json","investigation-final-v38.csv","3730-crosswalk-final-v38.csv","source-package-inventory-v38.csv")
    inputs={"v37/row-challenge-v37.json":V37/"row-challenge-v37.json",
            "v37/investigation-final-v37.csv":V37/"investigation-final-v37.csv",
            "v37/3730-crosswalk-final-v37.csv":V37/"3730-crosswalk-final-v37.csv",
            "live-issue-snapshot-v38.json":HERE/"live-issue-snapshot-v38.json"}
    validation={"reference_tip_at_start":"44772095872665264473eddf7131eb897b1821f0",
                "source_reference_package":V37_NAME,"source_anneal_revision":"bd0956be95c5f798f0c0484921b9b9d1fc6e9988",
                "row_count":len(out),"investigation_count":len(investigations),"suggestion_count":len(suggestions),
                "suggestion_destination_links":links,
                "status_counts":{"investigations":dict(Counter(r["status"] for r in investigations)),"suggestions":dict(Counter(r["status"] for r in suggestions))},
                "changed_status_ids":[],"changed_gate_ids":[],"changed_residual_ids":sorted(DIRECT),"changed_prerequisite_ids":[],
                "direct_evidence_ids":sorted(DIRECT),"bounded_context_ids":[],"source_packages":list(PACKAGES),
                "inventory_files":len(inventory),"input_sha256":{name:sha(path) for name,path in inputs.items()},
                "generated_sha256":{name:sha(HERE/name) for name in generated}}
    (HERE/"validation-v38.json").write_text(json.dumps(validation,indent=2,sort_keys=True)+"\n")
    print(json.dumps({key:validation[key] for key in ("row_count","suggestion_destination_links","changed_residual_ids","inventory_files")},sort_keys=True))

if __name__=="__main__":main()
