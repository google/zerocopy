#!/usr/bin/env python3
"""Derive v39 directly from published v38 and the reviewed warm-bin full-field report."""
import csv
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V38_NAME = "anneal-3730-3731-final-coverage-audit-2026-09-29-v38"
V38 = REPORTS / V38_NAME / "support"
SOURCE = "anneal-3731-i075-warm-bin-full-field-2026-09-29"
PACKAGES = (V38_NAME, SOURCE)
DIRECT = {"I079"}
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
    prior=json.loads((V38/"live-issue-snapshot-v38.json").read_text())
    for n,state in ((3730,"closed"),(3731,"open")):
        x=live["issues"][str(n)];old=prior["issues"][str(n)]
        assert x["number"]==n and x["state"]==state
        assert x["body"]==old["body"] and x["body_sha256"]==sha_text(x["body"])==old["body_sha256"]
        assert len(x["comments"])==len(old["comments"])==1
        assert x["comments"][0]["id"]==old["comments"][0]["id"]
        assert x["comments"][0]["body"]==old["comments"][0]["body"]
        assert x["comments"][0]["body_sha256"]==sha_text(x["comments"][0]["body"])

def main():
    live=json.loads((HERE/"live-issue-snapshot-v39.json").read_text());verify_live(live)
    prior=json.loads((V38/"row-challenge-v38.json").read_text())
    assert len(prior)==333 and len({r["id"] for r in prior})==333
    evidence=[f"reports/{SOURCE}/{name}" for name in EVIDENCE_NAMES]
    assert all((ROOT/name).is_file() for name in evidence)
    updates={
      "I079": (
        " Separately, the pinned --bin subject_matrix_cli cold and retained-target forced-dirty repeat now have an exhaustive full decoded-field comparison: their 30 differing leaves are one requested destination path and 29 positional short_names leaves across 11 of 15 array slots; all 15 typed-key/name entries agree. Both original compact JSON files round-trip byte for byte, so those differences account for the two raw hash values in this exact pair. No function declaration, embedded source contents or other decoded model field differs. This does not establish semantic equivalence, a general canonicalizer, cache-fresh warm producer behavior, or Anneal cache-key policy.",
        "Direct bounded LLBC byte-identity explanation for one forced-dirty retained-target pair; the v38 product gate and general provenance/normalization prerequisite remain.")}
    out=[]
    for old in prior:
        row=dict(old);item=row["id"]
        if item in DIRECT:
            addition,assessment=updates[item]
            residual=row["v38_specific_remaining_delta"]+addition
            files=evidence;packages=[SOURCE];relation="direct bounded retained-artifact evidence"
            review=HERE.parent.name
            assert row["v38_status"]=="partial"
        else:
            residual=row["v38_specific_remaining_delta"]
            assessment=f"The warm-bin full-field comparison does not directly exercise {item} ({row['title']}); the v38 residual and prerequisite remain."
            files=[];packages=[];relation="no direct v39 evidence";review=row["v38_review_package"]
        row.update({"v39_status":row["v38_status"],"v39_gate_categories":row["v38_gate_categories"],
                    "v39_specific_remaining_delta":residual,"v39_scope_assessment":assessment,
                    "v39_review_package":review,"v39_new_evidence_packages":packages,
                    "v39_evidence_files":files,"v39_next_prerequisite":row["v38_next_prerequisite"],
                    "v39_evidence_relation":relation})
        out.append(row)
    assert {r["id"] for r in out if r["v39_specific_remaining_delta"]!=r["v38_specific_remaining_delta"]}==DIRECT
    assert all(r["v39_status"]==r["v38_status"] and r["v39_gate_categories"]==r["v38_gate_categories"] and r["v39_next_prerequisite"]==r["v38_next_prerequisite"] for r in out)
    (HERE/"row-challenge-v39.json").write_text(json.dumps(out,indent=2,sort_keys=True,ensure_ascii=False)+"\n")
    by_id={r["id"]:r for r in out}
    fields=("v39_status","v39_gate_categories","v39_specific_remaining_delta","v39_scope_assessment","v39_review_package","v39_new_evidence_packages","v39_evidence_files","v39_next_prerequisite","v39_evidence_relation")
    def extend(old_name,key,new_name):
        rows=[]
        for old in read_csv(V38/old_name):
            row=dict(old);source=by_id[row[key]]
            for field in fields:
                value=source[field];row[field]=";".join(value) if isinstance(value,list) else value
            rows.append(row)
        write_csv(HERE/new_name,rows)
        return rows
    investigations=extend("investigation-final-v38.csv","id","investigation-final-v39.csv")
    suggestions=extend("3730-crosswalk-final-v38.csv","3730_id","3730-crosswalk-final-v39.csv")
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
    write_csv(HERE/"source-package-inventory-v39.csv",inventory)
    generated=("row-challenge-v39.json","investigation-final-v39.csv","3730-crosswalk-final-v39.csv","source-package-inventory-v39.csv")
    inputs={"v38/row-challenge-v38.json":V38/"row-challenge-v38.json",
            "v38/investigation-final-v38.csv":V38/"investigation-final-v38.csv",
            "v38/3730-crosswalk-final-v38.csv":V38/"3730-crosswalk-final-v38.csv",
            "live-issue-snapshot-v39.json":HERE/"live-issue-snapshot-v39.json"}
    validation={"reference_tip_at_start":"f15ee4d3a9896c17b13c3167e364cb98f11a259f",
                "source_reference_package":V38_NAME,"source_anneal_revision":"bd0956be95c5f798f0c0484921b9b9d1fc6e9988",
                "row_count":len(out),"investigation_count":len(investigations),"suggestion_count":len(suggestions),
                "suggestion_destination_links":links,
                "status_counts":{"investigations":dict(Counter(r["status"] for r in investigations)),"suggestions":dict(Counter(r["status"] for r in suggestions))},
                "changed_status_ids":[],"changed_gate_ids":[],"changed_residual_ids":sorted(DIRECT),"changed_prerequisite_ids":[],
                "direct_evidence_ids":sorted(DIRECT),"bounded_context_ids":[],"source_packages":list(PACKAGES),
                "inventory_files":len(inventory),"input_sha256":{name:sha(path) for name,path in inputs.items()},
                "generated_sha256":{name:sha(HERE/name) for name in generated}}
    (HERE/"validation-v39.json").write_text(json.dumps(validation,indent=2,sort_keys=True)+"\n")
    print(json.dumps({key:validation[key] for key in ("row_count","suggestion_destination_links","changed_residual_ids","inventory_files")},sort_keys=True))

if __name__=="__main__":main()
