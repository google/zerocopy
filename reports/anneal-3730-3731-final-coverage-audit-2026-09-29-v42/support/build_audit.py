#!/usr/bin/env python3
"""Derive v42 directly from published v41 and the reviewed I079 ASCII-local source-span report."""
import csv
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V41_NAME = "anneal-3730-3731-final-coverage-audit-2026-09-29-v41"
V41 = REPORTS / V41_NAME / "support"
SOURCE = "anneal-3731-i079-local-span-source-text-2026-09-29"
PACKAGES = (V41_NAME, SOURCE)
DIRECT = {"I079"}
EVIDENCE_NAMES = ("REPORT.md", "REPORT.json", "support/check.py", "support/compare.py",
                  "support/comparison.json", "support/source-results.json",
                  "support/source-states/baseline.rs", "support/source-states/edited.rs")

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def sha_text(value): return hashlib.sha256(value.encode()).hexdigest()
def read_csv(path):
    with path.open(newline="") as stream: return list(csv.DictReader(stream))
def write_csv(path, rows):
    with path.open("w", newline="") as stream:
        writer=csv.DictWriter(stream,fieldnames=list(rows[0]),lineterminator="\n")
        writer.writeheader();writer.writerows(rows)

def verify_live(live):
    prior=json.loads((V41/"live-issue-snapshot-v41.json").read_text())
    for n,state in ((3730,"closed"),(3731,"open")):
        x=live["issues"][str(n)];old=prior["issues"][str(n)]
        assert x["number"]==n and x["state"]==state
        assert x["body"]==old["body"] and x["body_sha256"]==sha_text(x["body"])==old["body_sha256"]
        assert len(x["comments"])==len(old["comments"])==1
        assert x["comments"][0]["id"]==old["comments"][0]["id"]
        assert x["comments"][0]["body"]==old["comments"][0]["body"]
        assert x["comments"][0]["body_sha256"]==sha_text(x["comments"][0]["body"])

def main():
    live=json.loads((HERE/"live-issue-snapshot-v42.json").read_text());verify_live(live)
    prior=json.loads((V41/"row-challenge-v41.json").read_text())
    assert len(prior)==333 and len({r["id"] for r in prior})==333
    evidence=[f"reports/{SOURCE}/{name}" for name in EVIDENCE_NAMES]
    assert all((ROOT/name).is_file() for name in evidence)
    updates={
      "I079": (
        " Separately, an offline ASCII-only source-span check of all 16 retained incremental-off/on edit/revert LLBCs finds 64 exact local app/src/lib.rs file-ID-0 item-span slices matching item_meta.source_text and the independently retained baseline or hash-verified one-expression edited Rust source state. In this fixture the matching offsets support one-based lines, zero-based columns and exclusive ends; shifted-start and inclusive-end controls fail, edited A and cold edited oracles carry wrapping_add(2), and unchanged B/reverted A carry baseline wrapping_add(1). Thirty-two local generated-file-ID-1 item records are explicitly excluded because their generated Rust source state was not independently retained. All tested source bytes are ASCII, so byte versus Unicode-scalar versus UTF-16 column units remain undetermined. This does not authenticate a Rust-to-Lean mapping, establish arbitrary source movement or Unicode span behavior, general LLBC normalization, annotation association, or Anneal cache-key policy.",
        "Direct bounded local ASCII source-provenance observation across 16 retained LLBCs; generated-file, Unicode, cross-layer and product identity gates remain.")}
    out=[]
    for old in prior:
        row=dict(old);item=row["id"]
        if item in DIRECT:
            addition,assessment=updates[item]
            residual=row["v41_specific_remaining_delta"]+addition
            files=evidence;packages=[SOURCE];relation="direct bounded retained-artifact evidence"
            review=HERE.parent.name
            assert row["v41_status"]=="partial"
        else:
            residual=row["v41_specific_remaining_delta"]
            assessment=f"The ASCII-local source-span comparison does not directly exercise {item} ({row['title']}); the v41 residual and prerequisite remain."
            files=[];packages=[];relation="no direct v42 evidence";review=row["v41_review_package"]
        row.update({"v42_status":row["v41_status"],"v42_gate_categories":row["v41_gate_categories"],
                    "v42_specific_remaining_delta":residual,"v42_scope_assessment":assessment,
                    "v42_review_package":review,"v42_new_evidence_packages":packages,
                    "v42_evidence_files":files,"v42_next_prerequisite":row["v41_next_prerequisite"],
                    "v42_evidence_relation":relation})
        out.append(row)
    assert {r["id"] for r in out if r["v42_specific_remaining_delta"]!=r["v41_specific_remaining_delta"]}==DIRECT
    assert all(r["v42_status"]==r["v41_status"] and r["v42_gate_categories"]==r["v41_gate_categories"] and r["v42_next_prerequisite"]==r["v41_next_prerequisite"] for r in out)
    (HERE/"row-challenge-v42.json").write_text(json.dumps(out,indent=2,sort_keys=True,ensure_ascii=False)+"\n")
    by_id={r["id"]:r for r in out}
    fields=("v42_status","v42_gate_categories","v42_specific_remaining_delta","v42_scope_assessment","v42_review_package","v42_new_evidence_packages","v42_evidence_files","v42_next_prerequisite","v42_evidence_relation")
    def extend(old_name,key,new_name):
        rows=[]
        for old in read_csv(V41/old_name):
            row=dict(old);source=by_id[row[key]]
            for field in fields:
                value=source[field];row[field]=";".join(value) if isinstance(value,list) else value
            rows.append(row)
        write_csv(HERE/new_name,rows)
        return rows
    investigations=extend("investigation-final-v41.csv","id","investigation-final-v42.csv")
    suggestions=extend("3730-crosswalk-final-v41.csv","3730_id","3730-crosswalk-final-v42.csv")
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
    write_csv(HERE/"source-package-inventory-v42.csv",inventory)
    generated=("row-challenge-v42.json","investigation-final-v42.csv","3730-crosswalk-final-v42.csv","source-package-inventory-v42.csv")
    inputs={"v41/row-challenge-v41.json":V41/"row-challenge-v41.json",
            "v41/investigation-final-v41.csv":V41/"investigation-final-v41.csv",
            "v41/3730-crosswalk-final-v41.csv":V41/"3730-crosswalk-final-v41.csv",
            "live-issue-snapshot-v42.json":HERE/"live-issue-snapshot-v42.json"}
    validation={"reference_tip_at_start":"974c035a2a32b8b873ad560b572eeda7a69679bb",
                "source_reference_package":V41_NAME,"source_anneal_revision":"bd0956be95c5f798f0c0484921b9b9d1fc6e9988",
                "row_count":len(out),"investigation_count":len(investigations),"suggestion_count":len(suggestions),
                "suggestion_destination_links":links,
                "status_counts":{"investigations":dict(Counter(r["status"] for r in investigations)),"suggestions":dict(Counter(r["status"] for r in suggestions))},
                "changed_status_ids":[],"changed_gate_ids":[],"changed_residual_ids":sorted(DIRECT),"changed_prerequisite_ids":[],
                "direct_evidence_ids":sorted(DIRECT),"bounded_context_ids":[],"source_packages":list(PACKAGES),
                "inventory_files":len(inventory),"input_sha256":{name:sha(path) for name,path in inputs.items()},
                "generated_sha256":{name:sha(HERE/name) for name in generated}}
    (HERE/"validation-v42.json").write_text(json.dumps(validation,indent=2,sort_keys=True)+"\n")
    print(json.dumps({key:validation[key] for key in ("row_count","suggestion_destination_links","changed_residual_ids","inventory_files")},sort_keys=True))

if __name__=="__main__":main()
