#!/usr/bin/env python3
"""Offline v42 audit checker: inherited rows, live scope, inventory and sources."""
import csv
import hashlib
import importlib.util
import json
import re
import subprocess
import sys
from pathlib import Path

HERE=Path(__file__).resolve().parent
REPORTS=HERE.parents[1]
ROOT=REPORTS.parent
V41=REPORTS/"anneal-3730-3731-final-coverage-audit-2026-09-29-v41"/"support"
DIRECT={"I079"}
SOURCE="anneal-3731-i079-local-span-source-text-2026-09-29"
FIELDS=("v42_status","v42_gate_categories","v42_specific_remaining_delta","v42_scope_assessment",
        "v42_review_package","v42_new_evidence_packages","v42_evidence_files",
        "v42_next_prerequisite","v42_evidence_relation")

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def rows(path):
    with path.open(newline="") as stream:return list(csv.DictReader(stream))

def main():
    v=json.loads((HERE/"validation-v42.json").read_text())
    assert v["reference_tip_at_start"]=="974c035a2a32b8b873ad560b572eeda7a69679bb"
    assert v["source_reference_package"]==V41.parent.name
    assert v["source_anneal_revision"]=="bd0956be95c5f798f0c0484921b9b9d1fc6e9988"
    assert (v["row_count"],v["investigation_count"],v["suggestion_count"],v["suggestion_destination_links"])==(333,159,174,345)
    assert v["status_counts"]=={"investigations":{"complete":4,"partial":151,"not-run":1,"conditional":3},
                                "suggestions":{"complete":3,"partial":162,"not-run":5,"conditional":4}}
    assert set(v["changed_residual_ids"])==set(v["direct_evidence_ids"])==DIRECT
    assert v["changed_status_ids"]==v["changed_gate_ids"]==v["changed_prerequisite_ids"]==[]
    assert v["bounded_context_ids"]==[]
    for name,expected in v["input_sha256"].items():
        path=V41/name[4:] if name.startswith("v41/") else HERE/name
        assert sha(path)==expected,name
    for name,expected in v["generated_sha256"].items():assert sha(HERE/name)==expected,name

    old=json.loads((V41/"row-challenge-v41.json").read_text())
    current=json.loads((HERE/"row-challenge-v42.json").read_text())
    assert len(old)==len(current)==333 and len({r["id"] for r in current})==333
    by_id={r["id"]:r for r in current}
    for before,row in zip(old,current):
        item=row["id"]
        assert all(row[k]==value for k,value in before.items()),item
        assert row["v42_status"]==row["v41_status"] and row["v42_gate_categories"]==row["v41_gate_categories"]
        assert row["v42_next_prerequisite"]==row["v41_next_prerequisite"]
        assert row["v42_scope_assessment"] and row["v42_specific_remaining_delta"]
        assert all((ROOT/path).is_file() for path in row["v42_evidence_files"]),item
        if item in DIRECT:
            assert row["v42_status"]=="partial" and row["v42_review_package"]==HERE.parent.name
            assert row["v42_new_evidence_packages"]==[SOURCE] and len(row["v42_evidence_files"])==8
            assert row["v42_specific_remaining_delta"]!=row["v41_specific_remaining_delta"]
            assert row["v42_evidence_relation"]=="direct bounded retained-artifact evidence"
        else:
            assert row["v42_specific_remaining_delta"]==row["v41_specific_remaining_delta"]
            assert row["v42_review_package"]==row["v41_review_package"]
            assert row["v42_new_evidence_packages"]==row["v42_evidence_files"]==[]
            assert "v41 residual and prerequisite remain" in row["v42_scope_assessment"]
            assert row["v42_evidence_relation"]=="no direct v42 evidence"
    assert {r["id"] for r in current if r["v42_specific_remaining_delta"]!=r["v41_specific_remaining_delta"]}==DIRECT
    prior=next(r for r in old if r["id"]=="I079")["v41_specific_remaining_delta"]
    residual=by_id["I079"]["v42_specific_remaining_delta"]
    assert residual.startswith(prior) and by_id["I079"]["v42_status"]=="partial"
    addition=residual[len(prior):]
    for phrase in ("16 retained", "64 exact local", "file-ID-0", "one-based lines", "zero-based columns", "exclusive ends", "shifted-start", "inclusive-end", "Thirty-two local generated-file-ID-1", "ASCII", "Unicode-scalar", "UTF-16", "undetermined", "Rust-to-Lean mapping", "Anneal cache-key policy"):
        assert phrase in addition,phrase
    for item in ("I149","I080","I083","I084","D03","E11","D06","I075","I076"):
        assert by_id[item]["v42_specific_remaining_delta"]==by_id[item]["v41_specific_remaining_delta"]

    for new,old_name,key,count in (("investigation-final-v42.csv","investigation-final-v41.csv","id",159),
                                   ("3730-crosswalk-final-v42.csv","3730-crosswalk-final-v41.csv","3730_id",174)):
        before=rows(V41/old_name);now=rows(HERE/new)
        assert len(before)==len(now)==count and [r[key] for r in before]==[r[key] for r in now]
        for a,b in zip(before,now):
            assert all(b[field]==value for field,value in a.items()),b[key]
            item=by_id[b[key]]
            assert b["status"]==b["v42_status"]==item["v42_status"]
            for field in FIELDS:
                value=item[field]
                assert b[field]==(";".join(value) if isinstance(value,list) else value),(b[key],field)

    live=json.loads((HERE/"live-issue-snapshot-v42.json").read_text())
    prev=json.loads((V41/"live-issue-snapshot-v41.json").read_text())
    assert live["source"]=="public GitHub REST issue and comments endpoints"
    assert live["fetched_at_utc"]==prev["fetched_at_utc"]
    for number,state in ((3730,"closed"),(3731,"open")):
        x=live["issues"][str(number)];p=prev["issues"][str(number)]
        assert x["number"]==number and x["state"]==state
        assert x["body"]==p["body"] and x["body_sha256"]==hashlib.sha256(x["body"].encode()).hexdigest()==p["body_sha256"]
        assert len(x["comments"])==len(p["comments"])==1
        y=x["comments"][0];z=p["comments"][0]
        assert y["id"]==z["id"] and y["body"]==z["body"]
        assert y["body_sha256"]==hashlib.sha256(y["body"].encode()).hexdigest()==z["body_sha256"]
    body=live["issues"]["3731"]["body"];comment=live["issues"]["3731"]["comments"][0]["body"]
    titles={item:re.sub(r"\s*\[[^]]+\]\.?$","",title).strip() for source in (body,comment)
            for item,title in re.findall(r"(?m)^\*\*(I\d{3})\s+[—.]\s+([^\n]*?)\*\*",source)}
    cross={item:(title.strip(),set(re.findall(r"I\d{3}",destinations))) for item,title,destinations in
           re.findall(r"(?m)^\| ([A-O]\d{2}) \| ([^|]+) \| ([^|]+) \|",comment)}
    investigations=rows(HERE/"investigation-final-v42.csv")
    suggestions=rows(HERE/"3730-crosswalk-final-v42.csv")
    assert len(titles)==159 and len(cross)==174
    assert all(r["title"]==titles[r["id"]] for r in investigations)
    assert all(r["suggestion"]==cross[r["3730_id"]][0] and set(r["3731_destinations"].split(";"))==cross[r["3730_id"]][1] for r in suggestions)
    assert sum(len(destinations) for _,destinations in cross.values())==345

    inventory=rows(HERE/"source-package-inventory-v42.csv")
    assert len(inventory)==v["inventory_files"] and len({r["path"] for r in inventory})==len(inventory)
    expected={path.relative_to(ROOT).as_posix() for package in v["source_packages"]
              for path in (REPORTS/package).rglob("*") if path.is_file() and "__pycache__" not in path.parts and path.suffix!=".pyc"}
    assert {r["path"] for r in inventory}==expected
    for row in inventory:assert sha(ROOT/row["path"])==row["sha256"],row["path"]
    assert v["source_packages"]==[V41.parent.name,SOURCE]
    for package in v["source_packages"]:
        path=REPORTS/package
        result=subprocess.run([sys.executable,"-B",str(path/"support/check.py")],cwd=ROOT,capture_output=True,text=True,timeout=120)
        assert result.returncode==0,(package,result.stdout,result.stderr)

    spec=importlib.util.spec_from_file_location("reference",ROOT/"tools/reference.py")
    reference=importlib.util.module_from_spec(spec);sys.modules[spec.name]=reference;spec.loader.exec_module(reference)
    for package in (V41.parent.name,SOURCE,HERE.parent.name):
        report,problems=reference._load_report(REPORTS/package)
        assert report is not None and not problems,(package,problems)
    metadata=json.loads((HERE.parent/"REPORT.json").read_text())
    prior_subject,issues_subject,source_subject=(x["identity"] for x in metadata["subjects"])
    assert prior_subject["reference_revision"]==v["reference_tip_at_start"]
    assert prior_subject["row_challenge_sha256"]==sha(V41/"row-challenge-v41.json")
    assert source_subject["compare_sha256"]==sha(REPORTS/SOURCE/"support/compare.py")
    assert source_subject["comparison_sha256"]==sha(REPORTS/SOURCE/"support/comparison.json")
    assert source_subject["source_report_sha256"]==sha(REPORTS/SOURCE/"REPORT.md")
    assert source_subject["source_results_sha256"]==sha(REPORTS/SOURCE/"support/source-results.json")
    assert source_subject["baseline_source_sha256"]==sha(REPORTS/SOURCE/"support/source-states/baseline.rs")
    assert source_subject["edited_source_sha256"]==sha(REPORTS/SOURCE/"support/source-states/edited.rs")
    for number in (3730,3731):
        issue=live["issues"][str(number)]
        assert issues_subject[f"issue_{number}_body_sha256"]==issue["body_sha256"]
        assert issues_subject[f"comment_{number}_sha256"]==issue["comments"][0]["body_sha256"]
    print(f"PASS: v42 333 rows, 345 links, one direct partial delta, {len(inventory)} source files and two source checkers")

if __name__=="__main__":main()
