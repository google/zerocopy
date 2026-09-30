#!/usr/bin/env python3
"""Offline v43 audit checker: inherited rows, live scope, inventory and sources."""
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
V42=REPORTS/"anneal-3730-3731-final-coverage-audit-2026-09-29-v42"/"support"
DIRECT={"I043","C02"}
SOURCE="anneal-3731-lake-nested-constructor-goal-positions-v4-30-0-rc2"
FIELDS=("v43_status","v43_gate_categories","v43_specific_remaining_delta","v43_scope_assessment",
        "v43_review_package","v43_new_evidence_packages","v43_evidence_files",
        "v43_next_prerequisite","v43_evidence_relation")

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def rows(path):
    with path.open(newline="") as stream:return list(csv.DictReader(stream))

def main():
    v=json.loads((HERE/"validation-v43.json").read_text())
    assert v["reference_tip_at_start"]=="29ea19d9dccef4f046d0b53eed0e8dc20b9c9ae7"
    assert v["source_reference_package"]==V42.parent.name
    assert v["source_anneal_revision"]=="bd0956be95c5f798f0c0484921b9b9d1fc6e9988"
    assert (v["row_count"],v["investigation_count"],v["suggestion_count"],v["suggestion_destination_links"])==(333,159,174,345)
    assert v["status_counts"]=={"investigations":{"complete":4,"partial":151,"not-run":1,"conditional":3},
                                "suggestions":{"complete":3,"partial":162,"not-run":5,"conditional":4}}
    assert set(v["changed_residual_ids"])==set(v["direct_evidence_ids"])==DIRECT
    assert v["changed_status_ids"]==v["changed_gate_ids"]==v["changed_prerequisite_ids"]==[]
    assert v["bounded_context_ids"]==[]
    for name,expected in v["input_sha256"].items():
        path=V42/name[4:] if name.startswith("v42/") else HERE/name
        assert sha(path)==expected,name
    for name,expected in v["generated_sha256"].items():assert sha(HERE/name)==expected,name

    old=json.loads((V42/"row-challenge-v42.json").read_text())
    current=json.loads((HERE/"row-challenge-v43.json").read_text())
    assert len(old)==len(current)==333 and len({r["id"] for r in current})==333
    by_id={r["id"]:r for r in current}
    for before,row in zip(old,current):
        item=row["id"]
        assert all(row[k]==value for k,value in before.items()),item
        assert row["v43_status"]==row["v42_status"] and row["v43_gate_categories"]==row["v42_gate_categories"]
        assert row["v43_next_prerequisite"]==row["v42_next_prerequisite"]
        assert row["v43_scope_assessment"] and row["v43_specific_remaining_delta"]
        assert all((ROOT/path).is_file() for path in row["v43_evidence_files"]),item
        if item in DIRECT:
            assert row["v43_status"]=="partial" and row["v43_review_package"]==HERE.parent.name
            assert row["v43_new_evidence_packages"]==[SOURCE] and len(row["v43_evidence_files"])==7
            assert row["v43_specific_remaining_delta"]!=row["v42_specific_remaining_delta"]
            assert row["v43_evidence_relation"]=="direct bounded Lake proofstate evidence"
        else:
            assert row["v43_specific_remaining_delta"]==row["v42_specific_remaining_delta"]
            assert row["v43_review_package"]==row["v42_review_package"]
            assert row["v43_new_evidence_packages"]==row["v43_evidence_files"]==[]
            assert "v42 residual and prerequisite remain" in row["v43_scope_assessment"]
            assert row["v43_evidence_relation"]=="no direct v43 evidence"
    assert {r["id"] for r in current if r["v43_specific_remaining_delta"]!=r["v42_specific_remaining_delta"]}==DIRECT
    for item in DIRECT:
        residual=by_id[item]["v43_specific_remaining_delta"]
        for phrase in ("13", "constructor", "two-bullet", "inner-have", "plainGoal/getInteractiveGoals",
                       "batch", "protocol transcript or lifecycle coverage", "whitespace", "term-proof",
                       "worker restart/reconnect", "RPC reconnect", "reference dereference/expiry" if item=="I043" else "object dereference/expiry",
                       "exact-version/import fencing", "Anneal", "Rust source map", "editor/MCP"):
            assert phrase in residual,(item,phrase)
        assert by_id[item]["v43_status"]=="partial" and by_id[item]["v43_gate_categories"]==["product"]
    assert "two left/right goals" in by_id["I043"]["v43_specific_remaining_delta"]
    assert "case names" in by_id["C02"]["v43_specific_remaining_delta"]
    for item in ("I079","I080","I083","I084","D03","E11","D06","I075","I076"):
        assert by_id[item]["v43_specific_remaining_delta"]==by_id[item]["v42_specific_remaining_delta"]

    for new,old_name,key,count in (("investigation-final-v43.csv","investigation-final-v42.csv","id",159),
                                   ("3730-crosswalk-final-v43.csv","3730-crosswalk-final-v42.csv","3730_id",174)):
        before=rows(V42/old_name);now=rows(HERE/new)
        assert len(before)==len(now)==count and [r[key] for r in before]==[r[key] for r in now]
        for a,b in zip(before,now):
            assert all(b[field]==value for field,value in a.items()),b[key]
            item=by_id[b[key]]
            assert b["status"]==b["v43_status"]==item["v43_status"]
            for field in FIELDS:
                value=item[field]
                assert b[field]==(";".join(value) if isinstance(value,list) else value),(b[key],field)

    live=json.loads((HERE/"live-issue-snapshot-v43.json").read_text())
    prev=json.loads((V42/"live-issue-snapshot-v42.json").read_text())
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
    investigations=rows(HERE/"investigation-final-v43.csv")
    suggestions=rows(HERE/"3730-crosswalk-final-v43.csv")
    assert len(titles)==159 and len(cross)==174
    assert all(r["title"]==titles[r["id"]] for r in investigations)
    assert all(r["suggestion"]==cross[r["3730_id"]][0] and set(r["3731_destinations"].split(";"))==cross[r["3730_id"]][1] for r in suggestions)
    assert sum(len(destinations) for _,destinations in cross.values())==345

    inventory=rows(HERE/"source-package-inventory-v43.csv")
    assert len(inventory)==v["inventory_files"] and len({r["path"] for r in inventory})==len(inventory)
    expected={path.relative_to(ROOT).as_posix() for package in v["source_packages"]
              for path in (REPORTS/package).rglob("*") if path.is_file() and "__pycache__" not in path.parts and path.suffix!=".pyc"}
    assert {r["path"] for r in inventory}==expected
    for row in inventory:assert sha(ROOT/row["path"])==row["sha256"],row["path"]
    assert v["source_packages"]==[V42.parent.name,SOURCE]
    for package in v["source_packages"]:
        path=REPORTS/package
        result=subprocess.run([sys.executable,"-B",str(path/"support/check.py")],cwd=ROOT,capture_output=True,text=True,timeout=120)
        assert result.returncode==0,(package,result.stdout,result.stderr)

    spec=importlib.util.spec_from_file_location("reference",ROOT/"tools/reference.py")
    reference=importlib.util.module_from_spec(spec);sys.modules[spec.name]=reference;spec.loader.exec_module(reference)
    for package in (V42.parent.name,SOURCE,HERE.parent.name):
        report,problems=reference._load_report(REPORTS/package)
        assert report is not None and not problems,(package,problems)
    metadata=json.loads((HERE.parent/"REPORT.json").read_text())
    prior_subject,issues_subject,source_subject=(x["identity"] for x in metadata["subjects"])
    assert prior_subject["reference_revision"]==v["reference_tip_at_start"]
    assert prior_subject["row_challenge_sha256"]==sha(V42/"row-challenge-v42.json")
    assert source_subject["source_report_sha256"]==sha(REPORTS/SOURCE/"REPORT.md")
    assert source_subject["results_sha256"]==sha(REPORTS/SOURCE/"support/results.json")
    assert source_subject["probe_sha256"]==sha(REPORTS/SOURCE/"support/probe.py")
    assert source_subject["revision"]=="3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc"
    for number in (3730,3731):
        issue=live["issues"][str(number)]
        assert issues_subject[f"issue_{number}_body_sha256"]==issue["body_sha256"]
        assert issues_subject[f"comment_{number}_sha256"]==issue["comments"][0]["body_sha256"]
    print(f"PASS: v43 333 rows, 345 links, two direct partial deltas, {len(inventory)} source files and two source checkers")

if __name__=="__main__":main()
