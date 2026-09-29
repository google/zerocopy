#!/usr/bin/env python3
"""Read-only offline v30 checker for all inherited rows and source evidence."""
import csv
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

HERE=Path(__file__).resolve().parent
REPORTS=HERE.parents[1]
ROOT=REPORTS.parent
V29=REPORTS/"anneal-3730-3731-final-coverage-audit-2026-09-29-v29"/"support"
V22=REPORTS/"anneal-3730-3731-final-coverage-audit-2026-09-29-v22"/"support"
CANCEL="anneal-3731-i080-incremental-on-shared-target-cancel-recovery-2026-09-29"
INVENTORY="anneal-3731-i094-installed-lean-lake-inventory-2026-09-29"
CONSUMERS="anneal-3731-two-concurrent-fresh-cache-goal-consumers-2026-09-29"
CHANGED={"I080","I089","I094","D06","F13"}
CONTEXT={"D03","F03","M01","F02","F04","F08","F20","I04","I092","I099","I114","I139","I078","I105"}
PACKAGES={"I080":[CANCEL],"D06":[CANCEL],"I094":[INVENTORY],"I089":[CONSUMERS],"F13":[CONSUMERS]}

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def rows(path):
    with path.open(newline="") as stream:return list(csv.DictReader(stream))

def main():
    v=json.loads((HERE/"validation-v30.json").read_text())
    assert v["reference_tip_at_start"]=="40b3024d5a3c73357abb6e90f10fcaf713768cd4"
    assert v["source_reference_package"]==V29.parent.name
    assert v["source_anneal_revision"]=="bd0956be95c5f798f0c0484921b9b9d1fc6e9988"
    assert (v["row_count"],v["investigation_count"],v["suggestion_count"],v["suggestion_destination_links"])==(333,159,174,345)
    assert v["changed_status_ids"]==v["changed_gate_ids"]==[]
    assert set(v["changed_residual_ids"])==set(v["changed_prerequisite_ids"])==set(v["direct_evidence_ids"])==CHANGED
    assert set(v["bounded_context_ids"])==CONTEXT
    assert v["status_counts"]=={"investigations":{"complete":4,"partial":151,"not-run":1,"conditional":3},
                                "suggestions":{"complete":3,"partial":162,"not-run":5,"conditional":4}}
    for name,expected in v["input_sha256"].items():
        path=V29/name[4:] if name.startswith("v29/") else V22/name[4:] if name.startswith("v22/") else HERE/name
        assert sha(path)==expected,name
    for name,expected in v["generated_sha256"].items():assert sha(HERE/name)==expected,name

    prior=json.loads((V29/"row-challenge-v29.json").read_text())
    current=json.loads((HERE/"row-challenge-v30.json").read_text())
    assert len(prior)==len(current)==333 and len({r["id"] for r in current})==333
    by_id={r["id"]:r for r in current}
    for old,row in zip(prior,current):
        item=row["id"]
        assert all(row[key]==value for key,value in old.items()),item
        assert row["v30_status"]==row["v29_status"] and row["v30_gate_categories"]==row["v29_gate_categories"]
        assert row["v30_specific_remaining_delta"] and row["v30_scope_assessment"] and row["v30_next_prerequisite"]
        assert all((ROOT/path).is_file() for path in row["v30_evidence_files"]),item
        if item in CHANGED:
            assert row["v30_status"]=="partial" and row["v30_review_package"]==HERE.parent.name
            assert row["v30_new_evidence_packages"]==PACKAGES[item] and row["v30_evidence_files"]
            assert row["v30_specific_remaining_delta"]!=row["v29_specific_remaining_delta"]
            assert row["v30_next_prerequisite"]!=row["v29_next_prerequisite"]
            assert row["v30_evidence_relation"]=="direct bounded component evidence"
        else:
            assert row["v30_specific_remaining_delta"]==row["v29_specific_remaining_delta"]
            assert row["v30_next_prerequisite"]==row["v29_next_prerequisite"]
            assert row["v30_review_package"]==row["v29_review_package"]
            assert row["v30_new_evidence_packages"]==row["v30_evidence_files"]==[]
            assert "v29 residual and prerequisite remain" in row["v30_scope_assessment"]
            assert row["v30_evidence_relation"]==("bounded context only" if item in CONTEXT else "no direct v30 evidence")
    assert {r["id"] for r in current if r["v30_specific_remaining_delta"]!=r["v29_specific_remaining_delta"]}==CHANGED
    assert {r["id"] for r in current if r["v30_next_prerequisite"]!=r["v29_next_prerequisite"]}==CHANGED
    assert "A left no LLBC" in by_id["I080"]["v30_specific_remaining_delta"]
    assert "No later compatible installed tuple" in by_id["I094"]["v30_specific_remaining_delta"]
    assert "Two independent source-only Lake consumer roots" in by_id["I089"]["v30_specific_remaining_delta"]
    assert "An incremental-on shared-target Charon pair" in by_id["D06"]["v30_specific_remaining_delta"]
    assert "two tiny consumers" in by_id["F13"]["v30_specific_remaining_delta"]
    assert by_id["F03"]["v30_specific_remaining_delta"]==by_id["F03"]["v29_specific_remaining_delta"]
    assert by_id["F02"]["v30_specific_remaining_delta"]==by_id["F02"]["v29_specific_remaining_delta"]

    for filename,key,count in (("investigation-final-v30.csv","id",159),("3730-crosswalk-final-v30.csv","3730_id",174)):
        before=rows(V29/filename.replace("-v30","-v29"));now=rows(HERE/filename)
        assert len(before)==len(now)==count and [r[key] for r in before]==[r[key] for r in now]
        for old,row in zip(before,now):
            assert all(row[field]==value for field,value in old.items()),row[key]
            choice=by_id[row[key]]
            assert row["status"]==row["v30_status"]==choice["v30_status"]
            for field in ("v30_status","v30_gate_categories","v30_specific_remaining_delta","v30_scope_assessment","v30_review_package","v30_new_evidence_packages","v30_evidence_files","v30_next_prerequisite","v30_evidence_relation"):
                value=choice[field]
                assert row[field]==(";".join(value) if isinstance(value,list) else value),(row[key],field)

    live=json.loads((HERE/"live-issue-snapshot-v30.json").read_text())
    frozen=json.loads((V22/"issue-scope-snapshot.json").read_text())
    prior_live=json.loads((V29/"live-issue-snapshot-v29.json").read_text())["issues"]
    assert live["source"]=="public GitHub REST issue and comments endpoints"
    assert live["fetched_at_utc"].startswith("2026-09-29T")
    for number,state,comment_id in ((3730,"closed",5884380373),(3731,"open",5884299718)):
        key=str(number);item=live["issues"][key]
        assert item["number"]==number and item["state"]==state and item["updated_at"]==prior_live[key]["updated_at"]
        assert item["body"]==frozen[key]["body"]==prior_live[key]["body"]
        assert item["body_sha256"]==hashlib.sha256(item["body"].encode()).hexdigest()==prior_live[key]["body_sha256"]
        assert len(item["comments"])==1 and item["comments"][0]["id"]==comment_id
        comment=item["comments"][0];old=prior_live[key]["comments"][0]
        assert comment["updated_at"]==old["updated_at"] and comment["body"]==frozen[key]["comments"][0]["body"]==old["body"]
        assert comment["body_sha256"]==hashlib.sha256(comment["body"].encode()).hexdigest()==old["body_sha256"]
    body=live["issues"]["3731"]["body"];comment=live["issues"]["3731"]["comments"][0]["body"]
    titles={item:re.sub(r"\s*\[[^]]+\]\.?$","",title).strip() for source in (body,comment)
            for item,title in re.findall(r"(?m)^\*\*(I\d{3})\s+[—.]\s+([^\n]*?)\*\*",source)}
    cross={item:(title.strip(),set(re.findall(r"I\d{3}",destinations))) for item,title,destinations in
           re.findall(r"(?m)^\| ([A-O]\d{2}) \| ([^|]+) \| ([^|]+) \|",comment)}
    investigation=rows(HERE/"investigation-final-v30.csv")
    suggestions=rows(HERE/"3730-crosswalk-final-v30.csv")
    assert len(titles)==159 and len(cross)==174
    assert all(r["title"]==titles[r["id"]] for r in investigation)
    assert all(r["suggestion"]==cross[r["3730_id"]][0] and set(r["3731_destinations"].split(";"))==cross[r["3730_id"]][1] for r in suggestions)
    assert sum(len(destinations) for _,destinations in cross.values())==345

    inventory=rows(HERE/"source-package-inventory-v30.csv")
    assert len(inventory)==v["inventory_files"] and len({r["path"] for r in inventory})==len(inventory)
    expected_paths={path.relative_to(ROOT).as_posix() for package in v["source_packages"]
                    for path in (REPORTS/package).rglob("*")
                    if path.is_file() and "__pycache__" not in path.parts and path.suffix!=".pyc"}
    assert {r["path"] for r in inventory}==expected_paths
    for row in inventory:assert sha(ROOT/row["path"])==row["sha256"],row["path"]
    for package in v["source_packages"]:
        path=REPORTS/package
        assert (path/"REPORT.md").is_file() and (path/"REPORT.json").is_file()
        result=subprocess.run([sys.executable,"-B",str(path/"support/check.py")],cwd=ROOT,capture_output=True,text=True,timeout=120)
        assert result.returncode==0,(package,result.stdout,result.stderr)
    print(f"PASS: v30 333 rows, 345 links, five direct partial deltas, {len(CONTEXT)} context-only exclusions, {len(inventory)} source files and four source checkers")

if __name__=="__main__":main()
