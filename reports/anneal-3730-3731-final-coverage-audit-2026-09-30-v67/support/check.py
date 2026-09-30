#!/usr/bin/env python3
"""Offline v67 checker: all inherited rows, exact crosswalk, bounded sources."""
import csv
import hashlib
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
REPORTS = ROOT / "reports"
V66 = REPORTS / "anneal-3730-3731-final-coverage-audit-2026-09-30-v66" / "support"
SOURCE = REPORTS / "anneal-3731-source-spec-synthesis-2026-09-30"
FIELDS = ("v67_status", "v67_gate_categories", "v67_specific_remaining_delta",
          "v67_scope_assessment", "v67_review_package", "v67_new_evidence_packages",
          "v67_evidence_files", "v67_next_prerequisite", "v67_evidence_relation", "v67_linked_source_ids")

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def rows(path):
    with path.open(newline="") as f:
        return list(csv.DictReader(f))

def main():
    v = json.loads((HERE / "validation-v67.json").read_text())
    mapping = json.loads((SOURCE / "support/id-map.json").read_text())
    assert v["reference_tip_at_start"] == "ebcdcadb63fefd1e6c0f46cb2030270ae3232837"
    assert v["v66_published_git_parent"] == "0c504d98f5abafcbbd1460738e6d753378a6460e"
    assert v["v66_ledger_source_commit"] == "57155f6541e478f201ae47d8a27da2f3d448df5e"
    assert v["v65_issue_snapshot_reused"] is True
    assert (v["row_count"],v["investigation_count"],v["suggestion_count"],v["suggestion_destination_links"],v["source_report_count"]) == (333,159,174,345,41)
    assert v["changed_status_ids"] == v["changed_gate_ids"] == v["changed_prerequisite_ids"] == v["changed_residual_ids"] == []
    assert v["mapped_investigation_ids"] == sorted(x for x,y in mapping.items() if y)
    assert v["no_new_id_specific_evidence_ids"] == sorted(x for x,y in mapping.items() if not y)
    assert set(v["no_new_id_specific_evidence_ids"]) == {"I057","I059","I061","I062"}
    for key,value in v["input_sha256"].items():
        p = V66 / key[4:] if key.startswith("v66/") else SOURCE / "support" / key[7:]
        assert sha(p) == value, key
    for key,value in v["generated_sha256"].items():
        assert sha(HERE / key) == value, key
    assert (HERE / "live-issue-snapshot-v67.json").read_bytes() == (V66 / "live-issue-snapshot-v66.json").read_bytes()
    old = json.loads((V66 / "row-challenge-v66.json").read_text())
    new = json.loads((HERE / "row-challenge-v67.json").read_text())
    assert len(old) == len(new) == 333 and [r["id"] for r in old] == [r["id"] for r in new]
    cross_old = rows(V66 / "3730-crosswalk-final-v66.csv")
    destinations = {r["3730_id"]: r["3731_destinations"].split(";") for r in cross_old}
    assert len(destinations) == 174 and sum(len(x) for x in destinations.values()) == 345
    context = []
    for prior,row in zip(old,new):
        item = row["id"]
        assert all(row[k] == value for k,value in prior.items()), item
        assert (row["v67_status"],row["v67_gate_categories"],row["v67_specific_remaining_delta"],row["v67_next_prerequisite"]) == (prior["v66_status"],prior["v66_gate_categories"],prior["v66_specific_remaining_delta"],prior["v66_next_prerequisite"]), item
        linked = ([item] if item in mapping and mapping[item] else [x for x in destinations.get(item,[]) if mapping.get(x)])
        assert row["v67_linked_source_ids"] == linked, item
        if linked:
            assert row["v67_new_evidence_packages"] == [SOURCE.name]
            assert row["v67_evidence_files"] == [f"reports/{SOURCE.name}/REPORT.md", f"reports/{SOURCE.name}/support/id-map.json"]
            assert row["v67_review_package"] == HERE.parent.name
            assert all((ROOT / p).is_file() for p in row["v67_evidence_files"])
            if prior["kind"] == "suggestion":context.append(item)
        else:
            assert row["v67_new_evidence_packages"] == row["v67_evidence_files"] == []
            assert row["v67_review_package"] == prior["v66_review_package"]
        if item in v["no_new_id_specific_evidence_ids"]:
            assert row["v67_evidence_relation"] == "no new ID-specific source evidence"
    assert context == v["context_suggestion_ids"] and len(context) == 48
    for current,previous,key,count in (("investigation-final-v67.csv","investigation-final-v66.csv","id",159),
                                       ("3730-crosswalk-final-v67.csv","3730-crosswalk-final-v66.csv","3730_id",174)):
        a,b=rows(HERE/current),rows(V66/previous)
        assert len(a)==len(b)==count and [r[key] for r in a]==[r[key] for r in b]
        by_id={r["id"]:r for r in new}
        for x,y in zip(a,b):
            assert all(x[k]==value for k,value in y.items()),x[key]
            source=by_id[x[key]]
            for field in FIELDS:
                value=source[field]
                assert x[field]==(";".join(value) if isinstance(value,list) else value), (x[key],field)
            assert x["status"]==x["v67_status"]
    inventory=rows(HERE/"source-package-inventory-v67.csv")
    assert len(inventory)==v["inventory_files"]
    expected=[]
    for package in (V66.parent.name,SOURCE.name):
        for p in sorted((REPORTS/package).rglob("*")):
            if p.is_file() and "__pycache__" not in p.parts and p.suffix!=".pyc":expected.append(p.relative_to(ROOT).as_posix())
    assert [r["path"] for r in inventory]==expected
    assert all(sha(ROOT/r["path"])==r["sha256"] and (ROOT/r["path"]).stat().st_size==int(r["size"]) for r in inventory)
    meta=json.loads((HERE.parent/"REPORT.json").read_text())
    assert meta["subjects"][0]["identity"]["reference_parent"]==v["reference_tip_at_start"]
    assert meta["subjects"][0]["identity"]["v66_published_git_parent"]==v["v66_published_git_parent"]
    assert meta["subjects"][1]["identity"]["id_map_sha256"]==sha(SOURCE/"support/id-map.json")
    assert meta["subjects"][2]["identity"]["snapshot_sha256"]==sha(HERE/"live-issue-snapshot-v67.json")
    assert "0c504d98f5abafcbbd1460738e6d753378a6460e" in (HERE.parent/"REPORT.md").read_text()
    proc=subprocess.run([sys.executable,"-B","support/check.py"],cwd=SOURCE,capture_output=True,text=True,timeout=15)
    assert proc.returncode==0 and "PASS: 41 source packages" in proc.stdout,(proc.stdout,proc.stderr)
    print("PASS: v67 inherited 333 rows, 345 links, 41 sources, 23-ID scope and lineage")

if __name__=="__main__":main()
