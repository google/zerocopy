#!/usr/bin/env python3
"""Derive v34 directly from published v33 and two reviewed source reports."""
import csv
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V33_NAME = "anneal-3730-3731-final-coverage-audit-2026-09-29-v33"
V33 = REPORTS / V33_NAME / "support"
SOURCE = "anneal-3731-i075-warm-multiunit-test-target-2026-09-29"
PACKAGES = (V33_NAME, SOURCE)
DIRECT = {"I075", "I076"}
EVIDENCE_NAMES = ("REPORT.md", "REPORT.json", "support/check.py", "support/results.json",
                  "support/probe.py", "support/artifacts/baseline.llbc",
                  "support/artifacts/warm_repeat.llbc", "support/raw/baseline.stderr",
                  "support/raw/warm_repeat.stderr", "support/fixture/Cargo.toml",
                  "support/fixture/tests/check.rs")

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def sha_text(value): return hashlib.sha256(value.encode()).hexdigest()
def read_csv(path):
    with path.open(newline="") as stream: return list(csv.DictReader(stream))
def write_csv(path, rows):
    with path.open("w", newline="") as stream:
        writer=csv.DictWriter(stream,fieldnames=list(rows[0]),lineterminator="\n")
        writer.writeheader();writer.writerows(rows)

def verify_live(live):
    prior=json.loads((V33/"live-issue-snapshot-v33.json").read_text())
    for n,state in ((3730,"closed"),(3731,"open")):
        x=live["issues"][str(n)];old=prior["issues"][str(n)]
        assert x["number"]==n and x["state"]==state
        assert x["body"]==old["body"] and x["body_sha256"]==sha_text(x["body"])==old["body_sha256"]
        assert len(x["comments"])==len(old["comments"])==1
        assert x["comments"][0]["id"]==old["comments"][0]["id"]
        assert x["comments"][0]["body"]==old["comments"][0]["body"]
        assert x["comments"][0]["body_sha256"]==sha_text(x["comments"][0]["body"])

def main():
    live=json.loads((HERE/"live-issue-snapshot-v34.json").read_text());verify_live(live)
    prior=json.loads((V33/"row-challenge-v33.json").read_text())
    assert len(prior)==333 and len({r["id"] for r in prior})==333
    evidence=[f"reports/{SOURCE}/{name}" for name in EVIDENCE_NAMES]
    assert all((ROOT/name).is_file() for name in evidence)
    updates={
      "I075": (
        "A pinned Charon 0.1.210 dependency-free Cargo fixture ran the same unchanged-source `--test check` request twice against one retained private target, with a fresh destination pathname for the warm repeat. Full verbose stderr recorded all three Charon-producing driver invocations both times: cold library, binary, test; warm library, test, binary. Both commands exited 0 and emitted parseable error-free LLBC, so this exact warm request did not skip Charon-producing units. The cold destination identified requested test `check`, but the warm destination identified `subject_matrix_cli` despite test compilation and command success. This narrows warm multi-unit producer attestation; other targets/wrappers and Anneal's rejection of a missing or wrong producer remain untested.",
        "An unchanged-source same-target warm multi-unit request directly tests whether Charon-producing drivers rerun and whether the resulting destination identifies the requested test; the V2 wrapper policy remains open."),
      "I076": (
        "In a two-call pinned Charon `--test check` fixture, the unchanged-source warm repeat re-invoked library, test and binary Charon drivers, exited 0, and wrote a new parseable error-free LLBC at a distinct destination. That destination identified `subject_matrix_cli`, not requested test `check`; the cold baseline destination identified `check`. The observed driver order is consistent with each final crate but does not prove low-level write interleaving or a general last-writer rule. Earlier sibling, feature, profile and cfg locator collisions remain separate evidence. Full unit identity, output-owner attestation, concurrent arbitration and Anneal publication remain untested.",
        "The warm multi-unit wrong-destination cell directly adds produced-output ownership evidence to I076; it does not run an Anneal publisher or establish general writer ordering.")}
    out=[]
    for old in prior:
        row=dict(old);item=row["id"]
        if item in DIRECT:
            residual,assessment=updates[item]
            files=evidence;packages=[SOURCE];relation="direct bounded component evidence"
            review=HERE.parent.name
            assert row["v33_status"]=="partial"
        else:
            residual=row["v33_specific_remaining_delta"]
            assessment=f"The warm multi-unit Charon report does not directly exercise {item} ({row['title']}); the v33 residual and prerequisite remain."
            files=[];packages=[];relation="no direct v34 evidence";review=row["v33_review_package"]
        row.update({"v34_status":row["v33_status"],"v34_gate_categories":row["v33_gate_categories"],
                    "v34_specific_remaining_delta":residual,"v34_scope_assessment":assessment,
                    "v34_review_package":review,"v34_new_evidence_packages":packages,
                    "v34_evidence_files":files,"v34_next_prerequisite":row["v33_next_prerequisite"],
                    "v34_evidence_relation":relation})
        out.append(row)
    assert {r["id"] for r in out if r["v34_specific_remaining_delta"]!=r["v33_specific_remaining_delta"]}==DIRECT
    assert all(r["v34_status"]==r["v33_status"] and r["v34_gate_categories"]==r["v33_gate_categories"] and r["v34_next_prerequisite"]==r["v33_next_prerequisite"] for r in out)
    (HERE/"row-challenge-v34.json").write_text(json.dumps(out,indent=2,sort_keys=True,ensure_ascii=False)+"\n")
    by_id={r["id"]:r for r in out}
    fields=("v34_status","v34_gate_categories","v34_specific_remaining_delta","v34_scope_assessment","v34_review_package","v34_new_evidence_packages","v34_evidence_files","v34_next_prerequisite","v34_evidence_relation")
    def extend(old_name,key,new_name):
        rows=[]
        for old in read_csv(V33/old_name):
            row=dict(old);source=by_id[row[key]]
            for field in fields:
                value=source[field];row[field]=";".join(value) if isinstance(value,list) else value
            rows.append(row)
        write_csv(HERE/new_name,rows)
        return rows
    investigations=extend("investigation-final-v33.csv","id","investigation-final-v34.csv")
    suggestions=extend("3730-crosswalk-final-v33.csv","3730_id","3730-crosswalk-final-v34.csv")
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
    write_csv(HERE/"source-package-inventory-v34.csv",inventory)
    generated=("row-challenge-v34.json","investigation-final-v34.csv","3730-crosswalk-final-v34.csv","source-package-inventory-v34.csv")
    inputs={"v33/row-challenge-v33.json":V33/"row-challenge-v33.json",
            "v33/investigation-final-v33.csv":V33/"investigation-final-v33.csv",
            "v33/3730-crosswalk-final-v33.csv":V33/"3730-crosswalk-final-v33.csv",
            "live-issue-snapshot-v34.json":HERE/"live-issue-snapshot-v34.json"}
    validation={"reference_tip_at_start":"71fc3a50aadd50902bbbd22743ce884218af391e",
                "source_reference_package":V33_NAME,"source_anneal_revision":"bd0956be95c5f798f0c0484921b9b9d1fc6e9988",
                "row_count":len(out),"investigation_count":len(investigations),"suggestion_count":len(suggestions),
                "suggestion_destination_links":links,
                "status_counts":{"investigations":dict(Counter(r["status"] for r in investigations)),"suggestions":dict(Counter(r["status"] for r in suggestions))},
                "changed_status_ids":[],"changed_gate_ids":[],"changed_residual_ids":sorted(DIRECT),"changed_prerequisite_ids":[],
                "direct_evidence_ids":sorted(DIRECT),"bounded_context_ids":[],"source_packages":list(PACKAGES),
                "inventory_files":len(inventory),"input_sha256":{name:sha(path) for name,path in inputs.items()},
                "generated_sha256":{name:sha(HERE/name) for name in generated}}
    (HERE/"validation-v34.json").write_text(json.dumps(validation,indent=2,sort_keys=True)+"\n")
    print(json.dumps({key:validation[key] for key in ("row_count","suggestion_destination_links","changed_residual_ids","inventory_files")},sort_keys=True))

if __name__=="__main__":main()
