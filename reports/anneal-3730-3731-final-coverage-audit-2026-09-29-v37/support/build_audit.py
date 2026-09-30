#!/usr/bin/env python3
"""Derive v37 directly from published v36 and the reviewed I080 full-field report."""
import csv
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V36_NAME = "anneal-3730-3731-final-coverage-audit-2026-09-29-v36"
V36 = REPORTS / V36_NAME / "support"
SOURCE = "anneal-3731-i080-full-field-cancel-oracle-2026-09-29"
PACKAGES = (V36_NAME, SOURCE)
DIRECT = {"I080", "D03", "D06"}
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
    prior=json.loads((V36/"live-issue-snapshot-v36.json").read_text())
    for n,state in ((3730,"closed"),(3731,"open")):
        x=live["issues"][str(n)];old=prior["issues"][str(n)]
        assert x["number"]==n and x["state"]==state
        assert x["body"]==old["body"] and x["body_sha256"]==sha_text(x["body"])==old["body_sha256"]
        assert len(x["comments"])==len(old["comments"])==1
        assert x["comments"][0]["id"]==old["comments"][0]["id"]
        assert x["comments"][0]["body"]==old["comments"][0]["body"]
        assert x["comments"][0]["body_sha256"]==sha_text(x["comments"][0]["body"])

def main():
    live=json.loads((HERE/"live-issue-snapshot-v37.json").read_text());verify_live(live)
    prior=json.loads((V36/"row-challenge-v36.json").read_text())
    assert len(prior)==333 and len({r["id"] for r in prior})==333
    evidence=[f"reports/{SOURCE}/{name}" for name in EVIDENCE_NAMES]
    assert all((ROOT/name).is_file() for name in evidence)
    updates={
      "I080": (
        "The warmed CARGO_INCREMENTAL=1 shared-target schedule remains: edited A was SIGTERM-canceled after its build-script marker while unchanged B waited on the Cargo build-directory lock and completed; same-target retry A completed, and canceled A left no LLBC at its distinct destination. Offline full-field comparison of retained LLBCs now shows that prewarm A, prewarm B and companion B each differ from their same source-state cold baseline B oracle, and recovered A from its cold edited A oracle, only in the requested destination path, generated-file local path and positional short_names order; typed-key/name maps agree. An edited-versus-baseline cold-oracle control detects the source/body change including literal 2 versus 1. These are decoded JSON observations for four completed outputs, not byte identity or semantic equivalence. Lock ownership timing, stage-wide descendant cleanup, path-sensitive output provenance, representative resource cost and Anneal transactional publication remain untested.",
        "Direct retained-output full-field comparison narrows the v36 output-identity residual; the cancellation mechanics, representative resource gate and Anneal ownership limits remain."),
      "D03": (
        "The prior private/shared cold/warm incremental matrix and sequential shared-target source edit/revert controls remain. Retained warmed cancellation/retry outputs now have a full decoded-field comparison: prewarm A, prewarm B and companion B against same source-state cold baseline B, and recovered A against cold edited A, differ only in destination path, generated-file local path and positional short_names order, with equal typed-key/name maps. The edited-versus-baseline oracle control detects a source/body change including literal 2 versus 1. This one tiny canceled-A/companion-B/retry-A schedule does not attest the complete Charon-producing Cargo unit, byte-identical or semantically equivalent LLBC, path-insensitive keys, representative Anneal target ownership, dirty shared/private workloads or a product publication policy.",
        "Direct full-field retained-output evidence strengthens the bounded Cargo reuse component; the v36 product/resource gates and producing-unit prerequisite remain."),
      "D06": (
        "An incremental-on shared-target Charon pair canceled edited A after its build-script marker while B remained live and logged a build-directory lock wait; B completed, canceled A left no LLBC, and same-target retry A completed. For the four retained completed same source-state outputs, full decoded-field comparison with cold oracles finds only destination path, generated-file local path and positional short_names order differences; typed-key/name maps agree. An edited-versus-baseline control detects source/body change including literal 2 versus 1. Selected process groups had no non-zombie members at one post-run sample and the private work tree was removed. The offline comparison does not add a cancellation schedule or resolve lock timing, all-stage cleanup, escaped descendants, repeated failures, last-good transactional publication, representative resources or an Anneal owner.",
        "Direct full-field comparison strengthens completed-output checks in the existing cancellation schedule; mechanics and the v36 product/resource gates remain.")}
    out=[]
    for old in prior:
        row=dict(old);item=row["id"]
        if item in DIRECT:
            residual,assessment=updates[item]
            files=evidence;packages=[SOURCE];relation="direct bounded retained-output evidence"
            review=HERE.parent.name
            assert row["v36_status"]=="partial"
        else:
            residual=row["v36_specific_remaining_delta"]
            assessment=f"The I080 retained-output comparison does not directly exercise {item} ({row['title']}); the v36 residual and prerequisite remain."
            files=[];packages=[];relation="no direct v37 evidence";review=row["v36_review_package"]
        row.update({"v37_status":row["v36_status"],"v37_gate_categories":row["v36_gate_categories"],
                    "v37_specific_remaining_delta":residual,"v37_scope_assessment":assessment,
                    "v37_review_package":review,"v37_new_evidence_packages":packages,
                    "v37_evidence_files":files,"v37_next_prerequisite":row["v36_next_prerequisite"],
                    "v37_evidence_relation":relation})
        out.append(row)
    assert {r["id"] for r in out if r["v37_specific_remaining_delta"]!=r["v36_specific_remaining_delta"]}==DIRECT
    assert all(r["v37_status"]==r["v36_status"] and r["v37_gate_categories"]==r["v36_gate_categories"] and r["v37_next_prerequisite"]==r["v36_next_prerequisite"] for r in out)
    (HERE/"row-challenge-v37.json").write_text(json.dumps(out,indent=2,sort_keys=True,ensure_ascii=False)+"\n")
    by_id={r["id"]:r for r in out}
    fields=("v37_status","v37_gate_categories","v37_specific_remaining_delta","v37_scope_assessment","v37_review_package","v37_new_evidence_packages","v37_evidence_files","v37_next_prerequisite","v37_evidence_relation")
    def extend(old_name,key,new_name):
        rows=[]
        for old in read_csv(V36/old_name):
            row=dict(old);source=by_id[row[key]]
            for field in fields:
                value=source[field];row[field]=";".join(value) if isinstance(value,list) else value
            rows.append(row)
        write_csv(HERE/new_name,rows)
        return rows
    investigations=extend("investigation-final-v36.csv","id","investigation-final-v37.csv")
    suggestions=extend("3730-crosswalk-final-v36.csv","3730_id","3730-crosswalk-final-v37.csv")
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
    write_csv(HERE/"source-package-inventory-v37.csv",inventory)
    generated=("row-challenge-v37.json","investigation-final-v37.csv","3730-crosswalk-final-v37.csv","source-package-inventory-v37.csv")
    inputs={"v36/row-challenge-v36.json":V36/"row-challenge-v36.json",
            "v36/investigation-final-v36.csv":V36/"investigation-final-v36.csv",
            "v36/3730-crosswalk-final-v36.csv":V36/"3730-crosswalk-final-v36.csv",
            "live-issue-snapshot-v37.json":HERE/"live-issue-snapshot-v37.json"}
    validation={"reference_tip_at_start":"52b16195ee71b52b936476b2efd6da2e49622cd0",
                "source_reference_package":V36_NAME,"source_anneal_revision":"bd0956be95c5f798f0c0484921b9b9d1fc6e9988",
                "row_count":len(out),"investigation_count":len(investigations),"suggestion_count":len(suggestions),
                "suggestion_destination_links":links,
                "status_counts":{"investigations":dict(Counter(r["status"] for r in investigations)),"suggestions":dict(Counter(r["status"] for r in suggestions))},
                "changed_status_ids":[],"changed_gate_ids":[],"changed_residual_ids":sorted(DIRECT),"changed_prerequisite_ids":[],
                "direct_evidence_ids":sorted(DIRECT),"bounded_context_ids":[],"source_packages":list(PACKAGES),
                "inventory_files":len(inventory),"input_sha256":{name:sha(path) for name,path in inputs.items()},
                "generated_sha256":{name:sha(HERE/name) for name in generated}}
    (HERE/"validation-v37.json").write_text(json.dumps(validation,indent=2,sort_keys=True)+"\n")
    print(json.dumps({key:validation[key] for key in ("row_count","suggestion_destination_links","changed_residual_ids","inventory_files")},sort_keys=True))

if __name__=="__main__":main()
