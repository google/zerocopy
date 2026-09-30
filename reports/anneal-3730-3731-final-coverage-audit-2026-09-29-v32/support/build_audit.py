#!/usr/bin/env python3
"""Derive v32 from published v31 and the reviewed I147 syntax report."""
import csv
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V31_NAME = "anneal-3730-3731-final-coverage-audit-2026-09-29-v31"
V31 = REPORTS / V31_NAME / "support"
SOURCE = "anneal-3731-i147-syntax-equivalent-rebuild-2026-09-29"
PACKAGES = (V31_NAME, SOURCE)
DIRECT = {"I147", "C06"}
EVIDENCE_NAMES = ("REPORT.md", "REPORT.json", "support/check.py", "support/transcript.json",
                  "support/baseline-Dep.lean", "support/edited-Dep.lean",
                  "support/baseline-Dep.olean", "support/edited-Dep.olean",
                  "support/baseline-Dep.ilean", "support/edited-Dep.ilean",
                  "support/baseline-Dep.trace", "support/edited-Dep.trace",
                  "support/candidate-results.json", "support/evidence-manifest.json")

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def sha_text(value): return hashlib.sha256(value.encode()).hexdigest()
def read_csv(path):
    with path.open(newline="") as stream: return list(csv.DictReader(stream))
def write_csv(path, rows):
    with path.open("w", newline="") as stream:
        writer=csv.DictWriter(stream,fieldnames=list(rows[0]),lineterminator="\n")
        writer.writeheader();writer.writerows(rows)

def verify_live(live):
    prior=json.loads((V31/"live-issue-snapshot-v31.json").read_text())
    for n,state in ((3730,"closed"),(3731,"open")):
        x=live["issues"][str(n)];old=prior["issues"][str(n)]
        assert x["number"]==n and x["state"]==state
        assert x["body"]==old["body"] and x["body_sha256"]==sha_text(x["body"])==old["body_sha256"]
        assert len(x["comments"])==len(old["comments"])==1
        assert x["comments"][0]["id"]==old["comments"][0]["id"]
        assert x["comments"][0]["body"]==old["comments"][0]["body"]
        assert x["comments"][0]["body_sha256"]==sha_text(x["comments"][0]["body"])

def main():
    live=json.loads((HERE/"live-issue-snapshot-v32.json").read_text());verify_live(live)
    prior=json.loads((V31/"row-challenge-v31.json").read_text())
    assert len(prior)==333 and len({r["id"] for r in prior})==333
    evidence=[f"reports/{SOURCE}/{name}" for name in EVIDENCE_NAMES]
    assert all((ROOT/name).is_file() for name in evidence)
    updates={
      "I147": (
        "A pinned Lean/Lake v4.30.0-rc2 same-path fixture changed `def selected : Nat := 7` to the equal-length `def selected:Nat := 0x7`. Lake rebuilt Dep: source, ILean and trace bytes changed, and OLean mtime changed, but baseline and rebuilt 4,616-byte OLeans were byte identical (SHA-256 c363ec99438400519e766fea241aaee6b7bafc2d593f5db9fd740bb5b7e69f62). Resident, newly opened, reopened and fresh-server proof queries plus fresh batch agreed on the 7 result. A longer parenthesized edit yielded different OLean bytes despite equal goals, so semantic equivalence does not generally imply artifact byte equality. This narrows the source-changed/artifact-identical component beyond the prior comment-only case; broader timestamps, options/native/setup identities and Anneal freshness policy remain untested.",
        "One syntax-level source change with a measured byte-identical rebuilt OLean directly narrows I147; negative variants bound the inference. Product freshness policy remains open."),
      "C06": (
        "A pinned same-path Lake rebuild after a noncomment Lean syntax edit changed Dep.lean, Dep.ilean and Dep.trace, and advanced the OLean mtime while the 4,616-byte OLean remained byte identical. Resident, new, reopened and fresh direct Lean consumers plus fresh batch all accepted the same selected = 7 proof. A separate longer parenthesized edit produced different OLean bytes even though its goal/value controls agreed; this is a negative byte-identity control, not another successful same-artifact cell. Actual Anneal producer identity, source/trace/ILean ownership and publication policy remain untested.",
        "The same-source-path changed-source/identical-rebuilt-OLean cell directly exercises C06; different-OLean candidates are explicit negative controls, while Anneal handling remains open.")}
    out=[]
    for old in prior:
        row=dict(old);item=row["id"]
        if item in DIRECT:
            residual,assessment=updates[item]
            files=evidence;packages=[SOURCE];relation="direct bounded component evidence"
            review=HERE.parent.name
            assert row["v31_status"]=="partial"
        else:
            residual=row["v31_specific_remaining_delta"]
            if item=="D03":
                assessment=("The inherited v31 residual's 'no job was canceled' describes its earlier sequential source-edit/revert cell. "
                            "A separately published I080/D06 warmed incremental-on shared-target probe did cancel edited A while B waited and completed, "
                            "then retried A against the same target with selected LLBC bodies matching cold oracles. "
                            "That small component does not attest the producing Cargo unit, representative Anneal target ownership, "
                            "stage-wide cleanup or full output correctness. D03's v31 prerequisite, status and product/resource gate remain; "
                            "I147 adds no direct D03 evidence.")
            else:
                assessment=f"The I147 syntax-equivalent rebuild does not directly exercise {item} ({row['title']}); the v31 residual and prerequisite remain."
            files=[];packages=[];relation="no direct v32 evidence";review=row["v31_review_package"]
        row.update({"v32_status":row["v31_status"],"v32_gate_categories":row["v31_gate_categories"],
                    "v32_specific_remaining_delta":residual,"v32_scope_assessment":assessment,
                    "v32_review_package":review,"v32_new_evidence_packages":packages,
                    "v32_evidence_files":files,"v32_next_prerequisite":row["v31_next_prerequisite"],
                    "v32_evidence_relation":relation})
        out.append(row)
    assert {r["id"] for r in out if r["v32_specific_remaining_delta"]!=r["v31_specific_remaining_delta"]}==DIRECT
    assert all(r["v32_status"]==r["v31_status"] and r["v32_gate_categories"]==r["v31_gate_categories"] and r["v32_next_prerequisite"]==r["v31_next_prerequisite"] for r in out)
    (HERE/"row-challenge-v32.json").write_text(json.dumps(out,indent=2,sort_keys=True,ensure_ascii=False)+"\n")
    by_id={r["id"]:r for r in out}
    fields=("v32_status","v32_gate_categories","v32_specific_remaining_delta","v32_scope_assessment","v32_review_package","v32_new_evidence_packages","v32_evidence_files","v32_next_prerequisite","v32_evidence_relation")
    def extend(old_name,key,new_name):
        rows=[]
        for old in read_csv(V31/old_name):
            row=dict(old);source=by_id[row[key]]
            for field in fields:
                value=source[field];row[field]=";".join(value) if isinstance(value,list) else value
            rows.append(row)
        write_csv(HERE/new_name,rows)
        return rows
    investigations=extend("investigation-final-v31.csv","id","investigation-final-v32.csv")
    suggestions=extend("3730-crosswalk-final-v31.csv","3730_id","3730-crosswalk-final-v32.csv")
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
    write_csv(HERE/"source-package-inventory-v32.csv",inventory)
    generated=("row-challenge-v32.json","investigation-final-v32.csv","3730-crosswalk-final-v32.csv","source-package-inventory-v32.csv")
    inputs={"v31/row-challenge-v31.json":V31/"row-challenge-v31.json",
            "v31/investigation-final-v31.csv":V31/"investigation-final-v31.csv",
            "v31/3730-crosswalk-final-v31.csv":V31/"3730-crosswalk-final-v31.csv",
            "live-issue-snapshot-v32.json":HERE/"live-issue-snapshot-v32.json"}
    validation={"reference_tip_at_start":"e26a9414ab48844eeb95b91ee8b743046c8a8982",
                "source_reference_package":V31_NAME,"source_anneal_revision":"bd0956be95c5f798f0c0484921b9b9d1fc6e9988",
                "row_count":len(out),"investigation_count":len(investigations),"suggestion_count":len(suggestions),
                "suggestion_destination_links":links,
                "status_counts":{"investigations":dict(Counter(r["status"] for r in investigations)),"suggestions":dict(Counter(r["status"] for r in suggestions))},
                "changed_status_ids":[],"changed_gate_ids":[],"changed_residual_ids":sorted(DIRECT),"changed_prerequisite_ids":[],
                "direct_evidence_ids":sorted(DIRECT),"bounded_context_ids":[],"source_packages":list(PACKAGES),
                "inventory_files":len(inventory),"input_sha256":{name:sha(path) for name,path in inputs.items()},
                "generated_sha256":{name:sha(HERE/name) for name in generated}}
    (HERE/"validation-v32.json").write_text(json.dumps(validation,indent=2,sort_keys=True)+"\n")
    print(json.dumps({key:validation[key] for key in ("row_count","suggestion_destination_links","changed_residual_ids","inventory_files")},sort_keys=True))

if __name__=="__main__":main()
