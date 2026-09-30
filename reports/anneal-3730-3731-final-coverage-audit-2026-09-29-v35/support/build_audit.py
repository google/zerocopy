#!/usr/bin/env python3
"""Derive v35 directly from published v34 and one reviewed source report."""
import csv
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V34_NAME = "anneal-3730-3731-final-coverage-audit-2026-09-29-v34"
V34 = REPORTS / V34_NAME / "support"
SOURCE = "anneal-3731-i075-warm-bin-target-2026-09-29"
PACKAGES = (V34_NAME, SOURCE)
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
    prior=json.loads((V34/"live-issue-snapshot-v34.json").read_text())
    for n,state in ((3730,"closed"),(3731,"open")):
        x=live["issues"][str(n)];old=prior["issues"][str(n)]
        assert x["number"]==n and x["state"]==state
        assert x["body"]==old["body"] and x["body_sha256"]==sha_text(x["body"])==old["body_sha256"]
        assert len(x["comments"])==len(old["comments"])==1
        assert x["comments"][0]["id"]==old["comments"][0]["id"]
        assert x["comments"][0]["body"]==old["comments"][0]["body"]
        assert x["comments"][0]["body_sha256"]==sha_text(x["comments"][0]["body"])

def main():
    live=json.loads((HERE/"live-issue-snapshot-v35.json").read_text());verify_live(live)
    prior=json.loads((V34/"row-challenge-v34.json").read_text())
    assert len(prior)==333 and len({r["id"] for r in prior})==333
    evidence=[f"reports/{SOURCE}/{name}" for name in EVIDENCE_NAMES]
    assert all((ROOT/name).is_file() for name in evidence)
    updates={
      "I075": (
        "A second pinned Charon 0.1.210 unchanged-source same-target repeat selected `--bin subject_matrix_cli` rather than v34's `--test check`. The retained target did not provide a cache-fresh warm cell: Cargo logged `Dirty subject_matrix ... couldn't read metadata for ... libsubject_matrix-....rlib`, then recompiled the library and binary. Both calls invoked those Charon drivers, exited 0, and created parseable error-free LLBC at distinct initially absent destinations; each identified requested binary `subject_matrix_cli`. This directly attests driver invocation and matching output under a dirty rebuild, not producer behavior when Cargo considers the cached unit Fresh. The v34 warm test destination contained the binary despite test compilation. Cache-fresh skip handling, other targets/wrappers and Anneal producer-attestation/rejection remain untested.",
        "An explicit selected-binary retained-target control directly shows Charon driver invocation after Cargo judged a dependency dirty; cache-fresh producer behavior and the Anneal wrapper policy remain open."),
      "I076": (
        "The new pinned `--bin subject_matrix_cli` cold/retained-target pair used unchanged source and distinct initially absent output paths. Cargo judged the second call dirty because it could not read metadata for the cached `libsubject_matrix-....rlib`, then invoked library and binary Charon drivers. Both calls emitted error-free LLBC whose decoded crate matched the requested binary. This positive selected-output control contrasts with v34's retained-target `--test check` mismatch, where the destination contained the binary after test compilation; neither pair establishes cache-fresh output behavior. Raw LLBC hashes differ without an established semantic difference. Complete compilation-unit identity, producer ownership, writer ordering, collision rejection and Anneal publication remain untested.",
        "The selected-binary output matches its requested crate under the observed dirty rebuild, bounding the earlier test-target mismatch without proving cache-fresh or complete output ownership.")}
    out=[]
    for old in prior:
        row=dict(old);item=row["id"]
        if item in DIRECT:
            residual,assessment=updates[item]
            files=evidence;packages=[SOURCE];relation="direct bounded component evidence"
            review=HERE.parent.name
            assert row["v34_status"]=="partial"
        else:
            residual=row["v34_specific_remaining_delta"]
            assessment=f"The warm selected-binary Charon report does not directly exercise {item} ({row['title']}); the v34 residual and prerequisite remain."
            files=[];packages=[];relation="no direct v35 evidence";review=row["v34_review_package"]
        row.update({"v35_status":row["v34_status"],"v35_gate_categories":row["v34_gate_categories"],
                    "v35_specific_remaining_delta":residual,"v35_scope_assessment":assessment,
                    "v35_review_package":review,"v35_new_evidence_packages":packages,
                    "v35_evidence_files":files,"v35_next_prerequisite":row["v34_next_prerequisite"],
                    "v35_evidence_relation":relation})
        out.append(row)
    assert {r["id"] for r in out if r["v35_specific_remaining_delta"]!=r["v34_specific_remaining_delta"]}==DIRECT
    assert all(r["v35_status"]==r["v34_status"] and r["v35_gate_categories"]==r["v34_gate_categories"] and r["v35_next_prerequisite"]==r["v34_next_prerequisite"] for r in out)
    (HERE/"row-challenge-v35.json").write_text(json.dumps(out,indent=2,sort_keys=True,ensure_ascii=False)+"\n")
    by_id={r["id"]:r for r in out}
    fields=("v35_status","v35_gate_categories","v35_specific_remaining_delta","v35_scope_assessment","v35_review_package","v35_new_evidence_packages","v35_evidence_files","v35_next_prerequisite","v35_evidence_relation")
    def extend(old_name,key,new_name):
        rows=[]
        for old in read_csv(V34/old_name):
            row=dict(old);source=by_id[row[key]]
            for field in fields:
                value=source[field];row[field]=";".join(value) if isinstance(value,list) else value
            rows.append(row)
        write_csv(HERE/new_name,rows)
        return rows
    investigations=extend("investigation-final-v34.csv","id","investigation-final-v35.csv")
    suggestions=extend("3730-crosswalk-final-v34.csv","3730_id","3730-crosswalk-final-v35.csv")
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
    write_csv(HERE/"source-package-inventory-v35.csv",inventory)
    generated=("row-challenge-v35.json","investigation-final-v35.csv","3730-crosswalk-final-v35.csv","source-package-inventory-v35.csv")
    inputs={"v34/row-challenge-v34.json":V34/"row-challenge-v34.json",
            "v34/investigation-final-v34.csv":V34/"investigation-final-v34.csv",
            "v34/3730-crosswalk-final-v34.csv":V34/"3730-crosswalk-final-v34.csv",
            "live-issue-snapshot-v35.json":HERE/"live-issue-snapshot-v35.json"}
    validation={"reference_tip_at_start":"641f55cfd54fcd3c6ba0de67643a62a29df4f3a1",
                "source_reference_package":V34_NAME,"source_anneal_revision":"bd0956be95c5f798f0c0484921b9b9d1fc6e9988",
                "row_count":len(out),"investigation_count":len(investigations),"suggestion_count":len(suggestions),
                "suggestion_destination_links":links,
                "status_counts":{"investigations":dict(Counter(r["status"] for r in investigations)),"suggestions":dict(Counter(r["status"] for r in suggestions))},
                "changed_status_ids":[],"changed_gate_ids":[],"changed_residual_ids":sorted(DIRECT),"changed_prerequisite_ids":[],
                "direct_evidence_ids":sorted(DIRECT),"bounded_context_ids":[],"source_packages":list(PACKAGES),
                "inventory_files":len(inventory),"input_sha256":{name:sha(path) for name,path in inputs.items()},
                "generated_sha256":{name:sha(HERE/name) for name in generated}}
    (HERE/"validation-v35.json").write_text(json.dumps(validation,indent=2,sort_keys=True)+"\n")
    print(json.dumps({key:validation[key] for key in ("row_count","suggestion_destination_links","changed_residual_ids","inventory_files")},sort_keys=True))

if __name__=="__main__":main()
