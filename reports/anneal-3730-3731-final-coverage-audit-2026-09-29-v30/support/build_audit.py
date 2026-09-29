#!/usr/bin/env python3
"""Derive v30's append-only ledger from published v29 and three reviewed reports."""
import csv
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V29_NAME = "anneal-3730-3731-final-coverage-audit-2026-09-29-v29"
V29 = REPORTS / V29_NAME / "support"
V22 = REPORTS / "anneal-3730-3731-final-coverage-audit-2026-09-29-v22" / "support"
CANCEL = "anneal-3731-i080-incremental-on-shared-target-cancel-recovery-2026-09-29"
INVENTORY = "anneal-3731-i094-installed-lean-lake-inventory-2026-09-29"
CONSUMERS = "anneal-3731-two-concurrent-fresh-cache-goal-consumers-2026-09-29"
SOURCE_PACKAGES = (V29_NAME, CANCEL, INVENTORY, CONSUMERS)

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def sha_text(value): return hashlib.sha256(value.encode()).hexdigest()
def csv_rows(path):
    with path.open(newline="") as stream: return list(csv.DictReader(stream))
def write_csv(path, rows):
    with path.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]), lineterminator="\n")
        writer.writeheader(); writer.writerows(rows)
def evidence(package, *names):
    out=[f"reports/{package}/{name}" for name in names]
    assert all((ROOT / name).is_file() for name in out), out
    return out

# Tuple: source package, residual, prerequisite, scope assessment, exact evidence.
UPDATES = {
    "I080": (CANCEL,
        "A new warmed shared Cargo target with CARGO_INCREMENTAL=1 underwent an edited-A versus unchanged-B overlap: after A's build-script entry marker, B started, A was SIGTERM-canceled while both process groups were live, and B waited on the build-directory lock then completed with baseline error-free LLBC. A left no LLBC at its distinct destination; a fresh A retry on the same shared target produced edited error-free LLBC. Five selected local body hashes for B and retried A match independent cold baseline/edited oracles. This one tiny schedule does not establish lock ownership timing, all LLBC fields, stage-wide descendant cleanup, path-sensitive output provenance, representative resource cost or Anneal transactional publication.",
        "Test representative Anneal-owned Charon snapshots under dirty shared/private targets with repeated cancellation across build, extraction and publication stages; trace descendants, locks, full output identity and resource peaks under guarded budgets.",
        "Incremental-on dirty shared-target cancellation and same-target retry directly fill one I080 schedule, while product ownership and sustained cleanup remain open.",
        ("REPORT.md","REPORT.json","support/check.py","support/results.json","support/artifacts/companion-B.llbc","support/artifacts/recovery-A.llbc")),
    "I094": (INVENTORY,
        "A read-only local inventory at reference@40b3024d found installed Lean/Lake v4.29.0 and v4.30.0-rc2 in the bundled Elan tree, one matching 4.30.0-rc2 Nix-store tuple, no usual home Elan toolchain directory, and Aeneas release/source pins both at v4.30.0-rc2. No later compatible installed tuple appeared in those bounded locations. This is an availability finding only: no upgraded Lake ownership/read-only comparison, broader installation search, remote release check or selected later compatible toolchain execution occurred.",
        "Select a later compatible Lean/Lake tuple with its coupled toolchain, then run the frozen-consumer Lake ownership/read-only comparison; obtain non-local dependencies only under the required user direction.",
        "The bounded installed-tool inventory directly narrows upgrade availability, not version-specific behavior or an actual upgrade comparison.",
        ("REPORT.md","REPORT.json","support/check.py","support/inventory.json","support/collect.py")),
    "I089": (CONSUMERS,
        "Two independent source-only Lake consumer roots simultaneously fetched Dep and Generated from a seeded cache under --no-build. Both matched seed OLean hashes, passed a direct batch theorem/value check, and each fresh lake --no-cache serve returned the same non-null first goal. Shared cache and original seed file/hash/mtime inventories were unchanged, with cache permissions and sandbox write denial; 24 resource samples saw no guard abort. This remains one tiny two-consumer schedule, with private writable producer trees and no actual Anneal archive, generated Rust model, syscall write trace, immutable mount or complete dependency graph.",
        "Supply a content-identified real Anneal prepared archive and matching generated consumers; repeat simultaneous cold first-goal runs with enforced read-only dependencies, write tracing, representative imports and resource bounds.",
        "Two concurrent fresh tiny consumers now directly exercise simultaneous cache fetch and first-goal use, while the real archive gate remains.",
        ("REPORT.md","REPORT.json","support/check.py","support/results.json","support/rejected-wrapper-results.json")),
    "D06": (CANCEL,
        "An incremental-on shared-target Charon pair now cancels edited A after its build-script marker while B remains live and logs a build-directory lock wait; B completes with cold-oracle baseline body map, canceled A leaves no LLBC, and same-target retry A matches its edited cold oracle. Selected process groups had no non-zombie members at one post-run sample and the private work tree was removed. The cancellation point, five-body projection and one cleanup sample do not cover all Charon stages, escaped descendants, transactional publication or an Anneal owner.",
        "Run stage-wide cancellation and retry in Anneal-owned scratch/publication transactions with descendant and lock tracing, last-good-output checks and representative resources across repeated schedules.",
        "A bounded successful companion/retry after SIGTERM directly narrows D06, but stage-wide cleanup and product transactions remain untested.",
        ("REPORT.md","REPORT.json","support/check.py","support/results.json","support/artifacts/companion-B.llbc","support/artifacts/recovery-A.llbc")),
    "F13": (CONSUMERS,
        "Two simultaneous source-only consumers fetched from the same seeded read-only Lake artifact cache with isolated writable build trees, then both returned the same first goal from separate fresh servers and matched direct batch output. The cache and original seed inventories had no net file/hash/mtime changes; the successful cell admitted under its resource gates. This is two tiny consumers rather than many representative Anneal consumers; no actual prepared archive, immutable producer mount, syscall write tracing, shared mutable package tree, or service scheduling ran.",
        "Repeat guarded many-consumer cold first-goal probes on the actual content-identified Anneal archive with enforced read-only dependencies, write/read tracing, representative imports and bounded resource scaling.",
        "A two-consumer read-only-cache first-goal control directly narrows F13 without satisfying its actual-archive or many-consumer scope.",
        ("REPORT.md","REPORT.json","support/check.py","support/results.json","support/rejected-wrapper-results.json")),
}

CONTEXT = {
    "D03": "The cancellation probe reuses a shared Cargo target, but adds no new source-selection or producing-unit attestation to D03's materialized-snapshot contract.",
    "F03": "The installed inventory found no later tuple in bounded local locations; it did not compare 4.30 with an upgraded Lake owner.",
    "M01": "No later compatible Lean/Lake tuple was run against interactive invariants.",
    "F02": "Two fresh consumers used a tiny prepared fixture, not the actual read-only Anneal archive/server probe.",
    "F04": "No real archive manifest was available or removed; this run did not execute that control.",
    "F08": "Both tiny consumers had first goals, but no causal readiness protocol or actual archive setup was tested.",
    "F20": "Cache-consumer inventories do not measure full-chain generated-module rebuild isolation or byte accounting.",
    "I04": "The successful tiny batch/live sequence did not cold-consume a batch-accepted Anneal archive.",
    "I092": "The two-consumer cache fetch did not test the exact Anneal no-build/no-cache server contract or missing/stale artifact families.",
    "I099": "Two matching tiny consumers are not a representative independent clean-versus-prepared Anneal oracle.",
    "I114": "Only two tiny Lake consumers ran; safe many-worker scaling and representative imports remain unmeasured.",
    "I139": "The two-consumer fixture lacked Anneal generated-project acceptance, model edits and service fences.",
    "I078": "The Charon cancellation fixture did not implement Anneal-level stage-wide cancellation or last-good publication.",
    "I105": "One Charon target retry does not establish transactional recovery across the full pipeline.",
}

def verify_live(live):
    frozen=json.loads((V22/"issue-scope-snapshot.json").read_text())
    prior=json.loads((V29/"live-issue-snapshot-v29.json").read_text())["issues"]
    for number,state in ((3730,"closed"),(3731,"open")):
        key=str(number);item=live["issues"][key]
        assert item["number"]==number and item["state"]==state
        assert item["body"]==prior[key]["body"]==frozen[key]["body"]
        assert item["body_sha256"]==sha_text(item["body"])==prior[key]["body_sha256"]
        assert len(item["comments"])==len(prior[key]["comments"])==1
        for comment,old,orig in zip(item["comments"],prior[key]["comments"],frozen[key]["comments"]):
            assert comment["id"]==old["id"] and comment["body"]==old["body"]==orig["body"]
            assert comment["body_sha256"]==sha_text(comment["body"])==old["body_sha256"]

def main():
    prior=json.loads((V29/"row-challenge-v29.json").read_text())
    live=json.loads((HERE/"live-issue-snapshot-v30.json").read_text())
    verify_live(live)
    assert len(prior)==333 and len({r["id"] for r in prior})==333
    assert len(UPDATES)==5 and not set(UPDATES)&set(CONTEXT)
    out=[]
    for old in prior:
        row=dict(old);item=row["id"]
        if item in UPDATES:
            package,residual,prerequisite,assessment,names=UPDATES[item]
            packages=[package];files=evidence(package,*names);relation="direct bounded component evidence"
            assert row["v29_status"]=="partial"
        elif item in CONTEXT:
            packages=[];files=[];residual=row["v29_specific_remaining_delta"];prerequisite=row["v29_next_prerequisite"]
            assessment=CONTEXT[item]+" The v29 residual and prerequisite remain.";relation="bounded context only"
        else:
            packages=[];files=[];residual=row["v29_specific_remaining_delta"];prerequisite=row["v29_next_prerequisite"]
            gate=";".join(row["v29_gate_categories"]) or "already resolved or conditional"
            assessment=f"None of the three new reports directly exercises {item} ({row['title']}) at its remaining {gate} gate; the v29 residual and prerequisite remain."
            relation="no direct v30 evidence"
        row.update({"v30_status":row["v29_status"],"v30_gate_categories":row["v29_gate_categories"],
                    "v30_specific_remaining_delta":residual,"v30_scope_assessment":assessment,
                    "v30_review_package":HERE.parent.name if item in UPDATES else row["v29_review_package"],
                    "v30_new_evidence_packages":packages,"v30_evidence_files":files,
                    "v30_next_prerequisite":prerequisite,"v30_evidence_relation":relation})
        out.append(row)
    assert {r["id"] for r in out if r["v30_specific_remaining_delta"]!=r["v29_specific_remaining_delta"]}==set(UPDATES)
    assert all(r["v30_status"]==r["v29_status"] and r["v30_gate_categories"]==r["v29_gate_categories"] for r in out)
    (HERE/"row-challenge-v30.json").write_text(json.dumps(out,indent=2,sort_keys=True,ensure_ascii=False)+"\n")
    by_id={r["id"]:r for r in out}
    fields=("v30_status","v30_gate_categories","v30_specific_remaining_delta","v30_scope_assessment","v30_review_package","v30_new_evidence_packages","v30_evidence_files","v30_next_prerequisite","v30_evidence_relation")
    def extend(name,key):
        rows=[]
        for before in csv_rows(V29/name):
            row=dict(before);choice=by_id[row[key]]
            for field in fields:
                value=choice[field];row[field]=";".join(value) if isinstance(value,list) else value
            rows.append(row)
        return rows
    investigations=extend("investigation-final-v29.csv","id")
    suggestions=extend("3730-crosswalk-final-v29.csv","3730_id")
    assert len(investigations)==159 and len(suggestions)==174
    write_csv(HERE/"investigation-final-v30.csv",investigations)
    write_csv(HERE/"3730-crosswalk-final-v30.csv",suggestions)
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
    for package in SOURCE_PACKAGES:
        for path in sorted((REPORTS/package).rglob("*")):
            if path.is_file() and "__pycache__" not in path.parts and path.suffix!=".pyc":
                inventory.append({"path":path.relative_to(ROOT).as_posix(),"sha256":sha(path)})
    write_csv(HERE/"source-package-inventory-v30.csv",inventory)
    generated=("row-challenge-v30.json","investigation-final-v30.csv","3730-crosswalk-final-v30.csv","source-package-inventory-v30.csv")
    inputs={"v29/row-challenge-v29.json":V29/"row-challenge-v29.json",
            "v29/investigation-final-v29.csv":V29/"investigation-final-v29.csv",
            "v29/3730-crosswalk-final-v29.csv":V29/"3730-crosswalk-final-v29.csv",
            "v22/issue-scope-snapshot.json":V22/"issue-scope-snapshot.json",
            "live-issue-snapshot-v30.json":HERE/"live-issue-snapshot-v30.json"}
    validation={"reference_tip_at_start":"40b3024d5a3c73357abb6e90f10fcaf713768cd4",
                "source_reference_package":V29_NAME,"source_anneal_revision":"bd0956be95c5f798f0c0484921b9b9d1fc6e9988",
                "row_count":len(out),"investigation_count":len(investigations),"suggestion_count":len(suggestions),
                "suggestion_destination_links":links,
                "status_counts":{"investigations":dict(Counter(r["status"] for r in investigations)),"suggestions":dict(Counter(r["status"] for r in suggestions))},
                "changed_status_ids":[],"changed_gate_ids":[],"changed_residual_ids":sorted(UPDATES),"changed_prerequisite_ids":sorted(UPDATES),
                "direct_evidence_ids":sorted(UPDATES),"bounded_context_ids":sorted(CONTEXT),
                "source_packages":list(SOURCE_PACKAGES),"inventory_files":len(inventory),
                "input_sha256":{name:sha(path) for name,path in inputs.items()},
                "generated_sha256":{name:sha(HERE/name) for name in generated}}
    (HERE/"validation-v30.json").write_text(json.dumps(validation,indent=2,sort_keys=True)+"\n")
    print(json.dumps({key:validation[key] for key in ("row_count","suggestion_destination_links","changed_residual_ids","inventory_files","status_counts")},sort_keys=True))

if __name__=="__main__":main()
