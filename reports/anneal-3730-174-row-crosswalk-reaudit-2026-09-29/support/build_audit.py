#!/usr/bin/env python3
"""Freeze a row-by-row read-only challenge of the v22 #3730 crosswalk."""
import csv
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
V22 = REPORTS / "anneal-3730-3731-final-coverage-audit-2026-09-29-v22/support"
CROSSWALK = V22 / "3730-crosswalk-final-v22.csv"
ISSUES = V22 / "issue-scope-snapshot.json"
CHALLENGE = V22 / "row-challenge-v22.json"

CORRECTIONS = {
    "C03": ("overbroad_complete", "partial", "I049", "Watched import replacement plus same-byte and changed-byte didChange left the pinned worker stale; close/reopen, fresh server and batch saw the new import. Further Lake launch/worker-supervisor refresh remains."),
    "D01": ("misstated_prerequisite", "partial", "I073/I074", "OCaml/Dune/opam absence is unrelated to the requested Rust overlay/Charon integration; the actual gate is an Anneal overlay consumer and matching Charon route."),
    "F02": ("misstated_prerequisite", "partial", "I089", "OCaml/Dune/opam absence does not gate read-only inspection of a prepared Anneal archive; the missing input is that archive and consumer contract."),
    "F12": ("stale_residual", "partial", "I108/I151", "Crosswalk residual says only the one-command conflict exists, but a cited shared-tree package already ran two conflicting writers and reverse kill; artifact/trace syscall interruption remains."),
    "F14": ("misstated_prerequisite", "partial", "I101", "OCaml/Dune/opam absence is unrelated to producer-removed relocation of a retained prepared archive; need the actual archive and consumer."),
    "F15": ("new_local_evidence", "partial", "I052", "Paired tiny Lake build at final path versus stage then rename is now executed; setup/server/batch agree, while Dep.trace retains staging paths. Real Anneal archive/generated consumer/native/retained-worker scope remains."),
    "F19": ("misstated_human_gate", "partial", "I099/I131/I132", "Original clean-build oracle requests independent construction and comparison, not human participants; the gate is frozen artifact/interface plus actual archive or consumer."),
    "I01": ("gate_and_citation_gap", "partial", "I001/I131/I132", "Human-only gate omits product/archive/interface work; destination I001 cites the embedded-proof/generated-model vertical package, absent from this crosswalk row's evidence list."),
    "I03": ("misstated_human_gate", "partial", "I131/I137/I138", "Original acceptance-oracle question does not require human participants; gate is a runnable product path and an independently constructed batch/live oracle."),
    "I04": ("misstated_prerequisite", "partial", "I089/I091/I131", "OCaml/Dune/opam absence is unrelated to the requested cold interactive prepared-archive comparison; need the real archive and consumer."),
    "I08": ("misstated_human_gate", "partial", "I130/I141", "Human-only gate omits the frozen protocol and running product interface needed before independent observation."),
}

PRODUCT_GATE_OMITTED = {"J01", "J02", "J03", "J04", "J05", "J06", "J07", "J08", "J09", "J10", "J12", "J14"}
for ident in PRODUCT_GATE_OMITTED:
    CORRECTIONS[ident] = ("omitted_product_gate", "partial", "", "Resource/platform prerequisite omits the actual prepared Anneal workload and scheduler/consumer needed for this parallel-scaling question.")

CONFIRMED = {
    "C04": "Narrow completion aligns with the cited component evidence; no further discrepancy found.",
    "C13": "Narrow completion aligns with the cited component evidence; no further discrepancy found.",
    "N11": "Narrow completion aligns with the cited component evidence; no further discrepancy found.",
    "F03": "Later compatible Lean/Lake pin is not cached; the stated gate is supported by local inventory.",
    "E01": "OCaml/Dune/opam toolchain absent; the stated dependency gate is supported by local inventory.",
    "E02": "OCaml/Dune/opam toolchain absent; the stated dependency gate is supported by local inventory.",
    "E03": "OCaml/Dune/opam toolchain absent; the stated dependency gate is supported by local inventory.",
    "L10": "OCaml/Dune/opam toolchain absent; the stated dependency gate is supported by local inventory.",
    "G03": "Actual MCP task broker/adapter remains unrun despite toy task lifecycle components.",
    "G15": "Actual producer-authenticated navigation remains unrun despite toy mapping components.",
}


def main():
    rows = list(csv.DictReader(CROSSWALK.open()))
    issues = json.loads(ISSUES.read_text())
    source, destination = issues["3730"]["body"], issues["3731"]["body"]
    challenge_ids = {x["id"] for x in json.loads(CHALLENGE.read_text())}
    package_cols = [c for c in rows[0] if c.endswith("packages")]
    evidence_cols = [c for c in rows[0] if c.endswith("evidence_files")]
    packages = sorted({v for row in rows for col in package_cols for v in row[col].split(";") if v})
    evidence = sorted({v for row in rows for col in evidence_cols for v in row[col].split(";") if v})
    assert len(rows) == 174 and len(packages) == 106 and len(evidence) == 364
    assert all((REPORTS / p).is_dir() for p in packages)
    assert all(((REPORTS.parent if f.startswith("reports/") else REPORTS) / f).is_file()
               for f in evidence)
    out = []
    for row in rows:
        ident = row["3730_id"]
        match = re.search(r"(?m)^### " + ident + r"\. [^\n]+", source)
        assert match, ident
        dests = row["3731_destinations"].split(";")
        assert all(dest in challenge_ids and (int(dest[1:]) > 144 or
                   re.search(r"\*\*" + dest + r"\s+—", destination))
                   for dest in dests), ident
        finding, status, target, note = CORRECTIONS.get(
            ident, ("no_further_discrepancy_found", row["v22_status"], "",
                    CONFIRMED.get(ident, "Exact question and cited destination/evidence remain aligned at the scoped v22 status; no additional discrepancy found.")))
        row_packages = sorted({v for col in package_cols for v in row[col].split(";") if v})
        row_evidence = sorted({v for col in evidence_cols for v in row[col].split(";") if v})
        out.append({"id": ident, "exact_question_heading": match.group(),
                    "suggestion": row["suggestion"], "destinations": dests,
                    "v22_status": row["v22_status"], "v22_gate_categories": row["v22_gate_categories"],
                    "v22_next_prerequisite": row["v22_next_prerequisite"],
                    "audit_finding": finding, "recommended_status": status,
                    "affected_destinations": target, "audit_note": note,
                    "cited_packages": row_packages, "cited_evidence_files": row_evidence})
    checks = json.loads((HERE / "checker-runs.json").read_text())
    assert len(checks) == 64 and sum(x["exit"] == 0 for x in checks) == 63
    result = {"source_csv_sha256": hashlib.sha256(CROSSWALK.read_bytes()).hexdigest(),
              "issue_snapshot_sha256": hashlib.sha256(ISSUES.read_bytes()).hexdigest(),
              "checker_runs_sha256": hashlib.sha256((HERE / "checker-runs.json").read_bytes()).hexdigest(),
              "row_count": len(out), "destination_link_count": sum(len(x["destinations"]) for x in out),
              "unique_cited_packages": len(packages), "unique_cited_files": len(evidence),
              "checker_passes": 63, "checker_failures": 1, "rows": out}
    (HERE / "audit.json").write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n")
    print(f"Wrote {len(out)} rows, {result['destination_link_count']} destinations; "
          f"{len(CORRECTIONS)} challenged rows")


if __name__ == "__main__":
    main()
