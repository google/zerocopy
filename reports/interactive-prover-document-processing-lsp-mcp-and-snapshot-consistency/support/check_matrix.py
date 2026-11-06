#!/usr/bin/env python3
"""Offline R386 frozen-corpus and official-source snapshot checker."""

import csv
import hashlib
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE = "ebcdcadb63fefd1e6c0f46cb2030270ae3232837"
FROZEN = "f64e634e06aaf8b7eae2fefb3a9d7f2ebf82d3b2"
PINS = {
    "E3": ("rocq-archive/coq-serapi", "6196f9f572ef9dd3749b885cabce7a57406cedb9", "serapi"),
    "E5": ("rocq-community/rocq-lsp", "2e0c43c34af6d6cad272ca2b8c4a417fe780bfbe", "rocq-lsp"),
}
CLAIM_PATHS = {
    4: {"E3": ["README.md", "serapi/serapi_protocol.mli"]},
    5: {"E3": ["serapi/serapi_protocol.mli"]},
    6: {"E5": ["README.md"]},
    7: {"E5": ["fleche/doc.ml"]},
    8: {"E5": ["etc/doc/PROTOCOL.md"]},
    9: {"E5": ["etc/doc/USER_MANUAL.md"]},
    11: {"E3": ["serapi/serapi_protocol.mli"], "E5": ["fleche/doc.ml", "etc/doc/PROTOCOL.md"]},
}


def need(ok, why):
    if not ok:
        raise AssertionError(why)


def git(*args):
    return subprocess.check_output(["git", *args], stderr=subprocess.DEVNULL)


def frozen_bytes(path):
    return git("show", f"{FROZEN}:{path}")


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def blob_sha(data):
    return hashlib.sha1(f"blob {len(data)}\0".encode() + data).hexdigest()


def paths_at(commit):
    need(git("rev-parse", f"{commit}^{{commit}}").decode().strip() == commit, "exact corpus commit")
    return {p for p in git("ls-tree", "-r", "--name-only", commit, "reports").decode().splitlines() if p.endswith("/REPORT.json")}


def run():
    m = json.loads((HERE / "matrix.json").read_text())
    need((m["schema"], m["baseline_reference_commit"], m["frozen_reference_commit"]) == (1, BASE, FROZEN), "corpus IDs")
    need((m["baseline_count"], m["current_count"]) == (581, 607), "corpus counts")
    inventory_bytes = (HERE / "version-inventory-ebcdcad-581.csv").read_bytes()
    need(sha256(inventory_bytes) == m["baseline_inventory_sha256"], "inventory hash")
    inventory = list(csv.DictReader(inventory_bytes.decode().splitlines()))
    baseline = set((HERE / "baseline-report-paths.txt").read_text().splitlines())
    frozen = paths_at(FROZEN)
    need(len(inventory) == len(baseline) == len(paths_at(BASE)) == 581, "baseline census")
    need(baseline == paths_at(BASE) == {r["report_json_at_commit"] for r in inventory}, "baseline path match")
    need(len(frozen) == 607 and baseline <= frozen, "current corpus census")
    additions = m["added_after_baseline"]
    need(len(additions) == 26 and {a["report_json"] for a in additions} == frozen - baseline, "26 added packages")
    for a in additions:
        need(a["report_md"] == a["report_json"].replace("REPORT.json", "REPORT.md"), "addition pair")
        need(sha256(frozen_bytes(a["report_json"])) == a["json_sha256"] and sha256(frozen_bytes(a["report_md"])) == a["md_sha256"], "addition hashes")

    rows = [r for r in inventory if r["inventory_id"] == "R386"]
    need(len(rows) == 1, "one R386")
    row = rows[0]
    cohort = list(csv.DictReader((HERE / "frozen-cohort.csv").open()))
    need(cohort == [{"inventory_id": "R386", "cohort": row["cohort"], "report_json": row["report_json_at_commit"], "report_md": row["report_md_at_commit"]}], "exact selector")
    need((m["inventory_id"], m["cohort"], m["title"], m["report_json"], m["report_md"]) == ("R386", row["cohort"], row["title"], row["report_json_at_commit"], row["report_md_at_commit"]), "inventory metadata")
    original_md = frozen_bytes(m["report_md"])
    original_meta = frozen_bytes(m["report_json"])
    original_evidence = frozen_bytes(m["evidence_map_path"])
    need((sha256(original_md), sha256(original_meta), sha256(original_evidence)) == (m["frozen_md_sha256"], m["frozen_json_sha256"], m["frozen_evidence_map_sha256"]), "frozen source bytes")
    meta, evidence = json.loads(original_meta), json.loads(original_evidence)
    need(meta["subjects"] == m["frozen_subjects_exact"] == json.loads(row["exact_pinned_subject_identities_json"]), "original subjects")
    lines = original_md.decode().splitlines()
    start = lines.index("## Summary") + 1
    while not lines[start].strip():
        start += 1
    end = lines.index("## Applicability")
    summary = "\n".join(lines[start:end]).rstrip()
    paragraphs = summary.split("\n\n")
    need(m["claim_locator"] == {"heading": "## Summary", "line": start + 1} and m["full_summary_exact"] == summary and len(paragraphs) == 6, "exact Summary")
    need(m["inventory_claim_excerpt_exact_or_normalized"] == row["claim_or_cell_to_recheck"], "inventory excerpt")
    need(m["summary_paragraphs"] == [{"number": n, "exact_excerpt": p, "runtime_result": "unexecuted_in_this_review"} for n, p in enumerate(paragraphs, 1)], "six paragraph excerpts")
    expected_claims = []
    for n, claim in enumerate(evidence["claims"], 1):
        mapped = CLAIM_PATHS.get(n, {})
        need(set(mapped) <= set(claim["evidence"]), "claim source links")
        expected_claims.append({"number": n, "exact_claim": claim["claim"], "evidence_ids": claim["evidence"], "mapped_source_paths": mapped, "source_result": "same_pinned_commit_no_forward_range" if mapped else "historical_or_derived_no_current_source_recheck", "runtime_result": "unexecuted_in_this_review"})
    need(m["evidence_claims"] == expected_claims and len(expected_claims) == 11, "eleven exact claims")

    obs_bytes = (HERE / "official-source-observation.json").read_bytes()
    need(sha256(obs_bytes) == m["official_observation_sha256"], "observation hash")
    obs = json.loads(obs_bytes)
    need(obs["schema"] == 1 and obs["observed_at_utc"] == "2026-09-30T22:02:11Z" and len(obs["repositories"]) == 2, "observation shape")
    need({r["evidence_id"] for r in obs["repositories"]} == PINS.keys(), "independent repositories")
    for repo_row in obs["repositories"]:
        key = repo_row["evidence_id"]
        repo, pin, folder = PINS[key]
        need((repo_row["repository"], repo_row["pinned_commit"], repo_row["current_default_branch"], repo_row["current_commit"]) == (repo, pin, "main", pin), "per-repo full commit identity")
        need(repo_row["ancestry"] == "identical_commit_zero_forward_range" and repo_row["forward_commit_count"] == 0 and repo_row["changed_paths"] == [], "zero-forward conclusion")
        raw_path = HERE / repo_row["raw_ref_snapshot_path"]
        need(raw_path == HERE / f"{folder}-refs.txt", "raw ref file")
        raw = raw_path.read_bytes()
        refs = {ref: sha for sha, ref in (line.split("\t") for line in raw.decode().splitlines())}
        need(sha256(raw) == repo_row["raw_ref_snapshot_sha256"] and refs == repo_row["refs"] == {"HEAD": pin, "refs/heads/main": pin}, "official ref snapshot")
        old_files = evidence["sources"][key]["files"]
        need(evidence["sources"][key]["identity"] == f"{repo}@{pin}", "evidence source identity")
        need(len(repo_row["files"]) == len(old_files) and {f["path"] for f in repo_row["files"]} == old_files.keys(), "source path map")
        for file_row in repo_row["files"]:
            path = file_row["path"]
            snapshot_path = HERE / file_row["snapshot_path"]
            need(snapshot_path == HERE / "snapshots" / folder / path, "snapshot path")
            data = snapshot_path.read_bytes()
            need(file_row["pinned_blob_sha1"] == file_row["current_blob_sha1"] == old_files[path] == blob_sha(data), "exact old/current blob")
            need(file_row["content_sha256"] == sha256(data) and file_row["size"] == len(data), "source snapshot bytes")
            need(file_row["raw_url"] == f"https://raw.githubusercontent.com/{repo}/{pin}/{path}", "commit-pinned source URL")
    need(m["source_result"] == "both_default_branches_same_as_pins_zero_forward_comparison" and m["runtime_result"] == "unexecuted_in_this_review" and m["anneal_product_result"] == "unassessed", "result bounds")
    print("OK: R386 exact six paragraphs and eleven evidence claims; 581/607 corpus and 26 additions; both official main refs equal pins; six source blobs match; runtime unexecuted")


if __name__ == "__main__":
    try:
        run()
    except Exception as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        raise
