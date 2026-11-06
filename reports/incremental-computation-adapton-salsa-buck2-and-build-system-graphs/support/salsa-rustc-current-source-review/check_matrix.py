#!/usr/bin/env python3
"""Offline R566 frozen-corpus and recorded source-evidence checker."""

import csv
import hashlib
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE = "ebcdcadb63fefd1e6c0f46cb2030270ae3232837"
FROZEN = "ca4e34659fadfb1ad24084db833adae9ffd8eb05"
REPOS = {
    "salsa": ("salsa-rs/salsa", "a7f8c558555f179ca02f6bdf7397d1317f91aa43", "30b614d826d697c47bc0f21591fab218f2004032", "master", "salsa-refs.txt", 3, 17),
    "rustc_dev_guide": ("rust-lang/rustc-dev-guide", "8ae6c255bb0675bbcb8bd0c197e8e70505bd7e85", "be8854f66df1b5450349061e45374ac072abd109", "main", "rustc-guide-refs.txt", 27, 11),
}
SALSA_TAG_OBJECT = "96fe729b8b435820ccf1b5a990d4d076352d67ce"
SALSA_TAG_COMMIT = "d434f8805c60ac60dce5f367ca91c5a7cd3e4c86"


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


def read_snapshot(record, repo, revision):
    path = record["path"]
    file = HERE / record["snapshot_path"]
    data = file.read_bytes()
    need(record["blob_sha1"] == blob_sha(data) and record["content_sha256"] == sha256(data) and record["size"] == len(data), "source snapshot hashes")
    need(record["raw_url"] == f"https://raw.githubusercontent.com/{repo}/{revision}/{path}", "commit-pinned source URL")
    return data


def run():
    m = json.loads((HERE / "matrix.json").read_text())
    need((m["schema"], m["baseline_reference_commit"], m["frozen_reference_commit"]) == (1, BASE, FROZEN), "corpus identity")
    need((m["baseline_count"], m["current_count"]) == (581, 609), "corpus counts")
    inv_bytes = (HERE / "version-inventory-ebcdcad-581.csv").read_bytes()
    need(sha256(inv_bytes) == m["baseline_inventory_sha256"], "inventory hash")
    inv = list(csv.DictReader(inv_bytes.decode().splitlines()))
    baseline = set((HERE / "baseline-report-paths.txt").read_text().splitlines())
    frozen = paths_at(FROZEN)
    need(len(inv) == len(baseline) == len(paths_at(BASE)) == 581, "baseline size")
    need(baseline == paths_at(BASE) == {r["report_json_at_commit"] for r in inv}, "baseline paths")
    need(len(frozen) == 609 and baseline <= frozen, "frozen report paths")
    additions = m["added_after_baseline"]
    need(len(additions) == 28 and {a["report_json"] for a in additions} == frozen - baseline, "28 additions")
    for a in additions:
        need(a["report_md"] == a["report_json"].replace("REPORT.json", "REPORT.md"), "addition pair")
        need(sha256(frozen_bytes(a["report_json"])) == a["json_sha256"] and sha256(frozen_bytes(a["report_md"])) == a["md_sha256"], "addition hashes")

    rows = [r for r in inv if r["inventory_id"] == "R566"]
    need(len(rows) == 1, "one R566")
    row = rows[0]
    selected = list(csv.DictReader((HERE / "frozen-cohort.csv").open()))
    need(selected == [{"inventory_id": "R566", "cohort": row["cohort"], "report_json": row["report_json_at_commit"], "report_md": row["report_md_at_commit"]}], "selector exactness")
    need((m["inventory_id"], m["cohort"], m["title"], m["report_json"], m["report_md"]) == ("R566", row["cohort"], row["title"], row["report_json_at_commit"], row["report_md_at_commit"]), "R566 identity")
    md_bytes, meta_bytes, evidence_bytes = (frozen_bytes(m[key]) for key in ("report_md", "report_json", "evidence_path"))
    need((sha256(md_bytes), sha256(meta_bytes), sha256(evidence_bytes)) == (m["frozen_md_sha256"], m["frozen_json_sha256"], m["frozen_evidence_sha256"]), "frozen report and evidence hashes")
    meta, evidence = json.loads(meta_bytes), json.loads(evidence_bytes)
    need(meta["subjects"] == m["frozen_subjects_exact"] == json.loads(row["exact_pinned_subject_identities_json"]), "original source subjects")
    lines = md_bytes.decode().splitlines()
    start = lines.index("## Summary") + 1
    while not lines[start].strip():
        start += 1
    end = lines.index("## Applicability")
    summary = "\n".join(lines[start:end]).rstrip()
    paragraphs = summary.split("\n\n")
    need(m["claim_locator"] == {"heading": "## Summary", "line": start + 1} and m["full_summary_exact"] == summary and len(paragraphs) == 3, "exact Summary")
    need(m["inventory_claim_excerpt_exact_or_normalized"] == row["claim_or_cell_to_recheck"], "inventory excerpt")
    need(m["summary_paragraphs"] == [{"number": n, "exact_excerpt": p, "runtime_result": "unexecuted_in_this_review"} for n, p in enumerate(paragraphs, 1)], "summary paragraphs")
    evidence_line = lines.index("## Evidence")
    findings = [{"heading": line, "line": n + 1} for n, line in enumerate(lines) if line.startswith("### ") and n < evidence_line]
    need(m["finding_locators"] == findings and len(findings) == 9, "Findings locators")
    need(m["pinned_source_map"] == {k: {"repository": evidence["sources"][k]["repository"], "revision": evidence["sources"][k]["revision"], "files": evidence["sources"][k]["files"]} for k in REPOS}, "exact evidence-map source pins")

    obs_bytes = (HERE / "official-source-observation.json").read_bytes()
    need(sha256(obs_bytes) == m["official_observation_sha256"], "official observation hash")
    obs = json.loads(obs_bytes)
    need(obs["schema"] == 1 and obs["observed_at_utc"] == "2026-09-30T22:10:29Z" and len(obs["repositories"]) == 2, "observation shape")
    need({r["key"] for r in obs["repositories"]} == REPOS.keys(), "independent repo rows")
    for entry in obs["repositories"]:
        key = entry["key"]
        repo, old, new, branch, refs_path, ahead, file_count = REPOS[key]
        need((entry["repository"], entry["pinned_commit"], entry["selected_current_commit"], entry["default_branch"], entry["raw_ref_path"]) == (repo, old, new, branch, refs_path), "repo identity")
        raw = (HERE / refs_path).read_bytes()
        refs = {ref: commit for commit, ref in (line.split("\t") for line in raw.decode().splitlines())}
        need(sha256(raw) == entry["raw_ref_sha256"] and refs == entry["refs"] == {"HEAD": new, f"refs/heads/{branch}": new}, "raw official refs")
        comp = entry["compare"]
        need((comp["status"], comp["ahead_by"], comp["behind_by"], comp["total_commits"], comp["returned_commit_count"], comp["returned_file_count"], comp["file_list_complete"]) == ("ahead", ahead, 0, ahead, ahead, file_count, True), "forward ancestry and compare completeness")
        changed = comp["changed_files"]
        changed_paths = {f["path"]: f for f in changed}
        need(len(changed) == len(changed_paths) == file_count, "unique complete changed paths")
        mapped = evidence["sources"][key]["files"]
        need(len(entry["mapped_files"]) == len(mapped) and {f["path"] for f in entry["mapped_files"]} == mapped.keys(), "mapped source paths")
        for f in entry["mapped_files"]:
            path = f["path"]
            need(f["old_blob_sha1"] == mapped[path], "original pinned blob")
            current = (HERE / f["current_snapshot_path"]).read_bytes()
            need(f["current_snapshot_path"] == f"snapshots/{key}/current/{path}" and blob_sha(current) == f["new_blob_sha1"] and sha256(current) == f["new_content_sha256"] and len(current) == f["new_size"], "current mapped snapshot")
            need(f["old_raw_url"] == f"https://raw.githubusercontent.com/{repo}/{old}/{path}" and f["new_raw_url"] == f"https://raw.githubusercontent.com/{repo}/{new}/{path}", "mapped source URLs")
            if path in changed_paths:
                need(f["new_blob_sha1"] == changed_paths[path]["blob_sha"] and f["old_blob_sha1"] != f["new_blob_sha1"], "changed mapped blob")
                pinned = (HERE / f["pinned_snapshot_path"]).read_bytes()
                need(f["pinned_snapshot_path"] == f"snapshots/{key}/pinned/{path}" and blob_sha(pinned) == f["old_blob_sha1"] and sha256(pinned) == f["old_content_sha256"] and len(pinned) == f["old_size"], "pinned changed snapshot")
                need(changed_paths[path]["patch"] and path == "book/src/cycles.md" and "cycle_initial" in changed_paths[path]["patch"] and "tracked structs" in changed_paths[path]["patch"], "mapped cycle doc delta")
            else:
                need(f["pinned_snapshot_path"] is None and f["old_blob_sha1"] == f["new_blob_sha1"] and f["old_content_sha256"] == f["new_content_sha256"] and f["old_size"] == f["new_size"], "unchanged mapped blob")
        if key == "salsa":
            need(set(mapped) & changed_paths.keys() == {"book/src/cycles.md"}, "one Salsa mapped delta")
            adjacent = entry["adjacent_implementation_files"]
            need({f["path"] for f in adjacent} == {"src/active_query.rs", "src/function/execute.rs", "src/function/fetch.rs", "tests/cycle_initial_tracked_struct.rs"}, "adjacent Salsa implementation paths")
            for f in adjacent:
                path = f["path"]
                need(path in changed_paths and bool(f["patch"]), "adjacent source patch")
                need(f["new"]["blob_sha1"] == changed_paths[path]["blob_sha"], "adjacent new blob")
                read_snapshot({"path": path, **f["new"]}, repo, new)
                if f["old"] is not None:
                    read_snapshot({"path": path, **f["old"]}, repo, old)
                else:
                    need(path == "tests/cycle_initial_tracked_struct.rs" and changed_paths[path]["status"] == "added", "added source test")
            need("cycle_initial" in next(f for f in adjacent if f["path"] == "src/function/fetch.rs")["patch"], "cycle implementation context")
        else:
            need(not (set(mapped) & changed_paths.keys()), "two guide pinned docs unchanged")
            adjacent = entry["adjacent_documentation_files"]
            need(len(adjacent) == 1 and adjacent[0]["path"] == "src/query.md" and adjacent[0]["path"] in changed_paths, "adjacent query doc")
            f = adjacent[0]
            need(f["new"]["blob_sha1"] == changed_paths["src/query.md"]["blob_sha"] and bool(f["patch"]), "query doc patch")
            old_query = read_snapshot({"path": "src/query.md", **f["old"]}, repo, old)
            new_query = read_snapshot({"path": "src/query.md", **f["new"]}, repo, new)
            need(" ".join(old_query.decode().split()) == " ".join(new_query.decode().split()), "query doc whitespace-only change")

    tag = obs["salsa_release"]
    tag_raw = (HERE / tag["raw_tag_refs_path"]).read_bytes()
    tag_refs = {ref: commit for commit, ref in (line.split("\t") for line in tag_raw.decode().splitlines())}
    need(sha256(tag_raw) == tag["raw_tag_refs_sha256"] and tag["raw_tag_refs_path"] == "salsa-release-tag-refs.txt", "release tag snapshot")
    need(tag_refs == {"refs/tags/salsa-v0.28.5": SALSA_TAG_OBJECT, "refs/tags/salsa-v0.28.5^{}": SALSA_TAG_COMMIT}, "annotated tag peeling")
    need((tag["tag_name"], tag["published_at"], tag["tag_ref_object_sha"], tag["peeled_commit"]) == ("salsa-v0.28.5", "2026-09-24T09:56:35Z", SALSA_TAG_OBJECT, SALSA_TAG_COMMIT), "official release identity")
    need(tag["relation_to_old"] == {"status": "ahead", "ahead_by": 9, "behind_by": 0} and tag["relation_to_current"] == {"status": "ahead", "ahead_by": 12, "behind_by": 0}, "release ancestry")
    need(obs["rustc_guide_release_endpoint"]["http_status"] == 404 and obs["rustc_guide_release_endpoint"]["status"] == "not_found", "guide release endpoint")
    need(m["source_results"] == {"salsa": "three_commit_forward_range_one_mapped_cycle_doc_changed_related_cycle_implementation_changed", "rustc_dev_guide": "twenty_seven_commit_forward_range_two_pinned_docs_unchanged_adjacent_query_doc_formatting_only"}, "source result categories")
    need(m["runtime_result"] == "unexecuted_in_this_review" and m["anneal_product_result"] == "unassessed" and m["compiler_source_review"] == "not_performed", "runtime/product boundaries")
    print("OK: R566 exact claims and pins; 581/609 corpus and 28 additions; Salsa 3/17 and guide 27/11 forward comparisons; seven mapped blobs and adjacent source; runtime unexecuted")


if __name__ == "__main__":
    try:
        run()
    except Exception as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        raise
