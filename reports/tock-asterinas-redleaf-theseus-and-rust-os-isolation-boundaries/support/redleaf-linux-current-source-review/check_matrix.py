#!/usr/bin/env python3
"""Offline R511 frozen-corpus and bounded official-source checker."""

import csv
import hashlib
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE = "ebcdcadb63fefd1e6c0f46cb2030270ae3232837"
FROZEN = "d8ebe60bc920363d4e43d95713e7e6a2de5363d7"
LINUX = "551c722f40809618230001baccf219193e22fc5a"
RED_OLD = "08753faee652495f55fc8cbb420e5123a183affc"
RED_NEW = "7194295d1968c8013ae6b3d104a9192f03516449"
LINUX_TAG_OBJECT = "5a956dde5526a634dca7ccad27c051ebcc306089"
LINUX_TAG_COMMIT = "72d3fcf802c45d00b300f25b848a93c3a2bd7c7e"
RED_PRESENT = {"kernel/src/heap.rs", "kernel/src/unwind.rs"}


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


def parse_refs(data):
    rows = [line.split("\t") for line in data.decode().splitlines()]
    need(all(len(row) == 2 for row in rows), "raw ref shape")
    return {ref: commit for commit, ref in rows}


def run():
    m = json.loads((HERE / "matrix.json").read_text())
    need((m["schema"], m["baseline_reference_commit"], m["frozen_reference_commit"]) == (1, BASE, FROZEN), "corpus IDs")
    need((m["baseline_count"], m["current_count"]) == (581, 615), "corpus counts")
    inv_bytes = (HERE / "version-inventory-ebcdcad-581.csv").read_bytes()
    need(sha256(inv_bytes) == m["baseline_inventory_sha256"], "inventory hash")
    inventory = list(csv.DictReader(inv_bytes.decode().splitlines()))
    baseline = set((HERE / "baseline-report-paths.txt").read_text().splitlines())
    frozen = paths_at(FROZEN)
    need(len(inventory) == len(baseline) == len(paths_at(BASE)) == 581, "baseline size")
    need(baseline == paths_at(BASE) == {r["report_json_at_commit"] for r in inventory}, "baseline paths")
    need(len(frozen) == 615 and baseline <= frozen, "frozen census")
    additions = m["added_after_baseline"]
    need(len(additions) == 34 and {a["report_json"] for a in additions} == frozen - baseline, "34 additions")
    for a in additions:
        need(a["report_md"] == a["report_json"].replace("REPORT.json", "REPORT.md"), "addition pair")
        need(sha256(frozen_bytes(a["report_json"])) == a["json_sha256"] and sha256(frozen_bytes(a["report_md"])) == a["md_sha256"], "addition hashes")

    selected = [r for r in inventory if r["inventory_id"] == "R511"]
    need(len(selected) == 1, "one R511")
    row = selected[0]
    cohort = list(csv.DictReader((HERE / "frozen-cohort.csv").open()))
    need(cohort == [{"inventory_id": "R511", "cohort": row["cohort"], "report_json": row["report_json_at_commit"], "report_md": row["report_md_at_commit"]}], "exact selector")
    need((m["inventory_id"], m["cohort"], m["title"], m["report_json"], m["report_md"]) == ("R511", row["cohort"], row["title"], row["report_json_at_commit"], row["report_md_at_commit"]), "inventory metadata")
    md_bytes, meta_bytes, em_bytes, cmp_bytes = (frozen_bytes(m[k]) for k in ("report_md", "report_json", "evidence_map_path", "comparison_matrix_path"))
    need((sha256(md_bytes), sha256(meta_bytes), sha256(em_bytes), sha256(cmp_bytes)) == (m["frozen_md_sha256"], m["frozen_json_sha256"], m["frozen_evidence_map_sha256"], m["frozen_comparison_matrix_sha256"]), "frozen report/support hashes")
    md, meta, em, comp = md_bytes.decode(), json.loads(meta_bytes), json.loads(em_bytes), json.loads(cmp_bytes)
    need(meta["subjects"] == m["frozen_subjects_exact"] == json.loads(row["exact_pinned_subject_identities_json"]), "original source subjects")
    need(em == m["evidence_map_exact"] and comp == m["comparison_matrix_exact"], "exact source/comparison maps")
    lines = md.splitlines()
    start = lines.index("## Summary") + 1
    while not lines[start].strip():
        start += 1
    end = lines.index("## Applicability")
    summary = "\n".join(lines[start:end]).rstrip()
    paragraphs = summary.split("\n\n")
    need(m["claim_locator"] == {"heading": "## Summary", "line": start + 1} and m["full_summary_exact"] == summary and len(paragraphs) == 4, "exact Summary")
    need(m["inventory_claim_excerpt_exact_or_normalized"] == row["claim_or_cell_to_recheck"], "inventory excerpt")
    need(m["summary_paragraphs"] == [{"number": n, "exact_excerpt": p, "runtime_result": "unexecuted_in_this_review"} for n, p in enumerate(paragraphs, 1)], "four summary paragraphs")
    findings = [{"heading": line, "line": n + 1} for n, line in enumerate(lines) if line.startswith("### ") and n < lines.index("## Evidence")]
    need(m["finding_locators"] == findings and len(findings) == 14, "Findings locators")
    need(meta["subjects"][2]["identity"]["revision"] == LINUX and meta["subjects"][1]["identity"]["revision"] == RED_OLD, "pin-to-repository resolution")

    obs_bytes = (HERE / "official-source-observation.json").read_bytes()
    need(sha256(obs_bytes) == m["official_observation_sha256"], "official observation hash")
    obs = json.loads(obs_bytes)
    need(obs["schema"] == 1 and obs["observed_at_utc"] == "2026-09-30", "observation identity")
    linux = obs["linux"]
    need((linux["repository"], linux["pinned_commit"], linux["selected_current_commit"], linux["default_branch"]) == ("torvalds/linux", LINUX, LINUX, "master"), "Linux source identity")
    linux_raw = (HERE / "linux-refs.txt").read_bytes()
    need(sha256(linux_raw) == linux["raw_ref_sha256"] and parse_refs(linux_raw) == linux["refs"] == {"HEAD": LINUX, "refs/heads/master": LINUX}, "Linux official refs")
    need(linux["compare"] == {"status": "identical", "ahead_by": 0, "behind_by": 0, "total_commits": 0, "changed_paths": []}, "Linux zero-forward range")
    linux_sources = [s for s in em["sources"] if s.get("identity", {}).get("repository") == "torvalds/linux"]
    expected = {s["identity"]["path"]: (s["id"], s["identity"]["blob"]) for s in linux_sources}
    need(len(expected) == len(linux["mapped_files"]) == 5 and {f["path"] for f in linux["mapped_files"]} == expected.keys(), "five Linux mapped paths")
    for f in linux["mapped_files"]:
        path = f["path"]
        source_id, pin_blob = expected[path]
        data = (HERE / f["snapshot_path"]).read_bytes()
        need(f["source_id"] == source_id and f["old_blob_sha1"] == f["new_blob_sha1"] == pin_blob == blob_sha(data), "Linux mapped blob continuity")
        need(f["snapshot_path"] == f"snapshots/linux/{path}" and f["content_sha256"] == sha256(data) and f["size"] == len(data), "Linux snapshot bytes")
        need(f["raw_url"] == f"https://raw.githubusercontent.com/torvalds/linux/{LINUX}/{path}", "Linux pinned URL")
    need(linux["github_release_endpoint"] == {"status": "not_found", "http_status": 404}, "Linux GitHub release endpoint")
    kernel_bytes = (HERE / "kernel-releases.json").read_bytes()
    kernel = json.loads(kernel_bytes)
    need(linux["kernel_org_latest_stable"] == {"version": "7.2.8", "source_snapshot_sha256": sha256(kernel_bytes)} and kernel["latest_stable"]["version"] == "7.2.8", "kernel.org release snapshot")
    tag_bytes = (HERE / "linux-mainline-tag-refs.txt").read_bytes()
    need(sha256(tag_bytes) == linux["mainline_tag"]["raw_ref_sha256"], "Linux tag ref hash")
    need(parse_refs(tag_bytes) == {"refs/tags/v7.3-rc5": LINUX_TAG_OBJECT, "refs/tags/v7.3-rc5^{}": LINUX_TAG_COMMIT}, "Linux annotated tag peel")
    need(linux["mainline_tag"]["tag"] == "v7.3-rc5" and linux["mainline_tag"]["tag_ref_object_sha"] == LINUX_TAG_OBJECT and linux["mainline_tag"]["peeled_commit"] == LINUX_TAG_COMMIT and linux["mainline_tag"]["relation_to_pinned"] == {"status": "ahead", "ahead_by": 37, "behind_by": 0}, "mainline tag ancestry")

    red = obs["redleaf"]
    need((red["repository"], red["paper_associated_commit"], red["observed_default_commit"]) == ("mars-research/redleaf", RED_OLD, RED_NEW), "RedLeaf identities")
    red_raw = (HERE / "redleaf-refs.txt").read_bytes()
    need(sha256(red_raw) == red["raw_ref_sha256"] and parse_refs(red_raw) == red["refs"] == {"HEAD": RED_NEW, "refs/heads/master": RED_NEW, "refs/heads/osdi20_camera_ready": RED_OLD}, "RedLeaf independent refs")
    need(red["compare"]["status"] == "diverged" and red["compare"]["ahead_by"] == 314 and red["compare"]["behind_by"] == 1 and red["compare"]["total_commits"] == 314 and red["compare"]["returned_file_count"] == 300 and red["compare"]["file_list_complete"] is False, "RedLeaf non-successor and compare cap")
    red_source = next(s for s in em["sources"] if s["id"] == "redleaf-osdi20-associated-source")
    red_expected = {a["path"]: a["blob"] for a in red_source["artifacts"]}
    need(len(red_expected) == len(red["mapped_files"]) == 7 and {f["path"] for f in red["mapped_files"]} == red_expected.keys(), "seven RedLeaf mapped paths")
    need(set(red["compare"]["mapped_paths_in_returned_file_list"]) <= red_expected.keys(), "bounded returned-list overlap")
    for f in red["mapped_files"]:
        path = f["path"]
        old_data = (HERE / f["old_snapshot_path"]).read_bytes()
        need(f["old_blob_sha1"] == red_expected[path] == blob_sha(old_data) and f["old_content_sha256"] == sha256(old_data) and f["old_size"] == len(old_data), "old RedLeaf mapped blob")
        need(f["old_snapshot_path"] == f"snapshots/redleaf/old/{path}" and f["old_raw_url"] == f"https://raw.githubusercontent.com/mars-research/redleaf/{RED_OLD}/{path}", "paper-associated source locator")
        need(f["new_raw_url"] == f"https://raw.githubusercontent.com/mars-research/redleaf/{RED_NEW}/{path}", "divergent master locator")
        if path in RED_PRESENT:
            data = (HERE / f["new_snapshot_path"]).read_bytes()
            need(f["new_status"] == "present" and f["new_blob_sha1"] == blob_sha(data) != f["old_blob_sha1"] and f["new_content_sha256"] == sha256(data) and f["new_size"] == len(data), "two changed surviving RedLeaf paths")
            need(f["new_snapshot_path"] == f"snapshots/redleaf/current-master/{path}", "divergent source snapshot")
        else:
            need(f["new_status"] == "missing" and f["new_http_status"] == 404, "five missing divergent RedLeaf paths")
    release_bytes = (HERE / "redleaf-latest-release.json").read_bytes()
    release = json.loads(release_bytes)
    need(red["github_release_endpoint"] == {"status": "found_non_matching", "tag_name": "bcache_v2", "published_at": "2020-05-07T18:54:58Z", "raw_snapshot_sha256": sha256(release_bytes)}, "RedLeaf unrelated release metadata")
    need(release["tag_name"] == "bcache_v2" and release["published_at"] == "2020-05-07T18:54:58Z", "RedLeaf release snapshot")
    need(m["linux_source_result"] == "same_pinned_commit_zero_forward_five_claim_files_same" and m["redleaf_source_result"] == "paper_branch_same_default_master_diverged_no_forward_successor" and m["runtime_result"] == "unexecuted_in_this_review" and m["anneal_product_result"] == "unassessed", "result bounds")
    print("OK: R511 exact claims, 581/615 corpus and 34 additions; Linux same pin/five blobs; RedLeaf branch same with divergent master (2 changed, 5 absent); runtime unexecuted")


if __name__ == "__main__":
    try:
        run()
    except Exception as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        raise
