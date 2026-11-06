#!/usr/bin/env python3
"""Offline checker for the frozen R346 corpus and recorded Buck2 source evidence."""

import csv
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE = "ebcdcadb63fefd1e6c0f46cb2030270ae3232837"
FROZEN = "ef8e39197bf8d1f6bb8753e7155c3a494fa8e2f4"
OLD = "738e69a6c5f1efb6a015645228e7a19ee9b1d9c0"
NEW = "b2b7ba58b5188aa35adc784d8ec6425dd93b98df"
TAG = "6507dd157a6f81a810c48583edf1758dd0c337c5"
LATEST = "0161ff601e2f82af9b8cd431e04e7d9acf9f305c"
DOCS = {
    "docs/about/why.md": "6799f38df279cc03f1806b1d0d447fb19570bcfa",
    "docs/about/benefits/compared_to_buck1.md": "296661b09239357fa870a55192dff6c5d54c25ca",
    "dice/dice/docs/index.md": "46897b9bd66a7bd055bbad8db7f363558347d4f0",
    "docs/insights_and_knowledge/modern_dice.md": "04a9950e2b077cdfdf91ca3e6e6ede68df508580",
}
ADJACENT = {
    "dice/dice/src/api/computations.rs": ("b5372f0e6763004f4c005b401035b5d0b95e81a2", "9890e896dd2bd1918fa2b552747640509165a8ca", "compute_with_key"),
    "dice/dice/src/epoch/ctx.rs": ("f2276da22e0feadd1306f82b712f9d6d40974300", "4ddce06d789b8c51fcc17a413743a388e5ba5028", "canonical_key"),
    "dice/dice/src/epoch/tests/general.rs": ("782daaa35d885c61896b5150c48eec6e6530b022", "71ca84ae0fa8ccc9afe5fc5745caa7e913fcfbdd", "Arc::ptr_eq"),
}


def need(condition, message):
    if not condition:
        raise AssertionError(message)


def git(*args):
    return subprocess.check_output(["git", *args], stderr=subprocess.DEVNULL)


def source_bytes(path):
    return git("show", f"{FROZEN}:{path}")


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def reports_at(commit):
    need(git("rev-parse", f"{commit}^{{commit}}").decode().strip() == commit, "corpus commit identity")
    return {p for p in git("ls-tree", "-r", "--name-only", commit, "reports").decode().splitlines() if p.endswith("/REPORT.json")}


def run():
    m = json.loads((HERE / "matrix.json").read_text())
    need((m["schema"], m["baseline_reference_commit"], m["frozen_reference_commit"]) == (1, BASE, FROZEN), "corpus IDs")
    need((m["baseline_count"], m["current_count"]) == (581, 605), "corpus counts")
    inventory_bytes = (HERE / "version-inventory-ebcdcad-581.csv").read_bytes()
    need(sha256(inventory_bytes) == m["baseline_inventory_sha256"], "inventory bytes")
    inventory = list(csv.DictReader(inventory_bytes.decode().splitlines()))
    baseline = set((HERE / "baseline-report-paths.txt").read_text().splitlines())
    frozen = reports_at(FROZEN)
    need(len(inventory) == len(baseline) == len(reports_at(BASE)) == 581, "baseline size")
    need(baseline == reports_at(BASE) == {r["report_json_at_commit"] for r in inventory}, "baseline path census")
    need(len(frozen) == 605 and baseline <= frozen, "frozen census")
    additions = m["added_after_baseline"]
    need(len(additions) == 24 and {a["report_json"] for a in additions} == frozen - baseline, "added report census")
    for a in additions:
        need(a["report_md"] == a["report_json"].replace("REPORT.json", "REPORT.md"), "addition pair")
        need(sha256(source_bytes(a["report_json"])) == a["json_sha256"] and sha256(source_bytes(a["report_md"])) == a["md_sha256"], "addition hashes")

    selected = [r for r in inventory if r["inventory_id"] == "R346"]
    need(len(selected) == 1, "R346 selector")
    row = selected[0]
    cohort = list(csv.DictReader((HERE / "frozen-cohort.csv").open()))
    need(cohort == [{"inventory_id": "R346", "cohort": row["cohort"], "report_json": row["report_json_at_commit"], "report_md": row["report_md_at_commit"]}], "cohort row")
    need((m["inventory_id"], m["cohort"], m["title"], m["report_json"], m["report_md"]) == ("R346", row["cohort"], row["title"], row["report_json_at_commit"], row["report_md_at_commit"]), "row identity")
    md_bytes, meta_bytes = source_bytes(m["report_md"]), source_bytes(m["report_json"])
    need((sha256(md_bytes), sha256(meta_bytes)) == (m["frozen_md_sha256"], m["frozen_json_sha256"]), "frozen report bytes")
    md = md_bytes.decode()
    meta = json.loads(meta_bytes)
    need(meta["subjects"] == m["frozen_subjects_exact"] == json.loads(row["exact_pinned_subject_identities_json"]), "subject pin identities")
    lines = md.splitlines()
    start = lines.index("## Summary") + 1
    while not lines[start].strip():
        start += 1
    end = lines.index("## Applicability")
    summary = "\n".join(lines[start:end]).rstrip()
    paragraphs = summary.split("\n\n")
    need(m["claim_locator"] == {"heading": "## Summary", "line": start + 1} and m["full_summary_exact"] == summary and len(paragraphs) == 6, "exact section")
    need(m["inventory_claim_excerpt_exact_or_normalized"] == row["claim_or_cell_to_recheck"], "inventory excerpt")
    need([p["number"] for p in m["summary_paragraphs"]] == list(range(1, 7)), "paragraph numbering")
    need([p["exact_excerpt"] for p in m["summary_paragraphs"]] == paragraphs, "paragraph excerpts")
    need(all(p["runtime_result"] == "unexecuted_in_this_review" and set(p["mapped_doc_paths"]) <= DOCS.keys() for p in m["summary_paragraphs"]), "paragraph bounds")
    need(m["summary_paragraphs"][3]["source_result"] == "mapped_docs_unchanged_adjacent_dice_api_delta_no_behavior_conclusion", "DICE claim bound")
    need(m["old_source_commit"] == OLD and m["selected_current_commit"] == NEW, "old/new identities")
    subject = next(s for s in meta["subjects"] if s["name"] == "Buck2 architecture and DICE")
    need(subject["identity"]["revision"] == OLD and subject["identity"]["repository"] == "facebook/buck2", "original source pin")
    for path, blob in DOCS.items():
        need(path in md and f"Blob: `{blob}`" in md, "original document evidence")
    need(set(x["path"] for x in m["mapped_doc_files"]) == DOCS.keys(), "four mapped docs")
    need(set(x["path"] for x in m["adjacent_dice_files"]) == ADJACENT.keys(), "three adjacent paths")

    observation_bytes = (HERE / "official-source-observation.json").read_bytes()
    need(sha256(observation_bytes) == m["official_observation_sha256"], "observation snapshot hash")
    o = json.loads(observation_bytes)
    refs = {ref: commit for commit, ref in (line.split("\t") for line in o["raw_ls_remote"].splitlines())}
    need(o["repository"] == "facebook/buck2" and o["branch"] == "main" and o["old_commit"] == OLD and o["selected_current_commit"] == NEW, "recorded source identity")
    need(refs == o["refs"] and refs["HEAD"] == refs["refs/heads/main"] == NEW, "raw main refs")
    need(refs["refs/tags/2026-09-15"] == TAG and refs["refs/tags/latest"] == LATEST, "tag identities")
    compare = o["compare"]
    need((compare["status"], compare["ahead_by"], compare["behind_by"], compare["total_commits"], compare["returned_file_count"], compare["file_list_complete"]) == ("ahead", 29, 0, 29, 114, True), "forward comparison")
    changed = compare["changed_files"]
    changed_paths = [f["path"] for f in changed]
    need(len(changed) == len(set(changed_paths)) == 114, "complete unique changed paths")
    need(not (DOCS.keys() & set(changed_paths)) and ADJACENT.keys() <= set(changed_paths), "claim path overlap")
    by_changed = {f["path"]: f for f in changed}
    need(o["release_endpoint"] == {"status": "not_found", "http_status": 404}, "release endpoint bound")
    tag = o["dated_tag"]
    need((tag["name"], tag["tag_ref_type"], tag["tag_ref_sha"], tag["peeled_type"], tag["peeled_commit"]) == ("2026-09-15", "commit", TAG, "commit", TAG), "date tag peel")
    need(tag["relation_to_old_pin"] == {"status": "ahead", "ahead_by": 514, "behind_by": 0} and tag["relation_to_selected_main"] == {"status": "ahead", "ahead_by": 543, "behind_by": 0}, "tag ancestry")
    tag_bytes = (HERE / "official-tag-refs.txt").read_bytes()
    need(sha256(tag_bytes) == m["official_tag_refs_sha256"] == o["tag_inventory"]["raw_ls_remote_sha256"], "tag snapshot hash")
    tag_lines = [line.split("\t") for line in tag_bytes.decode().splitlines()]
    date_tags = [(ref, commit) for commit, ref in tag_lines if re.fullmatch(r"refs/tags/\d{4}-\d{2}-\d{2}", ref)]
    need(len(tag_lines) == 79 and len(date_tags) == 77 and len(date_tags) == len(set(ref for ref, _ in date_tags)), "tag census")
    need(max(date_tags)[0] == "refs/tags/2026-09-15" and dict(date_tags)["refs/tags/2026-09-15"] == TAG, "newest dated tag")
    need(o["tag_inventory"]["total_ref_lines"] == 79 and o["tag_inventory"]["date_named_tags"] == 77 and o["tag_inventory"]["latest_date_named_tag"] == {"name": "2026-09-15", "ref_sha": TAG}, "recorded tag census")
    recheck_bytes = (HERE / "official-ref-recheck.txt").read_bytes()
    recheck = o["floating_latest_recheck"]
    need(sha256(recheck_bytes) == m["official_ref_recheck_sha256"] == recheck["raw_ls_remote_sha256"], "live ref recheck bytes")
    rechecked_refs = {ref: commit for commit, ref in (line.split("\t") for line in recheck_bytes.decode().splitlines())}
    need(rechecked_refs == recheck["refs"], "live ref recheck parse")
    need(recheck["observed_at_utc"] == "2026-09-30T21:55:50Z" and recheck["original_snapshot_latest_ref_sha"] == LATEST, "floating tag observation times")
    need(rechecked_refs == {"HEAD": NEW, "refs/heads/main": NEW, "refs/tags/2026-09-15": TAG, "refs/tags/latest": NEW}, "floating latest moved to selected main")
    need(recheck["interpretation"] == "floating_tag_moved_from_original_snapshot_to_selected_main", "floating tag interpretation")

    for row in o["mapped_files"]:
        path = row["path"]
        need(path in DOCS and row["old"]["git_blob_sha1"] == row["new"]["git_blob_sha1"] == DOCS[path], "mapped doc blob continuity")
        need(row["old"]["content_sha256"] == row["new"]["content_sha256"] and row["old"]["size"] == row["new"]["size"], "mapped doc bytes continuity")
        need(row["old"]["url"].endswith(f"/{OLD}/{path}") and row["new"]["url"].endswith(f"/{NEW}/{path}"), "mapped source URLs")
        need(next(x for x in m["mapped_doc_files"] if x["path"] == path) == {"path": path, "old_blob_sha1": DOCS[path], "new_blob_sha1": DOCS[path]}, "mapped matrix blob")
    need(len(o["mapped_files"]) == 4, "mapped file count")
    for row in o["adjacent_dice_files"]:
        path = row["path"]
        need(path in ADJACENT, "adjacent path")
        old, new, token = ADJACENT[path]
        need(row["old"]["git_blob_sha1"] == old and row["new"]["git_blob_sha1"] == new and old != new, "adjacent blob delta")
        need(row["old"]["content_sha256"] != row["new"]["content_sha256"], "adjacent content delta")
        need(row["old"]["url"].endswith(f"/{OLD}/{path}") and row["new"]["url"].endswith(f"/{NEW}/{path}"), "adjacent source URLs")
        need(by_changed[path]["blob_sha"] == new and token in (by_changed[path]["patch"] or ""), "claim-adjacent patch")
        need(next(x for x in m["adjacent_dice_files"] if x["path"] == path) == {"path": path, "old_blob_sha1": old, "new_blob_sha1": new}, "adjacent matrix blob")
    need(len(o["adjacent_dice_files"]) == 3, "adjacent file count")
    need(m["source_result"] == "mapped_docs_unchanged_adjacent_dice_api_delta_no_architecture_or_behavior_conclusion" and m["runtime_result"] == "unexecuted_in_this_review" and m["anneal_product_result"] == "unassessed" and m["full_source_archive_sha256"] is None, "result boundaries")
    print("OK: R346 exact six-paragraph claim and pins; 581/605 corpus and 24 additions; Buck2 29-commit ancestry, 114 paths, four unchanged docs and three adjacent DICE source deltas; floating latest rechecked; runtime unexecuted")


if __name__ == "__main__":
    try:
        run()
    except Exception as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        raise
