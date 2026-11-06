#!/usr/bin/env python3
"""Offline R389 frozen-corpus and six-repository source checker."""

import csv
import hashlib
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE = "ebcdcadb63fefd1e6c0f46cb2030270ae3232837"
FROZEN = "2720194c6f74fe5489428adecc1ded39df98b096"
PINS = {
    "dafny-lang/dafny": ("5f717bf447b19d38cad1b69b1bf9a9f102feccfb", "Source/DafnyCore/Verifier/BoogieGenerator.cs", "f097f9c6be4b349b913c9df6853687fb57047fdf"),
    "boogie-org/boogie": ("fcecf73a49d11ad3ab16729abd03169e5ecfd938", "README.md", "422b2f8869a30ae6c5fd8056a159c1000f2da4ff"),
    "viperproject/silver": ("da1c8993b66feb39976e3609e2580a4661137a0f", "src/main/scala/viper/silver/verifier/VerificationResult.scala", "95980f6c5d21d2bf264ec388ddd6a885f5b494f0"),
    "viperproject/silicon": ("6ceff8be6ba55d858b7d018fdfeb866b7e8aa0ed", "README.md", "d4983b9cdbd67dcc0bce44d67c3fa55bf299540d"),
    "viperproject/carbon": ("6421cfda16d35f37cb9a7966f04fcd2d96abdda2", "README.md", "3146d1b9a61dfa66d547c18e08cecde8a7317dee"),
    "viperproject/viperserver": ("4cc5bbbe18d4a83e4b398da3904ba9696256611b", "README.md", "a35027560fcf3580590277758797a0c41bb43d2d"),
}
CLAIM_MAP = {
    "boogie-ivl-boundary": ["boogie-org/boogie"],
    "dafny-batch-layer": ["dafny-lang/dafny"],
    "backend-attempt-instability": [],
    "viper-multiple-backends": ["viperproject/silicon", "viperproject/carbon"],
    "viper-result-provenance": ["viperproject/silver", "viperproject/viperserver"],
    "anneal-conditional-obligation-interface": [],
}
RELEASES = {
    "dafny-lang/dafny": ("v4.11.0", "a04eea4dab324219e438f94ccc5ff0abcad11d86", "fcb2042d6d043a2634f0854338c08feeaaaf4ae2", "diverged", 68, 3),
    "boogie-org/boogie": ("v3.5.7", "01a4d1fe1b380c6343c1909ef38ffc510b812957", "01a4d1fe1b380c6343c1909ef38ffc510b812957", "ahead", 14, 0),
    "viperproject/silver": ("v.21.07-release", "8da1aea1e1027a9e9f4672e03159b0f91659d5b9", "3ea54220f1d2bc4adcc3151fa2080c198dbbd641", "ahead", 905, 0),
    "viperproject/viperserver": ("v.26.08-release", "7f07f320e713555959860b08e062545adfb123f2", "99be0e6df388579d77368a41f29a8bae1a2c4400", "ahead", 2, 0),
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


def parse_refs(data):
    rows = [line.split("\t") for line in data.decode().splitlines()]
    need(all(len(row) == 2 for row in rows), "raw ref shape")
    return {ref: commit for commit, ref in rows}


def run():
    m = json.loads((HERE / "matrix.json").read_text())
    need((m["schema"], m["baseline_reference_commit"], m["frozen_reference_commit"]) == (1, BASE, FROZEN), "corpus IDs")
    need((m["baseline_count"], m["current_count"]) == (581, 611), "corpus counts")
    inventory_bytes = (HERE / "version-inventory-ebcdcad-581.csv").read_bytes()
    need(sha256(inventory_bytes) == m["baseline_inventory_sha256"], "inventory hash")
    inventory = list(csv.DictReader(inventory_bytes.decode().splitlines()))
    baseline = set((HERE / "baseline-report-paths.txt").read_text().splitlines())
    frozen = paths_at(FROZEN)
    need(len(inventory) == len(baseline) == len(paths_at(BASE)) == 581, "baseline size")
    need(baseline == paths_at(BASE) == {r["report_json_at_commit"] for r in inventory}, "baseline paths")
    need(len(frozen) == 611 and baseline <= frozen, "frozen census")
    additions = m["added_after_baseline"]
    need(len(additions) == 30 and {a["report_json"] for a in additions} == frozen - baseline, "30 additions")
    for a in additions:
        need(a["report_md"] == a["report_json"].replace("REPORT.json", "REPORT.md"), "addition pair")
        need(sha256(frozen_bytes(a["report_json"])) == a["json_sha256"] and sha256(frozen_bytes(a["report_md"])) == a["md_sha256"], "addition hashes")

    selected = [r for r in inventory if r["inventory_id"] == "R389"]
    need(len(selected) == 1, "R389 selector")
    row = selected[0]
    cohort = list(csv.DictReader((HERE / "frozen-cohort.csv").open()))
    need(cohort == [{"inventory_id": "R389", "cohort": row["cohort"], "report_json": row["report_json_at_commit"], "report_md": row["report_md_at_commit"]}], "cohort selector")
    need((m["inventory_id"], m["cohort"], m["title"], m["report_json"], m["report_md"]) == ("R389", row["cohort"], row["title"], row["report_json_at_commit"], row["report_md_at_commit"]), "row identity")
    md_bytes, meta_bytes, map_bytes = (frozen_bytes(m[k]) for k in ("report_md", "report_json", "evidence_map_path"))
    need((sha256(md_bytes), sha256(meta_bytes), sha256(map_bytes)) == (m["frozen_md_sha256"], m["frozen_json_sha256"], m["frozen_evidence_map_sha256"]), "original hashes")
    md, meta, evidence = md_bytes.decode(), json.loads(meta_bytes), json.loads(map_bytes)
    need(meta["subjects"] == m["frozen_subjects_exact"] == json.loads(row["exact_pinned_subject_identities_json"]), "source subjects")
    lines = md.splitlines()
    start = lines.index("## Summary") + 1
    while not lines[start].strip():
        start += 1
    end = lines.index("## Applicability")
    summary = "\n".join(lines[start:end]).rstrip()
    paragraphs = summary.split("\n\n")
    need(m["claim_locator"] == {"heading": "## Summary", "line": start + 1} and m["full_summary_exact"] == summary and len(paragraphs) == 5, "exact Summary")
    need(m["inventory_claim_excerpt_exact_or_normalized"] == row["claim_or_cell_to_recheck"], "inventory excerpt")
    need(m["summary_paragraphs"] == [{"number": n, "exact_excerpt": p, "runtime_result": "unexecuted_in_this_review"} for n, p in enumerate(paragraphs, 1)], "summary paragraphs")
    findings = [{"heading": line, "line": n + 1} for n, line in enumerate(lines) if line.startswith("### ") and n < lines.index("## Evidence")]
    need(m["finding_locators"] == findings and len(findings) == 7, "Findings locators")
    expected_claims = [{"id": c["id"], "exact_supports": c["supports"], "kind": c["kind"], "exact_evidence": c["evidence"], "mapped_repositories": CLAIM_MAP[c["id"]], "source_result": "same_pinned_commit_zero_forward_range" if CLAIM_MAP[c["id"]] else "historical_or_derived_no_current_source_recheck", "runtime_result": "unexecuted_in_this_review"} for c in evidence["claims"]]
    need(m["evidence_claims"] == expected_claims and len(expected_claims) == 6, "six exact evidence claims")
    pins = [{"repository": s["identity"]["repository"], "revision": s["identity"]["revision"], "path": s["identity"]["path"]} for s in meta["subjects"][:6]]
    need(m["six_independent_source_pins"] == pins and {p["repository"] for p in pins} == PINS.keys(), "six source pins")

    obs_bytes = (HERE / "official-source-observation.json").read_bytes()
    need(sha256(obs_bytes) == m["official_observation_sha256"], "observation hash")
    obs = json.loads(obs_bytes)
    need(obs["schema"] == 1 and obs["observed_at_utc"] == "2026-09-30" and len(obs["repositories"]) == 6, "observation shape")
    need({r["repository"] for r in obs["repositories"]} == PINS.keys(), "independent repos")
    for r in obs["repositories"]:
        repo = r["repository"]
        pin, path, expected_blob = PINS[repo]
        slug = repo.split("/")[-1]
        need((r["pinned_commit"], r["selected_current_commit"], r["default_branch"], r["raw_ref_path"]) == (pin, pin, "master", f"{slug}-refs.txt"), "full commit identity")
        raw = (HERE / r["raw_ref_path"]).read_bytes()
        need(sha256(raw) == r["raw_ref_sha256"] and parse_refs(raw) == r["refs"] == {"HEAD": pin, "refs/heads/master": pin}, "official raw refs")
        need(r["compare"] == {"status": "identical", "ahead_by": 0, "behind_by": 0, "total_commits": 0, "changed_paths": []}, "zero-forward source comparison")
        f = r["mapped_file"]
        need(f["path"] == path and f["old_blob_sha1"] == f["current_blob_sha1"] == expected_blob, "claim mapped blob")
        data = (HERE / f["snapshot_path"]).read_bytes()
        need(f["snapshot_path"] == f"snapshots/{slug}/{path}" and blob_sha(data) == expected_blob and sha256(data) == f["content_sha256"] and len(data) == f["size"], "preserved source bytes")
        need(f["raw_url"] == f"https://raw.githubusercontent.com/{repo}/{pin}/{path}", "commit-pinned source URL")
        need(expected_blob in md and f"{repo}@{pin}" in md, "original evidence locator")
        rel = r["release"]
        need(rel["api_url"] == f"https://api.github.com/repos/{repo}/releases/latest", "release endpoint")
        if repo in RELEASES:
            tag, tag_obj, peeled, status, ahead, behind = RELEASES[repo]
            tag_bytes = (HERE / rel["raw_tag_ref_path"]).read_bytes()
            refs = parse_refs(tag_bytes)
            expected_refs = {f"refs/tags/{tag}": tag_obj}
            if peeled != tag_obj:
                expected_refs[f"refs/tags/{tag}^{{}}"] = peeled
            need(sha256(tag_bytes) == rel["raw_tag_ref_sha256"] and refs == expected_refs, "release tag peel")
            need((rel["status"], rel["tag_name"], rel["tag_ref_object_sha"], rel["peeled_commit"], rel["tag_ref_type"]) == ("found", tag, tag_obj, peeled, "annotated" if tag_obj != peeled else "lightweight"), "release identity")
            need(rel["relation_to_main"] == {"status": status, "ahead_by": ahead, "behind_by": behind, "total_commits": ahead}, "release ancestry")
            need(rel["html_url"] == f"https://github.com/{repo}/releases/tag/{tag}", "official release URL")
        else:
            need(rel == {"status": "not_found", "api_url": f"https://api.github.com/repos/{repo}/releases/latest", "http_status": 404}, "no GitHub Release object")
    need(m["source_result"] == "six_default_branches_equal_exact_report_pins_zero_forward_source_range" and m["runtime_result"] == "unexecuted_in_this_review" and m["anneal_product_result"] == "unassessed", "result bounds")
    print("OK: R389 exact five-paragraph and six-claim corpus; 581/611 with 30 additions; six same-commit official refs/blobs; releases kept separate; runtime unexecuted")


if __name__ == "__main__":
    try:
        run()
    except Exception as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        raise
