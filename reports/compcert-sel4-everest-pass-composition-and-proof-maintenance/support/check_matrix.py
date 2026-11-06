#!/usr/bin/env python3
"""Offline R507/R578 frozen-corpus and official-source checker."""

import csv
import hashlib
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE = "ebcdcadb63fefd1e6c0f46cb2030270ae3232837"
FROZEN = "47d8250bff3ea17f1fbb4340370032e03692617b"
PINS = {
    "seL4/l4v": ("6b4076aeb35f7803b7c232963e5f996545e3acb5", "6b4076aeb35f7803b7c232963e5f996545e3acb5", "master", 2),
    "seL4/verification-manifest": ("f1f7a4289585e9610733ea041c1849e46af9701b", "f1f7a4289585e9610733ea041c1849e46af9701b", "master", 1),
    "AbsInt/CompCert": ("74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6", "66a9fd06ef88619cc94765ca995a1018f7259b5c", "master", 3),
    "hacl-star/hacl-star": ("504c2987452f87fe44bce9b9f12e19d6e051761f", "504c2987452f87fe44bce9b9f12e19d6e051761f", "main", 1),
    "FStarLang/karamel": ("9abbb865b10a0cd5c557da81c024c3965cb6ff53", "9abbb865b10a0cd5c557da81c024c3965cb6ff53", "master", 2),
    "project-everest/everest": ("2a3f67dab56be02d1793b2801ef08f368423a3ac", "2a3f67dab56be02d1793b2801ef08f368423a3ac", "master", 1),
}
RELEASES = {
    "seL4/l4v": ("seL4-16.0.0", "0d4cc5d902deaa275d1019dccb39f230934bfaa1", "611fc6472917bc1ce38164da5eef0026c2a862e5", 92),
    "AbsInt/CompCert": ("v3.18", "14d616046360a0b2611ebdfc2f98368af402e1f7", "14d616046360a0b2611ebdfc2f98368af402e1f7", 14),
    "hacl-star/hacl-star": ("ocaml-v0.4.5", "172edb4f76cc5ab1f0afaf24a192424df39bd415", "d3f857dc195918692bc7d9c99d650c9d41104245", 2898),
    "FStarLang/karamel": ("v0.9.6.0", "34cff2cd74a1f63a06551dd2e7627ef0878e07ee", "34cff2cd74a1f63a06551dd2e7627ef0878e07ee", 3002),
}
COMP_CHANGED = {"cfrontend/CPragmas.ml", "common/Switch.v", "common/Switchaux.ml", "cparser/Lexer.mll", "test"}


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
    need((m["baseline_count"], m["current_count"]) == (581, 613), "corpus counts")
    inventory_bytes = (HERE / "version-inventory-ebcdcad-581.csv").read_bytes()
    need(sha256(inventory_bytes) == m["baseline_inventory_sha256"], "inventory hash")
    inventory = list(csv.DictReader(inventory_bytes.decode().splitlines()))
    baseline = set((HERE / "baseline-report-paths.txt").read_text().splitlines())
    frozen = paths_at(FROZEN)
    need(len(inventory) == len(baseline) == len(paths_at(BASE)) == 581, "baseline size")
    need(baseline == paths_at(BASE) == {r["report_json_at_commit"] for r in inventory}, "baseline paths")
    need(len(frozen) == 613 and baseline <= frozen, "frozen census")
    additions = m["added_after_baseline"]
    need(len(additions) == 32 and {a["report_json"] for a in additions} == frozen - baseline, "32 additions")
    for a in additions:
        need(a["report_md"] == a["report_json"].replace("REPORT.json", "REPORT.md"), "addition pair")
        need(sha256(frozen_bytes(a["report_json"])) == a["json_sha256"] and sha256(frozen_bytes(a["report_md"])) == a["md_sha256"], "addition hashes")

    selected = {r["inventory_id"]: r for r in inventory if r["inventory_id"] in {"R507", "R578"}}
    need(selected.keys() == {"R507", "R578"}, "two distinct selectors")
    cohort = list(csv.DictReader((HERE / "frozen-cohort.csv").open()))
    need(cohort == [{"inventory_id": rid, "cohort": selected[rid]["cohort"], "report_json": selected[rid]["report_json_at_commit"], "report_md": selected[rid]["report_md_at_commit"]} for rid in ("R507", "R578")], "cohort exactness")
    need([r["inventory_id"] for r in m["rows"]] == ["R507", "R578"], "matrix row order")
    maps = {}
    for r in m["rows"]:
        rid = r["inventory_id"]
        inventory_row = selected[rid]
        need((r["classification"], r["cohort"], r["title"], r["report_json"], r["report_md"]) == (inventory_row["classification"], inventory_row["cohort"], inventory_row["title"], inventory_row["report_json_at_commit"], inventory_row["report_md_at_commit"]), "per-report inventory identity")
        md_bytes, meta_bytes, map_bytes, auxiliary_bytes = (frozen_bytes(r[k]) for k in ("report_md", "report_json", "source_map_path", "auxiliary_path"))
        need((sha256(md_bytes), sha256(meta_bytes), sha256(map_bytes), sha256(auxiliary_bytes)) == (r["frozen_md_sha256"], r["frozen_json_sha256"], r["frozen_source_map_sha256"], r["frozen_auxiliary_sha256"]), "per-report frozen hashes")
        md, meta, source_map, auxiliary = md_bytes.decode(), json.loads(meta_bytes), json.loads(map_bytes), json.loads(auxiliary_bytes)
        need(meta["subjects"] == r["frozen_subjects_exact"] == json.loads(inventory_row["exact_pinned_subject_identities_json"]), "per-report subjects")
        need(source_map == r["source_map_exact"] and auxiliary == r["auxiliary_exact"], "frozen source/support maps")
        lines = md.splitlines()
        start = lines.index("## Summary") + 1
        while not lines[start].strip():
            start += 1
        end = lines.index("## Applicability")
        summary = "\n".join(lines[start:end]).rstrip()
        paragraphs = summary.split("\n\n")
        need(r["claim_locator"] == {"heading": "## Summary", "line": start + 1} and r["full_summary_exact"] == summary, "exact Summary")
        need(r["inventory_claim_excerpt_exact_or_normalized"] == inventory_row["claim_or_cell_to_recheck"], "inventory excerpt")
        need(r["summary_paragraphs"] == [{"number": n, "exact_excerpt": p, "runtime_result": "unexecuted_in_this_review"} for n, p in enumerate(paragraphs, 1)], "exact summary paragraphs")
        findings = [{"heading": line, "line": n + 1} for n, line in enumerate(lines) if line.startswith("### ") and n < lines.index("## Evidence")]
        need(r["finding_locators"] == findings and len(findings) == (19 if rid == "R507" else 7), "Findings locators")
        need(r["runtime_result"] == "unexecuted_in_this_review" and r["anneal_product_result"] == "unassessed", "row result bounds")
        maps[rid] = source_map
    need(selected["R578"]["classification"] == "no_newer_release", "R578 classification preserved")
    comp507 = next(s for s in maps["R507"]["sources"] if s.get("id") == "compcert-core")
    comp578 = {s["path"]: s["blob"] for s in maps["R578"]["sources"] if s.get("repository") == "AbsInt/CompCert"}
    need(comp507["files"] == comp578 and len(comp578) == 3, "shared CompCert pin and blobs, distinct claims")

    obs_bytes = (HERE / "official-source-observation.json").read_bytes()
    need(sha256(obs_bytes) == m["official_observation_sha256"], "observation hash")
    obs = json.loads(obs_bytes)
    need(obs["schema"] == 1 and obs["observed_at_utc"] == "2026-09-30" and len(obs["repositories"]) == 6, "observation shape")
    need({r["repository"] for r in obs["repositories"]} == PINS.keys(), "six independent repositories")
    r507_sources = [s for s in maps["R507"]["sources"] if s.get("repository") in PINS]
    expected_files = {}
    for s in r507_sources:
        paths = s.get("files") or {s["path"]: s["blob"]}
        for path, blob in paths.items():
            expected_files[(s["repository"], path)] = (s["id"], blob)
    need(len(expected_files) == 10, "ten R507 source files")
    for r in obs["repositories"]:
        repo = r["repository"]
        pin, current, branch, count = PINS[repo]
        slug = repo.replace("/", "--")
        need((r["pinned_commit"], r["selected_current_commit"], r["default_branch"], r["raw_ref_path"]) == (pin, current, branch, f"{slug}-refs.txt"), "full repo identity")
        raw = (HERE / r["raw_ref_path"]).read_bytes()
        need(sha256(raw) == r["raw_ref_sha256"] and parse_refs(raw) == r["refs"] == {"HEAD": current, f"refs/heads/{branch}": current}, "official refs")
        comp = r["compare"]
        if repo == "AbsInt/CompCert":
            need((comp["status"], comp["ahead_by"], comp["behind_by"], comp["total_commits"], comp["returned_file_count"]) == ("ahead", 4, 0, 4, 5), "CompCert forward range")
            need({f["path"] for f in comp["changed_files"]} == COMP_CHANGED, "complete CompCert changed paths")
            need(len({f["path"] for f in comp["changed_files"]}) == 5, "unique CompCert paths")
        else:
            need(comp == {"status": "identical", "ahead_by": 0, "behind_by": 0, "total_commits": 0, "returned_file_count": 0, "changed_files": []}, "same-commit source line")
        need(len(r["mapped_files"]) == count and {f["path"] for f in r["mapped_files"]} == {path for rr, path in expected_files if rr == repo}, "mapped file inventory")
        for f in r["mapped_files"]:
            path = f["path"]
            source_id, expected_blob = expected_files[(repo, path)]
            need(f["source_id"] == source_id and f["pinned_blob_sha1"] == f["current_blob_sha1"] == expected_blob, "mapped original/current blob")
            data = (HERE / f["snapshot_path"]).read_bytes()
            need(f["snapshot_path"] == f"snapshots/{slug}/{path}" and blob_sha(data) == expected_blob and sha256(data) == f["content_sha256"] and len(data) == f["size"], "snapshot source bytes")
            need(f["old_raw_url"] == f"https://raw.githubusercontent.com/{repo}/{pin}/{path}" and f["new_raw_url"] == f"https://raw.githubusercontent.com/{repo}/{current}/{path}", "commit-pinned source URLs")
        need(not ({f["path"] for f in r["mapped_files"]} & {f["path"] for f in comp["changed_files"]}), "claim files absent from changed paths")
        release = r["release"]
        need(release["api_url"] == f"https://api.github.com/repos/{repo}/releases/latest", "release endpoint")
        if repo in RELEASES:
            tag, obj, peeled, ahead = RELEASES[repo]
            raw_tag = (HERE / release["raw_tag_ref_path"]).read_bytes()
            refs = {f"refs/tags/{tag}": obj}
            if obj != peeled:
                refs[f"refs/tags/{tag}^{{}}"] = peeled
            need(sha256(raw_tag) == release["raw_tag_ref_sha256"] and parse_refs(raw_tag) == refs, "release tag refs and peel")
            need((release["status"], release["tag_name"], release["tag_ref_object_sha"], release["peeled_commit"], release["tag_ref_type"]) == ("found", tag, obj, peeled, "annotated" if obj != peeled else "lightweight"), "release identity")
            need(release["relation_to_pinned"] == {"status": "ahead", "ahead_by": ahead, "behind_by": 0, "total_commits": ahead}, "release ancestry")
            need(release["html_url"] == f"https://github.com/{repo}/releases/tag/{tag}", "official release URL")
        else:
            need(release == {"status": "not_found", "api_url": f"https://api.github.com/repos/{repo}/releases/latest", "http_status": 404}, "no GitHub Release object")
    need(m["runtime_result"] == "unexecuted_in_this_review" and m["anneal_product_result"] == "unassessed", "overall result bounds")
    print("OK: distinct R507/R578 claims; 581/613 corpus and 32 additions; five same-pin repos, CompCert +4/5 with three unchanged mapped blobs; runtime unexecuted")


if __name__ == "__main__":
    try:
        run()
    except Exception as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        raise
