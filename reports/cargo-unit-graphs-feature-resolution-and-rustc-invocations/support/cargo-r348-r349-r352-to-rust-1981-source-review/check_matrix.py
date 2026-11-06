#!/usr/bin/env python3
"""Offline frozen-corpus and official-source check for Cargo R348/R349/R352."""

from __future__ import annotations

import csv
import difflib
import hashlib
import json
import re
import subprocess
from pathlib import Path


SUPPORT = Path(__file__).resolve().parent
ROOT = SUPPORT.parents[2]
M = json.loads((SUPPORT / "matrix.json").read_text())
O = json.loads((SUPPORT / "source-observation.json").read_text())


def ensure(value: bool, name: str) -> None:
    if not value:
        raise AssertionError(name)


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def git(*args: str) -> bytes:
    return subprocess.check_output(["git", *args], cwd=ROOT)


def frozen(path: str) -> bytes:
    return git("show", M["frozen_reference_commit"] + ":" + path)


def source(side: str, path: str) -> str:
    return (SUPPORT / "snapshots" / side / path).read_text()


def main() -> None:
    ensure(M["frozen_reference_commit"] == "1b6f146d7951402e10102354a131b5cee9c5f855", "frozen parent")
    ensure(git("rev-parse", "HEAD").decode().strip() == M["frozen_reference_commit"], "checkout HEAD")
    ensure(M["baseline_reference_commit"] == "ebcdcadb63fefd1e6c0f46cb2030270ae3232837", "baseline parent")
    inventory = (SUPPORT / "version-inventory-ebcdcad-581.csv").read_bytes()
    ensure(sha(inventory) == M["baseline_inventory_sha256"], "inventory hash")
    rows = list(csv.DictReader(inventory.decode().splitlines()))
    ensure(len(rows) == M["baseline_count"] == 581, "inventory count")
    frozen_paths = [p for p in git("ls-tree", "-r", "--name-only", M["frozen_reference_commit"], "reports").decode().splitlines() if p.endswith("/REPORT.json")]
    ensure(len(frozen_paths) == M["frozen_report_count"] == 622, "frozen report count")
    selected = list(csv.DictReader((SUPPORT / "frozen-cohort.csv").open()))
    ensure([r["inventory_id"] for r in selected] == ["R348", "R349", "R352"], "exact selector")
    ensure([r["inventory_id"] for r in M["rows"]] == ["R348", "R349", "R352"], "matrix rows")
    norm = lambda s: re.sub(r"\s+", " ", s.replace("`", "")).strip()
    for row, selector in zip(M["rows"], selected):
        inv = rows[int(row["inventory_id"][1:]) - 1]
        ensure(inv["inventory_id"] == row["inventory_id"], "inventory row")
        ensure(inv["cohort"] == row["cohort"] == "Cargo/rustc nightly-2026-05-31", "cohort")
        ensure(inv["title"] == row["title"], "title")
        for kind in ("json", "md"):
            path = row["report_" + kind]
            ensure(path == inv["report_" + kind + "_at_commit"] == selector["report_" + kind], "report path")
            ensure(sha(frozen(path)) == row["report_" + kind + "_sha256"], "frozen report hash")
        md = frozen(row["report_md"]).decode()
        source_json = json.loads(frozen(row["report_json"]))
        ensure(source_json["subjects"] == row["frozen_subjects_exact"], "original subjects")
        ensure(row["inventory_claim_excerpt_normalized"] == inv["claim_or_cell_to_recheck"], "inventory excerpt")
        ensure(norm(row["inventory_claim_excerpt_normalized"]) in norm(md), "excerpt occurs in report")
        summary = md.split("## Summary\n", 1)[1].split("\n## ", 1)[0].strip()
        ensure(summary == row["full_summary_exact"], "exact Summary")
        paragraphs = summary.split("\n\n")
        ensure([p["exact_excerpt"] for p in row["claim_clauses"]] == paragraphs, "exact claim clauses")
        ensure([p["paragraph"] for p in row["claim_clauses"]] == list(range(1, len(paragraphs) + 1)), "claim numbering")
        ensure(all(p["runtime_status"] == "unexecuted_in_this_review" for p in row["claim_clauses"]), "claim runtime")
        ensure(row["runtime_status"] == "unexecuted_in_this_review" and row["product_status"] == "unassessed", "row bounds")
        ensure(row["crosswalk_status"] == "not_updated", "crosswalk bound")
        for companion in row.get("companion_files", []):
            ensure(sha(frozen(companion["path"])) == companion["sha256"], "R352 companion")

    old_gitlink = json.loads((SUPPORT / "rust-old-cargo-gitlink.json").read_text())
    new_gitlink = json.loads((SUPPORT / "rust-1981-cargo-gitlink.json").read_text())
    ensure(old_gitlink["type"] == new_gitlink["type"] == "submodule", "Cargo gitlink type")
    ensure(old_gitlink["submodule_git_url"] == new_gitlink["submodule_git_url"] == "https://github.com/rust-lang/cargo.git", "Cargo repo")
    ensure(old_gitlink["sha"] == M["old_cargo_commit"] == O["old_cargo_commit"], "old Cargo source")
    ensure(new_gitlink["sha"] == M["new_cargo_commit"] == O["new_cargo_commit"], "stable Cargo source")
    ensure(M["old_rust_commit"] == "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65", "old Rust identity")
    ensure(M["new_rust_tag_commit"] == "48a229ceaefd4985c50990b14116b6d856af0985", "new Rust identity")
    refs = (SUPPORT / "rust-tag-refs.txt").read_text().splitlines()
    ensure(refs == [
        "18ed059b1465ce6195154de3250a668f1dd3b1fa\trefs/tags/1.98.1",
        M["new_rust_tag_commit"] + "\trefs/tags/1.98.1^{}",
    ], "annotated tag peel")
    ensure(json.loads((SUPPORT / "rust-1981-release.json").read_text())["tag_name"] == "1.98.1", "release identity")
    comparison = json.loads((SUPPORT / "cargo-compare.json").read_text())
    for key in ("status", "ahead_by", "behind_by", "total_commits"):
        ensure(comparison[key] == M["cargo_compare"][key], "compare " + key)
    ensure((comparison["status"], comparison["ahead_by"], comparison["behind_by"]) == ("ahead", 219, 0), "forward Cargo ancestry")
    ensure(comparison["base_commit"]["sha"] == M["old_cargo_commit"], "compare base")
    ensure(comparison["commits"][-1]["sha"] == M["new_cargo_commit"], "compare tip")
    ensure(len(comparison["files"]) == M["cargo_compare"]["returned_file_count"] == 175, "compare files")
    ensure(len(comparison["commits"]) == M["cargo_compare"]["returned_commit_count"] == 219, "compare commits")

    ensure(sha((SUPPORT / "source-observation.json").read_bytes()) == M["source_observation_sha256"], "source manifest hash")
    ensure(len(O["files"]) == 17, "mapped path count")
    ensure(len(set(f["path"] for f in O["files"])) == 17, "unique mapped paths")
    changed = 0
    compared = {f["filename"]: f for f in comparison["files"]}
    for mapped in O["files"]:
        path = mapped["path"]
        for side, commit in (("old", M["old_cargo_commit"]), ("new", M["new_cargo_commit"])):
            identity = mapped[side]
            data = (SUPPORT / identity["snapshot"]).read_bytes()
            ensure(identity["commit"] == commit, "snapshot commit")
            ensure(identity["url"] == f"https://raw.githubusercontent.com/rust-lang/cargo/{commit}/{path}", "commit URL")
            ensure(len(data) == identity["size"] and sha(data) == identity["sha256"] and blob(data) == identity["git_blob_sha1"], "snapshot hashes: " + path)
        same = mapped["old"]["git_blob_sha1"] == mapped["new"]["git_blob_sha1"]
        ensure(same == mapped["same_blob"], "blob status")
        if same:
            ensure(path not in compared, "unchanged path in compare")
        else:
            changed += 1
            ensure(compared[path]["status"] == "modified" and compared[path]["sha"] == mapped["new"]["git_blob_sha1"], "official changed path")
            a = source("old", path).splitlines(keepends=True)
            b = source("new", path).splitlines(keepends=True)
            patch = "".join(difflib.unified_diff(a, b, fromfile="old/" + path, tofile="new/" + path, n=3)).encode()
            ensure((SUPPORT / mapped["diff_path"]).read_bytes() == patch, "exact mapped diff")
            ensure(sha(patch) == mapped["diff_sha256"], "diff hash")
    ensure(changed == 5, "five changed and twelve unchanged files")
    ensure(set(M["rows"][0]["mapped_source_paths"]) <= {f["path"] for f in O["files"]}, "R348 mapping")
    ensure(set(M["rows"][1]["mapped_source_paths"]) <= {f["path"] for f in O["files"]}, "R349 mapping")
    ensure(set(M["rows"][2]["mapped_source_paths"]) <= {f["path"] for f in O["files"]}, "R352 mapping")
    ensure(all(next(f for f in O["files"] if f["path"] == p)["same_blob"] for p in M["rows"][1]["mapped_source_paths"]), "R349 exact source continuity")
    doc = "src/doc/src/reference/unstable.md"
    section = lambda s: s.split("## unit-graph\n", 1)[1].split("\n## ", 1)[0]
    ensure(section(source("old", doc)) == section(source("new", doc)), "unchanged unit-graph section")
    compiler_old = source("old", "src/cargo/core/compiler/mod.rs")
    compiler_new = source("new", "src/cargo/core/compiler/mod.rs")
    ensure("if map.contains_key(&unit)" in compiler_old and "if dep.unit.target.is_custom_build()" in compiler_new, "dependency arg delta")
    comp_old = source("old", "src/cargo/core/compiler/compilation.rs")
    comp_new = source("new", "src/cargo/core/compiler/compilation.rs")
    ensure("HashMap<CompileKind, PathBuf>" in comp_old and "HashMap<CompileKind, BTreeSet<PathBuf>>" in comp_new, "search path delta")
    custom_old = source("old", "src/cargo/core/compiler/custom_build.rs")
    custom_new = source("new", "src/cargo/core/compiler/custom_build.rs")
    ensure('cmd.env("CARGO_TRIM_PATHS",' in custom_old and 'cmd.env("CARGO_TRIM_PATHS_SCOPE",' in custom_new and '"CARGO_TRIM_PATHS_REMAP"' in custom_new, "build-script env delta")
    ensure(M["runtime_status"] == "unexecuted_in_this_review" and M["product_status"] == "unassessed" and M["audit_disposition"] == "unchanged", "result bounds")
    print("PASS: exact R348/R349/R352, 622 frozen reports, 17 mapped files/34 snapshots (12 identical, 5 changed), Cargo gitlink ancestry; runtime unexecuted")


if __name__ == "__main__":
    main()
