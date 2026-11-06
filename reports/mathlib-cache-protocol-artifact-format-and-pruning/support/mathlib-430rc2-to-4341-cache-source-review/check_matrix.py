#!/usr/bin/env python3
"""Offline integrity check for the frozen four-row Mathlib source review."""

from __future__ import annotations

import csv
import hashlib
import json
import subprocess
from pathlib import Path


SUPPORT = Path(__file__).resolve().parent
ROOT = SUPPORT.parents[2]
MATRIX = json.loads((SUPPORT / "matrix.json").read_text())
OBS = json.loads((SUPPORT / "official-source-observation.json").read_text())
OLD = "ebcdcadb63fefd1e6c0f46cb2030270ae3232837"
FROZEN = "2ab4fa557cc4d42351aaec1d89d3e8e7801911b5"
IDS = ["R495", "R496", "R497", "R498"]


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git(*args: str) -> bytes:
    return subprocess.check_output(["git", *args], cwd=ROOT)


def blob(data: bytes) -> str:
    payload = b"blob " + str(len(data)).encode() + b"\0" + data
    return hashlib.sha1(payload).hexdigest()


def require(ok: bool, message: str) -> None:
    if not ok:
        raise AssertionError(message)


def frozen_bytes(path: str) -> bytes:
    return git("show", FROZEN + ":" + path)


def main() -> None:
    require(git("rev-parse", "HEAD").decode().strip() == FROZEN, "wrong parent HEAD")
    require(MATRIX["baseline_reference_commit"] == OLD, "baseline commit")
    require(MATRIX["frozen_reference_commit"] == FROZEN, "frozen commit")
    inventory = (SUPPORT / "version-inventory-ebcdcad-581.csv").read_bytes()
    require(sha(inventory) == MATRIX["baseline_inventory_sha256"], "inventory hash")
    inventory_rows = list(csv.DictReader(inventory.decode().splitlines()))
    require(len(inventory_rows) == MATRIX["baseline_count"] == 581, "baseline count")
    old_paths = (SUPPORT / "baseline-report-paths.txt").read_text().splitlines()
    require(len(old_paths) == 581 and len(set(old_paths)) == 581, "baseline paths")
    require(old_paths == [r["report_json_at_commit"] for r in inventory_rows], "inventory/path alignment")
    for path in old_paths:
        require(git("cat-file", "-e", OLD + ":" + path) == b"", "baseline Git path: " + path)
    current_paths = sorted(p for p in git("ls-tree", "-r", "--name-only", FROZEN, "reports").decode().splitlines() if p.endswith("/REPORT.json"))
    require(len(current_paths) == MATRIX["current_count"] == 617, "frozen report count")
    added = MATRIX["added_after_baseline"]
    require(len(added) == 36, "added count")
    require([x["report_json"] for x in added] == sorted(set(current_paths) - set(old_paths)), "added path reconciliation")
    for item in added:
        for ext in ("json", "md"):
            require(sha(frozen_bytes(item["report_" + ext])) == item[ext + "_sha256"], "added file hash")

    rows = MATRIX["rows"]
    require([r["inventory_id"] for r in rows] == IDS, "four exact inventory rows")
    selected = list(csv.DictReader((SUPPORT / "frozen-cohort.csv").open()))
    require([r["inventory_id"] for r in selected] == IDS, "selector CSV")
    for row, selector in zip(rows, selected):
        inv = inventory_rows[int(row["inventory_id"][1:]) - 1]
        require(inv["inventory_id"] == row["inventory_id"], "inventory ordering")
        for key in ("cohort", "report_json", "report_md"):
            require(selector[key] == row[key], "selector mapping " + key)
        require(row["report_json"] == inv["report_json_at_commit"], "inventory JSON mapping")
        require(row["report_md"] == inv["report_md_at_commit"], "inventory MD mapping")
        require(sha(frozen_bytes(row["report_json"])) == row["frozen_json_sha256"], "source JSON hash")
        md = frozen_bytes(row["report_md"])
        require(sha(md) == row["frozen_md_sha256"], "source MD hash")
        md_text = md.decode()
        original = json.loads(frozen_bytes(row["report_json"]))
        require(original["subjects"] == row["frozen_subjects_exact"], "original subject identities")
        require(row["full_summary_exact"] in md_text, "exact Summary block")
        for para in row["summary_paragraphs"]:
            require(para["exact_excerpt"] in md_text, "summary excerpt")
            require(para["runtime_result"] == "unexecuted_in_this_review", "summary runtime")
        require(md_text.splitlines()[row["claim_locator"]["line"] - 1].startswith(row["full_summary_exact"].splitlines()[0]), "summary claim line")
        require(row["claim_locator"]["heading"] in md_text.splitlines()[:row["claim_locator"]["line"]], "summary heading")
        for locator in row["finding_locators"]:
            lines = md_text.splitlines()
            require(lines[locator["line"] - 1] == locator["heading"], "frozen heading/line")
        for support in row["support_sources"]:
            content = frozen_bytes(support["path"])
            require(sha(content) == support["sha256"], "frozen support hash")
            require(json.loads(content) == support["exact_json"], "frozen support JSON")
        require(row["runtime_result"] == "unexecuted_in_this_review", "row runtime")
        require(row["anneal_product_result"] == "unassessed", "row product")

    require(sha((SUPPORT / "official-source-observation.json").read_bytes()) == MATRIX["official_observation_sha256"], "observation hash")
    repo_expect = {
        "mathlib": ("leanprover-community/mathlib4", "5450b53e5ddc75d46418fabb605edbf36bd0beb6", "d13f23b723b8a846827a245b89c10fc7d3f11612", 9),
        "lean": ("leanprover/lean4", "3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc", "5045d0056413266e57c625dcd7c365b10e377c52", 2),
    }
    for repo in OBS["repositories"]:
        key = repo["key"]
        name, old, new, count = repo_expect[key]
        require((repo["repository"], repo["old_commit"], repo["new_commit"]) == (name, old, new), "repo identity")
        require(repo["old_tag"] == "v4.30.0-rc2" and repo["new_tag"] == "v4.34.1", "repo tag names")
        require(repo["tag_refs"] == {"refs/tags/v4.30.0-rc2": old, "refs/tags/v4.34.1": new}, "tag ref map")
        refs = (SUPPORT / repo["raw_tag_refs_path"]).read_bytes()
        require(sha(refs) == repo["raw_tag_refs_sha256"], "tag refs hash")
        require(refs.decode().splitlines() == [old + "\trefs/tags/v4.30.0-rc2", new + "\trefs/tags/v4.34.1"], "raw immutable tag refs")
        require(len(repo["mapped_files"]) == count, "mapped path count")
        require(repo["compare"]["returned_file_count"] == 300 and not repo["compare"]["file_list_complete"], "compare truncation")
        require(repo["compare"]["returned_commit_count"] == 250, "compare commit cap")
        require((repo["compare"]["ahead_by"], repo["compare"]["behind_by"]) == ((3951, 0) if key == "mathlib" else (1008, 13)), "compare ancestry bounds")
        for mapped in repo["mapped_files"]:
            path = mapped["path"]
            for side, commit in (("old", old), ("new", new)):
                data = (SUPPORT / mapped[side + "_snapshot_path"]).read_bytes()
                require(sha(data) == mapped[side + "_content_sha256"], "snapshot SHA256 " + path)
                require(blob(data) == mapped[side + "_blob_sha1"], "Git blob SHA1 " + path)
                require(len(data) == mapped[side + "_size"], "snapshot size " + path)
                require(mapped[side + "_raw_url"] == f"https://raw.githubusercontent.com/{name}/{commit}/{path}", "commit-pinned URL")
            new_lines = (SUPPORT / mapped["new_snapshot_path"]).read_text().splitlines()
            for token, line_numbers in mapped.get("current_source_locators", {}).items():
                for number in line_numbers:
                    require(token in new_lines[number - 1], "source locator " + path + ":" + str(number))

    def source(repo: str, side: str, path: str) -> str:
        return (SUPPORT / "snapshots" / repo / side / path).read_text()

    require(source("mathlib", "old", "Cache/Lean.lean") == source("mathlib", "new", "Cache/Lean.lean"), "naming blob continuity")
    require("def rootHashGeneration : UInt64 := 4" in source("mathlib", "old", "Cache/IO.lean"), "old root generation")
    require("def rootHashGeneration : UInt64 := 5" in source("mathlib", "new", "Cache/IO.lean"), "new root generation")
    require("ir.sig" not in source("mathlib", "old", "Cache/IO.lean") and "ir.sig" in source("mathlib", "new", "Cache/IO.lean"), "optional payload delta")
    require("PARTSUFFIX" not in source("mathlib", "old", "Cache/IO.lean") and "PARTSUFFIX" in source("mathlib", "new", "Cache/IO.lean"), "temporary file delta")
    require("leanprover/lean4:v4.34.1" in source("mathlib", "new", "lean-toolchain"), "matched new toolchain")
    require(source("lean", "old", "src/Lean/Parser/Module/Syntax.lean") == source("lean", "new", "src/Lean/Parser/Module/Syntax.lean"), "import syntax continuity")
    require(MATRIX["audit_crosswalk_result"] == "not_updated_in_this_candidate", "crosswalk boundary")
    require(MATRIX["runtime_result"] == "unexecuted_in_this_review" and MATRIX["anneal_product_result"] == "unassessed", "review boundary")
    print("PASS: 581 baseline / 617 frozen / 36 added; exact R495-R498 claims; 22 official snapshots; source-only boundaries")


if __name__ == "__main__":
    main()
