#!/usr/bin/env python3
"""Verify retained source snapshots and narrow source-contract drift offline.

This checker never invokes Aeneas, Charon, Lean, Rust, or the network. Its
results are source observations, not evidence of executable behavior.
"""

from __future__ import annotations

import csv
import hashlib
import json
import re
import subprocess
from collections import Counter
from pathlib import Path


HERE = Path(__file__).resolve().parent


def git_blob_sha1(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def first_claim_paragraph(markdown: str) -> str:
    match = re.search(
        r"(?mi)^## Summary\s*\n+([\s\S]*?)(?=\n\s*\n|\n## |\Z)", markdown
    )
    if match:
        return match.group(1)
    lines = markdown.splitlines()
    start = next((i for i, line in enumerate(lines) if line.startswith("# ")), 0)
    remainder = "\n".join(lines[start + 1 :])
    return re.split(r"\n\s*\n", remainder.strip())[0]


def normalized_claim_excerpt(paragraph: str) -> str:
    labels_only = re.sub(r"\[([^\]]+)\]\([^)]*\)", r"\1", paragraph)
    return re.sub(r"\s+", " ", labels_only).strip()


def main() -> None:
    manifest = json.loads((HERE / "source-snapshot-manifest.json").read_text())
    snapshots = {}
    for item in manifest["snapshots"]:
        data = (HERE / item["saved_path"]).read_bytes()
        assert len(data) == item["byte_count"]
        assert hashlib.sha256(data).hexdigest() == item["sha256"]
        assert git_blob_sha1(data) == item["git_blob_sha1"]
        snapshots[item["system"], item["era"], item["upstream_path"]] = data.decode()

    def get(system: str, era: str, path: str) -> str:
        return snapshots[system, era, path]

    old_main = get("aeneas", "old", "src/Main.ml")
    new_main = get("aeneas", "new", "src/Main.ml")
    old_config = get("aeneas", "old", "src/Config.ml")
    new_config = get("aeneas", "new", "src/Config.ml")
    emit_json = get("aeneas", "new", "src/EmitJson.ml")
    emit_doc = get("aeneas", "new", "documentation/emit-json.md")
    old_charon_meta = get("charon", "old", "charon/src/ast/meta.rs")
    new_charon_meta = get("charon", "new", "charon/src/ast/meta.rs")

    checks = {
        "aeneas_emit_json_cli_added": '"-emit-json"' not in old_main
        and '"-emit-json"' in new_main
        and "let emit_json = ref false" not in old_config
        and "let emit_json = ref false" in new_config,
        "aeneas_translation_json_source_added": "translation.json" in emit_json
        and "def_id : int" in emit_json
        and "lean_name : string" in emit_json
        and "rust_name : string" in emit_json
        and "-emit-json" in emit_doc,
        "aeneas_lean_module_default_added": '"-use-lean-modules"' not in old_main
        and '"-use-lean-modules"' in new_main
        and "let use_lean_modules = ref true" not in old_config
        and "let use_lean_modules = ref true" in new_config,
        "aeneas_cli_still_file_oriented_in_source": "Usage: %s [OPTIONS] FILE" in new_main
        and "one file at a time" in new_main,
        "aeneas_charon_pin_changed": "a535e914f74db4fd9e6be7048f4233270d8945c0"
        in get("aeneas", "old", "charon-pin")
        and "e435e5f341863a49a7e85d2fee9988bc0c687c82"
        in get("aeneas", "new", "charon-pin"),
        "aeneas_lean_pin_changed": "v4.30.0-rc2"
        in get("aeneas", "old", "backends/lean/lean-toolchain")
        and "v4.31.0" in get("aeneas", "new", "backends/lean/lean-toolchain"),
        "paired_charon_rust_pin_changed": "nightly-2026-05-31"
        in get("charon", "old", "charon/rust-toolchain")
        and "nightly-2026-09-17"
        in get("charon", "new", "charon/rust-toolchain"),
        "separate_june3_charon_not_confused_with_pair": "nightly-2026-06-01"
        in get("charon", "separate-june3", "charon/rust-toolchain")
        and "nightly-2026-06-01"
        not in get("charon", "old", "charon/rust-toolchain"),
        "charon_started_from_source_field_added": "started_from: bool"
        not in old_charon_meta
        and "started_from: bool" in new_charon_meta,
    }
    assert all(checks.values()), checks

    with (HERE / "claim-matrix-ebcdcad-169.csv").open(newline="") as handle:
        rows = list(csv.DictReader(handle))
    assert len(rows) == 169
    assert len({row["report_path_at_ebcdcad"] for row in rows}) == 169
    assert Counter(row["selection_basis"] for row in rows) == {
        "metadata_or_cohort": 150,
        "title_or_summary_only": 19,
    }
    assert all("No newer" in row["runtime_status"] for row in rows)
    assert all(row["report_section_locator"] for row in rows)

    frozen = json.loads((HERE / "frozen-claim-excerpts-ebcdcad-169.json").read_text())
    revision = frozen["frozen_reference_revision"]
    assert revision == "ebcdcadb63fefd1e6c0f46cb2030270ae3232837"
    assert len(revision) == 40
    by_path = {item["report_path"]: item for item in frozen["excerpts"]}
    assert len(by_path) == len(rows) == 169
    for row in rows:
        item = by_path[row["report_path_at_ebcdcad"]]
        assert row["inventory_id"] == item["inventory_id"]
        paragraph = item["verbatim_source_paragraph"]
        assert normalized_claim_excerpt(paragraph) == row["claim_or_cell_to_recheck"]

    # The candidate worktree retains the immutable source commit. A detached
    # Data mirror can still check every preserved paragraph and normalization
    # above, but cannot claim to have re-read the Git object if it is absent.
    repo_result = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        cwd=HERE,
        capture_output=True,
        text=True,
        check=False,
    )
    frozen_git_verified = False
    if repo_result.returncode == 0:
        repo = Path(repo_result.stdout.strip())
        exists = subprocess.run(
            ["git", "cat-file", "-e", f"{revision}^{{commit}}"],
            cwd=repo,
            capture_output=True,
            check=False,
        )
        if exists.returncode == 0:
            frozen_git_verified = True
            for row in rows:
                path = row["report_path_at_ebcdcad"]
                item = by_path[path]
                raw = subprocess.check_output(
                    ["git", "show", f"{revision}:{path}"], cwd=repo
                )
                assert git_blob_sha1(raw) == item["source_report_git_blob_sha1"]
                assert first_claim_paragraph(raw.decode()) == item["verbatim_source_paragraph"]

    metadata = json.loads((HERE.parent / "REPORT.json").read_text())
    assert any(
        subject["identity"].get("revision") == revision
        for subject in metadata["subjects"]
    )
    assert revision in (HERE.parent / "REPORT.md").read_text()

    with (HERE / "source-path-diff.csv").open(newline="") as handle:
        diff_rows = list(csv.DictReader(handle))
    assert Counter(row["repository"] for row in diff_rows) == {
        "aeneas": 536,
        "charon": 992,
    }

    print(
        json.dumps(
            {
                "status": "passed_source_only",
                "source_contract_checks": checks,
                "snapshot_count": len(snapshots),
                "matrix_rows": len(rows),
                "normalized_claim_excerpts_verified": len(rows),
                "frozen_git_source_verified": frozen_git_verified,
                "selection_basis": dict(Counter(row["selection_basis"] for row in rows)),
                "changed_paths": dict(Counter(row["repository"] for row in diff_rows)),
                "runtime_executed": False,
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
