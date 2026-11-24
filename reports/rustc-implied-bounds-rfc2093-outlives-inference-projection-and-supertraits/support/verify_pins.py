#!/usr/bin/env python3
"""Verify every 40-hex GitHub commit pin in REPORT.json and every cited upstream
raw file path (including path-move negative controls between 14210df0e and 058c70105).
Uses Python 3.10+ standard library + curl only.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any

CITED_FILES: list[tuple[str, str, str]] = [
    ("rust-lang/rust", "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65", "compiler/rustc_hir_analysis/src/outlives/mod.rs"),
    ("rust-lang/rust", "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65", "compiler/rustc_hir_analysis/src/outlives/implicit_infer.rs"),
    ("rust-lang/rust", "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65", "compiler/rustc_hir_analysis/src/outlives/utils.rs"),
    ("rust-lang/rust", "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65", "compiler/rustc_hir_analysis/src/outlives/explicit.rs"),
    ("rust-lang/rust", "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65", "compiler/rustc_hir_analysis/src/outlives/dump.rs"),
    ("rust-lang/rust", "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65", "compiler/rustc_hir_analysis/src/check/wfcheck.rs"),
    ("rust-lang/rust", "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65", "compiler/rustc_hir_analysis/src/collect/predicates_of.rs"),
    ("rust-lang/rust", "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65", "compiler/rustc_hir_analysis/src/collect/type_of.rs"),
    ("rust-lang/rust", "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65", "compiler/rustc_hir_analysis/src/impl_wf_check.rs"),
    ("rust-lang/rust", "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65", "compiler/rustc_ty_utils/src/implied_bounds.rs"),
    ("rust-lang/rust", "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65", "compiler/rustc_trait_selection/src/traits/query/type_op/implied_outlives_bounds.rs"),
    ("rust-lang/rust", "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65", "compiler/rustc_trait_selection/src/traits/outlives_bounds.rs"),
    ("rust-lang/rust", "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65", "compiler/rustc_trait_selection/src/traits/project.rs"),
    ("rust-lang/rust", "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65", "compiler/rustc_trait_selection/src/traits/wf.rs"),
    ("rust-lang/rust", "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65", "compiler/rustc_trait_selection/src/traits/engine.rs"),
    ("rust-lang/rust", "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65", "compiler/rustc_trait_selection/src/regions.rs"),
    ("rust-lang/rust", "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65", "compiler/rustc_type_ir/src/elaborate.rs"),
    ("rust-lang/rust", "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65", "compiler/rustc_type_ir/src/outlives.rs"),
    ("rust-lang/rust", "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65", "compiler/rustc_borrowck/src/type_check/free_region_relations.rs"),
    ("rust-lang/rust", "058c701055c4b6f60f622d616afc0349911c38c3", "compiler/rustc_hir_analysis/src/outlives/mod.rs"),
    ("rust-lang/rust", "058c701055c4b6f60f622d616afc0349911c38c3", "compiler/rustc_hir_analysis/src/outlives/implicit_infer.rs"),
    ("rust-lang/rust", "058c701055c4b6f60f622d616afc0349911c38c3", "compiler/rustc_hir_analysis/src/outlives/utils.rs"),
    ("rust-lang/rust", "058c701055c4b6f60f622d616afc0349911c38c3", "compiler/rustc_hir_analysis/src/check/wfcheck.rs"),
    ("rust-lang/rust", "058c701055c4b6f60f622d616afc0349911c38c3", "compiler/rustc_hir_analysis/src/collect/clauses_of.rs"),
    ("rust-lang/rust", "058c701055c4b6f60f622d616afc0349911c38c3", "compiler/rustc_hir_analysis/src/collect/type_of.rs"),
    ("rust-lang/rust", "058c701055c4b6f60f622d616afc0349911c38c3", "compiler/rustc_trait_selection/src/traits/implied_outlives_bounds.rs"),
    ("rust-lang/rust", "058c701055c4b6f60f622d616afc0349911c38c3", "compiler/rustc_trait_selection/src/traits/project.rs"),
    ("rust-lang/rust", "058c701055c4b6f60f622d616afc0349911c38c3", "compiler/rustc_type_ir/src/elaborate.rs"),
    ("rust-lang/rfcs", "f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07", "text/2093-infer-outlives.md"),
    ("rust-lang/rfcs", "f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07", "text/1214-projections-lifetimes-and-wf.md"),
    ("rust-lang/reference", "ad35aca481751a06afeb23820a672b0f3b11a476", "src/trait-bounds.md"),
    ("rust-lang/reference", "ad35aca481751a06afeb23820a672b0f3b11a476", "src/lifetime-elision.md"),
    ("rust-lang/reference", "ad35aca481751a06afeb23820a672b0f3b11a476", "src/items/associated-items.md"),
    ("joshlf/anneal", "c131b320eeeb26ef692e5afd5ec8db49ee518613", "trusted/lean/Trusted/MirAst.lean"),
    ("joshlf/anneal", "c131b320eeeb26ef692e5afd5ec8db49ee518613", "trusted/audit/TrustedBoundary.lean"),
    ("joshlf/anneal", "c131b320eeeb26ef692e5afd5ec8db49ee518613", "trusted/rustc-capture/src/driver.rs"),
]

ABSENT_PATHS: list[tuple[str, str, str]] = [
    ("rust-lang/rust", "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65", "compiler/rustc_hir_analysis/src/collect/clauses_of.rs"),
    ("rust-lang/rust", "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65", "compiler/rustc_trait_selection/src/traits/implied_outlives_bounds.rs"),
    ("rust-lang/rust", "058c701055c4b6f60f622d616afc0349911c38c3", "compiler/rustc_hir_analysis/src/collect/predicates_of.rs"),
    ("rust-lang/rust", "058c701055c4b6f60f622d616afc0349911c38c3", "compiler/rustc_trait_selection/src/traits/query/type_op/implied_outlives_bounds.rs"),
]


def http_head_or_get(url: str, accept: str | None = None, method: str = "HEAD") -> tuple[int, bytes]:
    cmd = ["curl", "-sS", "-m", "15", "-L"]
    if method == "HEAD":
        cmd.append("-I")
    if accept:
        cmd.extend(["-H", f"Accept: {accept}"])
    cmd.extend(["-H", "User-Agent: reference-corpus-pin-verifier/1.0"])
    if method == "HEAD":
        cmd.extend(["-o", "/dev/null", "-w", "%{http_code}", url])
        proc = subprocess.run(cmd, capture_output=True, check=False)
        code_str = proc.stdout.decode("utf-8", errors="replace").strip()
        return (int(code_str) if code_str.isdigit() else 0), b""
    else:
        cmd.extend(["-w", "\n%{http_code}", url])
        proc = subprocess.run(cmd, capture_output=True, check=False)
        raw = proc.stdout
        if b"\n" in raw:
            body, code_b = raw.rsplit(b"\n", 1)
            code_str = code_b.decode("utf-8", errors="replace").strip()
            return (int(code_str) if code_str.isdigit() else 0), body
        return 0, raw


def verify_commit(repo: str, sha: str, gh_args: list[str] | None) -> dict[str, Any]:
    if gh_args:
        proc = subprocess.run(
            [*gh_args, "api", f"repos/{repo}/commits/{sha}", "--jq", ".sha"],
            capture_output=True,
            text=True,
            timeout=20,
            check=False,
        )
        if proc.returncode == 0 and proc.stdout.strip() == sha:
            return {"repository": repo, "revision": sha, "method": "gh_api", "verified": True}

    api_url = f"https://api.github.com/repos/{repo}/commits/{sha}"
    status, body = http_head_or_get(api_url, accept="application/vnd.github+json", method="GET")
    if status == 200:
        data = json.loads(body.decode("utf-8"))
        matched = data.get("sha") == sha
        return {
            "repository": repo,
            "revision": sha,
            "method": "github_rest_api",
            "http_status": status,
            "commit_date": data.get("commit", {}).get("committer", {}).get("date"),
            "verified": matched,
        }

    html_url = f"https://github.com/{repo}/commit/{sha}"
    h_status, _ = http_head_or_get(html_url, method="HEAD")
    return {
        "repository": repo,
        "revision": sha,
        "method": "github_commit_head",
        "rest_api_status": status,
        "http_status": h_status,
        "verified": h_status == 200,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--report-json",
        type=Path,
        default=None,
        help="Path to REPORT.json (default: ../REPORT.json)",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=None,
        help="Output receipt path (default: support/pin_receipt.json)",
    )
    parser.add_argument(
        "--gh-cmd",
        default=None,
        help="Optional gh command prefix (e.g. 'gh')",
    )
    args = parser.parse_args()

    support_dir = Path(__file__).resolve().parent
    report_path = args.report_json.resolve() if args.report_json else (support_dir.parent / "REPORT.json")
    out_path = args.out.resolve() if args.out else (support_dir / "pin_receipt.json")
    gh_args = args.gh_cmd.split() if args.gh_cmd else None

    meta = json.loads(report_path.read_text(encoding="utf-8"))
    commit_results: list[dict[str, Any]] = []
    for subj in meta.get("subjects", []):
        ident = subj.get("identity", {})
        repo = ident.get("repository")
        rev = ident.get("revision")
        if repo and rev:
            commit_results.append(verify_commit(repo, rev, gh_args))

    file_results: list[dict[str, Any]] = []
    for repo, sha, path in CITED_FILES:
        url = f"https://raw.githubusercontent.com/{repo}/{sha}/{path}"
        status, _ = http_head_or_get(url, method="HEAD")
        file_results.append(
            {
                "repository": repo,
                "revision": sha,
                "path": path,
                "expected_present": True,
                "http_status": status,
                "verified": status == 200,
            }
        )

    for repo, sha, path in ABSENT_PATHS:
        url = f"https://raw.githubusercontent.com/{repo}/{sha}/{path}"
        status, _ = http_head_or_get(url, method="HEAD")
        file_results.append(
            {
                "repository": repo,
                "revision": sha,
                "path": path,
                "expected_present": False,
                "http_status": status,
                "verified": status == 404,
            }
        )

    all_ok = all(r["verified"] for r in commit_results) and all(r["verified"] for r in file_results)
    receipt = {
        "commits": commit_results,
        "files": file_results,
        "commits_verified": sum(1 for r in commit_results if r["verified"]),
        "commits_total": len(commit_results),
        "files_verified": sum(1 for r in file_results if r["verified"]),
        "files_total": len(file_results),
        "all_verified": all_ok,
    }
    out_path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        f"Pin check: {receipt['commits_verified']}/{receipt['commits_total']} commits, "
        f"{receipt['files_verified']}/{receipt['files_total']} files verified."
    )
    if not all_ok:
        for r in commit_results + file_results:
            if not r["verified"]:
                print(f"FAILED: {r}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
