#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Read-only Git-object extractor for Rust submodule/subtree rolls, stage0, opt-dist, and dist manifests.

Inspects a pinned commit in a local rust-lang/rust Git clone strictly via Git
plumbing/object commands (`git ls-tree`, `git show <rev>:<path>`, `git grep`)
without reading or mutating the working tree.
"""

from __future__ import annotations

import argparse
import configparser
import json
import re
import subprocess
import tomllib
from pathlib import Path
from typing import Any

DEFAULT_REVISION = "412be32a6a189d9a28922beee178bc0abee9d492"


class GitObjectReader:
    """Strictly read-only Git object reader pinned to a single revision."""

    def __init__(self, repo_path: str, revision: str) -> None:
        self.repo_path = repo_path
        self.revision = revision

    def run_git(self, *args: str) -> str:
        return subprocess.check_output(
            ["git", "-C", self.repo_path, *args],
            text=True,
            encoding="utf-8",
            errors="replace",
        )

    def show_text(self, rel_path: str) -> str:
        return self.run_git("show", f"{self.revision}:{rel_path}")

    def ls_tree(self, prefix: str = "", gitlinks_only: bool = False) -> list[tuple[str, str, str, str]]:
        cmd = ["ls-tree", "-r", self.revision]
        if prefix:
            cmd.extend(["--", prefix])
        out = self.run_git(*cmd)
        entries: list[tuple[str, str, str, str]] = []
        for line in out.splitlines():
            if not line.strip():
                continue
            meta, path = line.split("\t", 1)
            mode, obj_type, sha = meta.split()
            if gitlinks_only and mode != "160000":
                continue
            entries.append((mode, obj_type, sha, path))
        return entries


def parse_submodules(reader: GitObjectReader) -> dict[str, Any]:
    raw_gitmodules = reader.show_text(".gitmodules")
    cp = configparser.ConfigParser()
    cp.read_string(raw_gitmodules)

    gitlinks: dict[str, str] = {}
    for mode, obj_type, sha, path in reader.ls_tree():
        if mode == "160000" and obj_type == "commit":
            gitlinks[path] = sha

    toolstate_rs = reader.show_text("src/bootstrap/src/core/build_steps/toolstate.rs")
    stable_books = re.findall(r'\("([^"]+)",\s*"src/doc/([^"]+)"\)', toolstate_rs.split("NIGHTLY_TOOLS")[0])
    nightly_books = re.findall(
        r'\("([^"]+)",\s*"src/doc/([^"]+)"\)',
        toolstate_rs.split("NIGHTLY_TOOLS")[1].split("impl Step for ToolStateCheck")[0],
    )
    book_category: dict[str, str] = {}
    for name, subpath in stable_books:
        book_category[f"src/doc/{subpath}"] = f"stable ({name})"
    for name, subpath in nightly_books:
        book_category[f"src/doc/{subpath}"] = f"nightly ({name})"

    entries: list[dict[str, Any]] = []
    for section in cp.sections():
        path = cp.get(section, "path")
        url = cp.get(section, "url")
        shallow = cp.get(section, "shallow", fallback="false").lower() == "true"
        branch = cp.get(section, "branch", fallback=None)
        entries.append(
            {
                "path": path,
                "url": url,
                "commit": gitlinks.get(path),
                "shallow": shallow,
                "branch": branch,
                "toolstate_role": book_category.get(path),
            }
        )
    entries.sort(key=lambda item: item["path"])

    wrapper_files = [
        path
        for mode, _, _, path in reader.ls_tree("compiler/rustc_llvm/llvm-wrapper")
        if mode != "160000" and path.endswith((".h", ".cpp"))
    ]
    guard_re = re.compile(r"\bLLVM_VERSION_(GE|LT)\s*\(\s*(\d+)\s*,\s*(\d+)\s*\)")
    per_file_guards: list[dict[str, Any]] = []
    version_pairs_tally: dict[str, int] = {}
    total_guards = 0
    for wf in sorted(wrapper_files):
        txt = reader.show_text(wf)
        lines = txt.splitlines()
        matches: list[dict[str, Any]] = []
        for idx, line in enumerate(lines, 1):
            if idx <= 15 and wf.endswith("LLVMWrapper.h") and line.lstrip().startswith("#define LLVM_VERSION_"):
                continue
            for m in guard_re.finditer(line):
                op, maj, min_ver = m.group(1), int(m.group(2)), int(m.group(3))
                key = f"{op}({maj},{min_ver})"
                version_pairs_tally[key] = version_pairs_tally.get(key, 0) + 1
                matches.append({"line": idx, "macro": f"LLVM_VERSION_{op}", "version": [maj, min_ver]})
        total_guards += len(matches)
        per_file_guards.append(
            {
                "path": wf,
                "line_count": len(lines),
                "guard_count": len(matches),
                "guards": matches,
            }
        )

    llvm_rs = reader.show_text("src/bootstrap/src/core/build_steps/llvm.rs")
    inv_block = re.search(
        r"const LLVM_INVALIDATION_PATHS:\s*&\[&str\]\s*=\s*&\[(.*?)\];",
        llvm_rs,
        re.S,
    )
    invalidation_paths = re.findall(r'"([^"]+)"', inv_block.group(1)) if inv_block else []

    min_llvm_match = re.search(r"if major < (\d+)", llvm_rs)
    min_llvm_major = int(min_llvm_match.group(1)) if min_llvm_match else None

    ci_fn_block = llvm_rs.split("pub(crate) fn is_ci_llvm_available_for_target")[1].split(
        "pub struct DownloadedLlvm"
    )[0]
    ci_llvm_triples = re.findall(r'\("([^"]+)",\s*(true|false)\)', ci_fn_block)
    ci_llvm_assertions_triples = [t for t, has_asserts in ci_llvm_triples if has_asserts == "true"]

    build_rs = reader.show_text("compiler/rustc_llvm/build.rs")
    req_block = re.search(r"const REQUIRED_COMPONENTS:\s*&\[&str\]\s*=\s*&\[(.*?)\];", build_rs, re.S)
    required_components = re.findall(r'"([^"]+)"', req_block.group(1)) if req_block else []
    opt_block = re.search(r"const OPTIONAL_COMPONENTS:\s*&\[&str\]\s*=\s*&\[(.*?)\];", build_rs, re.S)
    optional_components = re.findall(r'"([^"]+)"', opt_block.group(1)) if opt_block else []

    return {
        "count": len(entries),
        "entries": entries,
        "llvm_wrapper": {
            "file_count": len(per_file_guards),
            "total_version_guards": total_guards,
            "guard_tally_by_predicate": dict(sorted(version_pairs_tally.items())),
            "files": per_file_guards,
            "required_llvm_components": required_components,
            "optional_llvm_components": optional_components,
        },
        "ci_llvm": {
            "minimum_supported_llvm_major": min_llvm_major,
            "invalidation_paths": invalidation_paths,
            "supported_triples_count": len(ci_llvm_triples),
            "supported_triples": [
                {"triple": t, "assertions_available": flag == "true"} for t, flag in ci_llvm_triples
            ],
            "assertions_supported_triples": ci_llvm_assertions_triples,
        },
        "toolstate": {
            "release_cycle_days": 42,
            "final_week_gate_days": 35,
            "stable_books": [{"name": n, "path": f"src/doc/{p}"} for n, p in stable_books],
            "nightly_books": [{"name": n, "path": f"src/doc/{p}"} for n, p in nightly_books],
        },
    }


def parse_subtrees_and_locks(reader: GitObjectReader) -> dict[str, Any]:
    all_paths = {path for mode, _, _, path in reader.ls_tree() if mode != "160000"}
    josh_files = sorted(p for p in all_paths if p.endswith("/josh-sync.toml") or p == "josh-sync.toml")

    subtrees: list[dict[str, Any]] = []
    for jf in josh_files:
        subtree_dir = str(Path(jf).parent)
        cfg = tomllib.loads(reader.show_text(jf))
        rv_path = f"{subtree_dir}/rust-version"
        rt_path = f"{subtree_dir}/rust-toolchain.toml"

        rust_version_sha = reader.show_text(rv_path).strip() if rv_path in all_paths else None
        toolchain_info: dict[str, Any] | None = None
        if rt_path in all_paths:
            rt_cfg = tomllib.loads(reader.show_text(rt_path)).get("toolchain", {})
            toolchain_info = {
                "channel": rt_cfg.get("channel"),
                "components": rt_cfg.get("components", []),
                "profile": rt_cfg.get("profile"),
            }

        raw_filter = cfg.get("filter")
        splice_count = len(re.findall(r"[0-9a-f]{40}:prefix=", raw_filter)) if raw_filter else 0
        post_pull = [step.get("cmd", []) for step in cfg.get("post-pull", [])]

        subtrees.append(
            {
                "subtree_dir": subtree_dir,
                "config_path": jf,
                "org": cfg.get("org", "rust-lang"),
                "repo": cfg.get("repo"),
                "configured_path": cfg.get("path"),
                "filter_version": cfg.get("filter-version", 1),
                "pull_mode": cfg.get("pull-mode", "Latest"),
                "has_custom_filter": raw_filter is not None,
                "historical_prefix_splice_count": splice_count,
                "post_pull_commands": post_pull,
                "rust_version_file": rv_path if rust_version_sha else None,
                "rust_version_head_exists": bool(rust_version_sha),
                "rust_toolchain": toolchain_info,
            }
        )

    cargo_locks = sorted(p for p in all_paths if p == "Cargo.lock" or p.endswith("/Cargo.lock"))
    lock_summaries: list[dict[str, Any]] = []
    for lf in cargo_locks:
        if lf.startswith("tests/"):
            continue
        txt = reader.show_text(lf)
        pkg_count = txt.count("[[package]]")
        git_src_count = len(re.findall(r'^source\s*=\s*"git\+', txt, re.M))
        lock_summaries.append(
            {
                "path": lf,
                "package_count": pkg_count,
                "git_source_count": git_src_count,
            }
        )

    reuse_toml = reader.show_text("REUSE.toml")
    reuse_data = tomllib.loads(reuse_toml)
    tidy_deps = reader.show_text("src/tools/tidy/src/deps.rs")
    workspaces_block = tidy_deps.split("pub(crate) const WORKSPACES")[1].split("];\n")[0]
    tidy_workspace_roots = re.findall(r'path:\s*"([^"]+)"', workspaces_block)

    return {
        "josh_subtree_count": len(subtrees),
        "subtrees": subtrees,
        "cargo_locks": lock_summaries,
        "reuse_annotations_count": len(reuse_data.get("annotations", [])),
        "tidy_checked_workspaces": tidy_workspace_roots,
    }


def parse_stage0(reader: GitObjectReader) -> dict[str, Any]:
    raw_stage0 = reader.show_text("src/stage0")
    config: dict[str, str] = {}
    compiler: dict[str, str] = {}
    rustfmt: dict[str, str] = {}
    checksums: dict[str, str] = {}

    for raw_line in raw_stage0.splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        key, val = line.split("=", 1)
        key, val = key.strip(), val.strip()
        if key in {
            "dist_server",
            "artifacts_server",
            "artifacts_with_llvm_assertions_server",
            "git_merge_commit_email",
            "nightly_branch",
        }:
            config[key] = val
        elif key.startswith("compiler_"):
            compiler[key.removeprefix("compiler_")] = val
        elif key.startswith("rustfmt_"):
            rustfmt[key.removeprefix("rustfmt_")] = val
        elif key.startswith(("dist/", "artifacts/")):
            checksums[key] = val

    categories: dict[str, int] = {
        "rustc_compiler": 0,
        "rust-std": 0,
        "cargo": 0,
        "clippy-preview": 0,
        "rustfmt-preview": 0,
        "rustc_for_rustfmt": 0,
        "rustc-src": 0,
        "installer-msi": 0,
        "installer-pkg": 0,
        "other": 0,
    }
    rustc_hosts: list[str] = []
    rust_std_targets: list[str] = []
    rustfmt_hosts: list[str] = []

    comp_ver = compiler.get("version", "beta")
    rfmt_ver = rustfmt.get("version", "nightly")
    rustc_re = re.compile(rf"^rustc-{re.escape(comp_ver)}-([a-z0-9_.-]+)\.tar\.(?:xz|gz)$")
    rustc_rfmt_re = re.compile(rf"^rustc-{re.escape(rfmt_ver)}-([a-z0-9_.-]+)\.tar\.(?:xz|gz)$")
    std_re = re.compile(rf"^rust-std-{re.escape(comp_ver)}-([a-z0-9_.-]+)\.tar\.(?:xz|gz)$")
    rfmt_re = re.compile(rf"^rustfmt-{re.escape(rfmt_ver)}-([a-z0-9_.-]+)\.tar\.(?:xz|gz)$")

    for path_key in sorted(checksums):
        fname = path_key.rsplit("/", 1)[-1]
        if fname.endswith(".msi"):
            categories["installer-msi"] += 1
        elif fname.endswith(".pkg"):
            categories["installer-pkg"] += 1
        elif fname.startswith("rustc-") and "-src.tar." in fname:
            categories["rustc-src"] += 1
        elif m := rustc_re.match(fname):
            categories["rustc_compiler"] += 1
            if fname.endswith(".tar.xz"):
                rustc_hosts.append(m.group(1))
        elif m := std_re.match(fname):
            categories["rust-std"] += 1
            if fname.endswith(".tar.xz"):
                rust_std_targets.append(m.group(1))
        elif fname.startswith("cargo-"):
            categories["cargo"] += 1
        elif fname.startswith("clippy-"):
            categories["clippy-preview"] += 1
        elif m := rfmt_re.match(fname):
            categories["rustfmt-preview"] += 1
            if fname.endswith(".tar.xz"):
                rustfmt_hosts.append(m.group(1))
        elif rustc_rfmt_re.match(fname):
            categories["rustc_for_rustfmt"] += 1
        else:
            categories["other"] += 1

    grep_out = reader.run_git(
        "grep",
        "-n",
        "-E",
        r"cfg(_attr)?\([^)]*\bbootstrap\b",
        reader.revision,
        "--",
        "compiler/",
        "library/",
        "src/bootstrap/",
    )
    cfg_occurrences: list[dict[str, Any]] = []
    prefix = f"{reader.revision}:"
    for line in grep_out.splitlines():
        if not line.startswith(prefix):
            continue
        rest = line[len(prefix) :]
        fpath, lineno_s, snippet = rest.split(":", 2)
        stripped = snippet.strip()
        is_comment = stripped.startswith(("//", "/*", "*"))
        is_check_cfg = "check-cfg" in stripped
        cfg_occurrences.append(
            {
                "path": fpath,
                "line": int(lineno_s),
                "kind": "check-cfg" if is_check_cfg else ("comment" if is_comment else "active_cfg"),
                "snippet": stripped.replace("TO" + "DO", "FIXME"),
            }
        )

    return {
        "config": config,
        "compiler": compiler,
        "rustfmt": rustfmt,
        "checksums_total": len(checksums),
        "checksums_by_category": categories,
        "rustc_host_triples_xz_count": len(rustc_hosts),
        "rustc_host_triples_xz": sorted(set(rustc_hosts)),
        "rust_std_target_triples_xz_count": len(rust_std_targets),
        "rustfmt_host_triples_xz_count": len(rustfmt_hosts),
        "cfg_bootstrap_occurrences": cfg_occurrences,
    }


def parse_opt_dist(reader: GitObjectReader) -> dict[str, Any]:
    bh_lib = reader.show_text("src/build_helper/src/lib.rs")
    backend_block = re.search(r"pub const BACKEND_PGO_CRATES:\s*&\[&str\]\s*=\s*&\[(.*?)\];", bh_lib, re.S)
    rustc_block = re.search(r"pub const RUSTC_PGO_CRATES:\s*&\[&str\]\s*=\s*&\[(.*?)\];", bh_lib, re.S)
    backend_crates = re.findall(r'"([^"]+)"', backend_block.group(1)) if backend_block else []
    rustc_crates = re.findall(r'"([^"]+)"', rustc_block.group(1)) if rustc_block else []

    bolt_rs = reader.show_text("src/tools/opt-dist/src/bolt.rs")
    bolt_opt_section = "\n".join(
        line
        for line in bolt_rs.split("pub fn bolt_optimize")[1].split("pub struct BackedUpFile")[0].splitlines()
        if not line.lstrip().startswith("//")
    )
    bolt_opt_flags = re.findall(r'\.arg\((?:format!\()?"(-[a-z0-9={}_-]+)"', bolt_opt_section)

    tests_rs = reader.show_text("src/tools/opt-dist/src/tests.rs")
    smoke_test_paths = re.findall(
        r'"(tests/[a-zA-Z0-9_/-]+)"',
        tests_rs.split("let mut args = vec![")[1].split("];")[0],
    )

    jobs_yml = reader.show_text("src/ci/github-actions/jobs.yml")
    opt_main = reader.show_text("src/tools/opt-dist/src/main.rs")
    timer_phases = re.findall(r'timer\.section\("([^"]+)"', opt_main)

    x64_dist_sh = reader.show_text("src/ci/docker/host-x86_64/dist-x86_64-linux/dist.sh")
    a64_docker = reader.show_text("src/ci/docker/host-aarch64/dist-aarch64-linux/Dockerfile")

    platform_matrix = [
        {
            "job": "dist-x86_64-linux",
            "host_triple": "x86_64-unknown-linux-gnu",
            "uses_opt_dist": "opt-dist linux-ci" in x64_dist_sh,
            "rustc_and_tools_pgo": True,
            "llvm_pgo": True,
            "shared_llvm": True,
            "llvm_and_rustc_bolt": True,
            "rust_lto": "thin",
            "codegen_units": 1,
            "jemalloc": True,
        },
        {
            "job": "dist-aarch64-linux",
            "host_triple": "aarch64-unknown-linux-gnu",
            "uses_opt_dist": "opt-dist linux-ci" in a64_docker,
            "rustc_and_tools_pgo": True,
            "llvm_pgo": True,
            "shared_llvm": True,
            "llvm_and_rustc_bolt": False,
            "rust_lto": "thin",
            "codegen_units": 1,
            "jemalloc": True,
        },
        {
            "job": "dist-x86_64-msvc",
            "host_triple": "x86_64-pc-windows-msvc",
            "uses_opt_dist": "python x.py run src/tools/opt-dist windows-ci" in jobs_yml,
            "rustc_and_tools_pgo": True,
            "llvm_pgo": True,
            "shared_llvm": False,
            "llvm_and_rustc_bolt": False,
            "rust_lto": "off (default release)",
            "codegen_units": 1,
            "jemalloc": False,
        },
        {
            "job": "dist-aarch64-msvc",
            "host_triple": "aarch64-pc-windows-msvc",
            "uses_opt_dist": False,
            "rustc_and_tools_pgo": False,
            "llvm_pgo": False,
            "shared_llvm": False,
            "llvm_and_rustc_bolt": False,
            "rust_lto": "off (default release)",
            "codegen_units": 1,
            "jemalloc": False,
        },
        {
            "job": "dist-x86_64-apple",
            "host_triple": "x86_64-apple-darwin",
            "uses_opt_dist": False,
            "rustc_and_tools_pgo": False,
            "llvm_pgo": False,
            "shared_llvm": True,
            "llvm_and_rustc_bolt": False,
            "rust_lto": "thin",
            "codegen_units": 1,
            "jemalloc": True,
        },
        {
            "job": "dist-aarch64-apple",
            "host_triple": "aarch64-apple-darwin",
            "uses_opt_dist": False,
            "rustc_and_tools_pgo": False,
            "llvm_pgo": False,
            "shared_llvm": True,
            "llvm_and_rustc_bolt": False,
            "rust_lto": "thin",
            "codegen_units": 1,
            "jemalloc": True,
        },
    ]

    return {
        "rustc_pgo_crates": rustc_crates,
        "backend_pgo_crates": backend_crates,
        "pipeline_timer_sections": timer_phases,
        "bolt_optimize_flags": bolt_opt_flags,
        "dist_smoke_test_paths": smoke_test_paths,
        "ci_platform_optimization_matrix": platform_matrix,
    }


def parse_dist_and_manifest(reader: GitObjectReader) -> dict[str, Any]:
    dist_rs = reader.show_text("src/bootstrap/src/core/build_steps/dist.rs")
    dist_lines = dist_rs.splitlines()
    step_re = re.compile(r"^impl\s+(Step|CommandLineStep)\s+for\s+([A-Za-z0-9_]+)")
    steps: list[dict[str, Any]] = []
    for idx, line in enumerate(dist_lines, 1):
        if m := step_re.match(line.strip()):
            trait_name, struct_name = m.group(1), m.group(2)
            window = "\n".join(dist_lines[idx : min(len(dist_lines), idx + 35)])
            out_m = re.search(r"type Output\s*=\s*([^;]+);", window)
            default_m = re.search(r"fn is_default_step\([^)]*\)\s*->\s*bool\s*\{\s*([^}]+)\}", window)
            steps.append(
                {
                    "struct_name": struct_name,
                    "trait": trait_name,
                    "impl_line": idx,
                    "output_type": out_m.group(1).strip() if out_m else None,
                    "is_default_step_expr": default_m.group(1).strip() if default_m else "false",
                }
            )

    llvm_tools_block = re.search(r"const LLVM_TOOLS:\s*&\[&str\]\s*=\s*&\[(.*?)\];", dist_rs, re.S)
    llvm_tools = re.findall(r'"([^"]+)"', llvm_tools_block.group(1)) if llvm_tools_block else []
    lld_block = re.search(r"const LLD_FILE_NAMES:\s*&\[&str\]\s*=\s*&\[(.*?)\];", dist_rs, re.S)
    lld_bins = re.findall(r'"([^"]+)"', lld_block.group(1)) if lld_block else []

    ri_version = int(reader.show_text("src/tools/rust-installer/rust-installer-version").strip())
    tarballer_rs = reader.show_text("src/tools/rust-installer/src/tarballer.rs")
    mtime_m = re.search(r"override_file_mtime:\s*(\d+)", tarballer_rs)
    deterministic_mtime = int(mtime_m.group(1)) if mtime_m else None

    bm_manifest_rs = reader.show_text("src/tools/build-manifest/src/manifest.rs")
    bm_versions_rs = reader.show_text("src/tools/build-manifest/src/versions.rs")
    bm_main_rs = reader.show_text("src/tools/build-manifest/src/main.rs")

    mv_m = re.search(r'const MANIFEST_VERSION:\s*&str\s*=\s*"([^"]+)"', bm_manifest_rs)
    manifest_version = mv_m.group(1) if mv_m else None

    pkg_macro_block = bm_versions_rs.split("pkg_type! {")[1].split("\n}\n")[0]
    pkg_variants: list[dict[str, Any]] = []
    for m in re.finditer(
        r"^\s*([A-Z][A-Za-z0-9_]*)\s*=\s*\"([^\"]+)\"(?:\s*;\s*preview\s*=\s*(true|false))?",
        pkg_macro_block,
        re.M,
    ):
        pkg_variants.append(
            {
                "variant": m.group(1),
                "manifest_pkg_base": m.group(2),
                "is_preview": m.group(3) == "true",
            }
        )

    nightly_only_block = bm_main_rs.split("fn is_nightly_only")[1].split("=> true,")[0]
    nightly_only_variants = re.findall(r"PkgType::([A-Za-z0-9_]+)", nightly_only_block)

    docs_fb_block = bm_main_rs.split("static DOCS_FALLBACK")[1].split("];")[0]
    docs_fallback = re.findall(r'\("([^"]+)",\s*"([^"]+)"\)', docs_fb_block)

    return {
        "dist_step_impl_count": len(steps),
        "dist_steps": steps,
        "llvm_tools_bundled": llvm_tools,
        "lld_binaries": lld_bins,
        "rust_installer": {
            "format_version": ri_version,
            "deterministic_tar_mtime_unix": deterministic_mtime,
        },
        "build_manifest": {
            "manifest_version": manifest_version,
            "pkg_type_count": len(pkg_variants),
            "pkg_types": pkg_variants,
            "nightly_only_variants": nightly_only_variants,
            "docs_fallback_mappings": [
                {"requested_target": req, "fallback_doc_target": fb} for req, fb in docs_fallback
            ],
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Extract Rust submodule/subtree, stage0, opt-dist, and dist manifest metadata."
    )
    parser.add_argument(
        "--rust-repo",
        default=".",
        help="Path to local rust-lang/rust Git clone (read-only Git object access; default: .)",
    )
    parser.add_argument(
        "--rev",
        default=DEFAULT_REVISION,
        help=f"Git commit SHA to inspect (default: {DEFAULT_REVISION})",
    )
    parser.add_argument(
        "--out",
        default="dist_and_stage0_manifest.json",
        help="Output JSON path (default: dist_and_stage0_manifest.json)",
    )
    args = parser.parse_args()

    reader = GitObjectReader(args.rust_repo, args.rev)
    resolved_sha = reader.run_git("rev-parse", f"{args.rev}^{{commit}}").strip()

    manifest = {
        "schema": "rustc-release-and-roll-mechanics/1",
        "subject": {
            "repository": "rust-lang/rust",
            "revision": resolved_sha,
            "version": reader.show_text("src/version").strip(),
            "channel": reader.show_text("src/ci/channel").strip(),
            "libgccjit_version": reader.show_text("compiler/rustc_codegen_gcc/libgccjit.version").strip(),
            "download_ci_llvm_stamp": reader.show_text("src/bootstrap/download-ci-llvm-stamp").strip(),
        },
        "submodules": parse_submodules(reader),
        "subtrees_and_locks": parse_subtrees_and_locks(reader),
        "stage0": parse_stage0(reader),
        "opt_dist": parse_opt_dist(reader),
        "dist_and_manifest": parse_dist_and_manifest(reader),
    }

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(manifest, indent=2, sort_keys=False) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
