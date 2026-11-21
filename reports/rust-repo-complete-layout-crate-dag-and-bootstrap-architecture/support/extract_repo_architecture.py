#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Deterministic Git-object repository architecture extractor for rust-lang/rust.

Reads a pinned commit of a local rust-lang/rust Git clone strictly via read-only
`git ls-tree` and `git cat-file --batch` streams without reading or mutating any
working-tree checkout. Produces a machine-readable JSON inventory covering:
  1. Top-level files, directories, `src/*` subtrees, and Cargo workspaces/locks.
  2. All `compiler/*` crates, nested `compiler/**/Cargo.toml` packages, and
     `src/librustdoc`: SLOC, Cargo DAG edges, topological depth, in/out-degree,
     architectural layer, and 3-way verification classification.
  3. All `TyCtxt` queries and `non_query` dep kinds declared in
     `compiler/rustc_middle/src/queries.rs`, their modifiers, and the crate-level
     `Providers` / `ExternProviders` registration map.
  4. All `library/*` directories, `Cargo.toml` manifests, `rustc-std-workspace-*`
     shims, and `#![feature(...)]` usage.
  5. All `src/tools/*` entries, `160000` Git submodules, and subtree-synced tools.
  6. `src/bootstrap` (`x.py`) `Step` / `CommandLineStep` implementations and
     `tests/*` suite metrics.
"""

from __future__ import annotations

import argparse
import configparser
import json
import re
import subprocess
import tomllib
from collections import defaultdict
from pathlib import Path

DEFAULT_REV = "412be32a6a189d9a28922beee178bc0abee9d492"

SOURCE_EXTS = (
    ".rs",
    ".py",
    ".sh",
    ".ps1",
    ".c",
    ".cpp",
    ".cc",
    ".h",
    ".hpp",
    ".js",
    ".mjs",
    ".ts",
    ".toml",
    ".yml",
    ".yaml",
    ".ftl",
)

CODE_EXTS = (".rs", ".c", ".cpp", ".cc", ".h", ".hpp", ".py", ".sh", ".js")

COMPILER_CRATE_TAXONOMY: dict[str, tuple[str, str]] = {
    # (architectural_layer, verification_split)
    # Foundations & substrates (semantic_middle_shared)
    "rustc_arena": ("L0: Foundation & Data Structures", "semantic_middle_shared"),
    "rustc_data_structures": ("L0: Foundation & Data Structures", "semantic_middle_shared"),
    "rustc_hashes": ("L0: Foundation & Data Structures", "semantic_middle_shared"),
    "rustc_index": ("L0: Foundation & Data Structures", "semantic_middle_shared"),
    "rustc_index_macros": ("L0: Foundation & Data Structures", "semantic_middle_shared"),
    "rustc_macros": ("L0: Foundation & Data Structures", "semantic_middle_shared"),
    "rustc_serialize": ("L0: Foundation & Data Structures", "semantic_middle_shared"),
    "rustc_span": ("L1: Span, Session & Diagnostics", "semantic_middle_shared"),
    "rustc_feature": ("L1: Span, Session & Diagnostics", "semantic_middle_shared"),
    "rustc_structures": ("L1: Span, Session & Diagnostics", "semantic_middle_shared"),
    "rustc_session": ("L1: Span, Session & Diagnostics", "semantic_middle_shared"),
    # Diagnostics, logging, FS & pretty-printing (diagnostic_driver_backend)
    "rustc_errors": ("L1: Span, Session & Diagnostics", "diagnostic_driver_backend"),
    "rustc_error_codes": ("L1: Span, Session & Diagnostics", "diagnostic_driver_backend"),
    "rustc_error_messages": ("L1: Span, Session & Diagnostics", "diagnostic_driver_backend"),
    "rustc_log": ("L0: Foundation & Data Structures", "diagnostic_driver_backend"),
    "rustc_fs_util": ("L0: Foundation & Data Structures", "diagnostic_driver_backend"),
    "rustc_graphviz": ("L0: Foundation & Data Structures", "diagnostic_driver_backend"),
    "rustc_thread_pool": ("L0: Foundation & Data Structures", "diagnostic_driver_backend"),
    "rustc_windows_rc": ("L0: Foundation & Data Structures", "diagnostic_driver_backend"),
    "rustc_ast_pretty": ("L2: Lexing, Parsing & AST", "diagnostic_driver_backend"),
    "rustc_hir_pretty": ("L4: Name Resolution & HIR Lowering", "diagnostic_driver_backend"),
    # Lexing, parsing, macros, resolution & HIR lowering (frontend_only)
    "rustc_lexer": ("L2: Lexing, Parsing & AST", "frontend_only"),
    "rustc_parse": ("L2: Lexing, Parsing & AST", "frontend_only"),
    "rustc_parse_format": ("L2: Lexing, Parsing & AST", "frontend_only"),
    "rustc_ast": ("L2: Lexing, Parsing & AST", "frontend_only"),
    "rustc_ast_ir": ("L2: Lexing, Parsing & AST", "frontend_only"),
    "rustc_ast_passes": ("L2: Lexing, Parsing & AST", "frontend_only"),
    "rustc_ast_lowering": ("L4: Name Resolution & HIR Lowering", "frontend_only"),
    "rustc_attr_ir": ("L3: Attributes & Macro Expansion", "frontend_only"),
    "rustc_attr_parsing": ("L3: Attributes & Macro Expansion", "frontend_only"),
    "rustc_expand": ("L3: Attributes & Macro Expansion", "frontend_only"),
    "rustc_expand_queries": ("L3: Attributes & Macro Expansion", "frontend_only"),
    "rustc_builtin_macros": ("L3: Attributes & Macro Expansion", "frontend_only"),
    "rustc_proc_macro": ("L3: Attributes & Macro Expansion", "frontend_only"),
    "rustc_resolve": ("L4: Name Resolution & HIR Lowering", "frontend_only"),
    "rustc_hir": ("L4: Name Resolution & HIR Lowering", "frontend_only"),
    "rustc_hir_id": ("L4: Name Resolution & HIR Lowering", "frontend_only"),
    # Type/trait checking, lints, pattern & borrow checking (frontend_only)
    "rustc_hir_analysis": ("L5: Types, Traits & HIR Analysis", "frontend_only"),
    "rustc_hir_typeck": ("L5: Types, Traits & HIR Analysis", "frontend_only"),
    "rustc_infer": ("L5: Types, Traits & HIR Analysis", "frontend_only"),
    "rustc_trait_selection": ("L5: Types, Traits & HIR Analysis", "frontend_only"),
    "rustc_next_trait_solver": ("L5: Types, Traits & HIR Analysis", "frontend_only"),
    "rustc_traits": ("L5: Types, Traits & HIR Analysis", "frontend_only"),
    "rustc_ty_walk": ("L5: Types, Traits & HIR Analysis", "frontend_only"),
    "rustc_privacy": ("L5: Types, Traits & HIR Analysis", "frontend_only"),
    "rustc_passes": ("L5: Types, Traits & HIR Analysis", "frontend_only"),
    "rustc_lint": ("L5: Types, Traits & HIR Analysis", "frontend_only"),
    "rustc_lint_defs": ("L5: Types, Traits & HIR Analysis", "frontend_only"),
    "rustc_pattern_analysis": ("L6: THIR, Borrowck & MIR Dataflow", "frontend_only"),
    "rustc_transmute": ("L5: Types, Traits & HIR Analysis", "frontend_only"),
    "rustc_mir_build": ("L6: THIR, Borrowck & MIR Dataflow", "frontend_only"),
    "rustc_borrowck": ("L6: THIR, Borrowck & MIR Dataflow", "frontend_only"),
    "rustc_mir_dataflow": ("L6: THIR, Borrowck & MIR Dataflow", "frontend_only"),
    # Shared ABI, target, TyCtxt, MIR, CTFE, metadata, codegen_ssa, public MIR
    "rustc_abi": ("L7: ABI, Target, TyCtxt & MIR Middle", "semantic_middle_shared"),
    "rustc_target": ("L7: ABI, Target, TyCtxt & MIR Middle", "semantic_middle_shared"),
    "rustc_type_ir": ("L7: ABI, Target, TyCtxt & MIR Middle", "semantic_middle_shared"),
    "rustc_type_ir_macros": ("L7: ABI, Target, TyCtxt & MIR Middle", "semantic_middle_shared"),
    "rustc_middle": ("L7: ABI, Target, TyCtxt & MIR Middle", "semantic_middle_shared"),
    "rustc_ty_utils": ("L7: ABI, Target, TyCtxt & MIR Middle", "semantic_middle_shared"),
    "rustc_const_eval": ("L7: ABI, Target, TyCtxt & MIR Middle", "semantic_middle_shared"),
    "rustc_mir_transform": ("L7: ABI, Target, TyCtxt & MIR Middle", "semantic_middle_shared"),
    "rustc_monomorphize": ("L9: Monomorphization, SSA & Backends", "semantic_middle_shared"),
    "rustc_symbol_mangling": ("L9: Monomorphization, SSA & Backends", "semantic_middle_shared"),
    "rustc_crate_store": ("L8: Metadata, Incremental & Query Engine", "semantic_middle_shared"),
    "rustc_metadata": ("L8: Metadata, Incremental & Query Engine", "semantic_middle_shared"),
    "rustc_incremental": ("L8: Metadata, Incremental & Query Engine", "semantic_middle_shared"),
    "rustc_query_impl": ("L8: Metadata, Incremental & Query Engine", "semantic_middle_shared"),
    "rustc_codegen_ssa": ("L9: Monomorphization, SSA & Backends", "semantic_middle_shared"),
    "rustc_sanitizers": ("L9: Monomorphization, SSA & Backends", "semantic_middle_shared"),
    "rustc_public": ("L10: Driver, Public MIR & Rustdoc", "semantic_middle_shared"),
    "rustc_public_bridge": ("L10: Driver, Public MIR & Rustdoc", "semantic_middle_shared"),
    # Concrete backends, CLI driver, interface & rustdoc (diagnostic_driver_backend)
    "rustc_codegen_llvm": ("L9: Monomorphization, SSA & Backends", "diagnostic_driver_backend"),
    "rustc_llvm": ("L9: Monomorphization, SSA & Backends", "diagnostic_driver_backend"),
    "rustc_codegen_cranelift": ("L9: Monomorphization, SSA & Backends", "diagnostic_driver_backend"),
    "rustc_codegen_gcc": ("L9: Monomorphization, SSA & Backends", "diagnostic_driver_backend"),
    "rustc_interface": ("L10: Driver, Public MIR & Rustdoc", "diagnostic_driver_backend"),
    "rustc_driver_impl": ("L10: Driver, Public MIR & Rustdoc", "diagnostic_driver_backend"),
    "rustc_driver": ("L10: Driver, Public MIR & Rustdoc", "diagnostic_driver_backend"),
    "rustc": ("L10: Driver, Public MIR & Rustdoc", "diagnostic_driver_backend"),
    "librustdoc": ("L10: Driver, Public MIR & Rustdoc", "diagnostic_driver_backend"),
}

TOOL_CLASSIFICATION: dict[str, str] = {
    "build-manifest": "release_and_dist",
    "bump-stage0": "build_and_bootstrap",
    "cargo": "submodule",
    "cargotest": "test_harness",
    "cherry-pick.sh": "standalone_script",
    "clippy": "linter_formatter_ide_subtree",
    "collect-license-metadata": "tidy_and_compliance",
    "compiletest": "test_harness",
    "coverage-dump": "test_harness",
    "enzyme": "submodule",
    "error_index_generator": "documentation",
    "features-status-dump": "documentation",
    "generate-copyright": "tidy_and_compliance",
    "generate-windows-sys": "build_and_bootstrap",
    "html-checker": "test_harness",
    "jsondocck": "test_harness",
    "jsondoclint": "test_harness",
    "libcxx-version": "build_and_bootstrap",
    "linkchecker": "documentation",
    "lint-docs": "documentation",
    "lld-wrapper": "linker_and_binary_wrapper",
    "llvm-bitcode-linker": "linker_and_binary_wrapper",
    "miri": "linter_formatter_ide_subtree",
    "miropt-test-tools": "test_harness",
    "nix-dev-shell": "build_and_bootstrap",
    "opt-dist": "release_and_dist",
    "publish_toolstate.py": "standalone_script",
    "remote-test-client": "test_harness",
    "remote-test-server": "test_harness",
    "replace-version-placeholder": "release_and_dist",
    "run-make-support": "test_harness",
    "rust-analyzer": "linter_formatter_ide_subtree",
    "rust-installer": "release_and_dist",
    "rustbook": "documentation",
    "rustc-perf": "submodule",
    "rustdoc": "documentation",
    "rustdoc-gui-test": "test_harness",
    "rustdoc-js": "test_harness",
    "rustdoc-themes": "documentation",
    "rustfmt": "linter_formatter_ide_subtree",
    "test-float-parse": "test_harness",
    "tidy": "tidy_and_compliance",
    "tier-check": "tidy_and_compliance",
    "unicode-table-generator": "build_and_bootstrap",
    "unstable-book-gen": "documentation",
    "wasm-component-ld": "linker_and_binary_wrapper",
    "x": "build_and_bootstrap",
}


class GitTreeReader:
    """Fast read-only Git tree/blob reader backed by `git ls-tree` and `git cat-file --batch`."""

    def __init__(self, repo: Path, rev: str) -> None:
        self.repo = repo
        self.rev = rev
        self.commit_sha = subprocess.check_output(
            ["git", "-C", str(repo), "rev-parse", f"{rev}^{{commit}}"], text=True
        ).strip()
        self.commit_date = subprocess.check_output(
            ["git", "-C", str(repo), "show", "-s", "--format=%cI", self.commit_sha], text=True
        ).strip()
        self.commit_subject = subprocess.check_output(
            ["git", "-C", str(repo), "show", "-s", "--format=%s", self.commit_sha], text=True
        ).strip()

        self.root_entries: list[tuple[str, str, str, str]] = []
        for line in subprocess.check_output(
            ["git", "-C", str(repo), "ls-tree", self.commit_sha], text=True
        ).splitlines():
            mode, typ, rest = line.split(" ", 2)
            sha, name = rest.split("\t", 1)
            self.root_entries.append((mode, typ, sha, name))

        self.all_entries: list[tuple[str, str, str, int, str]] = []
        self.blob_sha_by_path: dict[str, str] = {}
        for line in subprocess.check_output(
            ["git", "-C", str(repo), "ls-tree", "-r", "-l", self.commit_sha], text=True
        ).splitlines():
            header, path = line.split("\t", 1)
            parts = header.split()
            mode, typ, sha, size_s = parts[0], parts[1], parts[2], parts[3]
            size = 0 if size_s == "-" else int(size_s)
            self.all_entries.append((mode, typ, sha, size, path))
            if typ == "blob":
                self.blob_sha_by_path[path] = sha

    def read_blobs(self, paths: list[str]) -> dict[str, bytes]:
        if not paths:
            return {}
        unique_paths = [p for p in dict.fromkeys(paths) if p in self.blob_sha_by_path]
        shas = [self.blob_sha_by_path[p] for p in unique_paths]
        proc = subprocess.Popen(
            ["git", "-C", str(self.repo), "cat-file", "--batch"],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
        )
        payload = ("\n".join(shas) + "\n").encode("ascii")
        stdout_bytes, _ = proc.communicate(payload)
        if proc.returncode != 0:
            raise RuntimeError(f"git cat-file --batch exited with {proc.returncode}")

        out: dict[str, bytes] = {}
        mv = memoryview(stdout_bytes)
        offset = 0
        for p in unique_paths:
            nl = stdout_bytes.index(b"\n", offset)
            header = bytes(mv[offset:nl]).decode("ascii")
            size = int(header.split()[2])
            start = nl + 1
            end = start + size
            out[p] = bytes(mv[start:end])
            offset = end + 1  # skip trailing LF
        return out

    def list_immediate(self, prefix: str) -> list[tuple[str, str, str, str]]:
        out = []
        for line in subprocess.check_output(
            ["git", "-C", str(self.repo), "ls-tree", f"{self.commit_sha}:{prefix}"], text=True
        ).splitlines():
            mode, typ, rest = line.split(" ", 2)
            sha, name = rest.split("\t", 1)
            out.append((mode, typ, sha, name))
        return out


def line_stats_from_bytes(raw_bytes: bytes) -> tuple[int, int]:
    if b"\x00" in raw_bytes[:8192]:
        return (0, 0)
    txt = raw_bytes.decode("utf-8", errors="ignore")
    lines = txt.splitlines()
    sloc = 0
    for line in lines:
        s = line.strip()
        if s and not s.startswith(("//", "/*", "*", "# ")):
            if s == "#":
                continue
            sloc += 1
    return (len(lines), sloc)


def rust_sloc_from_text(txt: str) -> tuple[int, int]:
    lines = txt.splitlines()
    sloc = 0
    for line in lines:
        s = line.strip()
        if s and not s.startswith("//") and not s.startswith("/*") and not s.startswith("*"):
            sloc += 1
    return (len(lines), sloc)


def extract_cargo_deps(data: dict) -> set[str]:
    deps: set[str] = set()

    def collect_table(tbl: dict) -> None:
        for k, v in tbl.items():
            if isinstance(v, dict) and "package" in v:
                deps.add(v["package"])
            else:
                deps.add(k)

    for sec in ("dependencies", "build-dependencies"):
        if isinstance(data.get(sec), dict):
            collect_table(data[sec])
    if isinstance(data.get("target"), dict):
        for _, tcfg in data["target"].items():
            if isinstance(tcfg, dict):
                for sec in ("dependencies", "build-dependencies"):
                    if isinstance(tcfg.get(sec), dict):
                        collect_table(tcfg[sec])
    return deps


def parse_queries_rs(queries_txt: str) -> dict:
    """Parse all `query` and `non_query` declarations from `compiler/rustc_middle/src/queries.rs`."""
    queries = []
    non_queries = []

    clean_lines = []
    for line in queries_txt.splitlines():
        stripped = line.lstrip()
        if stripped.startswith("//"):
            clean_lines.append("")
        else:
            clean_lines.append(line.split("//")[0])
    clean = "\n".join(clean_lines)

    for m_nq in re.finditer(r"^\s*non_query\s+([A-Za-z0-9_]+)\b", clean, re.M):
        line_no = clean[: m_nq.start()].count("\n") + 1
        non_queries.append({"name": m_nq.group(1), "line": line_no})

    known_mods = [
        "arena_cache",
        "cache_on_disk",
        "depth_limit",
        "eval_always",
        "feedable",
        "handle_cycle_error",
        "no_force",
        "no_hash",
        "separate_provide_extern",
    ]
    mod_counts = {k: 0 for k in known_mods}
    mod_counts["desc"] = 0
    mod_counts["returns_error_guaranteed"] = 0

    pos = 0
    q_pat = re.compile(r"^\s*query\s+([a-z0-9_]+)\s*\(", re.M)
    while True:
        m = q_pat.search(clean, pos)
        if not m:
            break
        qname = m.group(1)
        line_no = clean[: m.start()].count("\n") + 1
        p_idx = m.end() - 1
        p_depth = 0
        while p_idx < len(clean):
            if clean[p_idx] == "(":
                p_depth += 1
            elif clean[p_idx] == ")":
                p_depth -= 1
                if p_depth == 0:
                    p_idx += 1
                    break
            p_idx += 1
        brace_open = clean.find("{", p_idx)
        ret_sig = " ".join(clean[p_idx:brace_open].split())
        b_idx = brace_open
        b_depth = 0
        while b_idx < len(clean):
            if clean[b_idx] == "{":
                b_depth += 1
            elif clean[b_idx] == "}":
                b_depth -= 1
                if b_depth == 0:
                    b_idx += 1
                    break
            b_idx += 1
        mod_block = clean[brace_open + 1 : b_idx - 1]
        mod_without_desc = re.sub(r"\bdesc\s*\{[^{}]*(?:\{[^{}]*\}[^{}]*)*\}", "", mod_block)
        tokens = set(re.findall(r"\b([a-z_]+)\b", mod_without_desc))
        q_mods = sorted(k for k in known_mods if k in tokens)
        for k in q_mods:
            mod_counts[k] += 1
        if re.search(r"\bdesc\s*\{", mod_block):
            mod_counts["desc"] += 1
        ret_err_guar = bool(re.search(r"Result\s*<.*,\s*ErrorGuaranteed\s*>", ret_sig))
        if ret_err_guar:
            mod_counts["returns_error_guaranteed"] += 1
        queries.append(
            {
                "name": qname,
                "line": line_no,
                "return_sig": ret_sig,
                "modifiers": q_mods,
                "returns_error_guaranteed": ret_err_guar,
            }
        )
        pos = b_idx

    return {
        "query_count": len(queries),
        "non_query_count": len(non_queries),
        "non_queries": non_queries,
        "modifier_counts": mod_counts,
        "queries": queries,
    }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--rust-repo", type=Path, default=Path("."), help="Path to rust-lang/rust Git repository")
    ap.add_argument("--rev", default=DEFAULT_REV, help="Git revision to inspect")
    ap.add_argument("--out", type=Path, default=Path("rust_repo_inventory.json"), help="Output JSON file")
    args = ap.parse_args()

    reader = GitTreeReader(args.rust_repo, args.rev)
    version_str = (
        reader.read_blobs(["src/version"])["src/version"].decode("utf-8").strip()
    )

    paths_to_read: list[str] = [".gitmodules", "triagebot.toml", "src/stage0"]
    for mode, typ, _, _, p in reader.all_entries:
        if typ != "blob":
            continue
        if p.count("/") == 0 or p.endswith(("Cargo.toml", "Cargo.lock")) or p.endswith(SOURCE_EXTS):
            paths_to_read.append(p)

    blobs = reader.read_blobs(paths_to_read)

    # 1. Top-level census
    top_dir_stats: dict[str, dict] = defaultdict(
        lambda: {"blobs": 0, "submodules": 0, "bytes": 0, "source_files": 0, "raw_lines": 0, "approx_sloc": 0}
    )
    src_subdir_stats: dict[str, dict] = defaultdict(
        lambda: {"blobs": 0, "submodules": 0, "bytes": 0, "source_files": 0, "raw_lines": 0, "approx_sloc": 0}
    )
    for mode, typ, sha, size, p in reader.all_entries:
        top = p.split("/", 1)[0]
        st = top_dir_stats[top]
        if typ == "commit":
            st["submodules"] += 1
        elif typ == "blob":
            st["blobs"] += 1
            st["bytes"] += size
            if p in blobs and p.endswith(CODE_EXTS):
                raw, sloc = line_stats_from_bytes(blobs[p])
                st["source_files"] += 1
                st["raw_lines"] += raw
                st["approx_sloc"] += sloc
        if p.startswith("src/") and p.count("/") >= 1:
            sub = p.split("/")[1]
            sst = src_subdir_stats[sub]
            if typ == "commit":
                sst["submodules"] += 1
            elif typ == "blob":
                sst["blobs"] += 1
                sst["bytes"] += size
                if p in blobs and p.endswith(CODE_EXTS):
                    raw, sloc = line_stats_from_bytes(blobs[p])
                    sst["source_files"] += 1
                    sst["raw_lines"] += raw
                    sst["approx_sloc"] += sloc

    root_files = []
    root_dirs = []
    for mode, typ, _, name in reader.root_entries:
        if typ == "blob":
            b = blobs.get(name, b"")
            raw, sloc = line_stats_from_bytes(b)
            root_files.append(
                {"name": name, "mode": mode, "bytes": len(b), "raw_lines": raw, "approx_sloc": sloc}
            )
        elif typ == "tree":
            st = top_dir_stats[name]
            root_dirs.append({"name": name, "mode": mode, **st})

    cargo_tomls = sorted(p for p in reader.blob_sha_by_path if p == "Cargo.toml" or p.endswith("/Cargo.toml"))
    cargo_locks = sorted(p for p in reader.blob_sha_by_path if p == "Cargo.lock" or p.endswith("/Cargo.lock"))
    workspaces = []
    for p in cargo_tomls:
        try:
            data = tomllib.loads(blobs[p].decode("utf-8"))
        except Exception:
            continue
        if "workspace" in data or "patch" in data:
            ws = data.get("workspace", {})
            patch = data.get("patch", {})
            workspaces.append(
                {
                    "path": p,
                    "has_package": "package" in data,
                    "resolver": ws.get("resolver"),
                    "members_count": len(ws.get("members", [])),
                    "members": ws.get("members", []),
                    "exclude": ws.get("exclude", []),
                    "patch_crates_io": list(patch.get("crates-io", {}).keys())
                    if isinstance(patch.get("crates-io"), dict)
                    else [],
                }
            )

    lock_summaries = []
    for p in cargo_locks:
        txt = blobs[p].decode("utf-8", errors="ignore")
        pkg_cnt = len(re.findall(r"^\[\[package\]\]", txt, re.M))
        lock_summaries.append({"path": p, "package_count": pkg_cnt})

    # 2. Compiler crates census
    compiler_cargo_paths = sorted(p for p in cargo_tomls if p.startswith("compiler/"))
    direct_compiler_dirs = sorted(
        name for _, typ, _, name in reader.list_immediate("compiler") if typ == "tree"
    )

    pkg_to_key: dict[str, str] = {}
    raw_crate_meta: dict[str, dict] = {}

    for d in direct_compiler_dirs:
        ct_path = f"compiler/{d}/Cargo.toml"
        ct = tomllib.loads(blobs[ct_path].decode("utf-8"))
        pkg = ct["package"]["name"]
        pkg_to_key[pkg] = d
        raw_crate_meta[d] = {"dir": f"compiler/{d}", "manifest": ct_path, "toml": ct, "pkg_name": pkg}

    rd_toml = tomllib.loads(blobs["src/librustdoc/Cargo.toml"].decode("utf-8"))
    pkg_to_key[rd_toml["package"]["name"]] = "librustdoc"
    raw_crate_meta["librustdoc"] = {
        "dir": "src/librustdoc",
        "manifest": "src/librustdoc/Cargo.toml",
        "toml": rd_toml,
        "pkg_name": rd_toml["package"]["name"],
    }

    nested_compiler_manifests = [p for p in compiler_cargo_paths if p.count("/") > 2]
    nested_prefixes = [p[: -len("Cargo.toml")] for p in nested_compiler_manifests]

    crate_line_stats: dict[str, dict] = {
        k: {"files": 0, "raw_lines": 0, "approx_sloc": 0, "cpp_files": 0, "cpp_raw_lines": 0}
        for k in raw_crate_meta
    }
    rustc_private_deps: dict[str, set[str]] = defaultdict(set)
    extern_crate_re = re.compile(r"^\s*extern\s+crate\s+(rustc_[a-z0-9_]+)\b", re.M)

    for mode, typ, _, _, p in reader.all_entries:
        if typ != "blob":
            continue
        if p.startswith("src/librustdoc/") and p.endswith((".rs", ".c", ".cpp", ".h")):
            txt = blobs[p].decode("utf-8", errors="ignore")
            raw, sloc = rust_sloc_from_text(txt)
            crate_line_stats["librustdoc"]["files"] += 1
            crate_line_stats["librustdoc"]["raw_lines"] += raw
            crate_line_stats["librustdoc"]["approx_sloc"] += sloc
            for m_ec in extern_crate_re.finditer(txt):
                if m_ec.group(1) in pkg_to_key:
                    rustc_private_deps["librustdoc"].add(pkg_to_key[m_ec.group(1)])
        elif p.startswith("compiler/") and p.count("/") >= 2:
            if any(p.startswith(np) for np in nested_prefixes):
                continue
            d = p.split("/")[1]
            if d in crate_line_stats and p.endswith((".rs", ".c", ".cpp", ".h")):
                txt = blobs[p].decode("utf-8", errors="ignore")
                raw, sloc = rust_sloc_from_text(txt)
                crate_line_stats[d]["files"] += 1
                crate_line_stats[d]["raw_lines"] += raw
                crate_line_stats[d]["approx_sloc"] += sloc
                if p.endswith((".c", ".cpp", ".h")):
                    crate_line_stats[d]["cpp_files"] += 1
                    crate_line_stats[d]["cpp_raw_lines"] += raw
                if p.endswith(".rs"):
                    for m_ec in extern_crate_re.finditer(txt):
                        if m_ec.group(1) in pkg_to_key and pkg_to_key[m_ec.group(1)] != d:
                            rustc_private_deps[d].add(pkg_to_key[m_ec.group(1)])

    internal_deps: dict[str, list[str]] = {}
    internal_dependents: dict[str, list[str]] = {k: [] for k in raw_crate_meta}
    for k, meta in raw_crate_meta.items():
        all_deps = extract_cargo_deps(meta["toml"])
        ideps = sorted({pkg_to_key[dep] for dep in all_deps if dep in pkg_to_key and pkg_to_key[dep] != k})
        internal_deps[k] = ideps
        for target_k in ideps:
            internal_dependents[target_k].append(k)
    for k in internal_dependents:
        internal_dependents[k].sort()

    memo_depth: dict[str, int] = {}
    memo_chain: dict[str, list[str]] = {}

    def get_depth(k: str) -> int:
        if k in memo_depth:
            return memo_depth[k]
        if not internal_deps[k]:
            memo_depth[k] = 0
            return 0
        d = 1 + max(get_depth(dep) for dep in internal_deps[k])
        memo_depth[k] = d
        return d

    def get_longest_chain(k: str) -> list[str]:
        if k in memo_chain:
            return memo_chain[k]
        best = [k]
        for dep in internal_deps[k]:
            cand = [k] + get_longest_chain(dep)
            if len(cand) > len(best):
                best = cand
        memo_chain[k] = best
        return best

    def get_trans_deps(k: str) -> set[str]:
        seen: set[str] = set()
        stack = list(internal_deps[k])
        while stack:
            cur = stack.pop()
            if cur not in seen:
                seen.add(cur)
                stack.extend(internal_deps[cur])
        return seen

    def get_trans_dependents(k: str) -> set[str]:
        seen: set[str] = set()
        stack = list(internal_dependents[k])
        while stack:
            cur = stack.pop()
            if cur not in seen:
                seen.add(cur)
                stack.extend(internal_dependents[cur])
        return seen

    compiler_crates_table = []
    for k in sorted(raw_crate_meta):
        meta = raw_crate_meta[k]
        ct = meta["toml"]
        pkg_sec = ct.get("package", {})
        lib_sec = ct.get("lib", {})
        crate_types = list(lib_sec.get("crate-type", ["rlib"]))
        if lib_sec.get("proc-macro"):
            crate_types = ["proc-macro"]
        if ct.get("bin"):
            crate_types = [b.get("name", pkg_sec.get("name", k)) + " (bin)" for b in ct["bin"]] + (
                crate_types
                if "lib" in ct or (f"{meta['dir']}/src/lib.rs" in reader.blob_sha_by_path)
                else []
            )
        layer, split = COMPILER_CRATE_TAXONOMY[k]
        st = crate_line_stats[k]
        compiler_crates_table.append(
            {
                "key": k,
                "dir": meta["dir"],
                "package_name": meta["pkg_name"],
                "edition": pkg_sec.get("edition", "2021"),
                "crate_types": crate_types,
                "files": st["files"],
                "raw_lines": st["raw_lines"],
                "approx_sloc": st["approx_sloc"],
                "cpp_raw_lines": st["cpp_raw_lines"],
                "internal_deps": internal_deps[k],
                "rustc_private_deps": sorted(rustc_private_deps.get(k, set())),
                "out_degree": len(internal_deps[k]),
                "in_degree": len(internal_dependents[k]),
                "transitive_deps_count": len(get_trans_deps(k)),
                "transitive_dependents_count": len(get_trans_dependents(k)),
                "topological_depth": get_depth(k),
                "architectural_layer": layer,
                "verification_split": split,
            }
        )

    nested_compiler_packages = []
    for p in nested_compiler_manifests:
        ct = tomllib.loads(blobs[p].decode("utf-8"))
        prefix = p[: -len("Cargo.toml")]
        files = 0
        raw = 0
        sloc = 0
        for _, typ, _, _, fp in reader.all_entries:
            if typ == "blob" and fp.startswith(prefix) and fp.endswith(".rs"):
                deeper = [
                    np for np in nested_prefixes if np != prefix and np.startswith(prefix) and fp.startswith(np)
                ]
                if deeper:
                    continue
                r, s = rust_sloc_from_text(blobs[fp].decode("utf-8", errors="ignore"))
                files += 1
                raw += r
                sloc += s
        nested_compiler_packages.append(
            {
                "manifest": p,
                "package_name": ct.get("package", {}).get("name", "<workspace-only>"),
                "files": files,
                "raw_lines": raw,
                "approx_sloc": sloc,
            }
        )

    longest_chain = max((get_longest_chain(k) for k in raw_crate_meta), key=len)

    # 3. Query-Provider Map
    query_info = parse_queries_rs(blobs["compiler/rustc_middle/src/queries.rs"].decode("utf-8"))
    known_query_names = {q["name"] for q in query_info["queries"]}

    local_providers_by_crate: dict[str, set[str]] = defaultdict(set)
    extern_providers_by_crate: dict[str, set[str]] = defaultdict(set)
    providers_by_query: dict[str, dict[str, list[str]]] = {
        q["name"]: {"local": [], "extern": [], "fed_in": []} for q in query_info["queries"]
    }

    def extract_struct_fields(text: str, struct_kw: str) -> list[str]:
        fields: list[str] = []
        pat = re.compile(rf"\b{struct_kw}\s*\{{")
        pos = 0
        while True:
            m = pat.search(text, pos)
            if not m:
                break
            idx = m.end()
            depth = 1
            entry_start = idx
            paren_depth = 0
            bracket_depth = 0
            while idx < len(text) and depth > 0:
                ch = text[idx]
                if ch == "{":
                    depth += 1
                elif ch == "}":
                    depth -= 1
                    if depth == 0:
                        seg = text[entry_start:idx].strip()
                        m_id = re.match(r"^([a-z][a-z0-9_]*)\b", seg)
                        if m_id:
                            fields.append(m_id.group(1))
                        break
                elif ch == "(":
                    paren_depth += 1
                elif ch == ")":
                    paren_depth = max(0, paren_depth - 1)
                elif ch == "[":
                    bracket_depth += 1
                elif ch == "]":
                    bracket_depth = max(0, bracket_depth - 1)
                elif ch == "," and depth == 1 and paren_depth == 0 and bracket_depth == 0:
                    seg = text[entry_start:idx].strip()
                    m_id = re.match(r"^([a-z][a-z0-9_]*)\b", seg)
                    if m_id:
                        fields.append(m_id.group(1))
                    entry_start = idx + 1
                idx += 1
            pos = idx + 1
        return fields

    assign_any_re = re.compile(
        r"\b([A-Za-z0-9_]+(?:\.(?:queries|extern_queries))?)\.([a-z0-9_]+)\s*=(?!=)"
    )
    feed_call_re = re.compile(r"\b[A-Za-z0-9_]*feed[A-Za-z0-9_]*\.([a-z0-9_]+)\s*\(")

    for p, raw_b in blobs.items():
        if not (p.startswith("compiler/") or p.startswith("src/librustdoc/")) or not p.endswith(".rs"):
            continue
        if any(p.startswith(np) for np in nested_prefixes):
            continue
        crate_k = "librustdoc" if p.startswith("src/librustdoc/") else p.split("/")[1]
        txt = raw_b.decode("utf-8", errors="ignore")
        txt_clean = "\n".join(
            "" if l.lstrip().startswith("//") else l.split("//")[0] for l in txt.splitlines()
        )
        for m in assign_any_re.finditer(txt_clean):
            lhs, qn = m.group(1), m.group(2)
            if qn not in known_query_names:
                continue
            if "extern" in lhs:
                extern_providers_by_crate[crate_k].add(qn)
            elif any(w in lhs for w in ("providers", "p", "queries")):
                local_providers_by_crate[crate_k].add(qn)
        for qn in extract_struct_fields(txt_clean, "Providers"):
            if qn in known_query_names:
                local_providers_by_crate[crate_k].add(qn)
        for qn in extract_struct_fields(txt_clean, "ExternProviders"):
            if qn in known_query_names:
                extern_providers_by_crate[crate_k].add(qn)
        if p == "compiler/rustc_metadata/src/rmeta/decoder/cstore_impl.rs":
            for qn in extract_struct_fields(txt_clean, "provide!"):
                if qn in known_query_names:
                    extern_providers_by_crate[crate_k].add(qn)
            # Also catch macro rules inside cstore_impl.rs mapping extern queries
            for m_id in re.finditer(r"\b([a-z][a-z0-9_]*)\b", txt_clean):
                qn = m_id.group(1)
                if qn in known_query_names:
                    q_obj = next(q for q in query_info["queries"] if q["name"] == qn)
                    if "separate_provide_extern" in q_obj["modifiers"]:
                        extern_providers_by_crate[crate_k].add(qn)
        for m_feed in feed_call_re.finditer(txt_clean):
            qn = m_feed.group(1)
            if qn in providers_by_query and crate_k not in providers_by_query[qn]["fed_in"]:
                providers_by_query[qn]["fed_in"].append(crate_k)

    for ck, qset in sorted(local_providers_by_crate.items()):
        for qn in sorted(qset):
            providers_by_query[qn]["local"].append(ck)
    for ck, qset in sorted(extern_providers_by_crate.items()):
        for qn in sorted(qset):
            providers_by_query[qn]["extern"].append(ck)

    crate_provider_summary = []
    all_provider_crates = sorted(set(local_providers_by_crate) | set(extern_providers_by_crate))
    for ck in all_provider_crates:
        loc_q = sorted(local_providers_by_crate.get(ck, set()))
        ext_q = sorted(extern_providers_by_crate.get(ck, set()))
        crate_provider_summary.append(
            {
                "crate": ck,
                "local_query_count": len(loc_q),
                "extern_query_count": len(ext_q),
                "sample_local_queries": loc_q[:12],
                "sample_extern_queries": ext_q[:12],
            }
        )

    # 4. Library census (`library/*`)
    lib_entries = reader.list_immediate("library")
    library_cargos = sorted(p for p in cargo_tomls if p.startswith("library/"))
    library_dirs_table = []
    feature_re = re.compile(r"#!\[\s*feature\s*\(([^)]*)\)\s*\]")

    for mode, typ, sha, name in lib_entries:
        if typ == "blob":
            continue
        sub_prefix = f"library/{name}/"
        sub_cargos = [p for p in library_cargos if p.startswith(sub_prefix)]
        rs_files = 0
        raw_lines = 0
        sloc = 0
        features_used: set[str] = set()
        for _, btyp, _, _, fp in reader.all_entries:
            if btyp == "blob" and fp.startswith(sub_prefix) and fp.endswith((".rs", ".c", ".S", ".s")):
                txt = blobs.get(fp, b"").decode("utf-8", errors="ignore")
                r, s = rust_sloc_from_text(txt)
                rs_files += 1
                raw_lines += r
                sloc += s
                for mf in feature_re.finditer(txt):
                    for tok in mf.group(1).split(","):
                        t = tok.strip()
                        if t and re.match(r"^[a-zA-Z0-9_]+$", t):
                            features_used.add(t)
        pkg_names = []
        path_deps = set()
        crates_io_std_deps = set()
        for cp in sub_cargos:
            ct = tomllib.loads(blobs[cp].decode("utf-8"))
            if "package" in ct:
                pkg_names.append(ct["package"]["name"])
            for sec in ("dependencies", "dev-dependencies", "build-dependencies"):
                for dk, dv in ct.get(sec, {}).items():
                    if isinstance(dv, dict):
                        if "path" in dv:
                            path_deps.add(dk)
                        elif "rustc-dep-of-std" in dv.get("features", []):
                            crates_io_std_deps.add(dk)
            for _, tcfg in ct.get("target", {}).items():
                if isinstance(tcfg, dict):
                    for dk, dv in tcfg.get("dependencies", {}).items():
                        if isinstance(dv, dict):
                            if "path" in dv:
                                path_deps.add(dk)
                            elif "rustc-dep-of-std" in dv.get("features", []):
                                crates_io_std_deps.add(dk)
        library_dirs_table.append(
            {
                "name": name,
                "entry_type": "submodule"
                if typ == "commit"
                else ("crate_tree" if sub_cargos else "non_cargo_dir"),
                "submodule_sha": sha if typ == "commit" else None,
                "cargo_toml_count": len(sub_cargos),
                "packages": pkg_names,
                "files": rs_files,
                "raw_lines": raw_lines,
                "approx_sloc": sloc,
                "path_deps": sorted(path_deps),
                "rustc_dep_of_std_crates": sorted(crates_io_std_deps),
                "unstable_feature_count": len(features_used),
                "sample_features": sorted(features_used)[:10],
            }
        )

    # 5. Submodules & `src/tools/*` census
    gitmodules_cfg = configparser.ConfigParser()
    gitmodules_cfg.read_string(blobs[".gitmodules"].decode("utf-8"))
    submod_meta_by_path: dict[str, dict] = {}
    for sec in gitmodules_cfg.sections():
        sp = gitmodules_cfg[sec].get("path", "").strip()
        url = gitmodules_cfg[sec].get("url", "").strip()
        branch = gitmodules_cfg[sec].get("branch", "").strip() or None
        shallow = gitmodules_cfg[sec].get("shallow", "").strip() == "true"
        gh_repo = re.sub(r"^https?://github\.com/", "", url)
        gh_repo = gh_repo[:-4] if gh_repo.endswith(".git") else gh_repo
        submod_meta_by_path[sp] = {
            "url": url,
            "github_repo": gh_repo,
            "branch": branch,
            "shallow": shallow,
        }

    submodules_table = []
    for mode, typ, sha, _, p in reader.all_entries:
        if typ == "commit":
            sm = submod_meta_by_path.get(p, {})
            submodules_table.append({"path": p, "revision": sha, **sm})

    tools_entries = reader.list_immediate("src/tools")
    tools_table = []
    for mode, typ, sha, name in tools_entries:
        full_p = f"src/tools/{name}"
        if typ == "commit":
            tools_table.append(
                {
                    "name": name,
                    "entry_type": "submodule",
                    "role": TOOL_CLASSIFICATION[name],
                    "submodule_sha": sha,
                    "cargo_toml_count": 0,
                    "files": 0,
                    "raw_lines": 0,
                    "approx_sloc": 0,
                }
            )
        elif typ == "blob":
            raw, sloc = line_stats_from_bytes(blobs.get(full_p, b""))
            tools_table.append(
                {
                    "name": name,
                    "entry_type": "script",
                    "role": TOOL_CLASSIFICATION[name],
                    "submodule_sha": None,
                    "cargo_toml_count": 0,
                    "files": 1,
                    "raw_lines": raw,
                    "approx_sloc": sloc,
                }
            )
        else:
            prefix = full_p + "/"
            tcargos = [cp for cp in cargo_tomls if cp.startswith(prefix)]
            files = 0
            raw = 0
            sloc = 0
            for _, btyp, _, _, fp in reader.all_entries:
                if btyp == "blob" and fp.startswith(prefix) and fp.endswith(CODE_EXTS):
                    r, s = line_stats_from_bytes(blobs.get(fp, b""))
                    files += 1
                    raw += r
                    sloc += s
            tools_table.append(
                {
                    "name": name,
                    "entry_type": "directory",
                    "role": TOOL_CLASSIFICATION[name],
                    "submodule_sha": None,
                    "cargo_toml_count": len(tcargos),
                    "files": files,
                    "raw_lines": raw,
                    "approx_sloc": sloc,
                }
            )

    # 6. Bootstrap Step implementations & `tests/*` suite census
    bootstrap_steps: dict[str, dict] = {}
    step_impl_re = re.compile(r"\bimpl(?:<[^>]+>)?\s+(Step|CommandLineStep)\s+for\s+([A-Za-z0-9_]+)")
    macro_step_re = re.compile(r"^\s*(tool|test|default_test|host_test)!\s*\(\s*([A-Za-z0-9_]+)", re.M)
    bootstrap_files = 0
    bootstrap_raw_lines = 0
    bootstrap_sloc = 0
    for p, raw_b in sorted(blobs.items()):
        if not p.startswith("src/bootstrap/") or not p.endswith((".rs", ".py")):
            continue
        txt = raw_b.decode("utf-8", errors="ignore")
        r, s = rust_sloc_from_text(txt)
        bootstrap_files += 1
        bootstrap_raw_lines += r
        bootstrap_sloc += s
        if p.startswith("src/bootstrap/src/core/build_steps/") and p.endswith(".rs"):
            mod_name = p[len("src/bootstrap/src/core/build_steps/") :]
            step_names = []
            cmd_step_names = []
            for m_st in step_impl_re.finditer(txt):
                if m_st.group(1) == "Step":
                    step_names.append(m_st.group(2))
                else:
                    cmd_step_names.append(m_st.group(2))
            macro_steps = [m_mc.group(2) for m_mc in macro_step_re.finditer(txt)]
            bootstrap_steps[mod_name] = {
                "raw_lines": r,
                "approx_sloc": s,
                "direct_step_impls": sorted(set(step_names)),
                "command_line_step_impls": sorted(set(cmd_step_names)),
                "macro_generated_steps": sorted(set(macro_steps)),
            }

    stage0_txt = blobs["src/stage0"].decode("utf-8")
    stage0_cfg = {}
    for line in stage0_txt.splitlines():
        if "=" in line and not line.startswith("#") and not line.startswith("dist/"):
            k, v = line.split("=", 1)
            stage0_cfg[k.strip()] = v.strip()

    tests_entries = reader.list_immediate("tests")
    tests_table = []
    for mode, typ, _, name in tests_entries:
        if typ == "blob":
            continue
        prefix = f"tests/{name}/"
        total_blobs = 0
        rs_files = 0
        stderr_files = 0
        for _, btyp, _, _, fp in reader.all_entries:
            if btyp == "blob" and fp.startswith(prefix):
                total_blobs += 1
                if fp.endswith(".rs"):
                    rs_files += 1
                elif fp.endswith(".stderr"):
                    stderr_files += 1
        tests_table.append(
            {
                "name": name,
                "role": "shared_auxiliary" if name == "auxiliary" else "compiletest_suite",
                "total_files": total_blobs,
                "rs_files": rs_files,
                "stderr_files": stderr_files,
            }
        )

    split_totals: dict[str, dict] = defaultdict(lambda: {"crates": 0, "raw_lines": 0, "approx_sloc": 0})
    for c in compiler_crates_table:
        sp = split_totals[c["verification_split"]]
        sp["crates"] += 1
        sp["raw_lines"] += c["raw_lines"]
        sp["approx_sloc"] += c["approx_sloc"]

    inventory = {
        "repository": "rust-lang/rust",
        "revision": reader.commit_sha,
        "commit_date": reader.commit_date,
        "commit_subject": reader.commit_subject,
        "in_tree_version": version_str,
        "stage0_metadata": stage0_cfg,
        "top_level": {
            "total_root_entries": len(reader.root_entries),
            "root_file_count": len(root_files),
            "root_dir_count": len(root_dirs),
            "total_tracked_blobs": sum(1 for _, t, _, _, _ in reader.all_entries if t == "blob"),
            "total_submodules": len(submodules_table),
            "root_files": root_files,
            "root_dirs": root_dirs,
            "src_subdirs": [{"name": k, **v} for k, v in sorted(src_subdir_stats.items())],
            "cargo_toml_total": len(cargo_tomls),
            "cargo_lock_total": len(cargo_locks),
            "workspaces": workspaces,
            "cargo_locks": lock_summaries,
        },
        "compiler": {
            "direct_crate_count": len(direct_compiler_dirs),
            "compiler_plus_rustdoc_count": len(compiler_crates_table),
            "compiler_cargo_toml_count": len(compiler_cargo_paths),
            "nested_package_count": len(nested_compiler_packages),
            "direct_compiler_raw_lines": sum(
                c["raw_lines"] for c in compiler_crates_table if c["key"] != "librustdoc"
            ),
            "direct_compiler_approx_sloc": sum(
                c["approx_sloc"] for c in compiler_crates_table if c["key"] != "librustdoc"
            ),
            "librustdoc_raw_lines": crate_line_stats["librustdoc"]["raw_lines"],
            "librustdoc_approx_sloc": crate_line_stats["librustdoc"]["approx_sloc"],
            "longest_chain_length": len(longest_chain),
            "longest_chain": longest_chain,
            "verification_split_totals": dict(split_totals),
            "crates": compiler_crates_table,
            "nested_packages": nested_compiler_packages,
        },
        "queries": {
            "query_count": query_info["query_count"],
            "non_query_count": query_info["non_query_count"],
            "non_queries": query_info["non_queries"],
            "modifier_counts": query_info["modifier_counts"],
            "provider_crates_count": len(crate_provider_summary),
            "providers_by_crate": crate_provider_summary,
            "unprovided_or_feed_only_queries": [
                {
                    "name": q["name"],
                    "modifiers": q["modifiers"],
                    "fed_in": providers_by_query[q["name"]]["fed_in"],
                }
                for q in query_info["queries"]
                if not providers_by_query[q["name"]]["local"]
            ],
        },
        "library": {
            "non_file_entry_count": len(library_dirs_table),
            "crate_tree_count": sum(1 for d in library_dirs_table if d["entry_type"] == "crate_tree"),
            "submodule_count": sum(1 for d in library_dirs_table if d["entry_type"] == "submodule"),
            "non_cargo_dir_count": sum(1 for d in library_dirs_table if d["entry_type"] == "non_cargo_dir"),
            "cargo_toml_count": len(library_cargos),
            "total_raw_lines": sum(d["raw_lines"] for d in library_dirs_table),
            "total_approx_sloc": sum(d["approx_sloc"] for d in library_dirs_table),
            "entries": library_dirs_table,
        },
        "tools_and_submodules": {
            "tools_entry_count": len(tools_table),
            "tools_role_counts": {
                role: sum(1 for t in tools_table if t["role"] == role)
                for role in sorted({t["role"] for t in tools_table})
            },
            "tools": tools_table,
            "submodule_count": len(submodules_table),
            "submodules": submodules_table,
        },
        "bootstrap": {
            "files": bootstrap_files,
            "raw_lines": bootstrap_raw_lines,
            "approx_sloc": bootstrap_sloc,
            "build_step_modules": bootstrap_steps,
        },
        "tests": {
            "directory_count": len(tests_table),
            "compiletest_suite_count": sum(1 for t in tests_table if t["role"] == "compiletest_suite"),
            "total_tracked_files": sum(t["total_files"] for t in tests_table) + 1,
            "directories": tests_table,
        },
    }

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(inventory, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
