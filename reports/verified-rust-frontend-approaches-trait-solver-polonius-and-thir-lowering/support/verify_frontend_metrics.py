#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

import json
import os
import re
import tomllib

RUST_ROOT = "os.environ.get("RUST_1991_ROOT", ".")"
OUT_JSON = "/tmp/f1_frontend_metrics.json"

FRONTEND_STAGE_MAP = {
    "1_lex_parse_ast": [
        "rustc_lexer",
        "rustc_parse",
        "rustc_ast",
        "rustc_ast_pretty",
        "rustc_ast_passes",
        "rustc_ast_ir",
    ],
    "2_expand_resolve_hir": [
        "rustc_expand",
        "rustc_builtin_macros",
        "rustc_proc_macro",
        "rustc_resolve",
        "rustc_hir",
        "rustc_hir_pretty",
        "rustc_passes",
    ],
    "3_type_ir_and_trait_solver": [
        "rustc_type_ir",
        "rustc_type_ir_macros",
        "rustc_next_trait_solver",
        "rustc_pattern_analysis",
    ],
    "4_typeck_infer_trait_selection": [
        "rustc_infer",
        "rustc_trait_selection",
        "rustc_hir_analysis",
        "rustc_hir_typeck",
        "rustc_traits",
    ],
    "5_thir_mir_build_borrowck_polonius": [
        "rustc_mir_build",
        "rustc_borrowck",
        "rustc_polonius",
        "rustc_mir_dataflow",
        "rustc_const_eval",
        "rustc_mir_transform",
    ],
    "6_middle_abi_metadata_diagnostics": [
        "rustc_middle",
        "rustc_abi",
        "rustc_target",
        "rustc_session",
        "rustc_metadata",
        "rustc_privacy",
        "rustc_lint",
        "rustc_lint_defs",
        "rustc_errors",
        "rustc_error_codes",
        "rustc_error_messages",
        "rustc_fluent_macro",
        "rustc_feature",
        "rustc_span",
        "rustc_data_structures",
        "rustc_index",
        "rustc_index_macros",
        "rustc_serialize",
        "rustc_Arena",
        "rustc_arena",
        "rustc_graphviz",
        "rustc_attr_parsing",
        "rustc_attr_data_structures",
        "rustc_hir_id",
        "rustc_Query_system",
        "rustc_query_system",
        "rustc_query_impl",
        "rustc_incremental",
        "rustc_transmute",
        "rustc_ty_utils",
        "rustc_symbol_mangling",
        "rustc_monomorphize",
        "rustc_sanitizers",
    ],
    "7_codegen_backends": [
        "rustc_codegen_ssa",
        "rustc_codegen_llvm",
        "rustc_llvm",
        "rustc_codegen_cranelift",
        "rustc_codegen_gcc",
    ],
}


def count_crate_stats(crate_dir):
    rs_files = 0
    rs_lines = 0
    rs_code_lines = 0
    ftl_files = 0
    ftl_lines = 0
    ftl_messages = 0
    for root, _, files in os.walk(crate_dir):
        if "target" in root.split(os.sep):
            continue
        for f in files:
            p = os.path.join(root, f)
            if f.endswith(".rs"):
                rs_files += 1
                with open(p, "r", encoding="utf-8", errors="replace") as fh:
                    for line in fh:
                        rs_lines += 1
                        s = line.strip()
                        if s and not s.startswith("//"):
                            rs_code_lines += 1
            elif f.endswith(".ftl"):
                ftl_files += 1
                with open(p, "r", encoding="utf-8", errors="replace") as fh:
                    for line in fh:
                        ftl_lines += 1
                        if re.match(r"^[a-zA-Z0-9_-]+\s*=", line):
                            ftl_messages += 1
    deps = []
    cargo_toml = os.path.join(crate_dir, "Cargo.toml")
    if os.path.exists(cargo_toml):
        with open(cargo_toml, "rb") as fh:
            data = tomllib.load(fh)
        deps = sorted(list(data.get("dependencies", {}).keys()))
    return {
        "rs_files": rs_files,
        "rs_lines": rs_lines,
        "rs_code_lines": rs_code_lines,
        "ftl_files": ftl_files,
        "ftl_lines": ftl_lines,
        "ftl_messages": ftl_messages,
        "dependencies": deps,
    }


def main():
    compiler_dir = os.path.join(RUST_ROOT, "compiler")
    crates = {}
    for entry in sorted(os.listdir(compiler_dir)):
        cpath = os.path.join(compiler_dir, entry)
        if os.path.isdir(cpath) and os.path.exists(os.path.join(cpath, "Cargo.toml")):
            crates[entry] = count_crate_stats(cpath)

    stage_summary = {}
    assigned = set()
    for stage, clist in FRONTEND_STAGE_MAP.items():
        s_files = 0
        s_lines = 0
        s_code = 0
        s_ftl = 0
        present = []
        for c in clist:
            if c in crates:
                assigned.add(c)
                present.append(c)
                s_files += crates[c]["rs_files"]
                s_lines += crates[c]["rs_lines"]
                s_code += crates[c]["rs_code_lines"]
                s_ftl += crates[c]["ftl_messages"]
        stage_summary[stage] = {
            "crates": present,
            "rs_files": s_files,
            "rs_lines": s_lines,
            "rs_code_lines": s_code,
            "ftl_messages": s_ftl,
        }

    unassigned = sorted(set(crates.keys()) - assigned)
    u_files = sum(crates[c]["rs_files"] for c in unassigned)
    u_lines = sum(crates[c]["rs_lines"] for c in unassigned)
    u_code = sum(crates[c]["rs_code_lines"] for c in unassigned)
    u_ftl = sum(crates[c]["ftl_messages"] for c in unassigned)
    stage_summary["8_driver_interface_other"] = {
        "crates": unassigned,
        "rs_files": u_files,
        "rs_lines": u_lines,
        "rs_code_lines": u_code,
        "ftl_messages": u_ftl,
    }

    # Inspect key files in rustc_next_trait_solver, rustc_polonius, rustc_borrowck, rustc_mir_build
    thir_file = os.path.join(compiler_dir, "rustc_middle/src/thir.rs")
    thir_expr_kinds = []
    if os.path.exists(thir_file):
        with open(thir_file, "r", encoding="utf-8") as fh:
            text = fh.read()
        m = re.search(r"pub enum ExprKind<'tcx>\s*\{(.*?)\n\}", text, re.S)
        if m:
            for line in m.group(1).splitlines():
                s = line.strip()
                if s and not s.startswith("//") and not s.startswith("#["):
                    variant = s.split("(")[0].split("{")[0].split(",")[0].strip()
                    if variant and variant[0].isupper():
                        thir_expr_kinds.append(variant)

    # Error codes count
    err_codes_file = os.path.join(compiler_dir, "rustc_error_codes/src/error_codes.rs")
    err_codes_count = 0
    if os.path.exists(err_codes_file):
        with open(err_codes_file, "r", encoding="utf-8") as fh:
            err_codes_count = len(re.findall(r"\bE\d{4}\b", fh.read()))

    out = {
        "total_compiler_crates": len(crates),
        "total_rs_lines": sum(c["rs_lines"] for c in crates.values()),
        "total_rs_code_lines": sum(c["rs_code_lines"] for c in crates.values()),
        "total_ftl_messages": sum(c["ftl_messages"] for c in crates.values()),
        "error_code_mentions_in_registry": err_codes_count,
        "stage_summary": stage_summary,
        "portable_solver_crates": {
            c: crates[c]
            for c in [
                "rustc_type_ir",
                "rustc_next_trait_solver",
                "rustc_pattern_analysis",
                "rustc_polonius",
                "rustc_borrowck",
                "rustc_mir_build",
                "rustc_hir_typeck",
                "rustc_hir_analysis",
                "rustc_trait_selection",
                "rustc_infer",
                "rustc_resolve",
                "rustc_expand",
                "rustc_parse",
            ]
            if c in crates
        },
        "thir_expr_kind_variants": thir_expr_kinds,
        "thir_expr_kind_count": len(thir_expr_kinds),
    }
    with open(OUT_JSON, "w", encoding="utf-8") as fh:
        json.dump(out, fh, indent=2)
    print("Wrote", OUT_JSON)
    print("Total compiler crates:", out["total_compiler_crates"])
    print("Total rs lines:", out["total_rs_lines"], "code lines:", out["total_rs_code_lines"])
    print("THIR ExprKind variants:", out["thir_expr_kind_count"])
    for st, info in stage_summary.items():
        print(f"  {st}: {len(info['crates'])} crates, {info['rs_lines']} lines ({info['rs_code_lines']} LOC), {info['ftl_messages']} ftl msgs")


if __name__ == "__main__":
    main()
