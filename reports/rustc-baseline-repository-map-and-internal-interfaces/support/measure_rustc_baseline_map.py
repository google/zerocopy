#!/usr/bin/env python3
"""Compute repository map and internal interface metrics for a rust-lang/rust checkout."""
import argparse
import json
import os
import re
import subprocess
from pathlib import Path


def git_rev(path: Path) -> str:
    return subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=str(path), text=True).strip()


def count_lines(root: Path, exts=(".rs", ".cpp", ".c", ".h", ".td")) -> dict:
    files = 0
    raw = 0
    sloc = 0
    for dp, dns, fns in os.walk(root):
        dns[:] = [d for d in dns if d not in (".git", "target", "build")]
        for f in fns:
            if exts and not f.endswith(exts):
                continue
            p = Path(dp) / f
            if p.is_symlink():
                continue
            try:
                txt = p.read_text(encoding="utf-8", errors="ignore")
            except Exception:
                continue
            files += 1
            lines = txt.splitlines()
            raw += len(lines)
            for l in lines:
                s = l.strip()
                if s and not s.startswith("//") and not s.startswith("/*") and not s.startswith("*"):
                    sloc += 1
    return {"files": files, "raw_lines": raw, "approx_sloc": sloc}


def parse_enum(root: Path, rel_path: str, enum_name: str) -> dict:
    p = root / rel_path
    lines = p.read_text(encoding="utf-8").splitlines()
    start_line = None
    brace_depth = 0
    in_enum = False
    variants = []
    pat = re.compile(rf"pub\s+enum\s+{re.escape(enum_name)}\b")
    for idx, line in enumerate(lines, 1):
        if not in_enum:
            if pat.search(line):
                in_enum = True
                start_line = idx
                brace_depth += line.count("{") - line.count("}")
        else:
            prev_depth = brace_depth
            clean = line.split("//")[0]
            if prev_depth == 1:
                m = re.match(r"^\s*(?:#\[[^\]]*\]\s*)*([A-Z][A-Za-z0-9_]*)\b", clean)
                if m and m.group(1) not in ("Doc",):
                    variants.append(m.group(1))
            brace_depth += clean.count("{") - clean.count("}")
            if brace_depth <= 0:
                return {
                    "file": rel_path,
                    "start_line": start_line,
                    "end_line": idx,
                    "count": len(variants),
                    "variants": variants,
                }
    return {"file": rel_path, "start_line": start_line, "count": len(variants), "variants": variants}


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--rust-root", required=True, type=Path, help="Path to rust-lang/rust checkout")
    ap.add_argument("--out", required=True, type=Path, help="Output JSON path")
    args = ap.parse_args()
    root = args.rust_root

    crates = {}
    for p in sorted((root / "compiler").iterdir()):
        if p.is_dir() and (p / "Cargo.toml").is_file():
            cargo_txt = (p / "Cargo.toml").read_text(encoding="utf-8", errors="ignore")
            deps = re.findall(r"^(rustc_[a-z0-9_]+)\s*=", cargo_txt, re.M)
            st = count_lines(p, (".rs", ".cpp", ".c", ".h"))
            crates[p.name] = {
                "files": st["files"],
                "raw_lines": st["raw_lines"],
                "approx_sloc": st["approx_sloc"],
                "rustc_deps": sorted(set(deps)),
            }

    dep_counts = {c: 0 for c in crates}
    for c, info in crates.items():
        for d in info["rustc_deps"]:
            if d in dep_counts:
                dep_counts[d] += 1

    memo_chain = {}

    def longest_chain(c: str) -> list[str]:
        if c in memo_chain:
            return memo_chain[c]
        best = [c]
        for d in crates.get(c, {}).get("rustc_deps", []):
            if d in crates:
                cand = [c] + longest_chain(d)
                if len(cand) > len(best):
                    best = cand
        memo_chain[c] = best
        return best

    max_chain = max((longest_chain(c) for c in crates), key=len)

    enums_to_check = [
        ("ast_ExprKind", "compiler/rustc_ast/src/ast.rs", "ExprKind"),
        ("ast_ItemKind", "compiler/rustc_ast/src/ast.rs", "ItemKind"),
        ("ast_PatKind", "compiler/rustc_ast/src/ast.rs", "PatKind"),
        ("ast_TyKind", "compiler/rustc_ast/src/ast.rs", "TyKind"),
        ("hir_ExprKind", "compiler/rustc_hir/src/hir.rs", "ExprKind"),
        ("hir_ItemKind", "compiler/rustc_hir/src/hir.rs", "ItemKind"),
        ("hir_PatKind", "compiler/rustc_hir/src/hir.rs", "PatKind"),
        ("hir_TyKind", "compiler/rustc_hir/src/hir.rs", "TyKind"),
        ("thir_ExprKind", "compiler/rustc_middle/src/thir.rs", "ExprKind"),
        ("thir_PatKind", "compiler/rustc_middle/src/thir.rs", "PatKind"),
        ("thir_StmtKind", "compiler/rustc_middle/src/thir.rs", "StmtKind"),
        ("mir_MirPhase", "compiler/rustc_middle/src/mir/syntax.rs", "MirPhase"),
        ("mir_AnalysisPhase", "compiler/rustc_middle/src/mir/syntax.rs", "AnalysisPhase"),
        ("mir_RuntimePhase", "compiler/rustc_middle/src/mir/syntax.rs", "RuntimePhase"),
        ("mir_StatementKind", "compiler/rustc_middle/src/mir/syntax.rs", "StatementKind"),
        ("mir_TerminatorKind", "compiler/rustc_middle/src/mir/syntax.rs", "TerminatorKind"),
        ("mir_Rvalue", "compiler/rustc_middle/src/mir/syntax.rs", "Rvalue"),
        ("mir_Operand", "compiler/rustc_middle/src/mir/syntax.rs", "Operand"),
        ("mir_ProjectionElem", "compiler/rustc_middle/src/mir/syntax.rs", "ProjectionElem"),
        ("mir_CastKind", "compiler/rustc_middle/src/mir/syntax.rs", "CastKind"),
        ("mir_BinOp", "compiler/rustc_middle/src/mir/syntax.rs", "BinOp"),
        ("mir_UnOp", "compiler/rustc_middle/src/mir/syntax.rs", "UnOp"),
        ("mir_AggregateKind", "compiler/rustc_middle/src/mir/syntax.rs", "AggregateKind"),
        ("mir_NonDivergingIntrinsic", "compiler/rustc_middle/src/mir/syntax.rs", "NonDivergingIntrinsic"),
        ("ty_TyKind", "compiler/rustc_type_ir/src/ty_kind.rs", "TyKind"),
        ("ty_InstanceKind", "compiler/rustc_middle/src/ty/instance.rs", "InstanceKind"),
        ("ty_ShimKind", "compiler/rustc_middle/src/ty/instance.rs", "ShimKind"),
    ]
    ir_enums = {k: parse_enum(root, rel, ename) for k, rel, ename in enums_to_check}

    queries_txt = (root / "compiler/rustc_middle/src/queries.rs").read_text(encoding="utf-8")
    query_names = re.findall(r"^\s*query\s+([a-z0-9_]+)\s*\(", queries_txt, re.M)

    trait_methods = {}
    for f in sorted((root / "compiler/rustc_codegen_ssa/src/traits").glob("*.rs")):
        txt = f.read_text(encoding="utf-8")
        for m in re.finditer(r"pub\s+trait\s+([A-Za-z0-9_]+)[^{]*\{", txt):
            tname = m.group(1)
            start = m.end()
            depth = 1
            pos = start
            while pos < len(txt) and depth > 0:
                if txt[pos] == "{":
                    depth += 1
                elif txt[pos] == "}":
                    depth -= 1
                pos += 1
            body = txt[start : pos - 1]
            fns = re.findall(r"^\s*fn\s+([a-z0-9_]+)\b", body, re.M)
            trait_methods[tname] = {
                "file": f"compiler/rustc_codegen_ssa/src/traits/{f.name}",
                "method_count": len(fns),
            }

    ffi_txt = (root / "compiler/rustc_codegen_llvm/src/llvm/ffi.rs").read_text(encoding="utf-8")
    ffi_fns = re.findall(r"\bfn\s+([A-Za-z0-9_]+)", ffi_txt)
    llvm_rust_fns = [x for x in ffi_fns if x.startswith("LLVMRust")]
    llvm_c_fns = [x for x in ffi_fns if x.startswith("LLVM") and not x.startswith("LLVMRust")]

    out = {
        "rust_revision": git_rev(root),
        "compiler_top_level_crates": len(crates),
        "compiler_total_raw_lines": sum(c["raw_lines"] for c in crates.values()),
        "compiler_total_approx_sloc": sum(c["approx_sloc"] for c in crates.values()),
        "longest_crate_chain": max_chain,
        "top_depended_crates": sorted(dep_counts.items(), key=lambda x: -x[1])[:15],
        "query_count": len(query_names),
        "codegen_traits": trait_methods,
        "codegen_traits_total_methods": sum(v["method_count"] for v in trait_methods.values()),
        "llvm_ffi": {
            "llvm_c_fns": len(llvm_c_fns),
            "llvm_rust_wrapper_fns": len(llvm_rust_fns),
            "wrapper_cpp": count_lines(root / "compiler/rustc_llvm/llvm-wrapper", (".cpp", ".h")),
        },
        "ir_enums": {
            k: {
                "file": v["file"],
                "start_line": v["start_line"],
                "end_line": v.get("end_line"),
                "count": v["count"],
                "variants": v["variants"],
            }
            for k, v in ir_enums.items()
        },
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
