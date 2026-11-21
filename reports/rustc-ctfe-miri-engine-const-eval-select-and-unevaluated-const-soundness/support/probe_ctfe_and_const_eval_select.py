#!/usr/bin/env python3
"""Standalone empirical probe for rustc CTFE, Const::Unevaluated, promote_consts, MIR GVN,
const_eval_select, is_val_statically_known, UnsafeCell interning, and Miri runtime semantics.

Requires only Python 3.10+ standard library and a nightly `rustc` toolchain (plus `miri` in the
active toolchain sysroot for standalone `#![no_core]` Miri checks).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
from typing import Any


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def resolve_tool(explicit: str | None, name: str) -> str | None:
    if explicit:
        return explicit
    found = shutil.which(name)
    if found:
        return found
    cargo_candidate = Path.home() / ".cargo" / "bin" / name
    if cargo_candidate.is_file():
        return str(cargo_candidate)
    return None


def sanitize_text(text: str, replacements: list[tuple[str, str]]) -> str:
    out = text
    for raw, repl in replacements:
        if raw:
            out = out.replace(raw, repl)
    return out


def run_cmd(
    cmd: list[str],
    cwd: Path,
    env: dict[str, str] | None = None,
    timeout: int = 120,
) -> subprocess.CompletedProcess[str]:
    merged_env = os.environ.copy()
    if env:
        merged_env.update(env)
    return subprocess.run(
        cmd,
        cwd=str(cwd),
        env=merged_env,
        capture_output=True,
        text=True,
        timeout=timeout,
    )


def classify_const_eval_select_site(rel_file: str, snippet: str) -> str:
    if rel_file == "core/src/intrinsics/mod.rs" and (
        "($($val,)*), compiletime, runtime" in snippet
        or "$crate::intrinsics::const_eval_select!" in snippet
    ):
        return "macro_definition"
    if (
        rel_file.startswith("core/src/ub_checks.rs")
        or (
            rel_file in ("core/src/ptr/const_ptr.rs", "core/src/ptr/mut_ptr.rs")
            and "if const { true }" in snippet
        )
        or (
            rel_file == "core/src/ffi/c_str.rs"
            and "from_bytes_with_nul" not in snippet
            and "input was not nul-terminated" in snippet
        )
    ):
        return "class_b_ub_and_safety_guard"
    if rel_file == "core/src/intrinsics/mod.rs" and (
        "contract_check" in snippet
        or "failed requires check" in snippet
        or "failed ensures check" in snippet
        or "miri_promise_symbolic_alignment" in snippet
    ):
        return "class_c_contract_and_miri_hook"
    if (
        rel_file in ("core/src/panic.rs", "core/src/panicking.rs", "core/src/str/mod.rs")
        or (rel_file == "alloc/src/alloc.rs" and "ct_error" in snippet)
    ):
        return "class_d_diverging_panic_and_error"
    if rel_file == "alloc/src/alloc.rs":
        return "class_e_const_heap_allocator"
    if rel_file.startswith("stdarch/"):
        return "class_f_simd_test_harness"
    return "class_a_algorithmic_and_provenance_refinement"


def scan_sysroot_library(sysroot: Path) -> dict[str, Any]:
    lib_dir = sysroot / "lib" / "rustlib" / "src" / "rust" / "library"
    if not lib_dir.is_dir():
        return {"available": False, "reason": "rust-src library directory not installed"}

    ces_re = re.compile(r"\bconst_eval_select\s*!?\s*\(")
    ivsk_re = re.compile(r"\bis_val_statically_known\s*(?:::<[^>]*>)?\s*\(")

    ces_sites: list[dict[str, Any]] = []
    ivsk_sites: list[dict[str, Any]] = []
    scanned_files = 0

    for rs in sorted(lib_dir.rglob("*.rs")):
        rel = rs.relative_to(lib_dir).as_posix()
        if "/tests/" in f"/{rel}" or "/benches/" in f"/{rel}":
            continue
        scanned_files += 1
        lines = rs.read_text(encoding="utf-8", errors="replace").splitlines()
        for idx, line in enumerate(lines, 1):
            stripped = line.strip()
            if stripped.startswith("//"):
                continue
            if (
                "fn const_eval_select" not in stripped
                and "macro const_eval_select" not in stripped
                and "macro_rules! const_eval_select" not in stripped
                and not stripped.startswith("pub use ")
                and ces_re.search(line)
            ):
                crate = rel.split("/", 1)[0]
                ctx = " ".join(x.strip() for x in lines[idx - 1 : min(len(lines), idx + 12)])
                cls = classify_const_eval_select_site(rel, ctx)
                ces_sites.append(
                    {
                        "crate": crate,
                        "file": rel,
                        "line": idx,
                        "is_macro": "const_eval_select!(" in line,
                        "class": cls,
                        "snippet": ctx[:240],
                    }
                )
            if (
                "fn is_val_statically_known" not in stripped
                and not stripped.startswith("pub use ")
                and ivsk_re.search(line)
            ):
                crate = rel.split("/", 1)[0]
                ivsk_sites.append(
                    {
                        "crate": crate,
                        "file": rel,
                        "line": idx,
                        "line_text": stripped,
                    }
                )

    by_crate_ces: dict[str, int] = {}
    by_class_ces: dict[str, int] = {}
    for site in ces_sites:
        by_crate_ces[site["crate"]] = by_crate_ces.get(site["crate"], 0) + 1
        by_class_ces[site["class"]] = by_class_ces.get(site["class"], 0) + 1

    by_crate_ivsk: dict[str, int] = {}
    for site in ivsk_sites:
        by_crate_ivsk[site["crate"]] = by_crate_ivsk.get(site["crate"], 0) + 1

    return {
        "available": True,
        "scanned_non_test_rs_files": scanned_files,
        "const_eval_select": {
            "total_sites": len(ces_sites),
            "by_crate": dict(sorted(by_crate_ces.items())),
            "by_class": dict(sorted(by_class_ces.items())),
            "sites": ces_sites,
        },
        "is_val_statically_known": {
            "total_sites": len(ivsk_sites),
            "by_crate": dict(sorted(by_crate_ivsk.items())),
            "sites": ivsk_sites,
        },
    }


def parse_kv_stdout(stdout: str) -> dict[str, str]:
    result: dict[str, str] = {}
    for line in stdout.strip().splitlines():
        for m in re.finditer(r"([A-Z0-9_]+)=(Some\([^)]*\)|[^\s]+)", line):
            result[m.group(1)] = m.group(2)
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rustc", default=None, help="Path to nightly rustc")
    parser.add_argument(
        "--out", default=None, help="Output directory (defaults to support/probe_output)"
    )
    args = parser.parse_args()

    support_dir = Path(__file__).resolve().parent
    specimens_dir = support_dir / "specimens"
    out_dir = Path(args.out).resolve() if args.out else (support_dir / "probe_output")
    out_dir.mkdir(parents=True, exist_ok=True)

    rustc = resolve_tool(args.rustc, "rustc")
    if not rustc:
        print("error: rustc not found", file=sys.stderr)
        return 1

    vv = run_cmd([rustc, "-vV"], support_dir)
    if vv.returncode != 0:
        print(f"error: rustc -vV failed: {vv.stderr}", file=sys.stderr)
        return 1
    rustc_vv = vv.stdout.strip()

    sysroot_proc = run_cmd([rustc, "--print", "sysroot"], support_dir)
    sysroot = Path(sysroot_proc.stdout.strip())
    miri_bin = sysroot / "bin" / "miri"
    has_miri = miri_bin.is_file()

    checks: list[dict[str, Any]] = []

    def record(name: str, passed: bool, detail: Any) -> None:
        checks.append({"name": name, "passed": bool(passed), "detail": detail})

    mir_excerpts: list[str] = []
    llvm_excerpts: list[str] = []
    specimen_hashes = {p.name: sha256_file(p) for p in sorted(specimens_dir.glob("*.rs"))}

    with tempfile.TemporaryDirectory(prefix="ctfe_ces_probe_") as raw_tmp:
        tmp = Path(raw_tmp)
        replacements = [
            (str(tmp), "<tmp>"),
            (str(specimens_dir), "support/specimens"),
            (str(support_dir), "support"),
            (str(sysroot), "<sysroot>"),
            (str(Path.home()), "<home>"),
        ]

        def read_matching_mir(dump_dir: Path, *substrs: str) -> str:
            matches = sorted(
                p for p in dump_dir.glob("*.mir") if all(s in p.name for s in substrs)
            )
            if not matches:
                return ""
            return sanitize_text(
                matches[-1].read_text(encoding="utf-8", errors="replace"), replacements
            )

        # ------------------------------------------------------------------
        # Specimen 1: MIR const forms, promotion, generic Const::Unevaluated, const_eval_select
        # ------------------------------------------------------------------
        s1_src = specimens_dir / "mir_const_forms_and_promotion.rs"
        s1_dump_o0 = tmp / "s1_dump_o0"
        s1_dump_o3 = tmp / "s1_dump_o3"
        s1_dump_o0.mkdir()
        s1_dump_o3.mkdir()

        s1_bin_o0 = tmp / "s1_o0"
        r_s1_o0 = run_cmd(
            [
                rustc,
                "--edition=2021",
                "-C",
                "opt-level=0",
                "-C",
                "debuginfo=0",
                f"--remap-path-prefix={specimens_dir}=support/specimens",
                "--emit=llvm-ir,link",
                "-Zdump-mir=runtime-post-cleanup|runtime-optimized",
                f"-Zdump-mir-dir={s1_dump_o0}",
                "-o",
                str(s1_bin_o0),
                str(s1_src),
            ],
            tmp,
        )
        s1_bin_o3 = tmp / "s1_o3"
        r_s1_o3 = run_cmd(
            [
                rustc,
                "--edition=2021",
                "-C",
                "opt-level=3",
                "-C",
                "debuginfo=0",
                f"--remap-path-prefix={specimens_dir}=support/specimens",
                "--emit=llvm-ir,link",
                "-Zdump-mir=runtime-post-cleanup|runtime-optimized",
                f"-Zdump-mir-dir={s1_dump_o3}",
                "-o",
                str(s1_bin_o3),
                str(s1_src),
            ],
            tmp,
        )
        s1_run_o0 = run_cmd([str(s1_bin_o0)], tmp) if r_s1_o0.returncode == 0 else None
        s1_run_o3 = run_cmd([str(s1_bin_o3)], tmp) if r_s1_o3.returncode == 0 else None

        record(
            "s1::compile_and_run_o0_o3_parity",
            r_s1_o0.returncode == 0
            and r_s1_o3.returncode == 0
            and s1_run_o0 is not None
            and s1_run_o3 is not None
            and s1_run_o0.returncode == 0
            and s1_run_o3.returncode == 0
            and s1_run_o0.stdout.strip() == s1_run_o3.stdout.strip(),
            {
                "stdout_o0": s1_run_o0.stdout.strip() if s1_run_o0 else r_s1_o0.stderr[:240],
                "stdout_o3": s1_run_o3.stdout.strip() if s1_run_o3 else r_s1_o3.stderr[:240],
            },
        )

        sum_postcleanup = read_matching_mir(
            s1_dump_o0, "sum_dispatch", "runtime-post-cleanup.after.mir"
        )
        sum_opt_o0 = read_matching_mir(
            s1_dump_o0, "sum_dispatch", "runtime-optimized.after.mir"
        )

        # Dump CtfeLimit specifically to capture `mir_for_ctfe` output after `remap_mir_for_const_eval_select(Const)`
        s1_ctfe_dir = tmp / "s1_ctfe_only"
        s1_ctfe_dir.mkdir()
        run_cmd(
            [
                rustc,
                "--edition=2021",
                "--crate-type=lib",
                "-C",
                "opt-level=0",
                f"--remap-path-prefix={specimens_dir}=support/specimens",
                "--emit=metadata",
                "-Zdump-mir=CtfeLimit",
                f"-Zdump-mir-dir={s1_ctfe_dir}",
                str(s1_src),
            ],
            tmp,
        )
        sum_ctfe_limit = read_matching_mir(s1_ctfe_dir, "sum_dispatch", "CtfeLimit.after.mir")
        tri_ctfe_limit = read_matching_mir(
            s1_ctfe_dir, "compute_triangular", "CtfeLimit.after.mir"
        )

        record(
            "s1::postcleanup_preserves_const_eval_select_both_arms",
            "const_eval_select" in sum_postcleanup
            and "sum_bytes_ct" in sum_postcleanup
            and "sum_bytes_rt" in sum_postcleanup,
            "both sum_bytes_ct and sum_bytes_rt present in Runtime(PostCleanup)",
        )
        record(
            "s1::mir_for_ctfe_remaps_to_const_arm_with_ctfe_limit",
            "const_eval_select" not in sum_ctfe_limit
            and "sum_bytes_ct" in sum_ctfe_limit
            and "sum_bytes_rt" not in sum_ctfe_limit
            and "ConstEvalCounter" in tri_ctfe_limit,
            "mir_for_ctfe calls sum_bytes_ct directly and injects ConstEvalCounter in loops",
        )
        record(
            "s1::runtime_optimized_remaps_to_rt_arm_even_at_o0",
            "const_eval_select" not in sum_opt_o0
            and "sum_bytes_rt" in sum_opt_o0
            and "sum_bytes_ct" not in sum_opt_o0,
            "remap_mir_for_const_eval_select(NotConst) runs unconditionally before mir-opt passes",
        )

        prom_post = read_matching_mir(
            s1_dump_o0, "promoted_and_unpromoted_borrows", "runtime-post-cleanup.after.mir"
        )
        prom_frags = sorted(
            p.name
            for p in s1_dump_o0.glob(
                "*promoted_and_unpromoted_borrows*promoted*runtime-post-cleanup.after.mir"
            )
        )
        record(
            "s1::implicit_promotion_emits_two_promoted_bodies_and_skips_fallible_dead_div",
            "promoted_and_unpromoted_borrows::promoted[0]" in prom_post
            and "promoted_and_unpromoted_borrows::promoted[1]" in prom_post
            and "Div(const 1_u32, const 0_u32)" in prom_post,
            {
                "promoted_0_and_1_in_mir": True,
                "promoted_dump_files": prom_frags,
            },
        )

        gen_post_o0 = read_matching_mir(
            s1_dump_o0, "generic_unevaluated", "runtime-post-cleanup.after.mir"
        )
        gen_opt_o3 = read_matching_mir(
            s1_dump_o3, "generic_unevaluated", "runtime-optimized.after.mir"
        )
        record(
            "s1::polymorphic_unevaluated_const_persists_while_inline_const_folds_at_o3",
            "<T as Cap>::LIMIT" in gen_post_o0
            and "generic_unevaluated::<T, N>::{constant#1}" in gen_post_o0
            and "<T as Cap>::LIMIT" in gen_opt_o3
            and "const 10_usize" in gen_opt_o3,
            "T::LIMIT stays Const::Unevaluated in polymorphic MIR while monomorphic inline const { 10 } folds at -O3",
        )

        mir_excerpts.extend(
            [
                "=== sum_dispatch (Runtime(PostCleanup)) ===\n" + sum_postcleanup.strip(),
                "=== sum_dispatch (mir_for_ctfe after CtfeLimit) ===\n" + sum_ctfe_limit.strip(),
                "=== sum_dispatch (Runtime(Optimized) at -O0) ===\n" + sum_opt_o0.strip(),
                "=== generic_unevaluated (Runtime(PostCleanup)) ===\n" + gen_post_o0.strip(),
                "=== generic_unevaluated (Runtime(Optimized) at -O3) ===\n" + gen_opt_o3.strip(),
                "=== promoted_and_unpromoted_borrows (Runtime(PostCleanup)) ===\n" + prom_post.strip(),
            ]
        )

        # ------------------------------------------------------------------
        # Specimen 2: GVN vs CompileTimeMachine & is_val_statically_known (-O0 vs -O3)
        # ------------------------------------------------------------------
        s2_src = specimens_dir / "gvn_ctfe_boundary_and_statically_known.rs"
        s2_gvn_dir = tmp / "s2_gvn"
        s2_gvn_dir.mkdir()
        s2_bin_o0 = tmp / "s2_o0"
        s2_bin_o3 = tmp / "s2_o3"

        r_s2_o0 = run_cmd(
            [
                rustc,
                "--edition=2021",
                "-C",
                "opt-level=0",
                "-C",
                "debuginfo=0",
                f"--remap-path-prefix={specimens_dir}=support/specimens",
                "-o",
                str(s2_bin_o0),
                str(s2_src),
            ],
            tmp,
        )
        r_s2_o3 = run_cmd(
            [
                rustc,
                "--edition=2021",
                "-C",
                "opt-level=3",
                "-C",
                "debuginfo=0",
                f"--remap-path-prefix={specimens_dir}=support/specimens",
                "-Zdump-mir=GVN",
                f"-Zdump-mir-dir={s2_gvn_dir}",
                "-o",
                str(s2_bin_o3),
                str(s2_src),
            ],
            tmp,
        )
        s2_run_o0 = run_cmd([str(s2_bin_o0)], tmp) if r_s2_o0.returncode == 0 else None
        s2_run_o3 = run_cmd([str(s2_bin_o3)], tmp) if r_s2_o3.returncode == 0 else None

        kv_s2_o0 = parse_kv_stdout(s2_run_o0.stdout if s2_run_o0 else "")
        kv_s2_o3 = parse_kv_stdout(s2_run_o3.stdout if s2_run_o3 else "")

        record(
            "s2::guaranteed_eq_static_vs_const_memory_in_ctfe",
            kv_s2_o0.get("STATIC_SAME") == "Some(true)"
            and kv_s2_o0.get("STATIC_DIFF") == "Some(false)"
            and kv_s2_o0.get("CONST_MEM_EQ") == "None",
            {
                "STATIC_SAME": kv_s2_o0.get("STATIC_SAME"),
                "STATIC_DIFF": kv_s2_o0.get("STATIC_DIFF"),
                "CONST_MEM_EQ": kv_s2_o0.get("CONST_MEM_EQ"),
            },
        )
        record(
            "s2::is_val_statically_known_flips_0_to_1_between_o0_and_o3_after_inlining",
            kv_s2_o0.get("CTFE_IVSK") == "false"
            and kv_s2_o0.get("KNOWN_CONST") == "0"
            and kv_s2_o3.get("KNOWN_CONST") == "1"
            and kv_s2_o0.get("KNOWN_OPAQUE") == "0"
            and kv_s2_o3.get("KNOWN_OPAQUE") == "0"
            and kv_s2_o3.get("NON_IMM") == "false",
            {
                "ctfe": kv_s2_o0.get("CTFE_IVSK"),
                "o0_const_arg": kv_s2_o0.get("KNOWN_CONST"),
                "o3_const_arg": kv_s2_o3.get("KNOWN_CONST"),
                "o0_opaque_arg": kv_s2_o0.get("KNOWN_OPAQUE"),
                "o3_opaque_arg": kv_s2_o3.get("KNOWN_OPAQUE"),
                "o3_non_immediate_array": kv_s2_o3.get("NON_IMM"),
            },
        )

        gvn_after = read_matching_mir(s2_gvn_dir, "gvn_scalar_vs_ptr_probe", "GVN.after.mir")
        record(
            "s2::mir_gvn_folds_scalar_unevaluated_const_but_preserves_ptr_expose_provenance",
            "const 51_u64" in gvn_after
            and "PointerExposeProvenance" in gvn_after
            and "PointerWithExposedProvenance" in gvn_after,
            "GVN folds `const { 6 * 7 } + 9` -> `const 51_u64` while keeping PointerExposeProvenance symbolic",
        )

        s2_ll_o0_path = tmp / "s2_o0.ll"
        s2_ll_o3_path = tmp / "s2_o3.ll"
        run_cmd(
            [
                rustc,
                "--edition=2021",
                "-C",
                "opt-level=0",
                "-C",
                "debuginfo=0",
                "--emit=llvm-ir",
                "-o",
                str(s2_ll_o0_path),
                str(s2_src),
            ],
            tmp,
        )
        run_cmd(
            [
                rustc,
                "--edition=2021",
                "-C",
                "opt-level=3",
                "-C",
                "debuginfo=0",
                "--emit=llvm-ir",
                "-o",
                str(s2_ll_o3_path),
                str(s2_src),
            ],
            tmp,
        )
        s2_ll_o0 = sanitize_text(s2_ll_o0_path.read_text(), replacements)
        s2_ll_o3 = sanitize_text(s2_ll_o3_path.read_text(), replacements)

        record(
            "s2::llvm_ir_emits_llvm_is_constant_at_o0_and_folds_away_at_o3",
            "@llvm.is.constant.i64" in s2_ll_o0 and "call i1 @llvm.is.constant" not in s2_ll_o3,
            {
                "o0_has_llvm_is_constant": "@llvm.is.constant.i64" in s2_ll_o0,
                "o3_calls_llvm_is_constant": "call i1 @llvm.is.constant" in s2_ll_o3,
            },
        )
        mir_excerpts.append("=== gvn_scalar_vs_ptr_probe (after GVN at -O3) ===\n" + gvn_after.strip())

        ivsk_ll_lines = [
            ln
            for ln in s2_ll_o0.splitlines()
            if "llvm.is.constant" in ln
            or "ivsk_observable_oracle" in ln
            or "ivsk_non_immediate_array" in ln
        ]
        llvm_excerpts.append(
            "=== Specimen 2 (-O0 LLVM IR lines mentioning llvm.is.constant / ivsk_*) ===\n"
            + "\n".join(ivsk_ll_lines[:25])
        )

        # ------------------------------------------------------------------
        # Specimen 3: UnsafeCell interning vs .rodata vs writable .data
        # ------------------------------------------------------------------
        s3_src = specimens_dir / "unsafecell_interning_and_rodata.rs"
        s3_bin_o3 = tmp / "s3_o3"
        s3_ll_path = tmp / "s3_o3.ll"
        s3_mir_dir = tmp / "s3_mir"
        s3_mir_dir.mkdir()
        r_s3 = run_cmd(
            [
                rustc,
                "--edition=2021",
                "-C",
                "opt-level=3",
                "-C",
                "debuginfo=0",
                f"--remap-path-prefix={specimens_dir}=support/specimens",
                "--emit=llvm-ir",
                "-o",
                str(s3_ll_path),
                str(s3_src),
            ],
            tmp,
        )
        r_s3_bin = run_cmd(
            [
                rustc,
                "--edition=2021",
                "-C",
                "opt-level=3",
                "-C",
                "debuginfo=0",
                "-Zdump-mir=runtime-post-cleanup",
                f"-Zdump-mir-dir={s3_mir_dir}",
                "-o",
                str(s3_bin_o3),
                str(s3_src),
            ],
            tmp,
        )
        s3_run = (
            run_cmd([str(s3_bin_o3)], tmp)
            if r_s3_bin.returncode == 0
            else subprocess.CompletedProcess(args=[], returncode=1, stdout="", stderr=r_s3_bin.stderr)
        )
        s3_ll = sanitize_text(s3_ll_path.read_text(), replacements) if r_s3.returncode == 0 else ""

        frozen_const_decl = [
            ln
            for ln in s3_ll.splitlines()
            if "FROZEN_STATIC" in ln and ("constant" in ln or "global" in ln)
        ]
        interior_mut_decl = [
            ln
            for ln in s3_ll.splitlines()
            if "INTERIOR_MUT_STATIC" in ln and ("constant" in ln or "global" in ln)
        ]
        s3_promoteds = list(s3_mir_dir.glob("*exercise_const_cells.promoted*.mir"))

        record(
            "s3::frozen_static_is_llvm_constant_while_unsafecell_static_is_mutable_global",
            any(" constant " in ln for ln in frozen_const_decl)
            and any(" global " in ln and " constant " not in ln for ln in interior_mut_decl),
            {
                "frozen_decl": frozen_const_decl[:2],
                "interior_mut_decl": interior_mut_decl[:2],
            },
        )
        record(
            "s3::const_unsafecell_not_promoted_and_fresh_per_use_plus_zst_cell_ref",
            r_s3_bin.returncode == 0
            and s3_run.returncode == 0
            and len(s3_promoteds) == 0,
            {
                "stdout": s3_run.stdout.strip(),
                "exercise_const_cells_promoted_count": len(s3_promoteds),
            },
        )
        llvm_excerpts.append(
            "=== Specimen 3 (LLVM global mutability: Freeze `constant` vs !Freeze `global`) ===\n"
            + "\n".join(frozen_const_decl[:2] + interior_mut_decl[:2])
        )

        # ------------------------------------------------------------------
        # Specimen 4: Divergent const_eval_select (CE1) and non-invariant ivsk (CE3)
        # ------------------------------------------------------------------
        s4_src = specimens_dir / "divergent_const_eval_select_and_ivsk_hazards.rs"
        s4_bin_o0 = tmp / "s4_o0"
        s4_bin_o3 = tmp / "s4_o3"
        r_s4_o0 = run_cmd(
            [rustc, "--edition=2021", "-C", "opt-level=0", "-o", str(s4_bin_o0), str(s4_src)], tmp
        )
        r_s4_o3 = run_cmd(
            [rustc, "--edition=2021", "-C", "opt-level=3", "-o", str(s4_bin_o3), str(s4_src)], tmp
        )
        s4_run_o0 = (
            run_cmd([str(s4_bin_o0)], tmp)
            if r_s4_o0.returncode == 0
            else subprocess.CompletedProcess(args=[], returncode=1, stdout="", stderr=r_s4_o0.stderr)
        )
        s4_run_o3 = (
            run_cmd([str(s4_bin_o3)], tmp)
            if r_s4_o3.returncode == 0
            else subprocess.CompletedProcess(args=[], returncode=1, stdout="", stderr=r_s4_o3.stderr)
        )

        kv_s4_o0 = parse_kv_stdout(s4_run_o0.stdout)
        kv_s4_o3 = parse_kv_stdout(s4_run_o3.stdout)
        record(
            "s4::unsound_const_eval_select_diverges_between_ctfe_and_runtime_without_error",
            s4_run_o0.returncode == 0
            and kv_s4_o0.get("CE1_CT") == "0"
            and kv_s4_o0.get("CE1_RT") == "1",
            {
                "CE1_CT": kv_s4_o0.get("CE1_CT"),
                "CE1_RT": kv_s4_o0.get("CE1_RT"),
            },
        )
        record(
            "s4::non_invariant_ivsk_violates_o0_vs_o3_refinement",
            kv_s4_o0.get("CE3_IVSK") == "200" and kv_s4_o3.get("CE3_IVSK") == "100",
            {"O0_CE3_IVSK": kv_s4_o0.get("CE3_IVSK"), "O3_CE3_IVSK": kv_s4_o3.get("CE3_IVSK")},
        )

        # ------------------------------------------------------------------
        # Specimen 5: Negative compile-fail & post-monomorphization error (PME) checks
        # ------------------------------------------------------------------
        s5_src = specimens_dir / "negative_ctfe_and_pme_cases.rs"

        def check_cfg_compile(cfg_name: str, opt_level: str = "0") -> dict[str, Any]:
            out_bin = tmp / f"neg_{cfg_name}_o{opt_level}"
            r = run_cmd(
                [
                    rustc,
                    "--edition=2021",
                    "--cfg",
                    cfg_name,
                    "-C",
                    f"opt-level={opt_level}",
                    f"--remap-path-prefix={specimens_dir}=support/specimens",
                    "-o",
                    str(out_bin),
                    str(s5_src),
                ],
                tmp,
            )
            first_err = next(
                (
                    ln
                    for ln in sanitize_text(r.stderr, replacements).splitlines()
                    if ln.startswith("error")
                ),
                "",
            )
            return {
                "rc": r.returncode,
                "first_error": first_err,
                "stderr_excerpt": "\n".join(
                    sanitize_text(r.stderr, replacements).splitlines()[:14]
                ),
            }

        c_ptr_int = check_cfg_compile("case_ptr_to_int")
        c_ptr_read = check_cfg_compile("case_ptr_read_as_int")
        c_raw_cmp = check_cfg_compile("case_raw_ptr_cmp")
        c_cell_ref = check_cfg_compile("case_inner_unsafecell")
        c_pme_ok = check_cfg_compile("case_pme_ok_u32", "3")
        c_pme_fail_o0 = check_cfg_compile("case_pme_dead_branch", "0")
        c_pme_fail_o3 = check_cfg_compile("case_pme_dead_branch", "3")
        c_inline_fail_o3 = check_cfg_compile("case_inline_const_dead_branch", "3")

        record(
            "s5::const_check_and_ctfe_reject_ptr_to_int_cast_and_ptr_byte_load",
            c_ptr_int["rc"] != 0
            and "pointers cannot be cast to integers during const eval" in c_ptr_int["stderr_excerpt"]
            and c_ptr_read["rc"] != 0
            and "unable to turn pointer into integer" in c_ptr_read["stderr_excerpt"],
            {
                "cast_err": c_ptr_int["first_error"],
                "read_ptr_as_int_err": c_ptr_read["first_error"],
            },
        )
        record(
            "s5::const_check_rejects_raw_pointer_relational_comparison",
            c_raw_cmp["rc"] != 0
            and "pointers cannot be reliably compared during const eval"
            in c_raw_cmp["stderr_excerpt"],
            c_raw_cmp["first_error"],
        )
        record(
            "s5::ctfe_validation_rejects_inner_unsafecell_behind_const_ref",
            c_cell_ref["rc"] != 0
            and "UnsafeCell` in read-only memory" in c_cell_ref["stderr_excerpt"],
            c_cell_ref["first_error"],
        )
        record(
            "s5::uninstantiated_failing_assoc_const_succeeds_until_monomorphized_even_in_dead_branch",
            c_pme_ok["rc"] == 0
            and c_pme_fail_o0["rc"] != 0
            and c_pme_fail_o3["rc"] != 0
            and "E0080" in c_pme_fail_o3["first_error"]
            and c_inline_fail_o3["rc"] != 0
            and "E0080" in c_inline_fail_o3["first_error"],
            {
                "u32_only_rc": c_pme_ok["rc"],
                "u64_in_if_false_o0": c_pme_fail_o0["first_error"],
                "u64_in_if_false_o3": c_pme_fail_o3["first_error"],
                "inline_const_in_if_false_o3": c_inline_fail_o3["first_error"],
            },
        )

        # ------------------------------------------------------------------
        # Specimen 6: Standalone `#![no_core]` Miri runtime vs CTFE verification
        # ------------------------------------------------------------------
        s6_src = specimens_dir / "miri_standalone_runtime_vs_ctfe.rs"
        if has_miri:
            r_miri_seed0 = run_cmd(
                [
                    str(miri_bin),
                    "--edition=2021",
                    "-Zmiri-seed=0",
                    f"--remap-path-prefix={specimens_dir}=support/specimens",
                    str(s6_src),
                ],
                tmp,
            )
            r_miri_seed1 = run_cmd(
                [
                    str(miri_bin),
                    "--edition=2021",
                    "-Zmiri-seed=1",
                    f"--remap-path-prefix={specimens_dir}=support/specimens",
                    str(s6_src),
                ],
                tmp,
            )
            r_miri_strict = run_cmd(
                [
                    str(miri_bin),
                    "--edition=2021",
                    "-Zmiri-strict-provenance",
                    f"--remap-path-prefix={specimens_dir}=support/specimens",
                    str(s6_src),
                ],
                tmp,
            )
            r_miri_rodata_ub = run_cmd(
                [
                    str(miri_bin),
                    "--edition=2021",
                    "--cfg",
                    "case_rodata_write_ub",
                    f"--remap-path-prefix={specimens_dir}=support/specimens",
                    str(s6_src),
                ],
                tmp,
            )
            strict_err = sanitize_text(r_miri_strict.stderr, replacements)
            rodata_err = sanitize_text(r_miri_rodata_ub.stderr, replacements)
            record(
                "s6::miri_permissive_executes_ptr_roundtrip_ces_divergence_and_nondet_ivsk_across_seeds",
                r_miri_seed0.returncode == 11 and r_miri_seed1.returncode == 10,
                {
                    "seed0_exit_code_ivsk_true": r_miri_seed0.returncode,
                    "seed1_exit_code_ivsk_false": r_miri_seed1.returncode,
                    "warning_present": "integer-to-pointer cast" in r_miri_seed0.stderr,
                },
            )
            record(
                "s6::miri_strict_provenance_rejects_int_to_ptr_and_catches_rodata_unsafecell_write_ub",
                r_miri_strict.returncode != 0
                and "unsupported operation: integer-to-pointer casts" in strict_err
                and r_miri_rodata_ub.returncode != 0
                and "Undefined Behavior: writing to" in rodata_err
                and "which is read-only" in rodata_err,
                {
                    "strict_provenance_first_err": next(
                        (ln for ln in strict_err.splitlines() if ln.startswith("error")), ""
                    ),
                    "rodata_write_first_err": next(
                        (ln for ln in rodata_err.splitlines() if ln.startswith("error")), ""
                    ),
                },
            )

    # ----------------------------------------------------------------------
    # Programmatic Sysroot Census
    # ----------------------------------------------------------------------
    census = scan_sysroot_library(sysroot)
    if census.get("available"):
        record(
            "census::sysroot_const_eval_select_32_sites_and_ivsk_sites_classified",
            census["const_eval_select"]["total_sites"] == 32
            and census["const_eval_select"]["by_crate"] == {"alloc": 5, "core": 26, "stdarch": 1}
            and census["const_eval_select"]["by_class"].get("class_b_ub_and_safety_guard") == 11
            and census["is_val_statically_known"]["total_sites"] >= 7,
            {
                "const_eval_select_total": census["const_eval_select"]["total_sites"],
                "const_eval_select_by_crate": census["const_eval_select"]["by_crate"],
                "const_eval_select_by_class": census["const_eval_select"]["by_class"],
                "is_val_statically_known_total": census["is_val_statically_known"]["total_sites"],
            },
        )

    passed_count = sum(1 for c in checks if c["passed"])
    total_count = len(checks)
    all_passed = passed_count == total_count

    results_payload = {
        "rustc_vv": rustc_vv,
        "miri_available": has_miri,
        "specimen_sha256": specimen_hashes,
        "passed_checks": passed_count,
        "total_checks": total_count,
        "all_passed": all_passed,
        "checks": checks,
    }

    (out_dir / "probe_results.json").write_text(
        json.dumps(results_payload, indent=2, sort_keys=False) + "\n", encoding="utf-8"
    )
    (out_dir / "sysroot_const_eval_census.json").write_text(
        json.dumps(census, indent=2, sort_keys=False) + "\n", encoding="utf-8"
    )
    (out_dir / "mir_excerpts.txt").write_text("\n\n".join(mir_excerpts) + "\n", encoding="utf-8")
    (out_dir / "llvm_ir_excerpts.txt").write_text(
        "\n\n".join(llvm_excerpts) + "\n", encoding="utf-8"
    )

    md_lines = [
        "# Live `rustc` & Miri CTFE / `const_eval_select` / GVN Probe Summary",
        "",
        f"- **Compiler:** `{rustc_vv.splitlines()[0]}`",
        f"- **Checks passed:** `{passed_count} / {total_count}`",
        f"- **Miri available:** `{has_miri}`",
        "",
        "| # | Check | Result |",
        "|---:|:---|:---:|",
    ]
    for idx, c in enumerate(checks, 1):
        md_lines.append(f"| {idx} | `{c['name']}` | {'PASS' if c['passed'] else 'FAIL'} |")
    (out_dir / "probe_summary.md").write_text("\n".join(md_lines) + "\n", encoding="utf-8")

    print(f"Probe completed: {passed_count}/{total_count} passed")
    for c in checks:
        if not c["passed"]:
            print(f"  FAIL: {c['name']} -> {c['detail']}", file=sys.stderr)
    return 0 if all_passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
