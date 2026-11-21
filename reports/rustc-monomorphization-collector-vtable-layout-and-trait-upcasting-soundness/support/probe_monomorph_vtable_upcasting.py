#!/usr/bin/env python3
"""Standalone rustc probe for monomorphization collection, vtable layout,
trait upcasting, InstanceKind shims, CGU linkage, and recursion/type-length limits.

Uses Python 3.10+ standard library only. Compiles and executes the preserved
Rust specimens under `support/specimens/`, captures `-Z print-mono-items=yes`,
`Runtime(PostCleanup)` MIR, LLVM IR (`--emit=llvm-ir`), and native outputs,
validates all structural and runtime assertions, and writes structured results.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run_cmd(cmd: list[str], cwd: Path | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=str(cwd) if cwd else None,
        capture_output=True,
        text=True,
        check=False,
    )


def parse_kv(stdout: str) -> dict[str, str]:
    out: dict[str, str] = {}
    for line in stdout.splitlines():
        if "=" in line:
            k, v = line.split("=", 1)
            out[k.strip()] = v.strip()
    return out


def parse_mono_items(stdout: str) -> list[dict[str, Any]]:
    """Parse lines emitted by `rustc -Z print-mono-items=yes`."""
    items: list[dict[str, Any]] = []
    for line in stdout.splitlines():
        if not line.startswith("MONO_ITEM "):
            continue
        rest = line[len("MONO_ITEM "):]
        if " @@ " not in rest:
            continue
        item_desc, cgu_part = rest.rsplit(" @@ ", 1)
        placements: list[dict[str, str]] = []
        for tok in cgu_part.strip().split():
            m = re.match(r"^([^\[]+)\[([^\]]+)\]$", tok)
            if m:
                placements.append({"cgu": m.group(1), "linkage": m.group(2)})
        items.append({"item": item_desc.strip(), "placements": placements})
    return items


def extract_llvm_fn(ir: str, symbol: str) -> str | None:
    m = re.search(rf"define [^\n]*@{re.escape(symbol)}\([^\n]*\n.*?\n\}}", ir, re.S)
    return m.group(0) if m else None


def find_line_of(path: Path, needle: str) -> int:
    for idx, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if needle in line:
            return idx
    raise ValueError(f"needle {needle!r} not found in {path}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--rustc",
        default="rustc",
        help="Path to rustc executable (default: rustc on PATH)",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=None,
        help="Output directory for probe_results.json and excerpts (default: support/probe_output)",
    )
    args = parser.parse_args()

    script_dir = Path(__file__).resolve().parent
    spec_dir = script_dir / "specimens"
    out_dir = args.out.resolve() if args.out else (script_dir / "probe_output")
    out_dir.mkdir(parents=True, exist_ok=True)

    rustc_ver = run_cmd([args.rustc, "-Vv"])
    if rustc_ver.returncode != 0:
        print(f"ERROR: failed to run {args.rustc} -Vv: {rustc_ver.stderr}", file=sys.stderr)
        return 1

    rustc_meta: dict[str, str] = {}
    ver_lines = rustc_ver.stdout.strip().splitlines()
    rustc_meta["header"] = ver_lines[0] if ver_lines else ""
    for line in ver_lines[1:]:
        if ":" in line:
            k, v = line.split(":", 1)
            rustc_meta[k.strip()] = v.strip()

    specimens = [
        "vtable_diamond_upcast.rs",
        "shims_and_mono_collection.rs",
        "multi_cgu_linkage.rs",
        "sep_dep.rs",
        "sep_app.rs",
        "poly_recursion_limit.rs",
        "type_length_limit.rs",
    ]
    specimen_hashes = {name: sha256_file(spec_dir / name) for name in specimens}

    checks: dict[str, dict[str, Any]] = {}

    def record_check(name: str, passed: bool, detail: Any = None) -> None:
        checks[name] = {"passed": bool(passed), "detail": detail}

    llvm_excerpts: list[str] = []
    mir_excerpts: list[str] = []
    mono_summary_lines: list[str] = []
    results: dict[str, Any] = {
        "rustc": rustc_meta,
        "specimen_sha256": specimen_hashes,
        "specimens": {},
        "checks": checks,
    }

    with tempfile.TemporaryDirectory(prefix="rustc_mono_vtable_probe_") as tmp_str:
        tmp = Path(tmp_str)

        remap_arg = f"--remap-path-prefix={spec_dir}=specimens"

        # ------------------------------------------------------------------
        # 0. Check CLI behavior of `-Z print-mono-items=lazy`
        # ------------------------------------------------------------------
        cli_test = run_cmd(
            [
                args.rustc,
                "--edition=2021",
                remap_arg,
                "-Z",
                "print-mono-items=lazy",
                "--crate-type=lib",
                "-o",
                str(tmp / "cli_reject.rlib"),
                str(spec_dir / "sep_dep.rs"),
            ]
        )
        cli_rejected_lazy = (
            cli_test.returncode != 0
            and "incorrect value `lazy` for unstable option `print-mono-items`" in cli_test.stderr
        )
        record_check(
            "cli::print_mono_items_requires_bool",
            cli_rejected_lazy,
            cli_test.stderr.strip(),
        )

        # ------------------------------------------------------------------
        # 1. Vtable layout, diamond upcasting, empty marker, Vacant, DropGlue
        # ------------------------------------------------------------------
        v_src = spec_dir / "vtable_diamond_upcast.rs"
        v_ll = tmp / "vtable_diamond_upcast.ll"
        v_bin = tmp / "vtable_diamond_upcast_bin"
        v_mir_dir = tmp / "mir_vtable"
        v_mir_dir.mkdir()

        c_v_ll = run_cmd(
            [
                args.rustc,
                "--edition=2021",
                remap_arg,
                "-C",
                "opt-level=0",
                "-C",
                "debuginfo=0",
                "--emit=llvm-ir",
                "-Z",
                "dump-mir=upcast_d_to_a|upcast_d_to_b|upcast_d_to_base|upcast_empty_to_sec|upcast_erase_principal|drop_box_super_b",
                "-Z",
                f"dump-mir-dir={v_mir_dir}",
                "-o",
                str(v_ll),
                str(v_src),
            ]
        )
        record_check("vtable::compile_llvm_ir", c_v_ll.returncode == 0, c_v_ll.stderr.strip())

        c_v_bin = run_cmd(
            [
                args.rustc,
                "--edition=2021",
                "-C",
                "opt-level=0",
                "-C",
                "debuginfo=0",
                "-o",
                str(v_bin),
                str(v_src),
            ]
        )
        record_check("vtable::compile_bin", c_v_bin.returncode == 0, c_v_bin.stderr.strip())

        v_run = run_cmd([str(v_bin)])
        v_kv = parse_kv(v_run.stdout)
        record_check("vtable::native_exit_zero", v_run.returncode == 0, v_run.stderr.strip())
        record_check(
            "vtable::single_chain_prefix_reuse",
            v_kv.get("single_same_mid") == "true"
            and v_kv.get("single_same_base") == "true"
            and v_kv.get("single_dispatch_ok") == "true",
            {k: v_kv.get(k) for k in ("single_same_mid", "single_same_base", "single_dispatch_ok")},
        )
        record_check(
            "vtable::diamond_prefix_vs_secondary_vptr",
            v_kv.get("diamond_a_reuses_vptr") == "true"
            and v_kv.get("diamond_base_reuses_vptr") == "true"
            and v_kv.get("diamond_b_uses_secondary_vptr") == "true"
            and v_kv.get("diamond_b_to_base_reuses_vptr") == "true"
            and v_kv.get("diamond_copy_dispatch_ok") == "true",
            {
                k: v_kv.get(k)
                for k in (
                    "diamond_a_reuses_vptr",
                    "diamond_base_reuses_vptr",
                    "diamond_b_uses_secondary_vptr",
                    "diamond_b_to_base_reuses_vptr",
                    "diamond_copy_dispatch_ok",
                )
            },
        )
        record_check(
            "vtable::empty_marker_prefix_reuse",
            v_kv.get("empty_marker_reuses_vptr") == "true"
            and v_kv.get("empty_marker_dispatch_ok") == "true",
            {k: v_kv.get(k) for k in ("empty_marker_reuses_vptr", "empty_marker_dispatch_ok")},
        )
        record_check(
            "vtable::auto_trait_erase_prefix_reuse",
            v_kv.get("auto_erase_reuses_vptr") == "true",
            v_kv.get("auto_erase_reuses_vptr"),
        )
        record_check(
            "vtable::vacant_always_dispatch",
            v_kv.get("vacant_always") == "107",
            v_kv.get("vacant_always"),
        )
        record_check(
            "vtable::drop_dispatch_through_upcasted_boxes",
            v_kv.get("box_copy_b_val") == "203"
            and v_kv.get("drop_leaf_dispatch_ok") == "true"
            and v_kv.get("drop_after_concrete") == "3009"
            and v_kv.get("box_dl_b_val") == "35"
            and v_kv.get("drop_after_upcast_b") == "8010"
            and v_kv.get("drop_after_upcast_send") == "15012",
            {
                k: v_kv.get(k)
                for k in (
                    "box_copy_b_val",
                    "drop_leaf_dispatch_ok",
                    "drop_after_concrete",
                    "box_dl_b_val",
                    "drop_after_upcast_b",
                    "drop_after_upcast_send",
                )
            },
        )

        # Parse LLVM IR globals and functions
        ir_text = v_ll.read_text(encoding="utf-8") if v_ll.exists() else ""
        vtable_globals = re.findall(r"^@vtable\.\d+ = .*$", ir_text, re.M)
        alloc_globals = {
            m.group(1): m.group(0)
            for m in re.finditer(r"^(@alloc_[0-9a-f]+) = .*$", ir_text, re.M)
        }

        copy_diamond_vt = next(
            (g for g in vtable_globals if "CopyLeaf" in g and "Diamond" in g), None
        )
        drop_diamond_vt = next(
            (g for g in vtable_globals if "DropLeaf" in g and "Diamond" in g), None
        )
        empty_marker_vt = next(
            (g for g in vtable_globals if "SubAfterEmpty" in g), None
        )
        vacant_vt = next(
            (g for g in vtable_globals if "CondVacant" in g), None
        )

        def find_embedded_alloc(vt_line: str | None) -> tuple[str | None, str | None]:
            if not vt_line:
                return None, None
            m = re.search(r"ptr (@alloc_[0-9a-f]+)", vt_line)
            if not m:
                return None, None
            sym = m.group(1)
            return sym, alloc_globals.get(sym)

        copy_super_b_sym, copy_super_b_vt = find_embedded_alloc(copy_diamond_vt)
        drop_super_b_sym, drop_super_b_vt = find_embedded_alloc(drop_diamond_vt)

        record_check(
            "llvm_ir::copy_diamond_vtable_null_drop_and_trait_vptr",
            copy_diamond_vt is not None
            and 'c"\\00\\00\\00\\00\\00\\00\\00\\00\\08\\00\\00\\00\\00\\00\\00\\00\\08\\00\\00\\00\\00\\00\\00\\00"' in copy_diamond_vt
            and copy_super_b_vt is not None
            and "Base" in copy_super_b_vt
            and "SuperB" in copy_super_b_vt
            and "SuperA" not in copy_super_b_vt,
            {"primary": copy_diamond_vt, "secondary_sym": copy_super_b_sym, "secondary": copy_super_b_vt},
        )
        record_check(
            "llvm_ir::drop_diamond_vtable_nonnull_drop_and_trait_vptr",
            drop_diamond_vt is not None
            and "drop_glue" in drop_diamond_vt
            and 'c"\\10\\00\\00\\00\\00\\00\\00\\00\\08\\00\\00\\00\\00\\00\\00\\00"' in drop_diamond_vt
            and drop_super_b_vt is not None
            and "drop_glue" in drop_super_b_vt
            and "Base" in drop_super_b_vt
            and "SuperB" in drop_super_b_vt,
            {"primary": drop_diamond_vt, "secondary_sym": drop_super_b_sym, "secondary": drop_super_b_vt},
        )
        record_check(
            "llvm_ir::empty_marker_has_no_trait_vptr",
            empty_marker_vt is not None and "@alloc_" not in empty_marker_vt,
            empty_marker_vt,
        )
        record_check(
            "llvm_ir::vacant_slot_is_undef",
            vacant_vt is not None and "[8 x i8] undef" in vacant_vt,
            vacant_vt,
        )

        fn_irs: dict[str, str | None] = {}
        for fn_name in [
            "upcast_single_mid",
            "upcast_single_base",
            "upcast_d_to_a",
            "upcast_d_to_b",
            "upcast_d_to_base",
            "upcast_b_to_base",
            "upcast_empty_to_sec",
            "upcast_erase_principal",
            "drop_box_super_b",
        ]:
            fn_irs[fn_name] = extract_llvm_fn(ir_text, fn_name)

        for zero_cost_fn in [
            "upcast_single_mid",
            "upcast_single_base",
            "upcast_d_to_a",
            "upcast_d_to_base",
            "upcast_b_to_base",
            "upcast_empty_to_sec",
            "upcast_erase_principal",
        ]:
            body = fn_irs[zero_cost_fn] or ""
            record_check(
                f"llvm_ir::zero_cost_{zero_cost_fn}",
                bool(body) and "load " not in body and "getelementptr" not in body,
                body,
            )

        upcast_b_ir = fn_irs["upcast_d_to_b"] or ""
        record_check(
            "llvm_ir::upcast_d_to_b_loads_offset_48_invariant_nonnull",
            "getelementptr inbounds i8, ptr %d.1, i64 48" in upcast_b_ir
            and "!invariant.load" in upcast_b_ir
            and "!nonnull" in upcast_b_ir,
            upcast_b_ir,
        )

        # Check null-checked slot[0] drop_in_place on dyn SuperB in LLVM IR
        drop_dyn_super_b_match = re.search(
            r"define [^\n]*drop_glue[^\n]*SuperB[^\n]*\n.*?\n\}",
            ir_text,
            re.S,
        )
        drop_dyn_super_b_ir = drop_dyn_super_b_match.group(0) if drop_dyn_super_b_match else ""
        record_check(
            "llvm_ir::dyn_drop_glue_null_checks_slot_0",
            "icmp ne ptr" in drop_dyn_super_b_ir and ", null" in drop_dyn_super_b_ir,
            drop_dyn_super_b_ir,
        )

        llvm_excerpts.append("=== SPECIMEN 1: VTABLE GLOBALS & EMBEDDED SUPERTRAIT VTABLES ===")
        for label, line in [
            ("CopyLeaf as Diamond", copy_diamond_vt),
            (f"CopyLeaf as SuperB ({copy_super_b_sym})", copy_super_b_vt),
            ("DropLeaf as Diamond", drop_diamond_vt),
            (f"DropLeaf as SuperB ({drop_super_b_sym})", drop_super_b_vt),
            ("CopyLeaf as SubAfterEmpty", empty_marker_vt),
            ("CopyLeaf as CondVacant<String>", vacant_vt),
        ]:
            llvm_excerpts.append(f"; {label}\n{line}")
        llvm_excerpts.append("\n=== SPECIMEN 1: UPCAST FUNCTIONS & DYN DROP GLUE ===")
        for fn_name in [
            "upcast_d_to_a",
            "upcast_d_to_b",
            "upcast_d_to_base",
            "upcast_empty_to_sec",
            "upcast_erase_principal",
        ]:
            llvm_excerpts.append(f"\n; {fn_name}\n{fn_irs[fn_name]}")
        llvm_excerpts.append(f"\n; drop_in_place::<dyn SuperB>\n{drop_dyn_super_b_ir}")

        # Capture Runtime(PostCleanup) MIR excerpts
        mir_files = sorted(v_mir_dir.glob("*runtime-post-cleanup*.mir"))
        if not mir_files:
            mir_files = sorted(v_mir_dir.glob("*PostCleanup*.mir"))
        if not mir_files:
            mir_files = sorted(v_mir_dir.glob("*after.mir"))
        post_cleanup_names = [f.name for f in mir_files]
        mir_excerpts.append("=== SPECIMEN 1: Runtime(PostCleanup) MIR EXCERPTS ===")
        for mf in mir_files:
            if any(
                k in mf.name
                for k in (
                    "upcast_d_to_a",
                    "upcast_d_to_b",
                    "upcast_empty_to_sec",
                    "upcast_erase_principal",
                )
            ) and "after" in mf.name:
                mir_excerpts.append(f"\n--- {mf.name} ---\n{mf.read_text(encoding='utf-8').strip()}")
        record_check(
            "mir::post_cleanup_dumps_captured",
            len(post_cleanup_names) >= 4,
            post_cleanup_names[:12],
        )

        results["specimens"]["vtable_diamond_upcast"] = {
            "runtime_kv": v_kv,
            "vtable_global_count": len(vtable_globals),
            "copy_diamond_vtable": copy_diamond_vt,
            "copy_super_b_vtable": copy_super_b_vt,
            "drop_diamond_vtable": drop_diamond_vt,
            "drop_super_b_vtable": drop_super_b_vt,
            "empty_marker_vtable": empty_marker_vt,
            "vacant_vtable": vacant_vt,
            "post_cleanup_mir_files": post_cleanup_names,
        }

        # ------------------------------------------------------------------
        # 2. Shims & Lazy vs Eager (-C link-dead-code=yes) mono-item collection
        # ------------------------------------------------------------------
        s_src = spec_dir / "shims_and_mono_collection.rs"
        s_lazy_bin = tmp / "shims_lazy"
        s_eager_bin = tmp / "shims_eager"
        s_ll = tmp / "shims.ll"
        s_mir_dir = tmp / "mir_shims"
        s_mir_dir.mkdir()

        c_s_lazy = run_cmd(
            [
                args.rustc,
                "--edition=2021",
                remap_arg,
                "-C",
                "opt-level=0",
                "-C",
                "debuginfo=0",
                "-Z",
                "print-mono-items=yes",
                "-o",
                str(s_lazy_bin),
                str(s_src),
            ]
        )
        c_s_eager = run_cmd(
            [
                args.rustc,
                "--edition=2021",
                remap_arg,
                "-C",
                "opt-level=0",
                "-C",
                "debuginfo=0",
                "-C",
                "link-dead-code=yes",
                "-Z",
                "print-mono-items=yes",
                "-o",
                str(s_eager_bin),
                str(s_src),
            ]
        )
        c_s_ir = run_cmd(
            [
                args.rustc,
                "--edition=2021",
                remap_arg,
                "-C",
                "opt-level=0",
                "-C",
                "debuginfo=0",
                "--emit=llvm-ir",
                "-Z",
                "dump-mir=reify_tracked_fn|reify_virtual_method",
                "-Z",
                f"dump-mir-dir={s_mir_dir}",
                "-o",
                str(s_ll),
                str(s_src),
            ]
        )
        record_check(
            "shims::compile_lazy_eager_ir",
            c_s_lazy.returncode == 0 and c_s_eager.returncode == 0 and c_s_ir.returncode == 0,
            {"lazy": c_s_lazy.stderr.strip(), "eager": c_s_eager.stderr.strip()},
        )

        s_run = run_cmd([str(s_lazy_bin)])
        s_kv = parse_kv(s_run.stdout)
        tracked_free_def_line = find_line_of(s_src, "pub fn tracked_free")
        tracked_impl_def_line = find_line_of(s_src, "fn tracked_on_impl(&self) -> u32 {")
        direct_call_line = find_line_of(s_src, "let direct_line = tracked_free(1);")

        record_check(
            "shims::runtime_values_and_track_caller_lines",
            s_run.returncode == 0
            and s_kv.get("vtable_shim") == "15"
            and s_kv.get("direct_line") == str(direct_call_line)
            and s_kv.get("reified_line") == str(tracked_free_def_line)
            and s_kv.get("virt_reify") == "60"
            and s_kv.get("vtable_track") == str(tracked_impl_def_line)
            and s_kv.get("cl_once") == "17"
            and s_kv.get("box_once") == "10"
            and s_kv.get("fnptr") == "15"
            and s_kv.get("fndef") == "16",
            {
                "kv": s_kv,
                "expected_direct_line": direct_call_line,
                "expected_reified_line": tracked_free_def_line,
                "expected_vtable_track_line": tracked_impl_def_line,
            },
        )

        lazy_items = parse_mono_items(c_s_lazy.stdout)
        eager_items = parse_mono_items(c_s_eager.stdout)
        lazy_names = {x["item"] for x in lazy_items}
        eager_names = {x["item"] for x in eager_items}
        eager_only = sorted(eager_names - lazy_names)

        has_vtable_shim = any("ByValConsume>::consume - shim(vtable)" in n for n in lazy_names)
        has_reify_tracked = any("tracked_free - shim(reify)" in n for n in lazy_names)
        has_reify_virtual = any("DynSpeak>::speak - shim(reify)" in n for n in lazy_names)
        has_reify_vtable_track = any("tracked_on_impl - shim(reify)" in n for n in lazy_names)
        has_closure_once_shim = any(n.endswith("FnOnce<(u64,)>>::call_once - shim") for n in lazy_names)
        has_fnptr_shim = any("fn(u64) -> u64 as std::ops::Fn<(u64,)>>::call - shim" in n for n in lazy_names)
        has_fndef_shim = any("{plain_fn} as std::ops::Fn<(u64,)>>::call - shim" in n for n in lazy_names)
        has_reified_noop_drop = any("drop_in_place::<CopyNoDrop>" in n for n in lazy_names)

        record_check(
            "shims::all_instance_kinds_collected_in_lazy",
            all(
                [
                    has_vtable_shim,
                    has_reify_tracked,
                    has_reify_virtual,
                    has_reify_vtable_track,
                    has_closure_once_shim,
                    has_fnptr_shim,
                    has_fndef_shim,
                    has_reified_noop_drop,
                ]
            ),
            {
                "VTableShim": has_vtable_shim,
                "ReifyShim_track_caller_fnptr": has_reify_tracked,
                "ReifyShim_virtual_fnptr": has_reify_virtual,
                "ReifyShim_track_caller_vtable": has_reify_vtable_track,
                "ClosureOnceShim": has_closure_once_shim,
                "FnPtrShim_fnptr": has_fnptr_shim,
                "FnPtrShim_fndef": has_fndef_shim,
                "DropGlue_reified_None": has_reified_noop_drop,
            },
        )

        record_check(
            "shims::eager_adds_dead_fn_unused_drop_and_default_trait_method",
            any("dead_non_generic" in n for n in eager_only)
            and any("UnusedDefaultTrait>::unused_default" in n for n in eager_only)
            and any("drop_glue::<UnusedDrop>" in n for n in eager_only)
            and any("<UnusedDrop as std::ops::Drop>::drop" in n for n in eager_only),
            {
                "lazy_count": len(lazy_items),
                "eager_count": len(eager_items),
                "eager_only": eager_only,
            },
        )

        # Verify internalization disabled under -C link-dead-code=yes
        lazy_linkages = {p["linkage"] for x in lazy_items for p in x["placements"]}
        eager_linkages = {p["linkage"] for x in eager_items for p in x["placements"]}
        record_check(
            "shims::link_dead_code_disables_internalization",
            "Internal" in lazy_linkages and eager_linkages == {"External"},
            {"lazy_linkages": sorted(lazy_linkages), "eager_linkages": sorted(eager_linkages)},
        )

        for mf in sorted(s_mir_dir.glob("*runtime-post-cleanup*after.mir")):
            mir_excerpts.append(f"\n--- {mf.name} ---\n{mf.read_text(encoding='utf-8').strip()}")

        s_ir_text = s_ll.read_text(encoding="utf-8") if s_ll.exists() else ""
        vtable_shim_ir_m = re.search(
            r"define [^\n]*ByValConsume[^\n]*consume[^\n]*vtable[^\n]*\n.*?\n\}",
            s_ir_text,
            re.S,
        )
        reify_track_ir_m = re.search(
            r"define [^\n]*tracked_free[^\n]*reify[^\n]*\n.*?\n\}",
            s_ir_text,
            re.S,
        )
        llvm_excerpts.append("\n=== SPECIMEN 2: VTableShim & ReifyShim LLVM IR ===")
        if vtable_shim_ir_m:
            llvm_excerpts.append(f"\n; VTableShim (<Payload as ByValConsume>::consume)\n{vtable_shim_ir_m.group(0)}")
        if reify_track_ir_m:
            llvm_excerpts.append(f"\n; ReifyShim (tracked_free)\n{reify_track_ir_m.group(0)}")

        mono_summary_lines.append("=== SPECIMEN 2: LAZY vs EAGER MONO ITEMS ===")
        mono_summary_lines.append(f"lazy_count={len(lazy_items)} eager_count={len(eager_items)} delta={len(eager_only)}")
        mono_summary_lines.append("eager_only:")
        for item in eager_only:
            mono_summary_lines.append(f"  + {item}")

        results["specimens"]["shims_and_mono_collection"] = {
            "runtime_kv": s_kv,
            "lazy_count": len(lazy_items),
            "eager_count": len(eager_items),
            "eager_only": eager_only,
            "lazy_linkages": sorted(lazy_linkages),
            "eager_linkages": sorted(eager_linkages),
            "shim_items_lazy": sorted(n for n in lazy_names if "shim" in n or "drop_in_place" in n),
        }

        # ------------------------------------------------------------------
        # 3. Multi-CGU linkage (Internal vs External, 0 LinkOnceODR, dup vtable)
        # ------------------------------------------------------------------
        cgu_src = spec_dir / "multi_cgu_linkage.rs"
        cgu_res: dict[str, Any] = {}
        for opt in ("0", "2"):
            cgu_bin = tmp / f"multi_cgu_o{opt}"
            c_cgu = run_cmd(
                [
                    args.rustc,
                    "--edition=2021",
                    "-C",
                    "codegen-units=4",
                    "-C",
                    f"opt-level={opt}",
                    "-C",
                    "debuginfo=0",
                    "-Z",
                    "print-mono-items=yes",
                    "-o",
                    str(cgu_bin),
                    str(cgu_src),
                ]
            )
            r_cgu = run_cmd([str(cgu_bin)]) if c_cgu.returncode == 0 else None
            m_items = parse_mono_items(c_cgu.stdout)
            linkage_hist: dict[str, int] = {}
            for it in m_items:
                for p in it["placements"]:
                    linkage_hist[p["linkage"]] = linkage_hist.get(p["linkage"], 0) + 1
            crate_items = [
                it
                for it in m_items
                if any(
                    k in it["item"]
                    for k in ("mod_a::", "mod_b::", "Token as Ping", "fn main")
                )
            ]
            cgu_res[f"O{opt}"] = {
                "compile_rc": c_cgu.returncode,
                "runtime_kv": parse_kv(r_cgu.stdout) if r_cgu else {},
                "total_mono_items": len(m_items),
                "linkage_histogram": linkage_hist,
                "crate_items": crate_items,
            }

        o0_items_map = {x["item"]: x["placements"] for x in cgu_res["O0"]["crate_items"]}
        o0_always = o0_items_map.get("fn mod_a::always_inline_helper", [])
        o0_priv_a = o0_items_map.get("fn mod_a::private_only_a", [])
        o0_shared_g = o0_items_map.get("fn mod_a::shared_generic::<u64>", [])

        record_check(
            "cgu::o0_localcopy_internalized_and_cross_cgu_external",
            len(o0_always) >= 2
            and all(p["linkage"] == "Internal" for p in o0_always)
            and len(o0_priv_a) == 1
            and o0_priv_a[0]["linkage"] == "Internal"
            and len(o0_shared_g) == 1
            and o0_shared_g[0]["linkage"] == "External",
            {
                "always_inline_helper": o0_always,
                "private_only_a": o0_priv_a,
                "shared_generic": o0_shared_g,
            },
        )
        record_check(
            "cgu::zero_linkonce_odr_emissions",
            cgu_res["O0"]["linkage_histogram"].get("OnceODR", 0) == 0
            and cgu_res["O2"]["linkage_histogram"].get("OnceODR", 0) == 0,
            {
                "O0": cgu_res["O0"]["linkage_histogram"],
                "O2": cgu_res["O2"]["linkage_histogram"],
            },
        )
        record_check(
            "cgu::intra_crate_duplicate_private_vtables",
            cgu_res["O0"]["runtime_kv"].get("same_vtable") == "false"
            and cgu_res["O0"]["runtime_kv"].get("res") == "136"
            and cgu_res["O2"]["runtime_kv"].get("same_vtable") == "false"
            and cgu_res["O2"]["runtime_kv"].get("res") == "136",
            {"O0": cgu_res["O0"]["runtime_kv"], "O2": cgu_res["O2"]["runtime_kv"]},
        )

        mono_summary_lines.append("\n=== SPECIMEN 3: MULTI-CGU (codegen-units=4) ===")
        for opt in ("O0", "O2"):
            mono_summary_lines.append(f"--- {opt} histogram={cgu_res[opt]['linkage_histogram']} ---")
            for it in cgu_res[opt]["crate_items"]:
                pl = " ".join(f"{p['cgu']}[{p['linkage']}]" for p in it["placements"])
                mono_summary_lines.append(f"  {it['item']} @@ {pl}")

        results["specimens"]["multi_cgu_linkage"] = cgu_res

        # ------------------------------------------------------------------
        # 4. Separate compilation (rlib + bin, -Z share-generics=yes vs no)
        # ------------------------------------------------------------------
        dep_src = spec_dir / "sep_dep.rs"
        app_src = spec_dir / "sep_app.rs"
        sep_res: dict[str, Any] = {}
        for mode in ("yes", "no"):
            rlib = tmp / f"libsep_dep_{mode}.rlib"
            app_bin = tmp / f"sep_app_{mode}"
            c_dep = run_cmd(
                [
                    args.rustc,
                    "--edition=2021",
                    "--crate-type=rlib",
                    "--crate-name=sep_dep",
                    "-C",
                    "opt-level=0",
                    "-Z",
                    f"share-generics={mode}",
                    "-Z",
                    "print-mono-items=yes",
                    "-o",
                    str(rlib),
                    str(dep_src),
                ]
            )
            c_app = run_cmd(
                [
                    args.rustc,
                    "--edition=2021",
                    "-C",
                    "opt-level=0",
                    "-Z",
                    f"share-generics={mode}",
                    "-Z",
                    "print-mono-items=yes",
                    "--extern",
                    f"sep_dep={rlib}",
                    "-o",
                    str(app_bin),
                    str(app_src),
                ]
            )
            r_app = run_cmd([str(app_bin)]) if c_app.returncode == 0 else None
            dep_items = parse_mono_items(c_dep.stdout)
            app_items = parse_mono_items(c_app.stdout)
            app_poly = sorted(x["item"] for x in app_items if "sep_dep::poly_" in x["item"])
            dep_poly = sorted(x["item"] for x in dep_items if "poly_" in x["item"])
            sep_res[f"share_{mode}"] = {
                "dep_rc": c_dep.returncode,
                "app_rc": c_app.returncode,
                "runtime_kv": parse_kv(r_app.stdout) if r_app else {},
                "dep_poly_items": dep_poly,
                "app_poly_items": app_poly,
            }

        yes_app_poly = sep_res["share_yes"]["app_poly_items"]
        no_app_poly = sep_res["share_no"]["app_poly_items"]
        record_check(
            "sep::share_generics_yes_reuses_upstream_poly_default_u64",
            "fn sep_dep::poly_default::<u64>" not in yes_app_poly
            and "fn sep_dep::poly_inline_never::<u64>" not in yes_app_poly
            and "fn sep_dep::poly_default::<i32>" in yes_app_poly,
            yes_app_poly,
        )
        record_check(
            "sep::share_generics_no_reinstantiates_default_but_still_reuses_inline_never",
            "fn sep_dep::poly_default::<u64>" in no_app_poly
            and "fn sep_dep::poly_inline_never::<u64>" not in no_app_poly
            and "fn sep_dep::poly_default::<i32>" in no_app_poly,
            no_app_poly,
        )
        record_check(
            "sep::cross_crate_duplicate_private_vtables",
            sep_res["share_yes"]["runtime_kv"].get("same_vtable") == "false"
            and sep_res["share_yes"]["runtime_kv"].get("a") == "10"
            and sep_res["share_yes"]["runtime_kv"].get("b") == "30"
            and sep_res["share_yes"]["runtime_kv"].get("c") == "3"
            and sep_res["share_yes"]["runtime_kv"].get("dep_sum") == "20",
            sep_res["share_yes"]["runtime_kv"],
        )

        mono_summary_lines.append("\n=== SPECIMEN 4: SEPARATE COMPILATION (-Z share-generics=yes vs no) ===")
        for mode in ("share_yes", "share_no"):
            mono_summary_lines.append(f"{mode} dep_poly={sep_res[mode]['dep_poly_items']}")
            mono_summary_lines.append(f"{mode} app_poly={sep_res[mode]['app_poly_items']}")

        results["specimens"]["separate_compilation"] = sep_res

        # ------------------------------------------------------------------
        # 5. Polymorphic recursion & type_length_limit negative compiles
        # ------------------------------------------------------------------
        pr_src = spec_dir / "poly_recursion_limit.rs"
        tl_src = spec_dir / "type_length_limit.rs"

        c_pr = run_cmd([args.rustc, "--edition=2021", remap_arg, "-o", str(tmp / "poly_rec"), str(pr_src)])
        c_tl_def = run_cmd([args.rustc, "--edition=2021", remap_arg, "-o", str(tmp / "tl_def"), str(tl_src)])
        c_tl_enf = run_cmd(
            [
                args.rustc,
                "--edition=2021",
                remap_arg,
                "-Z",
                "enforce-type-length-limit=yes",
                "-o",
                str(tmp / "tl_enf"),
                str(tl_src),
            ]
        )

        pr_first_err = next((l for l in c_pr.stderr.splitlines() if l.startswith("error:")), "")
        tl_def_first_err = next((l for l in c_tl_def.stderr.splitlines() if l.startswith("error:")), "")
        tl_enf_first_err = next((l for l in c_tl_enf.stderr.splitlines() if l.startswith("error:")), "")

        record_check(
            "limits::poly_recursion_hits_recursion_limit",
            c_pr.returncode != 0 and "reached the recursion limit while instantiating" in pr_first_err,
            pr_first_err,
        )
        record_check(
            "limits::type_length_limit_not_enforced_by_default",
            c_tl_def.returncode != 0
            and "reached the recursion limit while instantiating" in tl_def_first_err,
            tl_def_first_err,
        )
        record_check(
            "limits::enforce_type_length_limit_flag_triggers_type_length_error",
            c_tl_enf.returncode != 0
            and "reached the type-length limit while instantiating" in tl_enf_first_err,
            tl_enf_first_err,
        )

        results["specimens"]["recursion_and_type_length_limits"] = {
            "poly_recursion_rc": c_pr.returncode,
            "poly_recursion_error": pr_first_err,
            "type_length_default_rc": c_tl_def.returncode,
            "type_length_default_error": tl_def_first_err,
            "type_length_enforced_rc": c_tl_enf.returncode,
            "type_length_enforced_error": tl_enf_first_err,
        }

    # Write outputs
    passed_count = sum(1 for c in checks.values() if c["passed"])
    total_count = len(checks)
    results["summary"] = {
        "checks_passed": passed_count,
        "checks_total": total_count,
        "all_passed": passed_count == total_count,
    }

    (out_dir / "probe_results.json").write_text(
        json.dumps(results, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    (out_dir / "llvm_ir_excerpts.txt").write_text(
        "\n".join(llvm_excerpts) + "\n", encoding="utf-8"
    )
    (out_dir / "mir_excerpts.txt").write_text(
        "\n".join(mir_excerpts) + "\n", encoding="utf-8"
    )
    (out_dir / "mono_items_summary.txt").write_text(
        "\n".join(mono_summary_lines) + "\n", encoding="utf-8"
    )

    summary_md = [
        "# Monomorphization, Vtable Layout, and Trait Upcasting Probe Summary",
        "",
        f"- **Compiler:** `{rustc_meta.get('header', '')}` (`commit-hash: {rustc_meta.get('commit-hash', '')}`, `LLVM version: {rustc_meta.get('LLVM version', '')}`, `host: {rustc_meta.get('host', '')}`)",
        f"- **Checks passed:** `{passed_count} / {total_count}`",
        "",
        "| Check | Passed |",
        "| :--- | :--- |",
    ]
    for name, info in sorted(checks.items()):
        summary_md.append(f"| `{name}` | `{info['passed']}` |")
    (out_dir / "probe_summary.md").write_text("\n".join(summary_md) + "\n", encoding="utf-8")

    print(f"Probe complete: {passed_count}/{total_count} checks passed.")
    if passed_count != total_count:
        for name, info in sorted(checks.items()):
            if not info["passed"]:
                print(f"FAILED: {name} -> {info['detail']}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
