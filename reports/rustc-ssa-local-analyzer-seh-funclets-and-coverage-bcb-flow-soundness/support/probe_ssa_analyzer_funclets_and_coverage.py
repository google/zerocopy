#!/usr/bin/env python3
"""Empirical compiler probe for:
1. rustc_codegen_ssa::mir::analyze::non_ssa_locals (6 #[custom_mir] pre-pass LLVM IR cases),
2. rustc_codegen_ssa::mir::analyze::cleanup_kinds (x86_64-pc-windows-msvc SEH cleanuppad promotion),
3. -C instrument-coverage BCB balanced-flow counter elimination, atomic __profc_ lowering,
   per-monomorphization inlined generic attribution, and the 5 ELF coverage sections.
"""

from __future__ import annotations

import argparse
import json
import os
import pathlib
import re
import shutil
import subprocess
import tempfile


def resolve_tools() -> tuple[str, str, str, str]:
    rustc = shutil.which("rustc") or str(pathlib.Path.home() / ".cargo" / "bin" / "rustc")
    if not pathlib.Path(rustc).exists():
        raise FileNotFoundError("rustc binary not found in PATH or ~/.cargo/bin")

    vv = subprocess.check_output([rustc, "-vV"], text=True)
    host_match = re.search(r"^host:\s*(\S+)", vv, re.M)
    if not host_match:
        raise RuntimeError(f"could not determine rustc host triple from:\n{vv}")
    host = host_match.group(1)

    sysroot = pathlib.Path(
        subprocess.check_output([rustc, "--print", "sysroot"], text=True).strip()
    )
    llvm_bin_dir = sysroot / "lib" / "rustlib" / host / "bin"

    def find_llvm(tool: str) -> str:
        candidate = llvm_bin_dir / tool
        if candidate.exists():
            return str(candidate)
        found = shutil.which(tool)
        if found:
            return found
        raise FileNotFoundError(f"LLVM tool {tool!r} not found in {llvm_bin_dir} or PATH")

    return rustc, find_llvm("llvm-profdata"), find_llvm("llvm-cov"), find_llvm("llvm-readobj")


def extract_llvm_fn(ir_text: str, fn_name: str) -> str:
    pattern = re.compile(rf"(define\b[^\n]*@{re.escape(fn_name)}\b.*?\n\}})", re.S)
    m = pattern.search(ir_text)
    if not m:
        raise KeyError(f"function @{fn_name} not found in LLVM IR")
    return m.group(1)


def summarize_ssa_fn(ir_fn: str) -> dict[str, object]:
    allocas = [ln.strip() for ln in ir_fn.splitlines() if "= alloca " in ln]
    phis = [ln.strip() for ln in ir_fn.splitlines() if "= phi " in ln]
    loads = [ln.strip() for ln in ir_fn.splitlines() if "= load " in ln]
    stores = [ln.strip() for ln in ir_fn.splitlines() if re.match(r"^\s*store\b", ln)]
    return {
        "alloca_count": len(allocas),
        "phi_count": len(phis),
        "load_count": len(loads),
        "store_count": len(stores),
        "allocas": allocas,
        "ir": ir_fn,
    }


def run_part_a(rustc: str, td: pathlib.Path) -> dict[str, object]:
    src = td / "part_a_local_analyzer.rs"
    src.write_text(
        """#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features)]
use core::intrinsics::mir::*;

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[no_mangle]
pub fn cm_1_single_def_dominated(_1: i32) -> i32 {
    mir! {
        let _2: i32;
        {
            _2 = _1 + 5;
            RET = _2 * 3;
            Return()
        }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[no_mangle]
pub fn cm_2_diamond_two_defs_forces_alloca(_1: bool, _2: i32) -> i32 {
    mir! {
        let _3: i32;
        {
            match _1 {
                true => bb1,
                _ => bb2,
            }
        }
        bb1 = {
            _3 = _2 + 10;
            Goto(bb3)
        }
        bb2 = {
            _3 = _2 + 20;
            Goto(bb3)
        }
        bb3 = {
            RET = _3;
            Return()
        }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[no_mangle]
pub fn cm_3_single_def_nondominating_read_forces_alloca(_1: bool, _2: i32) -> i32 {
    mir! {
        let _3: i32;
        {
            match _1 {
                true => bb1,
                _ => bb2,
            }
        }
        bb1 = {
            _3 = _2 + 77;
            Goto(bb2)
        }
        bb2 = {
            RET = _3;
            Return()
        }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[no_mangle]
pub fn cm_4_scalarpair_field_read_direct_ssa(_1: (i32, i64)) -> i64 {
    mir! {
        {
            RET = _1.1;
            Return()
        }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[no_mangle]
pub fn cm_5_scalarpair_field_write_forces_alloca(_1: i32, _2: i64) -> i64 {
    mir! {
        let _3: (i32, i64);
        {
            _3.0 = _1;
            _3.1 = _2;
            RET = _3.1;
            Return()
        }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[no_mangle]
pub fn cm_6_raw_borrow_forces_alloca(_1: i32) -> i32 {
    mir! {
        let _2: i32;
        let _3: *const i32;
        {
            _2 = _1 + 1;
            _3 = &raw const _2;
            RET = _2;
            Return()
        }
    }
}
"""
    )
    ll_out = td / "part_a.ll"
    subprocess.run(
        [
            rustc,
            "--crate-name=ssa_probe",
            "--crate-type=lib",
            "--edition=2021",
            "-C",
            "opt-level=2",
            "-C",
            "no-prepopulate-passes",
            "--emit=llvm-ir",
            str(src),
            "-o",
            str(ll_out),
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    ir_text = ll_out.read_text()
    cases = [
        "cm_1_single_def_dominated",
        "cm_2_diamond_two_defs_forces_alloca",
        "cm_3_single_def_nondominating_read_forces_alloca",
        "cm_4_scalarpair_field_read_direct_ssa",
        "cm_5_scalarpair_field_write_forces_alloca",
        "cm_6_raw_borrow_forces_alloca",
    ]
    return {name: summarize_ssa_fn(extract_llvm_fn(ir_text, name)) for name in cases}


def run_part_b(rustc: str, td: pathlib.Path) -> dict[str, object]:
    src = td / "msvc_funclet.rs"
    src.write_text(
        """#![feature(no_core, lang_items, auto_traits, intrinsics)]
#![allow(internal_features)]
#![no_core]

#[lang = "pointee_sized"] pub trait PointeeSized {}
#[lang = "meta_sized"] pub trait MetaSized: PointeeSized {}
#[lang = "sized"] pub trait Sized: MetaSized {}
#[lang = "copy"] pub trait Copy {}
#[lang = "freeze"] pub unsafe auto trait Freeze {}
#[lang = "unpin"] pub auto trait Unpin {}
#[lang = "unsafe_unpin"] pub unsafe auto trait UnsafeUnpin {}
#[lang = "legacy_receiver"] pub trait LegacyReceiver {}
impl<T: ?Sized> LegacyReceiver for &T {}
impl<T: ?Sized> LegacyReceiver for &mut T {}
#[lang = "drop"] pub trait Drop { fn drop(&mut self); }

#[rustc_intrinsic]
pub const fn forget<T>(_: T);

#[lang = "panic_in_cleanup"]
fn panic_in_cleanup() -> ! { loop {} }

#[lang = "drop_glue"]
#[inline(never)]
pub unsafe fn drop_in_place_shim<T: ?Sized>(_to_drop: *mut T) {
    unsafe { ext_side_effect(); }
}

unsafe extern "C" {
    #[lang = "eh_personality"]
    fn __CxxFrameHandler3() -> i32;
}

unsafe extern "C-unwind" {
    fn may_throw_outer();
    fn may_throw_inner();
    fn may_throw_left();
    fn may_throw_right();
    fn ext_side_effect();
}

pub struct OuterGuard;
pub struct InnerGuard;
impl Drop for OuterGuard { fn drop(&mut self) {} }
impl Drop for InnerGuard { fn drop(&mut self) {} }

#[no_mangle]
pub unsafe fn seh_shared_cleanup_promotion() {
    let _outer = OuterGuard;
    unsafe { may_throw_outer(); }
    {
        let _inner = InnerGuard;
        unsafe { may_throw_inner(); }
    }
}

#[no_mangle]
pub unsafe fn seh_true_internal_join_promotion(branch: bool) {
    let outer = OuterGuard;
    if branch {
        let left = InnerGuard;
        unsafe { may_throw_left(); }
        forget(left);
    } else {
        let right = InnerGuard;
        unsafe { may_throw_right(); }
        forget(right);
    }
    forget(outer);
}
"""
    )
    ll_out = td / "msvc_funclet.ll"
    proc = subprocess.run(
        [
            rustc,
            "--crate-name=msvc_funclet",
            "--crate-type=lib",
            "--edition=2021",
            "--target=x86_64-pc-windows-msvc",
            "-C",
            "symbol-mangling-version=v0",
            "-C",
            "opt-level=2",
            "-C",
            "no-prepopulate-passes",
            "--emit=llvm-ir",
            str(src),
            "-o",
            str(ll_out),
        ],
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        raise RuntimeError(f"Part B compile failed ({proc.returncode}):\n{proc.stderr}")

    ir_module = ll_out.read_text()
    shared_ir = extract_llvm_fn(ir_module, "seh_shared_cleanup_promotion")
    join_ir = extract_llvm_fn(ir_module, "seh_true_internal_join_promotion")

    def fn_seh_stats(fn_ir: str) -> dict[str, object]:
        pad_defs = [ln.strip() for ln in fn_ir.splitlines() if "= cleanuppad " in ln]
        pad_tokens = [ln.strip() for ln in fn_ir.splitlines() if "cleanuppad" in ln and "funclet_" not in ln]
        rets = [ln.strip() for ln in fn_ir.splitlines() if "cleanupret " in ln]
        invokes = [ln.strip() for ln in fn_ir.splitlines() if "invoke " in ln]
        return {
            "cleanuppad_def_count": len(pad_defs),
            "cleanuppad_defs": pad_defs,
            "cleanuppad_all_lines_count": len(pad_tokens),
            "cleanupret_count": len(rets),
            "cleanuprets": rets,
            "invoke_count": len(invokes),
            "ir": fn_ir,
        }

    mod_pad_defs = [ln.strip() for ln in ir_module.splitlines() if "= cleanuppad " in ln]
    shared_stats = fn_seh_stats(shared_ir)
    join_stats = fn_seh_stats(join_ir)
    return {
        "rc": proc.returncode,
        "module_cleanuppad_def_count": len(mod_pad_defs),
        "module_cleanuppad_all_lines_count": sum(
            1 for ln in ir_module.splitlines() if "cleanuppad" in ln and "funclet_" not in ln
        ),
        "cleanuppad_count": shared_stats["cleanuppad_all_lines_count"],
        "cleanupret_count": shared_stats["cleanupret_count"],
        "invoke_count": shared_stats["invoke_count"],
        "cleanuppads": [
            ln.strip() for ln in shared_ir.splitlines() if "cleanuppad" in ln and "funclet_" not in ln
        ],
        "cleanuprets": shared_stats["cleanuprets"],
        "ir": shared_ir,
        "seh_true_internal_join_promotion": join_stats,
    }


def run_part_c(
    rustc: str,
    llvm_profdata: str,
    llvm_cov: str,
    llvm_readobj: str,
    td: pathlib.Path,
) -> dict[str, object]:
    src = td / "cov_specimen.rs"
    src.write_text(
        """#[inline(never)]
pub fn hot_loop_diamond(n: u32) -> u32 {
    let mut i = 0_u32;
    let mut acc = 0_u32;
    while i < n {
        if (i & 3) == 0 {
            acc += 3;
        } else {
            acc += 1;
        }
        i += 1;
    }
    acc
}

#[inline(always)]
pub fn generic_inlined<T: Copy>(val: T, take_left: bool) -> (T, u32) {
    if take_left {
        (val, 11)
    } else {
        (val, 22)
    }
}

fn main() {
    let s = hot_loop_diamond(std::hint::black_box(100));
    assert_eq!(s, 25 * 3 + 75 * 1);
    let mut tag_sum = 0_u32;
    for _ in 0..10 {
        tag_sum += generic_inlined(std::hint::black_box(5_u32), std::hint::black_box(true)).1;
    }
    for _ in 0..7 {
        tag_sum += generic_inlined(std::hint::black_box(9_u64), std::hint::black_box(false)).1;
    }
    assert_eq!(tag_sum, 10 * 11 + 7 * 22);
}
"""
    )

    mir_dir = td / "mir_dump"
    mir_dir.mkdir()
    ll_prepass_out = td / "cov_specimen_prepass.ll"
    ll_opt_out = td / "cov_specimen_opt.ll"
    bin_out = td / "cov_specimen"

    subprocess.run(
        [
            rustc,
            "--crate-name=cov_specimen",
            "--edition=2021",
            "-C",
            "symbol-mangling-version=v0",
            "-C",
            "opt-level=2",
            "-C",
            "no-prepopulate-passes",
            "-C",
            "instrument-coverage",
            "-Zdump-mir=hot_loop_diamond",
            f"-Zdump-mir-dir={mir_dir}",
            "--emit=llvm-ir",
            str(src),
            "-o",
            str(ll_prepass_out),
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    subprocess.run(
        [
            rustc,
            "--crate-name=cov_specimen",
            "--edition=2021",
            "-C",
            "symbol-mangling-version=v0",
            "-C",
            "opt-level=2",
            "-C",
            "instrument-coverage",
            "--emit=llvm-ir,link",
            str(src),
            "-o",
            str(bin_out),
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    shutil.move(str(td / "cov_specimen.ll"), str(ll_opt_out))

    after_mir_files = sorted(mir_dir.glob("*.InstrumentCoverage.after.mir"))
    if len(after_mir_files) != 1:
        raise RuntimeError(f"expected 1 InstrumentCoverage.after.mir, got {len(after_mir_files)}")
    mir_text = after_mir_files[0].read_text()
    mir_text_scrubbed = mir_text.replace(str(td), "<scratch>")

    hot_loop_mir_bbs = len(re.findall(r"^\s*bb\d+\s*(?:\(cleanup\))?\s*:\s*\{", mir_text, re.M))
    hot_loop_noncleanup_bbs = len(re.findall(r"^\s*bb\d+\s*:\s*\{", mir_text, re.M))
    hot_loop_virtual_counters = sorted(
        {int(m.group(1)) for m in re.finditer(r"Coverage::VirtualCounter\(bcb(\d+)\)", mir_text)}
    )
    hot_loop_virtual_counter_stmt_count = mir_text.count("Coverage::VirtualCounter(")

    before_mir_files = sorted(mir_dir.glob("*.InstrumentCoverage.before.mir"))
    hot_loop_coverage_points = 0
    if before_mir_files:
        before_text = before_mir_files[0].read_text()
        hot_loop_coverage_points = before_text.count("Coverage::Point(") + before_text.count("Coverage::SpanMarker")

    ll_text = ll_prepass_out.read_text()
    m_hot = re.search(
        r"(define\b[^\n]*@([^\s(]*hot_loop_diamond[^\s(]*)\(.*?\n\})", ll_text, re.S
    )
    if not m_hot:
        raise KeyError("hot_loop_diamond pre-pass LLVM IR not found")
    hot_loop_ir = m_hot.group(1)
    hot_loop_symbol = m_hot.group(2)
    hot_loop_increments = [ln.strip() for ln in hot_loop_ir.splitlines() if "atomicrmw" in ln]

    m_main = re.search(r"(define\b[^\n]*@[^\s(]*cov_specimen[^\s(]*main\b\(.*?\n\})", ll_text, re.S)
    main_increments = (
        [ln.strip() for ln in m_main.group(1).splitlines() if "atomicrmw" in ln]
        if m_main
        else []
    )

    ll_opt_text = ll_opt_out.read_text()
    m_hot_opt = re.search(
        r"(define\b[^\n]*@[^\s(]*hot_loop_diamond[^\s(]*\(.*?\n\})", ll_opt_text, re.S
    )
    hot_loop_opt_increments = (
        [ln.strip() for ln in m_hot_opt.group(1).splitlines() if "atomicrmw" in ln]
        if m_hot_opt
        else []
    )

    sec_out = subprocess.check_output([llvm_readobj, "--sections", str(bin_out)], text=True)
    elf_sections = [
        ln.strip()
        for ln in sec_out.splitlines()
        if re.search(r"Name:\s*__llvm_(covmap|covfun|prf_cnts|prf_data|prf_names)\b", ln)
    ]

    profraw = td / "default.profraw"
    subprocess.run([str(bin_out)], env={**os.environ, "LLVM_PROFILE_FILE": str(profraw)}, check=True)
    profdata = td / "cov.profdata"
    subprocess.run(
        [llvm_profdata, "merge", "-sparse", str(profraw), "-o", str(profdata)],
        check=True,
        capture_output=True,
        text=True,
    )

    cov_export_raw = subprocess.check_output(
        [llvm_cov, "export", str(bin_out), f"-instr-profile={profdata}"],
        text=True,
    )
    cov_export = json.loads(cov_export_raw)
    cov_show = subprocess.check_output(
        [llvm_cov, "show", str(bin_out), f"-instr-profile={profdata}"],
        text=True,
    )

    funcs = []
    for f in sorted(cov_export["data"][0]["functions"], key=lambda item: item["name"]):
        regions = f.get("regions", [])
        funcs.append(
            {
                "name": f["name"],
                "count": f["count"],
                "regions_count": len(regions),
                "region_exec_counts": [r[4] for r in regions],
            }
        )

    return {
        "hot_loop_symbol": hot_loop_symbol,
        "hot_loop_mir_total_bbs": hot_loop_mir_bbs,
        "hot_loop_mir_noncleanup_bbs": hot_loop_noncleanup_bbs,
        "hot_loop_virtual_counters_bcb": len(hot_loop_virtual_counters),
        "hot_loop_virtual_counter_stmt_count": hot_loop_virtual_counter_stmt_count,
        "hot_loop_coverage_points_before_pass": hot_loop_coverage_points,
        "hot_loop_physical_atomic_increments_in_prepass_llvm_ir": len(hot_loop_increments),
        "hot_loop_physical_atomic_increments_in_opt2_llvm_ir": len(hot_loop_opt_increments),
        "hot_loop_increment_calls": hot_loop_increments,
        "main_inlined_increment_calls_count_prepass": len(main_increments),
        "elf_coverage_sections": elf_sections,
        "llvm_cov_functions": funcs,
        "llvm_cov_show_annotated": cov_show.replace(str(td), "<scratch>"),
        "hot_loop_instrument_coverage_after_mir": mir_text_scrubbed,
        "hot_loop_prepass_llvm_ir": hot_loop_ir,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out",
        type=pathlib.Path,
        default=None,
        help="Optional output JSON path (prints to stdout if omitted)",
    )
    args = parser.parse_args()

    rustc, llvm_profdata, llvm_cov, llvm_readobj = resolve_tools()
    rustc_version = subprocess.check_output([rustc, "-vV"], text=True).strip()

    with tempfile.TemporaryDirectory() as td_str:
        td = pathlib.Path(td_str)
        result = {
            "rustc_version": rustc_version,
            "part_a_local_analyzer_ssa_vs_memory": run_part_a(rustc, td),
            "part_b_msvc_seh_funclet_promotion": run_part_b(rustc, td),
            "part_c_instrument_coverage_bcb_flow": run_part_c(
                rustc, llvm_profdata, llvm_cov, llvm_readobj, td
            ),
        }

    rendered = json.dumps(result, indent=2) + "\n"
    if args.out is not None:
        args.out.write_text(rendered)
    else:
        print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
