#!/usr/bin/env python3
"""Standalone empirical probe for MIR `CastKind::{Transmute, BoxDerefTransmute, Subtype}`:
1. Miri operational-semantics matrix (`PointerExposeProvenance` vs `Transmute` provenance stripping,
   `PadPair` uninit padding UB vs `[MaybeUninit<u8>; 4]` preservation, `reset_padding` wiping
   previously initialized padding bytes, `[MaybeUninit<u8>; 8]` preserving pointer provenance vs
   `[u8; 8]` clearing it, and `0u32 -> NonZeroU32` scalar validity UB vs `MaybeUninit<NonZeroU32>`).
2. CTFE pointer-to-integer transmute rejection (`ReadPointerAsInt`).
3. Pre-pass LLVM IR (`-C opt-level=1 -C no-prepopulate-passes --emit=llvm-ir`) across all
   `codegen_transmute_operand` (`cg_transmute`) `BackendRepr` arms and `transmute_scalar` /
   `assume_scalar_range` (including `NonZeroU32`, wrapping `Ordering` `255..=1`, `SimdVector`
   non-pointer `bitcast` vs pointer-SIMD `alloca` fallback, `ScalarPair -> ScalarPair` in-register
   transmute, `Scalar -> ScalarPair` `alloca` + `@llvm.lifetime.start`, and `Memory -> Scalar`
   source-aligned load), plus `-C opt-level=2` downstream folding of `x == 0` after a discarded
   `transmute::<u32, NonZeroU32>(x)`.
4. MIR dump check of `Subtyper` (`CastKind::Subtype`) and `LowerIntrinsics` (`CastKind::Transmute`).

Standard library only (Python 3.10+). Scrubs all host paths before writing JSON.
"""
from __future__ import annotations

import argparse
import json
import os
import pathlib
import re
import subprocess
import sys
import tempfile
from typing import Any


MIRI_CASES: dict[str, dict[str, Any]] = {
    "as_cast_exposes_provenance_ok": {
        "extra_flags": ["-Zmiri-permissive-provenance"],
        "expected_rc": 0,
        "expected_diag_substr": None,
        "source": r"""#![no_std]
#![no_main]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }

#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let x = 0xCAFE_BABE_u32;
    let addr = (&raw const x) as usize;
    let p = core::ptr::with_exposed_provenance::<u32>(addr);
    if unsafe { *p } == 0xCAFE_BABE_u32 { 0 } else { 1 }
}
""",
    },
    "transmute_ptr_to_usize_strips_without_exposing_ub": {
        "extra_flags": ["-Zmiri-permissive-provenance"],
        "expected_rc": 1,
        "expected_diag_substr": "dangling pointer (it has no provenance)",
        "source": r"""#![no_std]
#![no_main]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }

#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let x = 0xCAFE_BABE_u32;
    let addr: usize = unsafe { core::mem::transmute(&raw const x) };
    let p = core::ptr::with_exposed_provenance::<u32>(addr);
    if unsafe { *p } == 0xCAFE_BABE_u32 { 0 } else { 1 }
}
""",
    },
    "pad_pair_to_u32_uninit_ub": {
        "extra_flags": [],
        "expected_rc": 1,
        "expected_diag_substr": "encountered uninitialized memory, but expected an integer",
        "source": r"""#![no_std]
#![no_main]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }

#[repr(C)]
struct PadPair(u8, u16);

#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let pair = PadPair(0x11, 0x2233);
    let v: u32 = unsafe { core::mem::transmute(pair) };
    if v == 0 { 1 } else { 0 }
}
""",
    },
    "pad_pair_to_maybe_uninit_bytes_ok": {
        "extra_flags": [],
        "expected_rc": 0,
        "expected_diag_substr": None,
        "source": r"""#![no_std]
#![no_main]
use core::mem::MaybeUninit;
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }

#[repr(C)]
struct PadPair(u8, u16);

#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let pair = PadPair(0x11, 0x2233);
    let bytes: [MaybeUninit<u8>; 4] = unsafe { core::mem::transmute(pair) };
    let b0 = unsafe { bytes[0].assume_init() };
    let b2 = unsafe { bytes[2].assume_init() };
    let b3 = unsafe { bytes[3].assume_init() };
    if b0 == 0x11 && b2 == 0x33 && b3 == 0x22 { 0 } else { 1 }
}
""",
    },
    "pad_pair_typed_copy_resets_prior_init_padding_ub": {
        "extra_flags": [],
        "expected_rc": 1,
        "expected_diag_substr": "encountered uninitialized memory, but expected an integer",
        "source": r"""#![no_std]
#![no_main]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }

#[repr(C)]
struct PadPair(u8, u16);

#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let all_init: u32 = 0xFF22_3311;
    let pair: PadPair = unsafe { core::mem::transmute(all_init) };
    let roundtrip: u32 = unsafe { core::mem::transmute(pair) };
    if roundtrip == 0 { 1 } else { 0 }
}
""",
    },
    "u32_zero_to_nonzero_u32_ub": {
        "extra_flags": [],
        "expected_rc": 1,
        "expected_diag_substr": "encountered 0, but expected something greater or equal to 1",
        "source": r"""#![no_std]
#![no_main]
use core::num::NonZeroU32;
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }

#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let _unused: NonZeroU32 = unsafe { core::mem::transmute(0u32) };
    0
}
""",
    },
    "u32_zero_to_maybe_uninit_nonzero_u32_ok": {
        "extra_flags": [],
        "expected_rc": 0,
        "expected_diag_substr": None,
        "source": r"""#![no_std]
#![no_main]
use core::mem::MaybeUninit;
use core::num::NonZeroU32;
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }

#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let _wrapped: MaybeUninit<NonZeroU32> = unsafe { core::mem::transmute(0u32) };
    0
}
""",
    },
    "ptr_transmute_through_maybe_uninit_bytes_strict_ok": {
        "extra_flags": ["-Zmiri-strict-provenance"],
        "expected_rc": 0,
        "expected_diag_substr": None,
        "source": r"""#![no_std]
#![no_main]
use core::mem::{MaybeUninit, size_of};
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }

#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let x = 0x1234_5678_u32;
    let p: *const u32 = &raw const x;
    let raw: [MaybeUninit<u8>; size_of::<*const u32>()] = unsafe { core::mem::transmute(p) };
    let q: *const u32 = unsafe { core::mem::transmute(raw) };
    if unsafe { *q } == 0x1234_5678_u32 { 0 } else { 1 }
}
""",
    },
    "ptr_transmute_through_u8_array_strips_provenance_ub": {
        "extra_flags": ["-Zmiri-permissive-provenance"],
        "expected_rc": 1,
        "expected_diag_substr": "dangling pointer (it has no provenance)",
        "source": r"""#![no_std]
#![no_main]
use core::mem::size_of;
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }

#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let x = 0x1234_5678_u32;
    let p: *const u32 = &raw const x;
    let raw: [u8; size_of::<*const u32>()] = unsafe { core::mem::transmute(p) };
    let q: *const u32 = unsafe { core::mem::transmute(raw) };
    if unsafe { *q } == 0x1234_5678_u32 { 0 } else { 1 }
}
""",
    },
}


CTFE_PTR_TO_INT_RS = r"""#![crate_type = "lib"]
static X: u32 = 42;
pub const BAD_ADDR: usize = unsafe { core::mem::transmute(&raw const X) };
"""


LLVM_IR_PROBE_RS = r"""#![feature(repr_simd)]
#![crate_type = "lib"]
#![allow(improper_ctypes_definitions)]

use core::cmp::Ordering;
use core::marker::PhantomData;
use core::mem::transmute;
use core::num::NonZeroU32;

#[repr(simd)]
pub struct I32x4([i32; 4]);

#[repr(simd)]
pub struct F32x4([f32; 4]);

#[repr(simd)]
pub struct PtrX4([*const u8; 4]);

#[repr(simd)]
pub struct UsizeX4([usize; 4]);

#[unsafe(no_mangle)]
pub unsafe fn tm_1_scalar_nonzero_assume(x: u32) -> NonZeroU32 {
    unsafe { transmute(x) }
}

#[unsafe(no_mangle)]
pub unsafe fn tm_2_scalar_u32_to_f32(x: u32) -> f32 {
    unsafe { transmute(x) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn tm_3_simd_bitcast(x: I32x4) -> F32x4 {
    unsafe { transmute(x) }
}

#[unsafe(no_mangle)]
pub unsafe fn tm_4_scalarpair_in_regs(x: (u32, u32)) -> (f32, NonZeroU32) {
    unsafe { transmute(x) }
}

#[unsafe(no_mangle)]
pub unsafe fn tm_5_scalar_to_scalarpair_alloca(x: u64) -> (u32, u32) {
    unsafe { transmute(x) }
}

#[unsafe(no_mangle)]
pub unsafe fn tm_6_ptr_to_usize_ptrtoint(p: *const u32) -> usize {
    unsafe { transmute(p) }
}

#[unsafe(no_mangle)]
pub fn tm_6b_as_cast_ptr_to_usize(p: *const u32) -> usize {
    p as usize
}

#[unsafe(no_mangle)]
pub unsafe fn tm_7_memory_to_scalar_source_align(arr: [u8; 16]) -> u128 {
    unsafe { transmute(arr) }
}

#[target_feature(enable = "avx")]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn tm_8_simd_ptr_to_int_alloca(v: PtrX4) -> UsizeX4 {
    unsafe { transmute(v) }
}

#[unsafe(no_mangle)]
pub unsafe fn tm_9_discarded_nonzero_assume_eq_zero(x: u32) -> bool {
    let _unused: NonZeroU32 = unsafe { transmute(x) };
    x == 0
}

#[unsafe(no_mangle)]
pub unsafe fn tm_10_wrapping_niche_ordering_assume(x: u8) -> Ordering {
    unsafe { transmute(x) }
}

#[unsafe(no_mangle)]
pub unsafe fn tm_11_zst_transmute(x: ()) -> PhantomData<u64> {
    unsafe { transmute(x) }
}

#[unsafe(no_mangle)]
pub fn subtype_hrtb_fn_ptr<'a>(f: for<'b> fn(&'b u8) -> &'b u8) -> fn(&'a u8) -> &'a u8 {
    f
}
"""


def run_cmd(argv: list[str], cwd: str, env: dict[str, str] | None = None) -> tuple[int, str, str]:
    proc = subprocess.run(argv, cwd=cwd, env=env, capture_output=True, text=True, timeout=300)
    return proc.returncode, proc.stdout, proc.stderr


def build_minimal_core_miri_sysroot(rustc: str, target: str, work: str) -> str:
    """Build a minimal 2-crate (`core` + `compiler_builtins`) `-Zalways-encode-mir -Zno-codegen`
    sysroot from the toolchain's own `rust-src` component so `#![no_std]` Miri probes run offline."""
    rc, sysroot_out, se = run_cmd([rustc, "--print", "sysroot"], work)
    if rc != 0:
        raise RuntimeError(f"rustc --print sysroot failed: {se}")
    tc_sysroot = pathlib.Path(sysroot_out.strip())
    core_src = tc_sysroot / "lib/rustlib/src/rust/library/core/src/lib.rs"
    if not core_src.exists():
        raise RuntimeError("toolchain is missing rust-src component (library/core/src/lib.rs)")

    miri_sysroot = pathlib.Path(work) / "miri_core_sysroot"
    lib_dir = miri_sysroot / "lib/rustlib" / target / "lib"
    lib_dir.mkdir(parents=True, exist_ok=True)

    rc_core, _, se_core = run_cmd(
        [
            rustc,
            "--edition=2024",
            "--crate-name",
            "core",
            "--crate-type",
            "rlib",
            "-C",
            "panic=abort",
            "-C",
            "embed-bitcode=no",
            "-Z",
            "force-unstable-if-unmarked",
            "-Z",
            "always-encode-mir",
            "-Z",
            "no-codegen",
            "-o",
            str(lib_dir / "libcore.rlib"),
            str(core_src),
        ],
        work,
    )
    if rc_core != 0:
        raise RuntimeError(f"building libcore.rlib for Miri failed:\n{se_core}")

    cb_src = pathlib.Path(work) / "compiler_builtins_stub.rs"
    cb_src.write_text(
        "#![allow(internal_features)]\n#![feature(compiler_builtins)]\n#![compiler_builtins]\n#![no_std]\n",
        encoding="utf-8",
    )
    rc_cb, _, se_cb = run_cmd(
        [
            rustc,
            "--edition=2024",
            "--crate-name",
            "compiler_builtins",
            "--crate-type",
            "rlib",
            "--sysroot",
            str(miri_sysroot),
            "-C",
            "panic=abort",
            "-C",
            "embed-bitcode=no",
            "-Z",
            "always-encode-mir",
            "-Z",
            "no-codegen",
            "-o",
            str(lib_dir / "libcompiler_builtins.rlib"),
            str(cb_src),
        ],
        work,
    )
    if rc_cb != 0:
        raise RuntimeError(f"building libcompiler_builtins.rlib for Miri failed:\n{se_cb}")
    return str(miri_sysroot)


def extract_llvm_fn(ir_text: str, fn_name: str) -> str:
    pattern = re.compile(
        rf"(^define\b[^\n]*@{re.escape(fn_name)}\b[^\n]*\{{.*?^\}})",
        re.MULTILINE | re.DOTALL,
    )
    m = pattern.search(ir_text)
    if not m:
        raise KeyError(f"LLVM function @{fn_name} not found in emitted IR")
    return m.group(1)


def classify_ir(fn_ir: str) -> dict[str, Any]:
    return {
        "has_alloca": bool(re.search(r"\balloca\b", fn_ir)),
        "has_llvm_assume": "@llvm.assume" in fn_ir,
        "has_bitcast": bool(re.search(r"\bbitcast\b", fn_ir)),
        "has_ptrtoint": bool(re.search(r"\bptrtoint\b", fn_ir)),
        "has_lifetime_start": "@llvm.lifetime.start" in fn_ir,
        "ir": fn_ir,
    }


def extract_diag_head(stderr: str, work: str) -> list[str]:
    out: list[str] = []
    for raw in stderr.splitlines():
        line = raw.replace(work, "<workdir>")
        if line.lstrip().startswith("--> "):
            continue
        if (
            line.startswith("error")
            or "Undefined Behavior occurred here" in line
            or line.strip().startswith("= help: this indicates a bug")
        ):
            out.append(line.rstrip())
    return out[:6]


def scrub_json(obj: Any, needles: list[tuple[str, str]]) -> str:
    text = json.dumps(obj, indent=2, sort_keys=True)
    for needle, repl in needles:
        if needle:
            text = text.replace(needle, repl)
    leak = re.search(r"""(?:^|[\s"'=:,\[(])/(?:[A-Za-z0-9._+-]+/)+[A-Za-z0-9._+-]*""", text, re.M)
    if leak:
        raise SystemExit(
            f"refusing to write output: absolute path survived scrubbing: {leak.group(0)[:80]!r}"
        )
    return text


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--rustc", default="rustc")
    ap.add_argument("--miri", default=None)
    ap.add_argument("--miri-sysroot", default=None)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()

    rc, vv, se = run_cmd([args.rustc, "-vV"], os.getcwd())
    if rc != 0:
        print(f"cannot run {args.rustc} -vV: {se}", file=sys.stderr)
        return 2
    tc_meta = dict(line.split(": ", 1) for line in vv.strip().splitlines()[1:] if ": " in line)
    host_target = tc_meta["host"]

    miri_bin = args.miri
    if miri_bin is None:
        cand = pathlib.Path(os.path.abspath(args.rustc)).parent / "miri"
        if cand.exists():
            miri_bin = str(cand)

    with tempfile.TemporaryDirectory(prefix="probe_transmute_") as work:
        # 1. Miri matrix
        miri_results: dict[str, Any] = {}
        miri_version_line: str | None = None
        if miri_bin is not None:
            mrc, mvv, _ = run_cmd([miri_bin, "--version"], work)
            if mrc == 0 and mvv.strip():
                miri_version_line = mvv.strip().splitlines()[0]
            sysroot = args.miri_sysroot or build_minimal_core_miri_sysroot(
                args.rustc, host_target, work
            )
            for case_name, spec in MIRI_CASES.items():
                src_file = pathlib.Path(work) / f"{case_name}.rs"
                src_file.write_text(spec["source"], encoding="utf-8")
                cmd = [
                    miri_bin,
                    "--edition=2024",
                    "-C",
                    "panic=abort",
                    "--sysroot",
                    sysroot,
                    *spec["extra_flags"],
                    str(src_file),
                ]
                crc, _, cse = run_cmd(cmd, work)
                miri_results[case_name] = {
                    "extra_flags": spec["extra_flags"],
                    "miri_rc": crc,
                    "diag_head": extract_diag_head(cse, work),
                }

        # 2. CTFE pointer-to-int transmute check
        ctfe_src = pathlib.Path(work) / "ctfe_ptr_to_int.rs"
        ctfe_src.write_text(CTFE_PTR_TO_INT_RS, encoding="utf-8")
        ctfe_rc, _, ctfe_se = run_cmd(
            [args.rustc, "--edition=2024", "--emit=metadata", str(ctfe_src)], work
        )

        # 3. Pre-pass LLVM IR (`-C opt-level=1 -C no-prepopulate-passes`)
        ir_src = pathlib.Path(work) / "llvm_ir_probe.rs"
        ir_src.write_text(LLVM_IR_PROBE_RS, encoding="utf-8")
        ir_pre_path = pathlib.Path(work) / "llvm_ir_prepass.ll"
        rc_pre, _, se_pre = run_cmd(
            [
                args.rustc,
                "--edition=2024",
                "-C",
                "opt-level=1",
                "-C",
                "no-prepopulate-passes",
                "-Z",
                "mir-opt-level=0",
                "--emit=llvm-ir",
                "-o",
                str(ir_pre_path),
                str(ir_src),
            ],
            work,
        )
        if rc_pre != 0:
            print(f"pre-pass LLVM IR compile failed:\n{se_pre}", file=sys.stderr)
            return 2
        ir_pre_text = ir_pre_path.read_text(encoding="utf-8")

        part_c_names = (
            "tm_1_scalar_nonzero_assume",
            "tm_2_scalar_u32_to_f32",
            "tm_3_simd_bitcast",
            "tm_4_scalarpair_in_regs",
            "tm_5_scalar_to_scalarpair_alloca",
            "tm_6_ptr_to_usize_ptrtoint",
        )
        part_c = {fn: classify_ir(extract_llvm_fn(ir_pre_text, fn)) for fn in part_c_names}

        extended_names = (
            "tm_6b_as_cast_ptr_to_usize",
            "tm_7_memory_to_scalar_source_align",
            "tm_8_simd_ptr_to_int_alloca",
            "tm_9_discarded_nonzero_assume_eq_zero",
            "tm_10_wrapping_niche_ordering_assume",
            "tm_11_zst_transmute",
            "subtype_hrtb_fn_ptr",
        )
        part_d_prepass = {
            fn: classify_ir(extract_llvm_fn(ir_pre_text, fn)) for fn in extended_names
        }

        # 4. Optimized LLVM IR (`-C opt-level=2`) for `tm_9_discarded_nonzero_assume_eq_zero`
        ir_opt_path = pathlib.Path(work) / "llvm_ir_opt2.ll"
        rc_opt, _, se_opt = run_cmd(
            [
                args.rustc,
                "--edition=2024",
                "-C",
                "opt-level=2",
                "--emit=llvm-ir",
                "-o",
                str(ir_opt_path),
                str(ir_src),
            ],
            work,
        )
        if rc_opt != 0:
            print(f"opt-level=2 LLVM IR compile failed:\n{se_opt}", file=sys.stderr)
            return 2
        ir_opt_text = ir_opt_path.read_text(encoding="utf-8")
        tm9_opt2_ir = extract_llvm_fn(ir_opt_text, "tm_9_discarded_nonzero_assume_eq_zero")

        # 5. MIR dump for `Subtyper` and `LowerIntrinsics`
        mir_dir = pathlib.Path(work) / "mir_dumps"
        mir_dir.mkdir(parents=True, exist_ok=True)
        rc_mir, _, se_mir = run_cmd(
            [
                args.rustc,
                "--edition=2024",
                "-Z",
                "mir-opt-level=0",
                "-Z",
                "dump-mir=all",
                f"-Zdump-mir-dir={mir_dir}",
                "--emit=mir",
                "-o",
                str(pathlib.Path(work) / "probe.mir"),
                str(ir_src),
            ],
            work,
        )
        if rc_mir != 0:
            print(f"MIR dump compile failed:\n{se_mir}", file=sys.stderr)
            return 2

        subtype_cast_lines: list[str] = []
        transmute_cast_lines: list[str] = []
        for dump_file in sorted(mir_dir.iterdir()):
            txt = dump_file.read_text(encoding="utf-8")
            if "subtype_hrtb_fn_ptr" in dump_file.name and dump_file.name.endswith("Subtyper.after.mir"):
                subtype_cast_lines = [
                    ln.strip() for ln in txt.splitlines() if "(Subtype)" in ln
                ]
            if "tm_1_scalar_nonzero_assume" in dump_file.name and dump_file.name.endswith(
                "LowerIntrinsics.after.mir"
            ):
                transmute_cast_lines = [
                    ln.strip() for ln in txt.splitlines() if "(Transmute)" in ln
                ]

        # 6. Assertions / discriminating checks
        checks: dict[str, bool] = {
            "ctfe_rejects_ptr_to_usize_transmute": ctfe_rc != 0
            and (
                "pointer" in ctfe_se.lower()
                or "transmute" in ctfe_se.lower()
                or "integer" in ctfe_se.lower()
            ),
            "tm_1_injects_llvm_assume_without_alloca": part_c["tm_1_scalar_nonzero_assume"][
                "has_llvm_assume"
            ]
            and not part_c["tm_1_scalar_nonzero_assume"]["has_alloca"]
            and "icmp ule i32" in part_c["tm_1_scalar_nonzero_assume"]["ir"],
            "tm_2_emits_scalar_bitcast": part_c["tm_2_scalar_u32_to_f32"]["has_bitcast"]
            and not part_c["tm_2_scalar_u32_to_f32"]["has_alloca"],
            "tm_3_emits_simd_vector_bitcast": part_c["tm_3_simd_bitcast"]["has_bitcast"]
            and "bitcast <4 x i32>" in part_c["tm_3_simd_bitcast"]["ir"]
            and not part_c["tm_3_simd_bitcast"]["has_alloca"],
            "tm_4_transmutes_scalarpair_in_registers_with_assume": part_c[
                "tm_4_scalarpair_in_regs"
            ]["has_bitcast"]
            and part_c["tm_4_scalarpair_in_regs"]["has_llvm_assume"]
            and not part_c["tm_4_scalarpair_in_regs"]["has_alloca"],
            "tm_5_falls_back_to_alloca_and_lifetime_start": part_c[
                "tm_5_scalar_to_scalarpair_alloca"
            ]["has_alloca"]
            and part_c["tm_5_scalar_to_scalarpair_alloca"]["has_lifetime_start"],
            "tm_6_lowers_ptr_to_usize_via_ptrtoint": part_c["tm_6_ptr_to_usize_ptrtoint"][
                "has_ptrtoint"
            ]
            and not part_c["tm_6_ptr_to_usize_ptrtoint"]["has_alloca"],
            "tm_7_memory_to_scalar_uses_source_align_1": "load i128, ptr"
            in part_d_prepass["tm_7_memory_to_scalar_source_align"]["ir"]
            and "align 1" in part_d_prepass["tm_7_memory_to_scalar_source_align"]["ir"],
            "tm_8_pointer_simd_uses_alloca_not_bitcast": part_d_prepass[
                "tm_8_simd_ptr_to_int_alloca"
            ]["has_alloca"]
            and not part_d_prepass["tm_8_simd_ptr_to_int_alloca"]["has_bitcast"],
            "tm_9_discarded_transmute_injects_assume_and_folds_eq_zero_to_false": part_d_prepass[
                "tm_9_discarded_nonzero_assume_eq_zero"
            ]["has_llvm_assume"]
            and "ret i1 false" in tm9_opt2_ir,
            "tm_10_wrapping_niche_ordering_emits_single_icmp_ule_assume": part_d_prepass[
                "tm_10_wrapping_niche_ordering_assume"
            ]["has_llvm_assume"]
            and "icmp ule i8" in part_d_prepass["tm_10_wrapping_niche_ordering_assume"]["ir"],
            "mir_subtyper_emits_castkind_subtype": len(subtype_cast_lines) == 1,
            "mir_lower_intrinsics_emits_castkind_transmute": len(transmute_cast_lines) == 1,
        }

        if miri_bin is not None:
            for case_name, spec in MIRI_CASES.items():
                obs = miri_results[case_name]
                ok = obs["miri_rc"] == spec["expected_rc"]
                if spec["expected_diag_substr"] is not None:
                    joined = "\n".join(obs["diag_head"])
                    ok = ok and (spec["expected_diag_substr"] in joined)
                checks[f"miri_{case_name}"] = ok

        payload = {
            "schema": "rustc-transmute-backend-repr-provenance-probe/1",
            "rustc_version": vv.strip(),
            "miri_version": miri_version_line,
            "part_a_b_miri_transmute_matrix": miri_results,
            "ctfe_ptr_to_usize_transmute": {
                "rustc_rc": ctfe_rc,
                "diag_head": extract_diag_head(ctfe_se, work),
            },
            "part_c_llvm_cg_transmute_arms": part_c,
            "part_d_extended_codegen_and_mir_probes": {
                "prepass_llvm_ir": part_d_prepass,
                "tm_9_opt_level_2_ir": tm9_opt2_ir,
                "mir_subtyper_after_cast_lines": subtype_cast_lines,
                "mir_lower_intrinsics_after_cast_lines": transmute_cast_lines,
            },
            "checks": checks,
            "summary": {
                "held_count": sum(1 for v in checks.values() if v),
                "failed_count": sum(1 for v in checks.values() if not v),
                "failed": sorted(k for k, v in checks.items() if not v),
            },
        }

        needles = [
            (work, "<workdir>"),
            (os.path.dirname(os.path.abspath(args.rustc)), "<toolchain-bin>"),
            (args.miri_sysroot or "", "<miri-sysroot>"),
            (os.path.expanduser("~"), "<home>"),
        ]
        scrubbed = scrub_json(payload, needles)

    if args.out:
        pathlib.Path(args.out).write_text(scrubbed + "\n", encoding="utf-8")
    else:
        print(scrubbed)

    failed = payload["summary"]["failed"]
    print(
        f"held={payload['summary']['held_count']} failed={payload['summary']['failed_count']}",
        file=sys.stderr,
    )
    for k in failed:
        print(f"FAILED: {k}", file=sys.stderr)
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
