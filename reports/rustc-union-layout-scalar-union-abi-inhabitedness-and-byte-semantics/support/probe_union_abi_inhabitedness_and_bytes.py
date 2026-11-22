#!/usr/bin/env python3
"""Standalone empirical probe for rustc union layout, Scalar::Union niche/validity
erasure, unconditional union inhabitedness, #[repr(transparent)] union ABI forwarding,
LLVM indirect dead_on_return passing, SysV x86-64 eightbyte union classification,
CTFE !Freeze checks, and byte-level partial overwrite / union_data_range semantics.

Executes real `rustc` and `miri` (building an offline no_std libcore sysroot from
`rust-src` so all Miri tests run deterministically without network access), emits
`-Zprint-type-sizes`, LLVM IR, and x86-64 assembly, and writes sanitized JSON with
local paths scrubbed.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


def _run(
    cmd: list[str],
    *,
    cwd: str | None = None,
    env: dict[str, str] | None = None,
    timeout: int = 120,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=cwd,
        env=env,
        text=True,
        capture_output=True,
        timeout=timeout,
    )


def _scrub(text: str, replacements: list[tuple[str, str]]) -> str:
    out = text
    for old, new in replacements:
        if old:
            out = out.replace(old, new)
    return out


def _find_tool(name: str) -> str:
    found = shutil.which(name)
    if found:
        return found
    cargo_bin = Path.home() / ".cargo" / "bin" / name
    if cargo_bin.exists():
        return str(cargo_bin)
    raise RuntimeError(f"Required tool not found on PATH or ~/.cargo/bin: {name}")


def _find_miri_bin(rustc_bin: str) -> str:
    rustup = shutil.which("rustup") or str(Path.home() / ".cargo" / "bin" / "rustup")
    if Path(rustup).exists():
        p = _run([rustup, "which", "miri"])
        if p.returncode == 0 and p.stdout.strip():
            return p.stdout.strip()
    sysroot = _run([rustc_bin, "--print", "sysroot"]).stdout.strip()
    cand = Path(sysroot) / "bin" / "miri"
    if cand.exists():
        return str(cand)
    raise RuntimeError("Could not locate `miri` binary for active rustc toolchain")


def _build_core_miri_sysroot(rustc_bin: str, workdir: Path, target_triple: str) -> Path:
    """Build a minimal offline `no_std` Miri sysroot (core + compiler_builtins stub)
    with `-Zalways-encode-mir` directly from `rust-src`."""
    sysroot = Path(_run([rustc_bin, "--print", "sysroot"]).stdout.strip())
    core_lib = sysroot / "lib" / "rustlib" / "src" / "rust" / "library" / "core" / "src" / "lib.rs"
    if not core_lib.exists():
        raise RuntimeError("rust-src libcore not found at expected toolchain sysroot path")

    mroot = workdir / "miri_core_sysroot"
    libdir = mroot / "lib" / "rustlib" / target_triple / "lib"
    libdir.mkdir(parents=True, exist_ok=True)

    cb_src = workdir / "compiler_builtins_stub.rs"
    cb_src.write_text(
        "#![feature(no_core, compiler_builtins)]\n"
        "#![no_core]\n"
        "#![compiler_builtins]\n",
        encoding="utf-8",
    )

    p_core = _run(
        [
            rustc_bin,
            "--crate-name", "core",
            "--crate-type", "rlib",
            "--edition", "2024",
            "-C", "panic=abort",
            "-Zalways-encode-mir",
            "-Zforce-unstable-if-unmarked",
            "-C", "opt-level=0",
            "-C", "debug-assertions=on",
            "-Zub-checks=yes",
            "--cfg=miri",
            str(core_lib),
            "-o", str(libdir / "libcore.rlib"),
        ],
        timeout=180,
    )
    if p_core.returncode != 0:
        raise RuntimeError(f"Failed to compile libcore for Miri sysroot:\n{p_core.stderr}")

    p_cb = _run(
        [
            rustc_bin,
            "--crate-name", "compiler_builtins",
            "--crate-type", "rlib",
            "--edition", "2024",
            "-C", "panic=abort",
            "-Zalways-encode-mir",
            "-Zforce-unstable-if-unmarked",
            str(cb_src),
            "-o", str(libdir / "libcompiler_builtins.rlib"),
        ],
        timeout=60,
    )
    if p_cb.returncode != 0:
        raise RuntimeError(f"Failed to compile compiler_builtins stub:\n{p_cb.stderr}")

    return mroot


def _extract_llvm_function(ll_text: str, name_substr: str) -> str:
    lines = ll_text.splitlines()
    out: list[str] = []
    capturing = False
    for ln in lines:
        if not capturing:
            if ln.startswith("define ") and name_substr in ln:
                capturing = True
                out.append(ln)
        else:
            out.append(ln)
            if ln.strip() == "}":
                break
    return "\n".join(out)


def _extract_asm_function(asm_text: str, symbol_substr: str) -> str:
    lines = asm_text.splitlines()
    out: list[str] = []
    capturing = False
    for ln in lines:
        if not capturing:
            if symbol_substr in ln and ln.endswith(":"):
                capturing = True
                out.append(ln)
        else:
            out.append(ln)
            if ln.strip() == ".cfi_endproc":
                break
    return "\n".join(out)


def _run_miri_case(
    name: str,
    nostd_src: str,
    std_src: str | None,
    rustc_bin: str,
    miri_bin: str,
    mroot: Path,
    workdir: Path,
    scrub_rules: list[tuple[str, str]],
) -> dict[str, Any]:
    nostd_path = workdir / f"{name}_miri.rs"
    nostd_path.write_text(nostd_src, encoding="utf-8")
    p_miri = _run(
        [
            miri_bin,
            "--edition=2024",
            "-C", "panic=abort",
            "-C", "opt-level=0",
            "--sysroot", str(mroot),
            str(nostd_path),
        ]
    )

    diag_lines: list[str] = []
    if p_miri.returncode != 0:
        in_ub = False
        for ln in p_miri.stderr.splitlines():
            if "error: Undefined Behavior:" in ln:
                in_ub = True
            if in_ub and any(
                tok in ln
                for tok in (
                    "error: Undefined Behavior:",
                    "Undefined Behavior occurred here",
                    "|",
                    "-->",
                    "= help:",
                )
            ):
                diag_lines.append(_scrub(ln, scrub_rules))

    res: dict[str, Any] = {
        "miri_rc": p_miri.returncode,
        "diag_head": [ln for ln in diag_lines if "Undefined Behavior:" in ln or "Undefined Behavior occurred here" in ln][:4],
        "diag_context": diag_lines[:10],
    }

    if std_src is not None:
        std_path = workdir / f"{name}_std.rs"
        bin_path = workdir / f"{name}_bin"
        std_path.write_text(std_src, encoding="utf-8")
        p_build = _run([rustc_bin, "--edition=2024", "-C", "opt-level=2", str(std_path), "-o", str(bin_path)])
        if p_build.returncode == 0:
            p_nat = _run([str(bin_path)])
            res["native_opt2_rc"] = p_nat.returncode
            res["native_opt2_stdout"] = p_nat.stdout.strip()
        else:
            res["native_opt2_build_rc"] = p_build.returncode
    return res


def _run_part_1_miri(
    rustc_bin: str,
    miri_bin: str,
    mroot: Path,
    workdir: Path,
    scrub_rules: list[tuple[str, str]],
) -> dict[str, Any]:
    cases: dict[str, dict[str, Any]] = {}

    # 1. NeverUnion inhabited OK (Infallible and ! fields, copied across fn boundary)
    cases["never_union_inhabited_ok"] = _run_miri_case(
        "never_union_inhabited_ok",
        """#![no_std]
#![no_main]
#![feature(never_type)]
use core::convert::Infallible;
use core::mem::MaybeUninit;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }

#[derive(Copy, Clone)]
pub union NeverUnion { f: Infallible }

#[derive(Copy, Clone)]
pub union BangUnion { b: ! }

#[inline(never)]
fn id_never(u: NeverUnion) -> NeverUnion { u }

#[inline(never)]
fn id_bang(u: BangUnion) -> BangUnion { u }

#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let u = unsafe { MaybeUninit::<NeverUnion>::uninit().assume_init() };
    let _u2 = id_never(core::hint::black_box(u));
    let b = unsafe { MaybeUninit::<BangUnion>::uninit().assume_init() };
    let _b2 = id_bang(core::hint::black_box(b));
    0
}
""",
        None, rustc_bin, miri_bin, mroot, workdir, scrub_rules,
    )

    # 2. Infallible assume_init is immediate UB (uninhabited contrast)
    cases["infallible_assume_init_ub"] = _run_miri_case(
        "infallible_assume_init_ub",
        """#![no_std]
#![no_main]
use core::convert::Infallible;
use core::mem::MaybeUninit;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }

#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let _x: Infallible = unsafe { MaybeUninit::<Infallible>::uninit().assume_init() };
    0
}
""",
        None, rustc_bin, miri_bin, mroot, workdir, scrub_rules,
    )

    # 3. NeverUnion field read UB (!)
    cases["never_union_field_read_ub"] = _run_miri_case(
        "never_union_field_read_ub",
        """#![no_std]
#![no_main]
#![feature(never_type)]
use core::mem::MaybeUninit;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }

#[derive(Copy, Clone)]
pub union BangUnion { b: ! }

#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let u = unsafe { MaybeUninit::<BangUnion>::uninit().assume_init() };
    let _v: ! = unsafe { u.b };
    0
}
""",
        None, rustc_bin, miri_bin, mroot, workdir, scrub_rules,
    )

    # 3b. NeverUnion field read UB (Infallible)
    cases["never_union_infallible_field_read_ub"] = _run_miri_case(
        "never_union_infallible_field_read_ub",
        """#![no_std]
#![no_main]
use core::convert::Infallible;
use core::mem::MaybeUninit;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }

#[derive(Copy, Clone)]
pub union NeverUnion { f: Infallible }

#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let u = unsafe { MaybeUninit::<NeverUnion>::uninit().assume_init() };
    let _v: Infallible = unsafe { u.f };
    0
}
""",
        None, rustc_bin, miri_bin, mroot, workdir, scrub_rules,
    )

    # 4. TwoNonZero union zero-bits & uninit-bits valid across fn calls
    cases["two_nonzero_union_zero_bits_ok"] = _run_miri_case(
        "two_nonzero_union_zero_bits_ok",
        """#![no_std]
#![no_main]
use core::mem::MaybeUninit;
use core::num::NonZeroU64;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }

#[derive(Copy, Clone)]
pub union TwoNonZero { a: NonZeroU64, b: NonZeroU64 }

#[inline(never)]
fn id_two(u: TwoNonZero) -> TwoNonZero { u }

#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let u_zero = unsafe { MaybeUninit::<TwoNonZero>::zeroed().assume_init() };
    let _u1 = id_two(core::hint::black_box(u_zero));
    let u_uninit = unsafe { MaybeUninit::<TwoNonZero>::uninit().assume_init() };
    let _u2 = id_two(core::hint::black_box(u_uninit));
    0
}
""",
        None, rustc_bin, miri_bin, mroot, workdir, scrub_rules,
    )

    # 5. TwoNonZero field read on zeroed union -> UB
    cases["two_nonzero_union_read_zero_field_ub"] = _run_miri_case(
        "two_nonzero_union_read_zero_field_ub",
        """#![no_std]
#![no_main]
use core::mem::MaybeUninit;
use core::num::NonZeroU64;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }

#[derive(Copy, Clone)]
pub union TwoNonZero { a: NonZeroU64, b: NonZeroU64 }

#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let u = unsafe { MaybeUninit::<TwoNonZero>::zeroed().assume_init() };
    let _v = unsafe { u.a };
    0
}
""",
        None, rustc_bin, miri_bin, mroot, workdir, scrub_rules,
    )

    # 6. #[repr(transparent)] union with NonZeroU64 accepts zero and uninit bits across call
    cases["repr_transparent_union_nonzero_zero_bits"] = _run_miri_case(
        "repr_transparent_union_nonzero_zero_bits",
        """#![no_std]
#![no_main]
#![feature(transparent_unions)]
use core::mem::MaybeUninit;
use core::num::NonZeroU64;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }

#[repr(transparent)]
#[derive(Copy, Clone)]
pub union TransNonZero { a: NonZeroU64, z: () }

#[inline(never)]
fn id_trans(u: TransNonZero) -> TransNonZero { u }

#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let u_zero = unsafe { MaybeUninit::<TransNonZero>::zeroed().assume_init() };
    let _u1 = id_trans(core::hint::black_box(u_zero));
    let u_uninit = unsafe { MaybeUninit::<TransNonZero>::uninit().assume_init() };
    let _u2 = id_trans(core::hint::black_box(u_uninit));
    let mu_uninit = unsafe { MaybeUninit::<MaybeUninit<NonZeroU64>>::uninit().assume_init() };
    let _mu2 = core::hint::black_box(mu_uninit);
    0
}
""",
        None, rustc_bin, miri_bin, mroot, workdir, scrub_rules,
    )

    # 7. #[repr(transparent)] struct wrapping NonZeroU64 rejects zero bits (contrast)
    cases["repr_transparent_struct_nonzero_zero_bits_ub"] = _run_miri_case(
        "repr_transparent_struct_nonzero_zero_bits_ub",
        """#![no_std]
#![no_main]
use core::mem::MaybeUninit;
use core::num::NonZeroU64;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }

#[repr(transparent)]
#[derive(Copy, Clone)]
pub struct PlainWrap(NonZeroU64);

#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let _w = unsafe { MaybeUninit::<PlainWrap>::zeroed().assume_init() };
    0
}
""",
        None, rustc_bin, miri_bin, mroot, workdir, scrub_rules,
    )

    # 8. Partial overwrite preserves sibling initialized bytes (and pointer provenance)
    cases["partial_overwrite_preserves_sibling_bytes_ok"] = _run_miri_case(
        "partial_overwrite_preserves_sibling_bytes_ok",
        """#![no_std]
#![no_main]
use core::mem::MaybeUninit;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }

#[repr(C)]
#[derive(Copy, Clone)]
pub union U32Lo { full_u32: u32, lo_u8: u8 }

#[repr(C)]
#[derive(Copy, Clone)]
pub union PairLo { pair: (u32, &'static u8), lo_u8: u8 }

static VAL: u8 = 77;

#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let mut u = U32Lo { full_u32: 0x11223344u32.to_le() };
    u.lo_u8 = 0x99;
    let full = u32::from_le(unsafe { u.full_u32 });
    if full != 0x11223399 {
        return 1;
    }

    // Overwriting low 1 byte in an uninit union initializes byte 0 and keeps reading lo_u8 valid
    let mut u_part = unsafe { MaybeUninit::<U32Lo>::uninit().assume_init() };
    u_part.lo_u8 = 0x55;
    if unsafe { u_part.lo_u8 } != 0x55 {
        return 2;
    }

    // Overwriting low u32 field preserves sibling reference provenance in second slot
    let mut p = PairLo { pair: (0xAABBCCDD, &VAL) };
    p.lo_u8 = 0xEE;
    let (_, r) = unsafe { p.pair };
    if *r != 77 {
        return 3;
    }
    0
}
""",
        """
#[repr(C)]
#[derive(Copy, Clone)]
pub union U32Lo { full_u32: u32, lo_u8: u8 }

fn main() {
    let mut u = U32Lo { full_u32: 0x11223344u32.to_le() };
    u.lo_u8 = 0x99;
    let full = u32::from_le(unsafe { u.full_u32 });
    assert_eq!(full, 0x11223399);
    println!("FULL=0x{:08x}", full);
}
""",
        rustc_bin, miri_bin, mroot, workdir, scrub_rules,
    )

    # 9. Partial overwrite into uninit union leaves upper bytes uninit -> full_u32 read is UB
    cases["partial_overwrite_uninit_upper_read_ub"] = _run_miri_case(
        "partial_overwrite_uninit_upper_read_ub",
        """#![no_std]
#![no_main]
use core::mem::MaybeUninit;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }

#[repr(C)]
#[derive(Copy, Clone)]
pub union U32Lo { full_u32: u32, lo_u8: u8 }

#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let mut u = unsafe { MaybeUninit::<U32Lo>::uninit().assume_init() };
    u.lo_u8 = 0x99;
    let _x = unsafe { u.full_u32 };
    0
}
""",
        None, rustc_bin, miri_bin, mroot, workdir, scrub_rules,
    )

    # 10. Union padding stripping via union_data_range on typed copy
    cases["union_data_range_padding_strip_ub"] = _run_miri_case(
        "union_data_range_padding_strip_ub",
        """#![no_std]
#![no_main]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }

#[repr(C)]
#[derive(Copy, Clone)]
struct PairU8U16(u8, u16);

#[repr(C)]
#[derive(Copy, Clone)]
pub union PadHoleUnion { pair: PairU8U16 }

#[inline(never)]
fn typed_copy(u: PadHoleUnion) -> PadHoleUnion { u }

#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let mut buf = [0xAAu8, 0xBB, 0xCC, 0xDD];
    let u1 = unsafe { *(&buf as *const [u8; 4] as *const PadHoleUnion) };
    let u2 = typed_copy(core::hint::black_box(u1));
    let byte1 = unsafe { *(&u2 as *const PadHoleUnion as *const u8).add(1) };
    if byte1 == 0 { 1 } else { 0 }
}
""",
        None, rustc_bin, miri_bin, mroot, workdir, scrub_rules,
    )

    # 11. Union with full-covering sibling field preserves byte 1 across typed copy
    cases["union_data_range_covered_byte_preserved_ok"] = _run_miri_case(
        "union_data_range_covered_byte_preserved_ok",
        """#![no_std]
#![no_main]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }

#[repr(C)]
#[derive(Copy, Clone)]
struct PairU8U16(u8, u16);

#[repr(C)]
#[derive(Copy, Clone)]
pub union FullCoverUnion { pair: PairU8U16, raw: [u8; 4] }

#[inline(never)]
fn typed_copy(u: FullCoverUnion) -> FullCoverUnion { u }

#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let buf = [0xAAu8, 0xBB, 0xCC, 0xDD];
    let u1 = unsafe { *(&buf as *const [u8; 4] as *const FullCoverUnion) };
    let u2 = typed_copy(core::hint::black_box(u1));
    let byte1 = unsafe { *(&u2 as *const FullCoverUnion as *const u8).add(1) };
    if byte1 == 0xBB { 0 } else { 1 }
}
""",
        None, rustc_bin, miri_bin, mroot, workdir, scrub_rules,
    )

    return cases


def _run_part_2_layouts_and_diags(
    rustc_bin: str,
    workdir: Path,
    scrub_rules: list[tuple[str, str]],
) -> dict[str, Any]:
    sizes_src = workdir / "sizes_probe.rs"
    sizes_src.write_text(
        r"""#![feature(transparent_unions, never_type)]
#![allow(dead_code)]
use core::convert::Infallible;
use core::mem::{MaybeUninit, align_of, size_of};
use core::num::NonZeroU64;

#[derive(Copy, Clone)]
pub union NeverUnion { pub f: Infallible }

#[derive(Copy, Clone)]
pub union BangUnion { pub b: ! }

#[repr(transparent)]
#[derive(Copy, Clone)]
pub struct PlainWrap(pub NonZeroU64);

#[derive(Copy, Clone)]
pub union TwoNonZero { pub a: NonZeroU64, pub b: NonZeroU64 }

#[repr(transparent)]
#[derive(Copy, Clone)]
pub union TransNonZero { pub a: NonZeroU64, pub z: () }

#[derive(Copy, Clone)]
pub union IntOrFloatRust { pub i: u64, pub f: f64 }

#[repr(C)]
#[derive(Copy, Clone)]
pub union IntOrFloatC { pub i: u64, pub f: f64 }

#[repr(align(16))]
#[derive(Copy, Clone)]
pub union OveralignedU64 { pub a: u64 }

#[repr(packed)]
#[derive(Copy, Clone)]
pub union PackedU64 { pub a: u64 }

#[repr(C)]
#[derive(Copy, Clone)]
pub union U32Lo { pub full_u32: u32, pub lo_u8: u8 }

fn main() {
    println!(
        "NEVER_SZ={} OPT_NEVER_SZ={} OPT_TWO_NZ={} OPT_TRANS_NZ={}",
        size_of::<NeverUnion>(),
        size_of::<Option<NeverUnion>>(),
        size_of::<Option<TwoNonZero>>(),
        size_of::<Option<TransNonZero>>(),
    );
    println!("{{");
    println!("  \"Infallible\": [{}, {}],", size_of::<Infallible>(), align_of::<Infallible>());
    println!("  \"Option_Infallible\": [{}, {}],", size_of::<Option<Infallible>>(), align_of::<Option<Infallible>>());
    println!("  \"NeverUnion\": [{}, {}],", size_of::<NeverUnion>(), align_of::<NeverUnion>());
    println!("  \"Option_NeverUnion\": [{}, {}],", size_of::<Option<NeverUnion>>(), align_of::<Option<NeverUnion>>());
    println!("  \"BangUnion\": [{}, {}],", size_of::<BangUnion>(), align_of::<BangUnion>());
    println!("  \"Option_BangUnion\": [{}, {}],", size_of::<Option<BangUnion>>(), align_of::<Option<BangUnion>>());
    println!("  \"PlainWrap\": [{}, {}],", size_of::<PlainWrap>(), align_of::<PlainWrap>());
    println!("  \"Option_PlainWrap\": [{}, {}],", size_of::<Option<PlainWrap>>(), align_of::<Option<PlainWrap>>());
    println!("  \"TwoNonZero\": [{}, {}],", size_of::<TwoNonZero>(), align_of::<TwoNonZero>());
    println!("  \"Option_TwoNonZero\": [{}, {}],", size_of::<Option<TwoNonZero>>(), align_of::<Option<TwoNonZero>>());
    println!("  \"TransNonZero\": [{}, {}],", size_of::<TransNonZero>(), align_of::<TransNonZero>());
    println!("  \"Option_TransNonZero\": [{}, {}],", size_of::<Option<TransNonZero>>(), align_of::<Option<TransNonZero>>());
    println!("  \"MaybeUninit_NonZeroU64\": [{}, {}],", size_of::<MaybeUninit<NonZeroU64>>(), align_of::<MaybeUninit<NonZeroU64>>());
    println!("  \"Option_MaybeUninit_NonZeroU64\": [{}, {}],", size_of::<Option<MaybeUninit<NonZeroU64>>>(), align_of::<Option<MaybeUninit<NonZeroU64>>>());
    println!("  \"IntOrFloatRust\": [{}, {}],", size_of::<IntOrFloatRust>(), align_of::<IntOrFloatRust>());
    println!("  \"IntOrFloatC\": [{}, {}],", size_of::<IntOrFloatC>(), align_of::<IntOrFloatC>());
    println!("  \"OveralignedU64\": [{}, {}],", size_of::<OveralignedU64>(), align_of::<OveralignedU64>());
    println!("  \"PackedU64\": [{}, {}],", size_of::<PackedU64>(), align_of::<PackedU64>());
    println!("  \"U32Lo\": [{}, {}]", size_of::<U32Lo>(), align_of::<U32Lo>());
    println!("}}");
}
""",
        encoding="utf-8",
    )

    bin_sz = workdir / "sizes_bin"
    p_b = _run([rustc_bin, "--edition=2024", "-C", "opt-level=2", str(sizes_src), "-o", str(bin_sz)])
    if p_b.returncode != 0:
        raise RuntimeError(f"sizes_probe build failed:\n{p_b.stderr}")
    p_r = _run([str(bin_sz)])
    if p_r.returncode != 0:
        raise RuntimeError(f"sizes_probe run failed:\n{p_r.stderr}")
    lines = p_r.stdout.splitlines()
    sizes_stdout = lines[0].strip()
    size_align_map = json.loads("\n".join(lines[1:]))

    # Run -Zprint-type-sizes
    p_pts = _run([rustc_bin, "--edition=2024", "-Zprint-type-sizes", str(sizes_src), "-o", str(workdir / "sizes_pts")])
    wanted = {
        "NeverUnion",
        "Option<NeverUnion>",
        "PlainWrap",
        "Option<PlainWrap>",
        "TwoNonZero",
        "Option<TwoNonZero>",
        "TransNonZero",
        "Option<TransNonZero>",
        "OveralignedU64",
        "PackedU64",
    }
    type_size_blocks: dict[str, list[str]] = {}
    cur: str | None = None
    for ln in p_pts.stdout.splitlines():
        if ln.startswith("print-type-size type: `"):
            cur = None
            m = re.search(r"`([^`]+)`", ln)
            if m:
                tn = m.group(1)
                for w in wanted:
                    if tn == w or tn.endswith(f"::{w}") or (w.startswith("Option<") and tn == f"std::option::{w}"):
                        cur = w
                        type_size_blocks[cur] = [ln]
                        break
        elif cur is not None and ln.startswith("print-type-size"):
            type_size_blocks[cur].append(ln)
        else:
            cur = None

    # Compile-time checks: E0740, E0658, CTFE UnsafeCell-in-union
    diag_specs = {
        "union_non_copy_e0740": (
            "#![crate_type = \"lib\"]\n"
            "pub struct HasDrop(u8);\n"
            "impl Drop for HasDrop { fn drop(&mut self) {} }\n"
            "pub union Bad { pub x: HasDrop }\n"
        ),
        "union_manually_drop_ok": (
            "#![crate_type = \"lib\"]\n"
            "use core::mem::ManuallyDrop;\n"
            "pub struct HasDrop(u8);\n"
            "impl Drop for HasDrop { fn drop(&mut self) {} }\n"
            "pub union Good { pub x: ManuallyDrop<HasDrop> }\n"
        ),
        "transparent_union_e0658": (
            "#![crate_type = \"lib\"]\n"
            "#[repr(transparent)]\n"
            "pub union Unstable { pub a: u64, pub z: () }\n"
        ),
        "ctfe_const_cell_union_ok": (
            "#![crate_type = \"lib\"]\n"
            "use core::cell::UnsafeCell;\n"
            "use core::mem::ManuallyDrop;\n"
            "pub union CellUnion { pub c: ManuallyDrop<UnsafeCell<u32>>, pub n: u32 }\n"
            "pub const C: CellUnion = CellUnion { n: 0 };\n"
        ),
        "ctfe_promoted_cell_union_e0492": (
            "#![crate_type = \"lib\"]\n"
            "use core::cell::UnsafeCell;\n"
            "use core::mem::ManuallyDrop;\n"
            "pub union CellUnion { pub c: ManuallyDrop<UnsafeCell<u32>>, pub n: u32 }\n"
            "unsafe impl Sync for CellUnion {}\n"
            "pub const C_REF: &CellUnion = &CellUnion { n: 0 };\n"
        ),
        "ctfe_unsafe_cell_in_union_readonly_e0080": (
            "#![crate_type = \"lib\"]\n"
            "use core::cell::UnsafeCell;\n"
            "use core::mem::ManuallyDrop;\n"
            "#[repr(C)]\n"
            "pub union CellUnion { pub c: ManuallyDrop<UnsafeCell<u32>>, pub n: u32 }\n"
            "unsafe impl Sync for CellUnion {}\n"
            "pub static BAD_REF: &CellUnion = unsafe { &*(&0u32 as *const u32 as *const CellUnion) };\n"
        ),
    }
    compile_checks: dict[str, Any] = {}
    for cname, csrc in diag_specs.items():
        fp = workdir / f"diag_{cname}.rs"
        fp.write_text(csrc, encoding="utf-8")
        p_c = _run([rustc_bin, "--edition=2024", str(fp), "-o", str(workdir / f"diag_{cname}.rlib")])
        err_codes = sorted(set(re.findall(r"error\[(E\d+)\]", p_c.stderr)))
        compile_checks[cname] = {
            "rustc_rc": p_c.returncode,
            "error_codes": err_codes,
            "stderr_head": [_scrub(ln, scrub_rules) for ln in p_c.stderr.splitlines()[:10]],
        }

    return {
        "sizes_stdout": sizes_stdout,
        "size_align_bytes": size_align_map,
        "print_type_sizes": type_size_blocks,
        "compile_checks": compile_checks,
    }


def _run_part_3_llvm_and_asm(
    rustc_bin: str,
    workdir: Path,
) -> dict[str, Any]:
    ir_src = workdir / "union_abi_ir.rs"
    ir_src.write_text(
        """#![feature(transparent_unions, never_type)]
#![crate_type = "lib"]
#![allow(dead_code)]
use core::mem::MaybeUninit;
use core::num::NonZeroU64;
use core::ptr::NonNull;

#[repr(transparent)]
#[derive(Copy, Clone)]
pub struct PlainWrap(pub NonZeroU64);

#[derive(Copy, Clone)]
pub union TwoNonZero { pub a: NonZeroU64, pub b: NonZeroU64 }

#[repr(transparent)]
#[derive(Copy, Clone)]
pub union TransNonZero { pub a: NonZeroU64, pub z: () }

#[repr(transparent)]
#[derive(Copy, Clone)]
pub union TransF64 { pub f: f64, pub z: () }

#[repr(C)]
#[derive(Copy, Clone)]
pub union ReprCF64 { pub f: f64 }

#[derive(Copy, Clone)]
pub union IntOrFloatRust { pub i: u64, pub f: f64 }

#[repr(C)]
#[derive(Copy, Clone)]
pub union IntOrFloatC { pub i: u64, pub f: f64 }

#[repr(align(16))]
#[derive(Copy, Clone)]
pub union OveralignedU64 { pub a: u64 }

#[repr(packed)]
#[derive(Copy, Clone)]
pub union PackedU64 { pub a: u64 }

#[derive(Copy, Clone)]
pub union HeterogeneousScalar { pub i: u32, pub f: f32 }

#[derive(Copy, Clone)]
pub union NonNullPtrUnion { pub p: NonNull<u8>, pub q: *const u8 }

#[unsafe(no_mangle)]
pub fn u_sig_0_plain_wrap(w: PlainWrap) -> PlainWrap { w }

#[unsafe(no_mangle)]
pub fn u_sig_1_two_nonzero(u: TwoNonZero) -> TwoNonZero { u }

#[unsafe(no_mangle)]
pub fn u_sig_2_trans_nonzero(u: TransNonZero) -> TransNonZero { u }

#[unsafe(no_mangle)]
pub fn u_sig_2b_maybe_uninit_nonzero(u: MaybeUninit<NonZeroU64>) -> MaybeUninit<NonZeroU64> { u }

#[unsafe(no_mangle)]
pub fn u_sig_2c_trans_f64(u: TransF64) -> f64 { unsafe { u.f } }

#[unsafe(no_mangle)]
pub fn u_sig_2d_repr_c_f64_rust_abi(u: ReprCF64) -> f64 { unsafe { u.f } }

#[unsafe(no_mangle)]
pub fn u_sig_3_int_float_rust(u: IntOrFloatRust) -> u64 { unsafe { u.i } }

#[unsafe(no_mangle)]
pub extern "C" fn u_sig_4_int_float_sysv_c(u: IntOrFloatC) -> u64 { unsafe { u.i } }

#[unsafe(no_mangle)]
pub fn u_sig_5_overaligned_u64(u: OveralignedU64) -> u64 { unsafe { u.a } }

#[unsafe(no_mangle)]
pub fn u_sig_6_packed_u64(u: PackedU64) -> u64 { unsafe { u.a } }

#[unsafe(no_mangle)]
pub fn u_sig_7_heterogeneous_scalar(u: HeterogeneousScalar) -> u32 { unsafe { u.i } }

#[unsafe(no_mangle)]
pub fn u_sig_8_ptr_union(u: NonNullPtrUnion) -> *const u8 { unsafe { u.q } }
""",
        encoding="utf-8",
    )

    ll_unopt_passes = workdir / "unopt_passes.ll"
    p_noopt = _run([
        rustc_bin, "--edition=2024", "-C", "opt-level=2", "-C", "no-prepopulate-passes",
        "--emit=llvm-ir=" + str(ll_unopt_passes), str(ir_src),
    ])
    if p_noopt.returncode != 0:
        raise RuntimeError(f"no-prepopulate-passes LLVM IR emit failed:\n{p_noopt.stderr}")

    ll_opt2 = workdir / "opt2.ll"
    asm_opt2 = workdir / "opt2.s"
    p_opt2 = _run([
        rustc_bin, "--edition=2024", "-C", "opt-level=2", "-Zmerge-functions=disabled",
        "--emit=llvm-ir=" + str(ll_opt2),
        "--emit=asm=" + str(asm_opt2),
        str(ir_src),
    ])
    if p_opt2.returncode != 0:
        raise RuntimeError(f"opt2 LLVM IR/asm emit failed:\n{p_opt2.stderr}")

    ll_pre_txt = ll_unopt_passes.read_text(encoding="utf-8")
    ll_opt2_txt = ll_opt2.read_text(encoding="utf-8")
    asm_txt = asm_opt2.read_text(encoding="utf-8")

    syms = [
        "u_sig_0_plain_wrap",
        "u_sig_1_two_nonzero",
        "u_sig_2_trans_nonzero",
        "u_sig_2b_maybe_uninit_nonzero",
        "u_sig_2c_trans_f64",
        "u_sig_2d_repr_c_f64_rust_abi",
        "u_sig_3_int_float_rust",
        "u_sig_4_int_float_sysv_c",
        "u_sig_5_overaligned_u64",
        "u_sig_6_packed_u64",
        "u_sig_7_heterogeneous_scalar",
        "u_sig_8_ptr_union",
    ]

    pre_headers: dict[str, str] = {}
    pre_bodies: dict[str, str] = {}
    opt2_headers: dict[str, str] = {}
    asm_funcs: dict[str, str] = {}

    for sym in syms:
        fn_pre = _extract_llvm_function(ll_pre_txt, f"@{sym}(")
        pre_bodies[sym] = fn_pre
        pre_headers[sym] = fn_pre.splitlines()[0].rstrip(" {").strip() if fn_pre else ""
        fn_opt2 = _extract_llvm_function(ll_opt2_txt, f"@{sym}(")
        opt2_headers[sym] = fn_opt2.splitlines()[0].rstrip(" {").strip() if fn_opt2 else ""
        asm_funcs[sym] = _extract_asm_function(asm_txt, sym)

    return {
        "llvm_define_headers_pre_merge": pre_headers,
        "llvm_define_bodies_pre_merge": pre_bodies,
        "llvm_define_headers_opt2": opt2_headers,
        "x86_64_asm_opt2": asm_funcs,
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out", type=Path, help="Output JSON path (prints to stdout if omitted)")
    args = ap.parse_args()

    rustc_bin = _find_tool("rustc")
    miri_bin = _find_miri_bin(rustc_bin)
    rustc_vv = _run([rustc_bin, "-vV"]).stdout.strip()
    miri_ver = _run([miri_bin, "--version"]).stdout.strip()
    host_m = re.search(r"^host:\s*(\S+)", rustc_vv, re.M)
    target_triple = host_m.group(1) if host_m else "x86_64-unknown-linux-gnu"
    sysroot_str = _run([rustc_bin, "--print", "sysroot"]).stdout.strip()

    with tempfile.TemporaryDirectory(prefix="union_probe_") as td:
        workdir = Path(td)
        scrub_rules = [
            (str(workdir), "<TMPDIR>"),
            (sysroot_str, "<SYSROOT>"),
            (str(Path.home()), "<HOME>"),
        ]
        mroot = _build_core_miri_sysroot(rustc_bin, workdir, target_triple)
        part_1 = _run_part_1_miri(rustc_bin, miri_bin, mroot, workdir, scrub_rules)
        part_2 = _run_part_2_layouts_and_diags(rustc_bin, workdir, scrub_rules)
        part_3 = _run_part_3_llvm_and_asm(rustc_bin, workdir)

    payload = {
        "rustc_version": rustc_vv,
        "miri_version": miri_ver,
        "target_triple": target_triple,
        "miri_cases": part_1,
        "layouts_and_diagnostics": part_2,
        "llvm_ir_and_asm": part_3,
    }

    encoded = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(encoded, encoding="utf-8")
        print(f"Wrote {args.out} ({len(encoded)} bytes)")
    else:
        sys.stdout.write(encoded)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
