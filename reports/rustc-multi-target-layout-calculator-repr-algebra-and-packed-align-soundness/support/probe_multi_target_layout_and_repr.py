#!/usr/bin/env python3
"""Multi-target rustc_abi layout, #[repr] algebra, E0588/aligned_fields_in_packed bypass,
x86_win32 ABI ICE, and -Z randomize-layout empirical probe.

Runs hermetically inside a TemporaryDirectory and emits JSON with zero host-specific paths.
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

TARGETS_9 = [
    "aarch64-apple-darwin",
    "aarch64-unknown-linux-gnu",
    "i686-pc-windows-msvc",
    "i686-unknown-linux-gnu",
    "riscv64gc-unknown-none-elf",
    "s390x-unknown-linux-gnu",
    "thumbv7m-none-eabi",
    "wasm32-unknown-unknown",
    "x86_64-unknown-linux-gnu",
]

NO_CORE_PRELUDE = """#![feature(no_core, lang_items, rustc_attrs, repr_simd)]
#![no_core]
#![allow(internal_features, non_camel_case_types, dead_code)]

#[lang = "pointee_sized"]
pub trait PointeeSized {}
#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}
#[lang = "sized"]
pub trait Sized: MetaSized {}
#[lang = "copy"]
pub trait Copy {}

impl Copy for bool {}
impl Copy for u8 {}
impl Copy for u16 {}
impl Copy for u32 {}
impl Copy for u64 {}
impl Copy for i64 {}
impl Copy for u128 {}
impl Copy for f32 {}
impl Copy for f64 {}
impl<T: PointeeSized> Copy for *const T {}
impl<T: Copy, const N: usize> Copy for [T; N] {}
"""


def find_rustc(explicit: str | None) -> str:
    if explicit:
        return explicit
    found = shutil.which("rustc")
    if found:
        return found
    cargo_rustc = Path.home() / ".cargo" / "bin" / "rustc"
    if cargo_rustc.exists():
        return str(cargo_rustc)
    raise RuntimeError("rustc not found in PATH or ~/.cargo/bin/rustc")


def scrub(text: str, tmpdir: str) -> str:
    return text.replace(tmpdir, "<TMP>").strip()


def run_cmd(cmd: list[str], tmpdir: str) -> tuple[int, str, str]:
    proc = subprocess.run(cmd, capture_output=True, text=True, check=False)
    return proc.returncode, scrub(proc.stdout, tmpdir), scrub(proc.stderr, tmpdir)


def parse_dump_layout_errors(stderr: str) -> dict[str, list[str]]:
    """Parse `#[rustc_dump_layout(...)]` diagnostic messages keyed by item identifier."""
    results: dict[str, list[str]] = {}
    lines = stderr.splitlines()
    for idx, line in enumerate(lines):
        m = re.match(r"^error:\s+(size:|align:|backend_repr:|homogeneous_aggregate:)\s*(.*)$", line)
        if not m:
            continue
        msg = f"{m.group(1)} {m.group(2)}".strip()
        # Look ahead for source snippet line containing the item name.
        item_name = None
        for look in range(idx + 1, min(idx + 8, len(lines))):
            sn = lines[look]
            im = re.search(r"\b(?:pub\s+)?(?:type|struct|enum|union)\s+([A-Za-z_][A-Za-z0-9_]*)\b", sn)
            if im:
                item_name = im.group(1)
                break
        if item_name is not None:
            results.setdefault(item_name, []).append(msg)
    return {k: results[k] for k in sorted(results)}


def probe_part_a(rustc: str, tmpdir: Path) -> dict[str, Any]:
    src = tmpdir / "part_a.rs"
    src.write_text(
        NO_CORE_PRELUDE
        + """
#[rustc_dump_layout(size, align, backend_repr)]
pub type P_Ptr = *const u8;

#[rustc_dump_layout(size, align, backend_repr)]
pub type P_U64 = u64;

#[rustc_dump_layout(size, align, backend_repr)]
pub type P_F64 = f64;

#[rustc_dump_layout(size, align, backend_repr)]
pub type P_U128 = u128;

#[repr(C)]
#[rustc_dump_layout(size, align, backend_repr)]
pub struct C_U8_U64(pub u8, pub u64);

#[repr(C)]
#[rustc_dump_layout(size, align, backend_repr)]
pub struct C_U8_U128(pub u8, pub u128);

#[rustc_dump_layout(size, align, backend_repr)]
pub struct Pair_U8_U64(pub u8, pub u64);

#[rustc_dump_layout(size, align, backend_repr)]
pub struct Pair_U8_U128(pub u8, pub u128);
""",
        encoding="utf-8",
    )
    out: dict[str, Any] = {}
    for target in TARGETS_9:
        out_meta = tmpdir / f"part_a_{target}.rmeta"
        _rc, _stdout, stderr = run_cmd(
            [rustc, "--crate-type=lib", f"--target={target}", "--emit=metadata", str(src), "-o", str(out_meta)],
            str(tmpdir),
        )
        out[target] = parse_dump_layout_errors(stderr)
    return out


def probe_part_b(rustc: str, tmpdir: Path) -> dict[str, Any]:
    src = tmpdir / "part_b.rs"
    src.write_text(
        NO_CORE_PRELUDE
        + """
#[repr(simd)]
#[rustc_dump_layout(size, align, backend_repr)]
pub struct SimdF32x3([f32; 3]);

#[repr(simd)]
#[rustc_dump_layout(size, align, backend_repr)]
pub struct SimdF32x4([f32; 4]);

#[repr(simd)]
#[rustc_dump_layout(size, align, backend_repr)]
pub struct SimdF32x6([f32; 6]);

#[repr(simd, packed)]
#[rustc_dump_layout(size, align, backend_repr)]
pub struct SimdPackedF32x3([f32; 3]);

#[repr(simd, packed)]
#[rustc_dump_layout(size, align, backend_repr)]
pub struct SimdPackedF32x4([f32; 4]);

#[repr(simd, packed)]
#[rustc_dump_layout(size, align, backend_repr)]
pub struct SimdPackedF32x6([f32; 6]);

#[repr(simd, packed)]
#[rustc_dump_layout(size, align, backend_repr)]
pub struct SimdPackedU8x3([u8; 3]);
""",
        encoding="utf-8",
    )
    out_meta = tmpdir / "part_b.rmeta"
    _rc, _stdout, stderr = run_cmd(
        [rustc, "--crate-type=lib", "--target=x86_64-unknown-linux-gnu", "--emit=metadata", str(src), "-o", str(out_meta)],
        str(tmpdir),
    )
    return parse_dump_layout_errors(stderr)


def probe_part_c(rustc: str, tmpdir: Path) -> dict[str, Any]:
    src = tmpdir / "part_c.rs"
    exe = tmpdir / "part_c_bin"
    src.write_text(
        """#![allow(dead_code)]
use std::mem::{offset_of, size_of};

struct FixedArrBool([u8; 4], bool);
struct MaybeDstArrBool<T: ?Sized>([u8; 4], T);

struct FixedEdge(u32, u8, bool);
struct MaybeDstEdge<T: ?Sized>(u32, bool, T);

enum EnumFixedEdge {
    A(FixedEdge),
    B([u8; 5]),
}

enum EnumMaybeDstEdge {
    A(MaybeDstEdge<u8>),
    B([u8; 5]),
}

// Pure NicheBias::End suppression isolation: identical field types & source order,
// with a ZST tail T = () so tail-pinning does not obstruct bool/u8 ordering.
struct FixedPureNiche(u32, bool, u8, ());
struct MaybeDstPureNiche<T: ?Sized>(u32, bool, u8, T);

enum EnumFixedPureNiche {
    A(FixedPureNiche),
    B([u8; 5]),
}

enum EnumMaybeDstPureNiche {
    A(MaybeDstPureNiche<()>),
    B([u8; 5]),
}

struct NoBool(u8, [u8; 16]);
struct WithBool(bool, [u8; 16]);

struct EndBias {
    a: u16,
    b: bool,
    c: u8,
}

fn main() {
    println!(
        "FIXED_ARR_BOOL_OFF=({},{}) MAYBEDST_ARR_BOOL_OFF=({},{}) FIXED_EDGE_OFF=({},{},{}) MAYBEDST_EDGE_OFF=({},{},{}) ENUM_FIXED_SZ={} ENUM_MAYBEDST_SZ={} FIXED_PURE_OFF=({},{},{},{}) MAYBEDST_PURE_OFF=({},{},{},{}) ENUM_FIXED_PURE_SZ={} ENUM_MAYBEDST_PURE_SZ={} NO_BOOL_OFF=({},{}) WITH_BOOL_OFF=({},{}) END_BIAS_OFF=({},{})",
        offset_of!(FixedArrBool, 0),
        offset_of!(FixedArrBool, 1),
        offset_of!(MaybeDstArrBool<bool>, 0),
        offset_of!(MaybeDstArrBool<bool>, 1),
        offset_of!(FixedEdge, 0),
        offset_of!(FixedEdge, 1),
        offset_of!(FixedEdge, 2),
        offset_of!(MaybeDstEdge<u8>, 0),
        offset_of!(MaybeDstEdge<u8>, 1),
        offset_of!(MaybeDstEdge<u8>, 2),
        size_of::<EnumFixedEdge>(),
        size_of::<EnumMaybeDstEdge>(),
        offset_of!(FixedPureNiche, 0),
        offset_of!(FixedPureNiche, 1),
        offset_of!(FixedPureNiche, 2),
        offset_of!(FixedPureNiche, 3),
        offset_of!(MaybeDstPureNiche<()>, 0),
        offset_of!(MaybeDstPureNiche<()>, 1),
        offset_of!(MaybeDstPureNiche<()>, 2),
        offset_of!(MaybeDstPureNiche<()>, 3),
        size_of::<EnumFixedPureNiche>(),
        size_of::<EnumMaybeDstPureNiche>(),
        offset_of!(NoBool, 0),
        offset_of!(NoBool, 1),
        offset_of!(WithBool, 0),
        offset_of!(WithBool, 1),
        offset_of!(EndBias, b),
        offset_of!(EndBias, a),
    );
}
""",
        encoding="utf-8",
    )
    crc, _cstdout, cstderr = run_cmd([rustc, str(src), "-o", str(exe)], str(tmpdir))
    if crc != 0:
        return {"compile_rc": crc, "compile_stderr": cstderr}
    rc, stdout, stderr = run_cmd([str(exe)], str(tmpdir))
    return {"rc": rc, "runtime_offsets": stdout, "stderr": stderr}


def probe_part_d(rustc: str, tmpdir: Path) -> dict[str, Any]:
    src = tmpdir / "part_d.rs"
    src.write_text(
        NO_CORE_PRELUDE
        + """
pub enum Never {}

#[repr(align(16))]
pub struct Align16Zst;

#[rustc_dump_layout(size, align, backend_repr)]
pub enum Dead1Zst {
    Live(u8),
    Dead(Never),
}

#[repr(C)]
#[rustc_dump_layout(size, align, backend_repr)]
pub enum ReprCDead1Zst {
    Live(u8),
    Dead(Never),
}

#[rustc_dump_layout(size, align, backend_repr)]
pub enum DeadPayload64 {
    Live(u8),
    Dead(Never, [u8; 64]),
}

#[rustc_dump_layout(size, align, backend_repr)]
pub enum DeadAlign16Zst {
    Live(u8),
    Dead(Never, Align16Zst),
}
""",
        encoding="utf-8",
    )
    out_meta = tmpdir / "part_d.rmeta"
    _rc, _stdout, stderr = run_cmd(
        [rustc, "--crate-type=lib", "--target=x86_64-unknown-linux-gnu", "--emit=metadata", str(src), "-o", str(out_meta)],
        str(tmpdir),
    )
    return parse_dump_layout_errors(stderr)


def probe_part_e(rustc: str, tmpdir: Path) -> dict[str, Any]:
    src = tmpdir / "part_e.rs"
    src.write_text(
        """#![feature(rustc_attrs)]
#![allow(internal_features, non_camel_case_types, dead_code)]
use std::num::NonZeroU64;

#[rustc_dump_layout(size, align, backend_repr)]
pub struct RustWrapScalar(pub u64);

#[repr(C)]
#[rustc_dump_layout(size, align, backend_repr, homogeneous_aggregate)]
pub struct ReprCWrapScalar(pub u64);

#[repr(C)]
#[rustc_dump_layout(size, align, backend_repr)]
pub struct ReprCWrapTuplePair(pub (u64, u64));

#[repr(C)]
#[rustc_dump_layout(size, align, backend_repr)]
pub struct ReprCTwoScalars(pub u64, pub u64);

#[rustc_dump_layout(size, align, backend_repr)]
pub union CommonScalarUnionSamePrim {
    pub a: u64,
    pub b: NonZeroU64,
}

#[rustc_dump_layout(size, align, backend_repr)]
pub union CommonScalarUnionMixedSign {
    pub a: u64,
    pub b: i64,
}

#[repr(C)]
#[rustc_dump_layout(size, align, backend_repr)]
pub union ReprCUnion {
    pub a: u64,
    pub b: NonZeroU64,
}

#[repr(packed)]
#[rustc_dump_layout(size, align, backend_repr)]
pub union PackedScalarUnion {
    pub a: u64,
    pub b: NonZeroU64,
}
""",
        encoding="utf-8",
    )
    out_meta = tmpdir / "part_e.rmeta"
    _rc, _stdout, stderr = run_cmd(
        [
            rustc,
            "--edition=2021",
            "--crate-type=lib",
            "--target=x86_64-unknown-linux-gnu",
            "--emit=metadata",
            str(src),
            "-o",
            str(out_meta),
        ],
        str(tmpdir),
    )
    return parse_dump_layout_errors(stderr)


def extract_error_summary(stderr: str) -> tuple[list[str], str]:
    codes = sorted(set(re.findall(r"error\[(E\d{4})\]", stderr)))
    first_err = ""
    for line in stderr.splitlines():
        if line.startswith("error"):
            first_err = line
            break
    return codes, first_err


def extract_panic_or_err(stderr: str) -> str:
    picked = []
    for line in stderr.splitlines():
        if "panicked at" in line or "abi alignment" in line or line.startswith("error"):
            # Scrub thread IDs for deterministic output while keeping source line and message.
            cleaned = re.sub(r"thread 'rustc' \(\d+\)", "thread 'rustc' (<TID>)", line)
            picked.append(cleaned)
            if len(picked) >= 2:
                break
    return " | ".join(picked)


def probe_part_f(rustc: str, tmpdir: Path) -> dict[str, Any]:
    out: dict[str, Any] = {}

    diag_cases: dict[str, str] = {
        "same_struct_packed_and_align_e0587": """
#[repr(C, packed, align(8))]
pub struct S(pub u32);
""",
        "conflicting_packed_1_and_2_e0634": """
#[repr(C, packed(1), packed(2))]
pub struct S(pub u32);
""",
        "packed_enum_rejected": """
#[repr(packed)]
pub enum E { A(u8), B(u16) }
""",
        "align_outer_containing_packed_inner_ok": """
#[repr(C, packed)]
pub struct P(pub u32);
#[repr(C, align(8))]
pub struct A(pub P);
""",
        "transparent_with_align16_zst_e0690": """
#[repr(align(16))]
pub struct Az;
#[repr(transparent)]
pub struct T(pub u8, pub Az);
""",
        "transparent_all_zst_with_align16_ok": """
#[repr(align(16))]
pub struct Az;
#[repr(transparent)]
pub struct T(pub (), pub Az);
""",
        "concrete_packed_containing_align_default": """
#[repr(C, align(8))]
pub struct Inner(pub u32);
#[repr(C, packed)]
pub struct Outer(pub Inner);
""",
        "concrete_packed_containing_align_allow_lint": """
#![allow(unknown_lints, aligned_fields_in_packed)]
#[repr(C, align(8))]
pub struct Inner(pub u32);
#[repr(C, packed)]
pub struct Outer(pub Inner);
""",
    }

    for name, body in diag_cases.items():
        src = tmpdir / f"part_f_{name}.rs"
        rmeta = tmpdir / f"part_f_{name}.rmeta"
        src.write_text(body, encoding="utf-8")
        rc, _stdout, stderr = run_cmd(
            [rustc, "--crate-type=lib", "--emit=metadata", str(src), "-o", str(rmeta)],
            str(tmpdir),
        )
        codes, first_err = extract_error_summary(stderr)
        out[name] = {"rc": rc, "error_codes": codes, "first_error": first_err}

    # Layout debug inspection of GenericPacked<Inner> and ArrayPacked on x86_64
    layout_src = tmpdir / "part_f_layouts.rs"
    layout_src.write_text(
        NO_CORE_PRELUDE
        + """
pub trait Assoc { type Out; }
impl Assoc for () { type Out = Inner; }

#[repr(C, align(8))]
pub struct Inner(pub u32);

#[repr(C, packed)]
pub struct GenericPacked<T>(pub T);

#[repr(C, packed)]
pub struct TuplePacked(pub (Inner,));

#[repr(C, packed)]
pub struct AliasPacked(pub <() as Assoc>::Out);

#[repr(C, packed)]
pub struct ArrayPacked(pub [Inner; 1]);

#[repr(C)]
pub struct ReprCDirectOuter(pub Inner);

#[repr(C)]
pub struct ReprCArrayOuter(pub [Inner; 1]);

#[rustc_dump_layout(debug)]
pub type LayoutGenericPacked = GenericPacked<Inner>;

#[rustc_dump_layout(debug)]
pub type LayoutTuplePacked = TuplePacked;

#[rustc_dump_layout(debug)]
pub type LayoutAliasPacked = AliasPacked;

#[rustc_dump_layout(debug)]
pub type LayoutArrayPacked = ArrayPacked;

#[rustc_dump_layout(debug)]
pub type LayoutReprCDirectOuter = ReprCDirectOuter;

#[rustc_dump_layout(debug)]
pub type LayoutReprCArrayOuter = ReprCArrayOuter;
""",
        encoding="utf-8",
    )
    _rc, _stdout, lstderr = run_cmd(
        [
            rustc,
            "--crate-type=lib",
            "--target=x86_64-unknown-linux-gnu",
            "--emit=metadata",
            str(layout_src),
            "-o",
            str(tmpdir / "part_f_layouts.rmeta"),
        ],
        str(tmpdir),
    )
    layout_fields: dict[str, dict[str, str]] = {}
    for ty_name in (
        "GenericPacked<Inner>",
        "TuplePacked",
        "AliasPacked",
        "ArrayPacked",
        "ReprCDirectOuter",
        "ReprCArrayOuter",
    ):
        pat = re.compile(
            rf"layout_of\({re.escape(ty_name)}\)\s*=\s*Layout\s*\{{(.*?)\n\s*-->",
            re.DOTALL,
        )
        m = pat.search(lstderr)
        if m:
            block = m.group(1)
            size_m = re.search(r"size:\s*(Size\([^)]+\))", block)
            align_m = re.search(r"align:\s*(?:(?:AbiAlign|AbiAndPrefAlign)\s*\{\s*abi:\s*(Align\([^)]+\))|(Align\([^)]+\)))", block, re.DOTALL)
            mra_m = re.search(r"max_repr_align:\s*(None|Some\(\s*Align\([^)]+\),?\s*\))", block, re.DOTALL)
            mra_val = re.sub(r"\s+", " ", mra_m.group(1)).replace("( ", "(").replace(", )", ")").replace(" )", ")") if mra_m else ""
            layout_fields[ty_name] = {
                "size": size_m.group(1).strip() if size_m else "",
                "abi_align": (align_m.group(1) or align_m.group(2)).strip() if align_m else "",
                "max_repr_align": mra_val,
            }
    out["bypass_layout_fields_x86_64"] = layout_fields

    # Also compare i686-pc-windows-msvc LLVM IR ABI passing for ReprCDirectOuter vs ReprCArrayOuter
    arr_abi_src = tmpdir / "part_f_arr_abi.rs"
    arr_abi_ll = tmpdir / "part_f_arr_abi.ll"
    arr_abi_src.write_text(
        """#![forbid(unsafe_code)]
#![feature(no_core, lang_items)]
#![no_core]
#![allow(internal_features)]
#[lang = "pointee_sized"] pub trait PointeeSized {}
#[lang = "meta_sized"] pub trait MetaSized: PointeeSized {}
#[lang = "sized"] pub trait Sized: MetaSized {}
#[lang = "copy"] pub trait Copy {}
impl Copy for u32 {}
#[repr(C, align(8))] pub struct Inner(pub u32);
#[repr(C)] pub struct ReprCDirectOuter(pub Inner);
#[repr(C)] pub struct ReprCArrayOuter(pub [Inner; 1]);
pub extern "C" fn take_direct(_x: ReprCDirectOuter) {}
pub extern "C" fn take_array(_x: ReprCArrayOuter) {}
""",
        encoding="utf-8",
    )
    arc, _astdout, _astderr = run_cmd(
        [
            rustc,
            "--crate-type=lib",
            "--target=i686-pc-windows-msvc",
            "--emit=llvm-ir",
            str(arr_abi_src),
            "-o",
            str(arr_abi_ll),
        ],
        str(tmpdir),
    )
    ir_sigs: dict[str, str] = {}
    if arc == 0 and arr_abi_ll.exists():
        for line in arr_abi_ll.read_text(encoding="utf-8").splitlines():
            if line.startswith("define ") and "take_direct" in line:
                ir_sigs["take_direct"] = line
            elif line.startswith("define ") and "take_array" in line:
                ir_sigs["take_array"] = line
    out["i686_msvc_array_max_repr_align_drop_llvm_ir"] = {"rc": arc, "signatures": ir_sigs}

    # Live safe #![forbid(unsafe_code)] bypass compilation on x86_64 vs i686-pc-windows-msvc
    bypass_sources = {
        "generic_param_bypass": """#![forbid(unsafe_code)]
#![feature(no_core, lang_items)]
#![no_core]
#![allow(internal_features)]
#[lang = "pointee_sized"] pub trait PointeeSized {}
#[lang = "meta_sized"] pub trait MetaSized: PointeeSized {}
#[lang = "sized"] pub trait Sized: MetaSized {}
#[lang = "copy"] pub trait Copy {}
impl Copy for u32 {}

#[repr(C, align(8))]
pub struct Inner(pub u32);

#[repr(C, packed)]
pub struct GenericPacked<T>(pub T);

pub extern "C" fn take_packed(x: GenericPacked<Inner>) -> u32 {
    let v = x.0;
    v.0
}
""",
        "tuple_wrapper_bypass": """#![forbid(unsafe_code)]
#![feature(no_core, lang_items)]
#![no_core]
#![allow(internal_features)]
#[lang = "pointee_sized"] pub trait PointeeSized {}
#[lang = "meta_sized"] pub trait MetaSized: PointeeSized {}
#[lang = "sized"] pub trait Sized: MetaSized {}
#[lang = "copy"] pub trait Copy {}
impl Copy for u32 {}

#[repr(C, align(8))]
pub struct Inner(pub u32);

#[repr(C, packed)]
pub struct TuplePacked(pub (Inner,));

pub extern "C" fn take_packed(_x: TuplePacked) {}
""",
        "alias_wrapper_bypass": """#![forbid(unsafe_code)]
#![feature(no_core, lang_items)]
#![no_core]
#![allow(internal_features)]
#[lang = "pointee_sized"] pub trait PointeeSized {}
#[lang = "meta_sized"] pub trait MetaSized: PointeeSized {}
#[lang = "sized"] pub trait Sized: MetaSized {}
#[lang = "copy"] pub trait Copy {}
impl Copy for u32 {}

pub trait Assoc { type Out; }
impl Assoc for () { type Out = Inner; }

#[repr(C, align(8))]
pub struct Inner(pub u32);

#[repr(C, packed)]
pub struct AliasPacked(pub <() as Assoc>::Out);

pub extern "C" fn take_packed(_x: AliasPacked) {}
""",
        "array_wrapper_bypass": """#![forbid(unsafe_code)]
#![feature(no_core, lang_items)]
#![no_core]
#![allow(internal_features)]
#[lang = "pointee_sized"] pub trait PointeeSized {}
#[lang = "meta_sized"] pub trait MetaSized: PointeeSized {}
#[lang = "sized"] pub trait Sized: MetaSized {}
#[lang = "copy"] pub trait Copy {}
impl Copy for u32 {}

#[repr(C, align(8))]
pub struct Inner(pub u32);

#[repr(C, packed)]
pub struct ArrayPacked(pub [Inner; 1]);

pub extern "C" fn take_packed(_x: ArrayPacked) {}
""",
    }

    for name, code in bypass_sources.items():
        src = tmpdir / f"part_f_{name}.rs"
        src.write_text(code, encoding="utf-8")
        for target in ("x86_64-unknown-linux-gnu", "i686-pc-windows-msvc"):
            ll = tmpdir / f"part_f_{name}_{target}.ll"
            rc, _stdout, stderr = run_cmd(
                [rustc, "--crate-type=lib", f"--target={target}", "--emit=llvm-ir", str(src), "-o", str(ll)],
                str(tmpdir),
            )
            out[f"{name}__{target}"] = {
                "rc": rc,
                "panic_or_err": extract_panic_or_err(stderr),
            }

    return out


def probe_part_g(rustc: str, tmpdir: Path) -> dict[str, Any]:
    src = tmpdir / "part_g.rs"
    src.write_text(
        """#![allow(dead_code)]
use std::mem::{offset_of, size_of};

struct RustFive(u64, u64, u64, u64, u64);

#[repr(C)]
struct ReprCFive(u64, u64, u64, u64, u64);

struct AllZst((), [u8; 0], [(); 16]);
enum SingleZstEnum { Only((), [u8; 0]) }
enum ZeroVariantEnum {}

fn main() {
    println!(
        "RUST=({},{},{},{},{}) REPRC=({},{},{},{},{}) ALLZST_SZ={} SINGLE_ZST_ENUM_SZ={} ZERO_VAR_ENUM_SZ={}",
        offset_of!(RustFive, 0),
        offset_of!(RustFive, 1),
        offset_of!(RustFive, 2),
        offset_of!(RustFive, 3),
        offset_of!(RustFive, 4),
        offset_of!(ReprCFive, 0),
        offset_of!(ReprCFive, 1),
        offset_of!(ReprCFive, 2),
        offset_of!(ReprCFive, 3),
        offset_of!(ReprCFive, 4),
        size_of::<AllZst>(),
        size_of::<SingleZstEnum>(),
        size_of::<ZeroVariantEnum>(),
    );
}
""",
        encoding="utf-8",
    )
    configs = [
        ("default_no_randomize", []),
        ("seed_1_run1", ["-Z", "randomize-layout", "-Z", "layout-seed=1"]),
        ("seed_1_run2", ["-Z", "randomize-layout", "-Z", "layout-seed=1"]),
        ("seed_2", ["-Z", "randomize-layout", "-Z", "layout-seed=2"]),
        ("seed_999", ["-Z", "randomize-layout", "-Z", "layout-seed=999"]),
    ]
    out: dict[str, Any] = {}
    for label, flags in configs:
        exe = tmpdir / f"part_g_{label}"
        crc, _cstdout, cstderr = run_cmd([rustc, *flags, str(src), "-o", str(exe)], str(tmpdir))
        if crc != 0:
            out[label] = {"compile_rc": crc, "compile_stderr": cstderr}
            continue
        rc, stdout, _stderr = run_cmd([str(exe)], str(tmpdir))
        out[label] = {"rc": rc, "stdout": stdout}
    return out


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rustc", default=None, help="Path to nightly rustc binary")
    parser.add_argument("--out", default=None, help="Optional JSON output file path")
    args = parser.parse_args()

    rustc = find_rustc(args.rustc)
    with tempfile.TemporaryDirectory(prefix="rustc_abi_layout_probe_") as td:
        tmpdir = Path(td)
        _vrc, ver_out, _verr = run_cmd([rustc, "-Vv"], td)
        payload = {
            "observed_at_utc": dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
            "rustc_version": ver_out,
            "part_a_multi_target_primitive_and_pair_matrix": probe_part_a(rustc, tmpdir),
            "part_b_simd_packed_pow2_vs_nonpow2": probe_part_b(rustc, tmpdir),
            "part_c_maybe_unsized_tail_pinning_and_niche_bias": probe_part_c(rustc, tmpdir),
            "part_d_uninhabited_non_1zst_variant_reservation": probe_part_d(rustc, tmpdir),
            "part_e_repr_c_scalar_vs_scalarpair_and_union_opt": probe_part_e(rustc, tmpdir),
            "part_f_packed_align_bypass_and_x86_win32_ice": probe_part_f(rustc, tmpdir),
            "part_g_randomize_layout_seed_and_zst_invariance": probe_part_g(rustc, tmpdir),
        }

    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.out:
        Path(args.out).write_text(rendered, encoding="utf-8")
    else:
        sys.stdout.write(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
