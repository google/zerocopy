#!/usr/bin/env python3
"""Executable reproducer suite for rustc improper_ctypes / improper_ctypes_definitions
blind spots, empty/ZST C vs C++ vs Rust layout divergence, invalid C-to-Rust bool/enum
discriminants under LLVM optimization, recursion-limit fail-open, and variadic call-site
type-checking gaps.

Uses only the Python 3.10+ standard library and cleans up all temporary build artifacts
via tempfile.TemporaryDirectory().
"""

import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

CASES_STABLE = [
    # --- Empty / ZST structs ---
    (
        "repr_c_empty_struct_decl",
        "#[repr(C)] pub struct Empty {}\nunsafe extern \"C\" { pub fn f(x: Empty); }",
        [],
    ),
    (
        "repr_c_only_unit_decl",
        "#[repr(C)] pub struct OnlyUnit(());\nunsafe extern \"C\" { pub fn f(x: OnlyUnit); }",
        [],
    ),
    (
        "repr_c_with_unit_decl",
        "#[repr(C)] pub struct WithUnit { pub a: u32, pub u: (), pub b: u32 }\nunsafe extern \"C\" { pub fn f(x: WithUnit); }",
        [],
    ),
    (
        "repr_c_only_zero_array_decl",
        "#[repr(C)] pub struct OnlyZeroArr([u8; 0]);\nunsafe extern \"C\" { pub fn f(x: OnlyZeroArr); }",
        [],
    ),
    (
        "repr_c_with_zero_array_decl",
        "#[repr(C)] pub struct WithZeroArr { pub a: u32, pub z: [u8; 0], pub b: u32 }\nunsafe extern \"C\" { pub fn f(x: WithZeroArr); }",
        [],
    ),
    # --- #[repr(transparent)] ---
    (
        "repr_transparent_only_unit_decl",
        "#[repr(transparent)] pub struct TUnit(());\nunsafe extern \"C\" { pub fn f(x: TUnit); }",
        [],
    ),
    (
        "repr_transparent_only_phantom_decl",
        "use core::marker::PhantomData;\n#[repr(transparent)] pub struct TPh(PhantomData<u8>);\nunsafe extern \"C\" { pub fn f(x: TPh); }",
        [],
    ),
    (
        "repr_transparent_overaligned_zst_decl",
        "#[repr(transparent)] pub struct TAlignZst([u32; 0]);\nunsafe extern \"C\" { pub fn f(x: TAlignZst); }",
        [],
    ),
    (
        "repr_transparent_with_non_ffi_1zst_decl",
        "pub struct RustZst;\n#[repr(transparent)] pub struct TWithZst(pub RustZst, pub u32);\nunsafe extern \"C\" { pub fn f(x: TWithZst); }",
        [],
    ),
    (
        "repr_transparent_wrapping_string_decl",
        "#[repr(transparent)] pub struct TString(pub String);\nunsafe extern \"C\" { pub fn f(x: TString); }",
        [],
    ),
    # --- Uninhabited types ---
    (
        "never_return_decl",
        "unsafe extern \"C\" { pub fn f() -> !; }",
        [],
    ),
    (
        "never_arg_decl",
        "unsafe extern \"C\" { pub fn f(x: !); }",
        [],
    ),
    (
        "never_static_decl",
        "unsafe extern \"C\" { pub static X: !; }",
        [],
    ),
    (
        "infallible_arg_and_ret_decl",
        "use core::convert::Infallible;\nunsafe extern \"C\" { pub fn f(x: Infallible) -> Infallible; }",
        [],
    ),
    (
        "repr_c_struct_with_never_decl",
        "#[repr(C)] pub struct S { pub a: u32, pub n: ! }\nunsafe extern \"C\" { pub fn f(x: S); }",
        [],
    ),
    # --- Niche-optimized Option / Result / custom enums ---
    (
        "option_nonnull_decl",
        "use core::ptr::NonNull;\nunsafe extern \"C\" { pub fn f(x: Option<NonNull<u8>>) -> Option<NonNull<u8>>; }",
        [],
    ),
    (
        "option_extern_c_fn_decl",
        "unsafe extern \"C\" { pub fn f(cb: Option<extern \"C\" fn(i32) -> i32>); }",
        [],
    ),
    (
        "option_ref_decl",
        "unsafe extern \"C\" { pub fn f(p: Option<&u32>); }",
        [],
    ),
    (
        "option_nonzero_u32_decl",
        "use core::num::NonZeroU32;\nunsafe extern \"C\" { pub fn f(x: Option<NonZeroU32>); }",
        [],
    ),
    (
        "result_nonnull_unit_decl",
        "use core::ptr::NonNull;\nunsafe extern \"C\" { pub fn f(x: Result<NonNull<u8>, ()>); }",
        [],
    ),
    (
        "custom_option_like_enum_decl",
        "use core::ptr::NonNull;\npub enum MyOpt { Some(NonNull<u8>), None }\nunsafe extern \"C\" { pub fn f(x: MyOpt); }",
        [],
    ),
    (
        "option_bool_decl",
        "unsafe extern \"C\" { pub fn f(x: Option<bool>); }",
        [],
    ),
    (
        "option_cell_ref_decl",
        "use core::cell::Cell;\nunsafe extern \"C\" { pub fn f(x: Option<Cell<&'static u8>>); }",
        [],
    ),
    (
        "option_box_decl",
        "unsafe extern \"C\" { pub fn f(x: Option<Box<u32>>); }",
        [],
    ),
    (
        "option_box_def",
        "pub extern \"C\" fn f(_x: Option<Box<u32>>) {}",
        [],
    ),
    # --- Value-validity / discriminant / char / bool ---
    (
        "bool_decl",
        "unsafe extern \"C\" { pub fn f(x: bool) -> bool; }",
        [],
    ),
    (
        "char_decl",
        "unsafe extern \"C\" { pub fn f(x: char) -> char; }",
        [],
    ),
    (
        "repr_c_enum_decl",
        "#[repr(C)] pub enum E { A = 0, B = 1 }\nunsafe extern \"C\" { pub fn f(x: E) -> E; }",
        [],
    ),
    (
        "repr_c_non_exhaustive_unit_enum_decl",
        "#[repr(C)] #[non_exhaustive] pub enum E { A = 0, B = 1 }\nunsafe extern \"C\" { pub fn f(x: E); }",
        [],
    ),
    (
        "repr_c_non_exhaustive_data_enum_decl",
        "#[repr(C)] #[non_exhaustive] pub enum E { A(u32), B(u64) }\nunsafe extern \"C\" { pub fn f(x: E); }",
        [],
    ),
    # --- Packed / Align ---
    (
        "repr_c_packed_decl",
        "#[repr(C, packed)] pub struct P { pub a: u8, pub b: u64 }\nunsafe extern \"C\" { pub fn f(x: P); }",
        [],
    ),
    (
        "repr_c_align16_decl",
        "#[repr(C, align(16))] pub struct A { pub a: u8 }\nunsafe extern \"C\" { pub fn f(x: A); }",
        [],
    ),
    (
        "repr_rust_packed_decl",
        "#[repr(packed)] pub struct P { pub a: u8, pub b: u64 }\nunsafe extern \"C\" { pub fn f(x: P); }",
        [],
    ),
    # --- Indirection & decl/def/fnptr asymmetries ---
    (
        "ref_mut_u32_decl",
        "unsafe extern \"C\" { pub fn f(x: &mut u32, y: &u32); }",
        [],
    ),
    (
        "raw_ptr_string_decl",
        "unsafe extern \"C\" { pub fn f(p: *const String); }",
        [],
    ),
    (
        "raw_ptr_string_def",
        "pub extern \"C\" fn f(_p: *const String) {}",
        [],
    ),
    (
        "ref_string_def",
        "pub extern \"C\" fn f(_p: &String) {}",
        [],
    ),
    (
        "box_u32_decl",
        "unsafe extern \"C\" { pub fn f(p: Box<u32>); }",
        [],
    ),
    (
        "box_string_decl",
        "unsafe extern \"C\" { pub fn f(p: Box<String>); }",
        [],
    ),
    (
        "box_string_def",
        "pub extern \"C\" fn f(_p: Box<String>) {}",
        [],
    ),
    (
        "fnptr_raw_ptr_string_in_decl",
        "unsafe extern \"C\" { pub fn f(cb: extern \"C\" fn(*const String)); }",
        [],
    ),
    (
        "generic_extern_c_def_with_string",
        "pub extern \"C\" fn gen_f<T>(_x: T) {}\npub fn call_it(s: String) { gen_f(s); }",
        [],
    ),
    # --- Std wrapper types & atomics & 128-bit ints ---
    (
        "unsafe_cell_u32_decl",
        "use core::cell::UnsafeCell;\nunsafe extern \"C\" { pub fn f(x: UnsafeCell<u32>); }",
        [],
    ),
    (
        "maybe_uninit_u32_decl",
        "use core::mem::MaybeUninit;\nunsafe extern \"C\" { pub fn f(x: MaybeUninit<u32>); }",
        [],
    ),
    (
        "manually_drop_u32_decl",
        "use core::mem::ManuallyDrop;\nunsafe extern \"C\" { pub fn f(x: ManuallyDrop<u32>); }",
        [],
    ),
    (
        "atomic_u64_decl",
        "use core::sync::atomic::AtomicU64;\nunsafe extern \"C\" { pub fn f(x: AtomicU64); }",
        [],
    ),
    (
        "i128_u128_decl",
        "unsafe extern \"C\" { pub fn f(a: i128, b: u128) -> u128; }",
        [],
    ),
    # --- FAMs & opaque patterns ---
    (
        "fam_dst_slice_ptr_decl",
        "#[repr(C)] pub struct Fam { pub len: usize, pub data: [u8] }\nunsafe extern \"C\" { pub fn f(p: *const Fam); }",
        [],
    ),
    (
        "fam_zero_len_array_ptr_decl",
        "#[repr(C)] pub struct Fam { pub len: usize, pub data: [u8; 0] }\nunsafe extern \"C\" { pub fn f(p: *const Fam); }",
        [],
    ),
    (
        "nomicon_opaque_struct_ptr_decl",
        "use core::marker::{PhantomData, PhantomPinned};\n#[repr(C)] pub struct Opaque { _data: [u8; 0], _marker: PhantomData<(*mut u8, PhantomPinned)> }\nunsafe extern \"C\" { pub fn f(p: *mut Opaque); }",
        [],
    ),
    # --- Recursion limit fail-open ---
    (
        "recursion_limit_fail_open_decl",
        "#![recursion_limit = \"4\"]\nunsafe extern \"C\" { pub fn f(p: *const *const *const *const *const String); }",
        [],
    ),
    # --- Variadic call-site non-FFI types ---
    (
        "variadic_call_non_ffi_types",
        "unsafe extern \"C\" { pub fn v(n: i32, ...); }\npub struct RustStruct { a: u8, b: u16 }\npub unsafe fn caller(s: String, r: RustStruct, c: char) {\n    unsafe { v(3, s, r, c, (1u8, 2u16)); }\n}",
        [],
    ),
    (
        "variadic_call_f32_error",
        "unsafe extern \"C\" { pub fn v(n: i32, ...); }\npub unsafe fn caller(x: f32) { unsafe { v(1, x); } }",
        [],
    ),
]

CASES_NIGHTLY = [
    (
        "extern_type_ptr_and_ref_decl",
        "#![feature(extern_types)]\nunsafe extern \"C\" { pub type Opaque; pub fn f(p: *mut Opaque, r: &Opaque); }",
        [],
    ),
    (
        "f16_f128_decl",
        "#![feature(f16, f128)]\nunsafe extern \"C\" { pub fn f(a: f16, b: f128) -> f128; }",
        [],
    ),
    (
        "repr_simd_with_simd_ffi_decl",
        "#![feature(repr_simd, simd_ffi)]\n#[repr(simd)] pub struct F32x4(pub [f32; 4]);\nunsafe extern \"C\" { pub fn f(a: F32x4) -> F32x4; }",
        [],
    ),
]


def rustc_cmd(toolchain):
    if toolchain:
        return ["rustc", f"+{toolchain}"]
    return ["rustc"]


def run_lint_case(toolchain, name, code, extra_args, tmpdir):
    src = Path(tmpdir) / f"{name}.rs"
    src.write_text("#![allow(dead_code, internal_features)]\n" + code + "\n")
    out = Path(tmpdir) / f"lib{name}.rmeta"
    cmd = rustc_cmd(toolchain) + [
        "--edition=2024",
        "--crate-type=lib",
        "--emit=metadata",
        "-D",
        "improper-ctypes",
        "-D",
        "improper-ctypes-definitions",
        "-o",
        str(out),
        str(src),
    ] + extra_args
    r = subprocess.run(cmd, capture_output=True, text=True)
    if r.returncode == 0:
        return {"verdict": "ACCEPTED_SILENTLY", "summary": ""}
    err_lines = [
        line.strip()
        for line in r.stderr.splitlines()
        if line.startswith("error") or "= note:" in line
    ]
    kind = "HARD_ERROR"
    if "improper-ctypes" in r.stderr or "improper_ctypes" in r.stderr or "is not FFI-safe" in r.stderr:
        kind = "IMPROPER_CTYPES_LINT"
    elif "E0617" in r.stderr:
        kind = "HARD_ERROR_E0617"
    elif "E0658" in r.stderr:
        kind = "HARD_ERROR_E0658_UNSTABLE"
    return {"verdict": kind, "summary": " | ".join(err_lines[:3])}


def run_empty_struct_live_probe(tmpdir, toolchain):
    """Demonstrates live ABI/layout corruption: Rust #[repr(C)] ZST field vs GCC C vs G++ C++."""
    c_src = Path(tmpdir) / "empty_c.c"
    c_src.write_text(r"""
#include <stddef.h>
#include <stdint.h>
struct Empty {};
struct WithEmpty { uint32_t a; struct Empty e; uint32_t b; };
size_t c_sizeof_empty(void) { return sizeof(struct Empty); }
size_t c_sizeof_with(void) { return sizeof(struct WithEmpty); }
size_t c_offsetof_b(void) { return offsetof(struct WithEmpty, b); }
uint64_t c_read_ab(struct WithEmpty w) { return ((uint64_t)w.a << 32) | w.b; }
""")
    cpp_src = Path(tmpdir) / "empty_cpp.cpp"
    cpp_src.write_text(r"""
#include <cstddef>
#include <cstdint>
struct Empty {};
struct WithEmpty { uint32_t a; Empty e; uint32_t b; };
struct WithNoUnique { uint32_t a; [[no_unique_address]] Empty e; uint32_t b; };
extern "C" {
size_t cpp_sizeof_empty() { return sizeof(Empty); }
size_t cpp_sizeof_with() { return sizeof(WithEmpty); }
size_t cpp_offsetof_b() { return offsetof(WithEmpty, b); }
size_t cpp_sizeof_no_unique() { return sizeof(WithNoUnique); }
size_t cpp_offsetof_no_unique_b() { return offsetof(WithNoUnique, b); }
uint64_t cpp_read_ab(WithEmpty w) { return (static_cast<uint64_t>(w.a) << 32) | w.b; }
}
""")
    rs_src = Path(tmpdir) / "empty_main.rs"
    rs_src.write_text(r"""
use core::mem::{offset_of, size_of};

#[repr(C)]
#[derive(Copy, Clone)]
pub struct EmptyZst([u8; 0]);

#[repr(C)]
#[derive(Copy, Clone)]
pub struct WithEmpty {
    pub a: u32,
    pub e: EmptyZst,
    pub b: u32,
}

unsafe extern "C" {
    fn c_sizeof_empty() -> usize;
    fn c_sizeof_with() -> usize;
    fn c_offsetof_b() -> usize;
    fn c_read_ab(w: WithEmpty) -> u64;
    fn cpp_sizeof_empty() -> usize;
    fn cpp_sizeof_with() -> usize;
    fn cpp_offsetof_b() -> usize;
    fn cpp_sizeof_no_unique() -> usize;
    fn cpp_offsetof_no_unique_b() -> usize;
    fn cpp_read_ab(w: WithEmpty) -> u64;
}

fn main() {
    let w = WithEmpty { a: 0x11223344, e: EmptyZst([]), b: 0x55667788 };
    unsafe {
        let c_val = c_read_ab(w);
        let cpp_val = cpp_read_ab(w);
        println!("rust_sizeof_empty={}", size_of::<EmptyZst>());
        println!("rust_sizeof_with={}", size_of::<WithEmpty>());
        println!("rust_offsetof_b={}", offset_of!(WithEmpty, b));
        println!("c_sizeof_empty={}", c_sizeof_empty());
        println!("c_sizeof_with={}", c_sizeof_with());
        println!("c_offsetof_b={}", c_offsetof_b());
        println!("cpp_sizeof_empty={}", cpp_sizeof_empty());
        println!("cpp_sizeof_with={}", cpp_sizeof_with());
        println!("cpp_offsetof_b={}", cpp_offsetof_b());
        println!("cpp_sizeof_no_unique={}", cpp_sizeof_no_unique());
        println!("cpp_offsetof_no_unique_b={}", cpp_offsetof_no_unique_b());
        println!("c_read_ab=0x{:016x}", c_val);
        println!("cpp_read_ab_corrupted=0x{:016x}", cpp_val);
    }
}
""")
    # Check GCC pedantic diagnostic for C23 empty struct
    ped = subprocess.run(
        ["gcc", "-std=c23", "-Wpedantic", "-c", str(c_src), "-o", str(Path(tmpdir) / "empty_c.o")],
        capture_output=True,
        text=True,
        check=True,
    )
    subprocess.run(
        ["g++", "-std=c++23", "-O2", "-c", str(cpp_src), "-o", str(Path(tmpdir) / "empty_cpp.o")],
        check=True,
    )
    exe = Path(tmpdir) / "empty_main"
    subprocess.run(
        rustc_cmd(toolchain)
        + [
            "--edition=2024",
            "-D",
            "improper-ctypes",
            "-C",
            "opt-level=2",
            str(rs_src),
            "-C",
            f"link-arg={Path(tmpdir) / 'empty_c.o'}",
            "-C",
            f"link-arg={Path(tmpdir) / 'empty_cpp.o'}",
            "-o",
            str(exe),
        ],
        check=True,
    )
    out = subprocess.check_output([str(exe)], text=True)
    res = {"gcc_c23_pedantic_stderr": ped.stderr.strip()}
    for line in out.strip().splitlines():
        k, v = line.split("=", 1)
        res[k] = v
    return res


def run_invalid_bool_enum_live_probe(tmpdir, toolchain):
    """Demonstrates LLVM IR noundef/range assumptions + live miscompilation when C returns invalid bool (2) or enum (99)."""
    c_src = Path(tmpdir) / "bad_val.c"
    c_src.write_text(r"""
#include <stdint.h>
uint8_t c_return_bool_two(void) { return 2; }
uint32_t c_return_enum_99(void) { return 99; }
""")
    rs_src = Path(tmpdir) / "bad_val.rs"
    rs_src.write_text(r"""
#![allow(dead_code)]
#[repr(C)]
#[derive(Copy, Clone)]
pub enum Color {
    Red = 0,
    Green = 1,
}

unsafe extern "C" {
    fn c_return_bool_two() -> bool;
    fn c_return_enum_99() -> Color;
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn classify_bool(b: bool) -> u8 {
    match b {
        false => 0,
        true => 1,
    }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn classify_color(c: Color) -> u32 {
    match c {
        Color::Red => 10,
        Color::Green => 20,
    }
}

fn main() {
    unsafe {
        let b = c_return_bool_two();
        // Rust's LLVM lowering emits `i1` / `range(i8 0, 2)` and zero-extends b directly in classify_bool!
        let classified_b = classify_bool(b);
        let raw_b = b as u8;
        let not_b = (!b) as u8;
        let c = c_return_enum_99();
        let classified_c = classify_color(c);
        println!("classified_bool={}", classified_b);
        println!("bool_as_u8={}", raw_b);
        println!("not_bool_as_u8={}", not_b);
        println!("classified_color={}", classified_c);
    }
}
""")
    subprocess.run(
        ["gcc", "-O2", "-c", str(c_src), "-o", str(Path(tmpdir) / "bad_val.o")],
        check=True,
    )
    ll_path = Path(tmpdir) / "bad_val.ll"
    subprocess.run(
        rustc_cmd(toolchain)
        + [
            "--edition=2024",
            "-D",
            "improper-ctypes",
            "-D",
            "improper-ctypes-definitions",
            "-C",
            "opt-level=3",
            "--emit=llvm-ir=" + str(ll_path),
            "--crate-type=lib",
            str(rs_src),
        ],
        check=True,
    )
    ll_text = ll_path.read_text()
    sigs = [
        line.strip()
        for line in ll_text.splitlines()
        if any(tok in line for tok in ["classify_bool", "classify_color", "c_return_bool_two", "c_return_enum_99"])
        and (line.startswith("define") or line.startswith("declare"))
    ]
    exe = Path(tmpdir) / "bad_val_main"
    subprocess.run(
        rustc_cmd(toolchain)
        + [
            "--edition=2024",
            "-D",
            "improper-ctypes",
            "-D",
            "improper-ctypes-definitions",
            "-C",
            "opt-level=3",
            str(rs_src),
            "-C",
            f"link-arg={Path(tmpdir) / 'bad_val.o'}",
            "-o",
            str(exe),
        ],
        check=True,
    )
    out = subprocess.check_output([str(exe)], text=True)
    res = {"llvm_ir_sigs": sigs}
    for line in out.strip().splitlines():
        k, v = line.split("=", 1)
        res[k] = v
    return res


def main():
    # Detect available rustup toolchains matching our study
    preferred = ["nightly-2026-06-01", "1.99.1", "nightly"]
    available = []
    if shutil.which("rustup"):
        installed = subprocess.check_output(["rustup", "toolchain", "list"], text=True)
        for tc in preferred:
            if any(line.startswith(tc) for line in installed.splitlines()):
                available.append(tc)
    if not available:
        available = [None]

    report = {"toolchains": {}, "lint_matrix": {}, "live_empty_struct": {}, "live_invalid_bool_enum": {}}
    with tempfile.TemporaryDirectory() as tmpdir:
        for tc in available:
            label = tc or "default"
            ver = subprocess.check_output(rustc_cmd(tc) + ["-Vv"], text=True).strip()
            report["toolchains"][label] = ver.splitlines()[0]
            tc_dir = Path(tmpdir) / label.replace(".", "_")
            tc_dir.mkdir(parents=True, exist_ok=True)
            is_nightly = "nightly" in ver
            cases = list(CASES_STABLE) + (list(CASES_NIGHTLY) if is_nightly else [])
            for name, code, args in cases:
                res = run_lint_case(tc, name, code, args, tc_dir)
                report["lint_matrix"].setdefault(name, {})[label] = res

        primary_tc = "1.99.1" if "1.99.1" in available else available[0]
        live_dir = Path(tmpdir) / "live"
        live_dir.mkdir()
        report["live_empty_struct"] = run_empty_struct_live_probe(live_dir, primary_tc)
        report["live_invalid_bool_enum"] = run_invalid_bool_enum_live_probe(live_dir, primary_tc)

    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
