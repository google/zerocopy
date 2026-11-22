#!/usr/bin/env python3
"""Real rustc (legacy + -Z next-solver=globally) and Miri probe for rustc_transmute.

Reproduces:
  1. The 38-case core TransmuteFrom<Src, ASSUME> matrix across legacy and next-solver.
  2. Extended 14-case diagnostic matrix covering NonZero (FieldsShape::Primitive),
     Option<bool> niche layouts, MaybeUninit<T>, char, &mut Cell<u8>, IfAny-as-IfAll
     flattening, and Answer::or(If(c), Yes) variant-order sensitivity.
  3. Miri union-transmute execution (prefix truncation + trailing-uninit extension).
  4. rust-lang/rust#164247 soundness repro (&Cell<u8> -> &u8 under Assume::NOTHING)
     at -O0, -O2, Miri Stacked Borrows, and Miri Tree Borrows, plus boundary probes
     for &mut Cell<u8> -> &u8, &(Cell<u8>, u8) -> &u8, and &(u8, Cell<u8>) -> &u8.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


COMMON_HEADER = """#![feature(transmutability)]
#![allow(dead_code, unused_imports, unused_variables)]
use core::cell::{Cell, UnsafeCell};
use core::mem::{Assume, MaybeUninit, TransmuteFrom};
use core::num::NonZero;

#[repr(u8)]
enum ZeroOrOne { Zero = 0, One = 1 }

#[repr(u8)]
enum TwoOnly { Two = 2 }

#[repr(C, align(2))]
struct PaddedAlign2(u8);

#[repr(C)]
struct HasPad { a: u8, b: u16 }

#[repr(C)]
struct PlainU8(u8);

enum Void {}

#[repr(C)]
struct NodeA<'a> { next: &'a NodeA<'a>, val: u8 }

#[repr(C)]
struct NodeB<'a> { next: &'a NodeB<'a>, val: u8 }

#[repr(C)]
union DstRefUnion<'a> {
    good: &'a u8,
    bad: &'a Cell<u8>,
}

#[repr(C, u8)]
enum SrcMixRefFirst<'a> {
    RefArm(&'a u8) = 0,
    ByteArm(u8) = 1,
}

#[repr(C, u8)]
enum DstMixRefFirst<'a> {
    RefArm(&'a Cell<u8>) = 0,
    ByteArm(u8) = 1,
}

#[repr(C, u8)]
enum SrcMixByteFirst<'a> {
    ByteArm(u8) = 0,
    RefArm(&'a u8) = 1,
}

#[repr(C, u8)]
enum DstMixByteFirst<'a> {
    ByteArm(u8) = 0,
    RefArm(&'a Cell<u8>) = 1,
}

#[repr(C)]
struct CellFirst(Cell<u8>, u8);

#[repr(C)]
struct CellSecond(u8, Cell<u8>);
"""

CORE_38_CASES: list[tuple[str, str]] = [
    ("bool_to_u8_nothing",
     "pub fn f(x: bool) -> u8 { unsafe { <u8 as TransmuteFrom<bool, { Assume::NOTHING }>>::transmute(x) } }"),
    ("u8_to_bool_nothing",
     "pub fn f(x: u8) -> bool { unsafe { <bool as TransmuteFrom<u8, { Assume::NOTHING }>>::transmute(x) } }"),
    ("u8_to_bool_validity",
     "pub fn f(x: u8) -> bool { unsafe { <bool as TransmuteFrom<u8, { Assume::VALIDITY }>>::transmute(x) } }"),
    ("two_only_to_bool_validity",
     "pub fn f(x: TwoOnly) -> bool { unsafe { <bool as TransmuteFrom<TwoOnly, { Assume::VALIDITY }>>::transmute(x) } }"),
    ("zero_or_one_to_bool_nothing",
     "pub fn f(x: ZeroOrOne) -> bool { unsafe { <bool as TransmuteFrom<ZeroOrOne, { Assume::NOTHING }>>::transmute(x) } }"),
    ("bool_to_zero_or_one_nothing",
     "pub fn f(x: bool) -> ZeroOrOne { unsafe { <ZeroOrOne as TransmuteFrom<bool, { Assume::NOTHING }>>::transmute(x) } }"),
    ("bool_to_zero_or_one_safety",
     "pub fn f(x: bool) -> ZeroOrOne { unsafe { <ZeroOrOne as TransmuteFrom<bool, { Assume::SAFETY }>>::transmute(x) } }"),
    ("u32_to_u8_prefix_trunc_nothing",
     "pub fn f(x: u32) -> u8 { unsafe { <u8 as TransmuteFrom<u32, { Assume::NOTHING }>>::transmute(x) } }"),
    ("u8_to_u16_too_big_nothing",
     "pub fn f(x: u8) -> u16 { unsafe { <u16 as TransmuteFrom<u8, { Assume::NOTHING }>>::transmute(x) } }"),
    ("u8_to_padded_align2_safety",
     "pub fn f(x: u8) -> PaddedAlign2 { unsafe { <PaddedAlign2 as TransmuteFrom<u8, { Assume::SAFETY }>>::transmute(x) } }"),
    ("u8_to_padded_align2_nothing",
     "pub fn f(x: u8) -> PaddedAlign2 { unsafe { <PaddedAlign2 as TransmuteFrom<u8, { Assume::NOTHING }>>::transmute(x) } }"),
    ("has_pad_to_u8_arr4_nothing",
     "pub fn f(x: HasPad) -> [u8; 4] { unsafe { <[u8; 4] as TransmuteFrom<HasPad, { Assume::NOTHING }>>::transmute(x) } }"),
    ("has_pad_to_mu_arr4_nothing",
     "pub fn f(x: HasPad) -> [MaybeUninit<u8>; 4] { unsafe { <[MaybeUninit<u8>; 4] as TransmuteFrom<HasPad, { Assume::NOTHING }>>::transmute(x) } }"),
    ("has_pad_to_mu_arr4_safety",
     "pub fn f(x: HasPad) -> [MaybeUninit<u8>; 4] { unsafe { <[MaybeUninit<u8>; 4] as TransmuteFrom<HasPad, { Assume::SAFETY }>>::transmute(x) } }"),
    ("u8_to_plain_struct_nothing",
     "pub fn f(x: u8) -> PlainU8 { unsafe { <PlainU8 as TransmuteFrom<u8, { Assume::NOTHING }>>::transmute(x) } }"),
    ("u8_to_plain_struct_safety",
     "pub fn f(x: u8) -> PlainU8 { unsafe { <PlainU8 as TransmuteFrom<u8, { Assume::SAFETY }>>::transmute(x) } }"),
    ("opt_nonzero_u8_to_u8_nothing",
     "pub fn f(x: Option<NonZero<u8>>) -> u8 { unsafe { <u8 as TransmuteFrom<Option<NonZero<u8>>, { Assume::NOTHING }>>::transmute(x) } }"),
    ("u8_to_opt_nonzero_u8_safety",
     "pub fn f(x: u8) -> Option<NonZero<u8>> { unsafe { <Option<NonZero<u8>> as TransmuteFrom<u8, { Assume::SAFETY }>>::transmute(x) } }"),
    ("void_to_u128_nothing",
     "pub fn f(x: Void) -> u128 { unsafe { <u128 as TransmuteFrom<Void, { Assume::NOTHING }>>::transmute(x) } }"),
    ("u8_to_void_all_assumes",
     "pub fn f(x: u8) -> Void { unsafe { <Void as TransmuteFrom<u8, { Assume { alignment: true, lifetimes: true, safety: true, validity: true } }>>::transmute(x) } }"),
    ("ref_bool_to_ref_u8_nothing",
     "pub fn f<'a>(x: &'a bool) -> &'a u8 { unsafe { <&'a u8 as TransmuteFrom<&'a bool, { Assume::NOTHING }>>::transmute(x) } }"),
    ("ref_u8_to_ref_mut_u8_nothing",
     "pub fn f<'a>(x: &'a u8) -> &'a mut u8 { unsafe { <&'a mut u8 as TransmuteFrom<&'a u8, { Assume::NOTHING }>>::transmute(x) } }"),
    ("ref_mut_u8_to_ref_u8_nothing",
     "pub fn f<'a>(x: &'a mut u8) -> &'a u8 { unsafe { <&'a u8 as TransmuteFrom<&'a mut u8, { Assume::NOTHING }>>::transmute(x) } }"),
    ("ref_mut_u32_to_ref_mut_u8_nothing",
     "pub fn f<'a>(x: &'a mut u32) -> &'a mut u8 { unsafe { <&'a mut u8 as TransmuteFrom<&'a mut u32, { Assume::NOTHING }>>::transmute(x) } }"),
    ("ref_u32_to_ref_u8_nothing",
     "pub fn f<'a>(x: &'a u32) -> &'a u8 { unsafe { <&'a u8 as TransmuteFrom<&'a u32, { Assume::NOTHING }>>::transmute(x) } }"),
    ("ref_u8_arr2_to_ref_u16_nothing",
     "pub fn f<'a>(x: &'a [u8; 2]) -> &'a u16 { unsafe { <&'a u16 as TransmuteFrom<&'a [u8; 2], { Assume::NOTHING }>>::transmute(x) } }"),
    ("ref_u8_arr2_to_ref_u16_align",
     "pub fn f<'a>(x: &'a [u8; 2]) -> &'a u16 { unsafe { <&'a u16 as TransmuteFrom<&'a [u8; 2], { Assume::ALIGNMENT }>>::transmute(x) } }"),
    ("ref_static_to_ref_a_nothing",
     "pub fn f<'a>(x: &'static u8) -> &'a u8 { unsafe { <&'a u8 as TransmuteFrom<&'static u8, { Assume::NOTHING }>>::transmute(x) } }"),
    ("ref_a_to_ref_static_nothing",
     "pub fn f<'a>(x: &'a u8) -> &'static u8 { unsafe { <&'static u8 as TransmuteFrom<&'a u8, { Assume::NOTHING }>>::transmute(x) } }"),
    ("ref_a_to_ref_static_lifetimes",
     "pub fn f<'a>(x: &'a u8) -> &'static u8 { unsafe { <&'static u8 as TransmuteFrom<&'a u8, { Assume::LIFETIMES }>>::transmute(x) } }"),
    ("ref_u8_to_ref_cell_u8_safety",
     "pub fn f<'a>(x: &'a u8) -> &'a Cell<u8> { unsafe { <&'a Cell<u8> as TransmuteFrom<&'a u8, { Assume::SAFETY }>>::transmute(x) } }"),
    ("ref_cell_u8_to_ref_u8_nothing",
     "pub fn f<'a>(x: &'a Cell<u8>) -> &'a u8 { unsafe { <&'a u8 as TransmuteFrom<&'a Cell<u8>, { Assume::NOTHING }>>::transmute(x) } }"),
    ("ref_cell_u8_to_ref_cell_u8_safety",
     "pub fn f<'a>(x: &'a Cell<u8>) -> &'a Cell<u8> { unsafe { <&'a Cell<u8> as TransmuteFrom<&'a Cell<u8>, { Assume::SAFETY }>>::transmute(x) } }"),
    ("ref_mut_cell_u8_to_ref_u8_nothing",
     "pub fn f<'a>(x: &'a mut Cell<u8>) -> &'a u8 { unsafe { <&'a u8 as TransmuteFrom<&'a mut Cell<u8>, { Assume::NOTHING }>>::transmute(x) } }"),
    ("ref_mut_u8_to_ref_cell_u8_safety",
     "pub fn f<'a>(x: &'a mut u8) -> &'a Cell<u8> { unsafe { <&'a Cell<u8> as TransmuteFrom<&'a mut u8, { Assume::SAFETY }>>::transmute(x) } }"),
    ("ref_unsafecell_u8_to_ref_u8_nothing",
     "pub fn f<'a>(x: &'a UnsafeCell<u8>) -> &'a u8 { unsafe { <&'a u8 as TransmuteFrom<&'a UnsafeCell<u8>, { Assume::NOTHING }>>::transmute(x) } }"),
    ("ref_mut_cell_u8_to_ref_mut_u8_safety",
     "pub fn f<'a>(x: &'a mut Cell<u8>) -> &'a mut u8 { unsafe { <&'a mut u8 as TransmuteFrom<&'a mut Cell<u8>, { Assume::SAFETY }>>::transmute(x) } }"),
    ("coinductive_node_a_to_node_b_safety",
     "pub fn f<'a>(x: &'a NodeA<'a>) -> &'a NodeB<'a> { unsafe { <&'a NodeB<'a> as TransmuteFrom<&'a NodeA<'a>, { Assume::SAFETY }>>::transmute(x) } }"),
]

EXTENDED_14_CASES: list[tuple[str, str]] = [
    ("nonzero_u8_to_u8_nothing",
     "pub fn f(x: NonZero<u8>) -> u8 { unsafe { <u8 as TransmuteFrom<NonZero<u8>, { Assume::NOTHING }>>::transmute(x) } }"),
    ("opt_bool_to_u8_nothing",
     "pub fn f(x: Option<bool>) -> u8 { unsafe { <u8 as TransmuteFrom<Option<bool>, { Assume::NOTHING }>>::transmute(x) } }"),
    ("u8_to_opt_bool_safety_validity",
     "pub fn f(x: u8) -> Option<bool> { unsafe { <Option<bool> as TransmuteFrom<u8, { Assume::SAFETY.and(Assume::VALIDITY) }>>::transmute(x) } }"),
    ("u8_to_mu_u8_nothing",
     "pub fn f(x: u8) -> MaybeUninit<u8> { unsafe { <MaybeUninit<u8> as TransmuteFrom<u8, { Assume::NOTHING }>>::transmute(x) } }"),
    ("u8_to_mu_u8_safety",
     "pub fn f(x: u8) -> MaybeUninit<u8> { unsafe { <MaybeUninit<u8> as TransmuteFrom<u8, { Assume::SAFETY }>>::transmute(x) } }"),
    ("mu_u8_to_u8_nothing",
     "pub fn f(x: MaybeUninit<u8>) -> u8 { unsafe { <u8 as TransmuteFrom<MaybeUninit<u8>, { Assume::NOTHING }>>::transmute(x) } }"),
    ("mu_u8_to_u8_validity",
     "pub fn f(x: MaybeUninit<u8>) -> u8 { unsafe { <u8 as TransmuteFrom<MaybeUninit<u8>, { Assume::VALIDITY }>>::transmute(x) } }"),
    ("char_to_u32_nothing",
     "pub fn f(x: char) -> u32 { unsafe { <u32 as TransmuteFrom<char, { Assume::NOTHING }>>::transmute(x) } }"),
    ("u32_to_char_nothing",
     "pub fn f(x: u32) -> char { unsafe { <char as TransmuteFrom<u32, { Assume::NOTHING }>>::transmute(x) } }"),
    ("u32_to_char_validity",
     "pub fn f(x: u32) -> char { unsafe { <char as TransmuteFrom<u32, { Assume::VALIDITY }>>::transmute(x) } }"),
    ("ref_mut_u8_to_ref_mut_cell_u8_safety",
     "pub fn f<'a>(x: &'a mut u8) -> &'a mut Cell<u8> { unsafe { <&'a mut Cell<u8> as TransmuteFrom<&'a mut u8, { Assume::SAFETY }>>::transmute(x) } }"),
    ("ifany_as_ifall_ref_union_safety",
     "pub fn f<'a>(x: &'a u8) -> DstRefUnion<'a> { unsafe { <DstRefUnion<'a> as TransmuteFrom<&'a u8, { Assume::SAFETY }>>::transmute(x) } }"),
    ("answer_or_ref_first_safety_validity",
     "pub fn f<'a>(x: SrcMixRefFirst<'a>) -> DstMixRefFirst<'a> { unsafe { <DstMixRefFirst<'a> as TransmuteFrom<SrcMixRefFirst<'a>, { Assume::SAFETY.and(Assume::VALIDITY) }>>::transmute(x) } }"),
    ("answer_or_byte_first_safety_validity",
     "pub fn f<'a>(x: SrcMixByteFirst<'a>) -> DstMixByteFirst<'a> { unsafe { <DstMixByteFirst<'a> as TransmuteFrom<SrcMixByteFirst<'a>, { Assume::SAFETY.and(Assume::VALIDITY) }>>::transmute(x) } }"),
]


def scrub_text(text: str, tmpdir: str) -> str:
    """Remove temporary and user-directory absolute paths from captured stderr/stdout."""
    home = os.path.expanduser("~")
    out = text.replace(tmpdir, "<TMPDIR>")
    if home:
        out = out.replace(home, "<USER_HOME>")
    out = re.sub(r"/(?:Users|[^/\s]+/local/[^/\s]+/[^/\s]+)/[^/\s]+", "<USER_HOME>", out)
    return out


def extract_error_summary(stderr: str, tmpdir: str) -> list[str]:
    lines = []
    for raw in scrub_text(stderr, tmpdir).splitlines():
        s = raw.strip()
        if (
            s.startswith("error")
            or s.startswith("= help:")
            or s.startswith("= note:")
            or "may carry safety invariants" in s
            or "is uninhabited" in s
            or "minimum alignment" in s
            or "requires that" in s
            or "Freeze" in s
            or "not yet supported" in s
            or "bit-incompatible" in s
            or "too big" in s
        ):
            lines.append(s)
    return lines[:8]


def run_rustc_case(
    tmpdir: Path, name: str, snippet: str, extra_args: list[str]
) -> tuple[bool, list[str]]:
    case_dir = tmpdir / name
    case_dir.mkdir(parents=True, exist_ok=True)
    src_path = case_dir / "lib.rs"
    src_path.write_text(COMMON_HEADER + "\n" + snippet + "\n", encoding="utf-8")
    out_path = case_dir / ("lib_next.rmeta" if extra_args else "lib_legacy.rmeta")
    cmd = [
        "rustc",
        "--edition=2024",
        "--crate-type=lib",
        "--emit=metadata",
        "-o",
        str(out_path),
        *extra_args,
        str(src_path),
    ]
    proc = subprocess.run(cmd, capture_output=True, text=True)
    ok = proc.returncode == 0
    return ok, ([] if ok else extract_error_summary(proc.stderr, str(tmpdir)))


def run_miri_crate(
    tmpdir: Path, crate_name: str, main_rs: str, miriflags: str = ""
) -> dict[str, Any]:
    cdir = tmpdir / crate_name
    (cdir / "src").mkdir(parents=True, exist_ok=True)
    (cdir / "Cargo.toml").write_text(
        f'[package]\nname = "{crate_name}"\nversion = "0.1.0"\nedition = "2024"\n',
        encoding="utf-8",
    )
    (cdir / "src" / "main.rs").write_text(main_rs, encoding="utf-8")
    env = os.environ.copy()
    if miriflags:
        env["MIRIFLAGS"] = miriflags
    else:
        env.pop("MIRIFLAGS", None)
    proc = subprocess.run(
        ["cargo", "miri", "run", "--offline"],
        cwd=str(cdir),
        env=env,
        capture_output=True,
        text=True,
    )
    stderr_clean = scrub_text(proc.stderr, str(tmpdir))
    ub_lines = [
        line.strip()
        for line in stderr_clean.splitlines()
        if any(
            tok in line
            for tok in (
                "Undefined Behavior",
                "SharedReadOnly",
                "Frozen",
                "Disabled",
                "Stacked Borrows",
                "Tree Borrows",
                "was created by",
            )
        )
    ][:8]
    return {
        "rc": proc.returncode,
        "stdout": proc.stdout.strip(),
        "ub_lines": ub_lines,
        "stderr_tail": stderr_clean.splitlines()[-6:],
    }


def capture_llvm_ir_sig(tmpdir: Path, name: str, main_rs: str, fn_marker: str) -> list[str]:
    src = tmpdir / f"{name}_ir.rs"
    ll = tmpdir / f"{name}_ir.ll"
    src.write_text(main_rs, encoding="utf-8")
    proc = subprocess.run(
        [
            "rustc",
            "--edition=2024",
            "-Copt-level=2",
            "--emit=llvm-ir",
            str(src),
            "-o",
            str(ll),
        ],
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0 or not ll.exists():
        return []
    hits = []
    for line in ll.read_text(encoding="utf-8").splitlines():
        if line.startswith("define ") and fn_marker in line:
            hits.append(line.strip())
    return hits


def run_native_binary(tmpdir: Path, name: str, main_rs: str, opt: str) -> dict[str, Any]:
    src = tmpdir / f"{name}_{opt}.rs"
    exe = tmpdir / f"{name}_{opt}.bin"
    src.write_text(main_rs, encoding="utf-8")
    cproc = subprocess.run(
        ["rustc", "--edition=2024", f"-Copt-level={opt}", str(src), "-o", str(exe)],
        capture_output=True,
        text=True,
    )
    if cproc.returncode != 0:
        return {
            "compile_rc": cproc.returncode,
            "run_rc": None,
            "stdout": "",
            "stderr": scrub_text(cproc.stderr, str(tmpdir)),
        }
    rproc = subprocess.run([str(exe)], capture_output=True, text=True)
    return {
        "compile_rc": 0,
        "run_rc": rproc.returncode,
        "stdout": rproc.stdout.strip(),
    }


def main() -> int:
    rustc_ver = subprocess.check_output(["rustc", "--version", "--verbose"], text=True).strip()
    miri_ver = subprocess.check_output(["cargo", "miri", "--version"], text=True).strip()

    with tempfile.TemporaryDirectory(prefix="rustc_transmute_probe_") as td:
        tmpdir = Path(td)

        core_results: dict[str, Any] = {}
        for name, snippet in CORE_38_CASES:
            leg_ok, leg_err = run_rustc_case(tmpdir, f"core_{name}", snippet, [])
            nxt_ok, nxt_err = run_rustc_case(
                tmpdir, f"core_{name}", snippet, ["-Z", "next-solver=globally"]
            )
            core_results[name] = {
                "legacy_ok": leg_ok,
                "next_solver_ok": nxt_ok,
                "solver_divergence": leg_ok != nxt_ok,
                "legacy_errors": leg_err,
                "next_errors": nxt_err,
            }

        extended_results: dict[str, Any] = {}
        for name, snippet in EXTENDED_14_CASES:
            leg_ok, leg_err = run_rustc_case(tmpdir, f"ext_{name}", snippet, [])
            nxt_ok, nxt_err = run_rustc_case(
                tmpdir, f"ext_{name}", snippet, ["-Z", "next-solver=globally"]
            )
            extended_results[name] = {
                "legacy_ok": leg_ok,
                "next_solver_ok": nxt_ok,
                "solver_divergence": leg_ok != nxt_ok,
                "legacy_errors": leg_err,
                "next_errors": nxt_err,
            }

        miri_union_src = """#![feature(transmutability)]
use core::mem::{Assume, TransmuteFrom};

#[repr(C, align(2))]
struct PaddedAlign2(u8);

fn main() {
    let ext: PaddedAlign2 = unsafe {
        <PaddedAlign2 as TransmuteFrom<u8, { Assume::SAFETY }>>::transmute(66u8)
    };
    let trunc: u8 = unsafe {
        <u8 as TransmuteFrom<u32, { Assume::NOTHING }>>::transmute(0x11223344u32)
    };
    println!("EXT={} TRUNC={:#04x}", ext.0, trunc);
}
"""
        miri_union_exec = run_miri_crate(tmpdir, "tx_miri_union", miri_union_src)

        repro_164247_src = """#![feature(transmutability)]
use core::cell::Cell;
use core::mem::{Assume, TransmuteFrom};

#[inline(never)]
fn observe_alias(cell: &Cell<u8>, ro: &u8) -> (u8, u8, u8) {
    let before = *ro;
    cell.set(99);
    let after = *ro;
    (before, after, cell.get())
}

fn main() {
    let cell = Cell::new(7u8);
    let ro: &u8 = unsafe {
        <&u8 as TransmuteFrom<&Cell<u8>, { Assume::NOTHING }>>::transmute(&cell)
    };
    let (b, a, c) = observe_alias(&cell, ro);
    println!("BEFORE={b} AFTER={a} CELL={c}");
}
"""
        repro_164247_inline_src = """#![feature(transmutability)]
use core::cell::Cell;
use core::mem::{Assume, TransmuteFrom};

fn main() {
    let cell = Cell::new(7u8);
    let ro: &u8 = unsafe {
        <&u8 as TransmuteFrom<&Cell<u8>, { Assume::NOTHING }>>::transmute(&cell)
    };
    let before = *ro;
    cell.set(99);
    let after = *ro;
    println!("BEFORE={before} AFTER={after} CELL={}", cell.get());
}
"""
        issue_164247 = {
            "native_O0": run_native_binary(tmpdir, "repro164247", repro_164247_src, "0"),
            "native_O2": run_native_binary(tmpdir, "repro164247", repro_164247_src, "2"),
            "llvm_ir_O2_observe_alias": capture_llvm_ir_sig(
                tmpdir, "repro164247", repro_164247_src, "observe_alias"
            ),
            "miri_stacked_borrows_protected": run_miri_crate(
                tmpdir, "repro164247_sb", repro_164247_src, ""
            ),
            "miri_tree_borrows_protected": run_miri_crate(
                tmpdir, "repro164247_tb", repro_164247_src, "-Zmiri-tree-borrows"
            ),
            "miri_stacked_borrows_unprotected": run_miri_crate(
                tmpdir, "repro164247_inline_sb", repro_164247_inline_src, ""
            ),
            "miri_tree_borrows_unprotected": run_miri_crate(
                tmpdir, "repro164247_inline_tb", repro_164247_inline_src, "-Zmiri-tree-borrows"
            ),
        }

        mut_cell_to_ref_src = """#![feature(transmutability)]
use core::cell::Cell;
use core::mem::{Assume, TransmuteFrom};

fn main() {
    let mut cell = Cell::new(42u8);
    let ro: &u8 = unsafe {
        <&u8 as TransmuteFrom<&mut Cell<u8>, { Assume::NOTHING }>>::transmute(&mut cell)
    };
    println!("MUT_CELL_TO_REF={}", *ro);
}
"""
        cell_first_prefix_src = """#![feature(transmutability)]
use core::cell::Cell;
use core::mem::{Assume, TransmuteFrom};

#[repr(C)]
struct CellFirst(Cell<u8>, u8);

fn main() {
    let s = CellFirst(Cell::new(7), 11);
    let ro: &u8 = unsafe {
        <&u8 as TransmuteFrom<&CellFirst, { Assume::NOTHING }>>::transmute(&s)
    };
    let b = *ro;
    s.0.set(99);
    let a = *ro;
    println!("CELL_FIRST B={b} A={a}");
}
"""
        cell_second_prefix_src = """#![feature(transmutability)]
use core::cell::Cell;
use core::mem::{Assume, TransmuteFrom};

#[repr(C)]
struct CellSecond(u8, Cell<u8>);

fn main() {
    let s = CellSecond(7, Cell::new(11));
    let ro: &u8 = unsafe {
        <&u8 as TransmuteFrom<&CellSecond, { Assume::NOTHING }>>::transmute(&s)
    };
    let b = *ro;
    s.1.set(99);
    let a = *ro;
    println!("CELL_SECOND B={b} A={a} CELL={}", s.1.get());
}
"""
        ref_aliasing_boundaries = {
            "mut_cell_to_ref_sb": run_miri_crate(tmpdir, "mut_cell_sb", mut_cell_to_ref_src, ""),
            "mut_cell_to_ref_tb": run_miri_crate(
                tmpdir, "mut_cell_tb", mut_cell_to_ref_src, "-Zmiri-tree-borrows"
            ),
            "cell_first_prefix_sb": run_miri_crate(
                tmpdir, "cell_first_sb", cell_first_prefix_src, ""
            ),
            "cell_first_prefix_tb": run_miri_crate(
                tmpdir, "cell_first_tb", cell_first_prefix_src, "-Zmiri-tree-borrows"
            ),
            "cell_second_prefix_sb": run_miri_crate(
                tmpdir, "cell_second_sb", cell_second_prefix_src, ""
            ),
            "cell_second_prefix_tb": run_miri_crate(
                tmpdir, "cell_second_tb", cell_second_prefix_src, "-Zmiri-tree-borrows"
            ),
        }

    result = {
        "rustc_version": rustc_ver,
        "miri_version": miri_ver,
        "core_case_count": len(core_results),
        "core_solver_divergences": sum(
            1 for v in core_results.values() if v["solver_divergence"]
        ),
        "core_cases": core_results,
        "extended_case_count": len(extended_results),
        "extended_solver_divergences": sum(
            1 for v in extended_results.values() if v["solver_divergence"]
        ),
        "extended_cases": extended_results,
        "miri_union_transmute_exec": miri_union_exec,
        "issue_164247_cell_to_ref_soundness_repro": issue_164247,
        "ref_aliasing_boundary_probes": ref_aliasing_boundaries,
    }

    out_path = Path(sys.argv[1]) if len(sys.argv) > 1 else None
    rendered = json.dumps(result, indent=2, ensure_ascii=True) + "\n"
    if out_path is not None:
        out_path.write_text(rendered, encoding="utf-8")
    else:
        sys.stdout.write(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
