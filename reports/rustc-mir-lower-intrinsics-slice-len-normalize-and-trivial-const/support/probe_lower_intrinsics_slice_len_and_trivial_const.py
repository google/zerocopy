#!/usr/bin/env python3
"""Live rustc & Miri differential probe for LowerIntrinsics, LowerSliceLenCalls,
PostAnalysisNormalize, and trivial_const.

Executes real rustc (and Miri when available) against standalone Rust specimens
in an ephemeral temporary directory and records exact MIR dumps, pass-pipeline
traces, exit codes, and diagnostics to JSON.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import Any


def _find_tool(name: str) -> str:
    found = shutil.which(name)
    if found:
        return found
    cargo_bin = Path.home() / ".cargo" / "bin" / name
    if cargo_bin.is_file():
        return str(cargo_bin)
    raise FileNotFoundError(f"required tool not found on PATH or ~/.cargo/bin: {name}")


def _sanitize_text(text: str, tmp_dir: Path) -> str:
    home_str = str(Path.home())
    cleaned = text.replace(str(tmp_dir), "<TMPDIR>")
    cleaned = cleaned.replace(home_str, "<HOME>")
    cleaned = re.sub(r"/rustc-dev/[0-9a-f]{40}/", "<RUSTC_SRC>/", cleaned)
    cleaned = re.sub(r"thread 'rustc' \(\d+\)", "thread 'rustc' (<TID>)", cleaned)
    return cleaned


def _run(
    cmd: list[str],
    cwd: Path,
    tmp_dir: Path,
    env: dict[str, str] | None = None,
) -> dict[str, Any]:
    proc = subprocess.run(
        cmd,
        cwd=str(cwd),
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        check=False,
    )
    return {
        "rc": proc.returncode,
        "stdout": _sanitize_text(proc.stdout, tmp_dir),
        "stderr": _sanitize_text(proc.stderr, tmp_dir),
    }


def _dump_files_for_item(dump_dir: Path, item_marker: str) -> list[str]:
    if not dump_dir.is_dir():
        return []
    return sorted(
        p.name
        for p in dump_dir.iterdir()
        if p.is_file() and f".{item_marker}." in p.name and p.name.endswith(".mir")
    )


def _read_first_matching_dump(
    dump_dir: Path, item_marker: str, suffix: str, tmp_dir: Path
) -> str | None:
    if not dump_dir.is_dir():
        return None
    matches = sorted(
        p
        for p in dump_dir.iterdir()
        if p.is_file() and f".{item_marker}." in p.name and p.name.endswith(suffix)
    )
    if not matches:
        return None
    return _sanitize_text(matches[0].read_text(encoding="utf-8"), tmp_dir)


TRIVIAL_CONST_OK_SRC = r"""
#![crate_type = "lib"]
#![feature(trivial_bounds, generic_const_items, type_alias_impl_trait)]
#![allow(dead_code, trivial_bounds, incomplete_features)]

pub const TRIV_A: usize = 42;
pub const TRIV_B: usize = TRIV_A;
pub const TRIV_C_CHAIN2: usize = TRIV_B;
pub const NON_TRIV_ARITH: usize = 40 + 2;

pub struct GenHolder<T>(pub core::marker::PhantomData<T>);
impl<T> GenHolder<T> {
    pub const ASSOC_TRIV: usize = 7;
}
pub const NON_TRIV_GENERIC_REF: usize = GenHolder::<u8>::ASSOC_TRIV;

pub type HiddenCopy = impl Copy;
#[define_opaque(HiddenCopy)]
pub const NON_TRIV_OPAQUE_DEF: HiddenCopy = 99usize;

pub const IMPOSSIBLE_CLAUSE_TRIV: usize = 7
where
    String: Copy;

pub fn use_consts() -> (usize, usize, usize, usize, usize) {
    (TRIV_A, TRIV_B, TRIV_C_CHAIN2, NON_TRIV_ARITH, NON_TRIV_GENERIC_REF)
}

pub fn read_impossible_triv() -> usize
where
    String: Copy,
{
    IMPOSSIBLE_CLAUSE_TRIV
}
"""

TRIVIAL_CONST_IMPOSSIBLE_NON_TRIV_SRC = r"""
#![crate_type = "lib"]
#![feature(trivial_bounds, generic_const_items)]
#![allow(dead_code, trivial_bounds, incomplete_features)]

pub const IMPOSSIBLE_CLAUSE_NON_TRIV: usize = 3 + 4
where
    String: Copy;
"""

LOWER_INTRINSICS_SRC = r"""
#![crate_type = "lib"]
#![feature(core_intrinsics, ptr_metadata, ub_checks)]
#![allow(internal_features, dead_code, unused_variables)]

use core::cmp::Ordering;
use core::intrinsics;

pub enum Void {}

pub struct UninhabitedSized(pub u64, pub Void);

pub unsafe fn probe_unreachable() -> ! {
    unsafe { intrinsics::unreachable() }
}

pub fn probe_runtime_checks() -> (bool, bool) {
    (intrinsics::ub_checks(), intrinsics::overflow_checks())
}

pub fn probe_forget(x: u64) {
    intrinsics::forget(x)
}

pub unsafe fn probe_copy_nonoverlapping(src: *const u32, dst: *mut u32, count: usize) {
    unsafe { intrinsics::copy_nonoverlapping(src, dst, count) }
}

pub unsafe fn probe_assume(b: bool) {
    unsafe { intrinsics::assume(b) }
}

pub unsafe fn probe_binops(
    a: u32,
    b: u32,
    s: u32,
) -> (u32, u32, u32, Ordering, u32, u32, u32, u32, u32, u32, u32) {
    unsafe {
        (
            intrinsics::wrapping_add(a, b),
            intrinsics::wrapping_sub(a, b),
            intrinsics::wrapping_mul(a, b),
            intrinsics::three_way_compare(a, b),
            intrinsics::unchecked_add(a, b),
            intrinsics::unchecked_sub(a, b),
            intrinsics::unchecked_mul(a, b),
            intrinsics::unchecked_div(a, b),
            intrinsics::unchecked_rem(a, b),
            intrinsics::unchecked_shl(a, s),
            intrinsics::unchecked_shr(a, s),
        )
    }
}

pub fn probe_with_overflow(a: u32, b: u32) -> ((u32, bool), (u32, bool), (u32, bool)) {
    (
        intrinsics::add_with_overflow(a, b),
        intrinsics::sub_with_overflow(a, b),
        intrinsics::mul_with_overflow(a, b),
    )
}

pub unsafe fn probe_read_via_copy_u32(p: *const u32) -> u32 {
    unsafe { intrinsics::read_via_copy(p) }
}

pub unsafe fn probe_read_via_copy_void(p: *const Void) -> Void {
    unsafe { intrinsics::read_via_copy(p) }
}

pub unsafe fn probe_read_via_copy_uninhabited_sized(p: *const UninhabitedSized) -> UninhabitedSized {
    unsafe { intrinsics::read_via_copy(p) }
}

#[repr(u8)]
pub enum Tag {
    A = 1,
    B = 7,
}

pub fn probe_discriminant_value(x: &Tag) -> u8 {
    intrinsics::discriminant_value(x)
}

pub unsafe fn probe_offset(p: *const u32, delta: isize) -> *const u32 {
    unsafe { intrinsics::offset(p, delta) }
}

pub unsafe fn probe_slice_get_unchecked_all4<'a>(
    cp: *const [u32],
    mp: *mut [u32],
    sr: &'a [u32],
    mr: &'a mut [u32],
    idx: usize,
) -> (*const u32, *mut u32, &'a u32, &'a mut u32) {
    unsafe {
        let a: *const u32 = intrinsics::slice_get_unchecked(cp, idx);
        let b: *mut u32 = intrinsics::slice_get_unchecked(mp, idx);
        let c: &'a u32 = intrinsics::slice_get_unchecked(sr, idx);
        let d: &'a mut u32 = intrinsics::slice_get_unchecked(mr, idx);
        (a, b, c, d)
    }
}

pub unsafe fn probe_transmute_u32_f32(x: u32) -> f32 {
    unsafe { intrinsics::transmute(x) }
}

pub unsafe fn probe_transmute_to_void(x: ()) -> Void {
    unsafe { intrinsics::transmute(x) }
}

pub unsafe fn probe_transmute_unchecked_to_void(x: ()) -> Void {
    unsafe { intrinsics::transmute_unchecked(x) }
}

pub fn probe_raw_ptr_roundtrip(p: *const u32, len: usize) -> usize {
    let sp: *const [u32] = intrinsics::aggregate_raw_ptr(p, len);
    intrinsics::ptr_metadata(sp)
}

pub fn probe_unlowered_ctpop(x: u32) -> u32 {
    intrinsics::ctpop(x)
}
"""

SLICE_LEN_SRC = r"""
#![crate_type = "lib"]
#![allow(dead_code)]

pub struct DropGuard(pub u32);
impl Drop for DropGuard {
    fn drop(&mut self) {
        core::hint::black_box(self.0);
    }
}

pub fn probe_slice_len(s: &[u32]) -> usize {
    s.len()
}

pub fn probe_slice_len_mut_reborrow(s: &mut [u32]) -> usize {
    s[0] = 1;
    s.len()
}

pub fn probe_slice_len_fn_ptr(s: &[u32]) -> usize {
    let f: fn(&[u32]) -> usize = <[u32]>::len;
    f(s)
}

pub fn probe_slice_len_sole_unwind_cleanup(s: &[u32], _g: DropGuard) -> usize {
    s.len()
}
"""

POST_ANALYSIS_NORMALIZE_SRC = r"""
#![crate_type = "lib"]
#![feature(type_alias_impl_trait)]
#![allow(dead_code)]

#[derive(Copy, Clone)]
pub struct Pair(pub u32, pub u64);

pub type OpaquePair = impl Copy;

#[define_opaque(OpaquePair)]
pub fn make_opaque_pair(x: u32, y: u64) -> OpaquePair {
    let p: Pair = Pair(x, y);
    p
}

#[define_opaque(OpaquePair)]
pub fn project_opaque_pair(p: OpaquePair) -> u64 {
    let Pair(_, y) = p;
    y
}

pub trait Assoc {
    type Out;
    fn project(self) -> Self::Out;
}

impl Assoc for u32 {
    type Out = u64;
    fn project(self) -> Self::Out {
        let annotated: <u32 as Assoc>::Out = self as u64;
        annotated
    }
}

pub fn probe_assoc_norm(x: u32) -> <u32 as Assoc>::Out {
    let tmp: <u32 as Assoc>::Out = x.project();
    tmp
}
"""

CUSTOM_MIR_INDIRECT_SLICE_GET_UNCHECKED_SRC = r"""
#![crate_type = "lib"]
#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features, dead_code)]

use core::intrinsics::mir::*;
use core::intrinsics::slice_get_unchecked;

#[custom_mir(dialect = "runtime", phase = "initial")]
pub unsafe fn ice_indirect_slice_get_unchecked(pp: &*const [u32], idx: usize) -> *const u32 {
    mir! {
        {
            Call(RET = slice_get_unchecked(*pp, idx), ReturnTo(bb1), UnwindUnreachable())
        }
        bb1 = {
            Return()
        }
    }
}
"""

ORDINARY_RUST_CONST_IDX_SLICE_GET_UNCHECKED_SRC = r"""
#![crate_type = "lib"]
#![feature(core_intrinsics)]
#![allow(internal_features, dead_code)]

pub unsafe fn ice_const_idx_slice_get_unchecked(sp: *const [u32]) -> *const u32 {
    unsafe { core::intrinsics::slice_get_unchecked(sp, 2) }
}
"""

CUSTOM_MIR_FIELD_PROJ_SLICE_GET_UNCHECKED_SRC = r"""
#![crate_type = "lib"]
#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features, dead_code)]

use core::intrinsics::mir::*;
use core::intrinsics::slice_get_unchecked;

#[custom_mir(dialect = "runtime", phase = "initial")]
pub unsafe fn field_proj_slice_get_unchecked(
    pair: (*const [u32], usize),
    idx: usize,
) -> *const u32 {
    mir! {
        {
            Call(RET = slice_get_unchecked(pair.0, idx), ReturnTo(bb1), UnwindUnreachable())
        }
        bb1 = {
            Return()
        }
    }
}
"""

CUSTOM_MIR_DIRECT_SLICE_GET_UNCHECKED_SRC = r"""
#![crate_type = "lib"]
#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features, dead_code)]

use core::intrinsics::mir::*;
use core::intrinsics::slice_get_unchecked;

#[custom_mir(dialect = "runtime", phase = "initial")]
pub unsafe fn ok_direct_slice_get_unchecked(p: *const [u32], idx: usize) -> *const u32 {
    mir! {
        {
            Call(RET = slice_get_unchecked(p, idx), ReturnTo(bb1), UnwindUnreachable())
        }
        bb1 = {
            Return()
        }
    }
}
"""

CUSTOM_MIR_INDIRECT_READ_VIA_COPY_SRC = r"""
#![crate_type = "lib"]
#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features, dead_code)]

use core::intrinsics::mir::*;
use core::intrinsics::read_via_copy;

#[custom_mir(dialect = "runtime", phase = "initial")]
pub unsafe fn ice_indirect_read_via_copy(pp: &*const u32) -> u32 {
    mir! {
        {
            Call(RET = read_via_copy(*pp), ReturnTo(bb1), UnwindUnreachable())
        }
        bb1 = {
            Return()
        }
    }
}
"""

CUSTOM_MIR_INDIRECT_DISCRIMINANT_SRC = r"""
#![crate_type = "lib"]
#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features, dead_code)]

use core::intrinsics::mir::*;
use core::intrinsics::discriminant_value;

#[repr(u8)]
pub enum Tag { A = 1, B = 2 }

#[custom_mir(dialect = "runtime", phase = "initial")]
pub fn probe_indirect_discriminant(pp: &&Tag) -> u8 {
    mir! {
        {
            Call(RET = discriminant_value(*pp), ReturnTo(bb1), UnwindUnreachable())
        }
        bb1 = {
            Return()
        }
    }
}
"""

MIRI_READ_VIA_COPY_VOID_NULL_SRC = r"""
#![feature(core_intrinsics)]
#![allow(internal_features)]

pub enum Void {}

pub fn main() {
    let null_ptr: *const Void = core::ptr::null();
    unsafe {
        let _v: Void = core::intrinsics::read_via_copy(null_ptr);
    }
}
"""

MIRI_READ_VIA_COPY_SIZED_UNINHABITED_NULL_SRC = r"""
#![feature(core_intrinsics)]
#![allow(internal_features)]

pub enum Void {}
#[allow(dead_code)]
pub struct UninhabitedSized(u64, Void);

pub fn main() {
    let null_ptr: *const UninhabitedSized = core::ptr::null();
    unsafe {
        let _v: UninhabitedSized = core::intrinsics::read_via_copy(null_ptr);
    }
}
"""

MIRI_READ_VIA_COPY_SIZED_UNINHABITED_VALID_SRC = r"""
#![feature(core_intrinsics)]
#![allow(internal_features)]

pub enum Void {}
#[allow(dead_code)]
pub struct UninhabitedSized(u64, Void);

pub fn main() {
    let buf: u64 = 0x1122_3344_5566_7788;
    let valid_ptr: *const UninhabitedSized = (&buf as *const u64).cast::<UninhabitedSized>();
    unsafe {
        let _v: UninhabitedSized = core::intrinsics::read_via_copy(valid_ptr);
    }
}
"""

MIRI_TRANSMUTE_TO_VOID_SRC = r"""
#![feature(core_intrinsics)]
#![allow(internal_features)]

pub enum Void {}

pub fn main() {
    unsafe {
        let _v: Void = core::intrinsics::transmute::<(), Void>(());
    }
}
"""

MIRI_AGGREGATE_PTR_METADATA_SRC = r"""
#![feature(core_intrinsics, ptr_metadata)]
#![allow(internal_features)]

pub fn main() {
    let arr = [10u32, 20, 30, 40];
    let p: *const u32 = arr.as_ptr();
    let sp: *const [u32] = core::intrinsics::aggregate_raw_ptr(p, 4usize);
    let m: usize = core::intrinsics::ptr_metadata(sp);
    assert_eq!(m, 4);
    let s: &[u32] = unsafe { &*sp };
    assert_eq!(s.len(), 4);
    let idx: usize = 2;
    let elem2: *const u32 = unsafe { core::intrinsics::slice_get_unchecked(sp, idx) };
    assert_eq!(unsafe { *elem2 }, 30);
}
"""

MIRI_SLICE_LEN_DANGLING_REF_SRC = r"""
pub fn main() {
    let raw: *const [u32] = core::ptr::slice_from_raw_parts(core::ptr::dangling::<u32>(), 5);
    let dangling_ref: &[u32] = unsafe { &*raw };
    let _n = dangling_ref.len();
}
"""


def run_miri_bin(cargo_bin: str, rust_src: str, name: str, tmp_dir: Path) -> dict[str, Any]:
    proj = tmp_dir / f"miri_{name}"
    (proj / "src").mkdir(parents=True, exist_ok=True)
    (proj / "Cargo.toml").write_text(
        f'[package]\nname = "miri_{name}"\nversion = "0.1.0"\nedition = "2024"\n',
        encoding="utf-8",
    )
    (proj / "src" / "main.rs").write_text(rust_src, encoding="utf-8")
    env = os.environ.copy()
    env["CARGO_TARGET_DIR"] = str(tmp_dir / "miri_target")
    res = _run([cargo_bin, "miri", "run", "--quiet"], cwd=proj, tmp_dir=tmp_dir, env=env)
    ub_lines = [
        ln
        for ln in res["stderr"].splitlines()
        if "error: Undefined Behavior:" in ln or "panicked at" in ln
    ]
    return {
        "rc": res["rc"],
        "stdout": res["stdout"].strip(),
        "ub_lines": ub_lines,
        "stderr_head": "\n".join(res["stderr"].splitlines()[:25]),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out",
        type=Path,
        default=Path(__file__).resolve().parent / "probe_results.json",
        help="Path to write JSON probe results.",
    )
    args = parser.parse_args()

    rustc = _find_tool("rustc")
    cargo = shutil.which("cargo") or str(Path.home() / ".cargo" / "bin" / "cargo")
    has_miri = shutil.which("cargo-miri") is not None or (
        Path.home() / ".cargo" / "bin" / "cargo-miri"
    ).is_file()

    with tempfile.TemporaryDirectory(prefix="probe_lower_intrinsics_") as td:
        tmp = Path(td)
        ver_res = _run([rustc, "--version", "-v"], cwd=tmp, tmp_dir=tmp)
        results: dict[str, Any] = {
            "rustc_version": ver_res["stdout"].strip(),
        }

        # ------------------------------------------------------------------
        # 1a. trivial_const MIR pipeline bypass probe (clean compilation)
        # ------------------------------------------------------------------
        triv_rs = tmp / "triv.rs"
        triv_rs.write_text(TRIVIAL_CONST_OK_SRC, encoding="utf-8")
        triv_dump = tmp / "triv_mir"
        triv_res = _run(
            [
                rustc,
                "--edition=2024",
                "--crate-name=triv_probe",
                "-Zdump-mir=all",
                f"-Zdump-mir-dir={triv_dump}",
                "--emit=mir",
                "-o",
                str(tmp / "triv_probe.mir"),
                str(triv_rs),
            ],
            cwd=tmp,
            tmp_dir=tmp,
        )
        const_names = [
            "TRIV_A",
            "TRIV_B",
            "TRIV_C_CHAIN2",
            "NON_TRIV_ARITH",
            "NON_TRIV_GENERIC_REF",
            "NON_TRIV_OPAQUE_DEF",
            "IMPOSSIBLE_CLAUSE_TRIV",
            "read_impossible_triv",
        ]
        triv_dumps = {name: _dump_files_for_item(triv_dump, name) for name in const_names}
        results["trivial_const"] = {
            "compile_rc": triv_res["rc"],
            "compile_stderr": triv_res["stderr"].strip(),
            "dump_counts": {k: len(v) for k, v in triv_dumps.items()},
            "dump_files": triv_dumps,
            "triv_a_built": _read_first_matching_dump(triv_dump, "TRIV_A", ".built.after.mir", tmp),
            "triv_b_built": _read_first_matching_dump(triv_dump, "TRIV_B", ".built.after.mir", tmp),
            "triv_c_chain2_built": _read_first_matching_dump(
                triv_dump, "TRIV_C_CHAIN2", ".built.after.mir", tmp
            ),
            "non_triv_arith_built": _read_first_matching_dump(
                triv_dump, "NON_TRIV_ARITH", ".built.after.mir", tmp
            ),
            "impossible_clause_triv_built": _read_first_matching_dump(
                triv_dump, "IMPOSSIBLE_CLAUSE_TRIV", ".built.after.mir", tmp
            ),
            "read_impossible_triv_after_impossible": _read_first_matching_dump(
                triv_dump, "read_impossible_triv", ".ImpossiblePredicates.after.mir", tmp
            ),
        }

        # 1b. Non-trivial impossible-clause const fails CTFE with E0080
        imp_nt_rs = tmp / "imp_nontriv.rs"
        imp_nt_rs.write_text(TRIVIAL_CONST_IMPOSSIBLE_NON_TRIV_SRC, encoding="utf-8")
        imp_nt_dump = tmp / "imp_nontriv_mir"
        imp_nt_res = _run(
            [
                rustc,
                "--edition=2024",
                "--crate-name=imp_nontriv_probe",
                "-Zdump-mir=all",
                f"-Zdump-mir-dir={imp_nt_dump}",
                "--emit=mir",
                "-o",
                str(tmp / "imp_nontriv_probe.mir"),
                str(imp_nt_rs),
            ],
            cwd=tmp,
            tmp_dir=tmp,
        )
        results["impossible_clause_non_triv"] = {
            "compile_rc": imp_nt_res["rc"],
            "compile_stderr": imp_nt_res["stderr"].strip(),
            "dump_count": len(_dump_files_for_item(imp_nt_dump, "IMPOSSIBLE_CLAUSE_NON_TRIV")),
            "after_impossible_predicates": _read_first_matching_dump(
                imp_nt_dump, "IMPOSSIBLE_CLAUSE_NON_TRIV", ".ImpossiblePredicates.after.mir", tmp
            ),
        }

        # ------------------------------------------------------------------
        # 2. LowerIntrinsics complete arm lowering probe
        # ------------------------------------------------------------------
        li_rs = tmp / "lower_intrinsics_probe.rs"
        li_rs.write_text(LOWER_INTRINSICS_SRC, encoding="utf-8")
        li_dump = tmp / "li_mir"
        li_res = _run(
            [
                rustc,
                "--edition=2024",
                "--crate-name=li_probe",
                "-Zdump-mir=LowerIntrinsics",
                f"-Zdump-mir-dir={li_dump}",
                "-Zmir-opt-level=0",
                "--emit=mir",
                "-o",
                str(tmp / "li_probe.mir"),
                str(li_rs),
            ],
            cwd=tmp,
            tmp_dir=tmp,
        )
        li_items = [
            "probe_unreachable",
            "probe_runtime_checks",
            "probe_forget",
            "probe_copy_nonoverlapping",
            "probe_assume",
            "probe_binops",
            "probe_with_overflow",
            "probe_read_via_copy_u32",
            "probe_read_via_copy_void",
            "probe_read_via_copy_uninhabited_sized",
            "probe_discriminant_value",
            "probe_offset",
            "probe_slice_get_unchecked_all4",
            "probe_transmute_u32_f32",
            "probe_transmute_to_void",
            "probe_transmute_unchecked_to_void",
            "probe_raw_ptr_roundtrip",
            "probe_unlowered_ctpop",
        ]
        li_mir: dict[str, dict[str, str | None]] = {}
        for item in li_items:
            li_mir[item] = {
                "before": _read_first_matching_dump(
                    li_dump, item, ".LowerIntrinsics.before.mir", tmp
                ),
                "after": _read_first_matching_dump(
                    li_dump, item, ".LowerIntrinsics.after.mir", tmp
                ),
            }
        results["lower_intrinsics"] = {
            "compile_rc": li_res["rc"],
            "compile_stderr": li_res["stderr"].strip(),
            "items": li_mir,
        }

        # ------------------------------------------------------------------
        # 3. LowerSliceLenCalls differential probe (-Zmir-opt-level=0 vs 1)
        # ------------------------------------------------------------------
        sl_rs = tmp / "slice_len_probe.rs"
        sl_rs.write_text(SLICE_LEN_SRC, encoding="utf-8")
        sl_results: dict[str, Any] = {}
        for opt_lvl in (0, 1):
            sl_dump = tmp / f"sl_mir_o{opt_lvl}"
            sl_res = _run(
                [
                    rustc,
                    "--edition=2024",
                    f"--crate-name=sl_probe_o{opt_lvl}",
                    "-Zdump-mir=LowerSliceLenCalls|runtime-optimized",
                    f"-Zdump-mir-dir={sl_dump}",
                    f"-Zmir-opt-level={opt_lvl}",
                    "--emit=mir",
                    "-o",
                    str(tmp / f"sl_probe_o{opt_lvl}.mir"),
                    str(sl_rs),
                ],
                cwd=tmp,
                tmp_dir=tmp,
            )
            sl_items = {}
            for fn_name in (
                "probe_slice_len",
                "probe_slice_len_mut_reborrow",
                "probe_slice_len_fn_ptr",
                "probe_slice_len_sole_unwind_cleanup",
            ):
                sl_items[fn_name] = {
                    "files": _dump_files_for_item(sl_dump, fn_name),
                    "before": _read_first_matching_dump(
                        sl_dump, fn_name, ".LowerSliceLenCalls.before.mir", tmp
                    ),
                    "after": _read_first_matching_dump(
                        sl_dump, fn_name, ".LowerSliceLenCalls.after.mir", tmp
                    ),
                    "optimized": _read_first_matching_dump(
                        sl_dump, fn_name, ".runtime-optimized.after.mir", tmp
                    ),
                }
            sl_results[f"mir_opt_level_{opt_lvl}"] = {
                "compile_rc": sl_res["rc"],
                "compile_stderr": sl_res["stderr"].strip(),
                "items": sl_items,
            }
        results["lower_slice_len"] = sl_results

        # ------------------------------------------------------------------
        # 4. PostAnalysisNormalize & CleanupPostBorrowck probe
        # ------------------------------------------------------------------
        pan_rs = tmp / "pan_probe.rs"
        pan_rs.write_text(POST_ANALYSIS_NORMALIZE_SRC, encoding="utf-8")
        pan_dump = tmp / "pan_mir"
        pan_res = _run(
            [
                rustc,
                "--edition=2024",
                "--crate-name=pan_probe",
                "-Zdump-mir=CleanupPostBorrowck|PostAnalysisNormalize",
                f"-Zdump-mir-dir={pan_dump}",
                "--emit=mir",
                "-o",
                str(tmp / "pan_probe.mir"),
                str(pan_rs),
            ],
            cwd=tmp,
            tmp_dir=tmp,
        )
        pan_items: dict[str, Any] = {}
        for fn_name in ("make_opaque_pair", "project_opaque_pair", "probe_assoc_norm"):
            pan_items[fn_name] = {
                "cleanup_before": _read_first_matching_dump(
                    pan_dump, fn_name, ".CleanupPostBorrowck.before.mir", tmp
                ),
                "cleanup_after": _read_first_matching_dump(
                    pan_dump, fn_name, ".CleanupPostBorrowck.after.mir", tmp
                ),
                "norm_before": _read_first_matching_dump(
                    pan_dump, fn_name, ".PostAnalysisNormalize.before.mir", tmp
                ),
                "norm_after": _read_first_matching_dump(
                    pan_dump, fn_name, ".PostAnalysisNormalize.after.mir", tmp
                ),
            }
        results["post_analysis_normalize"] = {
            "compile_rc": pan_res["rc"],
            "compile_stderr": pan_res["stderr"].strip(),
            "items": pan_items,
        }

        # ------------------------------------------------------------------
        # 5. custom_mir & constant-index ICE and control probes
        # ------------------------------------------------------------------
        custom_cases = [
            (
                "indirect_slice_get_unchecked",
                CUSTOM_MIR_INDIRECT_SLICE_GET_UNCHECKED_SRC,
                "ice_indirect_slice_get_unchecked",
                [],
            ),
            (
                "const_index_slice_get_unchecked",
                ORDINARY_RUST_CONST_IDX_SLICE_GET_UNCHECKED_SRC,
                "ice_const_idx_slice_get_unchecked",
                [],
            ),
            (
                "field_proj_slice_get_unchecked_validate_mir",
                CUSTOM_MIR_FIELD_PROJ_SLICE_GET_UNCHECKED_SRC,
                "field_proj_slice_get_unchecked",
                ["-Zvalidate-mir"],
            ),
            (
                "direct_slice_get_unchecked_control",
                CUSTOM_MIR_DIRECT_SLICE_GET_UNCHECKED_SRC,
                "ok_direct_slice_get_unchecked",
                [],
            ),
            (
                "indirect_read_via_copy",
                CUSTOM_MIR_INDIRECT_READ_VIA_COPY_SRC,
                "ice_indirect_read_via_copy",
                [],
            ),
            (
                "indirect_discriminant_no_validate",
                CUSTOM_MIR_INDIRECT_DISCRIMINANT_SRC,
                "probe_indirect_discriminant",
                [],
            ),
            (
                "indirect_discriminant_validate_mir",
                CUSTOM_MIR_INDIRECT_DISCRIMINANT_SRC,
                "probe_indirect_discriminant",
                ["-Zvalidate-mir"],
            ),
        ]
        custom_results: dict[str, Any] = {}
        for cname, csrc, fn_marker, extra_flags in custom_cases:
            crs = tmp / f"{cname}.rs"
            crs.write_text(csrc, encoding="utf-8")
            cdump = tmp / f"dump_{cname}"
            cres = _run(
                [
                    rustc,
                    "--edition=2024",
                    f"--crate-name={cname}",
                    "-Zdump-mir=LowerIntrinsics",
                    f"-Zdump-mir-dir={cdump}",
                    *extra_flags,
                    "--emit=mir",
                    "-o",
                    str(tmp / f"{cname}.mir"),
                    str(crs),
                ],
                cwd=tmp,
                tmp_dir=tmp,
            )
            panic_lines = [
                ln
                for ln in cres["stderr"].splitlines()
                if any(
                    tok in ln
                    for tok in (
                        "panicked at",
                        "assertion failed",
                        "Option::unwrap",
                        "internal compiler error",
                        "Only passing a local",
                        "is_indirect",
                        "broken MIR",
                        "Deref",
                    )
                )
            ]
            custom_results[cname] = {
                "rc": cres["rc"],
                "hit_is_indirect_ice": "assertion failed: !place.is_indirect()" in cres["stderr"],
                "hit_const_idx_unwrap_ice": "called `Option::unwrap()` on a `None` value"
                in cres["stderr"],
                "hit_only_local_span_bug": "Only passing a local is supported" in cres["stderr"],
                "hit_validate_mir_broken": "broken MIR" in cres["stderr"],
                "panic_lines": panic_lines[:8],
                "lower_intrinsics_before": _read_first_matching_dump(
                    cdump, fn_marker, ".LowerIntrinsics.before.mir", tmp
                ),
                "lower_intrinsics_after": _read_first_matching_dump(
                    cdump, fn_marker, ".LowerIntrinsics.after.mir", tmp
                ),
            }
        results["custom_mir_probes"] = custom_results

        # ------------------------------------------------------------------
        # 6. Miri runtime operational-semantics probes (if cargo-miri present)
        # ------------------------------------------------------------------
        if has_miri:
            miri_ver = _run([cargo, "miri", "--version"], cwd=tmp, tmp_dir=tmp)
            results["miri"] = {
                "version": miri_ver["stdout"].strip(),
                "read_via_copy_void_null": run_miri_bin(
                    cargo, MIRI_READ_VIA_COPY_VOID_NULL_SRC, "rvc_void_null", tmp
                ),
                "read_via_copy_sized_uninhabited_null": run_miri_bin(
                    cargo,
                    MIRI_READ_VIA_COPY_SIZED_UNINHABITED_NULL_SRC,
                    "rvc_sized_null",
                    tmp,
                ),
                "read_via_copy_sized_uninhabited_valid": run_miri_bin(
                    cargo,
                    MIRI_READ_VIA_COPY_SIZED_UNINHABITED_VALID_SRC,
                    "rvc_sized_valid",
                    tmp,
                ),
                "transmute_unit_to_void": run_miri_bin(
                    cargo, MIRI_TRANSMUTE_TO_VOID_SRC, "transmute_void", tmp
                ),
                "aggregate_raw_ptr_metadata_roundtrip": run_miri_bin(
                    cargo, MIRI_AGGREGATE_PTR_METADATA_SRC, "raw_ptr_rt", tmp
                ),
                "slice_len_dangling_ref": run_miri_bin(
                    cargo, MIRI_SLICE_LEN_DANGLING_REF_SRC, "slice_len_dang", tmp
                ),
            }
        else:
            results["miri"] = {"available": False}

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(f"wrote {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
