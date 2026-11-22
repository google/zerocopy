#!/usr/bin/env python3
"""Empirical probe for rustc `unsafe_binders` (`TyKind::UnsafeBinder`,
`Rvalue::WrapUnsafeBinder`, `ProjectionElem::UnwrapUnsafeBinder`):

- Part A: Live execution, 4-tier `Option` null-niche sizes, default `v0` vs
  `legacy` symbol mangling, and Miri default vs `-Zmiri-disable-validation`.
- Part B: LLVM IR parameter/return attributes across the 4-tier wrapper lattice
  (`&T`, `MaybeDangling<&T>`, `unsafe<'a> &'a T`, `MaybeUninit<&T>`) at
  `-O -C no-prepopulate-passes`, `-O`, and `-C opt-level=0`; MIR emission; and
  dangling / misaligned binder behavior under Miri.
- Part C: Bidirectional `E0133` `unsafe` gates, deliberate `!Copy` move-only
  linearity (`E0277`, `E0382`), auto/builtin trait checks, and the three live
  compiler ICEs (`v0.rs`, `validity.rs`, `consts.rs`).

Requires a nightly `rustc` (and optionally `miri` + prebuilt Miri sysroot).
Uses only the Python 3.10+ standard library.
"""

from __future__ import annotations

import argparse
import datetime
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


def _find_rustc() -> str:
    env_path = os.environ.get("RUSTC")
    if env_path:
        return env_path
    found = shutil.which("rustc")
    if found:
        return found
    home_cargo = Path.home() / ".cargo" / "bin" / "rustc"
    if home_cargo.exists():
        return str(home_cargo)
    raise RuntimeError("rustc not found in PATH or ~/.cargo/bin")


def _find_miri(rustc: str) -> tuple[str | None, str | None]:
    sysroot = subprocess.check_output([rustc, "--print", "sysroot"], text=True).strip()
    miri_bin = Path(sysroot) / "bin" / "miri"
    if not miri_bin.exists():
        which_miri = shutil.which("miri")
        miri_bin = Path(which_miri) if which_miri else None
    miri_sysroot = os.environ.get("MIRI_SYSROOT")
    if not miri_sysroot:
        cache_miri = Path.home() / ".cache" / "miri"
        if (cache_miri / "lib").is_dir():
            miri_sysroot = str(cache_miri)
    return (str(miri_bin) if miri_bin else None, miri_sysroot)


def _sanitize(text: str, tmpdir: str) -> str:
    return text.replace(tmpdir, "<TMP>")


def _trim_ice(text: str, max_lines: int = 18) -> str:
    lines = text.splitlines()
    if len(lines) <= max_lines:
        return text
    return "\n".join(lines[:max_lines]) + f"\n... ({len(lines) - max_lines} more lines)"


def _panic_line(stderr: str) -> str | None:
    lines = stderr.splitlines()
    for i, line in enumerate(lines):
        if "panicked at " in line:
            msg = lines[i + 1].strip() if i + 1 < len(lines) else ""
            return f"{line.strip()} | {msg}" if msg else line.strip()
    return None


def _run_rustc(
    rustc: str,
    code: str,
    filename: str,
    extra_args: list[str],
    crate_type: str = "lib",
    run_binary: bool = False,
) -> dict[str, Any]:
    with tempfile.TemporaryDirectory(prefix="ubind_probe_") as d:
        src = Path(d) / filename
        src.write_text(code, encoding="utf-8")
        if "--emit=llvm-ir" in extra_args:
            out = Path(d) / "out.ll"
        elif "--emit=mir" in extra_args:
            out = Path(d) / "out.mir"
        elif crate_type == "bin":
            out = Path(d) / "out_bin"
        else:
            out = Path(d) / "out.rlib"
        cmd = [
            rustc,
            "--edition=2024",
            f"--crate-type={crate_type}",
            str(src),
            "-o",
            str(out),
            *extra_args,
        ]
        p = subprocess.run(cmd, capture_output=True, text=True)
        res: dict[str, Any] = {
            "rc": p.returncode,
            "panic_summary": _panic_line(p.stderr),
            "stderr": _trim_ice(_sanitize(p.stderr, d)),
        }
        if "--emit=llvm-ir" in extra_args and out.exists():
            ir_text = out.read_text(encoding="utf-8")
            res["llvm_define_lines"] = [
                line for line in ir_text.splitlines() if line.startswith("define ")
            ]
        if "--emit=mir" in extra_args and out.exists():
            mir_text = out.read_text(encoding="utf-8")
            res["mir_excerpt"] = mir_text[:4000]
        if run_binary and p.returncode == 0 and out.exists():
            rp = subprocess.run([str(out)], capture_output=True, text=True)
            res["run_rc"] = rp.returncode
            res["run_stdout"] = rp.stdout.strip()
            res["run_stderr"] = rp.stderr.strip()
        return res


def _run_miri(
    miri_bin: str | None,
    miri_sysroot: str | None,
    code: str,
    filename: str,
    extra_args: list[str],
) -> dict[str, Any]:
    if not miri_bin or not miri_sysroot:
        return {
            "skipped": True,
            "reason": f"miri_bin={miri_bin!r}, miri_sysroot={miri_sysroot!r}",
        }
    with tempfile.TemporaryDirectory(prefix="ubind_miri_") as d:
        src = Path(d) / filename
        src.write_text(code, encoding="utf-8")
        cmd = [
            miri_bin,
            "--edition=2024",
            "--sysroot",
            miri_sysroot,
            *extra_args,
            str(src),
        ]
        p = subprocess.run(cmd, capture_output=True, text=True)
        return {
            "rc": p.returncode,
            "panic_summary": _panic_line(p.stderr),
            "stdout": p.stdout.strip(),
            "stderr": _trim_ice(_sanitize(p.stderr, d)),
        }


PART_A_LIVE_BIN = r'''
#![feature(unsafe_binders, maybe_dangling)]
use core::mem::{MaybeDangling, MaybeUninit, size_of};
use core::unsafe_binder::{unwrap_binder, wrap_binder};

#[inline(never)]
fn check_niche_and_exec() -> (usize, usize, usize, usize, usize, u64, u64) {
    let x: u64 = 42;
    let b: unsafe<'a> &'a u64 = unsafe { wrap_binder!(&x) };
    let out: u64 = unsafe { *unwrap_binder!(b) };
    let mut slot: u64 = 0;
    let bm: unsafe<'a> &'a mut u64 = unsafe { wrap_binder!(&mut slot) };
    unsafe { *unwrap_binder!(bm) = out; }
    (
        size_of::<Option<&u64>>(),
        size_of::<Option<MaybeDangling<&u64>>>(),
        size_of::<Option<unsafe<'a> &'a u64>>(),
        size_of::<Option<unsafe<'a> &'a mut u64>>(),
        size_of::<Option<MaybeUninit<&u64>>>(),
        out,
        slot,
    )
}

fn main() {
    let (r, md, sh, mu, uninit, out, slot) = check_niche_and_exec();
    println!(
        "OPT_REF={r} OPT_MD={md} OPT_SHARED={sh} OPT_MUT={mu} OPT_UNINIT={uninit} OUT={out} SLOT={slot}"
    );
}
'''

PART_B_LLVM_LIB = r'''
#![feature(unsafe_binders, maybe_dangling)]
use core::mem::{MaybeDangling, MaybeUninit};
use core::unsafe_binder::{unwrap_binder, wrap_binder};

#[unsafe(no_mangle)]
pub fn pass_plain_ref(r: &u64) -> &u64 { r }

#[unsafe(no_mangle)]
pub fn pass_plain_mut(r: &mut u64) -> &mut u64 { r }

#[unsafe(no_mangle)]
pub fn pass_maybe_dangling_shared(r: MaybeDangling<&u64>) -> MaybeDangling<&u64> { r }

#[unsafe(no_mangle)]
pub fn pass_maybe_dangling_mut(r: MaybeDangling<&mut u64>) -> MaybeDangling<&mut u64> { r }

#[unsafe(no_mangle)]
pub fn pass_unsafe_binder_shared(b: unsafe<'a> &'a u64) -> u64 {
    unsafe { *unwrap_binder!(b) }
}

#[unsafe(no_mangle)]
pub fn pass_unsafe_binder_unused(_b: unsafe<'a> &'a u64) -> u64 { 7 }

#[unsafe(no_mangle)]
pub fn pass_unsafe_binder_mut(_b: unsafe<'a> &'a mut u64) -> u64 { 9 }

#[unsafe(no_mangle)]
pub fn pass_maybe_uninit(_m: MaybeUninit<&u64>) -> u64 { 11 }

#[unsafe(no_mangle)]
pub fn opt_unsafe_binder_is_some(o: Option<unsafe<'a> &'a u64>) -> bool {
    o.is_some()
}

#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct Wrap<'a>(pub &'a u64);

#[derive(Copy, Clone)]
pub struct Pair<'a>(pub &'a u64, pub u64);

#[unsafe(no_mangle)]
pub fn pass_wide_slice_binder(_b: unsafe<'a> &'a [u64]) -> u64 { 2 }

#[unsafe(no_mangle)]
pub fn pass_mut_slice_binder(_b: unsafe<'a> &'a mut [u64]) -> u64 { 3 }

#[unsafe(no_mangle)]
pub fn pass_tuple_binder(_b: unsafe<'a> (&'a u64, u64)) -> u64 { 4 }

#[unsafe(no_mangle)]
pub fn pass_mut_tuple_binder(_b: unsafe<'a> (&'a mut u64, u64)) -> u64 { 5 }

#[unsafe(no_mangle)]
pub fn pass_struct_binder(_b: unsafe<'a> Pair<'a>) -> u64 { 6 }

#[unsafe(no_mangle)]
pub fn pass_newtype_binder(_b: unsafe<'a> Wrap<'a>) -> u64 { 7 }

#[unsafe(no_mangle)]
pub fn pass_opt_newtype_binder(o: Option<unsafe<'a> Wrap<'a>>) -> bool { o.is_some() }

#[unsafe(no_mangle)]
pub fn wrap_and_unwrap_roundtrip(x: &u64) -> u64 {
    let b: unsafe<'a> &'a u64 = unsafe { wrap_binder!(x) };
    unsafe { *unwrap_binder!(b) }
}
'''

PART_B_MIR_SNIPPET = r'''
#![feature(unsafe_binders)]
use core::unsafe_binder::{unwrap_binder, wrap_binder};

pub fn wrap_and_unwrap_roundtrip(x: &u64) -> u64 {
    let b: unsafe<'a> &'a u64 = unsafe { wrap_binder!(x) };
    unsafe { *unwrap_binder!(b) }
}
'''

PART_B_DANGLING_UNUSED_BIN = r'''
#![feature(unsafe_binders)]
use core::unsafe_binder::wrap_binder;

#[inline(never)]
fn sink_unused(_b: unsafe<'a> &'a u64) -> u64 { 7 }

fn main() {
    let bx = Box::new(42u64);
    let b: unsafe<'a> &'a u64 = unsafe { wrap_binder!(&*bx) };
    drop(bx);
    let r = sink_unused(b);
    println!("DANGLING_UNUSED={r}");
}
'''

PART_B_DANGLING_UNWRAP_UB_BIN = r'''
#![feature(unsafe_binders)]
use core::unsafe_binder::{unwrap_binder, wrap_binder};

fn main() {
    let bx = Box::new(42u64);
    let b: unsafe<'a> &'a u64 = unsafe { wrap_binder!(&*bx) };
    drop(bx);
    let v = unsafe { *unwrap_binder!(b) };
    println!("UAF={v}");
}
'''

PART_B_MISALIGNED_UNUSED_BIN = r'''
#![feature(unsafe_binders)]

#[inline(never)]
fn sink_unused(_b: unsafe<'a> &'a u64) -> u64 { 7 }

fn main() {
    let b: unsafe<'a> &'a u64 = unsafe { core::mem::transmute::<usize, unsafe<'a> &'a u64>(1usize) };
    let r = sink_unused(b);
    println!("MISALIGNED_UNUSED={r}");
}
'''

PART_C_CASES: dict[str, tuple[str, list[str], str]] = {
    "wrap_binder_without_unsafe_rejected_e0133": (
        r'''#![feature(unsafe_binders)]
use core::unsafe_binder::wrap_binder;
pub fn bad_wrap(r: &u64) -> unsafe<'a> &'a u64 {
    wrap_binder!(r)
}
''',
        ["-Z", "unstable-options", "-C", "symbol-mangling-version=legacy"],
        "lib",
    ),
    "unwrap_binder_without_unsafe_rejected_e0133": (
        r'''#![feature(unsafe_binders)]
use core::unsafe_binder::unwrap_binder;
pub fn bad_unwrap(b: unsafe<'a> &'a u64) -> u64 {
    *unwrap_binder!(b)
}
''',
        ["-Z", "unstable-options", "-C", "symbol-mangling-version=legacy"],
        "lib",
    ),
    "shared_ref_unsafe_binder_not_copy_e0277": (
        r'''#![feature(unsafe_binders)]
fn need_copy<T: Copy>() {}
pub fn check() { need_copy::<unsafe<'a> &'a u64>(); }
''',
        ["-Z", "unstable-options", "-C", "symbol-mangling-version=legacy"],
        "lib",
    ),
    "shared_ref_unsafe_binder_not_clone_e0277": (
        r'''#![feature(unsafe_binders)]
fn need_clone<T: Clone>() {}
pub fn check() { need_clone::<unsafe<'a> &'a u64>(); }
''',
        ["-Z", "unstable-options", "-C", "symbol-mangling-version=legacy"],
        "lib",
    ),
    "shared_ref_unsafe_binder_move_e0382": (
        r'''#![feature(unsafe_binders)]
pub fn dup(b: unsafe<'a> &'a u64) -> (unsafe<'a> &'a u64, unsafe<'a> &'a u64) {
    (b, b)
}
''',
        ["-Z", "unstable-options", "-C", "symbol-mangling-version=legacy"],
        "lib",
    ),
    "mut_ref_unsafe_binder_not_copy_e0382": (
        r'''#![feature(unsafe_binders)]
pub fn dup(b: unsafe<'a> &'a mut u32) -> (unsafe<'a> &'a mut u32, unsafe<'a> &'a mut u32) {
    (b, b)
}
''',
        ["-Z", "unstable-options", "-C", "symbol-mangling-version=legacy"],
        "lib",
    ),
    "auto_traits_sized_send_sync_on_unsafe_binder": (
        r'''#![feature(unsafe_binders)]
fn need_sized_send_sync<T: Sized + Send + Sync>() {}
pub fn check() { need_sized_send_sync::<unsafe<'a> &'a u64>(); }
''',
        ["-Z", "unstable-options", "-C", "symbol-mangling-version=legacy"],
        "lib",
    ),
    "nested_unsafe_binder_rejected_no_drop_e0277": (
        r'''#![feature(unsafe_binders)]
pub fn nested(_: unsafe<'a> unsafe<'b> &'a &'b u64) {}
''',
        ["-Z", "unstable-options", "-C", "symbol-mangling-version=legacy"],
        "lib",
    ),
    "nested_unsafe_binder_via_manually_drop_ok": (
        r'''#![feature(unsafe_binders)]
use core::mem::ManuallyDrop;
pub fn nested_md(_: unsafe<'a> ManuallyDrop<unsafe<'b> &'a &'b u64>) {}
''',
        ["-Z", "unstable-options", "-C", "symbol-mangling-version=legacy"],
        "lib",
    ),
    "forbid_unsafe_v0_mangling_size_of_ice": (
        r'''#![forbid(unsafe_code)]
#![feature(unsafe_binders)]
pub fn size_of_binder() -> usize {
    core::mem::size_of::<unsafe<'a> &'a u64>()
}
''',
        [],
        "lib",
    ),
    "forbid_unsafe_legacy_mangling_size_of_ok": (
        r'''#![forbid(unsafe_code)]
#![feature(unsafe_binders)]
pub fn size_of_binder() -> usize {
    core::mem::size_of::<unsafe<'a> &'a u64>()
}
''',
        ["-Z", "unstable-options", "-C", "symbol-mangling-version=legacy"],
        "lib",
    ),
    "ctfe_const_unsafe_binder_ice": (
        r'''#![feature(unsafe_binders)]
use core::unsafe_binder::wrap_binder;
const X: u64 = 7;
const B: unsafe<'a> &'a u64 = unsafe { wrap_binder!(&X) };
pub fn use_b() -> usize { core::mem::size_of_val(&B) }
''',
        ["-Z", "unstable-options", "-C", "symbol-mangling-version=legacy"],
        "lib",
    ),
    "gce_wrap_unsafe_binder_ice": (
        r'''#![feature(unsafe_binders, generic_const_exprs)]
use core::unsafe_binder::wrap_binder;
const fn id<const N: usize>(_: unsafe<'a> &'a [u8; N]) -> usize { N }
pub fn f<const N: usize>() where [(); id::<N>(wrap_binder!(&[0u8; N]))]: {}
''',
        ["-Z", "unstable-options", "-C", "symbol-mangling-version=legacy"],
        "lib",
    ),
}


def run_all() -> dict[str, Any]:
    rustc = _find_rustc()
    rustc_v = subprocess.check_output([rustc, "-vV"], text=True).strip()
    miri_bin, miri_sysroot = _find_miri(rustc)
    miri_v = None
    if miri_bin:
        p = subprocess.run([miri_bin, "--version"], capture_output=True, text=True)
        miri_v = p.stdout.strip() or p.stderr.strip()

    legacy_flags = ["-Z", "unstable-options", "-C", "symbol-mangling-version=legacy"]

    part_a = {
        "default_v0_mangling": _run_rustc(
            rustc, PART_A_LIVE_BIN, "part_a.rs", [], crate_type="bin", run_binary=False
        ),
        "legacy_mangling_and_native": _run_rustc(
            rustc, PART_A_LIVE_BIN, "part_a.rs", legacy_flags, crate_type="bin", run_binary=True
        ),
        "miri_default_validity": _run_miri(
            miri_bin, miri_sysroot, PART_A_LIVE_BIN, "part_a.rs", legacy_flags
        ),
        "miri_disable_validation_tb": _run_miri(
            miri_bin,
            miri_sysroot,
            PART_A_LIVE_BIN,
            "part_a.rs",
            [*legacy_flags, "-Zmiri-disable-validation", "-Zmiri-tree-borrows"],
        ),
    }

    part_b = {
        "llvm_ir_opt_no_prepopulate": _run_rustc(
            rustc,
            PART_B_LLVM_LIB,
            "part_b_llvm.rs",
            ["-O", "-C", "no-prepopulate-passes", "--emit=llvm-ir", *legacy_flags],
            crate_type="lib",
        ),
        "llvm_ir_opt": _run_rustc(
            rustc,
            PART_B_LLVM_LIB,
            "part_b_llvm.rs",
            ["-O", "--emit=llvm-ir", *legacy_flags],
            crate_type="lib",
        ),
        "llvm_ir_o0": _run_rustc(
            rustc,
            PART_B_LLVM_LIB,
            "part_b_llvm.rs",
            ["-C", "opt-level=0", "--emit=llvm-ir", *legacy_flags],
            crate_type="lib",
        ),
        "mir_dump": _run_rustc(
            rustc,
            PART_B_MIR_SNIPPET,
            "part_b_mir.rs",
            ["--emit=mir", *legacy_flags],
            crate_type="lib",
        ),
        "dangling_binder_miri_sb_default": _run_miri(
            miri_bin, miri_sysroot, PART_B_DANGLING_UNUSED_BIN, "dangling_unused.rs", legacy_flags
        ),
        "dangling_binder_miri_tb_default": _run_miri(
            miri_bin,
            miri_sysroot,
            PART_B_DANGLING_UNUSED_BIN,
            "dangling_unused.rs",
            [*legacy_flags, "-Zmiri-tree-borrows"],
        ),
        "dangling_binder_miri_tb_disable_validation": _run_miri(
            miri_bin,
            miri_sysroot,
            PART_B_DANGLING_UNUSED_BIN,
            "dangling_unused.rs",
            [*legacy_flags, "-Zmiri-disable-validation", "-Zmiri-tree-borrows"],
        ),
        "dangling_binder_unwrap_ub_miri_tb_disable_validation": _run_miri(
            miri_bin,
            miri_sysroot,
            PART_B_DANGLING_UNWRAP_UB_BIN,
            "dangling_unwrap_ub.rs",
            [*legacy_flags, "-Zmiri-disable-validation", "-Zmiri-tree-borrows"],
        ),
        "misaligned_binder_unused_miri_tb_disable_validation": _run_miri(
            miri_bin,
            miri_sysroot,
            PART_B_MISALIGNED_UNUSED_BIN,
            "misaligned_unused.rs",
            [*legacy_flags, "-Zmiri-disable-validation", "-Zmiri-tree-borrows"],
        ),
        "misaligned_binder_unused_native": _run_rustc(
            rustc,
            PART_B_MISALIGNED_UNUSED_BIN,
            "misaligned_unused.rs",
            ["-O", *legacy_flags],
            crate_type="bin",
            run_binary=True,
        ),
    }

    part_c = {}
    for name, (code, flags, ct) in PART_C_CASES.items():
        part_c[name] = _run_rustc(rustc, code, f"{name}.rs", flags, crate_type=ct)

    return {
        "timestamp_utc": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "rustc_version": rustc_v,
        "miri_version": miri_v,
        "part_a_live_execution_niche_and_miri": part_a,
        "part_b_llvm_ir_attrs_mir_and_dangling_miri": part_b,
        "part_c_safety_gates_linearity_and_three_ices": part_c,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, help="Optional path to write JSON output")
    args = parser.parse_args(argv)
    result = run_all()
    payload = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(payload, encoding="utf-8")
    else:
        sys.stdout.write(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
