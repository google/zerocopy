#!/usr/bin/env python3
"""Empirical rustc + Miri probe for match lowering, fake borrows, guards, or-patterns,
uninhabited / #[non_exhaustive] exhaustiveness, and slice/range MIR lowering.

Reproduces and records:
  1. FakeBorrowKind::{Shallow, Deep} + FakeRead(ForMatchGuard) borrowck matrix
     (including E0506 vs E0510 diagnostic split, unswitched local & unswitched
     variant-payload projection permissions, deref/slice prefix shallow borrows,
     Box<T> DerefPatBorrowMode::Box shallow-pair lowering, and custom DerefPure
     TestableCase::Deref deep fake-borrow lowering `&fake _1`).
  2. Native + Miri (Stacked Borrows and Tree Borrows) execution parity for
     or-pattern guard re-evaluation, final-sub-branch LIFO drop scheduling,
     non-Copy guard-failure non-consumption, and unswitched local mutation.
  3. Cross-crate uninhabited (Void) & #[non_exhaustive] single-variant
     exhaustiveness + Built/PostCleanup MIR audit, paired with 3 Miri executions
     distinguishing `*const Void` wildcard PlaceMention from `&Void` UB.
  4. Slice and range pattern Runtime(PostCleanup) MIR lowering (UnOp::PtrMetadata,
     ConstantIndex from-end, Subslice from-end, and Ge/Le/Lt/Eq comparisons).
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import shutil
import socket
import subprocess
import sys
import tempfile
from typing import Any


def _find_rustc_and_miri() -> tuple[str, str, Path]:
    rustc = shutil.which("rustc")
    if not rustc:
        cand = Path.home() / ".cargo" / "bin" / "rustc"
        if cand.exists():
            rustc = str(cand)
    if not rustc:
        raise RuntimeError("rustc not found in PATH or ~/.cargo/bin")

    sysroot_proc = subprocess.run(
        [rustc, "--print", "sysroot"],
        capture_output=True,
        text=True,
        check=True,
        timeout=15,
    )
    toolchain_root = Path(sysroot_proc.stdout.strip())
    miri_cand = toolchain_root / "bin" / "miri"
    if not miri_cand.exists():
        found_miri = shutil.which("miri")
        if not found_miri:
            raise RuntimeError("miri driver binary not found in toolchain sysroot or PATH")
        miri_bin = found_miri
    else:
        miri_bin = str(miri_cand)
    return rustc, miri_bin, toolchain_root


def _clean_env() -> dict[str, str]:
    env = dict(os.environ)
    cargo_bin = str(Path.home() / ".cargo" / "bin")
    path_parts = env.get("PATH", "").split(os.pathsep)
    if cargo_bin not in path_parts and os.path.isdir(cargo_bin):
        env["PATH"] = os.pathsep.join([cargo_bin, *path_parts])
    return env


def _scrub_text(text: str, tmp_dir: Path | None = None) -> str:
    out = text
    if tmp_dir is not None:
        out = out.replace(str(tmp_dir.resolve()), "<TMP>")
        out = out.replace(str(tmp_dir), "<TMP>")
    home = str(Path.home())
    if home and home != "/":
        out = out.replace(home, "<HOME>")
    host = socket.gethostname()
    if host:
        out = out.replace(host, "<HOST>")
    out = re.sub(r"/tmp/[^\s:\"']+", "<TMP>", out)
    return out


def _extract_error_codes(stderr: str) -> list[str]:
    return sorted(set(re.findall(r"error\[E\d{4}\]", stderr)))


def _stderr_summary_lines(stderr: str, tmp_dir: Path, limit: int = 5) -> list[str]:
    scrubbed = _scrub_text(stderr, tmp_dir)
    kept: list[str] = []
    for raw in scrubbed.splitlines():
        line = raw.strip()
        if not line:
            continue
        if (
            line.startswith("error")
            or line.startswith("= help:")
            or line.startswith("For more information")
            or "Undefined Behavior" in line
        ):
            kept.append(line)
        if len(kept) >= limit:
            break
    return kept


def _extract_fn_mir(mir_text: str, fn_name: str) -> str:
    lines = mir_text.splitlines()
    captured: list[str] = []
    in_fn = False
    brace_depth = 0
    header_re = re.compile(rf"^fn\s+(?:[A-Za-z0-9_]+::)*{re.escape(fn_name)}\s*\(")
    for line in lines:
        if not in_fn:
            if header_re.search(line):
                in_fn = True
                brace_depth = line.count("{") - line.count("}")
                captured.append(line)
        else:
            captured.append(line)
            brace_depth += line.count("{") - line.count("}")
            if brace_depth <= 0 and line.strip() == "}":
                break
    return "\n".join(captured)


def _compile_and_inspect_mir(
    rustc: str,
    env: dict[str, str],
    src_code: str,
    fn_name: str,
    extra_args: list[str] | None = None,
) -> dict[str, Any]:
    with tempfile.TemporaryDirectory() as td:
        tmp_path = Path(td)
        src_file = tmp_path / "probe.rs"
        dump_dir = tmp_path / "mir_dump"
        dump_dir.mkdir(parents=True, exist_ok=True)
        out_rlib = tmp_path / "libprobe.rlib"
        src_file.write_text(src_code, encoding="utf-8")

        cmd = [
            rustc,
            "--edition=2024",
            "--crate-type=lib",
            "-Z",
            f"dump-mir-dir={dump_dir}",
            "-Z",
            "dump-mir=built|CleanupPostBorrowck|runtime-optimized",
            *(extra_args or []),
            str(src_file),
            "-o",
            str(out_rlib),
        ]
        proc = subprocess.run(cmd, env=env, capture_output=True, text=True, timeout=60)

        built_mir = ""
        post_cleanup_mir = ""
        runtime_mir = ""
        for mf in sorted(dump_dir.glob("*.mir")):
            name = mf.name
            if f".{fn_name}." not in name and not name.startswith(f"probe.{fn_name}."):
                continue
            content = _scrub_text(mf.read_text(encoding="utf-8"), tmp_path)
            if name.endswith(".built.after.mir"):
                built_mir = _extract_fn_mir(content, fn_name) or content
            elif "CleanupPostBorrowck.after.mir" in name:
                post_cleanup_mir = _extract_fn_mir(content, fn_name) or content
            elif name.endswith(".runtime-optimized.after.mir"):
                runtime_mir = _extract_fn_mir(content, fn_name) or content

        # Note: in rustc MIR pretty-printing, FakeBorrowKind::Shallow prints as
        # `&fake shallow <place>` while FakeBorrowKind::Deep prints as `&fake <place>`.
        fake_borrows = sorted(
            set(re.findall(r"&fake(?:\s+shallow)?\s+[^\n;]+", built_mir))
        )
        fake_reads = sorted(set(re.findall(r"FakeRead\([^\n;]+\)", built_mir)))
        post_fake_borrows = sorted(
            set(re.findall(r"&fake(?:\s+shallow)?\s+[^\n;]+", post_cleanup_mir))
        )
        post_fake_reads = sorted(
            set(re.findall(r"FakeRead\([^\n;]+\)", post_cleanup_mir))
        )

        return {
            "compile_rc": proc.returncode,
            "error_codes": _extract_error_codes(proc.stderr),
            "stderr_head": _stderr_summary_lines(proc.stderr, tmp_path),
            "fake_borrows_in_built_mir": fake_borrows,
            "fake_reads_in_built_mir": fake_reads,
            "fake_borrows_after_cleanup_post_borrowck": post_fake_borrows,
            "fake_reads_after_cleanup_post_borrowck": post_fake_reads,
            "built_mir": built_mir,
            "post_cleanup_mir": post_cleanup_mir,
            "runtime_mir": runtime_mir,
        }


def _build_hermetic_miri_sysroot(
    rustc: str, toolchain_root: Path, env: dict[str, str], sysroot_dir: Path
) -> None:
    """Build a self-contained offline Miri sysroot (core + compiler_builtins + alloc)
    directly from the active rustc toolchain's bundled library sources."""
    host_proc = subprocess.run(
        [rustc, "-vV"], env=env, capture_output=True, text=True, check=True, timeout=15
    )
    host_triple = "x86_64-unknown-linux-gnu"
    for line in host_proc.stdout.splitlines():
        if line.startswith("host:"):
            host_triple = line.split(":", 1)[1].strip()
            break

    lib_src = toolchain_root / "lib" / "rustlib" / "src" / "rust" / "library"
    libdir = sysroot_dir / "lib" / "rustlib" / host_triple / "lib"
    libdir.mkdir(parents=True, exist_ok=True)

    subprocess.run(
        [
            rustc,
            "--edition=2024",
            "--crate-name=core",
            "--crate-type=rlib",
            "-Zalways-encode-mir",
            "-Cpanic=abort",
            "--cap-lints=allow",
            str(lib_src / "core" / "src" / "lib.rs"),
            "-o",
            str(libdir / "libcore.rlib"),
        ],
        env=env,
        check=True,
        capture_output=True,
        text=True,
        timeout=120,
    )

    cb_rs = sysroot_dir / "compiler_builtins_stub.rs"
    cb_rs.write_text(
        "#![feature(compiler_builtins)]\n#![no_std]\n#![compiler_builtins]\n",
        encoding="utf-8",
    )
    subprocess.run(
        [
            rustc,
            "--edition=2024",
            "--crate-name=compiler_builtins",
            "--crate-type=rlib",
            "--sysroot",
            str(sysroot_dir),
            "-Zalways-encode-mir",
            "-Cpanic=abort",
            "--cap-lints=allow",
            str(cb_rs),
            "-o",
            str(libdir / "libcompiler_builtins.rlib"),
        ],
        env=env,
        check=True,
        capture_output=True,
        text=True,
        timeout=30,
    )

    subprocess.run(
        [
            rustc,
            "--edition=2024",
            "--crate-name=alloc",
            "--crate-type=rlib",
            "--sysroot",
            str(sysroot_dir),
            "-Zalways-encode-mir",
            "-Cpanic=abort",
            "--cap-lints=allow",
            str(lib_src / "alloc" / "src" / "lib.rs"),
            "-o",
            str(libdir / "liballoc.rlib"),
        ],
        env=env,
        check=True,
        capture_output=True,
        text=True,
        timeout=90,
    )


MIRI_PREAMBLE = """#![no_std]
#![no_main]
extern crate alloc;
use alloc::{format, string::{String, ToString}, vec::Vec};
use core::{alloc::{GlobalAlloc, Layout}, cell::RefCell};

unsafe extern "Rust" {
    fn miri_alloc(size: usize, align: usize) -> *mut u8;
    fn miri_dealloc(ptr: *mut u8, size: usize, align: usize);
    fn miri_write_to_stdout(bytes: &[u8]);
}

struct MiriHostAlloc;
unsafe impl GlobalAlloc for MiriHostAlloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        unsafe { miri_alloc(layout.size(), layout.align()) }
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { miri_dealloc(ptr, layout.size(), layout.align()) }
    }
}

#[global_allocator]
static GLOBAL_MIRI_ALLOC: MiriHostAlloc = MiriHostAlloc;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo<'_>) -> ! {
    loop {}
}

fn miri_println(s: &str) {
    unsafe {
        miri_write_to_stdout(s.as_bytes());
        miri_write_to_stdout(b"\\n");
    }
}
"""


def _run_hermetic_miri(
    miri_bin: str,
    miri_sysroot: Path,
    env: dict[str, str],
    body_rs: str,
    extra_miri_args: list[str] | None = None,
) -> dict[str, Any]:
    with tempfile.TemporaryDirectory() as td:
        tmp_path = Path(td)
        src_file = tmp_path / "miri_case.rs"
        src_file.write_text(MIRI_PREAMBLE + "\n" + body_rs, encoding="utf-8")
        cmd = [
            miri_bin,
            "--sysroot",
            str(miri_sysroot),
            "--edition=2024",
            "-Cpanic=abort",
            *(extra_miri_args or []),
            str(src_file),
        ]
        proc = subprocess.run(cmd, env=env, capture_output=True, text=True, timeout=60)
        return {
            "rc": proc.returncode,
            "stdout_lines": [
                _scrub_text(l.strip(), tmp_path)
                for l in proc.stdout.splitlines()
                if l.strip()
            ],
            "ub_summary": _stderr_summary_lines(proc.stderr, tmp_path, limit=5),
        }


def run_probe_1_fake_borrow_matrix(rustc: str, env: dict[str, str]) -> dict[str, Any]:
    cases: dict[str, tuple[str, str]] = {
        "mutate_switched_enum_with_binding_in_guard": (
            "target",
            """
pub fn target(mut x: Option<i32>) -> i32 {
    match x {
        Some(_v) if { x = None; false } => 1,
        Some(v) => v,
        None => 0,
    }
}
""",
        ),
        "mutate_switched_enum_wildcard_payload_in_guard": (
            "target",
            """
pub fn target(mut x: Option<i32>) -> i32 {
    match x {
        Some(_) if { x = None; false } => 1,
        Some(v) => v,
        None => 0,
    }
}
""",
        ),
        "mutate_unswitched_payload_projection_allowed": (
            "target",
            """
pub fn target(mut x: (Option<i32>, bool)) -> i32 {
    match x {
        (Some(_), false) => 1,
        _ if {
            if let Some(ref mut y) = x.0 {
                *y += 10;
            }
            false
        } => 2,
        (Some(v), true) => v,
        (None, _) => 0,
    }
}
""",
        ),
        "mutate_unswitched_local_in_guard_allowed": (
            "target",
            """
pub fn target(mut u: bool) -> bool {
    match u {
        _ if { u = true; false } => false,
        x => x,
    }
}
""",
        ),
        "mutate_deref_prefix_bound_in_guard": (
            "target",
            """
pub fn target<'a>(mut x: &'a i32, alt: &'a i32) -> i32 {
    match *x {
        y if { y == 1 && { x = alt; true } } => y,
        _ => 3,
    }
}
""",
        ),
        "mutate_slice_ref_prefix_in_guard": (
            "target",
            """
pub fn target<'a>(mut x: &'a [i32], empty: &'a [i32]) -> i32 {
    match x {
        [head, ..] if { let _ = head; x = empty; false } => 1,
        _ => 0,
    }
}
""",
        ),
        "mutate_box_deref_pat_in_guard_shallow_pair": (
            "target",
            """
#![feature(deref_patterns)]
pub fn target(mut b: Box<bool>) -> u32 {
    match b {
        deref!(true) => 1,
        _ if { *b = true; false } => 2,
        deref!(false) => 3,
    }
}
""",
        ),
        "mutate_custom_deref_pure_in_guard_deep_borrow": (
            "target",
            """
#![feature(deref_patterns, deref_pure_trait)]
use core::ops::{Deref, DerefPure};

pub struct SmartBool(pub bool);

impl Deref for SmartBool {
    type Target = bool;
    fn deref(&self) -> &bool {
        &self.0
    }
}

unsafe impl DerefPure for SmartBool {}

pub fn target(mut s: SmartBool) -> u32 {
    match s {
        deref!(true) => 1,
        _ if { s.0 = true; false } => 2,
        deref!(false) => 3,
    }
}
""",
        ),
        "mutate_unswitched_box_inner_without_deref_pat_allowed": (
            "target",
            """
pub fn target(mut b: Box<bool>) -> bool {
    match b {
        _ if { *b = true; false } => false,
        moved_box => *moved_box,
    }
}
""",
        ),
    }

    results: dict[str, Any] = {}
    for key, (fn_name, code) in cases.items():
        info = _compile_and_inspect_mir(rustc, env, code, fn_name)
        results[key] = {
            "compile_rc": info["compile_rc"],
            "error_codes": info["error_codes"],
            "stderr_head": info["stderr_head"],
            "fake_borrows_in_built_mir": info["fake_borrows_in_built_mir"],
            "fake_reads_in_built_mir": info["fake_reads_in_built_mir"],
            "fake_borrows_after_cleanup_post_borrowck": info[
                "fake_borrows_after_cleanup_post_borrowck"
            ],
            "fake_reads_after_cleanup_post_borrowck": info[
                "fake_reads_after_cleanup_post_borrowck"
            ],
        }
    return results


SHARED_OR_GUARD_LOGIC = """
struct DropTok<'a> {
    label: &'static str,
    id: u32,
    log: &'a RefCell<Vec<String>>,
}

impl<'a> Drop for DropTok<'a> {
    fn drop(&mut self) {
        self.log.borrow_mut().push(format!("drop:{}:{}", self.label, self.id));
    }
}

fn or_guard_reeval() -> (i32, Vec<String>) {
    let log = RefCell::new(Vec::new());
    let scrut = (Some(1), Some(2));
    let res = match scrut {
        (Some(x), _) | (_, Some(x)) if {
            log.borrow_mut().push(format!("guard:{x}"));
            x == 2
        } => x * 10,
        _ => 0,
    };
    (res, log.into_inner())
}

fn run_drop_branch(which: usize) -> Vec<String> {
    let log = RefCell::new(Vec::new());
    {
        let t1 = DropTok { label: "first", id: 1, log: &log };
        let t2 = DropTok { label: "second", id: 2, log: &log };
        let scrut: Result<(DropTok<'_>, DropTok<'_>), (DropTok<'_>, DropTok<'_>)> =
            if which == 0 { Ok((t1, t2)) } else { Err((t1, t2)) };
        match scrut {
            Ok((a, b)) | Err((b, a)) if a.id > 0 && b.id > 0 => {
                log.borrow_mut().push(format!("arm:a={}:b={}", a.label, b.label));
            }
            _ => {
                log.borrow_mut().push("fallback".to_string());
            }
        }
    }
    log.into_inner()
}

fn run_guard_fail_no_premature_move() -> Vec<String> {
    let log = RefCell::new(Vec::new());
    {
        let t1 = DropTok { label: "left", id: 1, log: &log };
        let t2 = DropTok { label: "right", id: 2, log: &log };
        let scrut: Result<(DropTok<'_>, DropTok<'_>), (DropTok<'_>, DropTok<'_>)> =
            Ok((t1, t2));
        match scrut {
            Ok((a, b)) | Err((b, a)) if {
                log.borrow_mut().push(format!("guard_fail:a={}:b={}", a.label, b.label));
                false
            } => {
                log.borrow_mut().push("unreachable_arm".to_string());
            }
            Ok((x, y)) | Err((x, y)) => {
                log.borrow_mut().push(format!("fallback_arm:x={}:y={}", x.label, y.label));
            }
        }
    }
    log.into_inner()
}

fn unswitched_mut_in_guard(mut u: bool) -> bool {
    match u {
        _ if { u = true; false } => false,
        x => x,
    }
}

fn unswitched_payload_mut_in_guard() -> i32 {
    let mut pair = (Some(5), true);
    match pair {
        (Some(_), false) => 0,
        _ if {
            if let Some(ref mut inner) = pair.0 {
                *inner += 37;
            }
            false
        } => 0,
        (Some(v), true) => v,
        (None, _) => -1,
    }
}
"""


def run_probe_2_or_pattern_guards_and_drop_order(
    rustc: str, miri_bin: str, miri_sysroot: Path, env: dict[str, str]
) -> dict[str, Any]:
    native_prog = (
        "use std::cell::RefCell;\n"
        + SHARED_OR_GUARD_LOGIC
        + """
fn main() {
    let (res, glog) = or_guard_reeval();
    println!("OR_GUARD_RES={res} LOG={glog:?}");
    println!("DROP_BRANCH0={:?}", run_drop_branch(0));
    println!("DROP_BRANCH1={:?}", run_drop_branch(1));
    println!("GUARD_FAIL_NONCOPY={:?}", run_guard_fail_no_premature_move());
    println!("UNSWITCHED_MUT_GUARD={}", unswitched_mut_in_guard(false));
    println!("UNSWITCHED_PAYLOAD_MUT_GUARD={}", unswitched_payload_mut_in_guard());
}
"""
    )
    miri_body = (
        SHARED_OR_GUARD_LOGIC
        + """
#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let (res, glog) = or_guard_reeval();
    miri_println(&format!("OR_GUARD_RES={res} LOG={glog:?}"));
    miri_println(&format!("DROP_BRANCH0={:?}", run_drop_branch(0)));
    miri_println(&format!("DROP_BRANCH1={:?}", run_drop_branch(1)));
    miri_println(&format!("GUARD_FAIL_NONCOPY={:?}", run_guard_fail_no_premature_move()));
    miri_println(&format!("UNSWITCHED_MUT_GUARD={}", unswitched_mut_in_guard(false)));
    miri_println(&format!("UNSWITCHED_PAYLOAD_MUT_GUARD={}", unswitched_payload_mut_in_guard()));
    0
}
"""
    )

    with tempfile.TemporaryDirectory() as td:
        tmp_path = Path(td)
        src_file = tmp_path / "main.rs"
        bin_file = tmp_path / "probe_bin"
        src_file.write_text(native_prog, encoding="utf-8")
        cproc = subprocess.run(
            [rustc, "--edition=2024", str(src_file), "-o", str(bin_file)],
            env=env,
            capture_output=True,
            text=True,
            timeout=60,
        )
        rproc = subprocess.run(
            [str(bin_file)],
            env=env,
            capture_output=True,
            text=True,
            timeout=30,
        )
        native_stdout = [l.strip() for l in rproc.stdout.splitlines() if l.strip()]

    miri_sb = _run_hermetic_miri(miri_bin, miri_sysroot, env, miri_body, extra_miri_args=[])
    miri_tb = _run_hermetic_miri(
        miri_bin, miri_sysroot, env, miri_body, extra_miri_args=["-Zmiri-tree-borrows"]
    )

    return {
        "compile_rc": cproc.returncode,
        "native_rc": rproc.returncode,
        "native_stdout": native_stdout,
        "miri_stacked_borrows_rc": miri_sb["rc"],
        "miri_stacked_borrows_stdout": miri_sb["stdout_lines"],
        "miri_tree_borrows_rc": miri_tb["rc"],
        "miri_tree_borrows_stdout": miri_tb["stdout_lines"],
        "native_equals_miri_stacked_and_tree": (
            miri_sb["rc"] == 0
            and miri_tb["rc"] == 0
            and native_stdout == miri_sb["stdout_lines"] == miri_tb["stdout_lines"]
        ),
    }


def run_probe_3_uninhabited_and_non_exhaustive(
    rustc: str, miri_bin: str, miri_sysroot: Path, env: dict[str, str]
) -> dict[str, Any]:
    upstream_src = """
pub enum Void {}

#[non_exhaustive]
pub enum SingleNonExh {
    Only,
}

pub enum SingleExh {
    Only,
}
"""
    downstream_cases: dict[str, tuple[str, str]] = {
        "match_void_by_val_empty": (
            "f",
            "pub fn f(v: upstream_defs::Void) -> i32 { match v {} }\n",
        ),
        "match_void_ref_empty": (
            "f",
            "pub fn f(v: &upstream_defs::Void) -> i32 { match *v {} }\n",
        ),
        "match_void_raw_ptr_empty": (
            "f",
            "pub unsafe fn f(p: *const upstream_defs::Void) -> i32 { unsafe { match *p {} } }\n",
        ),
        "match_void_raw_ptr_wildcard": (
            "f",
            "pub unsafe fn f(p: *const upstream_defs::Void) -> i32 { unsafe { match *p { _ => 99 } } }\n",
        ),
        "match_non_exh_single_no_wild": (
            "f",
            """
pub fn f(x: upstream_defs::SingleNonExh) -> i32 {
    match x {
        upstream_defs::SingleNonExh::Only => 1,
    }
}
""",
        ),
        "match_non_exh_single_with_wild": (
            "f",
            """
pub fn f(x: upstream_defs::SingleNonExh) -> i32 {
    match x {
        upstream_defs::SingleNonExh::Only => 1,
        _ => 2,
    }
}
""",
        ),
        "match_exh_single_no_wild": (
            "f",
            """
pub fn f(x: upstream_defs::SingleExh) -> i32 {
    match x {
        upstream_defs::SingleExh::Only => 1,
    }
}
""",
        ),
    }

    downstream_matrix: dict[str, Any] = {}
    with tempfile.TemporaryDirectory() as td:
        tmp_path = Path(td)
        up_rs = tmp_path / "upstream_defs.rs"
        up_rlib = tmp_path / "libupstream_defs.rlib"
        up_rs.write_text(upstream_src, encoding="utf-8")
        up_proc = subprocess.run(
            [
                rustc,
                "--edition=2024",
                "--crate-type=rlib",
                "--crate-name=upstream_defs",
                str(up_rs),
                "-o",
                str(up_rlib),
            ],
            env=env,
            capture_output=True,
            text=True,
            timeout=60,
        )
        upstream_rc = up_proc.returncode

        for key, (fn_name, code) in downstream_cases.items():
            info = _compile_and_inspect_mir(
                rustc,
                env,
                code,
                fn_name,
                extra_args=["--extern", f"upstream_defs={up_rlib}"],
            )
            built = info["built_mir"]
            post = info["post_cleanup_mir"] or built
            downstream_matrix[key] = {
                "compile_rc": info["compile_rc"],
                "error_codes": info["error_codes"],
                "stderr_head": info["stderr_head"],
                "has_discriminant_read": "discriminant(" in post,
                "has_switch_int": "switchInt(" in post,
                "has_unreachable": "unreachable;" in post,
                "has_fake_read_matched_in_built": "FakeRead(ForMatchedPlace(" in built,
                "has_place_mention_in_post_cleanup": "PlaceMention(" in post,
            }

    miri_cases = {
        "raw_wildcard_null": """
pub enum Void {}
#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let p: *const Void = core::ptr::null();
    let res = unsafe { match *p { _ => 99 } };
    miri_println(&format!("RES={res}"));
    0
}
""",
        "raw_wildcard_valid": """
pub enum Void {}
#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let backing = 0u8;
    let p: *const Void = (&raw const backing).cast::<Void>();
    let res = unsafe { match *p { _ => 99 } };
    miri_println(&format!("RES={res}"));
    0
}
""",
        "ref_empty_from_valid": """
pub enum Void {}
#[allow(unreachable_code)]
#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let backing = 0u8;
    let p: *const Void = (&raw const backing).cast::<Void>();
    let res: i32 = unsafe {
        let r: &Void = &*p;
        match *r {}
    };
    miri_println(&format!("RES={res}"));
    0
}
""",
    }
    miri_results: dict[str, Any] = {}
    for k, body in miri_cases.items():
        mres = _run_hermetic_miri(
            miri_bin, miri_sysroot, env, body, extra_miri_args=["-Zmiri-tree-borrows"]
        )
        miri_results[k] = {
            "rc": mres["rc"],
            "stdout": "\n".join(mres["stdout_lines"]),
            "ub_summary": mres["ub_summary"],
        }

    return {
        "upstream_compile_rc": upstream_rc,
        "downstream_matrix": downstream_matrix,
        "miri_void_tests": miri_results,
    }


def run_probe_4_slice_and_range_mir(rustc: str, env: dict[str, str]) -> dict[str, Any]:
    src = """
pub fn classify_slice_and_ranges(xs: &[u32], tag: i32) -> u32 {
    let s_part = match xs {
        [] => 0,
        [only] => *only,
        [first, mid @ .., last] => first.wrapping_add(*last).wrapping_add(mid.len() as u32),
    };
    let r_part = match tag {
        ..=-1 => 10,
        0..=9 => 20,
        10..20 => 30,
        20.. => 40,
    };
    s_part.wrapping_add(r_part)
}

pub fn classify_fixed_array(arr: &[u32; 4]) -> u32 {
    match arr {
        [0, mid @ .., last] => (mid.len() as u32).wrapping_add(*last),
        [a, _, _, d] => a.wrapping_add(*d),
    }
}
"""
    slice_info = _compile_and_inspect_mir(rustc, env, src, "classify_slice_and_ranges")
    array_info = _compile_and_inspect_mir(rustc, env, src, "classify_fixed_array")
    post_slice = slice_info["post_cleanup_mir"]
    post_array = array_info["post_cleanup_mir"]

    cmp_ops = sorted(set(re.findall(r"\b(?:Eq|Ge|Le|Lt|Gt)\(", post_slice)))
    return {
        "compile_rc": slice_info["compile_rc"],
        "slice_and_range_fn": {
            "has_ptr_metadata": "PtrMetadata(" in post_slice,
            "has_legacy_rvalue_len": "Len(" in post_slice,
            "has_subslice_from_end_proj": "[1:-1]" in post_slice,
            "has_constant_index_from_end": "[-1 of 2]" in post_slice,
            "has_constant_index_prefix": "[0 of 2]" in post_slice,
            "range_and_len_cmp_ops": cmp_ops,
            "switch_int_count": post_slice.count("switchInt("),
        },
        "fixed_array_fn": {
            "has_ptr_metadata": "PtrMetadata(" in post_array,
            "has_static_subslice_proj": "[1..3]" in post_array or "[1:3]" in post_array,
            "has_static_suffix_index": "[3 of 4]" in post_array,
            "has_from_end_index": "[-" in post_array,
        },
    }


def verify_invariants(payload: dict[str, Any]) -> None:
    p1 = payload["probe_1_fake_borrow_matrix"]
    assert p1["mutate_switched_enum_with_binding_in_guard"]["error_codes"] == ["error[E0506]"]
    assert p1["mutate_switched_enum_wildcard_payload_in_guard"]["error_codes"] == ["error[E0510]"]
    assert p1["mutate_deref_prefix_bound_in_guard"]["error_codes"] == ["error[E0510]"]
    assert p1["mutate_slice_ref_prefix_in_guard"]["error_codes"] == ["error[E0510]"]
    assert p1["mutate_box_deref_pat_in_guard_shallow_pair"]["fake_borrows_in_built_mir"] == [
        "&fake shallow (*_1)",
        "&fake shallow _1",
    ]
    assert p1["mutate_custom_deref_pure_in_guard_deep_borrow"]["fake_borrows_in_built_mir"] == [
        "&fake _1"
    ]
    assert p1["mutate_unswitched_local_in_guard_allowed"]["compile_rc"] == 0
    assert p1["mutate_unswitched_box_inner_without_deref_pat_allowed"]["compile_rc"] == 0
    assert p1["mutate_unswitched_payload_projection_allowed"]["compile_rc"] == 0
    for case_data in p1.values():
        assert case_data["fake_borrows_after_cleanup_post_borrowck"] == []
        assert case_data["fake_reads_after_cleanup_post_borrowck"] == []

    p2 = payload["probe_2_or_pattern_guards_and_drop_order"]
    assert p2["native_equals_miri_stacked_and_tree"] is True
    assert p2["native_rc"] == 0 and p2["miri_stacked_borrows_rc"] == 0 and p2["miri_tree_borrows_rc"] == 0

    p3 = payload["probe_3_uninhabited_and_non_exhaustive"]
    dm = p3["downstream_matrix"]
    assert dm["match_non_exh_single_no_wild"]["error_codes"] == ["error[E0004]"]
    assert dm["match_non_exh_single_with_wild"]["has_discriminant_read"] is True
    assert dm["match_non_exh_single_with_wild"]["has_switch_int"] is True
    assert dm["match_exh_single_no_wild"]["has_discriminant_read"] is False
    assert dm["match_exh_single_no_wild"]["has_switch_int"] is False
    assert dm["match_void_raw_ptr_wildcard"]["has_unreachable"] is False
    mv = p3["miri_void_tests"]
    assert mv["raw_wildcard_null"]["rc"] == 0 and mv["raw_wildcard_null"]["stdout"] == "RES=99"
    assert mv["raw_wildcard_valid"]["rc"] == 0 and mv["raw_wildcard_valid"]["stdout"] == "RES=99"
    assert mv["ref_empty_from_valid"]["rc"] == 1

    p4 = payload["probe_4_slice_and_range_mir"]
    assert p4["slice_and_range_fn"]["has_ptr_metadata"] is True
    assert p4["slice_and_range_fn"]["has_legacy_rvalue_len"] is False
    assert p4["fixed_array_fn"]["has_ptr_metadata"] is False


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        "--out",
        dest="output",
        default="",
        help="Optional path to write JSON output.",
    )
    args = parser.parse_args(argv)

    rustc, miri_bin, toolchain_root = _find_rustc_and_miri()
    env = _clean_env()

    ver_proc = subprocess.run(
        [rustc, "--version", "--verbose"],
        env=env,
        capture_output=True,
        text=True,
        check=True,
        timeout=15,
    )
    miri_ver_proc = subprocess.run(
        [miri_bin, "--version"],
        env=env,
        capture_output=True,
        text=True,
        check=True,
        timeout=15,
    )

    with tempfile.TemporaryDirectory() as sysroot_td:
        miri_sysroot = Path(sysroot_td) / "miri_sysroot"
        _build_hermetic_miri_sysroot(rustc, toolchain_root, env, miri_sysroot)

        payload = {
            "rustc_version_verbose": _scrub_text(ver_proc.stdout.strip()),
            "miri_version": _scrub_text(miri_ver_proc.stdout.strip()),
            "probe_1_fake_borrow_matrix": run_probe_1_fake_borrow_matrix(rustc, env),
            "probe_2_or_pattern_guards_and_drop_order": run_probe_2_or_pattern_guards_and_drop_order(
                rustc, miri_bin, miri_sysroot, env
            ),
            "probe_3_uninhabited_and_non_exhaustive": run_probe_3_uninhabited_and_non_exhaustive(
                rustc, miri_bin, miri_sysroot, env
            ),
            "probe_4_slice_and_range_mir": run_probe_4_slice_and_range_mir(rustc, env),
        }

    verify_invariants(payload)
    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.output:
        out_path = Path(args.output)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(rendered, encoding="utf-8")
        print(f"wrote {out_path} ({len(rendered)} bytes)")
    else:
        sys.stdout.write(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
