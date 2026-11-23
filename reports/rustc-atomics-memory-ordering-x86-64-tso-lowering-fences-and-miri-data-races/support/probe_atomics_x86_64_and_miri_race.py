#!/usr/bin/env python3
"""Reproducible live rustc LLVM IR / x86_64 ASM lowering and Miri race probe."""

from __future__ import annotations

import json
import os
import pathlib
import re
import subprocess
import tempfile
from datetime import datetime, timezone

RUST_CODEGEN_PROBE = r"""
#![no_std]
#![crate_type = "lib"]

use core::sync::atomic::{AtomicU8, AtomicU32, AtomicU64, Ordering, compiler_fence, fence};

#[unsafe(no_mangle)]
pub extern "C" fn load_relaxed(a: &AtomicU64) -> u64 {
    a.load(Ordering::Relaxed)
}

#[unsafe(no_mangle)]
pub extern "C" fn load_acquire(a: &AtomicU64) -> u64 {
    a.load(Ordering::Acquire)
}

#[unsafe(no_mangle)]
pub extern "C" fn load_seqcst(a: &AtomicU64) -> u64 {
    a.load(Ordering::SeqCst)
}

#[unsafe(no_mangle)]
pub extern "C" fn store_relaxed(a: &AtomicU64, v: u64) {
    a.store(v, Ordering::Relaxed);
}

#[unsafe(no_mangle)]
pub extern "C" fn store_release(a: &AtomicU64, v: u64) {
    a.store(v, Ordering::Release);
}

#[unsafe(no_mangle)]
pub extern "C" fn store_seqcst(a: &AtomicU64, v: u64) {
    a.store(v, Ordering::SeqCst);
}

#[unsafe(no_mangle)]
pub extern "C" fn swap_relaxed(a: &AtomicU64, v: u64) -> u64 {
    a.swap(v, Ordering::Relaxed)
}

#[unsafe(no_mangle)]
pub extern "C" fn swap_acqrel(a: &AtomicU64, v: u64) -> u64 {
    a.swap(v, Ordering::AcqRel)
}

#[unsafe(no_mangle)]
pub extern "C" fn swap_seqcst(a: &AtomicU64, v: u64) -> u64 {
    a.swap(v, Ordering::SeqCst)
}

#[unsafe(no_mangle)]
pub extern "C" fn fetch_add_relaxed(a: &AtomicU64, v: u64) -> u64 {
    a.fetch_add(v, Ordering::Relaxed)
}

#[unsafe(no_mangle)]
pub extern "C" fn fetch_add_acquire(a: &AtomicU64, v: u64) -> u64 {
    a.fetch_add(v, Ordering::Acquire)
}

#[unsafe(no_mangle)]
pub extern "C" fn fetch_add_release(a: &AtomicU64, v: u64) -> u64 {
    a.fetch_add(v, Ordering::Release)
}

#[unsafe(no_mangle)]
pub extern "C" fn fetch_add_acqrel(a: &AtomicU64, v: u64) -> u64 {
    a.fetch_add(v, Ordering::AcqRel)
}

#[unsafe(no_mangle)]
pub extern "C" fn fetch_add_seqcst(a: &AtomicU64, v: u64) -> u64 {
    a.fetch_add(v, Ordering::SeqCst)
}

#[unsafe(no_mangle)]
pub extern "C" fn fetch_or_used_acqrel(a: &AtomicU64, v: u64) -> u64 {
    a.fetch_or(v, Ordering::AcqRel)
}

#[unsafe(no_mangle)]
pub extern "C" fn fetch_or_discarded_acqrel(a: &AtomicU64, v: u64) {
    let _ = a.fetch_or(v, Ordering::AcqRel);
}

#[unsafe(no_mangle)]
pub extern "C" fn cas_strong_acqrel_acquire(a: &AtomicU64, cur: u64, new: u64) -> bool {
    a.compare_exchange(cur, new, Ordering::AcqRel, Ordering::Acquire).is_ok()
}

#[unsafe(no_mangle)]
pub extern "C" fn cas_strong_seqcst_seqcst(a: &AtomicU64, cur: u64, new: u64) -> bool {
    a.compare_exchange(cur, new, Ordering::SeqCst, Ordering::SeqCst).is_ok()
}

#[unsafe(no_mangle)]
pub extern "C" fn cas_weak_relaxed_relaxed(a: &AtomicU64, cur: u64, new: u64) -> bool {
    a.compare_exchange_weak(cur, new, Ordering::Relaxed, Ordering::Relaxed).is_ok()
}

#[unsafe(no_mangle)]
pub extern "C" fn cas_weak_acqrel_acquire(a: &AtomicU64, cur: u64, new: u64) -> bool {
    a.compare_exchange_weak(cur, new, Ordering::AcqRel, Ordering::Acquire).is_ok()
}

#[unsafe(no_mangle)]
pub extern "C" fn cas_u32_strong_acqrel_acquire(a: &AtomicU32, cur: u32, new: u32) -> bool {
    a.compare_exchange(cur, new, Ordering::AcqRel, Ordering::Acquire).is_ok()
}

#[unsafe(no_mangle)]
pub extern "C" fn fetch_and_u8_discarded_acqrel(a: &AtomicU8, v: u8) {
    let _ = a.fetch_and(v, Ordering::AcqRel);
}

#[unsafe(no_mangle)]
pub extern "C" fn hw_fence_acquire() {
    fence(Ordering::Acquire);
}

#[unsafe(no_mangle)]
pub extern "C" fn hw_fence_release() {
    fence(Ordering::Release);
}

#[unsafe(no_mangle)]
pub extern "C" fn hw_fence_acqrel() {
    fence(Ordering::AcqRel);
}

#[unsafe(no_mangle)]
pub extern "C" fn hw_fence_seqcst() {
    fence(Ordering::SeqCst);
}

#[unsafe(no_mangle)]
pub extern "C" fn comp_fence_acquire_only() {
    compiler_fence(Ordering::Acquire);
}

#[unsafe(no_mangle)]
pub extern "C" fn comp_fence_seqcst_only() {
    compiler_fence(Ordering::SeqCst);
}

#[unsafe(no_mangle)]
pub extern "C" fn comp_fence_seqcst_two_loads(a: &AtomicU64) -> u64 {
    let x = a.load(Ordering::Relaxed);
    compiler_fence(Ordering::SeqCst);
    let y = a.load(Ordering::Relaxed);
    x.wrapping_add(y)
}

#[unsafe(no_mangle)]
pub extern "C" fn no_fence_two_loads(a: &AtomicU64) -> u64 {
    let x = a.load(Ordering::Relaxed);
    let y = a.load(Ordering::Relaxed);
    x.wrapping_add(y)
}

#[unsafe(no_mangle)]
pub extern "C" fn hw_fence_acqrel_with_loads(a: &AtomicU64) -> u64 {
    let x = a.load(Ordering::Relaxed);
    fence(Ordering::AcqRel);
    let y = a.load(Ordering::Relaxed);
    x.wrapping_add(y)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn raw_ptr_two_loads_no_fence(p: *const u64) -> u64 {
    let x = unsafe { *p };
    let y = unsafe { *p };
    x.wrapping_add(y)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn raw_ptr_two_loads_with_cfence(p: *const u64) -> u64 {
    let x = unsafe { *p };
    compiler_fence(Ordering::SeqCst);
    let y = unsafe { *p };
    x.wrapping_add(y)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn raw_ptr_two_stores_no_fence(p: *mut u64) {
    unsafe {
        *p = 1;
        *p = 2;
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn raw_ptr_two_stores_with_cfence(p: *mut u64) {
    unsafe {
        *p = 1;
        compiler_fence(Ordering::SeqCst);
        *p = 2;
    }
}
"""

MIRI_PROGRAMS = {
    "miri_release_acquire_message_passing_ok": r"""
use std::cell::UnsafeCell;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread;

struct Shared {
    data: UnsafeCell<u64>,
    flag: AtomicU64,
}
unsafe impl Sync for Shared {}

fn main() {
    let shared = Arc::new(Shared {
        data: UnsafeCell::new(0),
        flag: AtomicU64::new(0),
    });
    let s_writer = Arc::clone(&shared);
    let handle = thread::spawn(move || {
        unsafe { *s_writer.data.get() = 42; }
        s_writer.flag.store(1, Ordering::Release);
    });
    while shared.flag.load(Ordering::Acquire) == 0 {
        thread::yield_now();
    }
    let observed = unsafe { *shared.data.get() };
    handle.join().unwrap();
    assert_eq!(observed, 42);
    println!("MIRI_ACQ_REL_OK={observed}");
}
""",
    "miri_relaxed_unsynchronized_data_race_ub": r"""
use std::cell::UnsafeCell;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread;

struct Shared {
    data: UnsafeCell<u64>,
    flag: AtomicU64,
}
unsafe impl Sync for Shared {}

fn main() {
    let shared = Arc::new(Shared {
        data: UnsafeCell::new(0),
        flag: AtomicU64::new(0),
    });
    let s_writer = Arc::clone(&shared);
    let handle = thread::spawn(move || {
        unsafe { *s_writer.data.get() = 42; }
        s_writer.flag.store(1, Ordering::Relaxed);
    });
    while shared.flag.load(Ordering::Relaxed) == 0 {
        thread::yield_now();
    }
    let observed = unsafe { *shared.data.get() };
    handle.join().unwrap();
    println!("MIRI_RELAXED_UNREACHABLE={observed}");
}
""",
    "miri_release_fence_acquire_fence_ok": r"""
use std::cell::UnsafeCell;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering, fence};
use std::thread;

struct Shared {
    data: UnsafeCell<u64>,
    flag: AtomicU64,
}
unsafe impl Sync for Shared {}

fn main() {
    let shared = Arc::new(Shared {
        data: UnsafeCell::new(0),
        flag: AtomicU64::new(0),
    });
    let s_writer = Arc::clone(&shared);
    let handle = thread::spawn(move || {
        unsafe { *s_writer.data.get() = 42; }
        fence(Ordering::Release);
        s_writer.flag.store(1, Ordering::Relaxed);
    });
    while shared.flag.load(Ordering::Relaxed) == 0 {
        thread::yield_now();
    }
    fence(Ordering::Acquire);
    let observed = unsafe { *shared.data.get() };
    handle.join().unwrap();
    assert_eq!(observed, 42);
    println!("MIRI_FENCE_ACQ_REL_OK={observed}");
}
""",
    "miri_compiler_fence_non_sync_data_race_ub": r"""
use std::cell::UnsafeCell;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering, compiler_fence};
use std::thread;

struct Shared {
    data: UnsafeCell<u64>,
    flag: AtomicU64,
}
unsafe impl Sync for Shared {}

fn main() {
    let shared = Arc::new(Shared {
        data: UnsafeCell::new(0),
        flag: AtomicU64::new(0),
    });
    let s_writer = Arc::clone(&shared);
    let handle = thread::spawn(move || {
        unsafe { *s_writer.data.get() = 42; }
        compiler_fence(Ordering::SeqCst);
        s_writer.flag.store(1, Ordering::Relaxed);
    });
    while shared.flag.load(Ordering::Relaxed) == 0 {
        thread::yield_now();
    }
    compiler_fence(Ordering::SeqCst);
    let observed = unsafe { *shared.data.get() };
    handle.join().unwrap();
    println!("MIRI_CFENCE_UNREACHABLE={observed}");
}
""",
    "miri_cas_weak_spurious_failure_check": r"""
use std::sync::atomic::{AtomicU64, Ordering};

fn main() {
    let a = AtomicU64::new(0);
    let mut spurious_failures: u64 = 0;
    for i in 0..64u64 {
        if a.compare_exchange_weak(i, i + 1, Ordering::AcqRel, Ordering::Acquire).is_err() {
            spurious_failures += 1;
            loop {
                if a.compare_exchange_weak(i, i + 1, Ordering::AcqRel, Ordering::Acquire).is_ok() {
                    break;
                }
                spurious_failures += 1;
            }
        }
    }
    let final_val = a.load(Ordering::Acquire);
    println!("MIRI_CAS_WEAK_OK final={final_val} spurious_failures={spurious_failures}");
}
""",
}

TARGET_FNS = [
    "load_relaxed",
    "load_acquire",
    "load_seqcst",
    "store_relaxed",
    "store_release",
    "store_seqcst",
    "swap_relaxed",
    "swap_acqrel",
    "swap_seqcst",
    "fetch_add_relaxed",
    "fetch_add_acquire",
    "fetch_add_release",
    "fetch_add_acqrel",
    "fetch_add_seqcst",
    "fetch_or_used_acqrel",
    "fetch_or_discarded_acqrel",
    "cas_strong_acqrel_acquire",
    "cas_strong_seqcst_seqcst",
    "cas_weak_relaxed_relaxed",
    "cas_weak_acqrel_acquire",
    "cas_u32_strong_acqrel_acquire",
    "fetch_and_u8_discarded_acqrel",
    "hw_fence_acquire",
    "hw_fence_release",
    "hw_fence_acqrel",
    "hw_fence_seqcst",
    "comp_fence_acquire_only",
    "comp_fence_seqcst_only",
    "comp_fence_seqcst_two_loads",
    "no_fence_two_loads",
    "hw_fence_acqrel_with_loads",
    "raw_ptr_two_loads_no_fence",
    "raw_ptr_two_loads_with_cfence",
    "raw_ptr_two_stores_no_fence",
    "raw_ptr_two_stores_with_cfence",
]


def sanitize_text(text: str, tmp_dir: str) -> str:
    home = str(pathlib.Path.home())
    out = text.replace(tmp_dir, "<tmp>")
    out = out.replace(home, "<home>")
    user = os.environ.get("USER", "")
    if user:
        out = out.replace(user, "<user>")
    return out


def extract_llvm_ir_fns(ll_text: str, fn_names: list[str]) -> dict[str, list[str]]:
    out: dict[str, list[str]] = {}
    lines = ll_text.splitlines()
    for name in fn_names:
        pat = re.compile(rf"^define\b.*@{re.escape(name)}\(")
        captured: list[str] = []
        in_fn = False
        for line in lines:
            if not in_fn:
                if pat.search(line):
                    in_fn = True
                    captured.append(line)
            else:
                captured.append(line)
                if line.strip() == "}":
                    break
        out[name] = captured
    return out


def extract_asm_fns(asm_text: str, fn_names: list[str]) -> dict[str, list[str]]:
    out: dict[str, list[str]] = {}
    lines = asm_text.splitlines()
    for name in fn_names:
        label = f"{name}:"
        captured: list[str] = []
        in_fn = False
        for line in lines:
            stripped = line.strip()
            if not in_fn:
                if stripped == label:
                    in_fn = True
                continue
            if stripped.startswith(".Lfunc_end") or stripped.startswith(".size\t" + name):
                break
            if not stripped or stripped.startswith("."):
                continue
            if stripped.startswith("#") and stripped != "#MEMBARRIER":
                continue
            captured.append(stripped)
        out[name] = captured
    return out


def run_codegen_profile(
    tmpdir: pathlib.Path,
    name: str,
    target: str,
    extra_args: list[str],
    fn_subset: list[str],
) -> dict[str, object]:
    src_path = tmpdir / f"{name}.rs"
    src_path.write_text(RUST_CODEGEN_PROBE, encoding="utf-8")
    out_dir = tmpdir / f"out_{name}"
    out_dir.mkdir(parents=True, exist_ok=True)
    cmd = [
        "rustc",
        "--edition",
        "2024",
        "--target",
        target,
        *extra_args,
        "--emit=llvm-ir,asm",
        "--out-dir",
        str(out_dir),
        str(src_path),
    ]
    proc = subprocess.run(cmd, capture_output=True, text=True, check=False)
    ll_files = list(out_dir.glob("*.ll"))
    s_files = list(out_dir.glob("*.s"))
    ll_text = ll_files[0].read_text(encoding="utf-8") if ll_files else ""
    s_text = s_files[0].read_text(encoding="utf-8") if s_files else ""
    return {
        "target": target,
        "extra_args": extra_args,
        "compile_returncode": proc.returncode,
        "compile_stderr": sanitize_text(proc.stderr.strip(), str(tmpdir)),
        "llvm_ir_by_fn": extract_llvm_ir_fns(ll_text, fn_subset),
        "asm_by_fn": extract_asm_fns(s_text, fn_subset),
    }


def run_miri_case(tmpdir: pathlib.Path, case_name: str, main_rs: str) -> dict[str, object]:
    proj = tmpdir / case_name
    (proj / "src").mkdir(parents=True, exist_ok=True)
    (proj / "Cargo.toml").write_text(
        '[package]\nname = "miri_probe"\nversion = "0.1.0"\nedition = "2024"\n',
        encoding="utf-8",
    )
    (proj / "src" / "main.rs").write_text(main_rs, encoding="utf-8")
    cmd = ["cargo", "+nightly", "miri", "run", "--offline"]
    proc = subprocess.run(cmd, cwd=proj, capture_output=True, text=True, check=False)
    return {
        "edition": "2024",
        "command": " ".join(cmd),
        "returncode": proc.returncode,
        "stdout": sanitize_text(proc.stdout.strip(), str(tmpdir)),
        "stderr": sanitize_text(proc.stderr.strip(), str(tmpdir)),
    }


def main() -> int:
    rustc_v = subprocess.run(
        ["rustc", "--version", "--verbose"], capture_output=True, text=True, check=True
    ).stdout.strip()
    miri_v = subprocess.run(
        ["cargo", "+nightly", "miri", "--version"], capture_output=True, text=True, check=True
    ).stdout.strip()

    with tempfile.TemporaryDirectory() as td:
        tmpdir = pathlib.Path(td)
        codegen_profiles = {
            "x86_64_O2_default": run_codegen_profile(
                tmpdir,
                "x86_64_O2_default",
                "x86_64-unknown-linux-gnu",
                ["-C", "opt-level=2"],
                TARGET_FNS,
            ),
            "x86_64_O2_no_redzone": run_codegen_profile(
                tmpdir,
                "x86_64_O2_no_redzone",
                "x86_64-unknown-linux-gnu",
                ["-C", "opt-level=2", "-C", "no-redzone=yes"],
                ["hw_fence_seqcst", "hw_fence_acqrel", "store_seqcst"],
            ),
            "i686_O2_default_sse2": run_codegen_profile(
                tmpdir,
                "i686_O2_default_sse2",
                "i686-unknown-linux-gnu",
                ["-C", "opt-level=2"],
                ["hw_fence_seqcst", "hw_fence_acqrel"],
            ),
            "i686_O2_nosse2": run_codegen_profile(
                tmpdir,
                "i686_O2_nosse2",
                "i686-unknown-linux-gnu",
                ["-C", "opt-level=2", "-C", "target-feature=-sse2"],
                ["hw_fence_seqcst", "hw_fence_acqrel"],
            ),
        }

        miri_cases = {
            name: run_miri_case(tmpdir, name, code)
            for name, code in MIRI_PROGRAMS.items()
        }

    payload = {
        "observed_at_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "rustc_version": rustc_v,
        "miri_version": miri_v,
        "experiments": {
            "a_llvm_ir_and_asm_lowering": codegen_profiles,
            "b_miri_thread_sync_vs_data_race": miri_cases,
        },
    }

    out_path = pathlib.Path(__file__).resolve().parent / "probe_results.json"
    out_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(f"wrote {out_path} ({out_path.stat().st_size} bytes)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
