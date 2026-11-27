#!/usr/bin/env python3
"""Measure exact nightly-2026-05-31 Runtime(PostCleanup) and optimized MIR
surfaces for toy concurrency primitives and real Rust stdlib concurrency
primitives. Self-contained and portable across rustup toolchains.
"""
import argparse
import json
import os
import re
import subprocess
import tempfile
from pathlib import Path

RUSTC = "rustc"
DEFAULT_TOOLCHAIN = "+nightly-2026-05-31"


def discover_rust_src(toolchain_flag: str, explicit_rust_src: str | None) -> Path:
    if explicit_rust_src:
        return Path(explicit_rust_src)
    cmd = [RUSTC]
    if toolchain_flag:
        cmd.append(toolchain_flag)
    cmd.extend(["--print", "sysroot"])
    sysroot = Path(subprocess.check_output(cmd, text=True).strip())
    return sysroot / "lib/rustlib/src/rust/library"

TOY_CRATE_RS = r"""
#![feature(core_intrinsics)]
#![allow(internal_features, dead_code, unused_unsafe)]
#![no_std]

use core::cell::UnsafeCell;
use core::mem::MaybeUninit;
use core::sync::atomic::{AtomicBool, AtomicU32, AtomicU64, AtomicUsize, Ordering, fence};

// 1. Minimal raw-method SpinLock<u64> (no Drop guard)
pub struct RawSpinLock {
    locked: AtomicBool,
    val: UnsafeCell<u64>,
}
unsafe impl Sync for RawSpinLock {}

impl RawSpinLock {
    pub const fn new(v: u64) -> Self {
        Self { locked: AtomicBool::new(false), val: UnsafeCell::new(v) }
    }
    pub fn try_lock(&self) -> bool {
        self.locked.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed).is_ok()
    }
    pub fn lock(&self) {
        while self.locked.compare_exchange_weak(false, true, Ordering::Acquire, Ordering::Relaxed).is_err() {
            while self.locked.load(Ordering::Relaxed) {
                core::hint::spin_loop();
            }
        }
    }
    pub unsafe fn unlock(&self) {
        self.locked.store(false, Ordering::Release);
    }
    pub fn with_lock_set(&self, x: u64) -> u64 {
        self.lock();
        let old = unsafe {
            let p = self.val.get();
            let prev = *p;
            *p = x;
            prev
        };
        unsafe { self.unlock(); }
        old
    }
}

// 1b. RAII Guard SpinLock (exercises Drop + cleanup unwinds if unwind enabled)
pub struct GuardSpinLock {
    locked: AtomicBool,
    val: UnsafeCell<u64>,
}
unsafe impl Sync for GuardSpinLock {}
pub struct SpinGuard<'a> {
    lock: &'a GuardSpinLock,
}
impl<'a> Drop for SpinGuard<'a> {
    fn drop(&mut self) {
        self.lock.locked.store(false, Ordering::Release);
    }
}
#[inline(never)]
fn maybe_panic_hook(x: u64) -> u64 { x.wrapping_add(1) }

impl GuardSpinLock {
    pub fn lock(&self) -> SpinGuard<'_> {
        while self.locked.swap(true, Ordering::Acquire) {
            core::hint::spin_loop();
        }
        SpinGuard { lock: self }
    }
    pub fn with_guard(&self) -> u64 {
        let g = self.lock();
        let res = unsafe {
            let p = g.lock.val.get();
            let v = maybe_panic_hook(*p);
            *p = v;
            v
        };
        drop(g);
        res
    }
    pub fn with_guard_scope(&self) -> u64 {
        let g = self.lock();
        unsafe {
            let p = g.lock.val.get();
            let v = maybe_panic_hook(*p);
            *p = v;
            v
        }
    }
}

// 2. TicketLock<u64>
pub struct TicketLock {
    next: AtomicU32,
    serving: AtomicU32,
    val: UnsafeCell<u64>,
}
unsafe impl Sync for TicketLock {}
impl TicketLock {
    pub fn lock(&self) {
        let t = self.next.fetch_add(1, Ordering::Relaxed);
        while self.serving.load(Ordering::Acquire) != t {
            core::hint::spin_loop();
        }
    }
    pub unsafe fn unlock(&self) {
        let cur = self.serving.load(Ordering::Relaxed);
        self.serving.store(cur.wrapping_add(1), Ordering::Release);
    }
}

// 3. SeqLock<[u64; 2]>
pub struct SeqLockPair {
    seq: AtomicU64,
    data: UnsafeCell<[u64; 2]>,
}
unsafe impl Sync for SeqLockPair {}
impl SeqLockPair {
    pub fn write(&self, a: u64, b: u64) {
        let s = self.seq.load(Ordering::Relaxed);
        self.seq.store(s.wrapping_add(1), Ordering::Release);
        // Wait: in real seqlock you either use release-fence or atomic stores; here write under single-writer lock
        fence(Ordering::Release);
        unsafe {
            let p = self.data.get();
            (*p)[0] = a;
            (*p)[1] = b;
        }
        self.seq.store(s.wrapping_add(2), Ordering::Release);
    }
    pub fn read(&self) -> [u64; 2] {
        loop {
            let s1 = self.seq.load(Ordering::Acquire);
            if s1 & 1 != 0 {
                core::hint::spin_loop();
                continue;
            }
            let v = unsafe { *self.data.get() };
            fence(Ordering::Acquire);
            let s2 = self.seq.load(Ordering::Relaxed);
            if s1 == s2 {
                return v;
            }
        }
    }
}

// 4. Core-only 3-state AtomicOnce<u64> (spin wait, no futex, no unwind)
const ONCE_INCOMPLETE: u32 = 0;
const ONCE_RUNNING: u32 = 1;
const ONCE_COMPLETE: u32 = 2;

pub struct AtomicOnceU64 {
    state: AtomicU32,
    val: UnsafeCell<MaybeUninit<u64>>,
}
unsafe impl Sync for AtomicOnceU64 {}
impl AtomicOnceU64 {
    pub const fn new() -> Self {
        Self { state: AtomicU32::new(ONCE_INCOMPLETE), val: UnsafeCell::new(MaybeUninit::uninit()) }
    }
    pub fn get(&self) -> Option<u64> {
        if self.state.load(Ordering::Acquire) == ONCE_COMPLETE {
            Some(unsafe { (*self.val.get()).assume_init() })
        } else {
            None
        }
    }
    pub fn get_or_init_val(&self, v: u64) -> u64 {
        if self.state.load(Ordering::Acquire) == ONCE_COMPLETE {
            return unsafe { (*self.val.get()).assume_init() };
        }
        loop {
            match self.state.compare_exchange(ONCE_INCOMPLETE, ONCE_RUNNING, Ordering::Acquire, Ordering::Acquire) {
                Ok(_) => {
                    unsafe { (*self.val.get()).write(v); }
                    self.state.store(ONCE_COMPLETE, Ordering::Release);
                    return v;
                }
                Err(s) if s == ONCE_COMPLETE => {
                    return unsafe { (*self.val.get()).assume_init() };
                }
                Err(_) => core::hint::spin_loop(),
            }
        }
    }
}

// 5. Core+Stub Futex Mutex model matching std::sys::sync::mutex::futex::Mutex (without poison)
#[inline(never)]
fn stub_futex_wait(_a: &AtomicU32, _expected: u32) {}
#[inline(never)]
fn stub_futex_wake(_a: &AtomicU32) {}

pub struct FutexMutexCore {
    state: AtomicU32,
    data: UnsafeCell<u64>,
}
unsafe impl Sync for FutexMutexCore {}
impl FutexMutexCore {
    pub fn lock(&self) {
        if self.state.compare_exchange(0, 1, Ordering::Acquire, Ordering::Relaxed).is_err() {
            self.lock_contended();
        }
    }
    #[inline(never)]
    fn lock_contended(&self) {
        let mut s = self.spin();
        if s == 0 {
            match self.state.compare_exchange(0, 1, Ordering::Acquire, Ordering::Relaxed) {
                Ok(_) => return,
                Err(cur) => s = cur,
            }
        }
        loop {
            if s != 2 && self.state.swap(2, Ordering::Acquire) == 0 {
                return;
            }
            stub_futex_wait(&self.state, 2);
            s = self.spin();
        }
    }
    fn spin(&self) -> u32 {
        let mut n = 100u32;
        loop {
            let s = self.state.load(Ordering::Relaxed);
            if s != 1 || n == 0 { return s; }
            core::hint::spin_loop();
            n -= 1;
        }
    }
    pub unsafe fn unlock(&self) {
        if self.state.swap(0, Ordering::Release) == 2 {
            stub_futex_wake(&self.state);
        }
    }
}

// 6. Arc refcount clone/drop fence core
pub struct ArcCountCore {
    strong: AtomicUsize,
}
impl ArcCountCore {
    pub fn clone_count(&self) -> usize {
        let old = self.strong.fetch_add(1, Ordering::Relaxed);
        if old > (isize::MAX as usize) {
            core::intrinsics::abort();
        }
        old
    }
    pub fn drop_is_last(&self) -> bool {
        if self.strong.fetch_sub(1, Ordering::Release) != 1 {
            return false;
        }
        fence(Ordering::Acquire);
        true
    }
}
"""

STD_WRAPPER_RS = r"""
#![feature(nonpoison_mutex, sync_nonpoison)]
use std::sync::{Arc, Condvar, Mutex, Once, OnceLock, RwLock};
use std::sync::nonpoison;

pub fn call_once_is_completed(o: &Once) -> bool {
    o.is_completed()
}
pub fn call_once_init(o: &Once) {
    o.call_once(|| {});
}
pub fn call_oncelock_get(l: &OnceLock<u64>) -> Option<&u64> {
    l.get()
}
pub fn call_oncelock_set(l: &OnceLock<u64>, v: u64) -> Result<(), u64> {
    l.set(v)
}
pub fn call_poison_mutex(m: &Mutex<u64>) -> u64 {
    let mut g = m.lock().unwrap();
    *g += 1;
    *g
}
pub fn call_nonpoison_mutex(m: &nonpoison::Mutex<u64>) -> u64 {
    let mut g = m.lock();
    *g += 1;
    *g
}
pub fn call_arc_clone_drop(a: Arc<u64>) -> u64 {
    let b = Arc::clone(&a);
    let v = *b;
    drop(b);
    v
}
pub fn call_rwlock(r: &RwLock<u64>) -> u64 {
    let mut w = r.write().unwrap();
    *w += 1;
    drop(w);
    *r.read().unwrap()
}
pub fn call_condvar(m: &Mutex<bool>, cv: &Condvar) {
    let mut g = m.lock().unwrap();
    while !*g {
        g = cv.wait(g).unwrap();
    }
    cv.notify_one();
}
"""


def normalize_fn_name(raw: str) -> str:
    # Strip ephemeral tempdir path like `<impl at /tmp/.../toy.rs:17:1: 17:17>::`
    return re.sub(r"/tmp/[^/]+/", "<tmp>/", raw)


def parse_mir_file(mir_path: Path):
    """Parse emitted MIR file or runtime-post-cleanup dump and inspect MIR constructs."""
    results = []
    txt = mir_path.read_text()
    fn_blocks = re.split(r"(?m)^fn\s+", txt)
    for sec in fn_blocks[1:]:
        header = sec.splitlines()[0].strip()
        name = normalize_fn_name(header.split("(")[0].strip())
        all_calls = []
        for m in re.finditer(
            r"(?m)^\s+(?:_[0-9]+\s*=\s*)?([A-Za-z0-9_:<>\[\], &'*.{}@#;]+?)\((?:[^()]|\([^()]*\))*\)\s*->\s*\[",
            sec,
        ):
            callee = m.group(1).strip()
            if not callee.startswith("bb"):
                all_calls.append(callee)
        has_drop = bool(re.search(r"(?m)^\s+drop\(", sec))
        has_unwind_cleanup = bool(re.search(r"unwind:\s*bb\d+|\(cleanup\)", sec))
        has_unwind_terminate = bool(re.search(r"unwind terminate", sec))
        has_assert = bool(re.search(r"(?m)^\s+assert\(", sec))
        has_raw_ptr = "*mut " in sec or "*const " in sec
        has_unsafe_cell = "UnsafeCell" in sec
        has_maybe_uninit = "MaybeUninit" in sec
        has_inline_asm = bool(re.search(r"(?m)^\s+asm!\(", sec))
        has_discriminant = "discriminant(" in sec
        has_panic_str = "panic" in sec or "begin_panic" in sec
        bb_count = len(re.findall(r"(?m)^\s+bb\d+(?:\s*\(cleanup\))?:", sec))
        atomic_calls = [c for c in all_calls if "atomic" in c or "compare_exchange" in c or "fence" in c]
        non_atomic_calls = sorted(set(c for c in all_calls if c not in atomic_calls))
        results.append(
            {
                "fn": name,
                "bb_count": bb_count,
                "atomic_calls": atomic_calls,
                "non_atomic_calls": non_atomic_calls,
                "has_drop": has_drop,
                "has_unwind_cleanup": has_unwind_cleanup,
                "has_unwind_terminate": has_unwind_terminate,
                "has_assert": has_assert,
                "has_panic_str": has_panic_str,
                "has_unsafe_cell": has_unsafe_cell,
                "has_maybe_uninit": has_maybe_uninit,
                "has_raw_ptr": has_raw_ptr,
                "has_discriminant": has_discriminant,
                "has_inline_asm": has_inline_asm,
            }
        )
    return results


def run_rustc_mir(toolchain_flag, name, src_text, opt_level, panic_mode, out_dir: Path):
    src_path = out_dir / f"{name}.rs"
    src_path.write_text(src_text)
    mir_path = out_dir / f"{name}_O{opt_level}_{panic_mode}.mir"
    dump_dir = out_dir / f"dump_{name}_O{opt_level}_{panic_mode}"
    dump_dir.mkdir(parents=True, exist_ok=True)
    cmd = [RUSTC]
    if toolchain_flag:
        cmd.append(toolchain_flag)
    cmd.extend([
        "--edition=2024",
        "--crate-type=lib",
        "-Zmir-preserve-ub",
        f"-Copt-level={opt_level}",
        "-Cdebug-assertions=no",
        "-Coverflow-checks=no",
        f"-Cpanic={panic_mode}",
        "-Zdump-mir=runtime-post-cleanup",
        f"-Zdump-mir-dir={dump_dir}",
        "--emit=mir",
        "-o",
        str(mir_path),
        str(src_path),
    ])
    res = subprocess.run(cmd, capture_output=True, text=True, check=False)
    if res.returncode != 0:
        raise RuntimeError(f"rustc failed for {name}: {res.stderr}")
    post_cleanup = []
    for f in sorted(dump_dir.glob("*runtime-post-cleanup.after.mir")):
        post_cleanup.extend(parse_mir_file(f))
    optimized = parse_mir_file(mir_path)
    return {"post_cleanup": post_cleanup, "optimized": optimized}


def audit_rust_src_files(rust_src: Path):
    """Static source-level census over pinned rust-src."""
    targets = {
        "sys_sync_once_futex": rust_src / "std/src/sys/sync/once/futex.rs",
        "sync_once": rust_src / "std/src/sync/once.rs",
        "sync_once_lock": rust_src / "std/src/sync/once_lock.rs",
        "sys_sync_mutex_futex": rust_src / "std/src/sys/sync/mutex/futex.rs",
        "sync_nonpoison_mutex": rust_src / "std/src/sync/nonpoison/mutex.rs",
        "sync_poison_mutex": rust_src / "std/src/sync/poison/mutex.rs",
        "sync_poison": rust_src / "std/src/sync/poison.rs",
        "sys_pal_unix_futex": rust_src / "std/src/sys/pal/unix/futex.rs",
        "alloc_sync_arc": rust_src / "alloc/src/sync.rs",
        "sys_sync_rwlock_futex": rust_src / "std/src/sys/sync/rwlock/futex.rs",
        "sys_sync_condvar_futex": rust_src / "std/src/sys/sync/condvar/futex.rs",
    }
    report = {}
    for key, path in targets.items():
        txt = path.read_text()
        report[key] = {
            "path": str(path.relative_to(rust_src)),
            "lines": len(txt.splitlines()),
            "orderings": sorted(
                set(re.findall(r"\b(Relaxed|Acquire|Release|AcqRel|SeqCst)\b", txt))
            ),
            "atomic_ops": sorted(
                set(
                    re.findall(
                        r"\.(load|store|swap|compare_exchange|compare_exchange_weak|fetch_add|fetch_sub|fetch_and|fetch_or|fetch_update|try_update|get_mut)\(",
                        txt,
                    )
                )
            ),
            "has_fence": "fence(" in txt,
            "has_unsafe_cell": "UnsafeCell" in txt,
            "has_cell": re.search(r"\bCell<", txt) is not None,
            "has_maybe_uninit": "MaybeUninit" in txt,
            "has_manually_drop": "ManuallyDrop" in txt,
            "has_non_null": "NonNull" in txt,
            "has_box": re.search(r"\bBox<|Box::", txt) is not None,
            "has_drop_impl": "impl" in txt and "Drop for" in txt,
            "has_futex_wait": "futex_wait" in txt,
            "has_futex_wake": "futex_wake" in txt,
            "has_libc_syscall": "libc::syscall" in txt or "SYS_futex" in txt,
            "has_panic_or_assert": "panic!(" in txt or "assert!(" in txt or "unreachable!(" in txt,
            "has_poison": "poison" in txt.lower() or "panicking" in txt,
            "has_thread_panicking": "panicking(" in txt,
            "has_dyn_fn": "dyn Fn" in txt,
            "has_spin_loop": "spin_loop" in txt,
        }
    return report


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--toolchain", default=DEFAULT_TOOLCHAIN, help="rustup toolchain flag (e.g. +nightly-2026-05-31 or empty)")
    ap.add_argument("--rust-src", default=None, help="optional path to rust/library")
    ap.add_argument("--out", default="-", help="JSON output path or '-' for stdout summary only")
    args = ap.parse_args()

    rust_src = discover_rust_src(args.toolchain, args.rust_src)
    with tempfile.TemporaryDirectory() as tmp:
        out = Path(tmp)
        toy_o0_abort = run_rustc_mir(args.toolchain, "toy", TOY_CRATE_RS, 0, "abort", out)
        toy_o0_unwind = run_rustc_mir(args.toolchain, "toy", TOY_CRATE_RS, 0, "unwind", out)
        toy_o1_abort = run_rustc_mir(args.toolchain, "toy", TOY_CRATE_RS, 1, "abort", out)
        std_o0_abort = run_rustc_mir(args.toolchain, "std_wrap", STD_WRAPPER_RS, 0, "abort", out)
        std_o0_unwind = run_rustc_mir(args.toolchain, "std_wrap", STD_WRAPPER_RS, 0, "unwind", out)
        rust_src_audit = audit_rust_src_files(rust_src)

    cmd_ver = [RUSTC] + ([args.toolchain] if args.toolchain else []) + ["--version"]
    summary = {
        "rustc_version": subprocess.check_output(cmd_ver, text=True).strip(),
        "toy_o0_abort": toy_o0_abort,
        "toy_o0_unwind": toy_o0_unwind,
        "toy_o1_abort": toy_o1_abort,
        "std_o0_abort": std_o0_abort,
        "std_o0_unwind": std_o0_unwind,
        "rust_src_audit": rust_src_audit,
    }
    if args.out != "-":
        out_json = Path(args.out)
        out_json.write_text(json.dumps(summary, indent=2) + "\n")
        print(f"Wrote {out_json}")
    else:
        print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
