#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Primary empirical probe of Anneal's concurrent MIR capture, TargetRole
specification boundary, SepPCM cancellativity, and vendor/lean-miri closure
seams across pinned rustc (f8a08b688c), host nightly rustc, and google/zerocopy
origin/main (64b0b6ae5788).
"""

import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

SAMPLE_CONCURRENT_RS = r"""
#![feature(thread_local)]
#![crate_type = "lib"]

use std::cell::UnsafeCell;
use std::mem::{ManuallyDrop, MaybeUninit};
use std::sync::atomic::{AtomicBool, AtomicPtr, AtomicUsize, Ordering, compiler_fence, fence};
use std::sync::{Arc, Barrier, Condvar, Mutex, Once, RwLock, mpsc};

pub static GLOBAL_COUNTER: AtomicUsize = AtomicUsize::new(0);

#[thread_local]
pub static TLS_SLOT: UnsafeCell<u64> = UnsafeCell::new(0);

pub struct SpinMutex<T> {
    locked: AtomicBool,
    data: UnsafeCell<T>,
}

unsafe impl<T: Send> Send for SpinMutex<T> {}
unsafe impl<T: Send> Sync for SpinMutex<T> {}

pub struct SpinGuard<'a, T> {
    lock: &'a SpinMutex<T>,
}

impl<T> SpinMutex<T> {
    pub const fn new(val: T) -> Self {
        Self {
            locked: AtomicBool::new(false),
            data: UnsafeCell::new(val),
        }
    }

    #[inline(never)]
    pub fn lock(&self) -> SpinGuard<'_, T> {
        while self
            .locked
            .compare_exchange_weak(false, true, Ordering::Acquire, Ordering::Relaxed)
            .is_err()
        {
            std::hint::spin_loop();
        }
        SpinGuard { lock: self }
    }

    #[inline(never)]
    pub fn get_mut(&mut self) -> &mut T {
        self.data.get_mut()
    }
}

impl<T> std::ops::Deref for SpinGuard<'_, T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { &*self.lock.data.get() }
    }
}

impl<T> std::ops::DerefMut for SpinGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.lock.data.get() }
    }
}

impl<T> Drop for SpinGuard<'_, T> {
    fn drop(&mut self) {
        self.lock.locked.store(false, Ordering::Release);
    }
}

#[inline(never)]
pub fn exercise_all_atomics(
    a: &AtomicUsize,
    p: &AtomicPtr<u64>,
    raw: *mut u64,
) -> (usize, *mut u64) {
    let v0 = a.load(Ordering::Acquire);
    a.store(v0.wrapping_add(1), Ordering::Release);
    let v1 = a.swap(42, Ordering::AcqRel);
    let _ = a.compare_exchange(42, 43, Ordering::AcqRel, Ordering::Acquire);
    let _ = a.compare_exchange_weak(43, 44, Ordering::SeqCst, Ordering::Relaxed);
    let _ = a.fetch_add(1, Ordering::AcqRel);
    let _ = a.fetch_sub(1, Ordering::Release);
    let _ = a.fetch_and(0xff, Ordering::Relaxed);
    let _ = a.fetch_or(0x10, Ordering::Relaxed);
    let _ = a.fetch_xor(0x01, Ordering::Relaxed);
    let _ = a.fetch_nand(0xff, Ordering::Relaxed);
    let _ = a.fetch_max(10, Ordering::Relaxed);
    let _ = a.fetch_min(5, Ordering::Relaxed);
    let old_ptr = p.swap(raw, Ordering::AcqRel);
    fence(Ordering::SeqCst);
    compiler_fence(Ordering::Acquire);
    let _ = GLOBAL_COUNTER.fetch_add(v1, Ordering::Relaxed);
    let tls_val = unsafe { *TLS_SLOT.get() };
    (v1.wrapping_add(tls_val as usize), old_ptr)
}

#[inline(never)]
pub fn exercise_guard_drop_and_unwind(m: &SpinMutex<u64>, may_panic: fn(u64) -> u64) -> u64 {
    let mut g = m.lock();
    *g = may_panic(*g);
    *g
}

#[inline(never)]
pub fn exercise_maybe_uninit_and_forget(m: &SpinMutex<MaybeUninit<u64>>) {
    let g = m.lock();
    let _ = ManuallyDrop::new(g);
}

#[inline(never)]
pub fn exercise_std_primitives(
    mtx: &Mutex<u64>,
    rw: &RwLock<u64>,
    cv: &Condvar,
    once: &Once,
    bar: &Barrier,
    arc: Arc<AtomicUsize>,
) {
    let g = mtx.lock().unwrap();
    let _g2 = cv.wait_while(g, |v| *v == 0).unwrap();
    let _r = rw.read().unwrap();
    once.call_once(|| {
        arc.fetch_add(1, Ordering::SeqCst);
    });
    let _ = bar.wait();
    let (tx, rx) = mpsc::sync_channel::<u64>(1);
    tx.send(7).unwrap();
    let _ = rx.recv().unwrap();
    std::thread::scope(|s| {
        s.spawn(|| {
            arc.fetch_add(1, Ordering::AcqRel);
        });
    });
}
"""


def find_pinned_anneal_rustc() -> Path | None:
    if "PINNED_RUSTC" in os.environ:
        return Path(os.environ["PINNED_RUSTC"])
    cache = Path.home() / ".cache/anneal/toolchain"
    if not cache.exists():
        return None
    for cand in sorted(cache.glob("*/rust/bin/rustc")):
        try:
            ver = subprocess.check_output(
                [str(cand), "--version", "--verbose"], text=True
            )
            if "f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1" in ver:
                return cand
        except Exception:
            continue
    return None


def find_host_nightly_rustc() -> Path:
    if "NIGHTLY_RUSTC" in os.environ:
        return Path(os.environ["NIGHTLY_RUSTC"])
    cand = Path.home() / ".rustup/toolchains/nightly-x86_64-unknown-linux-gnu/bin/rustc"
    if cand.exists():
        return cand
    return Path(
        subprocess.check_output(
            ["rustup", "which", "--toolchain", "nightly", "rustc"], text=True
        ).strip()
    )


def inspect_mir_with_rustc(rustc_bin: Path, label: str) -> dict:
    ver = subprocess.check_output(
        [str(rustc_bin), "--version", "--verbose"], text=True
    ).strip()
    env = dict(os.environ)
    lib_dir = rustc_bin.parent.parent / "lib"
    if lib_dir.exists():
        env["LD_LIBRARY_PATH"] = f"{lib_dir}:{env.get('LD_LIBRARY_PATH', '')}"

    intrinsics_rs = (
        rustc_bin.parent.parent / "lib/rustlib/src/rust/library/core/src/intrinsics/mod.rs"
    )
    atomic_load_sig = None
    atomic_store_sig = None
    if intrinsics_rs.exists():
        txt_i = intrinsics_rs.read_text()
        ml = re.search(r"pub\s+(?:const\s+)?unsafe\s+fn\s+atomic_load<[^>]+>", txt_i)
        ms = re.search(r"pub\s+(?:const\s+)?unsafe\s+fn\s+atomic_store<[^>]+>", txt_i)
        if ml:
            atomic_load_sig = " ".join(ml.group(0).split())
        if ms:
            atomic_store_sig = " ".join(ms.group(0).split())

    with tempfile.TemporaryDirectory() as td:
        td_path = Path(td)
        src = td_path / "concurrent_probe.rs"
        dump_dir = td_path / "mir_dump"
        dump_dbg_dir = td_path / "mir_dump_dbg"
        dump_dir.mkdir()
        dump_dbg_dir.mkdir()
        mir_opt = td_path / "opt.mir"
        src.write_text(SAMPLE_CONCURRENT_RS)

        # 1. Exact Anneal capture profile: -Copt-level=0 -Cdebug-assertions=no -Coverflow-checks=no
        subprocess.run(
            [
                str(rustc_bin),
                "--edition=2024",
                "-Copt-level=0",
                "-Cdebug-assertions=no",
                "-Coverflow-checks=no",
                "-Zdump-mir=all",
                f"-Zdump-mir-dir={dump_dir}",
                "--emit=metadata,obj",
                "--out-dir",
                str(td_path),
                str(src),
            ],
            env=env,
            check=True,
        )
        pc_files = sorted(dump_dir.glob("*.runtime-post-cleanup.after.mir"))
        assert len(pc_files) > 0, "Expected runtime-post-cleanup MIR dumps"
        pc_text = "\n".join(p.read_text() for p in pc_files)

        # 2. Control with -Cdebug-assertions=yes to confirm 3-2-000 precedes 3-2-001.CheckAlignment
        subprocess.run(
            [
                str(rustc_bin),
                "--edition=2024",
                "-Copt-level=0",
                "-Cdebug-assertions=yes",
                "-Coverflow-checks=no",
                "-Zdump-mir=all",
                f"-Zdump-mir-dir={dump_dbg_dir}",
                "--emit=metadata,obj",
                "--out-dir",
                str(td_path),
                str(src),
            ],
            env=env,
            check=True,
        )
        dbg_pc_files = sorted(dump_dbg_dir.glob("*.runtime-post-cleanup.after.mir"))
        dbg_ca_files = sorted(dump_dbg_dir.glob("*.CheckAlignment.after.mir"))
        dbg_pc_transmutes = sum(
            len(re.findall(r"\(Transmute\)", p.read_text())) for p in dbg_pc_files
        )
        dbg_ca_transmutes = sum(
            len(re.findall(r"\(Transmute\)", p.read_text())) for p in dbg_ca_files
        )

        # 3. Optimized MIR (-O)
        subprocess.run(
            [
                str(rustc_bin),
                "--edition=2024",
                "-O",
                "--emit=mir",
                "-o",
                str(mir_opt),
                str(src),
            ],
            env=env,
            check=True,
        )
        opt_text = mir_opt.read_text()

    def summarize(text: str) -> dict:
        all_atomic_generic = sorted(set(re.findall(r"\batomic_[a-z0-9_]+::<[^>]+>", text)))
        core_intrinsics = [
            s for s in all_atomic_generic if "AtomicOrdering::" in s or ", false>" in s or ", true>" in s
        ]
        sync_helpers = [s for s in all_atomic_generic if s not in core_intrinsics]
        return {
            "lines": len(text.splitlines()),
            "sha256": hashlib.sha256(text.encode()).hexdigest(),
            "atomic_method_calls": len(re.findall(r"Atomic::<[^>]+>::[a-z_]+\(", text)),
            "inlined_core_intrinsics": core_intrinsics,
            "sync_atomic_helper_calls": sync_helpers,
            "tls_ref_rvalues": len(re.findall(r"&/\*tls\*/", text)),
            "static_alloc_consts": len(re.findall(r"alloc[0-9]+ \(static:", text)),
            "cleanup_blocks": len(re.findall(r"\(cleanup\):", text)),
            "drop_terminators": len(re.findall(r"\bdrop\(", text)),
            "unwind_resume": len(re.findall(r"\bresume\b", text)),
            "unwind_terminate": len(re.findall(r"terminate\(", text)),
            "raw_addr_of": len(re.findall(r"&raw (?:const|mut)", text)),
            "transmute_casts": len(re.findall(r"\(Transmute\)", text)),
            "ptr_to_ptr_casts": len(re.findall(r"\(PtrToPtr\)", text)),
        }

    return {
        "label": label,
        "rustc_version": ver.splitlines()[0],
        "rustc_commit": next(
            (l.split(":", 1)[1].strip() for l in ver.splitlines() if l.startswith("commit-hash:")),
            "unknown",
        ),
        "core_intrinsics_atomic_load_sig": atomic_load_sig,
        "core_intrinsics_atomic_store_sig": atomic_store_sig,
        "post_cleanup_capture_profile": summarize(pc_text),
        "debug_assertions_control": {
            "post_cleanup_transmutes": dbg_pc_transmutes,
            "after_check_alignment_transmutes": dbg_ca_transmutes,
            "check_alignment_files_emitted": len(dbg_ca_files) > 0,
        },
        "optimized_mir_O": summarize(opt_text),
    }


def read_git_file(zc_repo: Path, rev: str, rel: str) -> str:
    return subprocess.check_output(
        ["git", "-C", str(zc_repo), "show", f"{rev}:{rel}"], text=True
    )


def inspect_anneal_seams(zc_repo: Path, rev: str) -> dict:
    capture_rs = read_git_file(zc_repo, rev, "anneal/trusted/rustc-capture/src/capture.rs")
    extract_rs = read_git_file(zc_repo, rev, "anneal/trusted/rustc-capture/src/extract.rs")
    ir_rs = read_git_file(zc_repo, rev, "anneal/trusted/rustc-capture/src/ir.rs")
    target_rs = read_git_file(zc_repo, rev, "anneal/trusted/cargo-anneal/src/target.rs")
    tb_lean = read_git_file(zc_repo, rev, "anneal/trusted/audit/TrustedBoundary.lean")
    sep_pcm = read_git_file(zc_repo, rev, "anneal/theory/Anneal/Core/SepPCM.lean")
    intrinsic_atomic_lean = read_git_file(
        zc_repo, rev, "anneal/vendor/lean-miri/Miri/Interpreter/IntrinsicAtomic.lean"
    )
    pin_json = json.loads(
        read_git_file(zc_repo, rev, "anneal/vendor/lean-miri/UPSTREAM_PIN.json")
    )

    hook_match = re.search(r"providers\.queries\.([a-z_]+)\s*=\s*hook", capture_rs)
    schema_match = re.search(r"pub const SCHEMA_VERSION:\s*u32\s*=\s*([0-9]+);", ir_rs)

    # Assert exact compiler flags and admission/rejection guards in capture.rs & extract.rs
    exact_capture_flags = all(
        flag in capture_rs
        for flag in ['"-Copt-level=0"', '"-Cdebug-assertions=no"', '"-Coverflow-checks=no"']
    )
    admits_scalar_v4 = all(
        tok in extract_rs
        for tok in [
            "IntWidth::I128",
            "Ty::OverflowPair",
            "Ty::Char",
            "Ty::Ordering",
            "mir::UnOp::Not",
            "mir::UnOp::Neg",
            "mir::BinOp::Div",
            "mir::BinOp::Rem",
            "mir::BinOp::AddWithOverflow",
            "mir::BinOp::SubWithOverflow",
            "mir::BinOp::MulWithOverflow",
            "mir::BinOp::Cmp",
            "CastKind::IntToInt",
        ]
    )
    rejects_concurrent_and_ptr = all(
        [
            "tcx.generics_of(def).count() != 0" in extract_rs,
            "tcx.intrinsic(def)" in extract_rs,
            "place projections are unsupported" in extract_rs,
            "try_to_scalar_int()" in extract_rs,
            'other => return Err(format!("unsupported rvalue: {other:?}"))' in extract_rs,
            'other => return Err(format!("unsupported terminator: {other:?}"))' in extract_rs,
            '"--extern"' in capture_rs,
            '"proc_macro"' in capture_rs,
        ]
    )
    assert exact_capture_flags and admits_scalar_v4 and rejects_concurrent_and_ptr

    emc_set = {e["module"] for e in pin_json["execution_machine_closure"]}
    miri_files = subprocess.check_output(
        ["git", "-C", str(zc_repo), "ls-tree", "-r", "--name-only", rev, "anneal/vendor/lean-miri/Miri"],
        text=True,
    ).splitlines()
    miri_mod_to_rel = {
        f.removeprefix("anneal/vendor/lean-miri/").removesuffix(".lean").replace("/", "."): f
        for f in miri_files
        if f.endswith(".lean")
    }

    def get_miri_imports(mod_name: str) -> list[str]:
        rel = miri_mod_to_rel.get(mod_name)
        if not rel:
            return []
        imps = []
        for line in read_git_file(zc_repo, rev, rel).splitlines():
            s = line.split("--")[0].strip()
            if s.startswith("import "):
                for tok in s[len("import ") :].split():
                    if tok.startswith("Miri."):
                        imps.append(tok)
        return imps

    def closure_delta(roots: list[str]) -> list[str]:
        vis = set()
        stk = list(roots)
        while stk:
            cur = stk.pop()
            if cur not in vis:
                vis.add(cur)
                stk.extend(d for d in get_miri_imports(cur) if d not in vis)
        return sorted(vis - emc_set)

    existing_ctrl = closure_delta(
        ["Miri.Interpreter.IntrinsicAtomic", "Miri.Concurrency.Scheduler", "Miri.TreeBorrows.TreeState"]
    )
    os_sync_9 = closure_delta([
        "Miri.Concurrency.FutexRuntime",
        "Miri.Concurrency.Sync",
        "Miri.Concurrency.InitOnce",
        "Miri.Concurrency.Join",
        "Miri.Interpreter.LinuxFutex",
        "Miri.Interpreter.LinuxFutexMachine",
        "Miri.Interpreter.PthreadSync",
        "Miri.Interpreter.ThreadMachine",
        "Miri.Interpreter.ThreadShimMachine",
    ])
    os_sync_with_exec_intrinsic = closure_delta([
        "Miri.Concurrency.FutexRuntime",
        "Miri.Concurrency.Sync",
        "Miri.Concurrency.InitOnce",
        "Miri.Concurrency.Join",
        "Miri.Interpreter.LinuxFutex",
        "Miri.Interpreter.LinuxFutexMachine",
        "Miri.Interpreter.PthreadSync",
        "Miri.Interpreter.ThreadMachine",
        "Miri.Interpreter.ThreadShimMachine",
        "Miri.Interpreter.ExecutionIntrinsic",
    ])

    assert len(existing_ctrl) == 0
    assert len(os_sync_9) == 25
    assert len(os_sync_with_exec_intrinsic) == 39

    concur_in_emc = sorted(m for m in emc_set if m.startswith("Miri.Concurrency."))
    tb_in_emc = sorted(m for m in emc_set if m.startswith("Miri.TreeBorrows."))
    interp_concur_in_emc = sorted(
        m
        for m in emc_set
        if m in {
            "Miri.Interpreter.IntrinsicAtomic",
            "Miri.Interpreter.AtomicMachine",
            "Miri.Interpreter.ThreadStacks",
            "Miri.Interpreter.ThreadLocal",
            "Miri.Interpreter.ThreadExit",
            "Miri.Interpreter.ThreadTls",
            "Miri.Interpreter.TlsDestructors",
            "Miri.Interpreter.MainThread",
        }
    )

    return {
        "zerocopy_revision": subprocess.check_output(
            ["git", "-C", str(zc_repo), "rev-parse", rev], text=True
        ).strip(),
        "mir_query_hook": hook_match.group(1) if hook_match else "NOT_FOUND",
        "capture_schema_version": int(schema_match.group(1)) if schema_match else -1,
        "exact_capture_flags_verified": exact_capture_flags,
        "admits_scalar_v4_verified": admits_scalar_v4,
        "rejects_concurrent_and_ptr_verified": rejects_concurrent_and_ptr,
        "lean_miri_intrinsic_atomic_has_volatile_const": (
            "volatileConst :" in intrinsic_atomic_lean
        ),
        "spec_role_forbids_theory_imports": (
            "Self::Specification => matches!(other, Self::Model | Self::Specification)"
            in target_rs
        ),
        "target_audit_hardcodes_crate_mk": (
            "let crateCtor : Name := `Trusted.MirSemantics.Crate.mk" in tb_lean
        ),
        "sep_pcm_expl_pcm_requires_cancellative": (
            "cancellative : ∀ a b₁ b₂ c : M," in sep_pcm
        ),
        "execution_machine_closure_total": len(emc_set),
        "already_in_closure_counts": {
            "Miri.Concurrency.*": len(concur_in_emc),
            "Miri.TreeBorrows.*": len(tb_in_emc),
            "Miri.Interpreter.{Atomic,Thread,Tls}": len(interp_concur_in_emc),
            "sum": len(concur_in_emc) + len(tb_in_emc) + len(interp_concur_in_emc),
        },
        "control_existing_closure_delta": len(existing_ctrl),
        "os_sync_9_roots_extra_count": len(os_sync_9),
        "os_sync_9_roots_extra_modules": os_sync_9,
        "os_sync_plus_exec_intrinsic_extra_count": len(os_sync_with_exec_intrinsic),
        "os_sync_plus_exec_intrinsic_extra_modules": os_sync_with_exec_intrinsic,
    }


def main() -> int:
    zc_repo = Path(os.environ["ZEROCOPY_ROOT"])
    rev = os.environ.get("ZEROCOPY_REV", "origin/main")
    results: dict = {}
    pinned = find_pinned_anneal_rustc()
    if pinned is not None:
        results["pinned_anneal_rustc"] = inspect_mir_with_rustc(
            pinned, "anneal-pinned-1.98.0-nightly"
        )
    results["host_nightly_rustc"] = inspect_mir_with_rustc(
        find_host_nightly_rustc(), "host-nightly"
    )
    results["anneal_seams"] = inspect_anneal_seams(zc_repo, rev)
    if "PROBE_OUT" in os.environ:
        Path(os.environ["PROBE_OUT"]).write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps(results, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
