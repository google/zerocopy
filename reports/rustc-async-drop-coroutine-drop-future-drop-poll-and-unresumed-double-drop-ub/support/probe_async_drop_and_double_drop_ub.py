#!/usr/bin/env python3
"""Reproducible rustc & Miri probe for #![feature(async_drop)],
TerminatorKind::CoroutineDrop, future_drop_poll / AsyncDropGlue shims,
unresumed upvar sync-fallback, cross-crate feature-gate non-transitivity,
and the live Miri heap use-after-free double-drop bug in async_drop_in_place.

Requires:
  - Nightly `rustc` supporting `#![feature(async_drop)]`
  - `cargo` with `miri` component installed (`cargo miri run`)

Usage:
  python3 probe_async_drop_and_double_drop_ub.py [--out results.json]
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


def _sanitize(text: str) -> str:
    home = os.path.expanduser("~")
    if home and home != "~":
        text = text.replace(home, "$HOME")
    return text


def _run(
    cmd: list[str],
    *,
    cwd: Path | None = None,
    env: dict[str, str] | None = None,
    timeout: int = 120,
) -> dict[str, Any]:
    proc = subprocess.run(
        cmd,
        cwd=str(cwd) if cwd else None,
        env=env,
        capture_output=True,
        text=True,
        timeout=timeout,
    )
    return {
        "cmd": cmd,
        "rc": proc.returncode,
        "stdout": _sanitize(proc.stdout),
        "stderr": _sanitize(proc.stderr),
    }


def _run_miri_crate(source: str, miri_flags: str = "-Zmiri-tree-borrows") -> dict[str, Any]:
    with tempfile.TemporaryDirectory(prefix="adrop_miri_") as td:
        root = Path(td)
        (root / "src").mkdir()
        (root / "Cargo.toml").write_text(
            '[package]\nname = "adrop_probe"\nversion = "0.1.0"\nedition = "2024"\n',
            encoding="utf-8",
        )
        (root / "src" / "main.rs").write_text(source, encoding="utf-8")
        env = os.environ.copy()
        env["MIRIFLAGS"] = miri_flags
        # Prefer --offline so probe works identically in air-gapped environments;
        # no external dependencies exist.
        res = _run(["cargo", "miri", "run", "--offline"], cwd=root, env=env)
        return {
            "miri_rc": res["rc"],
            "stdout": res["stdout"].strip(),
            "stderr": res["stderr"],
        }


C1_SRC = r"""
#![feature(async_drop)]
use std::future::AsyncDrop;
use std::pin::Pin;

struct OnlyAsync;
impl AsyncDrop for OnlyAsync {
    async fn drop(self: Pin<&mut Self>) {}
}

fn main() {
    let _ = OnlyAsync;
}
"""

C2_SRC = r"""
#![feature(async_drop)]
use std::future::{AsyncDrop, Future};
use std::marker::PhantomPinned;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::pin::Pin;
use std::sync::Mutex;
use std::task::{Context, Poll, Waker};

static LOG: Mutex<Vec<String>> = Mutex::new(Vec::new());

struct YieldOnce(bool);
impl Future for YieldOnce {
    type Output = ();
    fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<()> {
        if !self.0 {
            self.0 = true;
            Poll::Pending
        } else {
            Poll::Ready(())
        }
    }
}

struct Guard {
    name: &'static str,
    val: u32,
    self_ptr: *const u32,
    _pin: PhantomPinned,
}

impl Guard {
    fn new(name: &'static str, val: u32) -> Self {
        Self { name, val, self_ptr: std::ptr::null(), _pin: PhantomPinned }
    }

    fn init_self_ref(self: Pin<&mut Self>) {
        // SAFETY: we only initialize the internal raw pointer; `self` is never moved.
        let this = unsafe { self.get_unchecked_mut() };
        this.self_ptr = &raw const this.val;
    }
}

impl Drop for Guard {
    fn drop(&mut self) {
        LOG.lock().unwrap().push(format!("sync:{}:{}", self.name, self.val));
    }
}

impl AsyncDrop for Guard {
    async fn drop(mut self: Pin<&mut Self>) {
        let addr_before = &raw const *self as usize;
        if !self.self_ptr.is_null() {
            let ptr_val = unsafe { *self.self_ptr };
            assert_eq!(ptr_val, self.val);
            assert_eq!(self.self_ptr, &raw const self.val);
        }
        LOG.lock().unwrap().push(format!("async_pre:{}:{}", self.name, self.val));
        YieldOnce(false).await;
        let addr_after = &raw const *self as usize;
        assert_eq!(addr_before, addr_after, "Pin address stability across .await in AsyncDrop::drop");
        if !self.self_ptr.is_null() {
            let ptr_val = unsafe { *self.self_ptr };
            assert_eq!(ptr_val, self.val);
            assert_eq!(self.self_ptr, &raw const self.val);
        }
        let bumped = {
            let this = unsafe { self.as_mut().get_unchecked_mut() };
            this.val += 100;
            this.val
        };
        if !self.self_ptr.is_null() {
            assert_eq!(unsafe { *self.self_ptr }, bumped);
        }
        LOG.lock().unwrap().push(format!("async_post:{}:{}", self.name, bumped));
    }
}

fn block_on<F: Future>(fut: F) -> F::Output {
    let mut fut = std::pin::pin!(fut);
    let waker = Waker::noop();
    let mut cx = Context::from_waker(&waker);
    loop {
        if let Poll::Ready(v) = fut.as_mut().poll(&mut cx) {
            return v;
        }
    }
}

fn main() {
    // 1. Sync scope always invokes sync Drop::drop.
    {
        let _sync = Guard::new("sync_ctx", 1);
    }

    // 2. Normal async scope exit invokes AsyncDrop::drop in reverse declaration order,
    //    preserving Pin<&mut Self> address stability and self-referential pointers across .await.
    block_on(async {
        let mut first = std::pin::pin!(Guard::new("first", 2));
        first.as_mut().init_self_ref();
        let mut second = std::pin::pin!(Guard::new("second", 3));
        second.as_mut().init_self_ref();
        YieldOnce(false).await;
        let _ = (&first, &second);
    });

    // 3. Unwind cleanup edge inside an async block forces sync Drop::drop (!unwind.is_cleanup()).
    let res = catch_unwind(AssertUnwindSafe(|| {
        block_on(async {
            let _unwind = Guard::new("unwind_cleanup", 4);
            panic!("boom");
        });
    }));
    assert!(res.is_err());

    let log = LOG.lock().unwrap();
    println!("C2_LOG={:?}", *log);
}
"""

C3_COMMON = r"""
#![feature(async_drop)]
#![allow(dead_code, unused_imports)]
use std::future::{AsyncDrop, Future, async_drop_in_place};
use std::mem::ManuallyDrop;
use std::pin::Pin;
use std::task::{Context, Poll, Waker};

struct YieldOnce(bool);
impl Future for YieldOnce {
    type Output = ();
    fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<()> {
        if !self.0 {
            self.0 = true;
            Poll::Pending
        } else {
            Poll::Ready(())
        }
    }
}

struct HeapAsyncGuard(Box<u32>);
impl Drop for HeapAsyncGuard {
    fn drop(&mut self) {
        println!("SYNC_DROP {}", *self.0);
    }
}
impl AsyncDrop for HeapAsyncGuard {
    async fn drop(self: Pin<&mut Self>) {
        println!("ASYNC_PRE {}", *self.0);
        YieldOnce(false).await;
        println!("ASYNC_POST {}", *self.0);
    }
}

struct ImmediateAsyncGuard(Box<u32>);
impl Drop for ImmediateAsyncGuard {
    fn drop(&mut self) {
        println!("IMMEDIATE_SYNC_DROP {}", *self.0);
    }
}
impl AsyncDrop for ImmediateAsyncGuard {
    async fn drop(self: Pin<&mut Self>) {
        println!("ASYNC_IMMEDIATE {}", *self.0);
    }
}

fn block_on<F: Future>(fut: F) -> F::Output {
    let mut fut = std::pin::pin!(fut);
    let waker = Waker::noop();
    let mut cx = Context::from_waker(&waker);
    loop {
        if let Poll::Ready(v) = fut.as_mut().poll(&mut cx) {
            return v;
        }
    }
}
"""

C3A_UNRESUMED_ASYNC = C3_COMMON + r"""
fn main() {
    block_on(async {
        let g = HeapAsyncGuard(Box::new(42));
        let mut slot = ManuallyDrop::new(async move {
            let g = g;
            YieldOnce(false).await;
            drop(g);
        });
        unsafe { async_drop_in_place(&mut *slot).await; }
    });
}
"""

C3B_UNRESUMED_PLAIN = C3_COMMON + r"""
fn main() {
    block_on(async {
        let b = Box::new(77u32);
        let mut slot = ManuallyDrop::new(async move {
            YieldOnce(false).await;
            drop(b);
        });
        unsafe { async_drop_in_place(&mut *slot).await; }
    });
}
"""

C3C_SUSPENDED_YIELDING_ASYNC = C3_COMMON + r"""
fn main() {
    block_on(async {
        let g = HeapAsyncGuard(Box::new(99));
        let mut slot = ManuallyDrop::new(async move {
            let g = g;
            YieldOnce(false).await;
            drop(g);
        });
        let waker = Waker::noop();
        let mut cx = Context::from_waker(&waker);
        let p = unsafe { Pin::new_unchecked(&mut *slot).poll(&mut cx) };
        assert!(matches!(p, Poll::Pending));
        unsafe { async_drop_in_place(&mut *slot).await; }
    });
}
"""

C3D_SUSPENDED_IMMEDIATE_ASYNC = C3_COMMON + r"""
fn main() {
    block_on(async {
        let mut slot = ManuallyDrop::new(async {
            let g = ImmediateAsyncGuard(Box::new(123));
            YieldOnce(false).await;
            drop(g);
        });
        let waker = Waker::noop();
        let mut cx = Context::from_waker(&waker);
        let p = unsafe { Pin::new_unchecked(&mut *slot).poll(&mut cx) };
        assert!(matches!(p, Poll::Pending));
        unsafe { async_drop_in_place(&mut *slot).await; }
    });
}
"""

C3E_SUSPENDED_UNMOVED_UPVAR = C3_COMMON + r"""
fn main() {
    block_on(async {
        let g = HeapAsyncGuard(Box::new(66));
        let mut slot = ManuallyDrop::new(async move {
            YieldOnce(false).await;
            let _keep = g;
        });
        let waker = Waker::noop();
        let mut cx = Context::from_waker(&waker);
        let p = unsafe { Pin::new_unchecked(&mut *slot).poll(&mut cx) };
        assert!(matches!(p, Poll::Pending));
        unsafe { async_drop_in_place(&mut *slot).await; }
    });
}
"""

C3F_SYNC_DRIVER_UNRESUMED_CONTROL = C3_COMMON + r"""
fn main() {
    let g = HeapAsyncGuard(Box::new(42));
    let mut slot = ManuallyDrop::new(async move {
        let g = g;
        YieldOnce(false).await;
        drop(g);
    });
    let drop_fut = unsafe { async_drop_in_place(&mut *slot) };
    block_on(drop_fut);
}
"""

C3G_SAFE_UNRESUMED_UPVAR_SYNC_FALLBACK = C3_COMMON + r"""
fn main() {
    block_on(async {
        let g = HeapAsyncGuard(Box::new(55));
        let _unresumed = async move {
            YieldOnce(false).await;
            let _keep = g;
        };
    });
}
"""

C4_DEP_SRC = r"""
#![feature(async_drop)]
use std::future::AsyncDrop;
use std::pin::Pin;
use std::sync::atomic::{AtomicUsize, Ordering};

pub struct DepGuard(pub &'static AtomicUsize);

impl Drop for DepGuard {
    fn drop(&mut self) {
        self.0.fetch_add(10, Ordering::SeqCst);
    }
}

impl AsyncDrop for DepGuard {
    async fn drop(self: Pin<&mut Self>) {
        self.0.fetch_add(1000, Ordering::SeqCst);
    }
}

pub struct DepWrap(pub DepGuard);
"""

C4_MAIN_SRC = r"""
extern crate dep;
use dep::{DepGuard, DepWrap};
use std::future::Future;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::task::{Context, Poll, Waker};

#[allow(dead_code)]
struct LocalWrap(DepGuard);

fn block_on<F: Future>(fut: F) -> F::Output {
    let mut fut = std::pin::pin!(fut);
    let waker = Waker::noop();
    let mut cx = Context::from_waker(&waker);
    loop {
        if let Poll::Ready(v) = fut.as_mut().poll(&mut cx) {
            return v;
        }
    }
}

fn main() {
    static BARE: AtomicUsize = AtomicUsize::new(0);
    static OPT: AtomicUsize = AtomicUsize::new(0);
    static ARR: AtomicUsize = AtomicUsize::new(0);
    static TUP: AtomicUsize = AtomicUsize::new(0);
    static BOXED: AtomicUsize = AtomicUsize::new(0);
    static WRAP: AtomicUsize = AtomicUsize::new(0);
    static DEP_WRAP: AtomicUsize = AtomicUsize::new(0);
    static PARTIAL_TUP: AtomicUsize = AtomicUsize::new(0);

    block_on(async {
        let _bare = DepGuard(&BARE);
        let _opt = Some(DepGuard(&OPT));
        let _arr = [DepGuard(&ARR)];
        let _tup = (DepGuard(&TUP),);
        let _box = Box::new(DepGuard(&BOXED));
        let _wrap = LocalWrap(DepGuard(&WRAP));
        let _dwrap = DepWrap(DepGuard(&DEP_WRAP));
        let ptup = (DepGuard(&PARTIAL_TUP), String::from("moved_out"));
        drop(ptup.1);
    });

    println!(
        "CROSS_CRATE bare={} opt={} arr={} tup={} box={} wrap={} dep_wrap={} partial_tup={}",
        BARE.load(Ordering::SeqCst),
        OPT.load(Ordering::SeqCst),
        ARR.load(Ordering::SeqCst),
        TUP.load(Ordering::SeqCst),
        BOXED.load(Ordering::SeqCst),
        WRAP.load(Ordering::SeqCst),
        DEP_WRAP.load(Ordering::SeqCst),
        PARTIAL_TUP.load(Ordering::SeqCst),
    );
}
"""


def run_all() -> dict[str, Any]:
    rustc_v = _run(["rustc", "--version", "--verbose"])
    miri_v = _run(["cargo", "miri", "--version"])
    results: dict[str, Any] = {
        "rustc_version": rustc_v["stdout"].strip(),
        "miri_version": miri_v["stdout"].strip(),
        "cases": {},
    }

    # Case 1: AsyncDrop impl without companion sync Drop impl
    with tempfile.TemporaryDirectory(prefix="adrop_c1_") as td:
        root = Path(td)
        src = root / "main.rs"
        src.write_text(C1_SRC, encoding="utf-8")
        c1 = _run(["rustc", "--edition=2024", str(src), "-o", str(root / "bin")])
        results["cases"]["c1_async_drop_without_sync_drop"] = {
            "compile_rc": c1["rc"],
            "compile_stderr": c1["stderr"],
        }

    # Case 2 (native): sync ctx, reverse async drop order with Pin self-ref across .await, unwind sync fallback
    with tempfile.TemporaryDirectory(prefix="adrop_c2_") as td:
        root = Path(td)
        src = root / "main.rs"
        bin_path = root / "bin"
        src.write_text(C2_SRC, encoding="utf-8")
        comp = _run(["rustc", "--edition=2024", str(src), "-o", str(bin_path)])
        entry: dict[str, Any] = {
            "compile_rc": comp["rc"],
            "compile_stderr": comp["stderr"],
        }
        if comp["rc"] == 0:
            run_res = _run([str(bin_path)])
            entry["run_rc"] = run_res["rc"]
            entry["stdout"] = run_res["stdout"].strip()
            entry["run_stderr"] = run_res["stderr"].strip()
        results["cases"]["c2_native_pin_order_and_unwind"] = entry

    # Case 2 (Miri Tree Borrows)
    results["cases"]["c2_miri_tree_borrows"] = _run_miri_crate(C2_SRC)

    # Case 3a..3g (Miri Tree Borrows)
    results["cases"]["c3a_miri_unresumed_with_async_drop"] = _run_miri_crate(C3A_UNRESUMED_ASYNC)
    results["cases"]["c3b_miri_unresumed_plain_box_coro"] = _run_miri_crate(C3B_UNRESUMED_PLAIN)
    results["cases"]["c3c_miri_suspended_yielding_async_drop"] = _run_miri_crate(C3C_SUSPENDED_YIELDING_ASYNC)
    results["cases"]["c3d_miri_suspended_immediate_async_drop"] = _run_miri_crate(C3D_SUSPENDED_IMMEDIATE_ASYNC)
    results["cases"]["c3e_miri_suspended_unmoved_upvar_async_drop"] = _run_miri_crate(C3E_SUSPENDED_UNMOVED_UPVAR)
    results["cases"]["c3f_miri_sync_driver_unresumed_control"] = _run_miri_crate(C3F_SYNC_DRIVER_UNRESUMED_CONTROL)
    results["cases"]["c3g_miri_safe_unresumed_upvar_sync_fallback"] = _run_miri_crate(
        C3G_SAFE_UNRESUMED_UPVAR_SYNC_FALLBACK
    )

    # Case 4: cross-crate non-transitive feature gate + partial-move flip
    with tempfile.TemporaryDirectory(prefix="adrop_c4_") as td:
        root = Path(td)
        dep_src = root / "dep.rs"
        main_src = root / "main.rs"
        dep_lib = root / "libdep.rlib"
        main_bin = root / "main"
        dep_src.write_text(C4_DEP_SRC, encoding="utf-8")
        main_src.write_text(C4_MAIN_SRC, encoding="utf-8")
        c_dep = _run([
            "rustc", "--edition=2024", "--crate-type=lib", "--crate-name=dep",
            str(dep_src), "-o", str(dep_lib),
        ])
        c_main = _run([
            "rustc", "--edition=2024", "--extern", f"dep={dep_lib}",
            str(main_src), "-o", str(main_bin),
        ])
        entry4: dict[str, Any] = {
            "dep_compile_rc": c_dep["rc"],
            "main_compile_rc": c_main["rc"],
            "main_compile_stderr": c_main["stderr"],
        }
        if c_main["rc"] == 0:
            run4 = _run([str(main_bin)])
            entry4["run_rc"] = run4["rc"]
            entry4["stdout"] = run4["stdout"].strip()
        results["cases"]["c4_cross_crate_non_transitive_gate"] = entry4

    return results


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, help="Optional path to write JSON results")
    args = parser.parse_args()

    results = run_all()
    rendered = json.dumps(results, indent=2) + "\n"
    if args.out:
        args.out.write_text(rendered, encoding="utf-8")
    else:
        sys.stdout.write(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
