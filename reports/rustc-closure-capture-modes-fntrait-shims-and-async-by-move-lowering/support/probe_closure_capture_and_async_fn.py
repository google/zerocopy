#!/usr/bin/env python3
"""Real rustc MIR, LLVM IR, and native execution probe for:
1. RFC 2229 disjoint field capture, Drop-ADT truncation (non-Copy vs Copy fields),
   drop ordering, and raw-pointer dereference capture boundaries.
2. UniqueImmBorrow (ty::BorrowKind::UniqueImmutable -> mir::MutBorrowKind::ClosureCapture),
   pretty-printed MIR erasure to `&mut`, and E0501 / E0596 discriminators (Edition 2018 vs 2024).
3. ClosureFnPointer coercion (resolving to ClosureOnceShim with PassMode::Ignore ZST self),
   extern "rust-call" argument untupling, ClosureOnceShim normal + unwind drop paths, and FnPtrShim.
4. AsyncFn / AsyncFnMut lending coroutines vs AsyncFnOnce coroutine_by_move_body synthesis,
   including 1-to-N field renumbering with bridging projections, FnOnce short-circuiting,
   ConstructCoroutineInClosure shim MIR, and mid-suspension DropGlue.

All specimens are compiled and executed live with the host `rustc` binary.
"""

from __future__ import annotations

import argparse
import datetime as _dt
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


def _sanitize(text: str, tmpdir: str) -> str:
    return text.replace(tmpdir, "<TMP>")


def _run(cmd: list[str], cwd: str | None = None, timeout: int = 120) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=cwd,
        text=True,
        capture_output=True,
        timeout=timeout,
        check=False,
    )


def _rustc_version() -> dict[str, str]:
    proc = _run(["rustc", "--version", "--verbose"])
    if proc.returncode != 0:
        raise RuntimeError(f"rustc --version --verbose failed: {proc.stderr}")
    info: dict[str, str] = {"raw": proc.stdout.strip()}
    for line in proc.stdout.splitlines():
        if ":" in line:
            k, v = line.split(":", 1)
            info[k.strip()] = v.strip()
        elif line.startswith("rustc "):
            info["summary"] = line.strip()
    return info


def _compile_and_run(
    tmpdir: Path,
    name: str,
    src: str,
    *,
    edition: str = "2024",
    extra_flags: list[str] | None = None,
    dump_mir: bool = False,
    emit_llvm: bool = False,
    execute: bool = True,
) -> dict[str, Any]:
    rs_path = tmpdir / f"{name}.rs"
    bin_path = tmpdir / name
    rs_path.write_text(src, encoding="utf-8")

    cmd = ["rustc", f"--edition={edition}", str(rs_path), "-o", str(bin_path)]
    mir_dir = tmpdir / f"mir_{name}"
    if dump_mir:
        mir_dir.mkdir(exist_ok=True)
        cmd.extend(["-Z", "dump-mir=all", "-Z", f"dump-mir-dir={mir_dir}"])
    if extra_flags:
        cmd.extend(extra_flags)

    comp = _run(cmd)
    res: dict[str, Any] = {
        "name": name,
        "edition": edition,
        "compile_rc": comp.returncode,
        "compile_stderr_first_lines": _sanitize(comp.stderr, str(tmpdir)).splitlines()[:12],
    }

    if emit_llvm and comp.returncode == 0:
        ll_path = tmpdir / f"{name}.ll"
        ll_cmd = [
            "rustc",
            f"--edition={edition}",
            str(rs_path),
            "--emit=llvm-ir",
            "-o",
            str(ll_path),
        ]
        if extra_flags:
            ll_cmd.extend(extra_flags)
        ll_comp = _run(ll_cmd)
        res["llvm_rc"] = ll_comp.returncode
        if ll_comp.returncode == 0 and ll_path.exists():
            res["_llvm_text"] = _sanitize(ll_path.read_text(encoding="utf-8"), str(tmpdir))

    if dump_mir and mir_dir.exists():
        res["_mir_dir"] = mir_dir

    if execute and comp.returncode == 0 and bin_path.exists():
        run_proc = _run([str(bin_path)])
        res["run_rc"] = run_proc.returncode
        res["run_stdout"] = _sanitize(run_proc.stdout, str(tmpdir)).strip()
        res["run_stderr"] = _sanitize(run_proc.stderr, str(tmpdir)).strip()

    return res


def _read_mir(mir_dir: Path, pattern: str, tmpdir: str) -> str | None:
    matches = sorted(mir_dir.glob(pattern))
    if not matches:
        return None
    return _sanitize(matches[0].read_text(encoding="utf-8"), tmpdir)


def _extract_matching_lines(text: str, regex: str, limit: int = 25) -> list[str]:
    pat = re.compile(regex)
    out = [line.rstrip() for line in text.splitlines() if pat.search(line)]
    return out[:limit]


def _extract_llvm_fn(llvm_text: str, header_regex: str, max_lines: int = 55) -> list[str]:
    pat = re.compile(header_regex)
    out: list[str] = []
    collecting = False
    for line in llvm_text.splitlines():
        if not collecting and line.startswith("define ") and pat.search(line):
            collecting = True
            out = [line]
        elif collecting:
            out.append(line)
            if line.strip() == "}":
                break
            if len(out) >= max_lines:
                out.append("  ; ... truncated ...")
                break
    return out


# ---------------------------------------------------------------------------
# Probe 1: RFC 2229 Disjoint Field Capture, Drop-ADT Truncation & Raw-Ptr Boundary
# ---------------------------------------------------------------------------

SRC_PROBE1_DISJOINT_AND_DROP = r"""
#![allow(dead_code, dropping_copy_types)]
use std::cell::RefCell;
use std::rc::Rc;

struct Tracked {
    tag: &'static str,
    val: i32,
    log: Rc<RefCell<Vec<String>>>,
}

impl Tracked {
    fn read_val(&self) -> i32 {
        self.val
    }
}

impl Drop for Tracked {
    fn drop(&mut self) {
        self.log.borrow_mut().push(format!("drop:{}", self.tag));
    }
}

struct PairNoDrop {
    a: Tracked,
    b: Tracked,
}

struct PairWithDrop {
    a: Tracked,
    b: Tracked,
    log: Rc<RefCell<Vec<String>>>,
}

impl Drop for PairWithDrop {
    fn drop(&mut self) {
        self.log.borrow_mut().push("drop:PairWithDrop".to_string());
    }
}

fn test_disjoint_no_drop_move_and_mut_borrow() -> (i32, Vec<String>) {
    let log = Rc::new(RefCell::new(Vec::new()));
    let mut p = PairNoDrop {
        a: Tracked { tag: "a", val: 10, log: Rc::clone(&log) },
        b: Tracked { tag: "b", val: 20, log: Rc::clone(&log) },
    };

    // Disjoint capture in ONE closure: moves p.a (ByValue) and mutably borrows p.b.val (&mut).
    let c_one = || {
        p.b.val += p.a.val;
        let moved_a = p.a;
        moved_a.val
    };
    let moved_val = c_one();
    log.borrow_mut().push("after_c_one".to_string());
    let final_b = p.b.val;
    drop(p.b);
    log.borrow_mut().push("after_p_b".to_string());
    (moved_val * 100 + final_b, log.borrow().clone())
}

fn test_split_non_copy_no_drop() -> Vec<String> {
    let log = Rc::new(RefCell::new(Vec::new()));
    let mut p = PairNoDrop {
        a: Tracked { tag: "a", val: 1, log: Rc::clone(&log) },
        b: Tracked { tag: "b", val: 2, log: Rc::clone(&log) },
    };
    // `p.a.read_val()` requires `&p.a` where `p.a: Tracked` is `!Copy`, so `move ||`
    // captures ONLY `p.a: Tracked` by value; `p.b` stays live in the caller!
    let c = move || p.a.read_val();
    p.b.val += 5;
    let _ = c();
    log.borrow_mut().push("before_c_drop".to_string());
    drop(c);
    log.borrow_mut().push("after_c_drop".to_string());
    drop(p.b);
    log.borrow().clone()
}

fn test_with_drop_non_copy_truncates_whole_adt() -> Vec<String> {
    let log = Rc::new(RefCell::new(Vec::new()));
    let p = PairWithDrop {
        a: Tracked { tag: "a", val: 1, log: Rc::clone(&log) },
        b: Tracked { tag: "b", val: 2, log: Rc::clone(&log) },
        log: Rc::clone(&log),
    };
    // `p.a: Tracked` is `!Copy`, and enclosing `PairWithDrop` implements `Drop`.
    // `restrict_precision_for_drop_types` truncates `p.a` to whole `p: PairWithDrop`!
    let c = move || p.a.read_val();
    let _ = c();
    log.borrow_mut().push("before_c_drop".to_string());
    drop(c);
    log.borrow_mut().push("after_c_drop".to_string());
    log.borrow().clone()
}

fn test_with_drop_copy_field_not_truncated() -> Vec<String> {
    let log = Rc::new(RefCell::new(Vec::new()));
    let p = PairWithDrop {
        a: Tracked { tag: "a", val: 7, log: Rc::clone(&log) },
        b: Tracked { tag: "b", val: 8, log: Rc::clone(&log) },
        log: Rc::clone(&log),
    };
    // `p.a.val` has `Copy` type `i32`, so `restrict_precision_for_drop_types` does NOT
    // truncate: closure copies `p.a.val: i32` and leaves `p` alive in caller!
    let c = move || p.a.val;
    let _ = c();
    log.borrow_mut().push("before_c_drop".to_string());
    drop(c);
    log.borrow_mut().push("after_c_drop".to_string());
    // `p` is still alive here and dropped explicitly after `c`:
    drop(p);
    log.borrow().clone()
}

fn test_raw_ptr_boundary_no_deref_on_capture() -> i32 {
    let raw: *const PairNoDrop = std::ptr::null();
    // `restrict_precision_for_unsafe` stops before raw-pointer `Deref`,
    // capturing `raw` by value without dereferencing the null pointer.
    let c = move || unsafe { (*raw).a.val };
    let sz = std::mem::size_of_val(&c);
    drop(c);
    sz as i32
}

fn main() {
    let (v1, l1) = test_disjoint_no_drop_move_and_mut_borrow();
    let l2 = test_split_non_copy_no_drop();
    let l3 = test_with_drop_non_copy_truncates_whole_adt();
    let l4 = test_with_drop_copy_field_not_truncated();
    let ptr_sz = test_raw_ptr_boundary_no_deref_on_capture();
    println!("disjoint_val={v1}");
    println!("disjoint_log={}", l1.join(","));
    println!("split_no_drop_log={}", l2.join(","));
    println!("with_drop_non_copy_log={}", l3.join(","));
    println!("with_drop_copy_field_log={}", l4.join(","));
    println!("raw_ptr_closure_size={ptr_sz}");
}
"""

SRC_PROBE1_NEG_MOVE_OUT_OF_DROP = r"""
struct PairWithDrop {
    a: String,
    b: String,
}
impl Drop for PairWithDrop {
    fn drop(&mut self) {}
}
fn main() {
    let p = PairWithDrop { a: String::from("a"), b: String::from("b") };
    let c = || {
        drop(p.a);
    };
    c();
    println!("{}", p.b);
}
"""

SRC_PROBE1_NEG_WHOLE_DROP_ADT_MOVED = r"""
struct PairWithDrop {
    a: String,
    b: String,
}
impl Drop for PairWithDrop {
    fn drop(&mut self) {}
}
fn main() {
    let p = PairWithDrop { a: String::from("a"), b: String::from("b") };
    let c = move || {
        let _ = p.a.len();
    };
    println!("{}", p.b);
    c();
}
"""

# ---------------------------------------------------------------------------
# Probe 2: UniqueImmBorrow (ty::BorrowKind::UniqueImmutable -> mir::MutBorrowKind::ClosureCapture)
# ---------------------------------------------------------------------------

SRC_PROBE2_UNIQUE_IMM = r"""
fn probe_2021_disjoint_deref_mut() -> i32 {
    let mut x = 10i32;
    let r: &mut i32 = &mut x;
    let mut c = || {
        *r += 5;
    };
    c();
    x
}

fn probe_2021_truncated_unique_imm() -> (i32, usize) {
    let mut x = 10i32;
    // `r` is NOT `mut r`!
    let r: &mut i32 = &mut x;
    let mut c = || {
        // Mentioning `&r` (ancestor) + `*r += 7` (descendant across &mut Deref)
        // forces `compute_min_captures` to truncate `*r` back to `r`, converting
        // `MutBorrow` -> `UniqueImmutable` (`MutBorrowKind::ClosureCapture`).
        let addr = (&r as *const &mut i32) as usize;
        *r += 7;
        addr
    };
    let addr = c();
    (x, addr)
}

fn main() {
    let a = probe_2021_disjoint_deref_mut();
    let (b, addr) = probe_2021_truncated_unique_imm();
    println!("disjoint_deref={a} unique_imm_val={b} nonzero_addr={}", addr != 0);
}
"""

SRC_PROBE2_NEG_USER_MUT_BORROW = r"""
fn main() {
    let mut x = 10i32;
    let r: &mut i32 = &mut x;
    let _p = &mut r;
}
"""

SRC_PROBE2_NEG_UNIQUE_IMM_TRUNCATED_2024 = r"""
fn main() {
    let mut x = 10i32;
    let r: &mut i32 = &mut x;
    let mut c = || {
        let _ = &r;
        *r += 7;
    };
    let _alias = &r;
    c();
}
"""

SRC_PROBE2_NEG_DISJOINT_DEREF_2024 = r"""
fn main() {
    let mut x = 10i32;
    let r: &mut i32 = &mut x;
    let mut c = || {
        *r += 5;
    };
    let _alias = &r;
    c();
}
"""

SRC_PROBE2_NEG_UNIQUE_IMM_2018 = r"""
fn main() {
    let mut x = 10i32;
    let r: &mut i32 = &mut x;
    let mut c = || {
        *r += 5;
    };
    let _alias = &r;
    c();
}
"""

# ---------------------------------------------------------------------------
# Probe 3: ClosureFnPointer, extern "rust-call" untupling, ClosureOnceShim & FnPtrShim
# ---------------------------------------------------------------------------

SRC_PROBE3_SHIMS = r"""
use std::cell::RefCell;
use std::rc::Rc;

struct DropTag {
    bias: i32,
    log: Rc<RefCell<Vec<&'static str>>>,
}

impl DropTag {
    #[inline(never)]
    fn get_bias(&self) -> i32 {
        self.bias
    }
}

impl Drop for DropTag {
    fn drop(&mut self) {
        self.log.borrow_mut().push("drop:env");
    }
}

#[inline(never)]
fn call_fn<F: Fn(i32, i32) -> i32>(f: &F, x: i32, y: i32) -> i32 {
    f(x, y)
}

#[inline(never)]
fn call_fn_mut<F: FnMut(i32, i32) -> i32>(f: &mut F, x: i32, y: i32) -> i32 {
    f(x, y)
}

#[inline(never)]
fn call_fn_once<F: FnOnce(i32, i32) -> i32>(f: F, x: i32, y: i32) -> i32 {
    f(x, y)
}

#[inline(never)]
fn plain_add(x: i32, y: i32) -> i32 {
    x + y
}

#[inline(never)]
fn coerce_non_capturing() -> fn(i32, i32) -> i32 {
    |x: i32, y: i32| x * 10 + y
}

fn main() {
    // 1. ClosureFnPointer coercion
    let fp: fn(i32, i32) -> i32 = coerce_non_capturing();
    let r_fp = fp(3, 4);

    // 2. FnPtrShim (fn pointer called through Fn / FnMut / FnOnce traits)
    let p_fn: fn(i32, i32) -> i32 = plain_add;
    let r_ptr_fn = call_fn(&p_fn, 5, 6);
    let mut p_mut = p_fn;
    let r_ptr_mut = call_fn_mut(&mut p_mut, 5, 6);
    let r_ptr_once = call_fn_once(p_fn, 5, 6);

    // 3. Capturing Fn closure owning non-Copy DropTag called via Fn, FnMut, and FnOnce
    //    `tag.get_bias()` takes `&tag`, so `move ||` captures `tag: DropTag` by value.
    let log = Rc::new(RefCell::new(Vec::new()));
    let tag = DropTag { bias: 100, log: Rc::clone(&log) };
    let mut c = move |x: i32, y: i32| x + y + tag.get_bias();
    let r_c_fn = call_fn(&c, 1, 2);
    let r_c_mut = call_fn_mut(&mut c, 2, 3);
    log.borrow_mut().push("before_call_once");
    let r_c_once = call_fn_once(c, 3, 4);
    log.borrow_mut().push("after_call_once");

    // 4. Panic unwind path in ClosureOnceShim drops `self` in cleanup pad before resuming
    let log_unwind = Rc::new(RefCell::new(Vec::new()));
    let res_unwind = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let tag2 = DropTag { bias: 1, log: Rc::clone(&log_unwind) };
        let c_panic = move |x: i32, _y: i32| -> i32 {
            if x == 0 {
                panic!("boom");
            }
            tag2.get_bias()
        };
        call_fn_once(c_panic, 0, 0)
    }));
    log_unwind.borrow_mut().push("after_catch");

    println!("fp={r_fp} ptr=({r_ptr_fn},{r_ptr_mut},{r_ptr_once}) cap=({r_c_fn},{r_c_mut},{r_c_once})");
    println!("closure_once_log={}", log.borrow().join(","));
    println!("closure_once_unwind_is_err={} log={}", res_unwind.is_err(), log_unwind.borrow().join(","));
}
"""

# ---------------------------------------------------------------------------
# Probe 4: AsyncFn / AsyncFnMut lending vs AsyncFnOnce coroutine_by_move_body
# ---------------------------------------------------------------------------

SRC_PROBE4_ASYNC_CLOSURE = r"""
use std::cell::RefCell;
use std::future::Future;
use std::ops::{AsyncFn, AsyncFnMut, AsyncFnOnce};
use std::pin::Pin;
use std::rc::Rc;
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

struct TrackedBuf {
    label: &'static str,
    text: String,
    log: Rc<RefCell<Vec<String>>>,
}

impl Drop for TrackedBuf {
    fn drop(&mut self) {
        self.log.borrow_mut().push(format!("drop:{}", self.label));
    }
}

struct SplitPairWithDrop {
    a: TrackedBuf,
    b: TrackedBuf,
    log: Rc<RefCell<Vec<String>>>,
}

impl Drop for SplitPairWithDrop {
    fn drop(&mut self) {
        self.log.borrow_mut().push("drop:SplitPairWithDrop".to_string());
    }
}

#[inline(never)]
async fn invoke_async_fn<F: AsyncFn(usize) -> usize>(f: &F, k: usize) -> usize {
    f(k).await
}

#[inline(never)]
async fn invoke_async_fn_mut<F: AsyncFnMut(usize) -> usize>(f: &mut F, k: usize) -> usize {
    f(k).await
}

#[inline(never)]
fn construct_once_future<F: AsyncFnOnce(usize) -> usize>(
    f: F,
    k: usize,
) -> impl Future<Output = usize> {
    // `f` is owned in this stack frame; returning the future pops this frame
    // BEFORE the future is ever polled!
    f(k)
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

#[inline(never)]
fn run_lending_and_by_move_case() -> (usize, usize, usize, Vec<String>) {
    let log = Rc::new(RefCell::new(Vec::new()));
    let buf = TrackedBuf {
        label: "buf1",
        text: String::from("hello-async"),
        log: Rc::clone(&log),
    };
    let mut f = async move |k: usize| -> usize {
        let n1 = buf.text.len();
        YieldOnce(false).await;
        let n2 = buf.text.len();
        n1 + n2 + k
    };

    let r_ref1 = block_on(invoke_async_fn(&f, 1));
    let r_mut1 = block_on(invoke_async_fn_mut(&mut f, 2));
    log.borrow_mut().push("before_make_once".to_string());
    let fut_once = construct_once_future(f, 3);
    // `construct_once_future`'s frame has returned, yet `buf1` MUST NOT be dropped yet!
    log.borrow_mut().push("after_make_once_before_poll".to_string());
    let r_once = block_on(fut_once);
    log.borrow_mut().push("after_poll_once".to_string());
    (r_ref1, r_mut1, r_once, log.borrow().clone())
}

#[inline(never)]
fn run_mid_suspension_drop_case() -> (bool, Vec<String>) {
    let log = Rc::new(RefCell::new(Vec::new()));
    let buf = TrackedBuf {
        label: "buf_suspend",
        text: String::from("suspend-me"),
        log: Rc::clone(&log),
    };
    let f = async move |k: usize| -> usize {
        let n1 = buf.text.len();
        YieldOnce(false).await;
        n1 + buf.text.len() + k
    };
    let fut_once = construct_once_future(f, 0);
    let mut boxed = Box::pin(fut_once);
    let waker = Waker::noop();
    let mut cx = Context::from_waker(&waker);
    let first_pending = matches!(boxed.as_mut().poll(&mut cx), Poll::Pending);
    log.borrow_mut().push("after_first_pending".to_string());
    drop(boxed);
    log.borrow_mut().push("after_drop_suspended".to_string());
    (first_pending, log.borrow().clone())
}

#[inline(never)]
fn run_already_fn_once_async_closure() -> (usize, Vec<String>) {
    let log = Rc::new(RefCell::new(Vec::new()));
    let buf = TrackedBuf {
        label: "buf_fnonce",
        text: String::from("consume"),
        log: Rc::clone(&log),
    };
    // Moves `buf` inside the async body -> coroutine_kind is ALREADY FnOnce,
    // so `coroutine_by_move_body_def_id` returns `coroutine_def_id` directly
    // without synthesizing `{synthetic#0}`.
    let f = async move |k: usize| -> usize {
        let n = buf.text.len();
        YieldOnce(false).await;
        drop(buf);
        n + k
    };
    let fut = construct_once_future(f, 5);
    let v = block_on(fut);
    (v, log.borrow().clone())
}

#[inline(never)]
fn run_one_to_two_bridging_renumber_case() -> (usize, usize, Vec<String>) {
    let log = Rc::new(RefCell::new(Vec::new()));
    let pair = SplitPairWithDrop {
        a: TrackedBuf { label: "sp_a", text: String::from("abc"), log: Rc::clone(&log) },
        b: TrackedBuf { label: "sp_b", text: String::from("defgh"), log: Rc::clone(&log) },
        log: Rc::clone(&log),
    };
    // Parent `async move ||` captures ONE whole `pair: SplitPairWithDrop` (Drop ADT truncation!),
    // while inner lending coroutine captures TWO disjoint refs (`&pair.a.text` at `_1.1`,
    // `&pair.b.text` at `_1.2`). `by_move_body.rs` must remap BOTH `_1.1` AND `_1.2` back to
    // parent field `_1.1: SplitPairWithDrop` with distinct bridging field projections!
    let f = async move |k: usize| -> usize {
        let pa = &pair.a.text;
        let pb = &pair.b.text;
        YieldOnce(false).await;
        pa.len() + pb.len() + k
    };
    let v_ref = block_on(invoke_async_fn(&f, 1));
    let fut_once = construct_once_future(f, 2);
    let v_once = block_on(fut_once);
    (v_ref, v_once, log.borrow().clone())
}

fn main() {
    let (r1, r2, r3, l1) = run_lending_and_by_move_case();
    let (pend, l2) = run_mid_suspension_drop_case();
    let (v_once_only, l3) = run_already_fn_once_async_closure();
    let (sp_ref, sp_once, l4) = run_one_to_two_bridging_renumber_case();
    println!("lending_vs_once=({r1},{r2},{r3}) log={}", l1.join(","));
    println!("mid_suspend_pending={pend} log={}", l2.join(","));
    println!("already_fnonce={v_once_only} log={}", l3.join(","));
    println!("split_pair=({sp_ref},{sp_once}) log={}", l4.join(","));
}
"""


def run_all_probes() -> dict[str, Any]:
    rustc_info = _rustc_version()
    out: dict[str, Any] = {
        "observed_at": _dt.datetime.now(_dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "rustc": rustc_info,
    }

    with tempfile.TemporaryDirectory(prefix="closure_async_probe_") as td:
        tmpdir = Path(td)

        # ---- Probe 1 ----
        p1_pos = _compile_and_run(
            tmpdir, "p1_disjoint_drop", SRC_PROBE1_DISJOINT_AND_DROP, dump_mir=True
        )
        p1_mir_dir: Path = p1_pos.pop("_mir_dir")
        mir_disjoint_fn = _read_mir(
            p1_mir_dir, "p1_disjoint_drop.test_disjoint_no_drop_move_and_mut_borrow.*built.after.mir", td
        ) or ""
        mir_disjoint_closure = _read_mir(
            p1_mir_dir, "p1_disjoint_drop.test_disjoint_no_drop_move_and_mut_borrow-{closure#0}.*built.after.mir", td
        ) or ""
        mir_split_fn = _read_mir(
            p1_mir_dir, "p1_disjoint_drop.test_split_non_copy_no_drop.*built.after.mir", td
        ) or ""
        mir_with_drop_nc = _read_mir(
            p1_mir_dir, "p1_disjoint_drop.test_with_drop_non_copy_truncates_whole_adt.*built.after.mir", td
        ) or ""
        mir_with_drop_cp = _read_mir(
            p1_mir_dir, "p1_disjoint_drop.test_with_drop_copy_field_not_truncated.*built.after.mir", td
        ) or ""
        mir_raw_ptr_fn = _read_mir(
            p1_mir_dir, "p1_disjoint_drop.test_raw_ptr_boundary_no_deref_on_capture.*built.after.mir", td
        ) or ""

        p1_neg_e0509 = _compile_and_run(
            tmpdir, "p1_neg_e0509", SRC_PROBE1_NEG_MOVE_OUT_OF_DROP, execute=False
        )
        p1_neg_e0382 = _compile_and_run(
            tmpdir, "p1_neg_e0382", SRC_PROBE1_NEG_WHOLE_DROP_ADT_MOVED, execute=False
        )

        out["probe1_rfc2229_disjoint_and_drop"] = {
            "positive": p1_pos,
            "mir_excerpts": {
                "disjoint_one_closure_construct": _extract_matching_lines(
                    mir_disjoint_fn, r"\{closure@|&mut \(\(_4\.1|move \(_4\.0"
                ),
                "disjoint_one_closure_body": mir_disjoint_closure.splitlines()[:22],
                "split_non_copy_no_drop_construct": _extract_matching_lines(
                    mir_split_fn, r"\{closure@|move \(_4\.0|BackwardIncompatibleDropHint"
                ),
                "with_drop_non_copy_truncates_whole_adt": _extract_matching_lines(
                    mir_with_drop_nc, r"\{closure@|move _4\b"
                ),
                "with_drop_copy_field_not_truncated": _extract_matching_lines(
                    mir_with_drop_cp, r"\{closure@|copy \(\(_4\.0"
                ),
                "raw_ptr_boundary_construct": _extract_matching_lines(
                    mir_raw_ptr_fn, r"\{closure@|null|copy _1"
                ),
            },
            "negative_move_out_of_drop_e0509": p1_neg_e0509,
            "negative_whole_drop_adt_moved_e0382": p1_neg_e0382,
        }

        # ---- Probe 2 ----
        p2_pos = _compile_and_run(
            tmpdir, "p2_unique_imm", SRC_PROBE2_UNIQUE_IMM, dump_mir=True
        )
        p2_mir_dir: Path = p2_pos.pop("_mir_dir")
        mir_p2_disjoint = _read_mir(
            p2_mir_dir, "p2_unique_imm.probe_2021_disjoint_deref_mut.*built.after.mir", td
        ) or ""
        mir_p2_uniq = _read_mir(
            p2_mir_dir, "p2_unique_imm.probe_2021_truncated_unique_imm.*built.after.mir", td
        ) or ""
        mir_p2_uniq_post = _read_mir(
            p2_mir_dir, "p2_unique_imm.probe_2021_truncated_unique_imm.*CleanupPostBorrowck.after.mir", td
        ) or ""

        p2_neg_e0596 = _compile_and_run(
            tmpdir, "p2_neg_e0596", SRC_PROBE2_NEG_USER_MUT_BORROW, execute=False
        )
        p2_neg_e0501_trunc_2024 = _compile_and_run(
            tmpdir, "p2_neg_e0501_trunc_2024", SRC_PROBE2_NEG_UNIQUE_IMM_TRUNCATED_2024, execute=False
        )
        p2_neg_e0501_deref_2024 = _compile_and_run(
            tmpdir, "p2_neg_e0501_deref_2024", SRC_PROBE2_NEG_DISJOINT_DEREF_2024, execute=False
        )
        p2_neg_e0501_2018 = _compile_and_run(
            tmpdir,
            "p2_neg_e0501_2018",
            SRC_PROBE2_NEG_UNIQUE_IMM_2018,
            edition="2018",
            execute=False,
        )

        out["probe2_unique_imm_borrow"] = {
            "positive": p2_pos,
            "mir_excerpts": {
                "disjoint_deref_2021_built": _extract_matching_lines(
                    mir_p2_disjoint, r"let _2:|&mut|&uniq|\{closure@"
                ),
                "truncated_unique_imm_2021_built": _extract_matching_lines(
                    mir_p2_uniq, r"let _2:|&mut|&uniq|\{closure@"
                ),
                "truncated_unique_imm_2021_post_cleanup": _extract_matching_lines(
                    mir_p2_uniq_post, r"let _2:|&mut|&uniq|\{closure@"
                ),
                "built_mir_prints_uniq_token": "&uniq" in mir_p2_uniq,
                "post_cleanup_prints_mut_on_non_mut_local_r": (
                    "let _2: &mut i32;" in mir_p2_uniq_post and "= &mut _2;" in mir_p2_uniq_post
                ),
            },
            "negative_user_mut_borrow_e0596": p2_neg_e0596,
            "negative_unique_imm_truncated_2024_e0501": p2_neg_e0501_trunc_2024,
            "negative_disjoint_deref_2024_e0501": p2_neg_e0501_deref_2024,
            "negative_unique_imm_2018_e0501": p2_neg_e0501_2018,
        }

        # ---- Probe 3 ----
        p3 = _compile_and_run(
            tmpdir,
            "p3_shims",
            SRC_PROBE3_SHIMS,
            extra_flags=["-C", "opt-level=0"],
            dump_mir=True,
            emit_llvm=True,
        )
        p3_mir_dir: Path = p3.pop("_mir_dir")
        p3_llvm: str = p3.pop("_llvm_text", "")
        mir_coerce = _read_mir(p3_mir_dir, "p3_shims.coerce_non_capturing.*built.after.mir", td) or ""
        mir_call_once_fn = _read_mir(p3_mir_dir, "p3_shims.call_fn_once.*built.after.mir", td) or ""
        mir_cap_closure = _read_mir(p3_mir_dir, "p3_shims.main-{closure#0}.*built.after.mir", td) or ""

        out["probe3_fn_trait_shims_and_rust_call"] = {
            "positive": p3,
            "mir_excerpts": {
                "coerce_non_capturing_built": _extract_matching_lines(
                    mir_coerce, r"ClosureFnPointer|\{closure@|PointerCoercion|return;"
                ),
                "call_fn_once_built": _extract_matching_lines(
                    mir_call_once_fn, r"fn call_fn_once|FnOnce::call_once|_0 ="
                ),
                "capturing_closure_body_signature": mir_cap_closure.splitlines()[:18],
            },
            "llvm_excerpts": {
                "coerce_non_capturing_fn_ir": _extract_llvm_fn(
                    p3_llvm, r"20coerce_non_capturing\("
                ),
                "closure_fn_pointer_target_call_once_shim_ir": _extract_llvm_fn(
                    p3_llvm, r"20coerce_non_capturing0.*FnOnce.*9call_once"
                ),
                "fn_ptr_shim_call_once_ir": _extract_llvm_fn(
                    p3_llvm, r"_RNvYFllEl.*FnOnceTllEE9call_once"
                ),
                "capturing_closure_call_once_shim_ir": _extract_llvm_fn(
                    p3_llvm, r"4main0.*FnOnceTllEE9call_once"
                ),
                "call_fn_mut_on_fn_closure_direct_dispatch_ir": _extract_llvm_fn(
                    p3_llvm, r"11call_fn_mutNCNvB2_4main0"
                ),
            },
        }

        # ---- Probe 4 ----
        p4 = _compile_and_run(
            tmpdir,
            "p4_async_closure",
            SRC_PROBE4_ASYNC_CLOSURE,
            extra_flags=["-C", "opt-level=0"],
            dump_mir=True,
            emit_llvm=True,
        )
        p4_mir_dir: Path = p4.pop("_mir_dir")
        p4_llvm: str = p4.pop("_llvm_text", "")

        state_transformed = sorted(
            p.name for p in p4_mir_dir.glob("*StateTransform.after.mir")
        )
        synthetic_built = sorted(
            p.name for p in p4_mir_dir.glob("*synthetic*built.after.mir")
        )
        construct_shims = sorted(
            p.name for p in p4_mir_dir.glob("*coroutine_closure_by_*")
        )

        lending_built = _read_mir(
            p4_mir_dir,
            "p4_async_closure.run_lending_and_by_move_case-{closure#0}-{closure#0}.*built.after.mir",
            td,
        ) or ""
        by_move_built = _read_mir(
            p4_mir_dir,
            "p4_async_closure.run_lending_and_by_move_case-{closure#0}-{synthetic#0}.*built.after.mir",
            td,
        ) or ""
        construct_shim_mir = _read_mir(
            p4_mir_dir,
            "p4_async_closure.run_lending_and_by_move_case-{closure#0}.*coroutine_closure_by_move.0.mir",
            td,
        ) or ""
        lending_state = _read_mir(
            p4_mir_dir,
            "p4_async_closure.run_lending_and_by_move_case-{closure#0}-{closure#0}.*StateTransform.after.mir",
            td,
        ) or ""
        by_move_state = _read_mir(
            p4_mir_dir,
            "p4_async_closure.run_lending_and_by_move_case-{closure#0}-{synthetic#0}.*StateTransform.after.mir",
            td,
        ) or ""
        split_lending_built = _read_mir(
            p4_mir_dir,
            "p4_async_closure.run_one_to_two_bridging_renumber_case-{closure#0}-{closure#0}.*built.after.mir",
            td,
        ) or ""
        split_by_move_built = _read_mir(
            p4_mir_dir,
            "p4_async_closure.run_one_to_two_bridging_renumber_case-{closure#0}-{synthetic#0}.*built.after.mir",
            td,
        ) or ""
        split_construct_shim_mir = _read_mir(
            p4_mir_dir,
            "p4_async_closure.run_one_to_two_bridging_renumber_case-{closure#0}.*coroutine_closure_by_move.0.mir",
            td,
        ) or ""

        already_fnonce_synthetics = [
            n for n in synthetic_built if "run_already_fn_once_async_closure" in n
        ]

        out["probe4_async_closure_by_move_body"] = {
            "positive": p4,
            "state_transformed_bodies": state_transformed,
            "synthetic_by_move_built_bodies": synthetic_built,
            "construct_coroutine_shim_dumps": construct_shims,
            "already_fnonce_synthesizes_synthetic_body": len(already_fnonce_synthetics) > 0,
            "mir_excerpts": {
                "construct_coroutine_by_move_shim_lending_case": construct_shim_mir.splitlines(),
                "construct_coroutine_by_move_shim_one_to_two_case": split_construct_shim_mir.splitlines(),
                "lending_closure0_header_and_upvar_access": _extract_matching_lines(
                    lending_built, r"^(fn |    debug buf|        _\d+ = &\(\*\(_1\.|        drop\(_1\))"
                ),
                "by_move_synthetic0_header_and_upvar_access": _extract_matching_lines(
                    by_move_built, r"^(fn |    debug buf|        _\d+ = &\(\(_1\.|        drop\(_1\))"
                ),
                "lending_state_transform_upvar_access": _extract_matching_lines(
                    lending_state, r"TrackedBuf|discriminant\(|drop\("
                )[:20],
                "by_move_state_transform_upvar_access": _extract_matching_lines(
                    by_move_state, r"TrackedBuf|discriminant\(|drop\("
                )[:20],
                "one_to_two_split_lending_upvars": _extract_matching_lines(
                    split_lending_built, r"debug |&\(\*\(_1\.|TrackedBuf|SplitPairWithDrop"
                ),
                "one_to_two_split_by_move_upvars": _extract_matching_lines(
                    split_by_move_built, r"debug |&\(\(\(_1\.|TrackedBuf|SplitPairWithDrop"
                ),
            },
            "llvm_sret_coroutine_sizes": _extract_matching_lines(
                p4_llvm,
                r"define internal void @_RN(C|SN)CNv.*run_(lending_and_by_move|mid_suspension_drop|already_fn_once|one_to_two_bridging)",
                limit=20,
            ),
        }

    return out


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out",
        type=Path,
        default=None,
        help="Optional path to write JSON results (defaults to stdout).",
    )
    args = parser.parse_args()
    results = run_all_probes()
    rendered = json.dumps(results, indent=2, ensure_ascii=True) + "\n"
    if args.out is not None:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(rendered, encoding="utf-8")
        print(f"wrote {args.out} ({len(rendered)} bytes)")
    else:
        sys.stdout.write(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
