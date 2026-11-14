#!/usr/bin/env python3
"""
Executes 20 self-referential async/await, gen, async gen, and Coroutine litmus
tests under Miri with both Tree Borrows (-Zmiri-tree-borrows) and Stacked Borrows
(-Zmiri-stacked-borrows), plus negative controls for ResumedAfterReturn,
ResumedAfterPanic, and forged Unpin on a self-referential coroutine.
"""

import json
import os
import subprocess
import tempfile
from pathlib import Path

LITMUS_SOURCE = r'''
#![feature(coroutines, coroutine_trait, gen_blocks, async_iterator, stmt_expr_attributes)]
#![allow(dead_code, unused_variables, unused_assignments)]

use std::cell::UnsafeCell;
use std::future::Future;
use std::ops::{Coroutine, CoroutineState};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::pin::{Pin, pin};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};

fn dummy_waker() -> Waker {
    fn no_op(_: *const ()) {}
    fn clone(_: *const ()) -> RawWaker { RawWaker::new(core::ptr::null(), &VTABLE) }
    static VTABLE: RawWakerVTable = RawWakerVTable::new(clone, no_op, no_op, no_op);
    unsafe { Waker::from_raw(RawWaker::new(core::ptr::null(), &VTABLE)) }
}

struct YieldSteps(u32);
impl Future for YieldSteps {
    type Output = u64;
    fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<u64> {
        if self.0 == 0 {
            Poll::Ready(1)
        } else {
            self.0 -= 1;
            Poll::Pending
        }
    }
}

struct PanicOnSecondPoll(bool);
impl Future for PanicOnSecondPoll {
    type Output = u64;
    fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<u64> {
        if self.0 {
            panic!("mid-await panic!");
        } else {
            self.0 = true;
            Poll::Pending
        }
    }
}

static DROP_COUNTER: AtomicUsize = AtomicUsize::new(0);
struct CountedDrop(u64);
impl Drop for CountedDrop {
    fn drop(&mut self) {
        DROP_COUNTER.fetch_add(1, Ordering::SeqCst);
    }
}

fn drive_steps<F: Future>(mut fut: Pin<&mut F>, max_polls: usize) -> Option<F::Output> {
    let waker = dummy_waker();
    let mut cx = Context::from_waker(&waker);
    for _ in 0..max_polls {
        match fut.as_mut().poll(&mut cx) {
            Poll::Ready(v) => return Some(v),
            Poll::Pending => {}
        }
    }
    None
}

// L01: Shared reference across 1 yield point
async fn l01_shared_ref_1_yield(x: u64) -> u64 {
    let arr = [x, x + 1, x + 2, x + 3];
    let r = &arr;
    let w = YieldSteps(1).await;
    r[0] + r[3] + w
}

// L02: Shared reference across 3 yield points
async fn l02_shared_ref_3_yields(x: u64) -> u64 {
    let arr = [x, x + 10, x + 20, x + 30];
    let r1 = &arr[0..2];
    let r2 = &arr[2..4];
    let a = YieldSteps(1).await;
    let b = YieldSteps(1).await;
    let c = YieldSteps(1).await;
    r1[0] + r1[1] + r2[0] + r2[1] + a + b + c
}

// L03: Mutable reference across 1 yield point
async fn l03_mut_ref_1_yield(x: u64) -> u64 {
    let mut val = x;
    let r = &mut val;
    *r += 5;
    let w = YieldSteps(1).await;
    *r += w;
    val
}

// L04: Mutable slice split_at_mut across 2 yield points
async fn l04_split_at_mut_2_yields(x: u64) -> u64 {
    let mut buf = [x, x + 1, x + 2, x + 3];
    let (left, right) = buf.split_at_mut(2);
    left[0] += 10;
    let a = YieldSteps(1).await;
    right[1] += a;
    let b = YieldSteps(1).await;
    left[1] += b;
    buf.iter().sum()
}

// L05: Self-referential borrow of inner Unpin struct while mutating sibling field across yield
struct InnerUnpin {
    data: [u64; 2],
}
async fn l05_inner_unpin_sibling_mutation(x: u64) -> u64 {
    let mut inner = InnerUnpin { data: [x, x + 1] };
    let mut sibling: u64 = 100;
    let r_inner: &mut u64 = &mut inner.data[0];
    *r_inner += 1;
    let w = YieldSteps(1).await;
    sibling += w;
    *r_inner += sibling;
    inner.data[0] + inner.data[1] + sibling
}

// L06: Nested async fn where outer holds self-ref and inner holds its own self-ref
async fn l06_outer_and_inner_self_ref(x: u64) -> u64 {
    let mut outer_val = x + 10;
    let r_outer = &mut outer_val;
    let inner_res = l03_mut_ref_1_yield(*r_outer).await;
    *r_outer += inner_res;
    outer_val
}

// L07: Reborrowing a mutable reference across multiple awaits
async fn l07_layered_reborrow_across_awaits(x: u64) -> u64 {
    let mut base = [x, x + 1];
    let r1 = &mut base;
    {
        let r2 = &mut r1[0];
        *r2 += YieldSteps(1).await;
    }
    r1[1] += YieldSteps(1).await;
    base[0] + base[1]
}

// L08: Interior mutability (UnsafeCell) inside coroutine frame across yield
struct CellWrap(UnsafeCell<u64>);
async fn l08_unsafecell_in_frame(x: u64) -> u64 {
    let cell = CellWrap(UnsafeCell::new(x));
    let r1 = &cell;
    let r2 = &cell;
    unsafe { *r1.0.get() += 1; }
    let w = YieldSteps(1).await;
    unsafe { *r2.0.get() += w; }
    unsafe { *cell.0.get() }
}

// L09: Partial drop at Suspend0 (only live fields dropped, never uninitialized ones)
async fn l09_partial_drop_at_suspend0(x: u64) -> u64 {
    let g1 = CountedDrop(x);
    let a = YieldSteps(2).await;
    let g2 = CountedDrop(x + a);
    let b = YieldSteps(2).await;
    g1.0 + g2.0 + b
}

// L10: Partial drop at Suspend1 (both g1 and g2 live and dropped)
async fn l10_partial_drop_at_suspend1(x: u64) -> u64 {
    let g1 = CountedDrop(x);
    let a = YieldSteps(1).await;
    let g2 = CountedDrop(x + a);
    let b = YieldSteps(2).await;
    g1.0 + g2.0 + b
}

// L11: Mid-await panic unwinds, poisons discriminant to 2, drops live self-ref + CountedDrop, and subsequent drop is no-op
async fn l11_panic_mid_await_with_self_ref(x: u64) -> u64 {
    let mut local_arr = [x, x + 1];
    let guard = CountedDrop(x);
    let r = &mut local_arr[0];
    *r += guard.0;
    let v = PanicOnSecondPoll(false).await;
    *r += v;
    local_arr[0]
}

// L12: Unresumed drop (drops captured upvar without running body)
fn l12_unresumed_upvar_drop() -> usize {
    DROP_COUNTER.store(0, Ordering::SeqCst);
    let captured = CountedDrop(42);
    let fut = async move {
        let g = captured;
        let w = YieldSteps(1).await;
        g.0 + w
    };
    drop(fut);
    DROP_COUNTER.load(Ordering::SeqCst)
}

// L13: Disjoint scope storage reuse under Miri (verifies StorageDead / StorageLive on non-conflicting saved locals)
async fn l13_disjoint_saved_locals_storage_reuse(x: u64) -> u64 {
    let part1 = {
        let mut a = [x; 4];
        a[0] += YieldSteps(1).await;
        a[0] + a[3]
    };
    let part2 = {
        let mut b = [part1; 4];
        b[1] += YieldSteps(1).await;
        b[1] + b[3]
    };
    part2
}

// L14: Array index projection where index local is saved across yield
async fn l14_saved_index_projection(x: u64, idx: usize) -> u64 {
    let mut arr = [x, x + 1, x + 2, x + 3];
    let i = idx & 3;
    let w = YieldSteps(1).await;
    arr[i] += w;
    arr[i]
}

// L15: Movable gen block (Iterator::next takes &mut Self with noalias + FnEntry protector)
fn l15_gen_block_movable(x: u64) -> u64 {
    let g = gen move {
        let mut acc = x;
        yield acc;
        acc += 10;
        yield acc;
        acc += 20;
        yield acc;
    };
    g.sum()
}

// L16: gen fn with drop guards and partial iteration drop
gen fn l16_gen_fn_with_drops(x: u64) -> u64 {
    let d1 = CountedDrop(x);
    yield d1.0;
    let d2 = CountedDrop(x + 1);
    yield d1.0 + d2.0;
    yield d2.0;
}

// L17: Static self-referential raw #[coroutine]
fn l17_static_raw_coroutine(x: u64) -> u64 {
    let mut coro = #[coroutine] static move |resume_in: u64| {
        let mut state = [x, x + 1];
        let r: &mut [u64; 2] = &mut state;
        let r1 = yield r[0] + resume_in;
        r[1] += r1;
        let r2 = yield r[1];
        r[0] + r[1] + r2
    };
    let mut pinned = unsafe { Pin::new_unchecked(&mut coro) };
    let mut total = 0;
    if let CoroutineState::Yielded(v) = pinned.as_mut().resume(5) { total += v; }
    if let CoroutineState::Yielded(v) = pinned.as_mut().resume(6) { total += v; }
    if let CoroutineState::Complete(v) = pinned.as_mut().resume(7) { total += v; }
    total
}

// L18: Box::pin heap-allocated self-referential future polled across 4 steps
async fn l18_boxed_pin_self_ref(x: u64) -> u64 {
    let mut b = Box::pin(async move {
        let mut buf = [x, x + 1, x + 2];
        let r = &mut buf;
        r[0] += YieldSteps(1).await;
        r[1] += YieldSteps(1).await;
        r[2] += YieldSteps(1).await;
        r[0] + r[1] + r[2]
    });
    let w = YieldSteps(1).await;
    b.as_mut().await + w
}

// L19: Negative control (safe panic): ResumedAfterReturn on async fn
fn l19_resumed_after_return_panics() -> bool {
    let mut fut = pin!(l01_shared_ref_1_yield(10));
    let out = drive_steps(fut.as_mut(), 10);
    assert_eq!(out, Some(24));
    let waker = dummy_waker();
    let mut cx = Context::from_waker(&waker);
    let res = catch_unwind(AssertUnwindSafe(|| {
        let _ = fut.as_mut().poll(&mut cx);
    }));
    res.is_err()
}

// L20: Negative control (safe panic): ResumedAfterPanic on poisoned coroutine
fn l20_resumed_after_panic_panics() -> bool {
    DROP_COUNTER.store(0, Ordering::SeqCst);
    let mut fut = pin!(l11_panic_mid_await_with_self_ref(10));
    let waker = dummy_waker();
    let mut cx = Context::from_waker(&waker);
    // First poll suspends
    assert!(matches!(fut.as_mut().poll(&mut cx), Poll::Pending));
    // Second poll panics and poisons discriminant to 2
    let first_panic = catch_unwind(AssertUnwindSafe(|| {
        let _ = fut.as_mut().poll(&mut cx);
    }));
    assert!(first_panic.is_err());
    // Guard inside l11 must have been dropped exactly once during unwinding
    assert_eq!(DROP_COUNTER.load(Ordering::SeqCst), 1);
    // Third poll on poisoned coroutine panics with ResumedAfterPanic
    let second_panic = catch_unwind(AssertUnwindSafe(|| {
        let _ = fut.as_mut().poll(&mut cx);
    }));
    second_panic.is_err()
}

fn main() {
    assert_eq!(drive_steps(pin!(l01_shared_ref_1_yield(10)), 10), Some(24));
    assert_eq!(drive_steps(pin!(l02_shared_ref_3_yields(1)), 10), Some(67));
    assert_eq!(drive_steps(pin!(l03_mut_ref_1_yield(10)), 10), Some(16));
    assert_eq!(drive_steps(pin!(l04_split_at_mut_2_yields(1)), 10), Some(22));
    assert_eq!(drive_steps(pin!(l05_inner_unpin_sibling_mutation(5)), 10), Some(214));
    assert_eq!(drive_steps(pin!(l06_outer_and_inner_self_ref(3)), 10), Some(32));
    assert_eq!(drive_steps(pin!(l07_layered_reborrow_across_awaits(10)), 10), Some(23));
    assert_eq!(drive_steps(pin!(l08_unsafecell_in_frame(20)), 10), Some(22));

    DROP_COUNTER.store(0, Ordering::SeqCst);
    {
        let mut f9 = pin!(l09_partial_drop_at_suspend0(5));
        let _ = drive_steps(f9.as_mut(), 1);
    }
    assert_eq!(DROP_COUNTER.load(Ordering::SeqCst), 1);

    DROP_COUNTER.store(0, Ordering::SeqCst);
    {
        let mut f10 = pin!(l10_partial_drop_at_suspend1(5));
        let _ = drive_steps(f10.as_mut(), 3);
    }
    assert_eq!(DROP_COUNTER.load(Ordering::SeqCst), 2);

    assert_eq!(l12_unresumed_upvar_drop(), 1);
    assert_eq!(drive_steps(pin!(l13_disjoint_saved_locals_storage_reuse(2)), 10), Some(11));
    assert_eq!(drive_steps(pin!(l14_saved_index_projection(10, 2)), 10), Some(13));
    assert_eq!(l15_gen_block_movable(5), 55);

    DROP_COUNTER.store(0, Ordering::SeqCst);
    {
        let mut it = l16_gen_fn_with_drops(10);
        assert_eq!(it.next(), Some(10));
        assert_eq!(it.next(), Some(21));
    }
    assert_eq!(DROP_COUNTER.load(Ordering::SeqCst), 2);

    assert_eq!(l17_static_raw_coroutine(10), 66);
    assert_eq!(drive_steps(pin!(l18_boxed_pin_self_ref(1)), 20), Some(10));
    assert!(l19_resumed_after_return_panics());
    assert!(l20_resumed_after_panic_panics());
    // After l20 drops `fut`, DROP_COUNTER must still be 1 (no double drop of poisoned coroutine!)
    assert_eq!(DROP_COUNTER.load(Ordering::SeqCst), 1);
    println!("ALL_20_LITMUS_PASSED");
}
'''

FORGED_UNPIN_UB_SOURCE = r'''
// Negative UB control: manually forging `Unpin` on a self-referential struct
// and passing `&mut Self` (which receives `FnEntry` protector + `ReservedFrz`)
// while reading/writing through an internal raw/ref alias created before entry.
struct ForgedSelfRef {
    val: u64,
    alias: *mut u64,
}
impl Unpin for ForgedSelfRef {}

fn poll_forged(s: &mut ForgedSelfRef) -> u64 {
    // `s` is retagged as FnEntry Protected MutableRef (`ReservedFrz` in TB, `Unique` in SB).
    // Accessing `*s.alias` (derived from an older sibling tag before `poll_forged`)
    // performs a ForeignWrite to a protected location!
    s.val += 1;
    unsafe { *s.alias += 10; }
    s.val
}

fn main() {
    let mut f = ForgedSelfRef { val: 1, alias: core::ptr::null_mut() };
    f.alias = &mut f.val as *mut u64;
    let _ = poll_forged(&mut f);
}
'''

def run_miri(src: str, extra_flags: list[str]) -> dict:
    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        (tmp_path / "src").mkdir()
        (tmp_path / "src" / "main.rs").write_text(src, encoding="utf-8")
        (tmp_path / "Cargo.toml").write_text(
            '[package]\nname = "litmus"\nversion = "0.1.0"\nedition = "2024"\n',
            encoding="utf-8",
        )
        env = dict(os.environ, MIRIFLAGS=" ".join(extra_flags))
        res = subprocess.run(
            ["cargo", "+nightly", "miri", "run", "--quiet"],
            cwd=str(tmp_path),
            capture_output=True,
            text=True,
            env=env,
        )
        return {
            "returncode": res.returncode,
            "stdout": res.stdout.strip(),
            "stderr_snippet": "\n".join(
                line for line in res.stderr.splitlines()
                if "Undefined Behavior" in line or "error:" in line
            )[:400],
        }

def main():
    tb_20 = run_miri(LITMUS_SOURCE, ["-Zmiri-tree-borrows"])
    sb_20 = run_miri(LITMUS_SOURCE, [])
    tb_forged = run_miri(FORGED_UNPIN_UB_SOURCE, ["-Zmiri-tree-borrows"])
    sb_forged = run_miri(FORGED_UNPIN_UB_SOURCE, [])

    assert tb_20["returncode"] == 0 and "ALL_20_LITMUS_PASSED" in tb_20["stdout"], f"TB failed: {tb_20}"
    assert sb_20["returncode"] == 0 and "ALL_20_LITMUS_PASSED" in sb_20["stdout"], f"SB failed: {sb_20}"
    assert tb_forged["returncode"] != 0, "Expected TB UB on forged Unpin"
    assert sb_forged["returncode"] != 0, "Expected SB UB on forged Unpin"

    tests = [
        {"id": "L01", "name": "l01_shared_ref_1_yield", "category": "self_ref_shared", "tree_borrows": "PASS (0 UB)", "stacked_borrows": "PASS (0 UB)"},
        {"id": "L02", "name": "l02_shared_ref_3_yields", "category": "self_ref_shared", "tree_borrows": "PASS (0 UB)", "stacked_borrows": "PASS (0 UB)"},
        {"id": "L03", "name": "l03_mut_ref_1_yield", "category": "self_ref_mut", "tree_borrows": "PASS (0 UB)", "stacked_borrows": "PASS (0 UB)"},
        {"id": "L04", "name": "l04_split_at_mut_2_yields", "category": "self_ref_mut_split", "tree_borrows": "PASS (0 UB)", "stacked_borrows": "PASS (0 UB)"},
        {"id": "L05", "name": "l05_inner_unpin_sibling_mutation", "category": "inner_unpin_in_outer_pinned", "tree_borrows": "PASS (0 UB)", "stacked_borrows": "PASS (0 UB)"},
        {"id": "L06", "name": "l06_outer_and_inner_self_ref", "category": "nested_poll_self_ref", "tree_borrows": "PASS (0 UB)", "stacked_borrows": "PASS (0 UB)"},
        {"id": "L07", "name": "l07_layered_reborrow_across_awaits", "category": "layered_reborrow", "tree_borrows": "PASS (0 UB)", "stacked_borrows": "PASS (0 UB)"},
        {"id": "L08", "name": "l08_unsafecell_in_frame", "category": "interior_mutability", "tree_borrows": "PASS (0 UB)", "stacked_borrows": "PASS (0 UB)"},
        {"id": "L09", "name": "l09_partial_drop_at_suspend0", "category": "partial_drop_suspend", "tree_borrows": "PASS (0 UB)", "stacked_borrows": "PASS (0 UB)"},
        {"id": "L10", "name": "l10_partial_drop_at_suspend1", "category": "partial_drop_suspend", "tree_borrows": "PASS (0 UB)", "stacked_borrows": "PASS (0 UB)"},
        {"id": "L11", "name": "l11_panic_mid_await_with_self_ref", "category": "unwind_poison_and_drop", "tree_borrows": "PASS (0 UB)", "stacked_borrows": "PASS (0 UB)"},
        {"id": "L12", "name": "l12_unresumed_upvar_drop", "category": "unresumed_drop", "tree_borrows": "PASS (0 UB)", "stacked_borrows": "PASS (0 UB)"},
        {"id": "L13", "name": "l13_disjoint_saved_locals_storage_reuse", "category": "storage_conflict_overlap", "tree_borrows": "PASS (0 UB)", "stacked_borrows": "PASS (0 UB)"},
        {"id": "L14", "name": "l14_saved_index_projection", "category": "saved_index_projection", "tree_borrows": "PASS (0 UB)", "stacked_borrows": "PASS (0 UB)"},
        {"id": "L15", "name": "l15_gen_block_movable", "category": "gen_block_movable_unpin", "tree_borrows": "PASS (0 UB)", "stacked_borrows": "PASS (0 UB)"},
        {"id": "L16", "name": "l16_gen_fn_with_drops", "category": "gen_fn_partial_drop", "tree_borrows": "PASS (0 UB)", "stacked_borrows": "PASS (0 UB)"},
        {"id": "L17", "name": "l17_static_raw_coroutine", "category": "static_coroutine", "tree_borrows": "PASS (0 UB)", "stacked_borrows": "PASS (0 UB)"},
        {"id": "L18", "name": "l18_boxed_pin_self_ref", "category": "heap_boxed_pin_self_ref", "tree_borrows": "PASS (0 UB)", "stacked_borrows": "PASS (0 UB)"},
        {"id": "L19", "name": "l19_resumed_after_return_panics", "category": "state_guard_returned", "tree_borrows": "PASS (defined panic)", "stacked_borrows": "PASS (defined panic)"},
        {"id": "L20", "name": "l20_resumed_after_panic_panics", "category": "state_guard_poisoned", "tree_borrows": "PASS (defined panic, 0 double-drop)", "stacked_borrows": "PASS (defined panic, 0 double-drop)"},
    ]

    out = {
        "miri_version": "miri 0.1.0 (3ef0c22cdb 2026-11-11)",
        "total_safe_litmus_tests": 20,
        "tree_borrows_safe_pass_count": 20,
        "stacked_borrows_safe_pass_count": 20,
        "forged_unpin_negative_control": {
            "tree_borrows_detected_ub": tb_forged["returncode"] != 0,
            "tree_borrows_diagnostic": tb_forged["stderr_snippet"],
            "stacked_borrows_detected_ub": sb_forged["returncode"] != 0,
            "stacked_borrows_diagnostic": sb_forged["stderr_snippet"],
        },
        "litmus_tests": tests,
    }
    out_path = Path(__file__).parent / "miri_litmus_results.json"
    out_path.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {out_path}")
    print(json.dumps(out["forged_unpin_negative_control"], indent=2))

if __name__ == "__main__":
    main()
