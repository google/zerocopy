#!/usr/bin/env python3
"""Live rustc verification probe for RFC 2229 disjoint closure captures,
ClosureKind inference, wildcard capture avoidance, deref truncation,
and async/coroutine StateTransform layout, storage-conflict overlap packing,
panic-poisoning, and !Unpin self-referential pinning.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import tempfile
from pathlib import Path


def sanitize(text: str, td: str) -> str:
    return text.replace(td, "<tmp>")


def run_rustc_case(
    name: str,
    code: str,
    edition: str = "2024",
    extra_args: list[str] | None = None,
    expect_compile_ok: bool = True,
    execute: bool = False,
    dump_mir_pass: str | None = None,
    mir_filter_prefixes: tuple[str, ...] = (),
) -> dict:
    extra_args = list(extra_args or [])
    with tempfile.TemporaryDirectory() as td:
        src = os.path.join(td, "probe.rs")
        exe = os.path.join(td, "probe")
        Path(src).write_text(code, encoding="utf-8")

        args = ["rustc", f"--edition={edition}", *extra_args]
        mir_dir = os.path.join(td, "mir_dumps")
        if dump_mir_pass is not None:
            os.makedirs(mir_dir, exist_ok=True)
            args.extend([f"-Zdump-mir={dump_mir_pass}", f"-Zdump-mir-dir={mir_dir}"])
        args.extend([src, "-o", exe])

        comp = subprocess.run(args, capture_output=True, text=True, timeout=120)
        result: dict = {
            "case": name,
            "edition": edition,
            "extra_args": extra_args,
            "compile_returncode": comp.returncode,
            "compile_stdout": sanitize(comp.stdout, td),
            "compile_stderr": sanitize(comp.stderr, td),
        }

        if "-Zprint-type-sizes" in extra_args:
            kept: list[str] = []
            keep_block = False
            type_size_lines = (result["compile_stdout"] + "\n" + result["compile_stderr"]).splitlines()
            for line in type_size_lines:
                if line.startswith("print-type-size type: "):
                    keep_block = any(
                        tok in line
                        for tok in (
                            "seq_non_overlapping",
                            "live_across_overlapping",
                            "self_ref_across_await",
                            "closure",
                            "BigRefTarget",
                            "SplitMove",
                            "Pair",
                        )
                    )
                if keep_block and line.startswith("print-type-size"):
                    kept.append(line)
            result["filtered_type_sizes"] = "\n".join(kept)

        if dump_mir_pass is not None and os.path.isdir(mir_dir):
            dumps: dict[str, str] = {}
            for fn in sorted(os.listdir(mir_dir)):
                if not mir_filter_prefixes or any(fn.startswith(p) for p in mir_filter_prefixes):
                    raw = Path(os.path.join(mir_dir, fn)).read_text(encoding="utf-8")
                    dumps[fn] = sanitize(raw, td)
            result["mir_dumps"] = dumps

        if expect_compile_ok and comp.returncode != 0:
            raise AssertionError(f"{name}: expected compile ok, got rc={comp.returncode}\n{result['compile_stderr']}")
        if not expect_compile_ok and comp.returncode == 0:
            raise AssertionError(f"{name}: expected compile error, got rc=0")

        if execute and comp.returncode == 0:
            run = subprocess.run([exe], capture_output=True, text=True, timeout=120)
            result["run_returncode"] = run.returncode
            result["run_stdout"] = sanitize(run.stdout, td).strip()
            result["run_stderr"] = sanitize(run.stderr, td).strip()
            if run.returncode != 0:
                raise AssertionError(f"{name}: runtime failed rc={run.returncode}\n{result['run_stderr']}")

        return result


def main() -> None:
    ver = subprocess.run(["rustc", "--version", "--verbose"], capture_output=True, text=True, check=True)
    rustc_version = ver.stdout.strip()

    # A1: Edition 2024 RFC 2229 disjoint field capture, ClosureKind inference,
    # UniqueImmutable, wildcard non-capture, move copy-field preservation,
    # and shared-ref deref truncation.
    a1_code = r'''
struct Pair {
    a: i32,
    b: String,
}

struct SplitMove {
    copy_n: u64,
    owned: String,
}

struct BigRefTarget {
    a: u64,
    buf: [u8; 64],
}

fn require_fn<F: Fn() -> i32>(f: &F) -> i32 { f() }
fn require_fn_mut<F: FnMut() -> i32>(f: &mut F) -> i32 { f() }
fn require_fn_once<F: FnOnce() -> usize>(f: F) -> usize { f() }

fn main() {
    // 1. Disjoint field borrows across closure and parent scope
    let mut p = Pair { a: 10, b: String::from("hi") };
    let read_a = || p.a;
    p.b.push('!');
    let va = read_a();

    // 2. ClosureKind lattice: Fn, FnMut, FnOnce + UniqueImmutable
    let c_val = 99i32;
    let cap_c = || c_val;
    let vc = require_fn(&cap_c);

    let mut mut_a = || { p.a += 5; p.a };
    let vmut = require_fn_mut(&mut mut_a);

    let mut z = 3i32;
    let r_mut: &mut i32 = &mut z;
    let mut uniq_c = || {
        let _p: *const &mut i32 = &r_mut;
        *r_mut += 5;
        *r_mut
    };
    let vuniq = require_fn_mut(&mut uniq_c);

    let s = String::from("consume");
    let once_c = || s.into_bytes().len();
    let vonce = require_fn_once(once_c);

    // 3. Wildcard non-capture vs reference capture vs field wildcard
    let p3 = Pair { a: 7, b: String::from("stay") };
    let wild_none = || { let _ = p3; 6i32 };
    let wild_field = || { let _ = p3.a; 7i32 };
    let wild_ref = || { let _ = &p3; 8i32 };
    let vw = wild_none() + wild_field() + wild_ref();

    // 4. `move` closure moving only copy_n while leaving owned intact
    let sm = SplitMove { copy_n: 77, owned: String::from("intact") };
    let move_copy_only = move || sm.copy_n + 1;
    let sz_move_copy = size_of_val(&move_copy_only);
    let vmove_copy = move_copy_only();
    let sm_owned_len = sm.owned.len();

    // 5. Shared-ref deref truncation (`truncate_capture_for_optimization`)
    let target = BigRefTarget { a: 123, buf: [9u8; 64] };
    let r_target: &BigRefTarget = &target;
    let trunc_shared = || r_target.a + 1;
    let sz_trunc_shared = size_of_val(&trunc_shared);
    let vtrunc = trunc_shared();

    println!(
        "A={} B={} STAY_LEN={} SZ_CAP_C={} VC={} SZ_MUT_A={} VMUT={} SZ_UNIQ={} VUNIQ={} VONCE={} SZ_WILD=({},{},{}) VW={} P3_LEN={} SZ_MOVE_COPY={} VMOVE_COPY={} SM_OWNED_LEN={} SZ_TRUNC_SHARED={} VTRUNC={}",
        va,
        p.b,
        p3.b.len(),
        size_of_val(&cap_c),
        vc,
        size_of_val(&mut_a),
        vmut,
        size_of_val(&uniq_c),
        vuniq,
        vonce,
        size_of_val(&wild_ref),
        size_of_val(&wild_none),
        size_of_val(&wild_field),
        vw,
        p3.b.len(),
        sz_move_copy,
        vmove_copy,
        sm_owned_len,
        sz_trunc_shared,
        vtrunc,
    );
}
'''
    a1 = run_rustc_case(
        "edition_2024_disjoint_and_traits_ok",
        a1_code,
        edition="2024",
        extra_args=["-Zprint-type-sizes"],
        expect_compile_ok=True,
        execute=True,
        dump_mir_pass="built",
        mir_filter_prefixes=("probe.main-{closure#",),
    )

    # A2: Edition 2018 rejects disjoint field borrow (E0502)
    a2_code = r'''
struct Pair {
    a: i32,
    b: String,
}

fn main() {
    let mut p = Pair { a: 10, b: String::from("hi") };
    let read_a = || p.a;
    p.b.push('!');
    let _ = read_a();
}
'''
    a2 = run_rustc_case(
        "edition_2018_disjoint_borrow_rejected_e0502",
        a2_code,
        edition="2018",
        expect_compile_ok=False,
    )
    assert "E0502" in a2["compile_stderr"], a2["compile_stderr"]

    # A3: Edition 2018 `move || sm.copy_n` moves whole struct (E0382)
    a3_code = r'''
struct SplitMove {
    copy_n: u64,
    owned: String,
}

fn main() {
    let sm = SplitMove { copy_n: 77, owned: String::from("intact") };
    let c = move || sm.copy_n + 1;
    let _ = sm.owned.len();
    let _ = c();
}
'''
    a3 = run_rustc_case(
        "edition_2018_move_copy_field_moves_whole_e0382",
        a3_code,
        edition="2018",
        expect_compile_ok=False,
    )
    assert "E0382" in a3["compile_stderr"], a3["compile_stderr"]

    # A4: `let _x = s;` moves vs wildcard `let _ = s;` does not
    a4_code = r'''
fn main() {
    let s = String::from("hello");
    let c1 = || { let _x = s; };
    c1();
    let _ = s.len();
}
'''
    a4 = run_rustc_case(
        "binding_move_let_x_rejected_e0382",
        a4_code,
        edition="2024",
        expect_compile_ok=False,
    )
    assert "E0382" in a4["compile_stderr"], a4["compile_stderr"]

    # A5: UniqueImmutable capture cannot implement Fn (E0525)
    a5_code = r'''
fn require_fn<F: Fn()>(_f: &F) {}

fn main() {
    let mut z = 3i32;
    let r: &mut i32 = &mut z;
    let c = || { *r += 5; };
    require_fn(&c);
}
'''
    a5 = run_rustc_case(
        "unique_immutable_not_fn_rejected_e0525",
        a5_code,
        edition="2024",
        expect_compile_ok=False,
    )
    assert "E0525" in a5["compile_stderr"], a5["compile_stderr"]

    # B1: Async StateTransform MIR dumps, -Zprint-type-sizes, and execution
    b1_code = r'''
use core::future::Future;
use core::pin::{Pin, pin};
use core::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};

struct YieldOnce(bool);
impl Future for YieldOnce {
    type Output = ();
    fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<()> {
        if self.0 { Poll::Ready(()) } else { self.0 = true; Poll::Pending }
    }
}

#[inline(never)]
fn touch(x: &[u8; 64]) -> u8 { x[0].wrapping_add(x[63]) }

async fn seq_non_overlapping() -> u8 {
    let acc1 = {
        let mut a = [1u8; 64];
        a[63] = 2;
        YieldOnce(false).await;
        touch(&a)
    };
    let acc2 = {
        let mut b = [3u8; 64];
        b[63] = 4;
        YieldOnce(false).await;
        touch(&b)
    };
    acc1.wrapping_add(acc2)
}

async fn live_across_overlapping() -> u8 {
    let mut a = [1u8; 64];
    a[63] = 2;
    let mut b = [3u8; 64];
    b[63] = 4;
    YieldOnce(false).await;
    let v1 = touch(&a);
    YieldOnce(false).await;
    v1.wrapping_add(touch(&b))
}

async fn self_ref_across_await() -> u8 {
    let x = [42u8; 64];
    let rx = &x[0];
    YieldOnce(false).await;
    *rx
}

fn noop_waker() -> Waker {
    unsafe fn clone(_: *const ()) -> RawWaker { RawWaker::new(core::ptr::null(), &VTABLE) }
    unsafe fn wake(_: *const ()) {}
    unsafe fn wake_by_ref(_: *const ()) {}
    unsafe fn drop(_: *const ()) {}
    static VTABLE: RawWakerVTable = RawWakerVTable::new(clone, wake, wake_by_ref, drop);
    unsafe { Waker::from_raw(RawWaker::new(core::ptr::null(), &VTABLE)) }
}

fn poll_to_completion<F: Future>(mut fut: Pin<&mut F>) -> F::Output {
    let w = noop_waker();
    let mut cx = Context::from_waker(&w);
    loop {
        if let Poll::Ready(v) = fut.as_mut().poll(&mut cx) {
            return v;
        }
    }
}

fn main() {
    let f_seq = pin!(seq_non_overlapping());
    let f_ovl = pin!(live_across_overlapping());
    let f_sr = pin!(self_ref_across_await());
    println!(
        "SEQ_SIZE={} OVL_SIZE={} SELF_REF_SIZE={} SEQ_ALIGN={} SR_ALIGN={}",
        size_of_val(&*f_seq),
        size_of_val(&*f_ovl),
        size_of_val(&*f_sr),
        align_of_val(&*f_seq),
        align_of_val(&*f_sr),
    );
    let r1 = poll_to_completion(f_seq);
    let r2 = poll_to_completion(f_ovl);
    let r3 = poll_to_completion(f_sr);
    println!("RES=({r1},{r2},{r3})");
}
'''
    b1 = run_rustc_case(
        "async_state_machine_sizes_mir_and_execution",
        b1_code,
        edition="2024",
        extra_args=["-Zprint-type-sizes"],
        expect_compile_ok=True,
        execute=True,
        dump_mir_pass="StateTransform",
        mir_filter_prefixes=(
            "probe.seq_non_overlapping",
            "probe.live_across_overlapping",
            "probe.self_ref_across_await",
        ),
    )

    # B2: Self-referential async block is !Unpin (E0277)
    b2_code = r'''
use core::future::Future;

struct YieldOnce(bool);
impl Future for YieldOnce {
    type Output = ();
    fn poll(mut self: core::pin::Pin<&mut Self>, _cx: &mut core::task::Context<'_>) -> core::task::Poll<()> {
        if self.0 { core::task::Poll::Ready(()) } else { self.0 = true; core::task::Poll::Pending }
    }
}

fn require_unpin<T: Unpin>(_t: &T) {}

fn main() {
    let fut_self_ref = async {
        let x = [7u8; 16];
        let rx = &x[0];
        YieldOnce(false).await;
        *rx
    };
    require_unpin(&fut_self_ref);
}
'''
    b2 = run_rustc_case(
        "async_self_ref_not_unpin_rejected_e0277",
        b2_code,
        edition="2024",
        expect_compile_ok=False,
    )
    assert "E0277" in b2["compile_stderr"], b2["compile_stderr"]

    # B3: Movable coroutine without self-ref across yield IS Unpin
    b3_code = r'''
#![feature(coroutines, coroutine_trait, stmt_expr_attributes)]
use core::ops::Coroutine;
use core::pin::Pin;

fn require_unpin<T: Unpin>(_t: &T) {}

fn main() {
    let mut c = #[coroutine] |x: i32| {
        let a = x + 1;
        let b = yield a;
        a + b
    };
    require_unpin(&c);
    let r1 = Pin::new(&mut c).resume(10);
    let r2 = Pin::new(&mut c).resume(2);
    println!("MOVABLE_UNPIN=({r1:?},{r2:?})");
}
'''
    b3 = run_rustc_case(
        "movable_coroutine_without_self_ref_is_unpin_ok",
        b3_code,
        edition="2024",
        expect_compile_ok=True,
        execute=True,
    )

    # B4: Panic-poisoning (POISONED=2) and RETURNED=1 re-poll traps + drop count
    b4_code = r'''
use core::future::Future;
use core::pin::Pin;
use core::sync::atomic::{AtomicUsize, Ordering};
use core::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};
use std::panic::{AssertUnwindSafe, catch_unwind};

struct YieldOnce(bool);
impl Future for YieldOnce {
    type Output = ();
    fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<()> {
        if self.0 { Poll::Ready(()) } else { self.0 = true; Poll::Pending }
    }
}

struct DropGuard<'a>(&'a AtomicUsize);
impl Drop for DropGuard<'_> {
    fn drop(&mut self) {
        self.0.fetch_add(1, Ordering::SeqCst);
    }
}

fn noop_waker() -> Waker {
    unsafe fn clone(_: *const ()) -> RawWaker { RawWaker::new(core::ptr::null(), &VTABLE) }
    unsafe fn wake(_: *const ()) {}
    unsafe fn wake_by_ref(_: *const ()) {}
    unsafe fn drop(_: *const ()) {}
    static VTABLE: RawWakerVTable = RawWakerVTable::new(clone, wake, wake_by_ref, drop);
    unsafe { Waker::from_raw(RawWaker::new(core::ptr::null(), &VTABLE)) }
}

fn panic_payload_str(err: Box<dyn core::any::Any + Send>) -> &'static str {
    if let Some(s) = err.downcast_ref::<&'static str>() {
        s
    } else if let Some(s) = err.downcast_ref::<String>() {
        Box::leak(s.clone().into_boxed_str())
    } else {
        "<non-str>"
    }
}

fn main() {
    let drops = AtomicUsize::new(0);
    let w = noop_waker();
    let mut cx = Context::from_waker(&w);

    let mut fut_panic = Box::pin(async {
        let _g = DropGuard(&drops);
        YieldOnce(false).await;
        panic!("boom_mid_async");
    });

    let p1 = fut_panic.as_mut().poll(&mut cx);
    let d_at_suspend = drops.load(Ordering::SeqCst);

    let r_panic = catch_unwind(AssertUnwindSafe(|| fut_panic.as_mut().poll(&mut cx)));
    let msg1 = panic_payload_str(r_panic.unwrap_err());
    let d_after_unwind = drops.load(Ordering::SeqCst);

    let r_repoll_poison = catch_unwind(AssertUnwindSafe(|| fut_panic.as_mut().poll(&mut cx)));
    let msg_poison = panic_payload_str(r_repoll_poison.unwrap_err());

    drop(fut_panic);
    let d_after_drop = drops.load(Ordering::SeqCst);

    let mut fut_done = Box::pin(async { 42u8 });
    let p_done = fut_done.as_mut().poll(&mut cx);
    let r_repoll_done = catch_unwind(AssertUnwindSafe(|| fut_done.as_mut().poll(&mut cx)));
    let msg_done = panic_payload_str(r_repoll_done.unwrap_err());

    println!(
        "FIRST_POLL={p1:?} DROPS=({d_at_suspend},{d_after_unwind},{d_after_drop}) PANIC1={msg1:?} REPOLL_POISON={msg_poison:?} DONE_POLL={p_done:?} REPOLL_DONE={msg_done:?}"
    );
}
'''
    b4 = run_rustc_case(
        "panic_poisoning_and_repoll_traps",
        b4_code,
        edition="2024",
        expect_compile_ok=True,
        execute=True,
    )

    out = {
        "rustc_version": rustc_version,
        "experiments": {
            "a_rfc2229_disjoint_capture_and_closure_kinds": {
                "edition_2024_disjoint_and_traits_ok": a1,
                "edition_2018_disjoint_borrow_rejected_e0502": a2,
                "edition_2018_move_copy_field_moves_whole_e0382": a3,
                "binding_move_let_x_rejected_e0382": a4,
                "unique_immutable_not_fn_rejected_e0525": a5,
            },
            "b_async_coroutine_state_layout_and_unpin": {
                "async_state_machine_sizes_mir_and_execution": b1,
                "async_self_ref_not_unpin_rejected_e0277": b2,
                "movable_coroutine_without_self_ref_is_unpin_ok": b3,
                "panic_poisoning_and_repoll_traps": b4,
            },
        },
    }

    out_path = Path(__file__).with_name("probe_results.json")
    out_path.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print("WROTE", out_path)
    print("A1:", a1["run_stdout"])
    print("B1:", b1["run_stdout"])
    print("B3:", b3["run_stdout"])
    print("B4:", b4["run_stdout"])


if __name__ == "__main__":
    main()
