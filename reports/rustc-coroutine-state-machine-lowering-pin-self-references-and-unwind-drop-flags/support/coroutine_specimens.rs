#![feature(coroutines, coroutine_trait, stmt_expr_attributes)]

use core::future::Future;
use core::ops::{Coroutine, CoroutineState};
use core::pin::Pin;
use core::sync::atomic::{AtomicUsize, Ordering};
use core::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::time::Instant;

// Global atomic counters used purely by the runtime verification harness (`main`)
// to record exact destructor invocations without allocating or mutating shared
// test vectors across unwind boundaries.
static UPVAR_DROPS: AtomicUsize = AtomicUsize::new(0);
static SCOPE_DROPS: AtomicUsize = AtomicUsize::new(0);
static COND_DROPS: AtomicUsize = AtomicUsize::new(0);
static INNER_DROPS: AtomicUsize = AtomicUsize::new(0);

fn reset_drop_counters() {
    UPVAR_DROPS.store(0, Ordering::SeqCst);
    SCOPE_DROPS.store(0, Ordering::SeqCst);
    COND_DROPS.store(0, Ordering::SeqCst);
    INNER_DROPS.store(0, Ordering::SeqCst);
}

fn snapshot_drop_counters() -> (usize, usize, usize, usize) {
    (
        UPVAR_DROPS.load(Ordering::SeqCst),
        SCOPE_DROPS.load(Ordering::SeqCst),
        COND_DROPS.load(Ordering::SeqCst),
        INNER_DROPS.load(Ordering::SeqCst),
    )
}

#[repr(u8)]
#[derive(Clone, Copy)]
pub enum GuardKind {
    Upvar = 1,
    Scope = 2,
    Cond = 3,
    Inner = 4,
}

pub struct DropGuard {
    pub kind: GuardKind,
    pub tag: u64,
}

impl Drop for DropGuard {
    #[inline(never)]
    fn drop(&mut self) {
        core::hint::black_box(self.tag);
        match self.kind {
            GuardKind::Upvar => {
                UPVAR_DROPS.fetch_add(1, Ordering::SeqCst);
            }
            GuardKind::Scope => {
                SCOPE_DROPS.fetch_add(1, Ordering::SeqCst);
            }
            GuardKind::Cond => {
                COND_DROPS.fetch_add(1, Ordering::SeqCst);
            }
            GuardKind::Inner => {
                INNER_DROPS.fetch_add(1, Ordering::SeqCst);
            }
        }
    }
}

/// Baseline `Unpin` two-step future written by hand.
pub struct ManualUnpinTwoStepFuture {
    pub state: u8,
    pub acc: u64,
}

impl Future for ManualUnpinTwoStepFuture {
    type Output = u64;

    #[inline(never)]
    fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<u64> {
        match self.state {
            0 => {
                self.acc = self.acc.wrapping_add(10);
                self.state = 1;
                Poll::Pending
            }
            1 => {
                self.acc = self.acc.wrapping_add(20);
                self.state = 2;
                Poll::Pending
            }
            _ => Poll::Ready(self.acc),
        }
    }
}

/// Helper two-step yield sub-future used inside `async fn` specimens.
pub struct StepFut {
    pub yielded: bool,
    pub val: u64,
    pub should_panic: bool,
}

impl Future for StepFut {
    type Output = u64;

    #[inline(never)]
    fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<u64> {
        if self.should_panic {
            panic!("intentional step future panic");
        }
        if !self.yielded {
            self.yielded = true;
            Poll::Pending
        } else {
            Poll::Ready(self.val)
        }
    }
}

/// Specimen 2: `Movability::Movable` (`Unpin`) coroutine with two disjoint `[u64; 4]`
/// arrays live across `yield #0` vs `yield #1`, allowing variant field overlap.
#[inline(never)]
pub fn make_movable_two_yield_coro(
    seed: u64,
) -> impl Coroutine<(), Yield = u64, Return = u64> + Unpin {
    #[coroutine]
    move |()| {
        let out0 = {
            let buf_a: [u64; 4] = [seed, seed + 1, seed + 2, seed + 3];
            yield buf_a[0];
            buf_a[1].wrapping_add(buf_a[3])
        };
        let buf_b: [u64; 4] = [out0, out0 + 10, out0 + 20, out0 + 30];
        yield buf_b[1];
        buf_b[2].wrapping_add(buf_b[3])
    }
}

/// Specimen 3: `async fn` with zero self-borrows across `.await` points (`!Unpin`
/// via `Movability::Static`), holding disjoint `[u64; 4]` buffers across two `.await`s.
pub async fn async_non_self_ref_two_await(x: u64) -> u64 {
    let first = {
        let buf_a: [u64; 4] = [x, x + 1, x + 2, x + 3];
        let v0 = StepFut {
            yielded: false,
            val: buf_a[0] + 5,
            should_panic: false,
        }
        .await;
        buf_a[1].wrapping_add(buf_a[2]).wrapping_add(v0)
    };
    let buf_b: [u64; 4] = [first, first + 4, first + 8, first + 12];
    let v1 = StepFut {
        yielded: false,
        val: buf_b[0] + 7,
        should_panic: false,
    }
    .await;
    buf_b[2].wrapping_add(buf_b[3]).wrapping_add(v1)
}

/// Specimen 4: `async fn` holding a shared self-reference `r: &u64` to local
/// `pinned_local` across two `.await` points (`!Unpin`, self-referential).
pub async fn async_self_ref_two_await(x: u64) -> u64 {
    let pinned_local: u64 = x.wrapping_add(10);
    let r: &u64 = &pinned_local;
    let y0 = StepFut {
        yielded: false,
        val: *r + 1,
        should_panic: false,
    }
    .await;
    let mid = (*r).wrapping_add(y0);
    let y1 = StepFut {
        yielded: false,
        val: mid + 2,
        should_panic: false,
    }
    .await;
    (*r).wrapping_add(mid).wrapping_add(y1)
}

#[inline(never)]
async fn inner_guarded_step(base: u64, panic_now: bool) -> u64 {
    let g_inner = DropGuard {
        kind: GuardKind::Inner,
        tag: base + 100,
    };
    let v = StepFut {
        yielded: false,
        val: base + 3,
        should_panic: panic_now,
    }
    .await;
    core::hint::black_box(&g_inner.tag);
    v.wrapping_add(g_inner.tag)
}

/// Specimen 5: Nested `.await` with an upvar `DropGuard`, a persistent scope
/// `DropGuard`, and a conditionally-dropped `DropGuard` synthesizing a saved
/// MIR `bool` drop flag across suspension point #2, plus a panic-unwind path.
pub async fn async_nested_drop_and_unwind(
    upvar_guard: DropGuard,
    seed: u64,
    early_drop: bool,
    trigger_panic: bool,
) -> u64 {
    let g_scope = DropGuard {
        kind: GuardKind::Scope,
        tag: seed + 1,
    };
    let g_cond = DropGuard {
        kind: GuardKind::Cond,
        tag: seed + 2,
    };

    let a = StepFut {
        yielded: false,
        val: seed + 10,
        should_panic: false,
    }
    .await;

    if early_drop {
        core::mem::drop(g_cond);
    }

    let b = inner_guarded_step(a + g_scope.tag + upvar_guard.tag, trigger_panic).await;
    b.wrapping_add(seed)
}

// Explicit non-inlined wrapper drivers so LLVM IR retains inspectable concrete
// definitions for `Pin<&mut Self>` / `&mut Self` at `-O2` and `-O3`.
#[inline(never)]
pub fn drive_manual_unpin(f: Pin<&mut ManualUnpinTwoStepFuture>, cx: &mut Context<'_>) -> Poll<u64> {
    f.poll(cx)
}

#[inline(never)]
pub fn drive_generic_future<F: Future<Output = u64>>(
    f: Pin<&mut F>,
    cx: &mut Context<'_>,
) -> Poll<u64> {
    f.poll(cx)
}

#[inline(never)]
pub fn drive_generic_coro<G: Coroutine<(), Yield = u64, Return = u64>>(
    g: Pin<&mut G>,
) -> CoroutineState<u64, u64> {
    g.resume(())
}

#[inline(never)]
pub fn drop_generic_future<F: Future<Output = u64>>(f: F) {
    core::hint::black_box(&f);
    core::mem::drop(f);
}

#[inline(never)]
pub fn retain_all_lowering_targets(cx: &mut Context<'_>) -> u64 {
    let mut m = ManualUnpinTwoStepFuture { state: 0, acc: 5 };
    let r0 = match drive_manual_unpin(Pin::new(&mut m), cx) {
        Poll::Pending => 1,
        Poll::Ready(v) => v,
    };

    let mut c_mov = make_movable_two_yield_coro(7);
    let r1 = match drive_generic_coro(Pin::new(&mut c_mov)) {
        CoroutineState::Yielded(v) => v,
        CoroutineState::Complete(v) => v,
    };

    let mut f_no_ref = core::pin::pin!(async_non_self_ref_two_await(9));
    let r2 = match drive_generic_future(f_no_ref.as_mut(), cx) {
        Poll::Pending => 2,
        Poll::Ready(v) => v,
    };

    let mut f_self = core::pin::pin!(async_self_ref_two_await(11));
    let r3 = match drive_generic_future(f_self.as_mut(), cx) {
        Poll::Pending => 3,
        Poll::Ready(v) => v,
    };

    let f_drop = async_nested_drop_and_unwind(
        DropGuard {
            kind: GuardKind::Upvar,
            tag: 13,
        },
        17,
        true,
        false,
    );
    let mut f_drop_pinned = core::pin::pin!(f_drop);
    let r4 = match drive_generic_future(f_drop_pinned.as_mut(), cx) {
        Poll::Pending => 4,
        Poll::Ready(v) => v,
    };

    let f_drop_only = async_nested_drop_and_unwind(
        DropGuard {
            kind: GuardKind::Upvar,
            tag: 19,
        },
        23,
        false,
        false,
    );
    drop_generic_future(f_drop_only);

    r0.wrapping_add(r1)
        .wrapping_add(r2)
        .wrapping_add(r3)
        .wrapping_add(r4)
}

fn noop_waker() -> Waker {
    unsafe fn clone(_: *const ()) -> RawWaker {
        RawWaker::new(core::ptr::null(), &VTABLE)
    }
    unsafe fn wake(_: *const ()) {}
    unsafe fn wake_by_ref(_: *const ()) {}
    unsafe fn drop_waker(_: *const ()) {}
    static VTABLE: RawWakerVTable = RawWakerVTable::new(clone, wake, wake_by_ref, drop_waker);
    unsafe { Waker::from_raw(RawWaker::new(core::ptr::null(), &VTABLE)) }
}

fn panic_message(err: &(dyn core::any::Any + Send)) -> String {
    if let Some(s) = err.downcast_ref::<&'static str>() {
        (*s).to_owned()
    } else if let Some(s) = err.downcast_ref::<String>() {
        s.clone()
    } else {
        format!("<type_id={:?}>", (*err).type_id())
    }
}

fn capture_panic_via_hook<F: FnOnce()>(f: F) -> String {
    use std::cell::RefCell;
    thread_local! {
        static LAST_PANIC_MSG: RefCell<String> = const { RefCell::new(String::new()) };
    }
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|info| {
        let msg = if let Some(s) = info.payload().downcast_ref::<&str>() {
            (*s).to_owned()
        } else if let Some(s) = info.payload().downcast_ref::<String>() {
            s.clone()
        } else {
            format!("{info}")
        };
        LAST_PANIC_MSG.with(|c| *c.borrow_mut() = msg);
    }));
    let res = catch_unwind(AssertUnwindSafe(f));
    std::panic::set_hook(prev);
    assert!(res.is_err(), "expected panic inside capture_panic_via_hook");
    let captured = LAST_PANIC_MSG.with(|c| c.borrow().clone());
    if captured.is_empty() {
        panic_message(&res.unwrap_err())
    } else {
        captured
    }
}

fn main() {
    let waker = noop_waker();
    let mut cx = Context::from_waker(&waker);

    // 1. Measure concrete sizes and alignments.
    let manual = ManualUnpinTwoStepFuture { state: 0, acc: 5 };
    let mov_coro = make_movable_two_yield_coro(7);
    let fut_non_self = async_non_self_ref_two_await(9);
    let fut_self = async_self_ref_two_await(11);
    let fut_nested = async_nested_drop_and_unwind(
        DropGuard {
            kind: GuardKind::Upvar,
            tag: 13,
        },
        17,
        false,
        false,
    );

    let sz_manual = core::mem::size_of_val(&manual);
    let al_manual = core::mem::align_of_val(&manual);
    let sz_mov = core::mem::size_of_val(&mov_coro);
    let al_mov = core::mem::align_of_val(&mov_coro);
    let sz_non_self = core::mem::size_of_val(&fut_non_self);
    let al_non_self = core::mem::align_of_val(&fut_non_self);
    let sz_self = core::mem::size_of_val(&fut_self);
    let al_self = core::mem::align_of_val(&fut_self);
    let sz_nested = core::mem::size_of_val(&fut_nested);
    let al_nested = core::mem::align_of_val(&fut_nested);

    core::mem::drop(fut_nested);

    // 2. Lifecycle Scenario A: Unresumed drop (state == 0).
    reset_drop_counters();
    {
        let f_unresumed = async_nested_drop_and_unwind(
            DropGuard {
                kind: GuardKind::Upvar,
                tag: 10,
            },
            20,
            false,
            false,
        );
        core::mem::drop(f_unresumed);
    }
    let drops_unresumed = snapshot_drop_counters();
    assert_eq!(drops_unresumed, (1, 0, 0, 0));

    // 3. Lifecycle Scenario B: Normal completion (early_drop = true & false) + re-poll panic.
    let mut repoll_after_return_msg = String::new();
    for early in [false, true] {
        reset_drop_counters();
        let mut f = Box::pin(async_nested_drop_and_unwind(
            DropGuard {
                kind: GuardKind::Upvar,
                tag: 10,
            },
            20,
            early,
            false,
        ));
        assert!(matches!(f.as_mut().poll(&mut cx), Poll::Pending));
        assert!(matches!(f.as_mut().poll(&mut cx), Poll::Pending));
        let ready = match f.as_mut().poll(&mut cx) {
            Poll::Ready(v) => v,
            Poll::Pending => panic!("expected Ready on 3rd poll"),
        };
        assert!(ready > 0);
        let drops_after_ready = snapshot_drop_counters();
        assert_eq!(drops_after_ready, (1, 1, 1, 1));

        let msg = capture_panic_via_hook(|| {
            let _ = f.as_mut().poll(&mut cx);
        });
        if repoll_after_return_msg.is_empty() {
            repoll_after_return_msg = msg;
        }
        core::mem::drop(f);
        assert_eq!(snapshot_drop_counters(), (1, 1, 1, 1));
    }

    // 4. Lifecycle Scenario C: Cancellation drop while suspended at Suspend0 (state 3) and Suspend1 (state 4).
    reset_drop_counters();
    {
        let mut f_s0 = Box::pin(async_nested_drop_and_unwind(
            DropGuard {
                kind: GuardKind::Upvar,
                tag: 10,
            },
            20,
            false,
            false,
        ));
        assert!(matches!(f_s0.as_mut().poll(&mut cx), Poll::Pending));
    }
    let drops_cancel_s0 = snapshot_drop_counters();
    assert_eq!(drops_cancel_s0, (1, 1, 1, 0));

    reset_drop_counters();
    {
        let mut f_s1_early = Box::pin(async_nested_drop_and_unwind(
            DropGuard {
                kind: GuardKind::Upvar,
                tag: 10,
            },
            20,
            true,
            false,
        ));
        assert!(matches!(f_s1_early.as_mut().poll(&mut cx), Poll::Pending));
        assert!(matches!(f_s1_early.as_mut().poll(&mut cx), Poll::Pending));
        // Cond already dropped before Suspend1; inner guard is live inside inner_guarded_step!
        assert_eq!(snapshot_drop_counters(), (0, 0, 1, 0));
    }
    let drops_cancel_s1_early = snapshot_drop_counters();
    assert_eq!(drops_cancel_s1_early, (1, 1, 1, 1));

    reset_drop_counters();
    {
        let mut f_s1_late = Box::pin(async_nested_drop_and_unwind(
            DropGuard {
                kind: GuardKind::Upvar,
                tag: 10,
            },
            20,
            false,
            false,
        ));
        assert!(matches!(f_s1_late.as_mut().poll(&mut cx), Poll::Pending));
        assert!(matches!(f_s1_late.as_mut().poll(&mut cx), Poll::Pending));
        assert_eq!(snapshot_drop_counters(), (0, 0, 0, 0));
    }
    let drops_cancel_s1_late = snapshot_drop_counters();
    assert_eq!(drops_cancel_s1_late, (1, 1, 1, 1));

    // 5. Lifecycle Scenario D: Panic unwind -> state=2 (Panicked) -> repoll panics + drop is no-op.
    reset_drop_counters();
    let mut f_panicked = Box::pin(async_nested_drop_and_unwind(
        DropGuard {
            kind: GuardKind::Upvar,
            tag: 10,
        },
        20,
        false,
        true,
    ));
    assert!(matches!(f_panicked.as_mut().poll(&mut cx), Poll::Pending));
    let body_panic_msg = capture_panic_via_hook(|| {
        let _ = f_panicked.as_mut().poll(&mut cx);
    });
    let drops_after_unwind = snapshot_drop_counters();
    assert_eq!(drops_after_unwind, (1, 1, 1, 1));

    let repoll_after_panic_msg = capture_panic_via_hook(|| {
        let _ = f_panicked.as_mut().poll(&mut cx);
    });
    let drops_after_repoll_panicked = snapshot_drop_counters();
    assert_eq!(drops_after_repoll_panicked, (1, 1, 1, 1));

    core::mem::drop(f_panicked);
    let drops_after_drop_panicked = snapshot_drop_counters();
    assert_eq!(drops_after_drop_panicked, (1, 1, 1, 1));

    // 6. Verify self-referential two-await runtime computation under Pin.
    let mut f_sr = Box::pin(async_self_ref_two_await(5));
    assert!(matches!(f_sr.as_mut().poll(&mut cx), Poll::Pending));
    assert!(matches!(f_sr.as_mut().poll(&mut cx), Poll::Pending));
    let sr_val = match f_sr.as_mut().poll(&mut cx) {
        Poll::Ready(v) => v,
        Poll::Pending => panic!("expected Ready"),
    };
    // pinned_local = 15, y0 = 16, mid = 31, y1 = 33 => 15 + 31 + 33 = 79
    assert_eq!(sr_val, 79);

    // 7. Micro-latency benchmark: 5 x 100,000 complete 3-poll cycles on async_self_ref_two_await.
    let mut trial_ns_per_poll = Vec::with_capacity(5);
    let mut sink: u64 = 0;
    for trial in 0..5u64 {
        let t0 = Instant::now();
        for i in 0..100_000u64 {
            let mut f = core::pin::pin!(async_self_ref_two_await(i.wrapping_add(trial)));
            let _ = core::hint::black_box(f.as_mut().poll(&mut cx));
            let _ = core::hint::black_box(f.as_mut().poll(&mut cx));
            if let Poll::Ready(v) = f.as_mut().poll(&mut cx) {
                sink = sink.wrapping_add(v);
            }
        }
        let elapsed_ns = t0.elapsed().as_nanos() as f64;
        trial_ns_per_poll.push(elapsed_ns / 300_000.0);
    }
    core::hint::black_box(sink);
    trial_ns_per_poll.sort_by(|a, b| a.total_cmp(b));
    let median_ns_per_poll = trial_ns_per_poll[2];

    println!("{{");
    println!("  \"sizes_bytes\": {{");
    println!("    \"manual_unpin_two_step\": [{sz_manual}, {al_manual}],");
    println!("    \"movable_two_yield_coro\": [{sz_mov}, {al_mov}],");
    println!("    \"async_non_self_ref_two_await\": [{sz_non_self}, {al_non_self}],");
    println!("    \"async_self_ref_two_await\": [{sz_self}, {al_self}],");
    println!("    \"async_nested_drop_and_unwind\": [{sz_nested}, {al_nested}]");
    println!("  }},");
    println!("  \"lifecycle_drop_counts\": {{");
    println!("    \"unresumed_drop\": [{}, {}, {}, {}],", drops_unresumed.0, drops_unresumed.1, drops_unresumed.2, drops_unresumed.3);
    println!("    \"normal_complete\": [1, 1, 1, 1],");
    println!("    \"cancel_at_suspend0\": [{}, {}, {}, {}],", drops_cancel_s0.0, drops_cancel_s0.1, drops_cancel_s0.2, drops_cancel_s0.3);
    println!("    \"cancel_at_suspend1_early_drop\": [{}, {}, {}, {}],", drops_cancel_s1_early.0, drops_cancel_s1_early.1, drops_cancel_s1_early.2, drops_cancel_s1_early.3);
    println!("    \"cancel_at_suspend1_late_drop\": [{}, {}, {}, {}],", drops_cancel_s1_late.0, drops_cancel_s1_late.1, drops_cancel_s1_late.2, drops_cancel_s1_late.3);
    println!("    \"after_unwind_poison\": [{}, {}, {}, {}],", drops_after_unwind.0, drops_after_unwind.1, drops_after_unwind.2, drops_after_unwind.3);
    println!("    \"after_repoll_panicked\": [{}, {}, {}, {}],", drops_after_repoll_panicked.0, drops_after_repoll_panicked.1, drops_after_repoll_panicked.2, drops_after_repoll_panicked.3);
    println!("    \"after_drop_panicked\": [{}, {}, {}, {}]", drops_after_drop_panicked.0, drops_after_drop_panicked.1, drops_after_drop_panicked.2, drops_after_drop_panicked.3);
    println!("  }},");
    println!("  \"panic_messages\": {{");
    println!("    \"body_unwind\": {:?},", body_panic_msg);
    println!("    \"resumed_after_return\": {:?},", repoll_after_return_msg);
    println!("    \"resumed_after_panic\": {:?}", repoll_after_panic_msg);
    println!("  }},");
    println!("  \"self_ref_result\": {sr_val},");
    println!("  \"bench_self_ref_ns_per_poll_median\": {median_ns_per_poll:.3},");
    println!("  \"bench_self_ref_ns_per_poll_trials\": [{:.3}, {:.3}, {:.3}, {:.3}, {:.3}]",
        trial_ns_per_poll[0], trial_ns_per_poll[1], trial_ns_per_poll[2], trial_ns_per_poll[3], trial_ns_per_poll[4]);
    println!("}}");
}
