//! Atomic and fence lowering probe.
//!
//! Compile as a `#![no_std]` rlib and inspect `--emit=mir,llvm-ir,asm`:
//!
//! ```text
//! rustc --edition=2021 --crate-type=rlib --crate-name=atomics -C opt-level=3 \
//!     --target x86_64-unknown-linux-gnu --emit=asm,llvm-ir atomic_lowering_probe.rs
//! ```
//!
//! Section A holds the 36 functions whose names and signatures match the
//! preserved 13-configuration measurement
//! (`atomic_lowering_13_config_measurements.json`). Section B adds functions
//! that only the live probe (`run_live_probe.py`) compiles.
#![no_std]
#![allow(static_mut_refs)]

use core::sync::atomic::{
    compiler_fence, fence, AtomicU32, AtomicU64, AtomicU8, Ordering::*,
};

// ---------------------------------------------------------------------------
// Section A: functions present in the preserved 13-configuration measurement.
// ---------------------------------------------------------------------------

#[no_mangle] pub fn at_u32_load_relaxed(a: &AtomicU32) -> u32 { a.load(Relaxed) }
#[no_mangle] pub fn at_u32_load_acquire(a: &AtomicU32) -> u32 { a.load(Acquire) }
#[no_mangle] pub fn at_u32_load_seqcst(a: &AtomicU32) -> u32 { a.load(SeqCst) }

#[no_mangle] pub fn at_u32_store_relaxed(a: &AtomicU32, v: u32) { a.store(v, Relaxed) }
#[no_mangle] pub fn at_u32_store_release(a: &AtomicU32, v: u32) { a.store(v, Release) }
#[no_mangle] pub fn at_u32_store_seqcst(a: &AtomicU32, v: u32) { a.store(v, SeqCst) }

#[no_mangle] pub fn at_u32_swap_relaxed(a: &AtomicU32, v: u32) -> u32 { a.swap(v, Relaxed) }
#[no_mangle] pub fn at_u32_swap_acquire(a: &AtomicU32, v: u32) -> u32 { a.swap(v, Acquire) }
#[no_mangle] pub fn at_u32_swap_release(a: &AtomicU32, v: u32) -> u32 { a.swap(v, Release) }
#[no_mangle] pub fn at_u32_swap_acqrel(a: &AtomicU32, v: u32) -> u32 { a.swap(v, AcqRel) }
#[no_mangle] pub fn at_u32_swap_seqcst(a: &AtomicU32, v: u32) -> u32 { a.swap(v, SeqCst) }

#[no_mangle] pub fn at_u32_fadd_relaxed(a: &AtomicU32, v: u32) -> u32 { a.fetch_add(v, Relaxed) }
#[no_mangle] pub fn at_u32_fadd_acquire(a: &AtomicU32, v: u32) -> u32 { a.fetch_add(v, Acquire) }
#[no_mangle] pub fn at_u32_fadd_release(a: &AtomicU32, v: u32) -> u32 { a.fetch_add(v, Release) }
#[no_mangle] pub fn at_u32_fadd_acqrel(a: &AtomicU32, v: u32) -> u32 { a.fetch_add(v, AcqRel) }
#[no_mangle] pub fn at_u32_fadd_seqcst(a: &AtomicU32, v: u32) -> u32 { a.fetch_add(v, SeqCst) }

#[no_mangle]
pub fn at_u32_cas_strong_acqrel_acq(a: &AtomicU32, c: u32, n: u32) -> u32 {
    match a.compare_exchange(c, n, AcqRel, Acquire) {
        Ok(v) | Err(v) => v,
    }
}

#[no_mangle]
pub fn at_u32_cas_strong_seqcst_seqcst(a: &AtomicU32, c: u32, n: u32) -> u32 {
    match a.compare_exchange(c, n, SeqCst, SeqCst) {
        Ok(v) | Err(v) => v,
    }
}

#[no_mangle]
pub fn at_u32_cas_weak_rel_rlx(a: &AtomicU32, c: u32, n: u32) -> u32 {
    match a.compare_exchange_weak(c, n, Release, Relaxed) {
        Ok(v) | Err(v) => v,
    }
}

#[no_mangle] pub fn at_u64_load_acquire(a: &AtomicU64) -> u64 { a.load(Acquire) }
#[no_mangle] pub fn at_u64_store_seqcst(a: &AtomicU64, v: u64) { a.store(v, SeqCst) }
#[no_mangle] pub fn at_u64_fadd_acqrel(a: &AtomicU64, v: u64) -> u64 { a.fetch_add(v, AcqRel) }

#[no_mangle]
pub fn at_u64_cas_seqcst(a: &AtomicU64, c: u64, n: u64) -> u64 {
    match a.compare_exchange(c, n, SeqCst, Acquire) {
        Ok(v) | Err(v) => v,
    }
}

#[no_mangle] pub fn at_u8_fand_acqrel(a: &AtomicU8, m: u8) -> u8 { a.fetch_and(m, AcqRel) }

#[no_mangle] pub fn at_fence_acquire() { fence(Acquire) }
#[no_mangle] pub fn at_fence_release() { fence(Release) }
#[no_mangle] pub fn at_fence_acqrel() { fence(AcqRel) }
#[no_mangle] pub fn at_fence_seqcst() { fence(SeqCst) }

#[no_mangle] pub fn at_cfence_acquire() { compiler_fence(Acquire) }
#[no_mangle] pub fn at_cfence_release() { compiler_fence(Release) }
#[no_mangle] pub fn at_cfence_acqrel() { compiler_fence(AcqRel) }
#[no_mangle] pub fn at_cfence_seqcst() { compiler_fence(SeqCst) }

/// The loaded value is unused. Does the optimizer delete the relaxed load?
#[no_mangle]
pub fn canary_dead_relaxed_load(a: &AtomicU32) -> u32 {
    let _ = a.load(Relaxed);
    42
}

/// Two back-to-back relaxed stores to one atomic. Does the optimizer merge them?
#[no_mangle]
pub fn canary_adjacent_relaxed_stores(a: &AtomicU32, x: u32, y: u32) {
    a.store(x, Relaxed);
    a.store(y, Relaxed);
}

/// A plain store through `&mut`, a release compiler fence, a relaxed atomic
/// store, an acquire compiler fence, then a reload of the `&mut` place.
#[no_mangle]
pub fn canary_cfence_blocks_store_hoist(flag: &AtomicU32, data: &mut u32, v: u32) -> u32 {
    *data = v;
    compiler_fence(Release);
    flag.store(1, Relaxed);
    compiler_fence(Acquire);
    *data
}

/// The same body without the two compiler fences.
#[no_mangle]
pub fn canary_no_cfence_store_forwarding(flag: &AtomicU32, data: &mut u32, v: u32) -> u32 {
    *data = v;
    flag.store(1, Relaxed);
    *data
}

// ---------------------------------------------------------------------------
// Section B: live-probe-only extensions.
// ---------------------------------------------------------------------------

#[no_mangle] pub fn ext_u64_load_relaxed(a: &AtomicU64) -> u64 { a.load(Relaxed) }
#[no_mangle] pub fn ext_u64_load_seqcst(a: &AtomicU64) -> u64 { a.load(SeqCst) }
#[no_mangle] pub fn ext_u64_store_relaxed(a: &AtomicU64, v: u64) { a.store(v, Relaxed) }
#[no_mangle] pub fn ext_u64_store_release(a: &AtomicU64, v: u64) { a.store(v, Release) }
#[no_mangle] pub fn ext_u64_swap_seqcst(a: &AtomicU64, v: u64) -> u64 { a.swap(v, SeqCst) }

/// The published datum of the `compiler_fence` documentation example: a
/// non-atomic static written by the main flow and read by a signal handler.
pub static mut IMPORTANT_VARIABLE: u32 = 0;
pub static IS_READY: AtomicU32 = AtomicU32::new(0);

/// `IMPORTANT_VARIABLE = v; compiler_fence(Release); IS_READY = 1; IMPORTANT_VARIABLE = w`.
/// The first store is overwritten before any same-thread read, so only the
/// compiler fence stops dead-store elimination from deleting it.
#[no_mangle]
pub fn canary_publish_then_overwrite_with_cfence(v: u32, w: u32) {
    unsafe { IMPORTANT_VARIABLE = v };
    compiler_fence(Release);
    IS_READY.store(1, Relaxed);
    unsafe { IMPORTANT_VARIABLE = w };
}

/// The same body without the compiler fence.
#[no_mangle]
pub fn canary_publish_then_overwrite_without_cfence(v: u32, w: u32) {
    unsafe { IMPORTANT_VARIABLE = v };
    IS_READY.store(1, Relaxed);
    unsafe { IMPORTANT_VARIABLE = w };
}

/// The signal-handler side of the documentation example.
#[no_mangle]
pub fn canary_handler_read_with_cfence() -> u32 {
    if IS_READY.load(Relaxed) != 0 {
        compiler_fence(Acquire);
        unsafe { IMPORTANT_VARIABLE }
    } else {
        0
    }
}
