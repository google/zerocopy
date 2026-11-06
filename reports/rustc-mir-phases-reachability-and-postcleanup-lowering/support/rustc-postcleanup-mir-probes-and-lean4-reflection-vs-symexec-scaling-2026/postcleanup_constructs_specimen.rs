// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Empirical specimen exercising five construct families at `rustc`'s
//! `Runtime(PostCleanup)` and `Runtime(Optimized)` MIR phases:
//!
//! 1. Loops and back-edge storage lifecycle (`while` loop and `Range` iterator
//!    `for` loop).
//! 2. Multi-field mutable borrows, nested reborrows, two-phase borrows, and raw
//!    pointer casts/projections.
//! 3. Multi-variant payload enums, discriminants, `SwitchInt`, and `Downcast`
//!    projections.
//! 4. Arrays, slices, indexing, pattern sub-slicing, and `PtrMetadata` vs.
//!    slice `.len()`.
//! 5. Drop elaboration, stack boolean drop flags, conditional moves, and unwind
//!    cleanup paths (`is_cleanup` + `UnwindResume`).

#![allow(dead_code)]

// ============================================================================
// Family 1: Loops & Back-Edge Storage Lifecycle
// ============================================================================

/// While loop with a loop-carried accumulator (`acc`, `i`) and an inner block-
/// scoped temporary (`step`) re-allocated on every iteration.
#[inline(never)]
pub fn while_loop_sum(n: usize) -> usize {
    let mut acc: usize = 0;
    let mut i: usize = 0;
    while i < n {
        let step: usize = i ^ 1;
        acc = acc.wrapping_add(step);
        i = i.wrapping_add(1);
    }
    acc
}

/// Iterator `for` loop over `0..n` exercising `IntoIterator::into_iter` and
/// `Iterator::next` inside the loop header.
#[inline(never)]
pub fn range_for_loop_sum(n: usize) -> usize {
    let mut acc: usize = 0;
    for x in 0..n {
        acc = acc.wrapping_add(x);
    }
    acc
}

// ============================================================================
// Family 2: Multi-Field Mutable Borrows, Nested Reborrows, Two-Phase Borrows,
//           and Raw Pointer Casts
// ============================================================================

/// Simultaneous mutable borrows of disjoint tuple fields (`&mut (*p).0` and
/// `&mut (*p).1`).
#[inline(never)]
pub fn disjoint_field_borrows(p: &mut (u64, u64)) -> u64 {
    let a: &mut u64 = &mut p.0;
    let b: &mut u64 = &mut p.1;
    *a = (*a).wrapping_add(*b);
    *a
}

/// Nested mutable reborrow (`&mut *r1`) followed by mutation through the inner
/// reborrow and read through the outer reborrow.
#[inline(never)]
pub fn nested_reborrow(x: &mut u64) -> u64 {
    let r1: &mut u64 = &mut *x;
    let r2: &mut u64 = &mut *r1;
    *r2 = (*r2).wrapping_add(1);
    *r1
}

/// Minimal receiver type used to trigger a genuine two-phase mutable borrow
/// (`BorrowKind::Mut { kind: MutBorrowKind::TwoPhaseBorrow }`) in `v.push(v.len())`.
pub struct TwoPhaseReceiver {
    pub count: usize,
    pub last: usize,
}

impl TwoPhaseReceiver {
    #[inline(never)]
    pub fn len(&self) -> usize {
        self.count
    }

    #[inline(never)]
    pub fn push(&mut self, val: usize) {
        self.last = val;
        self.count = self.count.wrapping_add(1);
    }
}

/// Method call `v.push(v.len())` where the receiver `&two-phase mut (*v)` is
/// reserved before evaluating `v.len()` (which takes a shared borrow `&(*v)`).
#[inline(never)]
pub fn two_phase_method_borrow(v: &mut TwoPhaseReceiver) -> usize {
    v.push(v.len());
    v.last
}

/// Raw pointer field projections (`&raw const (*p).1` and `&raw mut (*m).0`)
/// and reference-to-raw-pointer casts.
#[inline(never)]
pub unsafe fn raw_ptr_projections(
    p: *const (u64, u32),
    m: *mut (u64, u32),
) -> (*const u32, *mut u64) {
    let f_const: *const u32 = unsafe { &raw const (*p).1 };
    let f_mut: *mut u64 = unsafe { &raw mut (*m).0 };
    (f_const, f_mut)
}

// ============================================================================
// Family 3: Enums, Discriminants, and Downcast Projections
// ============================================================================

/// Multi-variant payload enum with unit, single-field, and multi-field variants.
pub enum Packet {
    Empty,
    Val(u64),
    Pair(u32, u32),
}

/// Constructs `Packet` variants (`AggregateKind::Adt`) and matches on them
/// (`Rvalue::Discriminant`, `TerminatorKind::SwitchInt`, `ProjectionElem::Downcast`).
#[inline(never)]
pub fn construct_and_match_packet(tag: u8, x: u64, a: u32, b: u32) -> u64 {
    let pkt = match tag {
        0 => Packet::Empty,
        1 => Packet::Val(x),
        _ => Packet::Pair(a, b),
    };
    match pkt {
        Packet::Empty => 0,
        Packet::Val(v) => v,
        Packet::Pair(lo, hi) => (lo as u64).wrapping_add(hi as u64),
    }
}

// ============================================================================
// Family 4: Slices, Arrays, Indexing, and `PtrMetadata`
// ============================================================================

/// Exercises fixed-size array indexing `arr[i]`, shared slice indexing `slice[i]`,
/// mutable slice indexing `mut_slice[i]`, slice pattern matching
/// `[head, rest @ .., tail]`, and explicit `slice.len()`.
#[inline(never)]
pub fn array_and_slice_ops(
    arr: &[u64; 4],
    slice: &[u64],
    mut_slice: &mut [u64],
    i: usize,
) -> u64 {
    let a = arr[i];
    let s = slice[i];
    mut_slice[i] = a.wrapping_add(s);
    let sub_sum = match slice {
        [head, rest @ .., tail] => (*head)
            .wrapping_add(*tail)
            .wrapping_add(rest.len() as u64),
        _ => 0,
    };
    mut_slice[i].wrapping_add(sub_sum)
}

// ============================================================================
// Family 5: Drop Elaboration, Conditional Drop Flags, and Unwind Cleanup Paths
// ============================================================================

/// Non-Copy type with a user-defined `Drop` implementation so `ElaborateDrops`
/// emits `TerminatorKind::Drop`, stack boolean drop flags, and unwind cleanup
/// paths.
pub struct DropTracked(pub u64);

impl Drop for DropTracked {
    #[inline(never)]
    fn drop(&mut self) {
        std::hint::black_box(self.0);
    }
}

#[inline(never)]
pub fn consume_tracked(t: DropTracked) -> u64 {
    t.0
}

/// Conditionally moves `d1` before calling `may_unwind()`, requiring
/// `ElaborateDrops` to maintain a stack boolean drop flag for `d1` along both
/// the normal return path and the unwind cleanup path (`is_cleanup`).
#[inline(never)]
pub fn conditional_move_and_unwind(
    cond: bool,
    x: u64,
    may_unwind: fn() -> u64,
) -> u64 {
    let d1 = DropTracked(x);
    let d2 = DropTracked(x.wrapping_add(1));
    let mut total = if cond {
        consume_tracked(d1)
    } else {
        0
    };
    total = total.wrapping_add(may_unwind());
    total.wrapping_add(d2.0)
}
