// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Specimen functions for probing `rustc` MIR lowering across `built` and
//! `Runtime(PostCleanup)` phases under varying compiler flags:
//! - partial moves out of multi-field non-`Copy` aggregates (`Operand::Move`),
//! - `StatementKind::PlaceMention` erasure vs. `-Z mir-preserve-ub` retention,
//! - dead-branch associated constant pruning (`SimplifyConstCondition` /
//!   `RemoveDeadBlocks`) vs. `mentioned_items` preservation, and
//! - compiler-inserted `TerminatorKind::Assert` vs. `core::panicking::panic`
//!   calls across `-C overflow-checks` and `-C debug-assertions` profiles.

#![no_std]
#![allow(dead_code)]

use core::marker::PhantomData;

pub struct NonCopy(pub usize);

pub struct Pair(pub NonCopy, pub NonCopy);

/// (a) Moves field `0` and then sibling field `1` out of a non-`Copy` pair.
/// In `Runtime(PostCleanup)` MIR, `_2 = move (_1.0: NonCopy)` is followed by
/// `_3 = move (_1.1: NonCopy)` while `_1` remains live (`StorageDead(_1)` is
/// not emitted until the end of the function).
pub fn partial_move_sibling(p: Pair) -> (NonCopy, NonCopy) {
    let a = p.0;
    let b = p.1;
    (a, b)
}

/// (b) Evaluates a raw pointer dereference in a place-mention binding
/// (`let _ = *p;`). Lowered to `PlaceMention((*_1))` in `built` MIR, erased by
/// `RemovePlaceMention` in default `Runtime(PostCleanup)` MIR, and retained in
/// `Runtime(PostCleanup)` MIR when `-Z mir-preserve-ub` is enabled.
pub unsafe fn place_mention_raw_ptr(p: *const usize) {
    unsafe {
        let _ = *p;
    }
}

pub struct Fail<T>(PhantomData<T>);

impl<T> Fail<T> {
    pub const C: usize = {
        assert!(core::mem::size_of::<T>() == 8);
        1
    };
}

/// (c) References associated constant `Fail::<T>::C` inside a syntactically
/// dead `if false` branch. `SimplifyConstCondition` and `RemoveDeadBlocks`
/// erase the dead basic block (removing `Fail::<T>::C` from basic blocks and
/// `required_consts` before `Runtime(PostCleanup)`), while `built` MIR and
/// `Body::mentioned_items` record the `Fail::<T>::C` reference.
pub fn dead_branch_pme<T>() -> usize {
    if false {
        let _ = Fail::<T>::C;
    }
    0
}

#[cfg(debug_assertions)]
pub fn debug_only_helper() -> u8 {
    1
}

/// (d.1) Checked addition: emits `AddWithOverflow` + `TerminatorKind::Assert`
/// when `-C overflow-checks=yes`, and wrapping `BinOp::Add` without `Assert`
/// when `-C overflow-checks=no`.
pub fn checked_add(x: u8) -> u8 {
    x + 1
}

/// (d.2) Soundness counterexample for `TerminatorKind::Assert` failure
/// semantics: under `-C overflow-checks=yes`, `x = 255` fails the overflow
/// `Assert` before reaching `y == 0`; under `-C overflow-checks=no`, `255 + 1`
/// wraps to `0` and enters the `unreachable_unchecked()` branch (`unreachable`
/// terminator).
pub fn bad_overflow(x: u8) -> u8 {
    let y = x + 1;
    if y == 0 {
        unsafe { core::hint::unreachable_unchecked() }
    }
    y
}

/// (d.3) User-level `assert!` macro: lowers to `SwitchInt` + a `Call`
/// terminator invoking `core::panicking::panic` under both debug and release
/// configurations, rather than `TerminatorKind::Assert`.
pub fn explicit_assert(x: u8) -> u8 {
    assert!(x > 0);
    x
}
