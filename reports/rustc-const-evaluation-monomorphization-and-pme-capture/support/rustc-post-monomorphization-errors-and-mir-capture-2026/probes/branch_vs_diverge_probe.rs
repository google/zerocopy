// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![crate_type = "lib"]
#![allow(unreachable_code, unused_variables)]

pub fn const_bounded_add<const N: usize>(x: usize) -> usize {
    const {
        assert!(N <= 1000);
    }
    if x <= 1000 { x + N } else { 0 }
}

// -----------------------------------------------------------------------------
// 1. Dead conditional branches (CFG-reachable from bb0 in mir_built)
// -----------------------------------------------------------------------------

pub fn case_if_false_const<const N: usize>() {
    if false {
        const {
            assert!(N <= 1000);
        }
    }
}

pub fn case_match_false_const<const N: usize>() {
    match false {
        true => const {
            assert!(N <= 1000);
        },
        false => (),
    }
}

pub fn case_if_const_false_const<const N: usize>() {
    if (const { false }) {
        const {
            assert!(N <= 1000);
        }
    }
}

pub fn case_let_b_false_if_b_const<const N: usize>() {
    let b = false;
    if b {
        const {
            assert!(N <= 1000);
        }
    }
}

pub fn case_if_false_call<const N: usize>(x: usize) {
    if false {
        let _ = const_bounded_add::<N>(x);
    }
}

pub fn case_match_false_call<const N: usize>(x: usize) {
    match false {
        true => {
            let _ = const_bounded_add::<N>(x);
        }
        false => (),
    }
}

pub fn case_if_const_false_call<const N: usize>(x: usize) {
    if (const { false }) {
        let _ = const_bounded_add::<N>(x);
    }
}

pub fn case_let_b_false_if_b_call<const N: usize>(x: usize) {
    let b = false;
    if b {
        let _ = const_bounded_add::<N>(x);
    }
}

// -----------------------------------------------------------------------------
// 2. Diverging statements before the PME (zero-predecessor block in mir_built)
// -----------------------------------------------------------------------------

pub fn case_after_return_const<const N: usize>() {
    return;
    const {
        assert!(N <= 1000);
    }
}

pub fn case_after_return_call<const N: usize>(x: usize) {
    return;
    let _ = const_bounded_add::<N>(x);
}

pub fn case_after_break_const<const N: usize>() {
    'blk: {
        break 'blk;
        const {
            assert!(N <= 1000);
        }
    }
}

pub fn case_after_break_call<const N: usize>(x: usize) {
    'blk: {
        break 'blk;
        let _ = const_bounded_add::<N>(x);
    }
}

pub fn case_after_continue_const<const N: usize>() {
    let mut done = false;
    while !done {
        done = true;
        continue;
        const {
            assert!(N <= 1000);
        }
    }
}

pub fn case_after_continue_call<const N: usize>(x: usize) {
    let mut done = false;
    while !done {
        done = true;
        continue;
        let _ = const_bounded_add::<N>(x);
    }
}

pub fn case_after_loop_const<const N: usize>() {
    loop {}
    const {
        assert!(N <= 1000);
    }
}

pub fn case_after_loop_call<const N: usize>(x: usize) {
    loop {}
    let _ = const_bounded_add::<N>(x);
}

// -----------------------------------------------------------------------------
// Monomorphic instantiation triggers (N = 2000 > 1000)
// -----------------------------------------------------------------------------

#[cfg(trig_if_false_const)]
pub fn t() {
    case_if_false_const::<2000>();
}

#[cfg(trig_match_false_const)]
pub fn t() {
    case_match_false_const::<2000>();
}

#[cfg(trig_if_const_false_const)]
pub fn t() {
    case_if_const_false_const::<2000>();
}

#[cfg(trig_let_b_false_if_b_const)]
pub fn t() {
    case_let_b_false_if_b_const::<2000>();
}

#[cfg(trig_if_false_call)]
pub fn t() {
    case_if_false_call::<2000>(5);
}

#[cfg(trig_match_false_call)]
pub fn t() {
    case_match_false_call::<2000>(5);
}

#[cfg(trig_if_const_false_call)]
pub fn t() {
    case_if_const_false_call::<2000>(5);
}

#[cfg(trig_let_b_false_if_b_call)]
pub fn t() {
    case_let_b_false_if_b_call::<2000>(5);
}

#[cfg(trig_after_return_const)]
pub fn t() {
    case_after_return_const::<2000>();
}

#[cfg(trig_after_return_call)]
pub fn t() {
    case_after_return_call::<2000>(5);
}

#[cfg(trig_after_break_const)]
pub fn t() {
    case_after_break_const::<2000>();
}

#[cfg(trig_after_break_call)]
pub fn t() {
    case_after_break_call::<2000>(5);
}

#[cfg(trig_after_continue_const)]
pub fn t() {
    case_after_continue_const::<2000>();
}

#[cfg(trig_after_continue_call)]
pub fn t() {
    case_after_continue_call::<2000>(5);
}

#[cfg(trig_after_loop_const)]
pub fn t() {
    case_after_loop_const::<2000>();
}

#[cfg(trig_after_loop_call)]
pub fn t() {
    case_after_loop_call::<2000>(5);
}
