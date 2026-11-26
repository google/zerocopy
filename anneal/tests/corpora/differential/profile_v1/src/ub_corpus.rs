// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![no_std]

//! Stage-1 Profile v1 litmus Undefined Behavior fixtures.
//!
//! Every UB helper also admits a benign non-UB input vector so differential
//! tests verify the model does not unconditionally fault on the operation.

pub unsafe fn u32_unchecked_add(a: u32, b: u32) -> u32 {
    unsafe { a.unchecked_add(b) }
}

pub unsafe fn i32_unchecked_add(a: i32, b: i32) -> i32 {
    unsafe { a.unchecked_add(b) }
}

pub unsafe fn i32_unchecked_sub(a: i32, b: i32) -> i32 {
    unsafe { a.unchecked_sub(b) }
}

pub unsafe fn i64_unchecked_sub(a: i64, b: i64) -> i64 {
    unsafe { a.unchecked_sub(b) }
}

pub unsafe fn i8_unchecked_mul(a: i8, b: i8) -> i8 {
    unsafe { a.unchecked_mul(b) }
}

pub unsafe fn branch_unchecked_add(trigger: bool) -> u32 {
    if trigger {
        unsafe { u32::MAX.unchecked_add(1) }
    } else {
        77
    }
}

pub unsafe fn branch_guarded_unchecked_sub(x: u32) -> u32 {
    if x > 10 {
        unsafe { 0u32.unchecked_sub(x) }
    } else {
        x + 1
    }
}

pub unsafe fn loop_to_unchecked_sub(mut n: u32, offset: u32) -> u32 {
    while n > 0 {
        n -= 1;
    }
    unsafe { n.unchecked_sub(offset) }
}
