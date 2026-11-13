// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![crate_type = "lib"]
use std::cell::UnsafeCell;
use std::marker::PhantomPinned;

#[repr(C)]
pub struct Big([u64; 8]);

#[no_mangle]
pub fn ref_shared_freeze(x: &u64) -> u64 { *x }

#[no_mangle]
pub fn ref_shared_cell(x: &UnsafeCell<u64>) -> u64 { unsafe { *x.get() } }

#[no_mangle]
pub fn ref_mut_unpin(x: &mut u64, v: u64) { *x = v; }

#[no_mangle]
pub fn ref_mut_not_unpin(x: &mut (u64, PhantomPinned), v: u64) { x.0 = v; }

#[no_mangle]
pub fn box_unpin(mut x: Box<u64>, v: u64) -> u64 { *x += v; *x }

#[no_mangle]
pub fn box_not_unpin(mut x: Box<(u64, PhantomPinned)>, v: u64) -> u64 { x.0 += v; x.0 }

#[no_mangle]
pub fn return_ref(x: &mut u64) -> &mut u64 { x }

#[no_mangle]
pub fn return_sret(v: u64) -> Big { Big([v; 8]) }

#[inline(always)]
pub fn inline_callee(a: &mut u64, b: &u64, c: &mut u64) {
    *a += *b;
    *c += *b;
}

#[no_mangle]
pub fn inline_caller(x: &mut u64, y: &u64, z: &mut u64) {
    inline_callee(x, y, z);
}

#[no_mangle]
pub unsafe fn raw_caller(x: *mut u64, y: *const u64, z: *mut u64) {
    inline_callee(&mut *x, &*y, &mut *z);
}

#[inline(always)]
pub fn inline_callee_mut(a: &mut u64, c: &mut u64) -> u64 {
    *a = 1;
    *c = 2;
    *a
}

#[no_mangle]
pub unsafe fn raw_caller_mut(x: *mut u64, z: *mut u64) -> u64 {
    inline_callee_mut(&mut *x, &mut *z)
}
