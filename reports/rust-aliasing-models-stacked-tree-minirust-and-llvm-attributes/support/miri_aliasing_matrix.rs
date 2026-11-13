// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![allow(unused, invalid_reference_casting)]
use std::cell::UnsafeCell;

fn empty_mut(_x: &mut u8) {}

// Case 1: SB fails, TB passes (unused &mut T created from raw pointer, then parent raw read, then passed to function).
fn case1_sb_fails_tb_passes() {
    let mut data = 0u8;
    let raw: *mut u8 = &mut data;
    let r: &mut u8 = unsafe { &mut *raw };
    let _val = unsafe { *raw };
    empty_mut(r);
}

// Case 2: SB passes, TB fails (raw pointer cast from &mut T is written, then parent root is read, then raw pointer is written again).
fn case2_sb_passes_tb_fails() {
    unsafe {
        let mut root = 6u8;
        let mref = &mut root;
        let ptr = mref as *mut u8;
        *ptr = 0;
        assert_eq!(root, 0);
        *ptr = 0;
    }
}

// Case 3: Protected Reserved &mut T sees a foreign read and then performs a local write (SB fails at foreign read; TB fails at local write).
fn case3_callee(x: &mut u8, raw: *const u8) {
    let _v = unsafe { *raw };
    *x = 42;
}
fn case3_protected_reserved_foreign_read_then_write() {
    let mut data = 0u8;
    let raw: *mut u8 = &mut data;
    let r = unsafe { &mut *raw };
    case3_callee(r, raw);
}

// Case 4: Protected Reserved &mut T sees a foreign read and returns without writing (SB fails; default TB passes; TB with -Zmiri-tree-borrows-implicit-writes fails).
fn case4_callee(_x: &mut u8, raw: *const u8) -> u8 {
    unsafe { *raw }
}
fn case4_protected_reserved_foreign_read_no_write() {
    let mut data = 7u8;
    let raw: *mut u8 = &mut data;
    let r = unsafe { &mut *raw };
    let v = case4_callee(r, raw);
    assert_eq!(v, 7);
}

// Case 5: Exposed provenance round-trip (`expose_provenance` + `with_exposed_provenance_mut`).
fn case5_exposed_provenance() {
    let mut data = 10u8;
    let addr = (&mut data as *mut u8).expose_provenance();
    let ptr: *mut u8 = std::ptr::with_exposed_provenance_mut(addr);
    unsafe { *ptr = 20; }
    assert_eq!(data, 20);
}

// Case 6: Sub-object UnsafeCell inside `&(u8, UnsafeCell<u8>)`: writing to the non-UnsafeCell byte 0 (SB and TB fail; no-tracker passes).
fn case6_write_non_cell_field_via_shared_ref() {
    #[repr(C)]
    struct Pair(u8, UnsafeCell<u8>);
    let p = Pair(1, UnsafeCell::new(2));
    let r: &Pair = &p;
    let base = r as *const Pair as *mut u8;
    unsafe { *base = 99; }
}

// Case 7: Sub-object UnsafeCell inside `&(u8, UnsafeCell<u8>)`: writing to the UnsafeCell byte 1 via direct cast without UnsafeCell::get (all models pass).
fn case7_write_cell_field_via_shared_ref() {
    #[repr(C)]
    struct Pair(u8, UnsafeCell<u8>);
    let p = Pair(1, UnsafeCell::new(2));
    let r: &Pair = &p;
    let base = r as *const Pair as *mut u8;
    unsafe { *base.add(1) = 99; }
    assert_eq!(unsafe { *p.1.get() }, 99);
}

fn main() {
    #[cfg(case = "1")] case1_sb_fails_tb_passes();
    #[cfg(case = "2")] case2_sb_passes_tb_fails();
    #[cfg(case = "3")] case3_protected_reserved_foreign_read_then_write();
    #[cfg(case = "4")] case4_protected_reserved_foreign_read_no_write();
    #[cfg(case = "5")] case5_exposed_provenance();
    #[cfg(case = "6")] case6_write_non_cell_field_via_shared_ref();
    #[cfg(case = "7")] case7_write_cell_field_via_shared_ref();
}
