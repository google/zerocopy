// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![feature(dropck_eyepatch)]
#![allow(dead_code, unused_variables, unused_assignments)]

use std::marker::PhantomData;
use std::sync::atomic::{AtomicUsize, Ordering};

pub struct TrackedGuard(pub usize);

impl Drop for TrackedGuard {
    #[inline(never)]
    fn drop(&mut self) {
        std::hint::black_box(self.0);
    }
}

pub struct GuardPair(pub TrackedGuard, pub TrackedGuard);

pub struct EyepatchGuard<'a>(pub &'a usize);

unsafe impl<#[may_dangle] 'a> Drop for EyepatchGuard<'a> {
    #[inline(never)]
    fn drop(&mut self) {
        // Does not dereference `self.0`, which may already be StorageDead.
        std::hint::black_box(self as *mut Self);
    }
}

#[repr(transparent)]
pub struct TransparentWithPhantom<T>(pub PhantomData<u64>, pub (), pub T);

/// Case 1: Assert with live droppable local (`UnwindAction::Cleanup(bb)` -> `Drop` -> `UnwindResume`).
pub fn assert_with_drop_cleanup(x: usize) -> usize {
    let g = TrackedGuard(10);
    assert!(x != 0);
    g.0 + x
}

/// Case 2: Conditional dynamic drop flag (`_drop_flag : bool`) on normal vs. cleanup path.
#[inline(never)]
pub fn may_unwind_callee(x: usize) -> usize {
    assert!(x < 100);
    x + 1
}

pub fn conditional_drop_flag_unwind(cond: bool, x: usize) -> usize {
    let g = TrackedGuard(20);
    if cond {
        drop(g);
    }
    may_unwind_callee(x)
}

/// Case 3: Partial move out of a multi-field struct (`DropStyle::Open` drop ladder).
pub fn open_drop_partial_move(cond: bool, x: usize) -> usize {
    let pair = GuardPair(TrackedGuard(1), TrackedGuard(2));
    if cond {
        let moved_first = pair.0;
        drop(moved_first);
    }
    may_unwind_callee(x)
}

/// Case 4: `#[may_dangle]` where `StorageDead` of the borrowed local precedes `Drop` of the guard.
pub fn may_dangle_storage_dead_order(x: usize) -> usize {
    let g;
    {
        let scoped_val = x + 1;
        g = EyepatchGuard(&scoped_val);
    }
    // `scoped_val` is already `StorageDead` here before `g` is dropped at scope exit.
    42
}

/// Case 5: `extern "C"` ABI boundary where cleanup still runs before `UnwindTerminate(Abi)`.
pub extern "C" fn extern_c_cleanup_then_terminate(x: usize) -> usize {
    let g = TrackedGuard(30);
    assert!(x != 0);
    g.0 + x
}

/// Case 6: Multi-field shared borrow `&pair.1` and `#[repr(transparent)]` with 1-ZST fields.
#[repr(C)]
pub struct TwoUsize {
    pub first: usize,
    pub second: usize,
}

pub fn borrow_second_field(s: &TwoUsize) -> usize {
    let r = &s.second;
    *r
}

pub unsafe fn transmute_copy_transparent_phantom<T>(src: &TransparentWithPhantom<T>) -> T {
    unsafe { core::mem::transmute_copy(src) }
}

/// Case 7: Intrinsics and stdlib primitives in `Runtime(PostCleanup)` MIR.
pub fn intrinsic_and_atomic_gallery<T>(a: &AtomicUsize, x: usize) -> usize {
    let sz = core::mem::size_of::<T>();
    let al = core::mem::align_of::<T>();
    let loaded = a.load(Ordering::Relaxed);
    let swapped = x.swap_bytes();
    let lz = x.leading_zeros() as usize;
    sz.wrapping_add(al).wrapping_add(loaded).wrapping_add(swapped).wrapping_add(lz)
}

fn main() {
    assert_eq!(assert_with_drop_cleanup(5), 15);
    assert_eq!(conditional_drop_flag_unwind(true, 10), 11);
    assert_eq!(conditional_drop_flag_unwind(false, 10), 11);
    assert_eq!(open_drop_partial_move(true, 10), 11);
    assert_eq!(open_drop_partial_move(false, 10), 11);
    assert_eq!(may_dangle_storage_dead_order(7), 42);
    assert_eq!(extern_c_cleanup_then_terminate(3), 33);
    let pair = TwoUsize { first: 11, second: 22 };
    assert_eq!(borrow_second_field(&pair), 22);
    let wrapped = TransparentWithPhantom(PhantomData, (), 99usize);
    let unwrapped: usize = unsafe { transmute_copy_transparent_phantom(&wrapped) };
    assert_eq!(unwrapped, 99);
    let atom = AtomicUsize::new(7);
    let _ = intrinsic_and_atomic_gallery::<u64>(&atom, 0x01020304usize);
    println!("ALL_PROBES_OK");
}
