//! MIR specimens: the probe script dumps these functions at several points of the MIR pipeline.
//!
//!     rustc --edition 2021 --crate-type=lib -C panic=unwind -Zdump-mir=<filter> -Zdump-mir-dir=<dir> mir_specimens.rs
//!
//! `write_via_move_direct` calls the `core::intrinsics::write_via_move` intrinsic itself; that is
//! the only reason for the feature gate.

#![feature(core_intrinsics)]
#![allow(internal_features)]
#![allow(dead_code)]

use std::mem::MaybeUninit;
use std::ptr::addr_of_mut;

pub struct Counted {
    pub tag: usize,
}

impl Drop for Counted {
    #[inline(never)]
    fn drop(&mut self) {
        std::hint::black_box(self.tag);
    }
}

/// Has drop glue through its fields but no `Drop` implementation, so fields can be moved out.
pub struct Pair {
    pub first: Counted,
    pub second: Counted,
}

#[inline(never)]
pub fn maybe_panic(yes: bool) {
    if yes {
        panic!("deliberate panic");
    }
}

/// `Box::new` of a sized value with drop glue.
pub fn box_new_sized(p: Pair) -> Box<Pair> {
    Box::new(p)
}

/// `Box::new` of a zero-sized value.
pub fn box_new_zst() -> Box<()> {
    Box::new(())
}

/// The intrinsic that `Box::new` uses to store its argument.
pub fn write_via_move_direct(ptr: *mut Pair, value: Pair) {
    unsafe { core::intrinsics::write_via_move(ptr, value) }
}

/// A `Box<MaybeUninit<Pair>>` that is half written when a call may unwind.
pub fn box_new_uninit_mid_init(should_panic: bool) -> Box<Pair> {
    let mut b: Box<MaybeUninit<Pair>> = Box::new_uninit();
    unsafe { addr_of_mut!((*b.as_mut_ptr()).first).write(Counted { tag: 1 }) };
    maybe_panic(should_panic);
    unsafe { addr_of_mut!((*b.as_mut_ptr()).second).write(Counted { tag: 2 }) };
    unsafe { b.assume_init() }
}

/// One field is moved out of the box, then a call may unwind.
pub fn box_partial_move(b: Box<Pair>, should_panic: bool) -> Counted {
    let first = b.first;
    maybe_panic(should_panic);
    first
}

/// One field is moved out of the box on one path only, so a drop flag is needed.
pub fn box_conditional_partial_move(b: Box<Pair>, take: bool) -> Option<Counted> {
    let r = if take { Some(b.first) } else { None };
    maybe_panic(take);
    r
}

/// The whole value is moved out of the box.
pub fn box_full_move_out(b: Box<Pair>) -> Pair {
    *b
}

/// A box that is simply dropped.
pub fn box_plain_drop(b: Box<Pair>) {
    drop(b)
}

/// Reads through a box.
pub fn box_deref_read(b: &Box<usize>) -> usize {
    **b
}

/// The `vec!` literal form.
pub fn vec_literal(a: Counted, b: Counted) -> Vec<Counted> {
    vec![a, b]
}
