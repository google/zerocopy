#![feature(core_intrinsics)]
#![allow(internal_features)]

extern crate alloc;
use alloc::alloc::{alloc, dealloc, Layout};
use alloc::boxed::Box;

#[no_mangle]
pub fn elide_box(x: u64) -> u64 {
    let b = Box::new(x + 1);
    *b
}

#[no_mangle]
pub unsafe fn alloc_then_zero(n: usize) -> *mut u8 {
    let layout = Layout::from_size_align_unchecked(n, 8);
    let p = alloc(layout);
    if !p.is_null() {
        core::ptr::write_bytes(p, 0, n);
    }
    p
}

#[no_mangle]
pub fn strict_with_addr(p: *const u64, mask: usize) -> *const u64 {
    p.map_addr(|a| a & mask)
}

#[no_mangle]
pub fn exposed_roundtrip(p: *const u64) -> *const u64 {
    let addr = p.expose_provenance();
    core::ptr::with_exposed_provenance(addr)
}

#[no_mangle]
pub unsafe fn offset_from_pair(a: *const u32, b: *const u32) -> (isize, usize) {
    (a.offset_from(b), a.offset_from_unsigned(b))
}

#[no_mangle]
pub fn disjoint_stack_lifetimes(cond: bool) -> u64 {
    let mut out = 0u64;
    {
        let a = [1u64; 8];
        out += core::hint::black_box(&a)[0];
    }
    {
        let b = [2u64; 8];
        out += core::hint::black_box(&b)[0];
    }
    if cond { out } else { 0 }
}

fn main() {
    assert_eq!(elide_box(41), 42);
    let x = 123u64;
    let p = &raw const x;
    assert_eq!(unsafe { *strict_with_addr(p, !0usize) }, 123);
    assert_eq!(unsafe { *exposed_roundtrip(p) }, 123);
    let arr = [10u32, 20, 30, 40];
    let base = arr.as_ptr();
    assert_eq!(unsafe { offset_from_pair(base.add(3), base.add(1)) }, (2, 2));
    assert_eq!(disjoint_stack_lifetimes(true), 3);
}
