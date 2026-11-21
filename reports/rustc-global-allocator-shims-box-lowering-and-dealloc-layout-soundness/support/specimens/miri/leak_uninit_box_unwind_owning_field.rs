//! A half-written `Box<MaybeUninit<Pair>>` whose written field owns a heap block is live when a
//! panic unwinds. The outer block is freed, but nothing drops the written field, so the block it
//! owns is never freed. This is a leak, not undefined behavior.
#![allow(dead_code)]
use std::mem::MaybeUninit;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::ptr::addr_of_mut;

struct Pair {
    first: Box<u64>,
    second: Box<u64>,
}

fn main() {
    let r = catch_unwind(AssertUnwindSafe(|| {
        let mut b: Box<MaybeUninit<Pair>> = Box::new_uninit();
        unsafe { addr_of_mut!((*b.as_mut_ptr()).first).write(Box::new(1)) };
        if std::hint::black_box(true) {
            panic!("deliberate panic");
        }
        unsafe { addr_of_mut!((*b.as_mut_ptr()).second).write(Box::new(2)) };
        let b = unsafe { b.assume_init() };
        std::hint::black_box(b);
    }));
    assert!(r.is_err());
    println!("unwound");
}
