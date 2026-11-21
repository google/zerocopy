//! A `Box<MaybeUninit<Pair>>` with only its first field written is treated as a `Box<Pair>` and
//! dropped: the destructor of the second field reads memory that was never initialized.
#![allow(dead_code)]
use std::mem::MaybeUninit;
use std::ptr::addr_of_mut;

struct Pair {
    first: Box<u64>,
    second: Box<u64>,
}

fn main() {
    let mut b: Box<MaybeUninit<Pair>> = Box::new_uninit();
    unsafe {
        addr_of_mut!((*b.as_mut_ptr()).first).write(Box::new(1));
        let wrong: Box<Pair> = b.assume_init();
        drop(wrong);
    }
}
