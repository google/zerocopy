//! A half-written `Box<MaybeUninit<[u64; 2]>>` is live when a panic unwinds. Expected: no error
//! and no leak (the block is freed; the element type owns nothing).
use std::mem::MaybeUninit;
use std::panic::{catch_unwind, AssertUnwindSafe};

fn main() {
    let r = catch_unwind(AssertUnwindSafe(|| {
        let mut b: Box<MaybeUninit<[u64; 2]>> = Box::new_uninit();
        unsafe { (b.as_mut_ptr() as *mut u64).write(1) };
        if std::hint::black_box(true) {
            panic!("deliberate panic");
        }
        let b = unsafe { b.assume_init() };
        std::hint::black_box(b);
    }));
    assert!(r.is_err());
    println!("ok");
}
