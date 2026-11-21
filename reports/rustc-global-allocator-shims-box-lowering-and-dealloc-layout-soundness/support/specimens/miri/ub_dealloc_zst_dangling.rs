//! Calling the global deallocation function on the dangling pointer of a zero-sized `Box`.
use std::alloc::{dealloc, Layout};

fn main() {
    let b: Box<()> = Box::new(());
    let p = Box::into_raw(b) as *mut u8;
    unsafe {
        dealloc(p, Layout::new::<()>());
    }
}
