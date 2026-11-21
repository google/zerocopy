//! Calling the global allocation function with a zero-sized layout.
use std::alloc::{alloc, Layout};

fn main() {
    unsafe {
        let p = alloc(Layout::from_size_align(0, 8).unwrap());
        std::hint::black_box(p);
    }
}
