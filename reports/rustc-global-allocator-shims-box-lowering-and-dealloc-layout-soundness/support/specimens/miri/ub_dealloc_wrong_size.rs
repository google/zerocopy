//! Deallocating with the right alignment but a different size than the block was allocated with.
use std::alloc::{alloc, dealloc, Layout};

fn main() {
    unsafe {
        let p = alloc(Layout::from_size_align(8, 8).unwrap());
        assert!(!p.is_null());
        dealloc(p, Layout::from_size_align(16, 8).unwrap());
    }
}
