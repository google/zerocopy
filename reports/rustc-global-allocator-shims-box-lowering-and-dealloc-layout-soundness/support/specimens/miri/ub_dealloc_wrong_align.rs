//! Deallocating with the right size but a different alignment than the block was allocated with.
use std::alloc::{alloc, dealloc, Layout};

fn main() {
    unsafe {
        let p = alloc(Layout::from_size_align(8, 8).unwrap());
        assert!(!p.is_null());
        dealloc(p, Layout::from_size_align(8, 4).unwrap());
    }
}
