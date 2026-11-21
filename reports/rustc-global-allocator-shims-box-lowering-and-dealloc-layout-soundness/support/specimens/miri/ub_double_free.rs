//! The same block is deallocated twice with its correct layout.
use std::alloc::{alloc, dealloc, Layout};

fn main() {
    unsafe {
        let l = Layout::from_size_align(8, 8).unwrap();
        let p = alloc(l);
        assert!(!p.is_null());
        dealloc(p, l);
        dealloc(p, l);
    }
}
