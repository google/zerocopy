
use std::ptr::NonNull;

pub struct Pointers {
    pub a: *const u8,
    pub b: *mut u8,
    pub c: NonNull<u8>,
}

pub fn ptr_arg(p: *const u8) -> *const u8 {
    p
}
