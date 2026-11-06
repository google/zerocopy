#![allow(dead_code)]

pub unsafe fn read_raw(ptr: *const u32) -> u32 {
    // This is deliberately unsupported by the selected Aeneas path.
    *ptr
}
