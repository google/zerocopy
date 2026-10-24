#![no_std]

#[inline(never)]
pub fn ub_boundary_probe(ptr: *const u32, flag: bool) -> u32 {
    let _ = unsafe { *ptr };
    if flag {} else {}
    0
}

#[inline(never)]
pub fn match_wildcard_probe(ptr: *const u32, flag: bool) -> u32 {
    unsafe {
        match *ptr {
            _ => {}
        }
    }
    if flag {} else {}
    0
}

#[inline(never)]
pub fn assign_underscore_probe(ptr: *const u32) -> u32 {
    unsafe {
        _ = *ptr;
    }
    0
}
