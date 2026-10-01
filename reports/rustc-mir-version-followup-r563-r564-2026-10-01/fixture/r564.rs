#![allow(dead_code)]

pub union Bits {
    pub word: u32,
    pub bytes: [u8; 4],
}

pub static mut COUNTER: u32 = 7;

pub unsafe fn unsafe_add(x: u32) -> u32 { x + 1 }

pub fn operations(p: *const u32, q: &u32) -> u32 {
    let raw = &raw const *q;
    let loaded = unsafe { *p };
    let unioned = unsafe { Bits { word: loaded }.word };
    let called = unsafe { unsafe_add(unioned) };
    let static_value = unsafe { COUNTER };
    unsafe { core::arch::asm!("nop"); }
    let _ = raw;
    called + static_value
}

pub unsafe fn copy_one(src: *const u8, dst: *mut u8) {
    unsafe { core::ptr::copy_nonoverlapping(src, dst, 1); }
}
