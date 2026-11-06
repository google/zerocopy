#![allow(dead_code)]
pub unsafe fn load(p: *const u32) -> u32 { unsafe { *p } }
