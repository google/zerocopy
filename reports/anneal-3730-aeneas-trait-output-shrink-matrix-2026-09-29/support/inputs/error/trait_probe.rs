#![allow(dead_code)]
pub trait Step { fn step(self) -> u32; }
impl Step for u32 { fn step(self) -> u32 { self.wrapping_add(1) } }
pub fn use_step(x: u32) -> u32 { x.step() }
pub fn bad(p: *mut u32) -> u32 { unsafe { *p } }
