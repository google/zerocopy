#![allow(dead_code)]
pub fn old(x: u32) -> u32 { x.wrapping_add(2) }
pub trait Step { fn step(self) -> u32; }
impl Step for u32 { fn step(self) -> u32 { self.wrapping_add(1) } }
unsafe extern "C" { fn external_double(x: u32) -> u32; }
pub fn external_call(x: u32) -> u32 { unsafe { external_double(x) } }
pub fn use_step(x: u32) -> u32 { x.step() }
