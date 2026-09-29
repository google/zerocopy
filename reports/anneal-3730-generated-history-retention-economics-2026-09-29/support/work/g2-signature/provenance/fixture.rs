#![allow(dead_code)]
pub mod core {
    pub trait Step { fn step(self, delta: u32) -> u32; }
    impl Step for u32 { fn step(self, delta: u32) -> u32 { self.wrapping_add(delta) } }
    pub fn use_step(x: u32) -> u32 { x.step(1) }
}
pub mod side {
    pub fn untouched(x: u32) -> u32 { x.wrapping_add(10) }
}
pub fn combine(x: u32) -> u32 { core::use_step(x).wrapping_add(side::untouched(x)) }
