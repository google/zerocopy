#![allow(dead_code)]
pub mod moved {
    pub mod core {
        pub fn use_step(x: u32) -> u32 { x.wrapping_add(1) }
    }
}
pub fn caller(x: u32) -> u32 { moved::core::use_step(x) }
