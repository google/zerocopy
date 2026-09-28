#![allow(dead_code)]
pub mod alpha { pub fn tick(x: u32) -> u32 { x.wrapping_add(1) } }
pub mod beta { pub fn tick(x: u32) -> u32 { x.wrapping_add(2) } }
pub fn call(x: u32) -> u32 { alpha::tick(x) }
