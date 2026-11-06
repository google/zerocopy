#![allow(dead_code)]
pub mod left { pub fn step(x: u32) -> u32 { x.wrapping_add(1) } }
pub mod right { pub fn step(x: u32) -> u32 { x.wrapping_add(2) } }
pub fn both(x: u32) -> u32 { left::step(right::step(x)) }
#[cfg(test)] mod tests { use super::*; #[test] fn values() { assert_eq!(left::step(0), 1); assert_eq!(right::step(0), 2); assert_eq!(both(0), 3); } }
