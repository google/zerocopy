#![allow(dead_code)]
pub type Count = u32;
pub fn inc(x: Count) -> Count { x.wrapping_add(1) }
