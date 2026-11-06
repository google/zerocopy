#![allow(dead_code)]
pub fn inc(x: u32) -> u32 { x.wrapping_add(1) }
pub fn twice(x: u32) -> u32 { inc(inc(x)) }
pub fn choose(x: u32) -> u32 { if x == 0 { twice(1) } else { inc(x) } }
