#![allow(dead_code)]
pub fn choose(x: u32) -> u32 { if x == 0 { twice(1) } else { inc(x) } }
pub fn twice(x: u32) -> u32 { inc(inc(x)) }
pub fn inc(x: u32) -> u32 { x.wrapping_add(1) }
