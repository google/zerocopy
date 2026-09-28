#![allow(dead_code)]
pub fn choose(b: bool, x: u32, y: u32) -> u32 { if b { x } else { y } }
pub fn bump(x: &mut u32) { *x = x.wrapping_add(1); }
