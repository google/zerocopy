#![allow(dead_code)]
pub fn captured(x: u32) -> u32 { let f = |y: u32| x.wrapping_add(y); f(2) }
