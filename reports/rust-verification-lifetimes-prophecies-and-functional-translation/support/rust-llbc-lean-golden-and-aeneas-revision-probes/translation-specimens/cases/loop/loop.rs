#![allow(dead_code)]
pub fn sum_to(n: u32) -> u32 { let mut x = 0u32; let mut i = 0u32; while i < n { x = x.wrapping_add(i); i = i.wrapping_add(1); } x }
