#![allow(dead_code)]

/// model-source-marker-A
pub fn step(x: u32) -> u32 {
    x.wrapping_add(1)
}

pub fn select(flag: bool, left: u32, right: u32) -> u32 {
    if flag { left } else { right }
}
