#![allow(dead_code)]

/// model-source-marker-B
pub fn step(x: u32) -> u32 {
    x.wrapping_add(2)
}

pub fn select(flag: bool, left: u32, right: u32) -> u32 {
    if flag { left } else { right }
}
