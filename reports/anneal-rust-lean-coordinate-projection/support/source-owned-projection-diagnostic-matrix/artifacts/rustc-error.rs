#![allow(dead_code)]

/// A Rust doc comment carrying an illustrative proof payload.
///| by
///|   /- 🦀 é -/ trivial
pub fn step(x: u32) -> u32 {
    "wrong"
}

/// A second authored payload.
///| by
///|   trivial
pub fn select(flag: bool, left: u32, right: u32) -> u32 {
    if flag { left } else { right }
}

macro_rules! emit_helper {
    () => {
        pub fn macro_generated(x: u32) -> u32 { x.wrapping_add(3) }
    };
}
emit_helper!();
