#![allow(dead_code)]

/// An ordinary Rust doc comment with 🦀 and é.
///| by
///|   trivial
pub fn annotated() -> u32 { 3 }

/// First part of a combined proof.
///| by
///|   constructor
pub fn first() -> u32 { 1 }

/// Second part of a combined proof.
///|   · trivial
///|   · trivial
pub fn second() -> u32 { 2 }

macro_rules! emit_nested {
    () => {
        pub fn macro_generated() -> u32 {
            let nested = { let inner = 4; inner };
            nested
        }
    };
}
emit_nested!();
