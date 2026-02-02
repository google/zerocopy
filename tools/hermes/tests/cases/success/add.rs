#!/usr/bin/env cargo
//! ```cargo
//! [package]
//! name = "test_case"
//! version = "0.1.0"
//! edition = "2021"
//!
//! [dependencies]
//! ```

///@ lean spec add (a b : U32)
///@ ensures |ret| ret.val = (a.val + b.val) % U32.size
///@ proof
///@   simp [add]
pub fn add(a: u32, b: u32) -> u32 {
    a.wrapping_add(b)
}

fn main() {
    let _ = add(1, 2);
}
