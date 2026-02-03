#!/usr/bin/env cargo
//! ```cargo
//! [package]
//! name = "incorrect_proof"
//! version = "0.1.0"
//! edition = "2021"
//!
//! [dependencies]
//! ```

///@ lean spec incorrect (x : U32)
///@ ensures |ret| ret.val = x.val + 1
///@ proof
///@   simp [incorrect]
///@   -- Error: x != x + 1, so this goal remains unsolved
pub fn incorrect(x: u32) -> u32 {
    x
}

fn main() {}
