#!/usr/bin/env cargo
//! ```cargo
//! [package]
//! name = "undefined_variable"
//! version = "0.1.0"
//! edition = "2021"
//!
//! [dependencies]
//! ```

///@ lean spec undefined_var (x : u32)
///@ ensures |ret| ret.val = y.val -- y is undefined
pub fn undefined_var(x: u32) -> u32 {
    x
}

fn main() {}
