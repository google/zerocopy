#!/usr/bin/env cargo
//! ```cargo
//! [package]
//! name = "syntax_error_in_spec"
//! version = "0.1.0"
//! edition = "2021"
//! 
//! [dependencies]
//! ```

///@ lean spec syntax_error (x : U32)
///@ ensures |ret| ((((
pub fn syntax_error(x: u32) -> u32 {
    x
}

fn main() {}
