#!/usr/bin/env cargo
//! ```cargo
//! [package]
//! name = "generic_id"
//! version = "0.1.0"
//! edition = "2021"
//!
//! [dependencies]
//! ```

///@ lean spec id (x : T)
///@ ensures |ret| ret = x
///@ proof
///@   simp [id]
pub fn id<T>(x: T) -> T {
    x
}

fn main() {}
