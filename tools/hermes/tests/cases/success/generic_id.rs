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
///@ : generic_id.id x = ok x
///@ proof
///@   simp [generic_id.id]
pub fn id<T>(x: T) -> T {
    x
}
fn main() {}
