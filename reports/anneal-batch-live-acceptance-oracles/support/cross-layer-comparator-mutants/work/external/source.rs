#![allow(dead_code)]
unsafe extern "C" { fn external_double(x: u32) -> u32; }
pub fn call(x: u32) -> u32 { unsafe { external_double(x) } }
