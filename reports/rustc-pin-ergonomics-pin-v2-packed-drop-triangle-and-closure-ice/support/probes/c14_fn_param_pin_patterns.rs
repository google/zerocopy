// `&pin` patterns in function parameters (the reproducer of rust-lang/rust issue 149225).
#![feature(pin_ergonomics)]
#![allow(incomplete_features)]
#![forbid(unsafe_code)]
#![crate_type = "lib"]

use std::pin::Pin;

pub fn patterns<'a>(&pin mut x: Pin<&mut i32>, &pin const y: Pin<&'a i32>) -> i32 {
    x + y
}
