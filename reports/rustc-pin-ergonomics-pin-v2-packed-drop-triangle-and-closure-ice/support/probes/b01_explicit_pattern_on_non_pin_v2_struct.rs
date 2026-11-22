// Gate: explicit `&pin mut` projection through a struct that is not `#[pin_v2]`.
#![feature(pin_ergonomics)]
#![allow(incomplete_features)]
#![forbid(unsafe_code)]
#![crate_type = "lib"]

pub struct Plain(pub u32);

pub fn f(p: &pin mut Plain) {
    let &pin mut Plain(ref pin mut x) = p;
    let _ = x;
}
