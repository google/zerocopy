// Gate: calling `Drop::pin_drop` explicitly.
#![feature(pin_ergonomics)]
#![allow(incomplete_features)]
#![forbid(unsafe_code)]
#![crate_type = "lib"]

#[pin_v2]
pub struct D(pub u32);

impl Drop for D {
    fn pin_drop(&pin mut self) {}
}

pub fn f(d: &pin mut D) {
    Drop::pin_drop(d);
}
