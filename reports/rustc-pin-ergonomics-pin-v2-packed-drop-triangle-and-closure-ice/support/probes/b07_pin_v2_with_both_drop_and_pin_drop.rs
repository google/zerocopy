// Gate: a `#[pin_v2]` type that implements both `drop` and `pin_drop`.
#![feature(pin_ergonomics)]
#![allow(incomplete_features)]
#![forbid(unsafe_code)]
#![crate_type = "lib"]

#[pin_v2]
pub struct BothDrops(pub u32);

impl Drop for BothDrops {
    fn drop(&mut self) {}
    fn pin_drop(&pin mut self) {}
}
