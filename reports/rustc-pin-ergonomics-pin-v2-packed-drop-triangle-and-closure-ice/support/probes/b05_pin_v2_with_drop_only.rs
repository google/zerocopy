// Gate: a `#[pin_v2]` type that implements `Drop::drop(&mut self)`.
#![feature(pin_ergonomics)]
#![allow(incomplete_features)]
#![forbid(unsafe_code)]
#![crate_type = "lib"]

#[pin_v2]
pub struct OnlyDrop(pub u32);

impl Drop for OnlyDrop {
    fn drop(&mut self) {}
}
