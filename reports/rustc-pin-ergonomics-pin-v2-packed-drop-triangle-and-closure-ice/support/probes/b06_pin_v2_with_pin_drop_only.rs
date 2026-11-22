// Control for b05: a `#[pin_v2]` type that implements only `Drop::pin_drop(&pin mut self)`.
#![feature(pin_ergonomics)]
#![allow(incomplete_features)]
#![forbid(unsafe_code)]
#![crate_type = "lib"]

#[pin_v2]
pub struct OnlyPinDrop(pub u32);

impl Drop for OnlyPinDrop {
    fn pin_drop(&pin mut self) {}
}
