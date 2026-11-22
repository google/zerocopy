// Control: a type that is not `#[pin_v2]` may implement only `pin_drop`.
#![feature(pin_ergonomics)]
#![allow(incomplete_features)]
#![forbid(unsafe_code)]
#![crate_type = "lib"]

pub struct NotMarked(pub u32);

impl Drop for NotMarked {
    fn pin_drop(&pin mut self) {}
}
