// Gate: implementing both methods is rejected for a type that is not `#[pin_v2]` as well.
#![feature(pin_ergonomics)]
#![allow(incomplete_features)]
#![forbid(unsafe_code)]
#![crate_type = "lib"]

pub struct BothDrops(pub u32);

impl Drop for BothDrops {
    fn drop(&mut self) {}
    fn pin_drop(&pin mut self) {}
}
