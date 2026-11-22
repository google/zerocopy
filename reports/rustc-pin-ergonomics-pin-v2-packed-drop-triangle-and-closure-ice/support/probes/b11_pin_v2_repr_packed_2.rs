// Gate: `#[pin_v2]` on a `#[repr(C, packed(2))]` struct.
#![feature(pin_ergonomics)]
#![allow(incomplete_features)]
#![forbid(unsafe_code)]
#![crate_type = "lib"]

#[pin_v2]
#[repr(C, packed(2))]
pub struct PackedPin2(pub u16, pub u32);
