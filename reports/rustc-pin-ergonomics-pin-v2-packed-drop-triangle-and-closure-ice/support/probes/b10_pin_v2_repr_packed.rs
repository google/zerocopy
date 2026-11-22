// Gate: `#[pin_v2]` on a `#[repr(packed)]` struct.
#![feature(pin_ergonomics)]
#![allow(incomplete_features)]
#![forbid(unsafe_code)]
#![crate_type = "lib"]

#[pin_v2]
#[repr(packed)]
pub struct PackedPin(pub u8, pub u32);
