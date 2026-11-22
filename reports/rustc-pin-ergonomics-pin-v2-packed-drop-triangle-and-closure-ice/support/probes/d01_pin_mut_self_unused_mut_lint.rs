// Incidental: compiled with lints enabled to record the `unused_mut` warning that the
// `&pin mut self` receiver sugar triggers although the source contains no removable `mut`
// binding.
#![feature(pin_ergonomics)]
#![allow(incomplete_features)]
#![forbid(unsafe_code)]
#![crate_type = "lib"]

#[pin_v2]
pub struct D(pub u32);

impl Drop for D {
    fn pin_drop(&pin mut self) {}
}
