// Control for b03: the same pattern with an `Unpin` field type is accepted.
#![feature(pin_ergonomics)]
#![allow(incomplete_features)]
#![forbid(unsafe_code)]
#![crate_type = "lib"]

#[pin_v2]
pub struct UnpinBox(pub u32);

pub fn f(p: &pin mut UnpinBox) -> u32 {
    let &pin mut UnpinBox(ref mut x) = p;
    *x += 1;
    *x
}
