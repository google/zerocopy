// Control: the `#[pin_v2]` attribute and the `&pin mut` type syntax without the feature gate.
#![forbid(unsafe_code)]
#![crate_type = "lib"]

#[pin_v2]
pub struct Marked(pub u32);

pub fn f(_: &pin mut Marked) {}
