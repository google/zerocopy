// Gate: an unpinned `ref mut` binding below `&pin mut` requires the field type to be `Unpin`.
#![feature(pin_ergonomics)]
#![allow(incomplete_features)]
#![forbid(unsafe_code)]
#![crate_type = "lib"]

use std::marker::PhantomPinned;

#[pin_v2]
pub struct PinnedBox(pub PhantomPinned);

pub fn f(p: &pin mut PinnedBox) {
    let &pin mut PinnedBox(ref mut x) = p;
    let _ = x;
}
