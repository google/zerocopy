// Gate: an explicit `Unpin` impl for a `#[pin_v2]` type.
#![feature(pin_ergonomics)]
#![allow(incomplete_features)]
#![forbid(unsafe_code)]
#![crate_type = "lib"]

use std::marker::PhantomPinned;

#[pin_v2]
pub struct Manual(pub PhantomPinned);

impl Unpin for Manual {}
