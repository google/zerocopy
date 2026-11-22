// The borrow expression `&pin mut place` on a local of a `!Unpin` type, followed by a use of
// the local after the pinned borrow has ended. Records whether the compiler lets the value be
// moved after it was pinned in place.
#![feature(pin_ergonomics)]
#![allow(incomplete_features)]
#![forbid(unsafe_code)]
#![crate_type = "lib"]

use std::marker::PhantomPinned;
use std::pin::Pin;

pub struct NotUnpin(pub u32, pub PhantomPinned);

fn observe(_: Pin<&mut NotUnpin>) {}

pub fn f() -> NotUnpin {
    let mut x = NotUnpin(1, PhantomPinned);
    observe(&pin mut x);
    x
}
