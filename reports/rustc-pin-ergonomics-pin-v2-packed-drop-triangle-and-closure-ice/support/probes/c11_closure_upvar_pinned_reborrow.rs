// An implicit pinned reborrow of a captured variable inside a closure.
#![feature(pin_ergonomics)]
#![allow(incomplete_features)]
#![forbid(unsafe_code)]
#![crate_type = "lib"]

#[pin_v2]
pub struct Pair {
    pub a: u32,
    pub b: u32,
}

fn take(_: &pin mut Pair) {}

pub fn f(mut p: &pin mut Pair) {
    let mut c = || take(p);
    c();
}
