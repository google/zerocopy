// Control: implicit pinned reborrows at coercion sites in a plain function body.
#![feature(pin_ergonomics)]
#![allow(incomplete_features)]
#![forbid(unsafe_code)]
#![crate_type = "lib"]

fn take(_: &pin mut u32) {}

pub fn f(mut q: &pin mut u32) -> u32 {
    take(q);
    take(q);
    *q
}
