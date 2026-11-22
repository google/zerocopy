// Two overlapping implicit pinned reborrows of the same `&pin mut` variable in a plain
// function body. The expected borrow error names the reborrowed place, which shows how the
// reborrow is lowered (a mutable borrow of the dereferenced pointer field of `Pin`).
#![feature(pin_ergonomics)]
#![allow(incomplete_features)]
#![forbid(unsafe_code)]
#![crate_type = "lib"]

pub fn f(q: &pin mut u32) -> u32 {
    let r: &pin mut u32 = q;
    let s: &pin mut u32 = q;
    *r + *s
}
