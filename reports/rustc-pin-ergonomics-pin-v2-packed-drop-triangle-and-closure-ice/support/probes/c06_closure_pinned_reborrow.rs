// An implicit pinned reborrow at a coercion site inside a closure (no pattern involved).
#![feature(pin_ergonomics)]
#![allow(incomplete_features)]
#![forbid(unsafe_code)]
#![crate_type = "lib"]

pub fn f(p: &pin mut u32) -> u32 {
    let c = |q: &pin mut u32| -> u32 {
        let r: &pin mut u32 = q;
        *r
    };
    c(p)
}
