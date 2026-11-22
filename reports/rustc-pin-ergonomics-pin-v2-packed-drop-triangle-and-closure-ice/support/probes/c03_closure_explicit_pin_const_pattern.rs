// An explicit `&pin const` struct pattern inside a closure.
#![feature(pin_ergonomics)]
#![allow(incomplete_features)]
#![forbid(unsafe_code)]
#![crate_type = "lib"]

#[pin_v2]
pub struct Pair {
    pub a: u32,
    pub b: u32,
}

pub fn f(p: &pin const Pair) -> u32 {
    let c = |q: &pin const Pair| -> u32 {
        let &pin const Pair { ref pin const a, ref b } = q;
        *a + *b
    };
    c(p)
}
