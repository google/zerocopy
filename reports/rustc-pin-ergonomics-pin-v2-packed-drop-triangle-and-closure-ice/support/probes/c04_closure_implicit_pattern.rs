// Control: match-ergonomics projection (no explicit `&pin` pattern) inside a closure.
#![feature(pin_ergonomics)]
#![allow(incomplete_features)]
#![forbid(unsafe_code)]
#![crate_type = "lib"]

#[pin_v2]
pub struct Pair {
    pub a: u32,
    pub b: u32,
}

pub fn f(p: &pin mut Pair) -> u32 {
    let c = |q: &pin mut Pair| -> u32 {
        let Pair { a, b } = q;
        *a + *b
    };
    c(p)
}
