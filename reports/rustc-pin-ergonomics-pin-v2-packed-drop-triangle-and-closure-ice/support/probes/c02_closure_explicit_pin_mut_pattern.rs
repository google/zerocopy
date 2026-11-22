// The same body as c01 inside a closure; the scrutinee is the closure's own parameter.
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
        let &pin mut Pair { ref pin mut a, ref mut b } = q;
        *b += 1;
        *a + *b
    };
    c(p)
}
