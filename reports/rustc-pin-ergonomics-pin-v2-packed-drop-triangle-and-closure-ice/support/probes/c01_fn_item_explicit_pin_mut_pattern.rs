// Control: an explicit `&pin mut` struct pattern in a plain function body.
#![feature(pin_ergonomics)]
#![allow(incomplete_features)]
#![forbid(unsafe_code)]
#![crate_type = "lib"]

#[pin_v2]
pub struct Pair {
    pub a: u32,
    pub b: u32,
}

pub fn f(q: &pin mut Pair) -> u32 {
    let &pin mut Pair { ref pin mut a, ref mut b } = q;
    *b += 1;
    *a + *b
}
