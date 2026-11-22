// The pattern of c02 applied to a captured variable instead of a closure parameter.
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
    let mut c = move || -> u32 {
        let &pin mut Pair { ref pin mut a, ref mut b } = p;
        *b += 1;
        *a + *b
    };
    c()
}
