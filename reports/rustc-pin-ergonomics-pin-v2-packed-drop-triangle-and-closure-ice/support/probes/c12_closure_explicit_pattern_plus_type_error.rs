// c02 plus an unrelated type error: the delayed bug is not reported when a real error is.
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
        let _: () = 1u8;
        *a + *b
    };
    c(p)
}
