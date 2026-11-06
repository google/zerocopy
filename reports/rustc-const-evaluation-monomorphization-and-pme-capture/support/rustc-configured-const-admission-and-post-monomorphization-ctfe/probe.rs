#![no_std]

pub trait Bound {
    const LIMIT: usize;

    fn marker() -> u8;
}

pub struct A;
pub struct B;

impl Bound for A {
    const LIMIT: usize = 1;

    #[inline(never)]
    fn marker() -> u8 {
        0xA1
    }
}

impl Bound for B {
    const LIMIT: usize = 0;

    #[inline(never)]
    fn marker() -> u8 {
        0xB0
    }
}

#[inline(never)]
pub fn checked<T: Bound, const N: usize>() -> u8 {
    const {
        assert!(N <= <T as Bound>::LIMIT);
    };
    <T as Bound>::marker()
}

#[cfg(probe_case = "a1")]
pub type Selected = A;

#[cfg(any(
    probe_case = "b0",
    probe_case = "b1",
    probe_case = "unused_b1"
))]
pub type Selected = B;

#[cfg(any(probe_case = "a1", probe_case = "b1"))]
pub fn entry() -> u8 {
    checked::<Selected, 1>()
}

#[cfg(any(probe_case = "b0", probe_case = "unused_b1"))]
pub fn entry() -> u8 {
    checked::<Selected, 0>()
}

// This private generic wrapper is never called or explicitly instantiated here.
// Its B1 call remains in the configured source for the unused-instance control.
#[cfg(probe_case = "unused_b1")]
#[allow(dead_code)]
fn never_instantiated<U>() -> u8 {
    checked::<B, 1>()
}
