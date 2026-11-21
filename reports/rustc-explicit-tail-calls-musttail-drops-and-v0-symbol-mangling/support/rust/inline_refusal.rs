// MIR-inliner behaviour on a callee whose body ends in `become`, with a control
// callee that is identical except that it uses an ordinary call.
//
// Both helpers are `#[inline(always)]`. The probe inspects the optimized MIR of the
// two `caller_of_*` functions: a helper that was MIR-inlined no longer appears as a
// call terminator in its caller.
#![crate_type = "lib"]
#![feature(explicit_tail_calls)]
#![allow(incomplete_features)]

#[inline(never)]
pub fn leaf(x: u64) -> u64 {
    std::hint::black_box(x).wrapping_mul(3)
}

#[inline(always)]
pub fn helper_become(x: u64) -> u64 {
    become leaf(x)
}

#[inline(always)]
pub fn helper_plain(x: u64) -> u64 {
    leaf(x)
}

pub fn caller_of_become(x: u64) -> u64 {
    helper_become(x).wrapping_add(1)
}

pub fn caller_of_plain(x: u64) -> u64 {
    helper_plain(x).wrapping_add(1)
}
