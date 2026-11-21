// Expected to be REJECTED: `#[rustc_force_inline]` on a function whose body contains
// a tail call. This exercises the definition-site validity check that the MIR inliner
// shares with its per-call-site check.
#![crate_type = "lib"]
#![feature(explicit_tail_calls, rustc_attrs)]
#![allow(incomplete_features, internal_features)]

#[inline(never)]
pub fn leaf(x: u64) -> u64 {
    x
}

#[rustc_force_inline]
pub fn forced(x: u64) -> u64 {
    become leaf(x)
}

pub fn caller(x: u64) -> u64 {
    forced(x)
}
