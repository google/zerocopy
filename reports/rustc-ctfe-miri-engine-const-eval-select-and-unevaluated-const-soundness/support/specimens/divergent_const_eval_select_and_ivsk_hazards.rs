#![feature(core_intrinsics, const_eval_select)]
#![allow(internal_features)]

use core::intrinsics::{const_eval_select, is_val_statically_known};

const fn ct_branch(_p: *const u64) -> u64 {
    0
}

fn rt_branch(p: *const u64) -> u64 {
    // Observes concrete pointer alignment / returns non-zero value, violating the relational
    // simulation contract of `const_eval_select` while remaining memory-safe in both arms.
    if p.addr().is_multiple_of(8) { 1 } else { 2 }
}

pub const fn buggy_select(r: &u64) -> u64 {
    const_eval_select((r as *const u64,), ct_branch, rt_branch)
}

pub const CT_OBSERVED: u64 = {
    let x = 42_u64;
    buggy_select(&x)
};

#[inline]
pub fn buggy_ivsk_branch(x: usize) -> u64 {
    if is_val_statically_known(x) { 100 } else { 200 }
}

fn main() {
    let x = 42_u64;
    let rt_observed = buggy_select(&x);
    let ivsk_observed = buggy_ivsk_branch(42);
    println!(
        "CE1_CT={} CE1_RT={} CE3_IVSK={}",
        CT_OBSERVED, rt_observed, ivsk_observed
    );
}
