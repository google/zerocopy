#![feature(contracts)]
#![allow(unused)]

use core::contracts::ensures;

// Probe for rust-lang/rust#139548: outer block in #[ensures({ *x = 0; move |_| true })]
// under -Zcontract-checks=no!
#[ensures({ *x = 0; move |_| true })]
pub fn side_effect_ensures_139548(x: &mut u32) -> u32 {
    *x
}
