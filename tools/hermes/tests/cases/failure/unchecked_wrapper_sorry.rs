#!/usr/bin/env cargo
//! ```cargo
//! [package]
//! name = "unchecked_wrapper"
//! version = "0.1.0"
//! edition = "2021"
//!
//! [dependencies]
//! ```

///@ lean spec raw_inc (x : U32)
///@ ensures |ret| ret.val = x.val + 1
///@ proof sorry
#[allow(unused_unsafe)]
unsafe fn raw_inc(x: u32) -> u32 {
    unsafe { x + 1 }
}

///@ lean spec safe_inc (x : U32)
///@ ensures |ret| if x.val < U32.rMax then ret.val = x.val + 1 else ret.val = 0
///@ proof
///@     simp [safe_inc]
///@     split
///@     case isTrue h =>
///@         have ⟨ret, h_call, h_val⟩ := raw_inc_spec x
///@         rw [h_call]
///@         simp_all
///@     case isFalse h =>
///@         simp
pub fn safe_inc(x: u32) -> u32 {
    if x < u32::MAX { unsafe { raw_inc(x) } } else { 0 }
}

fn main() {}
