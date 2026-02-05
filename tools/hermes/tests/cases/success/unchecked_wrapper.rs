#!/usr/bin/env cargo
//! ```cargo
//! [package]
//! name = "unchecked_wrapper"
//! version = "0.1.0"
//! edition = "2021"
//! 
//! [dependencies]
//! ```

/*@ lean
<<<<<<< Updated upstream
spec raw_inc (x : U32)
: ∃ ret, raw_inc x = ok ret ∧ ret.val = x.val + 1
=======
model raw_inc (x : u32)
requires h_safe : x.val < 4294967295
ensures |ret| ret.val = x.val + 1
>>>>>>> Stashed changes
@*/
#[allow(unused_unsafe)]
unsafe fn raw_inc(x: u32) -> u32 {
    unsafe { x + 1 }
}

/*@ lean
<<<<<<< Updated upstream
spec safe_inc (x : U32)
: ∃ ret, safe_inc x = ok ret ∧
  (if x.val < 4294967295 then ret.val = x.val + 1 else ret.val = 0)
@*/
/*@ proof
  sorry
=======
spec safe_inc (x : u32)
    ensures |ret|
    if x.val < 4294967295 then ret.val = x.val + 1 else ret.val = 0
@*/
/*@ proof
:= by
    simp [safe_inc]
    split
    case inl h =>
        simp [raw_inc]
        simp [h]
    case inr h =>
        simp
>>>>>>> Stashed changes
@*/
pub fn safe_inc(x: u32) -> u32 {
    if x < u32::MAX {
        unsafe { raw_inc(x) }
    } else {
        0
    }
}
fn main() {}
