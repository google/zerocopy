#!/usr/bin/env cargo
//! ```cargo
//! [package]
//! edition = "2021"
//! 
//! [dependencies]
//! ```

/*@ lean
spec checked_add (a b : U32)
: ∃ ret, checked_add a b = ok ret ∧
  (match ret with
  | none => a.val + b.val > 4294967295 
  | some r => r.val = a.val + b.val)
@*/
/*@ proof
  sorry
@*/
pub fn checked_add(a: u32, b: u32) -> Option<u32> {
    a.checked_add(b)
}
fn main() {}
