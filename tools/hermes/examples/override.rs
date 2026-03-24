// This example demonstrates how to override the auto-generated implicit
// `verify_is_valid` macro when Lean's `simp` tactic cannot automatically prove
// a type's structural invariant.
//
// By supplying a `proof unnamed` block, we manually construct the synthesized
// goal ourselves.

/// ```lean, hermes
/// proof unnamed
///   -- In a real scenario, this manual proof would be more complex and
///   -- potentially require importing additional user lemmas. Here we just
///   -- use `sorry` to prove the example point, but we must first configure
///   -- hermes to accept it with `--allow-sorry`.
///   intro_all
///   sorry
/// ```
pub fn do_something_complex(_x: u32) {}

fn main() {}
