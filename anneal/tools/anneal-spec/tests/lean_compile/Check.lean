-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- Pins the meaning of the helpers that `spec.rs` lowers into `Spec.lean`:
-- Rust's truncating `/` and `%`, two's-complement wrapping, and parameters
-- that must not capture the generated names they are named after.
prelude
import Spec

namespace Spec.Check

open Spec

example : pure_one = 1 := rfl

-- `/` and `%` truncate towards zero.
example : pure_tdiv_is (-7) 2 (-3) := by unfold pure_tdiv_is; decide
example : ¬ pure_tdiv_is (-7) 2 (-4) := by unfold pure_tdiv_is; decide
example : pure_tdiv_is 7 (-2) (-3) := by unfold pure_tdiv_is; decide
example : pure_tmod_is (-7) 2 (-1) := by unfold pure_tmod_is; decide
example : ¬ pure_tmod_is (-7) 2 1 := by unfold pure_tmod_is; decide
example : pure_tmod_is 7 (-2) 1 := by unfold pure_tmod_is; decide

-- Wrapping arithmetic reduces into the type's range.
example : pure_wadd_is 200 100 44 := by unfold pure_wadd_is; decide
example : pure_wsub_is (-128) 1 127 := by unfold pure_wsub_is; decide
example : pure_wsub_is 127 (-1) (-128) := by unfold pure_wsub_is; decide
example : pure_wmul_is 300 300 24464 := by unfold pure_wmul_is; decide

-- Had the parameter `pure_one` captured `Spec.pure_one`, the first argument
-- would be unconstrained. (Had `intTdiv` or `intTmod` captured the operator
-- helpers, `Spec.lean` would not have compiled.)
example : pure_no_capture 1 5 8 3 0 0 := by unfold pure_no_capture; decide
example : ¬ pure_no_capture 2 5 8 3 0 0 := by unfold pure_no_capture; decide
example : ¬ pure_no_capture 1 5 7 3 0 0 := by unfold pure_no_capture; decide
example : ¬ pure_no_capture 1 5 8 3 1 0 := by unfold pure_no_capture; decide
example : ¬ pure_no_capture 1 5 8 3 0 (-1) := by unfold pure_no_capture; decide

-- `Val` has no `DecidableEq`, so this one is proved directly.
example : pure_unit_eq 0 := by unfold pure_unit_eq; exact ⟨rfl, rfl⟩

-- `bounded` (sorted first as `fn0`) lowers `max_steps` to an exact `Nat`
-- formula over unsigned `Val` arguments:
-- `34 * 10 + 10 / 3 + 10 % 2 + wrapping_add(1, 1) + 540 = 340 + 3 + 0 + 2 + 540 = 885`.
private def u64Usize (n : Nat) : Trusted.MirSemantics.Val :=
  .scalar ⟨.isize, false, BitVec.ofNat 128 n⟩

example : fn0_max_steps { args := [u64Usize 10, u64Usize 3] } = 885 := rfl

end Spec.Check
