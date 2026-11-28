-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- Pins the meaning of the helpers that `spec.rs` lowers into `Spec.lean`:
-- Rust's truncating `/` and `%`, two's-complement wrapping, the values of
-- integer constants, and parameters that must not capture the generated names
-- they are named after.
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

-- Integer constants lower to their values on the profile v1 target, where
-- `usize` and `isize` are 64 bits wide and `T::BITS` is the bit width.
example : pure_consts_are 18446744073709551615 (-9223372036854775808) (-128)
    340282366920938463463374607431768211455 64 := by
  unfold pure_consts_are; decide
example : ¬ pure_consts_are 4294967295 (-9223372036854775808) (-128)
    340282366920938463463374607431768211455 64 := by
  unfold pure_consts_are; decide
example : ¬ pure_consts_are 18446744073709551615 (-9223372036854775808) (-128)
    340282366920938463463374607431768211455 32 := by
  unfold pure_consts_are; decide

-- `consts` (sorted second as `fn1`) lowers
-- `max_steps = u8::MAX + u32::BITS * 2 + n / u16::MAX`:
-- `255 + 32 * 2 + 131070 / 65535 = 255 + 64 + 2 = 321`.
example : fn1_max_steps { args := [u64Usize 131070] } = 321 := rfl

-- An `if` that chooses a value takes the branch its condition selects,
-- through an `else if` chain.
example : pure_clamp (-5) 0 10 = 0 := by unfold pure_clamp; decide
example : pure_clamp 15 0 10 = 10 := by unfold pure_clamp; decide
example : pure_clamp 7 0 10 = 7 := by unfold pure_clamp; decide
example : pure_sign_is (-3) (-1) := by unfold pure_sign_is; decide
example : ¬ pure_sign_is (-3) 1 := by unfold pure_sign_is; decide
example : pure_sign_is 0 0 := by unfold pure_sign_is; decide
example : pure_sign_is 9 1 := by unfold pure_sign_is; decide

-- A `bool`-valued `if` constrains only the branch its condition selects.
example : pure_div_or_zero_is 7 0 0 := by unfold pure_div_or_zero_is; decide
example : ¬ pure_div_or_zero_is 7 0 1 := by unfold pure_div_or_zero_is; decide
example : pure_div_or_zero_is 7 2 3 := by unfold pure_div_or_zero_is; decide
example : ¬ pure_div_or_zero_is 7 2 4 := by unfold pure_div_or_zero_is; decide

-- A `bool` helper parameter is a `Prop`, so these are proved directly.
example : pure_flag_is True 1 :=
  ⟨fun _ => rfl, fun h => absurd True.intro h⟩
example : pure_flag_is False 0 :=
  ⟨fun h => absurd h id, fun _ => rfl⟩
example : ¬ pure_flag_is True 0 := fun h => absurd (h.1 True.intro) (by decide)

-- `piecewise` (sorted fifth as `fn4`) lowers
-- `max_steps = if n > 100 { n } else { 100 }`.
private def u32Val (n : Nat) : Trusted.MirSemantics.Val :=
  .scalar ⟨.i32, false, BitVec.ofNat 128 n⟩

example : fn4_max_steps { args := [u32Val 250, .bool true] } = 250 := rfl
example : fn4_max_steps { args := [u32Val 7, .bool true] } = 100 := rfl

-- A `let` binding takes its initializer's value in the rest of its block,
-- including in helper bodies and `if` branches.
example : pure_let_sum_is 2 3 5 := by unfold pure_let_sum_is; decide
example : ¬ pure_let_sum_is 2 3 6 := by unfold pure_let_sum_is; decide
example : pure_let_pick 20 = 9 := by unfold pure_let_pick; decide
example : pure_let_pick 4 = 4 := by unfold pure_let_pick; decide
example : pure_let_div_is 7 2 3 := by unfold pure_let_div_is; decide
example : ¬ pure_let_div_is 7 2 4 := by unfold pure_let_div_is; decide
example : pure_let_div_is 7 0 0 := by unfold pure_let_div_is; decide
example : ¬ pure_let_div_is 7 0 1 := by unfold pure_let_div_is; decide

example : pure_let_guarded_pick 6 2 = 1 := by unfold pure_let_guarded_pick; decide
example : pure_let_guarded_pick 1 2 = 0 := by unfold pure_let_guarded_pick; decide
example : pure_let_guarded_pick 6 0 = 2 := by unfold pure_let_guarded_pick; decide
example : pure_let_math_cond_is 5 1 := by unfold pure_let_math_cond_is; decide
example : pure_let_math_cond_is 0 0 := by unfold pure_let_math_cond_is; decide
example : ¬ pure_let_math_cond_is 5 0 := by unfold pure_let_math_cond_is; decide

-- `stepped` (sorted sixth as `fn5`) lowers `max_steps` with two `let`s:
-- `max(2 * n, 7)`.
private def u8Val (n : Nat) : Trusted.MirSemantics.Val :=
  .scalar ⟨.i8, false, BitVec.ofNat 128 n⟩

example : fn5_max_steps { args := [u32Val 10, u8Val 0] } = 20 := rfl
example : fn5_max_steps { args := [u32Val 2, u8Val 0] } = 7 := rfl

end Spec.Check
