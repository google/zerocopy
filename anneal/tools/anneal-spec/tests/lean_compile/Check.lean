-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- Pins the meaning of the helpers that `spec.rs` lowers into `Spec.lean`:
-- Rust's truncating `/` and `%`, two's-complement wrapping and saturation,
-- negation, `abs_diff`, the values of integer constants, and parameters that
-- must not capture the generated names they are named after.
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

-- A `match` takes the first arm whose pattern matches, through
-- or-patterns, constants, and name bindings.
example : pure_match_bucket 0 = 0 := by unfold pure_match_bucket; decide
example : pure_match_bucket 2 = 1 := by unfold pure_match_bucket; decide
example : pure_match_bucket 255 = 3 := by unfold pure_match_bucket; decide
example : pure_match_bucket 7 = 2 := by unfold pure_match_bucket; decide
example : pure_match_div_is 7 2 3 := by unfold pure_match_div_is; decide
example : ¬ pure_match_div_is 7 2 4 := by unfold pure_match_div_is; decide
example : pure_match_div_is 7 0 0 := by unfold pure_match_div_is; decide
example : ¬ pure_match_div_is 7 0 1 := by unfold pure_match_div_is; decide

-- A `bool` helper parameter is a `Prop`, so these are proved directly.
example : pure_match_flag_is True 1 :=
  ⟨fun _ => rfl, fun h => absurd True.intro h⟩
example : pure_match_flag_is False 0 :=
  ⟨fun h => absurd h id, fun _ => rfl⟩

-- `tiered` (sorted seventh as `fn6`) lowers
-- `max_steps = match n { 0 => 1, m => m * 2 }`.
example : fn6_max_steps { args := [u32Val 0, u8Val 0] } = 1 := rfl
example : fn6_max_steps { args := [u32Val 5, u8Val 0] } = 10 := rfl

-- Saturating arithmetic clamps the exact result to the type's range.
example : pure_sadd_is 200 100 255 := by unfold pure_sadd_is; decide
example : ¬ pure_sadd_is 200 100 44 := by unfold pure_sadd_is; decide
example : pure_sadd_is 1 2 3 := by unfold pure_sadd_is; decide
example : pure_ssub_is (-128) 1 (-128) := by unfold pure_ssub_is; decide
example : pure_ssub_is 127 (-1) 127 := by unfold pure_ssub_is; decide
example : pure_ssub_is 5 7 (-2) := by unfold pure_ssub_is; decide
example : ¬ pure_ssub_is (-128) 1 127 := by unfold pure_ssub_is; decide
example : pure_smul_is 300 300 32767 := by unfold pure_smul_is; decide
example : pure_smul_is (-300) 300 (-32768) := by unfold pure_smul_is; decide
example : pure_smul_is (-3) 4 (-12) := by unfold pure_smul_is; decide
example : pure_sneg_is (-128) 127 := by unfold pure_sneg_is; decide
example : pure_sneg_is 127 (-127) := by unfold pure_sneg_is; decide
example : pure_sneg_is 0 0 := by unfold pure_sneg_is; decide
example : ¬ pure_sneg_is (-128) (-128) := by unfold pure_sneg_is; decide

-- Negation wraps, and overflows, only at the edge of the type's range: at
-- every nonzero value of an unsigned type and at `MIN` of a signed one.
example : pure_wneg_u_is 1 255 := by unfold pure_wneg_u_is; decide
example : pure_wneg_u_is 0 0 := by unfold pure_wneg_u_is; decide
example : pure_wneg_i_is (-128) (-128) := by unfold pure_wneg_i_is; decide
example : pure_wneg_i_is 5 (-5) := by unfold pure_wneg_i_is; decide
example : pure_neg_ok_u 0 := by unfold pure_neg_ok_u; decide
example : ¬ pure_neg_ok_u 1 := by unfold pure_neg_ok_u; decide
example : pure_neg_ok_i 127 := by unfold pure_neg_ok_i; decide
example : pure_neg_ok_i (-127) := by unfold pure_neg_ok_i; decide
example : ¬ pure_neg_ok_i (-128) := by unfold pure_neg_ok_i; decide

-- `abs_diff` is exact even between the extremes of a signed type.
example : pure_diff_i_is (-128) 127 255 := by unfold pure_diff_i_is; decide
example : pure_diff_i_is 127 (-128) 255 := by unfold pure_diff_i_is; decide
example : pure_diff_i_is 3 3 0 := by unfold pure_diff_i_is; decide
example : ¬ pure_diff_i_is (-128) 127 1 := by unfold pure_diff_i_is; decide
example : pure_diff_u_is 0 4294967295 4294967295 := by unfold pure_diff_u_is; decide
example : pure_diff_u_is 9 2 7 := by unfold pure_diff_u_is; decide

-- Had the binder of the inner saturating result captured the parameter
-- `saturating`, these would differ.
example : pure_sat_nested 3 = 7 := by unfold pure_sat_nested; decide
example : pure_sat_nested 100 = 201 := by unfold pure_sat_nested; decide
example : pure_sat_nested 200 = 255 := by unfold pure_sat_nested; decide

-- `usat` (sorted eighth as `fn7`) lowers
-- `max_steps = abs_diff(a, b) + saturating_add(n, 1u32)`.
example : fn7_max_steps { args := [u8Val 9, u8Val 2, u32Val 5] } = 13 := rfl
example : fn7_max_steps { args := [u8Val 3, u8Val 250, u32Val 4294967295] } =
    4294967542 := rfl

end Spec.Check
