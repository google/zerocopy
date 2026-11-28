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

-- Bitwise operators act on two's-complement bits.
example : pure_bits_u_is 0xF0 0x3C 0x30 0xFC 0xCC 0x0F := by unfold pure_bits_u_is; decide
example : ¬ pure_bits_u_is 0xF0 0x3C 0x30 0xFC 0xCC 0xF0 := by unfold pure_bits_u_is; decide
example : pure_bits_i_is (-8) 3 0 (-5) (-5) 7 := by unfold pure_bits_i_is; decide
example : pure_bits_i_is (-128) (-1) (-128) (-1) 127 127 := by unfold pure_bits_i_is; decide
example : ¬ pure_bits_i_is (-8) 3 0 (-5) (-5) (-7) := by unfold pure_bits_i_is; decide

-- `<<` drops the bits shifted past the width, and `>>` is logical on
-- unsigned and arithmetic on signed types.
example : pure_shifts_u 0b10110001 = 0b10001101 := by unfold pure_shifts_u; decide
example : pure_shifts_i 64 = -128 := by unfold pure_shifts_i; decide
example : pure_shifts_i (-128) = -1 := by unfold pure_shifts_i; decide
example : pure_shifts_i (-3) = 5 := by unfold pure_shifts_i; decide
example : pure_shl_i 64 = -128 := by unfold pure_shl_i; decide
example : pure_shl_i (-128) = 0 := by unfold pure_shl_i; decide
example : pure_shl_i (-3) = -6 := by unfold pure_shl_i; decide
example : pure_shifts_let 1000 = 2000 := by unfold pure_shifts_let; decide
example : pure_shifts_let (-1000) = -2000 := by unfold pure_shifts_let; decide
example : pure_shifts_let 0x7FF8 = -16 := by unfold pure_shifts_let; decide

-- `as` keeps a value that fits and otherwise reduces it modulo `2^bits`.
example : pure_cast_u8 300 = 44 := by unfold pure_cast_u8; decide
example : pure_cast_u8 (-1) = 255 := by unfold pure_cast_u8; decide
example : pure_cast_u8 255 = 255 := by unfold pure_cast_u8; decide
example : pure_cast_i8 200 = -56 := by unfold pure_cast_i8; decide
example : pure_cast_i8 128 = -128 := by unfold pure_cast_i8; decide
example : pure_cast_i8 127 = 127 := by unfold pure_cast_i8; decide
example : pure_cast_i8 65535 = -1 := by unfold pure_cast_i8; decide
example : pure_cast_u32 (-1) = 4294967295 := by unfold pure_cast_u32; decide
example : pure_cast_u32 127 = 127 := by unfold pure_cast_u32; decide
example : pure_cast_chain (-1) = 255 := by unfold pure_cast_chain; decide
example : pure_cast_chain 256 = 0 := by unfold pure_cast_chain; decide
example : pure_cast_widen (-128) = -128 := by unfold pure_cast_widen; decide
example : pure_cast_lt 1 2 = 1 := by unfold pure_cast_lt; decide
example : pure_cast_lt 2 1 = 0 := by unfold pure_cast_lt; decide
example : pure_cast_math 200 100 = 44 := by unfold pure_cast_math; decide

-- Integer methods.
example : pure_wadd_method 127 1 = -128 := by unfold pure_wadd_method; decide
example : pure_min_max 1 2 = 3 := by unfold pure_min_max; decide
example : pure_min_max 5 2 = 3 := by unfold pure_min_max; decide
example : pure_min_max 7 9 = 7 := by unfold pure_min_max; decide
example : pure_clamp_i (-100) = -5 := by unfold pure_clamp_i; decide
example : pure_clamp_i 100 = 5 := by unfold pure_clamp_i; decide
example : pure_clamp_i 3 = 3 := by unfold pure_clamp_i; decide
example : ¬ pure_pow2 0 := by unfold pure_pow2; decide
example : pure_pow2 1 := by unfold pure_pow2; decide
example : pure_pow2 64 := by unfold pure_pow2; decide
example : ¬ pure_pow2 96 := by unfold pure_pow2; decide
example : pure_pow2 2147483648 := by unfold pure_pow2; decide
example : ¬ pure_pow2 4294967295 := by unfold pure_pow2; decide

-- `div_ceil`, `is_multiple_of`, and rotations.
example : pure_dceil 7 2 = 4 := by unfold pure_dceil; decide
example : pure_dceil 8 2 = 4 := by unfold pure_dceil; decide
example : pure_dceil 0 3 = 0 := by unfold pure_dceil; decide
example : pure_dceil 255 1 = 255 := by unfold pure_dceil; decide
example : pure_dceil 255 255 = 1 := by unfold pure_dceil; decide
example : pure_dceil 1 0 = 0 := by unfold pure_dceil; decide
example : pure_multiple 6 3 := by unfold pure_multiple; decide
example : ¬ pure_multiple 7 3 := by unfold pure_multiple; decide
example : pure_multiple 0 0 := by unfold pure_multiple; decide
example : ¬ pure_multiple 5 0 := by unfold pure_multiple; decide
example : pure_rotl 129 1 = 3 := by unfold pure_rotl; decide
example : pure_rotl 129 9 = 3 := by unfold pure_rotl; decide
example : pure_rotl 129 0 = 129 := by unfold pure_rotl; decide
example : pure_rotl 1 7 = 128 := by unfold pure_rotl; decide
example : pure_rotr_i 1 1 = -128 := by unfold pure_rotr_i; decide
example : pure_rotr_i (-128) 7 = 1 := by unfold pure_rotr_i; decide
example : pure_rotr_i (-1) 3 = -1 := by unfold pure_rotr_i; decide
example : pure_rotr_i 2 1 = 1 := by unfold pure_rotr_i; decide
example : pure_rotl64 1 = 9223372036854775808 := by unfold pure_rotl64; decide
example : pure_rotl64 2 = 1 := by unfold pure_rotl64; decide

-- Sign tests, `signum`, magnitudes, and same-width bit casts.
example : pure_sig (-5) = -1 := by unfold pure_sig; decide
example : pure_sig 0 = 0 := by unfold pure_sig; decide
example : pure_sig 7 = 1 := by unfold pure_sig; decide
example : ¬ pure_nonzero 0 := by unfold pure_nonzero; decide
example : pure_nonzero (-1) := by unfold pure_nonzero; decide
example : pure_nonzero 1 := by unfold pure_nonzero; decide
example : pure_negative (-1) := by unfold pure_negative; decide
example : ¬ pure_negative 0 := by unfold pure_negative; decide
example : pure_uabs (-128) = 128 := by unfold pure_uabs; decide
example : pure_uabs (-5) = 5 := by unfold pure_uabs; decide
example : pure_uabs 7 = 7 := by unfold pure_uabs; decide
example : pure_sabs (-128) = 127 := by unfold pure_sabs; decide
example : pure_sabs (-5) = 5 := by unfold pure_sabs; decide
example : pure_wabs (-128) = -128 := by unfold pure_wabs; decide
example : pure_wabs (-5) = 5 := by unfold pure_wabs; decide
example : pure_to_signed 255 = -1 := by unfold pure_to_signed; decide
example : pure_to_signed 127 = 127 := by unfold pure_to_signed; decide
example : pure_to_signed 128 = -128 := by unfold pure_to_signed; decide
example : pure_to_unsigned (-1) = 255 := by unfold pure_to_unsigned; decide
example : pure_to_unsigned (-128) = 128 := by unfold pure_to_unsigned; decide
example : pure_to_unsigned 5 = 5 := by unfold pure_to_unsigned; decide

-- Mixed-signedness arithmetic.
example : pure_wadd_signed 250 10 = 4 := by unfold pure_wadd_signed; decide
example : pure_wadd_signed 5 (-10) = 251 := by unfold pure_wadd_signed; decide
example : pure_wadd_signed 5 (-3) = 2 := by unfold pure_wadd_signed; decide
example : pure_sadd_signed 250 10 = 255 := by unfold pure_sadd_signed; decide
example : pure_sadd_signed 5 (-10) = 0 := by unfold pure_sadd_signed; decide
example : pure_sadd_signed 5 3 = 8 := by unfold pure_sadd_signed; decide
example : pure_wsub_signed 5 10 = 251 := by unfold pure_wsub_signed; decide
example : pure_wsub_signed 250 (-10) = 4 := by unfold pure_wsub_signed; decide
example : pure_wsub_signed 5 3 = 2 := by unfold pure_wsub_signed; decide
example : pure_ssub_signed 5 10 = 0 := by unfold pure_ssub_signed; decide
example : pure_ssub_signed 250 (-10) = 255 := by unfold pure_ssub_signed; decide
example : pure_ssub_signed 5 (-3) = 8 := by unfold pure_ssub_signed; decide
example : pure_wadd_unsigned 100 200 = 44 := by unfold pure_wadd_unsigned; decide
example : pure_wadd_unsigned (-128) 255 = 127 := by unfold pure_wadd_unsigned; decide
example : pure_wadd_unsigned 127 1 = -128 := by unfold pure_wadd_unsigned; decide
example : pure_wsub_unsigned (-100) 200 = -44 := by unfold pure_wsub_unsigned; decide
example : pure_wsub_unsigned 0 255 = 1 := by unfold pure_wsub_unsigned; decide
example : pure_wsub_unsigned (-128) 1 = 127 := by unfold pure_wsub_unsigned; decide
example : pure_sadd_unsigned 100 200 = 127 := by unfold pure_sadd_unsigned; decide
example : pure_sadd_unsigned (-128) 255 = 127 := by unfold pure_sadd_unsigned; decide
example : pure_sadd_unsigned (-128) 100 = -28 := by unfold pure_sadd_unsigned; decide
example : pure_ssub_unsigned (-100) 200 = -128 := by unfold pure_ssub_unsigned; decide
example : pure_ssub_unsigned 127 255 = -128 := by unfold pure_ssub_unsigned; decide
example : pure_ssub_unsigned 10 5 = 5 := by unfold pure_ssub_unsigned; decide

-- Unbounded shifts and `midpoint`.
example : pure_ushl 1 8 = 0 := by unfold pure_ushl; decide
example : pure_ushl 1 7 = 128 := by unfold pure_ushl; decide
example : pure_ushl 3 1 = 6 := by unfold pure_ushl; decide
example : pure_ushl 1 4294967295 = 0 := by unfold pure_ushl; decide
example : pure_ishl 64 1 = -128 := by unfold pure_ishl; decide
example : pure_ishl (-1) 8 = 0 := by unfold pure_ishl; decide
example : pure_ishl (-1) 7 = -128 := by unfold pure_ishl; decide
example : pure_ushr 5 4294967295 = 0 := by unfold pure_ushr; decide
example : pure_ushr 256 4 = 16 := by unfold pure_ushr; decide
example : pure_ushr 4294967295 31 = 1 := by unfold pure_ushr; decide
example : pure_ishr (-1) 9 = -1 := by unfold pure_ishr; decide
example : pure_ishr (-128) 7 = -1 := by unfold pure_ishr; decide
example : pure_ishr 100 200 = 0 := by unfold pure_ishr; decide
example : pure_ishr (-128) 1 = -64 := by unfold pure_ishr; decide
example : pure_mid_u 255 254 = 254 := by unfold pure_mid_u; decide
example : pure_mid_u 0 255 = 127 := by unfold pure_mid_u; decide
example : pure_mid_u 7 0 = 3 := by unfold pure_mid_u; decide
example : pure_mid_i (-3) 0 = -1 := by unfold pure_mid_i; decide
example : pure_mid_i (-3) (-4) = -3 := by unfold pure_mid_i; decide
example : pure_mid_i 3 4 = 3 := by unfold pure_mid_i; decide
example : pure_mid_i (-128) 127 = 0 := by unfold pure_mid_i; decide

-- Division methods, checked against Rust.
example : pure_wdiv (-128) (-1) = -128 := by unfold pure_wdiv; decide
example : pure_wrem (-128) (-1) = 0 := by unfold pure_wrem; decide
example : pure_wdive (-128) (-1) = -128 := by unfold pure_wdive; decide
example : pure_wreme (-128) (-1) = 0 := by unfold pure_wreme; decide
example : pure_wdiv (-7) 2 = -3 := by unfold pure_wdiv; decide
example : pure_wrem (-7) 2 = -1 := by unfold pure_wrem; decide
example : pure_wdive (-7) 2 = -4 := by unfold pure_wdive; decide
example : pure_wreme (-7) 2 = 1 := by unfold pure_wreme; decide
example : pure_wdiv 7 (-2) = -3 := by unfold pure_wdiv; decide
example : pure_wrem 7 (-2) = 1 := by unfold pure_wrem; decide
example : pure_wdive 7 (-2) = -3 := by unfold pure_wdive; decide
example : pure_wreme 7 (-2) = 1 := by unfold pure_wreme; decide
example : pure_wdiv (-7) (-2) = 3 := by unfold pure_wdiv; decide
example : pure_wrem (-7) (-2) = -1 := by unfold pure_wrem; decide
example : pure_wdive (-7) (-2) = 4 := by unfold pure_wdive; decide
example : pure_wreme (-7) (-2) = 1 := by unfold pure_wreme; decide
example : pure_wdiv (-4) 3 = -1 := by unfold pure_wdiv; decide
example : pure_wrem (-4) 3 = -1 := by unfold pure_wrem; decide
example : pure_wdive (-4) 3 = -2 := by unfold pure_wdive; decide
example : pure_wreme (-4) 3 = 2 := by unfold pure_wreme; decide
example : pure_wdiv 5 0 = 0 := by unfold pure_wdiv; decide
example : pure_wrem 5 0 = 0 := by unfold pure_wrem; decide
example : pure_wdive 5 0 = 0 := by unfold pure_wdive; decide
example : pure_wreme 5 0 = 0 := by unfold pure_wreme; decide
example : pure_dive 7 2 = 3 := by unfold pure_dive; decide
example : pure_reme 7 2 = 1 := by unfold pure_reme; decide
example : pure_dive 255 16 = 15 := by unfold pure_dive; decide
example : pure_reme 255 16 = 15 := by unfold pure_reme; decide
example : pure_dive 0 9 = 0 := by unfold pure_dive; decide
example : pure_reme 0 9 = 0 := by unfold pure_reme; decide

-- Saturating and overflow-checked division.
example : pure_sdiv (-128) (-1) = 127 := by unfold pure_sdiv; decide
example : pure_sdiv (-7) 2 = -3 := by unfold pure_sdiv; decide
example : pure_sdiv 127 (-1) = -127 := by unfold pure_sdiv; decide
example : pure_sdiv 5 0 = 0 := by unfold pure_sdiv; decide
example : pure_sdiv_u 7 2 = 3 := by unfold pure_sdiv_u; decide
example : pure_sdiv_u 255 1 = 255 := by unfold pure_sdiv_u; decide
example : ¬ pure_nodiv (-128) (-1) := by unfold pure_nodiv; decide
example : pure_nodiv (-128) 1 := by unfold pure_nodiv; decide
example : pure_nodiv 127 (-1) := by unfold pure_nodiv; decide
example : pure_nodiv 5 0 := by unfold pure_nodiv; decide

-- `swap_bytes`, checked against Rust.
example : pure_swap_i8 (-5) = -5 := by unfold pure_swap_i8; decide
example : pure_swap_u16 4660 = 13330 := by unfold pure_swap_u16; decide
example : pure_swap_u16 255 = 65280 := by unfold pure_swap_u16; decide
example : pure_swap_i16 (-2) = -257 := by unfold pure_swap_i16; decide
example : pure_swap_i32 305419896 = 2018915346 := by unfold pure_swap_i32; decide
example : pure_swap_i32 (-1) = -1 := by unfold pure_swap_i32; decide
example : pure_swap_i32 128 = -2147483648 := by unfold pure_swap_i32; decide
example : pure_swap_u64 1 = 72057594037927936 := by unfold pure_swap_u64; decide
example : pure_swap_u64 72623859790382856 = 578437695752307201 := by unfold pure_swap_u64; decide
example : pure_swap_i128 1 = 1329227995784915872903807060280344576 := by unfold pure_swap_i128; decide
example : pure_swap_u128 128 = 170141183460469231731687303715884105728 := by unfold pure_swap_u128; decide

-- `reverse_bits`, `count_ones`, and `count_zeros`, checked against Rust.
example : pure_rev_u8 1 = 128 := by unfold pure_rev_u8; decide
example : pure_rev_i8 (-2) = 127 := by unfold pure_rev_i8; decide
example : pure_rev_u16 1 = 32768 := by unfold pure_rev_u16; decide
example : pure_rev_i32 1 = -2147483648 := by unfold pure_rev_i32; decide
example : pure_rev_u32 305419896 = 510274632 := by unfold pure_rev_u32; decide
example : pure_rev_u64 1 = 9223372036854775808 := by unfold pure_rev_u64; decide
example : pure_rev_i128 1 = -170141183460469231731687303715884105728 := by unfold pure_rev_i128; decide
example : pure_rev_u128 1 = 170141183460469231731687303715884105728 := by unfold pure_rev_u128; decide
example : pure_ones_i8 (-1) = 8 := by unfold pure_ones_i8; decide
example : pure_ones_u16 21845 = 8 := by unfold pure_ones_u16; decide
example : pure_ones_i16 (-2) = 15 := by unfold pure_ones_i16; decide
example : pure_ones_u32 305419896 = 13 := by unfold pure_ones_u32; decide
example : pure_ones_i64 (-9223372036854775808) = 1 := by unfold pure_ones_i64; decide
example : pure_ones_i128 (-1) = 128 := by unfold pure_ones_i128; decide
example : pure_zeros_u8 240 = 4 := by unfold pure_zeros_u8; decide
example : pure_zeros_usize 1 = 63 := by unfold pure_zeros_usize; decide
example : pure_zeros_u128 0 = 128 := by unfold pure_zeros_u128; decide

-- Leading and trailing counts, checked against Rust.
example : pure_lz_u8 0 = 8 := by unfold pure_lz_u8; decide
example : pure_lz_u8 1 = 7 := by unfold pure_lz_u8; decide
example : pure_lz_u8 255 = 0 := by unfold pure_lz_u8; decide
example : pure_lz_i8 (-128) = 0 := by unfold pure_lz_i8; decide
example : pure_lz_i8 (-1) = 0 := by unfold pure_lz_i8; decide
example : pure_lz_i32 1 = 31 := by unfold pure_lz_i32; decide
example : pure_lz_u128 1 = 127 := by unfold pure_lz_u128; decide
example : pure_tz_u16 0 = 16 := by unfold pure_tz_u16; decide
example : pure_tz_u8 8 = 3 := by unfold pure_tz_u8; decide
example : pure_tz_i64 (-9223372036854775808) = 63 := by unfold pure_tz_i64; decide
example : pure_tz_u128 0 = 128 := by unfold pure_tz_u128; decide
example : pure_lo_i8 (-1) = 8 := by unfold pure_lo_i8; decide
example : pure_lo_i8 (-128) = 1 := by unfold pure_lo_i8; decide
example : pure_lo_u32 0 = 0 := by unfold pure_lo_u32; decide
example : pure_lo_u8 240 = 4 := by unfold pure_lo_u8; decide
example : pure_lo_i64 (-2) = 63 := by unfold pure_lo_i64; decide
example : pure_to_i128 (-1) = 128 := by unfold pure_to_i128; decide
example : pure_to_u8 7 = 3 := by unfold pure_to_u8; decide
example : pure_to_u8 0 = 0 := by unfold pure_to_u8; decide
example : pure_to_i8 127 = 7 := by unfold pure_to_i8; decide
example : pure_to_usize 65535 = 16 := by unfold pure_to_usize; decide

-- Inclusive range patterns.
example : pure_classify (-128) = 0 := by unfold pure_classify; decide
example : pure_classify (-1) = 0 := by unfold pure_classify; decide
example : pure_classify 0 = 1 := by unfold pure_classify; decide
example : pure_classify 5 = 2 := by unfold pure_classify; decide
example : pure_classify 25 = 2 := by unfold pure_classify; decide
example : pure_classify 15 = 3 := by unfold pure_classify; decide
example : pure_classify 127 = 3 := by unfold pure_classify; decide
example : pure_clamp_byte 7 = 7 := by unfold pure_clamp_byte; decide
example : pure_clamp_byte 255 = 255 := by unfold pure_clamp_byte; decide
example : pure_clamp_byte 300 = 255 := by unfold pure_clamp_byte; decide

-- `ilog2` is the position of the highest set bit of a positive receiver.
example : pure_log2_or_zero 1 = 0 := by unfold pure_log2_or_zero; decide
example : pure_log2_or_zero 2 = 1 := by unfold pure_log2_or_zero; decide
example : pure_log2_or_zero 3 = 1 := by unfold pure_log2_or_zero; decide
example : pure_log2_or_zero 255 = 7 := by unfold pure_log2_or_zero; decide
example : pure_log2_or_zero 256 = 8 := by unfold pure_log2_or_zero; decide
example : pure_log2_or_zero 32767 = 14 := by unfold pure_log2_or_zero; decide
example : pure_log2_or_zero 0 = 0 := by unfold pure_log2_or_zero; decide
example : pure_log2_or_zero (-5) = 0 := by unfold pure_log2_or_zero; decide
example : pure_log2_u64 1 = 0 := by unfold pure_log2_u64; decide
example : pure_log2_u64 1099511627775 = 39 := by unfold pure_log2_u64; decide
example : pure_log2_u64 1099511627776 = 40 := by unfold pure_log2_u64; decide
example : pure_log2_u64 18446744073709551615 = 63 := by unfold pure_log2_u64; decide
example : pure_log2_u64 0 = 0 := by unfold pure_log2_u64; decide
example : pure_log2_i8 127 = 6 := by unfold pure_log2_i8; decide
example : pure_log2_i8 64 = 6 := by unfold pure_log2_i8; decide
example : pure_log2_i8 63 = 5 := by unfold pure_log2_i8; decide
example : pure_log2_i8 (-128) = 0 := by unfold pure_log2_i8; decide

-- `next_power_of_two` is the least power of two at or above its receiver.
example : pure_npot_u8 0 = 1 := by unfold pure_npot_u8; decide
example : pure_npot_u8 1 = 1 := by unfold pure_npot_u8; decide
example : pure_npot_u8 2 = 2 := by unfold pure_npot_u8; decide
example : pure_npot_u8 3 = 4 := by unfold pure_npot_u8; decide
example : pure_npot_u8 5 = 8 := by unfold pure_npot_u8; decide
example : pure_npot_u8 127 = 128 := by unfold pure_npot_u8; decide
example : pure_npot_u8 128 = 128 := by unfold pure_npot_u8; decide
example : pure_npot_u8 129 = 0 := by unfold pure_npot_u8; decide
example : pure_npot_u64 1000 = 1024 := by unfold pure_npot_u64; decide
example : pure_npot_u64 1099511627776 = 1099511627776 := by unfold pure_npot_u64; decide
example : pure_npot_u64 1099511627777 = 2199023255552 := by unfold pure_npot_u64; decide
example : pure_npot_u64 9223372036854775808 = 9223372036854775808 := by
  unfold pure_npot_u64; decide
example : pure_npot_u64 9223372036854775809 = 0 := by unfold pure_npot_u64; decide

-- `name @ pattern` binds the scrutinee in arms that test it.
example : pure_at_bind 0 = 0 := by unfold pure_at_bind; decide
example : pure_at_bind 1 = 1 := by unfold pure_at_bind; decide
example : pure_at_bind 2 = 2 := by unfold pure_at_bind; decide
example : pure_at_bind 3 = 1 := by unfold pure_at_bind; decide
example : pure_at_bind 200 = 7 := by unfold pure_at_bind; decide
example : pure_at_bind 201 = 100 := by unfold pure_at_bind; decide
example : pure_at_npot 1000 = 1024 := by unfold pure_at_npot; decide
example : pure_at_npot 32768 = 32768 := by unfold pure_at_npot; decide
example : pure_at_npot 32769 = 0 := by unfold pure_at_npot; decide

-- The masked shifts take the amount modulo the width.
example : pure_wshl_is 1 17 2 := by unfold pure_wshl_is; decide
example : pure_wshl_is 0x8001 1 2 := by unfold pure_wshl_is; decide
example : pure_wshr_is (-32768) 31 (-1) := by unfold pure_wshr_is; decide
example : ¬ pure_wshr_is (-32768) 31 1 := by unfold pure_wshr_is; decide

-- `usat` (sorted eighth as `fn7`) binds `let k: u32 = 31;` in `max_steps =`
-- `abs_diff(a, b) + saturating_add(n, 1u32) + (n & 15u32) + (n >> 30) + (n >> k)`
-- `+ n as u8 as u32 + a.max(b) as u32 + n.div_ceil(8)`
-- `+ a.cast_signed().unsigned_abs() as u32 + b.saturating_add_signed(-1) as u32`
-- `+ n.unbounded_shr(31) + n.div_euclid(16) + n.saturating_div(1024)`
-- `+ n.swap_bytes() + n.count_ones() + n.leading_zeros()`
-- `+ (if n > 0 { n.ilog2() } else { 0 })`
-- `+ (if n <= 1000 { n.next_power_of_two() } else { 0 })`
-- `+ (match n { j @ 1..=9 => j, _ => 0 }) + match n { 0..=9 => 1, _ => 2 }`.
example : fn7_max_steps { args := [u8Val 9, u8Val 2, u32Val 5] } = 83886170 := rfl
example : fn7_max_steps { args := [u8Val 3, u8Val 250, u32Val 4294967295] } =
    9399436349 := rfl
example : fn7_max_steps { args := [u8Val 9, u8Val 2, u32Val 0] } = 61 := rfl

end Spec.Check
