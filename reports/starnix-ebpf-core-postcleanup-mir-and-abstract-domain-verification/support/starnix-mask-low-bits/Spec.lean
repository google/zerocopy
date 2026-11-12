-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Trusted.Mvp

namespace Spec

open Trusted.Mvp

/-- Functional specification of `scalar_value::U64Range::mask_low_bits(value, bit_count)`. -/
def maskLowBitsSpec (value bitCount : Word) : Word :=
  if bitCount == 0 then 0
  else if decide (64 ≤ bitCount.toNat) then value
  else value &&& (((1 : Word) <<< bitCount.toNat) - 1)

/-- For every valid `(value: u64, bit_count: u32)` input pair, execution is safe and
    returns `maskLowBitsSpec value bitCount`. -/
def exactMaskLowBits (body : Body) : Prop :=
  ∀ value bitCount : Word,
    validValue (.int 32 false) bitCount = true →
    Safe body [value, bitCount] ∧
    Returns body [value, bitCount] (maskLowBitsSpec value bitCount)

def specs : Specs :=
  { safety := fun _ _ => True
    property := fun program => ∃ body, program.bodies = [body] ∧
      exactMaskLowBits body }

end Spec
