-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import GuardRefuteWf

/-!
# Negative Refutations for `Trusted.MirSemantics.Enum` Validity Guards

Exercises both clauses of `isUnicodeScalar` (`<= 0x10ffff` and surrogate-range
exclusion `[0xd800, 0xdfff]`) end-to-end through `evalConstLit` and
`WellFormed`, and the Profile v2 rejection of overflow-pair pointee types in
`isSupportedV2LocalTy`.
-/

namespace GuardMutation

open Trusted.MirAst Trusted.MirSemantics

/-- Guard `enum_char_above_unicode_max`: code point `0x110000` exceeds the
maximum Unicode scalar value `0x10FFFF` and faults with `.undefined`. -/
theorem refute_enum_char_above_unicode_max :
    ReachesResult (mkConstRetProg .char 0x110000) queryEmpty
      (.fault .undefined) ∧
    ¬ WellFormed (mkConstRetProg .char 0x110000) queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `enum_char_surrogate_gap`: UTF-16 surrogate code point `0xD800` is
not a Unicode scalar value and faults with `.undefined`. -/
theorem refute_enum_char_surrogate_gap :
    ReachesResult (mkConstRetProg .char 0xd800) queryEmpty
      (.fault .undefined) ∧
    ¬ WellFormed (mkConstRetProg .char 0xd800) queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `enum_v2_overflow_pair_pointee`: no Profile v2 local may be a
reference or raw pointer to an overflow pair `(T, bool)`, so the pair's
unchecked byte layout stays unobservable. -/
theorem refute_enum_v2_overflow_pair_pointee :
    isSupportedV2LocalTy (.rawPtr .shared (.tuple [.int .i8 false, .bool])) =
      false ∧
    isSupportedV2LocalTy (.ref .mut (.tuple [.int .i32 true, .bool])) = false :=
  ⟨rfl, rfl⟩

/-- Anti-overreach canary: an overflow pair itself, and pointers to its
integer or `bool` field types, remain admitted local types. -/
theorem positive_enum_v2_overflow_pair_local :
    isSupportedV2LocalTy (.tuple [.int .i8 false, .bool]) = true ∧
    isSupportedV2LocalTy (.rawPtr .shared (.int .i8 false)) = true ∧
    isSupportedV2LocalTy (.ref .shared .bool) = true :=
  ⟨rfl, rfl, rfl⟩

end GuardMutation
