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
`WellFormed`.
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

end GuardMutation
