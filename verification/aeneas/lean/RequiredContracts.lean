/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Aeneas
public import ContractSimps
public import Mathlib.Tactic.Convert
public section
open Lean Aeneas Aeneas.Std

namespace AeneasContracts

-- Domain-specific normalizers may be registered locally by the checking module.
attribute [contract_simps] WP.spec_equiv_exists UScalar.eq_equiv
  UScalar.coe_max UScalar.lt_equiv UScalar.le_equiv

/-- Prove an independently authored proposition from a supplied theorem.
Conversion, congruence, case splitting and `grind` produce an ordinary kernel
checked proof. Matcher names are never compared or assumed equivalent. The
bounded congruence pass exposes input and output matches beneath quantifiers. -/
macro "check_contract " expected:ident " using " candidate:term : command => do
  let witness := mkIdentFrom expected (expected.getId.appendAfter "_checked")
  `(theorem $witness : $expected := by
    unfold $expected
    first
    | exact ($candidate)
    | convert ($candidate) using 1 <;> simp only [contract_simps]
      all_goals
        (congr! 4
         all_goals first | rfl | (split <;> simp_all only []) | grind))

end AeneasContracts
