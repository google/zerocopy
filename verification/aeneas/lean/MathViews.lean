/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/


module
public import Invariants
import all Invariants
public import ContractSimps
@[expose] public section
open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs
set_option linter.unusedSimpArgs false

def encodingValid (code : layout.RoundingAlignAndPhase) : Prop :=
  0 < code._0.val.val

@[simp, contract_simps] theorem nonzero_valid_iff (a : NonZeroUsize) :
    isValid a ↔ 0 < a.val.val := Iff.rfl

@[simp, contract_simps] theorem encoding_valid_iff (code : layout.RoundingAlignAndPhase) :
    isValid code ↔ encodingValid code := by
  simp [isValid, IsValid.isValid, layout.RoundingAlignAndPhase.aeneasValid,
    Zerocopy.Invariants.rounding_encoding_valid, encodingValid]

@[simp, contract_simps] theorem scalar_valid_iff (x : UScalar ty) : isValid x ↔ True := Iff.rfl

@[contract_simps] theorem normalized_nat_pos_iff (n : Nat) :
    Nat.le (Nat.succ 0) n ↔ 0 < n := Nat.succ_le_iff

attribute [contract_simps] and_true true_and and_self true_implies forall_true_iff

attribute [contract_simps] encodingValid

end Zerocopy.Proofs
