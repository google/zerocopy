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

-- Independently stated representation domains. A mathematical size view alone
-- does not distinguish a zero raw encoding from a valid encoding of one.
def encodingValid (code : layout.RoundingAlignAndPhase) : Prop :=
  0 < code._0.val.val

def trailingValid {E : Type} [IsValid E] (tail : layout.TrailingSliceLayout E) : Prop :=
  isValid tail.elem_size ∧ encodingValid tail.size_rounding_align_and_phase

def sizeInfoValid {E : Type} [IsValid E] (info : layout.SizeInfo E) : Prop :=
  match info with
  | .Sized _ => True
  | .SliceDst tail => trailingValid tail

def layoutValid (self : layout.DstLayout) : Prop :=
  0 < self.align.val.val ∧ sizeInfoValid self.size_info

@[simp, contract_simps] theorem nonzero_valid_iff (a : NonZeroUsize) :
    isValid a ↔ 0 < a.val.val := Iff.rfl

@[simp, contract_simps] theorem encoding_valid_iff (code : layout.RoundingAlignAndPhase) :
    isValid code ↔ encodingValid code := by
  simp [isValid, IsValid.isValid, layout.RoundingAlignAndPhase.aeneasValid,
    Zerocopy.Invariants.rounding_encoding_valid, encodingValid]

@[simp, contract_simps] theorem trailing_valid_iff {E : Type} [IsValid E]
    (tail : layout.TrailingSliceLayout E) : isValid tail ↔ trailingValid tail := by
  simp [isValid, IsValid.isValid, layout.TrailingSliceLayout.aeneasValid,
    layout.RoundingAlignAndPhase.aeneasValid, Zerocopy.Invariants.rounding_encoding_valid,
    trailingValid, encodingValid, and_comm]

@[simp, contract_simps] theorem size_info_valid_iff {E : Type} [IsValid E]
    (info : layout.SizeInfo E) : isValid info ↔ sizeInfoValid info := by
  cases info <;> simp [isValid, IsValid.isValid, layout.SizeInfo.aeneasValid,
    layout.TrailingSliceLayout.aeneasValid, layout.RoundingAlignAndPhase.aeneasValid,
    Zerocopy.Invariants.rounding_encoding_valid, sizeInfoValid, trailingValid,
    encodingValid, and_comm]

@[simp, contract_simps] theorem layout_valid_iff (self : layout.DstLayout) :
    isValid self ↔ layoutValid self := by
  cases self with
  | mk align info unpadded =>
    cases info <;> simp [isValid, IsValid.isValid, layout.DstLayout.aeneasValid,
      layout.SizeInfo.aeneasValid, layout.TrailingSliceLayout.aeneasValid,
      layout.RoundingAlignAndPhase.aeneasValid, Zerocopy.Invariants.rounding_encoding_valid,
      layoutValid, sizeInfoValid, trailingValid, encodingValid, and_comm]

@[simp, contract_simps] theorem scalar_valid_iff (x : UScalar ty) : isValid x ↔ True := Iff.rfl
@[simp, contract_simps] theorem cast_type_valid_iff (side : layout.CastType) : isValid side ↔ True := by
  cases side <;> rfl

attribute [contract_simps] and_true true_and and_self true_implies forall_true_iff

attribute [contract_simps] encodingValid trailingValid sizeInfoValid layoutValid

end Zerocopy.Proofs

namespace Zerocopy.Proofs
set_option linter.unusedSimpArgs false

@[simp, contract_simps] theorem cast_result_valid_iff
    (r : core.result.Result (Usize × Usize) layout.MetadataCastError) : isValid r ↔ True := by
  cases r with
  | Ok pair => cases pair; simp [isValid, IsValid.isValid, validRustResult]
  | Err error =>
    cases error <;> simp [isValid, IsValid.isValid, validRustResult,
      layout.MetadataCastError.aeneasValid]

-- WHNF uses Nat.le directly; retain a pointwise bridge to the authored <.
@[contract_simps] theorem normalized_nat_pos_iff (n : Nat) :
    Nat.le (Nat.succ 0) n ↔ 0 < n := Nat.succ_le_iff

end Zerocopy.Proofs
