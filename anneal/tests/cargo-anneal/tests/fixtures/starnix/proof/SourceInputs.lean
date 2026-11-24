-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Anneal.MirWp
public import Inputs

@[expose] public section

namespace Endianness

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

theorem bodyDataWidthVal_of_paramTys (body : Body) (ety : EnumTy)
    (paramTys : (body.locals.drop 1).take body.argumentCount =
      [.bool, .enum ety, .int .i64 false])
    (w : Nat) :
    bodyDataWidthVal body w = .enumVal ety w := by
  cases h_loc : body.locals with
  | nil => simp [h_loc] at paramTys
  | cons l0 ls0 =>
    cases ls0 with
    | nil => simp [h_loc] at paramTys
    | cons l1 ls1 =>
      cases ls1 with
      | nil =>
        cases h_ac : body.argumentCount with
        | zero => simp [h_loc, h_ac] at paramTys
        | succ k => simp [h_loc, h_ac] at paramTys
      | cons l2 ls2 =>
        cases h_ac : body.argumentCount with
        | zero => simp [h_loc, h_ac] at paramTys
        | succ k0 =>
          cases k0 with
          | zero => simp [h_loc, h_ac] at paramTys
          | succ k1 =>
            have h_l2 : l2 = .enum ety := by
              simp [h_loc, h_ac] at paramTys
              exact paramTys.2.1
            subst h_l2
            simp [bodyDataWidthVal, h_loc]

/-- Valid source entries have exactly the finite flag and width cases. -/
theorem validArgs3_elim (body : Body) (ety : EnumTy)
    (paramTys : (body.locals.drop 1).take body.argumentCount =
      [.bool, .enum ety, .int .i64 false])
    (h_ds : ety.discriminants = [0, 1, 2, 3])
    (p : List Val → Prop)
    (inputs : ∀ flag : Bool, ∀ width : Fin 4, ∀ value : Word,
      p (bodyEndianArgs body flag width.val value)) :
    ∀ args, ValidEntryArgs body args → p args := by
  intro args valid
  unfold ValidEntryArgs at valid
  rw [paramTys] at valid
  cases args with
  | nil => cases valid
  | cons a0 rest0 =>
    cases rest0 with
    | nil => simp [checkArgsMatch] at valid
    | cons a1 rest1 =>
      cases rest1 with
      | nil => simp [checkArgsMatch] at valid
      | cons a2 rest2 =>
        cases rest2 with
        | cons _ _ => simp [checkArgsMatch] at valid
        | nil =>
          simp only [checkArgsMatch, Bool.and_eq_true] at valid
          let ⟨flag, hf⟩ := checkVal_bool_iff.mp valid.1
          let ⟨_, ⟨width, hw⟩⟩ := checkVal_enum_iff.mp valid.2.1
          have h_len : ety.discriminants.length = 4 := by rw [h_ds]; rfl
          let width4 : Fin 4 := ⟨width.val, h_len ▸ width.isLt⟩
          let ⟨bits, hv, hTrunc⟩ := checkVal_int_iff.mp valid.2.2.1
          have h_value : a2 = u64Val (bvExtractLsb 63 0 bits) :=
            hv.trans (congrArg (fun b => Val.scalar ⟨.i64, false, b⟩) hTrunc.symm)
          subst hf hw
          rw [h_value]
          have h_dw := bodyDataWidthVal_of_paramTys body ety paramTys
            width4.val
          have h_eq :
              [.bool flag, .enumVal ety width4.val,
                u64Val (bvExtractLsb 63 0 bits)] =
              bodyEndianArgs body flag width4.val (bvExtractLsb 63 0 bits) := by
            unfold bodyEndianArgs
            rw [h_dw]
          rw [h_eq]
          exact inputs flag width4 (bvExtractLsb 63 0 bits)

theorem validEntryArgs_bodyEndianArgs (body : Body) (ety : EnumTy)
    (paramTys : (body.locals.drop 1).take body.argumentCount =
      [.bool, .enum ety, .int .i64 false])
    (h_ds : ety.discriminants = [0, 1, 2, 3])
    (h_adm : enumAdmitted ety = true)
    (flag : Bool) (width : Fin 4) (value : Word) :
    ValidEntryArgs body (bodyEndianArgs body flag width.val value) := by
  unfold ValidEntryArgs bodyEndianArgs
  rw [paramTys, bodyDataWidthVal_of_paramTys body ety paramTys width.val]
  have h_blt : Nat.blt width.val ety.discriminants.length = true := by
    rw [h_ds]
    exact Nat.ble_eq_true_of_le width.isLt
  have h_enum : checkVal (.enumVal ety width.val) (.enum ety) = true := by
    simp [checkVal, Val.ty?, h_adm, h_blt, MirTy.beq, EnumTy.beq_iff.mpr rfl]
  have h_bool : checkVal (.bool flag) .bool = true := rfl
  have h_u64 : checkVal (u64Val value) (.int .i64 false) = true :=
    checkVal_u64_bvZeroExtend value
  simp [checkArgsMatch, h_bool, h_enum, h_u64]

end Endianness

end
