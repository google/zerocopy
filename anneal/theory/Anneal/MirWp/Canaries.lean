-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.NotationExtra
public import Init.Data.BitVec.BasicAux
public import Init.Data.Int.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Nat.Bitwise.Basic
public import Init.Control.Except
public import Trusted
public import Trusted.MirAst
public import Trusted.MirSemantics
public import Anneal.MirWp.Core
public import Anneal.MirWp.Scalars
public import Anneal.MirWp.Reflection

public section

namespace Anneal.MirWp

open Trusted.MirAst Trusted.MirSemantics

/-! ## Concrete Day-1 Non-Vacuity and Parameter-Boundary Canaries -/

/-- Canary `D1`: `progAddU32` on `(30, 12)` is well-formed and returns `42`. -/
theorem canary_positive_add_anneal_base : CanaryPositiveAddAnnealClaim :=
  positiveCanary_of_exec (fuel := 2) rfl

/-- Canary `D2`: `progEmptyUnitFn` is well-formed and returns `Val.unit`. -/
theorem canary_positive_empty_unit_fn_base : CanaryPositiveEmptyUnitFnClaim :=
  positiveCanary_of_exec (fuel := 1) rfl

/-- Control-flow and statement canary (`nop`, `storageLive`, `storageDead`,
`goto`, and both matched and `otherwise` arms of `switchInt`). -/
theorem canary_positive_stmts_and_cf_anneal_base :
    CanaryPositiveStmtsAndCfAnnealClaim :=
  ⟨positiveCanary_of_exec (fuel := 10) rfl,
   positiveCanary_of_exec (fuel := 10) rfl⟩

/-- Unary-operator canary (`UnOp.not` on `bool` and `u8`, `UnOp.neg` on signed
`i8` including wrapping `-INT_MIN == INT_MIN`). -/
theorem canary_positive_unop_anneal_base : CanaryPositiveUnopAnnealClaim :=
  ⟨positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl⟩

/-- Binary-operator canary covering every supported `BinOp` variant at boundary
values across unsigned integers, signed integers, shifts, and booleans. -/
theorem canary_positive_all_binops_anneal_base :
    CanaryPositiveAllBinopsAnnealClaim :=
  ⟨positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl⟩

/-- Integer-width boundary canary covering all six `IntWidth` variants (`.i8`,
`.i16`, `.i32`, `.i64`, `.i128`, `.isize`) in both unsigned (`MAX + 1 = 0`) and
signed (`INT_MAX + 1 = INT_MIN`) modes. -/
theorem canary_positive_all_int_widths_anneal_base :
    CanaryPositiveAllIntWidthsAnnealClaim :=
  ⟨⟨positiveCanary_of_exec (fuel := 2) rfl,
    positiveCanary_of_exec (fuel := 2) rfl⟩,
   ⟨positiveCanary_of_exec (fuel := 2) rfl,
    positiveCanary_of_exec (fuel := 2) rfl⟩,
   ⟨positiveCanary_of_exec (fuel := 2) rfl,
    positiveCanary_of_exec (fuel := 2) rfl⟩,
   ⟨positiveCanary_of_exec (fuel := 2) rfl,
    positiveCanary_of_exec (fuel := 2) rfl⟩,
   ⟨positiveCanary_of_exec (fuel := 2) rfl,
    positiveCanary_of_exec (fuel := 2) rfl⟩,
   ⟨positiveCanary_of_exec (fuel := 2) rfl,
    positiveCanary_of_exec (fuel := 2) rfl⟩⟩

/-- Canary `D3`: dividing by zero reaches `.fault .undefined` (and not
`.fault .unsupported`) and refutes `WellFormed`. -/
theorem canary_negative_ub_div_zero_anneal_base :
    CanaryNegativeUbDivZeroAnnealClaim :=
  negativeCanary_of_execFault (fuel := 1)
    (fun h => FaultKind.noConfusion h) rfl

/-- Canary `D4`: signed `(-128i8) % (-1i8)` reaches `.fault .undefined` (and
not `.fault .unsupported`) and refutes `WellFormed`. -/
theorem canary_negative_ub_signed_rem_overflow_i8_base :
    CanaryNegativeUbSignedRemOverflowI8Claim :=
  negativeCanary_of_execFault (fuel := 1)
    (fun h => FaultKind.noConfusion h) rfl

/-- Canary `D5`: executing `.unsupported` reaches `.fault .unsupported` (and
not `.fault .undefined`) and refutes `WellFormed`. -/
theorem canary_negative_unsupported_anneal_base :
    CanaryNegativeUnsupportedAnnealClaim :=
  negativeCanary_of_execFault (fuel := 1)
    (fun h => FaultKind.noConfusion h) rfl

/-- Unchecked-overflow canary: on `(u32::MAX, 1)`, `AddUnchecked`
(`progAddUncheckedU32`) reaches `.fault .undefined` (and not
`.fault .unsupported`) and refutes `WellFormed`, while wrapping `Add`
(`progAddU32`) on the same inputs is well-formed and returns `0`. -/
theorem canary_negative_ub_add_unchecked_overflow_u32_base :
    CanaryNegativeUbAddUncheckedOverflowU32Claim :=
  ⟨negativeCanary_of_execFault (fuel := 1)
     (fun h => FaultKind.noConfusion h) rfl,
   positiveCanary_of_exec (fuel := 2) rfl⟩

/-- Shift-overflow canary: `ShlUnchecked` at shift amount `== bitWidth` (`32`
on `u32`) and `ShrUnchecked` at negative signed shift (`-1i8` on `u32`) both
reach `.fault .undefined` (and not `.fault .unsupported`). -/
theorem canary_negative_ub_shift_unchecked_at_bitwidth_anneal_base :
    CanaryNegativeUbShiftUncheckedAtBitwidthAnnealClaim :=
  ⟨negativeCanary_of_execFault (fuel := 1)
     (fun h => FaultKind.noConfusion h) rfl,
   negativeCanary_of_execFault (fuel := 1)
     (fun h => FaultKind.noConfusion h) rfl⟩

/-- Storage-dead read canary: reading a local after `StatementKind.storageDead`
reaches `.fault .undefined` (and not `.fault .unsupported`). -/
theorem canary_negative_ub_storage_dead_read_anneal_base :
    CanaryNegativeUbStorageDeadReadAnnealClaim :=
  negativeCanary_of_execFault (fuel := 4)
    (fun h => FaultKind.noConfusion h) rfl

/-- Storage-dead return-place canary: executing `StatementKind.storageDead 0`
on `_0` reaches `.fault .unsupported` (and not `.fault .undefined`). -/
theorem canary_negative_ub_storage_dead_return_place_anneal_base :
    CanaryNegativeUbStorageDeadReturnPlaceAnnealClaim :=
  negativeCanary_of_execFault (fuel := 1)
    (fun h => FaultKind.noConfusion h) rfl

/-- Unreachable terminator canary: executing `TerminatorKind.unreachable`
reaches `.fault .undefined` (and not `.fault .unsupported`). -/
theorem canary_negative_ub_unreachable_anneal_base :
    CanaryNegativeUbUnreachableAnnealClaim :=
  negativeCanary_of_execFault (fuel := 1)
    (fun h => FaultKind.noConfusion h) rfl

/-- Unsigned-negation canary: executing `UnOp.neg` on an unsigned integer
(`u32`) reaches `.fault .unsupported` (and not `.fault .undefined`). -/
theorem canary_negative_unsupported_unsigned_neg_anneal_base :
    CanaryNegativeUnsupportedUnsignedNegAnnealClaim :=
  negativeCanary_of_execFault (fuel := 1)
    (fun h => FaultKind.noConfusion h) rfl

/-- Explicit-repr fieldless enum positive canary: `#[repr(u8)]` non-index tag
decoding + `u8` `Rvalue.discriminant` and signed `i8` -> `isize` sign-extended
tag decoding. -/
theorem canary_positive_enum_explicit_repr_anneal_base :
    CanaryPositiveEnumExplicitReprAnnealClaim :=
  ⟨positiveCanary_of_exec (fuel := 5) rfl,
   positiveCanary_of_exec (fuel := 5) rfl⟩

/-- Single-variant inhabited ZST enum positive canary: implicit return without
writing `_0`, non-deinitializing `Operand.move`, `ConstLit.zeroSized`, and
`Rvalue.discriminant`. -/
theorem canary_positive_zst_single_enum_anneal_base :
    CanaryPositiveZstSingleEnumAnnealClaim :=
  ⟨positiveCanary_of_exec (fuel := 1) rfl,
   positiveCanary_of_exec (fuel := 10) rfl⟩

/-- Fieldless enum negative UB canary: invalid constant scalar tag `1` on
`ReprU8 { A = 10, B = 20 }` and reading `Rvalue.discriminant` from an
uninitialized scalar-tagged enum local both reach `.fault .undefined`. -/
theorem canary_negative_ub_enum_invalid_tag_and_uninit_anneal_base :
    CanaryNegativeUbEnumInvalidTagAndUninitAnnealClaim :=
  ⟨negativeCanary_of_execFault (fuel := 2)
     (fun h => FaultKind.noConfusion h) rfl,
   negativeCanary_of_execFault (fuel := 2)
     (fun h => FaultKind.noConfusion h) rfl⟩

/-- Crate/unit/body verification canary exercising positive `CrateTheorem` and
`UnitTheorem` acceptance, safe vs. `unsafe` contract gating (`isUnsafe`),
`MirTy.never` static-admission non-vacuity, `p.bodies[defId]` lookup binding in
`BodyVerified`, empty-`bodies` / out-of-bounds `entryDefId` / duplicate
`identity` rejection, non-`BodyVerified` body rejection inside a crate, false
`specs.property` rejection, and `.crate` vs. `.unit` scope mismatch rejection.
-/
theorem canary_crate_and_body_verified_anneal_base :
    CanaryCrateAndBodyVerifiedAnnealClaim := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩
    intro defId body hGet
    cases defId with
    | zero =>
      injection hGet with hBody; subst hBody
      refine ⟨rfl, rfl, fun args hArgs _ => ?_⟩
      cases args with
      | nil =>
        refine (positiveCanary_of_exec (fuel := 1) (expectedRet := .unit) ?_).1
        rfl
      | cons _ _ => exact Bool.noConfusion hArgs
    | succ defId =>
      cases defId with
      | zero =>
        injection hGet with hBody; subst hBody
        refine ⟨rfl, rfl, fun args _ hSafe => ?_⟩
        have hEq : args = [.bool true] := hSafe rfl
        subst hEq
        refine (positiveCanary_of_exec (fuel := 3)
          (expectedRet := u32Val 42) ?_).1
        rfl
      | succ defId =>
        cases defId with
        | zero =>
          injection hGet with hBody; subst hBody
          refine ⟨rfl, rfl, fun args hArgs _ => ?_⟩
          cases args with
          | nil => exact Bool.noConfusion hArgs
          | cons v rest =>
            have hCheck : checkVal v .never = true := by
              revert hArgs
              change (checkVal v .never && checkArgsMatch rest []) = true → _
              cases checkVal v .never <;> intro h <;>
                first | rfl | exact Bool.noConfusion h
            rw [checkVal_never_false v] at hCheck
            exact Bool.noConfusion hCheck
        | succ _ =>
          dsimp [canaryValidCrate, Trusted.MirSemantics.getElem?] at hGet
          cases hGet
  · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩
    intro defId body hGet
    cases defId with
    | zero =>
      injection hGet with hBody; subst hBody
      refine ⟨rfl, rfl, fun args hArgs _ => ?_⟩
      cases args with
      | nil =>
        refine (positiveCanary_of_exec (fuel := 1) (expectedRet := .unit) ?_).1
        rfl
      | cons _ _ => exact Bool.noConfusion hArgs
    | succ _ =>
      dsimp [Trusted.MirSemantics.getElem?] at hGet
      cases hGet
  · intro hVer
    have hWf := hVer.2.2 [.bool false] rfl (fun h => Bool.noConfusion h)
    have hNeg : NegativeCanaryClaim
        (entryProgForBody {
          scope := .unit
          pointerWidthBits := 64
          mirProfileVersion := 1
          bodies := [canaryUnsafeGuardedBody false]
        } 0)
        { args := [.bool false] } .undefined .unsupported :=
      negativeCanary_of_execFault (fuel := 2)
        (fun h => FaultKind.noConfusion h) rfl
    exact hNeg.2.2 hWf
  · intro hVer
    exact Bool.noConfusion hVer.2.1
  · intro hVer
    have hEq : canarySafeUnitBody = canaryUnsafeGuardedBody false := by
      injection hVer.1
    have hArg : (canarySafeUnitBody).argumentCount =
        (canaryUnsafeGuardedBody false).argumentCount :=
      congrArg Body.argumentCount hEq
    exact Nat.noConfusion hArg
  · intro hVer
    have hEq : canaryUnsafeGuardedBody false = canaryNeverParamBody false := by
      injection hVer.1
    have hLoc : (canaryUnsafeGuardedBody false).locals =
        (canaryNeverParamBody false).locals :=
      congrArg Body.locals hEq
    injection hLoc with hHead
    exact MirTy.noConfusion hHead
  · intro hCrate
    exact Bool.noConfusion hCrate.2.2.2.1
  · intro hUnit
    exact Bool.noConfusion hUnit.2.2.2.2.1
  · intro hCrate
    exact Bool.noConfusion hCrate.2.2.2.2.2.1
  · intro hCrate
    have hVer :=
      hCrate.2.2.2.2.2.2.1 1 (canaryUnsafeGuardedBody false) rfl
    have hWf := hVer.2.2 [.bool false] rfl (fun h => Bool.noConfusion h)
    have hNeg : NegativeCanaryClaim
        (entryProgForBody {
          scope := .crate
          pointerWidthBits := 64
          mirProfileVersion := 1
          bodies := [canarySafeUnitBody, canaryUnsafeGuardedBody false]
        } 1)
        { args := [.bool false] } .undefined .unsupported :=
      negativeCanary_of_execFault (fuel := 2)
        (fun h => FaultKind.noConfusion h) rfl
    exact hNeg.2.2 hWf
  · intro hCrate
    exact hCrate.2.2.2.2.2.2.2
  · intro hUnit
    exact hUnit.2.2.2.2.2.2.2
  · intro hCrate
    exact VerificationScope.noConfusion hCrate.1
  · intro hUnit
    exact VerificationScope.noConfusion hUnit.1

/-- Memory-lifecycle canary: `forceAllocation`, `.indirect` reads, writes,
moves, discriminant reads, and returns, `StorageLive` / `StorageDead`
deallocation, use-after-free, uninitialized-byte reads, and type checks that
precede memory reads, all evaluated by the kernel. -/
theorem canary_memory_lifecycle_anneal_base :
    CanaryMemoryLifecycleAnnealClaim :=
  ⟨positiveCanary_of_exec (fuel := 5) rfl,
   ⟨_, _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   ⟨_, _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   ⟨_, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl⟩,
   ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- `char` and `BinOp.cmp` canary: `char` comparisons, `Cmp` on `char`, signed
and unsigned integers, the discriminant of an `Ordering`, and `switchInt` on a
`char`, all evaluated by the kernel. -/
theorem canary_positive_char_and_cmp_anneal_base :
    CanaryPositiveCharAndCmpAnnealClaim :=
  ⟨positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 3) rfl,
   positiveCanary_of_exec (fuel := 3) rfl,
   positiveCanary_of_exec (fuel := 3) rfl⟩

/-- Negative `char` and `BinOp.cmp` canary: an invalid `char` constant and an
invalid `char` switch case are UB, while `Cmp` on `bool` and `Not` on `char`
are unsupported. -/
theorem canary_negative_char_and_cmp_anneal_base :
    CanaryNegativeCharAndCmpAnnealClaim :=
  ⟨negativeCanary_of_execFault (fuel := 1)
     (fun h => FaultKind.noConfusion h) rfl,
   negativeCanary_of_execFault (fuel := 1)
     (fun h => FaultKind.noConfusion h) rfl,
   negativeCanary_of_execFault (fuel := 1)
     (fun h => FaultKind.noConfusion h) rfl,
   negativeCanary_of_execFault (fuel := 1)
     (fun h => FaultKind.noConfusion h) rfl⟩

/-- Overflowing arithmetic canary (`BinOp.{add,sub,mul}WithOverflow`) across
unsigned, signed, and 128-bit operands. -/
theorem canary_positive_overflow_ops_anneal_base :
    CanaryPositiveOverflowOpsAnnealClaim :=
  ⟨positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl⟩

/-- `CastKind.intToInt` canary: sign extension, zero extension, truncation, and
`bool`, `char`, and `u8`-to-`char` conversions. -/
theorem canary_positive_int_to_int_cast_anneal_base :
    CanaryPositiveIntToIntCastAnnealClaim :=
  ⟨positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl⟩

/-- Negative `CastKind.intToInt` canary: non-`u8` values to `char` and casts to
`bool` are unsupported, and casting an uninitialized local is UB. -/
theorem canary_negative_int_to_int_cast_anneal_base :
    CanaryNegativeIntToIntCastAnnealClaim :=
  ⟨negativeCanary_of_execFault (fuel := 1)
     (fun h => FaultKind.noConfusion h) rfl,
   negativeCanary_of_execFault (fuel := 1)
     (fun h => FaultKind.noConfusion h) rfl,
   negativeCanary_of_execFault (fuel := 1)
     (fun h => FaultKind.noConfusion h) rfl,
   negativeCanary_of_execFault (fuel := 2)
     (fun h => FaultKind.noConfusion h) rfl⟩

end Anneal.MirWp

end
