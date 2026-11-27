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
public import Anneal.MirWp.Execution
public import Anneal.MirWp.V2Memory

public section

namespace Anneal.MirWp

open Trusted.MirAst Trusted.MirSemantics

/-! ## Concrete Day-1 Non-Vacuity and Parameter-Boundary Canaries -/

/-- Canary `D1`: `progAddU32` on `(30, 12)` is well-formed and returns `42`. -/
theorem canary_positive_add_anneal : CanaryPositiveAddAnnealClaim :=
  positiveCanary_of_exec (fuel := 2) rfl

/-- Canary `D2`: `progEmptyUnitFn` is well-formed and returns `Val.unit`. -/
theorem canary_positive_empty_unit_fn : CanaryPositiveEmptyUnitFnClaim :=
  positiveCanary_of_exec (fuel := 1) rfl

/-- Control-flow and statement canary (`nop`, `storageLive`, `storageDead`,
`goto`, and both matched and `otherwise` arms of `switchInt`). -/
theorem canary_positive_stmts_and_cf_anneal :
    CanaryPositiveStmtsAndCfAnnealClaim :=
  ⟨positiveCanary_of_exec (fuel := 10) rfl,
   positiveCanary_of_exec (fuel := 10) rfl⟩

/-- Unary-operator canary (`UnOp.not` on `bool` and `u8`, `UnOp.neg` on signed
`i8` including wrapping `-INT_MIN == INT_MIN`). -/
theorem canary_positive_unop_anneal : CanaryPositiveUnopAnnealClaim :=
  ⟨positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl⟩

/-- Binary-operator canary covering every supported `BinOp` variant at boundary
values across unsigned integers, signed integers, shifts, and booleans. -/
theorem canary_positive_all_binops_anneal :
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
theorem canary_positive_all_int_widths_anneal :
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
theorem canary_negative_ub_div_zero_anneal :
    CanaryNegativeUbDivZeroAnnealClaim :=
  negativeCanary_of_execFault (fuel := 1)
    (fun h => FaultKind.noConfusion h) rfl

/-- Canary `D4`: signed `(-128i8) % (-1i8)` reaches `.fault .undefined` (and
not `.fault .unsupported`) and refutes `WellFormed`. -/
theorem canary_negative_ub_signed_rem_overflow_i8 :
    CanaryNegativeUbSignedRemOverflowI8Claim :=
  negativeCanary_of_execFault (fuel := 1)
    (fun h => FaultKind.noConfusion h) rfl

/-- Canary `D5`: executing `.unsupported` reaches `.fault .unsupported` (and
not `.fault .undefined`) and refutes `WellFormed`. -/
theorem canary_negative_unsupported_anneal :
    CanaryNegativeUnsupportedAnnealClaim :=
  negativeCanary_of_execFault (fuel := 1)
    (fun h => FaultKind.noConfusion h) rfl

/-- Unchecked-overflow canary: on `(u32::MAX, 1)`, `AddUnchecked`
(`progAddUncheckedU32`) reaches `.fault .undefined` (and not
`.fault .unsupported`) and refutes `WellFormed`, while wrapping `Add`
(`progAddU32`) on the same inputs is well-formed and returns `0`. -/
theorem canary_negative_ub_add_unchecked_overflow_u32 :
    CanaryNegativeUbAddUncheckedOverflowU32Claim :=
  ⟨negativeCanary_of_execFault (fuel := 1)
     (fun h => FaultKind.noConfusion h) rfl,
   positiveCanary_of_exec (fuel := 2) rfl⟩

/-- Shift-overflow canary: `ShlUnchecked` at shift amount `== bitWidth` (`32`
on `u32`) and `ShrUnchecked` at negative signed shift (`-1i8` on `u32`) both
reach `.fault .undefined` (and not `.fault .unsupported`). -/
theorem canary_negative_ub_shift_unchecked_at_bitwidth_anneal :
    CanaryNegativeUbShiftUncheckedAtBitwidthAnnealClaim :=
  ⟨negativeCanary_of_execFault (fuel := 1)
     (fun h => FaultKind.noConfusion h) rfl,
   negativeCanary_of_execFault (fuel := 1)
     (fun h => FaultKind.noConfusion h) rfl⟩

/-- Storage-dead read canary: reading a local after `StatementKind.storageDead`
reaches `.fault .undefined` (and not `.fault .unsupported`). -/
theorem canary_negative_ub_storage_dead_read_anneal :
    CanaryNegativeUbStorageDeadReadAnnealClaim :=
  negativeCanary_of_execFault (fuel := 4)
    (fun h => FaultKind.noConfusion h) rfl

/-- Storage-dead return-place canary: executing `StatementKind.storageDead 0`
on `_0` reaches `.fault .unsupported` (and not `.fault .undefined`). -/
theorem canary_negative_ub_storage_dead_return_place_anneal :
    CanaryNegativeUbStorageDeadReturnPlaceAnnealClaim :=
  negativeCanary_of_execFault (fuel := 1)
    (fun h => FaultKind.noConfusion h) rfl

/-- Unreachable terminator canary: executing `TerminatorKind.unreachable`
reaches `.fault .undefined` (and not `.fault .unsupported`). -/
theorem canary_negative_ub_unreachable_anneal :
    CanaryNegativeUbUnreachableAnnealClaim :=
  negativeCanary_of_execFault (fuel := 1)
    (fun h => FaultKind.noConfusion h) rfl

/-- Unsigned-negation canary: executing `UnOp.neg` on an unsigned integer
(`u32`) reaches `.fault .unsupported` (and not `.fault .undefined`). -/
theorem canary_negative_unsupported_unsigned_neg_anneal :
    CanaryNegativeUnsupportedUnsignedNegAnnealClaim :=
  negativeCanary_of_execFault (fuel := 1)
    (fun h => FaultKind.noConfusion h) rfl

/-- Explicit-repr fieldless enum positive canary: `#[repr(u8)]` non-index tag
decoding + `u8` `Rvalue.discriminant` and signed `i8` -> `isize` sign-extended
tag decoding. -/
theorem canary_positive_enum_explicit_repr_anneal :
    CanaryPositiveEnumExplicitReprAnnealClaim :=
  ⟨positiveCanary_of_exec (fuel := 5) rfl,
   positiveCanary_of_exec (fuel := 5) rfl⟩

/-- Single-variant inhabited ZST enum positive canary: implicit return without
writing `_0`, non-deinitializing `Operand.move`, `ConstLit.zeroSized`, and
`Rvalue.discriminant`. -/
theorem canary_positive_zst_single_enum_anneal :
    CanaryPositiveZstSingleEnumAnnealClaim :=
  ⟨positiveCanary_of_exec (fuel := 1) rfl,
   positiveCanary_of_exec (fuel := 10) rfl⟩

/-- Fieldless enum negative UB canary: invalid constant scalar tag `1` on
`ReprU8 { A = 10, B = 20 }` and reading `Rvalue.discriminant` from an
uninitialized scalar-tagged enum local both reach `.fault .undefined`. -/
theorem canary_negative_ub_enum_invalid_tag_and_uninit_anneal :
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
theorem canary_crate_and_body_verified_anneal :
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
theorem canary_memory_lifecycle_anneal :
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
theorem canary_positive_char_and_cmp_anneal :
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
theorem canary_negative_char_and_cmp_anneal :
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
theorem canary_positive_overflow_ops_anneal :
    CanaryPositiveOverflowOpsAnnealClaim :=
  ⟨positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl⟩

/-- `CastKind.intToInt` canary: sign extension, zero extension, truncation, and
`bool`, `char`, and `u8`-to-`char` conversions. -/
theorem canary_positive_int_to_int_cast_anneal :
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
theorem canary_negative_int_to_int_cast_anneal :
    CanaryNegativeIntToIntCastAnnealClaim :=
  ⟨negativeCanary_of_execFault (fuel := 1)
     (fun h => FaultKind.noConfusion h) rfl,
   negativeCanary_of_execFault (fuel := 1)
     (fun h => FaultKind.noConfusion h) rfl,
   negativeCanary_of_execFault (fuel := 1)
     (fun h => FaultKind.noConfusion h) rfl,
   negativeCanary_of_execFault (fuel := 2)
     (fun h => FaultKind.noConfusion h) rfl⟩

/-! ## Abstract-Modulus Cast, Scalar-Op, and Flat `entryLocals` Canaries -/

/-- Symbolic negative `isize as usize` cast canary exercising
`evalIntToIntCast_signed_of_neg` on an arbitrary negative 64-bit `isize` bit
pattern without triggering kernel recursion on `Int.subNatNat (2^128) k`. -/
theorem canary_symbolic_neg_isize_to_usize_cast (b : BitVec 128)
    (hGe : intWidthHalfModulus .isize ≤ b.toNat)
    (hLt : b.toNat < intWidthModulus .isize) :
    evalIntToIntCast (.scalar ⟨.isize, true, b⟩) (.int .isize false) =
      .ok (.scalar ⟨.isize, false,
        BitVec.ofNat 128
          (intWidthModulus .isize -
            (Nat.mod (intWidthModulus .isize - b.toNat - 1) (intWidthModulus .isize) + 1))⟩) :=
  evalIntToIntCast_signed_of_neg .isize .isize false hGe hLt

/-- Concrete negative `-1isize as usize` (`b = 2^64 - 1`) cast canary showing
that `evalIntToIntCast_signed_same_width` avoids the `#4295` kernel deep
recursion trap on concrete 64-bit negative bit patterns. -/
theorem canary_concrete_neg1_isize_to_usize_cast :
    evalIntToIntCast
      (.scalar ⟨.isize, true, BitVec.ofNat 128 (Nat.pow 2 64 - 1)⟩)
      (.int .isize false) =
    .ok (.scalar ⟨.isize, false, BitVec.ofNat 128 (Nat.pow 2 64 - 1)⟩) :=
  evalIntToIntCast_signed_same_width (wSrc := .isize) (wDst := .isize)
    false rfl (by decide)

/-- Symbolic widening signed `i8 as i64` negative cast canary exercising
`evalIntToIntCast_signed_of_neg` across distinct widths (`2^8 ∣ 2^64`). -/
theorem canary_symbolic_neg_i8_to_i64_cast (b : BitVec 128)
    (hGe : intWidthHalfModulus .i8 ≤ b.toNat)
    (hLt : b.toNat < intWidthModulus .i8) :
    evalIntToIntCast (.scalar ⟨.i8, true, b⟩) (.int .i64 true) =
      .ok (.scalar ⟨.i64, true,
        BitVec.ofNat 128
          (intWidthModulus .i64 -
            (Nat.mod (intWidthModulus .i8 - b.toNat - 1) (intWidthModulus .i64) + 1))⟩) :=
  evalIntToIntCast_signed_of_neg .i8 .i64 true hGe hLt

/-- Symbolic `decodeScalar` + `evalBinOp` unsigned width-parametric canary
exercising `evalBinOp_bitAnd_eq`, `evalBinOp_add_unsigned_eq`, and
`evalBinOp_cmp_eq` without concrete width unfolding. -/
theorem canary_symbolic_scalar_ops (w : IntWidth) (b1 b2 : BitVec 128)
    (h1 : b1.toNat < intWidthModulus w)
    (h2 : b2.toNat < intWidthModulus w) :
    evalBinOp .bitAnd (.scalar ⟨w, false, b1⟩) (.scalar ⟨w, false, b2⟩) =
      .ok (.scalar ⟨w, false, truncateBits w (BitVec.ofNat 128 (Nat.land b1.toNat b2.toNat))⟩) ∧
    evalBinOp .add (.scalar ⟨w, false, b1⟩) (.scalar ⟨w, false, b2⟩) =
      .ok (.scalar ⟨w, false,
        BitVec.ofNat 128 (Nat.mod (b1.toNat + b2.toNat) (intWidthModulus w))⟩) ∧
    evalBinOp .lt (.scalar ⟨w, false, b1⟩) (.scalar ⟨w, false, b2⟩) =
      .ok (.bool (decide (decodeScalar ⟨w, false, b1⟩ < decodeScalar ⟨w, false, b2⟩))) :=
  ⟨evalBinOp_bitAnd_eq w false b1 b2 h1 h2,
   evalBinOp_add_unsigned_eq w h1 h2,
   (evalBinOp_cmp_eq w false b1 b2).2.2.1⟩

/-- Fixture body shared by `canary_flat_entryLocals_eq`. -/
@[expose] def canaryFlatEntryLocalsBody : Body :=
  { identity := "canary_flat_entry_locals"
    argumentCount := 1
    locals := [.int .isize false, .int .isize false, .int .isize false, .bool]
    basicBlocks := [
      { statements := [.storageLive 2, .storageDead 2]
        terminator := .return_
        cleanup := false }
    ] }

/-- Flat `entryLocals` equivalence canary verifying that `entryLocals` matches
`initLocalsLoop` identically on a multi-local body with storage annotations. -/
theorem canary_flat_entryLocals_eq (args : List Val)
    (hValid : ValidEntryArgs canaryFlatEntryLocalsBody args) :
    initLocalsLoop canaryFlatEntryLocalsBody args 0
        canaryFlatEntryLocalsBody.locals =
      entryLocals canaryFlatEntryLocalsBody args [.dead, .immediate none] :=
  initLocalsLoop_eq_entryLocals hValid (by decide) rfl

@[expose] def usizeTyV2 : MirTy := .int .isize false

@[expose] def divUsizeBodyV2 : Body := {
  argumentCount := 2
  locals := [usizeTyV2, usizeTyV2, usizeTyV2, .bool]
  basicBlocks := [
    {
      statements := [
        .assign ⟨3, []⟩
          (.binaryOp .eq (.copy ⟨2, []⟩)
            (.constant ⟨usizeTyV2, .scalar (BitVec.ofNat 128 0)⟩))
      ]
      terminator := .assert (.copy ⟨3, []⟩) false .divByZero 1 .continue_
    },
    {
      statements := [
        .assign ⟨0, []⟩ (.binaryOp .div (.copy ⟨1, []⟩) (.copy ⟨2, []⟩))
      ]
      terminator := .return_
    }
  ]
  isUnsafe := false
  identity := "canary::div_usize_v2"
}

@[expose] def divUsizeProgV2 (ps : PanicStrategy := .abort) : Program := {
  entryDefId := 0
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 2
  panicStrategy := ps
  hasLocalPanicHandler := false
  bodies := [divUsizeBodyV2]
}

@[expose] def divUsizeRetVal (a b : ScalarVal) : Val :=
  .scalar ⟨.isize, false, BitVec.ofNat 128 (Nat.div a.bits.toNat b.bits.toNat)⟩

@[expose] def divUsizeContractAllowAbort : SafeContractV2 := {
  behaviorPre := fun _ => True
  effects := { allowAbort := true }
  postReturn := fun q out =>
    match q.args with
    | [.scalar a, .scalar b] => out = ⟨divUsizeRetVal a b, q.callerMem⟩
    | _ => False
  postAbort := fun q cm => cm = q.callerMem
}

@[expose] def divUsizeContractNoAbort : SafeContractV2 := {
  behaviorPre := fun q =>
    match q.args with
    | [_, .scalar b] => b.bits.toNat ≠ 0
    | _ => False
  effects := EffectMaskV2.noAbort
  postReturn := fun q out =>
    match q.args with
    | [.scalar a, .scalar b] => out = ⟨divUsizeRetVal a b, q.callerMem⟩
    | _ => False
}

private theorem execStateV2_step {p : Program} {fuel : Nat} {s s' : State}
    {post : TerminalOut → Prop}
    (h_step : evalStepV2 p s = .step s')
    (h_next : execStateV2 p fuel s' post) :
    execStateV2 p (fuel + 1) s post := by
  change (match evalStepV2 p s with
    | .step st' => execStateV2 p fuel st' post
    | .done out => post out
    | .fault _ => False)
  rw [h_step]
  exact h_next

private theorem execStateV2_done {p : Program} {fuel : Nat} {s : State}
    {out : TerminalOut} {post : TerminalOut → Prop}
    (h_step : evalStepV2 p s = .done out)
    (h_post : post out) :
    execStateV2 p (fuel + 1) s post := by
  change (match evalStepV2 p s with
    | .step st' => execStateV2 p fuel st' post
    | .done out => post out
    | .fault _ => False)
  rw [h_step]
  exact h_post

private theorem scalarVal_isize_toNat_lt {sv : ScalarVal}
    (hWf : sv.wf = true) (hW : sv.width = .isize) :
    sv.bits.toNat < Nat.pow 2 64 := by
  unfold ScalarVal.wf at hWf
  rw [hW] at hWf
  have hTr : truncateBits .isize sv.bits = sv.bits := eq_of_beq hWf
  rw [← hTr, toNat_truncateBits]
  exact Nat.mod_lt _ (by decide)

private theorem divUsize_eq_evalBinOp (bBits : BitVec 128)
    (hB : truncateBits .isize bBits = bBits) :
    evalBinOp .eq (.scalar ⟨.isize, false, bBits⟩)
      (.scalar ⟨.isize, false, BitVec.ofNat 128 0⟩) =
      .ok (.bool (bBits.toNat == 0)) := by
  dsimp only [evalBinOp, decodeScalar]
  rw [hB]
  change (if false then Except.error FaultKind.unsupported
    else if false then Except.error FaultKind.unsupported
    else Except.ok (Val.bool (Int.ofNat bBits.toNat == (0 : Int)))) =
    Except.ok (Val.bool (bBits.toNat == 0))
  cases bBits.toNat <;> rfl

private theorem divUsize_div_evalBinOp (aBits bBits : BitVec 128)
    (hA : truncateBits .isize aBits = aBits)
    (hB : truncateBits .isize bBits = bBits)
    (hLt : aBits.toNat < Nat.pow 2 64)
    (hNz : (bBits.toNat == 0) = false) :
    evalBinOp .div (.scalar ⟨.isize, false, aBits⟩)
      (.scalar ⟨.isize, false, bBits⟩) =
      .ok (.scalar ⟨.isize, false,
        BitVec.ofNat 128 (Nat.div aBits.toNat bBits.toNat)⟩) := by
  have hDivLt : Nat.div aBits.toNat bBits.toNat < Nat.pow 2 64 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hLt
  have hDiv128 : Nat.div aBits.toNat bBits.toNat < Nat.pow 2 128 :=
    Nat.lt_trans hDivLt (by decide)
  have hR0 : ((Int.ofNat bBits.toNat == (0 : Int))) = false := by
    cases hN : bBits.toNat with
    | zero => rw [hN] at hNz; cases hNz
    | succ _ => rfl
  have hMod128 :
      (intEmod (Int.ofNat (Nat.div aBits.toNat bBits.toNat))
        (Int.ofNat (Nat.pow 2 128))).toNat = Nat.div aBits.toNat bBits.toNat := by
    have hM : Nat.mod (Nat.div aBits.toNat bBits.toNat) (Nat.pow 2 128) =
        Nat.div aBits.toNat bBits.toNat :=
      Nat.mod_eq_of_lt hDiv128
    change (Int.ofNat (Nat.mod (Nat.div aBits.toNat bBits.toNat)
      (Nat.pow 2 128))).toNat = Nat.div aBits.toNat bBits.toNat
    rw [hM]
    rfl
  have hTrEq :
      truncateBits .isize (BitVec.ofNat 128 (Nat.div aBits.toNat bBits.toNat)) =
        BitVec.ofNat 128 (Nat.div aBits.toNat bBits.toNat) := by
    apply bitVec_eq_of_toNat_eq
    rw [toNat_truncateBits]
    have hBv :
        (BitVec.ofNat 128 (Nat.div aBits.toNat bBits.toNat)).toNat =
          Nat.mod (Nat.div aBits.toNat bBits.toNat) (Nat.pow 2 128) := rfl
    have hM128 : Nat.mod (Nat.div aBits.toNat bBits.toNat) (Nat.pow 2 128) =
        Nat.div aBits.toNat bBits.toNat :=
      Nat.mod_eq_of_lt hDiv128
    rw [hBv, hM128]
    exact Nat.mod_eq_of_lt hDivLt
  dsimp only [evalBinOp, evalArithOp, decodeScalar]
  rw [hA, hB]
  change (if false then Except.error FaultKind.unsupported
    else if false then Except.error FaultKind.unsupported
    else if true && (Int.ofNat bBits.toNat == (0 : Int)) then Except.error FaultKind.undefined
    else if false && true &&
        (Int.ofNat aBits.toNat == signedMinInt .isize &&
          Int.ofNat bBits.toNat == Neg.neg 1) then Except.error FaultKind.undefined
    else
      match truncateScalar .isize false
          (intTdiv (Int.ofNat aBits.toNat) (Int.ofNat bBits.toNat)) with
      | .error k => Except.error k
      | .ok (val, lossy) =>
        if ((decide (intTdiv (Int.ofNat aBits.toNat) (Int.ofNat bBits.toNat) < 0) ||
            decide (intTdiv (Int.ofNat aBits.toNat) (Int.ofNat bBits.toNat) ≥
              HPow.hPow (2 : Int) 128)) || lossy) && false then Except.error FaultKind.undefined
        else if false then Except.error FaultKind.unsupported
        else Except.ok (Val.scalar val)) = _
  rw [hR0]
  dsimp only [truncateScalar, intTdiv, bvOfInt]
  rw [hMod128, hTrEq]
  simp [Bool.and_false, bne_self_eq_false]

private theorem divUsize_init_ok (ps : PanicStrategy) {q : Query}
    (hValid : ValidEntryArgsV2 divUsizeBodyV2 q) :
    ∃ a b : ScalarVal,
      a.width = .isize ∧ a.signed = false ∧ a.wf = true ∧
      b.width = .isize ∧ b.signed = false ∧ b.wf = true ∧
      q.args = [.scalar a, .scalar b] ∧
      validCallerMemory q.callerMem = true ∧
      initStateV2 (divUsizeProgV2 ps) q =
        .ok ⟨[⟨0, 0, 0,
            [.immediate none, .immediate (some (.scalar a)),
              .immediate (some (.scalar b)), .immediate none],
            none, none, none⟩],
          q.callerMem, entryMemoryWithCaller q.callerMem⟩ := by
  let ⟨hCM, hArgs, _, _⟩ := hValid
  dsimp only [divUsizeBodyV2] at hArgs
  change checkArgsMatchV2 q.args [usizeTyV2, usizeTyV2] = true at hArgs
  cases hA0 : q.args with
  | nil => rw [hA0] at hArgs; cases hArgs
  | cons v1 tl1 =>
    rw [hA0] at hArgs
    dsimp only [checkArgsMatchV2] at hArgs
    cases hC1 : checkValV2 v1 usizeTyV2 with
    | false => rw [hC1] at hArgs; cases hArgs
    | true =>
      rw [hC1] at hArgs
      change checkArgsMatchV2 tl1 [usizeTyV2] = true at hArgs
      cases tl1 with
      | nil => cases hArgs
      | cons v2 tl2 =>
        dsimp only [checkArgsMatchV2] at hArgs
        cases hC2 : checkValV2 v2 usizeTyV2 with
        | false => rw [hC2] at hArgs; cases hArgs
        | true =>
          rw [hC2] at hArgs
          change checkArgsMatchV2 tl2 [] = true at hArgs
          cases tl2 with
          | cons _ _ => cases hArgs
          | nil =>
            let ⟨a, haEq, hWA, hSA, hWfA⟩ := checkValV2_isize_scalar hC1
            let ⟨b, hbEq, hWB, hSB, hWfB⟩ := checkValV2_isize_scalar hC2
            subst haEq; subst hbEq
            refine ⟨a, b, hWA, hSA, hWfA, hWB, hSB, hWfB, rfl, hCM, ?_⟩
            have hArgs' : checkArgsMatchV2 q.args
                ((divUsizeBodyV2.locals.drop 1).take divUsizeBodyV2.argumentCount) = true := by
              rw [hA0]
              dsimp only [checkArgsMatchV2, checkValV2, checkVal, Val.ty?,
                divUsizeBodyV2, usizeTyV2, List.drop, List.take]
              rw [hWfA, hWfB, hWA, hWB, hSA, hSB]; rfl
            have hRefs' : refsValidInMemList (entryMemoryWithCaller q.callerMem)
                ((divUsizeBodyV2.locals.drop 1).take divUsizeBodyV2.argumentCount) q.args = true := by
              rw [hA0]; rfl
            have hDisj' : spansPairwiseDisjoint (refAccessSpansList
                ((divUsizeBodyV2.locals.drop 1).take divUsizeBodyV2.argumentCount) q.args) = true := by
              rw [hA0]; rfl
            have hOk := initStateV2_ok_of (p := divUsizeProgV2 ps) (q := q)
              (body := divUsizeBodyV2) rfl rfl hCM rfl rfl rfl rfl rfl rfl rfl rfl
              hArgs' hRefs' hDisj'
            rw [hA0] at hOk
            exact hOk

private theorem divUsize_step_bb0_eq
    (ps : PanicStrategy) (a b : ScalarVal) (cm : CallerMemory) (res : Bool)
    (hbEq : b = ⟨.isize, false, b.bits⟩)
    (hEqOp : evalBinOp .eq (.scalar ⟨.isize, false, b.bits⟩)
      (.scalar ⟨.isize, false, BitVec.ofNat 128 0⟩) = .ok (.bool res)) :
    evalStepV2 (divUsizeProgV2 ps)
      ⟨[⟨0, 0, 0,
          [.immediate none, .immediate (some (.scalar a)),
            .immediate (some (.scalar b)), .immediate none],
          none, none, none⟩],
        cm, entryMemoryWithCaller cm⟩ =
      .step ⟨[⟨0, 0, 1,
          [.immediate none, .immediate (some (.scalar a)),
            .immediate (some (.scalar b)), .immediate (some (.bool res))],
          none, none, none⟩],
        cm, entryMemoryWithCaller cm⟩ := by
  have hSup : (!isSupportedV2LocalTy usizeTyV2) = false := rfl
  have hPrim : (!isPrimitiveReadableTy usizeTyV2) = false := rfl
  have hZTr : (truncateBits .isize (BitVec.ofNat 128 0) != BitVec.ofNat 128 0) = false := rfl
  have hChk : (!checkValV2 (.bool res) .bool) = false := by cases res <;> rfl
  have hRv :
      evalRvalueV2 divUsizeBodyV2.locals
        [.immediate none, .immediate (some (.scalar a)),
          .immediate (some (.scalar b)), .immediate none]
        (entryMemoryWithCaller cm) .bool
        (.binaryOp .eq (.copy ⟨2, []⟩)
          (.constant ⟨usizeTyV2, .scalar (BitVec.ofNat 128 0)⟩)) =
        .ok (.bool res,
          [.immediate none, .immediate (some (.scalar a)),
            .immediate (some (.scalar b)), .immediate none],
          entryMemoryWithCaller cm) := by
    have hOp1 :
        evalPrimitiveOperandV2 divUsizeBodyV2.locals
          [.immediate none, .immediate (some (.scalar a)),
            .immediate (some (.scalar b)), .immediate none]
          (entryMemoryWithCaller cm) (.copy ⟨2, []⟩) =
          .ok (.scalar b,
            [.immediate none, .immediate (some (.scalar a)),
              .immediate (some (.scalar b)), .immediate none],
            entryMemoryWithCaller cm) := rfl
    have hOp2 :
        evalPrimitiveOperandV2 divUsizeBodyV2.locals
          [.immediate none, .immediate (some (.scalar a)),
            .immediate (some (.scalar b)), .immediate none]
          (entryMemoryWithCaller cm)
          (.constant ⟨usizeTyV2, .scalar (BitVec.ofNat 128 0)⟩) =
          .ok (.scalar ⟨.isize, false, BitVec.ofNat 128 0⟩,
            [.immediate none, .immediate (some (.scalar a)),
              .immediate (some (.scalar b)), .immediate none],
            entryMemoryWithCaller cm) := rfl
    unfold evalRvalueV2
    dsimp only
    rw [hOp1]
    dsimp only
    rw [hOp2]
    dsimp only
    rw [hbEq, hEqOp]
  have hWr :
      writePlaceDestV2
        [.immediate none, .immediate (some (.scalar a)),
          .immediate (some (.scalar b)), .immediate none]
        (entryMemoryWithCaller cm) (.local 3) .bool (.bool res) =
        .ok ([.immediate none, .immediate (some (.scalar a)),
              .immediate (some (.scalar b)), .immediate (some (.bool res))],
          entryMemoryWithCaller cm) := by
    unfold writePlaceDestV2
    simp [hChk, Trusted.MirSemantics.getElem?, Trusted.MirSemantics.setElem?]
  unfold evalStepV2
  dsimp only [divUsizeProgV2, divUsizeBodyV2, Trusted.MirSemantics.getElem?]
  change evalStatementV2 divUsizeBodyV2
      ⟨0, 0, 0, [.immediate none, .immediate (some (.scalar a)),
        .immediate (some (.scalar b)), .immediate none], none, none, none⟩
      (entryMemoryWithCaller cm) cm
      (.assign ⟨3, []⟩ (.binaryOp .eq (.copy ⟨2, []⟩)
        (.constant ⟨usizeTyV2, .scalar (BitVec.ofNat 128 0)⟩))) = _
  unfold evalStatementV2
  change (match evalRvalueV2 divUsizeBodyV2.locals
      [.immediate none, .immediate (some (.scalar a)),
        .immediate (some (.scalar b)), .immediate none]
      (entryMemoryWithCaller cm) .bool
      (.binaryOp .eq (.copy ⟨2, []⟩)
        (.constant ⟨usizeTyV2, .scalar (BitVec.ofNat 128 0)⟩)) with
    | .error k => StepResult.fault k
    | .ok (val, locals1, mem1) =>
      match writePlaceDestV2 locals1 mem1 (.local 3) .bool val with
      | .error k => StepResult.fault k
      | .ok (locals2, mem2) =>
        StepResult.step ({
          frames := [{ defId := 0, blockIdx := 0, stmtIdx := 1, locals := locals2 }]
          callerMem := cm
          mem := mem2
        } : State)) = _
  rw [hRv]
  dsimp only
  rw [hWr]

private theorem divUsize_step_bb1_div
    (ps : PanicStrategy) (a b : ScalarVal) (cm : CallerMemory)
    (haEq : a = ⟨.isize, false, a.bits⟩)
    (hbEq : b = ⟨.isize, false, b.bits⟩)
    (hDivOp : evalBinOp .div (.scalar ⟨.isize, false, a.bits⟩)
      (.scalar ⟨.isize, false, b.bits⟩) = .ok (divUsizeRetVal a b))
    (hOutWf : (⟨.isize, false,
      BitVec.ofNat 128 (Nat.div a.bits.toNat b.bits.toNat)⟩ : ScalarVal).wf = true) :
    evalStepV2 (divUsizeProgV2 ps)
      ⟨[⟨0, 1, 0,
          [.immediate none, .immediate (some (.scalar a)),
            .immediate (some (.scalar b)), .immediate (some (.bool false))],
          none, none, none⟩],
        cm, entryMemoryWithCaller cm⟩ =
      .step ⟨[⟨0, 1, 1,
          [.immediate (some (divUsizeRetVal a b)), .immediate (some (.scalar a)),
            .immediate (some (.scalar b)), .immediate (some (.bool false))],
          none, none, none⟩],
        cm, entryMemoryWithCaller cm⟩ := by
  have hSup : (!isSupportedV2LocalTy usizeTyV2) = false := rfl
  have hPrim : (!isPrimitiveReadableTy usizeTyV2) = false := rfl
  have hChk : (!checkValV2 (divUsizeRetVal a b) usizeTyV2) = false := by
    dsimp only [checkValV2, checkVal, Val.ty?, MirTy.beq, divUsizeRetVal, usizeTyV2]
    rw [hOutWf]
    rfl
  have hRv :
      evalRvalueV2 divUsizeBodyV2.locals
        [.immediate none, .immediate (some (.scalar a)),
          .immediate (some (.scalar b)), .immediate (some (.bool false))]
        (entryMemoryWithCaller cm) usizeTyV2
        (.binaryOp .div (.copy ⟨1, []⟩) (.copy ⟨2, []⟩)) =
        .ok (divUsizeRetVal a b,
          [.immediate none, .immediate (some (.scalar a)),
            .immediate (some (.scalar b)), .immediate (some (.bool false))],
          entryMemoryWithCaller cm) := by
    have hOp1 :
        evalPrimitiveOperandV2 divUsizeBodyV2.locals
          [.immediate none, .immediate (some (.scalar a)),
            .immediate (some (.scalar b)), .immediate (some (.bool false))]
          (entryMemoryWithCaller cm) (.copy ⟨1, []⟩) =
          .ok (.scalar a,
            [.immediate none, .immediate (some (.scalar a)),
              .immediate (some (.scalar b)), .immediate (some (.bool false))],
            entryMemoryWithCaller cm) := rfl
    have hOp2 :
        evalPrimitiveOperandV2 divUsizeBodyV2.locals
          [.immediate none, .immediate (some (.scalar a)),
            .immediate (some (.scalar b)), .immediate (some (.bool false))]
          (entryMemoryWithCaller cm) (.copy ⟨2, []⟩) =
          .ok (.scalar b,
            [.immediate none, .immediate (some (.scalar a)),
              .immediate (some (.scalar b)), .immediate (some (.bool false))],
            entryMemoryWithCaller cm) := rfl
    unfold evalRvalueV2
    dsimp only
    rw [hOp1]
    dsimp only
    rw [hOp2]
    dsimp only
    rw [haEq, hbEq, hDivOp]
    rfl
  have hWr :
      writePlaceDestV2
        [.immediate none, .immediate (some (.scalar a)),
          .immediate (some (.scalar b)), .immediate (some (.bool false))]
        (entryMemoryWithCaller cm) (.local 0) usizeTyV2 (divUsizeRetVal a b) =
        .ok ([.immediate (some (divUsizeRetVal a b)), .immediate (some (.scalar a)),
              .immediate (some (.scalar b)), .immediate (some (.bool false))],
          entryMemoryWithCaller cm) := by
    unfold writePlaceDestV2
    simp [hChk, Trusted.MirSemantics.getElem?, Trusted.MirSemantics.setElem?]
  unfold evalStepV2
  dsimp only [divUsizeProgV2, divUsizeBodyV2, Trusted.MirSemantics.getElem?]
  change evalStatementV2 divUsizeBodyV2
      ⟨0, 1, 0, [.immediate none, .immediate (some (.scalar a)),
        .immediate (some (.scalar b)), .immediate (some (.bool false))],
        none, none, none⟩
      (entryMemoryWithCaller cm) cm
      (.assign ⟨0, []⟩ (.binaryOp .div (.copy ⟨1, []⟩) (.copy ⟨2, []⟩))) = _
  unfold evalStatementV2
  change (match evalRvalueV2 divUsizeBodyV2.locals
      [.immediate none, .immediate (some (.scalar a)),
        .immediate (some (.scalar b)), .immediate (some (.bool false))]
      (entryMemoryWithCaller cm) usizeTyV2
      (.binaryOp .div (.copy ⟨1, []⟩) (.copy ⟨2, []⟩)) with
    | .error k => StepResult.fault k
    | .ok (val, locals1, mem1) =>
      match writePlaceDestV2 locals1 mem1 (.local 0) usizeTyV2 val with
      | .error k => StepResult.fault k
      | .ok (locals2, mem2) =>
        StepResult.step ({
          frames := [{ defId := 0, blockIdx := 1, stmtIdx := 1, locals := locals2 }]
          callerMem := cm
          mem := mem2
        } : State)) = _
  rw [hRv]
  dsimp only
  rw [hWr]

private theorem divUsize_abort_of_zero {ps : PanicStrategy} {q : Query}
    {a b : ScalarVal}
    (hCM : validCallerMemory q.callerMem = true)
    (hInit : initStateV2 (divUsizeProgV2 ps) q =
      .ok ⟨[⟨0, 0, 0,
          [.immediate none, .immediate (some (.scalar a)),
            .immediate (some (.scalar b)), .immediate none],
          none, none, none⟩],
        q.callerMem, entryMemoryWithCaller q.callerMem⟩)
    (hBW : b.width = .isize) (hBS : b.signed = false) (hBWf : b.wf = true)
    (hZero : b.bits.toNat = 0) :
    ∃ s1 : State,
      StepV2 (divUsizeProgV2 ps)
        ⟨[⟨0, 0, 0,
            [.immediate none, .immediate (some (.scalar a)),
              .immediate (some (.scalar b)), .immediate none],
            none, none, none⟩],
          q.callerMem, entryMemoryWithCaller q.callerMem⟩ (.step s1) ∧
      StepV2 (divUsizeProgV2 ps) s1
        (match ps with
         | .abort => .done (.aborted q.callerMem)
         | .unwind => .fault .unsupported) := by
  have hBTr : truncateBits .isize b.bits = b.bits := by
    unfold ScalarVal.wf at hBWf; rw [hBW] at hBWf; exact eq_of_beq hBWf
  have hbEq : b = ⟨.isize, false, b.bits⟩ := by
    cases b; subst hBW; subst hBS; rfl
  have hOp : evalBinOp .eq (.scalar ⟨.isize, false, b.bits⟩)
      (.scalar ⟨.isize, false, BitVec.ofNat 128 0⟩) = .ok (.bool true) := by
    rw [divUsize_eq_evalBinOp b.bits hBTr, hZero]; rfl
  refine ⟨⟨[⟨0, 0, 1,
      [.immediate none, .immediate (some (.scalar a)),
        .immediate (some (.scalar b)), .immediate (some (.bool true))],
      none, none, none⟩],
    q.callerMem, entryMemoryWithCaller q.callerMem⟩, ?_, ?_⟩
  · refine ⟨0, rfl, divUsize_step_bb0_eq ps a b q.callerMem true hbEq hOp⟩
  · refine ⟨0, rfl, ?_⟩
    unfold evalStepV2Choice evalStepV2 evalTerminatorV2 evalPrimitiveOperandV2
      evalOperandToSlotV2 readPlaceV2
    simp [divUsizeProgV2, divUsizeBodyV2, Trusted.MirSemantics.getElem?,
      isSupportedV2LocalTy, isPrimitiveReadableTy, evalAssertFailure]
    cases ps
    · rfl
    · dsimp only
      rw [extractCallerMemory_entry q.callerMem hCM]

/-- Pass-1 `SafeContractV2` and `EffectMaskV2` positive and negative non-vacuity
canaries on a 2-argument `usize` division MIR body:
1. `--panic abort` verifies `SafeContractV2` with `allowAbort := true` over all
   `ValidEntryArgsV2` inputs;
2. `--panic abort` verifies `EffectMaskV2.noAbort` when `behaviorPre` excludes
   division by zero (`b != 0`);
3. `--panic abort` rejects default fail-closed `SafeContractV2`
   (`allowAbort := false`) when `behaviorPre := True` fails to exclude `b = 0`;
4. `--panic unwind` rejects the panicking division body fail-closed even when
   `allowAbort := true` because non-abort panics fault `.unsupported`. -/
theorem canary_safe_contract_v2_div_usize :
    BodySatisfiesSafeContractV2 (divUsizeProgV2 .abort) 0 divUsizeBodyV2
      divUsizeContractAllowAbort ∧
    BodySatisfiesSafeContractV2 (divUsizeProgV2 .abort) 0 divUsizeBodyV2
      divUsizeContractNoAbort ∧
    ¬ BodySatisfiesSafeContractV2 (divUsizeProgV2 .abort) 0 divUsizeBodyV2
      { behaviorPre := fun _ => True } ∧
    ¬ BodySatisfiesSafeContractV2 (divUsizeProgV2 .unwind) 0 divUsizeBodyV2
      { behaviorPre := fun _ => True,
        effects := { allowAbort := true },
        postAbort := fun _ _ => True } := by
  have hCommon : ∀ (allowAbort : Bool) (q : Query),
      ValidEntryArgsV2 divUsizeBodyV2 q →
      (if allowAbort then True else
        match q.args with | [_, .scalar b] => b.bits.toNat ≠ 0 | _ => False) →
      SatisfiesPostV2 (divUsizeProgV2 .abort) q
        ((if allowAbort then divUsizeContractAllowAbort
          else divUsizeContractNoAbort).post q) := by
    intro allowAbort q hValid hPre
    let ⟨a, b, hAW, hAS, hAWf, hBW, hBS, hBWf, hArgsEq, hCM, hInit⟩ :=
      divUsize_init_ok .abort hValid
    have hATr : truncateBits .isize a.bits = a.bits := by
      unfold ScalarVal.wf at hAWf; rw [hAW] at hAWf; exact eq_of_beq hAWf
    have hBTr : truncateBits .isize b.bits = b.bits := by
      unfold ScalarVal.wf at hBWf; rw [hBW] at hBWf; exact eq_of_beq hBWf
    have haEq : a = ⟨.isize, false, a.bits⟩ := by
      cases a; subst hAW; subst hAS; rfl
    have hbEq : b = ⟨.isize, false, b.bits⟩ := by
      cases b; subst hBW; subst hBS; rfl
    cases hBz : (b.bits.toNat == 0) with
    | true =>
      have hZero : b.bits.toNat = 0 := beq_iff_eq.mp hBz
      cases allowAbort with
      | false =>
        rw [hArgsEq] at hPre
        exact False.elim (hPre hZero)
      | true =>
        have hEqOp : evalBinOp .eq (.scalar ⟨.isize, false, b.bits⟩)
            (.scalar ⟨.isize, false, BitVec.ofNat 128 0⟩) = .ok (.bool true) := by
          rw [divUsize_eq_evalBinOp b.bits hBTr, hBz]
        have hS1 := divUsize_step_bb0_eq .abort a b q.callerMem true hbEq hEqOp
        have hS2 : evalStepV2 (divUsizeProgV2 .abort)
            ⟨[⟨0, 0, 1,
                [.immediate none, .immediate (some (.scalar a)),
                  .immediate (some (.scalar b)), .immediate (some (.bool true))],
                none, none, none⟩],
              q.callerMem, entryMemoryWithCaller q.callerMem⟩ =
            .done (.aborted q.callerMem) := by
          unfold evalStepV2 evalTerminatorV2 evalPrimitiveOperandV2
            evalOperandToSlotV2 readPlaceV2
          simp [divUsizeProgV2, divUsizeBodyV2, Trusted.MirSemantics.getElem?,
            isSupportedV2LocalTy, isPrimitiveReadableTy, evalAssertFailure,
            extractCallerMemory_entry q.callerMem hCM]
        have hExec : execProgV2 (divUsizeProgV2 .abort) 2 q
            (fun o => o = .aborted q.callerMem) := by
          unfold execProgV2
          rw [hInit]
          exact execStateV2_step hS1 (execStateV2_done hS2 rfl)
        exact (spec_and_behaviorV2_of_exec_eq hExec).2.2.2
          (divUsizeContractAllowAbort.post q) ⟨rfl, rfl⟩
    | false =>
      have hEqOp : evalBinOp .eq (.scalar ⟨.isize, false, b.bits⟩)
          (.scalar ⟨.isize, false, BitVec.ofNat 128 0⟩) = .ok (.bool false) := by
        rw [divUsize_eq_evalBinOp b.bits hBTr, hBz]
      have hALt := scalarVal_isize_toNat_lt hAWf hAW
      have hDivOp := divUsize_div_evalBinOp a.bits b.bits hATr hBTr hALt hBz
      have hOutWf : (⟨.isize, false,
          BitVec.ofNat 128 (Nat.div a.bits.toNat b.bits.toNat)⟩ : ScalarVal).wf = true := by
        have hDivLt : Nat.div a.bits.toNat b.bits.toNat < Nat.pow 2 64 :=
          Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hALt
        have hDiv128 : Nat.div a.bits.toNat b.bits.toNat < Nat.pow 2 128 :=
          Nat.lt_trans hDivLt (by decide)
        unfold ScalarVal.wf
        apply beq_iff_eq.mpr
        apply bitVec_eq_of_toNat_eq
        rw [toNat_truncateBits]
        have hBv :
            (BitVec.ofNat 128 (Nat.div a.bits.toNat b.bits.toNat)).toNat =
              Nat.mod (Nat.div a.bits.toNat b.bits.toNat) (Nat.pow 2 128) := rfl
        have hM128 : Nat.mod (Nat.div a.bits.toNat b.bits.toNat) (Nat.pow 2 128) =
            Nat.div a.bits.toNat b.bits.toNat :=
          Nat.mod_eq_of_lt hDiv128
        rw [hBv, hM128]
        exact Nat.mod_eq_of_lt hDivLt
      have hS1 := divUsize_step_bb0_eq .abort a b q.callerMem false hbEq hEqOp
      have hS2 : evalStepV2 (divUsizeProgV2 .abort)
          ⟨[⟨0, 0, 1,
              [.immediate none, .immediate (some (.scalar a)),
                .immediate (some (.scalar b)), .immediate (some (.bool false))],
              none, none, none⟩],
            q.callerMem, entryMemoryWithCaller q.callerMem⟩ =
          .step ⟨[⟨0, 1, 0,
              [.immediate none, .immediate (some (.scalar a)),
                .immediate (some (.scalar b)), .immediate (some (.bool false))],
              none, none, none⟩],
            q.callerMem, entryMemoryWithCaller q.callerMem⟩ := by
        unfold evalStepV2 evalTerminatorV2 evalPrimitiveOperandV2
          evalOperandToSlotV2 readPlaceV2
        simp [divUsizeProgV2, divUsizeBodyV2, Trusted.MirSemantics.getElem?,
          isSupportedV2LocalTy, isPrimitiveReadableTy, jumpToBlock]
      have hS3 := divUsize_step_bb1_div .abort a b q.callerMem haEq hbEq hDivOp hOutWf
      have hS4 : evalStepV2 (divUsizeProgV2 .abort)
          ⟨[⟨0, 1, 1,
              [.immediate (some (divUsizeRetVal a b)), .immediate (some (.scalar a)),
                .immediate (some (.scalar b)), .immediate (some (.bool false))],
              none, none, none⟩],
            q.callerMem, entryMemoryWithCaller q.callerMem⟩ =
          .done (.returned ⟨divUsizeRetVal a b, q.callerMem⟩) := by
        have hR1 : (!refsStayInCallerMem q.callerMem usizeTyV2 (divUsizeRetVal a b)) = false := rfl
        have hR2 : (!refsValidInMem (entryMemoryWithCaller q.callerMem) usizeTyV2
            (divUsizeRetVal a b)) = false := rfl
        have hR3 : (!spansPairwiseDisjoint (refAccessSpans usizeTyV2
            (divUsizeRetVal a b))) = false := rfl
        unfold evalStepV2 evalTerminatorV2
        dsimp only [Trusted.MirSemantics.getElem?, divUsizeProgV2, divUsizeBodyV2]
        change (if (!refsStayInCallerMem q.callerMem usizeTyV2 (divUsizeRetVal a b)) ||
              (!refsValidInMem (entryMemoryWithCaller q.callerMem) usizeTyV2
                (divUsizeRetVal a b)) ||
              (!spansPairwiseDisjoint (refAccessSpans usizeTyV2
                (divUsizeRetVal a b))) then
            StepResult.fault .undefined
          else
            StepResult.done (TerminalOut.returned ⟨divUsizeRetVal a b,
              extractCallerMemory q.callerMem (entryMemoryWithCaller q.callerMem)⟩)) = _
        rw [hR1, hR2, hR3, extractCallerMemory_entry q.callerMem hCM]
        rfl
      have hExec : execProgV2 (divUsizeProgV2 .abort) 4 q
          (fun o => o = .returned ⟨divUsizeRetVal a b, q.callerMem⟩) := by
        unfold execProgV2
        rw [hInit]
        exact execStateV2_step hS1 (execStateV2_step hS2
          (execStateV2_step hS3 (execStateV2_done hS4 rfl)))
      have hSpec := (spec_and_behaviorV2_of_exec_eq hExec).2.2.2
        ((if allowAbort then divUsizeContractAllowAbort
          else divUsizeContractNoAbort).post q)
      refine hSpec ?_
      cases allowAbort
      · change divUsizeContractNoAbort.post q
          (.returned ⟨divUsizeRetVal a b, q.callerMem⟩)
        dsimp only [divUsizeContractNoAbort, SafeContractV2.post]
        rw [hArgsEq]
      · change divUsizeContractAllowAbort.post q
          (.returned ⟨divUsizeRetVal a b, q.callerMem⟩)
        dsimp only [divUsizeContractAllowAbort, SafeContractV2.post]
        rw [hArgsEq]
  refine ⟨⟨rfl, rfl, fun q hV _ => hCommon true q hV trivial⟩,
          ⟨rfl, rfl, fun q hV hPre => hCommon false q hV hPre⟩, ?_, ?_⟩
  · intro hSat
    let q0 : Query := {
      args := [.scalar ⟨.isize, false, BitVec.ofNat 128 1⟩,
               .scalar ⟨.isize, false, BitVec.ofNat 128 0⟩]
      callerMem := ⟨[]⟩
    }
    have hV0 : ValidEntryArgsV2 divUsizeBodyV2 q0 := ⟨rfl, rfl, rfl, rfl⟩
    let ⟨a, b, _, _, _, hBW, hBS, hBWf, hArgsEq, hCM, hInit0⟩ := divUsize_init_ok .abort hV0
    cases hArgsEq
    let ⟨s1, hStep0, hStep1⟩ := divUsize_abort_of_zero hCM hInit0 hBW hBS hBWf rfl
    have hBeh : BehaviorV2 (entryProgForBody (divUsizeProgV2 .abort) 0) q0
        (.aborted q0.callerMem) := by
      unfold BehaviorV2 ReachesResultV2
      change match initStateV2 (divUsizeProgV2 .abort) q0 with
        | .error _ => False
        | .ok s₀ => ∃ s : State, ReachesV2 (divUsizeProgV2 .abort) s₀ s ∧
            StepV2 (divUsizeProgV2 .abort) s (.done (.aborted q0.callerMem))
      rw [hInit0]
      exact ⟨s1, ReachesV2.tail (ReachesV2.refl _) hStep0, hStep1⟩
    have hPost := (hSat.2.2 q0 hV0 trivial).2 (.aborted q0.callerMem) hBeh
    cases hPost.1
  · intro hSat
    let q0 : Query := {
      args := [.scalar ⟨.isize, false, BitVec.ofNat 128 1⟩,
               .scalar ⟨.isize, false, BitVec.ofNat 128 0⟩]
      callerMem := ⟨[]⟩
    }
    have hV0 : ValidEntryArgsV2 divUsizeBodyV2 q0 := ⟨rfl, rfl, rfl, rfl⟩
    let ⟨a, b, _, _, _, hBW, hBS, hBWf, hArgsEq, hCM, hInit0⟩ := divUsize_init_ok .unwind hV0
    cases hArgsEq
    let ⟨s1, hStep0, hStep1⟩ := divUsize_abort_of_zero hCM hInit0 hBW hBS hBWf rfl
    have hFault : ReachesResultV2 (entryProgForBody (divUsizeProgV2 .unwind) 0) q0
        (.fault .unsupported) := by
      unfold ReachesResultV2
      change match initStateV2 (divUsizeProgV2 .unwind) q0 with
        | .error _ => False
        | .ok s₀ => ∃ s : State, ReachesV2 (divUsizeProgV2 .unwind) s₀ s ∧
            StepV2 (divUsizeProgV2 .unwind) s (.fault .unsupported)
      rw [hInit0]
      exact ⟨s1, ReachesV2.tail (ReachesV2.refl _) hStep0, hStep1⟩
    exact (hSat.2.2 q0 hV0 trivial).1.2 .unsupported hFault

private theorem validEntryBool_eq_singleton {isU : Bool} {args : List Val}
    (h : ValidEntryArgs (canaryContractUnsafeGuardBody isU) args) :
    ∃ b : Bool, args = [.bool b] := by
  dsimp [ValidEntryArgs, canaryContractUnsafeGuardBody] at h
  cases args with
  | nil => cases h
  | cons a rest =>
    cases rest with
    | cons _ _ =>
      change (checkVal a .bool && false) = true at h
      cases hChk : checkVal a .bool <;> rw [hChk] at h <;> cases h
    | nil =>
      change (checkVal a .bool && true) = true at h
      cases hChk : checkVal a .bool <;> rw [hChk] at h
      · cases h
      · cases a with
        | bool b => exact ⟨b, rfl⟩
        | char _ | ordering _ | unit | ptr _ | bytes _ | slicePtr _ _ | rangeTo _
          | rangeFrom _ | array _ => cases hChk
        | scalar sv =>
          dsimp [checkVal, Val.ty?] at hChk
          cases hWf : sv.wf <;> rw [hWf] at hChk <;> cases hChk
        | enumVal ety v =>
          dsimp [checkVal, Val.ty?] at hChk
          cases hAdm : (enumAdmitted ety && Nat.blt v ety.discriminants.length) <;>
            rw [hAdm] at hChk <;> cases hChk
        | tuple xs =>
          cases xs with
          | nil => cases hChk
          | cons x xs' =>
            cases xs' with
            | nil => cases x <;> cases hChk
            | cons y ys =>
              cases ys with
              | cons _ _ =>
                cases x with
                | scalar _ => cases y <;> cases hChk
                | _ => cases hChk
              | nil =>
                cases x with
                | scalar sv =>
                  cases y with
                  | bool _ =>
                    dsimp [checkVal, Val.ty?] at hChk
                    cases hWf : sv.wf <;> rw [hWf] at hChk <;> cases hChk
                  | _ => cases hChk
                | _ => cases hChk

/-- Contract-core canary exercising `scalarAsInt`, `safetyPre` vs.
`behaviorPre` isolation, `terminates` refusal on a self-loop, `requireInhabited`
non-vacuity enforcement inside `UnitTheorem`, and duplicate-identity rejection
in `ContractSpecs`. -/
theorem canary_contract_anneal : CanaryContractAnnealClaim := by
  have hSafeUnitExec :
      WellFormed {
        scope := .unit
        pointerWidthBits := 64
        mirProfileVersion := 1
        bodies := [canarySafeUnitBody]
      } queryEmpty ∧
      Behavior {
        scope := .unit
        pointerWidthBits := 64
        mirProfileVersion := 1
        bodies := [canarySafeUnitBody]
      } queryEmpty (.returned ⟨.unit, ⟨[]⟩⟩) ∧
      ¬ Diverges {
        scope := .unit
        pointerWidthBits := 64
        mirProfileVersion := 1
        bodies := [canarySafeUnitBody]
      } queryEmpty ∧
      ∀ post : TerminalOut → Prop,
        post (.returned ⟨.unit, ⟨[]⟩⟩) →
        SatisfiesPost {
          scope := .unit
          pointerWidthBits := 64
          mirProfileVersion := 1
          bodies := [canarySafeUnitBody]
        } queryEmpty post :=
    spec_and_behavior_of_wp_eq
      (p := {
        scope := .unit
        pointerWidthBits := 64
        mirProfileVersion := 1
        bodies := [canarySafeUnitBody]
      })
      (q := queryEmpty) (fuel := 1) (out := .returned ⟨.unit, ⟨[]⟩⟩)
      (wpProg_of_execProg rfl)
  have hUnsafeOk :=
    spec_and_behavior_of_wp_eq
      (p := entryProgForBody {
        scope := .unit
        pointerWidthBits := 64
        mirProfileVersion := 1
        bodies := [canaryContractUnsafeGuardBody true]
      } 0)
      (q := { args := [.bool true] }) (fuel := 5)
      (out := .returned ⟨.unit, ⟨[]⟩⟩)
      (wpProg_of_execProg rfl)
  have hSafeUnitPair :=
    spec_and_behavior_of_wp_eq
      (p := entryProgForBody {
        scope := .unit
        pointerWidthBits := 64
        mirProfileVersion := 1
        bodies := [canarySafeUnitBody, canaryContractLoopBody]
      } 0)
      (q := queryEmpty) (fuel := 1)
      (out := .returned ⟨.unit, ⟨[]⟩⟩)
      (wpProg_of_execProg rfl)
  let loopStart :=
    mkState 0 0
      (initLocalsLoop canaryContractLoopBody [] 0 canaryContractLoopBody.locals)
  have hLoopStep :
      evalStep (bodyProg canaryContractLoopBody) 0 loopStart =
        .step loopStart :=
    rfl
  have hLoopInv :
      ProductiveInvariant canaryContractLoopBody loopStart
        (fun s => s = loopStart) := by
    refine ⟨rfl, ?_, ?_⟩
    · intro _ _ hBefore hStep
      subst hBefore
      have hEq := hLoopStep.symm.trans hStep
      injection hEq with hSt
      exact hSt.symm
    · intro _ hEq
      subst hEq
      exact ⟨loopStart, hLoopStep⟩
  have hLoopDiv :=
    diverges_of_productiveInvariant
      (p := {
        scope := .unit
        pointerWidthBits := 64
        mirProfileVersion := 1
        bodies := [canaryContractLoopBody]
      })
      (defId := 0) (body := canaryContractLoopBody) (args := [])
      rfl rfl rfl hLoopInv
  have hLoopWf :
      WellFormed
        (entryProgForBody {
          scope := .unit
          pointerWidthBits := 64
          mirProfileVersion := 1
          bodies := [canaryContractLoopBody]
        } 0)
        { args := [] } :=
    wellFormed_entryProg_of_safe rfl rfl rfl (safeFrom_selfLoop hLoopStep)
  have hLoopDivPair :=
    diverges_of_productiveInvariant
      (p := {
        scope := .unit
        pointerWidthBits := 64
        mirProfileVersion := 1
        bodies := [canarySafeUnitBody, canaryContractLoopBody]
      })
      (defId := 1) (body := canaryContractLoopBody) (args := [])
      rfl rfl rfl hLoopInv
  have hLoopEntryRefuted :
      ¬ bodySatisfiesContractEntry {
        scope := .unit
        pointerWidthBits := 64
        mirProfileVersion := 1
        bodies := [canarySafeUnitBody, canaryContractLoopBody]
      } {
        identity := "canary::contract_loop"
        contract := { effects := EffectMask.totalNormal }
        requireInhabited := false
      } := by
    intro ⟨defId, body, hGet, hId, _, hSat, _⟩
    cases defId with
    | zero =>
      injection hGet with hEq; subst hEq
      exact Bool.noConfusion hId
    | succ n =>
      cases n with
      | zero =>
        injection hGet with hEq; subst hEq
        have hEntry := hSat.2.2 [] rfl
        exact (hEntry.2 ⟨fun h => Bool.noConfusion h, trivial⟩).2 rfl
          hLoopDivPair.1
      | succ _ =>
        dsimp [Trusted.MirSemantics.getElem?] at hGet
        cases hGet
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · rfl
  · rfl
  · rfl
  · exact fun _ => rfl
  · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, ?_, trivial⟩
    · intro defId body hGet
      cases defId with
      | zero =>
        injection hGet with hEq; subst hEq
        refine ⟨rfl, rfl, fun args hArgs hSafe => ?_⟩
        let ⟨b, hArgsEq⟩ := validEntryBool_eq_singleton hArgs
        subst hArgsEq
        have hEqTrue := hSafe rfl
        injection hEqTrue with hHead
        injection hHead with hB
        subst hB
        exact hUnsafeOk.1
      | succ _ =>
        dsimp [Trusted.MirSemantics.getElem?] at hGet
        cases hGet
    · refine ⟨0, canaryContractUnsafeGuardBody true, rfl, rfl, rfl, ?_, ?_⟩
      · refine ⟨rfl, rfl, fun args hArgs => ?_⟩
        let ⟨b, hArgsEq⟩ := validEntryBool_eq_singleton hArgs
        subst hArgsEq
        refine ⟨?_, ?_⟩
        · intro hSafe
          have hEqTrue := hSafe rfl
          injection hEqTrue with hHead
          injection hHead with hB
          subst hB
          exact hUnsafeOk.1
        · intro hBehPre
          have hEqTrue := hBehPre.1 rfl
          injection hEqTrue with hHead
          injection hHead with hB
          subst hB
          refine ⟨fun out hOut => ?_, fun _ => hUnsafeOk.2.2.1⟩
          have hSat :=
            (hUnsafeOk.2.2.2 (fun o => o = .returned ⟨.unit, ⟨[]⟩⟩) rfl).2
              out hOut
          rw [hSat]
      · intro _
        exact ⟨[.bool true], rfl, fun _ => rfl, trivial⟩
  · intro c hc hSat
    subst hc
    have hEntry := hSat.2.2 [.bool false] rfl
    have hWf := hEntry.1 (fun h => Bool.noConfusion h)
    have hNeg : NegativeCanaryClaim
        (entryProgForBody {
          scope := .unit
          pointerWidthBits := 64
          mirProfileVersion := 1
          bodies := [canaryContractUnsafeGuardBody false]
        } 0)
        { args := [.bool false] } .undefined .unsupported :=
      negativeCanary_of_execFault (fuel := 2)
        (fun h => FaultKind.noConfusion h) rfl
    exact hNeg.2.2 hWf
  · intro hSat
    have hEntry := hSat.2.2 [] rfl
    have hNotDiv :=
      (hEntry.2 ⟨fun h => Bool.noConfusion h, trivial⟩).2 rfl
    exact hNotDiv hLoopDiv.1
  · refine ⟨rfl, rfl, fun args hArgs => ?_⟩
    cases args with
    | cons _ _ => cases hArgs
    | nil =>
      exact ⟨fun _ => hLoopWf,
        fun _ => ⟨fun out hOut => False.elim (hLoopDiv.2 out hOut),
          fun h => Bool.noConfusion h⟩⟩
  · intro hUnit
    let ⟨_, _, _, _, _, _, hInh⟩ := hUnit.2.2.2.2.2.2.2.2.1
    let ⟨_, _, _, hFalse⟩ := hInh rfl
    exact hFalse
  · intro e hEntry
    subst hEntry
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, ?_, trivial⟩
    · intro defId body hGet
      cases defId with
      | zero =>
        injection hGet with hEq; subst hEq
        refine ⟨rfl, rfl, fun args hArgs _ => ?_⟩
        cases args with
        | nil => exact hSafeUnitExec.1
        | cons _ _ => cases hArgs
      | succ _ =>
        dsimp [Trusted.MirSemantics.getElem?] at hGet
        cases hGet
    · refine ⟨0, canarySafeUnitBody, rfl, rfl, trivial, ⟨rfl, rfl, fun args hArgs => ?_⟩, ?_⟩
      · cases args with
        | cons _ _ => cases hArgs
        | nil => exact ⟨fun _ => hSafeUnitExec.1, fun hBeh => False.elim hBeh.2⟩
      · intro hReq
        exact Bool.noConfusion hReq
  · intro hInh
    let ⟨_, _, _, hFalse⟩ := hInh
    exact hFalse
  · intro e hEntry hUnit
    subst hEntry
    exact Bool.noConfusion hUnit.2.2.2.2.2.2.2.1
  · intro ⟨defId, body, hGet, hId, hSig, _⟩
    cases defId with
    | zero =>
      injection hGet with hEq; subst hEq
      exact Bool.noConfusion hSig
    | succ _ =>
      dsimp [Trusted.MirSemantics.getElem?] at hGet
      cases hGet
  · intro ⟨defId, body, hGet, hId, hSig, _⟩
    cases defId with
    | zero =>
      injection hGet with hEq; subst hEq
      exact Bool.noConfusion hSig
    | succ _ =>
      dsimp [Trusted.MirSemantics.getElem?] at hGet
      cases hGet
  · intro ⟨defId, body, hGet, hId, hSig, _⟩
    cases defId with
    | zero =>
      injection hGet with hEq; subst hEq
      exact Bool.noConfusion hSig
    | succ _ =>
      dsimp [Trusted.MirSemantics.getElem?] at hGet
      cases hGet
  · intro hSat
    have hEntry := hSat.2.2 [.bool true] rfl
    have hRet : Val.unit = Val.bool true :=
      (hEntry.2 ⟨fun _ => rfl, trivial⟩).1 _ hUnsafeOk.2.1
    exact Val.noConfusion hRet
  · refine ⟨0, canarySafeUnitBody, rfl, rfl, trivial,
      ⟨rfl, rfl, fun args hArgs => ?_⟩, fun h => Bool.noConfusion h⟩
    cases args with
    | cons _ _ => cases hArgs
    | nil =>
      refine ⟨fun _ => hSafeUnitPair.1,
        fun _ => ⟨fun out hBeh => ?_, fun h => Bool.noConfusion h⟩⟩
      cases out with
      | returned _ => exact trivial
      | unwound _ => exact ⟨rfl, trivial⟩
      | aborted _ =>
        exact TerminalOut.noConfusion
          ((hSafeUnitPair.2.2.2 (fun o => o = .returned ⟨.unit, ⟨[]⟩⟩)
            rfl).2 _ hBeh)
  · intro ⟨defId, body, hGet, hId, _⟩
    cases defId with
    | zero =>
      injection hGet with hEq; subst hEq
      exact Bool.noConfusion hId
    | succ n =>
      cases n with
      | zero =>
        injection hGet with hEq; subst hEq
        exact Bool.noConfusion hId
      | succ _ =>
        dsimp [Trusted.MirSemantics.getElem?] at hGet
        cases hGet
  · intro ⟨args, hValid, _⟩
    dsimp [ValidEntryArgs, canaryNeverParamBody] at hValid
    cases args with
    | nil => cases hValid
    | cons a rest =>
      cases rest with
      | cons _ _ =>
        change (checkVal a .never && false) = true at hValid
        cases hChk : checkVal a .never <;> rw [hChk] at hValid <;>
          cases hValid
      | nil =>
        change (checkVal a .never && true) = true at hValid
        rw [checkVal_never_false a] at hValid
        cases hValid
  · exact hLoopEntryRefuted
  · intro h
    exact hLoopEntryRefuted h.2.1
  · intro ⟨_, _, hPre⟩
    exact hPre.1 rfl
  · intro specs hSpecs
    subst hSpecs
    refine ⟨rfl, fun h => ?_, fun h => h, trivial⟩
    have hEq : [Val.bool false] = [Val.bool true] := h
    injection hEq with hHead _
    injection hHead with hB
    exact Bool.noConfusion hB

/-! ## Width- and Signedness-Parametric Arithmetic Canaries -/

/-- `unchecked_mul` on in-range `usize` values (the shape `add_scaled_metadata`
needs) without unfolding `evalArithOp` or `truncateScalar`. -/
theorem canary_usize_mulUnchecked_of_lt {a c : Nat}
    (ha : a < intWidthModulus .isize) (hc : c < intWidthModulus .isize)
    (hac : a * c < intWidthModulus .isize) :
    evalBinOp .mulUnchecked
        (.scalar ⟨.isize, false, BitVec.ofNat 128 a⟩)
        (.scalar ⟨.isize, false, BitVec.ofNat 128 c⟩) =
      .ok (.scalar ⟨.isize, false, BitVec.ofNat 128 (a * c)⟩) := by
  have h128 : intWidthModulus .isize < Nat.pow 2 128 := by decide
  have ha' : (BitVec.ofNat 128 a).toNat = a :=
    Nat.mod_eq_of_lt (Nat.lt_trans ha h128)
  have hc' : (BitVec.ofNat 128 c).toNat = c :=
    Nat.mod_eq_of_lt (Nat.lt_trans hc h128)
  have h := evalBinOp_mulUnchecked_unsigned_of_lt .isize
    (b₁ := BitVec.ofNat 128 a) (b₂ := BitVec.ofNat 128 c)
    (by rw [ha']; exact ha) (by rw [hc']; exact hc)
    (by rw [ha', hc']; exact hac)
  rw [ha', hc'] at h
  exact h

/-- Symbolic signed `i64` wrapping `.add` of a negative and a non-negative
operand through `evalBinOp_add_eq` and the `decodeScalar` lemmas, with no
`2^128` subtraction in sight. -/
theorem canary_symbolic_i64_add_neg {b₁ b₂ : BitVec 128}
    (hGe : intWidthHalfModulus .i64 ≤ b₁.toNat)
    (hLt : b₁.toNat < intWidthModulus .i64)
    (h₂ : b₂.toNat < intWidthHalfModulus .i64) :
    evalBinOp .add (.scalar ⟨.i64, true, b₁⟩) (.scalar ⟨.i64, true, b₂⟩) =
      .ok (.scalar ⟨.i64, true, truncateBits .i64 (bvOfInt 128
        (Int.negSucc (intWidthModulus .i64 - b₁.toNat - 1) +
          Int.ofNat b₂.toNat))⟩) := by
  rw [evalBinOp_add_eq, decodeScalar_signed_of_ge_half hGe hLt,
    decodeScalar_signed_of_lt_half h₂]

/-- Symbolic `u128` wrapping `.sub` closed form. -/
theorem canary_symbolic_u128_sub {b₁ b₂ : BitVec 128}
    (h₁ : b₁.toNat < intWidthModulus .i128)
    (h₂ : b₂.toNat < intWidthModulus .i128) :
    evalBinOp .sub (.scalar ⟨.i128, false, b₁⟩) (.scalar ⟨.i128, false, b₂⟩) =
      .ok (.scalar ⟨.i128, false, BitVec.ofNat 128
        (Nat.mod (b₁.toNat + (intWidthModulus .i128 - b₂.toNat))
          (intWidthModulus .i128))⟩) :=
  evalBinOp_sub_unsigned_eq .i128 h₁ h₂

end Anneal.MirWp

end
