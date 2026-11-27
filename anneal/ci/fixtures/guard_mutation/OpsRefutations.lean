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
# Negative Refutations for `Trusted.MirSemantics.Ops` Guards

Each theorem proves that a concrete program violating one arithmetic, shift,
cast, unary, or type-compatibility guard in `Trusted/MirSemantics/Ops.lean`
faults as expected and refutes `WellFormed` (or reports overflow faithfully for
`WithOverflow`). Disabling that exact guard must break the matching theorem.
-/

namespace GuardMutation

open Trusted.MirAst Trusted.MirSemantics

/-- Guard `ops_shift_unchecked_overflow`: `shlUnchecked` at `shift == bitWidth`
and `shrUnchecked` at a negative shift amount both fault with `.undefined`. -/
theorem refute_ops_shift_unchecked_overflow :
    (ReachesResult (mkBinOpProg .shlUnchecked u32Ty u32Ty u32Ty)
      { args := [u32Val 1, u32Val 32] } (.fault .undefined) ∧
     ¬ WellFormed (mkBinOpProg .shlUnchecked u32Ty u32Ty u32Ty)
      { args := [u32Val 1, u32Val 32] }) ∧
    (ReachesResult (mkBinOpProg .shrUnchecked u32Ty u32Ty i8Ty)
      { args := [u32Val 1, i8Val 255] } (.fault .undefined) ∧
     ¬ WellFormed (mkBinOpProg .shrUnchecked u32Ty u32Ty i8Ty)
      { args := [u32Val 1, i8Val 255] }) :=
  ⟨refutes_wf_of_execFault (fuel := 1) rfl,
   refutes_wf_of_execFault (fuel := 1) rfl⟩

/-- Guard `ops_div_rem_by_zero`: integer division and remainder by zero both
fault with `.undefined` rather than returning Lean's totalized `Nat.div`/`mod`
value. -/
theorem refute_ops_div_rem_by_zero :
    (ReachesResult (mkBinOpProg .div u32Ty u32Ty u32Ty)
      { args := [u32Val 10, u32Val 0] } (.fault .undefined) ∧
     ¬ WellFormed (mkBinOpProg .div u32Ty u32Ty u32Ty)
      { args := [u32Val 10, u32Val 0] }) ∧
    (ReachesResult (mkBinOpProg .rem u32Ty u32Ty u32Ty)
      { args := [u32Val 10, u32Val 0] } (.fault .undefined) ∧
     ¬ WellFormed (mkBinOpProg .rem u32Ty u32Ty u32Ty)
      { args := [u32Val 10, u32Val 0] }) :=
  ⟨refutes_wf_of_execFault (fuel := 1) rfl,
   refutes_wf_of_execFault (fuel := 1) rfl⟩

/-- Guard `ops_signed_div_rem_min_neg1`: signed `INT_MIN / -1` and
`INT_MIN % -1` both fault with `.undefined`. -/
theorem refute_ops_signed_div_rem_min_neg1 :
    (ReachesResult (mkBinOpProg .div i8Ty i8Ty i8Ty)
      { args := [i8Val 128, i8Val 255] } (.fault .undefined) ∧
     ¬ WellFormed (mkBinOpProg .div i8Ty i8Ty i8Ty)
      { args := [i8Val 128, i8Val 255] }) ∧
    (ReachesResult (mkBinOpProg .rem i8Ty i8Ty i8Ty)
      { args := [i8Val 128, i8Val 255] } (.fault .undefined) ∧
     ¬ WellFormed (mkBinOpProg .rem i8Ty i8Ty i8Ty)
      { args := [i8Val 128, i8Val 255] }) :=
  ⟨refutes_wf_of_execFault (fuel := 1) rfl,
   refutes_wf_of_execFault (fuel := 1) rfl⟩

/-- Guard `ops_arith_unchecked_overflow`: overflowing `addUnchecked` faults
with `.undefined` instead of wrapping. -/
theorem refute_ops_arith_unchecked_overflow :
    ReachesResult (mkBinOpProg .addUnchecked u32Ty u32Ty u32Ty)
      { args := [u32Val 4294967295, u32Val 1] } (.fault .undefined) ∧
    ¬ WellFormed (mkBinOpProg .addUnchecked u32Ty u32Ty u32Ty)
      { args := [u32Val 4294967295, u32Val 1] } :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `ops_scalar_wf_width_check`: `ScalarVal.wf` rejects an over-wide `u8`
argument (`bits = 256`) at entry with `.unsupported`. -/
theorem refute_ops_scalar_wf_width_check :
    ReachesResult (mkSingleBlockProg 1 [.unit, u8Ty] [] .return_)
      { args := [u8Val 256] } (.fault .unsupported) ∧
    ¬ WellFormed (mkSingleBlockProg 1 [.unit, u8Ty] [] .return_)
      { args := [u8Val 256] } :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Maximum signed 128-bit integer bit pattern (`2^127 - 1`). -/
noncomputable def i128MaxBits : Nat := Nat.pow 2 127 - 1

/-- Minimum signed 128-bit integer bit pattern (`2^127`, representing `-2^127`).
-/
noncomputable def i128MinBits : Nat := Nat.pow 2 127

/-- Maximum unsigned 128-bit integer bit pattern (`2^128 - 1`). -/
noncomputable def u128MaxBits : Nat := Nat.pow 2 128 - 1

/-- Guard `ops_arith_host_overflow_signed`: 128-bit signed `i128::MAX + 1` and
`i128::MIN - 1` (where `truncateScalar` has `lossy = false`) fault `.undefined`
via the signed `hostOverflow` guard. -/
theorem refute_ops_arith_host_overflow_signed :
    (ReachesResult (mkBinOpProg .addUnchecked i128Ty i128Ty i128Ty)
      { args := [i128Val i128MaxBits, i128Val 1] } (.fault .undefined) ∧
     ¬ WellFormed (mkBinOpProg .addUnchecked i128Ty i128Ty i128Ty)
      { args := [i128Val i128MaxBits, i128Val 1] }) ∧
    (ReachesResult (mkBinOpProg .subUnchecked i128Ty i128Ty i128Ty)
      { args := [i128Val i128MinBits, i128Val 1] } (.fault .undefined) ∧
     ¬ WellFormed (mkBinOpProg .subUnchecked i128Ty i128Ty i128Ty)
      { args := [i128Val i128MinBits, i128Val 1] }) :=
  ⟨refutes_wf_of_execFault (fuel := 1) rfl,
   refutes_wf_of_execFault (fuel := 1) rfl⟩

/-- Guard `ops_arith_host_overflow_unsigned`: 128-bit unsigned `u128::MAX + 1`
and `0 - 1` (where `truncateScalar` has `lossy = false`) fault `.undefined` via
the unsigned `hostOverflow` guard. -/
theorem refute_ops_arith_host_overflow_unsigned :
    (ReachesResult (mkBinOpProg .addUnchecked u128Ty u128Ty u128Ty)
      { args := [u128Val u128MaxBits, u128Val 1] } (.fault .undefined) ∧
     ¬ WellFormed (mkBinOpProg .addUnchecked u128Ty u128Ty u128Ty)
      { args := [u128Val u128MaxBits, u128Val 1] }) ∧
    (ReachesResult (mkBinOpProg .subUnchecked u128Ty u128Ty u128Ty)
      { args := [u128Val 0, u128Val 1] } (.fault .undefined) ∧
     ¬ WellFormed (mkBinOpProg .subUnchecked u128Ty u128Ty u128Ty)
      { args := [u128Val 0, u128Val 1] }) :=
  ⟨refutes_wf_of_execFault (fuel := 1) rfl,
   refutes_wf_of_execFault (fuel := 1) rfl⟩

/-- Guard `ops_arith_with_overflow_flag`: `addWithOverflow(255u8, 1u8)` reports
overflow flag `true` (not `false`) so checked-overflow consumers observe it. -/
theorem refute_ops_arith_with_overflow_flag :
    Behavior (mkBinOpProg .addWithOverflow (.tuple [u8Ty, .bool]) u8Ty u8Ty)
      { args := [u8Val 255, u8Val 1] }
      (.returned ⟨.tuple [u8Val 0, .bool true], ⟨[]⟩⟩) :=
  behavior_of_execDone (fuel := 2) rfl

/-- Guard `ops_binop_scalar_type_mismatch`: non-shift integer binary ops reject
mismatched operand widths (`u32 + u8`) and signedness (`u32 + i32`) with
`.unsupported`. -/
theorem refute_ops_binop_scalar_type_mismatch :
    (ReachesResult (mkBinOpProg .add u32Ty u32Ty u8Ty)
      { args := [u32Val 1, u8Val 1] } (.fault .unsupported) ∧
     ¬ WellFormed (mkBinOpProg .add u32Ty u32Ty u8Ty)
      { args := [u32Val 1, u8Val 1] }) ∧
    (ReachesResult (mkBinOpProg .add u32Ty u32Ty i32Ty)
      { args := [u32Val 1, i32Val 1] } (.fault .unsupported) ∧
     ¬ WellFormed (mkBinOpProg .add u32Ty u32Ty i32Ty)
      { args := [u32Val 1, i32Val 1] }) :=
  ⟨refutes_wf_of_execFault (fuel := 1) rfl,
   refutes_wf_of_execFault (fuel := 1) rfl⟩

/-- Guard `ops_binop_scalar_unsupported_op`: `BinOp.offset` on integer scalars
faults with `.unsupported`. -/
theorem refute_ops_binop_scalar_unsupported_op :
    ReachesResult (mkBinOpProg .offset u32Ty u32Ty u32Ty)
      { args := [u32Val 1, u32Val 1] } (.fault .unsupported) ∧
    ¬ WellFormed (mkBinOpProg .offset u32Ty u32Ty u32Ty)
      { args := [u32Val 1, u32Val 1] } :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `ops_binop_bool_unsupported_op`: unsupported binary operators on
`bool` (`BinOp.add`) fault with `.unsupported`. -/
theorem refute_ops_binop_bool_unsupported_op :
    ReachesResult (mkBinOpProg .add .bool .bool .bool)
      { args := [.bool false, .bool true] } (.fault .unsupported) ∧
    ¬ WellFormed (mkBinOpProg .add .bool .bool .bool)
      { args := [.bool false, .bool true] } :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `ops_binop_char_unsupported_op`: arithmetic binary operators on
`char` (`BinOp.add`) fault with `.unsupported`. -/
theorem refute_ops_binop_char_unsupported_op :
    ReachesResult (mkBinOpProg .add .bool .char .char)
      { args := [.char 'a', .char 'b'] } (.fault .unsupported) ∧
    ¬ WellFormed (mkBinOpProg .add .bool .char .char)
      { args := [.char 'a', .char 'b'] } :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `ops_binop_mixed_operand_types`: `evalBinOp` catch-all rejects mixed
operand types (`u32` and `bool`) with `.unsupported`. -/
theorem refute_ops_binop_mixed_operand_types :
    ReachesResult (mkBinOpProg .eq .bool u32Ty .bool)
      { args := [u32Val 1, .bool true] } (.fault .unsupported) ∧
    ¬ WellFormed (mkBinOpProg .eq .bool u32Ty .bool)
      { args := [u32Val 1, .bool true] } :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Program casting `_1 : srcTy` to `dstTy` via `CastKind.intToInt`. -/
noncomputable def mkIntToIntCastProg (srcTy dstTy : MirTy) : Program :=
  mkSingleBlockProg 1 [dstTy, srcTy]
    [.assign ⟨0, []⟩ (.cast .intToInt (.copy ⟨1, []⟩) dstTy)]

/-- Guard `ops_cast_int_to_char_above_u8`: `CastKind.intToInt` into `.char`
rejects values `> 255` (such as `256u32` and surrogate `0xD800u32`) with
`.unsupported`. -/
theorem refute_ops_cast_int_to_char_above_u8 :
    (ReachesResult (mkIntToIntCastProg u32Ty .char)
      { args := [u32Val 256] } (.fault .unsupported) ∧
     ¬ WellFormed (mkIntToIntCastProg u32Ty .char)
      { args := [u32Val 256] }) ∧
    (ReachesResult (mkIntToIntCastProg u32Ty .char)
      { args := [u32Val 0xd800] } (.fault .unsupported) ∧
     ¬ WellFormed (mkIntToIntCastProg u32Ty .char)
      { args := [u32Val 0xd800] }) :=
  ⟨refutes_wf_of_execFault (fuel := 1) rfl,
   refutes_wf_of_execFault (fuel := 1) rfl⟩

/-- Guard `ops_cast_unsupported_target`: `CastKind.intToInt` to a non-integer,
non-`char` target (`.bool`) faults with `.unsupported`. -/
theorem refute_ops_cast_unsupported_target :
    ReachesResult (mkIntToIntCastProg u8Ty .bool)
      { args := [u8Val 1] } (.fault .unsupported) ∧
    ¬ WellFormed (mkIntToIntCastProg u8Ty .bool)
      { args := [u8Val 1] } :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Program applying unary operator `op` to `_1 : ty` into `_0 : dstTy`. -/
noncomputable def mkUnOpProg (op : UnOp) (dstTy srcTy : MirTy) : Program :=
  mkSingleBlockProg 1 [dstTy, srcTy]
    [.assign ⟨0, []⟩ (.unaryOp op (.copy ⟨1, []⟩))]

/-- Guard `ops_unop_neg_unsigned`: `UnOp.neg` on an unsigned integer (`u32`)
faults with `.unsupported`. -/
theorem refute_ops_unop_neg_unsigned :
    ReachesResult (mkUnOpProg .neg u32Ty u32Ty)
      { args := [u32Val 1] } (.fault .unsupported) ∧
    ¬ WellFormed (mkUnOpProg .neg u32Ty u32Ty)
      { args := [u32Val 1] } :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `ops_unop_unsupported_combo`: `UnOp.not` on `char` and `UnOp.neg` on
`bool` both fault with `.unsupported`. -/
theorem refute_ops_unop_unsupported_combo :
    (ReachesResult (mkUnOpProg .not .bool .char)
      { args := [.char 'a'] } (.fault .unsupported) ∧
     ¬ WellFormed (mkUnOpProg .not .bool .char)
      { args := [.char 'a'] }) ∧
    (ReachesResult (mkUnOpProg .neg .bool .bool)
      { args := [.bool true] } (.fault .unsupported) ∧
     ¬ WellFormed (mkUnOpProg .neg .bool .bool)
      { args := [.bool true] }) :=
  ⟨refutes_wf_of_execFault (fuel := 1) rfl,
   refutes_wf_of_execFault (fuel := 1) rfl⟩

end GuardMutation
