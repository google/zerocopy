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
# Negative Refutations for `Trusted.MirSemantics.Ops` UB Guards

Each theorem proves that a concrete program violating one arithmetic or shift
UB guard reaches `.fault .undefined` and refutes `WellFormed`. Disabling that
exact guard in `Trusted/MirSemantics/Ops.lean` must break the matching theorem.
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

/-- Guard `ops_binop_width_sign_mismatch`: non-shift integer binary operations
must reject mismatched signedness (`u32 + i32`) or width (`u32 + u8`) with
`.unsupported`. -/
theorem refute_ops_binop_width_sign_mismatch :
    (ReachesResult (mkBinOpProg .add u32Ty u32Ty (.int .i32 true))
      { args := [u32Val 1, scalarNatVal .i32 true 1] }
      (.fault .unsupported) ∧
     ¬ WellFormed (mkBinOpProg .add u32Ty u32Ty (.int .i32 true))
      { args := [u32Val 1, scalarNatVal .i32 true 1] }) ∧
    (ReachesResult (mkBinOpProg .add u32Ty u32Ty u8Ty)
      { args := [u32Val 1, scalarNatVal .i8 false 1] }
      (.fault .unsupported) ∧
     ¬ WellFormed (mkBinOpProg .add u32Ty u32Ty u8Ty)
      { args := [u32Val 1, scalarNatVal .i8 false 1] }) :=
  ⟨refutes_wf_of_execFault (fuel := 1) rfl,
   refutes_wf_of_execFault (fuel := 1) rfl⟩

/-- Guard `ops_int_to_char_above_u8_max`: `CastKind::IntToInt` targeting
`char` rejects integers above `255` (`u8::MAX`) with `.unsupported`. -/
theorem refute_ops_int_to_char_above_u8_max :
    let prog := mkSingleBlockProg 1 [.char, u32Ty]
      [.assign ⟨0, []⟩ (.cast .intToInt (.copy ⟨1, []⟩) .char)]
    ReachesResult prog { args := [u32Val 256] } (.fault .unsupported) ∧
    ¬ WellFormed prog { args := [u32Val 256] } :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `ops_unsigned_neg_unsupported`: `UnOp::Neg` on an unsigned scalar
faults with `.unsupported` instead of wrapping. -/
theorem refute_ops_unsigned_neg_unsupported :
    let prog := mkSingleBlockProg 1 [u32Ty, u32Ty]
      [.assign ⟨0, []⟩ (.unaryOp .neg (.copy ⟨1, []⟩))]
    ReachesResult prog { args := [u32Val 1] } (.fault .unsupported) ∧
    ¬ WellFormed prog { args := [u32Val 1] } :=
  refutes_wf_of_execFault (fuel := 1) rfl

end GuardMutation
