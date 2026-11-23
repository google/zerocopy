-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Anneal.CnfOrd.Ord
public import Anneal.CnfOrd.Worklist

public section
namespace Anneal.CnfOrd

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp Anneal.LoopInv

/-!
# `< ω^ω` Symbolic MIR & Multi-Rank Worklist Canaries (`Anneal.CnfOrd.Canaries`)

End-to-end positive and fail-closed negative canaries for `Anneal.CnfOrd`
(`0` `noncomputable`, `0` `._unsafe_rec`, `0` `omega`):

1. **Symbolic 2-tier resetting MIR CFG (`lexResetProg`, `lexReset_spec`,
   `lexReset_returns`):** Proves `SatisfiesPost` and `PositiveCanaryClaim`
   (`WellFormed ∧ Behavior`) across all `2^96` symbolic `u32` triples
   `(outer, inner, resetBound)` where decrementing `outer` resets `inner` to the
   arbitrary runtime input `resetBound` (`ω · outer + inner` drops in `< ω^ω`
   via `wpLoop_cnfNorm_exists` + `cnfLt_of_coeff_drop`).
2. **Dynamic 4-tier `5 → 3 → 2 → 1 → 0` multi-rank worklist cascade
   (`tower53210`, `policyTower53210`, `canary_tower53210_converges`):**
   Exercises arbitrary-depth `isStrictlyDescendingTower` convergence and
   concrete 61-task / 62-step wavefront drain by `rfl`.
3. **Fail-closed negative regression suite
   (`canary_cnford_negative_fail_closed_tests`):** Zero-axiom (`[]`) negative
   checks confirming rejection of equal-rank and upward spawns, non-canonical
   exponents, zero coefficients, irreflexive/asymmetric `cnfLt` violations, and
   non-decreasing equal-rank pool transitions.
-/

/-! ## 1. Symbolic 2-Tier Resetting MIR Loop (`lex_reset`) -/

abbrev lexU32Ty : MirTy := .int .i32 false

/-- Reads scalar `bits.toNat` of local `idx` in top frame (`0` if absent). -/
@[expose] def readFrameU32Nat (idx : Nat) (s : State) : Nat :=
  match s.frames with
  | [] => 0
  | fr :: _ =>
    let slotOpt : Option LocalSlot :=
      (fr.locals.foldr
        (fun x ih k => match k with | 0 => some x | k' + 1 => ih k')
        (fun _ => none)) idx
    match slotOpt with
    | some (.immediate (some (.scalar sv))) => sv.bits.toNat
    | _ => 0

/-- Raw `< ω^ω` ranking `ω^1 · _1 + ω^0 · _2` extracted from MIR `State`. -/
@[expose] def lexResetRawRank (s : State) : CnfOrd :=
  [(1, readFrameU32Nat 1 s), (0, readFrameU32Nat 2 s)]

/-- Entry block `bb0`: `_0 = const 0_u32; goto bb1`. -/
@[expose] def lexResetEntry : BasicBlock := {
  statements := [
    .assign ⟨0, []⟩
      (.use (.constant ⟨lexU32Ty, .scalar (BitVec.ofNat 128 0)⟩))
  ]
  terminator := .goto 1
}

/-- Inner loop header `bb1`: `switchInt(copy _2) -> [0: bb3, otherwise: bb2]`.
-/
@[expose] def lexResetInnerHeader : BasicBlock := {
  statements := []
  terminator := .switchInt (.copy ⟨2, []⟩) {
    branches := [(BitVec.ofNat 128 0, 3)]
    otherwise := 2
  }
}

/-- Inner decrement `bb2`: `_2 = Sub(copy _2, const 1_u32); goto bb1`. -/
@[expose] def lexResetInnerDec : BasicBlock := {
  statements := [
    .assign ⟨2, []⟩
      (.binaryOp .sub (.copy ⟨2, []⟩)
        (.constant ⟨lexU32Ty, .scalar (BitVec.ofNat 128 1)⟩))
  ]
  terminator := .goto 1
}

/-- Outer header `bb3`: `switchInt(copy _1) -> [0: bb5, otherwise: bb4]`. -/
@[expose] def lexResetOuterHeader : BasicBlock := {
  statements := []
  terminator := .switchInt (.copy ⟨1, []⟩) {
    branches := [(BitVec.ofNat 128 0, 5)]
    otherwise := 4
  }
}

/-- Outer decrement + dynamic inner reset `bb4`:
`_1 = Sub(copy _1, 1); _2 = copy _3; _0 = Add(copy _0, 1); goto bb1`. -/
@[expose] def lexResetOuterBody : BasicBlock := {
  statements := [
    .assign ⟨1, []⟩
      (.binaryOp .sub (.copy ⟨1, []⟩)
        (.constant ⟨lexU32Ty, .scalar (BitVec.ofNat 128 1)⟩)),
    .assign ⟨2, []⟩ (.use (.copy ⟨3, []⟩)),
    .assign ⟨0, []⟩
      (.binaryOp .add (.copy ⟨0, []⟩)
        (.constant ⟨lexU32Ty, .scalar (BitVec.ofNat 128 1)⟩))
  ]
  terminator := .goto 1
}

/-- Exit block `bb5`: `return`. -/
@[expose] def lexResetExit : BasicBlock := {
  statements := []
  terminator := .return_
}

/-- MIR `Body` for `fn lex_reset(outer: u32, inner: u32, reset_bound: u32)`. -/
@[expose] def lexResetBody : Body := {
  argumentCount := 3
  locals := [lexU32Ty, lexU32Ty, lexU32Ty, lexU32Ty]
  basicBlocks := [
    lexResetEntry,
    lexResetInnerHeader,
    lexResetInnerDec,
    lexResetOuterHeader,
    lexResetOuterBody,
    lexResetExit
  ]
  identity := "lex_reset"
}

/-- Single-body `Program` for `lex_reset`. -/
@[expose] def lexResetProg : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [lexResetBody]
}

/-- Loop-header state at `bb1` holding `(acc, outRem, inRem, resetB)`. -/
@[expose] def lexResetAt (acc outRem inRem resetB : Nat) : State :=
  mkState 1 0
    [u32Slot acc, u32Slot outRem, u32Slot inRem, u32Slot resetB]
    0 { nextAllocId := 2, allocations := [] }

/-- Loop invariant at `bb1` for initial `(outer, resetB)`. -/
@[expose] def lexResetInv (outer resetB : Nat) (s : State) : Prop :=
  ∃ acc outRem inRem,
    acc + outRem = outer ∧
    inRem < Nat.pow 2 32 ∧
    s = lexResetAt acc outRem inRem resetB

/-- Loop exit state at `bb1`: both counters have reached `0` and `_0 = outer`.
-/
@[expose] def lexResetDone (outer resetB : Nat) (s : State) : Prop :=
  s = lexResetAt outer 0 0 resetB

/-- Postcondition for `lexResetProg`: returns `outer`. -/
@[expose] def lexResetPost (outer : Nat) (out : TerminalOut) : Prop :=
  out = .returned ⟨u32Val outer, ⟨[]⟩⟩

private theorem evalStatement_assign_copy_u32 {body : Body} {frame : FrameState}
    {m : MemoryState} {cm : CallerMemory} {dstIdx : LocalId}
    {srcOp : Operand} {val : Val} {ls ls' : List LocalSlot}
    (hLoc : Trusted.MirSemantics.getElem? body.locals dstIdx = some u32Ty)
    (hRv : evalRvalue body.locals frame.locals m u32Ty (.use srcOp) =
      .ok (val, ls, m))
    (hW : writePlace ls m dstIdx u32Ty val = .ok (ls', m)) :
    evalStatement body frame m cm (.assign ⟨dstIdx, []⟩ (.use srcOp)) =
      .step {
        frames := [{ frame with stmtIdx := frame.stmtIdx + 1, locals := ls' }]
        callerMem := cm
        mem := m
      } := by
  unfold evalStatement
  dsimp only
  rw [hLoc]
  dsimp only
  rw [hRv]
  dsimp only
  rw [hW]
  rfl

private theorem lexReset_validArgs {o i r : Nat}
    (ho : o < Nat.pow 2 32) (hi : i < Nat.pow 2 32) (hr : r < Nat.pow 2 32) :
    ValidEntryArgs lexResetBody [u32Val o, u32Val i, u32Val r] :=
  (checkArgsMatch_cons_iff
    (args := [u32Val o, u32Val i, u32Val r])
    (ty := u32Ty) (tys := [u32Ty, u32Ty])).mpr
    ⟨u32Val o, [u32Val i, u32Val r], rfl, checkVal_u32Val ho,
      (checkArgsMatch_cons_iff
        (args := [u32Val i, u32Val r])
        (ty := u32Ty) (tys := [u32Ty])).mpr
        ⟨u32Val i, [u32Val r], rfl, checkVal_u32Val hi,
          (checkArgsMatch_cons_iff
            (args := [u32Val r]) (ty := u32Ty) (tys := [])).mpr
            ⟨u32Val r, [], rfl, checkVal_u32Val hr, rfl⟩⟩⟩

private theorem lexReset_initState {o i r : Nat}
    (ho : o < Nat.pow 2 32) (hi : i < Nat.pow 2 32) (hr : r < Nat.pow 2 32) :
    initState lexResetProg { args := [u32Val o, u32Val i, u32Val r] } =
      .ok (mkState 0 0 [.immediate none, u32Slot o, u32Slot i, u32Slot r]) :=
  initState_eq_ok (body := lexResetBody) rfl rfl (lexReset_validArgs ho hi hr)

private theorem lexReset_step_inner_switch (acc outRem resetB : Nat) {k : Nat}
    (hk : k + 1 < Nat.pow 2 32) :
    evalStep lexResetProg 0 (lexResetAt acc outRem (k + 1) resetB) =
      .step (mkState 2 0
        [u32Slot acc, u32Slot outRem, u32Slot (k + 1), u32Slot resetB]) := by
  have hSw : evalSwitchBranches .i32 (BitVec.ofNat 128 (k + 1)) 2
      [(BitVec.ofNat 128 0, 3)] = .ok 2 :=
    evalSwitchBranches_single_ne rfl (switch_beq_false_u32 hk)
  exact evalTerminator_switchInt_scalar
    (body := lexResetBody) (bb := lexResetInnerHeader)
    (frame := frameAt 1 0
      [u32Slot acc, u32Slot outRem, u32Slot (k + 1), u32Slot resetB])
    (discr := .copy ⟨2, []⟩)
    (targets := { branches := [(BitVec.ofNat 128 0, 3)], otherwise := 2 })
    (sv := ⟨.i32, false, BitVec.ofNat 128 (k + 1)⟩)
    (ls := [u32Slot acc, u32Slot outRem, u32Slot (k + 1), u32Slot resetB])
    (m := entryMemory) (m₁ := entryMemory) (cm := ⟨[]⟩)
    rfl rfl hSw

private theorem lexReset_step_inner_dec (acc outRem resetB : Nat) {k : Nat}
    (hk : k + 1 < Nat.pow 2 32) :
    evalStep lexResetProg 0
        (mkState 2 0
          [u32Slot acc, u32Slot outRem, u32Slot (k + 1), u32Slot resetB]) =
      .step (mkState 2 1
        [u32Slot acc, u32Slot outRem, u32Slot k, u32Slot resetB]) := by
  have hk' : k < Nat.pow 2 32 := Nat.lt_trans (Nat.lt_succ_self k) hk
  have hChk : checkVal (u32Val k) u32Ty = true := checkVal_u32Val hk'
  have hRv : evalRvalue lexResetBody.locals
      [u32Slot acc, u32Slot outRem, u32Slot (k + 1), u32Slot resetB]
      entryMemory u32Ty
      (.binaryOp .sub (.copy ⟨2, []⟩)
        (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩)) =
      .ok (u32Val k,
        [u32Slot acc, u32Slot outRem, u32Slot (k + 1), u32Slot resetB],
        entryMemory) :=
    evalRvalue_binaryOp (lVal := u32Val (k + 1)) (rVal := u32Val 1)
      (ls₁ := [u32Slot acc, u32Slot outRem, u32Slot (k + 1), u32Slot resetB])
      (m₁ := entryMemory) rfl rfl (evalBinOp_sub_u32 hk)
  have hW : writePlace
      [u32Slot acc, u32Slot outRem, u32Slot (k + 1), u32Slot resetB]
      entryMemory 2 u32Ty (u32Val k) =
      .ok ([u32Slot acc, u32Slot outRem, u32Slot k, u32Slot resetB],
        entryMemory) := by
    unfold writePlace
    cases hC : checkVal (u32Val k) u32Ty with
    | false => rw [hC] at hChk; cases hChk
    | true => rfl
  exact evalStatement_assign_binaryOp
    (body := lexResetBody)
    (frame := frameAt 2 0
      [u32Slot acc, u32Slot outRem, u32Slot (k + 1), u32Slot resetB])
    (dst := ⟨2, []⟩) (dstTy := u32Ty) (cm := ⟨[]⟩)
    rfl rfl hRv hW

private theorem lexReset_step_outer_switch (acc resetB : Nat) {m : Nat}
    (hm : m + 1 < Nat.pow 2 32) :
    evalStep lexResetProg 0
        (mkState 3 0
          [u32Slot acc, u32Slot (m + 1), u32Slot 0, u32Slot resetB]) =
      .step (mkState 4 0
        [u32Slot acc, u32Slot (m + 1), u32Slot 0, u32Slot resetB]) := by
  have hSw : evalSwitchBranches .i32 (BitVec.ofNat 128 (m + 1)) 4
      [(BitVec.ofNat 128 0, 5)] = .ok 4 :=
    evalSwitchBranches_single_ne rfl (switch_beq_false_u32 hm)
  exact evalTerminator_switchInt_scalar
    (body := lexResetBody) (bb := lexResetOuterHeader)
    (frame := frameAt 3 0
      [u32Slot acc, u32Slot (m + 1), u32Slot 0, u32Slot resetB])
    (discr := .copy ⟨1, []⟩)
    (targets := { branches := [(BitVec.ofNat 128 0, 5)], otherwise := 4 })
    (sv := ⟨.i32, false, BitVec.ofNat 128 (m + 1)⟩)
    (ls := [u32Slot acc, u32Slot (m + 1), u32Slot 0, u32Slot resetB])
    (m := entryMemory) (m₁ := entryMemory) (cm := ⟨[]⟩)
    rfl rfl hSw

private theorem lexReset_step_outer_dec (acc resetB : Nat) {m : Nat}
    (hm : m + 1 < Nat.pow 2 32) :
    evalStep lexResetProg 0
        (mkState 4 0
          [u32Slot acc, u32Slot (m + 1), u32Slot 0, u32Slot resetB]) =
      .step (mkState 4 1
        [u32Slot acc, u32Slot m, u32Slot 0, u32Slot resetB]) := by
  have hm' : m < Nat.pow 2 32 := Nat.lt_trans (Nat.lt_succ_self m) hm
  have hChk : checkVal (u32Val m) u32Ty = true := checkVal_u32Val hm'
  have hRv : evalRvalue lexResetBody.locals
      [u32Slot acc, u32Slot (m + 1), u32Slot 0, u32Slot resetB]
      entryMemory u32Ty
      (.binaryOp .sub (.copy ⟨1, []⟩)
        (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩)) =
      .ok (u32Val m,
        [u32Slot acc, u32Slot (m + 1), u32Slot 0, u32Slot resetB],
        entryMemory) :=
    evalRvalue_binaryOp (lVal := u32Val (m + 1)) (rVal := u32Val 1)
      (ls₁ := [u32Slot acc, u32Slot (m + 1), u32Slot 0, u32Slot resetB])
      (m₁ := entryMemory) rfl rfl (evalBinOp_sub_u32 hm)
  have hW : writePlace
      [u32Slot acc, u32Slot (m + 1), u32Slot 0, u32Slot resetB]
      entryMemory 1 u32Ty (u32Val m) =
      .ok ([u32Slot acc, u32Slot m, u32Slot 0, u32Slot resetB],
        entryMemory) := by
    unfold writePlace
    cases hC : checkVal (u32Val m) u32Ty with
    | false => rw [hC] at hChk; cases hChk
    | true => rfl
  exact evalStatement_assign_binaryOp
    (body := lexResetBody)
    (frame := frameAt 4 0
      [u32Slot acc, u32Slot (m + 1), u32Slot 0, u32Slot resetB])
    (dst := ⟨1, []⟩) (dstTy := u32Ty) (cm := ⟨[]⟩)
    rfl rfl hRv hW

private theorem lexReset_step_reset_inner (acc m : Nat) {resetB : Nat}
    (hr : resetB < Nat.pow 2 32) :
    evalStep lexResetProg 0
        (mkState 4 1
          [u32Slot acc, u32Slot m, u32Slot 0, u32Slot resetB]) =
      .step (mkState 4 2
        [u32Slot acc, u32Slot m, u32Slot resetB, u32Slot resetB]) := by
  have hChk : checkVal (u32Val resetB) u32Ty = true := checkVal_u32Val hr
  have hW : writePlace
      [u32Slot acc, u32Slot m, u32Slot 0, u32Slot resetB]
      entryMemory 2 u32Ty (u32Val resetB) =
      .ok ([u32Slot acc, u32Slot m, u32Slot resetB, u32Slot resetB],
        entryMemory) := by
    unfold writePlace
    cases hC : checkVal (u32Val resetB) u32Ty with
    | false => rw [hC] at hChk; cases hChk
    | true => rfl
  exact evalStatement_assign_copy_u32
    (body := lexResetBody)
    (frame := frameAt 4 1
      [u32Slot acc, u32Slot m, u32Slot 0, u32Slot resetB])
    (dstIdx := 2) (srcOp := .copy ⟨3, []⟩) (cm := ⟨[]⟩)
    rfl rfl hW

private theorem lexReset_step_inc_acc (m resetB : Nat) {acc : Nat}
    (hAcc : acc + 1 < Nat.pow 2 32) :
    evalStep lexResetProg 0
        (mkState 4 2
          [u32Slot acc, u32Slot m, u32Slot resetB, u32Slot resetB]) =
      .step (mkState 4 3
        [u32Slot (acc + 1), u32Slot m, u32Slot resetB, u32Slot resetB]) := by
  have hChk : checkVal (u32Val (acc + 1)) u32Ty = true := checkVal_u32Val hAcc
  have hRv : evalRvalue lexResetBody.locals
      [u32Slot acc, u32Slot m, u32Slot resetB, u32Slot resetB]
      entryMemory u32Ty
      (.binaryOp .add (.copy ⟨0, []⟩)
        (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩)) =
      .ok (u32Val (acc + 1),
        [u32Slot acc, u32Slot m, u32Slot resetB, u32Slot resetB],
        entryMemory) :=
    evalRvalue_binaryOp (lVal := u32Val acc) (rVal := u32Val 1)
      (ls₁ := [u32Slot acc, u32Slot m, u32Slot resetB, u32Slot resetB])
      (m₁ := entryMemory) rfl rfl (evalBinOp_add_u32 hAcc)
  have hW : writePlace
      [u32Slot acc, u32Slot m, u32Slot resetB, u32Slot resetB]
      entryMemory 0 u32Ty (u32Val (acc + 1)) =
      .ok ([u32Slot (acc + 1), u32Slot m, u32Slot resetB, u32Slot resetB],
        entryMemory) := by
    unfold writePlace
    cases hC : checkVal (u32Val (acc + 1)) u32Ty with
    | false => rw [hC] at hChk; cases hChk
    | true => rfl
  exact evalStatement_assign_binaryOp
    (body := lexResetBody)
    (frame := frameAt 4 2
      [u32Slot acc, u32Slot m, u32Slot resetB, u32Slot resetB])
    (dst := ⟨0, []⟩) (dstTy := u32Ty) (cm := ⟨[]⟩)
    rfl rfl hRv hW

private theorem lexResetRawRank_at (acc outRem inRem resetB : Nat)
    (ho : outRem < Nat.pow 2 32) (hi : inRem < Nat.pow 2 32) :
    lexResetRawRank (lexResetAt acc outRem inRem resetB) =
      [(1, outRem), (0, inRem)] := by
  unfold lexResetRawRank lexResetAt readFrameU32Nat mkState u32Slot
  dsimp only [List.foldr]
  rw [toNat_ofNat_u32 ho, toNat_ofNat_u32 hi]

private theorem natLt_succ_self_c (n : Nat) : natLt n (n + 1) = true := by
  dsimp only [natLt]
  induction n with
  | zero => rfl
  | succ _ ih => exact ih

private theorem natBeq_false_gt0 (q : Nat) (hGt : natLt 0 q = true) :
    Nat.beq 0 q = false := by
  cases q with
  | zero => cases hGt
  | succ _ => rfl

private theorem natBeq_false_gt1 (q : Nat) (hGt : natLt 1 q = true) :
    Nat.beq 1 q = false ∧ Nat.beq 0 q = false := by
  cases q with
  | zero => cases hGt
  | succ q1 =>
    cases q1 with
    | zero => cases hGt
    | succ _ => exact ⟨rfl, rfl⟩

private theorem cnfLt_lex_inner_drop (outRem k : Nat) :
    cnfLt (cnfNorm [(1, outRem), (0, k)])
      (cnfNorm [(1, outRem), (0, k + 1)]) = true := by
  apply cnfLt_of_coeff_drop _ _
    (isCanonicalCnf_cnfNorm _) (isCanonicalCnf_cnfNorm _) 0
  · rw [cnfCoeffAt_cnfNorm, cnfCoeffAt_cnfNorm]
    dsimp only [cnfCoeffAt, List.foldr, Nat.beq]
    rw [Nat.add_zero, Nat.add_zero]
    exact natLt_succ_self_c k
  · intro q hGt
    rw [cnfCoeffAt_cnfNorm, cnfCoeffAt_cnfNorm]
    dsimp only [cnfCoeffAt, List.foldr]
    rw [natBeq_false_gt0 q hGt]

private theorem cnfLt_lex_outer_drop (m resetB : Nat) :
    cnfLt (cnfNorm [(1, m), (0, resetB)])
      (cnfNorm [(1, m + 1), (0, 0)]) = true := by
  apply cnfLt_of_coeff_drop _ _
    (isCanonicalCnf_cnfNorm _) (isCanonicalCnf_cnfNorm _) 1
  · rw [cnfCoeffAt_cnfNorm, cnfCoeffAt_cnfNorm]
    dsimp only [cnfCoeffAt, List.foldr, Nat.beq]
    rw [Nat.add_zero, Nat.add_zero]
    exact natLt_succ_self_c m
  · intro q hGt
    rw [cnfCoeffAt_cnfNorm, cnfCoeffAt_cnfNorm]
    dsimp only [cnfCoeffAt, List.foldr]
    have hNe := natBeq_false_gt1 q hGt
    rw [hNe.1, hNe.2]

private theorem lexReset_loop_step {onDone : TerminalOut → Prop}
    {onFault : FaultKind → Prop} {outer resetB : Nat}
    (ho : outer < Nat.pow 2 32) (hr : resetB < Nat.pow 2 32)
    (s : State) (hInv : lexResetInv outer resetB s) :
    lexResetDone outer resetB s ∨
    (∃ f, wpUntil lexResetProg
      (fun s' =>
        (lexResetInv outer resetB s' ∧
          cnfLt (cnfNorm (lexResetRawRank s'))
            (cnfNorm (lexResetRawRank s)) = true) ∨
        lexResetDone outer resetB s')
      onDone onFault f s) := by
  let ⟨acc, outRem, inRem, hSum, hInLt, hs⟩ := hInv
  subst hs
  have hOutLt : outRem < Nat.pow 2 32 :=
    Nat.lt_of_le_of_lt (Nat.le_add_left outRem acc) (by rw [hSum]; exact ho)
  cases inRem with
  | succ k =>
    have hk' : k < Nat.pow 2 32 := Nat.lt_trans (Nat.lt_succ_self k) hInLt
    refine Or.inr ⟨3, ?_⟩
    refine wpUntil_step_eq (lexReset_step_inner_switch acc outRem resetB hInLt)
      (wpUntil_step_eq (lexReset_step_inner_dec acc outRem resetB hInLt)
        (wpUntil_step_eq
          (rfl : evalStep lexResetProg 0 _ =
            .step (lexResetAt acc outRem k resetB))
          (wpUntil_stop (Or.inl ⟨?_, ?_⟩))))
    · exact ⟨acc, outRem, k, hSum, hk', rfl⟩
    · rw [lexResetRawRank_at acc outRem k resetB hOutLt hk',
        lexResetRawRank_at acc outRem (k + 1) resetB hOutLt hInLt]
      exact cnfLt_lex_inner_drop outRem k
  | zero =>
    cases outRem with
    | zero =>
      rw [Nat.add_zero] at hSum
      subst hSum
      exact Or.inl rfl
    | succ m =>
      have hm' : m < Nat.pow 2 32 := Nat.lt_trans (Nat.lt_succ_self m) hOutLt
      have hAcc1 : acc + 1 < Nat.pow 2 32 :=
        Nat.lt_of_le_of_lt
          (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le m)) acc)
          (by rw [hSum]; exact ho)
      have hSumNext : (acc + 1) + m = outer := by
        rw [Nat.add_assoc acc 1 m, Nat.add_comm 1 m]
        exact hSum
      refine Or.inr ⟨6, ?_⟩
      refine wpUntil_step_eq
        (rfl : evalStep lexResetProg 0 _ =
          .step (mkState 3 0
            [u32Slot acc, u32Slot (m + 1), u32Slot 0, u32Slot resetB]))
        (wpUntil_step_eq (lexReset_step_outer_switch acc resetB hOutLt)
          (wpUntil_step_eq (lexReset_step_outer_dec acc resetB hOutLt)
            (wpUntil_step_eq (lexReset_step_reset_inner acc m hr)
              (wpUntil_step_eq (lexReset_step_inc_acc m resetB hAcc1)
                (wpUntil_step_eq
                  (rfl : evalStep lexResetProg 0 _ =
                    .step (lexResetAt (acc + 1) m resetB resetB))
                  (wpUntil_stop (Or.inl ⟨?_, ?_⟩)))))))
      · exact ⟨acc + 1, m, resetB, hSumNext, hr, rfl⟩
      · rw [lexResetRawRank_at (acc + 1) m resetB resetB hm' hr,
          lexResetRawRank_at acc (m + 1) 0 resetB hOutLt hInLt]
        exact cnfLt_lex_outer_drop m resetB

private theorem lexReset_exit (outer resetB : Nat) (s : State)
    (hDone : lexResetDone outer resetB s) :
    ∃ f, wpState lexResetProg f s (lexResetPost outer) := by
  subst hDone
  exact ⟨3, wpOutcomeState_of_execOutcomeState rfl⟩

/-- Symbolic `< ω^ω` MIR canary (`SatisfiesPost` + `Behavior`): for every
`(outer, inner, resetBound)` below `2^32`, `lexResetProg` terminates without
faulting and returns `outer`, despite resetting `inner := resetBound` on every
outer decrement. -/
theorem lexReset_spec (outer inner resetBound : Nat)
    (ho : outer < Nat.pow 2 32)
    (hi : inner < Nat.pow 2 32)
    (hr : resetBound < Nat.pow 2 32) :
    SatisfiesPost lexResetProg
        { args := [u32Val outer, u32Val inner, u32Val resetBound] }
        (lexResetPost outer) ∧
      ∃ out,
        Behavior lexResetProg
          { args := [u32Val outer, u32Val inner, u32Val resetBound] } out ∧
        lexResetPost outer out := by
  let ⟨F, hF⟩ :=
    wpLoop_cnfNorm_exists
      (p := lexResetProg)
      (Inv := lexResetInv outer resetBound)
      (Exit := lexResetDone outer resetBound)
      (onDone := lexResetPost outer)
      (onFault := fun _ => False)
      (rawRank := lexResetRawRank)
      (lexReset_loop_step ho hr)
      (lexResetAt 0 outer inner resetBound)
      ⟨0, outer, inner, Nat.zero_add outer, hi, rfl⟩
  exact wellFormed_and_spec_of_wpUntil
    (lexReset_initState ho hi hr)
    (wpUntil_step_eq rfl (wpUntil_step_eq rfl hF))
    (lexReset_exit outer resetBound)

/-- Symbolic `< ω^ω` MIR canary in `PositiveCanaryClaim` form. -/
theorem lexReset_returns (outer inner resetBound : Nat)
    (ho : outer < Nat.pow 2 32)
    (hi : inner < Nat.pow 2 32)
    (hr : resetBound < Nat.pow 2 32) :
    PositiveCanaryClaim lexResetProg
      { args := [u32Val outer, u32Val inner, u32Val resetBound] }
      (u32Val outer) := by
  let ⟨hSat, _, hBeh, hOut⟩ := lexReset_spec outer inner resetBound ho hi hr
  subst hOut
  exact ⟨hSat.1, hBeh⟩

/-! ## 2. Multi-Rank 4-Tier `5 → 3 → 2 → 1 → 0` Wavefront Canary -/

/-- 4-tier strictly descending rank tower `[5, 3, 2, 1, 0]` (`0 < r_{i+1} < r_i`
across 3 interior tiers). -/
@[expose] def tower53210 : List Nat := [5, 3, 2, 1, 0]

/-- Spawn policy stepping down `tower53210` with fanout `2` at each hop. -/
@[expose] def policyTower53210 : SpawnPolicy := towerLookupNext tower53210 2 0

/-- Initial `WorklistPool` with one rank-`5` root task (`remYields = 1`),
spawning `1 + 4 + 8 + 16 + 32 = 61` tasks across `62` steps. -/
@[expose] def multiRankPool0 : WorklistPool := {
  fifoQueue := [RankedTask.mk 0 5 1]
  stealDeque := []
  nextTaskId := 1
  completedCount := 0
  stepCount := 0
}

/-- End-to-end arbitrary-depth rank-tower convergence & concrete 61-task /
62-step `rfl` drain canary. -/
theorem canary_tower53210_converges :
    (∀ (ranks : List Nat) (fanout childYields : Nat) (w0 : WorklistPool),
      isStrictlyDescendingTower ranks = true →
      ∃ wFinal : WorklistPool,
        WorklistConverges (towerLookupNext ranks fanout childYields) w0 wFinal ∧
        wFinal.fifoQueue = [] ∧
        wFinal.stealDeque = [] ∧
        poolMeasure wFinal = []) ∧
    isStrictlyDescendingTower tower53210 = true ∧
    (match runWorklistSteps 63 policyTower53210 multiRankPool0 with
     | none => false
     | some wf =>
       Nat.beq wf.completedCount 61 &&
       Nat.beq wf.stepCount 62 &&
       Nat.beq (poolMeasure wf).length 0) = true := by
  refine ⟨?_, rfl, rfl⟩
  intro ranks fanout childYields w0 hDesc
  have hPol := towerLookupNext_admissible ranks fanout childYields hDesc
  cases worklist_terminates_all _ hPol w0 with
  | intro wFinal hRes =>
    exact ⟨wFinal, hRes.1, hRes.2.1, hRes.2.2.1, hRes.2.2.2.1⟩

/-! ## 3. Zero-Axiom Fail-Closed Negative Regression Suite -/

/-- Zero-axiom (`[]`) fail-closed negative regression suite:
1. Out-of-order exponents `[(1, 1), (3, 1)]` rejected by `isCanonicalCnf`;
2. Duplicate exponents `[(2, 1), (2, 3)]` rejected by `isCanonicalCnf`;
3. Zero-coefficient term `[(2, 0)]` rejected by `isCanonicalCnf`;
4. `cnfLt` rejects equal ordinals (`irrefl`);
5. `cnfLt` rejects strictly larger LHS even when lower-exponent coefficient is
   arbitrarily larger (`ω^2 · 1 < ω^1 · 999 = false`);
6. Equal-rank child spawn (`3 → 3`, fanout `1`) rejected by `spawnAdmissible`;
7. Upward-rank child spawn (`2 → 4`, fanout `1`) rejected by `spawnAdmissible`;
8. Non-descending tower `[5, 3, 3, 0]` rejected by `isStrictlyDescendingTower`;
9. Unchecked equal-rank spawn increases `poolMeasure` (`cnfLt` = `false`). -/
theorem canary_cnford_negative_fail_closed_tests :
    isCanonicalCnf [(1, 1), (3, 1)] = false ∧
    isCanonicalCnf [(2, 1), (2, 3)] = false ∧
    isCanonicalCnf [(2, 0)] = false ∧
    cnfLt [(3, 2), (0, 5)] [(3, 2), (0, 5)] = false ∧
    cnfLt [(2, 1)] [(1, 999)] = false ∧
    spawnAdmissible 3 1 3 = false ∧
    spawnAdmissible 2 1 4 = false ∧
    isStrictlyDescendingTower [5, 3, 3, 0] = false ∧
    cnfLt
      (poolMeasure {
        fifoQueue := [RankedTask.mk 0 5 1, RankedTask.mk 1 5 0]
        stealDeque := []
        nextTaskId := 2
        completedCount := 0
        stepCount := 1
      })
      (poolMeasure multiRankPool0) = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Anneal.CnfOrd

end
