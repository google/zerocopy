-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.Data.BitVec.BasicAux
public import Trusted.MirAst
public import Trusted.MirSemantics
public import Anneal.MirWp
public import Anneal.Core.StageCut
public import Anneal.ConjunctiveWp.Wlp

public section

/-!
# Concrete Canaries for `Anneal.ConjunctiveWp`

End-to-end concrete witnesses and single-cause fail-closed negative regressions
exercising `Anneal.ConjunctiveWp`:

1. `canary_pow2_countdown_sum_40`: verifies a 4-block `u32` countdown-sum loop
   executing `165` MIR steps (`40` iterations) in `@Nat.rec` depth `8`
   (`pow2Fuel 8 = 256`) via `execProgPow2` / `rfl`, proving
   `PositiveCanaryClaim` (`40 * 41 / 2 = 820`).
2. `canary_asymmetric_twoPass_and_conj_verified`: exercises asymmetric-fuel
   `wellFormed_and_spec_of_wlp_and_safety_le` (`fuelSafe = 5 ≤ 16 = fuelWlp`)
   and minimum-budget `wpProg_conj` (`compNatMin 8 5 = 5`) on a 4-block diamond
   absolute-difference MIR program.
3. `canary_productive_selfLoop_diverges_and_pow2`: proves constructive
   `Diverges` and `DivergesAtChoices` (`0` `Classical.choice`) on a 1-block
   self-loop, lifts a 1-step invariant in `k` doubling steps via
   `wpPow2Cont_inv` + `wlpOutcomeState_of_wpPow2Cont` to `pow2Fuel k` (`2^k`
   steps for every `k : Nat`), and contrasts universal partial-correctness
   satisfaction (`∀ fuel, wlpProgStrict ... (fun _ => False)`) against
   universal total-WP refutation (`∀ fuel, ¬ wpProg ... (fun _ => True)`).
4. `canary_conjunctiveWp_negative_fail_closed_tests`: 8 single-cause negative
   and boundary conjuncts covering tight `pow2Fuel` exhaustion (`k = 7`,
   `128 < 165`), wrong return postconditions, mid-run division-by-zero
   (`execWlpProg` vs. `execWlpProgStrict` paired with a non-zero divisor
   positive control), and ill-formed entry queries.

All definitions are computable (`0` `noncomputable`, `0` `._unsafe_rec`, `0`
`omega`). Pure fixture definitions use `[]` zero axioms; theorems over
`Trusted.MirSemantics` use `[propext]` only (`0` `Classical.choice`, `0`
`Quot.sound`).
-/

namespace Anneal.ConjunctiveWp

open Trusted.MirAst Trusted.MirSemantics
open Anneal.MirWp Anneal.Core

/-- Computable `u32` MIR type descriptor (`IntWidth.i32`, unsigned). -/
@[expose] def cwpU32Ty : MirTy := .int .i32 false

/-- Computable `u32` scalar value constructor from `n : Nat`. -/
@[expose] def cwpU32Val (n : Nat) : Val :=
  .scalar ⟨.i32, false, BitVec.ofNat 128 n⟩

/-- Computable `u32` constant operand constructor from `n : Nat`. -/
@[expose] def cwpU32Const (n : Nat) : Operand :=
  .constant ⟨cwpU32Ty, .scalar (BitVec.ofNat 128 n)⟩

/-- Computable entry `Query` constructor with empty `callerMem`. -/
@[expose] def cwpQuery (args : List Val) : Query :=
  { args := args, callerMem := ⟨[]⟩ }

/-- Computable check testing whether `out` returned scalar bit-pattern `n`. -/
@[expose] def cwpReturnedScalarEq (n : Nat) (out : TerminalOut) : Bool :=
  match out with
  | .returned r =>
    match r.ret with
    | .scalar s => Nat.beq s.bits.toNat n
    | .ptr _ | .slicePtr _ _ | .rangeTo _ | .rangeFrom _ | .bool _ | .char _
    | .ordering _ | .unit | .enumVal _ _ | .tuple _ | .array _
    | .bytes _ | .optionVal _ | .range _ _ => false
  | .unwound _ | .aborted _ => false

/-- Four-block `u32` countdown-sum loop `fn sum_to(n: u32) -> u32`:
- `bb0`: `_0 = 0; _2 = copy _1; goto bb1` (`3` steps)
- `bb1`: `switchInt(copy _2) [0 -> bb3, otherwise -> bb2]` (`1` step/iter)
- `bb2`: `_0 = add(_0, _2); _2 = sub(_2, 1); goto bb1` (`3` steps/iter)
- `bb3`: `return` (`1` step)
On `n = 40`, execution takes `3 + 40 * 4 + 2 = 165` MIR steps. -/
@[expose] def progCountdownSumU32 : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [cwpU32Ty, cwpU32Ty, cwpU32Ty]
    basicBlocks := [
      { statements := [
          .assign ⟨0, []⟩ (.use (cwpU32Const 0)),
          .assign ⟨2, []⟩ (.use (.copy ⟨1, []⟩))
        ]
        terminator := .goto 1 },
      { statements := []
        terminator := .switchInt (.copy ⟨2, []⟩) {
          branches := [(BitVec.ofNat 128 0, 3)]
          otherwise := 2
        } },
      { statements := [
          .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨0, []⟩) (.copy ⟨2, []⟩)),
          .assign ⟨2, []⟩ (.binaryOp .sub (.copy ⟨2, []⟩) (cwpU32Const 1))
        ]
        terminator := .goto 1 },
      { statements := []
        terminator := .return_ }
    ]
  }]

/-- Canary 1 (`[propext]`): `progCountdownSumU32(40)` (`165` MIR steps) reduces
by `rfl` via depth-`8` `execProgPow2` (`pow2Fuel 8 = 256`), establishing
`PositiveCanaryClaim` for `820`. -/
theorem canary_pow2_countdown_sum_40 :
    PositiveCanaryClaim progCountdownSumU32 (cwpQuery [cwpU32Val 40])
      (cwpU32Val 820) :=
  positiveCanary_of_execProgPow2 (k := 8) rfl

/-- Four-block diamond `u32` absolute-difference program
`fn abs_diff(a: u32, b: u32) -> u32`. -/
@[expose] def progAbsDiffU32 : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 2
    locals := [cwpU32Ty, cwpU32Ty, cwpU32Ty, .bool]
    basicBlocks := [
      { statements := [
          .assign ⟨3, []⟩ (.binaryOp .lt (.copy ⟨1, []⟩) (.copy ⟨2, []⟩))
        ]
        terminator := .switchInt (.move ⟨3, []⟩) {
          branches := [(BitVec.ofNat 128 0, 2)]
          otherwise := 1
        } },
      { statements := [
          .assign ⟨0, []⟩ (.binaryOp .sub (.copy ⟨2, []⟩) (.copy ⟨1, []⟩))
        ]
        terminator := .goto 3 },
      { statements := [
          .assign ⟨0, []⟩ (.binaryOp .sub (.copy ⟨1, []⟩) (.copy ⟨2, []⟩))
        ]
        terminator := .goto 3 },
      { statements := []
        terminator := .return_ }
    ]
  }]

/-- Canary 2 (`[propext]`): asymmetric-fuel two-pass adequacy (`fuelSafe = 5 ≤
16 = fuelWlp`) and unequal-fuel conjunctive `wpProg_conj` (`compNatMin 8 5 =
5`) on `progAbsDiffU32`. -/
theorem canary_asymmetric_twoPass_and_conj_verified :
    (SatisfiesPost progAbsDiffU32 (cwpQuery [cwpU32Val 17, cwpU32Val 42])
      (fun out => out = .returned ⟨cwpU32Val 25, ⟨[]⟩⟩) ∧
     ¬ Diverges progAbsDiffU32 (cwpQuery [cwpU32Val 17, cwpU32Val 42])) ∧
    wpProg progAbsDiffU32 (compNatMin 8 5)
      (cwpQuery [cwpU32Val 42, cwpU32Val 17])
      (fun out =>
        out = .returned ⟨cwpU32Val 25, ⟨[]⟩⟩ ∧
        out ≠ .returned ⟨cwpU32Val 0, ⟨[]⟩⟩) := by
  have hLe : (5 : Nat) ≤ 16 := Nat.le_add_right 5 11
  have hWlp :
      wlpProg progAbsDiffU32 16 (cwpQuery [cwpU32Val 17, cwpU32Val 42])
        (fun out => out = .returned ⟨cwpU32Val 25, ⟨[]⟩⟩) :=
    wlpProg_of_execWlpProg rfl
  have hSafe :
      wpProg progAbsDiffU32 5 (cwpQuery [cwpU32Val 17, cwpU32Val 42])
        (fun _ => True) :=
    wpProg_of_execProg True.intro
  have hSpec := wellFormed_and_spec_of_wlp_and_safety_le hLe hWlp hSafe
  have hConj1 :
      wpProg progAbsDiffU32 8 (cwpQuery [cwpU32Val 42, cwpU32Val 17])
        (fun out => out = .returned ⟨cwpU32Val 25, ⟨[]⟩⟩) :=
    wpProg_of_execProg rfl
  have hConj2 :
      wpProg progAbsDiffU32 5 (cwpQuery [cwpU32Val 42, cwpU32Val 17])
        (fun out => out ≠ .returned ⟨cwpU32Val 0, ⟨[]⟩⟩) :=
    wpProg_of_execProg (fun h =>
      Bool.noConfusion
        (Eq.trans (rfl : true = _)
          (Eq.trans (congrArg (cwpReturnedScalarEq 25) h) (rfl : _ = false))))
  exact ⟨⟨hSpec.1, hSpec.2.1⟩, wpProg_conj hConj1 hConj2⟩

/-- Minimal 0-argument infinite self-loop `fn spin() { loop { goto bb0 } }`. -/
@[expose] def progSelfLoopUnit : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [.unit]
    basicBlocks := [{
      statements := []
      terminator := .goto 0
    }]
  }]

/-- Entry state of `progSelfLoopUnit` on empty query `cwpQuery []`. -/
@[expose] def stateSelfLoop0 : State :=
  { frames := [{
      defId := 0
      blockIdx := 0
      stmtIdx := 0
      locals := [.immediate (some .unit)]
    }]
    callerMem := ⟨[]⟩
    mem := ⟨2, []⟩ }

/-- State invariant pinning execution to `stateSelfLoop0`. -/
@[expose] def invSelfLoop0 (s : State) : Prop :=
  s = stateSelfLoop0

/-- Canary 3 (`[propext]`): `progSelfLoopUnit` constructively satisfies
`Diverges` and `DivergesAtChoices`, lifts a 1-step invariant via
`wpPow2Cont_inv` across `pow2Fuel k` (`2^k`) steps for every `k : Nat` without
unary Peano recursion, satisfies `wlpProgStrict ... (fun _ => False)` at every
finite fuel, and refutes `wpProg` at every finite fuel. -/
theorem canary_productive_selfLoop_diverges_and_pow2 :
    Diverges progSelfLoopUnit (cwpQuery []) ∧
    DivergesAtChoices progSelfLoopUnit (cwpQuery []) (fun _ => 0) ∧
    (∀ k : Nat,
      wlpProgStrict progSelfLoopUnit (pow2Fuel k) (cwpQuery [])
        (fun _ => False)) ∧
    (∀ fuel : Nat,
      wlpProgStrict progSelfLoopUnit fuel (cwpQuery []) (fun _ => False)) ∧
    (∀ fuel : Nat,
      ¬ wpProg progSelfLoopUnit fuel (cwpQuery []) (fun _ => True)) := by
  have hInit : initState progSelfLoopUnit (cwpQuery []) = .ok stateSelfLoop0 :=
    rfl
  have hInitInv : invSelfLoop0 stateSelfLoop0 := rfl
  have hw :
      ProductiveStepWitness progSelfLoopUnit (fun s => s) invSelfLoop0 :=
    { stepOk := fun s hs => by
        unfold invSelfLoop0 at hs
        rw [hs]
        rfl
      preserves := fun _ hs => hs }
  have hDiv : Diverges progSelfLoopUnit (cwpQuery []) :=
    diverges_of_productiveWitness hInit hInitInv hw
  have hDivCh : DivergesAtChoices progSelfLoopUnit (cwpQuery []) (fun _ => 0) :=
    divergesAtChoices_of_productiveWitness hInit hInitInv hw
  have hStepPow2 :
      ∀ s : State, invSelfLoop0 s →
        wpPow2Cont progSelfLoopUnit (fun _ => False) (fun _ => False) 0
          invSelfLoop0 s := by
    intro s hs
    unfold invSelfLoop0 at hs
    rw [hs]
    refine ⟨⟨0, rfl⟩, fun ch hch => ?_⟩
    subst hch
    exact hInitInv
  have hPowK :
      ∀ k : Nat,
        wlpProgStrict progSelfLoopUnit (pow2Fuel k) (cwpQuery [])
          (fun _ => False) := by
    intro k
    unfold wlpProgStrict
    rw [hInit]
    exact wlpOutcomeState_of_wpPow2Cont
      (wpPow2Cont_inv hStepPow2 k hInitInv)
  refine ⟨hDiv, hDivCh, hPowK, ?_, ?_⟩
  · intro fuel
    unfold wlpProgStrict
    rw [hInit]
    exact wlpOutcomeState_of_productiveWitness hw (fun _ => False)
      (fun _ => False) fuel hInitInv
  · intro fuel hWp
    exact (wellFormed_and_spec_of_wp_base progSelfLoopUnit (cwpQuery []) fuel
      (fun _ => True) hWp).2.1 hDiv

/-- Single-block `u32` division program used to contrast `execWlpProg` vs.
`execWlpProgStrict` on division by zero. -/
@[expose] def progDivU32 : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 2
    locals := [cwpU32Ty, cwpU32Ty, cwpU32Ty]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.binaryOp .div (.copy ⟨1, []⟩) (.copy ⟨2, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Canary 4 (`[propext]`): 8 single-cause negative and boundary regressions:
1. Tight `pow2Fuel` exhaustion (`k = 7`, `128 < 165` steps) rejected;
2. Wrong postcondition value (`821 ≠ 820`) at `k = 8` rejected;
3. Non-strict `execWlpProg` accepts division-by-zero fault (`onFault = True`);
4. Strict `execWlpProgStrict` rejects division-by-zero fault (`onFault =
   False`), while accepting non-zero divisor `10 / 2 = 5`;
5–7. Entry initialization failure (`args := []` on 1-arg body) rejected by
   `execWlpProg`, `execWlpProgStrict`, and `execProgPow2`. -/
theorem canary_conjunctiveWp_negative_fail_closed_tests :
    (¬ execProgPow2 progCountdownSumU32 7 (cwpQuery [cwpU32Val 40])
      (fun _ => True)) ∧
    (¬ execProgPow2 progCountdownSumU32 8 (cwpQuery [cwpU32Val 40])
      (fun out => out = .returned ⟨cwpU32Val 821, ⟨[]⟩⟩)) ∧
    execWlpProg progDivU32 4 (cwpQuery [cwpU32Val 10, cwpU32Val 0])
      (fun _ => False) ∧
    (¬ execWlpProgStrict progDivU32 4 (cwpQuery [cwpU32Val 10, cwpU32Val 0])
      (fun _ => True)) ∧
    execWlpProgStrict progDivU32 4 (cwpQuery [cwpU32Val 10, cwpU32Val 2])
      (fun out => out = .returned ⟨cwpU32Val 5, ⟨[]⟩⟩) ∧
    (¬ execWlpProg progCountdownSumU32 4 (cwpQuery []) (fun _ => True)) ∧
    (¬ execWlpProgStrict progCountdownSumU32 4 (cwpQuery []) (fun _ => True)) ∧
    (¬ execProgPow2 progCountdownSumU32 4 (cwpQuery []) (fun _ => True)) :=
  ⟨fun h => h,
   fun h =>
     Bool.noConfusion
       (Eq.trans (rfl : true = _)
         (Eq.trans (congrArg (cwpReturnedScalarEq 820) h) (rfl : _ = false))),
   True.intro,
   fun h => h,
   rfl,
   fun h => h,
   fun h => h,
   fun h => h⟩

end Anneal.ConjunctiveWp

end
