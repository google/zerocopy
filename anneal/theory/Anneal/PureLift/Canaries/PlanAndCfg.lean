-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.Data.List.Basic
import Init.Data.Nat.Basic
import Anneal.PureLift.Lens
import Anneal.PureLift.PermTree
import Anneal.PureLift.LoanGraph
import Anneal.PureLift.SpatialPin
import Anneal.PureLift.Plan
import Anneal.PureLift.BlockCfg
import Anneal.PureLift.Adapter

import Anneal.PureLift.Canaries.Fixtures

namespace Anneal.PureLift

/-! ## Part III: Plan, BlockCfg, and Adapter Edge Cases -/


/-- Initialize locals `1 ..= 10` to `.nat 1 ..= .nat 10` in order. -/
def highLocalPrefixPlan : FlowPlan StdVal :=
  (List.range 10).foldr
    (fun i acc =>
      .seq (.act (.assign (.localSub (i + 1) []) (.constVal (.nat (i + 1)))))
        acc)
    .skip

/-- Symbolic branch merge preserves locals at index $\ge 8$ written by both
branches. -/
def highLocalBranchPlan : FlowPlan StdVal :=
  .seq highLocalPrefixPlan
    (.seq
      (.branch (.use (.localSub 0 []))
        (.act (.assign (.localSub 10 []) (.constVal (.nat 77))))
        (.act (.assign (.localSub 2 []) (.constVal (.nat 33)))))
      (.act (.assign (.localSub 11 []) (.use (.localSub 10 [])))))

/-- A local appended in only one branch (local `11`) may be uninitialized after
the join, so reading it fails. -/
def branchOnlyLocalPlan : FlowPlan StdVal :=
  .seq highLocalPrefixPlan
    (.seq
      (.branch (.use (.localSub 0 []))
        (.act (.assign (.localSub 11 []) (.constVal (.nat 77))))
        .skip)
      (.act (.assign (.localSub 12 []) (.use (.localSub 11 [])))))

theorem high_local_branch_join_preserves_above_eight (cond : Bool) :
    evalFnValue stdValAlg
      [⟨.byVal, .symBool cond⟩]
      highLocalBranchPlan
      (.use (.localSub 11 [])) =
    .ok ⟨zipStdVal (.symBool cond) (.nat 77) (.nat 10), []⟩ ∧
    evalFnValue stdValAlg
      [⟨.byVal, .symBool cond⟩]
      branchOnlyLocalPlan
      (.constVal .unit) = .fail ∧
    -- Reading a never-written local fails instead of yielding `defaultVal`:
    evalFnValue stdValAlg [] .skip (.use (.localSub 99 [])) = .fail ∧
    -- Writing two or more slots past the end fails instead of padding:
    evalFnValue stdValAlg [⟨.byVal, .nat 1⟩]
      (.act (.assign (.localSub 5 []) (.constVal (.nat 2))))
      (.constVal .unit) = .fail := ⟨rfl, rfl, rfl, rfl⟩


theorem explicit_join_remaps_distinct_branch_loan_ids
    (cond : Bool) (vx vy : Nat) :
    evalFnValue stdValAlg
      [⟨.byVal, .symBool cond⟩,
       ⟨.mutRef 0 [], .nat vx⟩,
       ⟨.mutRef 1 [], .nat vy⟩]
      explicitJoinRemapLoanIdsPlan
      (.constVal .unit) =
    .ok ⟨.unit,
      [zipStdVal (.symBool cond) (.nat 50) (.nat vx),
       zipStdVal (.symBool cond) (.nat vy) (.nat 50)]⟩ := by
  cases cond <;> rfl

/-- `.branchExplicitJoin` fails closed when a join pair names a nonexistent loan
ID. -/
theorem explicit_join_rejects_nonexistent_loan_id (cond : Bool) :
    evalFnValue stdValAlg
      [⟨.byVal, .symBool cond⟩]
      (.branchExplicitJoin (.use (.localSub 0 [])) .skip .skip [(99, 99)])
      (.constVal .unit) = .fail := rfl

/-- Symbolic branch joining two `.call`s that return mutable borrows (`lensCall`
targets) preserves both backward lenses under `.choice` and writes back to the
selected caller-owned referent when the joined loan ends. -/
def singleMutIdSummary (offset : Nat) : CallSummary StdVal where
  returnsMutBorrow := true
  fwd _ mutVals :=
    match mutVals with
    | [⟨_, .nat v⟩] => some (.nat (v + offset))
    | _ => none
  back _ _ vFinal :=
    match vFinal with
    | ⟨_, .nat vf⟩ => some [.nat (vf + offset)]
    | _ => none

def branchJoinLensCallsPlan : FlowPlan StdVal :=
  .seq
    (.branch (.use (.localSub 0 []))
      (.act (.call 3 (singleMutIdSummary 10) [] [.derefSub 1 []]))
      (.act (.call 3 (singleMutIdSummary 20) [] [.derefSub 2 []])))
    (.seq
      (.act (.assign (.derefSub 3 []) (.constVal (.nat 100))))
      (.act (.endLoan 2)))

theorem branch_join_lens_calls_writeback_verified
    (cond : Bool) (vx vy : Nat) :
    evalFnValue stdValAlg
      [⟨.byVal, .symBool cond⟩,
       ⟨.mutRef 0 [], .nat vx⟩,
       ⟨.mutRef 1 [], .nat vy⟩]
      branchJoinLensCallsPlan
      (.constVal .unit) =
    .ok ⟨.unit,
      [zipStdVal (.symBool cond) (.nat 110) (.nat vx),
       zipStdVal (.symBool cond) (.nat vy) (.nat 120)]⟩ := by
  cases cond <;> rfl


def branchJoinRegionGroupsPlan : FlowPlan StdVal :=
  .seq
    (.branch (.use (.localSub 0 []))
      (.act (.callMultiRegion [] [regionSpecWithAdd 5]))
      (.act (.callMultiRegion [] [regionSpecWithAdd 50])))
    (.seq
      (.act (.assign (.derefSub 2 []) (.constVal (.nat 300))))
      (.act (.endRegionGroup 0)))

theorem branch_join_region_groups_merges_backFn (cond : Bool) (vx : Nat) :
    evalFnValue stdValAlg
      [⟨.byVal, .symBool cond⟩, ⟨.mutRef 0 [], .nat vx⟩]
      branchJoinRegionGroupsPlan
      (.constVal .unit) =
    .ok ⟨.unit,
      [zipStdVal (.symBool cond) (.nat 305) (.nat 350)]⟩ := rfl

theorem branch_join_mismatched_region_groups_rejected
    (cond : Bool) (vx : Nat) :
    planStepFails
      [⟨.byVal, .symBool cond⟩, ⟨.mutRef 0 [], .nat vx⟩]
      (.branch (.use (.localSub 0 []))
        (.act (.callMultiRegion [] [regionSpecWithAdd 5]))
        (.act (.callMultiRegion []
          [{ regionSpecWithAdd 50 with groupId := 9 }]))) = true ∧
    planStepFails
      [⟨.byVal, .symBool cond⟩, ⟨.mutRef 0 [], .nat vx⟩]
      (.branch (.use (.localSub 0 []))
        (.act (.callMultiRegion [] [regionSpecWithAdd 5]))
        (.act (.callMultiRegion [] [regionSpecWithAdd 50]))) = false :=
  ⟨rfl, rfl⟩

/-- Spatial provenance counter takes `max st1.nextSpatialTag st2.nextSpatialTag`
across symbolic branch joins so post-join `freezeSpatial` never reuses an
in-branch tag. -/
def branchSpatialTagFreshnessPlan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 2 .mutBorrow (.derefSub 1 [])))
    (.seq
      (.branch (.use (.localSub 0 []))
        (.seq
          (.act (.freezeSpatial 1 valueCellCodec))
          (.act (.reabsorbSpatial 1 valueCellCodec)))
        .skip)
      (.seq
        (.act (.freezeSpatial 1 valueCellCodec))
        (.seq
          (.act (.mutateSpatial 1 1 [.init (.nat 88)]))
          (.seq
            (.act (.reabsorbSpatial 1 valueCellCodec))
            (.act (.endLoan 1))))))

theorem branch_spatial_tag_freshness_verified (cond : Bool) (vx : Nat) :
    evalFnValue stdValAlg
      [⟨.byVal, .symBool cond⟩, ⟨.mutRef 0 [], .nat vx⟩]
      branchSpatialTagFreshnessPlan
      (.constVal .unit) =
    .ok ⟨.unit, [.nat 88]⟩ := rfl

/-- Output-free region group (`outDsts = []`) reserves its `lockLid` in
`st.loans` so a subsequent sibling borrow gets a distinct `LoanId` and does not
collide when ending. -/
def outputFreeRegionSpec : RegionGroupSpec StdVal where
  groupId := 0
  requiredChildren := []
  inputPlaces := [.derefSub 0 [0]]
  outDsts := []
  fwdOuts := fun _ _ => some []
  backFn := fun _ muts _ _ =>
    match muts with
    | [⟨_, .nat v0⟩] => some ([.nat (v0 + 7)], [])
    | _ => none

def outputFreeRegionThenSiblingBorrowPlan : FlowPlan StdVal :=
  .seq
    (.act (.callMultiRegion [] [outputFreeRegionSpec]))
    (.seq
      (.act (.borrow 1 .mutBorrow (.derefSub 0 [1])))
      (.seq
        (.act (.assign (.derefSub 1 []) (.constVal (.nat 42))))
        (.seq
          (.act (.endLoan 2))
          (.act (.endRegionGroup 0)))))

theorem output_free_region_no_lockLid_collision (v0 v1 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      outputFreeRegionThenSiblingBorrowPlan
      (.constVal .unit) =
    .ok ⟨.unit, [.pair (.nat (v0 + 7)) (.nat 42)]⟩ := rfl

/-- `PrimAction.endLoanAtLocal` retires a freshly allocated reborrow on every
iteration of a `.whileLoop`. -/
def loopReborrowWithEndLoanAtLocalPlan (fuel : Nat) : FlowPlan StdVal :=
  .whileLoop fuel
    (.binary stdLtBool (.derefSub 0 []) (.localSub 1 []))
    (.seq
      (.act (.borrow 2 .mutBorrow (.derefSub 0 [])))
      (.seq
        (.act (.assign (.derefSub 2 []) (.unary stdInc (.derefSub 2 []))))
        (.act (.endLoanAtLocal 2))))

theorem loop_reborrow_with_endLoanAtLocal_verified :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .nat 1⟩, ⟨.byVal, .nat 4⟩]
      (loopReborrowWithEndLoanAtLocalPlan 4)
      (.constVal .unit) =
    .ok ⟨.unit, [.nat 4]⟩ := rfl

/-- Two-block CFG used to check concrete `BasicBlock` execution against the
equivalent straight-line plan run by `evalFnValue`. -/
def sampleTwoBlockCfg : List (BasicBlock StdVal) :=
  [ ⟨.act (.assign (.localSub 1 []) (.constVal (.nat 20))), .goto 1⟩
  , ⟨.act (.assign (.localSub 1 []) (.unary stdInc (.localSub 1 []))),
     .ret (.use (.localSub 1 []))⟩
  ]

theorem blockCfg_two_block_exec_and_equiv_test :
    (match initFnState stdValAlg [⟨.byVal, .nat 0⟩] with
     | .ok st0 =>
       runBlockCfg (stepBasicBlock stdValAlg sampleTwoBlockCfg) 0 st0 3 =
         .ret ⟨.nat 21, []⟩ ∧
       evalFnValue stdValAlg [⟨.byVal, .nat 0⟩]
         (.seq
           (.act (.assign (.localSub 1 []) (.constVal (.nat 20))))
           (.act (.assign (.localSub 1 []) (.unary stdInc (.localSub 1 [])))))
         (.use (.localSub 1 [])) =
         .ok ⟨.nat 21, []⟩
     | .fail => False) :=
  ⟨rfl, rfl⟩

/-- Step function for the `M2ExecutesTo.step_choice` and
`m3SpatialModel.disjointSubPlaces` tests. -/
def m2ChoiceStep : Nat → M2StepResult Nat Nat StdVal
  | 0 => .choice (fun s' => s' = 1 ∨ s' = 2)
  | _ => .terminated ⟨.nat 99, []⟩

theorem m2_choice_and_m3_subPathDisjoint_tests :
    M2ExecutesTo m2ChoiceStep ⟨0, [], none⟩ (1 + 1)
      ⟨1, [], some ⟨.nat 99, []⟩⟩ ∧
    subPathDisjoint [0] [0, 1] = false ∧
    subPathDisjoint [0, 1] [0] = false ∧
    subPathDisjoint [0, 1] [0, 2] = true ∧
    subPathDisjoint [0] [1] = true := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  exact M2ExecutesTo.trans
    (M2ExecutesTo.step_choice rfl (Or.inl rfl))
    (M2ExecutesTo.step_term rfl)

/-- `m3SpatialModel.ownSubPlace` accepts sub-place permissions projected out of
a split permission tree with `getPathPerm` and rejects mismatched loan tags
(`c.tag ≠ lid`). -/
theorem m3_ownSubPlace_projects_split_and_checks_loan_tag :
    let sp := m3SpatialModel StdVal
    let heap : List (M3Cell StdVal) :=
      [ ⟨0, 0, [0], 1, .activeUnique, .init (.nat 10)⟩,
        ⟨0, 0, [1], 2, .frozen, .init (.nat 20)⟩ ]
    let splitPerm : PermTree :=
      .split [([0], .mutLocked 1), ([1], .shared [2])]
    sp.ownSubPlace heap (0, 0) [0] 0 (getPathPerm [0] splitPerm) (.nat 10) ∧
    sp.ownSubPlace heap (0, 0) [1] 0 (getPathPerm [1] splitPerm) (.nat 20) ∧
    ¬ sp.ownSubPlace heap (0, 0) [0] 0 (.mutLocked 99) (.nat 10) := by
  refine ⟨⟨rfl, ⟨rfl, Or.inl rfl⟩⟩, ⟨rfl, ⟨rfl, rfl⟩⟩, ?_⟩
  intro hBad
  cases hBad with
  | intro _ hTag =>
    cases hTag with
    | intro hEq _ => nomatch hEq

/-- `FlowPlan.branchExplicitJoin` short-circuits on concrete boolean conditions
(`.bool true` / `.bool false`), executing only the taken arm. -/
theorem branchExplicitJoin_concrete_bool_short_circuits :
    let plan : FlowPlan StdVal :=
      .branchExplicitJoin (.use (.localSub 0 []))
        (.act (.assign (.localSub 1 []) (.constVal (.nat 42))))
        (.act (.endLoan 99))
        []
    evalFnValue stdValAlg [⟨.byVal, .bool true⟩] plan (.use (.localSub 1 [])) =
      .ok ⟨.nat 42, []⟩ := rfl

/-- `joinSymState` rejects branch merges when `st1.regionDeposits` and
`st2.regionDeposits` have different lengths or different producers. -/
theorem joinSymState_rejects_unequal_regionDeposits :
    let st1 : SymState StdVal := ⟨[], [], [], [(0, .nat 1)], [], 0⟩
    let st2 : SymState StdVal :=
      ⟨[], [], [], [(0, .nat 1), (0, .nat 2)], [], 0⟩
    let st3 : SymState StdVal := ⟨[], [], [], [(1, .nat 1)], [], 0⟩
    joinSymState stdValAlg (.symBool true) st1 st2 = none ∧
    joinSymState stdValAlg (.symBool true) st1 st3 = none := ⟨rfl, rfl⟩

/-- `FlowPlan.earlyReturn` evaluates `retExpr` before running `cleanupLoans` and
`cleanupGroups`, allowing `return *r` where `r`'s loan is retired by the return
cleanup. -/
theorem earlyReturn_evaluates_retExpr_before_cleanup (v0 v1 : Nat) :
    let plan : FlowPlan StdVal :=
      .seq
        (.act (.borrow 1 .mutBorrow (.derefSub 0 [0])))
        (.seq
          (.act (.assign (.derefSub 1 [])
            (.unary (stdAddNat 7) (.derefSub 1 []))))
          (.earlyReturn [1] [] (.use (.derefSub 1 []))))
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      plan
      (.constVal (.nat 0)) =
    .ok ⟨.nat (v0 + 7), [.pair (.nat (v0 + 7)) (.nat v1)]⟩ := rfl

/-- `applyJoinPairs` remaps encoded references stored inside loan cell values
(`e2.cell.val` and `e.cell.val`) in addition to `st2.locals`. -/
theorem applyJoinPairs_remaps_loan_cell_ref_values :
    let e0 : LoanEntry StdVal :=
      ⟨0, .activeMut, ⟨.refVal 1 [], .unborrowed⟩, .rootParam 0⟩
    let e1Active : LoanEntry StdVal :=
      ⟨1, .activeMut, ⟨.nat 55, .unborrowed⟩, .direct (.localReg 0) []⟩
    let e2Ended : LoanEntry StdVal :=
      ⟨2, .ended, ⟨.nat 0, .unborrowed⟩, .direct (.localReg 0) []⟩
    let st1 : SymState StdVal :=
      ⟨[⟨.nat 55, .mutLocked 1⟩], [e0, e1Active, e2Ended], [], [], [], 0⟩
    let e0In2 : LoanEntry StdVal :=
      ⟨0, .activeMut, ⟨.refVal 2 [], .unborrowed⟩, .rootParam 0⟩
    let e1Ended : LoanEntry StdVal :=
      ⟨1, .ended, ⟨.nat 0, .unborrowed⟩, .direct (.localReg 0) []⟩
    let e2Active : LoanEntry StdVal :=
      ⟨2, .activeMut, ⟨.refVal 2 [0], .unborrowed⟩, .direct (.localReg 0) []⟩
    let st2 : SymState StdVal :=
      ⟨[⟨.nat 55, .mutLocked 2⟩], [e0In2, e1Ended, e2Active], [], [], [], 0⟩
    match applyJoinPairs stdValAlg [(1, 2)] st1 st2 with
    | some st2' =>
      match findLoan 0 st2'.loans, findLoan 1 st2'.loans with
      | some e0', some e1' =>
        e0'.cell.val = .refVal 1 [] ∧ e1'.cell.val = .refVal 1 [0]
      | _, _ => False
    | none => False :=
  ⟨rfl, rfl⟩

/-- Unit tests for `FlowPlan.whileLoop` (early return propagation,
fuel exhaustion failure, and non-boolean condition failure), `initFnState`
(duplicate/overlapping parameter `rootId` rejection and disjoint sibling
sub-path acceptance), and `evalFnReturningMut` negative guards. -/
theorem plan_whileLoop_initFnState_and_returningMut_tests :
    -- 1. `.whileLoop` propagates `.earlyReturn` immediately on iteration 1:
    evalFnValue stdValAlg [⟨.byVal, .bool true⟩]
      (.whileLoop 5 (.use (.localSub 0 []))
        (.earlyReturn [] [] (.constVal (.nat 77))))
      (.constVal (.nat 0)) = .ok ⟨.nat 77, []⟩ ∧
    -- 2. `.whileLoop` fails closed when fuel is exhausted while condition is
    -- true, or when condition is non-boolean:
    evalFnValue stdValAlg [⟨.byVal, .bool true⟩]
      (.whileLoop 2 (.use (.localSub 0 [])) .skip)
      (.constVal (.nat 0)) = .fail ∧
    evalFnValue stdValAlg [⟨.byVal, .nat 5⟩]
      (.whileLoop 2 (.use (.localSub 0 [])) .skip)
      (.constVal (.nat 0)) = .fail ∧
    -- 3. `initFnState` rejects overlapping parameter borrows on the same
    -- `rootId`, while allowing disjoint sibling sub-paths `[0]` and `[1]` or
    -- multiple `.sharedRef` parameters on the same `rootId`:
    initFnState stdValAlg
      [⟨.mutRef 0 [], .nat 1⟩, ⟨.mutRef 0 [], .nat 2⟩] = .fail ∧
    initFnState stdValAlg
      [⟨.sharedRef 0 [], .nat 1⟩, ⟨.mutRef 0 [], .nat 2⟩] = .fail ∧
    initFnState stdValAlg
      [⟨.mutRef 0 [0], .nat 1⟩, ⟨.mutRef 0 [0, 1], .nat 2⟩] = .fail ∧
    (match initFnState stdValAlg
        [⟨.mutRef 0 [0], .nat 1⟩, ⟨.mutRef 0 [1], .nat 2⟩] with
     | .ok _ => True
     | .fail => False) ∧
    (match initFnState stdValAlg
        [⟨.sharedRef 0 [], .nat 1⟩, ⟨.sharedRef 0 [], .nat 1⟩] with
     | .ok _ => True
     | .fail => False) ∧
    -- 4. `evalFnReturningMut` rejects returning a non-reference local or
    -- returning a shared reference as mutable:
    (match evalFnReturningMut stdValAlg [⟨.byVal, .nat 10⟩] .skip 0 with
     | .fail => True
     | .ok _ => False) ∧
    (match evalFnReturningMut stdValAlg [⟨.sharedRef 0 [], .nat 10⟩]
        .skip 0 with
     | .fail => True
     | .ok _ => False) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, trivial, trivial, trivial, trivial⟩

/-- Unit tests for `BlockCfg` terminators (`BlockTerm.branch`,
`BlockTerm.goto`, `BlockTerm.ret`), out-of-bounds block IDs (`.fault`), zero
fuel (`.diverged`), and `cfg_certificate_step_sound`. -/
def sampleBranchBlockCfg : List (BasicBlock StdVal) :=
  [ ⟨.skip, .branch (.use (.localSub 0 [])) 1 2⟩
  , ⟨.act (.assign (.localSub 1 []) (.constVal (.nat 10))),
     .goto 3⟩
  , ⟨.act (.assign (.localSub 1 []) (.constVal (.nat 20))),
     .goto 3⟩
  , ⟨.skip, .ret (.use (.localSub 1 []))⟩
  ]

theorem blockCfg_terminators_and_certificate_tests :
    (match initFnState stdValAlg [⟨.byVal, .bool true⟩] with
     | .ok stT =>
       runBlockCfg (stepBasicBlock stdValAlg sampleBranchBlockCfg) 0 stT 4 =
         .ret ⟨.nat 10, []⟩ ∧
       runBlockCfg (stepBasicBlock stdValAlg sampleBranchBlockCfg) 99 stT 2 =
         .fault ∧
       runBlockCfg (stepBasicBlock stdValAlg sampleBranchBlockCfg) 0 stT 0 =
         .diverged
     | .fail => False) ∧
    (match initFnState stdValAlg [⟨.byVal, .bool false⟩] with
     | .ok stF =>
       runBlockCfg (stepBasicBlock stdValAlg sampleBranchBlockCfg) 0 stF 4 =
         .ret ⟨.nat 20, []⟩
     | .fail => False) ∧
    runBlockCfg
      (stepBasicBlock stdValAlg
        [⟨.act (.assign (.localSub 1 []) (.constVal (.nat 42))),
          .ret (.use (.localSub 1 []))⟩])
      0 ⟨[⟨.nat 0, .unborrowed⟩], [], [], [], [], 0⟩ 1 =
      .ret ⟨.nat 42, []⟩ := by
  refine ⟨⟨rfl, rfl, rfl⟩, rfl, ?_⟩
  exact cfg_certificate_step_sound stdValAlg
    [⟨.byVal, .nat 0⟩]
    (.act (.assign (.localSub 1 []) (.constVal (.nat 42))))
    (.use (.localSub 1 []))
    ⟨[⟨.nat 0, .unborrowed⟩], [], [], [], [], 0⟩
    ⟨.nat 42, []⟩
    rfl
    rfl

/-- Tests for:
1. `callMultiRegion` inside a `.whileLoop` (replacing inactive
   `RegionGroupEntry` entries across iterations so later iterations are not
   shadowed by iteration `0`, and rejecting duplicate active `groupId`),
2. `applyJoinPairs` remapping loan IDs inside nested `StdVal.pair` values,
   `regionGroups`, and `regionDeposits`,
3. Multi-argument `.call` returning a mutable borrow over two disjoint sub-paths
   (`[0]` and `[1]`) of the same owner (`releaseLoanPermAtPath`), and
4. Symbolic branches where one arm takes `.earlyReturn` and the other arm
   continues into subsequent statements (`ExecFlow.guardedContinuing`). -/
def loopRegionGroupPlan (fuel : Nat) : FlowPlan StdVal :=
  .whileLoop fuel
    (.binary stdLtBool (.derefSub 0 []) (.localSub 1 []))
    (.seq
      (.act (.callMultiRegion []
        [{ regionSpecWithAdd 1 with inputPlaces := [.derefSub 0 []] }]))
      (.act (.endRegionGroup 0)))

def pairSwapMutBorrowSummary : CallSummary StdVal where
  returnsMutBorrow := true
  fwd _ mutVals :=
    match mutVals with
    | [v0, _] => some v0
    | _ => none
  back _ mutVals vFinal :=
    match mutVals with
    | [_, v1] => some [vFinal, v1]
    | _ => none

def sameOwnerTwoSubpathMutCallPlan : FlowPlan StdVal :=
  .seq
    (.act (.call 1 pairSwapMutBorrowSummary []
      [.derefSub 0 [0], .derefSub 0 [1]]))
    (.seq
      (.act (.assign (.derefSub 1 []) (.constVal (.nat 88))))
      (.act (.endLoan 1)))

def symbolicMixedEarlyReturnPlan : FlowPlan StdVal :=
  .seq
    (.branch (.use (.localSub 0 []))
      (.seq
        (.act (.assign (.derefSub 1 []) (.constVal (.nat 10))))
        (.earlyReturn [] [] (.constVal (.nat 1))))
      (.act (.assign (.derefSub 1 []) (.constVal (.nat 20)))))
    (.act (.assign (.derefSub 1 [])
      (.unary (stdAddNat 5) (.derefSub 1 []))))

theorem region_group_in_loop_verified :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .nat 1⟩, ⟨.byVal, .nat 3⟩]
      (loopRegionGroupPlan 3)
      (.constVal .unit) = .ok ⟨.unit, [.nat 3]⟩ := rfl

theorem region_group_duplicate_spec_rejected (v0 v1 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      (.act (.callMultiRegion []
        [ { regionSpecWithAdd 1 with
              inputPlaces := [.derefSub 0 [0]], outDsts := [1] }
        , { regionSpecWithAdd 2 with
              inputPlaces := [.derefSub 0 [1]], outDsts := [2] } ]))
      (.constVal .unit) = .fail := rfl

theorem plan_and_loan_graph_edge_case_tests
    (cond : Bool) (v0 v1 : Nat) :
    -- 1. `callMultiRegion` in a loop updates across multiple iterations, and
    -- duplicate active `groupId` in the same `callMultiRegion` fails:
    (evalFnValue stdValAlg
      [⟨.mutRef 0 [], .nat 1⟩, ⟨.byVal, .nat 3⟩]
      (loopRegionGroupPlan 3)
      (.constVal .unit) = .ok ⟨.unit, [.nat 3]⟩ ∧
     evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      (.act (.callMultiRegion []
        [ { regionSpecWithAdd 1 with
              inputPlaces := [.derefSub 0 [0]], outDsts := [1] }
        , { regionSpecWithAdd 2 with
              inputPlaces := [.derefSub 0 [1]], outDsts := [2] } ]))
      (.constVal .unit) = .fail) ∧
    -- 2. `applyJoinPairs` remaps references nested inside `.pair`,
    -- `regionGroups`, and `regionDeposits`:
    (let e0 : LoanEntry StdVal :=
       ⟨0, .activeMut, ⟨.pair (.refVal 1 []) (.nat 0), .unborrowed⟩,
        .rootParam 0⟩
     let e1Act : LoanEntry StdVal :=
       ⟨1, .activeMut, ⟨.nat 5, .unborrowed⟩, .regionOut 0 0⟩
     let e2End : LoanEntry StdVal :=
       ⟨2, .ended, ⟨.nat 0, .unborrowed⟩, .regionOut 0 0⟩
     let rg1 : RegionGroupEntry StdVal :=
       ⟨0, true, 1, [(.parentLoan 1, [])], [1], [],
        fun outs deps => some (outs, deps)⟩
     let st1 : SymState StdVal :=
       ⟨[], [e0, e1Act, e2End], [rg1], [(5, .refVal 1 [])], [], 0⟩
     let e0In2 : LoanEntry StdVal :=
       ⟨0, .activeMut, ⟨.pair (.refVal 2 []) (.nat 0), .unborrowed⟩,
        .rootParam 0⟩
     let e1End : LoanEntry StdVal :=
       ⟨1, .ended, ⟨.nat 0, .unborrowed⟩, .regionOut 0 0⟩
     let e2Act : LoanEntry StdVal :=
       ⟨2, .activeMut, ⟨.nat 5, .unborrowed⟩, .regionOut 0 0⟩
     let rg2 : RegionGroupEntry StdVal :=
       ⟨0, true, 2, [(.parentLoan 2, [])], [2], [],
        fun outs deps => some (outs, deps)⟩
     let st2 : SymState StdVal :=
       ⟨[], [e0In2, e1End, e2Act], [rg2], [(5, .refVal 2 [])], [], 0⟩
     match applyJoinPairs stdValAlg [(1, 2)] st1 st2 with
     | some st2' =>
       st2'.regionDeposits = [(5, .refVal 1 [])] ∧
       (match findLoan 0 st2'.loans, findRegionGroup 0 st2'.regionGroups with
        | some e0', some rg' =>
          e0'.cell.val = .pair (.refVal 1 []) (.nat 0) ∧
          rg'.lockLid = 1 ∧
          rg'.outputLoans = [1] ∧
          rg'.inputTargets = [(.parentLoan 1, [])]
        | _, _ => False)
     | none => False) ∧
    -- 3. Multi-leaf `.lensCall` on disjoint sub-paths of the same owner:
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      sameOwnerTwoSubpathMutCallPlan
      (.constVal .unit) =
      .ok ⟨.unit, [.pair (.nat 88) (.nat v1)]⟩ ∧
    -- 4. Symbolic mixed early-return branch (`ExecFlow.guardedContinuing`):
    evalFnValue stdValAlg
      [⟨.byVal, .symBool cond⟩, ⟨.mutRef 0 [], .nat v0⟩]
      symbolicMixedEarlyReturnPlan
      (.constVal (.nat 0)) =
      .ok ⟨zipStdVal (.symBool cond) (.nat 1) (.nat 0),
           [zipStdVal (.symBool cond) (.nat 10) (.nat 25)]⟩ :=
  ⟨⟨region_group_in_loop_verified,
    region_group_duplicate_spec_rejected v0 v1⟩,
   ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩⟩,
   rfl,
   rfl⟩

/-- Tests for `Adapter`, `Plan`, and `Canaries`:
1. `spatialBindingsHold` ties unborrowed bound loans to `e.id` and `e.phase`
   (`effectiveBoundLoanPerm`), rejecting spatial cells bound to a different
   loan ID or wrong borrow kind,
2. Sequential `callMultiRegion` invocations after ending a prior region group
   do not leak earlier deposits into later region group callbacks (a group
   receives only deposits from its `requiredChildren`), and
3. `projectBranchStdVal` preserves `.choice` nodes guarded by a different
   condition value (`.symBool false` when projecting `.symBool true`) while
   projecting `.choice` nodes guarded by the projected condition. -/
theorem spatial_binding_deposit_scope_and_projection_tests :
    -- 1. `spatialBindingsHold` checks `e.id` and `e.phase` when `e.cell.perm`
    -- is `.unborrowed`:
    (let loan3 : LoanEntry StdVal :=
       ⟨3, .activeMut, ⟨.nat 10, .unborrowed⟩, .rootParam 0⟩
     let stLoan3 : SymState StdVal := ⟨[], [loan3], [], [], [], 0⟩
     let cellOk : M3Cell StdVal :=
       ⟨0, 0, [], 3, .activeUnique, .init (.nat 10)⟩
     let cellWrongLid : M3Cell StdVal :=
       ⟨0, 0, [], 9, .activeUnique, .init (.nat 10)⟩
     let cellWrongKind : M3Cell StdVal :=
       ⟨0, 0, [], 3, .frozen, .init (.nat 10)⟩
     effectiveBoundLoanPerm 3 (LoanPhase.activeMut (Val := StdVal))
       .unborrowed = .mutLocked 3 ∧
     spatialBindingsHold (m3SpatialModel StdVal) [(3, (0, 0), [])]
       stLoan3 [cellOk] ∧
     (spatialBindingsHold (m3SpatialModel StdVal) [(3, (0, 0), [])]
       stLoan3 [cellWrongLid] → False) ∧
     (spatialBindingsHold (m3SpatialModel StdVal) [(3, (0, 0), [])]
       stLoan3 [cellWrongKind] → False)) ∧
    -- 2. Sequential `callMultiRegion` after `endRegionGroup 0` does not leak
    -- prior `regionDeposits` into the second call's callback:
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .nat 10⟩]
      (.seq
        (.act (.callMultiRegion []
          [{ regionSpecWithAdd 5 with
              inputPlaces := [.derefSub 0 []], outDsts := [1] }]))
        (.seq
          (.act (.endRegionGroup 0))
          (.seq
            (.act (.callMultiRegion []
              [{ regionSpecWithAdd 7 with
                  inputPlaces := [.derefSub 0 []], outDsts := [1] }]))
            (.act (.endRegionGroup 0)))))
      (.use (.derefSub 0 [])) = .ok ⟨.nat 22, [.nat 22]⟩ ∧
    -- 3. `projectBranchStdVal` projects the matching condition and preserves
    -- a different condition value:
    projectBranchStdVal (.symBool true) true
      (.choice (.symBool true) (.nat 1) (.nat 2)) = .nat 1 ∧
    projectBranchStdVal (.symBool true) true
      (.choice (.symBool false) (.nat 1) (.nat 2)) =
      .choice (.symBool false) (.nat 1) (.nat 2) :=
  ⟨⟨rfl,
    ⟨⟨trivial, trivial⟩, ⟨⟨rfl, ⟨rfl, ⟨rfl, Or.inl rfl⟩⟩⟩, trivial⟩⟩,
    (fun h => nomatch h.2.1.2.2.1),
    (fun h =>
      match h.2.1.2.2.2 with
      | Or.inl h1 => nomatch h1
      | Or.inr h2 => nomatch h2)⟩,
   rfl, rfl, rfl⟩

/-- Tests for `Adapter`, `Plan`, and `Canaries`:
1. `zipOrKeepSameRef` recursively zips aggregate fields across symbolic branch
   joins so a post-join field projection (`.localSub reg [0]`) succeeds on an
   aggregate left unchanged by both branches,
2. `joinLoanEntries` accepts symbolic branches where one arm creates and ends a
   scoped branch-local loan (`allEndedBranchLocalLoans`),
3. `stdAdd` preserves both choice guards when adding symbolic values under
   distinct conditions `c1 ≠ c2`, and
4. `m3LookupCell` and `m3SpatialModel.ownSubPlace` reject heaps containing
   duplicate or prefix-overlapping concrete cells at `(allocId, offset)`. -/
theorem aggregate_join_branch_local_loan_and_heap_lookup_tests
    (cond : Bool) (v0 v1 : Nat) :
    -- 1. Post-join field projection `.localSub 1 [0]` on an aggregate local
    -- after a symbolic branch:
    evalFnValue stdValAlg
      [⟨.byVal, .symBool cond⟩, ⟨.byVal, .pair (.nat v0) (.nat v1)⟩]
      (.seq
        (.branch (.use (.localSub 0 []))
          (.act (.assign (.localSub 2 []) (.constVal (.nat 10))))
          (.act (.assign (.localSub 2 []) (.constVal (.nat 20)))))
        (.act (.assign (.localSub 3 []) (.use (.localSub 1 [0])))))
      (.use (.localSub 3 [])) =
      .ok ⟨zipStdVal (.symBool cond) (.nat v0) (.nat v0), []⟩ ∧
    -- 2. Symbolic branch where only the true arm creates and ends a scoped
    -- borrow of `*p`:
    evalFnValue stdValAlg
      [⟨.byVal, .symBool cond⟩, ⟨.mutRef 0 [], .nat v0⟩]
      (.branch (.use (.localSub 0 []))
        (.seq
          (.act (.borrow 2 .mutBorrow (.derefSub 1 [])))
          (.seq
            (.act (.assign (.derefSub 2 []) (.constVal (.nat 99))))
            (.act (.endLoan 1))))
        .skip)
      (.constVal .unit) =
      .ok ⟨.unit, [zipStdVal (.symBool cond) (.nat 99) (.nat v0)]⟩ ∧
    -- 3. `stdAdd` preserves both guards when `c1 ≠ c2`:
    stdAdd
      (.choice (.symBool true) (.nat 1) (.nat 2))
      (.choice (.symBool false) (.nat 10) (.nat 20)) =
      some (.choice (.symBool true)
        (.choice (.symBool false) (.nat 11) (.nat 21))
        (.choice (.symBool false) (.nat 12) (.nat 22))) ∧
    -- 4. `m3SpatialModel.ownSubPlace` rejects duplicate or prefix-overlapping
    -- cells at `(0, 0)`:
    (let dupHeap : List (M3Cell StdVal) :=
       [ ⟨0, 0, [], 1, .activeUnique, .init (.nat 10)⟩
       , ⟨0, 0, [], 1, .activeUnique, .init (.nat 20)⟩ ]
     let overlapHeap : List (M3Cell StdVal) :=
       [ ⟨0, 0, [], 1, .activeUnique, .init (.pair (.nat 1) (.nat 2))⟩
       , ⟨0, 0, [0], 2, .activeUnique, .init (.nat 99)⟩ ]
     ((m3SpatialModel StdVal).ownSubPlace dupHeap (0, 0) [] 1 .unborrowed
        (.nat 10) → False) ∧
     ((m3SpatialModel StdVal).ownSubPlace overlapHeap (0, 0) [] 1 .unborrowed
        (.pair (.nat 1) (.nat 2)) → False)) :=
  ⟨rfl, rfl, rfl, ⟨fun h => h, fun h => h⟩⟩

/-- A five-level left-nested pair `((((1, 2), 3), 4), 5), 6)`. -/
def deepNestedStdVal : StdVal :=
  .pair (.pair (.pair (.pair (.pair (.nat 1) (.nat 2)) (.nat 3)) (.nat 4))
    (.nat 5)) (.nat 6)

/-- Tests for `Plan`, `BlockCfg`, and `Adapter`:
1. Dereferencing a handle local that is itself mutably borrowed fails,
2. Aliased `.sharedRef` parameters on one root observe a single coherent value
   (derived from the earlier loan, or, for a shared parameter that strictly
   encloses an earlier one, re-derived for the earlier loan from the larger
   value),
3. `applyJoinPairs` rejects renaming involving a root-parameter loan,
4. Returning a `&mut` backed by a local of the current frame fails,
5. Symbolic joins merge aggregates field by field at any depth (here, five
   nested levels),
6. `CfgCertificate.singleBlock` carries usable CFG-to-plan evidence, and
7. `spatialFinalBindingsHold` requires each final root cell to keep the root
   loan's tag. -/
theorem borrowed_handle_shared_alias_and_frame_escape_tests
    (cond : Bool) (v0 : Nat) :
    -- 1. `*r` through a mutably borrowed handle `r`:
    evalFnValue stdValAlg [⟨.mutRef 0 [], .nat v0⟩]
      (.seq
        (.act (.borrow 1 .mutBorrow (.localSub 0 [])))
        (.act (.assign (.derefSub 0 []) (.constVal (.nat 5)))))
      (.constVal .unit) = .fail ∧
    -- 2. Coherent aliased shared parameters:
    evalFnValue stdValAlg [⟨.sharedRef 0 [], .nat 1⟩, ⟨.sharedRef 0 [], .nat 2⟩]
      .skip (.use (.derefSub 1 [])) = .ok ⟨.nat 1, []⟩ ∧
    evalFnValue stdValAlg
      [⟨.sharedRef 0 [], .pair (.nat 1) (.nat 2)⟩, ⟨.sharedRef 0 [1], .nat 9⟩]
      .skip (.use (.derefSub 1 [])) = .ok ⟨.nat 2, []⟩ ∧
    evalFnValue stdValAlg
      [⟨.sharedRef 0 [0], .nat 1⟩, ⟨.sharedRef 0 [], .pair (.nat 5) (.nat 6)⟩]
      .skip (.use (.derefSub 0 [])) = .ok ⟨.nat 5, []⟩ ∧
    -- 3. Explicit join pairs never rename root loans:
    (let cell : PlaceCell StdVal := ⟨.nat 0, .unborrowed⟩
     let st1 : SymState StdVal :=
       ⟨[], [⟨0, .activeMut, cell, .rootParam 0⟩,
             ⟨1, .ended, cell, .direct (.localReg 5) []⟩], [], [], [], 0⟩
     let st2 : SymState StdVal :=
       ⟨[], [⟨0, .ended, cell, .rootParam 0⟩,
             ⟨1, .activeMut, cell, .direct (.localReg 5) []⟩], [], [], [], 0⟩
     let st1' : SymState StdVal :=
       ⟨[], [⟨0, .activeMut, cell, .direct (.localReg 4) []⟩,
             ⟨1, .ended, cell, .direct (.localReg 5) []⟩], [], [], [], 0⟩
     let st2' : SymState StdVal :=
       ⟨[], [⟨0, .ended, cell, .direct (.localReg 4) []⟩,
             ⟨1, .activeMut, cell, .direct (.localReg 5) []⟩], [], [], [], 0⟩
     applyJoinPairs stdValAlg [(0, 1)] st1 st2 = none ∧
     (match applyJoinPairs stdValAlg [(0, 1)] st1' st2' with
      | some _ => True
      | none => False)) ∧
    -- 4. `&mut` to a local cannot be returned:
    (match evalFnReturningMut stdValAlg [⟨.byVal, .nat v0⟩]
        (.act (.borrow 1 .mutBorrow (.localSub 0 []))) 1 with
     | .fail => True
     | .ok _ => False) ∧
    -- 5. Five-level aggregate stays projectable after a no-op symbolic join:
    evalFnValue stdValAlg [⟨.byVal, .symBool cond⟩, ⟨.byVal, deepNestedStdVal⟩]
      (.branch (.use (.localSub 0 [])) .skip .skip)
      (.use (.localSub 1 [0, 0, 0, 0, 0])) =
      .ok ⟨zipStdVal (.symBool cond) (.nat 1) (.nat 1), []⟩ ∧
    -- 6. Single-block certificate evidence:
    (∀ st0,
      initFnState stdValAlg [⟨.byVal, .nat 0⟩] = .ok st0 →
      runBlockCfg
        (stepBasicBlock stdValAlg
          (CfgCertificate.singleBlock stdValAlg
            (.act (.assign (.localSub 1 []) (.constVal (.nat 20))))
            (.use (.localSub 1 []))).blocks)
        0 st0 1 = .ret ⟨.nat 20, []⟩) ∧
    -- 7. Final root cells must keep the root loan's tag:
    spatialFinalBindingsHold (m3SpatialModel StdVal) [(0, (0, 0), [])]
      ⟨.unit, [.nat 1]⟩ [⟨0, 0, [], 0, .activeUnique, .init (.nat 1)⟩] ∧
    ¬ spatialFinalBindingsHold (m3SpatialModel StdVal) [(0, (0, 0), [])]
      ⟨.unit, [.nat 1]⟩ [⟨0, 0, [], 7, .activeUnique, .init (.nat 1)⟩] :=
  ⟨rfl, rfl, rfl, rfl, ⟨rfl, trivial⟩, trivial, rfl,
   fun st0 hInit =>
     (CfgCertificate.singleBlock stdValAlg
       (.act (.assign (.localSub 1 []) (.constVal (.nat 20))))
       (.use (.localSub 1 []))).sound [⟨.byVal, .nat 0⟩] st0 _ hInit rfl,
   ⟨⟨rfl, ⟨rfl, Or.inl rfl⟩⟩, rfl⟩,
   (by
     intro h
     cases h with
     | intro hOwn _ =>
       cases hOwn with
       | intro _ hPerm => cases hPerm.1)⟩

/-- Output-free region group locking `(*local 1).0`, used when testing active
region locks across an explicit branch join (`branchExplicitJoin`). -/
def outputFreeRegionOnLocal1Spec : RegionGroupSpec StdVal where
  groupId := 0
  requiredChildren := []
  inputPlaces := [.derefSub 1 [0]]
  outDsts := []
  fwdOuts := fun _ _ => some []
  backFn := fun _ muts _ _ =>
    match muts with
    | [⟨_, .nat v0⟩] => some ([.nat (v0 + 7)], [])
    | _ => none

/-- Admitted plan in which the false arm of `branchExplicitJoin` holds an active
output-free region group (whose ended lock sentinel sits at loan `1`) alongside
a continuing borrow at loan `2`, renamed by `joinPairs = [(1, 2)]` before
writeback and `endRegionGroup 0`. -/
def outputFreeRegionExplicitJoinPlan : FlowPlan StdVal :=
  .seq
    (.branchExplicitJoin (.use (.localSub 0 []))
      (.earlyReturn [] [] (.constVal (.nat 99)))
      (.seq
        (.act (.callMultiRegion [] [outputFreeRegionOnLocal1Spec]))
        (.act (.borrow 2 .mutBorrow (.derefSub 1 [1]))))
      [(1, 2)])
    (.seq
      (.act (.assign (.derefSub 2 []) (.constVal (.nat 42))))
      (.seq
        (.act (.endLoan 1))
        (.act (.endRegionGroup 0))))

/-- Active output-free region lock guards:
1. direct `renameLoanInState` refuses to overwrite the ended `lockLid` (`1`) of
   an active output-free region group, and
2. once that region group ends (`!g.active`, lock released), `renameLoanInState`
   allows reusing `1`. -/
theorem output_free_region_lock_guard_tests (v0 v1 : Nat) :
    let init : EvalOutcome (SymState StdVal) :=
      initFnState stdValAlg [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
    let activeAndBorrow : EvalOutcome (SymState StdVal) :=
      match init with
      | .ok st0 =>
        match stepAction stdValAlg
            (.callMultiRegion [] [outputFreeRegionSpec]) st0 with
        | .ok stRg =>
          stepAction stdValAlg (.borrow 1 .mutBorrow (.derefSub 0 [1])) stRg
        | .fail => .fail
      | .fail => .fail
    let isNone (o : Option (SymState StdVal)) : Bool :=
      match o with
      | some _ => false
      | none => true
    match activeAndBorrow with
    | .ok stLocked =>
      isNone (renameLoanInState stdValAlg 1 2 stLocked) = true ∧
      match stepAction stdValAlg (.endRegionGroup 0) stLocked with
      | .ok stGroupEnded =>
        isNone (renameLoanInState stdValAlg 1 2 stGroupEnded) = false
      | .fail => False
    | .fail => False :=
  ⟨rfl, rfl⟩

/-- Admitted explicit-join plan (`cond = .bool false`) colliding with the
active region group's `lockLid` (`1`), evacuating it to `3`, renaming the
continuing borrow `2 -> 1`, and finishing `endLoan 1` and `endRegionGroup 0`.
-/
theorem output_free_region_explicit_join_bool_plan_test :
    evalFnValue stdValAlg
      [⟨.byVal, .bool false⟩, ⟨.mutRef 0 [], .pair (.nat 10) (.nat 20)⟩]
      outputFreeRegionExplicitJoinPlan
      (.constVal .unit) =
      .ok ⟨.unit, [.pair (.nat 17) (.nat 42)]⟩ :=
  rfl

/-- Symbolic branch variant of `outputFreeRegionExplicitJoinPlan` (`asBool =
none`): true arm early-returns while the false arm continues with an active
output-free region group whose lock collides with `joinPairs = [(1, 2)]`,
before `endLoan 1` and `endRegionGroup 0` complete. -/
theorem output_free_region_explicit_join_sym_plan_test (cond : Bool) :
    evalFnValue stdValAlg
      [⟨.byVal, .symBool cond⟩, ⟨.mutRef 0 [], .pair (.nat 10) (.nat 20)⟩]
      outputFreeRegionExplicitJoinPlan
      (.constVal .unit) =
      .ok ⟨zipStdVal (.symBool cond) (.nat 99) .unit,
        [.pair
          (zipStdVal (.symBool cond) (.nat 10) (.nat 17))
          (zipStdVal (.symBool cond) (.nat 20) (.nat 42))]⟩ := by
  cases cond <;> rfl

/-- Explicit-join plan starting from a state with an active child borrow `1`
whose concrete `.choice (.bool true)` target's untaken false arm names
`.parentLoan 0`. The false arm retires loan `0` (possible because
`noActiveChildLoanEdgesIn` prunes the untaken arm) and allocates loan `2`, and
`branchExplicitJoin` aligns `[(0, 2)]` before ending loans `1` and `0`. -/
def concreteChoicePruneExplicitJoinPlan : FlowPlan StdVal :=
  .seq
    (.branchExplicitJoin (.use (.localSub 0 []))
      (.act (.assign (.derefSub 4 []) (.constVal (.nat 100))))
      (.seq
        (.act (.assign (.derefSub 4 []) (.constVal (.nat 200))))
        (.seq
          (.act (.endLoan 0))
          (.seq
            (.act (.borrow 4 .mutBorrow (.localSub 2 [])))
            (.act (.assign (.derefSub 4 []) (.constVal (.nat 300)))))))
      [(0, 2)])
    (.seq
      (.act (.assign (.derefSub 3 []) (.constVal (.nat 77))))
      (.seq
        (.act (.endLoan 1))
        (.act (.endLoan 0))))

/-- Concrete conditional-borrow `branchExplicitJoin` test: verifies that
`evalPlan` evaluates `concreteChoicePruneExplicitJoinPlan` cleanly for both a
symbolic outer branch (`cond : Bool`) and a concrete false branch without
creating spurious evacuation loans (`stFinal.loans.length = 3`). -/
theorem concrete_choice_prune_explicit_join_tests (cond : Bool) :
    let mkSt0 (cVal : StdVal) : SymState StdVal :=
      ⟨[ ⟨cVal, .unborrowed⟩
       , ⟨.nat 20, .mutLocked 1⟩
       , ⟨.nat 10, .mutLocked 0⟩
       , ⟨.refVal 1 [], .unborrowed⟩
       , ⟨.refVal 0 [], .unborrowed⟩ ],
       [ ⟨0, .activeMut, ⟨.nat 10, .unborrowed⟩, .direct (.localReg 2) []⟩
       , ⟨1, .activeMut, ⟨.nat 20, .unborrowed⟩,
          .choice (.bool true) (.direct (.localReg 1) [])
            (.direct (.parentLoan 0) [])⟩ ],
       [], [], [], 0⟩
    (match evalPlan stdValAlg concreteChoicePruneExplicitJoinPlan
        (mkSt0 (.symBool cond)) with
     | .ok (.continuing stFinal) =>
       stFinal.loans.length = 3 ∧
       stFinal.loans.all (fun e => e.phase.isEnded) = true ∧
       getLocal stdValAlg 1 stFinal =
         some (zipStdVal (.symBool cond) (.nat 77) (.nat 77)) ∧
       getLocal stdValAlg 2 stFinal =
         some (zipStdVal (.symBool cond) (.nat 100) (.nat 300))
     | _ => False) ∧
    (match evalPlan stdValAlg concreteChoicePruneExplicitJoinPlan
        (mkSt0 (.bool false)) with
     | .ok (.continuing stFalseFinal) =>
       stFalseFinal.loans.length = 3 ∧
       stFalseFinal.loans.all (fun e => e.phase.isEnded) = true ∧
       getLocal stdValAlg 1 stFalseFinal = some (.nat 77) ∧
       getLocal stdValAlg 2 stFalseFinal = some (.nat 300)
     | _ => False) := by
  cases cond <;> exact ⟨⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩

end Anneal.PureLift
