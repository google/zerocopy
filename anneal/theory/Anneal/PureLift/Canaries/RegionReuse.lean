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

/-! ### Region-Group Reuse, Handle Copies, and Join Shapes -/

/-- Field accessor for `metaStdValAlg`: only the first component of a
`StdVal.pair` is a field. -/
def metaStdGetField (idx : FieldIdx) (v : StdVal) : Option StdVal :=
  match idx, v with
  | 0, ⟨_, .pairBranch fl _ a _⟩ => some ⟨fl, a⟩
  | _, _ => none

/-- Field updater for `metaStdValAlg`; the second component of the pair is
preserved as non-field metadata. -/
def metaStdSetField (idx : FieldIdx) (v child : StdVal) : Option StdVal :=
  match idx, v, child with
  | 0, ⟨_, .pairBranch _ fr _ b⟩, ⟨fChild, tChild⟩ =>
    some ⟨fChild + fr + 1, .pairBranch fChild fr tChild b⟩
  | _, _, _ => none

theorem metaStd_getField_setField (f : FieldIdx) (s a : StdVal)
    (hGet : metaStdGetField f s = some a) :
    metaStdSetField f s a = some s := by
  cases f with
  | zero =>
    cases s with
    | mk _ ts =>
      cases ts with
      | pairBranch fl fr l r =>
        injection hGet with hEq
        subst hEq
        rfl
      | unit => nomatch hGet
      | nat _ => nomatch hGet
      | bool _ => nomatch hGet
      | symBool _ => nomatch hGet
      | refVal _ _ => nomatch hGet
      | choice _ _ _ _ _ _ => nomatch hGet
  | succ _ => nomatch hGet

theorem metaStd_setField_getField (f : FieldIdx) (s a s' : StdVal)
    (hPut : metaStdSetField f s a = some s') :
    metaStdGetField f s' = some a := by
  cases f with
  | zero =>
    cases s with
    | mk _ ts =>
      cases ts with
      | pairBranch fl fr l r =>
        cases a with
        | mk fa ta =>
          injection hPut with hEq
          subst hEq
          rfl
      | unit => nomatch hPut
      | nat _ => nomatch hPut
      | bool _ => nomatch hPut
      | symBool _ => nomatch hPut
      | refVal _ _ => nomatch hPut
      | choice _ _ _ _ _ _ => nomatch hPut
  | succ _ => nomatch hPut

theorem metaStd_setField_setField (f : FieldIdx) (s a1 a2 s1 : StdVal)
    (hPut1 : metaStdSetField f s a1 = some s1) :
    metaStdSetField f s1 a2 = metaStdSetField f s a2 := by
  cases f with
  | zero =>
    cases s with
    | mk _ ts =>
      cases ts with
      | pairBranch fl fr l r =>
        cases a1 with
        | mk f1 t1 =>
          cases a2 with
          | mk f2 t2 =>
            injection hPut1 with hEq
            subst hEq
            rfl
      | unit => nomatch hPut1
      | nat _ => nomatch hPut1
      | bool _ => nomatch hPut1
      | symBool _ => nomatch hPut1
      | refVal _ _ => nomatch hPut1
      | choice _ _ _ _ _ _ => nomatch hPut1
  | succ _ => nomatch hPut1

theorem metaStd_getField_setField_other (f g : FieldIdx) (s a s' : StdVal)
    (hNe : f ≠ g) (hPut : metaStdSetField f s a = some s') :
    metaStdGetField g s' = metaStdGetField g s := by
  cases f with
  | zero =>
    cases g with
    | zero => exact False.elim (hNe rfl)
    | succ _ => rfl
  | succ _ => nomatch hPut

theorem metaStd_setField_setField_comm (f g : FieldIdx) (s a b s1 s2 : StdVal)
    (hNe : f ≠ g) (h1 : metaStdSetField f s a = some s1)
    (h2 : metaStdSetField g s1 b = some s2) :
    Exists fun s1' =>
      metaStdSetField g s b = some s1' ∧ metaStdSetField f s1' a = some s2 := by
  cases f with
  | zero =>
    cases g with
    | zero => exact False.elim (hNe rfl)
    | succ _ => nomatch h2
  | succ _ => nomatch h1

theorem metaStd_getField_lt_sizeBound (f : FieldIdx) (v c : StdVal)
    (hGet : metaStdGetField f v = some c) :
    f < v.fuel ∧ c.fuel < v.fuel := by
  cases f with
  | zero =>
    cases v with
    | mk fv tv =>
      cases tv with
      | pairBranch fl fr l r =>
        injection hGet with hEq
        subst hEq
        exact ⟨Nat.zero_lt_succ _,
          Nat.lt_succ_of_le (Nat.le_add_right fl fr)⟩
      | unit => nomatch hGet
      | nat _ => nomatch hGet
      | bool _ => nomatch hGet
      | symBool _ => nomatch hGet
      | refVal _ _ => nomatch hGet
      | choice _ _ _ _ _ _ => nomatch hGet
  | succ _ => nomatch hGet

theorem metaStd_decodeRef_getField (f : FieldIdx) (v : StdVal)
    (r : LoanId × SubPath) (hDec : stdDecodeRef v = some r) :
    metaStdGetField f v = none := by
  cases v with
  | mk fv tv =>
    cases tv with
    | refVal _ _ => cases f <;> rfl
    | unit => nomatch hDec
    | nat _ => nomatch hDec
    | bool _ => nomatch hDec
    | symBool _ => nomatch hDec
    | pairBranch _ _ _ _ => nomatch hDec
    | choice _ _ _ _ _ _ => nomatch hDec

theorem metaStd_getField_remapRefInVal (oldLid newLid : LoanId)
    (f : FieldIdx) (v : StdVal) :
    metaStdGetField f (remapStdVal oldLid newLid v) =
      (metaStdGetField f v).map (remapStdVal oldLid newLid) := by
  cases f with
  | succ _ =>
    -- Only index `0` is ever a field.
    rfl
  | zero =>
    cases v with
    | mk fv tv =>
      cases tv with
      | unit => rfl
      | nat _ => rfl
      | bool _ => rfl
      | symBool _ => rfl
      | refVal lid path =>
        change metaStdGetField 0
            (remapStdVal oldLid newLid (.refVal lid path)) = _
        rw [remapStdVal_refVal]
        rfl
      | pairBranch fl fr a b =>
        change metaStdGetField 0
            (remapStdVal oldLid newLid (.pair ⟨fl, a⟩ ⟨fr, b⟩)) = _
        rw [remapStdVal_pair]
        rfl
      | choice fc ft ff c vt vf =>
        change metaStdGetField 0 (remapStdVal oldLid newLid
            (.choice ⟨fc, c⟩ ⟨ft, vt⟩ ⟨ff, vf⟩)) = _
        rw [remapStdVal_choice]
        rfl

theorem metaStd_remapRefInVal_leaf (oldLid newLid : LoanId) (v : StdVal)
    (hDec : stdDecodeRef v = none) (hFields : ∀ f, metaStdGetField f v = none)
    (hSplit : stdBranchSplit v = none) : remapStdVal oldLid newLid v = v :=
  stdVal_remapRefInVal_leaf oldLid newLid v hDec
    (fun f => by
      cases v with
      | mk fv tv =>
        cases tv with
        | pairBranch _ _ _ _ => exact nomatch hFields 0
        | unit => cases f with | zero => rfl | succ f' => cases f' <;> rfl
        | nat _ => cases f with | zero => rfl | succ f' => cases f' <;> rfl
        | bool _ => cases f with | zero => rfl | succ f' => cases f' <;> rfl
        | symBool _ =>
          cases f with
          | zero => rfl
          | succ f' => cases f' <;> rfl
        | refVal _ _ =>
          cases f with
          | zero => rfl
          | succ f' => cases f' <;> rfl
        | choice _ _ _ _ _ _ =>
          cases f with
          | zero => rfl
          | succ f' => cases f' <;> rfl)
    hSplit

/-- Test algebra whose aggregates carry non-field metadata: a `StdVal.pair`
exposes only its first component as a field, and its second component plays the
role of an outer tag (like a `MirVal.adt` discriminant). It therefore never
reports two aggregates as field-wise mergeable. Handle renaming still renames
handles inside the tag (`remapStdVal`); the `ValAlgebra` laws allow that, since
they constrain only what `getField` and the other observers expose. -/
theorem metaStd_getField_projectBranchVal (cond : StdVal) (branch : Bool)
    (f : FieldIdx) (s a : StdVal) (hGet : metaStdGetField f s = some a) :
    metaStdGetField f (projectBranchStdVal cond branch s) =
      some (projectBranchStdVal cond branch a) := by
  cases f with
  | succ _ => nomatch hGet
  | zero =>
    cases s with
    | mk fs ts =>
      cases ts with
      | unit => nomatch hGet
      | nat _ => nomatch hGet
      | bool _ => nomatch hGet
      | symBool _ => nomatch hGet
      | refVal _ _ => nomatch hGet
      | choice _ _ _ _ _ _ => nomatch hGet
      | pairBranch fl fr l r =>
        injection hGet with hEq
        subst hEq
        change metaStdGetField 0
            (projectBranchStdVal cond branch (.pair ⟨fl, l⟩ ⟨fr, r⟩)) = _
        rw [projectBranchStdVal_pair]
        rfl

def metaStdValAlg : ValAlgebra StdVal :=
  { stdValAlg with
    getField := metaStdGetField
    getField_projectBranchVal := metaStd_getField_projectBranchVal
    setField := metaStdSetField
    getField_setField := metaStd_getField_setField
    setField_getField := metaStd_setField_getField
    setField_setField := metaStd_setField_setField
    getField_setField_other := metaStd_getField_setField_other
    setField_setField_comm := metaStd_setField_setField_comm
    getField_lt_sizeBound := metaStd_getField_lt_sizeBound
    decodeRef_getField := metaStd_decodeRef_getField
    getField_remapRefInVal := metaStd_getField_remapRefInVal
    remapRefInVal_leaf := metaStd_remapRefInVal_leaf
    sameAggregateShape := fun _ _ => false
    sameAggregateShape_ext := fun _ _ hShape _ => nomatch hShape
    sameAggregateShape_setField := fun _ _ _ _ _ hShape _ => nomatch hShape }

/-- By-value call summary returning its single pure argument. -/
def identityByValSummary : CallSummary StdVal where
  returnsMutBorrow := false
  fwd pureVals _ :=
    match pureVals with
    | [v] => some v
    | _ => none
  back _ _ _ := some []

/-- By-value call summary that ignores its argument and returns `.unit`, so
only the argument check can reject a call. -/
def dropArgSummary : CallSummary StdVal where
  returnsMutBorrow := false
  fwd _ _ := some .unit
  back _ _ _ := some []

/-- By-value call summary that fabricates a handle to loan `0`. -/
def forgeHandleSummary : CallSummary StdVal where
  returnsMutBorrow := false
  fwd _ _ := some (.refVal 0 [])
  back _ _ _ := some []


/-- Install parent group `0` requiring child group `1`, end the child, and then
install a second child `1`, either while the parent is still active
(`endParentFirst = false`) or after the parent ends. Every group is ended
before returning. -/
def regionReusePlan (endParentFirst : Bool) : FlowPlan StdVal :=
  let reinstallChild : FlowPlan StdVal :=
    .seq (.act (.callMultiRegion [] [bareRegionSpec 1 []]))
      (.act (.endRegionGroup 1))
  .seq
    (.act (.callMultiRegion []
      [bareRegionSpec 0 [1], bareRegionSpec 1 []]))
    (.seq
      (.act (.endRegionGroup 1))
      (match endParentFirst with
       | true => .seq (.act (.endRegionGroup 0)) reinstallChild
       | false => .seq reinstallChild (.act (.endRegionGroup 0))))

/-- A guard that itself depends on `.symBool true`. -/
def dependentGuard : StdVal :=
  zipStdVal (.symBool true) (.bool true) (.bool false)

/-- Loan `5` with an active child borrow of its field `[0]`, so the binding of
its root sub-place sees a `.split` permission. -/
def splitLoanState : SymState StdVal :=
  ⟨[], [⟨5, .activeMut,
         ⟨.pair (.nat 1) (.nat 2), .split [([0], .mutLocked 6)]⟩,
         .rootParam 0⟩], [], [], [], 0⟩

/-- One concrete cell at `(0, 0, [])` holding loan `5`'s value under `tag`. -/
def splitHeap (tag : Nat) : List (M3Cell StdVal) :=
  [⟨0, 0, [], tag, .activeUnique, .init (.pair (.nat 1) (.nat 2))⟩]

/-- Reinstalling a completed child region group while a parent from an earlier
invocation still requires it fails, even though the plan later ends every
group. -/
theorem region_group_reuse_while_parent_active_rejected :
    evalFnValue stdValAlg [] (regionReusePlan false) (.constVal .unit) =
      .fail :=
  rfl

/-- Reinstalling child region group `1` after the parent that required it has
ended succeeds; together with
`region_group_reuse_while_parent_active_rejected` this shows that only the
reuse ordering is rejected. -/
theorem region_group_reuse_after_parent_ends :
    evalFnValue stdValAlg [] (regionReusePlan true) (.constVal .unit) =
      .ok ⟨.unit, []⟩ :=
  rfl

/-- Tests for copying borrow handles: a value containing a
handle to an active mutable loan, an ended loan, or a loan that does not exist
cannot be copied by `assign`, by a by-value call argument, or by a by-value
call result, while root-level shared handles (`subPath = []`) can. -/
theorem mut_handle_copy_tests :
    evalFnValue stdValAlg [⟨.mutRef 0 [], .nat 5⟩]
      (.act (.assign (.localSub 1 []) (.use (.localSub 0 []))))
      (.constVal .unit) = .fail ∧
    evalFnValue stdValAlg [⟨.mutRef 0 [], .nat 5⟩]
      (.act (.assign (.localSub 1 [])
        (.constVal (.pair (.refVal 0 []) .unit))))
      (.constVal .unit) = .fail ∧
    evalFnValue stdValAlg [⟨.byVal, .nat 5⟩]
      (.act (.assign (.localSub 1 []) (.constVal (.refVal 3 []))))
      (.constVal .unit) = .fail ∧
    evalFnValue stdValAlg [⟨.mutRef 0 [], .nat 5⟩]
      (.act (.call 1 dropArgSummary [.use (.localSub 0 [])] []))
      (.constVal .unit) = .fail ∧
    evalFnValue stdValAlg [⟨.mutRef 0 [], .nat 5⟩]
      (.act (.call 1 forgeHandleSummary [] []))
      (.constVal .unit) = .fail ∧
    evalFnValue stdValAlg [⟨.sharedRef 0 [], .nat 5⟩]
      (.act (.assign (.localSub 1 []) (.use (.localSub 0 []))))
      (.use (.derefSub 1 [])) = .ok ⟨.nat 5, []⟩ ∧
    evalFnValue stdValAlg [⟨.mutRef 0 [], .nat 5⟩]
      (.seq (.act (.borrow 1 .mutBorrow (.derefSub 0 [])))
        (.seq (.act (.endLoan 1))
          (.act (.assign (.localSub 2 []) (.use (.localSub 1 []))))))
      (.constVal .unit) = .fail :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Tests for `Plan`, `Adapter`, and
`Canaries` (see also `region_group_reuse_while_parent_active_rejected`,
`region_group_reuse_after_parent_ends`, and
`mut_handle_copy_tests`):
1. Branch joins merge aggregates field by field only when
   `sameAggregateShape` vouches that no non-field data differs; otherwise the
   whole aggregate goes through `zipVal`,
2. Storing a borrow handle or call result into a local more than one slot past
   the end, or into a local the borrow itself just locked, fails instead of
   leaving a loan without its handle,
3. `endLoanAtLocal` refuses to read a handle local that is mutably borrowed,
4. `projectBranchStdVal` projects guards that themselves depend on the
   projected condition,
5. `spatialBindingsHold` ties the concrete cell of a `.split` sub-place to the
   bound loan's tag, and
6. `getPath_putPath_diverging` derives sibling-field preservation from
   `getField_setField_other`. -/
theorem aggregate_shape_local_slot_and_guard_tests :
    -- 1. Field-wise merge requires `sameAggregateShape`:
    zipOrKeepSameRef metaStdValAlg (.symBool true)
      (.pair (.nat 1) (.nat 7)) (.pair (.nat 1) (.nat 8)) =
      .choice (.symBool true) (.pair (.nat 1) (.nat 7))
        (.pair (.nat 1) (.nat 8)) ∧
    zipOrKeepSameRef stdValAlg (.symBool true)
      (.pair (.nat 1) (.nat 7)) (.pair (.nat 1) (.nat 8)) =
      .pair (.choice (.symBool true) (.nat 1) (.nat 1))
        (.choice (.symBool true) (.nat 7) (.nat 8)) ∧
    evalFnValue metaStdValAlg
      [⟨.byVal, .symBool true⟩, ⟨.byVal, .pair (.nat 1) (.nat 7)⟩]
      (.branch (.use (.localSub 0 []))
        .skip
        (.act (.assign (.localSub 1 [])
          (.constVal (.pair (.nat 1) (.nat 8))))))
      (.use (.localSub 1 [])) =
      .ok ⟨.choice (.symBool true) (.pair (.nat 1) (.nat 7))
             (.pair (.nat 1) (.nat 8)), []⟩ ∧
    -- 2. Destinations must exist or be the next fresh local:
    evalFnValue stdValAlg [⟨.mutRef 0 [], .nat 5⟩]
      (.seq (.act (.borrow 3 .mutBorrow (.derefSub 0 []))) (.act (.endLoan 1)))
      (.constVal .unit) = .fail ∧
    evalFnValue stdValAlg [⟨.mutRef 0 [], .nat 5⟩]
      (.seq (.act (.borrow 1 .mutBorrow (.derefSub 0 []))) (.act (.endLoan 1)))
      (.constVal .unit) = .ok ⟨.unit, [.nat 5]⟩ ∧
    evalFnValue stdValAlg [⟨.byVal, .nat 5⟩]
      (.act (.borrow 0 .mutBorrow (.localSub 0 [])))
      (.constVal .unit) = .fail ∧
    evalFnValue stdValAlg [⟨.byVal, .nat 5⟩]
      (.act (.call 3 identityByValSummary [.constVal (.nat 9)] []))
      (.constVal .unit) = .fail ∧
    evalFnValue stdValAlg [⟨.byVal, .nat 5⟩]
      (.act (.call 1 identityByValSummary [.constVal (.nat 9)] []))
      (.use (.localSub 1 [])) = .ok ⟨.nat 9, []⟩ ∧
    evalFnValue stdValAlg [⟨.mutRef 0 [], .nat 5⟩]
      (.seq
        (.act (.callMultiRegion []
          [{ regionSpecWithAdd 1 with
              inputPlaces := [.derefSub 0 []], outDsts := [3] }]))
        (.act (.endRegionGroup 0)))
      (.constVal .unit) = .fail ∧
    evalFnValue stdValAlg [⟨.mutRef 0 [], .nat 5⟩]
      (.seq
        (.act (.callMultiRegion []
          [{ regionSpecWithAdd 1 with
              inputPlaces := [.derefSub 0 []], outDsts := [1] }]))
        (.act (.endRegionGroup 0)))
      (.constVal .unit) = .ok ⟨.unit, [.nat 6]⟩ ∧
    -- 3. A mutably borrowed handle local cannot be read to end its loan:
    evalFnValue stdValAlg [⟨.mutRef 0 [], .nat 5⟩]
      (.seq (.act (.borrow 1 .mutBorrow (.derefSub 0 [])))
        (.seq (.act (.borrow 2 .mutBorrow (.localSub 1 [])))
          (.seq (.act (.endLoanAtLocal 1)) (.act (.endLoan 2)))))
      (.constVal .unit) = .fail ∧
    evalFnValue stdValAlg [⟨.mutRef 0 [], .nat 5⟩]
      (.seq (.act (.borrow 1 .mutBorrow (.derefSub 0 [])))
        (.seq (.act (.borrow 2 .mutBorrow (.localSub 1 [])))
          (.seq (.act (.endLoan 2)) (.act (.endLoanAtLocal 1)))))
      (.constVal .unit) = .ok ⟨.unit, [.nat 5]⟩ ∧
    -- 4. Dependent guards are projected:
    projectBranchStdVal (.symBool true) true
      (.choice dependentGuard (.nat 1) (.nat 2)) = .nat 1 ∧
    projectBranchStdVal (.symBool true) false
      (.choice dependentGuard (.nat 1) (.nat 2)) = .nat 2 ∧
    -- 5. A `.split` root cell must carry the bound loan's tag:
    spatialBindingsHold (m3SpatialModel StdVal) [(5, (0, 0), [])]
      splitLoanState (splitHeap 5) ∧
    ¬ spatialBindingsHold (m3SpatialModel StdVal) [(5, (0, 0), [])]
      splitLoanState (splitHeap 999) ∧
    -- 6. Diverging sub-paths are separated by the field laws:
    (∀ (s v s' : StdVal),
      putPath stdValAlg [0, 1] s v = some s' →
      getPath stdValAlg [0, 0] s' = getPath stdValAlg [0, 0] s) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   ⟨⟨trivial, trivial⟩, ⟨⟨rfl, ⟨rfl, ⟨rfl, rfl⟩⟩⟩, trivial⟩⟩,
   (fun h => nomatch h.2.1.2.2.1),
   fun s v s' hPut =>
     getPath_putPath_diverging stdValAlg 1 0 [] [] (fun h => nomatch h) [0]
       s v s' hPut⟩

/-! ### Region Deposits, Field Commutation, and Region Outputs -/


/-- Install independent groups `0` and `1` over `*p.0` and `*p.1`, then end
them in the order `gids`. Both groups deposit a value that no parent consumes.
-/
def independentGroupsPlan (gids : List RegionGroupId) :
    FlowPlan StdVal :=
  .seq
    (.act (.callMultiRegion []
      [ countingRegionSpec 0 [] (.derefSub 0 [0])
      , countingRegionSpec 1 [] (.derefSub 0 [1]) ]))
    (listFold .skip (fun gid _ ih => .seq (.act (.endRegionGroup gid)) ih) gids)

/-- Install parent `0` (requiring child `1`) over `*p.0`, child `1` over
`*p.1.0`, and unrelated group `2` over `*p.1.1`, then end them in the order
`gids`. Only the child deposits a value. -/
def childDepositPlan (gids : List RegionGroupId) : FlowPlan StdVal :=
  .seq
    (.act (.callMultiRegion []
      [ countingRegionSpec 0 [1] (.derefSub 0 [0]) []
      , countingRegionSpec 1 [] (.derefSub 0 [1, 0])
      , countingRegionSpec 2 [] (.derefSub 0 [1, 1]) [] ]))
    (listFold .skip (fun gid _ ih => .seq (.act (.endRegionGroup gid)) ih) gids)

/-- The value of loan `0` after running `plan` from the entry state of
`params`, if the plan falls through. -/
def loan0After (params : List (ParamInput StdVal))
    (plan : FlowPlan StdVal) : Option StdVal :=
  match initFnState stdValAlg params with
  | .ok st0 =>
    match evalPlan stdValAlg plan st0 with
    | .ok (.continuing st) => (findLoan 0 st.loans).map (fun e => e.cell.val)
    | _ => none
  | .fail => none

/-- Regression tests for scoped region deposits and commuting field updates:
1. Independent region groups receive no deposits, so ending them in either
   order writes back the same values; their unconsumed deposits then block a
   clean return,
2. A child's deposits reach only the parent that lists it in
   `requiredChildren`, regardless of when an unrelated group ends, and the
   parent consumes them (`takeChildDeposits` orders them by child, then by
   deposit order), and
3. `putPath_putPath_diverging_comm` makes updates of diverging sub-paths
   order-independent as whole values. -/
theorem region_deposit_scope_and_commutation_tests :
    -- 1. Independent groups, both orders:
    loan0After [⟨.mutRef 0 [], .pair (.nat 5) (.nat 5)⟩]
      (independentGroupsPlan [0, 1]) =
      some (.pair (.nat 0) (.nat 0)) ∧
    loan0After [⟨.mutRef 0 [], .pair (.nat 5) (.nat 5)⟩]
      (independentGroupsPlan [1, 0]) =
      some (.pair (.nat 0) (.nat 0)) ∧
    evalFnValue stdValAlg [⟨.mutRef 0 [], .pair (.nat 5) (.nat 5)⟩]
      (independentGroupsPlan [0, 1]) (.constVal .unit) = .fail ∧
    -- 2. Only the declared parent sees (and consumes) the child's deposit:
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat 5) (.pair (.nat 5) (.nat 5))⟩]
      (childDepositPlan [1, 2, 0]) (.constVal .unit) =
      .ok ⟨.unit, [.pair (.nat 1) (.pair (.nat 0) (.nat 0))]⟩ ∧
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat 5) (.pair (.nat 5) (.nat 5))⟩]
      (childDepositPlan [2, 1, 0]) (.constVal .unit) =
      .ok ⟨.unit, [.pair (.nat 1) (.pair (.nat 0) (.nat 0))]⟩ ∧
    (match endRegionGroupInState stdValAlg 1
        ⟨[], [], [⟨1, true, 0, [], [], [], fun _ _ => some ([], [.nat 9])⟩,
              ⟨0, true, 1, [], [], [1], fun _ deps => some ([], deps)⟩],
         [(7, .nat 3)], [], 0⟩ with
     | .ok st1 =>
       match endRegionGroupInState stdValAlg 0 st1 with
       | .ok st2 => st2.regionDeposits = [(7, .nat 3), (0, .nat 9)]
       | .fail => False
     | .fail => False) ∧
    takeChildDeposits [2, 1]
      [(1, StdVal.nat 10), (3, .nat 30), (2, .nat 20), (1, .nat 11)] =
      ([.nat 20, .nat 10, .nat 11], [(3, .nat 30)]) ∧
    -- 3. Diverging updates commute:
    (∀ (s v w s1 s2 : StdVal),
      putPath stdValAlg [0, 1] s v = some s1 →
      putPath stdValAlg [1] s1 w = some s2 →
      Exists fun s1' =>
        putPath stdValAlg [1] s w = some s1' ∧
        putPath stdValAlg [0, 1] s1' v = some s2) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   fun s v w s1 s2 hP hQ =>
     putPath_putPath_diverging_comm stdValAlg 0 1 [1] [] (fun h => nomatch h)
       s v w s1 s2 hP hQ⟩

/-- Region group `gid` over `input` with one output bound to `dst`; its
backward function writes the output's final value back to `input` and makes
no deposits. -/
def noDepositRegionSpec (gid : RegionGroupId) (input : PlaceExpr)
    (dst : LocalId) : RegionGroupSpec StdVal where
  groupId := gid
  requiredChildren := []
  inputPlaces := [input]
  outDsts := [dst]
  fwdOuts := fun _ muts =>
    match muts with
    | [v] => some [v]
    | _ => none
  backFn := fun _ _ outs _ =>
    match outs with
    | [v] => some ([v], [])
    | _ => none

/-- Install group `3` over `*p` with its output in `dst`, set the output to
`7`, and end the group. -/
def installAndEndPlan (dst : LocalId) : FlowPlan StdVal :=
  .seq
    (.act (.callMultiRegion []
      [noDepositRegionSpec 3 (.derefSub 1 []) dst]))
    (.seq
      (.act (.assign (.derefSub dst []) (.constVal (.nat 7))))
      (.act (.endRegionGroup 3)))

/-- A two-block CFG whose entry block branches on local `0` to block `1` on
both edges. -/
def sameTargetCfg : List (BasicBlock StdVal) :=
  [ ⟨.skip, .branch (.use (.localSub 0 [])) 1 1⟩
  , ⟨.act (.assign (.localSub 1 []) (.constVal (.nat 10))),
     .ret (.use (.localSub 1 []))⟩ ]

/-- Regression tests for multi-region output destinations, branch-local region
groups at joins, and CFG branches with identical successors:
1. A call whose outputs share a destination local fails, within one group or
   across groups, while distinct destinations succeed,
2. A symbolic join accepts a region group installed and fully ended in one
   branch (new, or reinstalled over a completed entry), but still rejects one
   that is active, left deposits, or is required by an active group, and
3. A symbolic CFG branch whose successors coincide runs the successor once and
   returns its result unmerged. -/
theorem region_outputs_joins_and_cfg_branch_tests :
    -- 1. Distinct output destinations:
    planStepFails [⟨.mutRef 0 [], .pair (.nat 1) (.nat 2)⟩]
      (.act (.callMultiRegion []
        [ { regionSpecWithAdd 1 with
              inputPlaces := [.derefSub 0 [0]], outDsts := [1] }
        , { regionSpecWithAdd 2 with
              groupId := 1, inputPlaces := [.derefSub 0 [1]], outDsts := [1] }
        ])) = true ∧
    planStepFails [⟨.mutRef 0 [], .nat 1⟩]
      (.act (.callMultiRegion []
        [ { regionSpecWithAdd 1 with
              inputPlaces := [.derefSub 0 []], outDsts := [1, 1]
              fwdOuts := fun _ muts =>
                match muts with
                | [v] => some [v, v]
                | _ => none } ])) = true ∧
    planStepFails [⟨.mutRef 0 [], .pair (.nat 1) (.nat 2)⟩]
      (.act (.callMultiRegion []
        [ { regionSpecWithAdd 1 with
              inputPlaces := [.derefSub 0 [0]], outDsts := [1] }
        , { regionSpecWithAdd 2 with
              groupId := 1, inputPlaces := [.derefSub 0 [1]], outDsts := [2] }
        ])) = false ∧
    evalFnValue stdValAlg [⟨.mutRef 0 [], .pair (.nat 1) (.nat 2)⟩]
      (.seq
        (.act (.callMultiRegion []
          [ { regionSpecWithAdd 1 with
                inputPlaces := [.derefSub 0 [0]], outDsts := [1] }
          , { regionSpecWithAdd 2 with
                groupId := 1, inputPlaces := [.derefSub 0 [1]],
                outDsts := [2] } ]))
        (.seq (.act (.endRegionGroup 1)) (.act (.endRegionGroup 0))))
      (.constVal .unit) = .ok ⟨.unit, [.pair (.nat 2) (.nat 4)]⟩ ∧
    -- 2. Branch-local region groups at joins:
    evalFnValue stdValAlg [⟨.byVal, .symBool true⟩, ⟨.mutRef 0 [], .nat 5⟩]
      (.branch (.use (.localSub 0 [])) (installAndEndPlan 2) .skip)
      (.constVal .unit) =
      .ok ⟨.unit, [zipStdVal (.symBool true) (.nat 7) (.nat 5)]⟩ ∧
    evalFnValue stdValAlg [⟨.byVal, .symBool true⟩, ⟨.mutRef 0 [], .nat 5⟩]
      (.seq (installAndEndPlan 2)
        (.branch (.use (.localSub 0 [])) (installAndEndPlan 2) .skip))
      (.constVal .unit) =
      .ok ⟨.unit, [zipStdVal (.symBool true) (.nat 7) (.nat 7)]⟩ ∧
    planStepFails [⟨.byVal, .symBool true⟩]
      (.branch (.use (.localSub 0 []))
        (.act (.callMultiRegion [] [bareRegionSpec 3 []])) .skip) =
      true ∧
    planStepFails [⟨.byVal, .symBool true⟩, ⟨.mutRef 0 [], .nat 5⟩]
      (.branch (.use (.localSub 0 []))
        (.seq
          (.act (.callMultiRegion []
            [countingRegionSpec 3 [] (.derefSub 1 [])]))
          (.act (.endRegionGroup 3)))
        .skip) = true ∧
    planStepFails [⟨.byVal, .symBool true⟩, ⟨.mutRef 0 [], .nat 5⟩]
      (.branch (.use (.localSub 0 []))
        (.seq
          (.act (.callMultiRegion []
            [countingRegionSpec 3 [] (.derefSub 1 []) []]))
          (.act (.endRegionGroup 3)))
        .skip) = false ∧
    joinRegionGroups stdValAlg (.symBool true)
      [⟨0, true, 0, [], [], [3], fun _ _ => none⟩,
       ⟨3, false, 1, [], [], [], fun _ _ => none⟩]
      [⟨0, true, 0, [], [], [3], fun _ _ => none⟩] = none ∧
    -- 3. Identical CFG successors:
    (match initFnState stdValAlg [⟨.byVal, .symBool true⟩] with
     | .ok st0 =>
       runBlockCfg (stepBasicBlock stdValAlg sameTargetCfg) 0 st0 2 =
         .ret ⟨.nat 10, []⟩
     | .fail => False) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Anneal.PureLift
