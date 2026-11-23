-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.Core
public import Init.Data.List.Basic
public import Init.Data.Nat.Basic
public import Anneal.PureLift.Lens
public import Anneal.PureLift.PermTree
public import Anneal.PureLift.LoanGraph
public import Anneal.PureLift.SpatialPin
public import Anneal.PureLift.Plan
public import Anneal.PureLift.BlockCfg
public import Anneal.PureLift.Adapter

public import Anneal.PureLift.Canaries.Fixtures

public section

namespace Anneal.PureLift

/-! ### Field Joins, Uninitialized Locals, Handles, and Writeback Ownership -/

/-- Field-index map for `gapStdValAlg`: field `1` is a pair's first component,
field `2` its second, and index `0` is a gap. -/
@[expose] def gapIdx (f : FieldIdx) : Option FieldIdx :=
  match f with
  | 1 => some 0
  | 2 => some 1
  | _ => none

theorem gapIdx_inj (f g i : FieldIdx) (hf : gapIdx f = some i)
    (hg : gapIdx g = some i) : f = g := by
  cases f with
  | zero => nomatch hf
  | succ f1 =>
    cases g with
    | zero => nomatch hg
    | succ g1 =>
      cases f1 with
      | zero =>
        cases g1 with
        | zero => rfl
        | succ g2 =>
          cases g2 with
          | zero =>
            injection hf with hf'
            injection hg with hg'
            subst hf'
            nomatch hg'
          | succ _ => nomatch hg
      | succ f2 =>
        cases f2 with
        | zero =>
          cases g1 with
          | zero =>
            injection hf with hf'
            injection hg with hg'
            subst hf'
            nomatch hg'
          | succ g2 =>
            cases g2 with
            | zero => rfl
            | succ _ => nomatch hg
        | succ _ => nomatch hf

@[expose] def gapGetField (f : FieldIdx) (v : StdVal) : Option StdVal :=
  match gapIdx f with
  | some i => stdValGetField i v
  | none => none

@[expose] def gapSetField (f : FieldIdx) (v child : StdVal) : Option StdVal :=
  match gapIdx f with
  | some i => stdValSetField i v child
  | none => none

theorem gap_getField_setField (f : FieldIdx) (s a : StdVal)
    (hGet : gapGetField f s = some a) : gapSetField f s a = some s := by
  unfold gapGetField at hGet
  unfold gapSetField
  revert hGet
  cases gapIdx f with
  | none =>
    intro hFalse
    nomatch hFalse
  | some i => exact stdVal_getField_setField i s a

theorem gap_setField_getField (f : FieldIdx) (s a s' : StdVal)
    (hPut : gapSetField f s a = some s') : gapGetField f s' = some a := by
  unfold gapSetField at hPut
  unfold gapGetField
  revert hPut
  cases gapIdx f with
  | none =>
    intro hFalse
    nomatch hFalse
  | some i => exact stdVal_setField_getField i s a s'

theorem gap_setField_setField (f : FieldIdx) (s a1 a2 s1 : StdVal)
    (hPut1 : gapSetField f s a1 = some s1) :
    gapSetField f s1 a2 = gapSetField f s a2 := by
  unfold gapSetField at hPut1
  unfold gapSetField
  revert hPut1
  cases gapIdx f with
  | none =>
    intro hFalse
    nomatch hFalse
  | some i => exact stdVal_setField_setField i s a1 a2 s1

theorem gap_getField_setField_other (f g : FieldIdx) (s a s' : StdVal)
    (hNe : f ≠ g) (hPut : gapSetField f s a = some s') :
    gapGetField g s' = gapGetField g s := by
  unfold gapSetField at hPut
  unfold gapGetField
  revert hPut
  cases hf : gapIdx f with
  | none =>
    intro hFalse
    nomatch hFalse
  | some i =>
    intro hPut
    cases hg : gapIdx g with
    | none => rfl
    | some j =>
      exact stdVal_getField_setField_other i j s a s'
        (fun hEq => hNe (gapIdx_inj f g j (hEq ▸ hf) hg)) hPut

theorem gap_setField_setField_comm (f g : FieldIdx) (s a b s1 s2 : StdVal)
    (hNe : f ≠ g) (h1 : gapSetField f s a = some s1)
    (h2 : gapSetField g s1 b = some s2) :
    Exists fun s1' =>
      gapSetField g s b = some s1' ∧ gapSetField f s1' a = some s2 := by
  unfold gapSetField at h1 h2
  unfold gapSetField
  revert h1 h2
  cases hf : gapIdx f with
  | none =>
    intro hFalse
    nomatch hFalse
  | some i =>
    cases hg : gapIdx g with
    | none =>
      intro _ hFalse
      nomatch hFalse
    | some j =>
      intro h1 h2
      exact stdVal_setField_setField_comm i j s a b s1 s2
        (fun hEq => hNe (gapIdx_inj f g j (hEq ▸ hf) hg)) h1 h2

theorem gap_getField_lt_sizeBound (f : FieldIdx) (v c : StdVal)
    (hGet : gapGetField f v = some c) :
    f < v.fuel ∧ c.fuel < v.fuel := by
  cases f with
  | zero => nomatch hGet
  | succ f1 =>
    cases f1 with
    | zero =>
      cases v with
      | mk fv tv =>
        cases tv with
        | pairBranch fl fr l r =>
          injection hGet with hEq
          subst hEq
          exact ⟨Nat.succ_lt_succ
            (Nat.lt_of_lt_of_le (stdValTree_fuel_pos l)
              (Nat.le_add_right fl fr)),
            Nat.lt_succ_of_le (Nat.le_add_right fl fr)⟩
        | unit => nomatch hGet
        | nat _ => nomatch hGet
        | bool _ => nomatch hGet
        | symBool _ => nomatch hGet
        | refVal _ _ => nomatch hGet
        | choice _ _ _ _ _ _ => nomatch hGet
    | succ f2 =>
      cases f2 with
      | zero =>
        cases v with
        | mk fv tv =>
          cases tv with
          | pairBranch fl fr l r =>
            injection hGet with hEq
            subst hEq
            exact ⟨Nat.succ_lt_succ
              (Nat.add_le_add (stdValTree_fuel_pos l) (stdValTree_fuel_pos r)),
              Nat.lt_succ_of_le (Nat.le_add_left fr fl)⟩
          | unit => nomatch hGet
          | nat _ => nomatch hGet
          | bool _ => nomatch hGet
          | symBool _ => nomatch hGet
          | refVal _ _ => nomatch hGet
          | choice _ _ _ _ _ _ => nomatch hGet
      | succ _ => nomatch hGet

theorem gap_sameAggregateShape_ext (v1 v2 : StdVal)
    (hShape : stdSameAggregateShape v1 v2 = true)
    (hFields : ∀ f, gapGetField f v1 = gapGetField f v2) : v1 = v2 :=
  stdVal_sameAggregateShape_ext v1 v2 hShape (fun f =>
    match f with
    | 0 => hFields 1
    | 1 => hFields 2
    | _ + 2 => rfl)

theorem gap_sameAggregateShape_setField (f : FieldIdx) (s a s' t : StdVal)
    (hShape : stdSameAggregateShape s t = true)
    (hPut : gapSetField f s a = some s') :
    stdSameAggregateShape s' t = true := by
  unfold gapSetField at hPut
  revert hPut
  cases gapIdx f with
  | none =>
    intro hFalse
    nomatch hFalse
  | some i => exact stdVal_sameAggregateShape_setField i s a s' t hShape

theorem gap_decodeRef_getField (f : FieldIdx) (v : StdVal)
    (r : LoanId × SubPath) (hDec : stdDecodeRef v = some r) :
    gapGetField f v = none := by
  unfold gapGetField
  cases gapIdx f with
  | none => rfl
  | some i => exact stdVal_decodeRef_getField i v r hDec

theorem gap_getField_remapRefInVal (oldLid newLid : LoanId) (f : FieldIdx)
    (v : StdVal) :
    gapGetField f (remapStdVal oldLid newLid v) =
      (gapGetField f v).map (remapStdVal oldLid newLid) := by
  unfold gapGetField
  cases gapIdx f with
  | none => rfl
  | some i => exact stdVal_getField_remapRefInVal oldLid newLid i v

theorem gap_remapRefInVal_leaf (oldLid newLid : LoanId) (v : StdVal)
    (hDec : stdDecodeRef v = none) (hFields : ∀ f, gapGetField f v = none)
    (hSplit : stdBranchSplit v = none) : remapStdVal oldLid newLid v = v :=
  -- `gapGetField (i + 1)` is `stdValGetField i` for the indices `0` and `1`
  -- that `stdValGetField` can answer.
  stdVal_remapRefInVal_leaf oldLid newLid v hDec
    (fun f =>
      match f with
      | 0 => hFields 1
      | 1 => hFields 2
      | _ + 2 => rfl)
    hSplit

/-- Test algebra over `StdVal` whose pairs expose their components at field
indices `1` and `2`, leaving a gap at index `0`. All `ValAlgebra` laws hold,
so traversals must neither require field `0` nor stop at the first missing
index. -/
theorem gap_getField_projectBranchVal (cond : StdVal) (branch : Bool)
    (f : FieldIdx) (s a : StdVal) (hGet : gapGetField f s = some a) :
    gapGetField f (projectBranchStdVal cond branch s) =
      some (projectBranchStdVal cond branch a) := by
  unfold gapGetField at hGet
  unfold gapGetField
  revert hGet
  cases gapIdx f with
  | none =>
    intro hFalse
    nomatch hFalse
  | some i => exact stdVal_getField_projectBranchVal cond branch i s a

@[expose] def gapStdValAlg : ValAlgebra StdVal :=
  { stdValAlg with
    getField := gapGetField
    getField_projectBranchVal := gap_getField_projectBranchVal
    setField := gapSetField
    getField_setField := gap_getField_setField
    setField_getField := gap_setField_getField
    setField_setField := gap_setField_setField
    getField_setField_other := gap_getField_setField_other
    setField_setField_comm := gap_setField_setField_comm
    getField_lt_sizeBound := gap_getField_lt_sizeBound
    decodeRef_getField := gap_decodeRef_getField
    getField_remapRefInVal := gap_getField_remapRefInVal
    remapRefInVal_leaf := gap_remapRefInVal_leaf
    sameAggregateShape_ext := gap_sameAggregateShape_ext
    sameAggregateShape_setField := gap_sameAggregateShape_setField }

/-- A by-value call summary whose backward function writes `out` back to its
single mutable argument. -/
@[expose] def writebackSummary (out : StdVal) : CallSummary StdVal where
  returnsMutBorrow := false
  fwd _ _ := some .unit
  back _ _ _ := some [out]

/-- Freeze loan `1` (a reborrow of `*p`), overwrite its spatial cell with
`cell`, and reabsorb it. -/
@[expose] def spatialOverwritePlan (cell : StdVal) : FlowPlan StdVal :=
  .seq (.act (.borrow 1 .mutBorrow (.derefSub 0 [])))
    (.seq (.act (.freezeSpatial 1 valueCellCodec))
      (.seq (.act (.mutateSpatial 0 0 [.init cell]))
        (.seq (.act (.reabsorbSpatial 1 valueCellCodec))
          (.act (.endLoan 1)))))

/-- Tests for:
1. Field-wise joins apply to aggregates without a field `0` and visit every
   field index below `sizeBound`, including indices after a gap,
2. Borrowing or passing as a mutable call argument a local that was never
   written fails,
3. Values that call summaries write back or that spatial cells reabsorb must
   not introduce new unique or forged handles, while handle-free values are
   still accepted,
4. By-value entry parameters cannot carry handles, and `evalFnValue` cannot
   return one. -/
theorem field_join_uninit_local_and_handle_tests :
    -- 1. Gap-aware field-wise join:
    zipOrKeepSameRef gapStdValAlg (.symBool true)
      (.pair (.nat 1) (.nat 7)) (.pair (.nat 1) (.nat 8)) =
      .pair (.choice (.symBool true) (.nat 1) (.nat 1))
        (.choice (.symBool true) (.nat 7) (.nat 8)) ∧
    -- 2. Missing locals:
    evalFnValue stdValAlg [⟨.byVal, .nat 1⟩]
      (.act (.borrow 2 .shared (.localSub 1 []))) (.constVal .unit) = .fail ∧
    evalFnValue stdValAlg [⟨.byVal, .nat 1⟩]
      (.act (.call 1 (writebackSummary (.nat 2)) [] [.localSub 1 []]))
      (.constVal .unit) = .fail ∧
    evalFnValue stdValAlg [⟨.byVal, .nat 1⟩]
      (.act (.assign (.localSub 1 [0]) (.constVal (.nat 2))))
      (.constVal .unit) = .fail ∧
    -- 3. Writeback and reabsorb values:
    evalFnValue stdValAlg [⟨.mutRef 0 [], .nat 5⟩, ⟨.byVal, .nat 1⟩]
      (.act (.call 2 (writebackSummary (.refVal 0 []))
        [] [.localSub 1 []]))
      (.constVal .unit) = .fail ∧
    evalFnValue stdValAlg [⟨.mutRef 0 [], .nat 5⟩, ⟨.byVal, .nat 1⟩]
      (.act (.call 2 (writebackSummary (.nat 2)) [] [.localSub 1 []]))
      (.use (.localSub 1 [])) = .ok ⟨.nat 2, [.nat 5]⟩ ∧
    evalFnValue stdValAlg [⟨.mutRef 0 [], .nat 5⟩]
      (spatialOverwritePlan (.refVal 7 [])) (.constVal .unit) = .fail ∧
    evalFnValue stdValAlg [⟨.mutRef 0 [], .nat 5⟩]
      (spatialOverwritePlan (.nat 9)) (.constVal .unit) =
      .ok ⟨.unit, [.nat 9]⟩ ∧
    -- 4. No handles through by-value entry parameters or value returns:
    initFnState stdValAlg [⟨.mutRef 0 [], .nat 5⟩, ⟨.byVal, .refVal 0 []⟩] =
      .fail ∧
    evalFnValue stdValAlg [⟨.mutRef 0 [], .nat 5⟩] .skip
      (.use (.localSub 0 [])) = .fail :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Tests for writeback and region-group ownership:
1. Ending a mutable loan fails while another live loan unconditionally
   targets an overlapping place,
2. A region group's children must belong to the same call and have a single
   parent, and a hand-built state in which two active groups share a child
   cannot end either of them, and
3. An explicit join pair renames a loan even when the renamed branch still
   holds a dead handle to the target loan ID: the ended loan that the handle
   names moves to a fresh ID (`3`), and the handle moves with it. -/
theorem writeback_overlap_region_child_and_stale_join_tests :
    -- 1. Overlapping live loan at writeback:
    endLoanInState stdValAlg 0
      ⟨[⟨.pair (.nat 1) (.nat 2), .mutJoined [0] [1]⟩],
       [⟨0, .activeMut, ⟨.pair (.nat 7) (.nat 8), .unborrowed⟩,
         .direct (.localReg 0) []⟩,
        ⟨1, .activeShared, ⟨.nat 1, .unborrowed⟩,
         .direct (.localReg 0) [0]⟩], [], [], [], 0⟩ = .fail ∧
    (match endLoanInState stdValAlg 0
        ⟨[⟨.pair (.nat 1) (.nat 2), .mutLocked 0⟩],
         [⟨0, .activeMut, ⟨.pair (.nat 7) (.nat 8), .unborrowed⟩,
           .direct (.localReg 0) []⟩], [], [], [], 0⟩ with
     | .ok st => st.locals.map (fun c => c.val) = [.pair (.nat 7) (.nat 8)]
     | .fail => False) ∧
    -- 2. Region-group parentage:
    planStepFails []
      (.act (.callMultiRegion []
        [ bareRegionSpec 0 [2], bareRegionSpec 1 [2]
        , bareRegionSpec 2 [] ])) = true ∧
    planStepFails []
      (.act (.callMultiRegion [] [bareRegionSpec 0 [5]])) = true ∧
    planStepFails []
      (.act (.callMultiRegion []
        [bareRegionSpec 0 [2], bareRegionSpec 2 []])) = false ∧
    endRegionGroupInState stdValAlg 2
      ⟨[], [], [⟨1, false, 0, [], [], [], fun _ _ => some ([], [])⟩,
              ⟨2, true, 1, [], [], [1], fun _ _ => some ([], [])⟩,
              ⟨3, true, 2, [], [], [1], fun _ _ => some ([], [])⟩],
       [(1, .nat 5)], [], 0⟩ = .fail ∧
    -- 3. A dead handle to the target ID moves with its ended loan:
    (let e0 : LoanEntry StdVal :=
       ⟨0, .activeMut, ⟨.nat 0, .unborrowed⟩, .rootParam 0⟩
     let st1 : SymState StdVal :=
       ⟨[⟨.nat 0, .mutLocked 1⟩],
        [e0, ⟨1, .activeMut, ⟨.nat 1, .unborrowed⟩, .direct (.localReg 0) []⟩,
         ⟨2, .ended, ⟨.nat 0, .unborrowed⟩, .direct (.localReg 0) []⟩],
        [], [], [], 0⟩
     let st2 (stale : StdVal) : SymState StdVal :=
       ⟨[⟨.nat 0, .mutLocked 2⟩, ⟨stale, .unborrowed⟩],
        [e0, ⟨1, .ended, ⟨.nat 0, .unborrowed⟩, .direct (.localReg 0) []⟩,
         ⟨2, .activeMut, ⟨.nat 1, .unborrowed⟩, .direct (.localReg 0) []⟩],
        [], [], [], 0⟩
     (match applyJoinPairs stdValAlg [(1, 2)] st1 (st2 (.refVal 1 [])) with
      | some st2' =>
        st2'.locals.map (fun c => c.val) = [.nat 0, .refVal 3 []] ∧
        (findLoan 1 st2'.loans).map (fun e => e.phase.isActive) = some true ∧
        (findLoan 3 st2'.loans).map (fun e => e.phase.isEnded) = some true
      | none => False) ∧
     (match applyJoinPairs stdValAlg [(1, 2)] st1 (st2 (.nat 3)) with
      | some _ => True
      | none => False)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, ⟨⟨rfl, rfl, rfl⟩, trivial⟩⟩

/-! ### Writeback Checks, Value Returns, and Explicit Joins -/

/-- Output-free region group `gid` over `input` whose backward function writes
`out` back to its single input and deposits nothing. -/
@[expose] def writeRegionSpec (gid : RegionGroupId) (input : PlaceExpr)
    (outs : List StdVal) : RegionGroupSpec StdVal where
  groupId := gid
  requiredChildren := []
  inputPlaces := [input]
  outDsts := []
  fwdOuts := fun _ _ => some []
  backFn := fun _ _ _ _ => some (outs, [])

/-- Tests for `LoanGraph` writeback checks:
1. A writeback is rejected when another live loan's target selects the place
   through a concrete `.choice`, or an active region group locks it,
2. Region writebacks may swap unique handles between their targets but not
   duplicate them, and
3. Handles hidden inside a symbolic choice's arms count as copies. -/
theorem writeback_choice_lock_and_handle_tests :
    -- 1. Concrete-choice target and region-group lock:
    (let x0 : PlaceCell StdVal :=
       ⟨.pair (.pair (.nat 1) (.nat 2)) (.nat 3),
        .split [([0], .mutLocked 1), ([0, 1], .mutLocked 2)]⟩
     let loan1 : LoanEntry StdVal :=
       ⟨1, .activeMut, ⟨.pair (.nat 5) (.nat 6), .unborrowed⟩,
        .direct (.localReg 0) [0]⟩
     let loan2 (t : BackTarget StdVal) : LoanEntry StdVal :=
       ⟨2, .activeMut, ⟨.nat 77, .unborrowed⟩, t⟩
     endLoanInState stdValAlg 1
       ⟨[x0, ⟨.nat 0, .unborrowed⟩],
        [loan1, loan2 (.choice (.bool true) (.direct (.localReg 0) [0, 1])
          (.direct (.localReg 1) []))], [], [], [], 0⟩ = .fail ∧
     (match endLoanInState stdValAlg 1
         ⟨[x0, ⟨.nat 0, .unborrowed⟩],
          [loan1, loan2 (.choice (.bool false) (.direct (.localReg 0) [0, 1])
            (.direct (.localReg 1) []))], [], [], [], 0⟩ with
      | .ok _ => True
      | .fail => False) ∧
     endLoanInState stdValAlg 1
       ⟨[⟨.pair (.pair (.nat 1) (.nat 2)) (.nat 3),
          .split [([0], .mutLocked 1), ([0, 1], .mutLocked 9)]⟩],
        [loan1],
        [⟨0, true, 9, [(.localReg 0, [0, 1])], [], [],
          fun _ _ => some ([.nat 0], [])⟩], [], [], 0⟩ = .fail) ∧
    -- 2. Swapping two `&mut` handles through a region writeback:
    (let st (outs : List StdVal) : SymState StdVal :=
       ⟨[⟨.refVal 3 [], .mutLocked 5⟩, ⟨.refVal 4 [], .mutLocked 5⟩],
        [⟨3, .activeMut, ⟨.nat 30, .unborrowed⟩, .rootParam 3⟩,
         ⟨4, .activeMut, ⟨.nat 40, .unborrowed⟩, .rootParam 4⟩,
         ⟨5, .ended, ⟨.unit, .unborrowed⟩, .regionOut 0 0⟩],
        [⟨0, true, 5, [(.localReg 0, []), (.localReg 1, [])], [], [],
          fun _ _ => some (outs, [])⟩], [], [], 0⟩
     (match endRegionGroupInState stdValAlg 0
         (st [.refVal 4 [], .refVal 3 []]) with
      | .ok st' =>
        st'.locals.map (fun c => c.val) = [.refVal 4 [], .refVal 3 []]
      | .fail => False) ∧
     endRegionGroupInState stdValAlg 0 (st [.refVal 3 [], .refVal 3 []]) =
       .fail) ∧
    -- 3. Choice arms are scanned for handles:
    copyableVal stdValAlg [⟨0, .activeMut, ⟨.nat 0, .unborrowed⟩, .rootParam 0⟩]
      (zipStdVal (.symBool true) (.refVal 0 []) (.refVal 0 [])) = false :=
  ⟨⟨rfl, trivial, rfl⟩, ⟨rfl, rfl⟩, rfl⟩

/-- Tests for value returns:
1. A handle hidden in one arm of a joined return value is rejected, whether
   it comes from an early return or from a joined local,
2. Final `&mut` parameter values may not carry handles,
3. Reference-parameter pointee values may not carry handles, and
4. A CFG applies the same check as `evalFnValue` to the value of a `.ret`
   terminator, and to a value merged with an early return that an earlier
   block left pending on one side of a symbolic branch, whether the block
   ends in a `.goto` or in a branch on a symbolic condition
   (`runBlockCfg_stepBasicBlock_handleFree` states the general result). -/
theorem value_return_tests :
    -- 1. Hidden handles in joined returns:
    evalFnValue stdValAlg [⟨.byVal, .symBool true⟩, ⟨.mutRef 0 [], .nat 5⟩]
      (.branch (.use (.localSub 0 []))
        (.earlyReturn [] [] (.use (.localSub 1 []))) .skip)
      (.constVal .unit) = .fail ∧
    evalFnValue stdValAlg [⟨.byVal, .symBool true⟩, ⟨.sharedRef 0 [], .nat 5⟩]
      (.branch (.use (.localSub 0 []))
        (.act (.assign (.localSub 2 []) (.use (.localSub 1 []))))
        (.act (.assign (.localSub 2 []) (.constVal (.nat 3)))))
      (.use (.localSub 2 [])) = .fail ∧
    -- 2. `*p = &local` leaks a callee handle through `mutFinals`:
    evalFnValue stdValAlg [⟨.mutRef 0 [], .nat 5⟩, ⟨.byVal, .nat 7⟩]
      (.seq (.act (.borrow 2 .shared (.localSub 1 [])))
        (.seq (.act (.assign (.derefSub 0 []) (.use (.localSub 2 []))))
          (.act (.endLoan 1))))
      (.constVal .unit) = .fail ∧
    -- 3. Handles in reference-parameter pointees:
    initFnState stdValAlg
      [⟨.mutRef 0 [], .refVal 1 []⟩, ⟨.sharedRef 1 [], .nat 5⟩] = .fail ∧
    -- 4. CFG value returns:
    (match initFnState stdValAlg [⟨.mutRef 0 [], .nat 5⟩] with
     | .ok st0 =>
       runBlockCfg
         (stepBasicBlock stdValAlg [⟨.skip, .ret (.use (.localSub 0 []))⟩])
         0 st0 1 = .fault
     | .fail => False) ∧
    (let params : List (ParamInput StdVal) :=
       [⟨.byVal, .symBool true⟩, ⟨.sharedRef 0 [], .nat 5⟩]
     -- Returns the shared parameter's handle if the condition holds.
     let body : FlowPlan StdVal :=
       .branch (.use (.localSub 0 []))
         (.earlyReturn [] [] (.use (.localSub 1 []))) .skip
     let exit : BasicBlock StdVal := ⟨.skip, .ret (.constVal (.nat 0))⟩
     (match initFnState stdValAlg params with
      | .ok st0 =>
        runBlockCfg (stepBasicBlock stdValAlg [⟨body, .goto 1⟩, exit])
          0 st0 2 = .fault ∧
        runBlockCfg
          (stepBasicBlock stdValAlg
            [⟨body, .branch (.use (.localSub 0 [])) 1 2⟩, exit, exit])
          0 st0 2 = .fault
      | .fail => False) ∧
     evalFnValue stdValAlg params body (.constVal (.nat 0)) = .fail) :=
  ⟨rfl, rfl, rfl, rfl, rfl, ⟨⟨rfl, rfl⟩, rfl⟩⟩

/-- Explicit join over arms that allocate different numbers of loans: the
false arm uses a scratch shared borrow (loan `2`) before its mutable borrow
(loan `3`), which the pair `(2, 3)` renames to the true arm's loan `2`. -/
@[expose] def unevenExplicitJoinPlan : FlowPlan StdVal :=
  .seq
    (.branchExplicitJoin (.use (.localSub 0 []))
      (.act (.borrow 3 .mutBorrow (.derefSub 1 [])))
      (.seq
        (.act (.borrow 3 .shared (.localSub 0 [])))
        (.seq
          (.act (.endLoan 2))
          (.act (.borrow 3 .mutBorrow (.derefSub 2 [])))))
      [(2, 3)])
    (.seq
      (.act (.assign (.derefSub 3 []) (.constVal (.nat 50))))
      (.act (.endLoan 2)))

/-- Tests for explicit joins and branch-local region
groups:
1. Explicit join pairs rename the false arm's loans when the condition is
   concrete `false`, when the arms allocate different numbers of loans, and
   when one arm returns,
2. Different branch-local region groups at the same table position join, and
3. Reinstalling a group fails while its earlier deposits are unconsumed. -/
theorem explicit_join_and_branch_local_region_tests :
    -- 1. Explicit joins:
    evalFnValue stdValAlg
      [⟨.byVal, .bool false⟩, ⟨.mutRef 0 [], .nat 1⟩, ⟨.mutRef 1 [], .nat 2⟩]
      explicitJoinRemapLoanIdsPlan (.constVal .unit) =
      .ok ⟨.unit, [.nat 1, .nat 50]⟩ ∧
    evalFnValue stdValAlg
      [⟨.byVal, .symBool true⟩, ⟨.mutRef 0 [], .nat 1⟩,
       ⟨.mutRef 1 [], .nat 2⟩]
      unevenExplicitJoinPlan (.constVal .unit) =
      .ok ⟨.unit, [zipStdVal (.symBool true) (.nat 50) (.nat 1),
                   zipStdVal (.symBool true) (.nat 2) (.nat 50)]⟩ ∧
    evalFnValue stdValAlg [⟨.byVal, .symBool true⟩]
      (.branchExplicitJoin (.use (.localSub 0 []))
        (.earlyReturn [] [] (.constVal (.nat 1))) .skip [(0, 0)])
      (.constVal (.nat 2)) =
      .ok ⟨zipStdVal (.symBool true) (.nat 1) (.nat 2), []⟩ ∧
    -- 2. Distinct branch-local groups:
    evalFnValue stdValAlg [⟨.byVal, .symBool true⟩, ⟨.mutRef 0 [], .nat 5⟩]
      (.branch (.use (.localSub 0 []))
        (.seq
          (.act (.callMultiRegion []
            [writeRegionSpec 0 (.derefSub 1 []) [.nat 6]]))
          (.act (.endRegionGroup 0)))
        (.seq
          (.act (.callMultiRegion []
            [writeRegionSpec 1 (.derefSub 1 []) [.nat 7]]))
          (.act (.endRegionGroup 1))))
      (.constVal .unit) =
      .ok ⟨.unit, [zipStdVal (.symBool true) (.nat 6) (.nat 7)]⟩ ∧
    -- 3. Leftover deposits block reinstalling their group:
    planStepFails [⟨.mutRef 0 [], .nat 5⟩]
      (.seq
        (.act (.callMultiRegion []
          [countingRegionSpec 0 [] (.derefSub 0 [])]))
        (.seq (.act (.endRegionGroup 0))
          (.act (.callMultiRegion []
            [countingRegionSpec 0 [] (.derefSub 0 []) []])))) = true ∧
    planStepFails [⟨.mutRef 0 [], .nat 5⟩]
      (.seq
        (.act (.callMultiRegion []
          [countingRegionSpec 0 [] (.derefSub 0 []) []]))
        (.seq (.act (.endRegionGroup 0))
          (.act (.callMultiRegion []
            [countingRegionSpec 0 [] (.derefSub 0 []) []])))) = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Choice Writebacks and Uneven Explicit Joins -/

/-- `let a = &mut x; let b = &mut y; let r = if c { &mut a } else { &mut b };`
followed by the end of `r`, `b`, and `a`: the reborrow `r` writes the
unchanged handle back to `a` (or `b`) through a symbolic `.choice` target. -/
@[expose] def choiceOverHandlesPlan : FlowPlan StdVal :=
  .seq (.act (.borrow 3 .mutBorrow (.localSub 1 [])))
    (.seq (.act (.borrow 4 .mutBorrow (.localSub 2 [])))
      (.seq
        (.branch (.use (.localSub 0 []))
          (.act (.borrow 5 .mutBorrow (.localSub 3 [])))
          (.act (.borrow 5 .mutBorrow (.localSub 4 []))))
        (.seq (.act (.endLoan 2))
          (.seq (.act (.endLoan 1)) (.act (.endLoan 0))))))

/-- Explicit join where the true arm takes a scratch shared borrow (loan `1`)
before its mutable borrow (loan `2`), and the false arm only takes the mutable
borrow (loan `1`); the pair `(2, 1)` renames the false arm's loan. -/
@[expose] def trueArmScratchPlan : FlowPlan StdVal :=
  .seq
    (.branchExplicitJoin (.use (.localSub 0 []))
      (.seq (.act (.borrow 3 .shared (.localSub 2 [])))
        (.seq (.act (.endLoan 1))
          (.act (.borrow 3 .mutBorrow (.derefSub 1 [])))))
      (.act (.borrow 3 .mutBorrow (.derefSub 1 [])))
      [(2, 1)])
    (.act (.endLoan 2))

/-- `true` iff `endLoanInState` succeeds on `st`. -/
@[expose] def endLoanOk (lid : LoanId) (st : SymState StdVal) : Bool :=
  match endLoanInState stdValAlg lid st with
  | .ok _ => true
  | .fail => false

/-- Tests for choice writebacks and uneven explicit joins:
1. Writing an unchanged `&mut` handle back through a symbolic `.choice` target
   counts the handle once, not once per arm,
2. Explicit join pairs work when the true arm allocates more loans than the
   false arm, for symbolic and concrete-`false` conditions, and
3. A writeback is rejected when another live loan's symbolic `.choice` target
   overlaps the place in a branch in which the write happens, while two loans
   with swapped arms (as a branch join produces) still end. -/
theorem choice_handle_and_explicit_join_padding_tests :
    -- 1. Choice over handles:
    evalFnValue stdValAlg
      [⟨.byVal, .symBool true⟩, ⟨.byVal, .nat 1⟩, ⟨.byVal, .nat 2⟩]
      choiceOverHandlesPlan (.constVal .unit) = .ok ⟨.unit, []⟩ ∧
    -- 2. True arm allocates more loans:
    evalFnValue stdValAlg
      [⟨.byVal, .symBool true⟩, ⟨.mutRef 0 [], .nat 5⟩, ⟨.byVal, .nat 7⟩]
      trueArmScratchPlan (.constVal .unit) =
      .ok ⟨.unit, [zipStdVal (.symBool true) (.nat 5) (.nat 5)]⟩ ∧
    evalFnValue stdValAlg
      [⟨.byVal, .bool false⟩, ⟨.mutRef 0 [], .nat 5⟩, ⟨.byVal, .nat 7⟩]
      trueArmScratchPlan (.constVal .unit) = .ok ⟨.unit, [.nat 5]⟩ ∧
    -- 3. Symbolic-choice overlap:
    (let x0 : PlaceCell StdVal :=
       ⟨.pair (.pair (.nat 1) (.nat 2)) (.nat 3),
        .split [([0], .mutLocked 1), ([0, 1], .mutLocked 2)]⟩
     let loan1 : LoanEntry StdVal :=
       ⟨1, .activeMut, ⟨.pair (.nat 5) (.nat 6), .unborrowed⟩,
        .direct (.localReg 0) [0]⟩
     let loan2 (t : BackTarget StdVal) : LoanEntry StdVal :=
       ⟨2, .activeMut, ⟨.nat 77, .unborrowed⟩, t⟩
     endLoanOk 1
       ⟨[x0], [loan1, loan2 (.choice (.symBool true)
          (.direct (.localReg 0) [0, 1]) (.direct (.localReg 0) [0, 1]))],
        [], [], [], 0⟩ = false) ∧
    (let c : StdVal := .symBool true
     let st : SymState StdVal :=
       ⟨[⟨.nat 1, .mutJoined [0, 1] []⟩, ⟨.nat 2, .mutJoined [0, 1] []⟩],
        [⟨0, .activeMut, ⟨zipStdVal c (.nat 10) (.nat 20), .unborrowed⟩,
          .choice c (.direct (.localReg 0) []) (.direct (.localReg 1) [])⟩,
         ⟨1, .activeMut, ⟨zipStdVal c (.nat 2) (.nat 1), .unborrowed⟩,
          .choice c (.direct (.localReg 1) []) (.direct (.localReg 0) [])⟩],
        [], [], [], 0⟩
     endLoanOk 0 st = true) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ### Branch-Wise Handle Accounting and Correlated Writebacks -/

/-- Region group `0` over locals `0` and `1`, whose callback returns `outs`.
The locals hold `zipVal c h3 h4` and `zipVal c h4 h3`, the state after
`if c {} else { mem::swap(&mut a, &mut b) }` for unique handles `h3`, `h4`:
in each branch each handle occurs once. -/
@[expose] def swappedChoiceState (outs : List StdVal) : SymState StdVal :=
  let c : StdVal := .symBool true
  ⟨[⟨zipStdVal c (.refVal 3 []) (.refVal 4 []), .mutLocked 5⟩,
    ⟨zipStdVal c (.refVal 4 []) (.refVal 3 []), .mutLocked 5⟩],
   [⟨3, .activeMut, ⟨.nat 30, .unborrowed⟩, .rootParam 3⟩,
    ⟨4, .activeMut, ⟨.nat 40, .unborrowed⟩, .rootParam 4⟩,
    ⟨5, .ended, ⟨.unit, .unborrowed⟩, .regionOut 0 0⟩],
   [⟨0, true, 5, [(.localReg 0, []), (.localReg 1, [])], [], [],
     fun _ _ => some (outs, [])⟩], [], [], 0⟩

/-- `true` iff ending region group `0` succeeds on `st`. -/
@[expose] def endGroup0Ok (st : SymState StdVal) : Bool :=
  match endRegionGroupInState stdValAlg 0 st with
  | .ok _ => true
  | .fail => false

/-- Local `0` is split between loan `1` at `[0]` and loan `2` at `[0, 1]`, and
locals `1` and `2` are borrowed by loans `1` and `2`; `t1` and `t2` are the
loans' targets. -/
@[expose] def correlatedOverlapState (t1 t2 : BackTarget LensTestVal) :
    SymState LensTestVal :=
  { locals := [⟨.node (.node (.atom 1) (.atom 2)) (.atom 3),
                .split [([0], .mutLocked 1), ([0, 1], .mutLocked 2)]⟩,
               ⟨.atom 9, .mutLocked 1⟩, ⟨.atom 8, .mutLocked 2⟩]
    loans := [⟨1, .activeMut, ⟨.node (.atom 50) (.atom 60), .unborrowed⟩, t1⟩,
              ⟨2, .activeMut, ⟨.atom 77, .unborrowed⟩, t2⟩]
    regionGroups := []
    regionDeposits := []
    spatial := []
    nextSpatialTag := 0 }

/-- `true` iff ending loan `1` succeeds on `st`. -/
@[expose] def endLoan1Ok (st : SymState LensTestVal) : Bool :=
  match endLoanInState lensTestValAlg 1 st with
  | .ok _ => true
  | .fail => false

/-- Tests that handle accounting compares counts branch by branch:
1. A writeback over the conditionally swapped pair cannot write `h3` to both
   places, although each place holds `h3` in some branch; neither can a
   single place holding `zipVal c h3 h4` take `h3`,
2. Writing the pair back unchanged, swapped, or as `[h3, h4]` keeps one of
   each handle per branch and succeeds, and an unchanged handle may still be
   written back as `zipVal c h0 h0`, and
3. Under a guard that `sameCond` cannot identify, the arms count as in any
   branch: the duplicate is still rejected, and so (conservatively) is the
   unchanged write, and
4. Distinct identifiable guards are enumerated independently: writing
   `zipVal c h3 h4` and `zipVal d h4 h3` over `[h3, h4]` duplicates a handle
   when `c` and `d` differ, so it is rejected, while the same write under one
   guard `c` is a conditional swap and succeeds. -/
theorem branchwise_handle_accounting_tests :
    let c : StdVal := .symBool true
    let d : StdVal := .symBool false
    let g : StdVal := .pair (.symBool true) (.nat 0)
    let loans := (swappedChoiceState []).loans
    -- 1. Duplicates are rejected:
    endGroup0Ok
      (swappedChoiceState [.refVal 3 [], .refVal 3 []]) = false ∧
    replaceableVal stdValAlg loans
      (zipStdVal c (.refVal 3 []) (.refVal 4 [])) (.refVal 3 []) = false ∧
    -- 2. Permutations within each branch succeed:
    endGroup0Ok
      (swappedChoiceState
        [zipStdVal c (.refVal 3 []) (.refVal 4 []),
         zipStdVal c (.refVal 4 []) (.refVal 3 [])]) = true ∧
    endGroup0Ok
      (swappedChoiceState
        [zipStdVal c (.refVal 4 []) (.refVal 3 []),
         zipStdVal c (.refVal 3 []) (.refVal 4 [])]) = true ∧
    endGroup0Ok
      (swappedChoiceState [.refVal 3 [], .refVal 4 []]) = true ∧
    replaceableVal stdValAlg loans
      (.refVal 3 []) (zipStdVal c (.refVal 3 []) (.refVal 3 [])) = true ∧
    -- 3. Unidentified guards:
    replaceableVal stdValAlg loans
      (zipStdVal g (.refVal 3 []) (.refVal 4 [])) (.refVal 3 []) = false ∧
    replaceableVal stdValAlg loans
      (zipStdVal g (.refVal 3 []) (.refVal 4 []))
      (zipStdVal g (.refVal 3 []) (.refVal 4 [])) = false ∧
    -- 4. Distinct guards:
    replaceableVals stdValAlg loans [.refVal 3 [], .refVal 4 []]
      [zipStdVal c (.refVal 3 []) (.refVal 4 []),
       zipStdVal d (.refVal 4 []) (.refVal 3 [])] = false ∧
    replaceableVals stdValAlg loans [.refVal 3 [], .refVal 4 []]
      [zipStdVal c (.refVal 3 []) (.refVal 4 []),
       zipStdVal c (.refVal 4 []) (.refVal 3 [])] = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `true` iff ending loan `a` and then loan `b` succeeds on `st`. -/
@[expose] def endLoansInOrderOk (a b : LoanId) (st : SymState LensTestVal) : Bool :=
  match endLoanInState lensTestValAlg a st with
  | .ok st1 =>
    match endLoanInState lensTestValAlg b st1 with
    | .ok _ => true
    | .fail => false
  | .fail => false

/-- Tests that a conditional writeback follows other live loans' choices on the
same guard in the same branch:
1. Loan `1` writes `x0[0]` when `symL` holds, and loan `2` observes `x0[0, 1]`
   in that same branch, so ending loan `1` is rejected, as it is when loan
   `1`'s target is unconditional,
2. With loan `2`'s arms swapped, the two loans never overlap in one branch,
   and because `evalBackVal` preserves aggregate fields via `zipOrKeepSameRef`
   and `projectBranchOrFields`, both loans end in either order,
3. If loan `2` branches on a different guard, some branch may combine the
   overlapping arms, so ending loan `1` is rejected, and
4. The same holds when loan `1` writes `x0[0]` through a `.lensCall` leaf
   inside the symbolic choice. -/
theorem conditional_writeback_correlation_tests :
    let symL : LensTestVal := .node (.atom 0) (.atom 0)
    let symM : LensTestVal := .node (.atom 0) (.atom 1)
    let x0 (p : SubPath) : BackTarget LensTestVal := .direct (.localReg 0) p
    let x1 : BackTarget LensTestVal := .direct (.localReg 1) []
    let x2 : BackTarget LensTestVal := .direct (.localReg 2) []
    let lens : BackTarget LensTestVal :=
      .lensCall [(.localReg 0, [0])] (fun v => some [v])
    -- 1. Same-branch overlap:
    endLoan1Ok
      (correlatedOverlapState (.choice symL (x0 [0]) x1)
        (.choice symL (x0 [0, 1]) x2)) = false ∧
    endLoan1Ok
      (correlatedOverlapState (x0 [0]) (.choice symL (x0 [0, 1]) x2)) =
      false ∧
    -- 2. Swapped arms:
    endLoan1Ok
      (correlatedOverlapState (.choice symL (x0 [0]) x1)
        (.choice symL x2 (x0 [0, 1]))) = true ∧
    endLoansInOrderOk 2 1
      (correlatedOverlapState (.choice symL (x0 [0]) x1)
        (.choice symL x2 (x0 [0, 1]))) = true ∧
    endLoansInOrderOk 1 2
      (correlatedOverlapState (.choice symL (x0 [0]) x1)
        (.choice symL x2 (x0 [0, 1]))) = true ∧
    -- 3. Independent guards:
    endLoan1Ok
      (correlatedOverlapState (.choice symL (x0 [0]) x1)
        (.choice symM (x0 [0, 1]) x2)) = false ∧
    -- 4. A `.lensCall` leaf under the choice:
    endLoan1Ok
      (correlatedOverlapState (.choice symL lens x1)
        (.choice symL (x0 [0, 1]) x2)) = false ∧
    endLoan1Ok
      (correlatedOverlapState (.choice symL lens x1)
        (.choice symL x2 (x0 [0, 1]))) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Handle renaming that retargets every handle to `t`, not only those to the
renamed loan. -/
@[expose] def retargetAllRemap (_ t : LoanId) (v : StdVal) : StdVal :=
  match v with
  | ⟨_, .refVal _ p⟩ => .refVal t p
  | other => other

/-- Handle renaming that also changes non-handle data: it adds `1000` to every
top-level number. -/
@[expose] def bumpNatRemap (oldLid newLid : LoanId) (v : StdVal) : StdVal :=
  match v with
  | ⟨_, .nat n⟩ => .nat (n + 1000)
  | other => remapStdVal oldLid newLid other

/-- The `ValAlgebra` laws for `remapRefInVal` exclude unfaithful renamings, so
no algebra can use one: `retargetAllRemap` breaks `decodeRef_remapRefInVal`
(renaming loan `2` to `3` must keep a handle to loan `1`), and `bumpNatRemap`
breaks `remapRefInVal_leaf` (a number has no handle, field, or arm, so it
must not change). -/
theorem unfaithful_remaps_break_laws :
    (¬ ∀ (oldLid newLid : LoanId) (v : StdVal),
      stdDecodeRef (retargetAllRemap oldLid newLid v) =
        (stdDecodeRef v).map
          (fun r => (if r.1 == oldLid then newLid else r.1, r.2))) ∧
    (¬ ∀ (oldLid newLid : LoanId) (v : StdVal),
      stdDecodeRef v = none → (∀ f, stdValGetField f v = none) →
      stdBranchSplit v = none → bumpNatRemap oldLid newLid v = v) :=
  ⟨(fun h => nomatch h 2 3 (.refVal 1 [])),
   (fun h =>
     nomatch h 2 3 (.nat 5) rfl
       (fun f =>
         match f with
         | 0 => rfl
         | 1 => rfl
         | _ + 2 => rfl)
       rfl)⟩

/-- An explicit join renaming the false arm's loan `3` to `2`, after which the
plan writes through both the renamed loan and the second root parameter. -/
@[expose] def explicitJoinRenamePlan : FlowPlan StdVal :=
  .seq
    (.branchExplicitJoin (.use (.localSub 0 []))
      (.act (.borrow 3 .mutBorrow (.derefSub 2 [])))
      (.seq
        (.act (.borrow 3 .shared (.localSub 0 [])))
        (.seq
          (.act (.endLoan 2))
          (.act (.borrow 3 .mutBorrow (.derefSub 2 [])))))
      [(2, 3)])
    (.seq (.act (.assign (.derefSub 3 []) (.constVal (.nat 50))))
      (.seq (.act (.assign (.derefSub 1 []) (.constVal (.nat 77))))
        (.act (.endLoan 2))))

/-- Renaming during an explicit join renames exactly the renamed loan's
handles: with a concrete `false` condition, the false arm's loan `3` becomes
loan `2`, and writes through it and through the second root parameter reach
the right parameters. -/
theorem explicit_join_rename_tests :
    let params : List (ParamInput StdVal) :=
      [⟨.byVal, .bool false⟩, ⟨.mutRef 0 [], .nat 1⟩, ⟨.mutRef 1 [], .nat 2⟩]
    evalFnValue stdValAlg params explicitJoinRenamePlan (.constVal .unit) =
      .ok ⟨.unit, [.nat 77, .nat 50]⟩ :=
  rfl

/-- Explicit join whose arms reborrow `*x` and `*y` in opposite orders: the
true arm takes loan `2` for `x` and loan `3` for `y`, and the false arm loan
`2` for `y` and loan `3` for `x`. The pairs `[(2, 3), (3, 2)]` exchange the
false arm's IDs; afterwards local `3` reborrows `x` and local `4` reborrows
`y` in both arms. -/
@[expose] def swappedLoanIdsJoinPlan : FlowPlan StdVal :=
  .seq
    (.branchExplicitJoin (.use (.localSub 0 []))
      (.seq (.act (.borrow 3 .mutBorrow (.derefSub 1 [])))
        (.act (.borrow 4 .mutBorrow (.derefSub 2 []))))
      (.seq (.act (.assign (.localSub 3 []) (.constVal (.nat 0))))
        (.seq (.act (.borrow 4 .mutBorrow (.derefSub 2 [])))
          (.act (.borrow 3 .mutBorrow (.derefSub 1 [])))))
      [(2, 3), (3, 2)])
    (.seq (.act (.assign (.derefSub 3 []) (.constVal (.nat 10))))
      (.seq (.act (.assign (.derefSub 4 []) (.constVal (.nat 20))))
        (.seq (.act (.endLoan 3)) (.act (.endLoan 2)))))

/-- Explicit join where the false arm takes a scratch shared borrow (loan `2`)
whose dead handle stays in local `3`, as in MIR before `StorageDead`, and then
the reborrow of `*x` (loan `3`) that the pair `(2, 3)` renames to the true
arm's loan `2`. -/
@[expose] def deadRefExplicitJoinPlan : FlowPlan StdVal :=
  .seq (.act (.assign (.localSub 3 []) (.constVal (.nat 0))))
    (.seq
      (.branchExplicitJoin (.use (.localSub 0 []))
        (.act (.borrow 4 .mutBorrow (.derefSub 1 [])))
        (.seq (.act (.borrow 3 .shared (.localSub 0 [])))
          (.seq (.act (.endLoan 2))
            (.act (.borrow 4 .mutBorrow (.derefSub 1 [])))))
        [(2, 3)])
      (.seq (.act (.assign (.derefSub 4 []) (.constVal (.nat 50))))
        (.act (.endLoan 2))))

/-- The state after an arm that reborrowed local `0` and then local `1`
(`swapped = false`: loan `2` borrows local `0` and loan `3` local `1`), or the
same locals in the opposite order (`swapped = true`). Locals `2` and `3` hold
the handles to the borrows of locals `0` and `1`. -/
@[expose] def twoReborrowsState (swapped : Bool) : SymState StdVal :=
  let l0 : LoanId := if swapped then 3 else 2
  let l1 : LoanId := if swapped then 2 else 3
  ⟨[⟨.nat 1, .mutLocked l0⟩, ⟨.nat 2, .mutLocked l1⟩,
    ⟨.refVal l0 [], .unborrowed⟩, ⟨.refVal l1 [], .unborrowed⟩],
   [⟨0, .ended, ⟨.unit, .unborrowed⟩, .direct (.localReg 0) []⟩,
    ⟨1, .ended, ⟨.unit, .unborrowed⟩, .direct (.localReg 0) []⟩,
    ⟨2, .activeMut, ⟨.nat 1, .unborrowed⟩,
     .direct (.localReg (if swapped then 1 else 0)) []⟩,
    ⟨3, .activeMut, ⟨.nat 2, .unborrowed⟩,
     .direct (.localReg (if swapped then 0 else 1)) []⟩],
   [], [], [], 0⟩

/-- Explicit join pairs may exchange two loan IDs (`relabelJoinLoans`): the
pairs `[(2, 3), (3, 2)]` turn the swapped state into the unswapped one, both
within one arm (`applySelfJoinPairs`) and against the other arm
(`applyJoinPairs`). The loan that moves out of the way first takes the fresh
ID `4`, which remains as an ended loan. -/
theorem explicit_join_swapped_loan_ids_tests :
    let renamedOk (o : Option (SymState StdVal)) : Prop :=
      match o with
      | some st =>
        st.locals.map (fun c => c.val) =
          [.nat 1, .nat 2, .refVal 2 [], .refVal 3 []] ∧
        st.locals.map (fun c => c.perm) =
          [.mutLocked 2, .mutLocked 3, .unborrowed, .unborrowed] ∧
        st.loans.map (fun e => (e.id, e.phase.isActive)) =
          [(0, false), (1, false), (2, true), (3, true), (4, false)]
      | none => False
    renamedOk
      (applySelfJoinPairs stdValAlg [(2, 3), (3, 2)] (twoReborrowsState true)) ∧
    renamedOk
      (applyJoinPairs stdValAlg [(2, 3), (3, 2)] (twoReborrowsState false)
        (twoReborrowsState true)) :=
  ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- `swappedLoanIdsJoinPlan` runs when only the false arm runs, so that its
loans must be renamed. -/
theorem explicit_join_swapped_loan_ids_plan_tests :
    evalFnValue stdValAlg
      [⟨.byVal, .bool false⟩, ⟨.mutRef 0 [], .nat 1⟩, ⟨.mutRef 1 [], .nat 2⟩]
      swappedLoanIdsJoinPlan (.constVal .unit) =
      .ok ⟨.unit, [.nat 10, .nat 20]⟩ :=
  rfl

/-- `deadRefExplicitJoinPlan` runs when only the false arm runs, so that its
mutable reborrow must take the ID of its dead scratch borrow. -/
theorem explicit_join_dead_ref_plan_tests :
    evalFnValue stdValAlg
      [⟨.byVal, .bool false⟩, ⟨.mutRef 0 [], .nat 1⟩, ⟨.mutRef 1 [], .nat 2⟩]
      deadRefExplicitJoinPlan (.constVal .unit) =
      .ok ⟨.unit, [.nat 50, .nat 2]⟩ :=
  rfl

/-- Test algebra that never reports two reference representations as equal
(`sameRefVal := fun _ _ => false`), modeling an algebra whose reference handles
carry extra non-decoded data so `zipOrKeepSameRef` preserves the conditional
choice instead of collapsing to the true-arm value. -/
@[expose] def opaqueRefStdValAlg : ValAlgebra StdVal :=
  { stdValAlg with
    sameRefVal := fun _ _ => false
    sameRefVal_eq := fun _ _ h => nomatch h }

/-- Regression tests for:
1. `projectBranchStdVal` and `lensTestProjectBranchVal` recursively projecting
   the selected arm when a value repeats the projected guard,
2. `stdAdd` recursing through multi-level nested `.choice` values produced by
   combining choices under distinct guards, and
3. `zipOrKeepSameRef` / `joinPlaceCells` preserving the conditional value when
   `sameRefVal` does not vouch that two reference representations are equal,
   while collapsing identical references when `sameRefVal` holds. -/
theorem recursive_projection_nested_add_and_ref_join_tests :
    let c : StdVal := .symBool true
    let d : StdVal := .symBool false
    let lc : LensTestVal := .node (.atom 0) (.atom 0)
    -- 1. Recursive arm projection in `projectBranchStdVal` and
    -- `lensTestProjectBranchVal`:
    projectBranchStdVal c true
      (.choice c (.choice c (.nat 1) (.nat 2)) (.nat 3)) = .nat 1 ∧
    projectBranchStdVal c false
      (.choice c (.nat 1) (.choice c (.nat 2) (.nat 3))) = .nat 3 ∧
    lensTestProjectBranchVal lc true
      (.choice lc (.choice lc (.atom 1) (.atom 2)) (.atom 3)) = .atom 1 ∧
    -- 2. `stdAdd` over nested `.choice` trees:
    (match stdAdd (.choice c (.nat 1) (.nat 2))
        (.choice d (.nat 10) (.nat 20)) with
     | some sum1 =>
       stdAdd sum1 (.nat 1) =
         some (.choice c
           (.choice d (.nat 12) (.nat 22))
           (.choice d (.nat 13) (.nat 23))) ∧
       stdAdd (.nat 1) sum1 =
         some (.choice c
           (.choice d (.nat 12) (.nat 22))
           (.choice d (.nat 13) (.nat 23)))
     | none => False) ∧
    -- 3. Full-reference equality check in `zipOrKeepSameRef`:
    zipOrKeepSameRef opaqueRefStdValAlg c (.refVal 0 []) (.refVal 0 []) =
      .choice c (.refVal 0 []) (.refVal 0 []) ∧
    zipOrKeepSameRef stdValAlg c (.refVal 0 []) (.refVal 0 []) =
      .refVal 0 [] ∧
    -- 4. `projectBranchOrFields` / `projectBranchValList` traverses aggregate
    -- fields, and ending a joined loan over aggregate pairs (`evalBackVal`)
    -- preserves `.pair` structure so subsequent field reads (`[0]`) succeed:
    projectBranchValList stdValAlg c true
      [.pair (.choice c (.nat 10) (.nat 20)) (.choice c (.nat 30) (.nat 40))] =
      [.pair (.nat 10) (.nat 30)] ∧
    evalFnValue stdValAlg
      [⟨.byVal, c⟩, ⟨.byVal, .pair (.nat 1) (.nat 2)⟩,
       ⟨.byVal, .pair (.nat 3) (.nat 4)⟩]
      (.seq
        (.branch (.use (.localSub 0 []))
          (.act (.borrow 3 .mutBorrow (.localSub 1 [])))
          (.act (.borrow 3 .mutBorrow (.localSub 2 []))))
        (.seq
          (.act (.endLoan 0))
          (.act (.assign (.localSub 4 []) (.use (.localSub 1 [0]))))))
      (.use (.localSub 4 [])) =
      .ok ⟨.choice c (.nat 1) (.nat 1), []⟩ ∧
    -- 5. `m3LookupCell` rejects prefix-overlapping cells at the same
    -- `(allocId, offset)` (`[]` and `[0]`), while accepting disjoint sibling
    -- sub-paths (`[0]` and `[1]`):
    m3LookupCell 0 0 []
      [ ⟨0, 0, [], 1, .activeUnique, .init (StdVal.pair (.nat 1) (.nat 2))⟩
      , ⟨0, 0, [0], 2, .activeUnique, .init (.nat 99)⟩ ] = none ∧
    m3LookupCell 0 0 [0]
      [ ⟨0, 0, [0], 1, .activeUnique, .init (StdVal.nat 1)⟩
      , ⟨0, 0, [1], 2, .activeUnique, .init (.nat 2)⟩ ] =
      some ⟨0, 0, [0], 1, .activeUnique, .init (.nat 1)⟩ :=
  ⟨rfl, rfl, rfl, ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Anneal.PureLift

end
