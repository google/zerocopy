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

/-!
## Part I: Core Borrow and Control-Flow Scenarios (`S1`–`S7`)
-/

/-- **S1 (`max_assign`)**: `if *x < y { *x = y }`. -/
@[expose] def s1MaxAssignPlan : FlowPlan StdVal :=
  .seq
    (.act (.assign (.localSub 2 [])
      (.binary stdLtSym (.derefSub 0 []) (.localSub 1 []))))
    (.branch (.use (.localSub 2 []))
      (.act (.assign (.derefSub 0 []) (.use (.localSub 1 []))))
      .skip)

theorem s1_max_assign_spec (vx vy : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .nat vx⟩, ⟨.byVal, .nat vy⟩]
      s1MaxAssignPlan
      (.constVal .unit) =
    .ok ⟨.unit,
      [zipStdVal (.symBool (Nat.blt vx vy)) (.nat vy) (.nat vx)]⟩ := rfl

/-- **S2 (`update_min`)**: Two `&mut` parameters with entry aliasing checks. -/
@[expose] def s2UpdateMinPlan : FlowPlan StdVal :=
  .seq
    (.act (.assign (.localSub 2 [])
      (.binary stdLtSym (.derefSub 0 []) (.derefSub 1 []))))
    (.branch (.use (.localSub 2 []))
      (.act (.assign (.derefSub 1 []) (.use (.derefSub 0 []))))
      (.act (.assign (.derefSub 0 []) (.use (.derefSub 1 [])))))

theorem s2_update_min_distinct_spec (vx vy : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .nat vx⟩, ⟨.mutRef 1 [], .nat vy⟩]
      s2UpdateMinPlan
      (.constVal .unit) =
    .ok ⟨.unit,
      [zipStdVal (.symBool (Nat.blt vx vy)) (.nat vx) (.nat vy),
       zipStdVal (.symBool (Nat.blt vx vy)) (.nat vx) (.nat vy)]⟩ := rfl

theorem s2_update_min_aliased_fails (vx : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .nat vx⟩, ⟨.mutRef 0 [], .nat vx⟩]
      s2UpdateMinPlan
      (.constVal .unit) = .fail := rfl

/-- **S3 (`shared_max` vs. `max_assign_shared`)**: Shared borrows permit
aliasing, whereas `&mut` + `&` on the same root is rejected. -/
@[expose] def s3SharedMaxPlan : FlowPlan StdVal :=
  .seq
    (.act (.assign (.localSub 2 [])
      (.binary stdLtSym (.derefSub 0 []) (.derefSub 1 []))))
    (.branch (.use (.localSub 2 []))
      (.act (.assign (.localSub 3 []) (.use (.derefSub 1 []))))
      (.act (.assign (.localSub 3 []) (.use (.derefSub 0 [])))))

theorem s3_shared_max_aliased_ok (va : Nat) :
    evalFnValue stdValAlg
      [⟨.sharedRef 0 [], .nat va⟩, ⟨.sharedRef 0 [], .nat va⟩]
      s3SharedMaxPlan
      (.use (.localSub 3 [])) =
    .ok ⟨zipStdVal (.symBool (Nat.blt va va)) (.nat va) (.nat va), []⟩ := rfl

theorem s3_max_assign_shared_aliased_fails (va : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .nat va⟩, ⟨.sharedRef 0 [], .nat va⟩]
      s1MaxAssignPlan
      (.constVal .unit) = .fail := rfl

/-- **S4 (`conditional_reborrow`)**: Diamond conditional reborrow
`let r = if cond { &mut *x } else { &mut *y }; *r += a; endLoan(r); *x += b`. -/
@[expose] def s4DiamondReborrowPlan : FlowPlan StdVal :=
  .seq
    (.branch (.use (.localSub 0 []))
      (.act (.borrow 5 .mutBorrow (.derefSub 1 [])))
      (.act (.borrow 5 .mutBorrow (.derefSub 2 []))))
    (.seq
      (.act (.assign (.derefSub 5 [])
        (.binary stdAdd (.derefSub 5 []) (.localSub 3 []))))
      (.seq
        (.act (.endLoan 2))
        (.act (.assign (.derefSub 1 [])
          (.binary stdAdd (.derefSub 1 []) (.localSub 4 []))))))

theorem s4_conditional_reborrow_symbolic (cond : Bool) (vx vy a b : Nat) :
    evalFnValue stdValAlg
      [⟨.byVal, .symBool cond⟩,
       ⟨.mutRef 0 [], .nat vx⟩,
       ⟨.mutRef 1 [], .nat vy⟩,
       ⟨.byVal, .nat a⟩,
       ⟨.byVal, .nat b⟩]
      s4DiamondReborrowPlan
      (.constVal .unit) =
    .ok ⟨.unit,
      [zipStdVal (.symBool cond) (.nat (vx + a + b)) (.nat (vx + b)),
       zipStdVal (.symBool cond) (.nat vy) (.nat (vy + a))]⟩ := by
  cases cond <;> rfl

/-- **S5 (`choose_mut` & `choose_test`)**: Function returning `&'a mut T` with
a lawful forward/backward lens and modular caller composition. -/
@[expose] def s5ChoosePlan : FlowPlan StdVal :=
  .branch (.use (.localSub 0 []))
    (.act (.borrow 3 .mutBorrow (.derefSub 1 [])))
    (.act (.borrow 3 .mutBorrow (.derefSub 2 [])))

theorem s5_choose_mut_spec (cond : Bool) (vx vy vNew : Nat) :
    match evalFnReturningMut stdValAlg
      [⟨.byVal, .symBool cond⟩,
       ⟨.mutRef 0 [], .nat vx⟩,
       ⟨.mutRef 1 [], .nat vy⟩]
      s5ChoosePlan 3 with
    | .ok (fwdVal, backFn) =>
      fwdVal = zipStdVal (.symBool cond) (.nat vx) (.nat vy) ∧
      backFn (.nat vNew) =
        some [zipStdVal (.symBool cond) (.nat vNew) (.nat vx),
              zipStdVal (.symBool cond) (.nat vy) (.nat vNew)]
    | .fail => False := by
  cases cond <;> exact ⟨rfl, rfl⟩

@[expose] def chooseCallSummary : CallSummary StdVal where
  returnsMutBorrow := true
  fwd pureVals mutVals :=
    match pureVals, mutVals with
    | [cond], [vx, vy] => some (zipStdVal cond vx vy)
    | _, _ => none
  back pureVals mutVals vFinal :=
    match pureVals, mutVals with
    | [cond], [vx, vy] =>
      some [zipStdVal cond (projectBranchStdVal cond true vFinal) vx,
            zipStdVal cond vy (projectBranchStdVal cond false vFinal)]
    | _, _ => none

@[expose] def choosePairLens (cond : Bool) : Lens (StdVal × StdVal) StdVal where
  get xy := chooseCallSummary.fwd [.bool cond] [xy.1, xy.2]
  put xy vNew :=
    match chooseCallSummary.back [.bool cond] [xy.1, xy.2] vNew with
    | some [x', y'] => some (x', y')
    | _ => none

theorem s5_choosePairLens_lawful (cond : Bool) :
    LawfulLens (StdVal × StdVal) StdVal (choosePairLens cond) where
  get_put := by
    intro s a hGet
    cases s with
    | mk x y =>
      cases cond <;> (
        dsimp [choosePairLens, chooseCallSummary, zipStdVal,
               projectBranchStdVal, StdVal.bool] at hGet
        injection hGet with hEq
        subst hEq
        rfl)
  put_get := by
    intro s a s' hPut
    cases s with
    | mk x y =>
      cases cond <;> (
        dsimp [choosePairLens, chooseCallSummary, zipStdVal,
               projectBranchStdVal, StdVal.bool] at hPut
        injection hPut with hEq
        subst hEq
        rfl)
  put_put := by
    intro s a1 a2 s1 hPut1
    cases s with
    | mk x y =>
      cases cond <;> (
        dsimp [choosePairLens, chooseCallSummary, zipStdVal,
               projectBranchStdVal, StdVal.bool] at hPut1
        injection hPut1 with hEq
        subst hEq
        rfl)

@[expose] def s5ChooseCallerPlan : FlowPlan StdVal :=
  .seq
    (.act (.call 4 chooseCallSummary
      [.use (.localSub 0 [])]
      [.derefSub 1 [], .derefSub 2 []]))
    (.seq
      (.act (.assign (.derefSub 4 [])
        (.binary stdAdd (.derefSub 4 []) (.localSub 3 []))))
      (.seq
        (.act (.endLoan 2))
        (.act (.assign (.derefSub 1 []) (.unary stdInc (.derefSub 1 []))))))

theorem s5_choose_caller_symbolic (cond : Bool) (vx vy delta : Nat) :
    evalFnValue stdValAlg
      [⟨.byVal, .symBool cond⟩,
       ⟨.mutRef 0 [], .nat vx⟩,
       ⟨.mutRef 1 [], .nat vy⟩,
       ⟨.byVal, .nat delta⟩]
      s5ChooseCallerPlan
      (.constVal .unit) =
    .ok ⟨.unit,
      [zipStdVal (.symBool cond) (.nat (vx + delta + 1)) (.nat (vx + 1)),
       zipStdVal (.symBool cond) (.nat vy) (.nat (vy + delta))]⟩ := by
  cases cond <;> rfl

/-- **S6 (`count_up`)**: Constructive `while` loop and non-vacuity on
insufficient fuel. -/
@[expose] def s6CountUpPlan (fuel : Nat) : FlowPlan StdVal :=
  .whileLoop fuel
    (.binary stdLtBool (.derefSub 0 []) (.localSub 1 []))
    (.act (.assign (.derefSub 0 []) (.unary stdInc (.derefSub 0 []))))

theorem s6_count_up_concrete :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .nat 2⟩, ⟨.byVal, .nat 5⟩]
      (s6CountUpPlan 3)
      (.constVal .unit) =
    .ok ⟨.unit, [.nat 5]⟩ := rfl

theorem s6_count_up_insufficient_fuel_fails :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .nat 2⟩, ⟨.byVal, .nat 5⟩]
      (s6CountUpPlan 1)
      (.constVal .unit) = .fail := rfl

/-- **S7 (`double_bounded`)**: Modular interprocedural call composition. -/
@[expose] def addInPlaceSummary : CallSummary StdVal where
  returnsMutBorrow := false
  fwd pureVals mutVals :=
    match pureVals, mutVals with
    | [⟨_, .nat _⟩], [⟨_, .nat _⟩] => some .unit
    | _, _ => none
  back pureVals mutVals _ :=
    match pureVals, mutVals with
    | [⟨_, .nat d⟩], [⟨_, .nat x⟩] => some [.nat (x + d)]
    | _, _ => none

@[expose] def s7DoubleCallPlan : FlowPlan StdVal :=
  .seq
    (.act (.call 2 addInPlaceSummary [.use (.localSub 1 [])] [.derefSub 0 []]))
    (.act (.call 2 addInPlaceSummary [.use (.localSub 1 [])] [.derefSub 0 []]))

theorem s7_double_bounded_spec (vx d : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .nat vx⟩, ⟨.byVal, .nat d⟩]
      s7DoubleCallPlan
      (.constVal .unit) =
    .ok ⟨.unit, [.nat (vx + d + d)]⟩ := rfl

/-!
## Part II: Held-Out Stress Scenarios (`H1`–`H5`) and Negative Canaries
-/

/-- **H1 Plan A**: Borrow `r0 = &mut (*p).0` (loan 1) and `r1 = &mut (*p).1`
(loan 2), swap them, end loan 1 then loan 2, and read root `*p` at `[]`. -/
@[expose] def h1SplitSwapEnd12Plan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 1 .mutBorrow (.derefSub 0 [0])))
    (.seq
      (.act (.borrow 2 .mutBorrow (.derefSub 0 [1])))
      (.seq
        (.act (.assign (.localSub 3 []) (.use (.derefSub 1 []))))
        (.seq
          (.act (.assign (.derefSub 1 []) (.use (.derefSub 2 []))))
          (.seq
            (.act (.assign (.derefSub 2 []) (.use (.localSub 3 []))))
            (.seq
              (.act (.endLoan 1))
              (.seq
                (.act (.endLoan 2))
                (.act (.assign (.localSub 4 []) (.use (.derefSub 0 []))))))))))

/-- **H1 Plan B**: Identical to Plan A except loan 2 (`&mut p.1`) ends before
loan 1 (`&mut p.0`). -/
@[expose] def h1SplitSwapEnd21Plan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 1 .mutBorrow (.derefSub 0 [0])))
    (.seq
      (.act (.borrow 2 .mutBorrow (.derefSub 0 [1])))
      (.seq
        (.act (.assign (.localSub 3 []) (.use (.derefSub 1 []))))
        (.seq
          (.act (.assign (.derefSub 1 []) (.use (.derefSub 2 []))))
          (.seq
            (.act (.assign (.derefSub 2 []) (.use (.localSub 3 []))))
            (.seq
              (.act (.endLoan 2))
              (.seq
                (.act (.endLoan 1))
                (.act (.assign (.localSub 4 []) (.use (.derefSub 0 []))))))))))

theorem h1_sibling_split_borrow_swap_spec (v0 v1 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      h1SplitSwapEnd12Plan
      (.use (.localSub 4 [])) =
    .ok ⟨.pair (.nat v1) (.nat v0), [.pair (.nat v1) (.nat v0)]⟩ := rfl

theorem h1_sibling_end_commutes_spec (v0 v1 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      h1SplitSwapEnd12Plan
      (.use (.localSub 4 [])) =
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      h1SplitSwapEnd21Plan
      (.use (.localSub 4 [])) := rfl

@[expose] def h1SharedAndMutSiblingsPlan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 1 .shared (.derefSub 0 [0])))
    (.seq
      (.act (.borrow 2 .mutBorrow (.derefSub 0 [1])))
      (.seq
        (.act (.assign (.derefSub 2 [])
          (.binary stdAdd (.derefSub 1 []) (.derefSub 2 []))))
        (.seq
          (.act (.endLoan 2))
          (.act (.endLoan 1)))))

theorem h1_shared_and_mut_disjoint_siblings_ok (v0 v1 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      h1SharedAndMutSiblingsPlan
      (.constVal .unit) =
    .ok ⟨.unit, [.pair (.nat v0) (.nat (v0 + v1))]⟩ := rfl

@[expose] def h1MultiSharedLoanIdTrackingPlan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 1 .shared (.derefSub 0 [0])))
    (.seq
      (.act (.borrow 2 .shared (.derefSub 0 [0])))
      (.seq
        (.act (.borrow 3 .mutBorrow (.derefSub 0 [1])))
        (.seq
          (.act (.endLoan 1))
          (.seq
            (.act (.assign (.derefSub 3 [])
              (.binary stdAdd (.derefSub 2 []) (.derefSub 3 []))))
            (.seq
              (.act (.endLoan 2))
              (.seq
                (.act (.endLoan 3))
                (.seq
                  (.act (.borrow 4 .mutBorrow (.derefSub 0 [0])))
                  (.seq
                    (.act (.assign (.derefSub 4 [])
                      (.unary stdInc (.derefSub 4 []))))
                    (.act (.endLoan 4))))))))))

theorem h1_multi_shared_loan_id_tracking_spec (v0 v1 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      h1MultiSharedLoanIdTrackingPlan
      (.constVal .unit) =
    .ok ⟨.unit, [.pair (.nat (v0 + 1)) (.nat (v0 + v1))]⟩ := rfl

@[expose] def h1BadMutWhileSecondSharedActivePlan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 1 .shared (.derefSub 0 [0])))
    (.seq
      (.act (.borrow 2 .shared (.derefSub 0 [0])))
      (.seq
        (.act (.endLoan 1))
        (.seq
          (.act (.borrow 3 .mutBorrow (.derefSub 0 [0])))
          (.seq (.act (.endLoan 3)) (.act (.endLoan 2))))))

theorem h1_reject_mut_while_second_shared_active (v0 v1 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      h1BadMutWhileSecondSharedActivePlan
      (.constVal .unit) = .fail := rfl

@[expose] def h1BadBorrowRootWhileFieldActivePlan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 1 .mutBorrow (.derefSub 0 [0])))
    (.seq
      (.act (.borrow 2 .mutBorrow (.derefSub 0 [])))
      (.seq (.act (.endLoan 2)) (.act (.endLoan 1))))

theorem h1_reject_root_borrow_while_field_active (v0 v1 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      h1BadBorrowRootWhileFieldActivePlan
      (.constVal .unit) = .fail := rfl

@[expose] def h1BadBorrowSubpathWhilePrefixActivePlan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 1 .mutBorrow (.derefSub 0 [0])))
    (.seq
      (.act (.borrow 2 .mutBorrow (.derefSub 0 [0, 1])))
      (.seq (.act (.endLoan 2)) (.act (.endLoan 1))))

theorem h1_reject_subpath_borrow_while_prefix_active (v0 v1 v2 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.pair (.nat v0) (.nat v1)) (.nat v2)⟩]
      h1BadBorrowSubpathWhilePrefixActivePlan
      (.constVal .unit) = .fail := rfl

/-- **H2**: Multi-region-group staggered termination with `requiredChildren`. -/
@[expose] def h2DependentRegionSpecs : List (RegionGroupSpec StdVal) :=
  [ { groupId := 0
      requiredChildren := [1]
      inputPlaces := [.derefSub 1 []]
      outDsts := [2]
      fwdOuts := fun _ muts =>
        match muts with
        | [vx] => some [vx]
        | _ => none
      backFn := fun _ _ outVals deps =>
        match outVals, deps with
        | [⟨_, .nat v0⟩], [⟨_, .nat vDep⟩] =>
          match stdAdd (.nat v0) (.nat vDep) with
          | some vSum => some ([vSum], [])
          | none => none
        | _, _ => none },
    { groupId := 1
      requiredChildren := []
      inputPlaces := []
      outDsts := [3]
      fwdOuts := fun pureVals _ =>
        match pureVals with
        | [vy] => some [vy]
        | _ => none
      backFn := fun _ _ outVals _ =>
        match outVals with
        | [v1] => some ([], [v1])
        | _ => none } ]

@[expose] def h2ValidMultiRegionPlan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 1 .mutBorrow (.derefSub 0 [0])))
    (.seq
      (.act (.callMultiRegion [.constVal (.nat 10)] h2DependentRegionSpecs))
      (.seq
        (.act (.assign (.derefSub 3 [])
          (.unary (stdAddNat 5) (.derefSub 3 []))))
        (.seq
          (.act (.endRegionGroup 1))
          (.seq
            (.act (.assign (.derefSub 2 [])
              (.unary stdInc (.derefSub 2 []))))
            (.seq
              (.act (.endRegionGroup 0))
              (.act (.endLoan 1)))))))

theorem h2_multi_region_valid_order_and_reborrow_propagation_spec
    (v0 v1 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      h2ValidMultiRegionPlan
      (.constVal .unit) =
    .ok ⟨.unit, [.pair (.nat (v0 + 1 + (10 + 5))) (.nat v1)]⟩ := rfl

@[expose] def h2BadOutOfOrderRegionPlan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 1 .mutBorrow (.derefSub 0 [0])))
    (.seq
      (.act (.callMultiRegion [.constVal (.nat 10)] h2DependentRegionSpecs))
      (.seq
        (.act (.endRegionGroup 0))
        (.seq
          (.act (.endRegionGroup 1))
          (.act (.endLoan 1)))))

theorem h2_multi_region_out_of_order_rejected (v0 v1 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      h2BadOutOfOrderRegionPlan
      (.constVal .unit) = .fail := rfl

@[expose] def h2BadEndRegionWhileOutputReborrowedPlan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 1 .mutBorrow (.derefSub 0 [0])))
    (.seq
      (.act (.callMultiRegion [.constVal (.nat 10)] h2DependentRegionSpecs))
      (.seq
        (.act (.borrow 4 .mutBorrow (.derefSub 3 [])))
        (.act (.endRegionGroup 1))))

theorem h2_reject_end_region_while_output_reborrowed (v0 v1 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      h2BadEndRegionWhileOutputReborrowedPlan
      (.constVal .unit) = .fail := rfl

@[expose] def h2ThreeLevelReborrowPlan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 2 .mutBorrow (.derefSub 0 [0])))
    (.seq
      (.act (.borrow 3 .mutBorrow (.derefSub 2 [])))
      (.seq
        (.act (.borrow 4 .mutBorrow (.derefSub 3 [])))
        (.seq
          (.act (.assign (.derefSub 4 [])
            (.binary stdAdd (.derefSub 4 []) (.localSub 1 []))))
          (.seq
            (.act (.endLoan 3))
            (.seq
              (.act (.assign (.derefSub 3 [])
                (.unary stdInc (.derefSub 3 []))))
              (.seq
                (.act (.endLoan 2))
                (.seq
                  (.act (.assign (.derefSub 2 [])
                    (.unary stdInc (.derefSub 2 []))))
                  (.act (.endLoan 1)))))))))

theorem h2_three_level_reborrow_chain_spec (v0 v1 delta : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩, ⟨.byVal, .nat delta⟩]
      h2ThreeLevelReborrowPlan
      (.constVal .unit) =
    .ok ⟨.unit, [.pair (.nat (v0 + delta + 1 + 1)) (.nat v1)]⟩ := rfl

/-- **H3**: Hybrid functional-spatial pinning and unpinned sibling isolation. -/
@[expose] def h3HybridSpatialSiblingPlan (vSpatialNew : Nat) : FlowPlan StdVal :=
  .seq
    (.act (.borrow 1 .mutBorrow (.derefSub 0 [0])))
    (.seq
      (.act (.borrow 2 .mutBorrow (.derefSub 0 [1])))
      (.seq
        (.act (.freezeSpatial 1 valueCellCodec))
        (.seq
          (.act (.assign (.derefSub 2 []) (.unary stdInc (.derefSub 2 []))))
          (.seq
            (.act (.mutateSpatial 0 0 [.init (.nat vSpatialNew)]))
            (.seq
              (.act (.reabsorbSpatial 1 valueCellCodec))
              (.seq
                (.act (.endLoan 1))
                (.act (.endLoan 2))))))))

theorem h3_hybrid_spatial_preserves_unpinned_sibling_spec
    (v0 v1 vSpatialNew : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      (h3HybridSpatialSiblingPlan vSpatialNew)
      (.constVal .unit) =
    .ok ⟨.unit, [.pair (.nat vSpatialNew) (.nat (v1 + 1))]⟩ := rfl

@[expose] def h3BadPureWriteWhileSpatialPinnedPlan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 1 .mutBorrow (.derefSub 0 [0])))
    (.seq
      (.act (.freezeSpatial 1 valueCellCodec))
      (.act (.assign (.derefSub 1 []) (.constVal (.nat 99)))))

@[expose] def h3BadEndLoanWhileSpatialPinnedPlan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 1 .mutBorrow (.derefSub 0 [0])))
    (.seq
      (.act (.freezeSpatial 1 valueCellCodec))
      (.act (.endLoan 1)))

theorem h3_reject_pure_write_and_end_while_spatial_pinned (v0 v1 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      h3BadPureWriteWhileSpatialPinnedPlan
      (.constVal .unit) = .fail ∧
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      h3BadEndLoanWhileSpatialPinnedPlan
      (.constVal .unit) = .fail :=
  ⟨rfl, rfl⟩

@[expose] def h3BadUninitReabsorbPlan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 1 .mutBorrow (.derefSub 0 [0])))
    (.seq
      (.act (.freezeSpatial 1 valueCellCodec))
      (.seq
        (.act (.mutateSpatial 0 0 [.uninit]))
        (.seq
          (.act (.reabsorbSpatial 1 valueCellCodec))
          (.act (.endLoan 1)))))

theorem h3_reject_uninit_reabsorb (v0 v1 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      h3BadUninitReabsorbPlan
      (.constVal .unit) = .fail := rfl

/-- **H4**: End-to-end operational bridges for machine styles `M1`, `M2`, and
`M3`. The `M1` and `M2` machines run `max_assign` (`if *x < y { *x = y }`) on
their own concrete state `(pc, x, y)`; `h4MaxAssignStateRel` ties that state to
the initial symbolic state through the values of `*x` and `y`. The plan
compares with the concrete `stdLtBool`, so its result is a concrete value that
the machine must reproduce. The bridges are instantiated at inputs that take
each branch, since kernel reduction cannot case-split an `if` on a
`Nat.blt` of variables. -/
@[expose] def h4MaxAssignConcretePlan : FlowPlan StdVal :=
  .seq
    (.act (.assign (.localSub 2 [])
      (.binary stdLtBool (.derefSub 0 []) (.localSub 1 []))))
    (.branch (.use (.localSub 2 []))
      (.act (.assign (.derefSub 0 []) (.use (.localSub 1 []))))
      .skip)

/-- `max_assign` machine state `(pc, x, y)` at entry (`pc = 0`) agrees with
the symbolic state on `*x` and `y`. -/
@[expose] def h4MaxAssignStateRel (st : SymState StdVal) (s : Nat × Nat × Nat) : Prop :=
  s.1 = 0 ∧
    readPlaceVal stdValAlg (.derefSub 0 []) st = some (.nat s.2.1) ∧
    readPlaceVal stdValAlg (.localSub 1 []) st = some (.nat s.2.2)

/-- `max_assign` as an `M1` step function: step `0` assigns `x := y` when
`x < y`, and step `1` returns the final `*x`. -/
@[expose] def m1MaxAssignStep : Nat × Nat × Nat → M1StepResult (Nat × Nat × Nat) StdVal
  | (0, x, y) =>
    .next (1,
      (match Nat.blt x y with
       | true => y
       | false => x), y)
  | (1, x, _) => .ret ⟨.unit, [.nat x]⟩
  | _ => .fault

/-- `max_assign` as an `M2` step function that also emits the inputs it
compares as observations. -/
@[expose] def m2MaxAssignStep :
    Nat × Nat × Nat → M2StepResult (Nat × Nat × Nat) Nat StdVal
  | (0, x, y) =>
    .step [x, y] (1,
      (match Nat.blt x y with
       | true => y
       | false => x), y)
  | (1, x, _) => .terminated ⟨.unit, [.nat x]⟩
  | _ => .failed

/-- The `M1` machine started on `*x = 3`, `y = 7` (the assigning branch)
returns `*x = 7`, matching the lifted result. -/
theorem h4_m1_bridge_sound_assigns :
    let ad := m1OperationalAdapter m1MaxAssignStep h4MaxAssignStateRel
    Exists fun k => Exists fun mFinal => Exists fun out =>
      ad.ExecutesTo (.running (0, 3, 7)) k mFinal ∧
      ad.FinalLoansRel out mFinal ∧
      out = ⟨.unit, [.nat 7]⟩ := by
  refine pure_lift_sound
    (m1OperationalAdapter m1MaxAssignStep h4MaxAssignStateRel)
    stdValAlg
    [⟨.mutRef 0 [], .nat 3⟩, ⟨.byVal, .nat 7⟩]
    h4MaxAssignConcretePlan
    (.constVal .unit)
    (fun out => out = ⟨.unit, [.nat 7]⟩)
    (.running (0, 3, 7))
    ⟨_, ⟨rfl, ⟨rfl, rfl, rfl⟩⟩⟩
    rfl
    ?_
  intro _ out _ _ hEval
  injection hEval with hOut
  subst hOut
  exact ⟨2, .returned ⟨.unit, [.nat 7]⟩, rfl, rfl⟩

/-- The `M1` machine started on `*x = 9`, `y = 4` (the skipping branch)
returns `*x = 9`, matching the lifted result. -/
theorem h4_m1_bridge_sound_skips :
    let ad := m1OperationalAdapter m1MaxAssignStep h4MaxAssignStateRel
    Exists fun k => Exists fun mFinal => Exists fun out =>
      ad.ExecutesTo (.running (0, 9, 4)) k mFinal ∧
      ad.FinalLoansRel out mFinal ∧
      out = ⟨.unit, [.nat 9]⟩ := by
  refine pure_lift_sound
    (m1OperationalAdapter m1MaxAssignStep h4MaxAssignStateRel)
    stdValAlg
    [⟨.mutRef 0 [], .nat 9⟩, ⟨.byVal, .nat 4⟩]
    h4MaxAssignConcretePlan
    (.constVal .unit)
    (fun out => out = ⟨.unit, [.nat 9]⟩)
    (.running (0, 9, 4))
    ⟨_, ⟨rfl, ⟨rfl, rfl, rfl⟩⟩⟩
    rfl
    ?_
  intro _ out _ _ hEval
  injection hEval with hOut
  subst hOut
  exact ⟨2, .returned ⟨.unit, [.nat 9]⟩, rfl, rfl⟩

/-- The `M2` machine started on `*x = 3`, `y = 7` emits the compared inputs
and terminates with `*x = 7`, matching the lifted result. -/
theorem h4_m2_bridge_sound_assigns :
    let ad := m2OperationalAdapter m2MaxAssignStep h4MaxAssignStateRel
    Exists fun k => Exists fun mFinal => Exists fun out =>
      ad.ExecutesTo ⟨(0, 3, 7), [], none⟩ k mFinal ∧
      ad.FinalLoansRel out mFinal ∧
      out = ⟨.unit, [.nat 7]⟩ := by
  refine pure_lift_sound
    (m2OperationalAdapter m2MaxAssignStep h4MaxAssignStateRel)
    stdValAlg
    [⟨.mutRef 0 [], .nat 3⟩, ⟨.byVal, .nat 7⟩]
    h4MaxAssignConcretePlan
    (.constVal .unit)
    (fun out => out = ⟨.unit, [.nat 7]⟩)
    ⟨(0, 3, 7), [], none⟩
    ⟨_, ⟨rfl, ⟨rfl, ⟨rfl, rfl, rfl⟩, trivial⟩⟩⟩
    rfl
    ?_
  intro _ out _ _ hEval
  injection hEval with hOut
  subst hOut
  exact ⟨1 + 1,
    ⟨(1, 7, 7), [] ++ [3, 7], some ⟨.unit, [.nat 7]⟩⟩,
    M2ExecutesTo.trans
      (M2ExecutesTo.step_emit rfl)
      (M2ExecutesTo.step_term rfl),
    rfl⟩

/-- The `M2` machine started on `*x = 9`, `y = 4` terminates with `*x = 9`,
matching the lifted result. -/
theorem h4_m2_bridge_sound_skips :
    let ad := m2OperationalAdapter m2MaxAssignStep h4MaxAssignStateRel
    Exists fun k => Exists fun mFinal => Exists fun out =>
      ad.ExecutesTo ⟨(0, 9, 4), [], none⟩ k mFinal ∧
      ad.FinalLoansRel out mFinal ∧
      out = ⟨.unit, [.nat 9]⟩ := by
  refine pure_lift_sound
    (m2OperationalAdapter m2MaxAssignStep h4MaxAssignStateRel)
    stdValAlg
    [⟨.mutRef 0 [], .nat 9⟩, ⟨.byVal, .nat 4⟩]
    h4MaxAssignConcretePlan
    (.constVal .unit)
    (fun out => out = ⟨.unit, [.nat 9]⟩)
    ⟨(0, 9, 4), [], none⟩
    ⟨_, ⟨rfl, ⟨rfl, ⟨rfl, rfl, rfl⟩, trivial⟩⟩⟩
    rfl
    ?_
  intro _ out _ _ hEval
  injection hEval with hOut
  subst hOut
  exact ⟨1 + 1,
    ⟨(1, 9, 4), [] ++ [9, 4], some ⟨.unit, [.nat 9]⟩⟩,
    M2ExecutesTo.trans
      (M2ExecutesTo.step_emit rfl)
      (M2ExecutesTo.step_term rfl),
    rfl⟩

@[expose] def m3SwapHeapStep (cells : List (M3Cell StdVal)) :
    M1StepResult (List (M3Cell StdVal)) StdVal :=
  match cells with
  | [ ⟨0, 0, [], 0, .activeUnique, .init ⟨_, .pairBranch fl fr a b⟩⟩,
      ⟨0, 1, [0], 1, .activeUnique, .init _⟩,
      ⟨0, 2, [1], 2, .activeUnique, .init _⟩ ] =>
    .next [
      ⟨0, 0, [], 0, .activeUnique, .init (.pair ⟨fr, b⟩ ⟨fl, a⟩)⟩,
      ⟨0, 1, [0], 1, .disabled, .init ⟨fr, b⟩⟩,
      ⟨0, 2, [1], 2, .disabled, .init ⟨fl, a⟩⟩ ]
  | [ ⟨0, 0, [], 0, .activeUnique, .init swapped⟩,
      ⟨0, 1, [0], 1, .disabled, _⟩,
      ⟨0, 2, [1], 2, .disabled, _⟩ ] =>
    .ret ⟨swapped, [swapped]⟩
  | _ => .fault

theorem h4_m3_tree_borrows_bridge_sound (v0 v1 : Nat) :
    let sp := m3SpatialModel StdVal
    let initHeap : List (M3Cell StdVal) :=
      [ ⟨0, 0, [], 0, .activeUnique, .init (.pair (.nat v0) (.nat v1))⟩,
        ⟨0, 1, [0], 1, .activeUnique, .init (.nat v0)⟩,
        ⟨0, 2, [1], 2, .activeUnique, .init (.nat v1)⟩ ]
    let splitPerm : PermTree :=
      .split [([0], .mutLocked 1), ([1], .mutLocked 2)]
    let ad :=
      m3OperationalAdapter m3SwapHeapStep (fun _ _ => True)
        ([(0, (0, 0), [])]) ([(0, (0, 0), [])])
    sp.ownSubPlace initHeap (0, 1) [0] 0 (getPathPerm [0] splitPerm)
      (.nat v0) ∧
    sp.ownSubPlace initHeap (0, 2) [1] 0 (getPathPerm [1] splitPerm)
      (.nat v1) ∧
    (Exists fun k => Exists fun mFinal => Exists fun out =>
      ad.ExecutesTo ⟨initHeap, none⟩ k mFinal ∧
      ad.FinalLoansRel out mFinal ∧
      out = ⟨.pair (.nat v1) (.nat v0), [.pair (.nat v1) (.nat v0)]⟩) := by
  refine ⟨⟨rfl, ⟨rfl, Or.inl rfl⟩⟩, ⟨rfl, ⟨rfl, Or.inl rfl⟩⟩, ?_⟩
  refine pure_lift_sound
    (m3OperationalAdapter m3SwapHeapStep (fun _ _ => True)
      ([(0, (0, 0), [])]) ([(0, (0, 0), [])]))
    stdValAlg
    ([⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩])
    h1SplitSwapEnd12Plan
    (.use (.localSub 4 []))
    (fun out => out = ⟨.pair (.nat v1) (.nat v0), [.pair (.nat v1) (.nat v0)]⟩)
    ⟨[ ⟨0, 0, [], 0, .activeUnique, .init (.pair (.nat v0) (.nat v1))⟩,
       ⟨0, 1, [0], 1, .activeUnique, .init (.nat v0)⟩,
       ⟨0, 2, [1], 2, .activeUnique, .init (.nat v1)⟩ ], none⟩
    ⟨_,
      ⟨rfl,
        ⟨rfl,
          ⟨⟨⟨trivial, trivial⟩,
            ⟨⟨rfl, ⟨rfl, ⟨rfl, Or.inl rfl⟩⟩⟩, trivial⟩⟩,
           trivial⟩⟩⟩⟩
    rfl
    ?_
  intro _ out _ _ hEval
  injection hEval with hOut
  subst hOut
  refine ⟨1 + 1,
    ⟨⟨[ ⟨0, 0, [], 0, .activeUnique, .init (.pair (.nat v1) (.nat v0))⟩,
        ⟨0, 1, [0], 1, .disabled, .init (.nat v1)⟩,
        ⟨0, 2, [1], 2, .disabled, .init (.nat v0)⟩ ],
      some ⟨.pair (.nat v1) (.nat v0), [.pair (.nat v1) (.nat v0)]⟩⟩,
    M3ExecutesTo.trans
      (M3ExecutesTo.step_heap rfl)
      (M3ExecutesTo.step_ret rfl),
    ⟨rfl, ⟨⟨rfl, ⟨rfl, Or.inl rfl⟩⟩, rfl⟩⟩⟩⟩

/-- **H5**: Nested early return inside sub-borrows and Goodhart rejection
canaries. -/
@[expose] def h5EarlyReturnNestedSubBorrowsPlan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 2 .mutBorrow (.derefSub 0 [0])))
    (.seq
      (.act (.borrow 3 .mutBorrow (.derefSub 2 [])))
      (.seq
        (.branch (.use (.localSub 1 []))
          (.seq
            (.act (.assign (.derefSub 3 [])
              (.unary (stdAddNat 10) (.derefSub 3 []))))
            (.earlyReturn [2, 1] [] (.constVal (.nat 1))))
          (.act (.endLoan 2)))
        (.seq
          (.act (.assign (.derefSub 2 [])
            (.unary (stdAddNat 100) (.derefSub 2 []))))
          (.act (.endLoan 1)))))

theorem h5_early_return_branch_taken_spec (v0 v1 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩, ⟨.byVal, .bool true⟩]
      h5EarlyReturnNestedSubBorrowsPlan
      (.constVal (.nat 0)) =
    .ok ⟨.nat 1, [.pair (.nat (v0 + 10)) (.nat v1)]⟩ := rfl

theorem h5_early_return_branch_not_taken_spec (v0 v1 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩, ⟨.byVal, .bool false⟩]
      h5EarlyReturnNestedSubBorrowsPlan
      (.constVal (.nat 0)) =
    .ok ⟨.nat 0, [.pair (.nat (v0 + 100)) (.nat v1)]⟩ := rfl

@[expose] def h5GoodhartEarlyReturnUnendedLoanPlan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 2 .mutBorrow (.derefSub 0 [0])))
    (.seq
      (.act (.borrow 3 .mutBorrow (.derefSub 2 [])))
      (.earlyReturn [2] [] (.constVal (.nat 1))))

theorem h5_goodhart_early_return_unended_loan_fails (v0 v1 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      h5GoodhartEarlyReturnUnendedLoanPlan
      (.constVal (.nat 0)) = .fail := rfl

@[expose] def h5GoodhartOutOfOrderEndLoanPlan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 2 .mutBorrow (.derefSub 0 [0])))
    (.seq
      (.act (.borrow 3 .mutBorrow (.derefSub 2 [])))
      (.seq
        (.act (.endLoan 1))
        (.act (.endLoan 2))))

theorem h5_goodhart_out_of_order_end_loan_fails (v0 v1 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      h5GoodhartOutOfOrderEndLoanPlan
      (.constVal .unit) = .fail := rfl

@[expose] def h5GoodhartDoubleEndLoanPlan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 1 .mutBorrow (.derefSub 0 [0])))
    (.seq
      (.act (.endLoan 1))
      (.act (.endLoan 1)))

theorem h5_goodhart_double_end_loan_fails (v0 v1 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      h5GoodhartDoubleEndLoanPlan
      (.constVal .unit) = .fail := rfl

@[expose] def h5GoodhartUnendedLoanAtReturnPlan : FlowPlan StdVal :=
  .act (.borrow 1 .mutBorrow (.derefSub 0 [0]))

theorem h5_goodhart_unended_loan_at_normal_return_fails (v0 v1 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      h5GoodhartUnendedLoanAtReturnPlan
      (.constVal .unit) = .fail := rfl

@[expose] def h5GoodhartReadLocalWhileMutBorrowedPlan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 1 .mutBorrow (.localSub 0 [])))
    (.seq
      (.act (.assign (.derefSub 1 []) (.constVal (.nat 99))))
      (.seq
        (.act (.assign (.localSub 2 []) (.use (.localSub 0 []))))
        (.act (.endLoan 0))))

theorem h5_goodhart_read_local_while_mut_borrowed_fails (v0 : Nat) :
    evalFnValue stdValAlg
      [⟨.byVal, .nat v0⟩]
      h5GoodhartReadLocalWhileMutBorrowedPlan
      (.use (.localSub 2 [])) = .fail := rfl

@[expose] def h5GoodhartAliasedBranchJoinPlan : FlowPlan StdVal :=
  .branchExplicitJoin (.use (.localSub 0 []))
    .skip
    .skip
    [(1, 2), (1, 3)]

theorem h5_goodhart_aliased_branch_join_fails (cond : Bool) :
    evalFnValue stdValAlg
      [⟨.byVal, .symBool cond⟩]
      h5GoodhartAliasedBranchJoinPlan
      (.constVal .unit) = .fail := rfl

end Anneal.PureLift

end
