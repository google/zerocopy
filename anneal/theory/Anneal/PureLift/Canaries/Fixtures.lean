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


namespace Anneal.PureLift

/-!
# Verification Suite and Negative Falsification Canaries (`Canaries`)

End-to-end kernel-verified test suite exercising `PureLift` across:
- **Part I (`S1`–`S7`)**: single mutable borrow (`max_assign`), two-reference
  disjoint vs. aliased entry validation (`update_min`), shared vs. mutable
  aliasing (`shared_max`), diamond conditional reborrows
  (`conditional_reborrow`), borrow-returning functions and lawful backward
  lenses (`choose_mut`), constructive loops (`count_up`), and modular call
  composition (`double_bounded`).
- **Part II (`H1`–`H5`)**: split sibling sub-place borrows and commutative loan
  release (`H1`), multi-region-group staggered termination with outlives order
  and 3-level reborrow chains (`H2`), hybrid functional-spatial pinning and
  reabsorption (`H3`), operational bridges to machine styles `M1`, `M2`, and
  `M3` (`H4`), and nested early return plus Goodhart vacuity rejection canaries
  (`H5`).
- **Part III**: edge cases and negative tests for `Plan`, `BlockCfg`, and
  `Adapter` (loops, entry validation, CFG terminators, spatial bindings, and
  branch joins), followed by focused suites on region-group reuse, handle
  copies, and join shapes; region deposits, field commutation, and region
  outputs; field joins, uninitialized locals, handles, and writeback
  ownership; writeback checks, value returns, and explicit joins; choice
  writebacks and uneven explicit joins; and branch-wise handle accounting and
  correlated writebacks.
-/

/-- Size-indexed representation of `StdVal` trees where the type index records
the exact structural node count, ensuring that `fuel` is unforgeable and
monotonically exceeds the recursion depth of every subtree. -/
inductive StdValTree : Nat → Type where
  | unit : StdValTree 1
  | nat (n : Nat) : StdValTree 1
  | bool (b : Bool) : StdValTree 1
  | symBool (b : Bool) : StdValTree 1
  | pairBranch (fl fr : Nat) (fst : StdValTree fl) (snd : StdValTree fr) :
      StdValTree (fl + fr + 1)
  | refVal (lid : LoanId) (path : SubPath) : StdValTree 1
  | choice (fc ft ff : Nat) (cond : StdValTree fc)
      (vt : StdValTree ft) (vf : StdValTree ff) :
      StdValTree (fc + ft + ff + 1)

/-- Reference value carrier for the `PureLift` verification suite, bundling a
structural fuel index `fuel` with a size-indexed `StdValTree fuel`. -/
structure StdVal where
  fuel : Nat
  tree : StdValTree fuel

def StdVal.unit : StdVal :=
  ⟨1, .unit⟩

def StdVal.nat (n : Nat) : StdVal :=
  ⟨1, .nat n⟩

def StdVal.bool (b : Bool) : StdVal :=
  ⟨1, .bool b⟩

def StdVal.symBool (b : Bool) : StdVal :=
  ⟨1, .symBool b⟩

/-- Smart constructor for binary aggregate pairs carrying exact structural
recursion fuel `fst.fuel + snd.fuel + 1`. -/
def StdVal.pair (fst snd : StdVal) : StdVal :=
  ⟨fst.fuel + snd.fuel + 1, .pairBranch fst.fuel snd.fuel fst.tree snd.tree⟩

def StdVal.refVal (lid : LoanId) (path : SubPath) : StdVal :=
  ⟨1, .refVal lid path⟩

def StdVal.choice (cond vt vf : StdVal) : StdVal :=
  ⟨cond.fuel + vt.fuel + vf.fuel + 1,
   .choice cond.fuel vt.fuel vf.fuel cond.tree vt.tree vf.tree⟩

def stdBoolEq (b1 b2 : Bool) : Bool :=
  match b1, b2 with
  | true, true => true
  | false, false => true
  | _, _ => false

theorem stdBoolEq_refl (b : Bool) : stdBoolEq b b = true := by
  cases b <;> rfl

def stdValEqStep (ih : StdVal → StdVal → Bool) (a b : StdVal) : Bool :=
  match a, b with
  | ⟨_, .unit⟩, ⟨_, .unit⟩ => true
  | ⟨_, .nat n1⟩, ⟨_, .nat n2⟩ => Nat.beq n1 n2
  | ⟨_, .bool b1⟩, ⟨_, .bool b2⟩ => stdBoolEq b1 b2
  | ⟨_, .symBool b1⟩, ⟨_, .symBool b2⟩ => stdBoolEq b1 b2
  | ⟨_, .pairBranch fl1 fr1 l1 r1⟩, ⟨_, .pairBranch fl2 fr2 l2 r2⟩ =>
    ih ⟨fl1, l1⟩ ⟨fl2, l2⟩ && ih ⟨fr1, r1⟩ ⟨fr2, r2⟩
  | ⟨_, .refVal lid1 p1⟩, ⟨_, .refVal lid2 p2⟩ =>
    Nat.beq lid1 lid2 && lensTestSubPathEq p1 p2
  | ⟨_, .choice fc1 ft1 ff1 c1 vt1 vf1⟩,
    ⟨_, .choice fc2 ft2 ff2 c2 vt2 vf2⟩ =>
    ih ⟨fc1, c1⟩ ⟨fc2, c2⟩ &&
    ih ⟨ft1, vt1⟩ ⟨ft2, vt2⟩ &&
    ih ⟨ff1, vf1⟩ ⟨ff2, vf2⟩
  | _, _ => false

def stdValEqFuel (k : Nat) (v1 v2 : StdVal) : Bool :=
  natFold
    (fun _ _ => false)
    (fun _ ih a b => stdValEqStep ih a b)
    k v1 v2

def stdValEq (v1 v2 : StdVal) : Bool :=
  stdValEqFuel v1.fuel v1 v2

theorem stdValTree_eq_refl :
    ∀ {f : Nat} (t : StdValTree f) (k : Nat),
      f ≤ k → stdValEqFuel k ⟨f, t⟩ ⟨f, t⟩ = true := by
  intro f t
  induction t with
  | unit =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ _ => rfl
  | nat n =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ _ =>
      change Nat.beq n n = true
      exact Nat.beq_refl n
  | bool b =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ _ =>
      change stdBoolEq b b = true
      exact stdBoolEq_refl b
  | symBool b =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ _ =>
      change stdBoolEq b b = true
      exact stdBoolEq_refl b
  | pairBranch fl fr l r ihl ihr =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ k' =>
      have hSub : fl + fr ≤ k' := Nat.le_of_succ_le_succ hLe
      have hFl : fl ≤ k' := Nat.le_trans (Nat.le_add_right fl fr) hSub
      have hFr : fr ≤ k' := Nat.le_trans (Nat.le_add_left fr fl) hSub
      change
        (stdValEqFuel k' ⟨fl, l⟩ ⟨fl, l⟩ &&
         stdValEqFuel k' ⟨fr, r⟩ ⟨fr, r⟩) = true
      rw [ihl k' hFl, ihr k' hFr]
      rfl
  | refVal lid path =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ _ =>
      change (Nat.beq lid lid && lensTestSubPathEq path path) = true
      rw [Nat.beq_refl lid, lensTestSubPathEq_refl path]
      rfl
  | choice fc ft ff c vt vf ihc iht ihf =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ k' =>
      have hSub : fc + ft + ff ≤ k' := Nat.le_of_succ_le_succ hLe
      have hSub12 : fc + ft ≤ k' :=
        Nat.le_trans (Nat.le_add_right (fc + ft) ff) hSub
      have hFc : fc ≤ k' := Nat.le_trans (Nat.le_add_right fc ft) hSub12
      have hFt : ft ≤ k' := Nat.le_trans (Nat.le_add_left ft fc) hSub12
      have hFf : ff ≤ k' := Nat.le_trans (Nat.le_add_left ff (fc + ft)) hSub
      change
        (stdValEqFuel k' ⟨fc, c⟩ ⟨fc, c⟩ &&
         stdValEqFuel k' ⟨ft, vt⟩ ⟨ft, vt⟩ &&
         stdValEqFuel k' ⟨ff, vf⟩ ⟨ff, vf⟩) = true
      rw [ihc k' hFc, iht k' hFt, ihf k' hFf]
      rfl

theorem stdValEq_refl (v : StdVal) : stdValEq v v = true := by
  cases v with
  | mk f t =>
    exact stdValTree_eq_refl t f (Nat.le_refl f)

def stdAsBool (v : StdVal) : Option Bool :=
  match v with
  | ⟨_, .bool b⟩ => some b
  | _ => none

def zipStdVal (cond vt vf : StdVal) : StdVal :=
  match stdAsBool cond with
  | some true => vt
  | some false => vf
  | none => .choice cond vt vf

def projectBranchStdStep (cond : StdVal) (branch : Bool)
    (ih : StdVal → StdVal) (v0 : StdVal) : StdVal :=
  match v0 with
  | ⟨_, .choice fc ft ff c vt vf⟩ =>
    if stdValEq cond ⟨fc, c⟩ then
      if branch then ih ⟨ft, vt⟩ else ih ⟨ff, vf⟩
    else
      -- The guard may itself depend on `cond`; projecting it can make it
      -- concrete, in which case `zipStdVal` selects the arm.
      zipStdVal (ih ⟨fc, c⟩) (ih ⟨ft, vt⟩) (ih ⟨ff, vf⟩)
  | ⟨_, .pairBranch fl fr l r⟩ =>
    .pair (ih ⟨fl, l⟩) (ih ⟨fr, r⟩)
  | other => other

def projectBranchStdFuel (cond : StdVal) (branch : Bool)
    (k : Nat) (v : StdVal) : StdVal :=
  natFold (fun v0 => v0)
    (fun _ ih v0 => projectBranchStdStep cond branch ih v0) k v

def projectBranchStdVal (cond : StdVal) (branch : Bool) (v : StdVal) :
    StdVal :=
  match stdAsBool cond with
  | some _ => v
  | none => projectBranchStdFuel cond branch v.fuel v

/-- One step of `remapStdVal`: rename a handle to `oldLid` at the root of `v0`
to `newLid`, and rename the children of `v0` with `ih`. -/
def remapStdStep (oldLid newLid : LoanId) (ih : StdVal → StdVal)
    (v0 : StdVal) : StdVal :=
  match v0 with
  | ⟨_, .unit⟩ => .unit
  | ⟨_, .nat n⟩ => .nat n
  | ⟨_, .bool b⟩ => .bool b
  | ⟨_, .symBool b⟩ => .symBool b
  | ⟨_, .pairBranch fl fr a b⟩ => .pair (ih ⟨fl, a⟩) (ih ⟨fr, b⟩)
  | ⟨_, .refVal lid path⟩ =>
    if lid == oldLid then .refVal newLid path else .refVal lid path
  | ⟨_, .choice fc ft ff c vt vf⟩ =>
    .choice (ih ⟨fc, c⟩) (ih ⟨ft, vt⟩) (ih ⟨ff, vf⟩)

/-- `remapStdStep` nested `k` deep; parts of `v` deeper than `k` are left
unchanged. -/
def remapStdFuel (oldLid newLid : LoanId) (k : Nat) (v : StdVal) : StdVal :=
  natFold (fun v0 => v0) (fun _ ih v0 => remapStdStep oldLid newLid ih v0) k v

/-- Rename every handle to loan `oldLid` inside `v` to `newLid`. The fuel
`v.fuel` exceeds the depth of every node of `v` (`remapStdFuel_eq`). -/
def remapStdVal (oldLid newLid : LoanId) (v : StdVal) : StdVal :=
  remapStdFuel oldLid newLid v.fuel v

def stdValGetField (idx : FieldIdx) (v : StdVal) : Option StdVal :=
  match idx, v with
  | 0, ⟨_, .pairBranch fl _ a _⟩ => some ⟨fl, a⟩
  | 1, ⟨_, .pairBranch _ fr _ b⟩ => some ⟨fr, b⟩
  | _, _ => none

def stdValSetField (idx : FieldIdx) (v child : StdVal) : Option StdVal :=
  match idx, v, child with
  | 0, ⟨_, .pairBranch _ fr _ b⟩, ⟨fChild, tChild⟩ =>
    some ⟨fChild + fr + 1, .pairBranch fChild fr tChild b⟩
  | 1, ⟨_, .pairBranch fl _ a _⟩, ⟨fChild, tChild⟩ =>
    some ⟨fl + fChild + 1, .pairBranch fl fChild a tChild⟩
  | _, _, _ => none

theorem stdVal_getField_setField (f : FieldIdx) (s a : StdVal)
    (hGet : stdValGetField f s = some a) :
    stdValSetField f s a = some s := by
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
  | succ f' =>
    cases f' with
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

theorem stdVal_setField_getField (f : FieldIdx) (s a s' : StdVal)
    (hPut : stdValSetField f s a = some s') :
    stdValGetField f s' = some a := by
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
  | succ f' =>
    cases f' with
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

theorem stdVal_setField_setField (f : FieldIdx) (s a1 a2 s1 : StdVal)
    (hPut1 : stdValSetField f s a1 = some s1) :
    stdValSetField f s1 a2 = stdValSetField f s a2 := by
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
  | succ f' =>
    cases f' with
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

theorem stdVal_getField_setField_other (f g : FieldIdx) (s a s' : StdVal)
    (hNe : f ≠ g) (hPut : stdValSetField f s a = some s') :
    stdValGetField g s' = stdValGetField g s := by
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
          cases g with
          | zero => exact False.elim (hNe rfl)
          | succ g' => cases g' <;> rfl
      | unit => nomatch hPut
      | nat _ => nomatch hPut
      | bool _ => nomatch hPut
      | symBool _ => nomatch hPut
      | refVal _ _ => nomatch hPut
      | choice _ _ _ _ _ _ => nomatch hPut
  | succ f' =>
    cases f' with
    | zero =>
      cases s with
      | mk _ ts =>
        cases ts with
        | pairBranch fl fr l r =>
          cases a with
          | mk fa ta =>
            injection hPut with hEq
            subst hEq
            cases g with
            | zero => rfl
            | succ g' =>
              cases g' with
              | zero => exact False.elim (hNe rfl)
              | succ _ => rfl
        | unit => nomatch hPut
        | nat _ => nomatch hPut
        | bool _ => nomatch hPut
        | symBool _ => nomatch hPut
        | refVal _ _ => nomatch hPut
        | choice _ _ _ _ _ _ => nomatch hPut
    | succ _ => nomatch hPut

theorem stdVal_setField_setField_comm (f g : FieldIdx) (s a b s1 s2 : StdVal)
    (hNe : f ≠ g) (h1 : stdValSetField f s a = some s1)
    (h2 : stdValSetField g s1 b = some s2) :
    Exists fun s1' =>
      stdValSetField g s b = some s1' ∧ stdValSetField f s1' a = some s2 := by
  cases a with
  | mk fa ta =>
    cases b with
    | mk fb tb =>
      cases f with
      | zero =>
        cases s with
        | mk _ ts =>
          cases ts with
          | pairBranch fl fr l r =>
            injection h1 with hEq1
            subst hEq1
            cases g with
            | zero => exact False.elim (hNe rfl)
            | succ g' =>
              cases g' with
              | zero =>
                injection h2 with hEq2
                subst hEq2
                exact ⟨_, rfl, rfl⟩
              | succ _ => nomatch h2
          | unit => nomatch h1
          | nat _ => nomatch h1
          | bool _ => nomatch h1
          | symBool _ => nomatch h1
          | refVal _ _ => nomatch h1
          | choice _ _ _ _ _ _ => nomatch h1
      | succ f' =>
        cases f' with
        | zero =>
          cases s with
          | mk _ ts =>
            cases ts with
            | pairBranch fl fr l r =>
              injection h1 with hEq1
              subst hEq1
              cases g with
              | zero =>
                injection h2 with hEq2
                subst hEq2
                exact ⟨_, rfl, rfl⟩
              | succ g' =>
                cases g' with
                | zero => exact False.elim (hNe rfl)
                | succ _ => nomatch h2
            | unit => nomatch h1
            | nat _ => nomatch h1
            | bool _ => nomatch h1
            | symBool _ => nomatch h1
            | refVal _ _ => nomatch h1
            | choice _ _ _ _ _ _ => nomatch h1
        | succ _ => nomatch h1

/-- Every `StdValTree` has positive size. -/
theorem stdValTree_fuel_pos : ∀ {f : Nat} (_ : StdValTree f), 0 < f
  | _, .unit => Nat.zero_lt_succ 0
  | _, .nat _ => Nat.zero_lt_succ 0
  | _, .bool _ => Nat.zero_lt_succ 0
  | _, .symBool _ => Nat.zero_lt_succ 0
  | _, .pairBranch _ _ _ _ => Nat.zero_lt_succ _
  | _, .refVal _ _ => Nat.zero_lt_succ 0
  | _, .choice _ _ _ _ _ _ => Nat.zero_lt_succ _

theorem stdVal_getField_lt_sizeBound (f : FieldIdx) (v c : StdVal)
    (hGet : stdValGetField f v = some c) : f < v.fuel ∧ c.fuel < v.fuel := by
  cases v with
  | mk fv tv =>
    cases f with
    | zero =>
      cases tv with
      | pairBranch fl fr l r =>
        injection hGet with hEq
        subst hEq
        exact ⟨Nat.zero_lt_succ _, Nat.lt_succ_of_le (Nat.le_add_right fl fr)⟩
      | unit => nomatch hGet
      | nat _ => nomatch hGet
      | bool _ => nomatch hGet
      | symBool _ => nomatch hGet
      | refVal _ _ => nomatch hGet
      | choice _ _ _ _ _ _ => nomatch hGet
    | succ f' =>
      cases f' with
      | zero =>
        cases tv with
        | pairBranch fl fr l r =>
          injection hGet with hEq
          subst hEq
          exact ⟨Nat.succ_lt_succ
              (Nat.lt_of_lt_of_le (stdValTree_fuel_pos l)
                (Nat.le_add_right fl fr)),
            Nat.lt_succ_of_le (Nat.le_add_left fr fl)⟩
        | unit => nomatch hGet
        | nat _ => nomatch hGet
        | bool _ => nomatch hGet
        | symBool _ => nomatch hGet
        | refVal _ _ => nomatch hGet
        | choice _ _ _ _ _ _ => nomatch hGet
      | succ _ => nomatch hGet

theorem projectBranchStdFuel_eq (cond : StdVal) (branch : Bool) :
    ∀ {n : Nat} (tr : StdValTree n) (k : Nat), n ≤ k →
      projectBranchStdFuel cond branch k ⟨n, tr⟩ =
        projectBranchStdFuel cond branch n ⟨n, tr⟩ := by
  intro n tr
  induction tr with
  | unit =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ _ => rfl
  | nat _ =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ _ => rfl
  | bool _ =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ _ => rfl
  | symBool _ =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ _ => rfl
  | refVal _ _ =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ _ => rfl
  | pairBranch fl fr l r ihl ihr =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ k' =>
      have hSub : fl + fr ≤ k' := Nat.le_of_succ_le_succ hLe
      have hL : fl ≤ fl + fr := Nat.le_add_right fl fr
      have hR : fr ≤ fl + fr := Nat.le_add_left fr fl
      change StdVal.pair (projectBranchStdFuel cond branch k' ⟨fl, l⟩)
          (projectBranchStdFuel cond branch k' ⟨fr, r⟩) =
        StdVal.pair (projectBranchStdFuel cond branch (fl + fr) ⟨fl, l⟩)
          (projectBranchStdFuel cond branch (fl + fr) ⟨fr, r⟩)
      rw [ihl k' (Nat.le_trans hL hSub), ihr k' (Nat.le_trans hR hSub),
        ihl _ hL, ihr _ hR]
  | choice fc ft ff c vt vf ihc iht ihf =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ k' =>
      have hSub : fc + ft + ff ≤ k' := Nat.le_of_succ_le_succ hLe
      have hC : fc ≤ fc + ft + ff :=
        Nat.le_trans (Nat.le_add_right fc ft) (Nat.le_add_right (fc + ft) ff)
      have hT : ft ≤ fc + ft + ff :=
        Nat.le_trans (Nat.le_add_left ft fc) (Nat.le_add_right (fc + ft) ff)
      have hF : ff ≤ fc + ft + ff := Nat.le_add_left ff (fc + ft)
      change
        (if stdValEq cond ⟨fc, c⟩ then
           if branch then projectBranchStdFuel cond branch k' ⟨ft, vt⟩
           else projectBranchStdFuel cond branch k' ⟨ff, vf⟩
         else
           zipStdVal (projectBranchStdFuel cond branch k' ⟨fc, c⟩)
             (projectBranchStdFuel cond branch k' ⟨ft, vt⟩)
             (projectBranchStdFuel cond branch k' ⟨ff, vf⟩)) =
        (if stdValEq cond ⟨fc, c⟩ then
           if branch then
             projectBranchStdFuel cond branch (fc + ft + ff) ⟨ft, vt⟩
           else
             projectBranchStdFuel cond branch (fc + ft + ff) ⟨ff, vf⟩
         else
           zipStdVal (projectBranchStdFuel cond branch (fc + ft + ff) ⟨fc, c⟩)
             (projectBranchStdFuel cond branch (fc + ft + ff) ⟨ft, vt⟩)
             (projectBranchStdFuel cond branch (fc + ft + ff) ⟨ff, vf⟩))
      rw [ihc k' (Nat.le_trans hC hSub), iht k' (Nat.le_trans hT hSub),
        ihf k' (Nat.le_trans hF hSub), ihc _ hC, iht _ hT, ihf _ hF]

theorem stdVal_projectBranchVal_concrete (cond : StdVal) (b branch : Bool)
    (v : StdVal) (hConcrete : stdAsBool cond = some b) :
    projectBranchStdVal cond branch v = v := by
  dsimp [projectBranchStdVal]
  rw [hConcrete]

theorem stdVal_projectBranchVal_zip_true (cond vt vf : StdVal)
    (hSym : stdAsBool cond = none) :
    projectBranchStdVal cond true (zipStdVal cond vt vf) =
      projectBranchStdVal cond true vt := by
  dsimp [projectBranchStdVal, zipStdVal]
  rw [hSym]
  cases cond with
  | mk fc tc =>
    cases vt with
    | mk ft tt =>
      cases vf with
      | mk ff tf =>
        have hT : ft ≤ fc + ft + ff :=
          Nat.le_trans (Nat.le_add_left ft fc) (Nat.le_add_right (fc + ft) ff)
        change
          (if stdValEq ⟨fc, tc⟩ ⟨fc, tc⟩ then
             projectBranchStdFuel ⟨fc, tc⟩ true (fc + ft + ff) ⟨ft, tt⟩
           else _) =
          projectBranchStdFuel ⟨fc, tc⟩ true ft ⟨ft, tt⟩
        rw [stdValEq_refl ⟨fc, tc⟩]
        exact projectBranchStdFuel_eq ⟨fc, tc⟩ true tt (fc + ft + ff) hT

theorem stdVal_projectBranchVal_zip_false (cond vt vf : StdVal)
    (hSym : stdAsBool cond = none) :
    projectBranchStdVal cond false (zipStdVal cond vt vf) =
      projectBranchStdVal cond false vf := by
  dsimp [projectBranchStdVal, zipStdVal]
  rw [hSym]
  cases cond with
  | mk fc tc =>
    cases vt with
    | mk ft tt =>
      cases vf with
      | mk ff tf =>
        have hF : ff ≤ fc + ft + ff := Nat.le_add_left ff (fc + ft)
        change
          (if stdValEq ⟨fc, tc⟩ ⟨fc, tc⟩ then
             projectBranchStdFuel ⟨fc, tc⟩ false (fc + ft + ff) ⟨ff, tf⟩
           else _) =
          projectBranchStdFuel ⟨fc, tc⟩ false ff ⟨ff, tf⟩
        rw [stdValEq_refl ⟨fc, tc⟩]
        exact projectBranchStdFuel_eq ⟨fc, tc⟩ false tf (fc + ft + ff) hF

theorem projectBranchStdVal_pair (cond : StdVal) (branch : Bool)
    (l r : StdVal) :
    projectBranchStdVal cond branch (.pair l r) =
      .pair (projectBranchStdVal cond branch l)
        (projectBranchStdVal cond branch r) := by
  dsimp [projectBranchStdVal]
  cases hCond : stdAsBool cond with
  | some _ => rfl
  | none =>
    cases l with
    | mk fl tl =>
      cases r with
      | mk fr tr =>
        change StdVal.pair
            (projectBranchStdFuel cond branch (fl + fr) ⟨fl, tl⟩)
            (projectBranchStdFuel cond branch (fl + fr) ⟨fr, tr⟩) = _
        rw [projectBranchStdFuel_eq cond branch tl _ (Nat.le_add_right fl fr),
            projectBranchStdFuel_eq cond branch tr _ (Nat.le_add_left fr fl)]

theorem stdVal_getField_projectBranchVal (cond : StdVal) (branch : Bool)
    (f : FieldIdx) (s a : StdVal) (hGet : stdValGetField f s = some a) :
    stdValGetField f (projectBranchStdVal cond branch s) =
      some (projectBranchStdVal cond branch a) := by
  cases s with
  | mk fs ts =>
    cases f with
    | zero =>
      cases ts with
      | pairBranch fl fr l r =>
        injection hGet with hEq
        subst hEq
        change stdValGetField 0
            (projectBranchStdVal cond branch (.pair ⟨fl, l⟩ ⟨fr, r⟩)) = _
        rw [projectBranchStdVal_pair]
        rfl
      | unit => nomatch hGet
      | nat _ => nomatch hGet
      | bool _ => nomatch hGet
      | symBool _ => nomatch hGet
      | refVal _ _ => nomatch hGet
      | choice _ _ _ _ _ _ => nomatch hGet
    | succ f' =>
      cases f' with
      | zero =>
        cases ts with
        | pairBranch fl fr l r =>
          injection hGet with hEq
          subst hEq
          change stdValGetField 1
              (projectBranchStdVal cond branch (.pair ⟨fl, l⟩ ⟨fr, r⟩)) = _
          rw [projectBranchStdVal_pair]
          rfl
        | unit => nomatch hGet
        | nat _ => nomatch hGet
        | bool _ => nomatch hGet
        | symBool _ => nomatch hGet
        | refVal _ _ => nomatch hGet
        | choice _ _ _ _ _ _ => nomatch hGet
      | succ _ => nomatch hGet

/-- `StdVal` aggregates are binary `.pair` nodes, which carry no data besides
their two fields. -/
def stdSameAggregateShape (v1 v2 : StdVal) : Bool :=
  match v1, v2 with
  | ⟨_, .pairBranch _ _ _ _⟩, ⟨_, .pairBranch _ _ _ _⟩ => true
  | _, _ => false

theorem stdVal_sameAggregateShape_ext (v1 v2 : StdVal)
    (hShape : stdSameAggregateShape v1 v2 = true)
    (hFields : ∀ f, stdValGetField f v1 = stdValGetField f v2) :
    v1 = v2 := by
  cases v1 with
  | mk f1 t1 =>
    cases v2 with
    | mk f2 t2 =>
      cases t1 <;> cases t2 <;>
        first
        | (have h0 := hFields 0
           have h1 := hFields 1
           injection h0 with h0'
           injection h1 with h1'
           cases h0'
           cases h1'
           rfl)
        | exact nomatch hShape

theorem stdVal_sameAggregateShape_setField (f : FieldIdx) (s a s' t : StdVal)
    (hShape : stdSameAggregateShape s t = true)
    (hPut : stdValSetField f s a = some s') :
    stdSameAggregateShape s' t = true := by
  cases s with
  | mk fs ts =>
    cases t with
    | mk ft tt =>
      cases ts <;> cases tt <;>
        first
        | (cases f with
           | zero =>
             injection hPut with hEq
             subst hEq
             rfl
           | succ f' =>
             cases f' with
             | zero =>
               injection hPut with hEq
               subst hEq
               rfl
             | succ _ => exact nomatch hPut)
        | exact nomatch hShape

/-- Handle decoding for `StdVal`: only `.refVal` leaves are handles. -/
def stdDecodeRef (v : StdVal) : Option (LoanId × SubPath) :=
  match v with
  | ⟨_, .refVal lid path⟩ => some (lid, path)
  | _ => none

theorem stdVal_decodeRef_getField (f : FieldIdx) (v : StdVal)
    (r : LoanId × SubPath) (hDec : stdDecodeRef v = some r) :
    stdValGetField f v = none := by
  cases v with
  | mk fv tv =>
    cases tv with
    | refVal _ _ =>
      cases f with
      | zero => rfl
      | succ f' => cases f' <;> rfl
    | unit => nomatch hDec
    | nat _ => nomatch hDec
    | bool _ => nomatch hDec
    | symBool _ => nomatch hDec
    | pairBranch _ _ _ _ => nomatch hDec
    | choice _ _ _ _ _ _ => nomatch hDec

/-- Guard and arms of a `StdVal` choice node. -/
def stdBranchSplit (v : StdVal) : Option (StdVal × StdVal × StdVal) :=
  match v with
  | ⟨_, .choice fc ft ff c vt vf⟩ => some (⟨fc, c⟩, ⟨ft, vt⟩, ⟨ff, vf⟩)
  | _ => none

theorem stdVal_decodeRef_branchSplit (v : StdVal) (r : LoanId × SubPath)
    (hDec : stdDecodeRef v = some r) : stdBranchSplit v = none := by
  cases v with
  | mk fv tv =>
    cases tv with
    | refVal _ _ => rfl
    | unit => nomatch hDec
    | nat _ => nomatch hDec
    | bool _ => nomatch hDec
    | symBool _ => nomatch hDec
    | pairBranch _ _ _ _ => nomatch hDec
    | choice _ _ _ _ _ _ => nomatch hDec

theorem stdVal_branchSplit_zipVal (cond vt vf : StdVal)
    (hSym : stdAsBool cond = none) :
    stdBranchSplit (zipStdVal cond vt vf) = some (cond, vt, vf) := by
  unfold zipStdVal
  rw [hSym]
  rfl

/-- Key of a `StdVal` condition that `stdSameCond` can compare: the tag of a
`.symBool` placeholder, the shape of every symbolic condition in this suite.
Other conditions get no key. -/
def stdCondKey (v : StdVal) : Option Bool :=
  match v with
  | ⟨_, .symBool b⟩ => some b
  | _ => none

theorem stdCondKey_eq (v : StdVal) (b : Bool) (h : stdCondKey v = some b) :
    v = .symBool b := by
  cases v with
  | mk fv tv =>
    cases tv with
    | symBool b' =>
      injection h with hb
      subst hb
      rfl
    | unit => nomatch h
    | nat _ => nomatch h
    | bool _ => nomatch h
    | pairBranch _ _ _ _ => nomatch h
    | refVal _ _ => nomatch h
    | choice _ _ _ _ _ _ => nomatch h

/-- Conservative condition equality for `StdVal`: equal keys (`stdCondKey`).
Conditions without a key are never reported equal. -/
def stdSameCond (c1 c2 : StdVal) : Bool :=
  match stdCondKey c1, stdCondKey c2 with
  | some b1, some b2 => stdBoolEq b1 b2
  | _, _ => false

theorem stdVal_sameCond_eq (c1 c2 : StdVal) (h : stdSameCond c1 c2 = true) :
    c1 = c2 := by
  unfold stdSameCond at h
  revert h
  cases h1 : stdCondKey c1 with
  | none =>
    intro h
    nomatch h
  | some b1 =>
    cases h2 : stdCondKey c2 with
    | none =>
      intro h
      nomatch h
    | some b2 =>
      intro h
      rw [stdCondKey_eq c1 b1 h1, stdCondKey_eq c2 b2 h2]
      cases b1 <;> cases b2 <;> first
        | rfl
        | nomatch h

theorem remapStdFuel_succ (oldLid newLid : LoanId) (k : Nat) (v : StdVal) :
    remapStdFuel oldLid newLid (k + 1) v =
      remapStdStep oldLid newLid (remapStdFuel oldLid newLid k) v :=
  rfl

/-- Any fuel at least the size of a value renames it completely. -/
theorem remapStdFuel_eq (oldLid newLid : LoanId) :
    ∀ {n : Nat} (tr : StdValTree n) (k : Nat), n ≤ k →
      remapStdFuel oldLid newLid k ⟨n, tr⟩ =
        remapStdVal oldLid newLid ⟨n, tr⟩ := by
  intro n tr
  induction tr with
  | unit =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ _ => rfl
  | nat _ =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ _ => rfl
  | bool _ =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ _ => rfl
  | symBool _ =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ _ => rfl
  | refVal _ _ =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ _ => rfl
  | pairBranch fl fr a b iha ihb =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ k' =>
      have hSub : fl + fr ≤ k' := Nat.le_of_succ_le_succ hLe
      have hL : fl ≤ fl + fr := Nat.le_add_right fl fr
      have hR : fr ≤ fl + fr := Nat.le_add_left fr fl
      change StdVal.pair (remapStdFuel oldLid newLid k' ⟨fl, a⟩)
          (remapStdFuel oldLid newLid k' ⟨fr, b⟩) =
        StdVal.pair (remapStdFuel oldLid newLid (fl + fr) ⟨fl, a⟩)
          (remapStdFuel oldLid newLid (fl + fr) ⟨fr, b⟩)
      rw [iha k' (Nat.le_trans hL hSub), ihb k' (Nat.le_trans hR hSub),
        iha _ hL, ihb _ hR]
  | choice fc ft ff c vt vf ihc iht ihf =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ k' =>
      have hSub : fc + ft + ff ≤ k' := Nat.le_of_succ_le_succ hLe
      have hC : fc ≤ fc + ft + ff :=
        Nat.le_trans (Nat.le_add_right fc ft) (Nat.le_add_right (fc + ft) ff)
      have hT : ft ≤ fc + ft + ff :=
        Nat.le_trans (Nat.le_add_left ft fc) (Nat.le_add_right (fc + ft) ff)
      have hF : ff ≤ fc + ft + ff := Nat.le_add_left ff (fc + ft)
      change StdVal.choice (remapStdFuel oldLid newLid k' ⟨fc, c⟩)
          (remapStdFuel oldLid newLid k' ⟨ft, vt⟩)
          (remapStdFuel oldLid newLid k' ⟨ff, vf⟩) =
        StdVal.choice (remapStdFuel oldLid newLid (fc + ft + ff) ⟨fc, c⟩)
          (remapStdFuel oldLid newLid (fc + ft + ff) ⟨ft, vt⟩)
          (remapStdFuel oldLid newLid (fc + ft + ff) ⟨ff, vf⟩)
      rw [ihc k' (Nat.le_trans hC hSub), iht k' (Nat.le_trans hT hSub),
        ihf k' (Nat.le_trans hF hSub), ihc _ hC, iht _ hT, ihf _ hF]

theorem remapStdVal_pair (oldLid newLid : LoanId) (a b : StdVal) :
    remapStdVal oldLid newLid (.pair a b) =
      .pair (remapStdVal oldLid newLid a) (remapStdVal oldLid newLid b) := by
  cases a with
  | mk fa ta =>
    cases b with
    | mk fb tb =>
      change StdVal.pair (remapStdFuel oldLid newLid (fa + fb) ⟨fa, ta⟩)
          (remapStdFuel oldLid newLid (fa + fb) ⟨fb, tb⟩) = _
      rw [remapStdFuel_eq oldLid newLid ta _ (Nat.le_add_right fa fb),
        remapStdFuel_eq oldLid newLid tb _ (Nat.le_add_left fb fa)]

theorem remapStdVal_choice (oldLid newLid : LoanId) (c vt vf : StdVal) :
    remapStdVal oldLid newLid (.choice c vt vf) =
      .choice (remapStdVal oldLid newLid c) (remapStdVal oldLid newLid vt)
        (remapStdVal oldLid newLid vf) := by
  cases c with
  | mk fc tc =>
    cases vt with
    | mk ft tt =>
      cases vf with
      | mk ff tf =>
        change StdVal.choice (remapStdFuel oldLid newLid (fc + ft + ff) ⟨fc, tc⟩)
            (remapStdFuel oldLid newLid (fc + ft + ff) ⟨ft, tt⟩)
            (remapStdFuel oldLid newLid (fc + ft + ff) ⟨ff, tf⟩) = _
        rw [remapStdFuel_eq oldLid newLid tc _
            (Nat.le_trans (Nat.le_add_right fc ft)
              (Nat.le_add_right (fc + ft) ff)),
          remapStdFuel_eq oldLid newLid tt _
            (Nat.le_trans (Nat.le_add_left ft fc)
              (Nat.le_add_right (fc + ft) ff)),
          remapStdFuel_eq oldLid newLid tf _ (Nat.le_add_left ff (fc + ft))]

theorem remapStdVal_refVal (oldLid newLid lid : LoanId) (path : SubPath) :
    remapStdVal oldLid newLid (.refVal lid path) =
      .refVal (if lid == oldLid then newLid else lid) path := by
  change (if lid == oldLid then StdVal.refVal newLid path
    else .refVal lid path) = _
  cases lid == oldLid <;> rfl

theorem stdVal_decodeRef_remapRefInVal (oldLid newLid : LoanId) (v : StdVal) :
    stdDecodeRef (remapStdVal oldLid newLid v) =
      (stdDecodeRef v).map
        (fun r => (if r.1 == oldLid then newLid else r.1, r.2)) := by
  cases v with
  | mk fv tv =>
    cases tv with
    | unit => rfl
    | nat _ => rfl
    | bool _ => rfl
    | symBool _ => rfl
    | refVal lid path =>
      change stdDecodeRef (remapStdVal oldLid newLid (.refVal lid path)) = _
      rw [remapStdVal_refVal]
      rfl
    | pairBranch fl fr a b =>
      change stdDecodeRef (remapStdVal oldLid newLid (.pair ⟨fl, a⟩ ⟨fr, b⟩)) = _
      rw [remapStdVal_pair]
      rfl
    | choice fc ft ff c vt vf =>
      change stdDecodeRef (remapStdVal oldLid newLid
          (.choice ⟨fc, c⟩ ⟨ft, vt⟩ ⟨ff, vf⟩)) = _
      rw [remapStdVal_choice]
      rfl

theorem stdVal_branchSplit_remapRefInVal (oldLid newLid : LoanId)
    (v : StdVal) :
    stdBranchSplit (remapStdVal oldLid newLid v) =
      (stdBranchSplit v).map (fun s =>
        (remapStdVal oldLid newLid s.1, remapStdVal oldLid newLid s.2.1,
         remapStdVal oldLid newLid s.2.2)) := by
  cases v with
  | mk fv tv =>
    cases tv with
    | unit => rfl
    | nat _ => rfl
    | bool _ => rfl
    | symBool _ => rfl
    | refVal lid path =>
      change stdBranchSplit (remapStdVal oldLid newLid (.refVal lid path)) = _
      rw [remapStdVal_refVal]
      rfl
    | pairBranch fl fr a b =>
      change stdBranchSplit
          (remapStdVal oldLid newLid (.pair ⟨fl, a⟩ ⟨fr, b⟩)) = _
      rw [remapStdVal_pair]
      rfl
    | choice fc ft ff c vt vf =>
      change stdBranchSplit (remapStdVal oldLid newLid
          (.choice ⟨fc, c⟩ ⟨ft, vt⟩ ⟨ff, vf⟩)) = _
      rw [remapStdVal_choice]
      rfl

theorem stdVal_getField_remapRefInVal (oldLid newLid : LoanId) (f : FieldIdx)
    (v : StdVal) :
    stdValGetField f (remapStdVal oldLid newLid v) =
      (stdValGetField f v).map (remapStdVal oldLid newLid) := by
  cases v with
  | mk fv tv =>
    cases tv with
    | unit => cases f with | zero => rfl | succ f' => cases f' <;> rfl
    | nat _ => cases f with | zero => rfl | succ f' => cases f' <;> rfl
    | bool _ => cases f with | zero => rfl | succ f' => cases f' <;> rfl
    | symBool _ => cases f with | zero => rfl | succ f' => cases f' <;> rfl
    | refVal lid path =>
      change stdValGetField f
          (remapStdVal oldLid newLid (.refVal lid path)) = _
      rw [remapStdVal_refVal]
      cases f with
      | zero => rfl
      | succ f' => cases f' <;> rfl
    | pairBranch fl fr a b =>
      change stdValGetField f
          (remapStdVal oldLid newLid (.pair ⟨fl, a⟩ ⟨fr, b⟩)) = _
      rw [remapStdVal_pair]
      cases f with
      | zero => rfl
      | succ f' => cases f' <;> rfl
    | choice fc ft ff c vt vf =>
      change stdValGetField f (remapStdVal oldLid newLid
          (.choice ⟨fc, c⟩ ⟨ft, vt⟩ ⟨ff, vf⟩)) = _
      rw [remapStdVal_choice]
      cases f with
      | zero => rfl
      | succ f' => cases f' <;> rfl

theorem stdVal_remapRefInVal_leaf (oldLid newLid : LoanId) (v : StdVal)
    (hDec : stdDecodeRef v = none) (hFields : ∀ f, stdValGetField f v = none)
    (hSplit : stdBranchSplit v = none) : remapStdVal oldLid newLid v = v := by
  cases v with
  | mk fv tv =>
    cases tv with
    | unit => rfl
    | nat _ => rfl
    | bool _ => rfl
    | symBool _ => rfl
    | refVal _ _ => nomatch hDec
    | pairBranch _ _ _ _ => nomatch hFields 0
    | choice _ _ _ _ _ _ => nomatch hSplit

def stdSameRefVal (v1 v2 : StdVal) : Bool :=
  match v1, v2 with
  | ⟨_, .refVal l1 p1⟩, ⟨_, .refVal l2 p2⟩ =>
    Nat.beq l1 l2 && lensTestSubPathEq p1 p2
  | _, _ => false

theorem stdVal_sameRefVal_eq (v1 v2 : StdVal)
    (h : stdSameRefVal v1 v2 = true) : v1 = v2 := by
  cases v1 with
  | mk f1 t1 =>
    cases v2 with
    | mk f2 t2 =>
      cases t1 with
      | refVal l1 p1 =>
        cases t2 with
        | refVal l2 p2 =>
          change (Nat.beq l1 l2 && lensTestSubPathEq p1 p2) = true at h
          revert h
          cases hL : Nat.beq l1 l2 with
          | false =>
            intro h
            nomatch h
          | true =>
            intro hP
            rw [Nat.eq_of_beq_eq_true hL, lensTestSubPathEq_eq p1 p2 hP]
        | unit => nomatch h
        | nat _ => nomatch h
        | bool _ => nomatch h
        | symBool _ => nomatch h
        | pairBranch _ _ _ _ => nomatch h
        | choice _ _ _ _ _ _ => nomatch h
      | unit => nomatch h
      | nat _ => nomatch h
      | bool _ => nomatch h
      | symBool _ => nomatch h
      | pairBranch _ _ _ _ => nomatch h
      | choice _ _ _ _ _ _ => nomatch h

def stdValAlg : ValAlgebra StdVal where
  defaultVal := .unit
  asBool := stdAsBool
  zipVal := zipStdVal
  getField := stdValGetField
  getField_projectBranchVal := stdVal_getField_projectBranchVal
  setField := stdValSetField
  getField_setField := stdVal_getField_setField
  setField_getField := stdVal_setField_getField
  setField_setField := stdVal_setField_setField
  getField_setField_other := stdVal_getField_setField_other
  setField_setField_comm := stdVal_setField_setField_comm
  encodeRef lid path := .refVal lid path
  decodeRef := stdDecodeRef
  decodeRef_encodeRef _ _ := rfl
  decodeRef_encodeSharedRef _ _ := rfl
  decodeRef_getField := stdVal_decodeRef_getField
  branchSplit := stdBranchSplit
  decodeRef_branchSplit := stdVal_decodeRef_branchSplit
  branchSplit_zipVal := stdVal_branchSplit_zipVal
  sameCond := stdSameCond
  sameCond_eq := stdVal_sameCond_eq
  sameRefVal := stdSameRefVal
  sameRefVal_eq := stdVal_sameRefVal_eq
  remapRefInVal := remapStdVal
  decodeRef_remapRefInVal := stdVal_decodeRef_remapRefInVal
  getField_remapRefInVal := stdVal_getField_remapRefInVal
  branchSplit_remapRefInVal := stdVal_branchSplit_remapRefInVal
  remapRefInVal_leaf := stdVal_remapRefInVal_leaf
  projectBranchVal := projectBranchStdVal
  projectBranchVal_concrete := stdVal_projectBranchVal_concrete
  projectBranchVal_zip_true := stdVal_projectBranchVal_zip_true
  projectBranchVal_zip_false := stdVal_projectBranchVal_zip_false
  sizeBound v := v.fuel
  getField_lt_sizeBound := stdVal_getField_lt_sizeBound
  sameAggregateShape := stdSameAggregateShape
  sameAggregateShape_ext := stdVal_sameAggregateShape_ext
  sameAggregateShape_setField := stdVal_sameAggregateShape_setField

/-- Add a concrete left operand `n1` to `v2`, distributing across any nested
`.choice` nodes in `v2`. -/
def stdAddLeafNat (n1 : Nat) (v2 : StdVal) : Option StdVal :=
  natFold
    (fun _ => none)
    (fun _ ih w =>
      match w with
      | ⟨_, .nat n2⟩ => some (.nat (n1 + n2))
      | ⟨_, .choice fc ft ff c vt vf⟩ =>
        match ih ⟨ft, vt⟩, ih ⟨ff, vf⟩ with
        | some t', some f' => some (.choice ⟨fc, c⟩ t' f')
        | _, _ => none
      | _ => none)
    v2.fuel v2

/-- Add two `StdVal` numbers or symbolic choices of numbers, distributing
addition across arbitrary nested `.choice` trees and collapsing matching
choice guards on the same step via `stdValEq`. -/
def stdAdd (v1 v2 : StdVal) : Option StdVal :=
  natFold
    (fun _ _ => none)
    (fun _ ih w1 w2 =>
      match w1 with
      | ⟨_, .nat n1⟩ => stdAddLeafNat n1 w2
      | ⟨_, .choice fc1 ft1 ff1 c1 vt1 vf1⟩ =>
        match w2 with
        | ⟨_, .choice fc2 ft2 ff2 c2 vt2 vf2⟩ =>
          if stdValEq ⟨fc1, c1⟩ ⟨fc2, c2⟩ then
            match ih ⟨ft1, vt1⟩ ⟨ft2, vt2⟩, ih ⟨ff1, vf1⟩ ⟨ff2, vf2⟩ with
            | some t', some f' => some (.choice ⟨fc1, c1⟩ t' f')
            | _, _ => none
          else
            match ih ⟨ft1, vt1⟩ w2, ih ⟨ff1, vf1⟩ w2 with
            | some t', some f' => some (.choice ⟨fc1, c1⟩ t' f')
            | _, _ => none
        | _ =>
          match ih ⟨ft1, vt1⟩ w2, ih ⟨ff1, vf1⟩ w2 with
          | some t', some f' => some (.choice ⟨fc1, c1⟩ t' f')
          | _, _ => none
      | _ => none)
    v1.fuel v1 v2

def stdAddNat (k : Nat) (v : StdVal) : Option StdVal :=
  stdAdd v (.nat k)

def stdInc (v : StdVal) : Option StdVal :=
  stdAddNat 1 v

def stdLtSym (v1 v2 : StdVal) : Option StdVal :=
  match v1, v2 with
  | ⟨_, .nat n1⟩, ⟨_, .nat n2⟩ => some (.symBool (Nat.blt n1 n2))
  | _, _ => none

def stdLtBool (v1 v2 : StdVal) : Option StdVal :=
  match v1, v2 with
  | ⟨_, .nat n1⟩, ⟨_, .nat n2⟩ => some (.bool (Nat.blt n1 n2))
  | _, _ => none

/-! ## Shared Plan and Region Fixtures -/

/-- `true` iff running `plan` from the entry state of `params` fails (and the
entry state itself is valid). Tests use it to observe a failure at the step
that should fail, rather than only at the return boundary. -/
def planStepFails (params : List (ParamInput StdVal))
    (plan : FlowPlan StdVal) : Bool :=
  match initFnState stdValAlg params with
  | .ok st0 =>
    match evalPlan stdValAlg plan st0 with
    | .fail => true
    | .ok _ => false
  | .fail => false

/-- `.branchExplicitJoin` remaps distinct branch-local loan IDs (`2` in the
true arm vs. `3` in the false arm after a scratch loan `2` ends) into canonical
loan `2` at the join point. -/
def explicitJoinRemapLoanIdsPlan : FlowPlan StdVal :=
  .seq
    (.branchExplicitJoin (.use (.localSub 0 []))
      (.seq
        (.act (.borrow 3 .mutBorrow (.derefSub 1 [])))
        (.seq
          (.act (.borrow 4 .shared (.localSub 0 [])))
          (.act (.endLoan 3))))
      (.seq
        (.act (.borrow 3 .shared (.localSub 0 [])))
        (.seq
          (.act (.endLoan 2))
          (.act (.borrow 3 .mutBorrow (.derefSub 2 [])))))
      [(2, 3)])
    (.seq
      (.act (.assign (.derefSub 3 []) (.constVal (.nat 50))))
      (.act (.endLoan 2)))

/-- Symbolic branch joining two active region groups with matching metadata
merges their `backFn`s under `cond`, while mismatched region-group metadata
fails closed. -/
def regionSpecWithAdd (k : Nat) : RegionGroupSpec StdVal where
  groupId := 0
  requiredChildren := []
  inputPlaces := [.derefSub 1 []]
  outDsts := [2]
  fwdOuts := fun _ muts =>
    match muts with
    | [vx] => some [vx]
    | _ => none
  backFn := fun _ _ outVals _ =>
    match outVals with
    | [⟨_, .nat vOut⟩] => some ([.nat (vOut + k)], [])
    | _ => none

/-- Output-free region group `gid` requiring the groups `children`; its
callback accepts any deposits and deposits nothing. -/
def bareRegionSpec (gid : RegionGroupId)
    (children : List RegionGroupId) : RegionGroupSpec StdVal where
  groupId := gid
  requiredChildren := children
  inputPlaces := []
  outDsts := []
  fwdOuts := fun _ _ => some []
  backFn := fun _ _ _ _ => some ([], [])

/-- Output-free region group `gid` that locks `input`, writes the number of
deposits its backward function received back to `input`, and deposits `dep`.
-/
def countingRegionSpec (gid : RegionGroupId)
    (children : List RegionGroupId) (input : PlaceExpr)
    (dep : List StdVal := [.nat 9]) : RegionGroupSpec StdVal where
  groupId := gid
  requiredChildren := children
  inputPlaces := [input]
  outDsts := []
  fwdOuts := fun _ _ => some []
  backFn := fun _ _ _ deps => some ([.nat deps.length], dep)

end Anneal.PureLift
