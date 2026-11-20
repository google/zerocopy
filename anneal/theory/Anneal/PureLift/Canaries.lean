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

/-!
## Part I: Core Borrow and Control-Flow Scenarios (`S1`–`S7`)
-/

/-- **S1 (`max_assign`)**: `if *x < y { *x = y }`. -/
def s1MaxAssignPlan : FlowPlan StdVal :=
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
def s2UpdateMinPlan : FlowPlan StdVal :=
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
def s3SharedMaxPlan : FlowPlan StdVal :=
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
def s4DiamondReborrowPlan : FlowPlan StdVal :=
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
def s5ChoosePlan : FlowPlan StdVal :=
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

def chooseCallSummary : CallSummary StdVal where
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

def choosePairLens (cond : Bool) : Lens (StdVal × StdVal) StdVal where
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

def s5ChooseCallerPlan : FlowPlan StdVal :=
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
def s6CountUpPlan (fuel : Nat) : FlowPlan StdVal :=
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
def addInPlaceSummary : CallSummary StdVal where
  returnsMutBorrow := false
  fwd pureVals mutVals :=
    match pureVals, mutVals with
    | [⟨_, .nat _⟩], [⟨_, .nat _⟩] => some .unit
    | _, _ => none
  back pureVals mutVals _ :=
    match pureVals, mutVals with
    | [⟨_, .nat d⟩], [⟨_, .nat x⟩] => some [.nat (x + d)]
    | _, _ => none

def s7DoubleCallPlan : FlowPlan StdVal :=
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
def h1SplitSwapEnd12Plan : FlowPlan StdVal :=
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
def h1SplitSwapEnd21Plan : FlowPlan StdVal :=
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

def h1SharedAndMutSiblingsPlan : FlowPlan StdVal :=
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

def h1MultiSharedLoanIdTrackingPlan : FlowPlan StdVal :=
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

def h1BadMutWhileSecondSharedActivePlan : FlowPlan StdVal :=
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

def h1BadBorrowRootWhileFieldActivePlan : FlowPlan StdVal :=
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

def h1BadBorrowSubpathWhilePrefixActivePlan : FlowPlan StdVal :=
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
def h2DependentRegionSpecs : List (RegionGroupSpec StdVal) :=
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

def h2ValidMultiRegionPlan : FlowPlan StdVal :=
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

def h2BadOutOfOrderRegionPlan : FlowPlan StdVal :=
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

def h2BadEndRegionWhileOutputReborrowedPlan : FlowPlan StdVal :=
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

def h2ThreeLevelReborrowPlan : FlowPlan StdVal :=
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
def h3HybridSpatialSiblingPlan (vSpatialNew : Nat) : FlowPlan StdVal :=
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

def h3BadPureWriteWhileSpatialPinnedPlan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 1 .mutBorrow (.derefSub 0 [0])))
    (.seq
      (.act (.freezeSpatial 1 valueCellCodec))
      (.act (.assign (.derefSub 1 []) (.constVal (.nat 99)))))

def h3BadEndLoanWhileSpatialPinnedPlan : FlowPlan StdVal :=
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

def h3BadUninitReabsorbPlan : FlowPlan StdVal :=
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
def h4MaxAssignConcretePlan : FlowPlan StdVal :=
  .seq
    (.act (.assign (.localSub 2 [])
      (.binary stdLtBool (.derefSub 0 []) (.localSub 1 []))))
    (.branch (.use (.localSub 2 []))
      (.act (.assign (.derefSub 0 []) (.use (.localSub 1 []))))
      .skip)

/-- `max_assign` machine state `(pc, x, y)` at entry (`pc = 0`) agrees with
the symbolic state on `*x` and `y`. -/
def h4MaxAssignStateRel (st : SymState StdVal) (s : Nat × Nat × Nat) : Prop :=
  s.1 = 0 ∧
    readPlaceVal stdValAlg (.derefSub 0 []) st = some (.nat s.2.1) ∧
    readPlaceVal stdValAlg (.localSub 1 []) st = some (.nat s.2.2)

/-- `max_assign` as an `M1` step function: step `0` assigns `x := y` when
`x < y`, and step `1` returns the final `*x`. -/
def m1MaxAssignStep : Nat × Nat × Nat → M1StepResult (Nat × Nat × Nat) StdVal
  | (0, x, y) =>
    .next (1,
      (match Nat.blt x y with
       | true => y
       | false => x), y)
  | (1, x, _) => .ret ⟨.unit, [.nat x]⟩
  | _ => .fault

/-- `max_assign` as an `M2` step function that also emits the inputs it
compares as observations. -/
def m2MaxAssignStep :
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

def m3SwapHeapStep (cells : List (M3Cell StdVal)) :
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
def h5EarlyReturnNestedSubBorrowsPlan : FlowPlan StdVal :=
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

def h5GoodhartEarlyReturnUnendedLoanPlan : FlowPlan StdVal :=
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

def h5GoodhartOutOfOrderEndLoanPlan : FlowPlan StdVal :=
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

def h5GoodhartDoubleEndLoanPlan : FlowPlan StdVal :=
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

def h5GoodhartUnendedLoanAtReturnPlan : FlowPlan StdVal :=
  .act (.borrow 1 .mutBorrow (.derefSub 0 [0]))

theorem h5_goodhart_unended_loan_at_normal_return_fails (v0 v1 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      h5GoodhartUnendedLoanAtReturnPlan
      (.constVal .unit) = .fail := rfl

def h5GoodhartReadLocalWhileMutBorrowedPlan : FlowPlan StdVal :=
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

def h5GoodhartAliasedBranchJoinPlan : FlowPlan StdVal :=
  .branchExplicitJoin (.use (.localSub 0 []))
    .skip
    .skip
    [(1, 2), (1, 3)]

theorem h5_goodhart_aliased_branch_join_fails (cond : Bool) :
    evalFnValue stdValAlg
      [⟨.byVal, .symBool cond⟩]
      h5GoodhartAliasedBranchJoinPlan
      (.constVal .unit) = .fail := rfl

/-! ## Part III: Plan, BlockCfg, and Adapter Edge Cases -/

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

/-! ### Field Joins, Uninitialized Locals, Handles, and Writeback Ownership -/

/-- Field-index map for `gapStdValAlg`: field `1` is a pair's first component,
field `2` its second, and index `0` is a gap. -/
def gapIdx (f : FieldIdx) : Option FieldIdx :=
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

def gapGetField (f : FieldIdx) (v : StdVal) : Option StdVal :=
  match gapIdx f with
  | some i => stdValGetField i v
  | none => none

def gapSetField (f : FieldIdx) (v child : StdVal) : Option StdVal :=
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

def gapStdValAlg : ValAlgebra StdVal :=
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
def writebackSummary (out : StdVal) : CallSummary StdVal where
  returnsMutBorrow := false
  fwd _ _ := some .unit
  back _ _ _ := some [out]

/-- Freeze loan `1` (a reborrow of `*p`), overwrite its spatial cell with
`cell`, and reabsorb it. -/
def spatialOverwritePlan (cell : StdVal) : FlowPlan StdVal :=
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
def writeRegionSpec (gid : RegionGroupId) (input : PlaceExpr)
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
def unevenExplicitJoinPlan : FlowPlan StdVal :=
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
def choiceOverHandlesPlan : FlowPlan StdVal :=
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
def trueArmScratchPlan : FlowPlan StdVal :=
  .seq
    (.branchExplicitJoin (.use (.localSub 0 []))
      (.seq (.act (.borrow 3 .shared (.localSub 2 [])))
        (.seq (.act (.endLoan 1))
          (.act (.borrow 3 .mutBorrow (.derefSub 1 [])))))
      (.act (.borrow 3 .mutBorrow (.derefSub 1 [])))
      [(2, 1)])
    (.act (.endLoan 2))

/-- `true` iff `endLoanInState` succeeds on `st`. -/
def endLoanOk (lid : LoanId) (st : SymState StdVal) : Bool :=
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
def swappedChoiceState (outs : List StdVal) : SymState StdVal :=
  let c : StdVal := .symBool true
  ⟨[⟨zipStdVal c (.refVal 3 []) (.refVal 4 []), .mutLocked 5⟩,
    ⟨zipStdVal c (.refVal 4 []) (.refVal 3 []), .mutLocked 5⟩],
   [⟨3, .activeMut, ⟨.nat 30, .unborrowed⟩, .rootParam 3⟩,
    ⟨4, .activeMut, ⟨.nat 40, .unborrowed⟩, .rootParam 4⟩,
    ⟨5, .ended, ⟨.unit, .unborrowed⟩, .regionOut 0 0⟩],
   [⟨0, true, 5, [(.localReg 0, []), (.localReg 1, [])], [], [],
     fun _ _ => some (outs, [])⟩], [], [], 0⟩

/-- `true` iff ending region group `0` succeeds on `st`. -/
def endGroup0Ok (st : SymState StdVal) : Bool :=
  match endRegionGroupInState stdValAlg 0 st with
  | .ok _ => true
  | .fail => false

/-- Local `0` is split between loan `1` at `[0]` and loan `2` at `[0, 1]`, and
locals `1` and `2` are borrowed by loans `1` and `2`; `t1` and `t2` are the
loans' targets. -/
def correlatedOverlapState (t1 t2 : BackTarget LensTestVal) :
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
def endLoan1Ok (st : SymState LensTestVal) : Bool :=
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
def endLoansInOrderOk (a b : LoanId) (st : SymState LensTestVal) : Bool :=
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
def retargetAllRemap (_ t : LoanId) (v : StdVal) : StdVal :=
  match v with
  | ⟨_, .refVal _ p⟩ => .refVal t p
  | other => other

/-- Handle renaming that also changes non-handle data: it adds `1000` to every
top-level number. -/
def bumpNatRemap (oldLid newLid : LoanId) (v : StdVal) : StdVal :=
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
def explicitJoinRenamePlan : FlowPlan StdVal :=
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
def swappedLoanIdsJoinPlan : FlowPlan StdVal :=
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
def deadRefExplicitJoinPlan : FlowPlan StdVal :=
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
def twoReborrowsState (swapped : Bool) : SymState StdVal :=
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
def opaqueRefStdValAlg : ValAlgebra StdVal :=
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
