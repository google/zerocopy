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

namespace Anneal.PureLift

/-!
# Bidirectional Lenses, Sub-Place Paths, and Value Algebra

Foundational definitions for the `PureLift` functional transformation. Inspired
by prior art in Aeneas (Ho and Protzenko, ICFP 2022), `PureLift` lifts
imperative programs with borrows, nested projections, and structured or
block-based control flow into pure functional computations.

This module defines:
- `EvalOutcome` and `HoldsFnSpec`: total evaluation outcomes where `.fail` maps
  to `False`, preventing vacuous truth on ill-formed borrow plans.
- `Lens` and `LawfulLens`: partial bidirectional lenses with identity and
  composition laws.
- `ValAlgebra`: the language-agnostic value interface supporting aggregate
  field projection, reference-handle encoding, boolean extraction, and
  conditional symbolic value merging.
-/

abbrev LocalId := Nat
abbrev LoanId := Nat
abbrev RegionGroupId := Nat
abbrev BlockId := Nat
abbrev FieldIdx := Nat
abbrev SubPath := List FieldIdx

/-- Fixed-depth call-by-name combinators (`fix4`, `fix8`, `fix16`).
Unlike `Nat.recCompiled` (`Nat.brecOn`) or `List.foldr` (`List.brecOn`), which
reduce the recursion spine in head position before inspecting the target value,
`fix8 step base x` places `step` directly in head position (`step (...) x`).
Consequently, base cases (`.unborrowed`, `.direct`, `.act`, `0`) discard the
recursive continuation `ih` in $O(1)$ `whnf` steps without emitting
compiler-only `_unsafe_rec` declarations. -/
def fix2 {α : Type} (step : α → α) (base : α) : α :=
  step (step base)

def fix4 {α : Type} (step : α → α) (base : α) : α :=
  fix2 step (fix2 step base)

def fix8 {α : Type} (step : α → α) (base : α) : α :=
  fix4 step (fix4 step base)

def fix16 {α : Type} (step : α → α) (base : α) : α :=
  fix8 step (fix8 step base)

/-- Total structural recursion on `Nat` indices via `@Nat.recCompiled`, avoiding
bounded fuel truncation at indices above eight while emitting zero
compiler-only `_unsafe_rec` declarations. -/
def natFold {α : Type} (zero : α) (succ : Nat → α → α) (n : Nat) : α :=
  @Nat.recCompiled (fun _ => α) zero succ n

/-- Total structural recursion on `List` spines via `List.foldr`, passing the
actual remaining list tail to `cons` and avoiding bounded fuel truncation on
lists longer than eight elements while emitting zero compiler-only
`_unsafe_rec` declarations. -/
def listFold {α β : Type} (nil : β) (cons : α → List α → β → β)
    (xs : List α) : β :=
  match
    xs.foldr
      (fun x (acc : List α × β) =>
        match acc with
        | (tail, ih) => (x :: tail, cons x tail ih))
      ([], nil)
  with
  | (_, res) => res

/-- Total evaluation outcome for `PureLift` plan execution.

Any borrow violation, aliasing conflict, unended loan at function return,
out-of-order region group termination, uninitialized spatial cell upon
reabsorption, or insufficient loop fuel evaluates to `.fail`. -/
inductive EvalOutcome (α : Type) where
  | ok (val : α)
  | fail

/-- Specification lifting predicate over `EvalOutcome`.

Mapping `.fail` to `False` guarantees that a proved specification always
witnesses successful evaluation without borrow or safety faults. -/
def HoldsFnSpec {α : Type} (out : EvalOutcome α) (post : α → Prop) : Prop :=
  match out with
  | .ok res => post res
  | .fail => False

theorem holdsFnSpec_not_fail {α : Type} (post : α → Prop) :
    ¬ HoldsFnSpec (.fail : EvalOutcome α) post :=
  fun h => h

/-- Pure functional output of a lifted function: pairs the direct return value
`ret` with the updated final values `mutFinals` of all external mutable-borrow
input parameters in declaration order. -/
structure FuncOut (Val : Type) where
  ret : Val
  mutFinals : List Val

/-- Partial bidirectional lens between an aggregate state `S` and a focused
view `A`. -/
structure Lens (S A : Type) where
  get : S → Option A
  put : S → A → Option S

/-- Well-behavedness laws (`get_put`, `put_get`, `put_put`) for a partial
bidirectional lens. -/
structure LawfulLens (S A : Type) (l : Lens S A) : Prop where
  get_put : ∀ s a, l.get s = some a → l.put s a = some s
  put_get : ∀ s a s', l.put s a = some s' → l.get s' = some a
  put_put : ∀ s a1 a2 s1, l.put s a1 = some s1 → l.put s1 a2 = l.put s a2

/-- Identity lens on `S`. -/
def Lens.id (S : Type) : Lens S S where
  get s := some s
  put _ a := some a

/-- Sequential composition of partial lenses `l1 : Lens S A` and
`l2 : Lens A B`. -/
def Lens.comp {S A B : Type} (l1 : Lens S A) (l2 : Lens A B) : Lens S B where
  get s :=
    match l1.get s with
    | some a => l2.get a
    | none => none
  put s b :=
    match l1.get s with
    | some a =>
      match l2.put a b with
      | some a' => l1.put s a'
      | none => none
    | none => none

theorem Lens.id_lawful (S : Type) : LawfulLens S S (Lens.id S) where
  get_put := by
    intro s a h
    injection h with hEq
    subst hEq
    rfl
  put_get := by
    intro s a s' h
    injection h with hEq
    subst hEq
    rfl
  put_put := by
    intro s a1 a2 s1 h
    injection h with hEq
    subst hEq
    rfl

theorem Lens.comp_lawful {S A B : Type} (l1 : Lens S A) (l2 : Lens A B)
    (h1 : LawfulLens S A l1) (h2 : LawfulLens A B l2) :
    LawfulLens S B (Lens.comp l1 l2) where
  get_put := by
    intro s b hGet
    dsimp [Lens.comp] at hGet
    dsimp [Lens.comp]
    revert hGet
    cases hG1 : l1.get s with
    | none =>
      intro hFalse
      nomatch hFalse
    | some a =>
      dsimp
      intro hG2
      rw [h2.get_put a b hG2]
      dsimp
      exact h1.get_put s a hG1
  put_get := by
    intro s b s' hPut
    dsimp [Lens.comp] at hPut
    dsimp [Lens.comp]
    revert hPut
    cases hG1 : l1.get s with
    | none =>
      intro hFalse
      nomatch hFalse
    | some a =>
      dsimp
      cases hP2 : l2.put a b with
      | none =>
        intro hFalse
        nomatch hFalse
      | some a' =>
        dsimp
        intro hP1
        rw [h1.put_get s a' s' hP1]
        dsimp
        exact h2.put_get a b a' hP2
  put_put := by
    intro s b1 b2 s1 hPut1
    dsimp [Lens.comp] at hPut1
    dsimp [Lens.comp]
    revert hPut1
    cases hG1 : l1.get s with
    | none =>
      intro hFalse
      nomatch hFalse
    | some a =>
      dsimp
      cases hP2 : l2.put a b1 with
      | none =>
        intro hFalse
        nomatch hFalse
      | some a1 =>
        dsimp
        intro hP1
        rw [h1.put_get s a1 s1 hP1]
        dsimp
        rw [h2.put_put a b1 b2 a1 hP2]
        cases l2.put a b2 with
        | none => rfl
        | some a2 =>
          dsimp
          exact h1.put_put s a1 a2 s1 hP1

/-- Language-agnostic value algebra equipping a carrier type `Val` with:
- `defaultVal`: default value for unallocated local slots,
- `asBool`: concrete boolean extraction for branch and loop conditions,
- `zipVal`, `projectBranchVal`, and the three branch-projection laws
  (`projectBranchVal_concrete`, `projectBranchVal_zip_true`,
  `projectBranchVal_zip_false`): symbolic conditional merge at diamond
  control-flow joins and lawful branch-specific value projection,
- `getField`, `setField`, the three bidirectional field-lens laws
  (`getField_setField`, `setField_getField`, `setField_setField`), the
  separation law `getField_setField_other`, and the commutation law
  `setField_setField_comm`: aggregate child projection and update by index.
  The separation law makes distinct field indices name distinct storage, so
  updating one field leaves every other field unchanged; borrow checking relies
  on it when it treats syntactically disjoint sub-paths as non-overlapping. The
  commutation law makes updates of distinct fields order-independent as whole
  values, including any data that `getField` does not expose, so lens and
  region writebacks to disjoint targets give the same owner value in either
  order,
- `encodeRef`, `encodeSharedRef`, `decodeRef`, and `decodeRefIsShared`:
  first-order borrow handle representation. The laws `decodeRef_encodeRef` and
  `decodeRef_encodeSharedRef` make decoding invert encoding, so a handle that
  a borrow stores names exactly the loan and sub-path it was created for, while
  `decodeRefIsShared_encodeSharedRef` and `decodeRefIsShared_encodeRef` ensure
  that whenever `encodeSharedRef` and `encodeRef` differ, `decodeRefIsShared`
  distinguishes shared-form from mutable-form handle encodings. The
  laws `decodeRef_getField` and `decodeRef_branchSplit` make a handle a leaf:
  a value that decodes as a handle has no fields and no branch arms,
- `branchSplit` and its law `branchSplit_zipVal`: the guard and the two arms
  of a symbolic `zipVal` choice. The arms are not fields, but
  `projectBranchVal` can expose them again, so a scan for borrow handles must
  visit them too. Every choice guard must itself be handle-free, so
  `branchSplit` can never expose a borrow handle hidden inside a guard,
- `remapRefInVal oldLid newLid` and its four laws: renaming the handles to loan
  `oldLid` inside a value into handles to `newLid` (explicit branch joins use
  it to give loans a common ID). A handle is renamed if it names `oldLid` and
  kept otherwise (`decodeRef_remapRefInVal`); fields, and the guard and arms
  of a choice, are renamed recursively (`getField_remapRefInVal` and
  `branchSplit_remapRefInVal`); and a value with no handle, field, or arm is
  unchanged (`remapRefInVal_leaf`). Together, the laws fix everything about
  the result that `decodeRef`, `getField`, and `branchSplit` can observe. They
  do not constrain data that those operations do not expose, such as an
  aggregate's tag or what a handle records besides its loan and sub-path,
- `sameCond` and its law `sameCond_eq`: a conservative test that two
  conditions are the same value, and so take the same truth value in every
  branch. Handle accounting and borrow checks use it to follow correlated
  choices branch by branch. An algebra may always answer `false`, which makes
  those checks treat every choice as independent,
- `sizeBound` and its law `getField_lt_sizeBound`: a strict upper bound on
  every field index of a value (the law) and an upper bound on its aggregate
  nesting depth. A traversal that enumerates fields (such as the handle scan
  behind `copyableVal`) can visit every index below `sizeBound`, and the law
  makes it complete; no fixed depth or width cutoff applies. A value nested
  more deeply than its bound exhausts the traversal budget, and the traversal
  must then fail closed or fall back to a conservative result.
- `sameAggregateShape` and its two laws (`sameAggregateShape_ext`,
  `sameAggregateShape_setField`): a conservative test that two aggregates
  differ at most in their fields. If it holds and every field agrees, the
  values are equal (`sameAggregateShape_ext`), so neither can carry tags or
  other non-field data that the other lacks; and updating a field of the first
  value keeps the relation (`sameAggregateShape_setField`). Together, the laws
  let a client rebuild one related value from the other exactly, by field
  updates alone. An algebra may always answer `false`, which leaves a client
  no such rebuild,
- `sameRefVal` and its law `sameRefVal_eq`: a conservative test that two
  encoded reference values are equal as full `Val` values (including any
  non-decoded handle data such as mutability, generation, or reborrow depth).
  Branch joins collapse two reference values to the first only when
  `sameRefVal` holds; an algebra may always answer `false`, which preserves
  the conditional `zipVal` value. -/
structure ValAlgebra (Val : Type) where
  defaultVal : Val
  asBool : Val → Option Bool
  zipVal : Val → Val → Val → Val
  projectBranchVal : Val → Bool → Val → Val := fun _ _ v => v
  projectBranchVal_concrete :
    ∀ (cond : Val) (b branch : Bool) (v : Val),
      asBool cond = some b → projectBranchVal cond branch v = v
  projectBranchVal_zip_true :
    ∀ (cond vt vf : Val),
      asBool cond = none →
      projectBranchVal cond true (zipVal cond vt vf) =
        projectBranchVal cond true vt
  projectBranchVal_zip_false :
    ∀ (cond vt vf : Val),
      asBool cond = none →
      projectBranchVal cond false (zipVal cond vt vf) =
        projectBranchVal cond false vf
  getField : FieldIdx → Val → Option Val
  getField_projectBranchVal :
    ∀ (cond : Val) (branch : Bool) (f : FieldIdx) (s a : Val),
      getField f s = some a →
      getField f (projectBranchVal cond branch s) =
        some (projectBranchVal cond branch a) := by
    intro _ _ _ _ _ hGet
    exact hGet
  setField : FieldIdx → Val → Val → Option Val
  getField_setField :
    ∀ (f : FieldIdx) (s a : Val),
      getField f s = some a → setField f s a = some s
  setField_getField :
    ∀ (f : FieldIdx) (s a s' : Val),
      setField f s a = some s' → getField f s' = some a
  setField_setField :
    ∀ (f : FieldIdx) (s a1 a2 s1 : Val),
      setField f s a1 = some s1 → setField f s1 a2 = setField f s a2
  getField_setField_other :
    ∀ (f g : FieldIdx) (s a s' : Val),
      f ≠ g → setField f s a = some s' → getField g s' = getField g s
  setField_setField_comm :
    ∀ (f g : FieldIdx) (s a b s1 s2 : Val),
      f ≠ g → setField f s a = some s1 → setField g s1 b = some s2 →
      Exists fun s1' => setField g s b = some s1' ∧ setField f s1' a = some s2
  encodeRef : LoanId → SubPath → Val
  encodeSharedRef : LoanId → SubPath → Val := encodeRef
  decodeRef : Val → Option (LoanId × SubPath)
  decodeRefIsShared : Val → Bool := fun _ => true
  decodeRef_encodeRef :
    ∀ (lid : LoanId) (path : SubPath),
      decodeRef (encodeRef lid path) = some (lid, path)
  decodeRef_encodeSharedRef :
    ∀ (lid : LoanId) (path : SubPath),
      decodeRef (encodeSharedRef lid path) = some (lid, path)
  decodeRefIsShared_encodeSharedRef :
    ∀ (lid : LoanId) (path : SubPath),
      decodeRefIsShared (encodeSharedRef lid path) = true := by
    intro _ _
    rfl
  decodeRefIsShared_encodeRef :
    ∀ (lid : LoanId) (path : SubPath),
      encodeSharedRef lid path = encodeRef lid path ∨
      decodeRefIsShared (encodeRef lid path) = false := by
    intro _ _
    exact Or.inl rfl
  decodeRef_getField :
    ∀ (f : FieldIdx) (v : Val) (r : LoanId × SubPath),
      decodeRef v = some r → getField f v = none
  branchSplit : Val → Option (Val × Val × Val)
  decodeRef_branchSplit :
    ∀ (v : Val) (r : LoanId × SubPath),
      decodeRef v = some r → branchSplit v = none
  branchSplit_zipVal :
    ∀ (cond vt vf : Val), asBool cond = none →
      branchSplit (zipVal cond vt vf) = some (cond, vt, vf)
  sameCond : Val → Val → Bool
  sameCond_eq : ∀ (c1 c2 : Val), sameCond c1 c2 = true → c1 = c2
  sameRefVal : Val → Val → Bool := fun _ _ => false
  sameRefVal_eq : ∀ (r1 r2 : Val), sameRefVal r1 r2 = true → r1 = r2 := by
    intro _ _ h
    nomatch h
  remapRefInVal : LoanId → LoanId → Val → Val
  decodeRef_remapRefInVal :
    ∀ (oldLid newLid : LoanId) (v : Val),
      decodeRef (remapRefInVal oldLid newLid v) =
        (decodeRef v).map
          (fun r => (if r.1 == oldLid then newLid else r.1, r.2))
  getField_remapRefInVal :
    ∀ (oldLid newLid : LoanId) (f : FieldIdx) (v : Val),
      getField f (remapRefInVal oldLid newLid v) =
        (getField f v).map (remapRefInVal oldLid newLid)
  branchSplit_remapRefInVal :
    ∀ (oldLid newLid : LoanId) (v : Val),
      branchSplit (remapRefInVal oldLid newLid v) =
        (branchSplit v).map (fun s =>
          (remapRefInVal oldLid newLid s.1, remapRefInVal oldLid newLid s.2.1,
           remapRefInVal oldLid newLid s.2.2))
  remapRefInVal_leaf :
    ∀ (oldLid newLid : LoanId) (v : Val),
      decodeRef v = none → (∀ f, getField f v = none) → branchSplit v = none →
      remapRefInVal oldLid newLid v = v
  sizeBound : Val → Nat
  getField_lt_sizeBound :
    ∀ (f : FieldIdx) (v c : Val),
      getField f v = some c → f < sizeBound v ∧ sizeBound c < sizeBound v
  sameAggregateShape : Val → Val → Bool
  sameAggregateShape_ext :
    ∀ (v1 v2 : Val),
      sameAggregateShape v1 v2 = true →
      (∀ f, getField f v1 = getField f v2) → v1 = v2
  sameAggregateShape_setField :
    ∀ (f : FieldIdx) (s a s' t : Val),
      sameAggregateShape s t = true → setField f s a = some s' →
      sameAggregateShape s' t = true

/-- Single-step field projection lens induced by `alg` at field index `f`. -/
def fieldLens {Val : Type} (alg : ValAlgebra Val) (f : FieldIdx) :
    Lens Val Val where
  get v := alg.getField f v
  put v sub := alg.setField f v sub

/-- Every `alg : ValAlgebra Val` induces a lawful single-step `fieldLens` at
every field index `f : FieldIdx`. -/
theorem fieldLens_lawful {Val : Type} (alg : ValAlgebra Val) (f : FieldIdx) :
    LawfulLens Val Val (fieldLens alg f) where
  get_put := alg.getField_setField f
  put_get := alg.setField_getField f
  put_put := alg.setField_setField f

/-- Read the nested sub-value at `SubPath` inside `v`. -/
def getPath {Val : Type} (alg : ValAlgebra Val) (path : SubPath) (v : Val) :
    Option Val :=
  path.foldr
    (fun f ih v0 =>
      match alg.getField f v0 with
      | some child => ih child
      | none => none)
    (fun v0 => some v0)
    v

/-- Update the nested sub-value at `SubPath` inside `vOld` to `vNew`. -/
def putPath {Val : Type} (alg : ValAlgebra Val) (path : SubPath)
    (vOld vNew : Val) : Option Val :=
  path.foldr
    (fun f ih vO vN =>
      match alg.getField f vO with
      | some childOld =>
        match ih childOld vN with
        | some childNew => alg.setField f vO childNew
        | none => none
      | none => none)
    (fun _ vN => some vN)
    vOld vNew

/-- Bidirectional lens focusing on the nested sub-place at `path`. -/
def subPathLens {Val : Type} (alg : ValAlgebra Val) (path : SubPath) :
    Lens Val Val where
  get v := getPath alg path v
  put v sub := putPath alg path v sub

/-- Every `alg : ValAlgebra Val` induces a lawful `subPathLens alg path` for
every nested projection path `path : SubPath`. -/
theorem subPathLens_lawful {Val : Type} (alg : ValAlgebra Val) :
    ∀ path : SubPath, LawfulLens Val Val (subPathLens alg path)
  | [] => Lens.id_lawful Val
  | f :: ps =>
    Lens.comp_lawful (fieldLens alg f) (subPathLens alg ps)
      (fieldLens_lawful alg f) (subPathLens_lawful alg ps)

/-- Updating the sub-place at `pre ++ f :: p` leaves the value at every
sub-place `pre ++ g :: q` with `f ≠ g` unchanged. Two sub-paths that diverge at
some index therefore name disjoint storage, which is what borrow checking
assumes when it treats them as non-overlapping. The proof uses
`getField_setField_other` at the diverging index and `setField_getField` on
the shared prefix. -/
theorem getPath_putPath_diverging {Val : Type} (alg : ValAlgebra Val)
    (f g : FieldIdx) (p q : SubPath) (hNe : f ≠ g) :
    ∀ (pre : SubPath) (s v s' : Val),
      putPath alg (pre ++ f :: p) s v = some s' →
      getPath alg (pre ++ g :: q) s' = getPath alg (pre ++ g :: q) s := by
  intro pre
  induction pre with
  | nil =>
    intro s v s' hPut
    change
      (match alg.getField f s with
       | some childOld =>
         match putPath alg p childOld v with
         | some childNew => alg.setField f s childNew
         | none => none
       | none => none) = some s' at hPut
    change
      (match alg.getField g s' with
       | some child => getPath alg q child
       | none => none) =
      (match alg.getField g s with
       | some child => getPath alg q child
       | none => none)
    revert hPut
    cases alg.getField f s with
    | none =>
      intro hFalse
      nomatch hFalse
    | some childOld =>
      dsimp only
      cases putPath alg p childOld v with
      | none =>
        intro hFalse
        nomatch hFalse
      | some childNew =>
        intro hSet
        rw [alg.getField_setField_other f g s childNew s' hNe hSet]
  | cons x pre ih =>
    intro s v s' hPut
    change
      (match alg.getField x s with
       | some childOld =>
         match putPath alg (pre ++ f :: p) childOld v with
         | some childNew => alg.setField x s childNew
         | none => none
       | none => none) = some s' at hPut
    change
      (match alg.getField x s' with
       | some child => getPath alg (pre ++ g :: q) child
       | none => none) =
      (match alg.getField x s with
       | some child => getPath alg (pre ++ g :: q) child
       | none => none)
    revert hPut
    cases alg.getField x s with
    | none =>
      intro hFalse
      nomatch hFalse
    | some childOld =>
      dsimp only
      cases hRec : putPath alg (pre ++ f :: p) childOld v with
      | none =>
        intro hFalse
        nomatch hFalse
      | some childNew =>
        intro hSet
        rw [alg.setField_getField x s childNew s' hSet]
        exact ih childOld v childNew hRec

/-- Updates of two sub-paths that diverge at their first index commute as whole
values: if `putPath (f :: p)` followed by `putPath (g :: q)` succeeds with
`f ≠ g`, the opposite order succeeds with the same result. This is the
order-independence that lens and region writebacks need when they update
disjoint targets of one owner; it follows from `getField_setField_other` and
`setField_setField_comm`. -/
theorem putPath_putPath_diverging_comm {Val : Type} (alg : ValAlgebra Val)
    (f g : FieldIdx) (p q : SubPath) (hNe : f ≠ g) (s v w s1 s2 : Val)
    (hP : putPath alg (f :: p) s v = some s1)
    (hQ : putPath alg (g :: q) s1 w = some s2) :
    Exists fun s1' =>
      putPath alg (g :: q) s w = some s1' ∧
      putPath alg (f :: p) s1' v = some s2 := by
  change
    (match alg.getField f s with
     | some childOld =>
       match putPath alg p childOld v with
       | some childNew => alg.setField f s childNew
       | none => none
     | none => none) = some s1 at hP
  change
    (match alg.getField g s1 with
     | some childOld =>
       match putPath alg q childOld w with
       | some childNew => alg.setField g s1 childNew
       | none => none
     | none => none) = some s2 at hQ
  change
    Exists fun s1' =>
      (match alg.getField g s with
       | some childOld =>
         match putPath alg q childOld w with
         | some childNew => alg.setField g s childNew
         | none => none
       | none => none) = some s1' ∧
      (match alg.getField f s1' with
       | some childOld =>
         match putPath alg p childOld v with
         | some childNew => alg.setField f s1' childNew
         | none => none
       | none => none) = some s2
  revert hP
  cases hF : alg.getField f s with
  | none =>
    intro hFalse
    nomatch hFalse
  | some c =>
    dsimp only
    cases hPc : putPath alg p c v with
    | none =>
      intro hFalse
      nomatch hFalse
    | some c' =>
      intro hP
      rw [alg.getField_setField_other f g s c' s1 hNe hP] at hQ
      revert hQ
      cases hG : alg.getField g s with
      | none =>
        intro hFalse
        nomatch hFalse
      | some d =>
        dsimp only
        cases hQd : putPath alg q d w with
        | none =>
          intro hFalse
          nomatch hFalse
        | some d' =>
          intro hQ
          cases alg.setField_setField_comm f g s c' d' s1 s2 hNe hP hQ with
          | intro s1' hs1' =>
            refine ⟨s1', hs1'.1, ?_⟩
            rw [alg.getField_setField_other g f s d' s1'
              (fun hEq => hNe hEq.symm) hs1'.1, hF]
            dsimp only
            rw [hPc]
            exact hs1'.2

/-- Conditional list selector used to merge `mutFinals` across branch joins
without requiring list-length side-conditions. -/
def zipValListBool {Val : Type} (c : Bool) (xs ys : List Val) : List Val :=
  match c with
  | true => xs
  | false => ys

/-- Elementwise conditional list merge for equal-length value lists. -/
def zipValListElem {Val : Type} (zipB : Bool → Val → Val → Val) (c : Bool)
    (xs ys : List Val) : List Val :=
  xs.foldr
    (fun x ih ys0 =>
      match ys0 with
      | [] => []
      | y :: ys' => zipB c x y :: ih ys')
    (fun _ => [])
    ys

/-- Pointwise conditional merge of two `FuncOut Val` results. -/
def zipFuncOut {Val : Type} (zipB : Bool → Val → Val → Val)
    (c : Bool) (t f : FuncOut Val) : FuncOut Val :=
  ⟨zipB c t.ret f.ret, zipValListBool c t.mutFinals f.mutFinals⟩

/-- Unconditional equivalence between `zipFuncOut` and top-level `if c then t
else f`, requiring zero side-conditions on `t.mutFinals` and `f.mutFinals`. -/
theorem zipFuncOut_eq_ite {Val : Type} (zipB : Bool → Val → Val → Val)
    (hTrue : ∀ x y, zipB true x y = x)
    (hFalse : ∀ x y, zipB false x y = y)
    (c : Bool) (t f : FuncOut Val) :
    zipFuncOut zipB c t f = (if c then t else f) := by
  cases t with
  | mk rt mt =>
    cases f with
    | mk rf mf =>
      cases c with
      | true =>
        dsimp [zipFuncOut, zipValListBool]
        rw [hTrue rt rf]
      | false =>
        dsimp [zipFuncOut, zipValListBool]
        rw [hFalse rt rf]

/-!
## Kernel-Checked Tests for `Lens`
-/

/-- Size-indexed tree representation for `LensTestVal`, enforcing in the type
system that every internal node's fuel index equals the exact structural size of
its subtrees plus one. -/
inductive LensTestTree : Nat → Type where
  | atom (n : Nat) : LensTestTree 1
  | branch (fl fr : Nat) (l : LensTestTree fl) (r : LensTestTree fr) :
      LensTestTree (fl + fr + 1)
  | choice (fc ft ff : Nat) (c : LensTestTree fc)
      (vt : LensTestTree ft) (vf : LensTestTree ff) :
      LensTestTree (fc + ft + ff + 1)
  | ref (lid : LoanId) (path : SubPath) : LensTestTree 1

/-- Binary tree test value used to exercise `ValAlgebra`, `getPath`, and
`putPath` at arbitrary nesting depths without `noncomputable` declarations,
fixed depth cutoffs, or forgeable fuel counters. -/
structure LensTestVal where
  fuel : Nat
  tree : LensTestTree fuel

namespace LensTestVal

/-- Atomic scalar leaf constructor. -/
def atom (n : Nat) : LensTestVal :=
  ⟨1, .atom n⟩

/-- Encoded reference leaf constructor. -/
def ref (lid : LoanId) (path : SubPath) : LensTestVal :=
  ⟨1, .ref lid path⟩

/-- Binary aggregate node constructor carrying unforgeable structural fuel
`l.fuel + r.fuel + 1`. -/
def node (l r : LensTestVal) : LensTestVal :=
  ⟨l.fuel + r.fuel + 1, .branch l.fuel r.fuel l.tree r.tree⟩

/-- Symbolic conditional choice node constructor carrying unforgeable structural
fuel `c.fuel + vt.fuel + vf.fuel + 1`. -/
def choice (c vt vf : LensTestVal) : LensTestVal :=
  ⟨c.fuel + vt.fuel + vf.fuel + 1,
   .choice c.fuel vt.fuel vf.fuel c.tree vt.tree vf.tree⟩

end LensTestVal

/-- One step of `remapLensTestVal`: rename a handle to `oldLid` at the root of
`x` to `newLid`, and rename the children of `x` with `ih`. -/
def remapLensTestStep (oldLid newLid : LoanId)
    (ih : LensTestVal → LensTestVal) (x : LensTestVal) : LensTestVal :=
  match x with
  | ⟨_, .atom n⟩ => .atom n
  | ⟨_, .branch fl fr l r⟩ => .node (ih ⟨fl, l⟩) (ih ⟨fr, r⟩)
  | ⟨_, .choice fc ft ff c vt vf⟩ =>
    .choice (ih ⟨fc, c⟩) (ih ⟨ft, vt⟩) (ih ⟨ff, vf⟩)
  | ⟨_, .ref lid path⟩ =>
    if lid == oldLid then .ref newLid path else .ref lid path

/-- `remapLensTestStep` nested `k` deep; parts of `v` deeper than `k` are left
unchanged. -/
def remapLensTestFuel (oldLid newLid : LoanId) (k : Nat) (v : LensTestVal) :
    LensTestVal :=
  natFold (fun x => x) (fun _ ih x => remapLensTestStep oldLid newLid ih x) k v

/-- Rename every handle to loan `oldLid` inside `v` to `newLid`. The fuel
`v.fuel` exceeds the depth of every node of `v`
(`remapLensTestFuel_eq`). -/
def remapLensTestVal (oldLid newLid : LoanId) (v : LensTestVal) : LensTestVal :=
  remapLensTestFuel oldLid newLid v.fuel v

def lensTestGetField (f : FieldIdx) (v : LensTestVal) : Option LensTestVal :=
  match f, v with
  | 0, ⟨_, .branch fl _ l _⟩ => some ⟨fl, l⟩
  | 1, ⟨_, .branch _ fr _ r⟩ => some ⟨fr, r⟩
  | _, _ => none

def lensTestSetField (f : FieldIdx) (v sub : LensTestVal) :
    Option LensTestVal :=
  match f, v, sub with
  | 0, ⟨_, .branch _ fr _ r⟩, ⟨fSub, tSub⟩ =>
    some ⟨fSub + fr + 1, .branch fSub fr tSub r⟩
  | 1, ⟨_, .branch fl _ l _⟩, ⟨fSub, tSub⟩ =>
    some ⟨fl + fSub + 1, .branch fl fSub l tSub⟩
  | _, _, _ => none

theorem lensTest_getField_setField (f : FieldIdx) (s a : LensTestVal)
    (hGet : lensTestGetField f s = some a) :
    lensTestSetField f s a = some s := by
  cases f with
  | zero =>
    cases s with
    | mk _ t =>
      cases t with
      | branch fl fr l r =>
        injection hGet with hEq
        subst hEq
        rfl
      | atom _ => nomatch hGet
      | choice _ _ _ _ _ _ => nomatch hGet
      | ref _ _ => nomatch hGet
  | succ f' =>
    cases f' with
    | zero =>
      cases s with
      | mk _ t =>
        cases t with
        | branch fl fr l r =>
          injection hGet with hEq
          subst hEq
          rfl
        | atom _ => nomatch hGet
        | choice _ _ _ _ _ _ => nomatch hGet
        | ref _ _ => nomatch hGet
    | succ _ => nomatch hGet

theorem lensTest_setField_getField (f : FieldIdx) (s a s' : LensTestVal)
    (hPut : lensTestSetField f s a = some s') :
    lensTestGetField f s' = some a := by
  cases f with
  | zero =>
    cases s with
    | mk _ t =>
      cases t with
      | branch fl fr l r =>
        cases a with
        | mk fSub tSub =>
          injection hPut with hEq
          subst hEq
          rfl
      | atom _ => nomatch hPut
      | choice _ _ _ _ _ _ => nomatch hPut
      | ref _ _ => nomatch hPut
  | succ f' =>
    cases f' with
    | zero =>
      cases s with
      | mk _ t =>
        cases t with
        | branch fl fr l r =>
          cases a with
          | mk fSub tSub =>
            injection hPut with hEq
            subst hEq
            rfl
        | atom _ => nomatch hPut
        | choice _ _ _ _ _ _ => nomatch hPut
        | ref _ _ => nomatch hPut
    | succ _ => nomatch hPut

theorem lensTest_setField_setField (f : FieldIdx)
    (s a1 a2 s1 : LensTestVal)
    (hPut1 : lensTestSetField f s a1 = some s1) :
    lensTestSetField f s1 a2 = lensTestSetField f s a2 := by
  cases f with
  | zero =>
    cases s with
    | mk _ t =>
      cases t with
      | branch fl fr l r =>
        cases a1 with
        | mk f1 t1 =>
          cases a2 with
          | mk f2 t2 =>
            injection hPut1 with hEq
            subst hEq
            rfl
      | atom _ => nomatch hPut1
      | choice _ _ _ _ _ _ => nomatch hPut1
      | ref _ _ => nomatch hPut1
  | succ f' =>
    cases f' with
    | zero =>
      cases s with
      | mk _ t =>
        cases t with
        | branch fl fr l r =>
          cases a1 with
          | mk f1 t1 =>
            cases a2 with
            | mk f2 t2 =>
              injection hPut1 with hEq
              subst hEq
              rfl
        | atom _ => nomatch hPut1
        | choice _ _ _ _ _ _ => nomatch hPut1
        | ref _ _ => nomatch hPut1
    | succ _ => nomatch hPut1

theorem lensTest_getField_setField_other (f g : FieldIdx)
    (s a s' : LensTestVal) (hNe : f ≠ g)
    (hPut : lensTestSetField f s a = some s') :
    lensTestGetField g s' = lensTestGetField g s := by
  cases f with
  | zero =>
    cases s with
    | mk _ t =>
      cases t with
      | branch fl fr l r =>
        cases a with
        | mk fa ta =>
          injection hPut with hEq
          subst hEq
          cases g with
          | zero => exact False.elim (hNe rfl)
          | succ g' => cases g' <;> rfl
      | atom _ => nomatch hPut
      | choice _ _ _ _ _ _ => nomatch hPut
      | ref _ _ => nomatch hPut
  | succ f' =>
    cases f' with
    | zero =>
      cases s with
      | mk _ t =>
        cases t with
        | branch fl fr l r =>
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
        | atom _ => nomatch hPut
        | choice _ _ _ _ _ _ => nomatch hPut
        | ref _ _ => nomatch hPut
    | succ _ => nomatch hPut

theorem lensTest_setField_setField_comm (f g : FieldIdx)
    (s a b s1 s2 : LensTestVal) (hNe : f ≠ g)
    (h1 : lensTestSetField f s a = some s1)
    (h2 : lensTestSetField g s1 b = some s2) :
    Exists fun s1' =>
      lensTestSetField g s b = some s1' ∧
      lensTestSetField f s1' a = some s2 := by
  cases a with
  | mk fa ta =>
    cases b with
    | mk fb tb =>
      cases f with
      | zero =>
        cases s with
        | mk _ t =>
          cases t with
          | branch fl fr l r =>
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
          | atom _ => nomatch h1
          | choice _ _ _ _ _ _ => nomatch h1
          | ref _ _ => nomatch h1
      | succ f' =>
        cases f' with
        | zero =>
          cases s with
          | mk _ t =>
            cases t with
            | branch fl fr l r =>
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
            | atom _ => nomatch h1
            | choice _ _ _ _ _ _ => nomatch h1
            | ref _ _ => nomatch h1
        | succ _ => nomatch h1

def lensTestSubPathEq (xs ys : SubPath) : Bool :=
  xs.foldr
    (fun a ih bs =>
      match bs with
      | [] => false
      | b :: bs' => Nat.beq a b && ih bs')
    (fun bs =>
      match bs with
      | [] => true
      | _ :: _ => false)
    ys

theorem lensTestSubPathEq_refl (xs : SubPath) :
    lensTestSubPathEq xs xs = true := by
  induction xs with
  | nil => rfl
  | cons x xs' ih =>
    change (Nat.beq x x && lensTestSubPathEq xs' xs') = true
    rw [Nat.beq_refl x, ih]
    rfl

theorem lensTestSubPathEq_eq :
    ∀ (xs ys : SubPath), lensTestSubPathEq xs ys = true → xs = ys := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    cases ys with
    | nil => rfl
    | cons _ _ => nomatch h
  | cons x xs' ih =>
    intro ys h
    cases ys with
    | nil => nomatch h
    | cons y ys' =>
      change (Nat.beq x y && lensTestSubPathEq xs' ys') = true at h
      revert h
      cases hxy : Nat.beq x y with
      | false =>
        intro h
        nomatch h
      | true =>
        intro h
        rw [Nat.eq_of_beq_eq_true hxy, ih ys' h]

def lensTestValEqStep (ih : LensTestVal → LensTestVal → Bool)
    (a b : LensTestVal) : Bool :=
  match a, b with
  | ⟨_, .atom n1⟩, ⟨_, .atom n2⟩ => Nat.beq n1 n2
  | ⟨_, .branch fl1 fr1 l1 r1⟩, ⟨_, .branch fl2 fr2 l2 r2⟩ =>
    ih ⟨fl1, l1⟩ ⟨fl2, l2⟩ && ih ⟨fr1, r1⟩ ⟨fr2, r2⟩
  | ⟨_, .choice fc1 ft1 ff1 c1 vt1 vf1⟩,
    ⟨_, .choice fc2 ft2 ff2 c2 vt2 vf2⟩ =>
    ih ⟨fc1, c1⟩ ⟨fc2, c2⟩ &&
    ih ⟨ft1, vt1⟩ ⟨ft2, vt2⟩ &&
    ih ⟨ff1, vf1⟩ ⟨ff2, vf2⟩
  | ⟨_, .ref lid1 p1⟩, ⟨_, .ref lid2 p2⟩ =>
    Nat.beq lid1 lid2 && lensTestSubPathEq p1 p2
  | _, _ => false

def lensTestValEqFuel (k : Nat) (v1 v2 : LensTestVal) : Bool :=
  natFold
    (fun _ _ => false)
    (fun _ ih a b => lensTestValEqStep ih a b)
    k v1 v2

def lensTestValEq (v1 v2 : LensTestVal) : Bool :=
  lensTestValEqFuel v1.fuel v1 v2

theorem lensTestTree_eq_refl :
    ∀ {f : Nat} (t : LensTestTree f) (k : Nat),
      f ≤ k → lensTestValEqFuel k ⟨f, t⟩ ⟨f, t⟩ = true := by
  intro f t
  induction t with
  | atom n =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ k' =>
      change Nat.beq n n = true
      exact Nat.beq_refl n
  | branch fl fr l r ihl ihr =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ k' =>
      have hSub : fl + fr ≤ k' := Nat.le_of_succ_le_succ hLe
      have hFl : fl ≤ k' := Nat.le_trans (Nat.le_add_right fl fr) hSub
      have hFr : fr ≤ k' := Nat.le_trans (Nat.le_add_left fr fl) hSub
      change
        (lensTestValEqFuel k' ⟨fl, l⟩ ⟨fl, l⟩ &&
         lensTestValEqFuel k' ⟨fr, r⟩ ⟨fr, r⟩) = true
      rw [ihl k' hFl, ihr k' hFr]
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
        (lensTestValEqFuel k' ⟨fc, c⟩ ⟨fc, c⟩ &&
         lensTestValEqFuel k' ⟨ft, vt⟩ ⟨ft, vt⟩ &&
         lensTestValEqFuel k' ⟨ff, vf⟩ ⟨ff, vf⟩) = true
      rw [ihc k' hFc, iht k' hFt, ihf k' hFf]
      rfl
  | ref lid path =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ k' =>
      change (Nat.beq lid lid && lensTestSubPathEq path path) = true
      rw [Nat.beq_refl lid, lensTestSubPathEq_refl path]
      rfl

theorem lensTestValEq_refl (v : LensTestVal) : lensTestValEq v v = true := by
  cases v with
  | mk f t =>
    exact lensTestTree_eq_refl t f (Nat.le_refl f)

def lensTestAsBool (v : LensTestVal) : Option Bool :=
  match v with
  | ⟨_, .atom n⟩ => some (n != 0)
  | _ => none

def lensTestZipVal (c vt vf : LensTestVal) : LensTestVal :=
  match lensTestAsBool c with
  | some true => vt
  | some false => vf
  | none => .choice c vt vf

def lensTestProjectBranchStep (c : LensTestVal) (branch : Bool)
    (ih : LensTestVal → LensTestVal) (v0 : LensTestVal) : LensTestVal :=
  match v0 with
  | ⟨_, .choice fc ft ff cond vt vf⟩ =>
    if lensTestValEq c ⟨fc, cond⟩ then
      if branch then ih ⟨ft, vt⟩ else ih ⟨ff, vf⟩
    else
      -- The guard may itself depend on `c`; projecting it can make it
      -- concrete, in which case `lensTestZipVal` selects the arm.
      lensTestZipVal (ih ⟨fc, cond⟩) (ih ⟨ft, vt⟩) (ih ⟨ff, vf⟩)
  | ⟨_, .branch fl fr l r⟩ =>
    .node (ih ⟨fl, l⟩) (ih ⟨fr, r⟩)
  | other => other

def lensTestProjectBranchFuel (c : LensTestVal) (branch : Bool)
    (k : Nat) (v : LensTestVal) : LensTestVal :=
  natFold (fun v0 => v0)
    (fun _ ih v0 => lensTestProjectBranchStep c branch ih v0) k v

def lensTestProjectBranchVal (c : LensTestVal) (branch : Bool)
    (v : LensTestVal) : LensTestVal :=
  match lensTestAsBool c with
  | some _ => v
  | none => lensTestProjectBranchFuel c branch v.fuel v

theorem lensTestProjectBranchFuel_eq (c : LensTestVal) (branch : Bool) :
    ∀ {n : Nat} (tr : LensTestTree n) (k : Nat), n ≤ k →
      lensTestProjectBranchFuel c branch k ⟨n, tr⟩ =
        lensTestProjectBranchFuel c branch n ⟨n, tr⟩ := by
  intro n tr
  induction tr with
  | atom _ =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ _ => rfl
  | ref _ _ =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ _ => rfl
  | branch fl fr l r ihl ihr =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ k' =>
      have hSub : fl + fr ≤ k' := Nat.le_of_succ_le_succ hLe
      have hL : fl ≤ fl + fr := Nat.le_add_right fl fr
      have hR : fr ≤ fl + fr := Nat.le_add_left fr fl
      change LensTestVal.node (lensTestProjectBranchFuel c branch k' ⟨fl, l⟩)
          (lensTestProjectBranchFuel c branch k' ⟨fr, r⟩) =
        LensTestVal.node (lensTestProjectBranchFuel c branch (fl + fr) ⟨fl, l⟩)
          (lensTestProjectBranchFuel c branch (fl + fr) ⟨fr, r⟩)
      rw [ihl k' (Nat.le_trans hL hSub), ihr k' (Nat.le_trans hR hSub),
        ihl _ hL, ihr _ hR]
  | choice fc ft ff cond vt vf ihc iht ihf =>
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
        (if lensTestValEq c ⟨fc, cond⟩ then
           if branch then lensTestProjectBranchFuel c branch k' ⟨ft, vt⟩
           else lensTestProjectBranchFuel c branch k' ⟨ff, vf⟩
         else
           lensTestZipVal (lensTestProjectBranchFuel c branch k' ⟨fc, cond⟩)
             (lensTestProjectBranchFuel c branch k' ⟨ft, vt⟩)
             (lensTestProjectBranchFuel c branch k' ⟨ff, vf⟩)) =
        (if lensTestValEq c ⟨fc, cond⟩ then
           if branch then
             lensTestProjectBranchFuel c branch (fc + ft + ff) ⟨ft, vt⟩
           else
             lensTestProjectBranchFuel c branch (fc + ft + ff) ⟨ff, vf⟩
         else
           lensTestZipVal
             (lensTestProjectBranchFuel c branch (fc + ft + ff) ⟨fc, cond⟩)
             (lensTestProjectBranchFuel c branch (fc + ft + ff) ⟨ft, vt⟩)
             (lensTestProjectBranchFuel c branch (fc + ft + ff) ⟨ff, vf⟩))
      rw [ihc k' (Nat.le_trans hC hSub), iht k' (Nat.le_trans hT hSub),
        ihf k' (Nat.le_trans hF hSub), ihc _ hC, iht _ hT, ihf _ hF]

theorem lensTest_projectBranchVal_concrete (cond : LensTestVal)
    (b branch : Bool) (v : LensTestVal)
    (hConcrete : lensTestAsBool cond = some b) :
    lensTestProjectBranchVal cond branch v = v := by
  dsimp [lensTestProjectBranchVal]
  rw [hConcrete]

theorem lensTest_projectBranchVal_zip_true (cond vt vf : LensTestVal)
    (hSym : lensTestAsBool cond = none) :
    lensTestProjectBranchVal cond true (lensTestZipVal cond vt vf) =
      lensTestProjectBranchVal cond true vt := by
  dsimp [lensTestProjectBranchVal, lensTestZipVal]
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
          (if lensTestValEq ⟨fc, tc⟩ ⟨fc, tc⟩ then
             lensTestProjectBranchFuel ⟨fc, tc⟩ true (fc + ft + ff) ⟨ft, tt⟩
           else _) =
          lensTestProjectBranchFuel ⟨fc, tc⟩ true ft ⟨ft, tt⟩
        rw [lensTestValEq_refl ⟨fc, tc⟩]
        exact lensTestProjectBranchFuel_eq ⟨fc, tc⟩ true tt (fc + ft + ff) hT

theorem lensTest_projectBranchVal_zip_false (cond vt vf : LensTestVal)
    (hSym : lensTestAsBool cond = none) :
    lensTestProjectBranchVal cond false (lensTestZipVal cond vt vf) =
      lensTestProjectBranchVal cond false vf := by
  dsimp [lensTestProjectBranchVal, lensTestZipVal]
  rw [hSym]
  cases cond with
  | mk fc tc =>
    cases vt with
    | mk ft tt =>
      cases vf with
      | mk ff tf =>
        have hF : ff ≤ fc + ft + ff := Nat.le_add_left ff (fc + ft)
        change
          (if lensTestValEq ⟨fc, tc⟩ ⟨fc, tc⟩ then
             lensTestProjectBranchFuel ⟨fc, tc⟩ false (fc + ft + ff) ⟨ff, tf⟩
           else _) =
          lensTestProjectBranchFuel ⟨fc, tc⟩ false ff ⟨ff, tf⟩
        rw [lensTestValEq_refl ⟨fc, tc⟩]
        exact lensTestProjectBranchFuel_eq ⟨fc, tc⟩ false tf (fc + ft + ff) hF

theorem lensTestProjectBranchVal_node (cond : LensTestVal) (branch : Bool)
    (l r : LensTestVal) :
    lensTestProjectBranchVal cond branch (.node l r) =
      .node (lensTestProjectBranchVal cond branch l)
        (lensTestProjectBranchVal cond branch r) := by
  dsimp [lensTestProjectBranchVal]
  cases hCond : lensTestAsBool cond with
  | some _ => rfl
  | none =>
    cases l with
    | mk fl tl =>
      cases r with
      | mk fr tr =>
        change LensTestVal.node
            (lensTestProjectBranchFuel cond branch (fl + fr) ⟨fl, tl⟩)
            (lensTestProjectBranchFuel cond branch (fl + fr) ⟨fr, tr⟩) = _
        rw [lensTestProjectBranchFuel_eq cond branch tl _
              (Nat.le_add_right fl fr),
            lensTestProjectBranchFuel_eq cond branch tr _
              (Nat.le_add_left fr fl)]

theorem lensTest_getField_projectBranchVal (cond : LensTestVal)
    (branch : Bool) (f : FieldIdx) (s a : LensTestVal)
    (hGet : lensTestGetField f s = some a) :
    lensTestGetField f (lensTestProjectBranchVal cond branch s) =
      some (lensTestProjectBranchVal cond branch a) := by
  cases s with
  | mk fs ts =>
    cases f with
    | zero =>
      cases ts with
      | branch fl fr l r =>
        injection hGet with hEq
        subst hEq
        change lensTestGetField 0
            (lensTestProjectBranchVal cond branch (.node ⟨fl, l⟩ ⟨fr, r⟩)) = _
        rw [lensTestProjectBranchVal_node]
        rfl
      | atom _ => nomatch hGet
      | ref _ _ => nomatch hGet
      | choice _ _ _ _ _ _ => nomatch hGet
    | succ f' =>
      cases f' with
      | zero =>
        cases ts with
        | branch fl fr l r =>
          injection hGet with hEq
          subst hEq
          change lensTestGetField 1
              (lensTestProjectBranchVal cond branch (.node ⟨fl, l⟩ ⟨fr, r⟩)) = _
          rw [lensTestProjectBranchVal_node]
          rfl
        | atom _ => nomatch hGet
        | ref _ _ => nomatch hGet
        | choice _ _ _ _ _ _ => nomatch hGet
      | succ _ => nomatch hGet

/-- Every `LensTestTree` has positive size. -/
theorem lensTestTree_fuel_pos : ∀ {f : Nat} (_ : LensTestTree f), 0 < f
  | _, .atom _ => Nat.zero_lt_succ 0
  | _, .branch _ _ _ _ => Nat.zero_lt_succ _
  | _, .choice _ _ _ _ _ _ => Nat.zero_lt_succ _
  | _, .ref _ _ => Nat.zero_lt_succ 0

theorem lensTest_getField_lt_sizeBound (f : FieldIdx) (v c : LensTestVal)
    (hGet : lensTestGetField f v = some c) : f < v.fuel ∧ c.fuel < v.fuel := by
  cases v with
  | mk fv tv =>
    cases f with
    | zero =>
      cases tv with
      | branch fl fr l r =>
        injection hGet with hEq
        subst hEq
        exact ⟨Nat.zero_lt_succ _, Nat.lt_succ_of_le (Nat.le_add_right fl fr)⟩
      | atom _ => nomatch hGet
      | choice _ _ _ _ _ _ => nomatch hGet
      | ref _ _ => nomatch hGet
    | succ f' =>
      cases f' with
      | zero =>
        cases tv with
        | branch fl fr l r =>
          injection hGet with hEq
          subst hEq
          exact ⟨Nat.succ_lt_succ
              (Nat.lt_of_lt_of_le (lensTestTree_fuel_pos l)
                (Nat.le_add_right fl fr)),
            Nat.lt_succ_of_le (Nat.le_add_left fr fl)⟩
        | atom _ => nomatch hGet
        | choice _ _ _ _ _ _ => nomatch hGet
        | ref _ _ => nomatch hGet
      | succ _ => nomatch hGet

/-- `LensTestVal` aggregates are binary `.branch` nodes, which carry no data
besides their two fields. -/
def lensTestSameAggregateShape (v1 v2 : LensTestVal) : Bool :=
  match v1, v2 with
  | ⟨_, .branch _ _ _ _⟩, ⟨_, .branch _ _ _ _⟩ => true
  | _, _ => false

theorem lensTest_sameAggregateShape_ext (v1 v2 : LensTestVal)
    (hShape : lensTestSameAggregateShape v1 v2 = true)
    (hFields : ∀ f, lensTestGetField f v1 = lensTestGetField f v2) :
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

theorem lensTest_sameAggregateShape_setField (f : FieldIdx)
    (s a s' t : LensTestVal)
    (hShape : lensTestSameAggregateShape s t = true)
    (hPut : lensTestSetField f s a = some s') :
    lensTestSameAggregateShape s' t = true := by
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

/-- Handle decoding for `LensTestVal`: only `.ref` leaves are handles. -/
def lensTestDecodeRef (v : LensTestVal) : Option (LoanId × SubPath) :=
  match v with
  | ⟨_, .ref lid path⟩ => some (lid, path)
  | _ => none

theorem lensTest_decodeRef_getField (f : FieldIdx) (v : LensTestVal)
    (r : LoanId × SubPath) (hDec : lensTestDecodeRef v = some r) :
    lensTestGetField f v = none := by
  cases v with
  | mk fv tv =>
    cases tv with
    | ref _ _ =>
      cases f with
      | zero => rfl
      | succ f' => cases f' <;> rfl
    | atom _ => nomatch hDec
    | branch _ _ _ _ => nomatch hDec
    | choice _ _ _ _ _ _ => nomatch hDec

/-- Guard and arms of a `LensTestVal` choice node. -/
def lensTestBranchSplit (v : LensTestVal) :
    Option (LensTestVal × LensTestVal × LensTestVal) :=
  match v with
  | ⟨_, .choice fc ft ff c vt vf⟩ => some (⟨fc, c⟩, ⟨ft, vt⟩, ⟨ff, vf⟩)
  | _ => none

theorem lensTest_decodeRef_branchSplit (v : LensTestVal)
    (r : LoanId × SubPath) (hDec : lensTestDecodeRef v = some r) :
    lensTestBranchSplit v = none := by
  cases v with
  | mk fv tv =>
    cases tv with
    | ref _ _ => rfl
    | atom _ => nomatch hDec
    | branch _ _ _ _ => nomatch hDec
    | choice _ _ _ _ _ _ => nomatch hDec

theorem lensTest_branchSplit_zipVal (cond vt vf : LensTestVal)
    (hSym : lensTestAsBool cond = none) :
    lensTestBranchSplit (lensTestZipVal cond vt vf) = some (cond, vt, vf) := by
  unfold lensTestZipVal
  rw [hSym]
  rfl

/-- Key of a `LensTestVal` condition that `lensTestSameCond` can compare: the
two atoms of a `.node (.atom a) (.atom b)` value. The test suite's symbolic
conditions have this shape; other conditions get no key. -/
def lensTestCondKey (v : LensTestVal) : Option (Nat × Nat) :=
  match v with
  | ⟨_, .branch _ _ (.atom a) (.atom b)⟩ => some (a, b)
  | _ => none

theorem lensTestCondKey_eq (v : LensTestVal) (a b : Nat)
    (h : lensTestCondKey v = some (a, b)) :
    v = .node (.atom a) (.atom b) := by
  cases v with
  | mk fv tv =>
    cases tv with
    | atom _ => nomatch h
    | ref _ _ => nomatch h
    | choice _ _ _ _ _ _ => nomatch h
    | branch fl fr l r =>
      cases l with
      | atom a' =>
        cases r with
        | atom b' =>
          injection h with hPair
          injection hPair with ha hb
          subst ha
          subst hb
          rfl
        | ref _ _ => nomatch h
        | branch _ _ _ _ => nomatch h
        | choice _ _ _ _ _ _ => nomatch h
      | ref _ _ => nomatch h
      | branch _ _ _ _ => nomatch h
      | choice _ _ _ _ _ _ => nomatch h

/-- Conservative condition equality for `LensTestVal`: equal keys
(`lensTestCondKey`). Conditions without a key are never reported equal. -/
def lensTestSameCond (c1 c2 : LensTestVal) : Bool :=
  match lensTestCondKey c1, lensTestCondKey c2 with
  | some (a1, b1), some (a2, b2) => Nat.beq a1 a2 && Nat.beq b1 b2
  | _, _ => false

theorem lensTest_sameCond_eq (c1 c2 : LensTestVal)
    (h : lensTestSameCond c1 c2 = true) : c1 = c2 := by
  unfold lensTestSameCond at h
  revert h
  cases h1 : lensTestCondKey c1 with
  | none =>
    intro h
    nomatch h
  | some p1 =>
    cases p1 with
    | mk a1 b1 =>
      cases h2 : lensTestCondKey c2 with
      | none =>
        intro h
        nomatch h
      | some p2 =>
        cases p2 with
        | mk a2 b2 =>
          change (Nat.beq a1 a2 && Nat.beq b1 b2) = true → c1 = c2
          cases hA : Nat.beq a1 a2 with
          | false =>
            intro h
            nomatch h
          | true =>
            cases hB : Nat.beq b1 b2 with
            | false =>
              intro h
              nomatch h
            | true =>
              intro _
              rw [lensTestCondKey_eq c1 a1 b1 h1,
                lensTestCondKey_eq c2 a2 b2 h2,
                Nat.eq_of_beq_eq_true hA, Nat.eq_of_beq_eq_true hB]

theorem remapLensTestFuel_succ (oldLid newLid : LoanId) (k : Nat)
    (v : LensTestVal) :
    remapLensTestFuel oldLid newLid (k + 1) v =
      remapLensTestStep oldLid newLid (remapLensTestFuel oldLid newLid k) v :=
  rfl

/-- Any fuel at least the size of a value renames it completely. -/
theorem remapLensTestFuel_eq (oldLid newLid : LoanId) :
    ∀ {n : Nat} (tr : LensTestTree n) (k : Nat), n ≤ k →
      remapLensTestFuel oldLid newLid k ⟨n, tr⟩ =
        remapLensTestVal oldLid newLid ⟨n, tr⟩ := by
  intro n tr
  induction tr with
  | atom _ =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ _ => rfl
  | ref _ _ =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ _ => rfl
  | branch fl fr l r ihl ihr =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ k' =>
      have hSub : fl + fr ≤ k' := Nat.le_of_succ_le_succ hLe
      have hL : fl ≤ fl + fr := Nat.le_add_right fl fr
      have hR : fr ≤ fl + fr := Nat.le_add_left fr fl
      change LensTestVal.node (remapLensTestFuel oldLid newLid k' ⟨fl, l⟩)
          (remapLensTestFuel oldLid newLid k' ⟨fr, r⟩) =
        LensTestVal.node (remapLensTestFuel oldLid newLid (fl + fr) ⟨fl, l⟩)
          (remapLensTestFuel oldLid newLid (fl + fr) ⟨fr, r⟩)
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
      change LensTestVal.choice (remapLensTestFuel oldLid newLid k' ⟨fc, c⟩)
          (remapLensTestFuel oldLid newLid k' ⟨ft, vt⟩)
          (remapLensTestFuel oldLid newLid k' ⟨ff, vf⟩) =
        LensTestVal.choice
          (remapLensTestFuel oldLid newLid (fc + ft + ff) ⟨fc, c⟩)
          (remapLensTestFuel oldLid newLid (fc + ft + ff) ⟨ft, vt⟩)
          (remapLensTestFuel oldLid newLid (fc + ft + ff) ⟨ff, vf⟩)
      rw [ihc k' (Nat.le_trans hC hSub), iht k' (Nat.le_trans hT hSub),
        ihf k' (Nat.le_trans hF hSub), ihc _ hC, iht _ hT, ihf _ hF]

theorem remapLensTestVal_node (oldLid newLid : LoanId) (l r : LensTestVal) :
    remapLensTestVal oldLid newLid (.node l r) =
      .node (remapLensTestVal oldLid newLid l)
        (remapLensTestVal oldLid newLid r) := by
  cases l with
  | mk fl tl =>
    cases r with
    | mk fr tr =>
      change LensTestVal.node (remapLensTestFuel oldLid newLid (fl + fr) ⟨fl, tl⟩)
          (remapLensTestFuel oldLid newLid (fl + fr) ⟨fr, tr⟩) = _
      rw [remapLensTestFuel_eq oldLid newLid tl _ (Nat.le_add_right fl fr),
        remapLensTestFuel_eq oldLid newLid tr _ (Nat.le_add_left fr fl)]

theorem remapLensTestVal_choice (oldLid newLid : LoanId)
    (c vt vf : LensTestVal) :
    remapLensTestVal oldLid newLid (.choice c vt vf) =
      .choice (remapLensTestVal oldLid newLid c)
        (remapLensTestVal oldLid newLid vt)
        (remapLensTestVal oldLid newLid vf) := by
  cases c with
  | mk fc tc =>
    cases vt with
    | mk ft tt =>
      cases vf with
      | mk ff tf =>
        change LensTestVal.choice
            (remapLensTestFuel oldLid newLid (fc + ft + ff) ⟨fc, tc⟩)
            (remapLensTestFuel oldLid newLid (fc + ft + ff) ⟨ft, tt⟩)
            (remapLensTestFuel oldLid newLid (fc + ft + ff) ⟨ff, tf⟩) = _
        rw [remapLensTestFuel_eq oldLid newLid tc _
            (Nat.le_trans (Nat.le_add_right fc ft)
              (Nat.le_add_right (fc + ft) ff)),
          remapLensTestFuel_eq oldLid newLid tt _
            (Nat.le_trans (Nat.le_add_left ft fc)
              (Nat.le_add_right (fc + ft) ff)),
          remapLensTestFuel_eq oldLid newLid tf _
            (Nat.le_add_left ff (fc + ft))]

theorem remapLensTestVal_ref (oldLid newLid lid : LoanId) (path : SubPath) :
    remapLensTestVal oldLid newLid (.ref lid path) =
      .ref (if lid == oldLid then newLid else lid) path := by
  change (if lid == oldLid then LensTestVal.ref newLid path else .ref lid path) =
    _
  cases lid == oldLid <;> rfl

theorem lensTest_decodeRef_remapRefInVal (oldLid newLid : LoanId)
    (v : LensTestVal) :
    lensTestDecodeRef (remapLensTestVal oldLid newLid v) =
      (lensTestDecodeRef v).map
        (fun r => (if r.1 == oldLid then newLid else r.1, r.2)) := by
  cases v with
  | mk fv tv =>
    cases tv with
    | atom _ => rfl
    | ref lid path =>
      change lensTestDecodeRef (remapLensTestVal oldLid newLid (.ref lid path)) =
        _
      rw [remapLensTestVal_ref]
      rfl
    | branch fl fr l r =>
      change lensTestDecodeRef
          (remapLensTestVal oldLid newLid (.node ⟨fl, l⟩ ⟨fr, r⟩)) = _
      rw [remapLensTestVal_node]
      rfl
    | choice fc ft ff c vt vf =>
      change lensTestDecodeRef (remapLensTestVal oldLid newLid
          (.choice ⟨fc, c⟩ ⟨ft, vt⟩ ⟨ff, vf⟩)) = _
      rw [remapLensTestVal_choice]
      rfl

theorem lensTest_getField_remapRefInVal (oldLid newLid : LoanId)
    (f : FieldIdx) (v : LensTestVal) :
    lensTestGetField f (remapLensTestVal oldLid newLid v) =
      (lensTestGetField f v).map (remapLensTestVal oldLid newLid) := by
  cases v with
  | mk fv tv =>
    cases tv with
    | atom _ =>
      cases f with
      | zero => rfl
      | succ f' => cases f' <;> rfl
    | ref lid path =>
      change lensTestGetField f
          (remapLensTestVal oldLid newLid (.ref lid path)) = _
      rw [remapLensTestVal_ref]
      cases f with
      | zero => rfl
      | succ f' => cases f' <;> rfl
    | branch fl fr l r =>
      change lensTestGetField f
          (remapLensTestVal oldLid newLid (.node ⟨fl, l⟩ ⟨fr, r⟩)) = _
      rw [remapLensTestVal_node]
      cases f with
      | zero => rfl
      | succ f' => cases f' <;> rfl
    | choice fc ft ff c vt vf =>
      change lensTestGetField f (remapLensTestVal oldLid newLid
          (.choice ⟨fc, c⟩ ⟨ft, vt⟩ ⟨ff, vf⟩)) = _
      rw [remapLensTestVal_choice]
      cases f with
      | zero => rfl
      | succ f' => cases f' <;> rfl

theorem lensTest_branchSplit_remapRefInVal (oldLid newLid : LoanId)
    (v : LensTestVal) :
    lensTestBranchSplit (remapLensTestVal oldLid newLid v) =
      (lensTestBranchSplit v).map (fun s =>
        (remapLensTestVal oldLid newLid s.1,
         remapLensTestVal oldLid newLid s.2.1,
         remapLensTestVal oldLid newLid s.2.2)) := by
  cases v with
  | mk fv tv =>
    cases tv with
    | atom _ => rfl
    | ref lid path =>
      change lensTestBranchSplit
          (remapLensTestVal oldLid newLid (.ref lid path)) = _
      rw [remapLensTestVal_ref]
      rfl
    | branch fl fr l r =>
      change lensTestBranchSplit
          (remapLensTestVal oldLid newLid (.node ⟨fl, l⟩ ⟨fr, r⟩)) = _
      rw [remapLensTestVal_node]
      rfl
    | choice fc ft ff c vt vf =>
      change lensTestBranchSplit (remapLensTestVal oldLid newLid
          (.choice ⟨fc, c⟩ ⟨ft, vt⟩ ⟨ff, vf⟩)) = _
      rw [remapLensTestVal_choice]
      rfl

theorem lensTest_remapRefInVal_leaf (oldLid newLid : LoanId) (v : LensTestVal)
    (hDec : lensTestDecodeRef v = none)
    (hFields : ∀ f, lensTestGetField f v = none)
    (hSplit : lensTestBranchSplit v = none) :
    remapLensTestVal oldLid newLid v = v := by
  cases v with
  | mk fv tv =>
    cases tv with
    | atom _ => rfl
    | ref _ _ => nomatch hDec
    | branch _ _ _ _ => nomatch hFields 0
    | choice _ _ _ _ _ _ => nomatch hSplit

def lensTestSameRefVal (v1 v2 : LensTestVal) : Bool :=
  match v1, v2 with
  | ⟨_, .ref l1 p1⟩, ⟨_, .ref l2 p2⟩ =>
    Nat.beq l1 l2 && lensTestSubPathEq p1 p2
  | _, _ => false

theorem lensTest_sameRefVal_eq (v1 v2 : LensTestVal)
    (h : lensTestSameRefVal v1 v2 = true) : v1 = v2 := by
  cases v1 with
  | mk f1 t1 =>
    cases v2 with
    | mk f2 t2 =>
      cases t1 with
      | ref l1 p1 =>
        cases t2 with
        | ref l2 p2 =>
          change (Nat.beq l1 l2 && lensTestSubPathEq p1 p2) = true at h
          revert h
          cases hL : Nat.beq l1 l2 with
          | false =>
            intro h
            nomatch h
          | true =>
            intro hP
            rw [Nat.eq_of_beq_eq_true hL, lensTestSubPathEq_eq p1 p2 hP]
        | atom _ => nomatch h
        | branch _ _ _ _ => nomatch h
        | choice _ _ _ _ _ _ => nomatch h
      | atom _ => nomatch h
      | branch _ _ _ _ => nomatch h
      | choice _ _ _ _ _ _ => nomatch h

def lensTestValAlg : ValAlgebra LensTestVal where
  defaultVal := .atom 0
  asBool := lensTestAsBool
  zipVal := lensTestZipVal
  projectBranchVal := lensTestProjectBranchVal
  projectBranchVal_concrete := lensTest_projectBranchVal_concrete
  projectBranchVal_zip_true := lensTest_projectBranchVal_zip_true
  projectBranchVal_zip_false := lensTest_projectBranchVal_zip_false
  getField := lensTestGetField
  getField_projectBranchVal := lensTest_getField_projectBranchVal
  setField := lensTestSetField
  getField_setField := lensTest_getField_setField
  setField_getField := lensTest_setField_getField
  setField_setField := lensTest_setField_setField
  getField_setField_other := lensTest_getField_setField_other
  setField_setField_comm := lensTest_setField_setField_comm
  encodeRef lid path := .ref lid path
  decodeRef := lensTestDecodeRef
  decodeRef_encodeRef _ _ := rfl
  decodeRef_encodeSharedRef _ _ := rfl
  decodeRef_getField := lensTest_decodeRef_getField
  branchSplit := lensTestBranchSplit
  decodeRef_branchSplit := lensTest_decodeRef_branchSplit
  branchSplit_zipVal := lensTest_branchSplit_zipVal
  sameCond := lensTestSameCond
  sameCond_eq := lensTest_sameCond_eq
  sameRefVal := lensTestSameRefVal
  sameRefVal_eq := lensTest_sameRefVal_eq
  remapRefInVal := remapLensTestVal
  decodeRef_remapRefInVal := lensTest_decodeRef_remapRefInVal
  getField_remapRefInVal := lensTest_getField_remapRefInVal
  branchSplit_remapRefInVal := lensTest_branchSplit_remapRefInVal
  remapRefInVal_leaf := lensTest_remapRefInVal_leaf
  sizeBound v := v.fuel
  getField_lt_sizeBound := lensTest_getField_lt_sizeBound
  sameAggregateShape := lensTestSameAggregateShape
  sameAggregateShape_ext := lensTest_sameAggregateShape_ext
  sameAggregateShape_setField := lensTest_sameAggregateShape_setField

theorem lensTestValAlg_fieldLens_lawful (f : FieldIdx) :
    LawfulLens LensTestVal LensTestVal (fieldLens lensTestValAlg f) :=
  fieldLens_lawful lensTestValAlg f

theorem lensTestValAlg_subPathLens_lawful (path : SubPath) :
    LawfulLens LensTestVal LensTestVal (subPathLens lensTestValAlg path) :=
  subPathLens_lawful lensTestValAlg path

/-- `natFold` is exact at indices well above eight (`n = 9`, `12`, `20`),
never truncating or aliasing. -/
theorem natFold_above_eight_exact :
    natFold 0 (fun _ acc => acc + 1) 9 = 9 ∧
    natFold 0 (fun _ acc => acc + 1) 12 = 12 ∧
    natFold 0 (fun _ acc => acc + 1) 20 = 20 :=
  ⟨rfl, rfl, rfl⟩

/-- `listFold` traverses lists longer than eight elements completely and passes
the exact remaining suffix to `cons`. -/
theorem listFold_above_eight_exact :
    listFold 0 (fun x _ acc => x + acc)
      [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] = 78 ∧
    listFold [] (fun _ tail _ => tail) [1, 2, 3] = [2, 3] :=
  ⟨rfl, rfl⟩

/-- Deep 10-level binary tree value for testing `getPath` and `putPath` beyond
depth 8. -/
def deepLensTestTree (leaf : Nat) : LensTestVal :=
  .node (.node (.node (.node (.node (.node (.node (.node (.node (.node
    (.atom leaf) (.atom 1)) (.atom 2)) (.atom 3)) (.atom 4)) (.atom 5))
    (.atom 6)) (.atom 7)) (.atom 8)) (.atom 9)) (.atom 10)

/-- `getPath` and `putPath` succeed and preserve sibling branches at depth
10. -/
theorem getPath_putPath_depth_ten (x y : Nat) :
    let path10 : SubPath := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    getPath lensTestValAlg path10 (deepLensTestTree x) = some (.atom x) ∧
    putPath lensTestValAlg path10 (deepLensTestTree x) (.atom y) =
      some (deepLensTestTree y) ∧
    getPath lensTestValAlg [1] (deepLensTestTree x) = some (.atom 10) ∧
    getPath lensTestValAlg [0, 0, 0, 2] (deepLensTestTree x) = none :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `HoldsFnSpec` succeeds on `.ok` and rejects `.fail`. -/
theorem holdsFnSpec_ok_and_fail_tests :
    HoldsFnSpec (.ok (42 : Nat)) (fun n => n = 42) ∧
    ¬ HoldsFnSpec (.fail : EvalOutcome Nat) (fun _ => True) :=
  ⟨rfl, holdsFnSpec_not_fail _⟩

/-- Unit tests for `fix2`/`fix4`/`fix8`/`fix16` combinators. -/
theorem fix_combinators_tests :
    fix2 (fun n => n + 1) 0 = 2 ∧
    fix4 (fun n => n + 1) 0 = 4 ∧
    fix8 (fun n => n + 1) 0 = 8 ∧
    fix16 (fun n => n + 1) 0 = 16 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Unit tests for `Lens.id`, `Lens.comp`, `Lens.id_lawful`, and
`Lens.comp_lawful`, including `none` propagation when an outer or inner lens
fails. -/
theorem lens_id_and_comp_tests :
    (Lens.id Nat).get 15 = some 15 ∧
    (Lens.id Nat).put 15 20 = some 20 ∧
    (Lens.comp (fieldLens lensTestValAlg 0) (fieldLens lensTestValAlg 1)).get
      (.node (.node (.atom 1) (.atom 2)) (.atom 3)) = some (.atom 2) ∧
    (Lens.comp (fieldLens lensTestValAlg 0) (fieldLens lensTestValAlg 1)).get
      (.node (.atom 1) (.atom 3)) = none ∧
    (Lens.comp (fieldLens lensTestValAlg 0) (fieldLens lensTestValAlg 1)).get
      (.atom 1) = none ∧
    (Lens.comp (fieldLens lensTestValAlg 0) (fieldLens lensTestValAlg 1)).put
      (.node (.node (.atom 1) (.atom 2)) (.atom 3)) (.atom 99) =
      some (.node (.node (.atom 1) (.atom 99)) (.atom 3)) ∧
    (Lens.comp (fieldLens lensTestValAlg 0) (fieldLens lensTestValAlg 1)).put
      (.node (.atom 1) (.atom 3)) (.atom 99) = none ∧
    (Lens.comp (fieldLens lensTestValAlg 0) (fieldLens lensTestValAlg 1)).put
      (.atom 1) (.atom 99) = none ∧
    LawfulLens LensTestVal LensTestVal (Lens.id LensTestVal) ∧
    LawfulLens LensTestVal LensTestVal
      (Lens.comp (fieldLens lensTestValAlg 0) (fieldLens lensTestValAlg 1)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   Lens.id_lawful LensTestVal,
   Lens.comp_lawful
     (fieldLens lensTestValAlg 0)
     (fieldLens lensTestValAlg 1)
     (lensTestValAlg_fieldLens_lawful 0)
     (lensTestValAlg_fieldLens_lawful 1)⟩

/-- Unit tests for `zipValListBool`, `zipValListElem`, `zipFuncOut`,
and `zipFuncOut_eq_ite`. -/
theorem zipVal_and_zipFuncOut_tests (c : Bool) :
    let zipB (b : Bool) (x y : Nat) : Nat := if b then x else y
    zipValListBool true [1, 2] [3] = [1, 2] ∧
    zipValListBool false [1, 2] [3] = [3] ∧
    zipValListElem zipB true [10, 20] [30, 40, 50] = [10, 20] ∧
    zipValListElem zipB false [10, 20] [30, 40, 50] = [30, 40] ∧
    zipFuncOut zipB c ⟨1, [10, 20]⟩ ⟨2, [30]⟩ =
      (if c then ⟨1, [10, 20]⟩ else ⟨2, [30]⟩) :=
  ⟨rfl, rfl, rfl, rfl,
   zipFuncOut_eq_ite
     (fun b x y => if b then x else y)
     (fun _ _ => rfl)
     (fun _ _ => rfl)
     c ⟨1, [10, 20]⟩ ⟨2, [30]⟩⟩

/-- Negative and boundary tests for `getPath`, `putPath`, `asBool`,
`zipVal`, `projectBranchVal`, `encodeRef`, `decodeRef`, and deep post-update
`remapRefInVal` on `lensTestValAlg`. -/
theorem lensTestValAlg_operations_and_failures_tests :
    getPath lensTestValAlg [0] (.atom 5) = none ∧
    getPath lensTestValAlg [0] (.ref 1 []) = none ∧
    getPath lensTestValAlg [2] (.node (.atom 1) (.atom 2)) = none ∧
    putPath lensTestValAlg [0] (.atom 5) (.atom 6) = none ∧
    putPath lensTestValAlg [0] (.ref 1 []) (.atom 6) = none ∧
    putPath lensTestValAlg [2] (.node (.atom 1) (.atom 2)) (.atom 6) = none ∧
    putPath lensTestValAlg [] (.atom 5) (.atom 9) = some (.atom 9) ∧
    lensTestValAlg.asBool (.atom 1) = some true ∧
    lensTestValAlg.asBool (.atom 0) = some false ∧
    lensTestValAlg.asBool (.node (.atom 1) (.atom 2)) = none ∧
    lensTestValAlg.zipVal (.atom 1) (.atom 10) (.atom 20) = .atom 10 ∧
    lensTestValAlg.zipVal (.atom 0) (.atom 10) (.atom 20) = .atom 20 ∧
    lensTestValAlg.zipVal (.ref 0 []) (.atom 10) (.atom 20) =
      .choice (.ref 0 []) (.atom 10) (.atom 20) ∧
    lensTestValAlg.projectBranchVal (.ref 0 []) true
      (.choice (.ref 0 []) (.atom 10) (.atom 20)) = .atom 10 ∧
    lensTestValAlg.projectBranchVal (.ref 0 []) false
      (.choice (.ref 0 []) (.atom 10) (.atom 20)) = .atom 20 ∧
    lensTestValAlg.decodeRef (lensTestValAlg.encodeRef 7 [0, 1]) =
      some (7, [0, 1]) ∧
    lensTestValAlg.decodeRef (lensTestValAlg.encodeSharedRef 7 [0, 1]) =
      some (7, [0, 1]) ∧
    lensTestValAlg.remapRefInVal 3 9
      (.node (.ref 3 [0]) (.node (.atom 1) (.ref 4 [1]))) =
      .node (.ref 9 [0]) (.node (.atom 1) (.ref 4 [1])) ∧
    (let path10 : SubPath := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
     match putPath lensTestValAlg path10 (deepLensTestTree 0) (.ref 3 [1]) with
     | some deepWithRef =>
       match putPath lensTestValAlg [0] (.node (.atom 0) (.atom 1))
           deepWithRef with
       | some replacedRoot =>
         getPath lensTestValAlg (0 :: path10)
           (lensTestValAlg.remapRefInVal 3 9 replacedRoot) =
           some (.ref 9 [1])
       | none => False
     | none => False) ∧
    lensTestValAlg.decodeRef (.atom 7) = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl⟩

end Anneal.PureLift
