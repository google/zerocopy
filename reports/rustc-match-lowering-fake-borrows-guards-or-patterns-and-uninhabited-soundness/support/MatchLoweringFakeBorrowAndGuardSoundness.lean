-- Copyright 2026 The Authors
-- SPDX-License-Identifier: Apache-2.0 OR MIT

/-!
# Mechanized Soundness of `rustc` Match Lowering: Fake Borrows, Or-Pattern Guards, and Uninhabited / `#[non_exhaustive]` Exhaustiveness

Pinned to `Lean v4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`).

Strict constructive kernel discipline (matching `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`
`TrustedBoundary.lean` hygiene):
- Purely constructive kernel proofs depending at most on `propext`.
- Structural recursion only; every `def` and term-level `abbrev` carries `noncomputable` so the
  Lean 4 IR compiler emits zero auxiliary unsafe recursion declarations.
- Zero trust-expanding tactics, reflection axioms, or unfinished proof obligations.

## Primary-Source Correspondence (`rust-lang/rust`)
1. `FakeBorrowCollector` (`compiler/rustc_mir_build/src/builder/matches/util.rs:103-231` at
   `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`; `util.rs:101-227` at
   `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) and `place_components_conflict`
   (`compiler/rustc_borrowck/src/places_conflict.rs:131-297`).
2. Or-pattern sub-branch guard lowering and reverse sub-branch drop scheduling
   (`compiler/rustc_mir_build/src/builder/matches/mod.rs:498-550, 2387-2529` and
   `compiler/rustc_mir_build/src/builder/scope.rs:1760-1774`).
3. Uninhabited (`Void` / `!`) place-mention vs `&Void` value-validity and cross-crate
   `#[non_exhaustive]` single-variant `TestKind::Switch` lowering
   (`compiler/rustc_mir_build/src/builder/matches/match_pair.rs:396-406`,
   `compiler/rustc_pattern_analysis/src/usefulness.rs:946-997`, and
   `compiler/rustc_const_eval/src/interpret/place.rs:470-538`).
-/

namespace MatchLoweringSoundness

/-! ## Section 1: Elementary Boolean Equality, Structured Places, and Store Semantics -/

/-- Structural boolean equality on `Nat` using primitive constructor recursion. -/
noncomputable def natBeq : Nat → Nat → Bool
  | 0, 0 => true
  | m + 1, n + 1 => natBeq m n
  | _, _ => false

theorem bool_and_eq_true {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a with
  | false => contradiction
  | true => exact ⟨rfl, h⟩

theorem bool_not_eq_true {a : Bool} (h : (!a) = true) : a = false := by
  cases a with
  | false => rfl
  | true => contradiction

theorem bool_not_eq_false {a : Bool} (h : (!a) = false) : a = true := by
  cases a with
  | false => contradiction
  | true => rfl

theorem natBeq_refl (n : Nat) : natBeq n n = true := by
  induction n with
  | zero => rfl
  | succ _ ih => exact ih

theorem natBeq_eq_of_true {m n : Nat} (h : natBeq m n = true) : m = n := by
  induction m generalizing n with
  | zero =>
    cases n with
    | zero => rfl
    | succ _ => contradiction
  | succ _ ih =>
    cases n with
    | zero => contradiction
    | succ _ => rw [ih h]

theorem natBeq_false_of_ne {m n : Nat} (hne : m ≠ n) : natBeq m n = false := by
  cases h : natBeq m n with
  | false => rfl
  | true => exact False.elim (hne (natBeq_eq_of_true h))

abbrev LocalId := Nat
abbrev VarId := Nat

/-- First-order MIR place projection elements (`rustc_middle::mir::ProjectionElem`):
- `.deref`: built-in `*p` (`&T` or `Box<T>` under `DerefPatBorrowMode::Box`).
- `.field idx`: struct/tuple field `p.idx` (including smart-pointer backing storage `s.0`).
- `.downcastField variant idx`: enum variant payload `((p as Variant(variant)).idx)`. -/
inductive ProjElem where
  | deref
  | field (idx : Nat)
  | downcastField (variant : Nat) (idx : Nat)

noncomputable def ProjElem.beq : ProjElem → ProjElem → Bool
  | .deref, .deref => true
  | .field i, .field j => natBeq i j
  | .downcastField v1 i1, .downcastField v2 i2 => natBeq v1 v2 && natBeq i1 i2
  | _, _ => false

theorem projElemBeq_refl (e : ProjElem) : ProjElem.beq e e = true := by
  cases e with
  | deref => rfl
  | field idx => exact natBeq_refl idx
  | downcastField v idx =>
    change (natBeq v v && natBeq idx idx) = true
    rw [natBeq_refl v, natBeq_refl idx]
    rfl

theorem projElemBeq_eq_of_true {a b : ProjElem} (h : ProjElem.beq a b = true) : a = b := by
  cases a with
  | deref =>
    cases b with
    | deref => rfl
    | field _ | downcastField _ _ => contradiction
  | field i =>
    cases b with
    | field j => rw [natBeq_eq_of_true h]
    | deref | downcastField _ _ => contradiction
  | downcastField v1 i1 =>
    cases b with
    | downcastField v2 i2 =>
      change (natBeq v1 v2 && natBeq i1 i2) = true at h
      rcases bool_and_eq_true h with ⟨hv, hi⟩
      rw [natBeq_eq_of_true hv, natBeq_eq_of_true hi]
    | deref | field _ => contradiction

/-- A MIR `Place`: root `localId` plus left-to-right `proj` list. -/
structure Place where
  localId : LocalId
  proj : List ProjElem

noncomputable def projListBeq : List ProjElem → List ProjElem → Bool
  | [], [] => true
  | x :: xs, y :: ys => ProjElem.beq x y && projListBeq xs ys
  | _, _ => false

noncomputable def Place.beq (a b : Place) : Bool :=
  natBeq a.localId b.localId && projListBeq a.proj b.proj

theorem projListBeq_refl (ps : List ProjElem) : projListBeq ps ps = true := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
    change (ProjElem.beq p p && projListBeq rest rest) = true
    rw [projElemBeq_refl p, ih]
    rfl

theorem placeBeq_refl (p : Place) : Place.beq p p = true := by
  cases p with
  | mk lid pr =>
    change (natBeq lid lid && projListBeq pr pr) = true
    rw [natBeq_refl lid, projListBeq_refl pr]
    rfl

theorem projListBeq_eq_of_true {xs ys : List ProjElem} (h : projListBeq xs ys = true) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => contradiction
  | cons x xrest ih =>
    cases ys with
    | nil => contradiction
    | cons y yrest =>
      change (ProjElem.beq x y && projListBeq xrest yrest) = true at h
      rcases bool_and_eq_true h with ⟨hxy, hrest⟩
      rw [projElemBeq_eq_of_true hxy, ih hrest]

theorem placeBeq_eq_of_true {a b : Place} (h : Place.beq a b = true) : a = b := by
  cases a with
  | mk la pa =>
    cases b with
    | mk lb pb =>
      change (natBeq la lb && projListBeq pa pb) = true at h
      rcases bool_and_eq_true h with ⟨hl, hp⟩
      rw [natBeq_eq_of_true hl, projListBeq_eq_of_true hp]

/-- Structured runtime values with disjoint type-directed constructors:
- `.scalar`: primitive integer/token values.
- `.boolVal`: primitive `bool`.
- `.tuple`: product/struct fields projected by `.field 0` and `.field 1`.
- `.enumAdt`: tagged enum values tested by `Rvalue::Discriminant` and projected by `.downcastField`.
- `.boxVal`: `Box<T>` projected directly by `.deref` (`DerefPatBorrowMode::Box`).
- `.smartPtr`: `DerefPure` smart pointer whose `<S as Deref>::deref` reads `backing`, which is
  also stored at `.field 0` (`DerefPatBorrowMode::Borrow` / `TestableCase::Deref`).
- `.refLocal`: shared reference `&T` pointing to an immutable borrowed local `target`. -/
inductive Val where
  | scalar (n : Nat)
  | boolVal (b : Bool)
  | tuple (f0 : Val) (f1 : Val)
  | enumAdt (variant : Nat) (f0 : Val) (f1 : Val)
  | boxVal (inner : Val)
  | smartPtr (backing : Val)
  | refLocal (target : LocalId)

abbrev Store := List (LocalId × Val)

noncomputable def storeLookup : Store → LocalId → Option Val
  | [], _ => none
  | (k, v) :: rest, q =>
    match natBeq k q with
    | true => some v
    | false => storeLookup rest q

noncomputable def storeUpdate : Store → LocalId → Val → Store
  | [], q, newVal => [(q, newVal)]
  | (k, v) :: rest, q, newVal =>
    match natBeq k q with
    | true => (k, newVal) :: rest
    | false => (k, v) :: storeUpdate rest q newVal

theorem storeLookup_update_same (st : Store) (q : LocalId) (v : Val) :
    storeLookup (storeUpdate st q v) q = some v := by
  induction st with
  | nil =>
    dsimp only [storeUpdate, storeLookup]
    rw [natBeq_refl q]
  | cons hd _ ih =>
    cases hd with
    | mk k _ =>
      dsimp only [storeUpdate]
      cases hkq : natBeq k q with
      | true =>
        dsimp only [storeLookup]
        rw [hkq]
      | false =>
        dsimp only [storeLookup]
        rw [hkq]
        exact ih

theorem storeLookup_update_ne (st : Store) {w q : LocalId} (v : Val)
    (hne : natBeq w q = false) :
    storeLookup (storeUpdate st w v) q = storeLookup st q := by
  induction st with
  | nil =>
    dsimp only [storeUpdate, storeLookup]
    rw [hne]
  | cons hd _ ih =>
    cases hd with
    | mk k _ =>
      dsimp only [storeUpdate, storeLookup]
      cases hkw : natBeq k w with
      | true =>
        have hkeq : k = w := natBeq_eq_of_true hkw
        subst hkeq
        dsimp only [storeLookup]
        rw [hne]
      | false =>
        dsimp only [storeLookup]
        cases natBeq k q with
        | true => rfl
        | false => exact ih

/-- Evaluate a projection path starting from `v`, using `st` to resolve `.refLocal` dereferences. -/
noncomputable def evalProj (st : Store) (v : Val) : List ProjElem → Option Val
  | [] => some v
  | .deref :: rest =>
    match v with
    | .boxVal inner => evalProj st inner rest
    | .refLocal target =>
      match storeLookup st target with
      | some tv => evalProj st tv rest
      | none => none
    | _ => none
  | .field 0 :: rest =>
    match v with
    | .tuple f0 _ => evalProj st f0 rest
    | .smartPtr backing => evalProj st backing rest
    | _ => none
  | .field (n + 1) :: rest =>
    match n, v with
    | 0, .tuple _ f1 => evalProj st f1 rest
    | _, _ => none
  | .downcastField expectedVar 0 :: rest =>
    match v with
    | .enumAdt tag f0 _ =>
      match natBeq tag expectedVar with
      | true => evalProj st f0 rest
      | false => none
    | _ => none
  | .downcastField expectedVar (n + 1) :: rest =>
    match n, v with
    | 0, .enumAdt tag _ f1 =>
      match natBeq tag expectedVar with
      | true => evalProj st f1 rest
      | false => none
    | _, _ => none

noncomputable def evalPlace (st : Store) (p : Place) : Option Val :=
  match storeLookup st p.localId with
  | some rootVal => evalProj st rootVal p.proj
  | none => none

/-- Functional update along an owned/mutable projection chain (shared references `Val.refLocal`
cannot be mutated through `.deref`, matching Rust). -/
noncomputable def writeAtProj (v : Val) : List ProjElem → Val → Option Val
  | [], newVal => some newVal
  | .deref :: rest, newVal =>
    match v with
    | .boxVal inner =>
      match writeAtProj inner rest newVal with
      | some inner' => some (.boxVal inner')
      | none => none
    | _ => none
  | .field 0 :: rest, newVal =>
    match v with
    | .tuple f0 f1 =>
      match writeAtProj f0 rest newVal with
      | some f0' => some (.tuple f0' f1)
      | none => none
    | .smartPtr backing =>
      match writeAtProj backing rest newVal with
      | some b' => some (.smartPtr b')
      | none => none
    | _ => none
  | .field (n + 1) :: rest, newVal =>
    match n, v with
    | 0, .tuple f0 f1 =>
      match writeAtProj f1 rest newVal with
      | some f1' => some (.tuple f0 f1')
      | none => none
    | _, _ => none
  | .downcastField expectedVar 0 :: rest, newVal =>
    match v with
    | .enumAdt tag f0 f1 =>
      match natBeq tag expectedVar with
      | true =>
        match writeAtProj f0 rest newVal with
        | some f0' => some (.enumAdt tag f0' f1)
        | none => none
      | false => none
    | _ => none
  | .downcastField expectedVar (n + 1) :: rest, newVal =>
    match n, v with
    | 0, .enumAdt tag f0 f1 =>
      match natBeq tag expectedVar with
      | true =>
        match writeAtProj f1 rest newVal with
        | some f1' => some (.enumAdt tag f0 f1')
        | none => none
      | false => none
    | _, _ => none

noncomputable def writePlace (st : Store) (p : Place) (newVal : Val) : Option Store :=
  match storeLookup st p.localId with
  | none => none
  | some rootVal =>
    match writeAtProj rootVal p.proj newVal with
    | some rootVal' => some (storeUpdate st p.localId rootVal')
    | none => none

/-! ## Section 2: `FakeBorrowKind::{Shallow, Deep}` Lattice, `places_conflict`, and `FakeBorrowCollector` -/

/-- Mirrors `rustc_middle::mir::FakeBorrowKind` (`Shallow < Deep`). -/
inductive FakeBorrowKind where
  | shallow
  | deep

noncomputable def FakeBorrowKind.le : FakeBorrowKind → FakeBorrowKind → Bool
  | .shallow, _ => true
  | .deep, .deep => true
  | .deep, .shallow => false

noncomputable def FakeBorrowKind.join : FakeBorrowKind → FakeBorrowKind → FakeBorrowKind
  | .deep, _ => .deep
  | _, .deep => .deep
  | .shallow, .shallow => .shallow

theorem fakeBorrowKind_le_refl (k : FakeBorrowKind) : k.le k = true := by
  cases k <;> rfl

theorem fakeBorrowKind_le_trans {a b c : FakeBorrowKind}
    (hab : a.le b = true) (hbc : b.le c = true) : a.le c = true := by
  cases a <;> cases b <;> cases c <;> first | rfl | contradiction

theorem fakeBorrowKind_le_join_left (a b : FakeBorrowKind) : a.le (a.join b) = true := by
  cases a <;> cases b <;> rfl

theorem fakeBorrowKind_le_join_right (a b : FakeBorrowKind) : b.le (a.join b) = true := by
  cases a <;> cases b <;> rfl

/-- Whether remaining borrow projections cross a `.deref` (`places_conflict.rs:219-225`:
a shallow assignment to `x` does NOT conflict with a borrow of `*x`, which is why
`FakeBorrowCollector::fake_borrow_deref_prefixes` must also borrow `x`). -/
noncomputable def hasDerefInTail : List ProjElem → Bool
  | [] => false
  | .deref :: _ => true
  | _ :: rest => hasDerefInTail rest

/-- Exact place-component conflict relation (`rustc_borrowck::places_conflict::place_components_conflict`,
`places_conflict.rs:131-297`) for a fake borrow `(borrowProj, kind)` against a shallow write at `writeProj`
on the same root `LocalId`. -/
noncomputable def projComponentsConflict (kind : FakeBorrowKind) :
    List ProjElem → List ProjElem → Bool
  | [], [] => true
  | [], _ :: _ =>
    match kind with
    | .shallow => false
    | .deep => true
  | bRest@(_ :: _), [] =>
    !hasDerefInTail bRest
  | bElem :: bRest, wElem :: wRest =>
    match ProjElem.beq bElem wElem with
    | true => projComponentsConflict kind bRest wRest
    | false => false

noncomputable def borrowConflictsWithWrite (bp : Place) (kind : FakeBorrowKind) (wp : Place) : Bool :=
  match natBeq bp.localId wp.localId with
  | false => false
  | true => projComponentsConflict kind bp.proj wp.proj

abbrev FakeBorrowList := List (Place × FakeBorrowKind)

noncomputable def upsertFakeBorrow (fbs : FakeBorrowList) (p : Place) (kind : FakeBorrowKind) :
    FakeBorrowList :=
  match fbs with
  | [] => [(p, kind)]
  | (q, oldK) :: rest =>
    match Place.beq q p with
    | true => (q, oldK.join kind) :: rest
    | false => (q, oldK) :: upsertFakeBorrow rest p kind

noncomputable def collectDerefPrefixPlaces (lid : LocalId) (accPrefix : List ProjElem) :
    List ProjElem → List Place
  | [] => []
  | .deref :: rest =>
    { localId := lid, proj := accPrefix } ::
      collectDerefPrefixPlaces lid (accPrefix ++ [.deref]) rest
  | e :: rest =>
    collectDerefPrefixPlaces lid (accPrefix ++ [e]) rest

noncomputable def upsertAllPlaces (fbs : FakeBorrowList) (ps : List Place) (kind : FakeBorrowKind) :
    FakeBorrowList :=
  match ps with
  | [] => fbs
  | p :: rest => upsertAllPlaces (upsertFakeBorrow fbs p kind) rest kind

/-- `FakeBorrowCollector::fake_borrow` (`util.rs:117-124`): borrow `p` AND all its deref prefixes. -/
noncomputable def recordFakeBorrow (fbs : FakeBorrowList) (p : Place) (kind : FakeBorrowKind) :
    FakeBorrowList :=
  let fbs1 := upsertFakeBorrow fbs p kind
  upsertAllPlaces fbs1 (collectDerefPrefixPlaces p.localId [] p.proj) kind

/-- `FakeBorrowCollector::visit_binding` (`util.rs:198-230`): borrow ONLY deref prefixes of `source`
with `FakeBorrowKind::Shallow` (permitting unswitched local mutation `u = true`). -/
noncomputable def recordBindingFakeBorrows (fbs : FakeBorrowList) (source : Place) :
    FakeBorrowList :=
  upsertAllPlaces fbs (collectDerefPrefixPlaces source.localId [] source.proj) .shallow

noncomputable def localInList (q : LocalId) : List LocalId → Bool
  | [] => false
  | k :: rest => natBeq k q || localInList q rest

noncomputable def fakeBorrowsAllowWrite (fbs : FakeBorrowList) (wp : Place) : Bool :=
  match fbs with
  | [] => true
  | (bp, kind) :: rest =>
    !borrowConflictsWithWrite bp kind wp && fakeBorrowsAllowWrite rest wp

noncomputable def borrowckAdmitsWrite
    (borrowedPointees : List LocalId) (fbs : FakeBorrowList) (wp : Place) : Bool :=
  !localInList wp.localId borrowedPointees && fakeBorrowsAllowWrite fbs wp

/-! ## Section 3: Operational Decision-Tree Matching & Guard-Stability Soundness (`Theorem 1`) -/

inductive TestOp where
  | switchVariant (p : Place)
  | switchBool (p : Place)
  | derefSmartBool (p : Place)

noncomputable def extractVariantTag : Option Val → Option Nat
  | some (.enumAdt tag _ _) => some tag
  | _ => none

noncomputable def extractBoolTag : Option Val → Option Nat
  | some (.boolVal false) => some 0
  | some (.boolVal true) => some 1
  | _ => none

noncomputable def extractSmartBoolTag : Option Val → Option Nat
  | some (.smartPtr (.boolVal false)) => some 0
  | some (.smartPtr (.boolVal true)) => some 1
  | _ => none

noncomputable def evalTestOp (st : Store) : TestOp → Option Nat
  | .switchVariant p => extractVariantTag (evalPlace st p)
  | .switchBool p => extractBoolTag (evalPlace st p)
  | .derefSmartBool p => extractSmartBoolTag (evalPlace st p)

noncomputable def collectTestOpFakeBorrows (fbs : FakeBorrowList) : TestOp → FakeBorrowList
  | .switchVariant p => recordFakeBorrow fbs p .shallow
  | .switchBool p => recordFakeBorrow fbs p .shallow
  | .derefSmartBool p => recordFakeBorrow fbs p .deep

structure GuardWrite where
  target : Place
  newVal : Val

noncomputable def applyGuardWrites (st : Store) : List GuardWrite → Option Store
  | [] => some st
  | w :: rest =>
    match writePlace st w.target w.newVal with
    | some st' => applyGuardWrites st' rest
    | none => none

inductive DecTree where
  | armLeaf (armId : Nat)
  | guardedArm (boundSources : List Place) (writes : List GuardWrite) (guardPass : Bool)
      (armId : Nat) (otherwiseTree : DecTree)
  | testBoolNode (p : Place) (onFalse : DecTree) (onTrue : DecTree)
  | testDerefBoolNode (p : Place) (onFalse : DecTree) (onTrue : DecTree)
  | switchTwoVariants (p : Place) (onVar0 : DecTree) (onVar1 : DecTree)
  | unreachableLeaf

inductive DecTreeOutcome where
  | matched (armId : Nat) (finalStore : Store)
  | stuckTypeError
  | reachedUnreachableUB

noncomputable def evalDecTree : DecTree → Store → DecTreeOutcome
  | .armLeaf armId, st => .matched armId st
  | .guardedArm _ writes guardPass armId otherwiseTree, st =>
    match applyGuardWrites st writes with
    | none => .stuckTypeError
    | some stAfterGuard =>
      match guardPass with
      | true => .matched armId stAfterGuard
      | false => evalDecTree otherwiseTree stAfterGuard
  | .testBoolNode p onFalse onTrue, st =>
    match evalTestOp st (.switchBool p) with
    | some 0 => evalDecTree onFalse st
    | some 1 => evalDecTree onTrue st
    | _ => .stuckTypeError
  | .testDerefBoolNode p onFalse onTrue, st =>
    match evalTestOp st (.derefSmartBool p) with
    | some 0 => evalDecTree onFalse st
    | some 1 => evalDecTree onTrue st
    | _ => .stuckTypeError
  | .switchTwoVariants p onVar0 onVar1, st =>
    match evalTestOp st (.switchVariant p) with
    | some 0 => evalDecTree onVar0 st
    | some 1 => evalDecTree onVar1 st
    | _ => .stuckTypeError
  | .unreachableLeaf, _ => .reachedUnreachableUB

noncomputable def collectBindingsFakeBorrows (fbs : FakeBorrowList) : List Place → FakeBorrowList
  | [] => fbs
  | src :: rest => collectBindingsFakeBorrows (recordBindingFakeBorrows fbs src) rest

noncomputable def collectTreeFakeBorrows (fbs : FakeBorrowList) : DecTree → FakeBorrowList
  | .armLeaf _ => fbs
  | .guardedArm boundSources _ _ _ otherwiseTree =>
    let fbs1 := collectBindingsFakeBorrows fbs boundSources
    collectTreeFakeBorrows fbs1 otherwiseTree
  | .testBoolNode p onFalse onTrue =>
    let fbs1 := collectTestOpFakeBorrows fbs (.switchBool p)
    let fbs2 := collectTreeFakeBorrows fbs1 onFalse
    collectTreeFakeBorrows fbs2 onTrue
  | .testDerefBoolNode p onFalse onTrue =>
    let fbs1 := collectTestOpFakeBorrows fbs (.derefSmartBool p)
    let fbs2 := collectTreeFakeBorrows fbs1 onFalse
    collectTreeFakeBorrows fbs2 onTrue
  | .switchTwoVariants p onVar0 onVar1 =>
    let fbs1 := collectTestOpFakeBorrows fbs (.switchVariant p)
    let fbs2 := collectTreeFakeBorrows fbs1 onVar0
    collectTreeFakeBorrows fbs2 onVar1
  | .unreachableLeaf => fbs

noncomputable def valRefsIn (borrowedPointees : List LocalId) : Val → Bool
  | .scalar _ | .boolVal _ => true
  | .tuple f0 f1 => valRefsIn borrowedPointees f0 && valRefsIn borrowedPointees f1
  | .enumAdt _ f0 f1 => valRefsIn borrowedPointees f0 && valRefsIn borrowedPointees f1
  | .boxVal inner => valRefsIn borrowedPointees inner
  | .smartPtr backing => valRefsIn borrowedPointees backing
  | .refLocal target => localInList target borrowedPointees

noncomputable def storeRefsIn (borrowedPointees : List LocalId) : Store → Bool
  | [] => true
  | (_, v) :: rest => valRefsIn borrowedPointees v && storeRefsIn borrowedPointees rest

noncomputable def guardWritesAdmitted
    (borrowedPointees : List LocalId) (fbs : FakeBorrowList) : List GuardWrite → Bool
  | [] => true
  | w :: rest =>
    borrowckAdmitsWrite borrowedPointees fbs w.target &&
      valRefsIn borrowedPointees w.newVal &&
      guardWritesAdmitted borrowedPointees fbs rest

noncomputable def allTreeGuardsBorrowckOk
    (borrowedPointees : List LocalId) (fbs : FakeBorrowList) : DecTree → Bool
  | .armLeaf _ => true
  | .guardedArm _ writes _ _ otherwiseTree =>
    guardWritesAdmitted borrowedPointees fbs writes &&
      allTreeGuardsBorrowckOk borrowedPointees fbs otherwiseTree
  | .testBoolNode _ onFalse onTrue =>
    allTreeGuardsBorrowckOk borrowedPointees fbs onFalse &&
      allTreeGuardsBorrowckOk borrowedPointees fbs onTrue
  | .testDerefBoolNode _ onFalse onTrue =>
    allTreeGuardsBorrowckOk borrowedPointees fbs onFalse &&
      allTreeGuardsBorrowckOk borrowedPointees fbs onTrue
  | .switchTwoVariants _ onVar0 onVar1 =>
    allTreeGuardsBorrowckOk borrowedPointees fbs onVar0 &&
      allTreeGuardsBorrowckOk borrowedPointees fbs onVar1
  | .unreachableLeaf => true

/-! ### Monotonicity & Membership Lemmas for `FakeBorrowCollector` -/

noncomputable def lookupFakeBorrow : FakeBorrowList → Place → Option FakeBorrowKind
  | [], _ => none
  | (q, k) :: rest, p =>
    match Place.beq q p with
    | true => some k
    | false => lookupFakeBorrow rest p

noncomputable def hasFakeBorrowAtLeast (fbs : FakeBorrowList) (p : Place) (req : FakeBorrowKind) :
    Bool :=
  match lookupFakeBorrow fbs p with
  | some k => req.le k
  | none => false

theorem borrowConflicts_mono {bp : Place} {k1 k2 : FakeBorrowKind} {wp : Place}
    (hle : k1.le k2 = true)
    (hc : borrowConflictsWithWrite bp k1 wp = true) :
    borrowConflictsWithWrite bp k2 wp = true := by
  dsimp only [borrowConflictsWithWrite] at hc ⊢
  cases hloc : natBeq bp.localId wp.localId with
  | false =>
    rw [hloc] at hc
    contradiction
  | true =>
    rw [hloc] at hc
    dsimp only at hc ⊢
    have hloop : ∀ (ps ws : List ProjElem),
        projComponentsConflict k1 ps ws = true →
        projComponentsConflict k2 ps ws = true := by
      intro ps
      induction ps with
      | nil =>
        intro ws hsub
        cases ws with
        | nil => rfl
        | cons _ _ =>
          dsimp only [projComponentsConflict] at hsub ⊢
          cases k1 <;> cases k2 <;> first | rfl | contradiction
      | cons bElem bRest ih =>
        intro ws hsub
        cases ws with
        | nil => exact hsub
        | cons wElem wRest =>
          dsimp only [projComponentsConflict] at hsub ⊢
          cases heq : ProjElem.beq bElem wElem with
          | false =>
            rw [heq] at hsub
            contradiction
          | true =>
            rw [heq] at hsub
            dsimp only at hsub ⊢
            exact ih wRest hsub
    exact hloop bp.proj wp.proj hc

theorem fakeBorrowsAllowWrite_respects_lookup
    {fbs : FakeBorrowList} {bp : Place} {req : FakeBorrowKind} {wp : Place}
    (hhas : hasFakeBorrowAtLeast fbs bp req = true)
    (hallow : fakeBorrowsAllowWrite fbs wp = true) :
    borrowConflictsWithWrite bp req wp = false := by
  induction fbs with
  | nil => contradiction
  | cons hd _ ih =>
    cases hd with
    | mk q k =>
      dsimp only [fakeBorrowsAllowWrite] at hallow
      rcases bool_and_eq_true hallow with ⟨hq, hallowTail⟩
      have hqFalse : borrowConflictsWithWrite q k wp = false := bool_not_eq_true hq
      dsimp only [hasFakeBorrowAtLeast, lookupFakeBorrow] at hhas
      cases hqp : Place.beq q bp with
      | true =>
        rw [hqp] at hhas
        dsimp only at hhas
        have hqeq : q = bp := placeBeq_eq_of_true hqp
        subst hqeq
        cases hc : borrowConflictsWithWrite q req wp with
        | false => rfl
        | true =>
          have hc2 : borrowConflictsWithWrite q k wp = true :=
            borrowConflicts_mono hhas hc
          rw [hc2] at hqFalse
          contradiction
      | false =>
        rw [hqp] at hhas
        dsimp only at hhas
        exact ih hhas hallowTail

theorem hasFakeBorrowAtLeast_upsert_self (fbs : FakeBorrowList) (p : Place) (k : FakeBorrowKind) :
    hasFakeBorrowAtLeast (upsertFakeBorrow fbs p k) p k = true := by
  induction fbs with
  | nil =>
    dsimp only [upsertFakeBorrow, hasFakeBorrowAtLeast, lookupFakeBorrow]
    rw [placeBeq_refl p]
    exact fakeBorrowKind_le_refl k
  | cons hd _ ih =>
    cases hd with
    | mk q oldK =>
      dsimp only [upsertFakeBorrow]
      cases hqp : Place.beq q p with
      | true =>
        dsimp only [hasFakeBorrowAtLeast, lookupFakeBorrow]
        rw [hqp]
        exact fakeBorrowKind_le_join_right oldK k
      | false =>
        dsimp only [hasFakeBorrowAtLeast, lookupFakeBorrow]
        rw [hqp]
        exact ih

theorem hasFakeBorrowAtLeast_upsert_preserves
    (fbs : FakeBorrowList) (p q : Place) (k req : FakeBorrowKind)
    (h : hasFakeBorrowAtLeast fbs q req = true) :
    hasFakeBorrowAtLeast (upsertFakeBorrow fbs p k) q req = true := by
  induction fbs with
  | nil => contradiction
  | cons hd _ ih =>
    cases hd with
    | mk r oldK =>
      dsimp only [upsertFakeBorrow]
      dsimp only [hasFakeBorrowAtLeast, lookupFakeBorrow] at h
      cases hrp : Place.beq r p with
      | true =>
        dsimp only [hasFakeBorrowAtLeast, lookupFakeBorrow]
        cases hrq : Place.beq r q with
        | true =>
          rw [hrq] at h
          dsimp only at h ⊢
          exact fakeBorrowKind_le_trans h (fakeBorrowKind_le_join_left oldK k)
        | false =>
          rw [hrq] at h
          exact h
      | false =>
        dsimp only [hasFakeBorrowAtLeast, lookupFakeBorrow]
        cases hrq : Place.beq r q with
        | true =>
          rw [hrq] at h
          exact h
        | false =>
          rw [hrq] at h
          dsimp only at h ⊢
          exact ih h

theorem hasFakeBorrowAtLeast_upsertAll_preserves
    (ps : List Place) (fbs : FakeBorrowList) (q : Place) (k req : FakeBorrowKind)
    (h : hasFakeBorrowAtLeast fbs q req = true) :
    hasFakeBorrowAtLeast (upsertAllPlaces fbs ps k) q req = true := by
  induction ps generalizing fbs with
  | nil => exact h
  | cons p _ ih =>
    dsimp only [upsertAllPlaces]
    exact ih (upsertFakeBorrow fbs p k) (hasFakeBorrowAtLeast_upsert_preserves fbs p q k req h)

theorem hasFakeBorrowAtLeast_upsertAll_mem
    (ps : List Place) (fbs : FakeBorrowList) (q : Place) (k : FakeBorrowKind)
    (hmem : q ∈ ps) :
    hasFakeBorrowAtLeast (upsertAllPlaces fbs ps k) q k = true := by
  induction ps generalizing fbs with
  | nil => cases hmem
  | cons p rest ih =>
    dsimp only [upsertAllPlaces]
    cases hmem with
    | head =>
      exact hasFakeBorrowAtLeast_upsertAll_preserves rest (upsertFakeBorrow fbs q k) q k k
        (hasFakeBorrowAtLeast_upsert_self fbs q k)
    | tail _ htail =>
      exact ih (upsertFakeBorrow fbs p k) htail

theorem hasFakeBorrowAtLeast_recordFakeBorrow_self
    (fbs : FakeBorrowList) (p : Place) (k : FakeBorrowKind) :
    hasFakeBorrowAtLeast (recordFakeBorrow fbs p k) p k = true := by
  unfold recordFakeBorrow
  exact hasFakeBorrowAtLeast_upsertAll_preserves
    (collectDerefPrefixPlaces p.localId [] p.proj)
    (upsertFakeBorrow fbs p k) p k k
    (hasFakeBorrowAtLeast_upsert_self fbs p k)

theorem hasFakeBorrowAtLeast_recordFakeBorrow_prefix
    (fbs : FakeBorrowList) (p q : Place) (k : FakeBorrowKind)
    (hmem : q ∈ collectDerefPrefixPlaces p.localId [] p.proj) :
    hasFakeBorrowAtLeast (recordFakeBorrow fbs p k) q k = true := by
  unfold recordFakeBorrow
  exact hasFakeBorrowAtLeast_upsertAll_mem
    (collectDerefPrefixPlaces p.localId [] p.proj)
    (upsertFakeBorrow fbs p k) q k hmem

theorem hasFakeBorrowAtLeast_recordFakeBorrow_preserves
    (fbs : FakeBorrowList) (p q : Place) (k req : FakeBorrowKind)
    (h : hasFakeBorrowAtLeast fbs q req = true) :
    hasFakeBorrowAtLeast (recordFakeBorrow fbs p k) q req = true := by
  unfold recordFakeBorrow
  exact hasFakeBorrowAtLeast_upsertAll_preserves
    (collectDerefPrefixPlaces p.localId [] p.proj)
    (upsertFakeBorrow fbs p k) q k req
    (hasFakeBorrowAtLeast_upsert_preserves fbs p q k req h)

theorem hasFakeBorrowAtLeast_collectTree_preserves
    (dt : DecTree) (fbs : FakeBorrowList) (q : Place) (req : FakeBorrowKind)
    (h : hasFakeBorrowAtLeast fbs q req = true) :
    hasFakeBorrowAtLeast (collectTreeFakeBorrows fbs dt) q req = true := by
  induction dt generalizing fbs with
  | armLeaf _ => exact h
  | unreachableLeaf => exact h
  | guardedArm srcs _ _ _ oTree ih =>
    dsimp only [collectTreeFakeBorrows]
    have hbind : ∀ (ss : List Place) (acc : FakeBorrowList),
        hasFakeBorrowAtLeast acc q req = true →
        hasFakeBorrowAtLeast (collectBindingsFakeBorrows acc ss) q req = true := by
      intro ss
      induction ss with
      | nil => intro _ hacc; exact hacc
      | cons _ _ ihs =>
        intro acc hacc
        dsimp only [collectBindingsFakeBorrows, recordBindingFakeBorrows]
        exact ihs _ (hasFakeBorrowAtLeast_upsertAll_preserves _ acc q .shallow req hacc)
    exact ih _ (hbind srcs fbs h)
  | testBoolNode p fTree tTree ihF ihT =>
    dsimp only [collectTreeFakeBorrows, collectTestOpFakeBorrows]
    exact ihT _ (ihF _ (hasFakeBorrowAtLeast_recordFakeBorrow_preserves fbs p q .shallow req h))
  | testDerefBoolNode p fTree tTree ihF ihT =>
    dsimp only [collectTreeFakeBorrows, collectTestOpFakeBorrows]
    exact ihT _ (ihF _ (hasFakeBorrowAtLeast_recordFakeBorrow_preserves fbs p q .deep req h))
  | switchTwoVariants p v0Tree v1Tree ih0 ih1 =>
    dsimp only [collectTreeFakeBorrows, collectTestOpFakeBorrows]
    exact ih1 _ (ih0 _ (hasFakeBorrowAtLeast_recordFakeBorrow_preserves fbs p q .shallow req h))

/-! ### Store-Ref & Projection-Frame Stability Lemmas -/

theorem writeAtProj_preserves_valRefsIn
    {borrowedPointees : List LocalId} {v v' newVal : Val} {ps : List ProjElem}
    (hv : valRefsIn borrowedPointees v = true)
    (hnew : valRefsIn borrowedPointees newVal = true)
    (hw : writeAtProj v ps newVal = some v') :
    valRefsIn borrowedPointees v' = true := by
  induction ps generalizing v v' with
  | nil =>
    cases v <;> (injection hw with hv'; rw [← hv']; exact hnew)
  | cons elem rest ih =>
    cases elem with
    | deref =>
      cases v with
      | boxVal inner =>
        change valRefsIn borrowedPointees inner = true at hv
        change (match writeAtProj inner rest newVal with
          | some inner' => some (.boxVal inner') | none => none) = some v' at hw
        cases hsub : writeAtProj inner rest newVal with
        | none => rw [hsub] at hw; contradiction
        | some inner' =>
          rw [hsub] at hw
          injection hw with hv'
          rw [← hv']
          change valRefsIn borrowedPointees inner' = true
          exact ih hv hsub
      | scalar _ | boolVal _ | tuple _ _ | enumAdt _ _ _ | smartPtr _ | refLocal _ =>
        contradiction
    | field idx =>
      cases idx with
      | zero =>
        cases v with
        | tuple f0 f1 =>
          rcases bool_and_eq_true hv with ⟨hf0, hf1⟩
          change (match writeAtProj f0 rest newVal with
            | some f0' => some (.tuple f0' f1) | none => none) = some v' at hw
          cases hsub : writeAtProj f0 rest newVal with
          | none => rw [hsub] at hw; contradiction
          | some f0' =>
            rw [hsub] at hw
            injection hw with hv'
            rw [← hv']
            change (valRefsIn borrowedPointees f0' && valRefsIn borrowedPointees f1) = true
            rw [ih hf0 hsub, hf1]
            rfl
        | smartPtr b =>
          change valRefsIn borrowedPointees b = true at hv
          change (match writeAtProj b rest newVal with
            | some b' => some (.smartPtr b') | none => none) = some v' at hw
          cases hsub : writeAtProj b rest newVal with
          | none => rw [hsub] at hw; contradiction
          | some b' =>
            rw [hsub] at hw
            injection hw with hv'
            rw [← hv']
            change valRefsIn borrowedPointees b' = true
            exact ih hv hsub
        | scalar _ | boolVal _ | enumAdt _ _ _ | boxVal _ | refLocal _ =>
          contradiction
      | succ idx1 =>
        cases idx1 with
        | zero =>
          cases v with
          | tuple f0 f1 =>
            rcases bool_and_eq_true hv with ⟨hf0, hf1⟩
            change (match writeAtProj f1 rest newVal with
              | some f1' => some (.tuple f0 f1') | none => none) = some v' at hw
            cases hsub : writeAtProj f1 rest newVal with
            | none => rw [hsub] at hw; contradiction
            | some f1' =>
              rw [hsub] at hw
              injection hw with hv'
              rw [← hv']
              change (valRefsIn borrowedPointees f0 && valRefsIn borrowedPointees f1') = true
              rw [hf0, ih hf1 hsub]
              rfl
          | scalar _ | boolVal _ | enumAdt _ _ _ | boxVal _ | smartPtr _ | refLocal _ =>
            contradiction
        | succ _ =>
          cases v <;> contradiction
    | downcastField expVar idx =>
      cases idx with
      | zero =>
        cases v with
        | enumAdt tag f0 f1 =>
          rcases bool_and_eq_true hv with ⟨hf0, hf1⟩
          change (match natBeq tag expVar with
            | true => match writeAtProj f0 rest newVal with
              | some f0' => some (.enumAdt tag f0' f1) | none => none
            | false => none) = some v' at hw
          cases htag : natBeq tag expVar with
          | false => rw [htag] at hw; contradiction
          | true =>
            rw [htag] at hw
            change (match writeAtProj f0 rest newVal with
              | some f0' => some (.enumAdt tag f0' f1) | none => none) = some v' at hw
            cases hsub : writeAtProj f0 rest newVal with
            | none => rw [hsub] at hw; contradiction
            | some f0' =>
              rw [hsub] at hw
              injection hw with hv'
              rw [← hv']
              change (valRefsIn borrowedPointees f0' && valRefsIn borrowedPointees f1) = true
              rw [ih hf0 hsub, hf1]
              rfl
        | scalar _ | boolVal _ | tuple _ _ | boxVal _ | smartPtr _ | refLocal _ =>
          contradiction
      | succ idx1 =>
        cases idx1 with
        | zero =>
          cases v with
          | enumAdt tag f0 f1 =>
            rcases bool_and_eq_true hv with ⟨hf0, hf1⟩
            change (match natBeq tag expVar with
              | true => match writeAtProj f1 rest newVal with
                | some f1' => some (.enumAdt tag f0 f1') | none => none
              | false => none) = some v' at hw
            cases htag : natBeq tag expVar with
            | false => rw [htag] at hw; contradiction
            | true =>
              rw [htag] at hw
              change (match writeAtProj f1 rest newVal with
                | some f1' => some (.enumAdt tag f0 f1') | none => none) = some v' at hw
              cases hsub : writeAtProj f1 rest newVal with
              | none => rw [hsub] at hw; contradiction
              | some f1' =>
                rw [hsub] at hw
                injection hw with hv'
                rw [← hv']
                change (valRefsIn borrowedPointees f0 && valRefsIn borrowedPointees f1') = true
                rw [hf0, ih hf1 hsub]
                rfl
          | scalar _ | boolVal _ | tuple _ _ | boxVal _ | smartPtr _ | refLocal _ =>
            contradiction
        | succ _ =>
          cases v <;> contradiction

theorem storeLookup_valRefsIn {borrowedPointees : List LocalId} {st : Store} {q : LocalId} {v : Val}
    (hst : storeRefsIn borrowedPointees st = true)
    (hlk : storeLookup st q = some v) :
    valRefsIn borrowedPointees v = true := by
  induction st with
  | nil => contradiction
  | cons hd _ ih =>
    cases hd with
    | mk k kv =>
      rcases bool_and_eq_true hst with ⟨hkv, hstTail⟩
      change (match natBeq k q with | true => some kv | false => storeLookup _ q) = some v at hlk
      cases hkq : natBeq k q with
      | true =>
        rw [hkq] at hlk
        injection hlk with heq
        rw [← heq]
        exact hkv
      | false =>
        rw [hkq] at hlk
        exact ih hstTail hlk

theorem storeUpdate_preserves_storeRefsIn
    {borrowedPointees : List LocalId} {st : Store} {q : LocalId} {v : Val}
    (hst : storeRefsIn borrowedPointees st = true)
    (hv : valRefsIn borrowedPointees v = true) :
    storeRefsIn borrowedPointees (storeUpdate st q v) = true := by
  induction st with
  | nil =>
    change (valRefsIn borrowedPointees v && true) = true
    rw [hv]
    rfl
  | cons hd tail ih =>
    cases hd with
    | mk k kv =>
      rcases bool_and_eq_true hst with ⟨hkv, hstTail⟩
      change storeRefsIn borrowedPointees (match natBeq k q with
        | true => (k, v) :: tail | false => (k, kv) :: storeUpdate tail q v) = true
      cases hkq : natBeq k q with
      | true =>
        change (valRefsIn borrowedPointees v && storeRefsIn borrowedPointees tail) = true
        rw [hv, hstTail]
        rfl
      | false =>
        change (valRefsIn borrowedPointees kv && storeRefsIn borrowedPointees (storeUpdate tail q v)) = true
        rw [hkv, ih hstTail]
        rfl

theorem evalProj_ignores_unborrowed_store_update
    {borrowedPointees : List LocalId} {st : Store} {wLoc : LocalId} {wVal : Val}
    (hwNotPointee : localInList wLoc borrowedPointees = false)
    (v : Val) (hv : valRefsIn borrowedPointees v = true)
    (hst : storeRefsIn borrowedPointees st = true)
    (ps : List ProjElem) :
    evalProj (storeUpdate st wLoc wVal) v ps = evalProj st v ps := by
  induction ps generalizing v with
  | nil => rfl
  | cons elem rest ih =>
    cases elem with
    | deref =>
      cases v with
      | boxVal inner => exact ih inner hv
      | refLocal target =>
        change localInList target borrowedPointees = true at hv
        change (match storeLookup (storeUpdate st wLoc wVal) target with
          | some tv => evalProj (storeUpdate st wLoc wVal) tv rest | none => none) =
          (match storeLookup st target with | some tv => evalProj st tv rest | none => none)
        have hne : natBeq wLoc target = false := by
          cases hwt : natBeq wLoc target with
          | false => rfl
          | true =>
            have heq : wLoc = target := natBeq_eq_of_true hwt
            subst heq
            rw [hv] at hwNotPointee
            contradiction
        rw [storeLookup_update_ne st wVal hne]
        cases hlk : storeLookup st target with
        | none => rfl
        | some tv =>
          exact ih tv (storeLookup_valRefsIn hst hlk)
      | scalar _ | boolVal _ | tuple _ _ | enumAdt _ _ _ | smartPtr _ => rfl
    | field idx =>
      cases idx with
      | zero =>
        cases v with
        | tuple f0 _ =>
          rcases bool_and_eq_true hv with ⟨hf0, _⟩
          exact ih f0 hf0
        | smartPtr b => exact ih b hv
        | scalar _ | boolVal _ | enumAdt _ _ _ | boxVal _ | refLocal _ => rfl
      | succ idx1 =>
        cases idx1 with
        | zero =>
          cases v with
          | tuple _ f1 =>
            rcases bool_and_eq_true hv with ⟨_, hf1⟩
            exact ih f1 hf1
          | scalar _ | boolVal _ | enumAdt _ _ _ | boxVal _ | smartPtr _ | refLocal _ => rfl
        | succ _ =>
          cases v <;> rfl
    | downcastField expVar idx =>
      cases idx with
      | zero =>
        cases v with
        | enumAdt tag f0 _ =>
          rcases bool_and_eq_true hv with ⟨hf0, _⟩
          change (match natBeq tag expVar with
            | true => evalProj (storeUpdate st wLoc wVal) f0 rest | false => none) =
            (match natBeq tag expVar with | true => evalProj st f0 rest | false => none)
          cases htag : natBeq tag expVar with
          | false => rfl
          | true => exact ih f0 hf0
        | scalar _ | boolVal _ | tuple _ _ | boxVal _ | smartPtr _ | refLocal _ => rfl
      | succ idx1 =>
        cases idx1 with
        | zero =>
          cases v with
          | enumAdt tag _ f1 =>
            rcases bool_and_eq_true hv with ⟨_, hf1⟩
            change (match natBeq tag expVar with
              | true => evalProj (storeUpdate st wLoc wVal) f1 rest | false => none) =
              (match natBeq tag expVar with | true => evalProj st f1 rest | false => none)
            cases htag : natBeq tag expVar with
            | false => rfl
            | true => exact ih f1 hf1
          | scalar _ | boolVal _ | tuple _ _ | boxVal _ | smartPtr _ | refLocal _ => rfl
        | succ _ =>
          cases v <;> rfl

noncomputable def noDerefPrefixConflicts (kind : FakeBorrowKind)
    (acc : List ProjElem) (bProj wProj : List ProjElem) : Bool :=
  match bProj with
  | [] => true
  | .deref :: rest =>
    !projComponentsConflict kind acc wProj &&
      noDerefPrefixConflicts kind (acc ++ [.deref]) rest wProj
  | e :: rest =>
    noDerefPrefixConflicts kind (acc ++ [e]) rest wProj

theorem collectDerefPrefixPlaces_gives_noDerefPrefixConflicts
    {fbs : FakeBorrowList} {lid : LocalId} {kind : FakeBorrowKind} {wp : Place}
    (hloc : natBeq lid wp.localId = true)
    (hallow : fakeBorrowsAllowWrite fbs wp = true) :
    ∀ (acc bProj : List ProjElem),
      (∀ q ∈ collectDerefPrefixPlaces lid acc bProj, hasFakeBorrowAtLeast fbs q kind = true) →
      noDerefPrefixConflicts kind acc bProj wp.proj = true := by
  intro acc bProj
  induction bProj generalizing acc with
  | nil => intro _; rfl
  | cons elem rest ih =>
    intro hmem
    cases elem with
    | deref =>
      dsimp only [noDerefPrefixConflicts]
      have hhead : hasFakeBorrowAtLeast fbs { localId := lid, proj := acc } kind = true :=
        hmem { localId := lid, proj := acc } (List.Mem.head _)
      have hnc : borrowConflictsWithWrite { localId := lid, proj := acc } kind wp = false :=
        fakeBorrowsAllowWrite_respects_lookup hhead hallow
      dsimp only [borrowConflictsWithWrite] at hnc
      rw [hloc] at hnc
      dsimp only at hnc
      rw [hnc]
      have htail := ih (acc ++ [.deref]) (fun q hq => hmem q (List.Mem.tail _ hq))
      rw [htail]
      rfl
    | field idx =>
      dsimp only [noDerefPrefixConflicts]
      exact ih (acc ++ [.field idx]) hmem
    | downcastField v idx =>
      dsimp only [noDerefPrefixConflicts]
      exact ih (acc ++ [.downcastField v idx]) hmem

theorem step_noDerefPrefixConflicts_same_elem
    {kind : FakeBorrowKind} {e : ProjElem} {bRest wRest : List ProjElem}
    (h : noDerefPrefixConflicts kind [e] bRest (e :: wRest) = true) :
    noDerefPrefixConflicts kind [] bRest wRest = true := by
  have hgen : ∀ (pre : List ProjElem),
      noDerefPrefixConflicts kind (e :: pre) bRest (e :: wRest) = true →
      noDerefPrefixConflicts kind pre bRest wRest = true := by
    clear h
    induction bRest with
    | nil => intro _ _; rfl
    | cons b0 _ ih =>
      intro pre hp
      cases b0 with
      | deref =>
        dsimp only [noDerefPrefixConflicts, List.cons_append] at hp ⊢
        have hce : projComponentsConflict kind (e :: pre) (e :: wRest) =
            projComponentsConflict kind pre wRest := by
          dsimp only [projComponentsConflict]
          rw [projElemBeq_refl e]
        rw [hce] at hp
        rcases bool_and_eq_true hp with ⟨hc, hpTail⟩
        rw [hc]
        exact ih (pre ++ [ProjElem.deref]) hpTail
      | field idx =>
        dsimp only [noDerefPrefixConflicts, List.cons_append] at hp ⊢
        exact ih (pre ++ [.field idx]) hp
      | downcastField v idx =>
        dsimp only [noDerefPrefixConflicts, List.cons_append] at hp ⊢
        exact ih (pre ++ [.downcastField v idx]) hp
  exact hgen [] h

theorem hasDerefInTail_append_field (pre : List ProjElem) (idx : Nat)
    (h : hasDerefInTail pre = false) :
    hasDerefInTail (pre ++ [.field idx]) = false := by
  induction pre with
  | nil => rfl
  | cons p _ ih =>
    cases p with
    | deref => contradiction
    | field _ => exact ih h
    | downcastField _ _ => exact ih h

theorem hasDerefInTail_append_downcast (pre : List ProjElem) (v idx : Nat)
    (h : hasDerefInTail pre = false) :
    hasDerefInTail (pre ++ [.downcastField v idx]) = false := by
  induction pre with
  | nil => rfl
  | cons p _ ih =>
    cases p with
    | deref => contradiction
    | field _ => exact ih h
    | downcastField _ _ => exact ih h

theorem noEmptyWrite_when_derefPrefixesProtected
    (kind : FakeBorrowKind) (pre bs : List ProjElem)
    (hpre : hasDerefInTail pre = false)
    (hbs : hasDerefInTail bs = true)
    (hnd : noDerefPrefixConflicts kind pre bs [] = true) :
    False := by
  induction bs generalizing pre with
  | nil => contradiction
  | cons x xs ih =>
    cases x with
    | deref =>
      dsimp only [noDerefPrefixConflicts] at hnd
      cases pre with
      | nil =>
        dsimp only [projComponentsConflict] at hnd
        contradiction
      | cons _ _ =>
        dsimp only [projComponentsConflict] at hnd
        rw [hpre] at hnd
        contradiction
    | field idx =>
      dsimp only [hasDerefInTail] at hbs
      dsimp only [noDerefPrefixConflicts] at hnd
      exact ih (pre ++ [.field idx]) (hasDerefInTail_append_field pre idx hpre) hbs hnd
    | downcastField dv idx =>
      dsimp only [hasDerefInTail] at hbs
      dsimp only [noDerefPrefixConflicts] at hnd
      exact ih (pre ++ [.downcastField dv idx])
        (hasDerefInTail_append_downcast pre dv idx hpre) hbs hnd

theorem disjointHeadProj_preserves_evalProj
    (st : Store) (bElem wElem : ProjElem) (bRest wRest : List ProjElem) (v v' newVal : Val)
    (hdisj : ProjElem.beq bElem wElem = false)
    (hw : writeAtProj v (wElem :: wRest) newVal = some v') :
    evalProj st v' (bElem :: bRest) = evalProj st v (bElem :: bRest) := by
  cases wElem with
  | deref =>
    cases v with
    | boxVal inner =>
      change (match writeAtProj inner wRest newVal with
        | some inner' => some (.boxVal inner') | none => none) = some v' at hw
      cases hsub : writeAtProj inner wRest newVal with
      | none => rw [hsub] at hw; contradiction
      | some _ =>
        rw [hsub] at hw
        injection hw with hv'
        rw [← hv']
        cases bElem with
        | deref => contradiction
        | field idx =>
          cases idx with
          | zero => rfl
          | succ idx1 => cases idx1 <;> rfl
        | downcastField _ idx =>
          cases idx with
          | zero => rfl
          | succ idx1 => cases idx1 <;> rfl
    | scalar _ | boolVal _ | tuple _ _ | enumAdt _ _ _ | smartPtr _ | refLocal _ =>
      contradiction
  | field wIdx =>
    cases wIdx with
    | zero =>
      cases v with
      | tuple f0 f1 =>
        change (match writeAtProj f0 wRest newVal with
          | some f0' => some (.tuple f0' f1) | none => none) = some v' at hw
        cases hsub : writeAtProj f0 wRest newVal with
        | none => rw [hsub] at hw; contradiction
        | some _ =>
          rw [hsub] at hw
          injection hw with hv'
          rw [← hv']
          cases bElem with
          | deref => rfl
          | downcastField _ idx =>
            cases idx with
            | zero => rfl
            | succ idx1 => cases idx1 <;> rfl
          | field bIdx =>
            cases bIdx with
            | zero => contradiction
            | succ bIdx1 => cases bIdx1 <;> rfl
      | smartPtr b =>
        change (match writeAtProj b wRest newVal with
          | some b' => some (.smartPtr b') | none => none) = some v' at hw
        cases hsub : writeAtProj b wRest newVal with
        | none => rw [hsub] at hw; contradiction
        | some _ =>
          rw [hsub] at hw
          injection hw with hv'
          rw [← hv']
          cases bElem with
          | deref => rfl
          | downcastField _ idx =>
            cases idx with
            | zero => rfl
            | succ idx1 => cases idx1 <;> rfl
          | field bIdx =>
            cases bIdx with
            | zero => contradiction
            | succ bIdx1 => cases bIdx1 <;> rfl
      | scalar _ | boolVal _ | enumAdt _ _ _ | boxVal _ | refLocal _ =>
        contradiction
    | succ wIdx1 =>
      cases wIdx1 with
      | zero =>
        cases v with
        | tuple f0 f1 =>
          change (match writeAtProj f1 wRest newVal with
            | some f1' => some (.tuple f0 f1') | none => none) = some v' at hw
          cases hsub : writeAtProj f1 wRest newVal with
          | none => rw [hsub] at hw; contradiction
          | some _ =>
            rw [hsub] at hw
            injection hw with hv'
            rw [← hv']
            cases bElem with
            | deref => rfl
            | downcastField _ idx =>
              cases idx with
              | zero => rfl
              | succ idx1 => cases idx1 <;> rfl
            | field bIdx =>
              cases bIdx with
              | zero => rfl
              | succ bIdx1 =>
                cases bIdx1 with
                | zero => contradiction
                | succ _ => rfl
        | scalar _ | boolVal _ | enumAdt _ _ _ | boxVal _ | smartPtr _ | refLocal _ =>
          contradiction
      | succ _ =>
        cases v <;> contradiction
  | downcastField wVar wIdx =>
    cases wIdx with
    | zero =>
      cases v with
      | enumAdt tag f0 f1 =>
        change (match natBeq tag wVar with
          | true => match writeAtProj f0 wRest newVal with
            | some f0' => some (.enumAdt tag f0' f1) | none => none
          | false => none) = some v' at hw
        cases htag : natBeq tag wVar with
        | false => rw [htag] at hw; contradiction
        | true =>
          rw [htag] at hw
          have htagEq : tag = wVar := natBeq_eq_of_true htag
          subst htagEq
          change (match writeAtProj f0 wRest newVal with
            | some f0' => some (.enumAdt tag f0' f1) | none => none) = some v' at hw
          cases hsub : writeAtProj f0 wRest newVal with
          | none => rw [hsub] at hw; contradiction
          | some f0' =>
            rw [hsub] at hw
            injection hw with hv'
            rw [← hv']
            cases bElem with
            | deref => rfl
            | field idx =>
              cases idx with
              | zero => rfl
              | succ idx1 => cases idx1 <;> rfl
            | downcastField bVar bIdx =>
              change (natBeq bVar tag && natBeq bIdx 0) = false at hdisj
              cases bIdx with
              | zero =>
                have hbv : natBeq bVar tag = false := by
                  cases hb : natBeq bVar tag with
                  | false => rfl
                  | true =>
                    rw [hb] at hdisj
                    contradiction
                have htb : natBeq tag bVar = false :=
                  natBeq_false_of_ne (fun hteq => by
                    subst hteq
                    rw [natBeq_refl tag] at hbv
                    contradiction)
                change (match natBeq tag bVar with
                  | true => evalProj st f0' bRest | false => none) =
                  (match natBeq tag bVar with | true => evalProj st f0 bRest | false => none)
                rw [htb]
              | succ bIdx1 =>
                cases bIdx1 <;> rfl
      | scalar _ | boolVal _ | tuple _ _ | boxVal _ | smartPtr _ | refLocal _ =>
        contradiction
    | succ wIdx1 =>
      cases wIdx1 with
      | zero =>
        cases v with
        | enumAdt tag f0 f1 =>
          change (match natBeq tag wVar with
            | true => match writeAtProj f1 wRest newVal with
              | some f1' => some (.enumAdt tag f0 f1') | none => none
            | false => none) = some v' at hw
          cases htag : natBeq tag wVar with
          | false => rw [htag] at hw; contradiction
          | true =>
            rw [htag] at hw
            have htagEq : tag = wVar := natBeq_eq_of_true htag
            subst htagEq
            change (match writeAtProj f1 wRest newVal with
              | some f1' => some (.enumAdt tag f0 f1') | none => none) = some v' at hw
            cases hsub : writeAtProj f1 wRest newVal with
            | none => rw [hsub] at hw; contradiction
            | some f1' =>
              rw [hsub] at hw
              injection hw with hv'
              rw [← hv']
              cases bElem with
              | deref => rfl
              | field idx =>
                cases idx with
                | zero => rfl
                | succ idx1 => cases idx1 <;> rfl
              | downcastField bVar bIdx =>
                change (natBeq bVar tag && natBeq bIdx 1) = false at hdisj
                cases bIdx with
                | zero => rfl
                | succ bIdx1 =>
                  cases bIdx1 with
                  | zero =>
                    have hbv : natBeq bVar tag = false := by
                      cases hb : natBeq bVar tag with
                      | false => rfl
                      | true =>
                        rw [hb] at hdisj
                        contradiction
                    have htb : natBeq tag bVar = false :=
                      natBeq_false_of_ne (fun hteq => by
                        subst hteq
                        rw [natBeq_refl tag] at hbv
                        contradiction)
                    change (match natBeq tag bVar with
                      | true => evalProj st f1' bRest | false => none) =
                      (match natBeq tag bVar with | true => evalProj st f1 bRest | false => none)
                    rw [htb]
                  | succ _ => rfl
        | scalar _ | boolVal _ | tuple _ _ | boxVal _ | smartPtr _ | refLocal _ =>
          contradiction
      | succ _ =>
        cases v <;> contradiction

theorem writeAtProj_preserves_deep_evalProj
    (st : Store) (bProj wProj : List ProjElem) (v v' newVal : Val)
    (hconf : projComponentsConflict .deep bProj wProj = false)
    (hderef : noDerefPrefixConflicts .deep [] bProj wProj = true)
    (hw : writeAtProj v wProj newVal = some v') :
    evalProj st v' bProj = evalProj st v bProj := by
  induction bProj generalizing wProj v v' with
  | nil =>
    cases wProj <;> contradiction
  | cons bElem bRest ih =>
    cases wProj with
    | nil =>
      change (!hasDerefInTail (bElem :: bRest)) = false at hconf
      have hbs : hasDerefInTail (bElem :: bRest) = true := bool_not_eq_false hconf
      exact False.elim (noEmptyWrite_when_derefPrefixesProtected .deep [] (bElem :: bRest) rfl hbs hderef)
    | cons wElem wRest =>
      change (match ProjElem.beq bElem wElem with
        | true => projComponentsConflict .deep bRest wRest | false => false) = false at hconf
      cases heq : ProjElem.beq bElem wElem with
      | false =>
        exact disjointHeadProj_preserves_evalProj st bElem wElem bRest wRest v v' newVal heq hw
      | true =>
        rw [heq] at hconf
        change projComponentsConflict .deep bRest wRest = false at hconf
        have hsame : bElem = wElem := projElemBeq_eq_of_true heq
        subst hsame
        cases bElem with
        | deref =>
          cases v with
          | boxVal inner =>
            change (match writeAtProj inner wRest newVal with
              | some inner' => some (.boxVal inner') | none => none) = some v' at hw
            cases hsub : writeAtProj inner wRest newVal with
            | none => rw [hsub] at hw; contradiction
            | some inner' =>
              rw [hsub] at hw
              injection hw with hv'
              rw [← hv']
              dsimp only [evalProj]
              dsimp only [noDerefPrefixConflicts] at hderef
              rcases bool_and_eq_true hderef with ⟨_, hderefTail⟩
              exact ih wRest inner inner' hconf (step_noDerefPrefixConflicts_same_elem hderefTail) hsub
          | scalar _ | boolVal _ | tuple _ _ | enumAdt _ _ _ | smartPtr _ | refLocal _ =>
            contradiction
        | field idx =>
          have hnd' : noDerefPrefixConflicts .deep [] bRest wRest = true :=
            step_noDerefPrefixConflicts_same_elem hderef
          cases idx with
          | zero =>
            cases v with
            | tuple f0 f1 =>
              change (match writeAtProj f0 wRest newVal with
                | some f0' => some (.tuple f0' f1) | none => none) = some v' at hw
              cases hsub : writeAtProj f0 wRest newVal with
              | none => rw [hsub] at hw; contradiction
              | some f0' =>
                rw [hsub] at hw
                injection hw with hv'
                rw [← hv']
                exact ih wRest f0 f0' hconf hnd' hsub
            | smartPtr b =>
              change (match writeAtProj b wRest newVal with
                | some b' => some (.smartPtr b') | none => none) = some v' at hw
              cases hsub : writeAtProj b wRest newVal with
              | none => rw [hsub] at hw; contradiction
              | some b' =>
                rw [hsub] at hw
                injection hw with hv'
                rw [← hv']
                exact ih wRest b b' hconf hnd' hsub
            | scalar _ | boolVal _ | enumAdt _ _ _ | boxVal _ | refLocal _ =>
              contradiction
          | succ idx1 =>
            cases idx1 with
            | zero =>
              cases v with
              | tuple f0 f1 =>
                change (match writeAtProj f1 wRest newVal with
                  | some f1' => some (.tuple f0 f1') | none => none) = some v' at hw
                cases hsub : writeAtProj f1 wRest newVal with
                | none => rw [hsub] at hw; contradiction
                | some f1' =>
                  rw [hsub] at hw
                  injection hw with hv'
                  rw [← hv']
                  exact ih wRest f1 f1' hconf hnd' hsub
              | scalar _ | boolVal _ | enumAdt _ _ _ | boxVal _ | smartPtr _ | refLocal _ =>
                contradiction
            | succ _ =>
              cases v <;> contradiction
        | downcastField expVar idx =>
          have hnd' : noDerefPrefixConflicts .deep [] bRest wRest = true :=
            step_noDerefPrefixConflicts_same_elem hderef
          cases idx with
          | zero =>
            cases v with
            | enumAdt tag f0 f1 =>
              change (match natBeq tag expVar with
                | true => match writeAtProj f0 wRest newVal with
                  | some f0' => some (.enumAdt tag f0' f1) | none => none
                | false => none) = some v' at hw
              cases htag : natBeq tag expVar with
              | false => rw [htag] at hw; contradiction
              | true =>
                rw [htag] at hw
                change (match writeAtProj f0 wRest newVal with
                  | some f0' => some (.enumAdt tag f0' f1) | none => none) = some v' at hw
                cases hsub : writeAtProj f0 wRest newVal with
                | none => rw [hsub] at hw; contradiction
                | some f0' =>
                  rw [hsub] at hw
                  injection hw with hv'
                  rw [← hv']
                  change (match natBeq tag expVar with | true => evalProj st f0' bRest | false => none) =
                    (match natBeq tag expVar with | true => evalProj st f0 bRest | false => none)
                  rw [htag]
                  exact ih wRest f0 f0' hconf hnd' hsub
            | scalar _ | boolVal _ | tuple _ _ | boxVal _ | smartPtr _ | refLocal _ =>
              contradiction
          | succ idx1 =>
            cases idx1 with
            | zero =>
              cases v with
              | enumAdt tag f0 f1 =>
                change (match natBeq tag expVar with
                  | true => match writeAtProj f1 wRest newVal with
                    | some f1' => some (.enumAdt tag f0 f1') | none => none
                  | false => none) = some v' at hw
                cases htag : natBeq tag expVar with
                | false => rw [htag] at hw; contradiction
                | true =>
                  rw [htag] at hw
                  change (match writeAtProj f1 wRest newVal with
                    | some f1' => some (.enumAdt tag f0 f1') | none => none) = some v' at hw
                  cases hsub : writeAtProj f1 wRest newVal with
                  | none => rw [hsub] at hw; contradiction
                  | some f1' =>
                    rw [hsub] at hw
                    injection hw with hv'
                    rw [← hv']
                    change (match natBeq tag expVar with | true => evalProj st f1' bRest | false => none) =
                      (match natBeq tag expVar with | true => evalProj st f1 bRest | false => none)
                    rw [htag]
                    exact ih wRest f1 f1' hconf hnd' hsub
              | scalar _ | boolVal _ | tuple _ _ | boxVal _ | smartPtr _ | refLocal _ =>
                contradiction
            | succ _ =>
              cases v <;> contradiction

noncomputable def preservesShallowOutcome (o1 o2 : Option Val) : Prop :=
  extractVariantTag o1 = extractVariantTag o2 ∧ extractBoolTag o1 = extractBoolTag o2

theorem preservesShallowOutcome_of_eq {o1 o2 : Option Val} (h : o1 = o2) :
    preservesShallowOutcome o1 o2 :=
  ⟨congrArg extractVariantTag h, congrArg extractBoolTag h⟩

theorem writeAtProj_preserves_shallow_outcome
    (st : Store) (bProj wProj : List ProjElem) (v v' newVal : Val)
    (hconf : projComponentsConflict .shallow bProj wProj = false)
    (hderef : noDerefPrefixConflicts .shallow [] bProj wProj = true)
    (hw : writeAtProj v wProj newVal = some v') :
    preservesShallowOutcome (evalProj st v' bProj) (evalProj st v bProj) := by
  induction bProj generalizing wProj v v' with
  | nil =>
    cases wProj with
    | nil => contradiction
    | cons wElem wRest =>
      cases wElem with
      | deref =>
        cases v with
        | boxVal inner =>
          change (match writeAtProj inner wRest newVal with
            | some inner' => some (.boxVal inner') | none => none) = some v' at hw
          cases hsub : writeAtProj inner wRest newVal with
          | none => rw [hsub] at hw; contradiction
          | some _ =>
            rw [hsub] at hw
            injection hw with hv'
            rw [← hv']
            exact ⟨rfl, rfl⟩
        | scalar _ | boolVal _ | tuple _ _ | enumAdt _ _ _ | smartPtr _ | refLocal _ =>
          contradiction
      | field wIdx =>
        cases wIdx with
        | zero =>
          cases v with
          | tuple f0 f1 =>
            change (match writeAtProj f0 wRest newVal with
              | some f0' => some (.tuple f0' f1) | none => none) = some v' at hw
            cases hsub : writeAtProj f0 wRest newVal with
            | none => rw [hsub] at hw; contradiction
            | some _ =>
              rw [hsub] at hw
              injection hw with hv'
              rw [← hv']
              exact ⟨rfl, rfl⟩
          | smartPtr b =>
            change (match writeAtProj b wRest newVal with
              | some b' => some (.smartPtr b') | none => none) = some v' at hw
            cases hsub : writeAtProj b wRest newVal with
            | none => rw [hsub] at hw; contradiction
            | some _ =>
              rw [hsub] at hw
              injection hw with hv'
              rw [← hv']
              exact ⟨rfl, rfl⟩
          | scalar _ | boolVal _ | enumAdt _ _ _ | boxVal _ | refLocal _ =>
            contradiction
        | succ wIdx1 =>
          cases wIdx1 with
          | zero =>
            cases v with
            | tuple f0 f1 =>
              change (match writeAtProj f1 wRest newVal with
                | some f1' => some (.tuple f0 f1') | none => none) = some v' at hw
              cases hsub : writeAtProj f1 wRest newVal with
              | none => rw [hsub] at hw; contradiction
              | some _ =>
                rw [hsub] at hw
                injection hw with hv'
                rw [← hv']
                exact ⟨rfl, rfl⟩
            | scalar _ | boolVal _ | enumAdt _ _ _ | boxVal _ | smartPtr _ | refLocal _ =>
              contradiction
          | succ _ =>
            cases v <;> contradiction
      | downcastField expVar wIdx =>
        cases wIdx with
        | zero =>
          cases v with
          | enumAdt tag f0 f1 =>
            change (match natBeq tag expVar with
              | true => match writeAtProj f0 wRest newVal with
                | some f0' => some (.enumAdt tag f0' f1) | none => none
              | false => none) = some v' at hw
            cases htag : natBeq tag expVar with
            | false => rw [htag] at hw; contradiction
            | true =>
              rw [htag] at hw
              change (match writeAtProj f0 wRest newVal with
                | some f0' => some (.enumAdt tag f0' f1) | none => none) = some v' at hw
              cases hsub : writeAtProj f0 wRest newVal with
              | none => rw [hsub] at hw; contradiction
              | some _ =>
                rw [hsub] at hw
                injection hw with hv'
                rw [← hv']
                exact ⟨rfl, rfl⟩
          | scalar _ | boolVal _ | tuple _ _ | boxVal _ | smartPtr _ | refLocal _ =>
            contradiction
        | succ wIdx1 =>
          cases wIdx1 with
          | zero =>
            cases v with
            | enumAdt tag f0 f1 =>
              change (match natBeq tag expVar with
                | true => match writeAtProj f1 wRest newVal with
                  | some f1' => some (.enumAdt tag f0 f1') | none => none
                | false => none) = some v' at hw
              cases htag : natBeq tag expVar with
              | false => rw [htag] at hw; contradiction
              | true =>
                rw [htag] at hw
                change (match writeAtProj f1 wRest newVal with
                  | some f1' => some (.enumAdt tag f0 f1') | none => none) = some v' at hw
                cases hsub : writeAtProj f1 wRest newVal with
                | none => rw [hsub] at hw; contradiction
                | some _ =>
                  rw [hsub] at hw
                  injection hw with hv'
                  rw [← hv']
                  exact ⟨rfl, rfl⟩
            | scalar _ | boolVal _ | tuple _ _ | boxVal _ | smartPtr _ | refLocal _ =>
              contradiction
          | succ _ =>
            cases v <;> contradiction
  | cons bElem bRest ih =>
    cases wProj with
    | nil =>
      change (!hasDerefInTail (bElem :: bRest)) = false at hconf
      have hbs : hasDerefInTail (bElem :: bRest) = true := bool_not_eq_false hconf
      exact False.elim (noEmptyWrite_when_derefPrefixesProtected .shallow [] (bElem :: bRest) rfl hbs hderef)
    | cons wElem wRest =>
      change (match ProjElem.beq bElem wElem with
        | true => projComponentsConflict .shallow bRest wRest | false => false) = false at hconf
      cases heq : ProjElem.beq bElem wElem with
      | false =>
        exact preservesShallowOutcome_of_eq
          (disjointHeadProj_preserves_evalProj st bElem wElem bRest wRest v v' newVal heq hw)
      | true =>
        rw [heq] at hconf
        change projComponentsConflict .shallow bRest wRest = false at hconf
        have hsame : bElem = wElem := projElemBeq_eq_of_true heq
        subst hsame
        cases bElem with
        | deref =>
          cases v with
          | boxVal inner =>
            change (match writeAtProj inner wRest newVal with
              | some inner' => some (.boxVal inner') | none => none) = some v' at hw
            cases hsub : writeAtProj inner wRest newVal with
            | none => rw [hsub] at hw; contradiction
            | some inner' =>
              rw [hsub] at hw
              injection hw with hv'
              rw [← hv']
              dsimp only [evalProj]
              dsimp only [noDerefPrefixConflicts] at hderef
              rcases bool_and_eq_true hderef with ⟨_, hderefTail⟩
              exact ih wRest inner inner' hconf (step_noDerefPrefixConflicts_same_elem hderefTail) hsub
          | scalar _ | boolVal _ | tuple _ _ | enumAdt _ _ _ | smartPtr _ | refLocal _ =>
            contradiction
        | field idx =>
          have hnd' : noDerefPrefixConflicts .shallow [] bRest wRest = true :=
            step_noDerefPrefixConflicts_same_elem hderef
          cases idx with
          | zero =>
            cases v with
            | tuple f0 f1 =>
              change (match writeAtProj f0 wRest newVal with
                | some f0' => some (.tuple f0' f1) | none => none) = some v' at hw
              cases hsub : writeAtProj f0 wRest newVal with
              | none => rw [hsub] at hw; contradiction
              | some f0' =>
                rw [hsub] at hw
                injection hw with hv'
                rw [← hv']
                exact ih wRest f0 f0' hconf hnd' hsub
            | smartPtr b =>
              change (match writeAtProj b wRest newVal with
                | some b' => some (.smartPtr b') | none => none) = some v' at hw
              cases hsub : writeAtProj b wRest newVal with
              | none => rw [hsub] at hw; contradiction
              | some b' =>
                rw [hsub] at hw
                injection hw with hv'
                rw [← hv']
                exact ih wRest b b' hconf hnd' hsub
            | scalar _ | boolVal _ | enumAdt _ _ _ | boxVal _ | refLocal _ =>
              contradiction
          | succ idx1 =>
            cases idx1 with
            | zero =>
              cases v with
              | tuple f0 f1 =>
                change (match writeAtProj f1 wRest newVal with
                  | some f1' => some (.tuple f0 f1') | none => none) = some v' at hw
                cases hsub : writeAtProj f1 wRest newVal with
                | none => rw [hsub] at hw; contradiction
                | some f1' =>
                  rw [hsub] at hw
                  injection hw with hv'
                  rw [← hv']
                  exact ih wRest f1 f1' hconf hnd' hsub
              | scalar _ | boolVal _ | enumAdt _ _ _ | boxVal _ | smartPtr _ | refLocal _ =>
                contradiction
            | succ _ =>
              cases v <;> contradiction
        | downcastField expVar idx =>
          have hnd' : noDerefPrefixConflicts .shallow [] bRest wRest = true :=
            step_noDerefPrefixConflicts_same_elem hderef
          cases idx with
          | zero =>
            cases v with
            | enumAdt tag f0 f1 =>
              change (match natBeq tag expVar with
                | true => match writeAtProj f0 wRest newVal with
                  | some f0' => some (.enumAdt tag f0' f1) | none => none
                | false => none) = some v' at hw
              cases htag : natBeq tag expVar with
              | false => rw [htag] at hw; contradiction
              | true =>
                rw [htag] at hw
                change (match writeAtProj f0 wRest newVal with
                  | some f0' => some (.enumAdt tag f0' f1) | none => none) = some v' at hw
                cases hsub : writeAtProj f0 wRest newVal with
                | none => rw [hsub] at hw; contradiction
                | some f0' =>
                  rw [hsub] at hw
                  injection hw with hv'
                  rw [← hv']
                  change preservesShallowOutcome
                    (match natBeq tag expVar with | true => evalProj st f0' bRest | false => none)
                    (match natBeq tag expVar with | true => evalProj st f0 bRest | false => none)
                  rw [htag]
                  exact ih wRest f0 f0' hconf hnd' hsub
            | scalar _ | boolVal _ | tuple _ _ | boxVal _ | smartPtr _ | refLocal _ =>
              contradiction
          | succ idx1 =>
            cases idx1 with
            | zero =>
              cases v with
              | enumAdt tag f0 f1 =>
                change (match natBeq tag expVar with
                  | true => match writeAtProj f1 wRest newVal with
                    | some f1' => some (.enumAdt tag f0 f1') | none => none
                  | false => none) = some v' at hw
                cases htag : natBeq tag expVar with
                | false => rw [htag] at hw; contradiction
                | true =>
                  rw [htag] at hw
                  change (match writeAtProj f1 wRest newVal with
                    | some f1' => some (.enumAdt tag f0 f1') | none => none) = some v' at hw
                  cases hsub : writeAtProj f1 wRest newVal with
                  | none => rw [hsub] at hw; contradiction
                  | some f1' =>
                    rw [hsub] at hw
                    injection hw with hv'
                    rw [← hv']
                    change preservesShallowOutcome
                      (match natBeq tag expVar with | true => evalProj st f1' bRest | false => none)
                      (match natBeq tag expVar with | true => evalProj st f1 bRest | false => none)
                    rw [htag]
                    exact ih wRest f1 f1' hconf hnd' hsub
              | scalar _ | boolVal _ | tuple _ _ | boxVal _ | smartPtr _ | refLocal _ =>
                contradiction
            | succ _ =>
              cases v <;> contradiction

noncomputable def fbsProtectsTestOp (fbs : FakeBorrowList) : TestOp → Prop
  | .switchVariant p | .switchBool p =>
    hasFakeBorrowAtLeast fbs p .shallow = true ∧
      ∀ q ∈ collectDerefPrefixPlaces p.localId [] p.proj,
        hasFakeBorrowAtLeast fbs q .shallow = true
  | .derefSmartBool p =>
    hasFakeBorrowAtLeast fbs p .deep = true ∧
      ∀ q ∈ collectDerefPrefixPlaces p.localId [] p.proj,
        hasFakeBorrowAtLeast fbs q .deep = true

theorem admittedWrite_preserves_testOp
    {borrowedPointees : List LocalId} {fbs : FakeBorrowList} {st st' : Store}
    {w : GuardWrite} {t : TestOp}
    (hst : storeRefsIn borrowedPointees st = true)
    (hprot : fbsProtectsTestOp fbs t)
    (hadm : borrowckAdmitsWrite borrowedPointees fbs w.target = true)
    (hnewRef : valRefsIn borrowedPointees w.newVal = true)
    (hw : writePlace st w.target w.newVal = some st') :
    evalTestOp st' t = evalTestOp st t ∧ storeRefsIn borrowedPointees st' = true := by
  rcases bool_and_eq_true hadm with ⟨hnp, hadmFb⟩
  have hwNotPointee : localInList w.target.localId borrowedPointees = false :=
    bool_not_eq_true hnp
  change (match storeLookup st w.target.localId with
    | none => none
    | some rootVal => match writeAtProj rootVal w.target.proj w.newVal with
      | some rootVal' => some (storeUpdate st w.target.localId rootVal')
      | none => none) = some st' at hw
  cases hroot : storeLookup st w.target.localId with
  | none => rw [hroot] at hw; contradiction
  | some wRoot =>
    rw [hroot] at hw
    change (match writeAtProj wRoot w.target.proj w.newVal with
      | some rootVal' => some (storeUpdate st w.target.localId rootVal')
      | none => none) = some st' at hw
    cases hwproj : writeAtProj wRoot w.target.proj w.newVal with
    | none => rw [hwproj] at hw; contradiction
    | some wRoot' =>
      rw [hwproj] at hw
      injection hw with hst'
      rw [← hst']
      have hwRootRefs : valRefsIn borrowedPointees wRoot = true :=
        storeLookup_valRefsIn hst hroot
      have hwRoot'Refs : valRefsIn borrowedPointees wRoot' = true :=
        writeAtProj_preserves_valRefsIn hwRootRefs hnewRef hwproj
      have hst'Refs : storeRefsIn borrowedPointees (storeUpdate st w.target.localId wRoot') = true :=
        storeUpdate_preserves_storeRefsIn hst hwRoot'Refs
      refine ⟨?_, hst'Refs⟩
      cases t with
      | switchVariant p =>
        rcases hprot with ⟨hp, hpre⟩
        dsimp only [evalTestOp, evalPlace]
        cases hloc : natBeq p.localId w.target.localId with
        | false =>
          have hne : natBeq w.target.localId p.localId = false :=
            natBeq_false_of_ne (fun heq => by
              rw [← heq, natBeq_refl] at hloc
              contradiction)
          rw [storeLookup_update_ne st wRoot' hne]
          cases hbRoot : storeLookup st p.localId with
          | none => rfl
          | some bRoot =>
            dsimp only
            rw [evalProj_ignores_unborrowed_store_update hwNotPointee bRoot
              (storeLookup_valRefsIn hst hbRoot) hst p.proj]
        | true =>
          have hpeq : p.localId = w.target.localId := natBeq_eq_of_true hloc
          rw [hpeq, storeLookup_update_same, hroot]
          dsimp only
          rw [evalProj_ignores_unborrowed_store_update hwNotPointee wRoot' hwRoot'Refs hst p.proj]
          have hnc : borrowConflictsWithWrite p .shallow w.target = false :=
            fakeBorrowsAllowWrite_respects_lookup hp hadmFb
          dsimp only [borrowConflictsWithWrite] at hnc
          rw [hloc] at hnc
          dsimp only at hnc
          have hnd := collectDerefPrefixPlaces_gives_noDerefPrefixConflicts hloc hadmFb [] p.proj hpre
          exact (writeAtProj_preserves_shallow_outcome st p.proj w.target.proj wRoot wRoot' w.newVal hnc hnd hwproj).1
      | switchBool p =>
        rcases hprot with ⟨hp, hpre⟩
        dsimp only [evalTestOp, evalPlace]
        cases hloc : natBeq p.localId w.target.localId with
        | false =>
          have hne : natBeq w.target.localId p.localId = false :=
            natBeq_false_of_ne (fun heq => by
              rw [← heq, natBeq_refl] at hloc
              contradiction)
          rw [storeLookup_update_ne st wRoot' hne]
          cases hbRoot : storeLookup st p.localId with
          | none => rfl
          | some bRoot =>
            dsimp only
            rw [evalProj_ignores_unborrowed_store_update hwNotPointee bRoot
              (storeLookup_valRefsIn hst hbRoot) hst p.proj]
        | true =>
          have hpeq : p.localId = w.target.localId := natBeq_eq_of_true hloc
          rw [hpeq, storeLookup_update_same, hroot]
          dsimp only
          rw [evalProj_ignores_unborrowed_store_update hwNotPointee wRoot' hwRoot'Refs hst p.proj]
          have hnc : borrowConflictsWithWrite p .shallow w.target = false :=
            fakeBorrowsAllowWrite_respects_lookup hp hadmFb
          dsimp only [borrowConflictsWithWrite] at hnc
          rw [hloc] at hnc
          dsimp only at hnc
          have hnd := collectDerefPrefixPlaces_gives_noDerefPrefixConflicts hloc hadmFb [] p.proj hpre
          exact (writeAtProj_preserves_shallow_outcome st p.proj w.target.proj wRoot wRoot' w.newVal hnc hnd hwproj).2
      | derefSmartBool p =>
        rcases hprot with ⟨hp, hpre⟩
        dsimp only [evalTestOp, evalPlace]
        cases hloc : natBeq p.localId w.target.localId with
        | false =>
          have hne : natBeq w.target.localId p.localId = false :=
            natBeq_false_of_ne (fun heq => by
              rw [← heq, natBeq_refl] at hloc
              contradiction)
          rw [storeLookup_update_ne st wRoot' hne]
          cases hbRoot : storeLookup st p.localId with
          | none => rfl
          | some bRoot =>
            dsimp only
            rw [evalProj_ignores_unborrowed_store_update hwNotPointee bRoot
              (storeLookup_valRefsIn hst hbRoot) hst p.proj]
        | true =>
          have hpeq : p.localId = w.target.localId := natBeq_eq_of_true hloc
          rw [hpeq, storeLookup_update_same, hroot]
          dsimp only
          rw [evalProj_ignores_unborrowed_store_update hwNotPointee wRoot' hwRoot'Refs hst p.proj]
          have hnc : borrowConflictsWithWrite p .deep w.target = false :=
            fakeBorrowsAllowWrite_respects_lookup hp hadmFb
          dsimp only [borrowConflictsWithWrite] at hnc
          rw [hloc] at hnc
          dsimp only at hnc
          have hnd := collectDerefPrefixPlaces_gives_noDerefPrefixConflicts hloc hadmFb [] p.proj hpre
          rw [writeAtProj_preserves_deep_evalProj st p.proj w.target.proj wRoot wRoot' w.newVal hnc hnd hwproj]

abbrev PathFacts := List (TestOp × Nat)

noncomputable def pathFactsHold (st : Store) : PathFacts → Prop
  | [] => True
  | (t, expected) :: rest => evalTestOp st t = some expected ∧ pathFactsHold st rest

noncomputable def fbsProtectsAllFacts (fbs : FakeBorrowList) : PathFacts → Prop
  | [] => True
  | (t, _) :: rest => fbsProtectsTestOp fbs t ∧ fbsProtectsAllFacts fbs rest

theorem admittedWrites_preserve_pathFacts
    {borrowedPointees : List LocalId} {fbs : FakeBorrowList}
    {writes : List GuardWrite} {st st' : Store} {facts : PathFacts}
    (hst : storeRefsIn borrowedPointees st = true)
    (hprot : fbsProtectsAllFacts fbs facts)
    (hadm : guardWritesAdmitted borrowedPointees fbs writes = true)
    (happly : applyGuardWrites st writes = some st')
    (hhold : pathFactsHold st facts) :
    pathFactsHold st' facts ∧ storeRefsIn borrowedPointees st' = true := by
  induction writes generalizing st with
  | nil =>
    injection happly with heq
    rw [← heq]
    exact ⟨hhold, hst⟩
  | cons w rest ih =>
    rcases bool_and_eq_true hadm with ⟨hab, hadmRest⟩
    rcases bool_and_eq_true hab with ⟨hw1, hw2⟩
    change (match writePlace st w.target w.newVal with
      | some st1 => applyGuardWrites st1 rest | none => none) = some st' at happly
    cases hstep : writePlace st w.target w.newVal with
    | none => rw [hstep] at happly; contradiction
    | some st1 =>
      rw [hstep] at happly
      change applyGuardWrites st1 rest = some st' at happly
      have hst1Refs : storeRefsIn borrowedPointees st1 = true := by
        have hstepCopy := hstep
        change (match storeLookup st w.target.localId with
          | none => none
          | some rVal => match writeAtProj rVal w.target.proj w.newVal with
            | some rVal' => some (storeUpdate st w.target.localId rVal')
            | none => none) = some st1 at hstepCopy
        cases hroot : storeLookup st w.target.localId with
        | none => rw [hroot] at hstepCopy; contradiction
        | some rVal =>
          rw [hroot] at hstepCopy
          change (match writeAtProj rVal w.target.proj w.newVal with
            | some rVal' => some (storeUpdate st w.target.localId rVal')
            | none => none) = some st1 at hstepCopy
          cases hwp : writeAtProj rVal w.target.proj w.newVal with
          | none => rw [hwp] at hstepCopy; contradiction
          | some rVal' =>
            rw [hwp] at hstepCopy
            injection hstepCopy with hst1eq
            rw [← hst1eq]
            exact storeUpdate_preserves_storeRefsIn hst
              (writeAtProj_preserves_valRefsIn (storeLookup_valRefsIn hst hroot) hw2 hwp)
      have hfacts1 : pathFactsHold st1 facts := by
        clear ih happly
        induction facts with
        | nil => trivial
        | cons tf _ ihf =>
          cases tf with
          | mk t _ =>
            rcases hprot with ⟨hpt, hprest⟩
            rcases hhold with ⟨hteq, hhrest⟩
            have hpres := (admittedWrite_preserves_testOp hst hpt hw1 hw2 hstep).1
            rw [← hpres] at hteq
            exact ⟨hteq, ihf hprest hhrest⟩
      exact ih hst1Refs hadmRest happly hfacts1

noncomputable def treeExhaustiveUnderFacts (facts : PathFacts) : DecTree → Prop
  | .armLeaf _ => True
  | .guardedArm _ _ _ _ otherwiseTree =>
    treeExhaustiveUnderFacts facts otherwiseTree
  | .testBoolNode p onFalse onTrue =>
    treeExhaustiveUnderFacts ((.switchBool p, 0) :: facts) onFalse ∧
      treeExhaustiveUnderFacts ((.switchBool p, 1) :: facts) onTrue
  | .testDerefBoolNode p onFalse onTrue =>
    treeExhaustiveUnderFacts ((.derefSmartBool p, 0) :: facts) onFalse ∧
      treeExhaustiveUnderFacts ((.derefSmartBool p, 1) :: facts) onTrue
  | .switchTwoVariants p onVar0 onVar1 =>
    treeExhaustiveUnderFacts ((.switchVariant p, 0) :: facts) onVar0 ∧
      treeExhaustiveUnderFacts ((.switchVariant p, 1) :: facts) onVar1
  | .unreachableLeaf =>
    ∀ st : Store, ¬ pathFactsHold st facts

theorem collectTestOp_protects_self (fbs : FakeBorrowList) (t : TestOp) :
    fbsProtectsTestOp (collectTestOpFakeBorrows fbs t) t := by
  cases t with
  | switchVariant p =>
    exact ⟨hasFakeBorrowAtLeast_recordFakeBorrow_self fbs p .shallow,
      fun q hq => hasFakeBorrowAtLeast_recordFakeBorrow_prefix fbs p q .shallow hq⟩
  | switchBool p =>
    exact ⟨hasFakeBorrowAtLeast_recordFakeBorrow_self fbs p .shallow,
      fun q hq => hasFakeBorrowAtLeast_recordFakeBorrow_prefix fbs p q .shallow hq⟩
  | derefSmartBool p =>
    exact ⟨hasFakeBorrowAtLeast_recordFakeBorrow_self fbs p .deep,
      fun q hq => hasFakeBorrowAtLeast_recordFakeBorrow_prefix fbs p q .deep hq⟩

theorem evalDecTree_no_unreachable_aux
    (borrowedPointees : List LocalId) (globalFbs : FakeBorrowList)
    (dt : DecTree) (facts : PathFacts) (st : Store)
    (hst : storeRefsIn borrowedPointees st = true)
    (hfacts : pathFactsHold st facts)
    (hprotFacts : fbsProtectsAllFacts globalFbs facts)
    (hborrowOk : allTreeGuardsBorrowckOk borrowedPointees globalFbs dt = true)
    (hexh : treeExhaustiveUnderFacts facts dt) :
    ∀ fbsSeed : FakeBorrowList,
      (∀ q req, hasFakeBorrowAtLeast (collectTreeFakeBorrows fbsSeed dt) q req = true →
        hasFakeBorrowAtLeast globalFbs q req = true) →
      evalDecTree dt st ≠ .reachedUnreachableUB := by
  induction dt generalizing facts st with
  | armLeaf _ =>
    intro _ _ hcontra
    contradiction
  | unreachableLeaf =>
    intro _ _ _
    exact hexh st hfacts
  | guardedArm srcs writes guardPass _ oTree ih =>
    intro fbsSeed hinc
    rcases bool_and_eq_true hborrowOk with ⟨hgw, hbO⟩
    dsimp only [evalDecTree]
    cases happ : applyGuardWrites st writes with
    | none => intro hc; contradiction
    | some stAfter =>
      dsimp only
      cases guardPass with
      | true => intro hc; contradiction
      | false =>
        have ⟨hfacts', hst'⟩ :=
          admittedWrites_preserve_pathFacts hst hprotFacts hgw happ hfacts
        exact ih facts stAfter hst' hfacts' hprotFacts hbO hexh
          (collectBindingsFakeBorrows fbsSeed srcs) hinc
  | testBoolNode p onFalse onTrue ihF ihT =>
    intro fbsSeed hinc
    rcases bool_and_eq_true hborrowOk with ⟨hbF, hbT⟩
    rcases hexh with ⟨hexhF, hexhT⟩
    have hprotSelf : fbsProtectsTestOp globalFbs (.switchBool p) := by
      have hseed := collectTestOp_protects_self fbsSeed (.switchBool p)
      rcases hseed with ⟨hp, hpre⟩
      refine ⟨hinc p .shallow (hasFakeBorrowAtLeast_collectTree_preserves onTrue _ p .shallow
        (hasFakeBorrowAtLeast_collectTree_preserves onFalse _ p .shallow hp)), ?_⟩
      intro q hq
      exact hinc q .shallow (hasFakeBorrowAtLeast_collectTree_preserves onTrue _ q .shallow
        (hasFakeBorrowAtLeast_collectTree_preserves onFalse _ q .shallow (hpre q hq)))
    dsimp only [evalDecTree]
    cases hev : evalTestOp st (.switchBool p) with
    | none => intro hc; contradiction
    | some tag =>
      cases tag with
      | zero =>
        exact ihF ((.switchBool p, 0) :: facts) st hst ⟨hev, hfacts⟩
          ⟨hprotSelf, hprotFacts⟩ hbF hexhF
          (collectTestOpFakeBorrows fbsSeed (.switchBool p))
          (fun q req hq => hinc q req (hasFakeBorrowAtLeast_collectTree_preserves onTrue _ q req hq))
      | succ tag1 =>
        cases tag1 with
        | zero =>
          exact ihT ((.switchBool p, 1) :: facts) st hst ⟨hev, hfacts⟩
            ⟨hprotSelf, hprotFacts⟩ hbT hexhT
            (collectTreeFakeBorrows (collectTestOpFakeBorrows fbsSeed (.switchBool p)) onFalse)
            hinc
        | succ _ => intro hc; contradiction
  | testDerefBoolNode p onFalse onTrue ihF ihT =>
    intro fbsSeed hinc
    rcases bool_and_eq_true hborrowOk with ⟨hbF, hbT⟩
    rcases hexh with ⟨hexhF, hexhT⟩
    have hprotSelf : fbsProtectsTestOp globalFbs (.derefSmartBool p) := by
      have hseed := collectTestOp_protects_self fbsSeed (.derefSmartBool p)
      rcases hseed with ⟨hp, hpre⟩
      refine ⟨hinc p .deep (hasFakeBorrowAtLeast_collectTree_preserves onTrue _ p .deep
        (hasFakeBorrowAtLeast_collectTree_preserves onFalse _ p .deep hp)), ?_⟩
      intro q hq
      exact hinc q .deep (hasFakeBorrowAtLeast_collectTree_preserves onTrue _ q .deep
        (hasFakeBorrowAtLeast_collectTree_preserves onFalse _ q .deep (hpre q hq)))
    dsimp only [evalDecTree]
    cases hev : evalTestOp st (.derefSmartBool p) with
    | none => intro hc; contradiction
    | some tag =>
      cases tag with
      | zero =>
        exact ihF ((.derefSmartBool p, 0) :: facts) st hst ⟨hev, hfacts⟩
          ⟨hprotSelf, hprotFacts⟩ hbF hexhF
          (collectTestOpFakeBorrows fbsSeed (.derefSmartBool p))
          (fun q req hq => hinc q req (hasFakeBorrowAtLeast_collectTree_preserves onTrue _ q req hq))
      | succ tag1 =>
        cases tag1 with
        | zero =>
          exact ihT ((.derefSmartBool p, 1) :: facts) st hst ⟨hev, hfacts⟩
            ⟨hprotSelf, hprotFacts⟩ hbT hexhT
            (collectTreeFakeBorrows (collectTestOpFakeBorrows fbsSeed (.derefSmartBool p)) onFalse)
            hinc
        | succ _ => intro hc; contradiction
  | switchTwoVariants p onVar0 onVar1 ih0 ih1 =>
    intro fbsSeed hinc
    rcases bool_and_eq_true hborrowOk with ⟨hb0, hb1⟩
    rcases hexh with ⟨hexh0, hexh1⟩
    have hprotSelf : fbsProtectsTestOp globalFbs (.switchVariant p) := by
      have hseed := collectTestOp_protects_self fbsSeed (.switchVariant p)
      rcases hseed with ⟨hp, hpre⟩
      refine ⟨hinc p .shallow (hasFakeBorrowAtLeast_collectTree_preserves onVar1 _ p .shallow
        (hasFakeBorrowAtLeast_collectTree_preserves onVar0 _ p .shallow hp)), ?_⟩
      intro q hq
      exact hinc q .shallow (hasFakeBorrowAtLeast_collectTree_preserves onVar1 _ q .shallow
        (hasFakeBorrowAtLeast_collectTree_preserves onVar0 _ q .shallow (hpre q hq)))
    dsimp only [evalDecTree]
    cases hev : evalTestOp st (.switchVariant p) with
    | none => intro hc; contradiction
    | some tag =>
      cases tag with
      | zero =>
        exact ih0 ((.switchVariant p, 0) :: facts) st hst ⟨hev, hfacts⟩
          ⟨hprotSelf, hprotFacts⟩ hb0 hexh0
          (collectTestOpFakeBorrows fbsSeed (.switchVariant p))
          (fun q req hq => hinc q req (hasFakeBorrowAtLeast_collectTree_preserves onVar1 _ q req hq))
      | succ tag1 =>
        cases tag1 with
        | zero =>
          exact ih1 ((.switchVariant p, 1) :: facts) st hst ⟨hev, hfacts⟩
            ⟨hprotSelf, hprotFacts⟩ hb1 hexh1
            (collectTreeFakeBorrows (collectTestOpFakeBorrows fbsSeed (.switchVariant p)) onVar0)
            hinc
        | succ _ => intro hc; contradiction

/-- **Theorem 1 (`fakeBorrow_prevents_unreachable_fallthrough`):**
For ANY lowered match decision tree `dt` whose branches are statically exhaustive (`treeExhaustiveUnderFacts [] dt`)
and whose guard mutations pass `mir_borrowck` against `collectTreeFakeBorrows [] dt`
(`FakeBorrowKind::Shallow` on switched places & deref prefixes, `FakeBorrowKind::Deep` on
`TestableCase::Deref`), executing `evalDecTree dt st₀` in `Runtime(PostCleanup)` MIR (after `&fake`
and `FakeRead` erasure) NEVER reaches `TerminatorKind::Unreachable` (`.reachedUnreachableUB`), even
when failing guards mutate unswitched locals or unborrowed variant-payload projections! -/
theorem fakeBorrow_prevents_unreachable_fallthrough
    (borrowedPointees : List LocalId) (dt : DecTree) (st₀ : Store)
    (hst₀ : storeRefsIn borrowedPointees st₀ = true)
    (hborrowOk : allTreeGuardsBorrowckOk borrowedPointees (collectTreeFakeBorrows [] dt) dt = true)
    (hexh : treeExhaustiveUnderFacts [] dt) :
    evalDecTree dt st₀ ≠ .reachedUnreachableUB :=
  evalDecTree_no_unreachable_aux
    borrowedPointees (collectTreeFakeBorrows [] dt) dt [] st₀ hst₀ trivial trivial
    hborrowOk hexh [] (fun _ _ h => h)

/-! ## Section 4: Or-Pattern Guard Backtracking & Final-Sub-Branch Drop Schedule (`Theorem 2`) -/

abbrev GuardLog := List Nat

structure OrSubPat where
  tryMatch : Store → Option (List (VarId × Val))
  bindingVars : List VarId

abbrev StatefulGuard := List (VarId × Val) → Store → GuardLog → (Bool × Store × GuardLog)

inductive OrMatchResult where
  | enteredArm (armId : Nat) (armBindings : List (VarId × Val)) (st : Store) (log : GuardLog)
  | fellThroughToOtherwise (st : Store) (log : GuardLog)

noncomputable def evalSourceOrArm :
    List OrSubPat → StatefulGuard → Nat → Store → GuardLog → OrMatchResult
  | [], _, _, st, log => .fellThroughToOtherwise st log
  | subpat :: rest, guardFn, armId, st, log =>
    match subpat.tryMatch st with
    | none => evalSourceOrArm rest guardFn armId st log
    | some refBindings =>
      let (passed, st', log') := guardFn refBindings st log
      match passed with
      | true => .enteredArm armId refBindings st' log'
      | false => evalSourceOrArm rest guardFn armId st' log'

inductive LoweredSubBranchChain where
  | otherwiseExit
  | subBranchNode
      (testAndBindForGuard : Store → Option (List (VarId × Val)))
      (loweredGuardCopy : StatefulGuard)
      (armTargetId : Nat)
      (otherwiseNext : LoweredSubBranchChain)

noncomputable def lowerOrArmToSubBranches :
    List OrSubPat → StatefulGuard → Nat → LoweredSubBranchChain
  | [], _, _ => .otherwiseExit
  | subpat :: rest, guardFn, armId =>
    .subBranchNode
      subpat.tryMatch
      guardFn
      armId
      (lowerOrArmToSubBranches rest guardFn armId)

noncomputable def execLoweredSubBranchChain :
    LoweredSubBranchChain → Store → GuardLog → OrMatchResult
  | .otherwiseExit, st, log => .fellThroughToOtherwise st log
  | .subBranchNode testBind guardCopy armId otherwiseNext, st, log =>
    match testBind st with
    | none => execLoweredSubBranchChain otherwiseNext st log
    | some guardRefBindings =>
      let (ok, st1, log1) := guardCopy guardRefBindings st log
      match ok with
      | true =>
        let armByValueBindings := guardRefBindings
        .enteredArm armId armByValueBindings st1 log1
      | false =>
        execLoweredSubBranchChain otherwiseNext st1 log1

/-- **Theorem 2 (`orPattern_guard_backtracking_exact`):**
For EVERY or-pattern alternative list `subpats` and EVERY side-effecting `StatefulGuard` `guardFn`,
executing `rustc_mir_build`'s split-sub-branch CFG (`lowerOrArmToSubBranches`) produces the EXACT
same arm/otherwise target, bound values, mutated store, and side-effecting guard re-evaluation
trace as source-level backtracking semantics (`evalSourceOrArm`)! -/
theorem orPattern_guard_backtracking_exact
    (subpats : List OrSubPat) (guardFn : StatefulGuard) (armId : Nat)
    (st : Store) (log : GuardLog) :
    execLoweredSubBranchChain (lowerOrArmToSubBranches subpats guardFn armId) st log =
      evalSourceOrArm subpats guardFn armId st log := by
  induction subpats generalizing st log with
  | nil => rfl
  | cons subpat rest ih =>
    dsimp only [lowerOrArmToSubBranches, execLoweredSubBranchChain, evalSourceOrArm]
    cases subpat.tryMatch st with
    | none => exact ih st log
    | some refBindings =>
      dsimp only
      cases guardFn refBindings st log with
      | mk passed restOut =>
        cases restOut with
        | mk st1 log1 =>
          dsimp only
          cases passed with
          | true => rfl
          | false => exact ih st1 log1

/-! ### Reverse-Sub-Branch Drop Scheduling (`Builder::bind_pattern` + `clear_match_arm_and_guard_scopes`) -/

noncomputable def scheduleLifoDropsForSubBranch (currentDrops : List VarId) : List VarId → List VarId
  | [] => currentDrops
  | v :: rest => scheduleLifoDropsForSubBranch (v :: currentDrops) rest

theorem scheduleLifoDrops_eq_reverse_append (acc vars : List VarId) :
    scheduleLifoDropsForSubBranch acc vars = vars.reverse ++ acc := by
  induction vars generalizing acc with
  | nil => rfl
  | cons v rest ih =>
    dsimp only [scheduleLifoDropsForSubBranch]
    rw [ih (v :: acc), List.reverse_cons, List.append_assoc]
    rfl

noncomputable def runSubBranchDropLoop (armScopeDrops : List VarId) : List OrSubPat → List VarId
  | [] => armScopeDrops
  | [finalSubBranch] =>
    scheduleLifoDropsForSubBranch armScopeDrops finalSubBranch.bindingVars
  | _ :: next :: rest =>
    runSubBranchDropLoop [] (next :: rest)

noncomputable def rustcLoweredArmDropOrder (subBranches : List OrSubPat) : List VarId :=
  runSubBranchDropLoop [] subBranches.reverse

noncomputable def naiveForwardArmDropOrder (subBranches : List OrSubPat) : List VarId :=
  runSubBranchDropLoop [] subBranches

theorem runSubBranchDropLoop_last (acc : List VarId) (init : List OrSubPat) (lastSub : OrSubPat) :
    runSubBranchDropLoop acc (init ++ [lastSub]) =
      match init with
      | [] => lastSub.bindingVars.reverse ++ acc
      | _ :: _ => lastSub.bindingVars.reverse := by
  induction init generalizing acc with
  | nil =>
    change scheduleLifoDropsForSubBranch acc lastSub.bindingVars = lastSub.bindingVars.reverse ++ acc
    exact scheduleLifoDrops_eq_reverse_append acc lastSub.bindingVars
  | cons _ tail ih =>
    cases tail with
    | nil =>
      change scheduleLifoDropsForSubBranch [] lastSub.bindingVars = lastSub.bindingVars.reverse
      rw [scheduleLifoDrops_eq_reverse_append, List.append_nil]
    | cons hd2 tail2 =>
      change runSubBranchDropLoop [] ((hd2 :: tail2) ++ [lastSub]) = lastSub.bindingVars.reverse
      exact ih []

/-- **Theorem 2b (`rustcLoweredArmDropOrder_matches_primary_lifo`):**
Because `bind_pattern` iterates `sub_branches.reverse` and `clear_match_arm_and_guard_scopes` wipes
drops on all non-final iterations, the single static drop schedule at `arm_block` exit ALWAYS equals
`firstSub.bindingVars.reverse` (reverse declaration order of the leftmost sub-pattern `firstSub`)! -/
theorem rustcLoweredArmDropOrder_matches_primary_lifo
    (firstSub : OrSubPat) (otherSubs : List OrSubPat) :
    rustcLoweredArmDropOrder (firstSub :: otherSubs) = firstSub.bindingVars.reverse := by
  unfold rustcLoweredArmDropOrder
  rw [List.reverse_cons]
  have h := runSubBranchDropLoop_last [] otherSubs.reverse firstSub
  revert h
  cases otherSubs.reverse with
  | nil =>
    intro h
    rw [List.append_nil] at h
    exact h
  | cons _ _ =>
    intro h
    exact h

noncomputable def resolveDroppedValues (env : List (VarId × Nat)) : List VarId → List Nat
  | [] => []
  | v :: rest =>
    let tok :=
      match env with
      | [] => 0
      | (k1, val1) :: envRest =>
        match natBeq k1 v with
        | true => val1
        | false =>
          match envRest with
          | (k2, val2) :: _ => if natBeq k2 v then val2 else 0
          | [] => 0
    tok :: resolveDroppedValues env rest

theorem okErrSwappedBindings_value_drop_asymmetry :
    let subOk : OrSubPat := { tryMatch := fun _ => none, bindingVars := [10, 11] }
    let subErr : OrSubPat := { tryMatch := fun _ => none, bindingVars := [11, 10] }
    let staticDropVars := rustcLoweredArmDropOrder [subOk, subErr]
    staticDropVars = [11, 10] ∧
      resolveDroppedValues [(10, 1), (11, 2)] staticDropVars = [2, 1] ∧
      resolveDroppedValues [(11, 1), (10, 2)] staticDropVars = [1, 2] :=
  ⟨rfl, rfl, rfl⟩

/-! ## Section 5: Uninhabited (`Void`) & `#[non_exhaustive]` Single-Variant Lowering (`Theorem 3`) -/

structure UpstreamEnumDef where
  declaredVariantCount : Nat
  isNonExhaustive : Bool

structure SingleVariantDownstreamMatch where
  onlyArmVal : Nat
  wildArmVal : Nat

inductive LoweredSingleVariantMir where
  | irrefutableDirectGoto (targetVal : Nat)
  | switchDiscriminant (expectedDiscr : Nat) (matchVal : Nat) (otherwiseVal : Nat)

noncomputable def natBlt : Nat → Nat → Bool
  | _, 0 => false
  | 0, _ + 1 => true
  | m + 1, n + 1 => natBlt m n

noncomputable def isVariantPatternRefutable (adt : UpstreamEnumDef) : Bool :=
  natBlt 1 adt.declaredVariantCount || adt.isNonExhaustive

noncomputable def lowerSingleVariantEnumMatch
    (adt : UpstreamEnumDef) (m : SingleVariantDownstreamMatch) : LoweredSingleVariantMir :=
  match isVariantPatternRefutable adt with
  | true => .switchDiscriminant 0 m.onlyArmVal m.wildArmVal
  | false => .irrefutableDirectGoto m.onlyArmVal

noncomputable def evalLoweredSingleVariantMir
    (mir : LoweredSingleVariantMir) (runtimeDiscr : Nat) : Nat :=
  match mir with
  | .irrefutableDirectGoto targetVal => targetVal
  | .switchDiscriminant expectedDiscr matchVal otherwiseVal =>
    match natBeq runtimeDiscr expectedDiscr with
    | true => matchVal
    | false => otherwiseVal

noncomputable def evalOpenWorldEnumSpec
    (m : SingleVariantDownstreamMatch) (runtimeDiscr : Nat) : Nat :=
  match natBeq runtimeDiscr 0 with
  | true => m.onlyArmVal
  | false => m.wildArmVal

/-- **Theorem 3 (`nonExhaustive_requires_discriminant_dispatch`):**
1. For ANY `#[non_exhaustive]` enum (`adt.isNonExhaustive = true`), EVEN when `adt.declaredVariantCount = 1`
   in crate version v1, `lowerSingleVariantEnumMatch` emits a real `Rvalue::Discriminant` + `SwitchInt`
   and dispatches EVERY open-world runtime discriminant `runtimeDiscr : Nat` identically to
   `evalOpenWorldEnumSpec`!
2. Conversely, for an exhaustive 1-variant enum (`adt = ⟨1, false⟩`), `lowerSingleVariantEnumMatch`
   elides `discriminant` and `SwitchInt` (`.irrefutableDirectGoto`) while agreeing with
   `evalOpenWorldEnumSpec` on the unique closed-world inhabitant `runtimeDiscr = 0`! -/
theorem nonExhaustive_requires_discriminant_dispatch
    (declaredCount : Nat) (m : SingleVariantDownstreamMatch) (runtimeDiscr : Nat) :
    let nonExhAdt : UpstreamEnumDef := { declaredVariantCount := declaredCount, isNonExhaustive := true }
    let exhSingleAdt : UpstreamEnumDef := { declaredVariantCount := 1, isNonExhaustive := false }
    lowerSingleVariantEnumMatch nonExhAdt m =
        .switchDiscriminant 0 m.onlyArmVal m.wildArmVal ∧
      evalLoweredSingleVariantMir (lowerSingleVariantEnumMatch nonExhAdt m) runtimeDiscr =
        evalOpenWorldEnumSpec m runtimeDiscr ∧
      lowerSingleVariantEnumMatch exhSingleAdt m = .irrefutableDirectGoto m.onlyArmVal ∧
      evalLoweredSingleVariantMir (lowerSingleVariantEnumMatch exhSingleAdt m) 0 =
        evalOpenWorldEnumSpec m 0 := by
  intro nonExhAdt exhSingleAdt
  have hrefTrue : isVariantPatternRefutable nonExhAdt = true := by
    unfold isVariantPatternRefutable
    cases natBlt 1 declaredCount <;> rfl
  have hrefFalse : isVariantPatternRefutable exhSingleAdt = false := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold lowerSingleVariantEnumMatch
    rw [hrefTrue]
  · unfold lowerSingleVariantEnumMatch
    rw [hrefTrue]
    rfl
  · unfold lowerSingleVariantEnumMatch
    rw [hrefFalse]
  · unfold lowerSingleVariantEnumMatch
    rw [hrefFalse]
    rfl

/-! ### Uninhabited `Void`: `*const Void` `PlaceMention` vs `&Void` Value-Validity UB -/

inductive RawPtrAddr where
  | nullAddr
  | validAlignedAddr

inductive MiriExecResult where
  | okReturn (val : Nat)
  | ubConstructingInvalidRefToUninhabited
  | ubEnteredUnreachable

noncomputable def evalMatchRawPtrVoidWildcard (_p : RawPtrAddr) (armVal : Nat) : MiriExecResult :=
  .okReturn armVal

noncomputable def evalMatchRawPtrVoidEmpty (_p : RawPtrAddr) : MiriExecResult :=
  .ubEnteredUnreachable

noncomputable def evalRefVoidEmptyMatch (_p : RawPtrAddr) : MiriExecResult :=
  .ubConstructingInvalidRefToUninhabited

theorem voidRawPtrWildcard_safe_vs_refVoid_ub (addr : RawPtrAddr) :
    evalMatchRawPtrVoidWildcard addr 99 = .okReturn 99 ∧
      evalMatchRawPtrVoidEmpty addr = .ubEnteredUnreachable ∧
      evalRefVoidEmptyMatch addr = .ubConstructingInvalidRefToUninhabited :=
  ⟨rfl, rfl, rfl⟩

/-! ## Section 6: Three Constructive Counterexamples (`ce1`, `ce2`, `ce3`) -/

noncomputable def buggyShallowDerefTreeCollector (fbs : FakeBorrowList) : DecTree → FakeBorrowList
  | .armLeaf _ => fbs
  | .guardedArm boundSources _ _ _ otherwiseTree =>
    buggyShallowDerefTreeCollector (collectBindingsFakeBorrows fbs boundSources) otherwiseTree
  | .testBoolNode p onFalse onTrue =>
    let fbs1 := recordFakeBorrow fbs p .shallow
    buggyShallowDerefTreeCollector (buggyShallowDerefTreeCollector fbs1 onFalse) onTrue
  | .testDerefBoolNode p onFalse onTrue =>
    let fbs1 := recordFakeBorrow fbs p .shallow
    buggyShallowDerefTreeCollector (buggyShallowDerefTreeCollector fbs1 onFalse) onTrue
  | .switchTwoVariants p onVar0 onVar1 =>
    let fbs1 := recordFakeBorrow fbs p .shallow
    buggyShallowDerefTreeCollector (buggyShallowDerefTreeCollector fbs1 onVar0) onVar1
  | .unreachableLeaf => fbs

noncomputable def ce1SmartBoolTree : DecTree :=
  let sPlace : Place := { localId := 1, proj := [] }
  let sField0 : Place := { localId := 1, proj := [.field 0] }
  let arm3OrUnreachable : DecTree :=
    .testDerefBoolNode sPlace (.armLeaf 3) .unreachableLeaf
  let arm2Guard : DecTree :=
    .guardedArm [] [{ target := sField0, newVal := .boolVal true }] false 2 arm3OrUnreachable
  .testDerefBoolNode sPlace arm2Guard (.armLeaf 1)

noncomputable def ce1InitStore : Store :=
  [(1, .smartPtr (.boolVal false))]

/-- **Counterexample 1 (`ce1_shallow_only_fake_borrow_on_deref_pat_reaches_unreachable_ub`):**
Assigning `FakeBorrowKind::Shallow` instead of `FakeBorrowKind::Deep` to `TestableCase::Deref`
causes `mir_borrowck` to accept `s.0 = true` inside the guard (`allTreeGuardsBorrowckOk = true`),
driving `SmartBool(false)` into `TerminatorKind::Unreachable` UB (`.reachedUnreachableUB`), whereas
`rustc`'s `FakeBorrowKind::Deep` rejects the guard (`allTreeGuardsBorrowckOk = false`, `E0510`)! -/
theorem ce1_shallow_only_fake_borrow_on_deref_pat_reaches_unreachable_ub :
    treeExhaustiveUnderFacts [] ce1SmartBoolTree ∧
      allTreeGuardsBorrowckOk [] (buggyShallowDerefTreeCollector [] ce1SmartBoolTree) ce1SmartBoolTree = true ∧
      evalDecTree ce1SmartBoolTree ce1InitStore = .reachedUnreachableUB ∧
      allTreeGuardsBorrowckOk [] (collectTreeFakeBorrows [] ce1SmartBoolTree) ce1SmartBoolTree = false := by
  refine ⟨?_, rfl, rfl, rfl⟩
  unfold ce1SmartBoolTree treeExhaustiveUnderFacts
  refine ⟨?_, trivial⟩
  refine ⟨trivial, ?_⟩
  intro st hfacts
  rcases hfacts with ⟨h1, h0, _⟩
  rw [h0] at h1
  contradiction

noncomputable def buggyNoPrefixBindingBorrows (fbs : FakeBorrowList) (_source : Place) :
    FakeBorrowList :=
  fbs

noncomputable def runBoundDerefGuardScenario :
    (Bool × Bool × Option Val × Option Val) :=
  let borrowedPointees : List LocalId := [10, 11]
  let st0 : Store := [(1, .refLocal 10), (10, .scalar 1), (11, .scalar 2)]
  let derefX : Place := { localId := 1, proj := [.deref] }
  let xLocal : Place := { localId := 1, proj := [] }
  let buggyFbs := buggyNoPrefixBindingBorrows [] derefX
  let soundFbs := recordBindingFakeBorrows [] derefX
  let buggyAllows := borrowckAdmitsWrite borrowedPointees buggyFbs xLocal
  let soundAllows := borrowckAdmitsWrite borrowedPointees soundFbs xLocal
  let valObservedInGuard := evalPlace st0 derefX
  let valCopiedIntoArmBody :=
    match writePlace st0 xLocal (.refLocal 11) with
    | some stAfterGuard => evalPlace stAfterGuard derefX
    | none => none
  (buggyAllows, soundAllows, valObservedInGuard, valCopiedIntoArmBody)

/-- **Counterexample 2 (`ce2_omitting_deref_prefix_fake_borrow_corrupts_arm_binding`):**
Omitting `fake_borrow_deref_prefixes` (`&fake shallow x`) allows `x = &2` in the guard (`buggyAllows = true`),
corrupting the arm body's lazy copy of `y = *x` from `some (.scalar 1)` (checked by the guard) to
`some (.scalar 2)`, whereas `recordBindingFakeBorrows` rejects `x = &2` (`soundAllows = false`, `E0510`)! -/
theorem ce2_omitting_deref_prefix_fake_borrow_corrupts_arm_binding :
    runBoundDerefGuardScenario =
      (true, false, some (.scalar 1), some (.scalar 2)) :=
  rfl

noncomputable def buggyClosedWorldSingleVariantLowering
    (adt : UpstreamEnumDef) (m : SingleVariantDownstreamMatch) : LoweredSingleVariantMir :=
  match natBlt 1 adt.declaredVariantCount with
  | true => .switchDiscriminant 0 m.onlyArmVal m.wildArmVal
  | false => .irrefutableDirectGoto m.onlyArmVal

/-- **Counterexample 3 (`ce3_omitting_discriminant_check_on_non_exhaustive_single_variant_misdispatches_future_variant`):**
Omitting `|| adt.isNonExhaustive` on a 1-variant `#[non_exhaustive]` enum elides `SwitchInt` and
misdispatches a newly added upstream variant (`runtimeDiscr = 1`) to `1` instead of `_ => 2`! -/
theorem ce3_omitting_discriminant_check_on_non_exhaustive_single_variant_misdispatches_future_variant :
    let adt : UpstreamEnumDef := { declaredVariantCount := 1, isNonExhaustive := true }
    let m : SingleVariantDownstreamMatch := { onlyArmVal := 1, wildArmVal := 2 }
    evalLoweredSingleVariantMir (buggyClosedWorldSingleVariantLowering adt m) 1 = 1 ∧
      evalLoweredSingleVariantMir (lowerSingleVariantEnumMatch adt m) 1 = 2 ∧
      evalOpenWorldEnumSpec m 1 = 2 ∧
      evalLoweredSingleVariantMir (buggyClosedWorldSingleVariantLowering adt m) 1 ≠
        evalOpenWorldEnumSpec m 1 := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro h
  contradiction

/-! ## Section 7: Kernel Axiom Footprint Verification -/

#print axioms fakeBorrow_prevents_unreachable_fallthrough
#print axioms orPattern_guard_backtracking_exact
#print axioms rustcLoweredArmDropOrder_matches_primary_lifo
#print axioms okErrSwappedBindings_value_drop_asymmetry
#print axioms nonExhaustive_requires_discriminant_dispatch
#print axioms voidRawPtrWildcard_safe_vs_refVoid_ub
#print axioms ce1_shallow_only_fake_borrow_on_deref_pat_reaches_unreachable_ub
#print axioms ce2_omitting_deref_prefix_fake_borrow_corrupts_arm_binding
#print axioms ce3_omitting_discriminant_check_on_non_exhaustive_single_variant_misdispatches_future_variant

end MatchLoweringSoundness
