-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under the BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.NotationExtra
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.List.Basic
import Init.Data.List.Notation
import Init.Data.Option.Basic
import Init.RCases

namespace Anneal.ConstGenericsValTreeSoundness

/-!
# Verified `rustc` Const Generics, `ValTree` Canonicalization, Syntactic `AbstractConst`
# Unification, and `ConstParamTy` / `StructuralPartialEq` Gate Soundness

Mechanized in pure `prelude` Lean `v4.34.1` with:
- Every value definition marked `noncomputable def` (zero `._unsafe_rec` helpers).
- Zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`, zero `native_decide`,
  zero `partial def`, and zero `deriving` clauses on inductive types.

Anchored to primary upstream sources (`rust-lang/rust@0259d5e9a81c6af08e40f8c204f2c0c41dca1647`,
`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, and
`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`):
- `compiler/rustc_type_ir/src/const_kind.rs` (`ConstKind`, `ValTreeKind`, `AnonConstKind`)
- `compiler/rustc_middle/src/ty/consts/kind.rs` (`Expr`, `ExprKind`)
- `compiler/rustc_middle/src/ty/consts/valtree.rs` (`ValTree`, `Value`, `destructure_adt_const`)
- `compiler/rustc_const_eval/src/const_eval/valtrees.rs` (`const_to_valtree_inner`, `valtree_to_const_value`)
- `compiler/rustc_symbol_mangling/src/v0.rs` (`print_const`)
- `compiler/rustc_hir_analysis/src/collect.rs` (`anon_const_kind`)
- `compiler/rustc_hir_analysis/src/collect/clauses_of.rs` (`const_evaluatable_clauses_of`)
- `compiler/rustc_trait_selection/src/traits/const_evaluatable.rs` (`is_const_evaluatable`, `satisfied_from_param_env`)
- `compiler/rustc_hir_analysis/src/coherence/builtin.rs` (`visit_implementation_of_const_param_ty`)
- `compiler/rustc_trait_selection/src/traits/misc.rs` (`type_allowed_to_implement_const_param_ty`)
- `compiler/rustc_ast_passes/src/feature_gate.rs` (`warn_next_solver_and_gce`, `check_features_requiring_new_solver`)
-/

/-! ## Section 1: Elementary Pure Equality Helpers (No `BEq` / `Decidable` Auxiliaries) -/

noncomputable def boolEq : Bool → Bool → Bool
  | true, true => true
  | false, false => true
  | _, _ => false

theorem boolEq_true_iff (a b : Bool) : boolEq a b = true ↔ a = b := by
  cases a <;> cases b <;> constructor <;> intro h <;> first | rfl | cases h

theorem boolEq_refl (a : Bool) : boolEq a a = true := by
  cases a <;> rfl

noncomputable def natEq : Nat → Nat → Bool
  | 0, 0 => true
  | 0, _ + 1 => false
  | _ + 1, 0 => false
  | a + 1, b + 1 => natEq a b

theorem natEq_refl (n : Nat) : natEq n n = true := by
  induction n with
  | zero => rfl
  | succ k ih => exact ih

theorem natEq_sound (a b : Nat) : natEq a b = true → a = b := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => intro _; rfl
    | succ _ => intro h; cases h
  | succ k ih =>
    cases b with
    | zero => intro h; cases h
    | succ m =>
      intro h
      have hk : k = m := ih m h
      rw [hk]

theorem natEq_true_iff (a b : Nat) : natEq a b = true ↔ a = b := by
  constructor
  · exact natEq_sound a b
  · intro h; rw [h]; exact natEq_refl b

noncomputable def natListEq : List Nat → List Nat → Bool
  | [], [] => true
  | x :: xs, y :: ys => boolAnd (natEq x y) (natListEq xs ys)
  | _, _ => false
where
  boolAnd : Bool → Bool → Bool
    | true, true => true
    | _, _ => false

noncomputable def bAnd : Bool → Bool → Bool
  | true, true => true
  | _, _ => false

noncomputable def bOr : Bool → Bool → Bool
  | false, false => false
  | _, _ => true

noncomputable def bNot : Bool → Bool
  | true => false
  | false => true

theorem bAnd_true_iff (a b : Bool) : bAnd a b = true ↔ (a = true ∧ b = true) := by
  cases a <;> cases b <;> constructor <;> intro h
  · cases h
  · cases h.1
  · cases h
  · cases h.1
  · cases h
  · cases h.2
  · exact ⟨rfl, rfl⟩
  · rfl

theorem bOr_true_iff (a b : Bool) : bOr a b = true ↔ (a = true ∨ b = true) := by
  cases a <;> cases b <;> constructor <;> intro h
  · cases h
  · cases h with
    | inl h1 => cases h1
    | inr h2 => cases h2
  · exact Or.inr rfl
  · rfl
  · exact Or.inl rfl
  · rfl
  · exact Or.inl rfl
  · rfl

theorem bAnd_refl_true (a : Bool) : bAnd a a = a := by
  cases a <;> rfl

noncomputable def natListBeq : List Nat → List Nat → Bool
  | [], [] => true
  | x :: xs, y :: ys => bAnd (natEq x y) (natListBeq xs ys)
  | _, _ => false

theorem natListBeq_refl (xs : List Nat) : natListBeq xs xs = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change bAnd (natEq x x) (natListBeq xs xs) = true
    rw [natEq_refl x, ih]
    rfl

theorem natListBeq_true_iff (xs ys : List Nat) : natListBeq xs ys = true ↔ xs = ys := by
  constructor
  · induction xs generalizing ys with
    | nil =>
      cases ys with
      | nil => intro _; rfl
      | cons _ _ => intro h; cases h
    | cons x xs ih =>
      cases ys with
      | nil => intro h; cases h
      | cons y ys =>
        intro h
        change bAnd (natEq x y) (natListBeq xs ys) = true at h
        have hp := (bAnd_true_iff (natEq x y) (natListBeq xs ys)).mp h
        have hx : x = y := (natEq_true_iff x y).mp hp.1
        have hxs : xs = ys := ih ys hp.2
        rw [hx, hxs]
  · intro h; rw [h]; exact natListBeq_refl ys

noncomputable def natLt : Nat → Nat → Bool
  | _, 0 => false
  | 0, _ + 1 => true
  | a + 1, b + 1 => natLt a b

theorem natLt_zero_false (n : Nat) : natLt n 0 = false := by
  cases n <;> rfl

theorem natLt_succ_self (n : Nat) : natLt n (n + 1) = true := by
  induction n with
  | zero => rfl
  | succ k ih => exact ih

noncomputable def listLen {α : Type} : List α → Nat
  | [] => 0
  | _ :: xs => listLen xs + 1

noncomputable def getAt {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => getAt xs n

noncomputable def allList {α : Type} (p : α → Bool) : List α → Bool
  | [] => true
  | x :: xs => bAnd (p x) (allList p xs)

theorem allList_true_cons {α : Type} (p : α → Bool) (x : α) (xs : List α) :
    allList p (x :: xs) = true ↔ (p x = true ∧ allList p xs = true) := by
  exact bAnd_true_iff (p x) (allList p xs)

/-! ## Section 2: `ConstTy`, `ValTree`, `CtfeMemVal`, and `constToValTree` Canonicalization -/

/-- Type-level constant parameter and value types modeled after `rustc_type_ir::TyKind`. -/
inductive ConstTy where
  | bool
  | char
  | uint (bits : Nat)
  | int (bits : Nat)
  | unit
  | array (elem : ConstTy) (len : Nat)
  | slice (elem : ConstTy)
  | str
  | ref (isMut : Bool) (inner : ConstTy)
  | structTy (id : Nat) (fields : List ConstTy)
  | enumTy (id : Nat) (variants : List (List ConstTy))
  | tuple (elems : List ConstTy)
  | unionTy (id : Nat) (alts : List ConstTy)
  | float32
  | fnPtr

/-- Canonical type-level value tree (`rustc_type_ir::ValTreeKind`). -/
inductive ValTree where
  | leaf (bits : Nat)
  | branch (children : List ValTree)

/-- Raw CTFE memory representation retaining `allocId`, padding bytes, and non-canonical
identities that `const_to_valtree_inner` erases or rejects. -/
inductive CtfeMemVal where
  | scalar (bits : Nat)
  | float32Bits (bits : Nat)
  | unitVal
  | refAlloc (allocId : Nat) (pointee : CtfeMemVal)
  | mutRefAlloc (allocId : Nat) (pointee : CtfeMemVal)
  | arrayVal (elems : List CtfeMemVal)
  | sliceVal (elems : List CtfeMemVal)
  | strVal (bytes : List Nat)
  | structVal (padBytes : List Nat) (fields : List CtfeMemVal)
  | enumVal (variantIdx : Nat) (padBytes : List Nat) (fields : List CtfeMemVal)
  | tupleVal (padBytes : List Nat) (elems : List CtfeMemVal)
  | unionVal (activeAlt : Nat) (rawBytes : List Nat)
  | fnPtrVal (instanceId : Nat)

mutual
  noncomputable def valTreeEq : ValTree → ValTree → Bool
    | .leaf a, .leaf b => natEq a b
    | .branch xs, .branch ys => valTreeListEq xs ys
    | _, _ => false

  noncomputable def valTreeListEq : List ValTree → List ValTree → Bool
    | [], [] => true
    | x :: xs, y :: ys => bAnd (valTreeEq x y) (valTreeListEq xs ys)
    | _, _ => false
end

mutual
  theorem valTreeEq_refl (v : ValTree) : valTreeEq v v = true := by
    cases v with
    | leaf a => exact natEq_refl a
    | branch xs => exact valTreeListEq_refl xs

  theorem valTreeListEq_refl : (xs : List ValTree) → valTreeListEq xs xs = true
    | [] => rfl
    | x :: xs => by
      change bAnd (valTreeEq x x) (valTreeListEq xs xs) = true
      rw [valTreeEq_refl x, valTreeListEq_refl xs]
      rfl
end

mutual
  theorem valTreeEq_sound : (a b : ValTree) → valTreeEq a b = true → a = b
    | .leaf x, .leaf y, h => by
      have hx : x = y := (natEq_true_iff x y).mp h
      rw [hx]
    | .leaf _, .branch _, h => by cases h
    | .branch _, .leaf _, h => by cases h
    | .branch xs, .branch ys, h => by
      have hxy : xs = ys := valTreeListEq_sound xs ys h
      rw [hxy]

  theorem valTreeListEq_sound : (xs ys : List ValTree) → valTreeListEq xs ys = true → xs = ys
    | [], [], _ => rfl
    | [], _ :: _, h => by cases h
    | _ :: _, [], h => by cases h
    | x :: xs, y :: ys, h => by
      change bAnd (valTreeEq x y) (valTreeListEq xs ys) = true at h
      have hp := (bAnd_true_iff (valTreeEq x y) (valTreeListEq xs ys)).mp h
      have hx : x = y := valTreeEq_sound x y hp.1
      have hxs : xs = ys := valTreeListEq_sound xs ys hp.2
      rw [hx, hxs]
end

theorem valTreeEq_true_iff (a b : ValTree) : valTreeEq a b = true ↔ a = b := by
  constructor
  · exact valTreeEq_sound a b
  · intro h; rw [h]; exact valTreeEq_refl b

mutual
  noncomputable def constTyEq : ConstTy → ConstTy → Bool
    | .bool, .bool => true
    | .char, .char => true
    | .uint w₁, .uint w₂ => natEq w₁ w₂
    | .int w₁, .int w₂ => natEq w₁ w₂
    | .unit, .unit => true
    | .array e₁ n₁, .array e₂ n₂ => bAnd (constTyEq e₁ e₂) (natEq n₁ n₂)
    | .slice e₁, .slice e₂ => constTyEq e₁ e₂
    | .str, .str => true
    | .ref m₁ i₁, .ref m₂ i₂ => bAnd (boolEq m₁ m₂) (constTyEq i₁ i₂)
    | .structTy id₁ fs₁, .structTy id₂ fs₂ => bAnd (natEq id₁ id₂) (constTyListEq fs₁ fs₂)
    | .enumTy id₁ vs₁, .enumTy id₂ vs₂ => bAnd (natEq id₁ id₂) (constTyVariantListEq vs₁ vs₂)
    | .tuple es₁, .tuple es₂ => constTyListEq es₁ es₂
    | .unionTy id₁ as₁, .unionTy id₂ as₂ => bAnd (natEq id₁ id₂) (constTyListEq as₁ as₂)
    | .float32, .float32 => true
    | .fnPtr, .fnPtr => true
    | _, _ => false

  noncomputable def constTyListEq : List ConstTy → List ConstTy → Bool
    | [], [] => true
    | x :: xs, y :: ys => bAnd (constTyEq x y) (constTyListEq xs ys)
    | _, _ => false

  noncomputable def constTyVariantListEq : List (List ConstTy) → List (List ConstTy) → Bool
    | [], [] => true
    | x :: xs, y :: ys => bAnd (constTyListEq x y) (constTyVariantListEq xs ys)
    | _, _ => false
end

/-- Valid scalar range check for canonical `ScalarInt` leaves (`valtrees.rs:113-119`). -/
noncomputable def scalarInRange : ConstTy → Nat → Bool
  | .bool, b => bOr (natEq b 0) (natEq b 1)
  | .char, b => natLt b 1114112
  | .uint w, b => natLt b (Nat.pow 2 w)
  | .int w, b => natLt b (Nat.pow 2 w)
  | _, _ => false

/-- Check whether `bytes` are valid `u8` scalar byte leaves (`< 256`). -/
noncomputable def bytesValid : List Nat → Bool
  | [] => true
  | b :: bs => bAnd (natLt b 256) (bytesValid bs)

/-- Convert raw byte list into `ValTree.branch` of `u8` leaves (`ValTree::from_raw_bytes`). -/
noncomputable def bytesToValTreeList : List Nat → List ValTree
  | [] => []
  | b :: bs => .leaf b :: bytesToValTreeList bs

/-- Extract raw byte list back from `ValTree` leaf list (`Value::try_to_raw_bytes`). -/
noncomputable def valTreeListToBytes : List ValTree → Option (List Nat)
  | [] => some []
  | .leaf b :: vs =>
    if natLt b 256 then
      match valTreeListToBytes vs with
      | some bs => some (b :: bs)
      | none => none
    else none
  | .branch _ :: _ => none

theorem bytesToValTreeList_roundtrip (bs : List Nat) (hb : bytesValid bs = true) :
    valTreeListToBytes (bytesToValTreeList bs) = some bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    change bAnd (natLt b 256) (bytesValid bs) = true at hb
    have hp := (bAnd_true_iff (natLt b 256) (bytesValid bs)).mp hb
    have hrest := ih hp.2
    change (if natLt b 256 then match valTreeListToBytes (bytesToValTreeList bs) with | some r => some (b :: r) | none => none else none) = some (b :: bs)
    rw [hp.1]
    simp [hrest]

noncomputable def mapOpt {α β : Type} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | x :: xs =>
    match f x, mapOpt f xs with
    | some y, some ys => some (y :: ys)
    | _, _ => none

noncomputable def mapOptBool {α : Type} (f : α → α → Option Bool) :
    List α → List α → Option Bool
  | [], [] => some true
  | x :: xs, y :: ys =>
    match f x y, mapOptBool f xs ys with
    | some b₁, some b₂ => some (bAnd b₁ b₂)
    | _, _ => none
  | _, _ => none

theorem mapOpt_nil {α β : Type} (f : α → Option β) : mapOpt f [] = some [] := rfl

theorem mapOpt_cons {α β : Type} (f : α → Option β) (x : α) (xs : List α) :
    mapOpt f (x :: xs) =
    match f x, mapOpt f xs with
    | some y, some ys => some (y :: ys)
    | _, _ => none := rfl

theorem mapOptBool_nil {α : Type} (f : α → α → Option Bool) : mapOptBool f [] [] = some true := rfl

theorem mapOptBool_cons {α : Type} (f : α → α → Option Bool) (x : α) (xs : List α)
    (y : α) (ys : List α) :
    mapOptBool f (x :: xs) (y :: ys) =
    match f x y, mapOptBool f xs ys with
    | some b₁, some b₂ => some (bAnd b₁ b₂)
    | _, _ => none := rfl

theorem mapOpt_roundtrip {α β : Type} (f : α → Option β) (g : β → Option α)
    (hfg : ∀ b a, f b = some a → g a = some b)
    (bs : List α) (as : List β)
    (h : mapOpt f bs = some as) :
    mapOpt g as = some bs := by
  induction bs generalizing as with
  | nil => cases h; rfl
  | cons b bs ih =>
    change (match f b, mapOpt f bs with | some y, some ys => some (y :: ys) | _, _ => none) = some as at h
    cases hb : f b with
    | none => rw [hb] at h; cases h
    | some y =>
      cases hbs : mapOpt f bs with
      | none => rw [hb, hbs] at h; cases h
      | some ys =>
        rw [hb, hbs] at h; injection h with has; rw [← has]
        have hg := hfg b y hb
        have hgs := ih ys hbs
        change (match g y, mapOpt g ys with | some b', some bs' => some (b' :: bs') | _, _ => none) = some (b :: bs)
        rw [hg, hgs]

/- Canonicalization from CTFE memory values (`CtfeMemVal`) to type-level `ValTree`,
matching `const_to_valtree_inner` (`compiler/rustc_const_eval/src/const_eval/valtrees.rs:83-219`):
- `&T` dereferences CTFE `AllocId`, erasing allocation identity.
- Structs, tuples, and enums project fields only, erasing `padBytes`.
- Enums prepend `ValTree.leaf variantIdx` before variant fields.
- `&mut`, unions, and `fn` pointers fail closed (`none`). -/
mutual
  noncomputable def constToValTree : ConstTy → CtfeMemVal → Option ValTree
    | .bool, .scalar b => if scalarInRange .bool b then some (.leaf b) else none
    | .char, .scalar b => if scalarInRange .char b then some (.leaf b) else none
    | .uint w, .scalar b => if scalarInRange (.uint w) b then some (.leaf b) else none
    | .int w, .scalar b => if scalarInRange (.int w) b then some (.leaf b) else none
    | .unit, .unitVal => some (.branch [])
    | .array elem len, .arrayVal elems =>
      if natEq (listLen elems) len then
        match mapOpt (fun x => constToValTree elem x) elems with
        | some vs => some (.branch vs)
        | none => none
      else none
    | .slice elem, .sliceVal elems =>
      match mapOpt (fun x => constToValTree elem x) elems with
      | some vs => some (.branch vs)
      | none => none
    | .str, .strVal bs =>
      if bytesValid bs then some (.branch (bytesToValTreeList bs)) else none
    | .ref false inner, .refAlloc _ target => constToValTree inner target
    | .structTy _ fieldTys, .structVal _ fieldVals =>
      match constToValTreeHeterog fieldTys fieldVals with
      | some vs => some (.branch vs)
      | none => none
    | .tuple elemTys, .tupleVal _ elemVals =>
      match constToValTreeHeterog elemTys elemVals with
      | some vs => some (.branch vs)
      | none => none
    | .enumTy _ variants, .enumVal vIdx _ fieldVals =>
      match constToValTreeVariants variants vIdx fieldVals with
      | some vs => some (.branch (.leaf vIdx :: vs))
      | none => none
    | _, _ => none

  noncomputable def constToValTreeHeterog : List ConstTy → List CtfeMemVal → Option (List ValTree)
    | [], [] => some []
    | t :: ts, x :: xs =>
      match constToValTree t x, constToValTreeHeterog ts xs with
      | some v, some vs => some (v :: vs)
      | _, _ => none
    | _, _ => none

  noncomputable def constToValTreeVariants :
      List (List ConstTy) → Nat → List CtfeMemVal → Option (List ValTree)
    | [], _, _ => none
    | fieldTys :: _, 0, fieldVals => constToValTreeHeterog fieldTys fieldVals
    | _ :: rest, k + 1, fieldVals => constToValTreeVariants rest k fieldVals
end

noncomputable def constToValTreeHomog (elem : ConstTy) : List CtfeMemVal → Option (List ValTree) :=
  mapOpt (constToValTree elem)

theorem constToValTreeVariants_eq_getAt (variants : List (List ConstTy)) (vIdx : Nat)
    (fieldVals : List CtfeMemVal) :
    constToValTreeVariants variants vIdx fieldVals =
    match getAt variants vIdx with
    | some fieldTys => constToValTreeHeterog fieldTys fieldVals
    | none => none := by
  induction variants generalizing vIdx with
  | nil => cases vIdx <;> rfl
  | cons _ tl ih =>
    cases vIdx with
    | zero => rfl
    | succ k => exact ih k

/- Reconstruction from `ValTree` back into a canonical CTFE memory value (`valtree_to_const_value`
and `valtree_into_mplace`, `valtrees.rs:298-487`), assigning canonical `allocId := 0` and
empty padding `padBytes := []`. -/
mutual
  noncomputable def valTreeToCtfeMem : ConstTy → ValTree → Option CtfeMemVal
    | .bool, .leaf b => if scalarInRange .bool b then some (.scalar b) else none
    | .char, .leaf b => if scalarInRange .char b then some (.scalar b) else none
    | .uint w, .leaf b => if scalarInRange (.uint w) b then some (.scalar b) else none
    | .int w, .leaf b => if scalarInRange (.int w) b then some (.scalar b) else none
    | .unit, .branch [] => some .unitVal
    | .array elem len, .branch vs =>
      if natEq (listLen vs) len then
        match mapOpt (fun v => valTreeToCtfeMem elem v) vs with
        | some elems => some (.arrayVal elems)
        | none => none
      else none
    | .slice elem, .branch vs =>
      match mapOpt (fun v => valTreeToCtfeMem elem v) vs with
      | some elems => some (.sliceVal elems)
      | none => none
    | .str, .branch vs =>
      match valTreeListToBytes vs with
      | some bs => some (.strVal bs)
      | none => none
    | .ref false inner, vt =>
      match valTreeToCtfeMem inner vt with
      | some target => some (.refAlloc 0 target)
      | none => none
    | .structTy _ fieldTys, .branch vs =>
      match valTreeToCtfeMemHeterog fieldTys vs with
      | some vals => some (.structVal [] vals)
      | none => none
    | .tuple elemTys, .branch vs =>
      match valTreeToCtfeMemHeterog elemTys vs with
      | some vals => some (.tupleVal [] vals)
      | none => none
    | .enumTy _ variants, .branch (.leaf vIdx :: vs) =>
      match valTreeToCtfeMemVariants variants vIdx vs with
      | some vals => some (.enumVal vIdx [] vals)
      | none => none
    | _, _ => none

  noncomputable def valTreeToCtfeMemHeterog : List ConstTy → List ValTree → Option (List CtfeMemVal)
    | [], [] => some []
    | t :: ts, v :: vs =>
      match valTreeToCtfeMem t v, valTreeToCtfeMemHeterog ts vs with
      | some x, some xs => some (x :: xs)
      | _, _ => none
    | _, _ => none

  noncomputable def valTreeToCtfeMemVariants :
      List (List ConstTy) → Nat → List ValTree → Option (List CtfeMemVal)
    | [], _, _ => none
    | fieldTys :: _, 0, vs => valTreeToCtfeMemHeterog fieldTys vs
    | _ :: rest, k + 1, vs => valTreeToCtfeMemVariants rest k vs
end

noncomputable def valTreeToCtfeMemHomog (elem : ConstTy) : List ValTree → Option (List CtfeMemVal) :=
  mapOpt (valTreeToCtfeMem elem)

theorem valTreeToCtfeMemVariants_eq_getAt (variants : List (List ConstTy)) (vIdx : Nat)
    (vs : List ValTree) :
    valTreeToCtfeMemVariants variants vIdx vs =
    match getAt variants vIdx with
    | some fieldTys => valTreeToCtfeMemHeterog fieldTys vs
    | none => none := by
  induction variants generalizing vIdx with
  | nil => cases vIdx <;> rfl
  | cons _ tl ih =>
    cases vIdx with
    | zero => rfl
    | succ k => exact ih k

/-! ### Pillar 1a Theorems: Erasure of `AllocId`, Padding, and Mutability/Union Rejection -/

theorem ctfe_alloc_id_erasure (inner : ConstTy) (a₁ a₂ : Nat) (target : CtfeMemVal) :
    constToValTree (.ref false inner) (.refAlloc a₁ target) =
    constToValTree (.ref false inner) (.refAlloc a₂ target) := by
  rfl

theorem struct_padding_erasure (sid : Nat) (flds : List ConstTy)
    (pad₁ pad₂ : List Nat) (vals : List CtfeMemVal) :
    constToValTree (.structTy sid flds) (.structVal pad₁ vals) =
    constToValTree (.structTy sid flds) (.structVal pad₂ vals) := by
  rfl

theorem tuple_padding_erasure (elemTys : List ConstTy)
    (pad₁ pad₂ : List Nat) (vals : List CtfeMemVal) :
    constToValTree (.tuple elemTys) (.tupleVal pad₁ vals) =
    constToValTree (.tuple elemTys) (.tupleVal pad₂ vals) := by
  rfl

theorem enum_padding_erasure (eid : Nat) (variants : List (List ConstTy))
    (vIdx : Nat) (pad₁ pad₂ : List Nat) (vals : List CtfeMemVal) :
    constToValTree (.enumTy eid variants) (.enumVal vIdx pad₁ vals) =
    constToValTree (.enumTy eid variants) (.enumVal vIdx pad₂ vals) := by
  rfl

theorem union_rejected_by_valtree (uid : Nat) (alts : List ConstTy) (m : CtfeMemVal) :
    constToValTree (.unionTy uid alts) m = none := by
  cases m <;> rfl

theorem fnPtr_rejected_by_valtree (m : CtfeMemVal) :
    constToValTree .fnPtr m = none := by
  cases m <;> rfl

theorem mut_ref_rejected_by_valtree (inner : ConstTy) (m : CtfeMemVal) :
    constToValTree (.ref true inner) m = none := by
  cases m <;> rfl

theorem scalar_listLen_homog (elem : ConstTy) (elems : List CtfeMemVal) (vs : List ValTree)
    (h : constToValTreeHomog elem elems = some vs) :
    listLen vs = listLen elems := by
  unfold constToValTreeHomog at h
  induction elems generalizing vs with
  | nil =>
    cases h
    rfl
  | cons x xs ih =>
    rw [mapOpt_cons] at h
    cases hx : constToValTree elem x with
    | none => rw [hx] at h; cases h
    | some v =>
      cases hxs : mapOpt (constToValTree elem) xs with
      | none => rw [hx, hxs] at h; cases h
      | some vs' =>
        rw [hx, hxs] at h
        injection h with hv
        rw [← hv]
        change listLen vs' + 1 = listLen xs + 1
        rw [ih vs' hxs]

theorem valTreeListToBytes_valid_and_roundtrip (vs : List ValTree) (bs : List Nat)
    (h : valTreeListToBytes vs = some bs) :
    bytesValid bs = true ∧ bytesToValTreeList bs = vs := by
  induction vs generalizing bs with
  | nil =>
    cases h
    exact ⟨rfl, rfl⟩
  | cons v vs ih =>
    cases v with
    | branch _ => cases h
    | leaf b =>
      change (if natLt b 256 then match valTreeListToBytes vs with | some r => some (b :: r) | none => none else none) = some bs at h
      cases hlt : natLt b 256 with
      | false => rw [hlt] at h; cases h
      | true =>
        rw [hlt] at h
        cases hrest : valTreeListToBytes vs with
        | none => rw [hrest] at h; cases h
        | some r =>
          rw [hrest] at h
          injection h with hbs
          rw [← hbs]
          have ihPair := ih r hrest
          constructor
          · change bAnd (natLt b 256) (bytesValid r) = true
            rw [hlt, ihPair.1]
            rfl
          · change ValTree.leaf b :: bytesToValTreeList r = ValTree.leaf b :: vs
            rw [ihPair.2]

theorem valTreeToCtfeMem_homog_len (elem : ConstTy) (vs : List ValTree) (elems : List CtfeMemVal)
    (h : valTreeToCtfeMemHomog elem vs = some elems) :
    listLen elems = listLen vs := by
  unfold valTreeToCtfeMemHomog at h
  induction vs generalizing elems with
  | nil => cases h; rfl
  | cons v vs ih =>
    rw [mapOpt_cons] at h
    cases hv : valTreeToCtfeMem elem v with
    | none => rw [hv] at h; cases h
    | some x =>
      cases hvs : mapOpt (valTreeToCtfeMem elem) vs with
      | none => rw [hv, hvs] at h; cases h
      | some xs =>
        rw [hv, hvs] at h
        injection h with he
        rw [← he]
        change listLen xs + 1 = listLen vs + 1
        rw [ih xs hvs]

/-! ### Round-Trip Soundness (`valtree_to_const_value` followed by `const_to_valtree`) -/

mutual
  theorem valTree_roundtrip (ty : ConstTy) (vt : ValTree) (m : CtfeMemVal)
      (h : valTreeToCtfeMem ty vt = some m) :
      constToValTree ty m = some vt := by
    cases ty with
    | bool =>
      cases vt with
      | branch _ => cases h
      | leaf b =>
        change (if scalarInRange .bool b then some (CtfeMemVal.scalar b) else none) = some m at h
        cases hr : scalarInRange .bool b with
        | false => rw [hr] at h; cases h
        | true =>
          rw [hr] at h; injection h with hm; rw [← hm]
          change (if scalarInRange .bool b then some (ValTree.leaf b) else none) = some (ValTree.leaf b)
          rw [hr]; rfl
    | char =>
      cases vt with
      | branch _ => cases h
      | leaf b =>
        change (if scalarInRange .char b then some (CtfeMemVal.scalar b) else none) = some m at h
        cases hr : scalarInRange .char b with
        | false => rw [hr] at h; cases h
        | true =>
          rw [hr] at h; injection h with hm; rw [← hm]
          change (if scalarInRange .char b then some (ValTree.leaf b) else none) = some (ValTree.leaf b)
          rw [hr]; rfl
    | uint w =>
      cases vt with
      | branch _ => cases h
      | leaf b =>
        change (if scalarInRange (.uint w) b then some (CtfeMemVal.scalar b) else none) = some m at h
        cases hr : scalarInRange (.uint w) b with
        | false => rw [hr] at h; cases h
        | true =>
          rw [hr] at h; injection h with hm; rw [← hm]
          change (if scalarInRange (.uint w) b then some (ValTree.leaf b) else none) = some (ValTree.leaf b)
          rw [hr]; rfl
    | int w =>
      cases vt with
      | branch _ => cases h
      | leaf b =>
        change (if scalarInRange (.int w) b then some (CtfeMemVal.scalar b) else none) = some m at h
        cases hr : scalarInRange (.int w) b with
        | false => rw [hr] at h; cases h
        | true =>
          rw [hr] at h; injection h with hm; rw [← hm]
          change (if scalarInRange (.int w) b then some (ValTree.leaf b) else none) = some (ValTree.leaf b)
          rw [hr]; rfl
    | unit =>
      cases vt with
      | leaf _ => cases h
      | branch vs =>
        cases vs with
        | cons _ _ => cases h
        | nil => cases h; rfl
    | array elem len =>
      cases vt with
      | leaf _ => cases h
      | branch vs =>
        change (if natEq (listLen vs) len then match valTreeToCtfeMemHomog elem vs with | some elems => some (.arrayVal elems) | none => none else none) = some m at h
        cases hlen : natEq (listLen vs) len with
        | false => rw [hlen] at h; cases h
        | true =>
          rw [hlen] at h
          cases hh : valTreeToCtfeMemHomog elem vs with
          | none => rw [hh] at h; cases h
          | some elems =>
            rw [hh] at h; injection h with hm; rw [← hm]
            have hEqLen : listLen elems = listLen vs := valTreeToCtfeMem_homog_len elem vs elems hh
            have hNatLen : natEq (listLen elems) len = true := by rw [hEqLen]; exact hlen
            have hRound := mapOpt_roundtrip (valTreeToCtfeMem elem) (constToValTree elem)
              (fun v x hv => valTree_roundtrip elem v x hv) vs elems hh
            change (if natEq (listLen elems) len then match mapOpt (fun x => constToValTree elem x) elems with | some vs' => some (ValTree.branch vs') | none => none else none) = some (ValTree.branch vs)
            rw [hNatLen, hRound]; rfl
    | slice elem =>
      cases vt with
      | leaf _ => cases h
      | branch vs =>
        change (match valTreeToCtfeMemHomog elem vs with | some elems => some (.sliceVal elems) | none => none) = some m at h
        cases hh : valTreeToCtfeMemHomog elem vs with
        | none => rw [hh] at h; cases h
        | some elems =>
          rw [hh] at h; injection h with hm; rw [← hm]
          have hRound := mapOpt_roundtrip (valTreeToCtfeMem elem) (constToValTree elem)
            (fun v x hv => valTree_roundtrip elem v x hv) vs elems hh
          change (match mapOpt (fun x => constToValTree elem x) elems with | some vs' => some (ValTree.branch vs') | none => none) = some (ValTree.branch vs)
          rw [hRound]
    | str =>
      cases vt with
      | leaf _ => cases h
      | branch vs =>
        change (match valTreeListToBytes vs with | some bs => some (.strVal bs) | none => none) = some m at h
        cases hb : valTreeListToBytes vs with
        | none => rw [hb] at h; cases h
        | some bs =>
          rw [hb] at h; injection h with hm; rw [← hm]
          have hPair := valTreeListToBytes_valid_and_roundtrip vs bs hb
          change (if bytesValid bs then some (ValTree.branch (bytesToValTreeList bs)) else none) = some (ValTree.branch vs)
          rw [hPair.1, hPair.2]; rfl
    | ref isMut inner =>
      cases isMut with
      | true => cases h
      | false =>
        change (match valTreeToCtfeMem inner vt with | some target => some (.refAlloc 0 target) | none => none) = some m at h
        cases ht : valTreeToCtfeMem inner vt with
        | none => rw [ht] at h; cases h
        | some target =>
          rw [ht] at h; injection h with hm; rw [← hm]
          exact valTree_roundtrip inner vt target ht
    | structTy _ fieldTys =>
      cases vt with
      | leaf _ => cases h
      | branch vs =>
        change (match valTreeToCtfeMemHeterog fieldTys vs with | some vals => some (.structVal [] vals) | none => none) = some m at h
        cases hh : valTreeToCtfeMemHeterog fieldTys vs with
        | none => rw [hh] at h; cases h
        | some vals =>
          rw [hh] at h; injection h with hm; rw [← hm]
          have hRound := valTreeHeterog_roundtrip fieldTys vs vals hh
          change (match constToValTreeHeterog fieldTys vals with | some vs' => some (ValTree.branch vs') | none => none) = some (ValTree.branch vs)
          rw [hRound]
    | tuple elemTys =>
      cases vt with
      | leaf _ => cases h
      | branch vs =>
        change (match valTreeToCtfeMemHeterog elemTys vs with | some vals => some (.tupleVal [] vals) | none => none) = some m at h
        cases hh : valTreeToCtfeMemHeterog elemTys vs with
        | none => rw [hh] at h; cases h
        | some vals =>
          rw [hh] at h; injection h with hm; rw [← hm]
          have hRound := valTreeHeterog_roundtrip elemTys vs vals hh
          change (match constToValTreeHeterog elemTys vals with | some vs' => some (ValTree.branch vs') | none => none) = some (ValTree.branch vs)
          rw [hRound]
    | enumTy _ variants =>
      cases vt with
      | leaf _ => cases h
      | branch vs =>
        cases vs with
        | nil => cases h
        | cons hd tl =>
          cases hd with
          | branch _ => cases h
          | leaf vIdx =>
            change (match valTreeToCtfeMemVariants variants vIdx tl with | some vals => some (.enumVal vIdx [] vals) | none => none) = some m at h
            cases hh : valTreeToCtfeMemVariants variants vIdx tl with
            | none => rw [hh] at h; cases h
            | some vals =>
              rw [hh] at h; injection h with hm; rw [← hm]
              have hRound := valTreeVariants_roundtrip variants vIdx tl vals hh
              change (match constToValTreeVariants variants vIdx vals with | some vs' => some (ValTree.branch (ValTree.leaf vIdx :: vs')) | none => none) = some (ValTree.branch (ValTree.leaf vIdx :: tl))
              rw [hRound]
    | unionTy _ _ => cases h
    | float32 => cases h
    | fnPtr => cases h

  theorem valTreeHeterog_roundtrip (ts : List ConstTy) (vs : List ValTree) (vals : List CtfeMemVal)
      (h : valTreeToCtfeMemHeterog ts vs = some vals) :
      constToValTreeHeterog ts vals = some vs := by
    cases ts with
    | nil =>
      cases vs with
      | nil => cases h; rfl
      | cons _ _ => cases h
    | cons t ts' =>
      cases vs with
      | nil => cases h
      | cons v vs' =>
        change (match valTreeToCtfeMem t v, valTreeToCtfeMemHeterog ts' vs' with | some x, some xs => some (x :: xs) | _, _ => none) = some vals at h
        cases hv : valTreeToCtfeMem t v with
        | none => rw [hv] at h; cases h
        | some x =>
          cases hvs : valTreeToCtfeMemHeterog ts' vs' with
          | none => rw [hv, hvs] at h; cases h
          | some xs =>
            rw [hv, hvs] at h; injection h with he; rw [← he]
            have h1 := valTree_roundtrip t v x hv
            have h2 := valTreeHeterog_roundtrip ts' vs' xs hvs
            change (match constToValTree t x, constToValTreeHeterog ts' xs with | some v', some vs'' => some (v' :: vs'') | _, _ => none) = some (v :: vs')
            rw [h1, h2]

  theorem valTreeVariants_roundtrip (variants : List (List ConstTy)) (vIdx : Nat)
      (vs : List ValTree) (vals : List CtfeMemVal)
      (h : valTreeToCtfeMemVariants variants vIdx vs = some vals) :
      constToValTreeVariants variants vIdx vals = some vs := by
    cases variants with
    | nil => cases h
    | cons fieldTys rest =>
      cases vIdx with
      | zero => exact valTreeHeterog_roundtrip fieldTys vs vals h
      | succ k => exact valTreeVariants_roundtrip rest k vs vals h
end

theorem valTreeHomog_roundtrip (elem : ConstTy) (vs : List ValTree) (elems : List CtfeMemVal)
    (h : valTreeToCtfeMemHomog elem vs = some elems) :
    constToValTreeHomog elem elems = some vs :=
  mapOpt_roundtrip (valTreeToCtfeMem elem) (constToValTree elem)
    (fun v x hv => valTree_roundtrip elem v x hv) vs elems h

/-! ## Section 3: Concrete Expression Evaluation, `TypeId` Coherence, and `v0` Symbol Deduplication -/

/-- Concrete compile-time constant expression syntax (`ConstKind` prior to `ValTree`
canonicalization). -/
inductive ConcreteConstExpr where
  | litNat (n : Nat)
  | litBool (b : Bool)
  | litStr (bytes : List Nat)
  | addNat (l r : ConcreteConstExpr)
  | mulNat (l r : ConcreteConstExpr)
  | shlNat (l r : ConcreteConstExpr)
  | boolNot (x : ConcreteConstExpr)
  | mkStruct (padBytes : List Nat) (fields : List ConcreteConstExpr)
  | mkEnum (vIdx : Nat) (padBytes : List Nat) (fields : List ConcreteConstExpr)
  | mkArray (elems : List ConcreteConstExpr)
  | mkSlice (elems : List ConcreteConstExpr)
  | mkRef (allocId : Nat) (target : ConcreteConstExpr)

mutual
  noncomputable def evalConcreteConst : ConcreteConstExpr → Option CtfeMemVal
    | .litNat n => some (.scalar n)
    | .litBool b => some (.scalar (if b then 1 else 0))
    | .litStr bs => some (.strVal bs)
    | .addNat l r =>
      match evalConcreteConst l, evalConcreteConst r with
      | some (.scalar a), some (.scalar b) => some (.scalar (a + b))
      | _, _ => none
    | .mulNat l r =>
      match evalConcreteConst l, evalConcreteConst r with
      | some (.scalar a), some (.scalar b) => some (.scalar (a * b))
      | _, _ => none
    | .shlNat l r =>
      match evalConcreteConst l, evalConcreteConst r with
      | some (.scalar a), some (.scalar b) => some (.scalar (Nat.shiftLeft a b))
      | _, _ => none
    | .boolNot x =>
      match evalConcreteConst x with
      | some (.scalar 0) => some (.scalar 1)
      | some (.scalar 1) => some (.scalar 0)
      | _ => none
    | .mkStruct pad fs =>
      match evalConcreteConstList fs with
      | some vs => some (.structVal pad vs)
      | none => none
    | .mkEnum idx pad fs =>
      match evalConcreteConstList fs with
      | some vs => some (.enumVal idx pad vs)
      | none => none
    | .mkArray es =>
      match evalConcreteConstList es with
      | some vs => some (.arrayVal vs)
      | none => none
    | .mkSlice es =>
      match evalConcreteConstList es with
      | some vs => some (.sliceVal vs)
      | none => none
    | .mkRef aid tgt =>
      match evalConcreteConst tgt with
      | some v => some (.refAlloc aid v)
      | none => none

  noncomputable def evalConcreteConstList : List ConcreteConstExpr → Option (List CtfeMemVal)
    | [] => some []
    | e :: es =>
      match evalConcreteConst e, evalConcreteConstList es with
      | some v, some vs => some (v :: vs)
      | _, _ => none
end

noncomputable def canonicalValTree (ty : ConstTy) (e : ConcreteConstExpr) : Option ValTree :=
  match evalConcreteConst e with
  | some m => constToValTree ty m
  | none => none

/-- Abstract `v0`-mangled const node modeling `compiler/rustc_symbol_mangling/src/v0.rs:771-947`
(`K...`): `kScalar` (`Kj4_`, `Kh5_`, `Kb1_`), `kStrBytes` (`KRe616e6e65616c_`),
`kRef`, `kArrayOrSlice` (`KA...E`), `kStruct` (`KV...S...E`), `kEnum` (`KV...T...E`). -/
inductive V0ConstSym where
  | kScalar (ty : ConstTy) (bits : Nat)
  | kUnit
  | kStrHexBytes (bytes : List Nat)
  | kRef (inner : V0ConstSym)
  | kAgg (elems : List V0ConstSym)
  | kStruct (adtId : Nat) (fields : List V0ConstSym)
  | kEnumVariant (adtId : Nat) (vIdx : Nat) (fields : List V0ConstSym)

mutual
  noncomputable def v0MangleValTree : ConstTy → ValTree → Option V0ConstSym
    | .bool, .leaf b => some (.kScalar .bool b)
    | .char, .leaf b => some (.kScalar .char b)
    | .uint w, .leaf b => some (.kScalar (.uint w) b)
    | .int w, .leaf b => some (.kScalar (.int w) b)
    | .unit, .branch [] => some .kUnit
    | .str, .branch vs =>
      match valTreeListToBytes vs with
      | some bs => some (.kStrHexBytes bs)
      | none => none
    | .ref false inner, vt =>
      match v0MangleValTree inner vt with
      | some s => some (.kRef s)
      | none => none
    | .array elem _, .branch vs =>
      match mapOpt (fun v => v0MangleValTree elem v) vs with
      | some ss => some (.kAgg ss)
      | none => none
    | .slice elem, .branch vs =>
      match mapOpt (fun v => v0MangleValTree elem v) vs with
      | some ss => some (.kAgg ss)
      | none => none
    | .tuple elemTys, .branch vs =>
      match v0MangleHeterog elemTys vs with
      | some ss => some (.kAgg ss)
      | none => none
    | .structTy sid fieldTys, .branch vs =>
      match v0MangleHeterog fieldTys vs with
      | some ss => some (.kStruct sid ss)
      | none => none
    | .enumTy eid variants, .branch (.leaf vIdx :: vs) =>
      match v0MangleVariants variants vIdx vs with
      | some ss => some (.kEnumVariant eid vIdx ss)
      | none => none
    | _, _ => none

  noncomputable def v0MangleHeterog : List ConstTy → List ValTree → Option (List V0ConstSym)
    | [], [] => some []
    | t :: ts, v :: vs =>
      match v0MangleValTree t v, v0MangleHeterog ts vs with
      | some s, some ss => some (s :: ss)
      | _, _ => none
    | _, _ => none

  noncomputable def v0MangleVariants :
      List (List ConstTy) → Nat → List ValTree → Option (List V0ConstSym)
    | [], _, _ => none
    | fieldTys :: _, 0, vs => v0MangleHeterog fieldTys vs
    | _ :: rest, k + 1, vs => v0MangleVariants rest k vs
end

noncomputable def v0MangleHomog (elem : ConstTy) : List ValTree → Option (List V0ConstSym) :=
  mapOpt (v0MangleValTree elem)

/-- `TypeId` and monomorphization key for a type-level constant argument `(ty, canonical_valtree)`. -/
structure TypeIdentityKey where
  carrierId : Nat
  paramTy : ConstTy
  valTree : ValTree

noncomputable def typeIdentityOf (carrierId : Nat) (ty : ConstTy) (e : ConcreteConstExpr) :
    Option TypeIdentityKey :=
  match canonicalValTree ty e with
  | some vt => some { carrierId := carrierId, paramTy := ty, valTree := vt }
  | none => none

noncomputable def v0SymbolOf (ty : ConstTy) (e : ConcreteConstExpr) : Option V0ConstSym :=
  match canonicalValTree ty e with
  | some vt => v0MangleValTree ty vt
  | none => none

/-! ### Pillar 1b Theorems: Evaluation Equivalence -> Canonical `ValTree`, `TypeId`, and `v0` Dedup -/

theorem eval_eq_implies_canonical_valtree (ty : ConstTy) (e₁ e₂ : ConcreteConstExpr)
    (m : CtfeMemVal)
    (h₁ : evalConcreteConst e₁ = some m)
    (h₂ : evalConcreteConst e₂ = some m) :
    canonicalValTree ty e₁ = canonicalValTree ty e₂ := by
  unfold canonicalValTree
  rw [h₁, h₂]

theorem canonical_valtree_determines_type_identity (carrierId : Nat) (ty : ConstTy)
    (e₁ e₂ : ConcreteConstExpr)
    (hvt : canonicalValTree ty e₁ = canonicalValTree ty e₂) :
    typeIdentityOf carrierId ty e₁ = typeIdentityOf carrierId ty e₂ := by
  unfold typeIdentityOf
  rw [hvt]

theorem canonical_valtree_determines_v0_symbol (ty : ConstTy)
    (e₁ e₂ : ConcreteConstExpr)
    (hvt : canonicalValTree ty e₁ = canonicalValTree ty e₂) :
    v0SymbolOf ty e₁ = v0SymbolOf ty e₂ := by
  unfold v0SymbolOf
  rw [hvt]

/-- End-to-end `TypeId` and `v0` monomorphization coherence theorem: any two concrete const
expressions evaluating to the same CTFE value yield identical `ValTree`, `TypeIdentityKey`,
and `v0` mangled symbol. -/
theorem eval_eq_guarantees_typeid_and_v0_dedup (carrierId : Nat) (ty : ConstTy)
    (e₁ e₂ : ConcreteConstExpr) (m : CtfeMemVal)
    (h₁ : evalConcreteConst e₁ = some m)
    (h₂ : evalConcreteConst e₂ = some m) :
    canonicalValTree ty e₁ = canonicalValTree ty e₂ ∧
    typeIdentityOf carrierId ty e₁ = typeIdentityOf carrierId ty e₂ ∧
    v0SymbolOf ty e₁ = v0SymbolOf ty e₂ := by
  have hvt := eval_eq_implies_canonical_valtree ty e₁ e₂ m h₁ h₂
  exact ⟨hvt, canonical_valtree_determines_type_identity carrierId ty e₁ e₂ hvt,
    canonical_valtree_determines_v0_symbol ty e₁ e₂ hvt⟩

/-! ### Concrete Verified `v0` & `TypeId` Witnesses Matching Empirical Probe Outputs -/

noncomputable def tyUsize : ConstTy := .uint 64
noncomputable def tyU8 : ConstTy := .uint 8
noncomputable def tyU32 : ConstTy := .uint 32
noncomputable def tyTag : ConstTy := .structTy 1 [tyU8, .bool]
noncomputable def tyPadded : ConstTy := .structTy 2 [.bool, tyU32]
noncomputable def tyMode : ConstTy := .enumTy 3 [[], [tyU8]]

theorem witness_array_2_plus_2_eq_4_valtree_and_v0 :
    canonicalValTree tyUsize (.addNat (.litNat 2) (.litNat 2)) =
      some (.leaf 4) ∧
    canonicalValTree tyUsize (.litNat 4) = some (.leaf 4) ∧
    v0SymbolOf tyUsize (.addNat (.litNat 2) (.litNat 2)) =
      v0SymbolOf tyUsize (.litNat 4) ∧
    typeIdentityOf 10 tyUsize (.addNat (.litNat 2) (.litNat 2)) =
      typeIdentityOf 10 tyUsize (.litNat 4) := by
  refine ⟨rfl, rfl, rfl, rfl⟩

theorem witness_tag_struct_dedup_with_padding :
    let e₁ : ConcreteConstExpr :=
      .mkStruct [17, 255] [.addNat (.litNat 2) (.litNat 3), .boolNot (.litBool false)]
    let e₂ : ConcreteConstExpr :=
      .mkStruct [0, 0] [.litNat 5, .litBool true]
    canonicalValTree tyTag e₁ = some (.branch [.leaf 5, .leaf 1]) ∧
    canonicalValTree tyTag e₂ = some (.branch [.leaf 5, .leaf 1]) ∧
    v0SymbolOf tyTag e₁ = v0SymbolOf tyTag e₂ ∧
    typeIdentityOf 20 tyTag e₁ = typeIdentityOf 20 tyTag e₂ := by
  refine ⟨rfl, rfl, rfl, rfl⟩

theorem witness_padded_struct_dedup_m2a :
    let e₁ : ConcreteConstExpr :=
      .mkStruct [11, 22, 33] [.litBool true, .litNat 42]
    let e₂ : ConcreteConstExpr :=
      .mkStruct [0, 0, 0] [.litBool true, .addNat (.litNat 40) (.litNat 2)]
    canonicalValTree tyPadded e₁ = some (.branch [.leaf 1, .leaf 42]) ∧
    canonicalValTree tyPadded e₂ = some (.branch [.leaf 1, .leaf 42]) ∧
    v0SymbolOf tyPadded e₁ = v0SymbolOf tyPadded e₂ := by
  refine ⟨rfl, rfl, rfl⟩

theorem witness_mode_enum_checked_7_dedup :
    let e₁ : ConcreteConstExpr := .mkEnum 1 [9] [.addNat (.litNat 3) (.litNat 4)]
    let e₂ : ConcreteConstExpr := .mkEnum 1 [0] [.litNat 7]
    canonicalValTree tyMode e₁ = some (.branch [.leaf 1, .leaf 7]) ∧
    canonicalValTree tyMode e₂ = some (.branch [.leaf 1, .leaf 7]) ∧
    v0SymbolOf tyMode e₁ = some (.kEnumVariant 3 1 [.kScalar tyU8 7]) ∧
    v0SymbolOf tyMode e₁ = v0SymbolOf tyMode e₂ := by
  refine ⟨rfl, rfl, rfl, rfl⟩

theorem witness_str_anneal_ref_dedup :
    let annealBytes : List Nat := [97, 110, 110, 101, 97, 108]
    let e₁ : ConcreteConstExpr := .mkRef 101 (.litStr annealBytes)
    let e₂ : ConcreteConstExpr := .mkRef 999 (.litStr annealBytes)
    v0SymbolOf (.ref false .str) e₁ = some (.kRef (.kStrHexBytes annealBytes)) ∧
    v0SymbolOf (.ref false .str) e₁ = v0SymbolOf (.ref false .str) e₂ ∧
    typeIdentityOf 30 (.ref false .str) e₁ = typeIdentityOf 30 (.ref false .str) e₂ := by
  refine ⟨rfl, rfl, rfl⟩

theorem witness_ref_tag_alloc_erasure :
    let e₁ : ConcreteConstExpr := .mkRef 7 (.mkStruct [42] [.litNat 5, .litBool true])
    let e₂ : ConcreteConstExpr := .mkRef 88 (.mkStruct [0] [.addNat (.litNat 2) (.litNat 3), .boolNot (.litBool false)])
    canonicalValTree (.ref false tyTag) e₁ = canonicalValTree (.ref false tyTag) e₂ ∧
    typeIdentityOf 40 (.ref false tyTag) e₁ = typeIdentityOf 40 (.ref false tyTag) e₂ := by
  refine ⟨rfl, rfl⟩

/-! ## Section 4: `min_const_generics` vs `generic_const_exprs` Syntactic Equality & Next-Solver -/

/-- Anonymous constant kind (`rustc_type_ir::AnonConstKind`, `collect.rs:1813-1841`). -/
inductive AnonConstKind where
  | gce
  | mcg
  | repeatExprCount
  | nonTypeSystemAnon
  | nonTypeSystemInline

/-- Unevaluated abstract constant AST (`ConstKind::{Param, Value, Expr, Alias}`,
`consts/kind.rs:13-24`, `abstract_const.rs`). -/
inductive AbstractConst where
  | param (idx : Nat)
  | lit (val : Nat)
  | add (lhs rhs : AbstractConst)
  | mul (lhs rhs : AbstractConst)
  | anon (defId : Nat) (args : List AbstractConst)

mutual
  noncomputable def abstractMentionsParam : AbstractConst → Bool
    | .param _ => true
    | .lit _ => false
    | .add l r => bOr (abstractMentionsParam l) (abstractMentionsParam r)
    | .mul l r => bOr (abstractMentionsParam l) (abstractMentionsParam r)
    | .anon _ args => abstractListMentionsParam args

  noncomputable def abstractListMentionsParam : List AbstractConst → Bool
    | [] => false
    | c :: cs => bOr (abstractMentionsParam c) (abstractListMentionsParam cs)
end

/-- `min_const_generics` admission rule (`AnonConstKind::MCG` vs `GCE`):
Under `.mcg`, a constant argument is admitted iff it is a standalone `.param idx` OR
contains zero generic parameter references (`!abstractMentionsParam c`). -/
noncomputable def anonConstAdmitted : AnonConstKind → AbstractConst → Bool
  | .gce, _ => true
  | .nonTypeSystemAnon, _ => true
  | .nonTypeSystemInline, _ => true
  | .mcg, .param _ => true
  | .mcg, c => bNot (abstractMentionsParam c)
  | .repeatExprCount, .param _ => true
  | .repeatExprCount, c => bNot (abstractMentionsParam c)

/- Total arithmetic semantics of `AbstractConst` under parameter valuation `ρ : Nat → Nat`
(for `anon` nodes we parameterize by an environment table `interpAnon`). -/
mutual
  noncomputable def evalAbstract (interpAnon : Nat → List Nat → Nat) (ρ : Nat → Nat) :
      AbstractConst → Nat
    | .param i => ρ i
    | .lit n => n
    | .add l r => evalAbstract interpAnon ρ l + evalAbstract interpAnon ρ r
    | .mul l r => evalAbstract interpAnon ρ l * evalAbstract interpAnon ρ r
    | .anon did args => interpAnon did (evalAbstractList interpAnon ρ args)

  noncomputable def evalAbstractList (interpAnon : Nat → List Nat → Nat) (ρ : Nat → Nat) :
      List AbstractConst → List Nat
    | [] => []
    | c :: cs => evalAbstract interpAnon ρ c :: evalAbstractList interpAnon ρ cs
end

/- Syntactic AST equality modeling `ocx.eq` on `ConstKind::Expr` in
`compiler/rustc_trait_selection/src/traits/const_evaluatable.rs:181`. -/
mutual
  noncomputable def synEq : AbstractConst → AbstractConst → Bool
    | .param i, .param j => natEq i j
    | .lit a, .lit b => natEq a b
    | .add l₁ r₁, .add l₂ r₂ => bAnd (synEq l₁ l₂) (synEq r₁ r₂)
    | .mul l₁ r₁, .mul l₂ r₂ => bAnd (synEq l₁ l₂) (synEq r₁ r₂)
    | .anon d₁ as₁, .anon d₂ as₂ => bAnd (natEq d₁ d₂) (synEqList as₁ as₂)
    | _, _ => false

  noncomputable def synEqList : List AbstractConst → List AbstractConst → Bool
    | [], [] => true
    | x :: xs, y :: ys => bAnd (synEq x y) (synEqList xs ys)
    | _, _ => false
end

mutual
  theorem synEq_refl (c : AbstractConst) : synEq c c = true := by
    cases c with
    | param i => exact natEq_refl i
    | lit n => exact natEq_refl n
    | add l r =>
      change bAnd (synEq l l) (synEq r r) = true
      rw [synEq_refl l, synEq_refl r]; rfl
    | mul l r =>
      change bAnd (synEq l l) (synEq r r) = true
      rw [synEq_refl l, synEq_refl r]; rfl
    | anon d args =>
      change bAnd (natEq d d) (synEqList args args) = true
      rw [natEq_refl d, synEqList_refl args]; rfl

  theorem synEqList_refl : (cs : List AbstractConst) → synEqList cs cs = true
    | [] => rfl
    | c :: cs => by
      change bAnd (synEq c c) (synEqList cs cs) = true
      rw [synEq_refl c, synEqList_refl cs]; rfl
end

mutual
  theorem synEq_sound : (a b : AbstractConst) → synEq a b = true → a = b
    | .param i, .param j, h => by rw [(natEq_true_iff i j).mp h]
    | .lit x, .lit y, h => by rw [(natEq_true_iff x y).mp h]
    | .add l₁ r₁, .add l₂ r₂, h => by
      change bAnd (synEq l₁ l₂) (synEq r₁ r₂) = true at h
      have hp := (bAnd_true_iff (synEq l₁ l₂) (synEq r₁ r₂)).mp h
      rw [synEq_sound l₁ l₂ hp.1, synEq_sound r₁ r₂ hp.2]
    | .mul l₁ r₁, .mul l₂ r₂, h => by
      change bAnd (synEq l₁ l₂) (synEq r₁ r₂) = true at h
      have hp := (bAnd_true_iff (synEq l₁ l₂) (synEq r₁ r₂)).mp h
      rw [synEq_sound l₁ l₂ hp.1, synEq_sound r₁ r₂ hp.2]
    | .anon d₁ as₁, .anon d₂ as₂, h => by
      change bAnd (natEq d₁ d₂) (synEqList as₁ as₂) = true at h
      have hp := (bAnd_true_iff (natEq d₁ d₂) (synEqList as₁ as₂)).mp h
      rw [(natEq_true_iff d₁ d₂).mp hp.1, synEqList_sound as₁ as₂ hp.2]
    | .param _, .lit _, h => by cases h
    | .param _, .add _ _, h => by cases h
    | .param _, .mul _ _, h => by cases h
    | .param _, .anon _ _, h => by cases h
    | .lit _, .param _, h => by cases h
    | .lit _, .add _ _, h => by cases h
    | .lit _, .mul _ _, h => by cases h
    | .lit _, .anon _ _, h => by cases h
    | .add _ _, .param _, h => by cases h
    | .add _ _, .lit _, h => by cases h
    | .add _ _, .mul _ _, h => by cases h
    | .add _ _, .anon _ _, h => by cases h
    | .mul _ _, .param _, h => by cases h
    | .mul _ _, .lit _, h => by cases h
    | .mul _ _, .add _ _, h => by cases h
    | .mul _ _, .anon _ _, h => by cases h
    | .anon _ _, .param _, h => by cases h
    | .anon _ _, .lit _, h => by cases h
    | .anon _ _, .add _ _, h => by cases h
    | .anon _ _, .mul _ _, h => by cases h

  theorem synEqList_sound : (as bs : List AbstractConst) → synEqList as bs = true → as = bs
    | [], [], _ => rfl
    | [], _ :: _, h => by cases h
    | _ :: _, [], h => by cases h
    | a :: as, b :: bs, h => by
      change bAnd (synEq a b) (synEqList as bs) = true at h
      have hp := (bAnd_true_iff (synEq a b) (synEqList as bs)).mp h
      rw [synEq_sound a b hp.1, synEqList_sound as bs hp.2]
end

theorem synEq_true_iff (a b : AbstractConst) : synEq a b = true ↔ a = b := by
  constructor
  · exact synEq_sound a b
  · intro h; rw [h]; exact synEq_refl b

/-- Models `Visitor` in `satisfied_from_param_env` (`const_evaluatable.rs:165-218`):
collects whether a target `ct` syntactically matches any subtree of a `ConstEvaluatable`
bound `b_ct`, tracking `single_match` (`none`, `some (some c)`, `some none` for ambiguity). -/
inductive MatchAccum where
  | noMatch
  | unique (c : AbstractConst)
  | ambiguous

noncomputable def mergeMatch : MatchAccum → MatchAccum → MatchAccum
  | .noMatch, m => m
  | m, .noMatch => m
  | .unique a, .unique b => if synEq a b then .unique a else .ambiguous
  | _, _ => .ambiguous

mutual
  noncomputable def visitSubtreeMatch (target : AbstractConst) (cand : AbstractConst) : MatchAccum :=
    let here := if synEq cand target then MatchAccum.unique cand else MatchAccum.noMatch
    let children := match cand with
      | .param _ | .lit _ => MatchAccum.noMatch
      | .add l r => mergeMatch (visitSubtreeMatch target l) (visitSubtreeMatch target r)
      | .mul l r => mergeMatch (visitSubtreeMatch target l) (visitSubtreeMatch target r)
      | .anon _ args => visitSubtreeMatchList target args
    mergeMatch here children

  noncomputable def visitSubtreeMatchList (target : AbstractConst) : List AbstractConst → MatchAccum
    | [] => MatchAccum.noMatch
    | c :: cs => mergeMatch (visitSubtreeMatch target c) (visitSubtreeMatchList target cs)
end

noncomputable def foldParamEnvMatches (target : AbstractConst) : List AbstractConst → MatchAccum
  | [] => MatchAccum.noMatch
  | b :: bs => mergeMatch (visitSubtreeMatch target b) (foldParamEnvMatches target bs)

noncomputable def satisfiedFromParamEnv (env : List AbstractConst) (target : AbstractConst) : Bool :=
  match foldParamEnvMatches target env with
  | .unique _ => true
  | _ => false

/-- Models the trait-solver gate between `generic_const_exprs` and `gca_const_items`
(`compiler/rustc_ast_passes/src/feature_gate.rs:735-783`). -/
inductive SolverMode where
  | legacy
  | nextCoherence
  | nextGlobally

inductive CompilerRelease where
  | v1_98_nightly
  | v1_102_plus_head

inductive SolverResolution where
  | active (effective : SolverMode) (warnedRevert : Bool)
  | rejectedIncompatible

noncomputable def resolveSolver (rel : CompilerRelease) (gceEnabled gcaEnabled : Bool)
    (requested : SolverMode) : SolverResolution :=
  if bAnd gceEnabled gcaEnabled then
    .rejectedIncompatible
  else if gceEnabled then
    match requested, rel with
    | .nextGlobally, .v1_98_nightly => .rejectedIncompatible
    | .nextGlobally, .v1_102_plus_head => .active .nextCoherence true
    | .nextCoherence, _ => .active .nextCoherence false
    | .legacy, _ => .active .legacy false
  else if gcaEnabled then
    match requested with
    | .nextGlobally => .active .nextGlobally false
    | _ => .rejectedIncompatible
  else
    .active requested false

/-! ### Pillar 2 Theorems: Syntactic Soundness, Incompleteness (`N + 1` vs `1 + N`), and Solver Gate -/

theorem synEq_implies_semEq (interpAnon : Nat → List Nat → Nat) (a b : AbstractConst)
    (h : synEq a b = true) :
    ∀ ρ, evalAbstract interpAnon ρ a = evalAbstract interpAnon ρ b := by
  intro ρ
  have hab : a = b := (synEq_true_iff a b).mp h
  rw [hab]

theorem gce_type_unification_preserves_array_len (interpAnon : Nat → List Nat → Nat)
    (c₁ c₂ : AbstractConst) (h : synEq c₁ c₂ = true) :
    ∀ ρ, evalAbstract interpAnon ρ c₁ = evalAbstract interpAnon ρ c₂ :=
  synEq_implies_semEq interpAnon c₁ c₂ h

theorem mcg_closed_const_env_independent (interpAnon : Nat → List Nat → Nat) :
    (c : AbstractConst) → abstractMentionsParam c = false →
    ∀ ρ₁ ρ₂, evalAbstract interpAnon ρ₁ c = evalAbstract interpAnon ρ₂ c
  | .param _, h, _, _ => by cases h
  | .lit _, _, _, _ => rfl
  | .add l r, h, ρ₁, ρ₂ => by
    change bOr (abstractMentionsParam l) (abstractMentionsParam r) = false at h
    cases hl : abstractMentionsParam l with
    | true => rw [hl] at h; cases h
    | false =>
      cases hr : abstractMentionsParam r with
      | true => rw [hl, hr] at h; cases h
      | false =>
        have ihl := mcg_closed_const_env_independent interpAnon l hl ρ₁ ρ₂
        have ihr := mcg_closed_const_env_independent interpAnon r hr ρ₁ ρ₂
        change evalAbstract interpAnon ρ₁ l + evalAbstract interpAnon ρ₁ r =
          evalAbstract interpAnon ρ₂ l + evalAbstract interpAnon ρ₂ r
        rw [ihl, ihr]
  | .mul l r, h, ρ₁, ρ₂ => by
    change bOr (abstractMentionsParam l) (abstractMentionsParam r) = false at h
    cases hl : abstractMentionsParam l with
    | true => rw [hl] at h; cases h
    | false =>
      cases hr : abstractMentionsParam r with
      | true => rw [hl, hr] at h; cases h
      | false =>
        have ihl := mcg_closed_const_env_independent interpAnon l hl ρ₁ ρ₂
        have ihr := mcg_closed_const_env_independent interpAnon r hr ρ₁ ρ₂
        change evalAbstract interpAnon ρ₁ l * evalAbstract interpAnon ρ₁ r =
          evalAbstract interpAnon ρ₂ l * evalAbstract interpAnon ρ₂ r
        rw [ihl, ihr]
  | .anon did args, h, ρ₁, ρ₂ => by
    change abstractListMentionsParam args = false at h
    have hargs : evalAbstractList interpAnon ρ₁ args = evalAbstractList interpAnon ρ₂ args :=
      mcg_closed_list_env_independent interpAnon args h ρ₁ ρ₂
    change interpAnon did (evalAbstractList interpAnon ρ₁ args) =
      interpAnon did (evalAbstractList interpAnon ρ₂ args)
    rw [hargs]
where
  mcg_closed_list_env_independent (interpAnon : Nat → List Nat → Nat) :
      (cs : List AbstractConst) → abstractListMentionsParam cs = false →
      ∀ ρ₁ ρ₂, evalAbstractList interpAnon ρ₁ cs = evalAbstractList interpAnon ρ₂ cs
    | [], _, _, _ => rfl
    | c :: cs, h, ρ₁, ρ₂ => by
      change bOr (abstractMentionsParam c) (abstractListMentionsParam cs) = false at h
      cases hc : abstractMentionsParam c with
      | true => rw [hc] at h; cases h
      | false =>
        cases hcs : abstractListMentionsParam cs with
        | true => rw [hc, hcs] at h; cases h
        | false =>
          have ihc := mcg_closed_const_env_independent interpAnon c hc ρ₁ ρ₂
          have ihcs := mcg_closed_list_env_independent interpAnon cs hcs ρ₁ ρ₂
          change evalAbstract interpAnon ρ₁ c :: evalAbstractList interpAnon ρ₁ cs =
            evalAbstract interpAnon ρ₂ c :: evalAbstractList interpAnon ρ₂ cs
          rw [ihc, ihcs]

theorem mcg_rejects_param_plus_one :
    anonConstAdmitted .mcg (.add (.param 0) (.lit 1)) = false := by
  rfl

theorem gce_admits_param_plus_one :
    anonConstAdmitted .gce (.add (.param 0) (.lit 1)) = true := by
  rfl

/-- Witness of syntactic-only unification incompleteness in `generic_const_exprs`:
`N + 1` and `1 + N` fail `synEq` (`E0308`), yet evaluate identically for ALL `ρ : Nat → Nat`! -/
theorem gce_syntactic_incompleteness_n_plus_1 (interpAnon : Nat → List Nat → Nat) :
    let nPlus1 : AbstractConst := .add (.param 0) (.lit 1)
    let onePlusN : AbstractConst := .add (.lit 1) (.param 0)
    synEq nPlus1 onePlusN = false ∧
    (∀ ρ : Nat → Nat, evalAbstract interpAnon ρ nPlus1 = evalAbstract interpAnon ρ onePlusN) := by
  refine ⟨rfl, ?_⟩
  intro ρ
  exact Nat.add_comm (ρ 0) 1

/-- Witness of associativity / constant-folding incompleteness in `generic_const_exprs`:
`(N + 1) + 2` and `N + 3` fail `synEq`, yet evaluate identically for ALL `ρ : Nat → Nat`. -/
theorem gce_syntactic_incompleteness_assoc_fold (interpAnon : Nat → List Nat → Nat) :
    let lhs : AbstractConst := .add (.add (.param 0) (.lit 1)) (.lit 2)
    let rhs : AbstractConst := .add (.param 0) (.lit 3)
    synEq lhs rhs = false ∧
    (∀ ρ : Nat → Nat, evalAbstract interpAnon ρ lhs = evalAbstract interpAnon ρ rhs) := by
  refine ⟨rfl, ?_⟩
  intro ρ
  exact Nat.add_assoc (ρ 0) 1 2

/-- Subtree satisfaction witness (`const_evaluatable.rs:165-167`):
`where [(); (N + 1) * 2]:` satisfies `[u8; N + 1]` in `ParamEnv`, whereas `[u8; 1 + N]` fails! -/
theorem gce_subtree_satisfaction_witness :
    let bound : AbstractConst := .mul (.add (.param 0) (.lit 1)) (.lit 2)
    let nPlus1 : AbstractConst := .add (.param 0) (.lit 1)
    let onePlusN : AbstractConst := .add (.lit 1) (.param 0)
    satisfiedFromParamEnv [bound] nPlus1 = true ∧
    satisfiedFromParamEnv [bound] onePlusN = false := by
  refine ⟨rfl, rfl⟩

/-- Mutual incompatibility of `generic_const_exprs` and `gca_const_items` across all solver modes,
plus `v1_98_nightly` hard error vs `v1_102_plus_head` auto-revert to `nextCoherence`. -/
theorem gce_solver_compatibility_theorems :
    (∀ rel mode, resolveSolver rel true true mode = .rejectedIncompatible) ∧
    resolveSolver .v1_98_nightly true false .nextGlobally = .rejectedIncompatible ∧
    resolveSolver .v1_102_plus_head true false .nextGlobally = .active .nextCoherence true ∧
    resolveSolver .v1_102_plus_head false true .nextGlobally = .active .nextGlobally false := by
  refine ⟨?_, rfl, rfl, rfl⟩
  intro rel mode
  cases rel <;> cases mode <;> rfl

/-! ## Section 5: `ConstParamTy` & `StructuralPartialEq` Gate, Bisimulation, & Counterexamples -/

/-- Feature flags gating `ConstParamTy` (`coherence/builtin.rs:183-205`, `traits/misc.rs:92-171`). -/
structure FeatureFlags where
  minAdtConstParams : Bool
  adtConstParams : Bool
  unsizedConstParams : Bool
  constParamTyUnchecked : Bool

/-- Per-ADT metadata inspected by `visit_implementation_of_const_param_ty`. -/
structure AdtMeta where
  isUnion : Bool
  isNonExhaustive : Bool
  hasPrivateField : Bool
  hasStructuralPartialEq : Bool
  hasEq : Bool

inductive AdmitError where
  | notAnAdtOrBuiltinAllowed
  | nonExhaustive
  | fieldVisMismatch
  | unsizedConstParamsRequired
  | missingStructuralPartialEq
  | missingEq
  | invalidInnerTy

noncomputable def adtHeaderCheck (flags : FeatureFlags) (meta_ : AdtMeta) : Option AdmitError :=
  if meta_.isUnion then
    some .notAnAdtOrBuiltinAllowed
  else if bAnd meta_.hasPrivateField (bNot flags.adtConstParams) then
    some .fieldVisMismatch
  else if bAnd meta_.isNonExhaustive (bNot flags.adtConstParams) then
    some .nonExhaustive
  else if bNot meta_.hasStructuralPartialEq then
    some .missingStructuralPartialEq
  else if bNot meta_.hasEq then
    some .missingEq
  else
    none

/- Models `visit_implementation_of_const_param_ty` + `type_allowed_to_implement_const_param_ty`
(`coherence/builtin.rs:170-245`, `traits/misc.rs:92-201`) when `constParamTyUnchecked = false`. -/
mutual
  noncomputable def admitConstParamTy (flags : FeatureFlags) (adtEnv : Nat → AdtMeta) :
      ConstTy → Option AdmitError
    | .bool | .char | .uint _ | .int _ | .unit => none
    | .float32 | .fnPtr | .unionTy _ _ => some .notAnAdtOrBuiltinAllowed
    | .ref true _ => some .notAnAdtOrBuiltinAllowed
    | .ref false inner =>
      if flags.unsizedConstParams then
        match admitConstParamTy flags adtEnv inner with
        | none => none
        | some _ => some .invalidInnerTy
      else
        some .unsizedConstParamsRequired
    | .slice elem =>
      if flags.unsizedConstParams then
        match admitConstParamTy flags adtEnv elem with
        | none => none
        | some _ => some .invalidInnerTy
      else
        some .unsizedConstParamsRequired
    | .str =>
      if flags.unsizedConstParams then none else some .unsizedConstParamsRequired
    | .array elem _ =>
      match admitConstParamTy flags adtEnv elem with
      | none => none
      | some _ => some .invalidInnerTy
    | .tuple elems =>
      match admitConstParamTyList flags adtEnv elems with
      | none => none
      | some _ => some .invalidInnerTy
    | .structTy sid fields =>
      if bOr flags.minAdtConstParams flags.adtConstParams then
        match adtHeaderCheck flags (adtEnv sid) with
        | some e => some e
        | none => admitConstParamTyList flags adtEnv fields
      else
        some .notAnAdtOrBuiltinAllowed
    | .enumTy eid variants =>
      if bOr flags.minAdtConstParams flags.adtConstParams then
        match adtHeaderCheck flags (adtEnv eid) with
        | some e => some e
        | none => admitConstParamTyVariants flags adtEnv variants
      else
        some .notAnAdtOrBuiltinAllowed

  noncomputable def admitConstParamTyList (flags : FeatureFlags) (adtEnv : Nat → AdtMeta) :
      List ConstTy → Option AdmitError
    | [] => none
    | t :: ts =>
      match admitConstParamTy flags adtEnv t with
      | some e => some e
      | none => admitConstParamTyList flags adtEnv ts

  noncomputable def admitConstParamTyVariants (flags : FeatureFlags) (adtEnv : Nat → AdtMeta) :
      List (List ConstTy) → Option AdmitError
    | [] => none
    | fs :: rest =>
      match admitConstParamTyList flags adtEnv fs with
      | some e => some e
      | none => admitConstParamTyVariants flags adtEnv rest
end

/- Structural equality semantics of `#[derive(PartialEq)]` (`StructuralPartialEq`) over
well-typed `CtfeMemVal` values: compares fields/elements structurally while ignoring
CTFE `allocId` and `padBytes`. -/
mutual
  noncomputable def structuralEq : ConstTy → CtfeMemVal → CtfeMemVal → Option Bool
    | .bool, .scalar a, .scalar b =>
      if bAnd (scalarInRange .bool a) (scalarInRange .bool b) then some (natEq a b) else none
    | .char, .scalar a, .scalar b =>
      if bAnd (scalarInRange .char a) (scalarInRange .char b) then some (natEq a b) else none
    | .uint w, .scalar a, .scalar b =>
      if bAnd (scalarInRange (.uint w) a) (scalarInRange (.uint w) b) then some (natEq a b) else none
    | .int w, .scalar a, .scalar b =>
      if bAnd (scalarInRange (.int w) a) (scalarInRange (.int w) b) then some (natEq a b) else none
    | .unit, .unitVal, .unitVal => some true
    | .array elem len, .arrayVal xs, .arrayVal ys =>
      if bAnd (natEq (listLen xs) len) (natEq (listLen ys) len) then
        mapOptBool (fun x y => structuralEq elem x y) xs ys
      else
        none
    | .slice elem, .sliceVal xs, .sliceVal ys => mapOptBool (fun x y => structuralEq elem x y) xs ys
    | .str, .strVal bs₁, .strVal bs₂ =>
      if bAnd (bytesValid bs₁) (bytesValid bs₂) then some (natListBeq bs₁ bs₂) else none
    | .ref false inner, .refAlloc _ t₁, .refAlloc _ t₂ => structuralEq inner t₁ t₂
    | .structTy _ fieldTys, .structVal _ xs, .structVal _ ys =>
      structuralEqHeterog fieldTys xs ys
    | .tuple elemTys, .tupleVal _ xs, .tupleVal _ ys =>
      structuralEqHeterog elemTys xs ys
    | .enumTy _ variants, .enumVal v₁ _ xs, .enumVal v₂ _ ys =>
      if natEq v₁ v₂ then
        structuralEqVariants variants v₁ xs ys
      else
        match constToValTreeVariants variants v₁ xs, constToValTreeVariants variants v₂ ys with
        | some _, some _ => some false
        | _, _ => none
    | _, _, _ => none

  noncomputable def structuralEqHeterog :
      List ConstTy → List CtfeMemVal → List CtfeMemVal → Option Bool
    | [], [], [] => some true
    | t :: ts, x :: xs, y :: ys =>
      match structuralEq t x y, structuralEqHeterog ts xs ys with
      | some b₁, some b₂ => some (bAnd b₁ b₂)
      | _, _ => none
    | _, _, _ => none

  noncomputable def structuralEqVariants :
      List (List ConstTy) → Nat → List CtfeMemVal → List CtfeMemVal → Option Bool
    | [], _, _, _ => none
    | ts :: _, 0, xs, ys => structuralEqHeterog ts xs ys
    | _ :: rest, v + 1, xs, ys => structuralEqVariants rest v xs ys
end

noncomputable def structuralEqHomog (elem : ConstTy) :
    List CtfeMemVal → List CtfeMemVal → Option Bool :=
  mapOptBool (structuralEq elem)

theorem structuralEqVariants_eq_getAt (variants : List (List ConstTy)) (v : Nat)
    (xs ys : List CtfeMemVal) :
    structuralEqVariants variants v xs ys =
    match getAt variants v with
    | some ts => structuralEqHeterog ts xs ys
    | none => none := by
  induction variants generalizing v with
  | nil => cases v <;> rfl
  | cons _ tl ih =>
    cases v with
    | zero => rfl
    | succ k => exact ih k

/-- Slice equality handles unequal-length slices cleanly as `some false` when both slices
are well-typed under `constToValTreeHomog`. -/
noncomputable def sliceStructuralEq (elem : ConstTy) (xs ys : List CtfeMemVal) : Option Bool :=
  match constToValTreeHomog elem xs, constToValTreeHomog elem ys with
  | some vs₁, some vs₂ => some (valTreeListEq vs₁ vs₂)
  | _, _ => none

/-- Well-typedness predicate linking `CtfeMemVal` to `constToValTree` for admitted types. -/
noncomputable def valTreeWellFormed (ty : ConstTy) (m : CtfeMemVal) : Prop :=
  ∃ vt, constToValTree ty m = some vt

theorem bytesToValTreeList_inj (bs₁ bs₂ : List Nat)
    (h : bytesToValTreeList bs₁ = bytesToValTreeList bs₂) : bs₁ = bs₂ := by
  induction bs₁ generalizing bs₂ with
  | nil =>
    cases bs₂ with
    | nil => rfl
    | cons _ _ => cases h
  | cons a bs₁ ih =>
    cases bs₂ with
    | nil => cases h
    | cons b bs₂ =>
      change ValTree.leaf a :: bytesToValTreeList bs₁ = ValTree.leaf b :: bytesToValTreeList bs₂ at h
      injection h with ha htl
      injection ha with hab
      rw [hab, ih bs₂ htl]

theorem bytesValid_head_tail (b : Nat) (bs : List Nat) (h : bytesValid (b :: bs) = true) :
    natLt b 256 = true ∧ bytesValid bs = true := by
  exact (bAnd_true_iff (natLt b 256) (bytesValid bs)).mp h

/-! ### Pillar 3 Main Soundness Theorem: `StructuralPartialEq` <-> `ValTree` Bisimulation -/

noncomputable def natLe : Nat → Nat → Bool
  | 0, _ => true
  | _ + 1, 0 => false
  | a + 1, b + 1 => natLe a b

theorem natLe_refl (n : Nat) : natLe n n = true := by
  induction n with
  | zero => rfl
  | succ k ih => exact ih

theorem natLe_succ_right {a b : Nat} (h : natLe a b = true) : natLe a (b + 1) = true := by
  induction a generalizing b with
  | zero => rfl
  | succ k ih =>
    cases b with
    | zero => cases h
    | succ m => exact ih h

theorem natLe_trans {a b c : Nat} (h₁ : natLe a b = true) (h₂ : natLe b c = true) :
    natLe a c = true := by
  induction a generalizing b c with
  | zero => rfl
  | succ k ih =>
    cases b with
    | zero => cases h₁
    | succ m =>
      cases c with
      | zero => cases h₂
      | succ n => exact ih h₁ h₂

theorem natLe_add_right (a b : Nat) : natLe a (a + b) = true := by
  induction b with
  | zero => exact natLe_refl a
  | succ k ih => exact natLe_succ_right ih

theorem natLe_add_left (a b : Nat) : natLe b (a + b) = true := by
  induction b with
  | zero => rfl
  | succ k ih => exact ih

mutual
  noncomputable def constTySize : ConstTy → Nat
    | .bool => 1
    | .char => 1
    | .uint _ => 1
    | .int _ => 1
    | .unit => 1
    | .array elem _ => constTySize elem + 1
    | .slice elem => constTySize elem + 1
    | .str => 1
    | .ref _ inner => constTySize inner + 1
    | .structTy _ fields => constTyListSize fields + 1
    | .enumTy _ variants => constTyVariantsSize variants + 1
    | .tuple elems => constTyListSize elems + 1
    | .unionTy _ _ => 1
    | .float32 => 1
    | .fnPtr => 1

  noncomputable def constTyListSize : List ConstTy → Nat
    | [] => 0
    | t :: ts => constTySize t + constTyListSize ts + 1

  noncomputable def constTyVariantsSize : List (List ConstTy) → Nat
    | [] => 0
    | fs :: rest => constTyListSize fs + constTyVariantsSize rest + 1
end

theorem constTySize_pos (ty : ConstTy) : ∃ k, constTySize ty = k + 1 := by
  cases ty <;> exact ⟨_, rfl⟩

theorem constTyListSize_head_le (t : ConstTy) (ts : List ConstTy) :
    natLe (constTySize t) (constTyListSize (t :: ts)) = true := by
  change natLe (constTySize t) ((constTySize t + constTyListSize ts) + 1) = true
  exact natLe_succ_right (natLe_add_right (constTySize t) (constTyListSize ts))

theorem constTyListSize_tail_le (t : ConstTy) (ts : List ConstTy) :
    natLe (constTyListSize ts) (constTyListSize (t :: ts)) = true := by
  change natLe (constTyListSize ts) ((constTySize t + constTyListSize ts) + 1) = true
  exact natLe_succ_right (natLe_add_left (constTySize t) (constTyListSize ts))

theorem constTyVariantsSize_getAt (variants : List (List ConstTy)) (v : Nat)
    (ts : List ConstTy) (hg : getAt variants v = some ts) :
    natLe (constTyListSize ts) (constTyVariantsSize variants) = true := by
  induction variants generalizing v with
  | nil => cases hg
  | cons hd tl ih =>
    cases v with
    | zero =>
      cases hg
      change natLe (constTyListSize ts) ((constTyListSize ts + constTyVariantsSize tl) + 1) = true
      exact natLe_succ_right (natLe_add_right (constTyListSize ts) (constTyVariantsSize tl))
    | succ k =>
      have htl := ih k hg
      change natLe (constTyListSize ts) ((constTyListSize hd + constTyVariantsSize tl) + 1) = true
      have hsub : natLe (constTyVariantsSize tl) ((constTyListSize hd + constTyVariantsSize tl) + 1) = true :=
        natLe_succ_right (natLe_add_left (constTyListSize hd) (constTyVariantsSize tl))
      exact natLe_trans htl hsub

theorem admitConstParamTyList_head_tail (flags : FeatureFlags) (adtEnv : Nat → AdtMeta)
    (t : ConstTy) (ts : List ConstTy)
    (h : admitConstParamTyList flags adtEnv (t :: ts) = none) :
    admitConstParamTy flags adtEnv t = none ∧ admitConstParamTyList flags adtEnv ts = none := by
  change (match admitConstParamTy flags adtEnv t with | some e => some e | none => admitConstParamTyList flags adtEnv ts) = none at h
  cases ht : admitConstParamTy flags adtEnv t with
  | some e => rw [ht] at h; cases h
  | none =>
    rw [ht] at h
    exact ⟨rfl, h⟩

theorem admitConstParamTyVariants_getAt (flags : FeatureFlags) (adtEnv : Nat → AdtMeta)
    (variants : List (List ConstTy)) (v : Nat) (ts : List ConstTy)
    (h : admitConstParamTyVariants flags adtEnv variants = none)
    (hg : getAt variants v = some ts) :
    admitConstParamTyList flags adtEnv ts = none := by
  induction variants generalizing v with
  | nil => cases hg
  | cons fs rest ih =>
    change (match admitConstParamTyList flags adtEnv fs with | some e => some e | none => admitConstParamTyVariants flags adtEnv rest) = none at h
    cases hfs : admitConstParamTyList flags adtEnv fs with
    | some _ => rw [hfs] at h; cases h
    | none =>
      rw [hfs] at h
      cases v with
      | zero => cases hg; exact hfs
      | succ k => exact ih k h hg

/-- Helper characterizing `structuralEqHomog` on homogeneous arrays/slices of equal length. -/
theorem structuralEqHomog_eq_valTreeListEq (elem : ConstTy)
    (ihElem : ∀ x y, valTreeWellFormed elem x → valTreeWellFormed elem y →
      (structuralEq elem x y = some true ↔
       ∃ vt, constToValTree elem x = some vt ∧ constToValTree elem y = some vt))
    (xs ys : List CtfeMemVal)
    (hxs : ∃ vs₁, constToValTreeHomog elem xs = some vs₁)
    (hys : ∃ vs₂, constToValTreeHomog elem ys = some vs₂) :
    structuralEqHomog elem xs ys = some true ↔
    (∃ vs, constToValTreeHomog elem xs = some vs ∧ constToValTreeHomog elem ys = some vs) := by
  unfold structuralEqHomog constToValTreeHomog at *
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil =>
      constructor
      · intro _; exact ⟨[], rfl, rfl⟩
      · intro _; rfl
    | cons y ys =>
      constructor
      · intro h; cases h
      · intro h
        rcases h with ⟨vs, h1, h2⟩
        rw [mapOpt_nil] at h1
        injection h1 with hvs
        rw [← hvs] at h2
        rw [mapOpt_cons] at h2
        cases h2' : constToValTree elem y with
        | none => rw [h2'] at h2; cases h2
        | some _ =>
          cases h2'' : mapOpt (constToValTree elem) ys <;> rw [h2', h2''] at h2 <;> cases h2
  | cons x xs ih =>
    cases ys with
    | nil =>
      constructor
      · intro h; cases h
      · intro h
        rcases h with ⟨vs, h1, h2⟩
        rw [mapOpt_nil] at h2
        injection h2 with hvs
        rw [← hvs, mapOpt_cons] at h1
        cases h1' : constToValTree elem x with
        | none => rw [h1'] at h1; cases h1
        | some _ =>
          cases h1'' : mapOpt (constToValTree elem) xs <;> rw [h1', h1''] at h1 <;> cases h1
    | cons y ys =>
      rcases hxs with ⟨vs₁, hxs'⟩
      rcases hys with ⟨vs₂, hys'⟩
      rw [mapOpt_cons] at hxs' hys'
      cases hx : constToValTree elem x with
      | none => rw [hx] at hxs'; cases hxs'
      | some vx =>
        cases hxt : mapOpt (constToValTree elem) xs with
        | none => rw [hx, hxt] at hxs'; cases hxs'
        | some vxs =>
          cases hy : constToValTree elem y with
          | none => rw [hy] at hys'; cases hys'
          | some vy =>
            cases hyt : mapOpt (constToValTree elem) ys with
            | none => rw [hy, hyt] at hys'; cases hys'
            | some vys =>
              have hrest := ih ys ⟨vxs, hxt⟩ ⟨vys, hyt⟩
              have ihxy := ihElem x y ⟨vx, hx⟩ ⟨vy, hy⟩
              constructor
              · intro h
                rw [mapOptBool_cons] at h
                cases hxy : structuralEq elem x y with
                | none => rw [hxy] at h; cases h
                | some b₁ =>
                  cases hrs : mapOptBool (structuralEq elem) xs ys with
                  | none => rw [hxy, hrs] at h; cases h
                  | some b₂ =>
                    rw [hxy, hrs] at h
                    injection h with hband
                    have hb := (bAnd_true_iff b₁ b₂).mp hband
                    rw [hb.1] at hxy
                    rw [hb.2] at hrs
                    have hhead := ihxy.mp hxy
                    have htail := hrest.mp hrs
                    rcases hhead with ⟨vh, hh1, hh2⟩
                    rcases htail with ⟨vt, ht1, ht2⟩
                    exact ⟨vh :: vt, by rw [mapOpt_cons, hh1, ht1],
                                     by rw [mapOpt_cons, hh2, ht2]⟩
              · intro h
                rcases h with ⟨vs, h1, h2⟩
                rw [mapOpt_cons, hx, hxt] at h1
                rw [mapOpt_cons, hy, hyt] at h2
                injection h1 with hv1
                injection h2 with hv2
                rw [← hv1] at hv2
                injection hv2 with hvh hvt
                have hh := ihxy.mpr ⟨vx, hx, by rw [hy, hvh]⟩
                have ht := hrest.mpr ⟨vxs, hxt, by rw [hyt, hvt]⟩
                rw [mapOptBool_cons, hh, ht]
                rfl

/-- Helper characterizing `structuralEqHeterog` over tuples, structs, and enum variants. -/
theorem structuralEqHeterog_eq_valTreeListEq (flags : FeatureFlags) (adtEnv : Nat → AdtMeta)
    (bound : Nat)
    (ihField : ∀ t, natLe (constTySize t) bound = true →
      admitConstParamTy flags adtEnv t = none →
      ∀ x y, valTreeWellFormed t x → valTreeWellFormed t y →
      (structuralEq t x y = some true ↔
       ∃ vt, constToValTree t x = some vt ∧ constToValTree t y = some vt))
    (ts : List ConstTy)
    (hle : natLe (constTyListSize ts) bound = true)
    (hadm : admitConstParamTyList flags adtEnv ts = none)
    (xs ys : List CtfeMemVal)
    (hxs : ∃ vs₁, constToValTreeHeterog ts xs = some vs₁)
    (hys : ∃ vs₂, constToValTreeHeterog ts ys = some vs₂) :
    structuralEqHeterog ts xs ys = some true ↔
    (∃ vs, constToValTreeHeterog ts xs = some vs ∧ constToValTreeHeterog ts ys = some vs) := by
  induction ts generalizing xs ys with
  | nil =>
    cases xs with
    | nil =>
      cases ys with
      | nil =>
        constructor
        · intro _; exact ⟨[], rfl, rfl⟩
        · intro _; rfl
      | cons _ _ =>
        rcases hys with ⟨_, hy'⟩; cases hy'
    | cons _ _ =>
      rcases hxs with ⟨_, hx'⟩; cases hx'
  | cons t ts ih =>
    cases xs with
    | nil => rcases hxs with ⟨_, hx'⟩; cases hx'
    | cons x xs =>
      cases ys with
      | nil => rcases hys with ⟨_, hy'⟩; cases hy'
      | cons y ys =>
        have htLe : natLe (constTySize t) bound = true :=
          natLe_trans (constTyListSize_head_le t ts) hle
        have htsLe : natLe (constTyListSize ts) bound = true :=
          natLe_trans (constTyListSize_tail_le t ts) hle
        have hadmPair := admitConstParamTyList_head_tail flags adtEnv t ts hadm
        rcases hxs with ⟨vs₁, hxs'⟩
        rcases hys with ⟨vs₂, hys'⟩
        change (match constToValTree t x, constToValTreeHeterog ts xs with | some v, some vs => some (v :: vs) | _, _ => none) = some vs₁ at hxs'
        change (match constToValTree t y, constToValTreeHeterog ts ys with | some v, some vs => some (v :: vs) | _, _ => none) = some vs₂ at hys'
        cases hx : constToValTree t x with
        | none => rw [hx] at hxs'; cases hxs'
        | some vx =>
          cases hxt : constToValTreeHeterog ts xs with
          | none => rw [hx, hxt] at hxs'; cases hxs'
          | some vxs =>
            cases hy : constToValTree t y with
            | none => rw [hy] at hys'; cases hys'
            | some vy =>
              cases hyt : constToValTreeHeterog ts ys with
              | none => rw [hy, hyt] at hys'; cases hys'
              | some vys =>
                have hrest := ih htsLe hadmPair.2 xs ys ⟨vxs, hxt⟩ ⟨vys, hyt⟩
                have ihxy := ihField t htLe hadmPair.1 x y ⟨vx, hx⟩ ⟨vy, hy⟩
                constructor
                · intro h
                  change (match structuralEq t x y, structuralEqHeterog ts xs ys with | some b₁, some b₂ => some (bAnd b₁ b₂) | _, _ => none) = some true at h
                  cases hxy : structuralEq t x y with
                  | none => rw [hxy] at h; cases h
                  | some b₁ =>
                    cases hrs : structuralEqHeterog ts xs ys with
                    | none => rw [hxy, hrs] at h; cases h
                    | some b₂ =>
                      rw [hxy, hrs] at h
                      injection h with hband
                      have hb := (bAnd_true_iff b₁ b₂).mp hband
                      rw [hb.1] at hxy
                      rw [hb.2] at hrs
                      have hhead := ihxy.mp hxy
                      have htail := hrest.mp hrs
                      rcases hhead with ⟨vh, hh1, hh2⟩
                      rcases htail with ⟨vt, ht1, ht2⟩
                      exact ⟨vh :: vt, by change (match constToValTree t x, constToValTreeHeterog ts xs with | some v, some vs => some (v :: vs) | _, _ => none) = some (vh :: vt); rw [hh1, ht1],
                                       by change (match constToValTree t y, constToValTreeHeterog ts ys with | some v, some vs => some (v :: vs) | _, _ => none) = some (vh :: vt); rw [hh2, ht2]⟩
                · intro h
                  rcases h with ⟨vs, h1, h2⟩
                  change (match constToValTree t x, constToValTreeHeterog ts xs with | some v, some vs => some (v :: vs) | _, _ => none) = some vs at h1
                  change (match constToValTree t y, constToValTreeHeterog ts ys with | some v, some vs => some (v :: vs) | _, _ => none) = some vs at h2
                  rw [hx, hxt] at h1
                  rw [hy, hyt] at h2
                  injection h1 with hv1
                  injection h2 with hv2
                  rw [← hv1] at hv2
                  injection hv2 with hvh hvt
                  have hh := ihxy.mpr ⟨vx, hx, by rw [hy, hvh]⟩
                  have ht := hrest.mpr ⟨vxs, hxt, by rw [hyt, hvt]⟩
                  change (match structuralEq t x y, structuralEqHeterog ts xs ys with | some b₁, some b₂ => some (bAnd b₁ b₂) | _, _ => none) = some true
                  rw [hh, ht]
                  rfl

/-- Main Pillar 3 Bisimulation Auxiliary Lemma (Well-Founded Induction on `constTySize`):
For every type `ty` admitted by `ConstParamTy` (`admitConstParamTy flags adtEnv ty = none`)
and all well-formed CTFE values `m₁, m₂` of `ty`, runtime structural `PartialEq` holds **iff**
`m₁` and `m₂` canonicalize to the **exact same `ValTree`**. -/
theorem structuralEq_iff_valTree_eq_aux (flags : FeatureFlags) (adtEnv : Nat → AdtMeta) :
    (sz : Nat) →
    ∀ (ty : ConstTy),
    natLe (constTySize ty) sz = true →
    admitConstParamTy flags adtEnv ty = none →
    ∀ m₁ m₂ : CtfeMemVal,
    valTreeWellFormed ty m₁ →
    valTreeWellFormed ty m₂ →
    (structuralEq ty m₁ m₂ = some true ↔
     ∃ vt, constToValTree ty m₁ = some vt ∧ constToValTree ty m₂ = some vt)
  | 0, ty, hsz, _, _, _, _, _ => by
    rcases constTySize_pos ty with ⟨k, hk⟩
    rw [hk] at hsz
    cases hsz
  | sz + 1, .bool, _, _, m₁, m₂, hm₁, hm₂ => by
      rcases hm₁ with ⟨vt₁, h₁⟩; rcases hm₂ with ⟨vt₂, h₂⟩
      cases m₁ with
      | scalar a =>
        cases m₂ with
        | scalar b =>
          change (if scalarInRange .bool a then some (ValTree.leaf a) else none) = some vt₁ at h₁
          change (if scalarInRange .bool b then some (ValTree.leaf b) else none) = some vt₂ at h₂
          cases ha : scalarInRange .bool a <;> rw [ha] at h₁
          · cases h₁
          · cases hb : scalarInRange .bool b <;> rw [hb] at h₂
            · cases h₂
            · injection h₁ with hv₁; injection h₂ with hv₂
              constructor
              · intro h
                change (if bAnd (scalarInRange .bool a) (scalarInRange .bool b) then some (natEq a b) else none) = some true at h
                rw [ha, hb] at h; change some (natEq a b) = some true at h
                injection h with heq
                have hab := (natEq_true_iff a b).mp heq
                exact ⟨ValTree.leaf b,
                  by change (if scalarInRange .bool a then some (ValTree.leaf a) else none) = some (ValTree.leaf b); rw [ha, hab]; rfl,
                  by change (if scalarInRange .bool b then some (ValTree.leaf b) else none) = some (ValTree.leaf b); rw [hb]; rfl⟩
              · intro h
                rcases h with ⟨vt, g₁, g₂⟩
                change (if scalarInRange .bool a then some (.leaf a) else none) = some vt at g₁
                change (if scalarInRange .bool b then some (.leaf b) else none) = some vt at g₂
                rw [ha] at g₁; rw [hb] at g₂
                injection g₁ with e₁; injection g₂ with e₂
                rw [← e₂] at e₁; injection e₁ with hab
                change (if bAnd (scalarInRange .bool a) (scalarInRange .bool b) then some (natEq a b) else none) = some true
                rw [ha, hb]
                have hne : natEq a b = true := (natEq_true_iff a b).mpr hab
                change some (natEq a b) = some true; rw [hne]
        | _ => cases h₂
      | _ => cases h₁
  | sz + 1, .char, _, _, m₁, m₂, hm₁, hm₂ => by
      rcases hm₁ with ⟨vt₁, h₁⟩; rcases hm₂ with ⟨vt₂, h₂⟩
      cases m₁ with
      | scalar a =>
        cases m₂ with
        | scalar b =>
          change (if scalarInRange .char a then some (.leaf a) else none) = some vt₁ at h₁
          change (if scalarInRange .char b then some (.leaf b) else none) = some vt₂ at h₂
          cases ha : scalarInRange .char a <;> rw [ha] at h₁
          · cases h₁
          · cases hb : scalarInRange .char b <;> rw [hb] at h₂
            · cases h₂
            · injection h₁ with hv₁; injection h₂ with hv₂
              constructor
              · intro h
                change (if bAnd (scalarInRange .char a) (scalarInRange .char b) then some (natEq a b) else none) = some true at h
                rw [ha, hb] at h; change some (natEq a b) = some true at h
                injection h with heq
                have hab := (natEq_true_iff a b).mp heq
                exact ⟨ValTree.leaf b,
                  by change (if scalarInRange .char a then some (ValTree.leaf a) else none) = some (ValTree.leaf b); rw [ha, hab]; rfl,
                  by change (if scalarInRange .char b then some (ValTree.leaf b) else none) = some (ValTree.leaf b); rw [hb]; rfl⟩
              · intro h
                rcases h with ⟨vt, g₁, g₂⟩
                change (if scalarInRange .char a then some (.leaf a) else none) = some vt at g₁
                change (if scalarInRange .char b then some (.leaf b) else none) = some vt at g₂
                rw [ha] at g₁; rw [hb] at g₂
                injection g₁ with e₁; injection g₂ with e₂
                rw [← e₂] at e₁; injection e₁ with hab
                change (if bAnd (scalarInRange .char a) (scalarInRange .char b) then some (natEq a b) else none) = some true
                rw [ha, hb]
                have hne : natEq a b = true := (natEq_true_iff a b).mpr hab
                change some (natEq a b) = some true; rw [hne]
        | _ => cases h₂
      | _ => cases h₁
  | sz + 1, .uint w, _, _, m₁, m₂, hm₁, hm₂ => by
      rcases hm₁ with ⟨vt₁, h₁⟩; rcases hm₂ with ⟨vt₂, h₂⟩
      cases m₁ with
      | scalar a =>
        cases m₂ with
        | scalar b =>
          change (if scalarInRange (.uint w) a then some (.leaf a) else none) = some vt₁ at h₁
          change (if scalarInRange (.uint w) b then some (.leaf b) else none) = some vt₂ at h₂
          cases ha : scalarInRange (.uint w) a <;> rw [ha] at h₁
          · cases h₁
          · cases hb : scalarInRange (.uint w) b <;> rw [hb] at h₂
            · cases h₂
            · injection h₁ with hv₁; injection h₂ with hv₂
              constructor
              · intro h
                change (if bAnd (scalarInRange (.uint w) a) (scalarInRange (.uint w) b) then some (natEq a b) else none) = some true at h
                rw [ha, hb] at h; change some (natEq a b) = some true at h
                injection h with heq
                have hab := (natEq_true_iff a b).mp heq
                exact ⟨ValTree.leaf b,
                  by change (if scalarInRange (.uint w) a then some (ValTree.leaf a) else none) = some (ValTree.leaf b); rw [ha, hab]; rfl,
                  by change (if scalarInRange (.uint w) b then some (ValTree.leaf b) else none) = some (ValTree.leaf b); rw [hb]; rfl⟩
              · intro h
                rcases h with ⟨vt, g₁, g₂⟩
                change (if scalarInRange (.uint w) a then some (.leaf a) else none) = some vt at g₁
                change (if scalarInRange (.uint w) b then some (.leaf b) else none) = some vt at g₂
                rw [ha] at g₁; rw [hb] at g₂
                injection g₁ with e₁; injection g₂ with e₂
                rw [← e₂] at e₁; injection e₁ with hab
                change (if bAnd (scalarInRange (.uint w) a) (scalarInRange (.uint w) b) then some (natEq a b) else none) = some true
                rw [ha, hb]
                have hne : natEq a b = true := (natEq_true_iff a b).mpr hab
                change some (natEq a b) = some true; rw [hne]
        | _ => cases h₂
      | _ => cases h₁
  | sz + 1, .int w, _, _, m₁, m₂, hm₁, hm₂ => by
      rcases hm₁ with ⟨vt₁, h₁⟩; rcases hm₂ with ⟨vt₂, h₂⟩
      cases m₁ with
      | scalar a =>
        cases m₂ with
        | scalar b =>
          change (if scalarInRange (.int w) a then some (.leaf a) else none) = some vt₁ at h₁
          change (if scalarInRange (.int w) b then some (.leaf b) else none) = some vt₂ at h₂
          cases ha : scalarInRange (.int w) a <;> rw [ha] at h₁
          · cases h₁
          · cases hb : scalarInRange (.int w) b <;> rw [hb] at h₂
            · cases h₂
            · injection h₁ with hv₁; injection h₂ with hv₂
              constructor
              · intro h
                change (if bAnd (scalarInRange (.int w) a) (scalarInRange (.int w) b) then some (natEq a b) else none) = some true at h
                rw [ha, hb] at h; change some (natEq a b) = some true at h
                injection h with heq
                have hab := (natEq_true_iff a b).mp heq
                exact ⟨ValTree.leaf b,
                  by change (if scalarInRange (.int w) a then some (ValTree.leaf a) else none) = some (ValTree.leaf b); rw [ha, hab]; rfl,
                  by change (if scalarInRange (.int w) b then some (ValTree.leaf b) else none) = some (ValTree.leaf b); rw [hb]; rfl⟩
              · intro h
                rcases h with ⟨vt, g₁, g₂⟩
                change (if scalarInRange (.int w) a then some (.leaf a) else none) = some vt at g₁
                change (if scalarInRange (.int w) b then some (.leaf b) else none) = some vt at g₂
                rw [ha] at g₁; rw [hb] at g₂
                injection g₁ with e₁; injection g₂ with e₂
                rw [← e₂] at e₁; injection e₁ with hab
                change (if bAnd (scalarInRange (.int w) a) (scalarInRange (.int w) b) then some (natEq a b) else none) = some true
                rw [ha, hb]
                have hne : natEq a b = true := (natEq_true_iff a b).mpr hab
                change some (natEq a b) = some true; rw [hne]
        | _ => cases h₂
      | _ => cases h₁
  | sz + 1, .unit, _, _, m₁, m₂, hm₁, hm₂ => by
      rcases hm₁ with ⟨vt₁, h₁⟩; rcases hm₂ with ⟨vt₂, h₂⟩
      cases m₁ with
      | unitVal =>
        cases m₂ with
        | unitVal =>
          constructor
          · intro _; exact ⟨.branch [], rfl, rfl⟩
          · intro _; rfl
        | _ => cases h₂
      | _ => cases h₁
  | sz + 1, .str, _, _, m₁, m₂, hm₁, hm₂ => by
      rcases hm₁ with ⟨vt₁, h₁⟩; rcases hm₂ with ⟨vt₂, h₂⟩
      cases m₁ with
      | strVal bs₁ =>
        cases m₂ with
        | strVal bs₂ =>
          change (if bytesValid bs₁ then some (ValTree.branch (bytesToValTreeList bs₁)) else none) = some vt₁ at h₁
          change (if bytesValid bs₂ then some (ValTree.branch (bytesToValTreeList bs₂)) else none) = some vt₂ at h₂
          cases hb₁ : bytesValid bs₁ <;> rw [hb₁] at h₁
          · cases h₁
          · cases hb₂ : bytesValid bs₂ <;> rw [hb₂] at h₂
            · cases h₂
            · injection h₁ with hv₁; injection h₂ with hv₂
              constructor
              · intro h
                change (if bAnd (bytesValid bs₁) (bytesValid bs₂) then some (natListBeq bs₁ bs₂) else none) = some true at h
                rw [hb₁, hb₂] at h; change some (natListBeq bs₁ bs₂) = some true at h
                injection h with hbeq
                have hbs : bs₁ = bs₂ := (natListBeq_true_iff bs₁ bs₂).mp hbeq
                exact ⟨ValTree.branch (bytesToValTreeList bs₂),
                  by change (if bytesValid bs₁ then some (ValTree.branch (bytesToValTreeList bs₁)) else none) = some (ValTree.branch (bytesToValTreeList bs₂)); rw [hb₁, hbs]; rfl,
                  by change (if bytesValid bs₂ then some (ValTree.branch (bytesToValTreeList bs₂)) else none) = some (ValTree.branch (bytesToValTreeList bs₂)); rw [hb₂]; rfl⟩
              · intro h
                rcases h with ⟨vt, g₁, g₂⟩
                change (if bytesValid bs₁ then some (.branch (bytesToValTreeList bs₁)) else none) = some vt at g₁
                change (if bytesValid bs₂ then some (.branch (bytesToValTreeList bs₂)) else none) = some vt at g₂
                rw [hb₁] at g₁; rw [hb₂] at g₂
                injection g₁ with e₁; injection g₂ with e₂
                rw [← e₂] at e₁; injection e₁ with hbl
                have hbs := bytesToValTreeList_inj bs₁ bs₂ hbl
                change (if bAnd (bytesValid bs₁) (bytesValid bs₂) then some (natListBeq bs₁ bs₂) else none) = some true
                rw [hb₁, hb₂]
                have heqb := (natListBeq_true_iff bs₁ bs₂).mpr hbs
                change some (natListBeq bs₁ bs₂) = some true; rw [heqb]
        | _ => cases h₂
      | _ => cases h₁
  | _, .float32, _, hadm, _, _, _, _ => by cases hadm
  | _, .fnPtr, _, hadm, _, _, _, _ => by cases hadm
  | _, .unionTy _ _, _, hadm, _, _, _, _ => by cases hadm
  | sz + 1, .ref isMut inner, hsz, hadm, m₁, m₂, hm₁, hm₂ => by
      cases isMut with
      | true => cases hadm
      | false =>
        change (if flags.unsizedConstParams then match admitConstParamTy flags adtEnv inner with | none => none | some _ => some AdmitError.invalidInnerTy else some AdmitError.unsizedConstParamsRequired) = none at hadm
        cases huns : flags.unsizedConstParams with
        | false => rw [huns] at hadm; cases hadm
        | true =>
          rw [huns] at hadm
          cases hadmInner : admitConstParamTy flags adtEnv inner with
          | some _ => rw [hadmInner] at hadm; cases hadm
          | none =>
            rcases hm₁ with ⟨vt₁, h₁⟩; rcases hm₂ with ⟨vt₂, h₂⟩
            cases m₁ with
            | refAlloc _ t₁ =>
              cases m₂ with
              | refAlloc _ t₂ =>
                exact structuralEq_iff_valTree_eq_aux flags adtEnv sz inner hsz hadmInner t₁ t₂ ⟨vt₁, h₁⟩ ⟨vt₂, h₂⟩
              | _ => cases h₂
            | _ => cases h₁
  | sz + 1, .array elem len, hsz, hadm, m₁, m₂, hm₁, hm₂ => by
      change (match admitConstParamTy flags adtEnv elem with | none => none | some _ => some AdmitError.invalidInnerTy) = none at hadm
      cases hadmElem : admitConstParamTy flags adtEnv elem with
      | some _ => rw [hadmElem] at hadm; cases hadm
      | none =>
        rcases hm₁ with ⟨vt₁, h₁⟩; rcases hm₂ with ⟨vt₂, h₂⟩
        cases m₁ with
        | arrayVal xs =>
          cases m₂ with
          | arrayVal ys =>
            change (if natEq (listLen xs) len then match constToValTreeHomog elem xs with | some vs => some (ValTree.branch vs) | none => none else none) = some vt₁ at h₁
            change (if natEq (listLen ys) len then match constToValTreeHomog elem ys with | some vs => some (ValTree.branch vs) | none => none else none) = some vt₂ at h₂
            cases hlx : natEq (listLen xs) len <;> rw [hlx] at h₁
            · cases h₁
            · cases hly : natEq (listLen ys) len <;> rw [hly] at h₂
              · cases h₂
              · cases hx : constToValTreeHomog elem xs <;> rw [hx] at h₁
                · cases h₁
                · cases hy : constToValTreeHomog elem ys <;> rw [hy] at h₂
                  · cases h₂
                  · rename_i vs₁ vs₂
                    have hHomog := structuralEqHomog_eq_valTreeListEq elem
                      (fun x y hx' hy' => structuralEq_iff_valTree_eq_aux flags adtEnv sz elem hsz hadmElem x y hx' hy')
                      xs ys ⟨vs₁, hx⟩ ⟨vs₂, hy⟩
                    constructor
                    · intro heq
                      change (if bAnd (natEq (listLen xs) len) (natEq (listLen ys) len) then structuralEqHomog elem xs ys else none) = some true at heq
                      rw [hlx, hly] at heq
                      have hvs := hHomog.mp heq
                      rcases hvs with ⟨vs, hvs₁, hvs₂⟩
                      exact ⟨ValTree.branch vs,
                        by change (if natEq (listLen xs) len then match constToValTreeHomog elem xs with | some vs' => some (ValTree.branch vs') | none => none else none) = some (ValTree.branch vs); rw [hlx, hvs₁]; rfl,
                        by change (if natEq (listLen ys) len then match constToValTreeHomog elem ys with | some vs' => some (ValTree.branch vs') | none => none else none) = some (ValTree.branch vs); rw [hly, hvs₂]; rfl⟩
                    · intro hvt
                      rcases hvt with ⟨vt, g₁, g₂⟩
                      change (if natEq (listLen xs) len then match constToValTreeHomog elem xs with | some vs' => some (ValTree.branch vs') | none => none else none) = some vt at g₁
                      change (if natEq (listLen ys) len then match constToValTreeHomog elem ys with | some vs' => some (ValTree.branch vs') | none => none else none) = some vt at g₂
                      rw [hlx, hx] at g₁; rw [hly, hy] at g₂
                      injection g₁ with ev₁; injection g₂ with ev₂
                      rw [← ev₁] at ev₂; injection ev₂ with evs
                      have heqHom := hHomog.mpr ⟨vs₁, hx, by rw [hy, evs]⟩
                      change (if bAnd (natEq (listLen xs) len) (natEq (listLen ys) len) then structuralEqHomog elem xs ys else none) = some true
                      rw [hlx, hly]
                      exact heqHom
          | _ => cases h₂
        | _ => cases h₁
  | sz + 1, .slice elem, hsz, hadm, m₁, m₂, hm₁, hm₂ => by
      change (if flags.unsizedConstParams then match admitConstParamTy flags adtEnv elem with | none => none | some _ => some AdmitError.invalidInnerTy else some AdmitError.unsizedConstParamsRequired) = none at hadm
      cases huns : flags.unsizedConstParams with
      | false => rw [huns] at hadm; cases hadm
      | true =>
        rw [huns] at hadm
        cases hadmElem : admitConstParamTy flags adtEnv elem with
        | some _ => rw [hadmElem] at hadm; cases hadm
        | none =>
          rcases hm₁ with ⟨vt₁, h₁⟩; rcases hm₂ with ⟨vt₂, h₂⟩
          cases m₁ with
          | sliceVal xs =>
            cases m₂ with
            | sliceVal ys =>
              change (match constToValTreeHomog elem xs with | some vs => some (ValTree.branch vs) | none => none) = some vt₁ at h₁
              change (match constToValTreeHomog elem ys with | some vs => some (ValTree.branch vs) | none => none) = some vt₂ at h₂
              cases hx : constToValTreeHomog elem xs <;> rw [hx] at h₁
              · cases h₁
              · cases hy : constToValTreeHomog elem ys <;> rw [hy] at h₂
                · cases h₂
                · rename_i vs₁ vs₂
                  have hHomog := structuralEqHomog_eq_valTreeListEq elem
                    (fun x y hx' hy' => structuralEq_iff_valTree_eq_aux flags adtEnv sz elem hsz hadmElem x y hx' hy')
                    xs ys ⟨vs₁, hx⟩ ⟨vs₂, hy⟩
                  constructor
                  · intro heq
                    change structuralEqHomog elem xs ys = some true at heq
                    have hvs := hHomog.mp heq
                    rcases hvs with ⟨vs, hvs₁, hvs₂⟩
                    exact ⟨ValTree.branch vs,
                      by change (match constToValTreeHomog elem xs with | some vs' => some (ValTree.branch vs') | none => none) = some (ValTree.branch vs); rw [hvs₁],
                      by change (match constToValTreeHomog elem ys with | some vs' => some (ValTree.branch vs') | none => none) = some (ValTree.branch vs); rw [hvs₂]⟩
                  · intro hvt
                    rcases hvt with ⟨vt, g₁, g₂⟩
                    change (match constToValTreeHomog elem xs with | some vs' => some (ValTree.branch vs') | none => none) = some vt at g₁
                    change (match constToValTreeHomog elem ys with | some vs' => some (ValTree.branch vs') | none => none) = some vt at g₂
                    rw [hx] at g₁; rw [hy] at g₂
                    injection g₁ with ev₁; injection g₂ with ev₂
                    rw [← ev₁] at ev₂; injection ev₂ with evs
                    change structuralEqHomog elem xs ys = some true
                    exact hHomog.mpr ⟨vs₁, hx, by rw [hy, evs]⟩
            | _ => cases h₂
          | _ => cases h₁
  | sz + 1, .tuple elemTys, hsz, hadm, m₁, m₂, hm₁, hm₂ => by
      change (match admitConstParamTyList flags adtEnv elemTys with | none => none | some _ => some AdmitError.invalidInnerTy) = none at hadm
      cases hadmList : admitConstParamTyList flags adtEnv elemTys with
      | some _ => rw [hadmList] at hadm; cases hadm
      | none =>
        rcases hm₁ with ⟨vt₁, h₁⟩; rcases hm₂ with ⟨vt₂, h₂⟩
        cases m₁ with
        | tupleVal _ xs =>
          cases m₂ with
          | tupleVal _ ys =>
            change (match constToValTreeHeterog elemTys xs with | some vs => some (ValTree.branch vs) | none => none) = some vt₁ at h₁
            change (match constToValTreeHeterog elemTys ys with | some vs => some (ValTree.branch vs) | none => none) = some vt₂ at h₂
            cases hx : constToValTreeHeterog elemTys xs <;> rw [hx] at h₁
            · cases h₁
            · cases hy : constToValTreeHeterog elemTys ys <;> rw [hy] at h₂
              · cases h₂
              · rename_i vs₁ vs₂
                have hHet := structuralEqHeterog_eq_valTreeListEq flags adtEnv sz
                  (structuralEq_iff_valTree_eq_aux flags adtEnv sz)
                  elemTys hsz hadmList xs ys ⟨vs₁, hx⟩ ⟨vs₂, hy⟩
                constructor
                · intro heq
                  have hvs := hHet.mp heq
                  rcases hvs with ⟨vs, hvs₁, hvs₂⟩
                  exact ⟨ValTree.branch vs,
                    by change (match constToValTreeHeterog elemTys xs with | some vs' => some (ValTree.branch vs') | none => none) = some (ValTree.branch vs); rw [hvs₁],
                    by change (match constToValTreeHeterog elemTys ys with | some vs' => some (ValTree.branch vs') | none => none) = some (ValTree.branch vs); rw [hvs₂]⟩
                · intro hvt
                  rcases hvt with ⟨vt, g₁, g₂⟩
                  change (match constToValTreeHeterog elemTys xs with | some vs' => some (ValTree.branch vs') | none => none) = some vt at g₁
                  change (match constToValTreeHeterog elemTys ys with | some vs' => some (ValTree.branch vs') | none => none) = some vt at g₂
                  rw [hx] at g₁; rw [hy] at g₂
                  injection g₁ with ev₁; injection g₂ with ev₂
                  rw [← ev₁] at ev₂; injection ev₂ with evs
                  exact hHet.mpr ⟨vs₁, hx, by rw [hy, evs]⟩
          | _ => cases h₂
        | _ => cases h₁
  | sz + 1, .structTy sid fieldTys, hsz, hadm, m₁, m₂, hm₁, hm₂ => by
      change (if bOr flags.minAdtConstParams flags.adtConstParams then match adtHeaderCheck flags (adtEnv sid) with | some e => some e | none => admitConstParamTyList flags adtEnv fieldTys else some AdmitError.notAnAdtOrBuiltinAllowed) = none at hadm
      cases hfeat : bOr flags.minAdtConstParams flags.adtConstParams with
      | false => rw [hfeat] at hadm; cases hadm
      | true =>
        rw [hfeat] at hadm
        cases hhdr : adtHeaderCheck flags (adtEnv sid) with
        | some _ => rw [hhdr] at hadm; cases hadm
        | none =>
          rw [hhdr] at hadm
          change admitConstParamTyList flags adtEnv fieldTys = none at hadm
          rcases hm₁ with ⟨vt₁, h₁⟩; rcases hm₂ with ⟨vt₂, h₂⟩
          cases m₁ with
          | structVal _ xs =>
            cases m₂ with
            | structVal _ ys =>
              change (match constToValTreeHeterog fieldTys xs with | some vs => some (ValTree.branch vs) | none => none) = some vt₁ at h₁
              change (match constToValTreeHeterog fieldTys ys with | some vs => some (ValTree.branch vs) | none => none) = some vt₂ at h₂
              cases hx : constToValTreeHeterog fieldTys xs <;> rw [hx] at h₁
              · cases h₁
              · cases hy : constToValTreeHeterog fieldTys ys <;> rw [hy] at h₂
                · cases h₂
                · rename_i vs₁ vs₂
                  have hHet := structuralEqHeterog_eq_valTreeListEq flags adtEnv sz
                    (structuralEq_iff_valTree_eq_aux flags adtEnv sz)
                    fieldTys hsz hadm xs ys ⟨vs₁, hx⟩ ⟨vs₂, hy⟩
                  constructor
                  · intro heq
                    have hvs := hHet.mp heq
                    rcases hvs with ⟨vs, hvs₁, hvs₂⟩
                    exact ⟨ValTree.branch vs,
                      by change (match constToValTreeHeterog fieldTys xs with | some vs' => some (ValTree.branch vs') | none => none) = some (ValTree.branch vs); rw [hvs₁],
                      by change (match constToValTreeHeterog fieldTys ys with | some vs' => some (ValTree.branch vs') | none => none) = some (ValTree.branch vs); rw [hvs₂]⟩
                  · intro hvt
                    rcases hvt with ⟨vt, g₁, g₂⟩
                    change (match constToValTreeHeterog fieldTys xs with | some vs' => some (ValTree.branch vs') | none => none) = some vt at g₁
                    change (match constToValTreeHeterog fieldTys ys with | some vs' => some (ValTree.branch vs') | none => none) = some vt at g₂
                    rw [hx] at g₁; rw [hy] at g₂
                    injection g₁ with ev₁; injection g₂ with ev₂
                    rw [← ev₁] at ev₂; injection ev₂ with evs
                    exact hHet.mpr ⟨vs₁, hx, by rw [hy, evs]⟩
            | _ => cases h₂
          | _ => cases h₁
  | sz + 1, .enumTy eid variants, hsz, hadm, m₁, m₂, hm₁, hm₂ => by
      change (if bOr flags.minAdtConstParams flags.adtConstParams then match adtHeaderCheck flags (adtEnv eid) with | some e => some e | none => admitConstParamTyVariants flags adtEnv variants else some AdmitError.notAnAdtOrBuiltinAllowed) = none at hadm
      cases hfeat : bOr flags.minAdtConstParams flags.adtConstParams with
      | false => rw [hfeat] at hadm; cases hadm
      | true =>
        rw [hfeat] at hadm
        cases hhdr : adtHeaderCheck flags (adtEnv eid) with
        | some _ => rw [hhdr] at hadm; cases hadm
        | none =>
          rw [hhdr] at hadm
          change admitConstParamTyVariants flags adtEnv variants = none at hadm
          rcases hm₁ with ⟨vt₁, h₁⟩; rcases hm₂ with ⟨vt₂, h₂⟩
          cases m₁ with
          | enumVal v₁ _ xs =>
            cases m₂ with
            | enumVal v₂ _ ys =>
              change (match constToValTreeVariants variants v₁ xs with | some vs => some (ValTree.branch (ValTree.leaf v₁ :: vs)) | none => none) = some vt₁ at h₁
              change (match constToValTreeVariants variants v₂ ys with | some vs => some (ValTree.branch (ValTree.leaf v₂ :: vs)) | none => none) = some vt₂ at h₂
              rw [constToValTreeVariants_eq_getAt] at h₁ h₂
              cases hg₁ : getAt variants v₁ with
              | none => rw [hg₁] at h₁; cases h₁
              | some ts₁ =>
                rw [hg₁] at h₁
                change (match constToValTreeHeterog ts₁ xs with | some vs => some (ValTree.branch (ValTree.leaf v₁ :: vs)) | none => none) = some vt₁ at h₁
                cases hg₂ : getAt variants v₂ with
                | none => rw [hg₂] at h₂; cases h₂
                | some ts₂ =>
                  rw [hg₂] at h₂
                  change (match constToValTreeHeterog ts₂ ys with | some vs => some (ValTree.branch (ValTree.leaf v₂ :: vs)) | none => none) = some vt₂ at h₂
                  cases hx : constToValTreeHeterog ts₁ xs <;> rw [hx] at h₁
                  · cases h₁
                  · cases hy : constToValTreeHeterog ts₂ ys <;> rw [hy] at h₂
                    · cases h₂
                    · rename_i vs₁ vs₂
                      have hts₁Le : natLe (constTyListSize ts₁) sz = true :=
                        natLe_trans (constTyVariantsSize_getAt variants v₁ ts₁ hg₁) hsz
                      have hadmTs : admitConstParamTyList flags adtEnv ts₁ = none :=
                        admitConstParamTyVariants_getAt flags adtEnv variants v₁ ts₁ hadm hg₁
                      constructor
                      · intro heq
                        change (if natEq v₁ v₂ then structuralEqVariants variants v₁ xs ys else match constToValTreeVariants variants v₁ xs, constToValTreeVariants variants v₂ ys with | some _, some _ => some false | _, _ => none) = some true at heq
                        rw [structuralEqVariants_eq_getAt, hg₁] at heq
                        cases hv : natEq v₁ v₂ with
                        | false =>
                          rw [hv] at heq
                          rw [constToValTreeVariants_eq_getAt, constToValTreeVariants_eq_getAt, hg₁, hg₂] at heq
                          change (match constToValTreeHeterog ts₁ xs, constToValTreeHeterog ts₂ ys with | some _, some _ => some false | _, _ => none) = some true at heq
                          rw [hx, hy] at heq; cases heq
                        | true =>
                          rw [hv] at heq
                          have hveq : v₁ = v₂ := (natEq_true_iff v₁ v₂).mp hv
                          have htsEq : ts₁ = ts₂ := by
                            rw [hveq] at hg₁
                            rw [hg₁] at hg₂
                            injection hg₂
                          have hy' : constToValTreeHeterog ts₁ ys = some vs₂ := by rw [htsEq]; exact hy
                          have hHet := structuralEqHeterog_eq_valTreeListEq flags adtEnv sz
                            (structuralEq_iff_valTree_eq_aux flags adtEnv sz)
                            ts₁ hts₁Le hadmTs xs ys ⟨vs₁, hx⟩ ⟨vs₂, hy'⟩
                          change structuralEqHeterog ts₁ xs ys = some true at heq
                          have hvs := hHet.mp heq
                          cases hvs with
                          | intro vs hvpair =>
                            cases hvpair with
                            | intro hvs₁ hvs₂ =>
                              refine ⟨ValTree.branch (ValTree.leaf v₁ :: vs), ?_, ?_⟩
                              · change (match constToValTreeVariants variants v₁ xs with | some vs' => some (ValTree.branch (ValTree.leaf v₁ :: vs')) | none => none) = some (ValTree.branch (ValTree.leaf v₁ :: vs))
                                rw [constToValTreeVariants_eq_getAt, hg₁]
                                change (match constToValTreeHeterog ts₁ xs with | some vs' => some (ValTree.branch (ValTree.leaf v₁ :: vs')) | none => none) = some (ValTree.branch (ValTree.leaf v₁ :: vs))
                                rw [hvs₁]
                              · change (match constToValTreeVariants variants v₂ ys with | some vs' => some (ValTree.branch (ValTree.leaf v₂ :: vs')) | none => none) = some (ValTree.branch (ValTree.leaf v₁ :: vs))
                                rw [constToValTreeVariants_eq_getAt, ← hveq, hg₁]
                                change (match constToValTreeHeterog ts₁ ys with | some vs' => some (ValTree.branch (ValTree.leaf v₁ :: vs')) | none => none) = some (ValTree.branch (ValTree.leaf v₁ :: vs))
                                rw [hvs₂]
                      · intro hvt
                        cases hvt with
                        | intro vt gpair =>
                          cases gpair with
                          | intro g₁ g₂ =>
                            change (match constToValTreeVariants variants v₁ xs with | some vs' => some (ValTree.branch (ValTree.leaf v₁ :: vs')) | none => none) = some vt at g₁
                            change (match constToValTreeVariants variants v₂ ys with | some vs' => some (ValTree.branch (ValTree.leaf v₂ :: vs')) | none => none) = some vt at g₂
                            rw [constToValTreeVariants_eq_getAt, hg₁] at g₁
                            rw [constToValTreeVariants_eq_getAt, hg₂] at g₂
                            change (match constToValTreeHeterog ts₁ xs with | some vs' => some (ValTree.branch (ValTree.leaf v₁ :: vs')) | none => none) = some vt at g₁
                            change (match constToValTreeHeterog ts₂ ys with | some vs' => some (ValTree.branch (ValTree.leaf v₂ :: vs')) | none => none) = some vt at g₂
                            rw [hx] at g₁; rw [hy] at g₂
                            injection g₁ with ev₁; injection g₂ with ev₂
                            rw [← ev₁] at ev₂; injection ev₂ with ehd
                            injection ehd with eIdx evs
                            injection eIdx with hvEq
                            have hvEq' : v₁ = v₂ := hvEq.symm
                            have htsEq : ts₁ = ts₂ := by
                              rw [hvEq'] at hg₁
                              rw [hg₁] at hg₂
                              injection hg₂
                            have hy' : constToValTreeHeterog ts₁ ys = some vs₂ := by rw [htsEq]; exact hy
                            have hHet := structuralEqHeterog_eq_valTreeListEq flags adtEnv sz
                              (structuralEq_iff_valTree_eq_aux flags adtEnv sz)
                              ts₁ hts₁Le hadmTs xs ys ⟨vs₁, hx⟩ ⟨vs₂, hy'⟩
                            have heqHet := hHet.mpr ⟨vs₁, hx, by rw [hy', evs]⟩
                            change (if natEq v₁ v₂ then structuralEqVariants variants v₁ xs ys else _) = some true
                            have hnat : natEq v₁ v₂ = true := (natEq_true_iff v₁ v₂).mpr hvEq'
                            rw [hnat, structuralEqVariants_eq_getAt, hg₁]
                            exact heqHet
            | _ => cases h₂
          | _ => cases h₁

/-- Main Pillar 3 Bisimulation Theorem (`StructuralPartialEq` <-> `ValTree` Equivalence):
For every type `ty` admitted by `ConstParamTy` (`admitConstParamTy flags adtEnv ty = none`,
modeling `coherence/builtin.rs:170-245`) and all well-formed CTFE values `m₁, m₂` of `ty`,
runtime structural `PartialEq` holds **if and only if** `m₁` and `m₂` canonicalize to the
**exact same `ValTree`**. -/
theorem structuralEq_iff_valTree_eq (flags : FeatureFlags) (adtEnv : Nat → AdtMeta)
    (ty : ConstTy) (hadm : admitConstParamTy flags adtEnv ty = none)
    (m₁ m₂ : CtfeMemVal) (hm₁ : valTreeWellFormed ty m₁) (hm₂ : valTreeWellFormed ty m₂) :
    structuralEq ty m₁ m₂ = some true ↔
    ∃ vt, constToValTree ty m₁ = some vt ∧ constToValTree ty m₂ = some vt :=
  structuralEq_iff_valTree_eq_aux flags adtEnv (constTySize ty) ty (natLe_refl _) hadm m₁ m₂ hm₁ hm₂

/-- Top-level Type-Identity Bisimulation Corollary:
Whenever `ty` is admitted by `ConstParamTy` and `e₁, e₂` evaluate to well-formed CTFE values
`m₁, m₂`, runtime `structuralEq ty m₁ m₂ = some true` guarantees identical `canonicalValTree`,
identical `TypeIdentityKey`, and identical `v0` mangled symbol; and conversely distinct
`TypeIdentityKey`s cannot be `structuralEq`. -/
theorem admitted_valtree_typeid_bisimulation (flags : FeatureFlags) (adtEnv : Nat → AdtMeta)
    (carrierId : Nat) (ty : ConstTy) (hadm : admitConstParamTy flags adtEnv ty = none)
    (e₁ e₂ : ConcreteConstExpr) (m₁ m₂ : CtfeMemVal)
    (he₁ : evalConcreteConst e₁ = some m₁) (he₂ : evalConcreteConst e₂ = some m₂)
    (hm₁ : valTreeWellFormed ty m₁) (hm₂ : valTreeWellFormed ty m₂)
    (hseq : structuralEq ty m₁ m₂ = some true) :
    canonicalValTree ty e₁ = canonicalValTree ty e₂ ∧
    typeIdentityOf carrierId ty e₁ = typeIdentityOf carrierId ty e₂ ∧
    v0SymbolOf ty e₁ = v0SymbolOf ty e₂ := by
  have hvt := (structuralEq_iff_valTree_eq flags adtEnv ty hadm m₁ m₂ hm₁ hm₂).mp hseq
  cases hvt with
  | intro vt hpair =>
    cases hpair with
    | intro h₁ h₂ =>
      have hc₁ : canonicalValTree ty e₁ = some vt := by unfold canonicalValTree; rw [he₁]; exact h₁
      have hc₂ : canonicalValTree ty e₂ = some vt := by unfold canonicalValTree; rw [he₂]; exact h₂
      have hcanon : canonicalValTree ty e₁ = canonicalValTree ty e₂ := by rw [hc₁, hc₂]
      exact ⟨hcanon, canonical_valtree_determines_type_identity carrierId ty e₁ e₂ hcanon,
        canonical_valtree_determines_v0_symbol ty e₁ e₂ hcanon⟩

/-! ### Pillar 3 Counterexamples: Why `f32`, `&mut`, Unions, and Manual `PartialEq` Must Fail -/

/-- Structured IEEE-754 `f32` representation modeling the bit-level canonicalization hazards
without triggering 2^31 Peano kernel reductions:
- `f32PosZero` (`+0.0`, IEEE-754 bits `0x00000000`)
- `f32NegZero` (`-0.0`, IEEE-754 bits `0x80000000`)
- `f32QNaN` (quiet `NaN`, IEEE-754 bits `0x7fc00000`). -/
structure F32BitRepr where
  signNeg : Bool
  expByte : Nat
  mantTag : Nat

noncomputable def f32PosZero : F32BitRepr := { signNeg := false, expByte := 0, mantTag := 0 }
noncomputable def f32NegZero : F32BitRepr := { signNeg := true, expByte := 0, mantTag := 0 }
noncomputable def f32QNaN : F32BitRepr := { signNeg := false, expByte := 255, mantTag := 1 }

noncomputable def f32BitReprEq (a b : F32BitRepr) : Bool :=
  bAnd (boolEq a.signNeg b.signNeg) (bAnd (natEq a.expByte b.expByte) (natEq a.mantTag b.mantTag))

noncomputable def ieee754F32Eq (a b : F32BitRepr) : Bool :=
  if bOr (bAnd (natEq a.expByte 255) (bNot (natEq a.mantTag 0)))
         (bAnd (natEq b.expByte 255) (bNot (natEq b.mantTag 0))) then
    false
  else if bAnd (bAnd (natEq a.expByte 0) (natEq a.mantTag 0))
               (bAnd (natEq b.expByte 0) (natEq b.mantTag 0)) then
    true
  else
    f32BitReprEq a b

/-- Bit-level float canonicalization in `ValTree` if float const-params were improperly admitted:
distinguishes `ScalarInt` leaves bitwise (`valtrees.rs:116`). -/
noncomputable def rawF32BitLeaf (a : F32BitRepr) : ValTree :=
  ValTree.branch [.leaf (if a.signNeg then 1 else 0), .leaf a.expByte, .leaf a.mantTag]

/-- Counterexample 1a (`-0.0` vs `+0.0`): `ieee754F32Eq +0.0 -0.0 = true`,
yet raw `ValTree` bit-leaves differ (`+0.0 = 0x00000000 ≠ -0.0 = 0x80000000`), breaking
`runtime_eq → TypeId_eq` coherence (`Foo<{0.0}>` vs `Foo<{-0.0}>`). -/
theorem f32_neg_zero_eq_pos_zero_yet_distinct_valtree :
    ieee754F32Eq f32PosZero f32NegZero = true ∧
    rawF32BitLeaf f32PosZero ≠ rawF32BitLeaf f32NegZero := by
  refine ⟨rfl, ?_⟩
  intro h
  cases h

/-- Counterexample 1b (`NaN != NaN`): two identical `qNaN` const bit leaves (`0x7fc00000`) are
equal as `ValTree`s (`rawF32BitLeaf f32QNaN = rawF32BitLeaf f32QNaN`), yet
`ieee754F32Eq f32QNaN f32QNaN = false`, breaking `ValTree_eq → runtime_eq` and reflexivity. -/
theorem f32_nan_irreflexive_vs_valtree_eq :
    rawF32BitLeaf f32QNaN = rawF32BitLeaf f32QNaN ∧
    ieee754F32Eq f32QNaN f32QNaN = false := by
  exact ⟨rfl, rfl⟩

/-- `ConstParamTy` gate unconditionally rejects `f32` (`float32`), `fnPtr`, `&mut T`, and unions
across all standard feature-flag combinations. -/
theorem constParamTy_rejects_f32_mut_union_fnptr (flags : FeatureFlags) (adtEnv : Nat → AdtMeta)
    (inner : ConstTy) (uid : Nat) (alts : List ConstTy) :
    admitConstParamTy flags adtEnv .float32 = some .notAnAdtOrBuiltinAllowed ∧
    admitConstParamTy flags adtEnv .fnPtr = some .notAnAdtOrBuiltinAllowed ∧
    admitConstParamTy flags adtEnv (.ref true inner) = some .notAnAdtOrBuiltinAllowed ∧
    admitConstParamTy flags adtEnv (.unionTy uid alts) = some .notAnAdtOrBuiltinAllowed := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Models the empirical unsoundness witness (`#[feature(adt_const_params, structural_match)]`
with manual `impl StructuralPartialEq for Weird` + constant-true `PartialEq`):
`Weird(0) == Weird(1)` evaluates to `true`, whereas their canonical `ValTree`, `TypeIdentityKey`,
and `v0` symbol hashes are strictly distinct (`RUNTIME_EQ = true`, `TYPEID_EQ = false`). -/
noncomputable def weirdConstantTrueEq (_ _ : Nat) : Bool := true

noncomputable def weirdTy : ConstTy := .structTy 99 [tyU8]

noncomputable def weirdAdtEnvNoStructMatch (_ : Nat) : AdtMeta :=
  { isUnion := false
    isNonExhaustive := false
    hasPrivateField := false
    hasStructuralPartialEq := false
    hasEq := true }

theorem admit_rejects_manual_partial_eq_weird (flags : FeatureFlags)
    (hfeat : bOr flags.minAdtConstParams flags.adtConstParams = true) :
    admitConstParamTy flags weirdAdtEnvNoStructMatch weirdTy = some .missingStructuralPartialEq := by
  change (if bOr flags.minAdtConstParams flags.adtConstParams then match adtHeaderCheck flags (weirdAdtEnvNoStructMatch 99) with | some e => some e | none => admitConstParamTyList flags weirdAdtEnvNoStructMatch [tyU8] else some .notAnAdtOrBuiltinAllowed) = some .missingStructuralPartialEq
  rw [hfeat]
  rfl

theorem weird_manual_structural_peq_unsoundness_witness :
    let w0 : ConcreteConstExpr := .mkStruct [] [.litNat 0]
    let w1 : ConcreteConstExpr := .mkStruct [] [.litNat 1]
    weirdConstantTrueEq 0 1 = true ∧
    canonicalValTree weirdTy w0 ≠ canonicalValTree weirdTy w1 ∧
    typeIdentityOf 99 weirdTy w0 ≠ typeIdentityOf 99 weirdTy w1 ∧
    v0SymbolOf weirdTy w0 ≠ v0SymbolOf weirdTy w1 := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h

/-- Feature-gate precision theorems (`min_adt_const_params` vs `adt_const_params` and
`unsized_const_params`), matching live differential compiler checks:
- Under `min_adt_const_params` only, private fields fail (`fieldVisMismatch`) and
  `#[non_exhaustive]` fails (`nonExhaustive`); under `adt_const_params`, both pass (`none`).
- `&T`, `[T]`, and `str` fail without `unsized_const_params` and pass once enabled. -/
theorem feature_gate_adt_and_unsized_precision :
    let minFlags : FeatureFlags :=
      { minAdtConstParams := true, adtConstParams := false, unsizedConstParams := false, constParamTyUnchecked := false }
    let fullFlags : FeatureFlags :=
      { minAdtConstParams := true, adtConstParams := true, unsizedConstParams := true, constParamTyUnchecked := false }
    let privAdt : AdtMeta :=
      { isUnion := false, isNonExhaustive := false, hasPrivateField := true, hasStructuralPartialEq := true, hasEq := true }
    let nonExhAdt : AdtMeta :=
      { isUnion := false, isNonExhaustive := true, hasPrivateField := false, hasStructuralPartialEq := true, hasEq := true }
    admitConstParamTy minFlags (fun _ => privAdt) (.structTy 1 [tyU8]) = some .fieldVisMismatch ∧
    admitConstParamTy minFlags (fun _ => nonExhAdt) (.structTy 2 [tyU8]) = some .nonExhaustive ∧
    admitConstParamTy fullFlags (fun _ => privAdt) (.structTy 1 [tyU8]) = none ∧
    admitConstParamTy fullFlags (fun _ => nonExhAdt) (.structTy 2 [tyU8]) = none ∧
    admitConstParamTy minFlags weirdAdtEnvNoStructMatch .str = some .unsizedConstParamsRequired ∧
    admitConstParamTy fullFlags weirdAdtEnvNoStructMatch .str = none ∧
    admitConstParamTy minFlags weirdAdtEnvNoStructMatch (.ref false tyU8) = some .unsizedConstParamsRequired ∧
    admitConstParamTy fullFlags weirdAdtEnvNoStructMatch (.ref false tyU8) = none := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Anneal.ConstGenericsValTreeSoundness
