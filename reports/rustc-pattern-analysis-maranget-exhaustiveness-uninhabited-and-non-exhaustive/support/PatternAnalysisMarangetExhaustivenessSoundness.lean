-- Copyright 2026 The Authors
-- SPDX-License-Identifier: Apache-2.0 OR MIT

/-!
# Mechanized Soundness of `rustc_pattern_analysis`: Maranget Specialization Matrix,
# Uninhabited Types vs `&Void`, Cross-Crate `#[non_exhaustive]`, Guards, Ranges, and `unreachable_patterns`

Pinned to `Lean v4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`).

Strict constructive kernel discipline:
- Zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`, zero `native_decide`.
- Zero `partial def`, zero `noncomputable section`, zero `deriving` on recursive inductives.
- Every `def` is explicitly marked `noncomputable def`, guaranteeing zero `._unsafe_rec` constants
  in the Lean environment.

## Primary-Source Correspondence (`rust-lang/rust`)
Audited at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly`) and cross-checked
against `49d734536222bf28bb6d07d885b3a81d145981da` and `960ba7cf7e8666ecb449402ca82b6e9e631bd227`:
1. `compiler/rustc_pattern_analysis/src/usefulness.rs`:
   - `PlaceValidity::{ValidOnly, MaybeInvalid}` and `PlaceValidity::specialize` (`848-878`).
   - `PlaceInfo::split_column_ctors` (`930-1006` at `14210df0`; `924-998` at `49d73453`/`960ba7cf`),
     including `is_toplevel_exception`, `empty_arms_are_unreachable`, `can_omit_empty_arms`,
     `PrivateUninhabited`, and `NonExhaustive` collapse.
   - `MatrixRow::new` (`1143-1153`), `is_under_guard`, `compute_exhaustiveness_and_usefulness` (`1704-1798`).
2. `compiler/rustc_pattern_analysis/src/constructor.rs`:
   - `IntRange::split` (`370-414`), `Constructor::{NonExhaustive, PrivateUninhabited}` (`729-739`),
     `Constructor::is_covered_by` (`811-831`), `ConstructorSet::split` (`1046-1205`).
3. `compiler/rustc_pattern_analysis/src/rustc.rs`:
   - `is_uninhabited` (`157-164`), `is_foreign_non_exhaustive_enum` (`167-172`),
     `ctor_sub_tys` / `PrivateUninhabitedField` (`230-281`), `ctors_for_ty` (`306-436`).
4. `compiler/rustc_mir_build/src/thir/pattern/check_match.rs`:
   - `is_known_valid_scrutinee` (`293-368`), `would_be_exhaustive_without_guards` (`576-584`),
     `report_non_exhaustive_match` (`1226-1316`, `"references are always considered inhabited"`).
-/

namespace PatternAnalysisSoundness

/-! ## Section 1: Constructive `Nat`, `Bool`, and `List` Primitives -/

/-- Structural equality on `Nat`. -/
noncomputable def natBeq : Nat → Nat → Bool
  | 0, 0 => true
  | m + 1, n + 1 => natBeq m n
  | _, _ => false

/-- Structural `≤` comparison on `Nat`. -/
noncomputable def natBle : Nat → Nat → Bool
  | 0, _ => true
  | _ + 1, 0 => false
  | m + 1, n + 1 => natBle m n

/-- Structural `<` comparison on `Nat`. -/
noncomputable def natBlt (m n : Nat) : Bool :=
  natBle (m + 1) n

/-- Structural boolean equality on `Bool`. -/
noncomputable def boolBeq : Bool → Bool → Bool
  | true, true => true
  | false, false => true
  | _, _ => false

theorem boolBeq_refl (b : Bool) : boolBeq b b = true := by
  cases b <;> rfl

theorem boolBeq_eq_of_true {a b : Bool} (h : boolBeq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | contradiction

theorem boolBeq_true_iff (a b : Bool) : boolBeq a b = true ↔ a = b := by
  constructor
  · exact boolBeq_eq_of_true
  · intro h; rw [h]; exact boolBeq_refl b

/-- Minimum of two `Nat` values. -/
noncomputable def natMin (m n : Nat) : Nat :=
  if natBle m n then m else n

/-- Maximum of two `Nat` values. -/
noncomputable def natMax (m n : Nat) : Nat :=
  if natBle m n then n else m

/-- Boolean conjunction elimination. -/
theorem boolAnd_eq_true {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a with
  | false => contradiction
  | true => exact ⟨rfl, h⟩

/-- Boolean conjunction introduction. -/
theorem boolAnd_intro {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by
  rw [ha, hb]
  rfl

/-- Boolean disjunction elimination. -/
theorem boolOr_eq_true {a b : Bool} (h : (a || b) = true) : a = true ∨ b = true := by
  cases a with
  | true => exact Or.inl rfl
  | false => exact Or.inr h

/-- Boolean disjunction introduction (left). -/
theorem boolOr_intro_left {a b : Bool} (ha : a = true) : (a || b) = true := by
  rw [ha]
  rfl

/-- Boolean disjunction introduction (right). -/
theorem boolOr_intro_right {a b : Bool} (hb : b = true) : (a || b) = true := by
  cases a with
  | true => rfl
  | false => exact hb

/-- Boolean disjunction false equivalence. -/
theorem boolOr_eq_false {a b : Bool} : (a || b) = false ↔ a = false ∧ b = false := by
  cases a with
  | true =>
    constructor
    · intro h; contradiction
    · intro h; exact False.elim (Bool.noConfusion h.1)
  | false =>
    constructor
    · intro h; exact ⟨rfl, h⟩
    · intro h; exact h.2

/-- Boolean negation elimination (`!a = true`). -/
theorem boolNot_eq_true {a : Bool} (h : (!a) = true) : a = false := by
  cases a with
  | false => rfl
  | true => contradiction

/-- Boolean negation elimination (`!a = false`). -/
theorem boolNot_eq_false {a : Bool} (h : (!a) = false) : a = true := by
  cases a with
  | false => contradiction
  | true => rfl

/-- Reflexivity of `natBeq`. -/
theorem natBeq_refl (n : Nat) : natBeq n n = true := by
  induction n with
  | zero => rfl
  | succ _ ih => exact ih

/-- Soundness of `natBeq`. -/
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

/-- Completeness of `natBeq` for equal values. -/
theorem natBeq_true_iff (m n : Nat) : natBeq m n = true ↔ m = n := by
  constructor
  · exact natBeq_eq_of_true
  · intro h; rw [h]; exact natBeq_refl n

/-- Soundness and completeness of `natBle` w.r.t. `Nat.le`. -/
theorem natBle_iff_le (m n : Nat) : natBle m n = true ↔ m ≤ n := by
  induction m generalizing n with
  | zero =>
    constructor
    · intro _; exact Nat.zero_le n
    · intro _; rfl
  | succ m ih =>
    cases n with
    | zero =>
      constructor
      · intro h; contradiction
      · intro h; exact False.elim (Nat.not_succ_le_zero m h)
    | succ n =>
      constructor
      · intro h; exact Nat.succ_le_succ ((ih n).mp h)
      · intro h; exact (ih n).mpr (Nat.le_of_succ_le_succ h)

/-- Reflexivity of `natBle`. -/
theorem natBle_refl (n : Nat) : natBle n n = true :=
  (natBle_iff_le n n).mpr (Nat.le_refl n)

/-- Soundness and completeness of `natBlt` w.r.t. `Nat.lt`. -/
theorem natBlt_iff_lt (m n : Nat) : natBlt m n = true ↔ m < n :=
  natBle_iff_le (m + 1) n

/-- False `natBle` implies strict `<` in reverse. -/
theorem natBle_false_iff_lt (m n : Nat) : natBle m n = false ↔ n < m := by
  cases h : natBle m n with
  | true =>
    constructor
    · intro h1; contradiction
    · intro hlt
      have hle : m ≤ n := (natBle_iff_le m n).mp h
      exact False.elim (Nat.not_le_of_gt hlt hle)
  | false =>
    constructor
    · intro _
      cases Nat.lt_or_ge n m with
      | inl hlt => exact hlt
      | inr hle =>
        have ht : natBle m n = true := (natBle_iff_le m n).mpr hle
        rw [ht] at h
        contradiction
    · intro _; rfl

/-- False `natBlt` implies `≤` in reverse. -/
theorem natBlt_false_iff_le (m n : Nat) : natBlt m n = false ↔ n ≤ m := by
  have h := natBle_false_iff_lt (m + 1) n
  constructor
  · intro hf
    exact Nat.le_of_lt_succ (h.mp hf)
  · intro hle
    exact h.mpr (Nat.lt_succ_of_le hle)

/-- `natMax` bounds left argument. -/
theorem natMax_ge_left (m n : Nat) : m ≤ natMax m n := by
  unfold natMax
  cases h : natBle m n
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact Nat.le_refl m
  · simp only [↓reduceIte]
    exact (natBle_iff_le m n).mp h

/-- `natMax` bounds right argument. -/
theorem natMax_ge_right (m n : Nat) : n ≤ natMax m n := by
  unfold natMax
  cases h : natBle m n
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact Nat.le_of_lt ((natBle_false_iff_lt m n).mp h)
  · simp only [↓reduceIte]
    exact Nat.le_refl n

/-- `natMax` equals one of its two inputs and is bounded by any common upper bound. -/
theorem natMax_le_of_le {m n k : Nat} (hm : m ≤ k) (hn : n ≤ k) : natMax m n ≤ k := by
  unfold natMax
  cases h : natBle m n
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact hm
  · simp only [↓reduceIte]
    exact hn

/-- `natMin` is bounded by left argument. -/
theorem natMin_le_left (m n : Nat) : natMin m n ≤ m := by
  unfold natMin
  cases h : natBle m n
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact Nat.le_of_lt ((natBle_false_iff_lt m n).mp h)
  · simp only [↓reduceIte]
    exact Nat.le_refl m

/-- `natMin` is bounded by right argument. -/
theorem natMin_le_right (m n : Nat) : natMin m n ≤ n := by
  unfold natMin
  cases h : natBle m n
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact Nat.le_refl n
  · simp only [↓reduceIte]
    exact (natBle_iff_le m n).mp h

/-- `natMin` bounds any common lower bound. -/
theorem natMin_ge_of_le {k m n : Nat} (hm : k ≤ m) (hn : k ≤ n) : k ≤ natMin m n := by
  unfold natMin
  cases h : natBle m n
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact hn
  · simp only [↓reduceIte]
    exact hm

/-- Universal boolean check on a list. -/
noncomputable def listAll {α : Type} (p : α → Bool) : List α → Bool
  | [] => true
  | x :: xs => p x && listAll p xs

/-- Existential boolean check on a list. -/
noncomputable def listAny {α : Type} (p : α → Bool) : List α → Bool
  | [] => false
  | x :: xs => p x || listAny p xs

/-- Sum of `Nat` list elements. -/
noncomputable def listSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + listSum xs

/-- Length-bounded element lookup on lists. -/
noncomputable def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGet? xs n

/-- Replicate a value `n` times. -/
noncomputable def listReplicate {α : Type} (n : Nat) (x : α) : List α :=
  match n with
  | 0 => []
  | k + 1 => x :: listReplicate k x

/-- Correctness of `listAll`. -/
theorem listAll_iff {α : Type} (p : α → Bool) (xs : List α) :
    listAll p xs = true ↔ ∀ x, x ∈ xs → p x = true := by
  induction xs with
  | nil =>
    constructor
    · intro _ x hx; exact False.elim (List.not_mem_nil hx)
    · intro _; rfl
  | cons y ys ih =>
    constructor
    · intro h x hx
      rcases boolAnd_eq_true h with ⟨hy, hys⟩
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hy
      · exact (ih.mp hys) x hx'
    · intro h
      apply boolAnd_intro
      · exact h y List.mem_cons_self
      · exact ih.mpr (fun x hx => h x (List.mem_cons_of_mem y hx))

/-- Correctness of `listAny`. -/
theorem listAny_iff {α : Type} (p : α → Bool) (xs : List α) :
    listAny p xs = true ↔ ∃ x, x ∈ xs ∧ p x = true := by
  induction xs with
  | nil =>
    constructor
    · intro h; contradiction
    · intro ⟨x, hx, _⟩; exact False.elim (List.not_mem_nil hx)
  | cons y ys ih =>
    constructor
    · intro h
      rcases boolOr_eq_true h with hy | hys
      · exact ⟨y, List.mem_cons_self, hy⟩
      · rcases ih.mp hys with ⟨x, hx, hp⟩
        exact ⟨x, List.mem_cons_of_mem y hx, hp⟩
    · intro ⟨x, hx, hp⟩
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact boolOr_intro_left hp
      · exact boolOr_intro_right (ih.mpr ⟨x, hx', hp⟩)

/-- `listAny` false iff no element satisfies `p`. -/
theorem listAny_eq_false_iff {α : Type} (p : α → Bool) (xs : List α) :
    listAny p xs = false ↔ ∀ x, x ∈ xs → p x = false := by
  induction xs with
  | nil =>
    constructor
    · intro _ x hx; exact False.elim (List.not_mem_nil hx)
    · intro _; rfl
  | cons y ys ih =>
    constructor
    · intro h x hx
      rcases boolOr_eq_false.mp h with ⟨hy, hys⟩
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hy
      · exact (ih.mp hys) x hx'
    · intro h
      apply boolOr_eq_false.mpr
      exact ⟨h y List.mem_cons_self, ih.mpr (fun x hx => h x (List.mem_cons_of_mem y hx))⟩

/-- If `listGet? xs idx = some x`, then `x ∈ xs`. -/
theorem listGet?_mem {α : Type} {xs : List α} {idx : Nat} {x : α}
    (h : listGet? xs idx = some x) : x ∈ xs := by
  induction xs generalizing idx with
  | nil => cases idx <;> contradiction
  | cons y ys ih =>
    cases idx with
    | zero =>
      cases h
      exact List.mem_cons_self
    | succ k =>
      exact List.mem_cons_of_mem y (ih h)

/-- Every element in `xs` has a witness index in `listGet?`. -/
theorem mem_iff_exists_listGet? {α : Type} {xs : List α} {x : α} :
    x ∈ xs ↔ ∃ idx, listGet? xs idx = some x := by
  induction xs with
  | nil =>
    constructor
    · intro h; exact False.elim (List.not_mem_nil h)
    · intro ⟨idx, h⟩; cases idx <;> contradiction
  | cons y ys ih =>
    constructor
    · intro h
      rcases List.mem_cons.mp h with rfl | hy
      · exact ⟨0, rfl⟩
      · rcases ih.mp hy with ⟨k, hk⟩
        exact ⟨k + 1, hk⟩
    · intro ⟨idx, h⟩
      exact listGet?_mem h

/-- Every element of `listReplicate n x` equals `x`. -/
theorem mem_listReplicate {α : Type} {n : Nat} {x y : α}
    (h : y ∈ listReplicate n x) : y = x := by
  induction n with
  | zero => exact False.elim (List.not_mem_nil h)
  | succ k ih =>
    rcases List.mem_cons.mp h with rfl | hk
    · rfl
    · exact ih hk

/-- Length of `listReplicate n x` is `n`. -/
theorem length_listReplicate {α : Type} (n : Nat) (x : α) :
    (listReplicate n x).length = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [listReplicate, ih]

/-- Elementary Nat sum bound: any member of `xs` is `≤ listSum xs`. -/
theorem le_listSum_of_mem {n : Nat} {xs : List Nat} (h : n ∈ xs) : n ≤ listSum xs := by
  induction xs with
  | nil => exact False.elim (List.not_mem_nil h)
  | cons y ys ih =>
    rcases List.mem_cons.mp h with rfl | h'
    · exact Nat.le_add_right n (listSum ys)
    · exact Nat.le_trans (ih h') (Nat.le_add_left (listSum ys) y)

/-- Elementary `map` weight sum bound. -/
theorem le_listSum_map_of_get? {α : Type} (f : α → Nat) {xs : List α} {idx : Nat} {x : α}
    (h : listGet? xs idx = some x) : f x ≤ listSum (xs.map f) := by
  apply le_listSum_of_mem
  exact List.mem_map_of_mem (listGet?_mem h)

/-- Helper: `a < b → a + c < b + c` without `omega`. -/
theorem add_lt_add_right_nat {a b c : Nat} (h : a < b) : a + c < b + c :=
  Nat.add_lt_add_right h c

/-! ## Section 2: `PlaceValidity`, Type Universe, Values, and Visible vs True Inhabitation -/

/-- Whether a place under pattern inspection is guaranteed to hold valid initialized data
(`rustc_pattern_analysis::usefulness::PlaceValidity`, `usefulness.rs:848-878`). -/
inductive PlaceValidity where
  | validOnly
  | maybeInvalid

/-- Structural equality on `PlaceValidity`. -/
noncomputable def PlaceValidity.beq : PlaceValidity → PlaceValidity → Bool
  | .validOnly, .validOnly => true
  | .maybeInvalid, .maybeInvalid => true
  | _, _ => false

/-- Check whether `PlaceValidity` is `validOnly`. -/
noncomputable def PlaceValidity.isKnownValid : PlaceValidity → Bool
  | .validOnly => true
  | .maybeInvalid => false

/-- Type universe modeling `rustc_pattern_analysis`'s core type categories:
- `unit`: `()`
- `bool`: `bool`
- `u8`: bounded scalar `0..=255` (models finite `IntRange` splitting)
- `void`: uninhabited zero-constructor type (`!` / `enum Void {}`)
- `pair`: 2-tuple `(A, B)`
- `struct2`: 2-field struct whose second field has visibility `privFieldVisible`
  (`ConstructorSet::Struct { empty }` + `PrivateUninhabitedField`)
- `enum`: ADT with variant payloads `variants` and cross-crate `nonExh` flag (`#[non_exhaustive]`)
- `ref`: `&T` (always inhabited; resets inner `PlaceValidity` to `maybeInvalid`). -/
inductive Ty where
  | unit
  | bool
  | u8
  | void
  | pair (fst snd : Ty)
  | struct2 (pubField privField : Ty) (privFieldVisible : Bool)
  | enum (variants : List Ty) (nonExh : Bool)
  | ref (inner : Ty)

mutual
  /-- Strictly positive structural weight of a `Ty` (mutually recursive for pure structural
  reduction with zero well-founded recursion), ensuring Maranget specialization terminates. -/
  noncomputable def tyWeight : Ty → Nat
    | .unit => 1
    | .bool => 1
    | .u8 => 1
    | .void => 1
    | .pair a b => 1 + tyWeight a + tyWeight b
    | .struct2 a b _ => 1 + tyWeight a + tyWeight b
    | .enum vs _ => 1 + tyWeightList vs
    | .ref inner => 1 + tyWeight inner

  /-- Total weight of a list of variant payload types. -/
  noncomputable def tyWeightList : List Ty → Nat
    | [] => 0
    | t :: ts => tyWeight t + tyWeightList ts
end

/-- Helper: extract left-branch weight bound without `omega`. -/
theorem le_left_of_one_add_add {a b w : Nat} (h : 1 + a + b ≤ w + 1) : a ≤ w := by
  have h1 : 1 + a ≤ 1 + a + b := Nat.le_add_right (1 + a) b
  have h2 : a + 1 ≤ w + 1 := by
    rw [Nat.add_comm a 1]
    exact Nat.le_trans h1 h
  exact Nat.le_of_succ_le_succ h2

/-- Helper: extract right-branch weight bound without `omega`. -/
theorem le_right_of_one_add_add {a b w : Nat} (h : 1 + a + b ≤ w + 1) : b ≤ w := by
  have h1 : 1 + b ≤ 1 + a + b := by
    rw [Nat.add_assoc, Nat.add_comm a b, ← Nat.add_assoc]
    exact Nat.le_add_right (1 + b) a
  have h2 : b + 1 ≤ w + 1 := by
    rw [Nat.add_comm b 1]
    exact Nat.le_trans h1 h
  exact Nat.le_of_succ_le_succ h2

/-- Lookup bound on `tyWeightList` for enum variant payloads. -/
theorem tyWeight_le_tyWeightList_of_get? {xs : List Ty} {idx : Nat} {x : Ty}
    (h : listGet? xs idx = some x) : tyWeight x ≤ tyWeightList xs := by
  induction xs generalizing idx with
  | nil => cases idx <;> contradiction
  | cons y ys ih =>
    cases idx with
    | zero =>
      cases h
      change tyWeight x ≤ tyWeight x + tyWeightList ys
      exact Nat.le_add_right (tyWeight x) (tyWeightList ys)
    | succ k =>
      change tyWeight x ≤ tyWeight y + tyWeightList ys
      exact Nat.le_trans (ih h) (Nat.le_add_left (tyWeightList ys) (tyWeight y))

/-- Every type has strictly positive structural weight (`≥ 1`). -/
theorem tyWeight_pos (t : Ty) : 1 ≤ tyWeight t := by
  cases t with
  | unit | bool | u8 | void => exact Nat.le_refl 1
  | pair a b =>
    change 1 ≤ 1 + tyWeight a + tyWeight b
    exact Nat.le_trans (Nat.le_add_right 1 (tyWeight a)) (Nat.le_add_right (1 + tyWeight a) (tyWeight b))
  | struct2 a b _ =>
    change 1 ≤ 1 + tyWeight a + tyWeight b
    exact Nat.le_trans (Nat.le_add_right 1 (tyWeight a)) (Nat.le_add_right (1 + tyWeight a) (tyWeight b))
  | enum vs _ =>
    change 1 ≤ 1 + tyWeightList vs
    exact Nat.le_add_right 1 _
  | ref inner =>
    change 1 ≤ 1 + tyWeight inner
    exact Nat.le_add_right 1 _

mutual
  /-- Module-local visible emptiness (`RustcPatCtxt::is_uninhabited`, `rustc.rs:157-164, 371-415`):
  - `.void` is empty;
  - `.ref _` is **never** empty (`"references are always considered inhabited"`);
  - `.struct2 a b bVis` is empty iff `a` is empty OR (`bVis = true` and `b` is empty);
  - `.enum variants nonExh` is empty iff `nonExh = false` and every variant payload is empty. -/
  noncomputable def tyIsEmpty : Ty → Bool
    | .unit => false
    | .bool => false
    | .u8 => false
    | .void => true
    | .pair a b => tyIsEmpty a || tyIsEmpty b
    | .struct2 a b bVis => tyIsEmpty a || (bVis && tyIsEmpty b)
    | .enum variants nonExh => (!nonExh) && tyIsEmptyList variants
    | .ref _ => false

  /-- Check whether every variant payload type in a list is empty. -/
  noncomputable def tyIsEmptyList : List Ty → Bool
    | [] => true
    | t :: ts => tyIsEmpty t && tyIsEmptyList ts
end

/-- Soundness of `tyIsEmptyList` on indexed variant payload lookup. -/
theorem tyIsEmpty_of_tyIsEmptyList {variants : List Ty} {idx : Nat} {pt : Ty}
    (hall : tyIsEmptyList variants = true) (hget : listGet? variants idx = some pt) :
    tyIsEmpty pt = true := by
  induction variants generalizing idx with
  | nil => cases idx <;> contradiction
  | cons v vs ih =>
    rcases boolAnd_eq_true hall with ⟨hv, hvs⟩
    cases idx with
    | zero =>
      cases hget
      exact hv
    | succ k =>
      exact ih hvs hget

/-- Runtime values for our pattern semantics.
- `invalid` represents uninitialized / invalid bits behind a reference or opaque private field
  (`PlaceValidity.maybeInvalid`).
- `hiddenCtor tag` represents an unknown upstream variant of a `#[non_exhaustive]` enum
  added after downstream compilation. -/
inductive Val where
  | invalid
  | unit
  | bool (b : Bool)
  | u8 (n : Nat)
  | pair (v1 v2 : Val)
  | ctor (idx : Nat) (payload : Val)
  | hiddenCtor (extraTag : Nat)
  | ref (pointee : Val)

/-- Visible typing relation `VisibleWellTyped val ty v`:
Captures the exact inhabitation assumptions enforced by `rustc_pattern_analysis`:
1. Under `.validOnly`, `.invalid` is forbidden at top-level value slots (`void` has 0 inhabitants).
2. Under `.maybeInvalid`, `.invalid` is permitted as a possible place state (for `&T` deref / pointer deref).
3. Entering `.ref inner` resets validity of `pointee` to `.maybeInvalid` (`PlaceValidity::specialize(Ref)`),
   making `Val.ref Val.invalid` valid at `.ref .void` even under `.validOnly`!
4. Entering an invisible field of `.struct2 _ _ false` permits `.invalid` (privacy boundary prevents
   downstream callers from concluding uninhabitedness of private fields).
5. A `#[non_exhaustive]` enum (`nonExh = true`) admits open-world `Val.hiddenCtor tag` values. -/
noncomputable def VisibleWellTyped : PlaceValidity → Ty → Val → Prop
  | .maybeInvalid, _, .invalid => True
  | .validOnly, _, .invalid => False
  | _, .unit, .unit => True
  | _, .bool, .bool _ => True
  | _, .u8, .u8 n => n ≤ 255
  | _, .void, _ => False
  | val, .pair a b, .pair v1 v2 => VisibleWellTyped val a v1 ∧ VisibleWellTyped val b v2
  | val, .struct2 a b true, .pair v1 v2 => VisibleWellTyped val a v1 ∧ VisibleWellTyped val b v2
  | val, .struct2 a b false, .pair v1 v2 =>
    VisibleWellTyped val a v1 ∧
    (if tyIsEmpty b then VisibleWellTyped .maybeInvalid b v2 else VisibleWellTyped val b v2)
  | val, .enum variants _, .ctor idx sub =>
    ∃ payloadTy, listGet? variants idx = some payloadTy ∧ VisibleWellTyped val payloadTy sub
  | _, .enum _ true, .hiddenCtor _ => True
  | _, .ref inner, .ref pt => VisibleWellTyped .maybeInvalid inner pt
  | _, _, _ => False

/-- Strict physical typing relation `TrueWellTyped val ty v` (without privacy opacity):
every field of `.struct2` must still satisfy the ambient validity `val`. -/
noncomputable def TrueWellTyped : PlaceValidity → Ty → Val → Prop
  | .maybeInvalid, _, .invalid => True
  | .validOnly, _, .invalid => False
  | _, .unit, .unit => True
  | _, .bool, .bool _ => True
  | _, .u8, .u8 n => n ≤ 255
  | _, .void, _ => False
  | val, .pair a b, .pair v1 v2 => TrueWellTyped val a v1 ∧ TrueWellTyped val b v2
  | val, .struct2 a b _, .pair v1 v2 => TrueWellTyped val a v1 ∧ TrueWellTyped val b v2
  | val, .enum variants _, .ctor idx sub =>
    ∃ payloadTy, listGet? variants idx = some payloadTy ∧ TrueWellTyped val payloadTy sub
  | _, .enum _ true, .hiddenCtor _ => True
  | _, .ref inner, .ref pt => TrueWellTyped .maybeInvalid inner pt
  | _, _, _ => False

/-- Monotonicity helper indexed by `tyWeight` bound to recurse cleanly across `enum variants`. -/
theorem visibleWellTyped_valid_to_maybe_bound :
    ∀ (w : Nat) (t : Ty) (v : Val),
      tyWeight t ≤ w →
      VisibleWellTyped .validOnly t v →
      VisibleWellTyped .maybeInvalid t v := by
  intro w
  induction w with
  | zero =>
    intro t v hw _
    have hpos := tyWeight_pos t
    exact False.elim (Nat.not_succ_le_zero 0 (Nat.le_trans hpos hw))
  | succ w' ih =>
    intro t v hw hv
    cases t with
    | unit =>
      cases v <;> first | contradiction | trivial
    | bool =>
      cases v <;> first | contradiction | trivial
    | u8 =>
      cases v with
      | u8 n => exact hv
      | invalid | unit | bool _ | pair _ _ | ctor _ _ | hiddenCtor _ | ref _ => contradiction
    | void =>
      cases v <;> contradiction
    | pair a b =>
      cases v with
      | pair v1 v2 =>
        have hwa : tyWeight a ≤ w' := le_left_of_one_add_add hw
        have hwb : tyWeight b ≤ w' := le_right_of_one_add_add hw
        exact ⟨ih a v1 hwa hv.1, ih b v2 hwb hv.2⟩
      | invalid | unit | bool _ | u8 _ | ctor _ _ | hiddenCtor _ | ref _ => contradiction
    | struct2 a b bVis =>
      cases v with
      | pair v1 v2 =>
        have hwa : tyWeight a ≤ w' := le_left_of_one_add_add hw
        have hwb : tyWeight b ≤ w' := le_right_of_one_add_add hw
        cases bVis with
        | true => exact ⟨ih a v1 hwa hv.1, ih b v2 hwb hv.2⟩
        | false =>
          rcases hv with ⟨hv1, hv2⟩
          dsimp only [VisibleWellTyped]
          cases he : tyIsEmpty b with
          | true =>
            have hv2' : VisibleWellTyped PlaceValidity.maybeInvalid b v2 := by
              rw [he] at hv2; exact hv2
            simp only [ite_true]
            exact ⟨ih a v1 hwa hv1, hv2'⟩
          | false =>
            have hv2' : VisibleWellTyped PlaceValidity.validOnly b v2 := by
              rw [he] at hv2; exact hv2
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact ⟨ih a v1 hwa hv1, ih b v2 hwb hv2'⟩
      | invalid | unit | bool _ | u8 _ | ctor _ _ | hiddenCtor _ | ref _ => contradiction
    | enum variants nonExh =>
      cases v with
      | ctor idx sub =>
        rcases hv with ⟨pt, hget, hsub⟩
        have hsum : tyWeight pt ≤ tyWeightList variants :=
          tyWeight_le_tyWeightList_of_get? hget
        change 1 + tyWeightList variants ≤ w' + 1 at hw
        rw [Nat.add_comm 1 (tyWeightList variants)] at hw
        have hwpt : tyWeight pt ≤ w' :=
          Nat.le_trans hsum (Nat.le_of_succ_le_succ hw)
        exact ⟨pt, hget, ih pt sub hwpt hsub⟩
      | hiddenCtor _ =>
        cases nonExh <;> first | contradiction | trivial
      | invalid | unit | bool _ | u8 _ | pair _ _ | ref _ => contradiction
    | ref inner =>
      cases v with
      | ref pt => exact hv
      | invalid | unit | bool _ | u8 _ | pair _ _ | ctor _ _ | hiddenCtor _ => contradiction

/-- Monotonicity of `VisibleWellTyped`: `.validOnly` implies `.maybeInvalid`. -/
theorem visibleWellTyped_valid_to_maybe {t : Ty} {v : Val}
    (h : VisibleWellTyped .validOnly t v) : VisibleWellTyped .maybeInvalid t v :=
  visibleWellTyped_valid_to_maybe_bound (tyWeight t) t v (Nat.le_refl (tyWeight t)) h

/-- Every strictly well-typed value (`TrueWellTyped`) is also visibly well-typed (`VisibleWellTyped`). -/
theorem trueWellTyped_implies_visible_bound :
    ∀ (w : Nat) (val : PlaceValidity) (t : Ty) (v : Val),
      tyWeight t ≤ w →
      TrueWellTyped val t v →
      VisibleWellTyped val t v := by
  intro w
  induction w with
  | zero =>
    intro _ t _ hw _
    exact False.elim (Nat.not_succ_le_zero 0 (Nat.le_trans (tyWeight_pos t) hw))
  | succ w' ih =>
    intro val t v hw ht
    cases val with
    | maybeInvalid =>
      cases v with
      | invalid => trivial
      | unit =>
        cases t <;> first | contradiction | trivial
      | bool b =>
        cases t <;> first | contradiction | trivial
      | u8 n =>
        cases t <;> first | contradiction | exact ht
      | pair v1 v2 =>
        cases t with
        | pair a b =>
          have hwa : tyWeight a ≤ w' := le_left_of_one_add_add hw
          have hwb : tyWeight b ≤ w' := le_right_of_one_add_add hw
          exact ⟨ih .maybeInvalid a v1 hwa ht.1, ih .maybeInvalid b v2 hwb ht.2⟩
        | struct2 a b bVis =>
          have hwa : tyWeight a ≤ w' := le_left_of_one_add_add hw
          have hwb : tyWeight b ≤ w' := le_right_of_one_add_add hw
          cases bVis with
          | true => exact ⟨ih .maybeInvalid a v1 hwa ht.1, ih .maybeInvalid b v2 hwb ht.2⟩
          | false =>
            dsimp only [VisibleWellTyped]
            cases he : tyIsEmpty b with
            | true =>
              simp only [ite_true]
              exact ⟨ih .maybeInvalid a v1 hwa ht.1, ih .maybeInvalid b v2 hwb ht.2⟩
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              exact ⟨ih .maybeInvalid a v1 hwa ht.1, ih .maybeInvalid b v2 hwb ht.2⟩
        | unit | bool | u8 | void | enum _ _ | ref _ => contradiction
      | ctor idx sub =>
        cases t with
        | enum variants nonExh =>
          rcases ht with ⟨pt, hget, hsub⟩
          have hsum : tyWeight pt ≤ tyWeightList variants :=
            tyWeight_le_tyWeightList_of_get? hget
          change 1 + tyWeightList variants ≤ w' + 1 at hw
          rw [Nat.add_comm 1 (tyWeightList variants)] at hw
          have hwpt : tyWeight pt ≤ w' := Nat.le_trans hsum (Nat.le_of_succ_le_succ hw)
          exact ⟨pt, hget, ih .maybeInvalid pt sub hwpt hsub⟩
        | unit | bool | u8 | void | pair _ _ | struct2 _ _ _ | ref _ => contradiction
      | hiddenCtor _ =>
        cases t with
        | enum _ nonExh => cases nonExh <;> first | contradiction | trivial
        | unit | bool | u8 | void | pair _ _ | struct2 _ _ _ | ref _ => contradiction
      | ref pt =>
        cases t with
        | ref inner =>
          have hwi : tyWeight inner ≤ w' := by
            change 1 + tyWeight inner ≤ w' + 1 at hw
            rw [Nat.add_comm 1 (tyWeight inner)] at hw
            exact Nat.le_of_succ_le_succ hw
          exact ih .maybeInvalid inner pt hwi ht
        | unit | bool | u8 | void | pair _ _ | struct2 _ _ _ | enum _ _ => contradiction
    | validOnly =>
      cases v with
      | invalid => contradiction
      | unit =>
        cases t <;> first | contradiction | trivial
      | bool b =>
        cases t <;> first | contradiction | trivial
      | u8 n =>
        cases t <;> first | contradiction | exact ht
      | pair v1 v2 =>
        cases t with
        | pair a b =>
          have hwa : tyWeight a ≤ w' := le_left_of_one_add_add hw
          have hwb : tyWeight b ≤ w' := le_right_of_one_add_add hw
          exact ⟨ih .validOnly a v1 hwa ht.1, ih .validOnly b v2 hwb ht.2⟩
        | struct2 a b bVis =>
          have hwa : tyWeight a ≤ w' := le_left_of_one_add_add hw
          have hwb : tyWeight b ≤ w' := le_right_of_one_add_add hw
          cases bVis with
          | true => exact ⟨ih .validOnly a v1 hwa ht.1, ih .validOnly b v2 hwb ht.2⟩
          | false =>
            dsimp only [VisibleWellTyped]
            cases he : tyIsEmpty b with
            | true =>
              simp only [ite_true]
              exact ⟨ih .validOnly a v1 hwa ht.1,
                visibleWellTyped_valid_to_maybe (ih .validOnly b v2 hwb ht.2)⟩
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              exact ⟨ih .validOnly a v1 hwa ht.1, ih .validOnly b v2 hwb ht.2⟩
        | unit | bool | u8 | void | enum _ _ | ref _ => contradiction
      | ctor idx sub =>
        cases t with
        | enum variants nonExh =>
          rcases ht with ⟨pt, hget, hsub⟩
          have hsum : tyWeight pt ≤ tyWeightList variants :=
            tyWeight_le_tyWeightList_of_get? hget
          change 1 + tyWeightList variants ≤ w' + 1 at hw
          rw [Nat.add_comm 1 (tyWeightList variants)] at hw
          have hwpt : tyWeight pt ≤ w' := Nat.le_trans hsum (Nat.le_of_succ_le_succ hw)
          exact ⟨pt, hget, ih .validOnly pt sub hwpt hsub⟩
        | unit | bool | u8 | void | pair _ _ | struct2 _ _ _ | ref _ => contradiction
      | hiddenCtor _ =>
        cases t with
        | enum _ nonExh => cases nonExh <;> first | contradiction | trivial
        | unit | bool | u8 | void | pair _ _ | struct2 _ _ _ | ref _ => contradiction
      | ref pt =>
        cases t with
        | ref inner =>
          have hwi : tyWeight inner ≤ w' := by
            change 1 + tyWeight inner ≤ w' + 1 at hw
            rw [Nat.add_comm 1 (tyWeight inner)] at hw
            exact Nat.le_of_succ_le_succ hw
          exact ih .maybeInvalid inner pt hwi ht
        | unit | bool | u8 | void | pair _ _ | struct2 _ _ _ | enum _ _ => contradiction

/-- Physical `TrueWellTyped` always implies `VisibleWellTyped`. -/
theorem trueWellTyped_implies_visible {val : PlaceValidity} {t : Ty} {v : Val}
    (ht : TrueWellTyped val t v) : VisibleWellTyped val t v :=
  trueWellTyped_implies_visible_bound (tyWeight t) val t v (Nat.le_refl (tyWeight t)) ht

/-- Under `.validOnly`, `.void` has no inhabitants. -/
theorem visibleWellTyped_void_validOnly_false {v : Val}
    (hv : VisibleWellTyped .validOnly .void v) : False := by
  cases v <;> contradiction

/-- Under `.validOnly`, an empty closed enum `.enum [] false` has no inhabitants. -/
theorem visibleWellTyped_empty_enum_validOnly_false {v : Val}
    (hv : VisibleWellTyped .validOnly (.enum [] false) v) : False := by
  cases v with
  | ctor idx sub =>
    rcases hv with ⟨pt, hget, _⟩
    cases idx <;> contradiction
  | invalid | unit | bool _ | u8 _ | pair _ _ | hiddenCtor _ | ref _ => contradiction

/-- Under `.validOnly`, `.ref .void` IS inhabited by `Val.ref Val.invalid`
(`"references are always considered inhabited"`, `check_match.rs:1312-1316`). -/
theorem visibleWellTyped_ref_void_inhabited :
    VisibleWellTyped .validOnly (.ref .void) (.ref .invalid) := by
  trivial

/-- If `tyIsEmpty t = true`, then `t` has no `VisibleWellTyped .validOnly` inhabitant. -/
theorem tyIsEmpty_sound_bound :
    ∀ (w : Nat) (t : Ty) (v : Val),
      tyWeight t ≤ w →
      tyIsEmpty t = true →
      VisibleWellTyped .validOnly t v →
      False := by
  intro w
  induction w with
  | zero =>
    intro t _ hw _ _
    exact False.elim (Nat.not_succ_le_zero 0 (Nat.le_trans (tyWeight_pos t) hw))
  | succ w' ih =>
    intro t v hw he hv
    cases t with
    | unit => contradiction
    | bool => contradiction
    | u8 => contradiction
    | ref _ => contradiction
    | void => exact visibleWellTyped_void_validOnly_false hv
    | pair a b =>
      cases v with
      | pair v1 v2 =>
        have hwa : tyWeight a ≤ w' := le_left_of_one_add_add hw
        have hwb : tyWeight b ≤ w' := le_right_of_one_add_add hw
        rcases boolOr_eq_true he with ha | hb
        · exact ih a v1 hwa ha hv.1
        · exact ih b v2 hwb hb hv.2
      | invalid | unit | bool _ | u8 _ | ctor _ _ | hiddenCtor _ | ref _ => contradiction
    | struct2 a b bVis =>
      cases v with
      | pair v1 v2 =>
        have hwa : tyWeight a ≤ w' := le_left_of_one_add_add hw
        have hwb : tyWeight b ≤ w' := le_right_of_one_add_add hw
        cases bVis with
        | false =>
          rcases boolOr_eq_true he with ha | hf
          · exact ih a v1 hwa ha hv.1
          · contradiction
        | true =>
          rcases boolOr_eq_true he with ha | htb
          · exact ih a v1 hwa ha hv.1
          · exact ih b v2 hwb htb hv.2
      | invalid | unit | bool _ | u8 _ | ctor _ _ | hiddenCtor _ | ref _ => contradiction
    | enum variants nonExh =>
      rcases boolAnd_eq_true he with ⟨hne, hall⟩
      have hneF : nonExh = false := boolNot_eq_true hne
      cases v with
      | ctor idx sub =>
        rcases hv with ⟨pt, hget, hsub⟩
        have hsum : tyWeight pt ≤ tyWeightList variants :=
          tyWeight_le_tyWeightList_of_get? hget
        change 1 + tyWeightList variants ≤ w' + 1 at hw
        rw [Nat.add_comm 1 (tyWeightList variants)] at hw
        have hwpt : tyWeight pt ≤ w' := Nat.le_trans hsum (Nat.le_of_succ_le_succ hw)
        have hptEmpty : tyIsEmpty pt = true :=
          tyIsEmpty_of_tyIsEmptyList hall hget
        exact ih pt sub hwpt hptEmpty hsub
      | hiddenCtor _ =>
        rw [hneF] at hv
        contradiction
      | invalid | unit | bool _ | u8 _ | pair _ _ | ref _ => contradiction

/-- Soundness of `tyIsEmpty`: empty types admit zero `.validOnly` inhabitants. -/
theorem tyIsEmpty_sound {t : Ty} {v : Val}
    (he : tyIsEmpty t = true) (hv : VisibleWellTyped .validOnly t v) : False :=
  tyIsEmpty_sound_bound (tyWeight t) t v (Nat.le_refl (tyWeight t)) he hv


/-! ## Section 3: `IntRange` Partitioning, `Ctor`, `CtorSet`, and `IntRange.split` Soundness -/

/-- Inclusive integer interval `[lo, hi]` representing scalar literal or range patterns
(`rustc_pattern_analysis::constructor::IntRange`). -/
structure IntRange where
  lo : Nat
  hi : Nat

/-- Construct a well-formed singleton range `[x, x]`. -/
noncomputable def IntRange.singleton (x : Nat) : IntRange :=
  { lo := x, hi := x }

/-- Decide membership `n ∈ [r.lo, r.hi]`. -/
noncomputable def IntRange.contains (r : IntRange) (n : Nat) : Bool :=
  natBle r.lo n && natBle n r.hi

/-- Decide subrange inclusion `sub ⊆ sup`. -/
noncomputable def IntRange.isSubrange (sub sup : IntRange) : Bool :=
  natBle sup.lo sub.lo && natBle sub.hi sup.hi

/-- Specification of `IntRange.contains`. -/
theorem intRange_contains_iff (r : IntRange) (n : Nat) :
    r.contains n = true ↔ r.lo ≤ n ∧ n ≤ r.hi := by
  unfold IntRange.contains
  constructor
  · intro h
    rcases boolAnd_eq_true h with ⟨h1, h2⟩
    exact ⟨(natBle_iff_le r.lo n).mp h1, (natBle_iff_le n r.hi).mp h2⟩
  · intro ⟨h1, h2⟩
    exact boolAnd_intro ((natBle_iff_le r.lo n).mpr h1) ((natBle_iff_le n r.hi).mpr h2)

/-- Specification of `IntRange.isSubrange`. -/
theorem intRange_isSubrange_iff (sub sup : IntRange) :
    sub.isSubrange sup = true ↔ sup.lo ≤ sub.lo ∧ sub.hi ≤ sup.hi := by
  unfold IntRange.isSubrange
  constructor
  · intro h
    rcases boolAnd_eq_true h with ⟨h1, h2⟩
    exact ⟨(natBle_iff_le sup.lo sub.lo).mp h1, (natBle_iff_le sub.hi sup.hi).mp h2⟩
  · intro ⟨h1, h2⟩
    exact boolAnd_intro ((natBle_iff_le sup.lo sub.lo).mpr h1) ((natBle_iff_le sub.hi sup.hi).mpr h2)

/-- One sub-interval produced during `IntRange` splitting (`Presence::Seen` vs `Unseen`). -/
structure RangePart where
  seen : Bool
  lo : Nat
  hi : Nat

/-- Insert one column range `r` into an existing interval `p`, splitting both `seen` and `unseen`
intervals at `r`'s endpoints so no output interval straddles any boundary of `r`
(`IntRange::split`, `constructor.rs:370-414`). -/
noncomputable def insertRangeIntoPart (r : IntRange) (p : RangePart) : List RangePart :=
  if natBlt r.hi r.lo || natBlt r.hi p.lo || natBlt p.hi r.lo then
    [p]
  else
    let left : List RangePart :=
      if natBlt p.lo r.lo then [{ seen := p.seen, lo := p.lo, hi := r.lo - 1 }] else []
    let mid : List RangePart :=
      [{ seen := true, lo := natMax p.lo r.lo, hi := natMin p.hi r.hi }]
    let right : List RangePart :=
      if natBlt r.hi p.hi then [{ seen := p.seen, lo := r.hi + 1, hi := p.hi }] else []
    left ++ mid ++ right

/-- Insert range `r` across all intervals in `parts`. -/
noncomputable def insertRangeIntoParts (r : IntRange) : List RangePart → List RangePart
  | [] => []
  | p :: ps => insertRangeIntoPart r p ++ insertRangeIntoParts r ps

/-- Fold all column ranges over `[lo, hi]` starting from `[{ seen := false, lo, hi }]`. -/
noncomputable def splitIntRangesAux (parts : List RangePart) : List IntRange → List RangePart
  | [] => parts
  | r :: rs => splitIntRangesAux (insertRangeIntoParts r parts) rs

/-- Partition `[lo, hi]` against a list of column ranges `rs`. -/
noncomputable def splitIntRanges (lo hi : Nat) (rs : List IntRange) : List RangePart :=
  splitIntRangesAux [{ seen := false, lo := lo, hi := hi }] rs

/-- Semantic invariant for a partition `parts` of `[baseLo, baseHi]` relative to `seenRs`:
1. Every `p ∈ parts` is non-empty (`p.lo ≤ p.hi`) and lies within `[baseLo, baseHi]`.
2. Every `n ∈ [baseLo, baseHi]` belongs to some `p ∈ parts`.
3. For every `p ∈ parts`, if `p.seen = true` then `∃ r ∈ seenRs, r.lo ≤ p.lo ∧ p.hi ≤ r.hi`.
4. For every `p ∈ parts`, if `p.seen = false` then every `r ∈ seenRs` is disjoint from `[p.lo, p.hi]`.
5. Sharp boundary splitting: for every `p ∈ parts` and `r ∈ seenRs`, either `p` lies wholly
   inside `r` (`r.lo ≤ p.lo ∧ p.hi ≤ r.hi`) or `p` is wholly disjoint from `r` (`IntRange.split`,
   `constructor.rs:370-414`). -/
noncomputable def PartsInvariant
    (baseLo baseHi : Nat) (seenRs : List IntRange) (parts : List RangePart) : Prop :=
  (∀ p, p ∈ parts → baseLo ≤ p.lo ∧ p.lo ≤ p.hi ∧ p.hi ≤ baseHi) ∧
  (∀ n, baseLo ≤ n → n ≤ baseHi → ∃ p, p ∈ parts ∧ p.lo ≤ n ∧ n ≤ p.hi) ∧
  (∀ p, p ∈ parts → p.seen = true → ∃ r, r ∈ seenRs ∧ r.lo ≤ p.lo ∧ p.hi ≤ r.hi) ∧
  (∀ p, p ∈ parts → p.seen = false → ∀ r, r ∈ seenRs → ∀ n, p.lo ≤ n → n ≤ p.hi →
    r.contains n = false) ∧
  (∀ p, p ∈ parts → ∀ r, r ∈ seenRs →
    (r.lo ≤ p.lo ∧ p.hi ≤ r.hi) ∨ (∀ n, p.lo ≤ n → n ≤ p.hi → r.contains n = false))

/-- Base partition invariant on `[{ seen := false, lo, hi }]` when `lo ≤ hi`. -/
theorem partsInvariant_init {lo hi : Nat} (hle : lo ≤ hi) :
    PartsInvariant lo hi [] [{ seen := false, lo := lo, hi := hi }] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact ⟨Nat.le_refl lo, hle, Nat.le_refl hi⟩
    · exact False.elim (List.not_mem_nil hp')
  · intro n hn1 hn2
    exact ⟨{ seen := false, lo := lo, hi := hi }, List.mem_cons_self, hn1, hn2⟩
  · intro p hp _
    rcases List.mem_cons.mp hp with rfl | hp'
    · contradiction
    · exact False.elim (List.not_mem_nil hp')
  · intro p _ _ r hr
    exact False.elim (List.not_mem_nil hr)
  · intro p _ r hr
    exact False.elim (List.not_mem_nil hr)

/-- Helper: `insertRangeIntoPart r p` preserves bounds, coverage, seen/unseen invariants, and
sharp boundary splitting against `r :: seenRs`. -/
theorem insertRangeIntoPart_inv {baseLo baseHi : Nat} {seenRs : List IntRange}
    (r : IntRange) (p : RangePart)
    (hpBounds : baseLo ≤ p.lo ∧ p.lo ≤ p.hi ∧ p.hi ≤ baseHi)
    (hpSeen : p.seen = true → ∃ r0, r0 ∈ seenRs ∧ r0.lo ≤ p.lo ∧ p.hi ≤ r0.hi)
    (hpUnseen : p.seen = false → ∀ r0, r0 ∈ seenRs → ∀ n, p.lo ≤ n → n ≤ p.hi →
      IntRange.contains r0 n = false)
    (hpSharp : ∀ r0, r0 ∈ seenRs →
      (r0.lo ≤ p.lo ∧ p.hi ≤ r0.hi) ∨ (∀ n, p.lo ≤ n → n ≤ p.hi → IntRange.contains r0 n = false)) :
    (∀ q, q ∈ insertRangeIntoPart r p → baseLo ≤ q.lo ∧ q.lo ≤ q.hi ∧ q.hi ≤ baseHi) ∧
    (∀ n, p.lo ≤ n → n ≤ p.hi → ∃ q, q ∈ insertRangeIntoPart r p ∧ q.lo ≤ n ∧ n ≤ q.hi) ∧
    (∀ q, q ∈ insertRangeIntoPart r p → q.seen = true →
      ∃ r0, r0 ∈ r :: seenRs ∧ r0.lo ≤ q.lo ∧ q.hi ≤ r0.hi) ∧
    (∀ q, q ∈ insertRangeIntoPart r p → q.seen = false →
      ∀ r0, r0 ∈ r :: seenRs → ∀ n, q.lo ≤ n → n ≤ q.hi → IntRange.contains r0 n = false) ∧
    (∀ q, q ∈ insertRangeIntoPart r p → ∀ r0, r0 ∈ r :: seenRs →
      (r0.lo ≤ q.lo ∧ q.hi ≤ r0.hi) ∨ (∀ n, q.lo ≤ n → n ≤ q.hi → IntRange.contains r0 n = false)) := by
  unfold insertRangeIntoPart
  cases hskip : (natBlt r.hi r.lo || natBlt r.hi p.lo || natBlt p.hi r.lo) with
  | true =>
    simp only [ite_true]
    have hdisjR : ∀ n, p.lo ≤ n → n ≤ p.hi → IntRange.contains r n = false := by
      intro n hn1 hn2
      cases hc : IntRange.contains r n with
      | false => rfl
      | true =>
        rcases (intRange_contains_iff r n).mp hc with ⟨hrlo, hrhi⟩
        rcases boolOr_eq_true hskip with h12 | hpBeforeR
        · rcases boolOr_eq_true h12 with hrEmpty | hrBeforeP
          · have hrLt : r.hi < r.lo := (natBlt_iff_lt r.hi r.lo).mp hrEmpty
            exact False.elim (Nat.not_le_of_gt hrLt (Nat.le_trans hrlo hrhi))
          · have hrLtP : r.hi < p.lo := (natBlt_iff_lt r.hi p.lo).mp hrBeforeP
            exact False.elim (Nat.not_le_of_gt hrLtP (Nat.le_trans hn1 hrhi))
        · have hpLtR : p.hi < r.lo := (natBlt_iff_lt p.hi r.lo).mp hpBeforeR
          exact False.elim (Nat.not_le_of_gt hpLtR (Nat.le_trans hrlo hn2))
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.mp hq with hEq | hq'
      · cases hEq; exact hpBounds
      · exact False.elim (List.not_mem_nil hq')
    · intro n hn1 hn2
      exact ⟨p, List.mem_cons_self, hn1, hn2⟩
    · intro q hq hqt
      rcases List.mem_cons.mp hq with hEq | hq'
      · cases hEq
        rcases hpSeen hqt with ⟨r0, hm, hlo, hhi⟩
        exact ⟨r0, List.mem_cons_of_mem r hm, hlo, hhi⟩
      · exact False.elim (List.not_mem_nil hq')
    · intro q hq hqf r0 hr0 n hn1 hn2
      rcases List.mem_cons.mp hq with hEq | hq'
      · cases hEq
        rcases List.mem_cons.mp hr0 with hEqR | hm
        · cases hEqR; exact hdisjR n hn1 hn2
        · exact hpUnseen hqf r0 hm n hn1 hn2
      · exact False.elim (List.not_mem_nil hq')
    · intro q hq r0 hr0
      rcases List.mem_cons.mp hq with hEq | hq'
      · cases hEq
        rcases List.mem_cons.mp hr0 with hEqR | hm
        · cases hEqR; exact Or.inr hdisjR
        · exact hpSharp r0 hm
      · exact False.elim (List.not_mem_nil hq')
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rcases boolOr_eq_false.mp hskip with ⟨h12, hpNotBeforeR⟩
    rcases boolOr_eq_false.mp h12 with ⟨hrNotEmpty, hrNotBeforeP⟩
    have hrLe : r.lo ≤ r.hi := (natBlt_false_iff_le r.hi r.lo).mp hrNotEmpty
    have hpGeRlo : r.lo ≤ p.hi := (natBlt_false_iff_le p.hi r.lo).mp hpNotBeforeR
    have hrGePlo : p.lo ≤ r.hi := (natBlt_false_iff_le r.hi p.lo).mp hrNotBeforeP
    have hMidLe : natMax p.lo r.lo ≤ natMin p.hi r.hi := by
      apply natMax_le_of_le
      · exact natMin_ge_of_le hpBounds.2.1 hrGePlo
      · exact natMin_ge_of_le hpGeRlo hrLe
    have hMidBounds : baseLo ≤ natMax p.lo r.lo ∧ natMax p.lo r.lo ≤ natMin p.hi r.hi ∧
        natMin p.hi r.hi ≤ baseHi := by
      refine ⟨Nat.le_trans hpBounds.1 (natMax_ge_left p.lo r.lo), hMidLe, ?_⟩
      exact Nat.le_trans (natMin_le_left p.hi r.hi) hpBounds.2.2
    have hSubP : ∀ (q : RangePart), q ∈
        (if natBlt p.lo r.lo then [{ seen := p.seen, lo := p.lo, hi := r.lo - 1 }] else []) ++
        [{ seen := true, lo := natMax p.lo r.lo, hi := natMin p.hi r.hi }] ++
        (if natBlt r.hi p.hi then [{ seen := p.seen, lo := r.hi + 1, hi := p.hi }] else []) →
        p.lo ≤ q.lo ∧ q.lo ≤ q.hi ∧ q.hi ≤ p.hi := by
      intro q hq
      rcases List.mem_append.mp hq with hLM | hR
      · rcases List.mem_append.mp hLM with hL | hM
        · cases hl : natBlt p.lo r.lo with
          | false => rw [hl] at hL; simp at hL
          | true =>
            rw [hl] at hL; simp only [ite_true, List.mem_singleton] at hL
            subst hL
            have hlt : p.lo < r.lo := (natBlt_iff_lt p.lo r.lo).mp hl
            exact ⟨Nat.le_refl p.lo, Nat.le_pred_of_lt hlt, Nat.le_trans (Nat.pred_le r.lo) hpGeRlo⟩
        · simp only [List.mem_singleton] at hM
          subst hM
          exact ⟨natMax_ge_left p.lo r.lo, hMidLe, natMin_le_left p.hi r.hi⟩
      · cases hr : natBlt r.hi p.hi with
        | false => rw [hr] at hR; simp at hR
        | true =>
          rw [hr] at hR; simp only [ite_true, List.mem_singleton] at hR
          subst hR
          have hlt : r.hi < p.hi := (natBlt_iff_lt r.hi p.hi).mp hr
          exact ⟨Nat.le_trans hrGePlo (Nat.le_succ r.hi), hlt, Nat.le_refl p.hi⟩
    have hSharpOld : ∀ (q : RangePart), p.lo ≤ q.lo → q.hi ≤ p.hi → ∀ r0, r0 ∈ seenRs →
        (r0.lo ≤ q.lo ∧ q.hi ≤ r0.hi) ∨
        (∀ n, q.lo ≤ n → n ≤ q.hi → IntRange.contains r0 n = false) := by
      intro q hq1 hq2 r0 hr0
      rcases hpSharp r0 hr0 with ⟨h1, h2⟩ | hdisj
      · exact Or.inl ⟨Nat.le_trans h1 hq1, Nat.le_trans hq2 h2⟩
      · exact Or.inr (fun n hn1 hn2 => hdisj n (Nat.le_trans hq1 hn1) (Nat.le_trans hn2 hq2))
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro q hq
      rcases hSubP q hq with ⟨h1, h2, h3⟩
      exact ⟨Nat.le_trans hpBounds.1 h1, h2, Nat.le_trans h3 hpBounds.2.2⟩
    · intro n hn1 hn2
      cases hnl : natBlt n r.lo with
      | true =>
        have hnLt : n < r.lo := (natBlt_iff_lt n r.lo).mp hnl
        have hpLt : p.lo < r.lo := Nat.lt_of_le_of_lt hn1 hnLt
        have hblt : natBlt p.lo r.lo = true := (natBlt_iff_lt p.lo r.lo).mpr hpLt
        refine ⟨{ seen := p.seen, lo := p.lo, hi := r.lo - 1 }, ?_, hn1, Nat.le_pred_of_lt hnLt⟩
        apply List.mem_append_left
        apply List.mem_append_left
        rw [hblt]; simp
      | false =>
        have hGeRlo : r.lo ≤ n := (natBlt_false_iff_le n r.lo).mp hnl
        cases hnr : natBlt r.hi n with
        | true =>
          have hnGt : r.hi < n := (natBlt_iff_lt r.hi n).mp hnr
          have hpGt : r.hi < p.hi := Nat.lt_of_lt_of_le hnGt hn2
          have hblt : natBlt r.hi p.hi = true := (natBlt_iff_lt r.hi p.hi).mpr hpGt
          refine ⟨{ seen := p.seen, lo := r.hi + 1, hi := p.hi }, ?_, hnGt, hn2⟩
          apply List.mem_append_right
          rw [hblt]; simp
        | false =>
          have hLeRhi : n ≤ r.hi := (natBlt_false_iff_le r.hi n).mp hnr
          refine ⟨{ seen := true, lo := natMax p.lo r.lo, hi := natMin p.hi r.hi }, ?_, ?_, ?_⟩
          · apply List.mem_append_left
            apply List.mem_append_right
            exact List.mem_cons_self
          · exact natMax_le_of_le hn1 hGeRlo
          · exact natMin_ge_of_le hn2 hLeRhi
    · intro q hq hqt
      rcases List.mem_append.mp hq with hLM | hR
      · rcases List.mem_append.mp hLM with hL | hM
        · cases hl : natBlt p.lo r.lo with
          | false => rw [hl] at hL; simp at hL
          | true =>
            rw [hl] at hL; simp only [ite_true, List.mem_singleton] at hL
            subst hL
            have hlt : p.lo < r.lo := (natBlt_iff_lt p.lo r.lo).mp hl
            rcases hpSeen hqt with ⟨r0, hm, hlo, hhi⟩
            exact ⟨r0, List.mem_cons_of_mem r hm, hlo,
              Nat.le_trans (Nat.le_trans (Nat.pred_le r.lo) hpGeRlo) hhi⟩
        · simp only [List.mem_singleton] at hM
          subst hM
          exact ⟨r, List.mem_cons_self, natMax_ge_right p.lo r.lo, natMin_le_right p.hi r.hi⟩
      · cases hr : natBlt r.hi p.hi with
        | false => rw [hr] at hR; simp at hR
        | true =>
          rw [hr] at hR; simp only [ite_true, List.mem_singleton] at hR
          subst hR
          rcases hpSeen hqt with ⟨r0, hm, hlo, hhi⟩
          exact ⟨r0, List.mem_cons_of_mem r hm,
            Nat.le_trans hlo (Nat.le_trans hrGePlo (Nat.le_succ r.hi)), hhi⟩
    · intro q hq hqf r0 hr0 n hn1 hn2
      have handleUnseen :
          p.seen = false →
          (q.lo ≥ p.lo ∧ q.hi ≤ p.hi) →
          (∀ m, q.lo ≤ m → m ≤ q.hi → IntRange.contains r m = false) →
          IntRange.contains r0 n = false := by
        intro hpF ⟨hqlo, hqhi⟩ hdisj
        rcases List.mem_cons.mp hr0 with hEqR | hm
        · cases hEqR; exact hdisj n hn1 hn2
        · exact hpUnseen hpF r0 hm n (Nat.le_trans hqlo hn1) (Nat.le_trans hn2 hqhi)
      rcases List.mem_append.mp hq with hLM | hR
      · rcases List.mem_append.mp hLM with hL | hM
        · cases hl : natBlt p.lo r.lo with
          | false => rw [hl] at hL; simp at hL
          | true =>
            rw [hl] at hL; simp only [ite_true, List.mem_singleton] at hL
            subst hL
            have hlt : p.lo < r.lo := (natBlt_iff_lt p.lo r.lo).mp hl
            apply handleUnseen hqf
            · exact ⟨Nat.le_refl p.lo, Nat.le_trans (Nat.pred_le r.lo) hpGeRlo⟩
            · intro m _ hmhi
              cases hc : IntRange.contains r m with
              | false => rfl
              | true =>
                rcases (intRange_contains_iff r m).mp hc with ⟨hrlo, _⟩
                have hmLt : m < r.lo := Nat.lt_of_le_of_lt hmhi (Nat.pred_lt_of_lt hlt)
                exact False.elim (Nat.not_le_of_gt hmLt hrlo)
        · simp only [List.mem_singleton] at hM
          subst hM; contradiction
      · cases hr : natBlt r.hi p.hi with
        | false => rw [hr] at hR; simp at hR
        | true =>
          rw [hr] at hR; simp only [ite_true, List.mem_singleton] at hR
          subst hR
          have hlt : r.hi < p.hi := (natBlt_iff_lt r.hi p.hi).mp hr
          apply handleUnseen hqf
          · exact ⟨Nat.le_trans hrGePlo (Nat.le_succ r.hi), Nat.le_refl p.hi⟩
          · intro m hmlo _
            cases hc : IntRange.contains r m with
            | false => rfl
            | true =>
              rcases (intRange_contains_iff r m).mp hc with ⟨_, hrhi⟩
              exact False.elim (Nat.not_le_of_gt hmlo hrhi)
    · intro q hq r0 hr0
      rcases hSubP q hq with ⟨hq1, _, hq2⟩
      rcases List.mem_cons.mp hr0 with hEqR | hm
      · cases hEqR
        rcases List.mem_append.mp hq with hLM | hR
        · rcases List.mem_append.mp hLM with hL | hM
          · cases hl : natBlt p.lo r.lo with
            | false => rw [hl] at hL; simp at hL
            | true =>
              rw [hl] at hL; simp only [ite_true, List.mem_singleton] at hL
              subst hL
              have hlt : p.lo < r.lo := (natBlt_iff_lt p.lo r.lo).mp hl
              refine Or.inr ?_
              intro n _ hnhi
              cases hc : IntRange.contains r n with
              | false => rfl
              | true =>
                rcases (intRange_contains_iff r n).mp hc with ⟨hrlo, _⟩
                have hnLt : n < r.lo := Nat.lt_of_le_of_lt hnhi (Nat.pred_lt_of_lt hlt)
                exact False.elim (Nat.not_le_of_gt hnLt hrlo)
          · simp only [List.mem_singleton] at hM
            subst hM
            exact Or.inl ⟨natMax_ge_right p.lo r.lo, natMin_le_right p.hi r.hi⟩
        · cases hr : natBlt r.hi p.hi with
          | false => rw [hr] at hR; simp at hR
          | true =>
            rw [hr] at hR; simp only [ite_true, List.mem_singleton] at hR
            subst hR
            refine Or.inr ?_
            intro n hnlo _
            cases hc : IntRange.contains r n with
            | false => rfl
            | true =>
              rcases (intRange_contains_iff r n).mp hc with ⟨_, hrhi⟩
              exact False.elim (Nat.not_le_of_gt hnlo hrhi)
      · exact hSharpOld q hq1 hq2 r0 hm

/-- Membership decomposition for `insertRangeIntoParts`: every output element comes from
`insertRangeIntoPart r p` for some `p ∈ parts`, and conversely. -/
theorem mem_insertRangeIntoParts_iff (r : IntRange) (parts : List RangePart) (q : RangePart) :
    q ∈ insertRangeIntoParts r parts ↔ ∃ p, p ∈ parts ∧ q ∈ insertRangeIntoPart r p := by
  induction parts with
  | nil =>
    constructor
    · intro h; exact False.elim (List.not_mem_nil h)
    · intro ⟨p, hp, _⟩; exact False.elim (List.not_mem_nil hp)
  | cons p ps ih =>
    constructor
    · intro h
      rcases List.mem_append.mp h with h1 | h2
      · exact ⟨p, List.mem_cons_self, h1⟩
      · rcases ih.mp h2 with ⟨p', hp', hq'⟩
        exact ⟨p', List.mem_cons_of_mem p hp', hq'⟩
    · intro ⟨p', hp', hq'⟩
      rcases List.mem_cons.mp hp' with rfl | hps
      · exact List.mem_append_left _ hq'
      · exact List.mem_append_right _ (ih.mpr ⟨p', hps, hq'⟩)

/-- `insertRangeIntoParts r` preserves `PartsInvariant` while extending `seenRs` with `r`. -/
theorem insertRangeIntoParts_inv {baseLo baseHi : Nat} {seenRs : List IntRange}
    {parts : List RangePart} (r : IntRange)
    (hinv : PartsInvariant baseLo baseHi seenRs parts) :
    PartsInvariant baseLo baseHi (r :: seenRs) (insertRangeIntoParts r parts) := by
  rcases hinv with ⟨hBounds, hCov, hSeen, hUnseen, hSharp⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    rcases (mem_insertRangeIntoParts_iff r parts q).mp hq with ⟨p, hp, hqp⟩
    exact (insertRangeIntoPart_inv r p (hBounds p hp) (hSeen p hp) (hUnseen p hp) (hSharp p hp)).1 q hqp
  · intro n hn1 hn2
    rcases hCov n hn1 hn2 with ⟨p, hp, hlo, hhi⟩
    rcases (insertRangeIntoPart_inv r p (hBounds p hp) (hSeen p hp) (hUnseen p hp) (hSharp p hp)).2.1
      n hlo hhi with ⟨q, hqp, qlo, qhi⟩
    exact ⟨q, (mem_insertRangeIntoParts_iff r parts q).mpr ⟨p, hp, hqp⟩, qlo, qhi⟩
  · intro q hq hqt
    rcases (mem_insertRangeIntoParts_iff r parts q).mp hq with ⟨p, hp, hqp⟩
    exact (insertRangeIntoPart_inv r p (hBounds p hp) (hSeen p hp) (hUnseen p hp)
      (hSharp p hp)).2.2.1 q hqp hqt
  · intro q hq hqf
    rcases (mem_insertRangeIntoParts_iff r parts q).mp hq with ⟨p, hp, hqp⟩
    exact (insertRangeIntoPart_inv r p (hBounds p hp) (hSeen p hp) (hUnseen p hp)
      (hSharp p hp)).2.2.2.1 q hqp hqf
  · intro q hq r0 hr0
    rcases (mem_insertRangeIntoParts_iff r parts q).mp hq with ⟨p, hp, hqp⟩
    exact (insertRangeIntoPart_inv r p (hBounds p hp) (hSeen p hp) (hUnseen p hp)
      (hSharp p hp)).2.2.2.2 q hqp r0 hr0

/-- Inductive preservation of `PartsInvariant` across a list of column ranges. -/
theorem splitIntRangesAux_inv {baseLo baseHi : Nat} :
    ∀ (rs seenRs : List IntRange) (parts : List RangePart),
      PartsInvariant baseLo baseHi seenRs parts →
      ∃ fullSeen, (∀ r, r ∈ fullSeen ↔ r ∈ rs ∨ r ∈ seenRs) ∧
        PartsInvariant baseLo baseHi fullSeen (splitIntRangesAux parts rs) := by
  intro rs
  induction rs with
  | nil =>
    intro seenRs parts hinv
    refine ⟨seenRs, ?_, hinv⟩
    intro r
    constructor
    · intro h; exact Or.inr h
    · intro h
      rcases h with h1 | h2
      · exact False.elim (List.not_mem_nil h1)
      · exact h2
  | cons r rs' ih =>
    intro seenRs parts hinv
    have hstep := insertRangeIntoParts_inv r hinv
    rcases ih (r :: seenRs) (insertRangeIntoParts r parts) hstep with ⟨fullSeen, hmem, hinv'⟩
    refine ⟨fullSeen, ?_, hinv'⟩
    intro r0
    constructor
    · intro h
      rcases (hmem r0).mp h with h1 | h2
      · exact Or.inl (List.mem_cons_of_mem r h1)
      · rcases List.mem_cons.mp h2 with rfl | h3
        · exact Or.inl List.mem_cons_self
        · exact Or.inr h3
    · intro h
      apply (hmem r0).mpr
      rcases h with h1 | h2
      · rcases List.mem_cons.mp h1 with rfl | h3
        · exact Or.inr List.mem_cons_self
        · exact Or.inl h3
      · exact Or.inr (List.mem_cons_of_mem r h2)

/-- **IntRange Splitting Soundness & Completeness (`IntRange::split`):**
For any `lo ≤ hi` and any list `rs` of column integer ranges:
1. Every `p ∈ splitIntRanges lo hi rs` is non-empty and inside `[lo, hi]`.
2. Every `n ∈ [lo, hi]` falls into some partition `p ∈ splitIntRanges lo hi rs`.
3. Every `seen = true` partition is a subrange of some `r ∈ rs` (`IntRange.isSubrange = true`).
4. Every `seen = false` partition contains NO integer matched by any `r ∈ rs`.
5. Sharp boundary splitting: every partition lies wholly inside `r` or wholly outside `r` for each
   `r ∈ rs`. -/
theorem splitIntRanges_sound_and_complete {lo hi : Nat} (hle : lo ≤ hi) (rs : List IntRange) :
    PartsInvariant lo hi rs (splitIntRanges lo hi rs) := by
  unfold splitIntRanges
  rcases splitIntRangesAux_inv rs [] [{ seen := false, lo := lo, hi := hi }]
      (partsInvariant_init hle) with ⟨fullSeen, hmem, hBounds, hCov, hSeen, hUnseen, hSharp⟩
  have hiff : ∀ r, r ∈ fullSeen ↔ r ∈ rs := by
    intro r
    constructor
    · intro h
      rcases (hmem r).mp h with h1 | h2
      · exact h1
      · exact False.elim (List.not_mem_nil h2)
    · intro h; exact (hmem r).mpr (Or.inl h)
  refine ⟨hBounds, hCov, ?_, ?_, ?_⟩
  · intro p hp hqt
    rcases hSeen p hp hqt with ⟨r, hr, h1, h2⟩
    exact ⟨r, (hiff r).mp hr, h1, h2⟩
  · intro p hp hqf r hr n hn1 hn2
    exact hUnseen p hp hqf r ((hiff r).mpr hr) n hn1 hn2
  · intro p hp r hr
    exact hSharp p hp r ((hiff r).mpr hr)

/-! ## Section 4: Constructors, Patterns, `WitnessPat`, `MatrixRow`, and `splitColumnCtors` -/

/-- Constructors in `rustc_pattern_analysis` (`constructor.rs:687-740`). -/
inductive Ctor where
  | unit
  | bool (b : Bool)
  | intRange (r : IntRange)
  | pair
  | variant (idx : Nat)
  | nonExhaustive
  | ref
  | orCtor
  | wild
  | missing
  | privateUninhabited
  | never

/-- Structural equality on `Ctor`. -/
noncomputable def Ctor.beq : Ctor → Ctor → Bool
  | .unit, .unit => true
  | .bool a, .bool b => boolBeq a b
  | .intRange r1, .intRange r2 => natBeq r1.lo r2.lo && natBeq r1.hi r2.hi
  | .pair, .pair => true
  | .variant i, .variant j => natBeq i j
  | .nonExhaustive, .nonExhaustive => true
  | .ref, .ref => true
  | .orCtor, .orCtor => true
  | .wild, .wild => true
  | .missing, .missing => true
  | .privateUninhabited, .privateUninhabited => true
  | .never, .never => true
  | _, _ => false

/-- Check whether `c` is `Ctor.nonExhaustive` (`constructor.rs:771-773`). -/
noncomputable def Ctor.isNonExhaustive : Ctor → Bool
  | .nonExhaustive => true
  | _ => false

/-- Constructor inclusion `Ctor.isCoveredBy self other` (`constructor.rs:811-831`):
- `(_, .wild) => true` (wildcards cover any constructor)
- `(.privateUninhabited, _) => true` (`PrivateUninhabited` skips everything)
- `(.missing | .nonExhaustive, _) => false` (only wildcard matches special sentinels)
- `(.intRange sub, .intRange sup) => sub.isSubrange sup` -/
noncomputable def Ctor.isCoveredBy : Ctor → Ctor → Bool
  | _, .wild => true
  | .privateUninhabited, _ => true
  | .missing, _ => false
  | .nonExhaustive, _ => false
  | .unit, .unit => true
  | .bool a, .bool b => boolBeq a b
  | .intRange sub, .intRange sup => sub.isSubrange sup
  | .pair, .pair => true
  | .variant i, .variant j => natBeq i j
  | .ref, .ref => true
  | _, _ => false

/-- Surface / lowered pattern AST (`DeconstructedPat` + `PatKind::Or`). -/
inductive Pat where
  | wild
  | unit
  | bool (b : Bool)
  | intRange (r : IntRange)
  | pair (p1 p2 : Pat)
  | variant (idx : Nat) (sub : Pat)
  | ref (sub : Pat)
  | orPat (p1 p2 : Pat)

/-- Extract the top-level `Ctor` of a `Pat`. -/
noncomputable def Pat.headCtor : Pat → Ctor
  | .wild => .wild
  | .unit => .unit
  | .bool b => .bool b
  | .intRange r => .intRange r
  | .pair _ _ => .pair
  | .variant idx _ => .variant idx
  | .ref _ => .ref
  | .orPat _ _ => .orCtor

/-- Check whether a pattern has no top-level `orPat` constructor. -/
noncomputable def Pat.isOrFreeHead : Pat → Bool
  | .orPat _ _ => false
  | _ => true

/-- Flatten all top-level `orPat` nodes of a pattern into its alternative branches
(`PatOrWild::flatten_or_pat`, `pat.rs:216-224`). -/
noncomputable def expandHeadOrPat : Pat → List Pat
  | .orPat p1 p2 => expandHeadOrPat p1 ++ expandHeadOrPat p2
  | p => [p]

/-- Operational match semantics `Pat.matchesVal p v`:
Wildcard `_` matches any value without reading invalid data (`usefulness.rs:510-512`),
whereas every non-wildcard constructor checks the value's runtime constructor and recurses. -/
noncomputable def Pat.matchesVal : Pat → Val → Bool
  | .wild, _ => true
  | .unit, .unit => true
  | .bool b, .bool bv => boolBeq b bv
  | .intRange r, .u8 n => r.contains n
  | .pair p1 p2, .pair v1 v2 => p1.matchesVal v1 && p2.matchesVal v2
  | .variant idx sub, .ctor vIdx vSub => natBeq idx vIdx && sub.matchesVal vSub
  | .ref sub, .ref pt => sub.matchesVal pt
  | .orPat p1 p2, v => p1.matchesVal v || p2.matchesVal v
  | _, _ => false

/-- Every branch produced by `expandHeadOrPat` is or-free at its head. -/
theorem expandHeadOrPat_orFree (p : Pat) :
    ∀ q, q ∈ expandHeadOrPat p → q.isOrFreeHead = true := by
  induction p with
  | orPat p1 p2 ih1 ih2 =>
    intro q hq
    rcases List.mem_append.mp hq with h1 | h2
    · exact ih1 q h1
    · exact ih2 q h2
  | wild | unit | bool _ | intRange _ | pair _ _ | variant _ _ | ref _ =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hnil
    · rfl
    · exact False.elim (List.not_mem_nil hnil)

/-- Soundness and completeness of `expandHeadOrPat` w.r.t. `Pat.matchesVal`. -/
theorem matchesVal_expandHeadOrPat_iff (p : Pat) (v : Val) :
    p.matchesVal v = true ↔ ∃ q, q ∈ expandHeadOrPat p ∧ q.matchesVal v = true := by
  induction p with
  | orPat p1 p2 ih1 ih2 =>
    constructor
    · intro h
      rcases boolOr_eq_true h with h1 | h2
      · rcases ih1.mp h1 with ⟨q, hq, hm⟩
        exact ⟨q, List.mem_append_left _ hq, hm⟩
      · rcases ih2.mp h2 with ⟨q, hq, hm⟩
        exact ⟨q, List.mem_append_right _ hq, hm⟩
    · intro ⟨q, hq, hm⟩
      rcases List.mem_append.mp hq with h1 | h2
      · exact boolOr_intro_left (ih1.mpr ⟨q, h1, hm⟩)
      · exact boolOr_intro_right (ih2.mpr ⟨q, h2, hm⟩)
  | wild | unit | bool _ | intRange _ | pair _ _ | variant _ _ | ref _ =>
    constructor
    · intro h; exact ⟨_, List.mem_cons_self, h⟩
    · intro ⟨q, hq, hm⟩
      rcases List.mem_cons.mp hq with rfl | hnil
      · exact hm
      · exact False.elim (List.not_mem_nil hnil)

/-- Match arm with optional pattern guard (`MatchArm`, `lib.rs:128-132`). -/
structure MatchArm where
  pat : Pat
  hasGuard : Bool

/-- Row of a Maranget pattern matrix (`MatrixRow`, `usefulness.rs:1108-1153`). -/
structure MatrixRow where
  pats : List Pat
  isUnderGuard : Bool
  armIdx : Nat

/-- Construct initial `MatrixRow` from a `MatchArm` (`MatrixRow::new`, `usefulness.rs:1143-1153`). -/
noncomputable def MatrixRow.new (arm : MatchArm) (armId : Nat) : MatrixRow :=
  { pats := [arm.pat], isUnderGuard := arm.hasGuard, armIdx := armId }

/-- Build matrix rows from arms with consecutive indices. -/
noncomputable def armsToRowsAux (idx : Nat) : List MatchArm → List MatrixRow
  | [] => []
  | a :: as => MatrixRow.new a idx :: armsToRowsAux (idx + 1) as

/-- Entrypoint conversion from `List MatchArm` to initial single-column `MatrixRow`s. -/
noncomputable def armsToRows (arms : List MatchArm) : List MatrixRow :=
  armsToRowsAux 0 arms

/-- Diagnostic non-exhaustiveness witness pattern (`WitnessPat`, `pat.rs:251-287`). -/
inductive WitnessPat where
  | wild
  | unit
  | bool (b : Bool)
  | intRange (r : IntRange)
  | pair (w1 w2 : WitnessPat)
  | variant (idx : Nat) (sub : WitnessPat)
  | ref (sub : WitnessPat)
  | nonExhaustive
  | privateUninhabited
  | never

/-- Semantic matching of a `WitnessPat` against a `Val` under `PlaceValidity`:
- `.wild` and `.privateUninhabited` match any value;
- `.never` matches `.invalid` inside `.maybeInvalid` places (matching stable rustc where `WitnessPat::Never` prints `_` when `never_patterns` is disabled, `rustc.rs:869`), and matches nothing under `.validOnly`;
- `.nonExhaustive` matches `Val.hiddenCtor _` (open-world future variant). -/
noncomputable def WitnessPat.matchesVal : PlaceValidity → WitnessPat → Val → Bool
  | _, .wild, _ => true
  | _, .privateUninhabited, _ => true
  | .maybeInvalid, .never, _ => true
  | .validOnly, .never, _ => false
  | _, .unit, .unit => true
  | _, .bool b, .bool bv => boolBeq b bv
  | _, .intRange r, .u8 n => r.contains n
  | val, .pair w1 w2, .pair v1 v2 => w1.matchesVal val v1 && w2.matchesVal val v2
  | val, .variant idx sub, .ctor vIdx vSub => natBeq idx vIdx && sub.matchesVal val vSub
  | _, .ref sub, .ref pt => sub.matchesVal .maybeInvalid pt
  | _, .nonExhaustive, .hiddenCtor _ => true
  | _, _, _ => false

/-- Wildcard witness construction (`WitnessPat::wildcard`, `pat.rs:268-272`). -/
noncomputable def WitnessPat.wildcardForTy (t : Ty) : WitnessPat :=
  if tyIsEmpty t then .never else .wild

/-- Wildcard-filled constructor witness (`WitnessPat::wild_from_ctor`, `pat.rs:277-287`). -/
noncomputable def wildFromCtor (t : Ty) (c : Ctor) : WitnessPat :=
  match c with
  | .wild => WitnessPat.wildcardForTy t
  | .unit => .unit
  | .bool b => .bool b
  | .intRange r => .intRange r
  | .pair =>
    match t with
    | .pair a b => .pair (WitnessPat.wildcardForTy a) (WitnessPat.wildcardForTy b)
    | .struct2 a b true => .pair (WitnessPat.wildcardForTy a) (WitnessPat.wildcardForTy b)
    | .struct2 a _ false => .pair (WitnessPat.wildcardForTy a) .wild
    | _ => .wild
  | .variant idx =>
    match t with
    | .enum vs _ =>
      match listGet? vs idx with
      | some pt => .variant idx (WitnessPat.wildcardForTy pt)
      | none => .wild
    | _ => .wild
  | .ref =>
    match t with
    | .ref inner => .ref (WitnessPat.wildcardForTy inner)
    | _ => .wild
  | .nonExhaustive => .nonExhaustive
  | .privateUninhabited => .privateUninhabited
  | .never => .never
  | .orCtor | .missing => .wild

/-- Place metadata for one column of the Maranget matrix (`PlaceInfo`, `usefulness.rs:892-902`). -/
structure ColCtx where
  ty : Ty
  privUninhabited : Bool
  validity : PlaceValidity
  isScrutinee : Bool
  exhPatterns : Bool

/-- Visibility of an enum variant (`constructor.rs:1117-1121`, `rustc.rs:395-402`). -/
inductive VariantVis where
  | visible
  | empty

/-- Constructor universe for a type (`ConstructorSet`, `constructor.rs:987-1011`). -/
inductive CtorSet where
  | unit
  | bool
  | u8
  | pair (empty : Bool)
  | variants (vis : List VariantVis) (nonExhaustive : Bool)
  | ref
  | noConstructors

/-- Build `CtorSet` for a `Ty` (`RustcPatCtxt::ctors_for_ty`, `rustc.rs:306-436`). -/
noncomputable def ctorsForTy : Ty → CtorSet
  | .unit => .unit
  | .bool => .bool
  | .u8 => .u8
  | .void => .noConstructors
  | .pair a b => .pair (tyIsEmpty a || tyIsEmpty b)
  | .struct2 a b bVis => .pair (tyIsEmpty a || (bVis && tyIsEmpty b))
  | .enum [] false => .noConstructors
  | .enum variants nonExh =>
    .variants (variants.map (fun pt => if tyIsEmpty pt then .empty else .visible)) nonExh
  | .ref _ => .ref

/-- Output of splitting a `CtorSet` against column constructors (`SplitConstructorSet`,
`constructor.rs:1035-1039`). -/
structure SplitCtorSet where
  present : List Ctor
  missing : List Ctor
  missingEmpty : List Ctor

/-- Collect all integer ranges from a list of constructors. -/
noncomputable def collectIntRanges : List Ctor → List IntRange
  | [] => []
  | .intRange r :: cs => r :: collectIntRanges cs
  | _ :: cs => collectIntRanges cs

/-- Check whether `c` appears in `ctors` using `Ctor.beq`. -/
noncomputable def hasCtor (target : Ctor) : List Ctor → Bool
  | [] => false
  | c :: cs => Ctor.beq target c || hasCtor target cs

/-- Check whether at least one concrete non-wildcard constructor appears. -/
noncomputable def hasConcreteCtor : List Ctor → Bool
  | [] => false
  | .wild :: cs => hasConcreteCtor cs
  | _ :: _ => true

/-- Split variants across seen vs unseen (`ConstructorSet::Variants`, `constructor.rs:1104-1131`). -/
noncomputable def splitVariantsAux
    (idx : Nat) (seen : List Ctor) : List VariantVis → (List Ctor × List Ctor × List Ctor)
  | [] => ([], [], [])
  | v :: vs =>
    let (pres, miss, missEmpty) := splitVariantsAux (idx + 1) seen vs
    let ctor := Ctor.variant idx
    if hasCtor ctor seen then
      (ctor :: pres, miss, missEmpty)
    else
      match v with
      | .visible => (pres, ctor :: miss, missEmpty)
      | .empty => (pres, miss, ctor :: missEmpty)

/-- Split `CtorSet` against the column constructors (`ConstructorSet::split`, `constructor.rs:1046-1205`). -/
noncomputable def splitCtorSet (cset : CtorSet) (colCtors : List Ctor) : SplitCtorSet :=
  match cset with
  | .unit =>
    if hasConcreteCtor colCtors then
      { present := [.unit], missing := [], missingEmpty := [] }
    else
      { present := [], missing := [.unit], missingEmpty := [] }
  | .bool =>
    let seenTrue := hasCtor (.bool true) colCtors
    let seenFalse := hasCtor (.bool false) colCtors
    let pres := (if seenTrue then [.bool true] else []) ++ (if seenFalse then [.bool false] else [])
    let miss := (if seenTrue then [] else [.bool true]) ++ (if seenFalse then [] else [.bool false])
    { present := pres, missing := miss, missingEmpty := [] }
  | .u8 =>
    let parts := splitIntRanges 0 255 (collectIntRanges colCtors)
    let pres := parts.filterMap (fun p => if p.seen then some (.intRange ⟨p.lo, p.hi⟩) else none)
    let miss := parts.filterMap (fun p => if p.seen then none else some (.intRange ⟨p.lo, p.hi⟩))
    { present := pres, missing := miss, missingEmpty := [] }
  | .pair empty =>
    if hasConcreteCtor colCtors then
      { present := [.pair], missing := [], missingEmpty := [] }
    else if empty then
      { present := [], missing := [], missingEmpty := [.pair] }
    else
      { present := [], missing := [.pair], missingEmpty := [] }
  | .variants vis nonExh =>
    let (pres, miss, missEmpty) := splitVariantsAux 0 colCtors vis
    let missFinal := if nonExh then miss ++ [.nonExhaustive] else miss
    { present := pres, missing := missFinal, missingEmpty := missEmpty }
  | .ref =>
    if hasConcreteCtor colCtors then
      { present := [.ref], missing := [], missingEmpty := [] }
    else
      { present := [], missing := [.ref], missingEmpty := [] }
  | .noConstructors =>
    { present := [], missing := [], missingEmpty := [.never] }

/-- Output of `splitColumnCtors`: `(splitCtors, missingCtors)`. -/
structure ColumnSplit where
  splitCtors : List Ctor
  missingCtors : List Ctor

/-- Exact formalization of `PlaceInfo::split_column_ctors` (`usefulness.rs:930-1006`):
1. Private uninhabited field -> `([.privateUninhabited], [])`.
2. Compute `isToplevelException := col.isScrutinee && isNoConstructors`,
   `emptyArmsAreUnreachable := col.validity.isKnownValid && (isToplevelException || col.exhPatterns)`,
   `canOmitEmptyArms := col.validity.isKnownValid || isToplevelException || col.exhPatterns`.
3. Append `.missing` to `splitCtors` unless `missing` is empty and `(missingEmpty.isEmpty || emptyArmsAreUnreachable)`.
4. Append `missingEmpty` to `missingCtors` iff `!canOmitEmptyArms`.
5. Collapse `missingCtors` to `[.nonExhaustive]` if any missing ctor is `.nonExhaustive`. -/
noncomputable def splitColumnCtors (col : ColCtx) (colCtors : List Ctor) : ColumnSplit :=
  if col.privUninhabited then
    { splitCtors := [.privateUninhabited], missingCtors := [] }
  else
    let cset := ctorsForTy col.ty
    let isToplevelException :=
      col.isScrutinee && match cset with | .noConstructors => true | _ => false
    let emptyArmsAreUnreachable :=
      col.validity.isKnownValid && (isToplevelException || col.exhPatterns)
    let canOmitEmptyArms :=
      col.validity.isKnownValid || isToplevelException || col.exhPatterns
    let splitSet := splitCtorSet cset colCtors
    let addMissing :=
      !(splitSet.missing.isEmpty && (splitSet.missingEmpty.isEmpty || emptyArmsAreUnreachable))
    let splitCtors :=
      splitSet.present ++ (if addMissing then [.missing] else [])
    let rawMissing :=
      splitSet.missing ++ (if canOmitEmptyArms then [] else splitSet.missingEmpty)
    let missingCtors :=
      if listAny Ctor.isNonExhaustive rawMissing then [.nonExhaustive] else rawMissing
    { splitCtors := splitCtors, missingCtors := missingCtors }

/-! ## Section 5: Maranget Matrix Specialization, Unspecialization, Usefulness, and Fuel Adequacy -/

/-- Expand all top-level `orPat` patterns in column 0 of a row (`MatrixRow::expand_or_pat`,
`usefulness.rs:1168-1178`). -/
noncomputable def expandHeadOrRow : MatrixRow → List MatrixRow
  | { pats := [], isUnderGuard := g, armIdx := idx } =>
    [{ pats := [], isUnderGuard := g, armIdx := idx }]
  | { pats := p :: ps, isUnderGuard := g, armIdx := idx } =>
    (expandHeadOrPat p).map (fun q => { pats := q :: ps, isUnderGuard := g, armIdx := idx })

/-- Expand all top-level `orPat` patterns in column 0 across an entire matrix. -/
noncomputable def expandHeadOrRows : List MatrixRow → List MatrixRow
  | [] => []
  | r :: rs => expandHeadOrRow r ++ expandHeadOrRows rs

/-- Extract the head constructor of a row (defaulting to `.wild` on empty rows). -/
noncomputable def MatrixRow.headCtor (r : MatrixRow) : Ctor :=
  match r.pats with
  | [] => .wild
  | p :: _ => p.headCtor

/-- Extract all head constructors from a matrix. -/
noncomputable def matrixHeadCtors (rows : List MatrixRow) : List Ctor :=
  rows.map MatrixRow.headCtor

/-- Specialize a single or-free head pattern `p` against constructor `c` of arity `arity`
(`PatOrWild::specialize`, `pat.rs:85-122, 228-237`). -/
noncomputable def specializePatHead (c : Ctor) (arity : Nat) (p : Pat) : Option (List Pat) :=
  match c with
  | .privateUninhabited => some []
  | _ =>
    if !c.isCoveredBy p.headCtor then
      none
    else
      match p with
      | .wild => some (listReplicate arity .wild)
      | .unit => some []
      | .bool _ => some []
      | .intRange _ => some []
      | .pair p1 p2 => some [p1, p2]
      | .variant _ sub => some [sub]
      | .ref sub => some [sub]
      | .orPat _ _ => none

/-- Specialize one row against constructor `c` (`MatrixRow::pop_head_constructor`,
`usefulness.rs:1182-1198`). -/
noncomputable def specializeRow (c : Ctor) (arity : Nat) (r : MatrixRow) : Option MatrixRow :=
  match r.pats with
  | [] => none
  | p :: ps =>
    match specializePatHead c arity p with
    | some subPats =>
      some { pats := subPats ++ ps, isUnderGuard := r.isUnderGuard, armIdx := r.armIdx }
    | none => none

/-- Specialize every row of a matrix against constructor `c` (`Matrix::specialize_constructor`,
`usefulness.rs:1283-1321`). -/
noncomputable def specializeRows (c : Ctor) (arity : Nat) : List MatrixRow → List MatrixRow
  | [] => []
  | r :: rs =>
    match specializeRow c arity r with
    | some r' => r' :: specializeRows c arity rs
    | none => specializeRows c arity rs

/-- Compute specialized sub-column contexts for `(col, c)` (`PlaceInfo::specialize`,
`usefulness.rs:907-920` and `RustcPatCtxt::ctor_sub_tys`, `rustc.rs:230-281`). -/
noncomputable def specializeCol (col : ColCtx) (c : Ctor) : List ColCtx :=
  match c with
  | .pair =>
    match col.ty with
    | .pair a b =>
      [ { ty := a, privUninhabited := false, validity := col.validity,
          isScrutinee := false, exhPatterns := col.exhPatterns },
        { ty := b, privUninhabited := false, validity := col.validity,
          isScrutinee := false, exhPatterns := col.exhPatterns } ]
    | .struct2 a b bVis =>
      let priv2 := (!bVis) && tyIsEmpty b
      let val2 := if priv2 then .maybeInvalid else col.validity
      [ { ty := a, privUninhabited := false, validity := col.validity,
          isScrutinee := false, exhPatterns := col.exhPatterns },
        { ty := b, privUninhabited := priv2, validity := val2,
          isScrutinee := false, exhPatterns := col.exhPatterns } ]
    | _ => []
  | .variant idx =>
    match col.ty with
    | .enum vs _ =>
      match listGet? vs idx with
      | some pt =>
        [ { ty := pt, privUninhabited := false, validity := col.validity,
            isScrutinee := false, exhPatterns := col.exhPatterns } ]
      | none => []
    | _ => []
  | .ref =>
    match col.ty with
    | .ref inner =>
      [ { ty := inner, privUninhabited := false, validity := .maybeInvalid,
          isScrutinee := false, exhPatterns := col.exhPatterns } ]
    | _ => []
  | _ => []

/-- Constructor arity matching `specializeCol` (`PatCx::ctor_arity`, `rustc.rs:284-301`). -/
noncomputable def ctorArityForCol (col : ColCtx) (c : Ctor) : Nat :=
  (specializeCol col c).length

/-- Total type-weight across a list of column contexts. -/
noncomputable def colsWeight : List ColCtx → Nat
  | [] => 0
  | c :: cs => tyWeight c.ty + colsWeight cs

/-- Every constructor specialization strictly decreases column weight. -/
theorem colsWeight_specializeCol_lt (col : ColCtx) (c : Ctor) :
    colsWeight (specializeCol col c) < tyWeight col.ty := by
  rcases col with ⟨ty, priv, val, scrut, exh⟩
  cases c with
  | unit | bool _ | intRange _ | nonExhaustive | orCtor | wild | missing
  | privateUninhabited | never =>
    change 0 < tyWeight ty
    exact Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) (tyWeight_pos ty)
  | pair =>
    cases ty with
    | unit | bool | u8 | void | enum _ _ | ref _ =>
      change 0 < tyWeight _
      exact Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) (tyWeight_pos _)
    | pair a b =>
      change (tyWeight a + (tyWeight b + 0)) < 1 + tyWeight a + tyWeight b
      rw [Nat.add_zero, Nat.add_comm 1 (tyWeight a), Nat.add_assoc, Nat.add_comm 1 (tyWeight b),
        ← Nat.add_assoc]
      exact Nat.lt_succ_self (tyWeight a + tyWeight b)
    | struct2 a b bVis =>
      change (tyWeight a + (tyWeight b + 0)) < 1 + tyWeight a + tyWeight b
      rw [Nat.add_zero, Nat.add_comm 1 (tyWeight a), Nat.add_assoc, Nat.add_comm 1 (tyWeight b),
        ← Nat.add_assoc]
      exact Nat.lt_succ_self (tyWeight a + tyWeight b)
  | variant idx =>
    cases ty with
    | unit | bool | u8 | void | pair _ _ | struct2 _ _ _ | ref _ =>
      change 0 < tyWeight _
      exact Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) (tyWeight_pos _)
    | enum vs nonExh =>
      change colsWeight (match listGet? vs idx with
        | some pt => [{ ty := pt, privUninhabited := false, validity := val,
                        isScrutinee := false, exhPatterns := exh }]
        | none => []) < 1 + tyWeightList vs
      cases hg : listGet? vs idx with
      | none =>
        change 0 < 1 + tyWeightList vs
        rw [Nat.add_comm 1 (tyWeightList vs)]
        exact Nat.zero_lt_succ (tyWeightList vs)
      | some pt =>
        change tyWeight pt + 0 < 1 + tyWeightList vs
        rw [Nat.add_zero, Nat.add_comm 1 (tyWeightList vs)]
        exact Nat.lt_succ_of_le (tyWeight_le_tyWeightList_of_get? hg)
  | ref =>
    cases ty with
    | unit | bool | u8 | void | pair _ _ | struct2 _ _ _ | enum _ _ =>
      change 0 < tyWeight _
      exact Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) (tyWeight_pos _)
    | ref inner =>
      change tyWeight inner + 0 < 1 + tyWeight inner
      rw [Nat.add_zero, Nat.add_comm 1 (tyWeight inner)]
      exact Nat.lt_succ_self (tyWeight inner)

/-- Total column weight strictly decreases on `specializeCol col c ++ cs`. -/
theorem colsWeight_append (l1 l2 : List ColCtx) :
    colsWeight (l1 ++ l2) = colsWeight l1 + colsWeight l2 := by
  induction l1 with
  | nil =>
    change colsWeight l2 = 0 + colsWeight l2
    rw [Nat.zero_add]
  | cons c cs ih =>
    change tyWeight c.ty + colsWeight (cs ++ l2) = (tyWeight c.ty + colsWeight cs) + colsWeight l2
    rw [ih, Nat.add_assoc]

/-- Strict decrease of `colsWeight` across one specialization step. -/
theorem colsWeight_specialize_lt (col : ColCtx) (c : Ctor) (cs : List ColCtx) :
    colsWeight (specializeCol col c ++ cs) < colsWeight (col :: cs) := by
  rw [colsWeight_append]
  change colsWeight (specializeCol col c) + colsWeight cs < tyWeight col.ty + colsWeight cs
  exact add_lt_add_right_nat (colsWeight_specializeCol_lt col c)

/-- Unspecialize a single witness stack (`WitnessStack::apply_constructor`, `usefulness.rs:1478-1507`). -/
noncomputable def unspecializeStack (col : ColCtx) (c : Ctor) (ws : List WitnessPat) :
    List WitnessPat :=
  match c with
  | .pair =>
    match ws with
    | w1 :: w2 :: rest => .pair w1 w2 :: rest
    | _ => .wild :: ws
  | .variant idx =>
    match ws with
    | w :: rest => .variant idx w :: rest
    | _ => .wild :: ws
  | .ref =>
    match ws with
    | w :: rest => .ref w :: rest
    | _ => .wild :: ws
  | .unit => .unit :: ws
  | .bool b => .bool b :: ws
  | .intRange r => .intRange r :: ws
  | .nonExhaustive => .nonExhaustive :: ws
  | .privateUninhabited => .privateUninhabited :: ws
  | .never => .never :: ws
  | .wild => WitnessPat.wildcardForTy col.ty :: ws
  | .orCtor | .missing => .wild :: ws

/-- Unspecialize a witness matrix for `ctor` and `missingCtors`
(`WitnessMatrix::apply_constructor`, `usefulness.rs:1555-1585`). -/
noncomputable def applyCtorToWitnesses
    (col : ColCtx) (missingCtors : List Ctor) (ctor : Ctor)
    (subWitnesses : List (List WitnessPat)) : List (List WitnessPat) :=
  match subWitnesses with
  | [] => []
  | _ =>
    match ctor with
    | .missing =>
      missingCtors.flatMap (fun m =>
        let witPat := wildFromCtor col.ty m
        subWitnesses.map (fun ws => witPat :: ws))
    | _ =>
      subWitnesses.map (unspecializeStack col ctor)

/-- Base-case scan at `cols = []` (`usefulness.rs:1717-1736`):
- Every row reached while `stillUseful = true` is added to `usefulIds`!
- Passing a guarded row (`isUnderGuard = true`) keeps `stillUseful = true`, so later rows
  and the virtual wildcard exhaustiveness row stay reachable/uncovered!
- Passing an unguarded row (`isUnderGuard = false`) sets `stillUseful = false`, making
  subsequent rows redundant and the leaf exhaustive! -/
noncomputable def evalBaseRows (stillUseful : Bool) :
    List MatrixRow → (Bool × List Nat)
  | [] => (stillUseful, [])
  | r :: rs =>
    let nextUseful := stillUseful && r.isUnderGuard
    let (finalUseful, tailIds) := evalBaseRows nextUseful rs
    let outIds := if stillUseful then r.armIdx :: tailIds else tailIds
    (finalUseful, outIds)

/-- Recursive branch combiner for `marangetCheckAux`, separating constructor iteration for clean
inductive reasoning. -/
noncomputable def marangetBranches
    (step : List ColCtx → List MatrixRow → (List (List WitnessPat) × List Nat))
    (col : ColCtx) (cs : List ColCtx) (missingCtors : List Ctor) (rows' : List MatrixRow) :
    List Ctor → (List (List WitnessPat) × List Nat)
  | [] => ([], [])
  | ctor :: rest =>
    let subCols := specializeCol col ctor
    let specRows := specializeRows ctor subCols.length rows'
    let (subWits, subIds) := step (subCols ++ cs) specRows
    let liftedWits := applyCtorToWitnesses col missingCtors ctor subWits
    let (restWits, restIds) := marangetBranches step col cs missingCtors rows' rest
    (liftedWits ++ restWits, subIds ++ restIds)

/-- Combined Maranget exhaustiveness + arm usefulness recursion on structural `fuel : Nat`. -/
noncomputable def marangetCheckAux
    (fuel : Nat) (cols : List ColCtx) (rows : List MatrixRow) :
    (List (List WitnessPat) × List Nat) :=
  match fuel with
  | 0 => ([], [])
  | fuel' + 1 =>
    match cols with
    | [] =>
      let (exhaustiveMissing, usefulIds) := evalBaseRows true rows
      let wits := if exhaustiveMissing then [[]] else []
      (wits, usefulIds)
    | col :: cs =>
      let rows' := expandHeadOrRows rows
      let heads := matrixHeadCtors rows'
      let split := splitColumnCtors col heads
      marangetBranches (marangetCheckAux fuel') col cs split.missingCtors rows' split.splitCtors

/-- Compute missing witnesses at sufficient fuel `colsWeight cols + 1`. -/
noncomputable def evalMarangetMatrix (cols : List ColCtx) (rows : List MatrixRow) :
    List (List WitnessPat) :=
  (marangetCheckAux (colsWeight cols + 1) cols rows).1

/-- Compute single-column missing witness patterns for a `match` expression. -/
noncomputable def evalMaranget (col : ColCtx) (arms : List MatchArm) : List WitnessPat :=
  (evalMarangetMatrix [col] (armsToRows arms)).map (fun ws =>
    match ws with
    | w :: _ => w
    | [] => .wild)

/-- Check whether `n ∈ ns` (`Nat` membership). -/
noncomputable def natMemBool (n : Nat) : List Nat → Bool
  | [] => false
  | x :: xs => natBeq n x || natMemBool n xs

/-- Compute per-arm usefulness flags (`true` = useful, `false` = redundant / `unreachable_patterns`). -/
noncomputable def evalArmUseful (col : ColCtx) (arms : List MatchArm) (armId : Nat) : Bool :=
  natMemBool armId (marangetCheckAux (colsWeight [col] + 1) [col] (armsToRows arms)).2

/-- Helper for multi-column value typing (`ColsVisibleWellTyped`). -/
noncomputable def ColsVisibleWellTyped : List ColCtx → List Val → Prop
  | [], [] => True
  | c :: cs, v :: vs => VisibleWellTyped c.validity c.ty v ∧ ColsVisibleWellTyped cs vs
  | _, _ => False

/-- Helper for multi-column pattern well-formedness (`PatWellFormed`):
ensures patterns only use constructors valid for `t`, and private uninhabited struct fields
(where `bVis = false` or `privUninhabited = true`) only use `.wild` (since private fields are
inaccessible outside their defining module in Rust). -/
noncomputable def PatWellFormed : Bool → Ty → Pat → Prop
  | _, _, .wild => True
  | false, .unit, .unit => True
  | false, .bool, .bool _ => True
  | false, .u8, .intRange _ => True
  | false, .pair a b, .pair p1 p2 => PatWellFormed false a p1 ∧ PatWellFormed false b p2
  | false, .struct2 a b true, .pair p1 p2 => PatWellFormed false a p1 ∧ PatWellFormed false b p2
  | false, .struct2 a b false, .pair p1 p2 =>
    PatWellFormed false a p1 ∧ PatWellFormed true b p2
  | false, .enum vs _, .variant idx sub =>
    ∃ pt, listGet? vs idx = some pt ∧ PatWellFormed false pt sub
  | false, .ref inner, .ref sub => PatWellFormed false inner sub
  | priv, t, .orPat p1 p2 => PatWellFormed priv t p1 ∧ PatWellFormed priv t p2
  | _, _, _ => False

/-- Multi-column pattern-list well-formedness. -/
noncomputable def RowWellFormed : List ColCtx → List Pat → Prop
  | [], [] => True
  | c :: cs, p :: ps => PatWellFormed c.privUninhabited c.ty p ∧ RowWellFormed cs ps
  | _, _ => False

/-- All rows of a matrix are well-formed for `cols`. -/
noncomputable def MatrixWellFormed (cols : List ColCtx) (rows : List MatrixRow) : Prop :=
  ∀ r, r ∈ rows → RowWellFormed cols r.pats

/-- Multi-column value matching for a list of patterns. -/
noncomputable def patsMatchVals : List Pat → List Val → Bool
  | [], [] => true
  | p :: ps, v :: vs => p.matchesVal v && patsMatchVals ps vs
  | _, _ => false

/-- Multi-column unguarded match predicate for a matrix (`true` iff some unguarded row matches). -/
noncomputable def rowsUnguardedMatch (rows : List MatrixRow) (vs : List Val) : Bool :=
  listAny (fun r => (!r.isUnderGuard) && patsMatchVals r.pats vs) rows

/-- Single-column unguarded match predicate for `List MatchArm`. -/
noncomputable def armsUnguardedMatch (arms : List MatchArm) (v : Val) : Bool :=
  listAny (fun a => (!a.hasGuard) && a.pat.matchesVal v) arms

/-- Multi-column witness matching predicate. -/
noncomputable def witnessesMatchVals : List ColCtx → List WitnessPat → List Val → Bool
  | [], [], [] => true
  | c :: cs, w :: ws, v :: vs => w.matchesVal c.validity v && witnessesMatchVals cs ws vs
  | _, _, _ => false

/-! ## Section 6: Soundness, Completeness, Witness Soundness, and Guard / NonExhaustive Theorems -/

/-- Exact classifier for types whose `ConstructorSet` is `NoConstructors` (`void` or closed `enum []`). -/
noncomputable def NoConstructorsTy : Ty → Bool
  | .void => true
  | .enum [] false => true
  | _ => false

/-- Check whether `c` satisfies the constructor invariants guaranteed by `rustc_pattern_analysis`:
a `privUninhabited` column is always an empty type paired with `PlaceValidity.maybeInvalid`. -/
noncomputable def ColsWellFormed : List ColCtx → Prop
  | [] => True
  | c :: cs =>
    (c.privUninhabited = true → tyIsEmpty c.ty = true ∧ c.validity = .maybeInvalid) ∧
    ColsWellFormed cs

/-- Ambient soundness condition restricting compiler flags that knowingly permit empty pattern
omission on `MaybeInvalid` places:
1. `#![feature(exhaustive_patterns)]` is disabled (`c.exhPatterns = false`);
2. A direct deref top-level exception (`c.isScrutinee && NoConstructorsTy c.ty &&
   c.validity == .maybeInvalid`) is excluded. -/
noncomputable def ColsSoundCtx : List ColCtx → Prop
  | [] => True
  | c :: cs =>
    c.exhPatterns = false ∧
    (c.validity = .validOnly ∨ (c.isScrutinee && NoConstructorsTy c.ty) = false) ∧
    ColsSoundCtx cs

/-- `ctorsForTy col.ty` is `.noConstructors` iff `NoConstructorsTy col.ty = true`. -/
theorem ctorsForTy_noConstructors_iff (t : Ty) :
    (match ctorsForTy t with | .noConstructors => true | _ => false) = NoConstructorsTy t := by
  cases t with
  | enum vs nonExh =>
    cases vs with
    | nil => cases nonExh <;> rfl
    | cons _ _ => rfl
  | unit | bool | u8 | void | pair _ _ | struct2 _ _ _ | ref _ => rfl

theorem colsWellFormed_append (cs1 cs2 : List ColCtx)
    (h1 : ColsWellFormed cs1) (h2 : ColsWellFormed cs2) : ColsWellFormed (cs1 ++ cs2) := by
  induction cs1 with
  | nil => exact h2
  | cons c cs1' ih => exact ⟨h1.1, ih h1.2⟩

theorem colsSoundCtx_append (cs1 cs2 : List ColCtx)
    (h1 : ColsSoundCtx cs1) (h2 : ColsSoundCtx cs2) : ColsSoundCtx (cs1 ++ cs2) := by
  induction cs1 with
  | nil => exact h2
  | cons c cs1' ih => exact ⟨h1.1, h1.2.1, ih h1.2.2⟩

/-- `specializeCol` preserves `ColsWellFormed`. -/
theorem colsWellFormed_specializeCol (col : ColCtx) (c : Ctor) (cs : List ColCtx)
    (hWF : ColsWellFormed (col :: cs)) : ColsWellFormed (specializeCol col c ++ cs) := by
  apply colsWellFormed_append _ cs _ hWF.2
  rcases col with ⟨ty, priv, val, scrut, exh⟩
  cases c with
  | unit | bool _ | intRange _ | nonExhaustive | orCtor | wild | missing
  | privateUninhabited | never =>
    trivial
  | pair =>
    cases ty with
    | pair a b =>
      dsimp only [specializeCol]
      exact ⟨fun h => False.elim (Bool.noConfusion h), fun h => False.elim (Bool.noConfusion h), trivial⟩
    | struct2 a b bVis =>
      dsimp only [specializeCol]
      refine ⟨fun h => False.elim (Bool.noConfusion h), ?_, trivial⟩
      intro hpriv
      cases bVis with
      | true => contradiction
      | false =>
        cases he : tyIsEmpty b with
        | true => exact ⟨rfl, rfl⟩
        | false =>
          dsimp only at hpriv
          have hf : (!false && tyIsEmpty b) = true := hpriv
          rw [he] at hf; contradiction
    | unit | bool | u8 | void | enum _ _ | ref _ =>
      dsimp only [specializeCol]; trivial
  | variant idx =>
    cases ty with
    | enum vs nonExh =>
      dsimp only [specializeCol]
      cases listGet? vs idx with
      | none => trivial
      | some pt => exact ⟨fun h => False.elim (Bool.noConfusion h), trivial⟩
    | unit | bool | u8 | void | pair _ _ | struct2 _ _ _ | ref _ =>
      dsimp only [specializeCol]; trivial
  | ref =>
    cases ty with
    | ref inner =>
      dsimp only [specializeCol]
      exact ⟨fun h => False.elim (Bool.noConfusion h), trivial⟩
    | unit | bool | u8 | void | pair _ _ | struct2 _ _ _ | enum _ _ =>
      dsimp only [specializeCol]; trivial

/-- `specializeCol` preserves `ColsSoundCtx`: every generated sub-column inherits
`exhPatterns = false` and sets `isScrutinee = false`. -/
theorem colsSoundCtx_specializeCol (col : ColCtx) (c : Ctor) (cs : List ColCtx)
    (hS : ColsSoundCtx (col :: cs)) : ColsSoundCtx (specializeCol col c ++ cs) := by
  apply colsSoundCtx_append _ cs _ hS.2.2
  have hexh : col.exhPatterns = false := hS.1
  rcases col with ⟨ty, priv, val, scrut, exh⟩
  cases c with
  | unit | bool _ | intRange _ | nonExhaustive | orCtor | wild | missing
  | privateUninhabited | never =>
    trivial
  | pair =>
    cases ty with
    | pair a b =>
      dsimp only [specializeCol]
      exact ⟨hexh, Or.inr rfl, hexh, Or.inr rfl, trivial⟩
    | struct2 a b bVis =>
      dsimp only [specializeCol]
      exact ⟨hexh, Or.inr rfl, hexh, Or.inr rfl, trivial⟩
    | unit | bool | u8 | void | enum _ _ | ref _ =>
      dsimp only [specializeCol]; trivial
  | variant idx =>
    cases ty with
    | enum vs nonExh =>
      dsimp only [specializeCol]
      cases listGet? vs idx with
      | none => trivial
      | some pt => exact ⟨hexh, Or.inr rfl, trivial⟩
    | unit | bool | u8 | void | pair _ _ | struct2 _ _ _ | ref _ =>
      dsimp only [specializeCol]; trivial
  | ref =>
    cases ty with
    | ref inner =>
      dsimp only [specializeCol]
      exact ⟨hexh, Or.inr rfl, trivial⟩
    | unit | bool | u8 | void | pair _ _ | struct2 _ _ _ | enum _ _ =>
      dsimp only [specializeCol]; trivial

/-- Exact per-place value domain matching `PlaceInfo` constructors and `rustc_pattern_analysis`:
- Under `.maybeInvalid` at non-private slots, `.invalid` occurs only at unconstructed
  `NoConstructorsTy` leaves (`.void` or closed empty `enum []`).
- At opaque `priv = true` slots (`.maybeInvalid`), `VisibleWellTyped .maybeInvalid t v` holds.
- Constructed inhabited/composite values keep their outer constructor recursively. -/
noncomputable def ValidPlaceVal : PlaceValidity → Bool → Ty → Val → Prop
  | .maybeInvalid, true, t, v => VisibleWellTyped .maybeInvalid t v
  | .validOnly, true, _, _ => False
  | .maybeInvalid, false, t, .invalid => NoConstructorsTy t = true
  | .validOnly, false, _, .invalid => False
  | _, false, .unit, .unit => True
  | _, false, .bool, .bool _ => True
  | _, false, .u8, .u8 n => n ≤ 255
  | val, false, .pair a b, .pair v1 v2 =>
    ValidPlaceVal val false a v1 ∧ ValidPlaceVal val false b v2
  | val, false, .struct2 a b true, .pair v1 v2 =>
    ValidPlaceVal val false a v1 ∧ ValidPlaceVal val false b v2
  | val, false, .struct2 a b false, .pair v1 v2 =>
    ValidPlaceVal val false a v1 ∧
    (if tyIsEmpty b then ValidPlaceVal .maybeInvalid true b v2 else ValidPlaceVal val false b v2)
  | val, false, .enum variants _, .ctor idx sub =>
    ∃ pt, listGet? variants idx = some pt ∧ ValidPlaceVal val false pt sub
  | _, false, .enum _ true, .hiddenCtor _ => True
  | _, false, .ref inner, .ref pt => ValidPlaceVal .maybeInvalid false inner pt
  | _, _, _, _ => False

/-- Monotonicity of `ValidPlaceVal`: `.validOnly` implies `.maybeInvalid` when `priv = false`. -/
theorem validPlaceVal_valid_to_maybe_bound :
    ∀ (w : Nat) (t : Ty) (v : Val),
      tyWeight t ≤ w →
      ValidPlaceVal .validOnly false t v →
      ValidPlaceVal .maybeInvalid false t v := by
  intro w
  induction w with
  | zero =>
    intro t _ hw _
    exact False.elim (Nat.not_succ_le_zero 0 (Nat.le_trans (tyWeight_pos t) hw))
  | succ w' ih =>
    intro t v hw hv
    cases t with
    | unit => cases v <;> first | contradiction | trivial
    | bool => cases v <;> first | contradiction | trivial
    | u8 =>
      cases v with
      | u8 n => exact hv
      | invalid | unit | bool _ | pair _ _ | ctor _ _ | hiddenCtor _ | ref _ => contradiction
    | void => cases v <;> contradiction
    | pair a b =>
      cases v with
      | pair v1 v2 =>
        exact ⟨ih a v1 (le_left_of_one_add_add hw) hv.1, ih b v2 (le_right_of_one_add_add hw) hv.2⟩
      | invalid | unit | bool _ | u8 _ | ctor _ _ | hiddenCtor _ | ref _ => contradiction
    | struct2 a b bVis =>
      cases v with
      | pair v1 v2 =>
        have hwa : tyWeight a ≤ w' := le_left_of_one_add_add hw
        have hwb : tyWeight b ≤ w' := le_right_of_one_add_add hw
        cases bVis with
        | true => exact ⟨ih a v1 hwa hv.1, ih b v2 hwb hv.2⟩
        | false =>
          rcases hv with ⟨hv1, hv2⟩
          dsimp only [ValidPlaceVal]
          cases he : tyIsEmpty b with
          | true =>
            have hv2' : ValidPlaceVal .maybeInvalid true b v2 := by rw [he] at hv2; exact hv2
            simp only [ite_true]
            exact ⟨ih a v1 hwa hv1, hv2'⟩
          | false =>
            have hv2' : ValidPlaceVal .validOnly false b v2 := by rw [he] at hv2; exact hv2
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact ⟨ih a v1 hwa hv1, ih b v2 hwb hv2'⟩
      | invalid | unit | bool _ | u8 _ | ctor _ _ | hiddenCtor _ | ref _ => contradiction
    | enum vs nonExh =>
      cases v with
      | ctor idx sub =>
        rcases hv with ⟨pt, hget, hsub⟩
        have hsum : tyWeight pt ≤ tyWeightList vs := tyWeight_le_tyWeightList_of_get? hget
        change 1 + tyWeightList vs ≤ w' + 1 at hw
        rw [Nat.add_comm 1 (tyWeightList vs)] at hw
        exact ⟨pt, hget, ih pt sub (Nat.le_trans hsum (Nat.le_of_succ_le_succ hw)) hsub⟩
      | hiddenCtor _ => cases nonExh <;> first | contradiction | trivial
      | invalid | unit | bool _ | u8 _ | pair _ _ | ref _ => contradiction
    | ref inner =>
      cases v with
      | ref pt => exact hv
      | invalid | unit | bool _ | u8 _ | pair _ _ | ctor _ _ | hiddenCtor _ => contradiction

theorem validPlaceVal_valid_to_maybe {t : Ty} {v : Val}
    (hv : ValidPlaceVal .validOnly false t v) : ValidPlaceVal .maybeInvalid false t v :=
  validPlaceVal_valid_to_maybe_bound (tyWeight t) t v (Nat.le_refl (tyWeight t)) hv

theorem validPlaceVal_maybeInvalid_true (t : Ty) (v : Val)
    (hv : ValidPlaceVal .maybeInvalid true t v) : VisibleWellTyped .maybeInvalid t v := by
  cases t <;> cases v <;> exact hv

theorem validPlaceVal_validOnly_true_false (t : Ty) (v : Val)
    (hv : ValidPlaceVal .validOnly true t v) : False := by
  cases t <;> cases v <;> exact hv

/-- Every `ValidPlaceVal` value also satisfies `VisibleWellTyped`. -/
theorem validPlaceVal_implies_visible_bound :
    ∀ (w : Nat) (val : PlaceValidity) (priv : Bool) (t : Ty) (v : Val),
      tyWeight t ≤ w →
      ValidPlaceVal val priv t v →
      VisibleWellTyped val t v := by
  intro w
  induction w with
  | zero =>
    intro _ _ t _ hw _
    exact False.elim (Nat.not_succ_le_zero 0 (Nat.le_trans (tyWeight_pos t) hw))
  | succ w' ih =>
    intro val priv t v hw hv
    cases val with
    | validOnly =>
      cases priv with
      | true => exact False.elim (validPlaceVal_validOnly_true_false t v hv)
      | false =>
        cases t with
        | unit => cases v <;> first | contradiction | trivial
        | bool => cases v <;> first | contradiction | trivial
        | u8 => cases v <;> first | contradiction | exact hv
        | void => cases v <;> contradiction
        | pair a b =>
          cases v with
          | pair v1 v2 =>
            exact ⟨ih .validOnly false a v1 (le_left_of_one_add_add hw) hv.1,
                   ih .validOnly false b v2 (le_right_of_one_add_add hw) hv.2⟩
          | invalid | unit | bool _ | u8 _ | ctor _ _ | hiddenCtor _ | ref _ => contradiction
        | struct2 a b bVis =>
          cases v with
          | pair v1 v2 =>
            have hwa : tyWeight a ≤ w' := le_left_of_one_add_add hw
            have hwb : tyWeight b ≤ w' := le_right_of_one_add_add hw
            cases bVis with
            | true => exact ⟨ih .validOnly false a v1 hwa hv.1, ih .validOnly false b v2 hwb hv.2⟩
            | false =>
              rcases hv with ⟨hv1, hv2⟩
              dsimp only [VisibleWellTyped]
              cases he : tyIsEmpty b with
              | true =>
                have hv2' : ValidPlaceVal .maybeInvalid true b v2 := by rw [he] at hv2; exact hv2
                simp only [ite_true]
                exact ⟨ih .validOnly false a v1 hwa hv1, validPlaceVal_maybeInvalid_true b v2 hv2'⟩
              | false =>
                have hv2' : ValidPlaceVal .validOnly false b v2 := by rw [he] at hv2; exact hv2
                simp only [Bool.false_eq_true, ↓reduceIte]
                exact ⟨ih .validOnly false a v1 hwa hv1, ih .validOnly false b v2 hwb hv2'⟩
          | invalid | unit | bool _ | u8 _ | ctor _ _ | hiddenCtor _ | ref _ => contradiction
        | enum vs nonExh =>
          cases v with
          | ctor idx sub =>
            rcases hv with ⟨pt, hget, hsub⟩
            have hsum : tyWeight pt ≤ tyWeightList vs := tyWeight_le_tyWeightList_of_get? hget
            change 1 + tyWeightList vs ≤ w' + 1 at hw
            rw [Nat.add_comm 1 (tyWeightList vs)] at hw
            exact ⟨pt, hget, ih .validOnly false pt sub (Nat.le_trans hsum (Nat.le_of_succ_le_succ hw)) hsub⟩
          | hiddenCtor _ => cases nonExh <;> first | contradiction | trivial
          | invalid | unit | bool _ | u8 _ | pair _ _ | ref _ => contradiction
        | ref inner =>
          cases v with
          | ref pt =>
            change 1 + tyWeight inner ≤ w' + 1 at hw
            rw [Nat.add_comm 1 (tyWeight inner)] at hw
            exact ih .maybeInvalid false inner pt (Nat.le_of_succ_le_succ hw) hv
          | invalid | unit | bool _ | u8 _ | pair _ _ | ctor _ _ | hiddenCtor _ => contradiction
    | maybeInvalid =>
      cases priv with
      | true => exact validPlaceVal_maybeInvalid_true t v hv
      | false =>
        cases v with
        | invalid => trivial
        | unit => cases t <;> first | contradiction | trivial
        | bool _ => cases t <;> first | contradiction | trivial
        | u8 _ => cases t <;> first | contradiction | exact hv
        | pair v1 v2 =>
          cases t with
          | pair a b =>
            exact ⟨ih .maybeInvalid false a v1 (le_left_of_one_add_add hw) hv.1,
                   ih .maybeInvalid false b v2 (le_right_of_one_add_add hw) hv.2⟩
          | struct2 a b bVis =>
            have hwa : tyWeight a ≤ w' := le_left_of_one_add_add hw
            have hwb : tyWeight b ≤ w' := le_right_of_one_add_add hw
            cases bVis with
            | true =>
              exact ⟨ih .maybeInvalid false a v1 hwa hv.1, ih .maybeInvalid false b v2 hwb hv.2⟩
            | false =>
              rcases hv with ⟨hv1, hv2⟩
              dsimp only [VisibleWellTyped]
              cases he : tyIsEmpty b with
              | true =>
                have hv2' : ValidPlaceVal .maybeInvalid true b v2 := by rw [he] at hv2; exact hv2
                simp only [ite_true]
                exact ⟨ih .maybeInvalid false a v1 hwa hv1, validPlaceVal_maybeInvalid_true b v2 hv2'⟩
              | false =>
                have hv2' : ValidPlaceVal .maybeInvalid false b v2 := by rw [he] at hv2; exact hv2
                simp only [Bool.false_eq_true, ↓reduceIte]
                exact ⟨ih .maybeInvalid false a v1 hwa hv1, ih .maybeInvalid false b v2 hwb hv2'⟩
          | unit | bool | u8 | void | enum _ _ | ref _ => contradiction
        | ctor idx sub =>
          cases t with
          | enum vs _ =>
            rcases hv with ⟨pt, hget, hsub⟩
            have hsum : tyWeight pt ≤ tyWeightList vs := tyWeight_le_tyWeightList_of_get? hget
            change 1 + tyWeightList vs ≤ w' + 1 at hw
            rw [Nat.add_comm 1 (tyWeightList vs)] at hw
            exact ⟨pt, hget, ih .maybeInvalid false pt sub (Nat.le_trans hsum (Nat.le_of_succ_le_succ hw)) hsub⟩
          | unit | bool | u8 | void | pair _ _ | struct2 _ _ _ | ref _ => contradiction
        | hiddenCtor _ =>
          cases t with
          | enum _ nonExh => cases nonExh <;> first | contradiction | trivial
          | unit | bool | u8 | void | pair _ _ | struct2 _ _ _ | ref _ => contradiction
        | ref pt =>
          cases t with
          | ref inner =>
            change 1 + tyWeight inner ≤ w' + 1 at hw
            rw [Nat.add_comm 1 (tyWeight inner)] at hw
            exact ih .maybeInvalid false inner pt (Nat.le_of_succ_le_succ hw) hv
          | unit | bool | u8 | void | pair _ _ | struct2 _ _ _ | enum _ _ => contradiction

theorem validPlaceVal_implies_visible {val : PlaceValidity} {priv : Bool} {t : Ty} {v : Val}
    (hv : ValidPlaceVal val priv t v) : VisibleWellTyped val t v :=
  validPlaceVal_implies_visible_bound (tyWeight t) val priv t v (Nat.le_refl (tyWeight t)) hv

/-- Well-formed runtime Rust value without uninitialized/invalid bits inside top-level inhabited
types (`.invalid` allowed behind references only at `NoConstructorsTy` leaves). -/
noncomputable def PureRustVal (t : Ty) (v : Val) : Prop :=
  TrueWellTyped .validOnly t v ∧ ValidPlaceVal .validOnly false t v

/-- Empty types admit no `ValidPlaceVal .validOnly` value. -/
theorem tyIsEmpty_validPlaceVal_validOnly_false {priv : Bool} {t : Ty} {v : Val}
    (he : tyIsEmpty t = true) (hv : ValidPlaceVal .validOnly priv t v) : False := by
  cases priv with
  | true => exact validPlaceVal_validOnly_true_false t v hv
  | false => exact tyIsEmpty_sound he (validPlaceVal_implies_visible hv)

/-- Construct a `ValidPlaceVal .maybeInvalid` value for EVERY type `t`. -/
theorem inhabitValidPlace_maybeInvalid_bound :
    ∀ (w : Nat) (priv : Bool) (t : Ty),
      tyWeight t ≤ w →
      ∃ v, ValidPlaceVal .maybeInvalid priv t v := by
  intro w
  induction w with
  | zero =>
    intro _ t hw
    exact False.elim (Nat.not_succ_le_zero 0 (Nat.le_trans (tyWeight_pos t) hw))
  | succ w' ih =>
    intro priv t hw
    cases priv with
    | true => exact ⟨.invalid, trivial⟩
    | false =>
      cases t with
      | unit => exact ⟨.unit, trivial⟩
      | bool => exact ⟨.bool false, trivial⟩
      | u8 => exact ⟨.u8 0, Nat.zero_le 255⟩
      | void => exact ⟨.invalid, rfl⟩
      | pair a b =>
        rcases ih false a (le_left_of_one_add_add hw) with ⟨v1, hv1⟩
        rcases ih false b (le_right_of_one_add_add hw) with ⟨v2, hv2⟩
        exact ⟨.pair v1 v2, hv1, hv2⟩
      | struct2 a b bVis =>
        rcases ih false a (le_left_of_one_add_add hw) with ⟨v1, hv1⟩
        cases bVis with
        | true =>
          rcases ih false b (le_right_of_one_add_add hw) with ⟨v2, hv2⟩
          exact ⟨.pair v1 v2, hv1, hv2⟩
        | false =>
          cases he : tyIsEmpty b with
          | true =>
            rcases ih true b (le_right_of_one_add_add hw) with ⟨v2, hv2⟩
            refine ⟨.pair v1 v2, ?_⟩
            dsimp only [ValidPlaceVal]
            rw [he]; simp only [ite_true]; exact ⟨hv1, hv2⟩
          | false =>
            rcases ih false b (le_right_of_one_add_add hw) with ⟨v2, hv2⟩
            refine ⟨.pair v1 v2, ?_⟩
            dsimp only [ValidPlaceVal]
            rw [he]; simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨hv1, hv2⟩
      | enum vs nonExh =>
        cases nonExh with
        | true => exact ⟨.hiddenCtor 0, trivial⟩
        | false =>
          cases vs with
          | nil => exact ⟨.invalid, rfl⟩
          | cons pt rest =>
            change 1 + (tyWeight pt + tyWeightList rest) ≤ w' + 1 at hw
            have hpt : tyWeight pt ≤ w' := by
              rw [Nat.add_comm 1 (tyWeight pt + tyWeightList rest)] at hw
              exact Nat.le_trans (Nat.le_add_right (tyWeight pt) (tyWeightList rest))
                (Nat.le_of_succ_le_succ hw)
            rcases ih false pt hpt with ⟨vpt, hvpt⟩
            exact ⟨.ctor 0 vpt, pt, rfl, hvpt⟩
      | ref inner =>
        change 1 + tyWeight inner ≤ w' + 1 at hw
        rw [Nat.add_comm 1 (tyWeight inner)] at hw
        rcases ih false inner (Nat.le_of_succ_le_succ hw) with ⟨pt, hpt⟩
        exact ⟨.ref pt, hpt⟩

theorem inhabitValidPlace_maybeInvalid (priv : Bool) (t : Ty) :
    ∃ v, ValidPlaceVal .maybeInvalid priv t v :=
  inhabitValidPlace_maybeInvalid_bound (tyWeight t) priv t (Nat.le_refl (tyWeight t))

/-- Helper: find an inhabited variant payload index when `tyIsEmptyList vs = false`. -/
theorem exists_nonEmpty_variant {vs : List Ty} (hf : tyIsEmptyList vs = false) :
    ∃ idx pt, listGet? vs idx = some pt ∧ tyIsEmpty pt = false := by
  induction vs with
  | nil => contradiction
  | cons v vs' ih =>
    cases hv : tyIsEmpty v with
    | false => exact ⟨0, v, rfl, hv⟩
    | true =>
      have hvs' : tyIsEmptyList vs' = false := by
        cases hrem : tyIsEmptyList vs' with
        | false => rfl
        | true =>
          dsimp only [tyIsEmptyList] at hf
          rw [hv, hrem] at hf
          contradiction
      rcases ih hvs' with ⟨idx, pt, hget, hne⟩
      exact ⟨idx + 1, pt, hget, hne⟩

/-- Every visibly non-empty type admits a `ValidPlaceVal .validOnly false` inhabitant. -/
theorem inhabitValidPlace_nonEmpty_bound :
    ∀ (w : Nat) (t : Ty),
      tyWeight t ≤ w →
      tyIsEmpty t = false →
      ∃ v, ValidPlaceVal .validOnly false t v := by
  intro w
  induction w with
  | zero =>
    intro t hw _
    exact False.elim (Nat.not_succ_le_zero 0 (Nat.le_trans (tyWeight_pos t) hw))
  | succ w' ih =>
    intro t hw hne
    cases t with
    | unit => exact ⟨.unit, trivial⟩
    | bool => exact ⟨.bool false, trivial⟩
    | u8 => exact ⟨.u8 0, Nat.zero_le 255⟩
    | void => contradiction
    | pair a b =>
      have hwa : tyWeight a ≤ w' := le_left_of_one_add_add hw
      have hwb : tyWeight b ≤ w' := le_right_of_one_add_add hw
      dsimp only [tyIsEmpty] at hne
      rcases boolOr_eq_false.mp hne with ⟨ha, hb⟩
      rcases ih a hwa ha with ⟨v1, hv1⟩
      rcases ih b hwb hb with ⟨v2, hv2⟩
      exact ⟨.pair v1 v2, hv1, hv2⟩
    | struct2 a b bVis =>
      have hwa : tyWeight a ≤ w' := le_left_of_one_add_add hw
      have hwb : tyWeight b ≤ w' := le_right_of_one_add_add hw
      dsimp only [tyIsEmpty] at hne
      rcases boolOr_eq_false.mp hne with ⟨ha, hbVis⟩
      rcases ih a hwa ha with ⟨v1, hv1⟩
      cases bVis with
      | true =>
        have htb : tyIsEmpty b = false := by
          cases hb' : tyIsEmpty b with
          | false => rfl
          | true => rw [hb'] at hbVis; contradiction
        rcases ih b hwb htb with ⟨v2, hv2⟩
        exact ⟨.pair v1 v2, hv1, hv2⟩
      | false =>
        cases he : tyIsEmpty b with
        | true =>
          refine ⟨.pair v1 .invalid, ?_⟩
          dsimp only [ValidPlaceVal]
          rw [he]; simp only [ite_true]; exact ⟨hv1, trivial⟩
        | false =>
          rcases ih b hwb he with ⟨v2, hv2⟩
          refine ⟨.pair v1 v2, ?_⟩
          dsimp only [ValidPlaceVal]
          rw [he]; simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨hv1, hv2⟩
    | enum vs nonExh =>
      cases nonExh with
      | true => exact ⟨.hiddenCtor 0, trivial⟩
      | false =>
        dsimp only [tyIsEmpty] at hne
        have hlist : tyIsEmptyList vs = false := by
          cases hl : tyIsEmptyList vs with
          | false => rfl
          | true => rw [hl] at hne; contradiction
        rcases exists_nonEmpty_variant hlist with ⟨idx, pt, hget, hptne⟩
        have hsum : tyWeight pt ≤ tyWeightList vs := tyWeight_le_tyWeightList_of_get? hget
        change 1 + tyWeightList vs ≤ w' + 1 at hw
        rw [Nat.add_comm 1 (tyWeightList vs)] at hw
        rcases ih pt (Nat.le_trans hsum (Nat.le_of_succ_le_succ hw)) hptne with ⟨vpt, hvpt⟩
        exact ⟨.ctor idx vpt, pt, hget, hvpt⟩
    | ref inner =>
      rcases inhabitValidPlace_maybeInvalid false inner with ⟨pt, hpt⟩
      exact ⟨.ref pt, hpt⟩

theorem inhabitValidPlace_nonEmpty {t : Ty} (hne : tyIsEmpty t = false) :
    ∃ v, ValidPlaceVal .validOnly false t v :=
  inhabitValidPlace_nonEmpty_bound (tyWeight t) t (Nat.le_refl (tyWeight t)) hne

/-- `WitnessPat.wildcardForTy` matches every well-formed `ValidPlaceVal` value under a well-formed `ColCtx`. -/
theorem wildcardForTy_matches_valid (col : ColCtx) (v : Val)
    (hCol : col.privUninhabited = true → tyIsEmpty col.ty = true ∧ col.validity = .maybeInvalid)
    (hv : ValidPlaceVal col.validity col.privUninhabited col.ty v) :
    (WitnessPat.wildcardForTy col.ty).matchesVal col.validity v = true := by
  unfold WitnessPat.wildcardForTy
  cases he : tyIsEmpty col.ty with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rfl
  | true =>
    simp only [ite_true]
    cases hval : col.validity with
    | maybeInvalid => rfl
    | validOnly =>
      cases hpriv : col.privUninhabited with
      | true =>
        have hbad := (hCol hpriv).2
        rw [hval] at hbad
        contradiction
      | false =>
        rw [hval, hpriv] at hv
        exact False.elim (tyIsEmpty_validPlaceVal_validOnly_false he hv)

/-- Multi-column `ValidPlaceVal` typing. -/
noncomputable def ColsValidPlaceVal : List ColCtx → List Val → Prop
  | [], [] => True
  | c :: cs, v :: vs => ValidPlaceVal c.validity c.privUninhabited c.ty v ∧ ColsValidPlaceVal cs vs
  | _, _ => False

theorem colsValidPlaceVal_implies_visible (cols : List ColCtx) (vs : List Val)
    (hv : ColsValidPlaceVal cols vs) : ColsVisibleWellTyped cols vs := by
  induction cols generalizing vs with
  | nil =>
    cases vs with
    | nil => trivial
    | cons _ _ => contradiction
  | cons c cs ih =>
    cases vs with
    | nil => contradiction
    | cons v vs' => exact ⟨validPlaceVal_implies_visible hv.1, ih vs' hv.2⟩

theorem colsValidPlaceVal_append (cs1 cs2 : List ColCtx) (vs1 vs2 : List Val)
    (h1 : ColsValidPlaceVal cs1 vs1) (h2 : ColsValidPlaceVal cs2 vs2) :
    ColsValidPlaceVal (cs1 ++ cs2) (vs1 ++ vs2) := by
  induction cs1 generalizing vs1 with
  | nil =>
    cases vs1 with
    | nil => exact h2
    | cons _ _ => contradiction
  | cons c cs1' ih =>
    cases vs1 with
    | nil => contradiction
    | cons v vs1' => exact ⟨h1.1, ih vs1' h1.2⟩

theorem colsValidPlaceVal_split (cs1 cs2 : List ColCtx) (vs : List Val)
    (h : ColsValidPlaceVal (cs1 ++ cs2) vs) :
    ∃ vs1 vs2, vs = vs1 ++ vs2 ∧ ColsValidPlaceVal cs1 vs1 ∧ ColsValidPlaceVal cs2 vs2 := by
  induction cs1 generalizing vs with
  | nil => exact ⟨[], vs, rfl, trivial, h⟩
  | cons c cs1' ih =>
    cases vs with
    | nil => contradiction
    | cons v vs' =>
      rcases ih vs' h.2 with ⟨vs1', vs2, rfl, h1', h2⟩
      exact ⟨v :: vs1', vs2, rfl, ⟨h.1, h1'⟩, h2⟩

theorem patWellFormed_true_to_any (priv : Bool) (t : Ty) (p : Pat)
    (h : PatWellFormed true t p) : PatWellFormed priv t p := by
  induction p with
  | wild => trivial
  | orPat p1 p2 ih1 ih2 =>
    dsimp only [PatWellFormed] at h ⊢
    exact ⟨ih1 h.1, ih2 h.2⟩
  | unit | bool _ | intRange _ | pair _ _ | variant _ _ | ref _ =>
    cases t <;> contradiction

theorem listAny_append {α : Type} (p : α → Bool) (xs ys : List α) :
    listAny p (xs ++ ys) = (listAny p xs || listAny p ys) := by
  induction xs with
  | nil =>
    change listAny p ys = (false || listAny p ys)
    cases listAny p ys <;> rfl
  | cons x xs' ih =>
    change (p x || listAny p (xs' ++ ys)) = ((p x || listAny p xs') || listAny p ys)
    rw [ih]
    cases p x <;> cases listAny p xs' <;> cases listAny p ys <;> rfl

theorem patsMatchVals_append (ps1 ps2 : List Pat) (vs1 vs2 : List Val)
    (hlen : ps1.length = vs1.length) :
    patsMatchVals (ps1 ++ ps2) (vs1 ++ vs2) = (patsMatchVals ps1 vs1 && patsMatchVals ps2 vs2) := by
  induction ps1 generalizing vs1 with
  | nil =>
    cases vs1 with
    | nil =>
      change patsMatchVals ps2 vs2 = (true && patsMatchVals ps2 vs2)
      cases patsMatchVals ps2 vs2 <;> rfl
    | cons _ _ => contradiction
  | cons p ps1' ih =>
    cases vs1 with
    | nil => contradiction
    | cons v vs1' =>
      have hlen' : ps1'.length = vs1'.length := Nat.succ_inj.mp hlen
      change (p.matchesVal v && patsMatchVals (ps1' ++ ps2) (vs1' ++ vs2)) =
        ((p.matchesVal v && patsMatchVals ps1' vs1') && patsMatchVals ps2 vs2)
      rw [ih vs1' hlen']
      cases p.matchesVal v <;> cases patsMatchVals ps1' vs1' <;> cases patsMatchVals ps2 vs2 <;> rfl

theorem patsMatchVals_wilds {k : Nat} {vs : List Val} (hlen : vs.length = k) :
    patsMatchVals (listReplicate k .wild) vs = true := by
  induction k generalizing vs with
  | zero =>
    cases vs with
    | nil => rfl
    | cons _ _ => contradiction
  | succ k' ih =>
    cases vs with
    | nil => contradiction
    | cons v vs' =>
      have hlen' : vs'.length = k' := Nat.succ_inj.mp hlen
      change (Pat.wild.matchesVal v && patsMatchVals (listReplicate k' .wild) vs') = true
      rw [ih hlen']
      rfl

theorem patsMatchVals_length_eq {ps : List Pat} {vs : List Val}
    (hm : patsMatchVals ps vs = true) : ps.length = vs.length := by
  induction ps generalizing vs with
  | nil =>
    cases vs with
    | nil => rfl
    | cons _ _ => contradiction
  | cons p ps' ih =>
    cases vs with
    | nil => contradiction
    | cons v vs' =>
      rcases boolAnd_eq_true hm with ⟨_, hrest⟩
      exact congrArg Nat.succ (ih hrest)

/-- Head-pattern or-freedom predicate on `MatrixRow`. -/
noncomputable def RowHeadOrFree (r : MatrixRow) : Prop :=
  ∀ p ps, r.pats = p :: ps → p.isOrFreeHead = true

noncomputable def MatrixHeadOrFree (rows : List MatrixRow) : Prop :=
  ∀ r, r ∈ rows → RowHeadOrFree r

theorem expandHeadOrRow_wellFormed (cols : List ColCtx) (r : MatrixRow)
    (hWF : RowWellFormed cols r.pats) :
    ∀ q, q ∈ expandHeadOrRow r → RowWellFormed cols q.pats := by
  rcases r with ⟨pats, g, idx⟩
  cases pats with
  | nil =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hnil
    · exact hWF
    · exact False.elim (List.not_mem_nil hnil)
  | cons p ps =>
    cases cols with
    | nil => contradiction
    | cons c cs =>
      intro q hq
      dsimp only [expandHeadOrRow] at hq
      rcases List.mem_map.mp hq with ⟨qPat, hqPat, rfl⟩
      refine ⟨?_, hWF.2⟩
      have hmono : ∀ pat, PatWellFormed c.privUninhabited c.ty pat →
          ∀ q0, q0 ∈ expandHeadOrPat pat → PatWellFormed c.privUninhabited c.ty q0 := by
        intro pat
        induction pat with
        | orPat p1 p2 ih1 ih2 =>
          intro hp q0 hq0
          rcases List.mem_append.mp hq0 with h1 | h2
          · exact ih1 hp.1 q0 h1
          · exact ih2 hp.2 q0 h2
        | wild | unit | bool _ | intRange _ | pair _ _ | variant _ _ | ref _ =>
          intro hp q0 hq0
          rcases List.mem_cons.mp hq0 with rfl | hnil
          · exact hp
          · exact False.elim (List.not_mem_nil hnil)
      exact hmono p hWF.1 qPat hqPat

theorem expandHeadOrRow_headOrFree (r : MatrixRow) :
    ∀ q, q ∈ expandHeadOrRow r → RowHeadOrFree q := by
  rcases r with ⟨pats, g, idx⟩
  cases pats with
  | nil =>
    intro q hq p ps hEq
    rcases List.mem_cons.mp hq with rfl | hnil
    · contradiction
    · exact False.elim (List.not_mem_nil hnil)
  | cons p ps =>
    intro q hq q' ps' hEq
    dsimp only [expandHeadOrRow] at hq
    rcases List.mem_map.mp hq with ⟨qPat, hqPat, hqEq⟩
    have hqOF := expandHeadOrPat_orFree p qPat hqPat
    rw [← hqEq] at hEq
    cases hEq
    exact hqOF

theorem expandHeadOrRows_wellFormed (cols : List ColCtx) (rows : List MatrixRow)
    (hWF : MatrixWellFormed cols rows) :
    MatrixWellFormed cols (expandHeadOrRows rows) := by
  induction rows with
  | nil =>
    intro q hq
    exact False.elim (List.not_mem_nil hq)
  | cons r rs ih =>
    intro q hq
    rcases List.mem_append.mp hq with h1 | h2
    · exact expandHeadOrRow_wellFormed cols r (hWF r List.mem_cons_self) q h1
    · exact ih (fun r0 hr0 => hWF r0 (List.mem_cons_of_mem r hr0)) q h2

theorem expandHeadOrRows_headOrFree (rows : List MatrixRow) :
    MatrixHeadOrFree (expandHeadOrRows rows) := by
  induction rows with
  | nil =>
    intro q hq
    exact False.elim (List.not_mem_nil hq)
  | cons r rs ih =>
    intro q hq
    rcases List.mem_append.mp hq with h1 | h2
    · exact expandHeadOrRow_headOrFree r q h1
    · exact ih q h2

theorem rowsUnguardedMatch_expandHeadOrRow_iff (r : MatrixRow) (vs : List Val) :
    rowsUnguardedMatch (expandHeadOrRow r) vs = ((!r.isUnderGuard) && patsMatchVals r.pats vs) := by
  rcases r with ⟨pats, g, idx⟩
  cases pats with
  | nil =>
    dsimp only [expandHeadOrRow, rowsUnguardedMatch, listAny]
    cases ((!g) && patsMatchVals [] vs) <;> rfl
  | cons p ps =>
    cases vs with
    | nil =>
      have hNone : rowsUnguardedMatch (expandHeadOrRow ⟨p :: ps, g, idx⟩) [] = false := by
        cases hres : rowsUnguardedMatch (expandHeadOrRow ⟨p :: ps, g, idx⟩) [] with
        | false => rfl
        | true =>
          rcases (listAny_iff _ _).mp hres with ⟨q, hq, hm⟩
          dsimp only [expandHeadOrRow] at hq
          rcases List.mem_map.mp hq with ⟨_, _, rfl⟩
          rcases boolAnd_eq_true hm with ⟨_, hpm⟩
          contradiction
      rw [hNone]
      cases g <;> rfl
    | cons v vsTail =>
      cases hb : ((!g) && patsMatchVals (p :: ps) (v :: vsTail)) with
      | true =>
        rcases boolAnd_eq_true hb with ⟨hgF, hpm⟩
        rcases boolAnd_eq_true hpm with ⟨hpv, hpsvs⟩
        rcases (matchesVal_expandHeadOrPat_iff p v).mp hpv with ⟨qPat, hqPat, hqv⟩
        apply (listAny_iff _ _).mpr
        refine ⟨{ pats := qPat :: ps, isUnderGuard := g, armIdx := idx }, ?_, ?_⟩
        · dsimp only [expandHeadOrRow]
          exact List.mem_map.mpr ⟨qPat, hqPat, rfl⟩
        · exact boolAnd_intro hgF (boolAnd_intro hqv hpsvs)
      | false =>
        apply (listAny_eq_false_iff _ _).mpr
        intro q hq
        dsimp only [expandHeadOrRow] at hq
        rcases List.mem_map.mp hq with ⟨qPat, hqPat, rfl⟩
        cases hqres : ((!g) && patsMatchVals (qPat :: ps) (v :: vsTail)) with
        | false => rfl
        | true =>
          rcases boolAnd_eq_true hqres with ⟨hgF, hpm⟩
          rcases boolAnd_eq_true hpm with ⟨hqv, hpsvs⟩
          have hpv : p.matchesVal v = true := (matchesVal_expandHeadOrPat_iff p v).mpr ⟨qPat, hqPat, hqv⟩
          have htrue : ((!g) && patsMatchVals (p :: ps) (v :: vsTail)) = true :=
            boolAnd_intro hgF (boolAnd_intro hpv hpsvs)
          rw [htrue] at hb
          contradiction

theorem rowsUnguardedMatch_expandHeadOrRows (rows : List MatrixRow) (vs : List Val) :
    rowsUnguardedMatch (expandHeadOrRows rows) vs = rowsUnguardedMatch rows vs := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    dsimp only [expandHeadOrRows, rowsUnguardedMatch]
    rw [listAny_append]
    change (rowsUnguardedMatch (expandHeadOrRow r) vs || rowsUnguardedMatch (expandHeadOrRows rs) vs) =
      (((!r.isUnderGuard) && patsMatchVals r.pats vs) || rowsUnguardedMatch rs vs)
    rw [rowsUnguardedMatch_expandHeadOrRow_iff, ih]

/-- Base-case behavior when `stillUseful = false`: `stillUseful` stays `false` forever. -/
theorem evalBaseRows_false_fst (rows : List MatrixRow) :
    (evalBaseRows false rows).1 = false := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    dsimp only [evalBaseRows]
    exact ih

/-- Base-case completeness at `cols = []` when `MatrixWellFormed [] rows`:
`evalBaseRows true rows` leaves `stillUseful = false` iff some unguarded row matches `[]`. -/
theorem evalBaseRows_true_iff (rows : List MatrixRow) (hWF : MatrixWellFormed [] rows) :
    (evalBaseRows true rows).1 = false ↔ rowsUnguardedMatch rows [] = true := by
  induction rows with
  | nil =>
    constructor
    · intro h; contradiction
    · intro h; contradiction
  | cons r rs ih =>
    have hrNil : r.pats = [] := by
      have hrwf := hWF r List.mem_cons_self
      cases hp : r.pats with
      | nil => rfl
      | cons _ _ => rw [hp] at hrwf; contradiction
    have hrsWF : MatrixWellFormed [] rs := fun r0 hr0 => hWF r0 (List.mem_cons_of_mem r hr0)
    dsimp only [evalBaseRows, rowsUnguardedMatch, listAny]
    cases hg : r.isUnderGuard with
    | false =>
      rw [hrNil, Bool.and_false, evalBaseRows_false_fst]
      constructor
      · intro _; rfl
      · intro _; rfl
    | true =>
      rw [hrNil]
      simp only [Bool.and_true]
      exact ih hrsWF

/-- Base-case witness soundness: if `(evalBaseRows true rows).1 = true`, then
`rowsUnguardedMatch rows [] = false`. -/
theorem evalBaseRows_witness_sound (rows : List MatrixRow) (hWF : MatrixWellFormed [] rows)
    (htrue : (evalBaseRows true rows).1 = true) :
    rowsUnguardedMatch rows [] = false := by
  cases hm : rowsUnguardedMatch rows [] with
  | false => rfl
  | true =>
    have hf := (evalBaseRows_true_iff rows hWF).mpr hm
    rw [hf] at htrue
    contradiction

/-- Exact semantic decomposition of a concrete constructor match `(col, v) ~> (c, subVs)`. -/
noncomputable def ValidCtorMatch (col : ColCtx) (c : Ctor) (v : Val) (subVs : List Val) : Prop :=
  match c with
  | .privateUninhabited => col.privUninhabited = true ∧ subVs = []
  | .unit => col.privUninhabited = false ∧ col.ty = .unit ∧ v = .unit ∧ subVs = []
  | .bool b => col.privUninhabited = false ∧ col.ty = .bool ∧ v = .bool b ∧ subVs = []
  | .intRange r =>
    col.privUninhabited = false ∧ col.ty = .u8 ∧
    ∃ n, n ≤ 255 ∧ v = .u8 n ∧ r.contains n = true ∧ subVs = []
  | .pair =>
    col.privUninhabited = false ∧ ∃ v1 v2, v = .pair v1 v2 ∧ subVs = [v1, v2] ∧
    (∃ a b, col.ty = .pair a b ∨ ∃ bVis, col.ty = .struct2 a b bVis)
  | .variant idx =>
    col.privUninhabited = false ∧ ∃ vs nonExh pt sub,
      col.ty = .enum vs nonExh ∧ listGet? vs idx = some pt ∧ v = .ctor idx sub ∧ subVs = [sub]
  | .ref =>
    col.privUninhabited = false ∧ ∃ inner pt, col.ty = .ref inner ∧ v = .ref pt ∧ subVs = [pt]
  | _ => False

theorem validCtorMatch_subCols {col : ColCtx} {c : Ctor} {v : Val} {subVs : List Val}
    (hv : ValidPlaceVal col.validity col.privUninhabited col.ty v)
    (hm : ValidCtorMatch col c v subVs) :
    ColsValidPlaceVal (specializeCol col c) subVs ∧
    subVs.length = (specializeCol col c).length := by
  rcases col with ⟨cty, cpriv, cval, cscrut, cexh⟩
  cases c with
  | privateUninhabited =>
    rcases hm with ⟨_, rfl⟩
    exact ⟨trivial, rfl⟩
  | unit =>
    rcases hm with ⟨_, _, _, rfl⟩
    exact ⟨trivial, rfl⟩
  | bool b =>
    rcases hm with ⟨_, _, _, rfl⟩
    exact ⟨trivial, rfl⟩
  | intRange r =>
    rcases hm with ⟨_, _, n, _, _, _, rfl⟩
    exact ⟨trivial, rfl⟩
  | pair =>
    rcases hm with ⟨hpriv, v1, v2, rfl, rfl, a, b, hty⟩
    dsimp only at hpriv hty
    subst hpriv
    rcases hty with hEq | ⟨bVis, hEq⟩
    · subst hEq
      cases cval <;> (dsimp only [ValidPlaceVal] at hv; exact ⟨⟨hv.1, hv.2, trivial⟩, rfl⟩)
    · subst hEq
      dsimp only [specializeCol]
      cases cval with
      | validOnly =>
        dsimp only [ValidPlaceVal] at hv
        cases bVis with
        | true => exact ⟨⟨hv.1, hv.2, trivial⟩, rfl⟩
        | false =>
          rcases hv with ⟨hv1, hv2⟩
          cases he : tyIsEmpty b with
          | true =>
            have hv2' : ValidPlaceVal .maybeInvalid true b v2 := by
              have htmp : (if tyIsEmpty b = true then ValidPlaceVal .maybeInvalid true b v2
                else ValidPlaceVal .validOnly false b v2) := hv2
              rw [he] at htmp; simp only [ite_true] at htmp; exact htmp
            exact ⟨⟨hv1, hv2', trivial⟩, rfl⟩
          | false =>
            have hv2' : ValidPlaceVal .validOnly false b v2 := by
              have htmp : (if tyIsEmpty b = true then ValidPlaceVal .maybeInvalid true b v2
                else ValidPlaceVal .validOnly false b v2) := hv2
              rw [he] at htmp; simp only [Bool.false_eq_true, ↓reduceIte] at htmp; exact htmp
            exact ⟨⟨hv1, hv2', trivial⟩, rfl⟩
      | maybeInvalid =>
        dsimp only [ValidPlaceVal] at hv
        cases bVis with
        | true => exact ⟨⟨hv.1, hv.2, trivial⟩, rfl⟩
        | false =>
          rcases hv with ⟨hv1, hv2⟩
          cases he : tyIsEmpty b with
          | true =>
            have hv2' : ValidPlaceVal .maybeInvalid true b v2 := by
              have htmp : (if tyIsEmpty b = true then ValidPlaceVal .maybeInvalid true b v2
                else ValidPlaceVal .maybeInvalid false b v2) := hv2
              rw [he] at htmp; simp only [ite_true] at htmp; exact htmp
            exact ⟨⟨hv1, hv2', trivial⟩, rfl⟩
          | false =>
            have hv2' : ValidPlaceVal .maybeInvalid false b v2 := by
              have htmp : (if tyIsEmpty b = true then ValidPlaceVal .maybeInvalid true b v2
                else ValidPlaceVal .maybeInvalid false b v2) := hv2
              rw [he] at htmp; simp only [Bool.false_eq_true, ↓reduceIte] at htmp; exact htmp
            exact ⟨⟨hv1, hv2', trivial⟩, rfl⟩
  | variant idx =>
    rcases hm with ⟨hpriv, vs, nonExh, pt, sub, hty, hget, rfl, rfl⟩
    dsimp only at hpriv hty
    subst hpriv hty
    have hv' : ∃ pt', listGet? vs idx = some pt' ∧ ValidPlaceVal cval false pt' sub := by
      cases cval <;> exact hv
    rcases hv' with ⟨pt', hget', hsub'⟩
    rw [hget] at hget'
    cases hget'
    dsimp only [specializeCol]
    rw [hget]
    exact ⟨⟨hsub', trivial⟩, rfl⟩
  | ref =>
    rcases hm with ⟨hpriv, inner, pt, hty, rfl, rfl⟩
    dsimp only at hpriv hty
    subst hpriv hty
    dsimp only [specializeCol]
    have hv' : ValidPlaceVal .maybeInvalid false inner pt := by
      cases cval <;> exact hv
    exact ⟨⟨hv', trivial⟩, rfl⟩
  | wild | orCtor | missing | nonExhaustive | never => contradiction

/-- Specializing an or-free well-formed pattern `p` along a concrete matching constructor `c`
either yields sub-patterns matching `subVs` identically, or fails iff `p` fails `v`. -/
theorem specializePatHead_ctor_iff
    {col : ColCtx} {c : Ctor} {v : Val} {subVs : List Val}
    (hm : ValidCtorMatch col c v subVs)
    (hsubLen : subVs.length = (specializeCol col c).length)
    (p : Pat) (horFree : p.isOrFreeHead = true)
    (hWF : PatWellFormed col.privUninhabited col.ty p)
    (hSharp : ∀ r pLo pHi, c = .intRange ⟨pLo, pHi⟩ → p = .intRange r →
      (r.lo ≤ pLo ∧ pHi ≤ r.hi) ∨ (∀ n, pLo ≤ n → n ≤ pHi → r.contains n = false)) :
    (∀ subPats, specializePatHead c (specializeCol col c).length p = some subPats →
      subPats.length = subVs.length ∧ patsMatchVals subPats subVs = p.matchesVal v) ∧
    (specializePatHead c (specializeCol col c).length p = none → p.matchesVal v = false) := by
  rcases col with ⟨cty, cpriv, cval, cscrut, cexh⟩
  cases c with
  | privateUninhabited =>
    rcases hm with ⟨hpriv, rfl⟩
    dsimp only at hpriv; subst hpriv
    cases p with
    | wild =>
      refine ⟨?_, ?_⟩
      · intro subPats hsp; cases hsp; exact ⟨rfl, rfl⟩
      · intro hsp; contradiction
    | orPat _ _ => contradiction
    | unit | bool _ | intRange _ | pair _ _ | variant _ _ | ref _ =>
      cases cty <;> contradiction
  | unit =>
    rcases hm with ⟨hpriv, hty, rfl, rfl⟩
    dsimp only at hpriv hty; subst hpriv hty
    cases p with
    | wild =>
      refine ⟨?_, ?_⟩
      · intro subPats hsp; cases hsp; exact ⟨rfl, rfl⟩
      · intro hsp; contradiction
    | unit =>
      refine ⟨?_, ?_⟩
      · intro subPats hsp; cases hsp; exact ⟨rfl, rfl⟩
      · intro hsp; contradiction
    | orPat _ _ => contradiction
    | bool _ | intRange _ | pair _ _ | variant _ _ | ref _ => contradiction
  | bool b =>
    rcases hm with ⟨hpriv, hty, rfl, rfl⟩
    dsimp only at hpriv hty; subst hpriv hty
    cases p with
    | wild =>
      refine ⟨?_, ?_⟩
      · intro subPats hsp; cases hsp; exact ⟨rfl, rfl⟩
      · intro hsp; contradiction
    | bool pb =>
      refine ⟨?_, ?_⟩
      · intro subPats hsp
        dsimp only [specializePatHead, Ctor.isCoveredBy, Pat.headCtor] at hsp
        cases b <;> cases pb <;> first | contradiction | (cases hsp; exact ⟨rfl, rfl⟩)
      · intro hsp
        dsimp only [specializePatHead, Ctor.isCoveredBy, Pat.headCtor] at hsp
        cases b <;> cases pb <;> first | contradiction | rfl
    | orPat _ _ => contradiction
    | unit | intRange _ | pair _ _ | variant _ _ | ref _ => contradiction
  | intRange cr =>
    rcases hm with ⟨hpriv, hty, n, _, rfl, hcrn, rfl⟩
    dsimp only at hpriv hty; subst hpriv hty
    cases p with
    | wild =>
      refine ⟨?_, ?_⟩
      · intro subPats hsp; cases hsp; exact ⟨rfl, rfl⟩
      · intro hsp; contradiction
    | intRange pr =>
      rcases (intRange_contains_iff cr n).mp hcrn with ⟨hcrlo, hcrhi⟩
      refine ⟨?_, ?_⟩
      · intro subPats hsp
        dsimp only [specializePatHead, Ctor.isCoveredBy, Pat.headCtor] at hsp
        cases hcov : cr.isSubrange pr with
        | false => simp only [hcov, Bool.not_false, ite_true] at hsp; contradiction
        | true =>
          simp only [hcov, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hsp
          cases hsp
          rcases (intRange_isSubrange_iff cr pr).mp hcov with ⟨hplo, hphi⟩
          have hprn : pr.contains n = true :=
            (intRange_contains_iff pr n).mpr ⟨Nat.le_trans hplo hcrlo, Nat.le_trans hcrhi hphi⟩
          dsimp only [Pat.matchesVal, patsMatchVals]
          exact ⟨rfl, hprn.symm⟩
      · intro hsp
        dsimp only [specializePatHead, Ctor.isCoveredBy, Pat.headCtor] at hsp
        cases hcov : cr.isSubrange pr with
        | true => simp only [hcov, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hsp; contradiction
        | false =>
          rcases hSharp pr cr.lo cr.hi rfl rfl with ⟨hlo, hhi⟩ | hdisj
          · have hcovT : cr.isSubrange pr = true := (intRange_isSubrange_iff cr pr).mpr ⟨hlo, hhi⟩
            rw [hcovT] at hcov; contradiction
          · dsimp only [Pat.matchesVal]
            exact hdisj n hcrlo hcrhi
    | orPat _ _ => contradiction
    | unit | bool _ | pair _ _ | variant _ _ | ref _ => contradiction
  | pair =>
    rcases hm with ⟨hpriv, v1, v2, rfl, rfl, a, b, hty⟩
    dsimp only at hpriv hty; subst hpriv
    cases p with
    | wild =>
      refine ⟨?_, ?_⟩
      · intro subPats hsp
        dsimp only [specializePatHead] at hsp; cases hsp
        have hlen2 : (specializeCol ⟨cty, false, cval, cscrut, cexh⟩ .pair).length = 2 := by
          rw [← hsubLen]; rfl
        rw [hlen2]
        exact ⟨rfl, rfl⟩
      · intro hsp; contradiction
    | pair p1 p2 =>
      refine ⟨?_, ?_⟩
      · intro subPats hsp
        dsimp only [specializePatHead, Ctor.isCoveredBy, Pat.headCtor] at hsp; cases hsp
        dsimp only [Pat.matchesVal, patsMatchVals]
        cases p1.matchesVal v1 <;> cases p2.matchesVal v2 <;> exact ⟨rfl, rfl⟩
      · intro hsp; contradiction
    | orPat _ _ => contradiction
    | unit | bool _ | intRange _ | variant _ _ | ref _ =>
      rcases hty with rfl | ⟨_, rfl⟩ <;> contradiction
  | variant idx =>
    rcases hm with ⟨hpriv, vs, nonExh, pt, sub, hty, hget, rfl, rfl⟩
    dsimp only at hpriv hty; subst hpriv hty
    cases p with
    | wild =>
      refine ⟨?_, ?_⟩
      · intro subPats hsp
        dsimp only [specializePatHead] at hsp; cases hsp
        have hlen1 : (specializeCol ⟨Ty.enum vs nonExh, false, cval, cscrut, cexh⟩ (.variant idx)).length = 1 := by
          rw [← hsubLen]; rfl
        rw [hlen1]
        exact ⟨rfl, rfl⟩
      · intro hsp; contradiction
    | variant pidx subPat =>
      refine ⟨?_, ?_⟩
      · intro subPats hsp
        dsimp only [specializePatHead, Ctor.isCoveredBy, Pat.headCtor] at hsp
        cases hEq : natBeq idx pidx with
        | false => simp only [hEq, Bool.not_false, ite_true] at hsp; contradiction
        | true =>
          simp only [hEq, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hsp
          cases hsp
          have hEqNat : idx = pidx := natBeq_eq_of_true hEq
          subst hEqNat
          dsimp only [Pat.matchesVal, patsMatchVals]
          rw [natBeq_refl]
          cases subPat.matchesVal sub <;> exact ⟨rfl, rfl⟩
      · intro hsp
        dsimp only [specializePatHead, Ctor.isCoveredBy, Pat.headCtor] at hsp
        cases hEq : natBeq idx pidx with
        | true => simp only [hEq, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hsp; contradiction
        | false =>
          dsimp only [Pat.matchesVal]
          cases hEq' : natBeq pidx idx with
          | true =>
            have hEqNat : pidx = idx := natBeq_eq_of_true hEq'
            subst hEqNat
            rw [natBeq_refl] at hEq; contradiction
          | false => rfl
    | orPat _ _ => contradiction
    | unit | bool _ | intRange _ | pair _ _ | ref _ => contradiction
  | ref =>
    rcases hm with ⟨hpriv, inner, pt, hty, rfl, rfl⟩
    dsimp only at hpriv hty; subst hpriv hty
    cases p with
    | wild =>
      refine ⟨?_, ?_⟩
      · intro subPats hsp
        dsimp only [specializePatHead] at hsp; cases hsp
        have hlen1 : (specializeCol ⟨Ty.ref inner, false, cval, cscrut, cexh⟩ .ref).length = 1 := by
          rw [← hsubLen]; rfl
        rw [hlen1]
        exact ⟨rfl, rfl⟩
      · intro hsp; contradiction
    | ref subPat =>
      refine ⟨?_, ?_⟩
      · intro subPats hsp
        dsimp only [specializePatHead] at hsp; cases hsp
        dsimp only [Pat.matchesVal, patsMatchVals]
        cases subPat.matchesVal pt <;> exact ⟨rfl, rfl⟩
      · intro hsp; contradiction
    | orPat _ _ => contradiction
    | unit | bool _ | intRange _ | pair _ _ | variant _ _ => contradiction
  | wild | orCtor | missing | nonExhaustive | never => contradiction

/-- Single-pattern specialization well-formedness helper. -/
theorem specializePatHead_wellFormed (col : ColCtx) (c : Ctor) (p : Pat) (subPats : List Pat)
    (horFree : p.isOrFreeHead = true) (hpWF : PatWellFormed col.privUninhabited col.ty p)
    (hsp : specializePatHead c (specializeCol col c).length p = some subPats) :
    RowWellFormed (specializeCol col c) subPats := by
  have hWilds : ∀ (subCs : List ColCtx), RowWellFormed subCs (listReplicate subCs.length Pat.wild) := by
    intro subCs
    induction subCs with
    | nil => trivial
    | cons _ scs ihs => exact ⟨trivial, ihs⟩
  cases p with
  | orPat _ _ => contradiction
  | wild =>
    cases c with
    | privateUninhabited =>
      dsimp only [specializePatHead] at hsp; cases hsp
      rcases col with ⟨cty, _, _, _, _⟩; cases cty <;> exact hWilds []
    | wild =>
      dsimp only [specializePatHead] at hsp; cases hsp; exact hWilds _
    | unit =>
      dsimp only [specializePatHead] at hsp; cases hsp; exact hWilds _
    | bool _ =>
      dsimp only [specializePatHead] at hsp; cases hsp; exact hWilds _
    | intRange _ =>
      dsimp only [specializePatHead] at hsp; cases hsp; exact hWilds _
    | pair =>
      dsimp only [specializePatHead] at hsp; cases hsp; exact hWilds _
    | variant _ =>
      dsimp only [specializePatHead] at hsp; cases hsp; exact hWilds _
    | ref =>
      dsimp only [specializePatHead] at hsp; cases hsp; exact hWilds _
    | nonExhaustive =>
      dsimp only [specializePatHead] at hsp; cases hsp; exact hWilds _
    | orCtor =>
      dsimp only [specializePatHead] at hsp; cases hsp; exact hWilds _
    | missing =>
      dsimp only [specializePatHead] at hsp; cases hsp; exact hWilds _
    | never =>
      dsimp only [specializePatHead] at hsp; cases hsp; exact hWilds _
  | unit =>
    rcases col with ⟨cty, cpriv, _, _, _⟩
    cases c with
    | privateUninhabited =>
      dsimp only [specializePatHead] at hsp; cases hsp; cases cty <;> exact trivial
    | unit =>
      dsimp only [specializePatHead] at hsp; cases hsp; cases cty <;> exact trivial
    | wild | bool _ | intRange _ | pair | variant _ | ref | nonExhaustive | orCtor | missing | never =>
      dsimp only [specializePatHead, Ctor.isCoveredBy, Pat.headCtor] at hsp; contradiction
  | bool pb =>
    rcases col with ⟨cty, cpriv, _, _, _⟩
    cases c with
    | privateUninhabited =>
      dsimp only [specializePatHead] at hsp; cases hsp; cases cty <;> exact trivial
    | bool cb =>
      dsimp only [specializePatHead, Ctor.isCoveredBy, Pat.headCtor] at hsp
      cases cb <;> cases pb <;> cases hsp <;> cases cty <;> exact trivial
    | wild | unit | intRange _ | pair | variant _ | ref | nonExhaustive | orCtor | missing | never =>
      dsimp only [specializePatHead, Ctor.isCoveredBy, Pat.headCtor] at hsp; contradiction
  | intRange pr =>
    rcases col with ⟨cty, cpriv, _, _, _⟩
    cases c with
    | privateUninhabited =>
      dsimp only [specializePatHead] at hsp; cases hsp; cases cty <;> exact trivial
    | intRange cr =>
      dsimp only [specializePatHead, Ctor.isCoveredBy, Pat.headCtor] at hsp
      cases hcov : cr.isSubrange pr with
      | false => simp only [hcov, Bool.not_false, ite_true] at hsp; contradiction
      | true =>
        simp only [hcov, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hsp
        cases hsp; cases cty <;> exact trivial
    | wild | unit | bool _ | pair | variant _ | ref | nonExhaustive | orCtor | missing | never =>
      dsimp only [specializePatHead, Ctor.isCoveredBy, Pat.headCtor] at hsp; contradiction
  | pair p1 p2 =>
    rcases col with ⟨cty, cpriv, cval, cscrut, cexh⟩
    cases c with
    | privateUninhabited =>
      dsimp only [specializePatHead] at hsp; cases hsp; cases cty <;> exact trivial
    | pair =>
      dsimp only [specializePatHead] at hsp; cases hsp
      cases cpriv with
      | true => contradiction
      | false =>
        cases cty with
        | pair a b => exact ⟨hpWF.1, hpWF.2, trivial⟩
        | struct2 a b bVis =>
          cases bVis with
          | true => exact ⟨hpWF.1, hpWF.2, trivial⟩
          | false => exact ⟨hpWF.1, patWellFormed_true_to_any _ b p2 hpWF.2, trivial⟩
        | unit | bool | u8 | void | enum _ _ | ref _ => contradiction
    | wild | unit | bool _ | intRange _ | variant _ | ref | nonExhaustive | orCtor | missing | never =>
      dsimp only [specializePatHead, Ctor.isCoveredBy, Pat.headCtor] at hsp; contradiction
  | variant pidx subPat =>
    rcases col with ⟨cty, cpriv, cval, cscrut, cexh⟩
    cases c with
    | privateUninhabited =>
      dsimp only [specializePatHead] at hsp; cases hsp; cases cty <;> exact trivial
    | variant idx =>
      dsimp only [specializePatHead, Ctor.isCoveredBy, Pat.headCtor] at hsp
      cases hEq : natBeq idx pidx with
      | false => simp only [hEq, Bool.not_false, ite_true] at hsp; contradiction
      | true =>
        simp only [hEq, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hsp
        cases hsp
        have hEqNat : idx = pidx := natBeq_eq_of_true hEq
        subst hEqNat
        cases cpriv with
        | true => contradiction
        | false =>
          cases cty with
          | enum vs nonExh =>
            rcases hpWF with ⟨pt, hget, hsub⟩
            dsimp only [specializeCol]
            rw [hget]
            exact ⟨hsub, trivial⟩
          | unit | bool | u8 | void | pair _ _ | struct2 _ _ _ | ref _ => contradiction
    | wild | unit | bool _ | intRange _ | pair | ref | nonExhaustive | orCtor | missing | never =>
      dsimp only [specializePatHead, Ctor.isCoveredBy, Pat.headCtor] at hsp; contradiction
  | ref subPat =>
    rcases col with ⟨cty, cpriv, cval, cscrut, cexh⟩
    cases c with
    | privateUninhabited =>
      dsimp only [specializePatHead] at hsp; cases hsp; cases cty <;> exact trivial
    | ref =>
      dsimp only [specializePatHead] at hsp; cases hsp
      cases cpriv with
      | true => contradiction
      | false =>
        cases cty with
        | ref inner => exact ⟨hpWF, trivial⟩
        | unit | bool | u8 | void | pair _ _ | struct2 _ _ _ | enum _ _ => contradiction
    | wild | unit | bool _ | intRange _ | pair | variant _ | nonExhaustive | orCtor | missing | never =>
      dsimp only [specializePatHead, Ctor.isCoveredBy, Pat.headCtor] at hsp; contradiction

/-- Full matrix specialization well-formedness preservation. -/
theorem specializeRows_wellFormed (col : ColCtx) (cs : List ColCtx) (c : Ctor)
    (rows : List MatrixRow) (hWFRows : MatrixWellFormed (col :: cs) rows)
    (hOrFree : MatrixHeadOrFree rows) :
    MatrixWellFormed (specializeCol col c ++ cs) (specializeRows c (specializeCol col c).length rows) := by
  induction rows with
  | nil =>
    intro r' hr'
    exact False.elim (List.not_mem_nil hr')
  | cons r rs ih =>
    have hrWF := hWFRows r List.mem_cons_self
    have hrOF := hOrFree r List.mem_cons_self
    have ih' := ih (fun r0 hr0 => hWFRows r0 (List.mem_cons_of_mem r hr0))
      (fun r0 hr0 => hOrFree r0 (List.mem_cons_of_mem r hr0))
    dsimp only [specializeRows]
    cases hsRow : specializeRow c (specializeCol col c).length r with
    | none => exact ih'
    | some r' =>
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq'
      · rcases r with ⟨pats, g, idx⟩
        cases pats with
        | nil => contradiction
        | cons p ps =>
          dsimp only [specializeRow] at hsRow
          cases hsp : specializePatHead c (specializeCol col c).length p with
          | none => rw [hsp] at hsRow; contradiction
          | some subPats =>
            rw [hsp] at hsRow; cases hsRow
            have hConcat : ∀ (subCs : List ColCtx) (subPs : List Pat),
                RowWellFormed subCs subPs → RowWellFormed cs ps →
                RowWellFormed (subCs ++ cs) (subPs ++ ps) := by
              intro subCs subPs h1 h2
              induction subCs generalizing subPs with
              | nil =>
                cases subPs with
                | nil => exact h2
                | cons _ _ => contradiction
              | cons sc scs ihc =>
                cases subPs with
                | nil => contradiction
                | cons sp sps => exact ⟨h1.1, ihc sps h1.2⟩
            exact hConcat _ _
              (specializePatHead_wellFormed col c p subPats (hrOF p ps rfl) hrWF.1 hsp)
              hrWF.2
      · exact ih' q hq'

/-- **Exact Row-Matching Equivalence Across Specialization on Constructor `c`**. -/
theorem rowsUnguardedMatch_specializeRows_ctor
    {col : ColCtx} {cs : List ColCtx} {c : Ctor} {v : Val} {subVs vsTail : List Val}
    (hm : ValidCtorMatch col c v subVs)
    (hsubLen : subVs.length = (specializeCol col c).length)
    (rows' : List MatrixRow)
    (hWF : MatrixWellFormed (col :: cs) rows')
    (hOF : MatrixHeadOrFree rows')
    (hSharp : ∀ r0 pLo pHi, c = .intRange ⟨pLo, pHi⟩ →
      (∀ row, row ∈ rows' → row.headCtor = .intRange r0 →
        (r0.lo ≤ pLo ∧ pHi ≤ r0.hi) ∨ (∀ n, pLo ≤ n → n ≤ pHi → r0.contains n = false))) :
    rowsUnguardedMatch (specializeRows c (specializeCol col c).length rows') (subVs ++ vsTail) =
      rowsUnguardedMatch rows' (v :: vsTail) := by
  induction rows' with
  | nil => rfl
  | cons r rs ih =>
    have hWF_rs : MatrixWellFormed (col :: cs) rs := fun r0 hr0 => hWF r0 (List.mem_cons_of_mem r hr0)
    have hOF_rs : MatrixHeadOrFree rs := fun r0 hr0 => hOF r0 (List.mem_cons_of_mem r hr0)
    have hSharp_rs : ∀ r0 pLo pHi, c = .intRange ⟨pLo, pHi⟩ →
        (∀ row, row ∈ rs → row.headCtor = .intRange r0 →
          (r0.lo ≤ pLo ∧ pHi ≤ r0.hi) ∨ (∀ n, pLo ≤ n → n ≤ pHi → r0.contains n = false)) :=
      fun r0 pLo pHi hc row hrow => hSharp r0 pLo pHi hc row (List.mem_cons_of_mem r hrow)
    have ih' := ih hWF_rs hOF_rs hSharp_rs
    have hrWF := hWF r List.mem_cons_self
    have hrOF := hOF r List.mem_cons_self
    rcases r with ⟨pats, g, idx⟩
    cases pats with
    | nil => contradiction
    | cons p ps =>
      have hpSharp : ∀ r0 pLo pHi, c = .intRange ⟨pLo, pHi⟩ → p = .intRange r0 →
          (r0.lo ≤ pLo ∧ pHi ≤ r0.hi) ∨ (∀ n, pLo ≤ n → n ≤ pHi → r0.contains n = false) := by
        intro r0 pLo pHi hc hpEq
        subst hpEq
        exact hSharp r0 pLo pHi hc ⟨Pat.intRange r0 :: ps, g, idx⟩ List.mem_cons_self rfl
      have hPatSpec := specializePatHead_ctor_iff hm hsubLen p (hrOF p ps rfl) hrWF.1 hpSharp
      dsimp only [specializeRows, specializeRow]
      cases hsp : specializePatHead c (specializeCol col c).length p with
      | none =>
        have hpmF := hPatSpec.2 hsp
        dsimp only [rowsUnguardedMatch, listAny, patsMatchVals]
        rw [hpmF]
        simp only [Bool.false_and, Bool.and_false, Bool.false_or]
        exact ih'
      | some subPats =>
        rcases hPatSpec.1 subPats hsp with ⟨hspLen, hspMatch⟩
        dsimp only [rowsUnguardedMatch, listAny, patsMatchVals]
        change (((!g) && patsMatchVals (subPats ++ ps) (subVs ++ vsTail)) ||
            rowsUnguardedMatch (specializeRows c (specializeCol col c).length rs) (subVs ++ vsTail)) =
          (((!g) && (p.matchesVal v && patsMatchVals ps vsTail)) || rowsUnguardedMatch rs (v :: vsTail))
        rw [patsMatchVals_append subPats ps subVs vsTail hspLen, hspMatch, ih']

/-- Exact missing-branch matching equivalence: when `col.privUninhabited = false` and `v` is
disjoint from every non-wildcard head pattern in `rows'`, specializing along `.missing` preserves
unguarded row matching identically. -/
theorem rowsUnguardedMatch_specializeRows_missing
    {col : ColCtx} {cs : List ColCtx} {v : Val} {vsTail : List Val}
    (rows' : List MatrixRow)
    (hWF : MatrixWellFormed (col :: cs) rows')
    (hOF : MatrixHeadOrFree rows')
    (hDisj : ∀ r p ps, r ∈ rows' → r.pats = p :: ps → p ≠ .wild → p.matchesVal v = false) :
    rowsUnguardedMatch (specializeRows .missing 0 rows') vsTail =
      rowsUnguardedMatch rows' (v :: vsTail) := by
  induction rows' with
  | nil => rfl
  | cons r rs ih =>
    have hWF_rs : MatrixWellFormed (col :: cs) rs := fun r0 hr0 => hWF r0 (List.mem_cons_of_mem r hr0)
    have hOF_rs : MatrixHeadOrFree rs := fun r0 hr0 => hOF r0 (List.mem_cons_of_mem r hr0)
    have hDisj_rs : ∀ r0 p0 ps0, r0 ∈ rs → r0.pats = p0 :: ps0 → p0 ≠ .wild → p0.matchesVal v = false :=
      fun r0 p0 ps0 hr0 => hDisj r0 p0 ps0 (List.mem_cons_of_mem r hr0)
    have ih' := ih hWF_rs hOF_rs hDisj_rs
    have hrOF := hOF r List.mem_cons_self
    rcases r with ⟨pats, g, idx⟩
    cases pats with
    | nil =>
      have hrwf := hWF ⟨[], g, idx⟩ List.mem_cons_self
      contradiction
    | cons p ps =>
      dsimp only [specializeRows, specializeRow]
      cases p with
      | wild =>
        have hspW : specializePatHead .missing 0 .wild = some [] := rfl
        rw [hspW]
        dsimp only [rowsUnguardedMatch, listAny, patsMatchVals, Pat.matchesVal, List.nil_append]
        have ih'' : listAny (fun r => !r.isUnderGuard && patsMatchVals r.pats vsTail)
            (specializeRows .missing 0 rs) =
            listAny (fun r => !r.isUnderGuard && patsMatchVals r.pats (v :: vsTail)) rs := ih'
        rw [ih'', Bool.true_and]
      | orPat _ _ =>
        have hbad := hrOF _ ps rfl
        contradiction
      | unit | bool _ | intRange _ | pair _ _ | variant _ _ | ref _ =>
        have hpmF : _ = false := hDisj ⟨_ :: ps, g, idx⟩ _ ps List.mem_cons_self rfl
          (fun hEq => by cases hEq)
        dsimp only [specializePatHead, Ctor.isCoveredBy, Pat.headCtor,
          rowsUnguardedMatch, listAny, patsMatchVals]
        rw [hpmF]
        simp only [Bool.false_and, Bool.and_false, Bool.false_or]
        exact ih'

/-- Helpers for `hasCtor`, `hasConcreteCtor`, `collectIntRanges`, `splitVariantsAux`, and
`List.filterMap` membership. -/
theorem hasCtor_bool_iff (b : Bool) (xs : List Ctor) :
    hasCtor (.bool b) xs = true ↔ Ctor.bool b ∈ xs := by
  induction xs with
  | nil => constructor <;> intro h <;> first | contradiction | exact False.elim (List.not_mem_nil h)
  | cons c cs ih =>
    dsimp only [hasCtor]
    constructor
    · intro h
      rcases boolOr_eq_true h with hEq | hTail
      · cases c with
        | bool cb =>
          have hbe : b = cb := (boolBeq_true_iff b cb).mp hEq
          subst hbe
          exact List.mem_cons_self
        | unit | intRange _ | pair | variant _ | nonExhaustive | ref
        | orCtor | wild | missing | privateUninhabited | never => contradiction
      · exact List.mem_cons_of_mem c (ih.mp hTail)
    · intro h
      rcases List.mem_cons.mp h with hEq | hTail
      · cases hEq
        apply boolOr_intro_left
        exact boolBeq_refl b
      · exact boolOr_intro_right (ih.mpr hTail)

theorem hasCtor_variant_iff (idx : Nat) (xs : List Ctor) :
    hasCtor (.variant idx) xs = true ↔ Ctor.variant idx ∈ xs := by
  induction xs with
  | nil => constructor <;> intro h <;> first | contradiction | exact False.elim (List.not_mem_nil h)
  | cons c cs ih =>
    dsimp only [hasCtor]
    constructor
    · intro h
      rcases boolOr_eq_true h with hEq | hTail
      · cases c with
        | variant j =>
          have hne : idx = j := natBeq_eq_of_true hEq
          subst hne
          exact List.mem_cons_self
        | unit | bool _ | intRange _ | pair | nonExhaustive | ref
        | orCtor | wild | missing | privateUninhabited | never => contradiction
      · exact List.mem_cons_of_mem c (ih.mp hTail)
    · intro h
      rcases List.mem_cons.mp h with hEq | hTail
      · cases hEq
        apply boolOr_intro_left
        exact natBeq_refl idx
      · exact boolOr_intro_right (ih.mpr hTail)

theorem mem_collectIntRanges_iff (r : IntRange) (xs : List Ctor) :
    r ∈ collectIntRanges xs ↔ Ctor.intRange r ∈ xs := by
  induction xs with
  | nil =>
    constructor <;> intro h <;> exact False.elim (List.not_mem_nil h)
  | cons c cs ih =>
    cases c with
    | intRange r0 =>
      dsimp only [collectIntRanges]
      constructor
      · intro h
        rcases List.mem_cons.mp h with rfl | hTail
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih.mp hTail)
      · intro h
        rcases List.mem_cons.mp h with hEq | hTail
        · cases hEq; exact List.mem_cons_self
        · exact List.mem_cons_of_mem r0 (ih.mpr hTail)
    | unit | bool _ | pair | variant _ | nonExhaustive | ref
    | orCtor | wild | missing | privateUninhabited | never =>
      dsimp only [collectIntRanges]
      constructor
      · intro h; exact List.mem_cons_of_mem _ (ih.mp h)
      · intro h
        rcases List.mem_cons.mp h with hEq | hTail
        · cases hEq
        · exact ih.mpr hTail

theorem hasConcreteCtor_iff (xs : List Ctor) :
    hasConcreteCtor xs = true ↔ ∃ c, c ∈ xs ∧ c ≠ .wild := by
  induction xs with
  | nil =>
    constructor
    · intro h; contradiction
    · intro ⟨_, hmem, _⟩; exact False.elim (List.not_mem_nil hmem)
  | cons c cs ih =>
    cases c with
    | wild =>
      dsimp only [hasConcreteCtor]
      constructor
      · intro h
        rcases ih.mp h with ⟨c0, hmem, hne⟩
        exact ⟨c0, List.mem_cons_of_mem _ hmem, hne⟩
      · intro ⟨c0, hmem, hne⟩
        rcases List.mem_cons.mp hmem with rfl | hTail
        · exact False.elim (hne rfl)
        · exact ih.mpr ⟨c0, hTail, hne⟩
    | unit | bool _ | intRange _ | pair | variant _ | nonExhaustive | ref
    | orCtor | missing | privateUninhabited | never =>
      dsimp only [hasConcreteCtor]
      constructor
      · intro _
        exact ⟨_, List.mem_cons_self, fun hEq => by cases hEq⟩
      · intro _; rfl

theorem mem_filterMap_iff {α β : Type} (f : α → Option β) (xs : List α) (y : β) :
    y ∈ xs.filterMap f ↔ ∃ x, x ∈ xs ∧ f x = some y := by
  induction xs with
  | nil =>
    constructor <;> intro h
    · exact False.elim (List.not_mem_nil h)
    · rcases h with ⟨_, hx, _⟩; exact False.elim (List.not_mem_nil hx)
  | cons x xs' ih =>
    dsimp only [List.filterMap]
    cases hx : f x with
    | none =>
      constructor
      · intro h
        rcases ih.mp h with ⟨a, ha, hfa⟩
        exact ⟨a, List.mem_cons_of_mem x ha, hfa⟩
      · intro ⟨a, ha, hfa⟩
        rcases List.mem_cons.mp ha with rfl | hTail
        · rw [hx] at hfa; contradiction
        · exact ih.mpr ⟨a, hTail, hfa⟩
    | some b =>
      constructor
      · intro h
        rcases List.mem_cons.mp h with rfl | hTail
        · exact ⟨x, List.mem_cons_self, hx⟩
        · rcases ih.mp hTail with ⟨a, ha, hfa⟩
          exact ⟨a, List.mem_cons_of_mem x ha, hfa⟩
      · intro ⟨a, ha, hfa⟩
        rcases List.mem_cons.mp ha with rfl | hTail
        · rw [hx] at hfa; cases hfa; exact List.mem_cons_self
        · exact List.mem_cons_of_mem b (ih.mpr ⟨a, hTail, hfa⟩)

theorem listGet?_map_iff {α β : Type} (f : α → β) (xs : List α) (k : Nat) (y : β) :
    listGet? (xs.map f) k = some y ↔ ∃ x, listGet? xs k = some x ∧ f x = y := by
  induction xs generalizing k with
  | nil =>
    cases k <;> constructor <;> intro h
    · contradiction
    · rcases h with ⟨_, hget, _⟩; contradiction
    · contradiction
    · rcases h with ⟨_, hget, _⟩; contradiction
  | cons x xs' ih =>
    cases k with
    | zero =>
      dsimp only [List.map, listGet?]
      constructor
      · intro h; cases h; exact ⟨x, rfl, rfl⟩
      · intro ⟨a, ha, hfa⟩; cases ha; rw [hfa]
    | succ k' =>
      dsimp only [List.map, listGet?]
      exact ih k'

theorem headCtor_mem_heads_of_mem {r : MatrixRow} {rows : List MatrixRow}
    (hr : r ∈ rows) : r.headCtor ∈ matrixHeadCtors rows := by
  unfold matrixHeadCtors
  exact List.mem_map.mpr ⟨r, hr, rfl⟩

theorem headCtor_of_cons {p : Pat} {ps : List Pat} {g : Bool} {idx : Nat} :
    ({ pats := p :: ps, isUnderGuard := g, armIdx := idx } : MatrixRow).headCtor = p.headCtor :=
  rfl

/-- Exact specification of `splitVariantsAux`: relates `(pres, miss, missEmpty)` to `listGet?`
and `hasCtor`. -/
theorem splitVariantsAux_spec :
    ∀ (vvis : List VariantVis) (base : Nat) (seen : List Ctor),
      let (pres, miss, missEmpty) := splitVariantsAux base seen vvis
      (∀ c, c ∈ pres → ∃ k v, listGet? vvis k = some v ∧ c = .variant (base + k) ∧ hasCtor c seen = true) ∧
      (∀ c, c ∈ miss → ∃ k, listGet? vvis k = some .visible ∧ c = .variant (base + k) ∧ hasCtor c seen = false) ∧
      (∀ c, c ∈ missEmpty → ∃ k, listGet? vvis k = some .empty ∧ c = .variant (base + k) ∧ hasCtor c seen = false) ∧
      (∀ k v, listGet? vvis k = some v →
        if hasCtor (.variant (base + k)) seen then .variant (base + k) ∈ pres
        else match v with | .visible => .variant (base + k) ∈ miss | .empty => .variant (base + k) ∈ missEmpty) := by
  intro vvis
  induction vvis with
  | nil =>
    intro base seen
    dsimp only [splitVariantsAux]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro _ h; exact False.elim (List.not_mem_nil h)
    · intro _ h; exact False.elim (List.not_mem_nil h)
    · intro _ h; exact False.elim (List.not_mem_nil h)
    · intro k _ hget; cases k <;> contradiction
  | cons v vs ih =>
    intro base seen
    have ih' := ih (base + 1) seen
    dsimp only [splitVariantsAux]
    rcases ih' with ⟨hPres, hMiss, hEmpty, hCov⟩
    cases hs : hasCtor (.variant base) seen with
    | true =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro c hcMem
        rcases List.mem_cons.mp hcMem with rfl | hTail
        · exact ⟨0, v, rfl, rfl, hs⟩
        · rcases hPres c hTail with ⟨k, v0, hget, rfl, hseen⟩
          refine ⟨k + 1, v0, hget, ?_, hseen⟩
          rw [Nat.add_assoc base 1 k, Nat.add_comm 1 k]
      · intro c hcMem
        rcases hMiss c hcMem with ⟨k, hget, rfl, hseen⟩
        exact ⟨k + 1, hget, by rw [Nat.add_assoc base 1 k, Nat.add_comm 1 k], hseen⟩
      · intro c hcMem
        rcases hEmpty c hcMem with ⟨k, hget, rfl, hseen⟩
        exact ⟨k + 1, hget, by rw [Nat.add_assoc base 1 k, Nat.add_comm 1 k], hseen⟩
      · intro k v0 hget
        cases k with
        | zero =>
          dsimp only [listGet?] at hget; cases hget
          rw [Nat.add_zero, hs]
          exact List.mem_cons_self
        | succ k' =>
          have hstep := hCov k' v0 hget
          have hAdd : base + 1 + k' = base + (k' + 1) := by rw [Nat.add_assoc, Nat.add_comm 1 k']
          rw [hAdd] at hstep
          cases hc' : hasCtor (.variant (base + (k' + 1))) seen with
          | true =>
            rw [hc'] at hstep
            exact List.mem_cons_of_mem _ hstep
          | false =>
            rw [hc'] at hstep
            exact hstep
    | false =>
      cases hv : v with
      | visible =>
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro c hcMem
          rcases hPres c hcMem with ⟨k, v0, hget, rfl, hseen⟩
          exact ⟨k + 1, v0, hget, by rw [Nat.add_assoc base 1 k, Nat.add_comm 1 k], hseen⟩
        · intro c hcMem
          rcases List.mem_cons.mp hcMem with rfl | hTail
          · exact ⟨0, rfl, rfl, hs⟩
          · rcases hMiss c hTail with ⟨k, hget, rfl, hseen⟩
            exact ⟨k + 1, hget, by rw [Nat.add_assoc base 1 k, Nat.add_comm 1 k], hseen⟩
        · intro c hcMem
          rcases hEmpty c hcMem with ⟨k, hget, rfl, hseen⟩
          exact ⟨k + 1, hget, by rw [Nat.add_assoc base 1 k, Nat.add_comm 1 k], hseen⟩
        · intro k v0 hget
          cases k with
          | zero =>
            dsimp only [listGet?] at hget; cases hget
            rw [Nat.add_zero, hs]
            exact List.mem_cons_self
          | succ k' =>
            have hstep := hCov k' v0 hget
            have hAdd : base + 1 + k' = base + (k' + 1) := by rw [Nat.add_assoc, Nat.add_comm 1 k']
            rw [hAdd] at hstep
            cases hc' : hasCtor (.variant (base + (k' + 1))) seen with
            | true => rw [hc'] at hstep; exact hstep
            | false =>
              rw [hc'] at hstep
              cases v0 with
              | visible => exact List.mem_cons_of_mem _ hstep
              | empty => exact hstep
      | empty =>
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro c hcMem
          rcases hPres c hcMem with ⟨k, v0, hget, rfl, hseen⟩
          exact ⟨k + 1, v0, hget, by rw [Nat.add_assoc base 1 k, Nat.add_comm 1 k], hseen⟩
        · intro c hcMem
          rcases hMiss c hcMem with ⟨k, hget, rfl, hseen⟩
          exact ⟨k + 1, hget, by rw [Nat.add_assoc base 1 k, Nat.add_comm 1 k], hseen⟩
        · intro c hcMem
          rcases List.mem_cons.mp hcMem with rfl | hTail
          · exact ⟨0, rfl, rfl, hs⟩
          · rcases hEmpty c hTail with ⟨k, hget, rfl, hseen⟩
            exact ⟨k + 1, hget, by rw [Nat.add_assoc base 1 k, Nat.add_comm 1 k], hseen⟩
        · intro k v0 hget
          cases k with
          | zero =>
            dsimp only [listGet?] at hget; cases hget
            rw [Nat.add_zero, hs]
            exact List.mem_cons_self
          | succ k' =>
            have hstep := hCov k' v0 hget
            have hAdd : base + 1 + k' = base + (k' + 1) := by rw [Nat.add_assoc, Nat.add_comm 1 k']
            rw [hAdd] at hstep
            cases hc' : hasCtor (.variant (base + (k' + 1))) seen with
            | true => rw [hc'] at hstep; exact hstep
            | false =>
              rw [hc'] at hstep
              cases v0 with
              | visible => exact hstep
              | empty => exact List.mem_cons_of_mem _ hstep

theorem mem_splitCtorSet_present_inv (t : Ty) (heads : List Ctor) (c : Ctor)
    (hmem : c ∈ (splitCtorSet (ctorsForTy t) heads).present) :
    match c with
    | .unit => t = .unit
    | .bool _ => t = .bool
    | .intRange r =>
      t = .u8 ∧ 0 ≤ r.lo ∧ r.lo ≤ r.hi ∧ r.hi ≤ 255 ∧
      (∀ r0, r0 ∈ collectIntRanges heads →
        (r0.lo ≤ r.lo ∧ r.hi ≤ r0.hi) ∨ (∀ n, r.lo ≤ n → n ≤ r.hi → r0.contains n = false))
    | .pair => ∃ a b, t = .pair a b ∨ ∃ bVis, t = .struct2 a b bVis
    | .variant idx => ∃ vs nonExh pt, t = .enum vs nonExh ∧ listGet? vs idx = some pt
    | .ref => ∃ inner, t = .ref inner
    | _ => False := by
  cases t with
  | unit =>
    dsimp only [ctorsForTy, splitCtorSet] at hmem
    cases hc : hasConcreteCtor heads with
    | false => rw [hc] at hmem; simp at hmem
    | true =>
      rw [hc] at hmem; simp only [ite_true, List.mem_singleton] at hmem
      subst hmem; rfl
  | bool =>
    dsimp only [ctorsForTy, splitCtorSet] at hmem
    rcases List.mem_append.mp hmem with h1 | h2
    · cases hT : hasCtor (.bool true) heads with
      | false => rw [hT] at h1; simp at h1
      | true =>
        rw [hT] at h1; simp only [ite_true, List.mem_singleton] at h1
        subst h1; rfl
    · cases hF : hasCtor (.bool false) heads with
      | false => rw [hF] at h2; simp at h2
      | true =>
        rw [hF] at h2; simp only [ite_true, List.mem_singleton] at h2
        subst h2; rfl
  | u8 =>
    dsimp only [ctorsForTy, splitCtorSet] at hmem
    rcases (mem_filterMap_iff _ _ _).mp hmem with ⟨p, hpMem, hpSome⟩
    cases hps : p.seen with
    | false => rw [hps] at hpSome; simp at hpSome
    | true =>
      rw [hps] at hpSome; simp only [ite_true, Option.some.injEq] at hpSome
      subst hpSome
      rcases splitIntRanges_sound_and_complete (Nat.zero_le 255) (collectIntRanges heads)
        with ⟨hBounds, _, _, _, hSharp⟩
      rcases hBounds p hpMem with ⟨h0, h1, h2⟩
      refine ⟨rfl, h0, h1, h2, ?_⟩
      intro r0 hr0
      exact hSharp p hpMem r0 hr0
  | void =>
    dsimp only [ctorsForTy, splitCtorSet] at hmem
    exact False.elim (List.not_mem_nil hmem)
  | pair a b =>
    dsimp only [ctorsForTy, splitCtorSet] at hmem
    cases hc : hasConcreteCtor heads with
    | false =>
      rw [hc] at hmem
      simp only [Bool.false_eq_true, ↓reduceIte] at hmem
      cases he : (tyIsEmpty a || tyIsEmpty b) <;>
        (rw [he] at hmem; simp only [Bool.false_eq_true, ↓reduceIte] at hmem;
         exact False.elim (List.not_mem_nil hmem))
    | true =>
      rw [hc] at hmem; simp only [ite_true, List.mem_singleton] at hmem
      subst hmem; exact ⟨a, b, Or.inl rfl⟩
  | struct2 a b bVis =>
    dsimp only [ctorsForTy, splitCtorSet] at hmem
    cases hc : hasConcreteCtor heads with
    | false =>
      rw [hc] at hmem
      simp only [Bool.false_eq_true, ↓reduceIte] at hmem
      cases he : (tyIsEmpty a || (bVis && tyIsEmpty b)) <;>
        (rw [he] at hmem; simp only [Bool.false_eq_true, ↓reduceIte] at hmem;
         exact False.elim (List.not_mem_nil hmem))
    | true =>
      rw [hc] at hmem; simp only [ite_true, List.mem_singleton] at hmem
      subst hmem; exact ⟨a, b, Or.inr ⟨bVis, rfl⟩⟩
  | enum vs nonExh =>
    cases vs with
    | nil =>
      cases nonExh with
      | false =>
        dsimp only [ctorsForTy, splitCtorSet] at hmem
        exact False.elim (List.not_mem_nil hmem)
      | true =>
        dsimp only [ctorsForTy, splitCtorSet] at hmem
        exact False.elim (List.not_mem_nil hmem)
    | cons v0 vs' =>
      dsimp only [ctorsForTy, splitCtorSet] at hmem
      have hSpec := (splitVariantsAux_spec
        ((v0 :: vs').map (fun pt => if tyIsEmpty pt then VariantVis.empty else VariantVis.visible))
        0 heads).1 c hmem
      rcases hSpec with ⟨k, vis, hgetMap, hcEq, _⟩
      rw [Nat.zero_add] at hcEq
      subst hcEq
      rcases (listGet?_map_iff _ _ k vis).mp hgetMap with ⟨pt, hgetPt, _⟩
      exact ⟨v0 :: vs', nonExh, pt, rfl, hgetPt⟩
  | ref inner =>
    dsimp only [ctorsForTy, splitCtorSet] at hmem
    cases hc : hasConcreteCtor heads with
    | false => rw [hc] at hmem; simp at hmem
    | true =>
      rw [hc] at hmem; simp only [ite_true, List.mem_singleton] at hmem
      subst hmem; exact ⟨inner, rfl⟩

/-- Given a present constructor `c` and valid sub-column values `subVs`, construct a valid outer
value `v` matching `c` with `subVs` and satisfying sharp splitting! -/
theorem presentCtor_construct_val
    {col : ColCtx} {heads : List Ctor} {c : Ctor} {subVs : List Val}
    (hcMem : c ∈ (splitColumnCtors col heads).splitCtors)
    (hcNotMiss : c ≠ .missing)
    (hColWF : col.privUninhabited = true → tyIsEmpty col.ty = true ∧ col.validity = .maybeInvalid)
    (hSub : ColsValidPlaceVal (specializeCol col c) subVs) :
    ∃ v, ValidPlaceVal col.validity col.privUninhabited col.ty v ∧
      ValidCtorMatch col c v subVs ∧
      subVs.length = (specializeCol col c).length ∧
      (∀ r0 pLo pHi, c = .intRange ⟨pLo, pHi⟩ → r0 ∈ collectIntRanges heads →
        (r0.lo ≤ pLo ∧ pHi ≤ r0.hi) ∨ (∀ n, pLo ≤ n → n ≤ pHi → r0.contains n = false)) := by
  rcases col with ⟨cty, cpriv, cval, cscrut, cexh⟩
  dsimp only [splitColumnCtors] at hcMem
  cases cpriv with
  | true =>
    dsimp only at hcMem hColWF
    simp only [ite_true, List.mem_singleton] at hcMem
    subst hcMem
    cases subVs with
    | cons _ _ => dsimp only [specializeCol] at hSub; contradiction
    | nil =>
      rcases hColWF rfl with ⟨_, hvalMaybe⟩
      refine ⟨.invalid, ?_, ⟨rfl, rfl⟩, rfl, (fun _ _ _ hbad _ => by cases hbad)⟩
      rw [hvalMaybe]; exact trivial
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hcMem
    rcases List.mem_append.mp hcMem with hPres | hMissOpt
    · have hInv := mem_splitCtorSet_present_inv cty heads c hPres
      cases c with
      | unit =>
        cases subVs with
        | cons _ _ => dsimp only [specializeCol] at hSub; contradiction
        | nil =>
          dsimp only at hInv; subst hInv
          refine ⟨.unit, ?_, ⟨rfl, rfl, rfl, rfl⟩, rfl, (fun _ _ _ hbad _ => by cases hbad)⟩
          cases cval <;> exact trivial
      | bool b =>
        cases subVs with
        | cons _ _ => dsimp only [specializeCol] at hSub; contradiction
        | nil =>
          dsimp only at hInv; subst hInv
          refine ⟨.bool b, ?_, ⟨rfl, rfl, rfl, rfl⟩, rfl, (fun _ _ _ hbad _ => by cases hbad)⟩
          cases cval <;> exact trivial
      | intRange r =>
        cases subVs with
        | cons _ _ => dsimp only [specializeCol] at hSub; contradiction
        | nil =>
          rcases hInv with ⟨htyEq, h0, hle, h255, hSharp⟩
          subst htyEq
          refine ⟨.u8 r.lo, ?_, ?_, rfl, ?_⟩
          · have hle255 : r.lo ≤ 255 := Nat.le_trans hle h255
            cases cval <;> exact hle255
          · refine ⟨rfl, rfl, r.lo, Nat.le_trans hle h255, rfl, ?_, rfl⟩
            exact (intRange_contains_iff r r.lo).mpr ⟨Nat.le_refl r.lo, hle⟩
          · intro r0 pLo pHi hEqR hr0
            cases hEqR
            exact hSharp r0 hr0
      | pair =>
        rcases hInv with ⟨a, b, hEq⟩
        rcases hEq with hPair | ⟨bVis, hStruct⟩
        · subst hPair
          dsimp only [specializeCol, ColsValidPlaceVal] at hSub
          cases subVs with
          | nil => contradiction
          | cons v1 rest =>
            cases rest with
            | nil => exact False.elim hSub.2
            | cons v2 tail =>
              cases tail with
              | cons _ _ => exact False.elim hSub.2.2
              | nil =>
                refine ⟨.pair v1 v2, ?_, ⟨rfl, v1, v2, rfl, rfl, a, b, Or.inl rfl⟩, rfl,
                  (fun _ _ _ hbad _ => by cases hbad)⟩
                cases cval <;> exact ⟨hSub.1, hSub.2.1⟩
        · subst hStruct
          dsimp only [specializeCol, ColsValidPlaceVal] at hSub
          cases subVs with
          | nil => contradiction
          | cons v1 rest =>
            cases rest with
            | nil => exact False.elim hSub.2
            | cons v2 tail =>
              cases tail with
              | cons _ _ => exact False.elim hSub.2.2
              | nil =>
                refine ⟨.pair v1 v2, ?_, ⟨rfl, v1, v2, rfl, rfl, a, b, Or.inr ⟨bVis, rfl⟩⟩, rfl,
                  (fun _ _ _ hbad _ => by cases hbad)⟩
                have hv1 : ValidPlaceVal cval false a v1 := hSub.1
                have hv2 := hSub.2.1
                cases cval with
                | validOnly =>
                  cases bVis with
                  | true => exact ⟨hv1, hv2⟩
                  | false =>
                    dsimp only [ValidPlaceVal]
                    cases he : tyIsEmpty b with
                    | true => rw [he] at hv2; exact ⟨hv1, hv2⟩
                    | false => rw [he] at hv2; exact ⟨hv1, hv2⟩
                | maybeInvalid =>
                  cases bVis with
                  | true => exact ⟨hv1, hv2⟩
                  | false =>
                    dsimp only [ValidPlaceVal]
                    cases he : tyIsEmpty b with
                    | true => rw [he] at hv2; exact ⟨hv1, hv2⟩
                    | false => rw [he] at hv2; exact ⟨hv1, hv2⟩
      | variant idx =>
        rcases hInv with ⟨vs, nonExh, pt, hEq, hget⟩
        subst hEq
        dsimp only [specializeCol] at hSub; rw [hget] at hSub
        cases subVs with
        | nil => contradiction
        | cons sub tail =>
          cases tail with
          | cons _ _ => exact False.elim hSub.2
          | nil =>
            refine ⟨.ctor idx sub, ?_, ⟨rfl, vs, nonExh, pt, sub, rfl, hget, rfl, rfl⟩, ?_,
              (fun _ _ _ hbad _ => by cases hbad)⟩
            · cases cval with
              | validOnly => exact ⟨pt, hget, hSub.1⟩
              | maybeInvalid => exact ⟨pt, hget, hSub.1⟩
            · dsimp only [specializeCol]; rw [hget]; rfl
      | ref =>
        rcases hInv with ⟨inner, hEq⟩
        subst hEq
        dsimp only [specializeCol] at hSub
        cases subVs with
        | nil => contradiction
        | cons pt tail =>
          cases tail with
          | cons _ _ => exact False.elim hSub.2
          | nil =>
            refine ⟨.ref pt, ?_, ⟨rfl, inner, pt, rfl, rfl, rfl⟩, rfl,
              (fun _ _ _ hbad _ => by cases hbad)⟩
            cases cval <;> exact hSub.1
      | wild | orCtor | missing | nonExhaustive | privateUninhabited | never => contradiction
    · cases hadd : !( (splitCtorSet (ctorsForTy cty) heads).missing.isEmpty &&
          ((splitCtorSet (ctorsForTy cty) heads).missingEmpty.isEmpty ||
            (cval.isKnownValid &&
              (cscrut && (match ctorsForTy cty with | .noConstructors => true | _ => false) ||
                cexh))) ) with
      | false =>
        rw [hadd] at hMissOpt; simp at hMissOpt
      | true =>
        rw [hadd] at hMissOpt; simp only [ite_true, List.mem_singleton] at hMissOpt
        exact False.elim (hcNotMiss hMissOpt)

/-- Tracks that every `privUninhabited = true` column in `cols` has emitted `.privateUninhabited`
in a witness stack `ws`, ensuring `WitnessPat.matchesVal` ignores validity differences at private
uninhabited struct fields (such as `struct Priv { pub a: u8, _v: Void }`). -/
noncomputable def WitnessMatchesPriv : List ColCtx → List WitnessPat → Prop
  | [], [] => True
  | c :: cs, w :: ws => (c.privUninhabited = true → w = .privateUninhabited) ∧ WitnessMatchesPriv cs ws
  | _, _ => False

theorem witnessMatchesPriv_append (cs1 cs2 : List ColCtx) (ws1 ws2 : List WitnessPat)
    (h1 : WitnessMatchesPriv cs1 ws1) (h2 : WitnessMatchesPriv cs2 ws2) :
    WitnessMatchesPriv (cs1 ++ cs2) (ws1 ++ ws2) := by
  induction cs1 generalizing ws1 with
  | nil =>
    cases ws1 with
    | nil => exact h2
    | cons _ _ => contradiction
  | cons c cs1' ih =>
    cases ws1 with
    | nil => contradiction
    | cons w ws1' => exact ⟨h1.1, ih ws1' h1.2⟩

theorem witnessMatchesPriv_split (cs1 cs2 : List ColCtx) (ws : List WitnessPat)
    (h : WitnessMatchesPriv (cs1 ++ cs2) ws) :
    ∃ ws1 ws2, ws = ws1 ++ ws2 ∧ WitnessMatchesPriv cs1 ws1 ∧ WitnessMatchesPriv cs2 ws2 := by
  induction cs1 generalizing ws with
  | nil => exact ⟨[], ws, rfl, trivial, h⟩
  | cons c cs1' ih =>
    cases ws with
    | nil => contradiction
    | cons w ws' =>
      rcases ih ws' h.2 with ⟨ws1', ws2, rfl, h1', h2⟩
      exact ⟨w :: ws1', ws2, rfl, ⟨h.1, h1'⟩, h2⟩

theorem witnessesMatchVals_append (cs1 cs2 : List ColCtx) (ws1 ws2 : List WitnessPat)
    (vs1 vs2 : List Val) (hlenW : ws1.length = cs1.length) (hlenV : vs1.length = cs1.length) :
    witnessesMatchVals (cs1 ++ cs2) (ws1 ++ ws2) (vs1 ++ vs2) =
      (witnessesMatchVals cs1 ws1 vs1 && witnessesMatchVals cs2 ws2 vs2) := by
  induction cs1 generalizing ws1 vs1 with
  | nil =>
    cases ws1 with
    | cons _ _ => contradiction
    | nil =>
      cases vs1 with
      | cons _ _ => contradiction
      | nil =>
        change witnessesMatchVals cs2 ws2 vs2 = (true && witnessesMatchVals cs2 ws2 vs2)
        cases witnessesMatchVals cs2 ws2 vs2 <;> rfl
  | cons c cs1' ih =>
    cases ws1 with
    | nil => contradiction
    | cons w ws1' =>
      cases vs1 with
      | nil => contradiction
      | cons v vs1' =>
        have hW' : ws1'.length = cs1'.length := Nat.succ_inj.mp hlenW
        have hV' : vs1'.length = cs1'.length := Nat.succ_inj.mp hlenV
        change (w.matchesVal c.validity v && witnessesMatchVals (cs1' ++ cs2) (ws1' ++ ws2) (vs1' ++ vs2)) =
          ((w.matchesVal c.validity v && witnessesMatchVals cs1' ws1' vs1') && witnessesMatchVals cs2 ws2 vs2)
        rw [ih ws1' vs1' hW' hV']
        cases w.matchesVal c.validity v <;> cases witnessesMatchVals cs1' ws1' vs1' <;>
          cases witnessesMatchVals cs2 ws2 vs2 <;> rfl

theorem witnessesMatchVals_lengths {cs : List ColCtx} {ws : List WitnessPat} {vs : List Val}
    (hm : witnessesMatchVals cs ws vs = true) :
    ws.length = cs.length ∧ vs.length = cs.length := by
  induction cs generalizing ws vs with
  | nil =>
    cases ws <;> cases vs <;> first | contradiction | exact ⟨rfl, rfl⟩
  | cons c cs' ih =>
    cases ws with
    | nil => contradiction
    | cons w ws' =>
      cases vs with
      | nil => contradiction
      | cons v vs' =>
        rcases boolAnd_eq_true hm with ⟨_, hrest⟩
        rcases ih hrest with ⟨h1, h2⟩
        exact ⟨congrArg Nat.succ h1, congrArg Nat.succ h2⟩

theorem witnessMatchesPriv_length {cs : List ColCtx} {ws : List WitnessPat}
    (h : WitnessMatchesPriv cs ws) : ws.length = cs.length := by
  induction cs generalizing ws with
  | nil => cases ws <;> first | contradiction | rfl
  | cons _ _ ih =>
    cases ws with
    | nil => contradiction
    | cons _ _ => exact congrArg Nat.succ (ih h.2)

/-- Witness correctness for `unspecializeStack`: valid sub-witnesses matching `specializeCol col c`
lift back to `col :: cs` matching `(v :: vsTail)`, and preserve `WitnessMatchesPriv`. -/
theorem unspecializeStack_matches_and_priv
    {col : ColCtx} {cs : List ColCtx} {c : Ctor} {v : Val} {subVs vsTail : List Val}
    {subWs : List WitnessPat}
    (hm : ValidCtorMatch col c v subVs)
    (hMatch : witnessesMatchVals (specializeCol col c ++ cs) subWs (subVs ++ vsTail) = true)
    (hPrivWs : WitnessMatchesPriv (specializeCol col c ++ cs) subWs) :
    witnessesMatchVals (col :: cs) (unspecializeStack col c subWs) (v :: vsTail) = true ∧
    WitnessMatchesPriv (col :: cs) (unspecializeStack col c subWs) := by
  rcases witnessMatchesPriv_split (specializeCol col c) cs subWs hPrivWs with
    ⟨wsHead, wsTail, rfl, hPrivHead, hPrivTail⟩
  have hSubLenW : wsHead.length = (specializeCol col c).length := witnessMatchesPriv_length hPrivHead
  have hSubLenV : subVs.length = (specializeCol col c).length := by
    rcases col with ⟨cty, cpriv, cval, cscrut, cexh⟩
    cases c with
    | privateUninhabited => rcases hm with ⟨_, rfl⟩; rfl
    | unit => rcases hm with ⟨_, _, _, rfl⟩; rfl
    | bool _ => rcases hm with ⟨_, _, _, rfl⟩; rfl
    | intRange _ => rcases hm with ⟨_, _, _, _, _, _, rfl⟩; rfl
    | pair =>
      rcases hm with ⟨_, _, _, _, rfl, a, b, hty⟩
      rcases hty with hEq | ⟨bVis, hEq⟩
      · dsimp only at hEq; subst hEq; rfl
      · dsimp only at hEq; subst hEq; rfl
    | variant idx =>
      rcases hm with ⟨_, vs, nonExh, pt, sub, hEq, hget, rfl, rfl⟩
      dsimp only at hEq; subst hEq
      dsimp only [specializeCol]; rw [hget]; rfl
    | ref =>
      rcases hm with ⟨_, inner, pt, hEq, rfl, rfl⟩
      dsimp only at hEq; subst hEq; rfl
    | wild | orCtor | missing | nonExhaustive | never => contradiction
  rw [witnessesMatchVals_append (specializeCol col c) cs wsHead wsTail subVs vsTail hSubLenW hSubLenV] at hMatch
  rcases boolAnd_eq_true hMatch with ⟨hHeadMatch, hTailMatch⟩
  rcases col with ⟨cty, cpriv, cval, cscrut, cexh⟩
  cases c with
  | privateUninhabited =>
    rcases hm with ⟨_, rfl⟩
    cases wsHead with
    | cons _ _ => contradiction
    | nil =>
      rw [List.nil_append]
      dsimp only [unspecializeStack, witnessesMatchVals, WitnessPat.matchesVal, WitnessMatchesPriv]
      exact ⟨boolAnd_intro rfl hTailMatch, ⟨fun _ => rfl, hPrivTail⟩⟩
  | unit =>
    rcases hm with ⟨hpriv, _, rfl, rfl⟩
    dsimp only at hpriv; subst hpriv
    cases wsHead with
    | cons _ _ => contradiction
    | nil =>
      rw [List.nil_append]
      dsimp only [unspecializeStack, witnessesMatchVals, WitnessPat.matchesVal, WitnessMatchesPriv]
      exact ⟨boolAnd_intro rfl hTailMatch, ⟨(fun hbad => by cases hbad), hPrivTail⟩⟩
  | bool b =>
    rcases hm with ⟨hpriv, _, rfl, rfl⟩
    dsimp only at hpriv; subst hpriv
    cases wsHead with
    | cons _ _ => contradiction
    | nil =>
      rw [List.nil_append]
      dsimp only [unspecializeStack, witnessesMatchVals, WitnessPat.matchesVal, WitnessMatchesPriv]
      rw [boolBeq_refl]
      exact ⟨boolAnd_intro rfl hTailMatch, ⟨(fun hbad => by cases hbad), hPrivTail⟩⟩
  | intRange cr =>
    rcases hm with ⟨hpriv, _, n, _, rfl, hcrn, rfl⟩
    dsimp only at hpriv; subst hpriv
    cases wsHead with
    | cons _ _ => contradiction
    | nil =>
      rw [List.nil_append]
      dsimp only [unspecializeStack, witnessesMatchVals, WitnessPat.matchesVal, WitnessMatchesPriv]
      rw [hcrn]
      exact ⟨boolAnd_intro rfl hTailMatch, ⟨(fun hbad => by cases hbad), hPrivTail⟩⟩
  | pair =>
    rcases hm with ⟨hpriv, v1, v2, rfl, rfl, a, b, hty⟩
    dsimp only at hpriv hty; subst hpriv
    rcases hty with rfl | ⟨bVis, rfl⟩
    · dsimp only [specializeCol] at hHeadMatch
      cases wsHead with
      | nil => dsimp only [witnessesMatchVals] at hHeadMatch; contradiction
      | cons w1 ws1 =>
        cases ws1 with
        | nil => dsimp only [witnessesMatchVals] at hHeadMatch; simp only [Bool.and_false] at hHeadMatch; contradiction
        | cons w2 ws2 =>
          cases ws2 with
          | cons _ _ => dsimp only [witnessesMatchVals] at hHeadMatch; simp only [Bool.and_false] at hHeadMatch; contradiction
          | nil =>
            dsimp only [witnessesMatchVals] at hHeadMatch
            rcases boolAnd_eq_true hHeadMatch with ⟨hw1, hw2'⟩
            rcases boolAnd_eq_true hw2' with ⟨hw2, _⟩
            dsimp only [List.cons_append, List.nil_append, unspecializeStack, witnessesMatchVals,
              WitnessPat.matchesVal, WitnessMatchesPriv]
            rw [hw1, hw2]
            exact ⟨boolAnd_intro rfl hTailMatch, ⟨(fun hbad => by cases hbad), hPrivTail⟩⟩
    · dsimp only [specializeCol] at hHeadMatch
      dsimp only [specializeCol, WitnessMatchesPriv] at hPrivHead
      cases wsHead with
      | nil => dsimp only [witnessesMatchVals] at hHeadMatch; contradiction
      | cons w1 ws1 =>
        cases ws1 with
        | nil => dsimp only [witnessesMatchVals] at hHeadMatch; simp only [Bool.and_false] at hHeadMatch; contradiction
        | cons w2 ws2 =>
          cases ws2 with
          | cons _ _ => dsimp only [witnessesMatchVals] at hHeadMatch; simp only [Bool.and_false] at hHeadMatch; contradiction
          | nil =>
            dsimp only [witnessesMatchVals] at hHeadMatch
            rcases boolAnd_eq_true hHeadMatch with ⟨hw1, hw2'⟩
            rcases boolAnd_eq_true hw2' with ⟨hw2, _⟩
            have hw2Col : w2.matchesVal cval v2 = true := by
              cases bVis with
              | true => exact hw2
              | false =>
                cases he : tyIsEmpty b with
                | false => rw [he] at hw2; exact hw2
                | true =>
                  have hpw2 := hPrivHead.2.1
                  rw [he] at hpw2
                  have hw2Eq : w2 = .privateUninhabited := hpw2 rfl
                  rw [hw2Eq]; rfl
            dsimp only [List.cons_append, List.nil_append, unspecializeStack, witnessesMatchVals,
              WitnessPat.matchesVal, WitnessMatchesPriv]
            rw [hw1, hw2Col]
            exact ⟨boolAnd_intro rfl hTailMatch, ⟨(fun hbad => by cases hbad), hPrivTail⟩⟩
  | variant idx =>
    rcases hm with ⟨hpriv, vs, nonExh, pt, sub, hEq, hget, rfl, rfl⟩
    dsimp only at hpriv hEq; subst hpriv hEq
    dsimp only [specializeCol] at hHeadMatch hPrivHead
    rw [hget] at hHeadMatch hPrivHead
    cases wsHead with
    | nil => dsimp only [witnessesMatchVals] at hHeadMatch; contradiction
    | cons w1 ws1 =>
      cases ws1 with
      | cons _ _ => dsimp only [witnessesMatchVals] at hHeadMatch; simp only [Bool.and_false] at hHeadMatch; contradiction
      | nil =>
        dsimp only [witnessesMatchVals] at hHeadMatch
        rcases boolAnd_eq_true hHeadMatch with ⟨hw1, _⟩
        dsimp only [List.cons_append, List.nil_append, unspecializeStack, witnessesMatchVals,
          WitnessPat.matchesVal, WitnessMatchesPriv]
        rw [natBeq_refl, hw1]
        exact ⟨boolAnd_intro rfl hTailMatch, ⟨(fun hbad => by cases hbad), hPrivTail⟩⟩
  | ref =>
    rcases hm with ⟨hpriv, inner, pt, hEq, rfl, rfl⟩
    dsimp only at hpriv hEq; subst hpriv hEq
    dsimp only [specializeCol] at hHeadMatch
    cases wsHead with
    | nil => dsimp only [witnessesMatchVals] at hHeadMatch; contradiction
    | cons w1 ws1 =>
      cases ws1 with
      | cons _ _ => dsimp only [witnessesMatchVals] at hHeadMatch; simp only [Bool.and_false] at hHeadMatch; contradiction
      | nil =>
        dsimp only [witnessesMatchVals] at hHeadMatch
        rcases boolAnd_eq_true hHeadMatch with ⟨hw1, _⟩
        dsimp only [List.cons_append, List.nil_append, unspecializeStack, witnessesMatchVals,
          WitnessPat.matchesVal, WitnessMatchesPriv]
        rw [hw1]
        exact ⟨boolAnd_intro rfl hTailMatch, ⟨(fun hbad => by cases hbad), hPrivTail⟩⟩
  | wild | orCtor | missing | nonExhaustive | never => contradiction

/-- Missing-constructor witness construction: for every `m ∈ (splitColumnCtors col heads).missingCtors`,
constructs a valid value `v` disjoint from every non-wildcard head pattern in `heads` and matched
by `wildFromCtor col.ty m`. -/
theorem missingCtor_construct_val
    {col : ColCtx} {heads : List Ctor} {m : Ctor}
    (hPrivF : col.privUninhabited = false)
    (hmMem : m ∈ (splitColumnCtors col heads).missingCtors) :
    ∃ v, ValidPlaceVal col.validity false col.ty v ∧
      (wildFromCtor col.ty m).matchesVal col.validity v = true ∧
      (∀ p, p.isOrFreeHead = true → PatWellFormed false col.ty p → p.headCtor ∈ heads → p ≠ .wild →
        p.matchesVal v = false) := by
  have hNoNonExhInEmpty : ∀ (cset : CtorSet) (c0 : Ctor),
      c0 ∈ (splitCtorSet cset heads).missingEmpty → c0 = .nonExhaustive → False := by
    intro cset c0 hc0 hEq
    subst hEq
    cases cset with
    | unit =>
      dsimp only [splitCtorSet] at hc0
      cases hc : hasConcreteCtor heads with
      | true => rw [hc] at hc0; simp only [ite_true] at hc0; exact False.elim (List.not_mem_nil hc0)
      | false =>
        rw [hc] at hc0; simp only [Bool.false_eq_true, ↓reduceIte] at hc0
        exact False.elim (List.not_mem_nil hc0)
    | bool => exact False.elim (List.not_mem_nil hc0)
    | u8 => exact False.elim (List.not_mem_nil hc0)
    | pair empty =>
      dsimp only [splitCtorSet] at hc0
      cases hc : hasConcreteCtor heads with
      | true => rw [hc] at hc0; simp only [ite_true] at hc0; exact False.elim (List.not_mem_nil hc0)
      | false =>
        rw [hc] at hc0; simp only [Bool.false_eq_true, ↓reduceIte] at hc0
        cases empty with
        | false => exact False.elim (List.not_mem_nil hc0)
        | true =>
          rcases List.mem_cons.mp hc0 with hbad | hnil
          · cases hbad
          · exact False.elim (List.not_mem_nil hnil)
    | ref =>
      dsimp only [splitCtorSet] at hc0
      cases hc : hasConcreteCtor heads with
      | true => rw [hc] at hc0; simp only [ite_true] at hc0; exact False.elim (List.not_mem_nil hc0)
      | false =>
        rw [hc] at hc0; simp only [Bool.false_eq_true, ↓reduceIte] at hc0
        exact False.elim (List.not_mem_nil hc0)
    | noConstructors =>
      rcases List.mem_cons.mp hc0 with hbad | hnil
      · cases hbad
      · exact False.elim (List.not_mem_nil hnil)
    | variants vis nonExh =>
      have hSpec := (splitVariantsAux_spec vis 0 heads).2.2.1 .nonExhaustive hc0
      rcases hSpec with ⟨_, _, hbad, _⟩
      cases hbad
  have hNonExhInMissing : ∀ (cset : CtorSet),
      .nonExhaustive ∈ (splitCtorSet cset heads).missing →
      ∃ vis, cset = .variants vis true := by
    intro cset hmem
    cases cset with
    | unit =>
      dsimp only [splitCtorSet] at hmem
      cases hc : hasConcreteCtor heads with
      | true => rw [hc] at hmem; exact False.elim (List.not_mem_nil hmem)
      | false =>
        rw [hc] at hmem
        rcases List.mem_cons.mp hmem with hbad | hnil
        · cases hbad
        · exact False.elim (List.not_mem_nil hnil)
    | bool =>
      dsimp only [splitCtorSet] at hmem
      rcases List.mem_append.mp hmem with hT | hF
      · cases h1 : hasCtor (.bool true) heads with
        | true => rw [h1] at hT; exact False.elim (List.not_mem_nil hT)
        | false =>
          rw [h1] at hT
          rcases List.mem_cons.mp hT with hbad | hnil
          · cases hbad
          · exact False.elim (List.not_mem_nil hnil)
      · cases h2 : hasCtor (.bool false) heads with
        | true => rw [h2] at hF; exact False.elim (List.not_mem_nil hF)
        | false =>
          rw [h2] at hF
          rcases List.mem_cons.mp hF with hbad | hnil
          · cases hbad
          · exact False.elim (List.not_mem_nil hnil)
    | u8 =>
      dsimp only [splitCtorSet] at hmem
      rcases (mem_filterMap_iff _ _ _).mp hmem with ⟨p, _, hpSome⟩
      cases hps : p.seen with
      | true => rw [hps] at hpSome; cases hpSome
      | false => rw [hps] at hpSome; cases hpSome
    | pair empty =>
      dsimp only [splitCtorSet] at hmem
      cases hc : hasConcreteCtor heads with
      | true => rw [hc] at hmem; exact False.elim (List.not_mem_nil hmem)
      | false =>
        cases empty with
        | true => rw [hc] at hmem; exact False.elim (List.not_mem_nil hmem)
        | false =>
          rw [hc] at hmem
          rcases List.mem_cons.mp hmem with hbad | hnil
          · cases hbad
          · exact False.elim (List.not_mem_nil hnil)
    | ref =>
      dsimp only [splitCtorSet] at hmem
      cases hc : hasConcreteCtor heads with
      | true => rw [hc] at hmem; exact False.elim (List.not_mem_nil hmem)
      | false =>
        rw [hc] at hmem
        rcases List.mem_cons.mp hmem with hbad | hnil
        · cases hbad
        · exact False.elim (List.not_mem_nil hnil)
    | noConstructors => exact False.elim (List.not_mem_nil hmem)
    | variants vis nonExh =>
      cases nonExh with
      | true => exact ⟨vis, rfl⟩
      | false =>
        dsimp only [splitCtorSet] at hmem
        have hSpec := (splitVariantsAux_spec vis 0 heads).2.1 .nonExhaustive hmem
        rcases hSpec with ⟨_, _, hbad, _⟩
        cases hbad
  rcases col with ⟨cty, cpriv, cval, cscrut, cexh⟩
  dsimp only at hPrivF
  subst hPrivF
  dsimp only [splitColumnCtors] at hmMem
  simp only [Bool.false_eq_true, ↓reduceIte] at hmMem
  cases hnonExhAny : listAny Ctor.isNonExhaustive
      ((splitCtorSet (ctorsForTy cty) heads).missing ++
        if cval.isKnownValid ||
            (cscrut && match ctorsForTy cty with | .noConstructors => true | _ => false) ||
            cexh
        then [] else (splitCtorSet (ctorsForTy cty) heads).missingEmpty) with
  | true =>
    rw [hnonExhAny] at hmMem
    simp only [ite_true, List.mem_singleton] at hmMem
    subst hmMem
    rcases (listAny_iff _ _).mp hnonExhAny with ⟨c0, hc0Mem, hc0NE⟩
    have hc0Eq : c0 = .nonExhaustive := by cases c0 <;> first | contradiction | rfl
    subst hc0Eq
    have hc0InMiss : Ctor.nonExhaustive ∈ (splitCtorSet (ctorsForTy cty) heads).missing := by
      rcases List.mem_append.mp hc0Mem with h1 | h2
      · exact h1
      · cases hcan : (cval.isKnownValid ||
            (cscrut && match ctorsForTy cty with | .noConstructors => true | _ => false) ||
            cexh) with
        | true => rw [hcan] at h2; exact False.elim (List.not_mem_nil h2)
        | false =>
          rw [hcan] at h2
          exact False.elim (hNoNonExhInEmpty (ctorsForTy cty) .nonExhaustive h2 rfl)
    rcases hNonExhInMissing (ctorsForTy cty) hc0InMiss with ⟨vis, hcsetEq⟩
    have hEnum : ∃ vs, cty = .enum vs true := by
      cases cty with
      | enum vs nonExh =>
        cases nonExh with
        | true => exact ⟨vs, rfl⟩
        | false =>
          cases vs with
          | nil => dsimp only [ctorsForTy] at hcsetEq; cases hcsetEq
          | cons _ _ => dsimp only [ctorsForTy] at hcsetEq; cases hcsetEq
      | unit | bool | u8 | void | pair _ _ | struct2 _ _ _ | ref _ =>
        dsimp only [ctorsForTy] at hcsetEq; cases hcsetEq
    rcases hEnum with ⟨vs, rfl⟩
    refine ⟨.hiddenCtor 0, ?_, rfl, ?_⟩
    · cases cval <;> trivial
    · intro p hpOF hpWF _ hpNW
      cases p with
      | wild => exact False.elim (hpNW rfl)
      | orPat _ _ => contradiction
      | variant _ _ => rfl
      | unit | bool _ | intRange _ | pair _ _ | ref _ => contradiction
  | false =>
    rw [hnonExhAny] at hmMem
    simp only [Bool.false_eq_true, ↓reduceIte] at hmMem
    rcases List.mem_append.mp hmMem with hMiss | hMissEmptyOpt
    · cases cty with
      | unit =>
        dsimp only [ctorsForTy, splitCtorSet] at hMiss
        cases hc : hasConcreteCtor heads with
        | true => rw [hc] at hMiss; exact False.elim (List.not_mem_nil hMiss)
        | false =>
          rw [hc] at hMiss; simp only [Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hMiss
          subst hMiss
          refine ⟨.unit, ?_, rfl, ?_⟩
          · cases cval <;> trivial
          · intro p hpOF hpWF hpHead hpNW
            cases p with
            | wild => exact False.elim (hpNW rfl)
            | orPat _ _ => contradiction
            | unit =>
              have hcon : hasConcreteCtor heads = true := (hasConcreteCtor_iff heads).mpr
                ⟨.unit, hpHead, (fun hbad => by cases hbad)⟩
              rw [hcon] at hc; contradiction
            | bool _ | intRange _ | pair _ _ | variant _ _ | ref _ => contradiction
      | bool =>
        dsimp only [ctorsForTy, splitCtorSet] at hMiss
        rcases List.mem_append.mp hMiss with hT | hF
        · cases hsT : hasCtor (.bool true) heads with
          | true => rw [hsT] at hT; exact False.elim (List.not_mem_nil hT)
          | false =>
            rw [hsT] at hT; simp only [Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hT
            subst hT
            refine ⟨.bool true, ?_, by dsimp only [wildFromCtor, WitnessPat.matchesVal]; rfl, ?_⟩
            · cases cval <;> trivial
            · intro p hpOF hpWF hpHead hpNW
              cases p with
              | wild => exact False.elim (hpNW rfl)
              | orPat _ _ => contradiction
              | bool pb =>
                cases pb with
                | true =>
                  have hbt : hasCtor (.bool true) heads = true := (hasCtor_bool_iff true heads).mpr hpHead
                  rw [hbt] at hsT; contradiction
                | false => rfl
              | unit | intRange _ | pair _ _ | variant _ _ | ref _ => contradiction
        · cases hsF : hasCtor (.bool false) heads with
          | true => rw [hsF] at hF; exact False.elim (List.not_mem_nil hF)
          | false =>
            rw [hsF] at hF; simp only [Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hF
            subst hF
            refine ⟨.bool false, ?_, by dsimp only [wildFromCtor, WitnessPat.matchesVal]; rfl, ?_⟩
            · cases cval <;> trivial
            · intro p hpOF hpWF hpHead hpNW
              cases p with
              | wild => exact False.elim (hpNW rfl)
              | orPat _ _ => contradiction
              | bool pb =>
                cases pb with
                | false =>
                  have hbf : hasCtor (.bool false) heads = true := (hasCtor_bool_iff false heads).mpr hpHead
                  rw [hbf] at hsF; contradiction
                | true => rfl
              | unit | intRange _ | pair _ _ | variant _ _ | ref _ => contradiction
      | u8 =>
        dsimp only [ctorsForTy, splitCtorSet] at hMiss
        rcases (mem_filterMap_iff _ _ _).mp hMiss with ⟨part, hpMem, hpSome⟩
        cases hps : part.seen with
        | true => rw [hps] at hpSome; cases hpSome
        | false =>
          rw [hps] at hpSome; simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hpSome
          subst hpSome
          rcases splitIntRanges_sound_and_complete (Nat.zero_le 255) (collectIntRanges heads)
            with ⟨hBounds, _, _, hUnseen, _⟩
          rcases hBounds part hpMem with ⟨_, hpLe, hpHi⟩
          refine ⟨.u8 part.lo, ?_, ?_, ?_⟩
          · have hle255 : part.lo ≤ 255 := Nat.le_trans hpLe hpHi
            cases cval <;> exact hle255
          · dsimp only [wildFromCtor, WitnessPat.matchesVal]
            exact (intRange_contains_iff ⟨part.lo, part.hi⟩ part.lo).mpr ⟨Nat.le_refl part.lo, hpLe⟩
          · intro p hpOF hpWF hpHead hpNW
            cases p with
            | wild => exact False.elim (hpNW rfl)
            | orPat _ _ => contradiction
            | intRange pr =>
              have hpr : pr ∈ collectIntRanges heads := (mem_collectIntRanges_iff pr heads).mpr hpHead
              exact hUnseen part hpMem hps pr hpr part.lo (Nat.le_refl part.lo) hpLe
            | unit | bool _ | pair _ _ | variant _ _ | ref _ => contradiction
      | void =>
        dsimp only [ctorsForTy, splitCtorSet] at hMiss
        exact False.elim (List.not_mem_nil hMiss)
      | pair a b =>
        dsimp only [ctorsForTy, splitCtorSet] at hMiss
        cases hc : hasConcreteCtor heads with
        | true => rw [hc] at hMiss; exact False.elim (List.not_mem_nil hMiss)
        | false =>
          rw [hc] at hMiss; simp only [Bool.false_eq_true, ↓reduceIte] at hMiss
          cases he : (tyIsEmpty a || tyIsEmpty b) with
          | true => rw [he] at hMiss; exact False.elim (List.not_mem_nil hMiss)
          | false =>
            rw [he] at hMiss; simp only [Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hMiss
            subst hMiss
            rcases boolOr_eq_false.mp he with ⟨haNE, hbNE⟩
            rcases inhabitValidPlace_nonEmpty haNE with ⟨v1, hv1⟩
            rcases inhabitValidPlace_nonEmpty hbNE with ⟨v2, hv2⟩
            refine ⟨.pair v1 v2, ?_, ?_, ?_⟩
            · cases cval with
              | validOnly => exact ⟨hv1, hv2⟩
              | maybeInvalid => exact ⟨validPlaceVal_valid_to_maybe hv1, validPlaceVal_valid_to_maybe hv2⟩
            · dsimp only [wildFromCtor, WitnessPat.matchesVal, WitnessPat.wildcardForTy]
              rw [haNE, hbNE]; rfl
            · intro p hpOF hpWF hpHead hpNW
              cases p with
              | wild => exact False.elim (hpNW rfl)
              | orPat _ _ => contradiction
              | pair _ _ =>
                have hcon : hasConcreteCtor heads = true := (hasConcreteCtor_iff heads).mpr
                  ⟨.pair, hpHead, (fun hbad => by cases hbad)⟩
                rw [hcon] at hc; contradiction
              | unit | bool _ | intRange _ | variant _ _ | ref _ => contradiction
      | struct2 a b bVis =>
        dsimp only [ctorsForTy, splitCtorSet] at hMiss
        cases hc : hasConcreteCtor heads with
        | true => rw [hc] at hMiss; exact False.elim (List.not_mem_nil hMiss)
        | false =>
          rw [hc] at hMiss; simp only [Bool.false_eq_true, ↓reduceIte] at hMiss
          cases he : (tyIsEmpty a || (bVis && tyIsEmpty b)) with
          | true => rw [he] at hMiss; exact False.elim (List.not_mem_nil hMiss)
          | false =>
            rw [he] at hMiss; simp only [Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hMiss
            subst hMiss
            rcases boolOr_eq_false.mp he with ⟨haNE, hbVis⟩
            rcases inhabitValidPlace_nonEmpty haNE with ⟨v1, hv1⟩
            cases bVis with
            | true =>
              have hbNE : tyIsEmpty b = false := by
                cases h : tyIsEmpty b <;> first | rfl | (rw [h] at hbVis; contradiction)
              rcases inhabitValidPlace_nonEmpty hbNE with ⟨v2, hv2⟩
              refine ⟨.pair v1 v2, ?_, ?_, ?_⟩
              · cases cval with
                | validOnly => exact ⟨hv1, hv2⟩
                | maybeInvalid => exact ⟨validPlaceVal_valid_to_maybe hv1, validPlaceVal_valid_to_maybe hv2⟩
              · dsimp only [wildFromCtor, WitnessPat.matchesVal, WitnessPat.wildcardForTy]
                rw [haNE, hbNE]; rfl
              · intro p hpOF hpWF hpHead hpNW
                cases p with
                | wild => exact False.elim (hpNW rfl)
                | orPat _ _ => contradiction
                | pair _ _ =>
                  have hcon : hasConcreteCtor heads = true := (hasConcreteCtor_iff heads).mpr
                    ⟨.pair, hpHead, (fun hbad => by cases hbad)⟩
                  rw [hcon] at hc; contradiction
                | unit | bool _ | intRange _ | variant _ _ | ref _ => contradiction
            | false =>
              cases heB : tyIsEmpty b with
              | true =>
                refine ⟨.pair v1 .invalid, ?_, ?_, ?_⟩
                · cases cval with
                  | validOnly =>
                    dsimp only [ValidPlaceVal]; rw [heB]; simp only [ite_true]; exact ⟨hv1, trivial⟩
                  | maybeInvalid =>
                    dsimp only [ValidPlaceVal]; rw [heB]; simp only [ite_true]
                    exact ⟨validPlaceVal_valid_to_maybe hv1, trivial⟩
                · dsimp only [wildFromCtor, WitnessPat.matchesVal, WitnessPat.wildcardForTy]
                  rw [haNE]; rfl
                · intro p hpOF hpWF hpHead hpNW
                  cases p with
                  | wild => exact False.elim (hpNW rfl)
                  | orPat _ _ => contradiction
                  | pair _ _ =>
                    have hcon : hasConcreteCtor heads = true := (hasConcreteCtor_iff heads).mpr
                      ⟨.pair, hpHead, (fun hbad => by cases hbad)⟩
                    rw [hcon] at hc; contradiction
                  | unit | bool _ | intRange _ | variant _ _ | ref _ => contradiction
              | false =>
                rcases inhabitValidPlace_nonEmpty heB with ⟨v2, hv2⟩
                refine ⟨.pair v1 v2, ?_, ?_, ?_⟩
                · cases cval with
                  | validOnly =>
                    dsimp only [ValidPlaceVal]; rw [heB]; simp only [Bool.false_eq_true, ↓reduceIte]
                    exact ⟨hv1, hv2⟩
                  | maybeInvalid =>
                    dsimp only [ValidPlaceVal]; rw [heB]; simp only [Bool.false_eq_true, ↓reduceIte]
                    exact ⟨validPlaceVal_valid_to_maybe hv1, validPlaceVal_valid_to_maybe hv2⟩
                · dsimp only [wildFromCtor, WitnessPat.matchesVal, WitnessPat.wildcardForTy]
                  rw [haNE]; rfl
                · intro p hpOF hpWF hpHead hpNW
                  cases p with
                  | wild => exact False.elim (hpNW rfl)
                  | orPat _ _ => contradiction
                  | pair _ _ =>
                    have hcon : hasConcreteCtor heads = true := (hasConcreteCtor_iff heads).mpr
                      ⟨.pair, hpHead, (fun hbad => by cases hbad)⟩
                    rw [hcon] at hc; contradiction
                  | unit | bool _ | intRange _ | variant _ _ | ref _ => contradiction
      | enum vs nonExh =>
        cases vs with
        | nil =>
          cases nonExh with
          | false => dsimp only [ctorsForTy, splitCtorSet] at hMiss; exact False.elim (List.not_mem_nil hMiss)
          | true =>
            dsimp only [ctorsForTy, splitCtorSet, splitVariantsAux] at hMiss
            rcases List.mem_cons.mp hMiss with rfl | hnil
            · refine ⟨.hiddenCtor 0, ?_, rfl, ?_⟩
              · cases cval <;> trivial
              · intro p hpOF hpWF _ hpNW
                cases p with
                | wild => exact False.elim (hpNW rfl)
                | orPat _ _ => contradiction
                | variant _ _ => rfl
                | unit | bool _ | intRange _ | pair _ _ | ref _ => contradiction
            · exact False.elim (List.not_mem_nil hnil)
        | cons v0 vs' =>
          dsimp only [ctorsForTy, splitCtorSet] at hMiss
          have hmVar : m ∈ (splitVariantsAux 0 heads
              ((v0 :: vs').map (fun pt => if tyIsEmpty pt then VariantVis.empty else VariantVis.visible))).2.1 := by
            cases hne : nonExh with
            | false => rw [hne] at hMiss; exact hMiss
            | true =>
              rw [hne] at hMiss
              rcases List.mem_append.mp hMiss with hV | hNE
              · exact hV
              · rcases List.mem_cons.mp hNE with rfl | hnil
                · have hbad : listAny Ctor.isNonExhaustive
                      ((splitCtorSet (ctorsForTy (.enum (v0 :: vs') true)) heads).missing ++
                        if cval.isKnownValid ||
                            (cscrut && match ctorsForTy (.enum (v0 :: vs') true) with
                              | .noConstructors => true | _ => false) ||
                            cexh
                        then [] else (splitCtorSet (ctorsForTy (.enum (v0 :: vs') true)) heads).missingEmpty) = true := by
                    apply (listAny_iff _ _).mpr
                    refine ⟨.nonExhaustive, List.mem_append_left _ ?_, rfl⟩
                    dsimp only [ctorsForTy, splitCtorSet]
                    exact List.mem_append_right _ List.mem_cons_self
                  rw [hne, hbad] at hnonExhAny; contradiction
                · exact False.elim (List.not_mem_nil hnil)
          have hSpec := (splitVariantsAux_spec
            ((v0 :: vs').map (fun pt => if tyIsEmpty pt then VariantVis.empty else VariantVis.visible))
            0 heads).2.1 m hmVar
          rcases hSpec with ⟨idx, hgetMap, hmEq, hSeenF⟩
          rw [Nat.zero_add] at hmEq
          subst hmEq
          rcases (listGet?_map_iff _ _ idx VariantVis.visible).mp hgetMap with ⟨pt, hgetPt, hVisEq⟩
          have hptNE : tyIsEmpty pt = false := by
            cases he : tyIsEmpty pt with
            | false => rfl
            | true => rw [he] at hVisEq; contradiction
          rcases inhabitValidPlace_nonEmpty hptNE with ⟨vpt, hvpt⟩
          refine ⟨.ctor idx vpt, ?_, ?_, ?_⟩
          · cases cval with
            | validOnly => exact ⟨pt, hgetPt, hvpt⟩
            | maybeInvalid => exact ⟨pt, hgetPt, validPlaceVal_valid_to_maybe hvpt⟩
          · dsimp only [wildFromCtor]
            rw [hgetPt]
            dsimp only [WitnessPat.matchesVal, WitnessPat.wildcardForTy]
            rw [hptNE, natBeq_refl]; rfl
          · intro p hpOF hpWF hpHead hpNW
            cases p with
            | wild => exact False.elim (hpNW rfl)
            | orPat _ _ => contradiction
            | variant pidx subPat =>
              dsimp only [Pat.matchesVal]
              cases hEq : natBeq pidx idx with
              | false => rfl
              | true =>
                have hEqNat : pidx = idx := natBeq_eq_of_true hEq
                subst hEqNat
                have hIn := (hasCtor_variant_iff pidx heads).mpr hpHead
                rw [hIn] at hSeenF; contradiction
            | unit | bool _ | intRange _ | pair _ _ | ref _ => contradiction
      | ref inner =>
        dsimp only [ctorsForTy, splitCtorSet] at hMiss
        cases hc : hasConcreteCtor heads with
        | true => rw [hc] at hMiss; exact False.elim (List.not_mem_nil hMiss)
        | false =>
          rw [hc] at hMiss; simp only [Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hMiss
          subst hMiss
          rcases inhabitValidPlace_maybeInvalid false inner with ⟨pt, hpt⟩
          refine ⟨.ref pt, ?_, ?_, ?_⟩
          · cases cval <;> exact hpt
          · dsimp only [wildFromCtor, WitnessPat.matchesVal]
            exact wildcardForTy_matches_valid
              { ty := inner, privUninhabited := false, validity := .maybeInvalid,
                isScrutinee := false, exhPatterns := cexh }
              pt (fun hbad => by cases hbad) hpt
          · intro p hpOF hpWF hpHead hpNW
            cases p with
            | wild => exact False.elim (hpNW rfl)
            | orPat _ _ => contradiction
            | ref _ =>
              have hcon : hasConcreteCtor heads = true := (hasConcreteCtor_iff heads).mpr
                ⟨.ref, hpHead, (fun hbad => by cases hbad)⟩
              rw [hcon] at hc; contradiction
            | unit | bool _ | intRange _ | pair _ _ | variant _ _ => contradiction
    · cases hcan : (cval.isKnownValid ||
          (cscrut && match ctorsForTy cty with | .noConstructors => true | _ => false) ||
          cexh) with
      | true => rw [hcan] at hMissEmptyOpt; exact False.elim (List.not_mem_nil hMissEmptyOpt)
      | false =>
        rw [hcan] at hMissEmptyOpt
        simp only [Bool.false_eq_true, ↓reduceIte] at hMissEmptyOpt
        rcases boolOr_eq_false.mp hcan with ⟨h12, _⟩
        rcases boolOr_eq_false.mp h12 with ⟨hValidF, _⟩
        have hColVal : cval = .maybeInvalid := by
          cases cval with
          | maybeInvalid => rfl
          | validOnly => contradiction
        subst hColVal
        cases cty with
        | unit =>
          dsimp only [ctorsForTy, splitCtorSet] at hMissEmptyOpt
          cases hc : hasConcreteCtor heads <;>
            (rw [hc] at hMissEmptyOpt; simp only [Bool.false_eq_true, ↓reduceIte] at hMissEmptyOpt;
             exact False.elim (List.not_mem_nil hMissEmptyOpt))
        | bool =>
          dsimp only [ctorsForTy, splitCtorSet] at hMissEmptyOpt
          exact False.elim (List.not_mem_nil hMissEmptyOpt)
        | u8 =>
          dsimp only [ctorsForTy, splitCtorSet] at hMissEmptyOpt
          exact False.elim (List.not_mem_nil hMissEmptyOpt)
        | ref _ =>
          dsimp only [ctorsForTy, splitCtorSet] at hMissEmptyOpt
          cases hc : hasConcreteCtor heads <;>
            (rw [hc] at hMissEmptyOpt; simp only [Bool.false_eq_true, ↓reduceIte] at hMissEmptyOpt;
             exact False.elim (List.not_mem_nil hMissEmptyOpt))
        | void =>
          dsimp only [ctorsForTy, splitCtorSet] at hMissEmptyOpt
          rcases List.mem_cons.mp hMissEmptyOpt with rfl | hnil
          · refine ⟨.invalid, rfl, rfl, ?_⟩
            intro p hpOF hpWF _ hpNW
            cases p with
            | wild => exact False.elim (hpNW rfl)
            | orPat _ _ => contradiction
            | unit | bool _ | intRange _ | pair _ _ | variant _ _ | ref _ => contradiction
          · exact False.elim (List.not_mem_nil hnil)
        | pair a b =>
          dsimp only [ctorsForTy, splitCtorSet] at hMissEmptyOpt
          cases hc : hasConcreteCtor heads with
          | true => rw [hc] at hMissEmptyOpt; exact False.elim (List.not_mem_nil hMissEmptyOpt)
          | false =>
            rw [hc] at hMissEmptyOpt; simp only [Bool.false_eq_true, ↓reduceIte] at hMissEmptyOpt
            cases he : (tyIsEmpty a || tyIsEmpty b) with
            | false => rw [he] at hMissEmptyOpt; exact False.elim (List.not_mem_nil hMissEmptyOpt)
            | true =>
              rw [he] at hMissEmptyOpt; simp only [ite_true, List.mem_singleton] at hMissEmptyOpt
              subst hMissEmptyOpt
              rcases inhabitValidPlace_maybeInvalid false a with ⟨v1, hv1⟩
              rcases inhabitValidPlace_maybeInvalid false b with ⟨v2, hv2⟩
              refine ⟨.pair v1 v2, ⟨hv1, hv2⟩, ?_, ?_⟩
              · dsimp only [wildFromCtor, WitnessPat.matchesVal]
                have hm1 := wildcardForTy_matches_valid
                  { ty := a, privUninhabited := false, validity := .maybeInvalid,
                    isScrutinee := false, exhPatterns := cexh }
                  v1 (fun hbad => by cases hbad) hv1
                have hm2 := wildcardForTy_matches_valid
                  { ty := b, privUninhabited := false, validity := .maybeInvalid,
                    isScrutinee := false, exhPatterns := cexh }
                  v2 (fun hbad => by cases hbad) hv2
                rw [hm1, hm2]; rfl
              · intro p hpOF hpWF hpHead hpNW
                cases p with
                | wild => exact False.elim (hpNW rfl)
                | orPat _ _ => contradiction
                | pair _ _ =>
                  have hcon : hasConcreteCtor heads = true := (hasConcreteCtor_iff heads).mpr
                    ⟨.pair, hpHead, (fun hbad => by cases hbad)⟩
                  rw [hcon] at hc; contradiction
                | unit | bool _ | intRange _ | variant _ _ | ref _ => contradiction
        | struct2 a b bVis =>
          dsimp only [ctorsForTy, splitCtorSet] at hMissEmptyOpt
          cases hc : hasConcreteCtor heads with
          | true => rw [hc] at hMissEmptyOpt; exact False.elim (List.not_mem_nil hMissEmptyOpt)
          | false =>
            rw [hc] at hMissEmptyOpt; simp only [Bool.false_eq_true, ↓reduceIte] at hMissEmptyOpt
            cases he : (tyIsEmpty a || (bVis && tyIsEmpty b)) with
            | false => rw [he] at hMissEmptyOpt; exact False.elim (List.not_mem_nil hMissEmptyOpt)
            | true =>
              rw [he] at hMissEmptyOpt; simp only [ite_true, List.mem_singleton] at hMissEmptyOpt
              subst hMissEmptyOpt
              rcases inhabitValidPlace_maybeInvalid false a with ⟨v1, hv1⟩
              cases bVis with
              | true =>
                rcases inhabitValidPlace_maybeInvalid false b with ⟨v2, hv2⟩
                refine ⟨.pair v1 v2, ⟨hv1, hv2⟩, ?_, ?_⟩
                · dsimp only [wildFromCtor, WitnessPat.matchesVal]
                  have hm1 := wildcardForTy_matches_valid
                    { ty := a, privUninhabited := false, validity := .maybeInvalid,
                      isScrutinee := false, exhPatterns := cexh }
                    v1 (fun hbad => by cases hbad) hv1
                  have hm2 := wildcardForTy_matches_valid
                    { ty := b, privUninhabited := false, validity := .maybeInvalid,
                      isScrutinee := false, exhPatterns := cexh }
                    v2 (fun hbad => by cases hbad) hv2
                  rw [hm1, hm2]; rfl
                · intro p hpOF hpWF hpHead hpNW
                  cases p with
                  | wild => exact False.elim (hpNW rfl)
                  | orPat _ _ => contradiction
                  | pair _ _ =>
                    have hcon : hasConcreteCtor heads = true := (hasConcreteCtor_iff heads).mpr
                      ⟨.pair, hpHead, (fun hbad => by cases hbad)⟩
                    rw [hcon] at hc; contradiction
                  | unit | bool _ | intRange _ | variant _ _ | ref _ => contradiction
              | false =>
                rcases inhabitValidPlace_maybeInvalid (tyIsEmpty b) b with ⟨v2, hv2⟩
                refine ⟨.pair v1 v2, ?_, ?_, ?_⟩
                · dsimp only [ValidPlaceVal]
                  cases heB : tyIsEmpty b with
                  | true => simp only [ite_true]; rw [heB] at hv2; exact ⟨hv1, hv2⟩
                  | false => simp only [Bool.false_eq_true, ↓reduceIte]; rw [heB] at hv2; exact ⟨hv1, hv2⟩
                · dsimp only [wildFromCtor, WitnessPat.matchesVal]
                  have hm1 := wildcardForTy_matches_valid
                    { ty := a, privUninhabited := false, validity := .maybeInvalid,
                      isScrutinee := false, exhPatterns := cexh }
                    v1 (fun hbad => by cases hbad) hv1
                  rw [hm1]; rfl
                · intro p hpOF hpWF hpHead hpNW
                  cases p with
                  | wild => exact False.elim (hpNW rfl)
                  | orPat _ _ => contradiction
                  | pair _ _ =>
                    have hcon : hasConcreteCtor heads = true := (hasConcreteCtor_iff heads).mpr
                      ⟨.pair, hpHead, (fun hbad => by cases hbad)⟩
                    rw [hcon] at hc; contradiction
                  | unit | bool _ | intRange _ | variant _ _ | ref _ => contradiction
        | enum vs nonExh =>
          cases vs with
          | nil =>
            cases nonExh with
            | true => dsimp only [ctorsForTy, splitCtorSet, splitVariantsAux] at hMissEmptyOpt; contradiction
            | false =>
              dsimp only [ctorsForTy, splitCtorSet] at hMissEmptyOpt
              rcases List.mem_cons.mp hMissEmptyOpt with rfl | hnil
              · refine ⟨.invalid, rfl, rfl, ?_⟩
                intro p hpOF hpWF _ hpNW
                cases p with
                | wild => exact False.elim (hpNW rfl)
                | orPat _ _ => contradiction
                | variant pidx _ => rcases hpWF with ⟨_, hget, _⟩; cases pidx <;> contradiction
                | unit | bool _ | intRange _ | pair _ _ | ref _ => contradiction
              · exact False.elim (List.not_mem_nil hnil)
          | cons v0 vs' =>
            dsimp only [ctorsForTy, splitCtorSet] at hMissEmptyOpt
            have hSpec := (splitVariantsAux_spec
              ((v0 :: vs').map (fun pt => if tyIsEmpty pt then VariantVis.empty else VariantVis.visible))
              0 heads).2.2.1 m hMissEmptyOpt
            rcases hSpec with ⟨idx, hgetMap, hmEq, hSeenF⟩
            rw [Nat.zero_add] at hmEq
            subst hmEq
            rcases (listGet?_map_iff _ _ idx VariantVis.empty).mp hgetMap with ⟨pt, hgetPt, hVisEq⟩
            rcases inhabitValidPlace_maybeInvalid false pt with ⟨vpt, hvpt⟩
            refine ⟨.ctor idx vpt, ⟨pt, hgetPt, hvpt⟩, ?_, ?_⟩
            · dsimp only [wildFromCtor]
              rw [hgetPt]
              dsimp only [WitnessPat.matchesVal]
              rw [natBeq_refl]
              exact wildcardForTy_matches_valid
                { ty := pt, privUninhabited := false, validity := .maybeInvalid,
                  isScrutinee := false, exhPatterns := cexh }
                vpt (fun hbad => by cases hbad) hvpt
            · intro p hpOF hpWF hpHead hpNW
              cases p with
              | wild => exact False.elim (hpNW rfl)
              | orPat _ _ => contradiction
              | variant pidx subPat =>
                dsimp only [Pat.matchesVal]
                cases hEq : natBeq pidx idx with
                | false => rfl
                | true =>
                  have hEqNat : pidx = idx := natBeq_eq_of_true hEq
                  subst hEqNat
                  have hIn := (hasCtor_variant_iff pidx heads).mpr hpHead
                  rw [hIn] at hSeenF; contradiction
              | unit | bool _ | intRange _ | pair _ _ | ref _ => contradiction

/-- Every valid value at a sound non-private column hits either a concrete present constructor in
`splitCtors` (with sharp boundary splitting) or the `.missing` fallback with non-empty `missingCtors`. -/
theorem validPlaceVal_to_splitColumnCtors
    {col : ColCtx} {heads : List Ctor} {v : Val}
    (hPrivF : col.privUninhabited = false)
    (hExhF : col.exhPatterns = false)
    (hTop : col.validity = .validOnly ∨ (col.isScrutinee && NoConstructorsTy col.ty) = false)
    (hv : ValidPlaceVal col.validity false col.ty v) :
    (∃ c ∈ (splitColumnCtors col heads).splitCtors, ∃ subVs,
      c ≠ .missing ∧ ValidCtorMatch col c v subVs ∧
      (∀ r0 pLo pHi, c = .intRange ⟨pLo, pHi⟩ → r0 ∈ collectIntRanges heads →
        (r0.lo ≤ pLo ∧ pHi ≤ r0.hi) ∨ (∀ n, pLo ≤ n → n ≤ pHi → r0.contains n = false)))
    ∨
    (.missing ∈ (splitColumnCtors col heads).splitCtors ∧
      (splitColumnCtors col heads).missingCtors ≠ [] ∧
      (∀ p, p.isOrFreeHead = true → PatWellFormed false col.ty p → p.headCtor ∈ heads → p ≠ .wild →
        p.matchesVal v = false)) := by
  have helperNonEmpty : ∀ {a b : List Ctor} {anyNE : Bool}, a ≠ [] →
      (if anyNE then [.nonExhaustive] else a ++ b) ≠ [] := by
    intro a b anyNE ha hbad
    cases anyNE with
    | true => simp at hbad
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hbad
      cases a <;> first | exact ha rfl | simp at hbad
  have helperNonEmptyR : ∀ {a b : List Ctor} {anyNE : Bool}, b ≠ [] →
      (if anyNE then [.nonExhaustive] else a ++ b) ≠ [] := by
    intro a b anyNE hb hbad
    cases anyNE with
    | true => simp at hbad
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hbad
      rcases List.append_eq_nil_iff.mp hbad with ⟨_, hbNil⟩
      exact hb hbNil
  rcases col with ⟨cty, cpriv, cval, cscrut, cexh⟩
  dsimp only at hPrivF hExhF hTop hv ⊢
  subst hPrivF hExhF
  dsimp only [splitColumnCtors]
  simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_false]
  cases cty with
  | void =>
    cases cval with
    | validOnly => cases v <;> contradiction
    | maybeInvalid =>
      have hScrutF : cscrut = false := by
        rcases hTop with hbad | hfalse
        · contradiction
        · cases cscrut <;> first | rfl | contradiction
      subst hScrutF
      cases v with
      | invalid =>
        right
        dsimp only [ctorsForTy, splitCtorSet, PlaceValidity.isKnownValid]
        refine ⟨List.mem_cons_self, ?_, ?_⟩
        · simp only [Bool.false_and, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
          intro hbad; cases hbad
        · intro p hpOF hpWF _ hpNW
          cases p with
          | wild => exact False.elim (hpNW rfl)
          | orPat _ _ => contradiction
          | unit | bool _ | intRange _ | pair _ _ | variant _ _ | ref _ => contradiction
      | unit | bool _ | u8 _ | pair _ _ | ctor _ _ | hiddenCtor _ | ref _ => contradiction
  | unit =>
    have hvEq : v = .unit := by
      cases cval <;> (cases v <;> first | contradiction | rfl)
    subst hvEq
    cases hc : hasConcreteCtor heads with
    | true =>
      left
      refine ⟨.unit, ?_, [], (fun hbad => by cases hbad), ⟨rfl, rfl, rfl, rfl⟩,
        (fun _ _ _ hbad _ => by cases hbad)⟩
      dsimp only [ctorsForTy, splitCtorSet]
      simp only [hc, ite_true]
      exact List.mem_append_left _ List.mem_cons_self
    | false =>
      right
      dsimp only [ctorsForTy, splitCtorSet]
      simp only [hc, Bool.false_eq_true, ↓reduceIte, List.isEmpty]
      refine ⟨List.mem_cons_self,
        (by first | exact helperNonEmpty (fun hbad => by cases hbad) | (intro hbad; cases hbad)), ?_⟩
      intro p hpOF hpWF hpHead hpNW
      cases p with
      | wild => exact False.elim (hpNW rfl)
      | orPat _ _ => contradiction
      | unit =>
        have hcon : hasConcreteCtor heads = true := (hasConcreteCtor_iff heads).mpr
          ⟨.unit, hpHead, (fun hbad => by cases hbad)⟩
        rw [hcon] at hc; contradiction
      | bool _ | intRange _ | pair _ _ | variant _ _ | ref _ => contradiction
  | bool =>
    have hb : ∃ bv, v = .bool bv := by
      cases cval <;> (cases v <;> first | contradiction | exact ⟨_, rfl⟩)
    rcases hb with ⟨bv, rfl⟩
    cases hs : hasCtor (.bool bv) heads with
    | true =>
      left
      refine ⟨.bool bv, ?_, [], (fun hbad => by cases hbad), ⟨rfl, rfl, rfl, rfl⟩,
        (fun _ _ _ hbad _ => by cases hbad)⟩
      dsimp only [ctorsForTy, splitCtorSet]
      apply List.mem_append_left
      cases bv with
      | true => apply List.mem_append_left; rw [hs]; exact List.mem_cons_self
      | false => apply List.mem_append_right; rw [hs]; exact List.mem_cons_self
    | false =>
      right
      have hmMiss : Ctor.bool bv ∈ (splitCtorSet (ctorsForTy Ty.bool) heads).missing := by
        dsimp only [ctorsForTy, splitCtorSet]
        cases bv with
        | true => apply List.mem_append_left; rw [hs]; exact List.mem_cons_self
        | false => apply List.mem_append_right; rw [hs]; exact List.mem_cons_self
      have hmNotNil : (splitCtorSet (ctorsForTy Ty.bool) heads).missing ≠ [] := by
        intro hNil; rw [hNil] at hmMiss; exact List.not_mem_nil hmMiss
      have hIsEmptyF : (splitCtorSet (ctorsForTy Ty.bool) heads).missing.isEmpty = false := by
        cases h : (splitCtorSet (ctorsForTy Ty.bool) heads).missing with
        | nil => exact False.elim (hmNotNil h)
        | cons _ _ => rfl
      rw [hIsEmptyF]
      refine ⟨List.mem_append_right _ List.mem_cons_self, helperNonEmpty hmNotNil, ?_⟩
      intro p hpOF hpWF hpHead hpNW
      cases p with
      | wild => exact False.elim (hpNW rfl)
      | orPat _ _ => contradiction
      | bool pb =>
        dsimp only [Pat.matchesVal]
        cases hEq : boolBeq pb bv with
        | false => rfl
        | true =>
          have hbe : pb = bv := (boolBeq_true_iff pb bv).mp hEq
          subst hbe
          have hbt := (hasCtor_bool_iff pb heads).mpr hpHead
          rw [hbt] at hs; contradiction
      | unit | intRange _ | pair _ _ | variant _ _ | ref _ => contradiction
  | u8 =>
    have hn : ∃ n, n ≤ 255 ∧ v = .u8 n := by
      cases cval <;> (cases v <;> first | contradiction | exact ⟨_, hv, rfl⟩)
    rcases hn with ⟨n, hn255, rfl⟩
    rcases splitIntRanges_sound_and_complete (Nat.zero_le 255) (collectIntRanges heads)
      with ⟨hBounds, hCov, _, hUnseen, hSharp⟩
    rcases hCov n (Nat.zero_le n) hn255 with ⟨part, hpMem, hplo, hphi⟩
    cases hps : part.seen with
    | true =>
      left
      refine ⟨.intRange ⟨part.lo, part.hi⟩, ?_, [], (fun hbad => by cases hbad), ?_, ?_⟩
      · dsimp only [ctorsForTy, splitCtorSet]
        apply List.mem_append_left
        apply (mem_filterMap_iff _ _ _).mpr
        refine ⟨part, hpMem, ?_⟩
        rw [hps]; rfl
      · refine ⟨rfl, rfl, n, hn255, rfl, ?_, rfl⟩
        exact (intRange_contains_iff ⟨part.lo, part.hi⟩ n).mpr ⟨hplo, hphi⟩
      · intro r0 pLo pHi hEqR hr0
        cases hEqR
        exact hSharp part hpMem r0 hr0
    | false =>
      right
      have hmMiss : Ctor.intRange ⟨part.lo, part.hi⟩ ∈ (splitCtorSet (ctorsForTy Ty.u8) heads).missing := by
        dsimp only [ctorsForTy, splitCtorSet]
        apply (mem_filterMap_iff _ _ _).mpr
        refine ⟨part, hpMem, ?_⟩
        rw [hps]; rfl
      have hmNotNil : (splitCtorSet (ctorsForTy Ty.u8) heads).missing ≠ [] := by
        intro hNil; rw [hNil] at hmMiss; exact List.not_mem_nil hmMiss
      have hIsEmptyF : (splitCtorSet (ctorsForTy Ty.u8) heads).missing.isEmpty = false := by
        cases h : (splitCtorSet (ctorsForTy Ty.u8) heads).missing with
        | nil => exact False.elim (hmNotNil h)
        | cons _ _ => rfl
      rw [hIsEmptyF]
      refine ⟨List.mem_append_right _ List.mem_cons_self, helperNonEmpty hmNotNil, ?_⟩
      intro p hpOF hpWF hpHead hpNW
      cases p with
      | wild => exact False.elim (hpNW rfl)
      | orPat _ _ => contradiction
      | intRange pr =>
        have hpr : pr ∈ collectIntRanges heads := (mem_collectIntRanges_iff pr heads).mpr hpHead
        exact hUnseen part hpMem hps pr hpr n hplo hphi
      | unit | bool _ | pair _ _ | variant _ _ | ref _ => contradiction
  | pair a b =>
    have hp : ∃ v1 v2, v = .pair v1 v2 := by
      cases cval <;> (cases v <;> first | contradiction | exact ⟨_, _, rfl⟩)
    rcases hp with ⟨v1, v2, rfl⟩
    cases hc : hasConcreteCtor heads with
    | true =>
      left
      refine ⟨.pair, ?_, [v1, v2], (fun hbad => by cases hbad),
        ⟨rfl, v1, v2, rfl, rfl, a, b, Or.inl rfl⟩, (fun _ _ _ hbad _ => by cases hbad)⟩
      dsimp only [ctorsForTy, splitCtorSet]
      simp only [hc, ite_true]
      exact List.mem_append_left _ List.mem_cons_self
    | false =>
      right
      cases he : (tyIsEmpty a || tyIsEmpty b) with
      | false =>
        dsimp only [ctorsForTy, splitCtorSet]
        simp only [hc, he, Bool.false_eq_true, ↓reduceIte, List.isEmpty]
        refine ⟨List.mem_cons_self,
          (by first | exact helperNonEmpty (fun hbad => by cases hbad) | (intro hbad; cases hbad)), ?_⟩
        intro p hpOF hpWF hpHead hpNW
        cases p with
        | wild => exact False.elim (hpNW rfl)
        | orPat _ _ => contradiction
        | pair _ _ =>
          have hcon : hasConcreteCtor heads = true := (hasConcreteCtor_iff heads).mpr
            ⟨.pair, hpHead, (fun hbad => by cases hbad)⟩
          rw [hcon] at hc; contradiction
        | unit | bool _ | intRange _ | variant _ _ | ref _ => contradiction
      | true =>
        have hValMaybe : cval = .maybeInvalid := by
          cases cval with
          | maybeInvalid => rfl
          | validOnly =>
            have hePair : tyIsEmpty (.pair a b) = true := he
            exact False.elim (tyIsEmpty_validPlaceVal_validOnly_false hePair hv)
        subst hValMaybe
        dsimp only [ctorsForTy, splitCtorSet, PlaceValidity.isKnownValid]
        simp only [hc, he, Bool.and_false, Bool.false_or,
          Bool.false_eq_true, ↓reduceIte, List.isEmpty]
        refine ⟨List.mem_cons_self,
          (by first | exact helperNonEmptyR (fun hbad => by cases hbad) | (intro hbad; cases hbad)), ?_⟩
        intro p hpOF hpWF hpHead hpNW
        cases p with
        | wild => exact False.elim (hpNW rfl)
        | orPat _ _ => contradiction
        | pair _ _ =>
          have hcon : hasConcreteCtor heads = true := (hasConcreteCtor_iff heads).mpr
            ⟨.pair, hpHead, (fun hbad => by cases hbad)⟩
          rw [hcon] at hc; contradiction
        | unit | bool _ | intRange _ | variant _ _ | ref _ => contradiction
  | struct2 a b bVis =>
    have hp : ∃ v1 v2, v = .pair v1 v2 := by
      cases cval <;> (cases v <;> first | contradiction | exact ⟨_, _, rfl⟩)
    rcases hp with ⟨v1, v2, rfl⟩
    cases hc : hasConcreteCtor heads with
    | true =>
      left
      refine ⟨.pair, ?_, [v1, v2], (fun hbad => by cases hbad),
        ⟨rfl, v1, v2, rfl, rfl, a, b, Or.inr ⟨bVis, rfl⟩⟩, (fun _ _ _ hbad _ => by cases hbad)⟩
      dsimp only [ctorsForTy, splitCtorSet]
      simp only [hc, ite_true]
      exact List.mem_append_left _ List.mem_cons_self
    | false =>
      right
      cases he : (tyIsEmpty a || (bVis && tyIsEmpty b)) with
      | false =>
        dsimp only [ctorsForTy, splitCtorSet]
        simp only [hc, he, Bool.false_eq_true, ↓reduceIte, List.isEmpty]
        refine ⟨List.mem_cons_self,
          (by first | exact helperNonEmpty (fun hbad => by cases hbad) | (intro hbad; cases hbad)), ?_⟩
        intro p hpOF hpWF hpHead hpNW
        cases p with
        | wild => exact False.elim (hpNW rfl)
        | orPat _ _ => contradiction
        | pair _ _ =>
          have hcon : hasConcreteCtor heads = true := (hasConcreteCtor_iff heads).mpr
            ⟨.pair, hpHead, (fun hbad => by cases hbad)⟩
          rw [hcon] at hc; contradiction
        | unit | bool _ | intRange _ | variant _ _ | ref _ => contradiction
      | true =>
        have hValMaybe : cval = .maybeInvalid := by
          cases cval with
          | maybeInvalid => rfl
          | validOnly =>
            have heStruct : tyIsEmpty (.struct2 a b bVis) = true := he
            exact False.elim (tyIsEmpty_validPlaceVal_validOnly_false heStruct hv)
        subst hValMaybe
        dsimp only [ctorsForTy, splitCtorSet, PlaceValidity.isKnownValid]
        simp only [hc, he, Bool.and_false, Bool.false_or,
          Bool.false_eq_true, ↓reduceIte, List.isEmpty]
        refine ⟨List.mem_cons_self,
          (by first | exact helperNonEmptyR (fun hbad => by cases hbad) | (intro hbad; cases hbad)), ?_⟩
        intro p hpOF hpWF hpHead hpNW
        cases p with
        | wild => exact False.elim (hpNW rfl)
        | orPat _ _ => contradiction
        | pair _ _ =>
          have hcon : hasConcreteCtor heads = true := (hasConcreteCtor_iff heads).mpr
            ⟨.pair, hpHead, (fun hbad => by cases hbad)⟩
          rw [hcon] at hc; contradiction
        | unit | bool _ | intRange _ | variant _ _ | ref _ => contradiction
  | ref inner =>
    have hpt : ∃ pt, v = .ref pt := by
      cases cval <;> (cases v <;> first | contradiction | exact ⟨_, rfl⟩)
    rcases hpt with ⟨pt, rfl⟩
    cases hc : hasConcreteCtor heads with
    | true =>
      left
      refine ⟨.ref, ?_, [pt], (fun hbad => by cases hbad),
        ⟨rfl, inner, pt, rfl, rfl, rfl⟩, (fun _ _ _ hbad _ => by cases hbad)⟩
      dsimp only [ctorsForTy, splitCtorSet]
      simp only [hc, ite_true]
      exact List.mem_append_left _ List.mem_cons_self
    | false =>
      right
      dsimp only [ctorsForTy, splitCtorSet]
      simp only [hc, Bool.false_eq_true, ↓reduceIte, List.isEmpty]
      refine ⟨List.mem_cons_self,
        (by first | exact helperNonEmpty (fun hbad => by cases hbad) | (intro hbad; cases hbad)), ?_⟩
      intro p hpOF hpWF hpHead hpNW
      cases p with
      | wild => exact False.elim (hpNW rfl)
      | orPat _ _ => contradiction
      | ref _ =>
        have hcon : hasConcreteCtor heads = true := (hasConcreteCtor_iff heads).mpr
          ⟨.ref, hpHead, (fun hbad => by cases hbad)⟩
        rw [hcon] at hc; contradiction
      | unit | bool _ | intRange _ | pair _ _ | variant _ _ => contradiction
  | enum vs nonExh =>
    cases hvCase : v with
    | invalid =>
      have hNil : vs = [] ∧ nonExh = false := by
        cases cval with
        | validOnly => rw [hvCase] at hv; contradiction
        | maybeInvalid =>
          rw [hvCase] at hv
          cases vs <;> cases nonExh <;> first | contradiction | exact ⟨rfl, rfl⟩
      rcases hNil with ⟨rfl, rfl⟩
      have hScrutF : cscrut = false := by
        rcases hTop with hvalV | hScrut
        · rw [hvCase, hvalV] at hv; contradiction
        · cases cscrut <;> first | rfl | contradiction
      subst hScrutF
      have hValMaybe : cval = .maybeInvalid := by
        cases cval with
        | maybeInvalid => rfl
        | validOnly => rw [hvCase] at hv; contradiction
      subst hValMaybe
      right
      dsimp only [ctorsForTy, splitCtorSet, PlaceValidity.isKnownValid]
      refine ⟨List.mem_cons_self, ?_, ?_⟩
      · simp only [Bool.false_and, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
        intro hbad; cases hbad
      · intro p hpOF hpWF _ hpNW
        cases p with
        | wild => exact False.elim (hpNW rfl)
        | orPat _ _ => contradiction
        | variant idx _ => rcases hpWF with ⟨_, hget, _⟩; cases idx <;> contradiction
        | unit | bool _ | intRange _ | pair _ _ | ref _ => contradiction
    | hiddenCtor tag =>
      have hNE : nonExh = true := by
        cases cval <;> (rw [hvCase] at hv; cases nonExh <;> first | contradiction | rfl)
      subst hNE
      right
      have hMissIn : Ctor.nonExhaustive ∈ (splitCtorSet (ctorsForTy (.enum vs true)) heads).missing := by
        cases vs <;> dsimp only [ctorsForTy, splitCtorSet]
        · exact List.mem_cons_self
        · exact List.mem_append_right _ List.mem_cons_self
      have hmNotNil : (splitCtorSet (ctorsForTy (.enum vs true)) heads).missing ≠ [] := by
        intro hNil; rw [hNil] at hMissIn; exact List.not_mem_nil hMissIn
      have hIsEmptyF : (splitCtorSet (ctorsForTy (.enum vs true)) heads).missing.isEmpty = false := by
        cases h : (splitCtorSet (ctorsForTy (.enum vs true)) heads).missing with
        | nil => exact False.elim (hmNotNil h)
        | cons _ _ => rfl
      rw [hIsEmptyF]
      refine ⟨List.mem_append_right _ List.mem_cons_self, helperNonEmpty hmNotNil, ?_⟩
      intro p hpOF hpWF _ hpNW
      cases p with
      | wild => exact False.elim (hpNW rfl)
      | orPat _ _ => contradiction
      | variant _ _ => rfl
      | unit | bool _ | intRange _ | pair _ _ | ref _ => contradiction
    | ctor idx sub =>
      have hSub : ∃ pt, listGet? vs idx = some pt ∧ ValidPlaceVal cval false pt sub := by
        cases cval <;> (rw [hvCase] at hv; exact hv)
      rcases hSub with ⟨pt, hgetPt, hvSub⟩
      have hCons : vs ≠ [] := by
        cases vs with
        | nil => cases idx <;> contradiction
        | cons _ _ => intro hbad; cases hbad
      cases hHas : hasCtor (.variant idx) heads with
      | true =>
        left
        refine ⟨.variant idx, ?_, [sub], (fun hbad => by cases hbad),
          ⟨rfl, vs, nonExh, pt, sub, rfl, hgetPt, rfl, rfl⟩,
          (fun _ _ _ hbad _ => by cases hbad)⟩
        cases hvs : vs with
        | nil => exact False.elim (hCons hvs)
        | cons v0 vs' =>
          rw [hvs] at hgetPt
          dsimp only [ctorsForTy, splitCtorSet]
          apply List.mem_append_left
          have hget' : listGet? ((v0 :: vs').map (fun x => if tyIsEmpty x then VariantVis.empty else VariantVis.visible)) idx =
              some (if tyIsEmpty pt then VariantVis.empty else VariantVis.visible) :=
            (listGet?_map_iff _ _ idx _).mpr ⟨pt, hgetPt, rfl⟩
          have hSpec := (splitVariantsAux_spec
            ((v0 :: vs').map (fun x => if tyIsEmpty x then VariantVis.empty else VariantVis.visible))
            0 heads).2.2.2 idx _ hget'
          rw [Nat.zero_add, hHas] at hSpec
          exact hSpec
      | false =>
        right
        cases hvs : vs with
        | nil => exact False.elim (hCons hvs)
        | cons v0 vs' =>
          rw [hvs] at hgetPt
          have hget' : listGet? ((v0 :: vs').map (fun x => if tyIsEmpty x then VariantVis.empty else VariantVis.visible)) idx =
              some (if tyIsEmpty pt then VariantVis.empty else VariantVis.visible) :=
            (listGet?_map_iff _ _ idx _).mpr ⟨pt, hgetPt, rfl⟩
          have hSpec := (splitVariantsAux_spec
            ((v0 :: vs').map (fun x => if tyIsEmpty x then VariantVis.empty else VariantVis.visible))
            0 heads).2.2.2 idx _ hget'
          rw [Nat.zero_add, hHas] at hSpec
          cases hePt : tyIsEmpty pt with
          | false =>
            rw [hePt] at hSpec
            dsimp only at hSpec
            have hmIn : Ctor.variant idx ∈ (splitCtorSet (ctorsForTy (.enum (v0 :: vs') nonExh)) heads).missing := by
              dsimp only [ctorsForTy, splitCtorSet]
              cases nonExh with
              | false => exact hSpec
              | true => exact List.mem_append_left _ hSpec
            have hmNotNil : (splitCtorSet (ctorsForTy (.enum (v0 :: vs') nonExh)) heads).missing ≠ [] := by
              intro hNil; rw [hNil] at hmIn; exact List.not_mem_nil hmIn
            have hIsEmptyF : (splitCtorSet (ctorsForTy (.enum (v0 :: vs') nonExh)) heads).missing.isEmpty = false := by
              cases h : (splitCtorSet (ctorsForTy (.enum (v0 :: vs') nonExh)) heads).missing with
              | nil => exact False.elim (hmNotNil h)
              | cons _ _ => rfl
            rw [hIsEmptyF]
            refine ⟨List.mem_append_right _ List.mem_cons_self, helperNonEmpty hmNotNil, ?_⟩
            intro p hpOF hpWF hpHead hpNW
            cases p with
            | wild => exact False.elim (hpNW rfl)
            | orPat _ _ => contradiction
            | variant pidx subPat =>
              dsimp only [Pat.matchesVal]
              cases hEq : natBeq pidx idx with
              | false => rfl
              | true =>
                have hEqNat : pidx = idx := natBeq_eq_of_true hEq
                subst hEqNat
                have hIn := (hasCtor_variant_iff pidx heads).mpr hpHead
                rw [hIn] at hHas; contradiction
            | unit | bool _ | intRange _ | pair _ _ | ref _ => contradiction
          | true =>
            have hValMaybe : cval = .maybeInvalid := by
              cases cval with
              | maybeInvalid => rfl
              | validOnly => exact False.elim (tyIsEmpty_validPlaceVal_validOnly_false hePt hvSub)
            subst hValMaybe
            rw [hePt] at hSpec
            dsimp only at hSpec
            have hmeIn : Ctor.variant idx ∈ (splitCtorSet (ctorsForTy (.enum (v0 :: vs') nonExh)) heads).missingEmpty :=
              hSpec
            have hmeNotNil : (splitCtorSet (ctorsForTy (.enum (v0 :: vs') nonExh)) heads).missingEmpty ≠ [] := by
              intro hNil; rw [hNil] at hmeIn; exact List.not_mem_nil hmeIn
            have hmeIsEmptyF : (splitCtorSet (ctorsForTy (.enum (v0 :: vs') nonExh)) heads).missingEmpty.isEmpty = false := by
              cases h : (splitCtorSet (ctorsForTy (.enum (v0 :: vs') nonExh)) heads).missingEmpty with
              | nil => exact False.elim (hmeNotNil h)
              | cons _ _ => rfl
            dsimp only [ctorsForTy, PlaceValidity.isKnownValid] at hmeIsEmptyF ⊢
            refine ⟨?_, ?_, ?_⟩
            · apply List.mem_append_right
              simp only [hmeIsEmptyF, Bool.false_or, Bool.and_false]
              exact List.mem_cons_self
            · simp only [Bool.and_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
              exact helperNonEmptyR hmeNotNil
            intro p hpOF hpWF hpHead hpNW
            cases p with
            | wild => exact False.elim (hpNW rfl)
            | orPat _ _ => contradiction
            | variant pidx subPat =>
              dsimp only [Pat.matchesVal]
              cases hEq : natBeq pidx idx with
              | false => rfl
              | true =>
                have hEqNat : pidx = idx := natBeq_eq_of_true hEq
                subst hEqNat
                have hIn := (hasCtor_variant_iff pidx heads).mpr hpHead
                rw [hIn] at hHas; contradiction
            | unit | bool _ | intRange _ | pair _ _ | ref _ => contradiction
    | unit | bool _ | u8 _ | pair _ _ | ref _ =>
      cases cval <;> (rw [hvCase] at hv; contradiction)

/-- Structural characterizations of `applyCtorToWitnesses` and `marangetBranches`. -/
theorem applyCtorToWitnesses_eq_nil_iff (col : ColCtx) (missingCtors : List Ctor) (ctor : Ctor)
    (subWits : List (List WitnessPat)) :
    applyCtorToWitnesses col missingCtors ctor subWits = [] ↔
      subWits = [] ∨ (ctor = .missing ∧ missingCtors = []) := by
  cases subWits with
  | nil =>
    dsimp only [applyCtorToWitnesses]
    exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
  | cons w ws =>
    cases ctor with
    | missing =>
      dsimp only [applyCtorToWitnesses]
      cases missingCtors with
      | nil => exact ⟨fun _ => Or.inr ⟨rfl, rfl⟩, fun _ => rfl⟩
      | cons m ms =>
        dsimp only [List.flatMap, List.map]
        constructor
        · intro h; contradiction
        · intro h
          rcases h with h1 | ⟨_, h2⟩
          · contradiction
          · contradiction
    | unit | bool _ | intRange _ | pair | variant _ | nonExhaustive | ref
    | orCtor | wild | privateUninhabited | never =>
      dsimp only [applyCtorToWitnesses, List.map]
      constructor
      · intro h; contradiction
      · intro h
        rcases h with h1 | ⟨hbad, _⟩
        · contradiction
        · cases hbad

theorem mem_applyCtorToWitnesses_iff (col : ColCtx) (missingCtors : List Ctor) (ctor : Ctor)
    (subWits : List (List WitnessPat)) (ws : List WitnessPat) :
    ws ∈ applyCtorToWitnesses col missingCtors ctor subWits ↔
      match ctor with
      | .missing => ∃ m subWs, m ∈ missingCtors ∧ subWs ∈ subWits ∧ ws = wildFromCtor col.ty m :: subWs
      | _ => ∃ subWs, subWs ∈ subWits ∧ ws = unspecializeStack col ctor subWs := by
  cases subWits with
  | nil =>
    dsimp only [applyCtorToWitnesses]
    cases ctor with
    | missing =>
      constructor <;> intro h
      · exact False.elim (List.not_mem_nil h)
      · rcases h with ⟨_, _, _, hbad, _⟩; exact False.elim (List.not_mem_nil hbad)
    | _ =>
      constructor <;> intro h
      · exact False.elim (List.not_mem_nil h)
      · rcases h with ⟨_, hbad, _⟩; exact False.elim (List.not_mem_nil hbad)
  | cons w0 ws0 =>
    cases ctor with
    | missing =>
      dsimp only [applyCtorToWitnesses]
      rw [List.mem_flatMap]
      constructor
      · intro ⟨m, hm, hmap⟩
        rcases List.mem_map.mp hmap with ⟨subWs, hsw, rfl⟩
        exact ⟨m, subWs, hm, hsw, rfl⟩
      · intro ⟨m, subWs, hm, hsw, hEq⟩
        subst hEq
        exact ⟨m, hm, List.mem_map.mpr ⟨subWs, hsw, rfl⟩⟩
    | unit | bool _ | intRange _ | pair | variant _ | nonExhaustive | ref
    | orCtor | wild | privateUninhabited | never =>
      dsimp only [applyCtorToWitnesses]
      rw [List.mem_map]
      constructor
      · intro ⟨subWs, hsw, hEq⟩; exact ⟨subWs, hsw, hEq.symm⟩
      · intro ⟨subWs, hsw, hEq⟩; exact ⟨subWs, hsw, hEq.symm⟩

theorem marangetBranches_nil_iff
    (step : List ColCtx → List MatrixRow → (List (List WitnessPat) × List Nat))
    (col : ColCtx) (cs : List ColCtx) (missingCtors : List Ctor)
    (rows' : List MatrixRow) (ctors : List Ctor) :
    (marangetBranches step col cs missingCtors rows' ctors).1 = [] ↔
      ∀ ctor, ctor ∈ ctors →
        applyCtorToWitnesses col missingCtors ctor
          (step (specializeCol col ctor ++ cs)
            (specializeRows ctor (specializeCol col ctor).length rows')).1 = [] := by
  induction ctors with
  | nil =>
    dsimp only [marangetBranches]
    exact ⟨fun _ _ h => False.elim (List.not_mem_nil h), fun _ => rfl⟩
  | cons ctor rest ih =>
    dsimp only [marangetBranches]
    rw [List.append_eq_nil_iff, ih]
    constructor
    · intro ⟨hHead, hRest⟩ c hc
      rcases List.mem_cons.mp hc with rfl | hTail
      · exact hHead
      · exact hRest c hTail
    · intro hAll
      exact ⟨hAll ctor List.mem_cons_self, fun c hc => hAll c (List.mem_cons_of_mem ctor hc)⟩

theorem mem_marangetBranches_fst_iff
    (step : List ColCtx → List MatrixRow → (List (List WitnessPat) × List Nat))
    (col : ColCtx) (cs : List ColCtx) (missingCtors : List Ctor)
    (rows' : List MatrixRow) (ctors : List Ctor) (ws : List WitnessPat) :
    ws ∈ (marangetBranches step col cs missingCtors rows' ctors).1 ↔
      ∃ ctor, ctor ∈ ctors ∧
        ws ∈ applyCtorToWitnesses col missingCtors ctor
          (step (specializeCol col ctor ++ cs)
            (specializeRows ctor (specializeCol col ctor).length rows')).1 := by
  induction ctors with
  | nil =>
    dsimp only [marangetBranches]
    constructor <;> intro h
    · exact False.elim (List.not_mem_nil h)
    · rcases h with ⟨_, hc, _⟩; exact False.elim (List.not_mem_nil hc)
  | cons ctor rest ih =>
    dsimp only [marangetBranches]
    rw [List.mem_append, ih]
    constructor
    · intro h
      rcases h with hHead | ⟨c, hc, hWs⟩
      · exact ⟨ctor, List.mem_cons_self, hHead⟩
      · exact ⟨c, List.mem_cons_of_mem ctor hc, hWs⟩
    · intro ⟨c, hc, hWs⟩
      rcases List.mem_cons.mp hc with rfl | hTail
      · exact Or.inl hWs
      · exact Or.inr ⟨c, hTail, hWs⟩

/-- **Master Soundness & Completeness Theorem (`marangetCheckAux`):**
For any fuel `fuel ≥ colsWeight cols + 1`, well-formed column contexts `cols`, sound ambient flags
`ColsSoundCtx cols`, and well-formed pattern matrix `rows`:
`marangetCheckAux` returns zero missing witnesses **if and only if** every well-typed value vector
`vs` is matched by some unguarded row of `rows`. -/
theorem marangetCheckAux_iff :
    ∀ (fuel : Nat) (cols : List ColCtx) (rows : List MatrixRow),
      colsWeight cols + 1 ≤ fuel →
      ColsWellFormed cols →
      ColsSoundCtx cols →
      MatrixWellFormed cols rows →
      ((marangetCheckAux fuel cols rows).1 = [] ↔
        ∀ vs, ColsValidPlaceVal cols vs → rowsUnguardedMatch rows vs = true) := by
  intro fuel
  induction fuel with
  | zero =>
    intro cols _ hfuel _ _ _
    exact False.elim (Nat.not_succ_le_zero (colsWeight cols) hfuel)
  | succ fuel' ih =>
    intro cols rows hfuel hWFCols hSoundCols hWFRows
    cases cols with
    | nil =>
      dsimp only [marangetCheckAux]
      constructor
      · intro hNil vs hvs
        cases vs with
        | cons _ _ => contradiction
        | nil =>
          have hBaseF : (evalBaseRows true rows).1 = false := by
            cases hb : (evalBaseRows true rows).1 with
            | false => rfl
            | true => rw [hb] at hNil; simp at hNil
          exact (evalBaseRows_true_iff rows hWFRows).mp hBaseF
      · intro hAll
        have hMatch : rowsUnguardedMatch rows [] = true := hAll [] trivial
        have hBaseF := (evalBaseRows_true_iff rows hWFRows).mpr hMatch
        rw [hBaseF]; rfl
    | cons col cs =>
      dsimp only [marangetCheckAux]
      rw [marangetBranches_nil_iff]
      have hWF' := expandHeadOrRows_wellFormed (col :: cs) rows hWFRows
      have hOF' := expandHeadOrRows_headOrFree rows
      have hColWF : col.privUninhabited = true → tyIsEmpty col.ty = true ∧ col.validity = .maybeInvalid :=
        hWFCols.1
      have hColExh : col.exhPatterns = false := hSoundCols.1
      have hColTop : col.validity = .validOnly ∨ (col.isScrutinee && NoConstructorsTy col.ty) = false :=
        hSoundCols.2.1
      have hBranchIH : ∀ ctor,
          ((marangetCheckAux fuel' (specializeCol col ctor ++ cs)
              (specializeRows ctor (specializeCol col ctor).length (expandHeadOrRows rows))).1 = [] ↔
            ∀ subVsAll, ColsValidPlaceVal (specializeCol col ctor ++ cs) subVsAll →
              rowsUnguardedMatch
                (specializeRows ctor (specializeCol col ctor).length (expandHeadOrRows rows)) subVsAll = true) := by
        intro ctor
        have hFuelSub : colsWeight (specializeCol col ctor ++ cs) + 1 ≤ fuel' := by
          have hlt := colsWeight_specialize_lt col ctor cs
          change colsWeight (specializeCol col ctor ++ cs) + 1 ≤ colsWeight (col :: cs) at hlt
          exact Nat.le_trans hlt (Nat.le_of_succ_le_succ hfuel)
        exact ih (specializeCol col ctor ++ cs)
          (specializeRows ctor (specializeCol col ctor).length (expandHeadOrRows rows))
          hFuelSub (colsWellFormed_specializeCol col ctor cs hWFCols)
          (colsSoundCtx_specializeCol col ctor cs hSoundCols)
          (specializeRows_wellFormed col cs ctor (expandHeadOrRows rows) hWF' hOF')
      have hSharpRel : ∀ (ctor : Ctor) r0 pLo pHi, ctor = Ctor.intRange ⟨pLo, pHi⟩ →
          (∀ pLo1 pHi1, ctor = Ctor.intRange ⟨pLo1, pHi1⟩ → r0 ∈ collectIntRanges (matrixHeadCtors (expandHeadOrRows rows)) →
            (r0.lo ≤ pLo1 ∧ pHi1 ≤ r0.hi) ∨ (∀ n, pLo1 ≤ n → n ≤ pHi1 → r0.contains n = false)) →
          (∀ row, row ∈ expandHeadOrRows rows → row.headCtor = .intRange r0 →
            (r0.lo ≤ pLo ∧ pHi ≤ r0.hi) ∨ (∀ n, pLo ≤ n → n ≤ pHi → r0.contains n = false)) := by
        intro ctor r0 pLo pHi hEqC hSh row hrow hhc
        have hr0In : r0 ∈ collectIntRanges (matrixHeadCtors (expandHeadOrRows rows)) := by
          apply (mem_collectIntRanges_iff r0 _).mpr
          rw [← hhc]
          exact headCtor_mem_heads_of_mem hrow
        exact hSh pLo pHi hEqC hr0In
      constructor
      · intro hBranches vs hvs
        cases vs with
        | nil => contradiction
        | cons v vsTail =>
          rw [← rowsUnguardedMatch_expandHeadOrRows rows (v :: vsTail)]
          cases hpriv : col.privUninhabited with
          | true =>
            have hPrivMem : Ctor.privateUninhabited ∈
                (splitColumnCtors col (matrixHeadCtors (expandHeadOrRows rows))).splitCtors := by
              dsimp only [splitColumnCtors]; rw [hpriv]; exact List.mem_cons_self
            have hApp := hBranches .privateUninhabited hPrivMem
            have hSubNil : (marangetCheckAux fuel' (specializeCol col .privateUninhabited ++ cs)
                (specializeRows .privateUninhabited (specializeCol col .privateUninhabited).length
                  (expandHeadOrRows rows))).1 = [] := by
              rcases (applyCtorToWitnesses_eq_nil_iff _ _ _ _).mp hApp with hNil | ⟨hbad, _⟩
              · exact hNil
              · cases hbad
            have hAllSub := (hBranchIH .privateUninhabited).mp hSubNil vsTail hvs.2
            have hmValid : ValidCtorMatch col .privateUninhabited v [] := ⟨hpriv, rfl⟩
            have hEqRow :
                rowsUnguardedMatch
                  (specializeRows .privateUninhabited (specializeCol col .privateUninhabited).length
                    (expandHeadOrRows rows))
                  ([] ++ vsTail) =
                rowsUnguardedMatch (expandHeadOrRows rows) (v :: vsTail) :=
              rowsUnguardedMatch_specializeRows_ctor hmValid rfl (expandHeadOrRows rows)
                hWF' hOF' (fun _ _ _ hbad _ => by cases hbad)
            exact hEqRow ▸ hAllSub
          | false =>
            have hv' : ValidPlaceVal col.validity false col.ty v := by rw [← hpriv]; exact hvs.1
            rcases validPlaceVal_to_splitColumnCtors hpriv hColExh hColTop hv' with
              ⟨c, hcMem, subVs, hcNotMiss, hCtorMatch, hSharp⟩ |
              ⟨hmMissMem, hmNotNil, hDisjV⟩
            · have hApp := hBranches c hcMem
              have hSubNil : (marangetCheckAux fuel' (specializeCol col c ++ cs)
                  (specializeRows c (specializeCol col c).length (expandHeadOrRows rows))).1 = [] := by
                rcases (applyCtorToWitnesses_eq_nil_iff _ _ _ _).mp hApp with hNil | ⟨hEqM, _⟩
                · exact hNil
                · exact False.elim (hcNotMiss hEqM)
              rcases validCtorMatch_subCols hvs.1 hCtorMatch with ⟨hSubColsVal, hSubLen⟩
              have hAllSub := (hBranchIH c).mp hSubNil (subVs ++ vsTail)
                (colsValidPlaceVal_append (specializeCol col c) cs subVs vsTail hSubColsVal hvs.2)
              have hEqRow :
                  rowsUnguardedMatch
                    (specializeRows c (specializeCol col c).length (expandHeadOrRows rows))
                    (subVs ++ vsTail) =
                  rowsUnguardedMatch (expandHeadOrRows rows) (v :: vsTail) :=
                rowsUnguardedMatch_specializeRows_ctor hCtorMatch hSubLen
                  (expandHeadOrRows rows) hWF' hOF' (fun r0 pLo pHi hEq => hSharpRel c r0 pLo pHi hEq (hSharp r0))
              exact hEqRow ▸ hAllSub
            · have hApp := hBranches .missing hmMissMem
              have hSubNil : (marangetCheckAux fuel' (specializeCol col .missing ++ cs)
                  (specializeRows .missing (specializeCol col .missing).length (expandHeadOrRows rows))).1 = [] := by
                rcases (applyCtorToWitnesses_eq_nil_iff _ _ _ _).mp hApp with hNil | ⟨_, hMissNil⟩
                · exact hNil
                · exact False.elim (hmNotNil hMissNil)
              have hAllSub := (hBranchIH .missing).mp hSubNil vsTail hvs.2
              have hDisjRows : ∀ row p ps, row ∈ expandHeadOrRows rows → row.pats = p :: ps →
                  p ≠ .wild → p.matchesVal v = false := by
                intro row p ps hrow hEqPats hpNW
                have hrWF := hWF' row hrow
                have hrOF := hOF' row hrow
                rw [hEqPats] at hrWF
                have hpOF := hrOF p ps hEqPats
                have hpHead : p.headCtor ∈ matrixHeadCtors (expandHeadOrRows rows) := by
                  have := headCtor_mem_heads_of_mem hrow
                  dsimp only [MatrixRow.headCtor] at this
                  rw [hEqPats] at this
                  exact this
                have hpWF' : PatWellFormed false col.ty p := by rw [← hpriv]; exact hrWF.1
                exact hDisjV p hpOF hpWF' hpHead hpNW
              have hEqRow :
            rowsUnguardedMatch (specializeRows .missing 0 (expandHeadOrRows rows)) vsTail =
              rowsUnguardedMatch (expandHeadOrRows rows) (v :: vsTail) :=
          rowsUnguardedMatch_specializeRows_missing (expandHeadOrRows rows) hWF' hOF' hDisjRows
              exact hEqRow ▸ hAllSub
      · intro hAllValid ctor hCtorMem
        cases hEqMiss : (match ctor with | .missing => true | _ => false) with
        | true =>
          have hIsMiss : ctor = .missing := by cases ctor <;> first | contradiction | rfl
          subst hIsMiss
          cases hmList : (splitColumnCtors col (matrixHeadCtors (expandHeadOrRows rows))).missingCtors with
          | nil => exact (applyCtorToWitnesses_eq_nil_iff _ _ _ _).mpr (Or.inr ⟨rfl, rfl⟩)
          | cons m ms =>
            have hPrivF : col.privUninhabited = false := by
              cases hpriv : col.privUninhabited with
              | false => rfl
              | true =>
                have hBad := hCtorMem
                dsimp only [splitColumnCtors] at hmList; rw [hpriv] at hmList; contradiction
            have hmIn : m ∈ (splitColumnCtors col (matrixHeadCtors (expandHeadOrRows rows))).missingCtors := by
              rw [hmList]; exact List.mem_cons_self
            rcases missingCtor_construct_val hPrivF hmIn with ⟨v, hv, _, hDisjV⟩
            have hSubNil : (marangetCheckAux fuel' (specializeCol col .missing ++ cs)
                (specializeRows .missing (specializeCol col .missing).length (expandHeadOrRows rows))).1 = [] := by
              apply (hBranchIH .missing).mpr
              intro vsTail hvsTail
              have hvCol : ValidPlaceVal col.validity col.privUninhabited col.ty v := by
                rw [hPrivF]; exact hv
              have hTrue := hAllValid (v :: vsTail) ⟨hvCol, hvsTail⟩
              rw [← rowsUnguardedMatch_expandHeadOrRows] at hTrue
              have hDisjRows : ∀ row p ps, row ∈ expandHeadOrRows rows → row.pats = p :: ps →
                  p ≠ .wild → p.matchesVal v = false := by
                intro row p ps hrow hEqPats hpNW
                have hrWF := hWF' row hrow
                have hrOF := hOF' row hrow
                rw [hEqPats] at hrWF
                have hpOF := hrOF p ps hEqPats
                have hpHead : p.headCtor ∈ matrixHeadCtors (expandHeadOrRows rows) := by
                  have := headCtor_mem_heads_of_mem hrow
                  dsimp only [MatrixRow.headCtor] at this
                  rw [hEqPats] at this
                  exact this
                have hpWF' : PatWellFormed false col.ty p := by rw [← hPrivF]; exact hrWF.1
                exact hDisjV p hpOF hpWF' hpHead hpNW
              have hEqRow :
            rowsUnguardedMatch (specializeRows .missing 0 (expandHeadOrRows rows)) vsTail =
              rowsUnguardedMatch (expandHeadOrRows rows) (v :: vsTail) :=
          rowsUnguardedMatch_specializeRows_missing (expandHeadOrRows rows) hWF' hOF' hDisjRows
              exact hEqRow.trans hTrue
            exact (applyCtorToWitnesses_eq_nil_iff _ _ _ _).mpr (Or.inl hSubNil)
        | false =>
          have hNotMiss : ctor ≠ .missing := by cases ctor <;> first | contradiction | (intro hbad; cases hbad)
          apply (applyCtorToWitnesses_eq_nil_iff _ _ _ _).mpr
          apply Or.inl
          apply (hBranchIH ctor).mpr
          intro subVsAll hSubAll
          rcases colsValidPlaceVal_split (specializeCol col ctor) cs subVsAll hSubAll with
            ⟨subVs, vsTail, rfl, hSubCols, hTail⟩
          rcases presentCtor_construct_val hCtorMem hNotMiss hColWF hSubCols with
            ⟨v, hv, hCtorMatch, hSubLen, hSharp⟩
          have hTrue := hAllValid (v :: vsTail) ⟨hv, hTail⟩
          rw [← rowsUnguardedMatch_expandHeadOrRows] at hTrue
          have hEqRow :
              rowsUnguardedMatch
                (specializeRows ctor (specializeCol col ctor).length (expandHeadOrRows rows))
                (subVs ++ vsTail) =
              rowsUnguardedMatch (expandHeadOrRows rows) (v :: vsTail) :=
            rowsUnguardedMatch_specializeRows_ctor hCtorMatch hSubLen
              (expandHeadOrRows rows) hWF' hOF' (fun r0 pLo pHi hEq => hSharpRel ctor r0 pLo pHi hEq (hSharp r0))
          exact hEqRow.trans hTrue

/-- **Master Unconditional Witness Soundness Theorem (`marangetCheckAux`):**
For ANY `fuel`, well-formed `cols` (even when `exhPatterns = true` or `isScrutinee` deref!),
and well-formed `rows`: every witness stack emitted in `(marangetCheckAux fuel cols rows).1` denotes
an actual valid value vector `vs` (`ColsValidPlaceVal cols vs`, hence `ColsVisibleWellTyped cols vs`)
that matches `ws` and misses every unguarded row of `rows`! -/
theorem marangetCheckAux_witness_sound :
    ∀ (fuel : Nat) (cols : List ColCtx) (rows : List MatrixRow),
      ColsWellFormed cols →
      MatrixWellFormed cols rows →
      ∀ ws, ws ∈ (marangetCheckAux fuel cols rows).1 →
        ∃ vs, ColsValidPlaceVal cols vs ∧ witnessesMatchVals cols ws vs = true ∧
          WitnessMatchesPriv cols ws ∧ rowsUnguardedMatch rows vs = false := by
  intro fuel
  induction fuel with
  | zero =>
    intro _ _ _ _ ws hws
    exact False.elim (List.not_mem_nil hws)
  | succ fuel' ih =>
    intro cols rows hWFCols hWFRows ws hws
    cases cols with
    | nil =>
      dsimp only [marangetCheckAux] at hws
      cases hb : (evalBaseRows true rows).1 with
      | false => rw [hb] at hws; simp at hws
      | true =>
        rw [hb] at hws; simp only [ite_true, List.mem_singleton] at hws
        subst hws
        exact ⟨[], trivial, rfl, trivial, evalBaseRows_witness_sound rows hWFRows hb⟩
    | cons col cs =>
      dsimp only [marangetCheckAux] at hws
      rcases (mem_marangetBranches_fst_iff _ col cs _ (expandHeadOrRows rows) _ ws).mp hws with
        ⟨ctor, hCtorMem, hAppMem⟩
      have hWF' := expandHeadOrRows_wellFormed (col :: cs) rows hWFRows
      have hOF' := expandHeadOrRows_headOrFree rows
      have hColWF : col.privUninhabited = true → tyIsEmpty col.ty = true ∧ col.validity = .maybeInvalid :=
        hWFCols.1
      have hSubIH := ih (specializeCol col ctor ++ cs)
        (specializeRows ctor (specializeCol col ctor).length (expandHeadOrRows rows))
        (colsWellFormed_specializeCol col ctor cs hWFCols)
        (specializeRows_wellFormed col cs ctor (expandHeadOrRows rows) hWF' hOF')
      cases hIsMiss : (match ctor with | .missing => true | _ => false) with
      | true =>
        have hEqM : ctor = .missing := by cases ctor <;> first | contradiction | rfl
        subst hEqM
        have hmSpec := (mem_applyCtorToWitnesses_iff col _ .missing _ ws).mp hAppMem
        dsimp only at hmSpec
        rcases hmSpec with ⟨m, subWs, hmIn, hSubWsMem, rfl⟩
        rcases hSubIH subWs hSubWsMem with ⟨vsTail, hTailVal, hTailMatch, hTailPriv, hTailUnmatched⟩
        have hPrivF : col.privUninhabited = false := by
          cases hpriv : col.privUninhabited with
          | false => rfl
          | true =>
            dsimp only [splitColumnCtors] at hmIn; rw [hpriv] at hmIn; exact False.elim (List.not_mem_nil hmIn)
        rcases missingCtor_construct_val hPrivF hmIn with ⟨v, hv, hwMatch, hDisjV⟩
        have hDisjRows : ∀ row p ps, row ∈ expandHeadOrRows rows → row.pats = p :: ps →
            p ≠ .wild → p.matchesVal v = false := by
          intro row p ps hrow hEqPats hpNW
          have hrWF := hWF' row hrow
          have hrOF := hOF' row hrow
          rw [hEqPats] at hrWF
          have hpOF := hrOF p ps hEqPats
          have hpHead : p.headCtor ∈ matrixHeadCtors (expandHeadOrRows rows) := by
            have := headCtor_mem_heads_of_mem hrow
            dsimp only [MatrixRow.headCtor] at this
            rw [hEqPats] at this
            exact this
          have hpWF' : PatWellFormed false col.ty p := by rw [← hPrivF]; exact hrWF.1
          exact hDisjV p hpOF hpWF' hpHead hpNW
        have hEqRow :
            rowsUnguardedMatch (specializeRows .missing 0 (expandHeadOrRows rows)) vsTail =
              rowsUnguardedMatch (expandHeadOrRows rows) (v :: vsTail) :=
          rowsUnguardedMatch_specializeRows_missing (expandHeadOrRows rows) hWF' hOF' hDisjRows
        have hvCol : ValidPlaceVal col.validity col.privUninhabited col.ty v := by rw [hPrivF]; exact hv
        refine ⟨v :: vsTail, ⟨hvCol, hTailVal⟩, ?_, ?_, ?_⟩
        · dsimp only [specializeCol, List.nil_append] at hTailMatch
          dsimp only [witnessesMatchVals]
          rw [hwMatch, hTailMatch]; rfl
        · exact ⟨fun hbad => by rw [hbad] at hPrivF; contradiction, hTailPriv⟩
        · rw [← rowsUnguardedMatch_expandHeadOrRows]
          exact hEqRow.symm.trans hTailUnmatched
      | false =>
        have hNotMiss : ctor ≠ .missing := by cases ctor <;> first | contradiction | (intro hbad; cases hbad)
        have hNonMissSpec : ∃ subWs,
            subWs ∈ (marangetCheckAux fuel' (specializeCol col ctor ++ cs)
              (specializeRows ctor (specializeCol col ctor).length (expandHeadOrRows rows))).1 ∧
            ws = unspecializeStack col ctor subWs := by
          have hmSpec := (mem_applyCtorToWitnesses_iff col _ ctor _ ws).mp hAppMem
          cases ctor <;> first | contradiction | exact hmSpec
        rcases hNonMissSpec with ⟨subWs, hSubWsMem, rfl⟩
        rcases hSubIH subWs hSubWsMem with ⟨subVsAll, hSubAllVal, hSubMatch, hSubPriv, hSubUnmatched⟩
        rcases colsValidPlaceVal_split (specializeCol col ctor) cs subVsAll hSubAllVal with
          ⟨subVs, vsTail, rfl, hSubColsVal, hTailVal⟩
        rcases presentCtor_construct_val hCtorMem hNotMiss hColWF hSubColsVal with
          ⟨v, hv, hCtorMatch, hSubLen, hSharp⟩
        rcases unspecializeStack_matches_and_priv hCtorMatch hSubMatch hSubPriv with ⟨hLifMatch, hLifPriv⟩
        have hSharpRel : ∀ r0 pLo pHi, ctor = .intRange ⟨pLo, pHi⟩ →
            (∀ row, row ∈ expandHeadOrRows rows → row.headCtor = .intRange r0 →
              (r0.lo ≤ pLo ∧ pHi ≤ r0.hi) ∨ (∀ n, pLo ≤ n → n ≤ pHi → r0.contains n = false)) := by
          intro r0 pLo pHi hEqC row hrow hhc
          have hr0In : r0 ∈ collectIntRanges (matrixHeadCtors (expandHeadOrRows rows)) := by
            apply (mem_collectIntRanges_iff r0 _).mpr
            rw [← hhc]
            exact headCtor_mem_heads_of_mem hrow
          exact hSharp r0 pLo pHi hEqC hr0In
        have hEqRow :
            rowsUnguardedMatch
              (specializeRows ctor (specializeCol col ctor).length (expandHeadOrRows rows))
              (subVs ++ vsTail) =
            rowsUnguardedMatch (expandHeadOrRows rows) (v :: vsTail) :=
          rowsUnguardedMatch_specializeRows_ctor hCtorMatch hSubLen
            (expandHeadOrRows rows) hWF' hOF' hSharpRel
        refine ⟨v :: vsTail, ⟨hv, hTailVal⟩, hLifMatch, hLifPriv, ?_⟩
        rw [← rowsUnguardedMatch_expandHeadOrRows]
        exact hEqRow.symm.trans hSubUnmatched

/-! ### Main Public Soundness, Completeness, Witness Soundness, and Domain Separation Theorems -/

/-- Exact correspondence between single-column `armsUnguardedMatch arms v` and matrix
`rowsUnguardedMatch (armsToRows arms) [v]`. -/
theorem armsUnguardedMatch_iff_rowsUnguardedMatch (arms : List MatchArm) (v : Val) :
    rowsUnguardedMatch (armsToRows arms) [v] = armsUnguardedMatch arms v := by
  have hAux : ∀ (idx : Nat) (as : List MatchArm),
      rowsUnguardedMatch (armsToRowsAux idx as) [v] = armsUnguardedMatch as v := by
    intro idx as
    induction as generalizing idx with
    | nil => rfl
    | cons a as' ih =>
      change ((!a.hasGuard && (a.pat.matchesVal v && true) ||
          rowsUnguardedMatch (armsToRowsAux (idx + 1) as') [v]) =
        (!a.hasGuard && a.pat.matchesVal v || armsUnguardedMatch as' v))
      rw [ih (idx + 1)]
      cases a.hasGuard <;> cases a.pat.matchesVal v <;> rfl
  exact hAux 0 arms

/-- Single-column `MatchArm` well-formedness lifts to `MatrixWellFormed [col] (armsToRows arms)`. -/
theorem matrixWellFormed_armsToRows (col : ColCtx) (arms : List MatchArm)
    (hWF : ∀ a, a ∈ arms → PatWellFormed col.privUninhabited col.ty a.pat) :
    MatrixWellFormed [col] (armsToRows arms) := by
  have hAux : ∀ (idx : Nat) (as : List MatchArm),
      (∀ a, a ∈ as → PatWellFormed col.privUninhabited col.ty a.pat) →
      MatrixWellFormed [col] (armsToRowsAux idx as) := by
    intro idx as hWfAs r hr
    induction as generalizing idx with
    | nil => exact False.elim (List.not_mem_nil hr)
    | cons a as' ih =>
      dsimp only [armsToRowsAux] at hr
      rcases List.mem_cons.mp hr with rfl | hTail
      · exact ⟨hWfAs a List.mem_cons_self, trivial⟩
      · exact ih (idx + 1) (fun a0 ha0 => hWfAs a0 (List.mem_cons_of_mem a ha0)) hTail
  exact hAux 0 arms hWF

/-- Map of `evalMaranget` empty iff `evalMarangetMatrix` empty. -/
theorem evalMaranget_nil_iff (col : ColCtx) (arms : List MatchArm) :
    evalMaranget col arms = [] ↔ evalMarangetMatrix [col] (armsToRows arms) = [] := by
  dsimp only [evalMaranget]
  cases evalMarangetMatrix [col] (armsToRows arms) <;> constructor <;> intro h <;> first | rfl | contradiction

/-- **Theorem 1: Soundness & Completeness of Maranget Exhaustiveness under `.validOnly`**:
For any non-private valid column (`validity = .validOnly`, `exhPatterns = false`) and well-formed
arms: `evalMaranget col arms = []` iff every `ValidPlaceVal .validOnly false col.ty` inhabitant is
matched by an unguarded arm. -/
theorem maranget_validOnly_sound_and_complete
    (col : ColCtx) (arms : List MatchArm)
    (hVal : col.validity = .validOnly) (hPriv : col.privUninhabited = false)
    (hExh : col.exhPatterns = false)
    (hWF : ∀ a, a ∈ arms → PatWellFormed false col.ty a.pat) :
    evalMaranget col arms = [] ↔
      ∀ v, ValidPlaceVal .validOnly false col.ty v → armsUnguardedMatch arms v = true := by
  rw [evalMaranget_nil_iff]
  unfold evalMarangetMatrix
  have hWFCols : ColsWellFormed [col] := ⟨fun hbad => by rw [hbad] at hPriv; contradiction, trivial⟩
  have hSoundCols : ColsSoundCtx [col] := ⟨hExh, Or.inl hVal, trivial⟩
  have hWFRows : MatrixWellFormed [col] (armsToRows arms) :=
    matrixWellFormed_armsToRows col arms (fun a ha => by rw [hPriv]; exact hWF a ha)
  rw [marangetCheckAux_iff (colsWeight [col] + 1) [col] (armsToRows arms)
    (Nat.le_refl _) hWFCols hSoundCols hWFRows]
  constructor
  · intro hAll v hv
    rw [← armsUnguardedMatch_iff_rowsUnguardedMatch arms v]
    apply hAll [v]
    refine ⟨?_, trivial⟩
    rw [hVal, hPriv]; exact hv
  · intro hAll vs hvs
    cases vs with
    | nil => contradiction
    | cons v rest =>
      cases rest with
      | cons _ _ => exact False.elim hvs.2
      | nil =>
        rw [armsUnguardedMatch_iff_rowsUnguardedMatch]
        apply hAll v
        have hv1 := hvs.1
        rw [hVal, hPriv] at hv1
        exact hv1

/-- **Theorem 2: Soundness & Completeness under `.maybeInvalid` (No Feature Bypass, No Deref Exception)**:
For `.maybeInvalid` sub-places (`!col.exhPatterns` and `!(col.isScrutinee && NoConstructorsTy col.ty)`),
`evalMaranget col arms = []` iff every `ValidPlaceVal .maybeInvalid` value is covered by an unguarded arm. -/
theorem maranget_maybeInvalid_sound_and_complete
    (col : ColCtx) (arms : List MatchArm)
    (hVal : col.validity = .maybeInvalid) (hExh : col.exhPatterns = false)
    (hNotTop : (col.isScrutinee && NoConstructorsTy col.ty) = false)
    (hColPriv : col.privUninhabited = true → tyIsEmpty col.ty = true)
    (hWF : ∀ a, a ∈ arms → PatWellFormed col.privUninhabited col.ty a.pat) :
    evalMaranget col arms = [] ↔
      ∀ v, ValidPlaceVal .maybeInvalid col.privUninhabited col.ty v → armsUnguardedMatch arms v = true := by
  rw [evalMaranget_nil_iff]
  unfold evalMarangetMatrix
  have hWFCols : ColsWellFormed [col] := ⟨fun hp => ⟨hColPriv hp, hVal⟩, trivial⟩
  have hSoundCols : ColsSoundCtx [col] := ⟨hExh, Or.inr hNotTop, trivial⟩
  have hWFRows : MatrixWellFormed [col] (armsToRows arms) := matrixWellFormed_armsToRows col arms hWF
  rw [marangetCheckAux_iff (colsWeight [col] + 1) [col] (armsToRows arms)
    (Nat.le_refl _) hWFCols hSoundCols hWFRows]
  constructor
  · intro hAll v hv
    rw [← armsUnguardedMatch_iff_rowsUnguardedMatch arms v]
    apply hAll [v]
    refine ⟨?_, trivial⟩
    rw [hVal]; exact hv
  · intro hAll vs hvs
    cases vs with
    | nil => contradiction
    | cons v rest =>
      cases rest with
      | cons _ _ => exact False.elim hvs.2
      | nil =>
        rw [armsUnguardedMatch_iff_rowsUnguardedMatch]
        apply hAll v
        have hv1 := hvs.1
        rw [hVal] at hv1
        exact hv1

/-- **Theorem 3: Multi-Column & Single-Column Witness Soundness (`witness_soundness`)**:
Every emitted `WitnessPat` vector in `evalMarangetMatrix cols rows` corresponds to an actual
visibly well-typed value vector `vs` (`ColsVisibleWellTyped cols vs`) matching the witness and
missing every unguarded row of `rows`! -/
theorem witness_soundness
    (cols : List ColCtx) (rows : List MatrixRow)
    (hWFCols : ColsWellFormed cols) (hWFRows : MatrixWellFormed cols rows)
    (ws : List WitnessPat) (hws : ws ∈ evalMarangetMatrix cols rows) :
    ∃ vs, ColsVisibleWellTyped cols vs ∧ witnessesMatchVals cols ws vs = true ∧
      rowsUnguardedMatch rows vs = false := by
  rcases marangetCheckAux_witness_sound (colsWeight cols + 1) cols rows hWFCols hWFRows ws hws with
    ⟨vs, hVal, hMatch, _, hUnmatched⟩
  exact ⟨vs, colsValidPlaceVal_implies_visible cols vs hVal, hMatch, hUnmatched⟩

theorem evalMaranget_witness_sound
    (col : ColCtx) (arms : List MatchArm)
    (hCol : col.privUninhabited = true → tyIsEmpty col.ty = true ∧ col.validity = .maybeInvalid)
    (hWF : ∀ a, a ∈ arms → PatWellFormed col.privUninhabited col.ty a.pat)
    (w : WitnessPat) (hw : w ∈ evalMaranget col arms) :
    ∃ v, VisibleWellTyped col.validity col.ty v ∧
      w.matchesVal col.validity v = true ∧ armsUnguardedMatch arms v = false := by
  dsimp only [evalMaranget] at hw
  rcases List.mem_map.mp hw with ⟨ws, hws, hwEq⟩
  rcases witness_soundness [col] (armsToRows arms) ⟨hCol, trivial⟩
      (matrixWellFormed_armsToRows col arms hWF) ws hws with ⟨vs, hVis, hMatch, hUn⟩
  cases ws with
  | nil =>
    cases vs with
    | nil => contradiction
    | cons _ _ => contradiction
  | cons w0 ws' =>
    cases ws' with
    | cons _ _ =>
      cases vs with
      | nil => contradiction
      | cons _ vs' =>
        cases vs' with
        | nil =>
          dsimp only [witnessesMatchVals] at hMatch
          rw [Bool.and_false] at hMatch
          contradiction
        | cons _ _ => exact False.elim hVis.2
    | nil =>
      cases vs with
      | nil => contradiction
      | cons v vs' =>
        cases vs' with
        | cons _ _ => exact False.elim hVis.2
        | nil =>
          dsimp only at hwEq
          subst hwEq
          dsimp only [witnessesMatchVals] at hMatch
          rcases boolAnd_eq_true hMatch with ⟨hwm, _⟩
          rw [armsUnguardedMatch_iff_rowsUnguardedMatch arms v] at hUn
          exact ⟨v, hVis.1, hwm, hUn⟩

/-- **Theorem 4: Empty-Type Exhaustiveness (`Void`, `enum Empty {}`, `Result<u32, Void>`)**:
Any uninhabited type (`tyIsEmpty col.ty = true`) matched by value under `.validOnly` is
unconditionally exhaustive with zero arms! -/
theorem uninhabited_void_closed_exhaustive
    (col : ColCtx) (hEmpty : tyIsEmpty col.ty = true)
    (hVal : col.validity = .validOnly) (hPriv : col.privUninhabited = false)
    (hExh : col.exhPatterns = false) :
    evalMaranget col [] = [] := by
  apply (maranget_validOnly_sound_and_complete col [] hVal hPriv hExh (fun _ ha => False.elim (List.not_mem_nil ha))).mpr
  intro v hv
  exact False.elim (tyIsEmpty_validPlaceVal_validOnly_false hEmpty hv)

/-- **Theorem 5: References Are Always Considered Inhabited (`&Void` / `&!` `E0004`)**:
`match r {}` on `r : &Void` ALWAYS reports `[.ref .never]` (even with `exhaustive_patterns`),
and `Val.ref Val.invalid` witnesses the missing uncovered value (`"references are always considered inhabited"`). -/
theorem ref_void_always_inhabited (exh : Bool) :
    let rVoidCol : ColCtx := {
      ty := .ref .void, privUninhabited := false, validity := .validOnly,
      isScrutinee := true, exhPatterns := exh
    }
    evalMaranget rVoidCol [] = [.ref .never] ∧
    ValidPlaceVal .validOnly false (.ref .void) (.ref .invalid) ∧
    (WitnessPat.ref .never).matchesVal .validOnly (.ref .invalid) = true := by
  cases exh <;> exact ⟨rfl, rfl, rfl⟩

/-- **Theorem 6: Deref Uninhabited Scrutinee Exception vs. Nested Empty Payload**:
- `match *r {}` on `r : &Void` (`isScrutinee = true, validity = .maybeInvalid`) is exhaustive (`[]`)
  via `is_toplevel_exception` (`usefulness.rs:962-966`).
- `match *r { Ok(_) => ... }` on `r : &Result<u8, Void>` specializes into `.void` with
  `isScrutinee = false`, yielding `[.variant 1 .never]` when `exhPatterns = false` (`E0004`) vs. `[]`
  when `exhPatterns = true` (`#![feature(exhaustive_patterns)]`). -/
theorem deref_void_toplevel_vs_nested :
    let derefVoidCol : ColCtx := {
      ty := .void, privUninhabited := false, validity := .maybeInvalid,
      isScrutinee := true, exhPatterns := false
    }
    let derefResStdCol : ColCtx := {
      ty := .enum [.u8, .void] false, privUninhabited := false, validity := .maybeInvalid,
      isScrutinee := true, exhPatterns := false
    }
    let derefResExhCol : ColCtx := {
      ty := .enum [.u8, .void] false, privUninhabited := false, validity := .maybeInvalid,
      isScrutinee := true, exhPatterns := true
    }
    evalMaranget derefVoidCol [] = [] ∧
    evalMaranget derefResStdCol [{ pat := .variant 0 .wild, hasGuard := false }] = [.variant 1 .never] ∧
    evalMaranget derefResExhCol [{ pat := .variant 0 .wild, hasGuard := false }] = [] :=
  ⟨rfl, rfl, rfl⟩

/-- Helper: any pattern matching `Val.hiddenCtor 0` must flatten via `expandHeadOrPat` to `.wild`. -/
theorem pat_matches_hiddenCtor_implies_wild (p : Pat)
    (hm : p.matchesVal (.hiddenCtor 0) = true) :
    .wild ∈ expandHeadOrPat p := by
  induction p with
  | wild => exact List.mem_cons_self
  | orPat p1 p2 ih1 ih2 =>
    dsimp only [Pat.matchesVal] at hm
    dsimp only [expandHeadOrPat]
    rcases boolOr_eq_true hm with h1 | h2
    · exact List.mem_append_left _ (ih1 h1)
    · exact List.mem_append_right _ (ih2 h2)
  | unit | bool _ | intRange _ | pair _ _ | variant _ _ | ref _ => contradiction

/-- **Theorem 7: `#[non_exhaustive]` Hidden-Constructor Exhaustiveness Soundness**:
Downstream matching on an open `#[non_exhaustive]` enum (`enum variants true`) can ONLY be
exhaustive if some unguarded arm flattens at its root to a wildcard `_` covering `Val.hiddenCtor 0`. -/
theorem non_exhaustive_hidden_ctor_unexhausted
    (variants : List Ty) (arms : List MatchArm)
    (hWF : ∀ a, a ∈ arms → PatWellFormed false (.enum variants true) a.pat)
    (hExhZero : evalMaranget {
      ty := .enum variants true, privUninhabited := false, validity := .validOnly,
      isScrutinee := true, exhPatterns := false
    } arms = []) :
    ∃ a, a ∈ arms ∧ a.hasGuard = false ∧ .wild ∈ expandHeadOrPat a.pat := by
  let col : ColCtx := {
    ty := .enum variants true, privUninhabited := false, validity := .validOnly,
    isScrutinee := true, exhPatterns := false
  }
  have hCovered := (maranget_validOnly_sound_and_complete col arms rfl rfl rfl hWF).mp hExhZero
    (.hiddenCtor 0) trivial
  rcases (listAny_iff _ _).mp hCovered with ⟨a, haMem, haMatch⟩
  rcases boolAnd_eq_true haMatch with ⟨hgF, hpm⟩
  exact ⟨a, haMem, boolNot_eq_true hgF, pat_matches_hiddenCtor_implies_wild a.pat hpm⟩

/-- **Theorem 8: `PrivateUninhabited` Module-Local vs. Downstream Separation**:
`struct Priv { pub a: u8, _v: Void }`:
- Module-local (`bVis = true`): `match s {}` is exhaustive (`[]`).
- Downstream (`bVis = false`): `match s {}` fails with `[.pair .wild .wild]` (`E0004`), while
  `Priv { tag: 0..=255, .. }` is exhaustive (`[]`). -/
theorem private_uninhabited_vs_visible_struct :
    let privLocal : ColCtx := {
      ty := .struct2 .u8 .void true, privUninhabited := false, validity := .validOnly,
      isScrutinee := true, exhPatterns := false
    }
    let privDownstream : ColCtx := {
      ty := .struct2 .u8 .void false, privUninhabited := false, validity := .validOnly,
      isScrutinee := true, exhPatterns := false
    }
    evalMaranget privLocal [] = [] ∧
    evalMaranget privDownstream [] = [.pair .wild .wild] ∧
    evalMaranget privDownstream [{ pat := .pair (.intRange ⟨0, 255⟩) .wild, hasGuard := false }] = [] :=
  ⟨rfl, rfl, rfl⟩

/-- **Theorem 9: Guard Over-Approximation Soundness**:
1. Dropping guarded rows preserves `rowsUnguardedMatch` exactly (`rowsUnguardedMatch_filter_unguarded`).
2. Exhaustiveness (`evalMaranget = []`) is completely invariant under stripping or adding arbitrary
   well-formed guarded arms (`evalMaranget_guard_overapprox_equiv`).
3. Complementary guarded `bool` arms (`true if g1, false if g2`) are non-exhaustive (`[.bool true, .bool false]`). -/
theorem rowsUnguardedMatch_filter_unguarded (rows : List MatrixRow) (vs : List Val) :
    rowsUnguardedMatch (rows.filter (fun r => !r.isUnderGuard)) vs = rowsUnguardedMatch rows vs := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    dsimp only [List.filter, rowsUnguardedMatch]
    cases hg : r.isUnderGuard with
    | true =>
      dsimp only [Bool.not_true, ↓reduceIte, listAny]
      rw [hg]; simp only [Bool.not_true, Bool.false_and, Bool.false_or]
      exact ih
    | false =>
      simp only [Bool.not_false]
      dsimp only [listAny]
      have ih' : listAny (fun r => !r.isUnderGuard && patsMatchVals r.pats vs)
          (rs.filter (fun r => !r.isUnderGuard)) =
          listAny (fun r => !r.isUnderGuard && patsMatchVals r.pats vs) rs := ih
      rw [ih']

theorem armsUnguardedMatch_filter_unguarded (arms : List MatchArm) (v : Val) :
    armsUnguardedMatch (arms.filter (fun a => !a.hasGuard)) v = armsUnguardedMatch arms v := by
  induction arms with
  | nil => rfl
  | cons a as ih =>
    dsimp only [List.filter, armsUnguardedMatch]
    cases hg : a.hasGuard with
    | true =>
      dsimp only [Bool.not_true, ↓reduceIte, listAny]
      rw [hg]; simp only [Bool.not_true, Bool.false_and, Bool.false_or]
      exact ih
    | false =>
      simp only [Bool.not_false]
      dsimp only [listAny]
      have ih' : listAny (fun a => !a.hasGuard && a.pat.matchesVal v)
          (as.filter (fun a => !a.hasGuard)) =
          listAny (fun a => !a.hasGuard && a.pat.matchesVal v) as := ih
      rw [ih']

theorem evalMaranget_guard_overapprox_equiv
    (col : ColCtx) (arms : List MatchArm)
    (hVal : col.validity = .validOnly) (hPriv : col.privUninhabited = false)
    (hExh : col.exhPatterns = false)
    (hWF : ∀ a, a ∈ arms → PatWellFormed false col.ty a.pat) :
    evalMaranget col arms = [] ↔ evalMaranget col (arms.filter (fun a => !a.hasGuard)) = [] := by
  have hWFFilt : ∀ a, a ∈ arms.filter (fun a => !a.hasGuard) → PatWellFormed false col.ty a.pat := by
    intro a ha
    rcases List.mem_filter.mp ha with ⟨haMem, _⟩
    exact hWF a haMem
  rw [maranget_validOnly_sound_and_complete col arms hVal hPriv hExh hWF,
    maranget_validOnly_sound_and_complete col (arms.filter (fun a => !a.hasGuard)) hVal hPriv hExh hWFFilt]
  constructor
  · intro hAll v hv; rw [armsUnguardedMatch_filter_unguarded]; exact hAll v hv
  · intro hAll v hv; rw [← armsUnguardedMatch_filter_unguarded]; exact hAll v hv

theorem complementary_guarded_bool_non_exhaustive :
    let boolCol : ColCtx := {
      ty := .bool, privUninhabited := false, validity := .validOnly,
      isScrutinee := true, exhPatterns := false
    }
    let guardedArms : List MatchArm := [
      { pat := .bool true, hasGuard := true },
      { pat := .bool false, hasGuard := true }
    ]
    evalMaranget boolCol guardedArms = [.bool true, .bool false] ∧
    evalMaranget boolCol guardedArms ≠ [] := by
  refine ⟨rfl, ?_⟩
  intro hbad; cases hbad

/-- **Theorem 10: Guarded Shadowing vs. Collective Integer-Range `unreachable_patterns`**:
- A guarded arm `0..=10 if flag` leaves subsequent arm `7` useful (`evalArmUseful = true`).
- Overlapping unguarded ranges `[0..=10, 5..=15, 7]` and `[0..=10, 11..=20, 5..=15]` both mark arm `2`
  unreachable (`evalArmUseful = false`, `unreachable_patterns` `"collectively making this unreachable"`). -/
theorem arm_usefulness_guard_and_range_overlap :
    let u8Col : ColCtx := {
      ty := .u8, privUninhabited := false, validity := .validOnly,
      isScrutinee := true, exhPatterns := false
    }
    evalArmUseful u8Col [{ pat := .intRange ⟨0, 10⟩, hasGuard := true }, { pat := .intRange ⟨7, 7⟩, hasGuard := false }] 1 = true ∧
    evalArmUseful u8Col [{ pat := .intRange ⟨0, 10⟩, hasGuard := false }, { pat := .intRange ⟨5, 15⟩, hasGuard := false },
      { pat := .intRange ⟨7, 7⟩, hasGuard := false }] 2 = false ∧
    evalArmUseful u8Col [{ pat := .intRange ⟨0, 10⟩, hasGuard := false }, { pat := .intRange ⟨11, 20⟩, hasGuard := false },
      { pat := .intRange ⟨5, 15⟩, hasGuard := false }] 2 = false :=
  ⟨rfl, rfl, rfl⟩

/-! ## Section 7: Negative Controls / Counterexamples and Kernel `#print axioms` Audit -/

/-- Counterexample 1: `&Void` (`match r {}`) is ALWAYS inhabited even with `exhaustive_patterns = true`,
and witness `WitnessPat.ref .never` matches `Val.ref Val.invalid`. -/
theorem ce1_ref_void_is_non_exhaustive :
    evalMaranget {
      ty := .ref .void, privUninhabited := false, validity := .validOnly,
      isScrutinee := true, exhPatterns := true
    } [] = [.ref .never] ∧
    (WitnessPat.ref .never).matchesVal .validOnly (.ref .invalid) = true :=
  ⟨rfl, rfl⟩

/-- Counterexample 2: Complementary guarded `bool` arms fail exhaustiveness (`E0004`), returning
witnesses matching BOTH `Val.bool true` and `Val.bool false`. -/
theorem ce2_guarded_bool_non_exhaustive :
    let boolCol : ColCtx := {
      ty := .bool, privUninhabited := false, validity := .validOnly,
      isScrutinee := true, exhPatterns := false
    }
    evalMaranget boolCol [{ pat := .bool true, hasGuard := true }, { pat := .bool false, hasGuard := true }] =
      [.bool true, .bool false] :=
  rfl

/-- Counterexample 3: Matching ALL visible variants of a `#[non_exhaustive]` enum downstream still
produces `[.nonExhaustive]`, matching `Val.hiddenCtor 0`. -/
theorem ce3_non_exhaustive_enum_all_visible_insufficient :
    let col : ColCtx := {
      ty := .enum [.unit, .u8] true, privUninhabited := false, validity := .validOnly,
      isScrutinee := true, exhPatterns := false
    }
    let arms : List MatchArm := [
      { pat := .variant 0 .wild, hasGuard := false },
      { pat := .variant 1 .wild, hasGuard := false }
    ]
    evalMaranget col arms = [.nonExhaustive] ∧
    WitnessPat.nonExhaustive.matchesVal .validOnly (.hiddenCtor 0) = true :=
  ⟨rfl, rfl⟩

/-- Counterexample 4: Matching `Ok(_)` on `&Result<u8, Void>` (`*r`) WITHOUT `#![feature(exhaustive_patterns)]`
rejects (`[.variant 1 .never]`), whereas matching a by-value `Result<u8, Void>` accepts (`[]`). -/
theorem ce4_deref_result_void_without_feature_non_exhaustive :
    let byRefDerefCol : ColCtx := {
      ty := .enum [.u8, .void] false, privUninhabited := false, validity := .maybeInvalid,
      isScrutinee := true, exhPatterns := false
    }
    let byValCol : ColCtx := {
      ty := .enum [.u8, .void] false, privUninhabited := false, validity := .validOnly,
      isScrutinee := true, exhPatterns := false
    }
    let okArm : List MatchArm := [{ pat := .variant 0 .wild, hasGuard := false }]
    evalMaranget byRefDerefCol okArm = [.variant 1 .never] ∧
    evalMaranget byValCol okArm = [] :=
  ⟨rfl, rfl⟩

#print axioms tyIsEmpty_sound
#print axioms splitIntRanges_sound_and_complete
#print axioms marangetCheckAux_iff
#print axioms marangetCheckAux_witness_sound
#print axioms maranget_validOnly_sound_and_complete
#print axioms maranget_maybeInvalid_sound_and_complete
#print axioms witness_soundness
#print axioms evalMaranget_witness_sound
#print axioms uninhabited_void_closed_exhaustive
#print axioms ref_void_always_inhabited
#print axioms deref_void_toplevel_vs_nested
#print axioms non_exhaustive_hidden_ctor_unexhausted
#print axioms private_uninhabited_vs_visible_struct
#print axioms evalMaranget_guard_overapprox_equiv
#print axioms complementary_guarded_bool_non_exhaustive
#print axioms arm_usefulness_guard_and_range_overlap
#print axioms ce1_ref_void_is_non_exhaustive
#print axioms ce2_guarded_bool_non_exhaustive
#print axioms ce3_non_exhaustive_enum_all_visible_insufficient
#print axioms ce4_deref_result_void_without_feature_non_exhaustive






