-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Stratified Semantic Worlds and Guarded Lift Monad

Step-indexed semantic type syntax (`SemTy`), delayed stage types (`LaterTy`),
canonical finite worlds (`World n`), world extension (`World.Le`), disjoint
world union (`World.union`), and the guarded lift monad (`StepLift`).
-/

namespace Tulip

/-- Heap locations are natural numbers (`ℕ`). -/
abbrev Loc := Nat

/-- Semantic type codes in `Type 1`, closed under arbitrary `Type 0` constants,
products, sums, Kripke function spaces, higher-order store computations (`comp`),
typed references (`ref`), guarded type delay (`later`), and guarded recursive
types (`var`, `mu`). -/
inductive SemTy : Type 1 where
  | const : Type 0 → SemTy
  | prod  : SemTy → SemTy → SemTy
  | sum   : SemTy → SemTy → SemTy
  | arr   : SemTy → SemTy → SemTy
  | comp  : SemTy → SemTy
  | ref   : SemTy → SemTy
  | later : SemTy → SemTy
  | var   : Nat → SemTy
  | mu    : SemTy → SemTy

/-- Structural rank of unguarded type constructors (`ref`, `later`, `var`, and `mu`
either shift stage or are atomic leaves, so they have rank `0`). -/
noncomputable def SemTy.rank : SemTy → Nat
  | .const _  => 0
  | .ref _    => 0
  | .later _  => 0
  | .var _    => 0
  | .mu _     => 0
  | .prod A B => max A.rank B.rank + 1
  | .sum A B  => max A.rank B.rank + 1
  | .arr A B  => max A.rank B.rank + 1
  | .comp A   => A.rank + 1

/-- De Bruijn substitution of `target` for variable `idx` in a `SemTy`. -/
noncomputable def SemTy.substAt (idx : Nat) (target : SemTy) : SemTy → SemTy
  | .const α  => .const α
  | .prod A B => .prod (SemTy.substAt idx target A) (SemTy.substAt idx target B)
  | .sum A B  => .sum (SemTy.substAt idx target A) (SemTy.substAt idx target B)
  | .arr A B  => .arr (SemTy.substAt idx target A) (SemTy.substAt idx target B)
  | .comp A   => .comp (SemTy.substAt idx target A)
  | .ref A    => .ref (SemTy.substAt idx target A)
  | .later A  => .later (SemTy.substAt idx target A)
  | .var k    => if k == idx then target else .var k
  | .mu body  => .mu (SemTy.substAt (idx + 1) target body)

/-- Unfold body substitution `body[target / 0]`. -/
noncomputable abbrev SemTy.subst0 (body target : SemTy) : SemTy :=
  body.substAt 0 target

/-- Delayed semantic type `(▸ SemTy)_n` in the topos of trees `Psh(ωᵒᵖ)`:
trivial (`PUnit`) at stage `0`, and `SemTy` at stages `n + 1`. -/
noncomputable def LaterTy : Nat → Type 1
  | 0     => PUnit
  | _ + 1 => SemTy

/-- Embedding `next_n : SemTy → LaterTy n`. -/
noncomputable def SemTy.nextAt : (n : Nat) → SemTy → LaterTy n
  | 0,     _ => PUnit.unit
  | _ + 1, A => A

/-- Restriction of delayed semantic types along `m ≤ n`. -/
noncomputable def LaterTy.restrict : {m n : Nat} → m ≤ n → LaterTy n → LaterTy m
  | 0,     _,     _,  _ => PUnit.unit
  | _ + 1, 0,     hm, _ => nomatch hm
  | _ + 1, _ + 1, _,  A => A

@[simp]
theorem LaterTy.restrict_refl {n : Nat} (T : LaterTy n) :
    LaterTy.restrict (Nat.le_refl n) T = T := by
  cases n <;> rfl

@[simp]
theorem LaterTy.restrict_trans {k m n : Nat} (hkm : k ≤ m) (hmn : m ≤ n) (T : LaterTy n) :
    LaterTy.restrict hkm (LaterTy.restrict hmn T) = LaterTy.restrict (Nat.le_trans hkm hmn) T := by
  cases k with
  | zero => rfl
  | succ k' =>
    cases m with
    | zero => exact nomatch hkm
    | succ m' =>
      cases n with
      | zero => exact nomatch hmn
      | succ n' => rfl

@[simp]
theorem LaterTy.restrict_nextAt {m n : Nat} (hmn : m ≤ n) (A : SemTy) :
    LaterTy.restrict hmn (SemTy.nextAt n A) = SemTy.nextAt m A := by
  cases m with
  | zero => rfl
  | succ m' =>
    cases n with
    | zero => exact nomatch hmn
    | succ n' => rfl

/-! ## Canonical Finite Worlds -/

/-- Computes the canonical minimal strict upper bound of `f`'s support below `B`. -/
noncomputable def tightBoundAux {α : Type u} (f : Nat → Option α) : Nat → Nat
  | 0     => 0
  | k + 1 =>
    match f k with
    | some _ => k + 1
    | none   => tightBoundAux f k

theorem tightBoundAux_le {α : Type u} (f : Nat → Option α) (B : Nat) :
    tightBoundAux f B ≤ B := by
  induction B with
  | zero => exact Nat.le_refl 0
  | succ k ih =>
    simp only [tightBoundAux]
    cases f k with
    | some _ => exact Nat.le_refl (k + 1)
    | none => exact Nat.le_succ_of_le ih

theorem tightBoundAux_bounded {α : Type u} (f : Nat → Option α) (B : Nat)
    (hB : ∀ l, B ≤ l → f l = none) :
    ∀ l, tightBoundAux f B ≤ l → f l = none := by
  induction B with
  | zero => exact hB
  | succ k ih =>
    intro l hl
    simp only [tightBoundAux] at hl
    cases hfk : f k with
    | some _ =>
      rw [hfk] at hl
      exact hB l hl
    | none =>
      rw [hfk] at hl
      apply ih (fun m hm => ?_) l hl
      by_cases hmk : m = k
      · subst hmk; exact hfk
      · exact hB m (by omega)

theorem tightBoundAux_tight {α : Type u} (f : Nat → Option α) (B : Nat) :
    ∀ k, tightBoundAux f B = k + 1 → (f k).isSome = true := by
  induction B with
  | zero =>
    intro k hk
    simp [tightBoundAux] at hk
  | succ m ih =>
    intro k hk
    simp only [tightBoundAux] at hk
    cases hfm : f m with
    | some v =>
      rw [hfm] at hk
      injection hk with hmk
      subst hmk
      simp [hfm]
    | none =>
      rw [hfm] at hk
      exact ih k hk

/-- A stratified semantic world `World n` is a finite partial map `ℕ ⇀_fin LaterTy n`
with canonical minimal strict upper bound `bound`, ensuring extensional equality
`w₁ = w₂ ↔ w₁.cells = w₂.cells` without quotient axioms or `Classical.choice`. -/
structure World (n : Nat) : Type 1 where
  cells   : Loc → Option (LaterTy n)
  bound   : Nat
  bounded : ∀ l, bound ≤ l → cells l = none
  tight   : ∀ k, bound = k + 1 → (cells k).isSome = true

/-- Smart constructor building a `World n` from any bounded `Loc → Option (LaterTy n)`. -/
noncomputable def World.ofBounded {n : Nat} (cells : Loc → Option (LaterTy n)) (B : Nat)
    (hB : ∀ l, B ≤ l → cells l = none) : World n where
  cells   := cells
  bound   := tightBoundAux cells B
  bounded := tightBoundAux_bounded cells B hB
  tight   := tightBoundAux_tight cells B

@[simp]
theorem World.ofBounded_cells {n : Nat} (cells : Loc → Option (LaterTy n)) (B : Nat)
    (hB : ∀ l, B ≤ l → cells l = none) :
    (World.ofBounded cells B hB).cells = cells := rfl

theorem World.bound_eq_of_cells_eq {n : Nat} {w₁ w₂ : World n}
    (h : w₁.cells = w₂.cells) : w₁.bound = w₂.bound := by
  by_cases hlt1 : w₁.bound < w₂.bound
  · cases hb2 : w₂.bound with
    | zero => omega
    | succ k =>
      have hk1 : w₁.bound ≤ k := by omega
      have hnone : w₁.cells k = none := w₁.bounded k hk1
      have hsome : (w₂.cells k).isSome = true := w₂.tight k hb2
      rw [h] at hnone
      rw [hnone] at hsome
      contradiction
  · by_cases hlt2 : w₂.bound < w₁.bound
    · cases hb1 : w₁.bound with
      | zero => omega
      | succ k =>
        have hk2 : w₂.bound ≤ k := by omega
        have hnone : w₂.cells k = none := w₂.bounded k hk2
        have hsome : (w₁.cells k).isSome = true := w₁.tight k hb1
        rw [← h] at hnone
        rw [hnone] at hsome
        contradiction
    · omega

theorem World.ext {n : Nat} {w₁ w₂ : World n}
    (h : ∀ l, w₁.cells l = w₂.cells l) : w₁ = w₂ := by
  have hc : w₁.cells = w₂.cells := funext h
  have hb : w₁.bound = w₂.bound := World.bound_eq_of_cells_eq hc
  cases w₁; cases w₂
  simp only at hc hb
  subst hc; subst hb
  rfl

/-- Domain membership predicate `l ∈ |w|`. -/
noncomputable def World.mem {n : Nat} (w : World n) (l : Loc) : Bool :=
  (w.cells l).isSome

theorem World.lt_bound_of_isSome {n : Nat} (w : World n) {l : Loc}
    (h : (w.cells l).isSome = true) : l < w.bound := by
  by_cases hlt : l < w.bound
  · exact hlt
  · have hge : w.bound ≤ l := Nat.le_of_not_lt hlt
    rw [w.bounded l hge] at h
    contradiction

theorem World.lt_bound_of_some {n : Nat} (w : World n) {l : Loc} {T : LaterTy n}
    (h : w.cells l = some T) : l < w.bound :=
  w.lt_bound_of_isSome (by simp [h])

/-- Maximum allocated location in `w` (`0` if empty or only `{0}`). -/
noncomputable def World.maxLoc {n : Nat} (w : World n) : Nat :=
  w.bound - 1

/-- Deterministic fresh location `maxLoc w + 1`, guaranteed outside `|w|`. -/
noncomputable def World.fresh {n : Nat} (w : World n) : Loc :=
  w.maxLoc + 1

theorem World.bound_le_fresh {n : Nat} (w : World n) : w.bound ≤ w.fresh := by
  unfold World.fresh World.maxLoc
  omega

@[simp]
theorem World.cells_fresh {n : Nat} (w : World n) : w.cells w.fresh = none :=
  w.bounded w.fresh w.bound_le_fresh

/-- Empty world `∅`. -/
noncomputable def World.empty (n : Nat) : World n :=
  World.ofBounded (fun _ => none) 0 (fun _ _ => rfl)

@[simp]
theorem World.empty_cells (n : Nat) (l : Loc) : (World.empty n).cells l = none := rfl

@[simp]
theorem World.empty_bound (n : Nat) : (World.empty n).bound = 0 := rfl

@[simp]
theorem World.empty_fresh (n : Nat) : (World.empty n).fresh = 1 := rfl

/-- Singleton world `{l ↦ T}`. -/
noncomputable def World.singleton (n : Nat) (l : Loc) (T : LaterTy n) : World n :=
  World.ofBounded (fun l' => if l' == l then some T else none) (l + 1) (by
    intro l' hl'
    dsimp only
    have hne : (l' == l) = false := beq_false_of_ne (by omega)
    rw [hne]; rfl)

@[simp]
theorem World.singleton_cells (n : Nat) (l l' : Loc) (T : LaterTy n) :
    (World.singleton n l T).cells l' = (if l' == l then some T else none) := rfl

/-- Insert or overwrite a location `l` with type `T` in world `w`. -/
noncomputable def World.insert {n : Nat} (w : World n) (l : Loc) (T : LaterTy n) : World n :=
  World.ofBounded (fun l' => if l' == l then some T else w.cells l') (max w.bound (l + 1)) (by
    intro l' hl'
    dsimp only
    have hne : (l' == l) = false := beq_false_of_ne (by omega)
    rw [hne]
    exact w.bounded l' (by omega))

@[simp]
theorem World.insert_cells {n : Nat} (w : World n) (l l' : Loc) (T : LaterTy n) :
    (w.insert l T).cells l' = (if l' == l then some T else w.cells l') := rfl

/-- Domain restriction `w|_U` to a Boolean predicate `U : Loc → Bool`. -/
noncomputable def World.restrictDom {n : Nat} (w : World n) (U : Loc → Bool) : World n :=
  World.ofBounded (fun l => if U l then w.cells l else none) w.bound (by
    intro l hl
    dsimp only
    rw [w.bounded l hl]
    cases U l <;> rfl)

@[simp]
theorem World.restrictDom_cells {n : Nat} (w : World n) (U : Loc → Bool) (l : Loc) :
    (w.restrictDom U).cells l = (if U l then w.cells l else none) := rfl

/-- Disjointness of world supports (`|w₁| ∩ |w₂| = ∅`). -/
def World.Disjoint {n : Nat} (w₁ w₂ : World n) : Prop :=
  ∀ l, w₁.cells l = none ∨ w₂.cells l = none

theorem World.Disjoint.symm {n : Nat} {w₁ w₂ : World n} (h : World.Disjoint w₁ w₂) :
    World.Disjoint w₂ w₁ :=
  fun l => (h l).symm

/-- Left-biased union of worlds, acting as disjoint world multiplication `w₁ · w₂`
whenever `World.Disjoint w₁ w₂`. -/
noncomputable def World.union {n : Nat} (w₁ w₂ : World n) : World n :=
  World.ofBounded
    (fun l => match w₁.cells l with | some T => some T | none => w₂.cells l)
    (max w₁.bound w₂.bound)
    (by
      intro l hl
      dsimp only
      rw [w₁.bounded l (by omega), w₂.bounded l (by omega)])

@[simp]
theorem World.union_cells {n : Nat} (w₁ w₂ : World n) (l : Loc) :
    (w₁.union w₂).cells l =
      (match w₁.cells l with | some T => some T | none => w₂.cells l) := rfl

theorem World.union_comm {n : Nat} {w₁ w₂ : World n} (h : World.Disjoint w₁ w₂) :
    w₁.union w₂ = w₂.union w₁ := by
  apply World.ext
  intro l
  simp only [World.union_cells]
  rcases h l with h1 | h2
  · rw [h1]; cases w₂.cells l <;> rfl
  · rw [h2]; cases w₁.cells l <;> rfl

theorem World.union_assoc {n : Nat} (w₁ w₂ w₃ : World n) :
    (w₁.union w₂).union w₃ = w₁.union (w₂.union w₃) := by
  apply World.ext
  intro l
  simp only [World.union_cells]
  cases w₁.cells l <;> rfl

@[simp]
theorem World.union_empty {n : Nat} (w : World n) : w.union (World.empty n) = w := by
  apply World.ext
  intro l
  simp only [World.union_cells, World.empty_cells]
  cases w.cells l <;> rfl

@[simp]
theorem World.empty_union {n : Nat} (w : World n) : (World.empty n).union w = w := by
  apply World.ext
  intro l
  simp [World.union_cells]

/-- World extension partial order `w₁ ≤ w₂`: `|w₁| ⊆ |w₂|` with identical type labels. -/
def World.Le {n : Nat} (w₁ w₂ : World n) : Prop :=
  ∀ l T, w₁.cells l = some T → w₂.cells l = some T

theorem World.le_refl {n : Nat} (w : World n) : World.Le w w :=
  fun _ _ h => h

theorem World.le_trans {n : Nat} {w₁ w₂ w₃ : World n}
    (h12 : World.Le w₁ w₂) (h23 : World.Le w₂ w₃) : World.Le w₁ w₃ :=
  fun l T h => h23 l T (h12 l T h)

theorem World.le_antisymm {n : Nat} {w₁ w₂ : World n}
    (h12 : World.Le w₁ w₂) (h21 : World.Le w₂ w₁) : w₁ = w₂ := by
  apply World.ext
  intro l
  cases h1 : w₁.cells l with
  | some T => exact (h12 l T h1).symm
  | none =>
    cases h2 : w₂.cells l with
    | none => rfl
    | some T =>
      have := h21 l T h2
      rw [h1] at this
      contradiction

theorem World.empty_le {n : Nat} (w : World n) : World.Le (World.empty n) w := by
  intro l T h
  simp at h

theorem World.restrictDom_le {n : Nat} (w : World n) (U : Loc → Bool) :
    World.Le (w.restrictDom U) w := by
  intro l T h
  simp only [World.restrictDom_cells] at h
  cases hU : U l
  · rw [hU] at h; contradiction
  · rw [hU] at h; exact h

theorem World.le_union_left {n : Nat} (w₁ w₂ : World n) : World.Le w₁ (w₁.union w₂) := by
  intro l T h
  simp [World.union_cells, h]

theorem World.le_union_right {n : Nat} {w₁ w₂ : World n} (hd : World.Disjoint w₁ w₂) :
    World.Le w₂ (w₁.union w₂) := by
  intro l T h
  simp only [World.union_cells]
  rcases hd l with h1 | h2
  · rw [h1]; exact h
  · rw [h2] at h; contradiction

theorem World.le_insert_fresh {n : Nat} (w : World n) (T : LaterTy n) :
    World.Le w (w.insert w.fresh T) := by
  intro l T' h
  simp only [World.insert_cells]
  have hne : (l == w.fresh) = false := by
    apply beq_false_of_ne
    intro heq
    subst heq
    rw [w.cells_fresh] at h
    contradiction
  rw [hne]
  exact h

/-- Stage restriction `World n → World m` along `m ≤ n`. -/
noncomputable def World.restrict {m n : Nat} (hmn : m ≤ n) (w : World n) : World m :=
  World.ofBounded (fun l => (w.cells l).map (LaterTy.restrict hmn)) w.bound (by
    intro l hl
    dsimp only
    rw [w.bounded l hl]
    rfl)

@[simp]
theorem World.restrict_cells {m n : Nat} (hmn : m ≤ n) (w : World n) (l : Loc) :
    (w.restrict hmn).cells l = (w.cells l).map (LaterTy.restrict hmn) := rfl

@[simp]
theorem World.restrict_refl {n : Nat} (w : World n) :
    w.restrict (Nat.le_refl n) = w := by
  apply World.ext
  intro l
  simp only [World.restrict_cells]
  cases w.cells l <;> simp

@[simp]
theorem World.restrict_trans {k m n : Nat} (hkm : k ≤ m) (hmn : m ≤ n) (w : World n) :
    (w.restrict hmn).restrict hkm = w.restrict (Nat.le_trans hkm hmn) := by
  apply World.ext
  intro l
  simp only [World.restrict_cells, Option.map_map]
  cases w.cells l <;> simp

theorem World.restrict_bound {m n : Nat} (hmn : m ≤ n) (w : World n) :
    (w.restrict hmn).bound = w.bound := by
  have hisSome : ∀ l, ((w.restrict hmn).cells l).isSome = (w.cells l).isSome := by
    intro l
    simp only [World.restrict_cells]
    cases w.cells l <;> rfl
  by_cases hlt1 : (w.restrict hmn).bound < w.bound
  · cases hbw : w.bound with
    | zero => omega
    | succ k =>
      have hk : (w.restrict hmn).bound ≤ k := by omega
      have hnone := (w.restrict hmn).bounded k hk
      have hsome := w.tight k hbw
      rw [← hisSome k, hnone] at hsome
      contradiction
  · by_cases hlt2 : w.bound < (w.restrict hmn).bound
    · cases hbr : (w.restrict hmn).bound with
      | zero => omega
      | succ k =>
        have hk : w.bound ≤ k := by omega
        have hnone := w.bounded k hk
        have hsome := (w.restrict hmn).tight k hbr
        rw [hisSome k, hnone] at hsome
        contradiction
    · omega

@[simp]
theorem World.restrict_fresh {m n : Nat} (hmn : m ≤ n) (w : World n) :
    (w.restrict hmn).fresh = w.fresh := by
  simp [World.fresh, World.maxLoc, World.restrict_bound]

theorem World.restrict_mono {m n : Nat} (hmn : m ≤ n) {w₁ w₂ : World n}
    (hle : World.Le w₁ w₂) : World.Le (w₁.restrict hmn) (w₂.restrict hmn) := by
  intro l T h
  simp only [World.restrict_cells] at h ⊢
  cases hc : w₁.cells l with
  | none => rw [hc] at h; contradiction
  | some T' =>
    rw [hc] at h
    simp only [Option.map] at h
    rw [hle l T' hc]
    simp [Option.map, h]

@[simp]
theorem World.restrict_insert {m n : Nat} (hmn : m ≤ n) (w : World n) (l : Loc) (T : LaterTy n) :
    (w.insert l T).restrict hmn = (w.restrict hmn).insert l (LaterTy.restrict hmn T) := by
  apply World.ext
  intro l'
  simp only [World.restrict_cells, World.insert_cells]
  cases l' == l <;> rfl

@[simp]
theorem World.restrict_union {m n : Nat} (hmn : m ≤ n) (w₁ w₂ : World n) :
    (w₁.union w₂).restrict hmn = (w₁.restrict hmn).union (w₂.restrict hmn) := by
  apply World.ext
  intro l
  simp only [World.restrict_cells, World.union_cells]
  cases w₁.cells l <;> rfl

@[simp]
theorem World.restrict_restrictDom {m n : Nat} (hmn : m ≤ n) (w : World n) (U : Loc → Bool) :
    (w.restrictDom U).restrict hmn = (w.restrict hmn).restrictDom U := by
  apply World.ext
  intro l
  simp only [World.restrict_cells, World.restrictDom_cells]
  cases U l <;> rfl

/-- Single-step world truncation `World (n + 1) → World n`. -/
noncomputable abbrev World.trunc {n : Nat} (w : World (n + 1)) : World n :=
  w.restrict (Nat.le_succ_of_le (Nat.le_refl n))

/-! ## Step-Indexed Guarded Lift Monad `L` (`StepLift`) -/

/-- The step-indexed guarded lift monad `L` (`L A = A + ▸ L A`, `paper.tex:1319`)
over stage-indexed answer families `X : (m : Nat) → m ≤ n → Type 1`. -/
noncomputable def StepLift : (n : Nat) → ((m : Nat) → m ≤ n → Type 1) → Type 1
  | 0,     X => X 0 (Nat.le_refl 0) ⊕ PUnit.{2}
  | k + 1, X =>
      X (k + 1) (Nat.le_refl (k + 1)) ⊕
        StepLift k (fun m hm => X m (Nat.le_succ_of_le hm))

/-- Immediate return `η : X_n → (L X)_n` (0 computation steps). -/
noncomputable def StepLift.ret : {n : Nat} → {X : (m : Nat) → m ≤ n → Type 1} →
    X n (Nat.le_refl n) → StepLift n X
  | 0,     _, x => Sum.inl x
  | _ + 1, _, x => Sum.inl x

/-- Stage-`0` guarded step (`ϑ` at horizon `0`). -/
noncomputable def StepLift.stepZero {X : (m : Nat) → m ≤ 0 → Type 1} : StepLift 0 X :=
  Sum.inr PUnit.unit

/-- Stage-`(k + 1)` guarded step (`ϑ : ▸(L X)_{k+1} → (L X)_{k+1}`). -/
noncomputable def StepLift.stepSucc {k : Nat} {X : (m : Nat) → m ≤ k + 1 → Type 1}
    (c : StepLift k (fun m hm => X m (Nat.le_succ_of_le hm))) : StepLift (k + 1) X :=
  Sum.inr c

/-- Monadic bind for `StepLift`. Lean's definitional proof irrelevance for `≤ : Prop`
makes the continuation's answer family definitionally equal to `Y`. -/
noncomputable def StepLift.bind : {n : Nat} → {X Y : (m : Nat) → m ≤ n → Type 1} →
    StepLift n X →
    (∀ (m : Nat) (hm : m ≤ n), X m hm → StepLift m (fun j hj => Y j (Nat.le_trans hj hm))) →
    StepLift n Y
  | 0,     _, _, Sum.inl x,  k => k 0 (Nat.le_refl 0) x
  | 0,     _, _, Sum.inr _,  _ => Sum.inr PUnit.unit
  | m + 1, _, _, Sum.inl x,  k => k (m + 1) (Nat.le_refl (m + 1)) x
  | _ + 1, _, _, Sum.inr c', k =>
      Sum.inr (StepLift.bind c' (fun j hj x => k j (Nat.le_succ_of_le hj) x))

@[simp]
theorem StepLift.bind_ret {n : Nat} {X Y : (m : Nat) → m ≤ n → Type 1}
    (x : X n (Nat.le_refl n))
    (k : ∀ (m : Nat) (hm : m ≤ n), X m hm → StepLift m (fun j hj => Y j (Nat.le_trans hj hm))) :
    StepLift.bind (StepLift.ret x) k = k n (Nat.le_refl n) x := by
  cases n <;> rfl

@[simp]
theorem StepLift.bind_stepZero {X Y : (m : Nat) → m ≤ 0 → Type 1}
    (k : ∀ (m : Nat) (hm : m ≤ 0), X m hm → StepLift m (fun j hj => Y j (Nat.le_trans hj hm))) :
    StepLift.bind (StepLift.stepZero (X := X)) k = StepLift.stepZero := rfl

@[simp]
theorem StepLift.bind_stepSucc {n : Nat} {X Y : (m : Nat) → m ≤ n + 1 → Type 1}
    (c : StepLift n (fun m hm => X m (Nat.le_succ_of_le hm)))
    (k : ∀ (m : Nat) (hm : m ≤ n + 1), X m hm → StepLift m (fun j hj => Y j (Nat.le_trans hj hm))) :
    StepLift.bind (StepLift.stepSucc c) k =
      StepLift.stepSucc (StepLift.bind c (fun j hj x => k j (Nat.le_succ_of_le hj) x)) := rfl

@[simp]
theorem StepLift.bind_ret_right {n : Nat} {X : (m : Nat) → m ≤ n → Type 1}
    (c : StepLift n X) :
    StepLift.bind c (fun _ _ x => StepLift.ret x) = c := by
  induction n with
  | zero =>
    cases c with
    | inl x => rfl
    | inr u => cases u; rfl
  | succ m ih =>
    cases c with
    | inl x => rfl
    | inr c' => exact congrArg Sum.inr (ih c')

theorem StepLift.bind_assoc {n : Nat} {X Y Z : (m : Nat) → m ≤ n → Type 1}
    (c : StepLift n X)
    (k₁ : ∀ (m : Nat) (hm : m ≤ n), X m hm → StepLift m (fun j hj => Y j (Nat.le_trans hj hm)))
    (k₂ : ∀ (m : Nat) (hm : m ≤ n), Y m hm → StepLift m (fun j hj => Z j (Nat.le_trans hj hm))) :
    StepLift.bind (StepLift.bind c k₁) k₂ =
      StepLift.bind c (fun m hm x =>
        StepLift.bind (k₁ m hm x) (fun j hj y => k₂ j (Nat.le_trans hj hm) y)) := by
  induction n with
  | zero =>
    cases c <;> rfl
  | succ m ih =>
    cases c with
    | inl x => rfl
    | inr c' => exact congrArg Sum.inr (ih c' _ _)

/-- Predicate lifting `c ⇓ Φ` (`StepLift.lLift`) from Construction 4.7
(`paper.tex:1341–1350`): asserts that within the current `n`-step observation window,
every terminal value produced by `c` satisfies `Φ` (automatically `True` once `c`
steps past the stage-`0` horizon). -/
noncomputable def StepLift.lLift : {n : Nat} → {X : (m : Nat) → m ≤ n → Type 1} →
    StepLift n X → (∀ (m : Nat) (hm : m ≤ n), X m hm → Prop) → Prop
  | 0,     _, Sum.inl x,  Φ => Φ 0 (Nat.le_refl 0) x
  | 0,     _, Sum.inr _,  _ => True
  | m + 1, _, Sum.inl x,  Φ => Φ (m + 1) (Nat.le_refl (m + 1)) x
  | _ + 1, _, Sum.inr c', Φ =>
      StepLift.lLift c' (fun j hj x => Φ j (Nat.le_succ_of_le hj) x)

@[simp]
theorem StepLift.lLift_ret {n : Nat} {X : (m : Nat) → m ≤ n → Type 1}
    (x : X n (Nat.le_refl n)) (Φ : ∀ (m : Nat) (hm : m ≤ n), X m hm → Prop) :
    StepLift.lLift (StepLift.ret x) Φ = Φ n (Nat.le_refl n) x := by
  cases n <;> rfl

@[simp]
theorem StepLift.lLift_stepZero {X : (m : Nat) → m ≤ 0 → Type 1}
    (Φ : ∀ (m : Nat) (hm : m ≤ 0), X m hm → Prop) :
    StepLift.lLift (StepLift.stepZero (X := X)) Φ = True := rfl

@[simp]
theorem StepLift.lLift_stepSucc {n : Nat} {X : (m : Nat) → m ≤ n + 1 → Type 1}
    (c : StepLift n (fun m hm => X m (Nat.le_succ_of_le hm)))
    (Φ : ∀ (m : Nat) (hm : m ≤ n + 1), X m hm → Prop) :
    StepLift.lLift (StepLift.stepSucc c) Φ =
      StepLift.lLift c (fun j hj x => Φ j (Nat.le_succ_of_le hj) x) := rfl

theorem StepLift.lLift_mono {n : Nat} {X : (m : Nat) → m ≤ n → Type 1}
    (c : StepLift n X) {Φ Ψ : ∀ (m : Nat) (hm : m ≤ n), X m hm → Prop}
    (himp : ∀ m hm x, Φ m hm x → Ψ m hm x) :
    StepLift.lLift c Φ → StepLift.lLift c Ψ := by
  induction n with
  | zero =>
    cases c with
    | inl x => exact himp 0 (Nat.le_refl 0) x
    | inr _ => exact id
  | succ m ih =>
    cases c with
    | inl x => exact himp (m + 1) (Nat.le_refl (m + 1)) x
    | inr c' => exact ih c' (fun j hj x => himp j (Nat.le_succ_of_le hj) x)

theorem StepLift.lLift_bind {n : Nat} {X Y : (m : Nat) → m ≤ n → Type 1}
    (c : StepLift n X)
    (k : ∀ (m : Nat) (hm : m ≤ n), X m hm → StepLift m (fun j hj => Y j (Nat.le_trans hj hm)))
    (Ψ : ∀ (m : Nat) (hm : m ≤ n), Y m hm → Prop) :
    StepLift.lLift c (fun m hm x =>
        StepLift.lLift (k m hm x) (fun j hj y => Ψ j (Nat.le_trans hj hm) y)) →
      StepLift.lLift (StepLift.bind c k) Ψ := by
  induction n with
  | zero =>
    cases c with
    | inl x => exact id
    | inr _ => exact fun _ => trivial
  | succ m ih =>
    cases c with
    | inl x => exact id
    | inr c' =>
      exact ih c' (fun j hj x => k j (Nat.le_succ_of_le hj) x)
        (fun j hj y => Ψ j (Nat.le_succ_of_le hj) y)

/-- Guarded fixed point `gfix` on `StepLift` computations: given a guarded step
body `f`, computes the canonical guarded fixed point at every stage `n`. -/
noncomputable def StepLift.gfix {X : Nat → Type 1}
    (f : ∀ (k : Nat), StepLift k (fun m _ => X m) → StepLift k (fun m _ => X m)) :
    (n : Nat) → StepLift n (fun m _ => X m)
  | 0     => StepLift.stepZero
  | k + 1 => StepLift.stepSucc (f k (StepLift.gfix f k))

/-- Diverging guarded computation `Ω = gfix id`, taking one step at every stage. -/
noncomputable def StepLift.omega {X : Nat → Type 1} (n : Nat) : StepLift n (fun m _ => X m) :=
  StepLift.gfix (fun _ c => c) n

theorem StepLift.omega_lLift_false {X : Nat → Type 1} (n : Nat) :
    StepLift.lLift (StepLift.omega (X := X) n) (fun _ _ _ => False) := by
  induction n with
  | zero => trivial
  | succ k ih => exact ih

end Tulip
