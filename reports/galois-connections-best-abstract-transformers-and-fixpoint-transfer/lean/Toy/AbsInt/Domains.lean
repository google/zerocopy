/-
Toy.AbsInt.Domains
==================

Small concrete abstract domains used as fixtures by the counterexamples,
non-vacuity witnesses and definition examples.  Each comes with a decidable
`≤` so that facts about closed terms are checked by `decide`.

* `B2`   — the two-element chain `lo ≤ hi`.
* `NR2`  — two elements, `a ≤ b ↔ a = lo`: transitive, not reflexive at `hi`.
* `NT3`  — `lo ≤ mid ≤ hi` (plus reflexivity) but not `lo ≤ hi`: reflexive, not transitive.
* `NT4`  — `z` below everything, `p ≤ q ≤ r`, not `p ≤ r`: reflexive, not transitive.
* `Dis2` — two elements with the discrete order (only `a ≤ a`).
* `V3`   — `bot` below two incomparable elements `x`, `y`.
* `W4`   — the poset `z < m < p`, `m < q`, with `p`, `q` incomparable.
* `NT4w` — a four-element reflexive, non-transitive relation with a least element.
* `PT`   — pairs of naturals under the product order, plus a top element.
* `UB`   — the "upper bound" domain `bot < atMost 0 < atMost 1 < … < top`, of infinite height.
* `E2`   — two elements, each below the other: a total preorder that is not antisymmetric.
* `NR3`  — three elements, transitive, not reflexive at `mid`.
* `Cyc3` — three elements with a strict cycle `c0 < c1 < c2 < c0`: reflexive, not transitive.
* `NB`   — pairs `(n, b)` with a reflexive, non-transitive relation of height `1`
  that still admits a non-stabilizing ascending sequence.

Plus helpers for the one-state concrete domain `Pred Unit`.
-/
import Toy.AbsInt.Basic

namespace Toy.AbsInt

/-! ## Helpers for `Pred Unit` -/

/-- An abstraction on the one-state concrete domain: `∅ ↦ lo`, `{()} ↦ hi`. -/
noncomputable def unitAlpha {A : Type} (lo hi : A) (x : Pred Unit) : A :=
  open Classical in if x () then hi else lo

theorem unitAlpha_pos {A : Type} (lo hi : A) {x : Pred Unit} (h : x ()) :
    unitAlpha lo hi x = hi := by
  unfold unitAlpha; simp [h]

theorem unitAlpha_neg {A : Type} (lo hi : A) {x : Pred Unit} (h : ¬ x ()) :
    unitAlpha lo hi x = lo := by
  unfold unitAlpha; simp [h]

/-- The constant-`∅` and constant-full predicates on `Unit`, as abbreviations. -/
abbrev E : Pred Unit := Pred.empty Unit
abbrev U : Pred Unit := Pred.univ Unit

theorem le_U {σ : Type} (x : Pred σ) : x ≤ Pred.univ σ := fun _ _ => trivial
theorem E_le {σ : Type} (x : Pred σ) : Pred.empty σ ≤ x := fun _ h => h.elim
theorem not_U_le_E : ¬ (U ≤ E) := fun h => h () trivial

/-! ## `B2`: the two-element chain -/

inductive B2 | lo | hi
  deriving DecidableEq, Repr

def B2.leb : B2 → B2 → Bool
  | .lo, _ => true
  | .hi, .hi => true
  | .hi, .lo => false

instance : LE B2 := ⟨fun a b => B2.leb a b = true⟩
instance (a b : B2) : Decidable (a ≤ b) := inferInstanceAs (Decidable (B2.leb a b = true))

theorem B2.isRefl : IsRefl B2 := by intro a; cases a <;> decide
theorem B2.le_hi (a : B2) : a ≤ B2.hi := by cases a <;> decide
theorem B2.lo_le (a : B2) : B2.lo ≤ a := by cases a <;> decide
theorem B2.isTrans : IsTrans B2 := by
  intro a b c; cases a <;> cases b <;> cases c <;> decide
theorem B2.acc : ACC B2 :=
  acc_of_rank (fun | .lo => 0 | .hi => 1) 1
    (by intro a b; cases a <;> cases b <;> decide)
    (by intro a; cases a <;> decide)

/-! ## `NR2`: transitive but not reflexive -/

inductive NR2 | lo | hi
  deriving DecidableEq, Repr

def NR2.leb : NR2 → NR2 → Bool
  | .lo, _ => true
  | .hi, _ => false

instance : LE NR2 := ⟨fun a b => NR2.leb a b = true⟩
instance (a b : NR2) : Decidable (a ≤ b) := inferInstanceAs (Decidable (NR2.leb a b = true))

theorem NR2.isTrans : IsTrans NR2 := by
  intro a b c; cases a <;> cases b <;> cases c <;> decide
theorem NR2.not_isRefl : ¬ IsRefl NR2 := fun h => absurd (h .hi) (by decide)

/-! ## `NT3`: reflexive but not transitive -/

inductive NT3 | lo | mid | hi
  deriving DecidableEq, Repr

def NT3.leb : NT3 → NT3 → Bool
  | .lo, .lo => true
  | .mid, .mid => true
  | .hi, .hi => true
  | .lo, .mid => true
  | .mid, .hi => true
  | _, _ => false

instance : LE NT3 := ⟨fun a b => NT3.leb a b = true⟩
instance (a b : NT3) : Decidable (a ≤ b) := inferInstanceAs (Decidable (NT3.leb a b = true))

theorem NT3.isRefl : IsRefl NT3 := by intro a; cases a <;> decide
theorem NT3.not_isTrans : ¬ IsTrans NT3 :=
  fun h => absurd (h .lo .mid .hi (by decide) (by decide)) (by decide)

/-! ## `NT4`: reflexive, a least element, not transitive -/

inductive NT4 | z | p | q | r
  deriving DecidableEq, Repr

def NT4.leb : NT4 → NT4 → Bool
  | .z, _ => true
  | .p, .p => true
  | .p, .q => true
  | .q, .q => true
  | .q, .r => true
  | .r, .r => true
  | _, _ => false

instance : LE NT4 := ⟨fun a b => NT4.leb a b = true⟩
instance (a b : NT4) : Decidable (a ≤ b) := inferInstanceAs (Decidable (NT4.leb a b = true))

theorem NT4.isRefl : IsRefl NT4 := by intro a; cases a <;> decide
theorem NT4.not_isTrans : ¬ IsTrans NT4 :=
  fun h => absurd (h .p .q .r (by decide) (by decide)) (by decide)

/-! ## `Dis2`: the discrete order on two elements -/

inductive Dis2 | a | b
  deriving DecidableEq, Repr

def Dis2.leb : Dis2 → Dis2 → Bool
  | .a, .a => true
  | .b, .b => true
  | _, _ => false

instance : LE Dis2 := ⟨fun x y => Dis2.leb x y = true⟩
instance (x y : Dis2) : Decidable (x ≤ y) := inferInstanceAs (Decidable (Dis2.leb x y = true))

theorem Dis2.isRefl : IsRefl Dis2 := by intro x; cases x <;> decide
theorem Dis2.isTrans : IsTrans Dis2 := by
  intro x y z; cases x <;> cases y <;> cases z <;> decide
theorem Dis2.heightLE : HeightLE Dis2 0 :=
  heightLE_of_rank (fun _ => 0) 0
    (by intro x y; cases x <;> cases y <;> decide)
    (by intro x; exact Nat.le_refl _)
theorem Dis2.acc : ACC Dis2 :=
  acc_of_rank (fun _ => 0) 0
    (by intro x y; cases x <;> cases y <;> decide)
    (by intro x; exact Nat.le_refl _)

/-! ## `V3`: a least element below two incomparable elements -/

inductive V3 | bot | x | y
  deriving DecidableEq, Repr

def V3.leb : V3 → V3 → Bool
  | .bot, _ => true
  | .x, .x => true
  | .y, .y => true
  | _, _ => false

instance : LE V3 := ⟨fun a b => V3.leb a b = true⟩
instance (a b : V3) : Decidable (a ≤ b) := inferInstanceAs (Decidable (V3.leb a b = true))

theorem V3.isRefl : IsRefl V3 := by intro a; cases a <;> decide
theorem V3.isTrans : IsTrans V3 := by
  intro a b c; cases a <;> cases b <;> cases c <;> decide
def V3.rank : V3 → Nat
  | .bot => 0
  | _ => 1
theorem V3.rank_strict : ∀ a b : V3, StrictLt a b → V3.rank a < V3.rank b := by
  intro a b; cases a <;> cases b <;> decide
theorem V3.heightLE : HeightLE V3 1 :=
  heightLE_of_rank V3.rank 1 V3.rank_strict (by intro a; cases a <;> decide)
theorem V3.acc : ACC V3 :=
  acc_of_rank V3.rank 1 V3.rank_strict (by intro a; cases a <;> decide)

/-! ## `W4`: the poset `z < m < p`, `m < q` -/

inductive W4 | z | m | p | q
  deriving DecidableEq, Repr

def W4.leb : W4 → W4 → Bool
  | .z, _ => true
  | .m, .m => true
  | .m, .p => true
  | .m, .q => true
  | .p, .p => true
  | .q, .q => true
  | _, _ => false

instance : LE W4 := ⟨fun a b => W4.leb a b = true⟩
instance (a b : W4) : Decidable (a ≤ b) := inferInstanceAs (Decidable (W4.leb a b = true))

theorem W4.isRefl : IsRefl W4 := by intro a; cases a <;> decide
theorem W4.isTrans : IsTrans W4 := by
  intro a b c; cases a <;> cases b <;> cases c <;> decide
theorem W4.acc : ACC W4 :=
  acc_of_rank (fun | .z => 0 | .m => 1 | .p => 2 | .q => 2) 2
    (by intro a b; cases a <;> cases b <;> decide)
    (by intro a; cases a <;> decide)

/-! ## `NT4w`: reflexive, least element `bot`, not transitive -/

inductive NT4w | bot | u | t | w
  deriving DecidableEq, Repr

def NT4w.leb : NT4w → NT4w → Bool
  | .bot, _ => true
  | .u, .u => true
  | .u, .bot => true
  | .t, .t => true
  | .t, .u => true
  | .t, .w => true
  | .w, .w => true
  | .w, .t => true
  | .w, .bot => true
  | _, _ => false

instance : LE NT4w := ⟨fun a b => NT4w.leb a b = true⟩
instance (a b : NT4w) : Decidable (a ≤ b) := inferInstanceAs (Decidable (NT4w.leb a b = true))

theorem NT4w.isRefl : IsRefl NT4w := by intro a; cases a <;> decide
theorem NT4w.not_isTrans : ¬ IsTrans NT4w :=
  fun h => absurd (h .t .u .bot (by decide) (by decide)) (by decide)
theorem NT4w.acc : ACC NT4w :=
  acc_of_rank (fun | .bot => 0 | .t => 1 | .u => 2 | .w => 0) 2
    (by intro a b; cases a <;> cases b <;> decide)
    (by intro a; cases a <;> decide)

/-! ## `PT`: pairs of naturals with the product order, plus a top element -/

inductive PT | pt (i j : Nat) | top
  deriving DecidableEq, Repr

def PT.leb : PT → PT → Bool
  | .pt i j, .pt i' j' => decide (i ≤ i') && decide (j ≤ j')
  | _, .top => true
  | .top, .pt _ _ => false

instance : LE PT := ⟨fun a b => PT.leb a b = true⟩
instance (a b : PT) : Decidable (a ≤ b) := inferInstanceAs (Decidable (PT.leb a b = true))

@[simp] theorem PT.pt_le_pt (i j i' j' : Nat) : (PT.pt i j ≤ PT.pt i' j') ↔ (i ≤ i' ∧ j ≤ j') := by
  show PT.leb _ _ = true ↔ _
  simp [PT.leb]
@[simp] theorem PT.le_top (a : PT) : a ≤ PT.top := by
  show PT.leb _ _ = true
  cases a <;> rfl
@[simp] theorem PT.not_top_le_pt (i j : Nat) : ¬ (PT.top ≤ PT.pt i j) := by
  show ¬ (PT.leb _ _ = true)
  simp [PT.leb]

theorem PT.isRefl : IsRefl PT := by
  intro a; cases a <;> simp
theorem PT.isTrans : IsTrans PT := by
  intro a b c hab hbc
  cases a <;> cases b <;> cases c <;> simp_all <;> omega

/-! ## `UB`: upper bounds of a natural-number counter (infinite height) -/

/-- The "upper bound" abstract domain for a natural-number variable:
`bot` (no value), `atMost n` (every value is `≤ n`), `top` (any value).  It has
infinite strictly ascending chains `atMost 0 < atMost 1 < …`. -/
inductive UB | bot | atMost (n : Nat) | top
  deriving DecidableEq, Repr

def UB.leb : UB → UB → Bool
  | .bot, _ => true
  | .atMost m, .atMost n => decide (m ≤ n)
  | _, .top => true
  | _, _ => false

instance : LE UB := ⟨fun a b => UB.leb a b = true⟩
instance (a b : UB) : Decidable (a ≤ b) := inferInstanceAs (Decidable (UB.leb a b = true))

@[simp] theorem UB.bot_le (a : UB) : UB.bot ≤ a := by
  show UB.leb _ _ = true
  cases a <;> rfl
@[simp] theorem UB.le_top (a : UB) : a ≤ UB.top := by
  show UB.leb _ _ = true
  cases a <;> rfl
@[simp] theorem UB.atMost_le_atMost (m n : Nat) : (UB.atMost m ≤ UB.atMost n) ↔ m ≤ n := by
  show UB.leb _ _ = true ↔ _
  simp [UB.leb]
@[simp] theorem UB.not_atMost_le_bot (m : Nat) : ¬ (UB.atMost m ≤ UB.bot) := by
  show ¬ (UB.leb _ _ = true)
  simp [UB.leb]
@[simp] theorem UB.not_top_le_bot : ¬ (UB.top ≤ UB.bot) := by
  show ¬ (UB.leb _ _ = true)
  simp [UB.leb]
@[simp] theorem UB.not_top_le_atMost (m : Nat) : ¬ (UB.top ≤ UB.atMost m) := by
  show ¬ (UB.leb _ _ = true)
  simp [UB.leb]

theorem UB.isRefl : IsRefl UB := by
  intro a; cases a <;> simp
theorem UB.isTrans : IsTrans UB := by
  intro a b c hab hbc
  cases a <;> cases b <;> cases c <;> simp_all <;> omega

/-- `UB` violates the ascending chain condition: `atMost 0 < atMost 1 < …`. -/
theorem UB.not_acc : ¬ ACC UB := by
  intro h
  apply h
  refine ⟨fun n => UB.atMost n, fun n => ?_⟩
  simp [StrictLt]

/-- Concretization for `UB`: `atMost n` denotes `{k | k ≤ n}`. -/
def ubGamma : UB → Pred Nat
  | .bot => fun _ => False
  | .atMost n => fun k => k ≤ n
  | .top => fun _ => True

theorem ubGamma_monotone : Monotone ubGamma := by
  intro a b hab k hk
  cases a <;> cases b <;> simp_all [ubGamma] <;> omega

/-- Positive example for `ubGamma`: `atMost 2` admits the value `1`. -/
theorem ubGamma_example_pos : ubGamma (UB.atMost 2) 1 := by
  show 1 ≤ 2; omega

/-- Negative example for `ubGamma`: `atMost 0` rejects the value `1`. -/
theorem ubGamma_example_neg : ¬ ubGamma (UB.atMost 0) 1 := by
  show ¬ (1 ≤ 0); omega

/-! ## `E2`: a two-element total preorder that is not antisymmetric -/

inductive E2 | a | b
  deriving DecidableEq, Repr

instance : LE E2 := ⟨fun _ _ => True⟩
instance (x y : E2) : Decidable (x ≤ y) := inferInstanceAs (Decidable True)

theorem E2.isRefl : IsRefl E2 := fun _ => trivial
theorem E2.isTrans : IsTrans E2 := fun _ _ _ _ _ => trivial
theorem E2.not_isAntisymm : ¬ IsAntisymm E2 :=
  fun h => absurd (h E2.a E2.b trivial trivial) (by decide)
theorem E2.heightLE : HeightLE E2 0 := by
  intro c k hc
  cases k with
  | zero => exact Nat.le_refl 0
  | succ k => exact ((hc 0 (Nat.zero_lt_succ k)).2 trivial).elim

/-! ## `NR3`: transitive, not reflexive at `mid` -/

inductive NR3 | lo | mid | hi
  deriving DecidableEq, Repr

def NR3.leb : NR3 → NR3 → Bool
  | .lo, _ => true
  | .mid, .hi => true
  | .hi, .hi => true
  | _, _ => false

instance : LE NR3 := ⟨fun a b => NR3.leb a b = true⟩
instance (a b : NR3) : Decidable (a ≤ b) := inferInstanceAs (Decidable (NR3.leb a b = true))

theorem NR3.isTrans : IsTrans NR3 := by
  intro a b c; cases a <;> cases b <;> cases c <;> decide
theorem NR3.not_isRefl : ¬ IsRefl NR3 := fun h => absurd (h .mid) (by decide)

/-! ## `Cyc3`: a reflexive relation with a strict cycle -/

inductive Cyc3 | c0 | c1 | c2
  deriving DecidableEq, Repr

def Cyc3.leb : Cyc3 → Cyc3 → Bool
  | .c0, .c0 => true
  | .c1, .c1 => true
  | .c2, .c2 => true
  | .c0, .c1 => true
  | .c1, .c2 => true
  | .c2, .c0 => true
  | _, _ => false

instance : LE Cyc3 := ⟨fun a b => Cyc3.leb a b = true⟩
instance (a b : Cyc3) : Decidable (a ≤ b) := inferInstanceAs (Decidable (Cyc3.leb a b = true))

/-- The successor along the cycle `c0 → c1 → c2 → c0`. -/
def Cyc3.next : Cyc3 → Cyc3
  | .c0 => .c1
  | .c1 => .c2
  | .c2 => .c0

theorem Cyc3.isRefl : IsRefl Cyc3 := by intro a; cases a <;> decide
theorem Cyc3.not_isTrans : ¬ IsTrans Cyc3 :=
  fun h => absurd (h .c0 .c1 .c2 (by decide) (by decide)) (by decide)
theorem Cyc3.strict_next (a : Cyc3) : StrictLt a a.next := by cases a <;> decide

/-! ## `NB`: a non-transitive relation of height `1` -/

/-- Pairs `(n, b)`; `(m, s) ≤ (n, t)` iff `m = n`, or `s = true`, `t = false` and
`n = m + 1`.  Reflexive, not transitive. -/
inductive NB | mk (n : Nat) (b : Bool)
  deriving DecidableEq, Repr

def NB.leb : NB → NB → Bool
  | .mk m s, .mk n t => decide (m = n) || (s && !t && decide (n = m + 1))

instance : LE NB := ⟨fun a b => NB.leb a b = true⟩
instance (a b : NB) : Decidable (a ≤ b) := inferInstanceAs (Decidable (NB.leb a b = true))

theorem NB.le_iff (m n : Nat) (s t : Bool) :
    (NB.mk m s ≤ NB.mk n t) ↔ (m = n ∨ (s = true ∧ t = false ∧ n = m + 1)) := by
  show NB.leb _ _ = true ↔ _
  cases s <;> cases t <;> simp [NB.leb]

theorem NB.isRefl : IsRefl NB := by
  intro a; cases a with
  | mk n b => exact (NB.le_iff n n b b).mpr (Or.inl rfl)

theorem NB.not_isTrans : ¬ IsTrans NB := by
  intro h
  have h1 : NB.mk 0 false ≤ NB.mk 0 true := (NB.le_iff 0 0 false true).mpr (Or.inl rfl)
  have h2 : NB.mk 0 true ≤ NB.mk 1 false :=
    (NB.le_iff 0 1 true false).mpr (Or.inr ⟨rfl, rfl, rfl⟩)
  have h3 := (NB.le_iff 0 1 false false).mp (h _ _ _ h1 h2)
  rcases h3 with h3 | ⟨h3, _, _⟩
  · exact absurd h3 (by decide)
  · exact absurd h3 (by decide)

/-- A strict step of `NB` always goes from a `true` tag to a `false` tag. -/
theorem NB.strict_tags {m n : Nat} {s t : Bool} (h : StrictLt (NB.mk m s) (NB.mk n t)) :
    s = true ∧ t = false := by
  obtain ⟨h1, h2⟩ := h
  rcases (NB.le_iff m n s t).mp h1 with e | ⟨hs, ht, _⟩
  · exact absurd ((NB.le_iff n m t s).mpr (Or.inl e.symm)) h2
  · exact ⟨hs, ht⟩

theorem NB.heightLE : HeightLE NB 1 := by
  intro c k hc
  apply Classical.byContradiction
  intro hk
  have s0 := hc 0 (by omega)
  have s1 := hc 1 (by omega)
  cases h0 : c 0 with
  | mk m0 b0 =>
    cases h1 : c 1 with
    | mk m1 b1 =>
      cases h2 : c 2 with
      | mk m2 b2 =>
        rw [h0, h1] at s0
        rw [h1, h2] at s1
        have t0 := NB.strict_tags s0
        have t1 := NB.strict_tags s1
        rw [t0.2] at t1
        exact absurd t1.1 (by decide)

end Toy.AbsInt
