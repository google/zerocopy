/-!
# Rust Variance Inference Lattice, Higher-Ranked Subtyping (`enter_forall` / `leak_check`),
# and `zerocopy` `PtrInner` / `Ptr<'a, T, I>` Referent Invariance Soundness

Standalone Lean v4.34.1 mechanization (no Mathlib, no external packages, constructive
proofs only: 0 `sorry`, 0 `Classical.choice`, 0 `omega`, 0 `bv_decide`, 0 `native_decide`,
0 `partial def`, and 0 `._unsafe_rec` constants).

Primary-source targets modeled by this formalization:
1. `compiler/rustc_type_ir/src/lib.rs` (`Variance`, `Variance::xform`, `UniverseIndex`)
2. `compiler/rustc_hir_analysis/src/variance/{mod,terms,constraints,solve}.rs`
3. `compiler/rustc_infer/src/infer/relate/higher_ranked.rs` (`enter_forall`, `leak_check`)
4. `compiler/rustc_infer/src/infer/relate/type_relating.rs` (`TypeRelating::binders`)
5. `google/zerocopy` `zerocopy/src/pointer/{inner,ptr}.rs` and `tests/ui/ptr-is-invariant-over-v.rs`
-/

namespace RustcVarianceHrtbPtr

/-!
## Part 1: The Four-Point Variance Semi-Lattice and `xform` Algebra

Mirrors `rustc_type_ir::Variance` (`+`, `-`, `o`, `*`) and `solve::glb` as well as
the PLDI'11 "Taming the Wildcards" composition operator `xform`.
-/

/-- The four-element variance lattice ordered by subtyping permissiveness:
    `invariant ≤ {covariant, contravariant} ≤ bivariant`. -/
inductive Variance where
  | covariant
  | contravariant
  | invariant
  | bivariant

/-- Constructive boolean equality on `Variance` (avoiding `deriving DecidableEq`). -/
noncomputable def Variance.beq : Variance → Variance → Bool
  | .covariant, .covariant => true
  | .contravariant, .contravariant => true
  | .invariant, .invariant => true
  | .bivariant, .bivariant => true
  | _, _ => false

theorem Variance.beq_eq_true_iff (a b : Variance) : a.beq b = true ↔ a = b := by
  cases a <;> cases b <;> constructor <;> intro h
  · rfl
  · rfl
  · exact Bool.noConfusion h
  · exact Variance.noConfusion h
  · exact Bool.noConfusion h
  · exact Variance.noConfusion h
  · exact Bool.noConfusion h
  · exact Variance.noConfusion h
  · exact Bool.noConfusion h
  · exact Variance.noConfusion h
  · rfl
  · rfl
  · exact Bool.noConfusion h
  · exact Variance.noConfusion h
  · exact Bool.noConfusion h
  · exact Variance.noConfusion h
  · exact Bool.noConfusion h
  · exact Variance.noConfusion h
  · exact Bool.noConfusion h
  · exact Variance.noConfusion h
  · rfl
  · rfl
  · exact Bool.noConfusion h
  · exact Variance.noConfusion h
  · exact Bool.noConfusion h
  · exact Variance.noConfusion h
  · exact Bool.noConfusion h
  · exact Variance.noConfusion h
  · exact Bool.noConfusion h
  · exact Variance.noConfusion h
  · rfl
  · rfl

theorem Variance.eq_or_ne (a b : Variance) : a = b ∨ a ≠ b := by
  cases a <;> cases b
  · exact Or.inl rfl
  · exact Or.inr (fun h => Variance.noConfusion h)
  · exact Or.inr (fun h => Variance.noConfusion h)
  · exact Or.inr (fun h => Variance.noConfusion h)
  · exact Or.inr (fun h => Variance.noConfusion h)
  · exact Or.inl rfl
  · exact Or.inr (fun h => Variance.noConfusion h)
  · exact Or.inr (fun h => Variance.noConfusion h)
  · exact Or.inr (fun h => Variance.noConfusion h)
  · exact Or.inr (fun h => Variance.noConfusion h)
  · exact Or.inl rfl
  · exact Or.inr (fun h => Variance.noConfusion h)
  · exact Or.inr (fun h => Variance.noConfusion h)
  · exact Or.inr (fun h => Variance.noConfusion h)
  · exact Or.inr (fun h => Variance.noConfusion h)
  · exact Or.inl rfl

/-- Whether a variance demands the covariant (`A ≤ B`) subtyping direction. -/
noncomputable def Variance.needsFwd : Variance → Bool
  | .covariant => true
  | .invariant => true
  | .contravariant => false
  | .bivariant => false

/-- Whether a variance demands the contravariant (`B ≤ A`) subtyping direction. -/
noncomputable def Variance.needsBwd : Variance → Bool
  | .contravariant => true
  | .invariant => true
  | .covariant => false
  | .bivariant => false

/-- Inverse mapping from `(needsFwd, needsBwd)` polarity bits to `Variance`. -/
noncomputable def Variance.ofDirs : Bool → Bool → Variance
  | false, false => .bivariant
  | true, false => .covariant
  | false, true => .contravariant
  | true, true => .invariant

theorem Variance.ofDirs_needs (v : Variance) : Variance.ofDirs v.needsFwd v.needsBwd = v := by
  cases v <;> rfl

/-- Greatest lower bound matching `compiler/rustc_hir_analysis/src/variance/solve.rs:14-31`. -/
noncomputable def Variance.glb (v1 v2 : Variance) : Variance :=
  match v1, v2 with
  | .invariant, _ => .invariant
  | _, .invariant => .invariant
  | .covariant, .contravariant => .invariant
  | .contravariant, .covariant => .invariant
  | .covariant, .covariant => .covariant
  | .contravariant, .contravariant => .contravariant
  | x, .bivariant => x
  | .bivariant, x => x

/-- Least upper bound of the four-point variance lattice. -/
noncomputable def Variance.lub (v1 v2 : Variance) : Variance :=
  match v1, v2 with
  | .bivariant, _ => .bivariant
  | _, .bivariant => .bivariant
  | .covariant, .contravariant => .bivariant
  | .contravariant, .covariant => .bivariant
  | .covariant, .covariant => .covariant
  | .contravariant, .contravariant => .contravariant
  | x, .invariant => x
  | .invariant, x => x

/-- Subtyping permissiveness preorder `v ≤ w` (`v` is at least as restrictive as `w`):
    `invariant ≤ covariant ≤ bivariant` and `invariant ≤ contravariant ≤ bivariant`. -/
noncomputable def Variance.leBool (v w : Variance) : Bool :=
  (!w.needsFwd || v.needsFwd) && (!w.needsBwd || v.needsBwd)

noncomputable def Variance.le (v w : Variance) : Prop :=
  v.leBool w = true

/-- Chain potential (distance down from `bivariant` = 2 to `invariant` = 0). -/
noncomputable def Variance.potential : Variance → Nat
  | .bivariant => 2
  | .covariant => 1
  | .contravariant => 1
  | .invariant => 0

/-- Exact `rustc_type_ir::Variance::xform` from `compiler/rustc_type_ir/src/lib.rs:306-326`.
    Note the left-biased order between `invariant` and `bivariant`:
    `invariant.xform bivariant = invariant` whereas `bivariant.xform invariant = bivariant`. -/
noncomputable def Variance.xform (outer inner : Variance) : Variance :=
  match outer, inner with
  | .covariant, .covariant => .covariant
  | .covariant, .contravariant => .contravariant
  | .covariant, .invariant => .invariant
  | .covariant, .bivariant => .bivariant
  | .contravariant, .covariant => .contravariant
  | .contravariant, .contravariant => .covariant
  | .contravariant, .invariant => .invariant
  | .contravariant, .bivariant => .bivariant
  | .invariant, _ => .invariant
  | .bivariant, _ => .bivariant

/-- Symmetric PLDI'11 composition (where `bivariant` absorbs on both sides). -/
noncomputable def Variance.xformPldi11 (outer inner : Variance) : Variance :=
  match outer, inner with
  | .bivariant, _ => .bivariant
  | _, .bivariant => .bivariant
  | .invariant, _ => .invariant
  | _, .invariant => .invariant
  | .covariant, x => x
  | .contravariant, .covariant => .contravariant
  | .contravariant, .contravariant => .covariant

/-! ### 1.1 Lattice Order, GLB, and LUB Theorems -/

theorem Variance.le_refl (v : Variance) : v.le v := by
  cases v <;> rfl

theorem Variance.le_antisymm {a b : Variance} (hab : a.le b) (hba : b.le a) : a = b := by
  cases a <;> cases b <;> first | rfl | exact Bool.noConfusion hab | exact Bool.noConfusion hba

theorem Variance.le_trans {a b c : Variance} (hab : a.le b) (hbc : b.le c) : a.le c := by
  cases a <;> cases b <;> cases c <;>
    first | rfl | exact Bool.noConfusion hab | exact Bool.noConfusion hbc

theorem Variance.invariant_bottom (v : Variance) : Variance.invariant.le v := by
  cases v <;> rfl

theorem Variance.bivariant_top (v : Variance) : v.le Variance.bivariant := by
  cases v <;> rfl

theorem Variance.glb_comm (a b : Variance) : a.glb b = b.glb a := by
  cases a <;> cases b <;> rfl

theorem Variance.glb_assoc (a b c : Variance) : (a.glb b).glb c = a.glb (b.glb c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem Variance.glb_idem (a : Variance) : a.glb a = a := by
  cases a <;> rfl

theorem Variance.glb_le_left (a b : Variance) : (a.glb b).le a := by
  cases a <;> cases b <;> rfl

theorem Variance.glb_le_right (a b : Variance) : (a.glb b).le b := by
  cases a <;> cases b <;> rfl

theorem Variance.le_glb {x a b : Variance} (ha : x.le a) (hb : x.le b) : x.le (a.glb b) := by
  cases x <;> cases a <;> cases b <;>
    first | rfl | exact Bool.noConfusion ha | exact Bool.noConfusion hb

theorem Variance.le_iff_glb_eq (a b : Variance) : a.le b ↔ a.glb b = a := by
  cases a <;> cases b <;> constructor <;> intro h <;>
    first | rfl | exact Bool.noConfusion h | exact Variance.noConfusion h

theorem Variance.glb_bivariant_right (a : Variance) : a.glb .bivariant = a := by
  cases a <;> rfl

theorem Variance.glb_invariant_right (a : Variance) : a.glb .invariant = .invariant := by
  cases a <;> rfl

theorem Variance.lub_comm (a b : Variance) : a.lub b = b.lub a := by
  cases a <;> cases b <;> rfl

theorem Variance.lub_assoc (a b c : Variance) : (a.lub b).lub c = a.lub (b.lub c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem Variance.lub_idem (a : Variance) : a.lub a = a := by
  cases a <;> rfl

theorem Variance.le_lub_left (a b : Variance) : a.le (a.lub b) := by
  cases a <;> cases b <;> rfl

theorem Variance.le_lub_right (a b : Variance) : b.le (a.lub b) := by
  cases a <;> cases b <;> rfl

theorem Variance.lub_le {a b x : Variance} (ha : a.le x) (hb : b.le x) : (a.lub b).le x := by
  cases a <;> cases b <;> cases x <;>
    first | rfl | exact Bool.noConfusion ha | exact Bool.noConfusion hb

theorem Variance.glb_lub_absorb (a b : Variance) : a.glb (a.lub b) = a := by
  cases a <;> cases b <;> rfl

theorem Variance.lub_glb_absorb (a b : Variance) : a.lub (a.glb b) = a := by
  cases a <;> cases b <;> rfl

theorem Variance.distrib_glb_lub (a b c : Variance) :
    a.glb (b.lub c) = (a.glb b).lub (a.glb c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem Variance.distrib_lub_glb (a b c : Variance) :
    a.lub (b.glb c) = (a.lub b).glb (a.lub c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-! ### 1.2 Monoid, Monotonicity, Antitonicity, and PLDI'11 Discrepancy Theorems for `xform` -/

theorem Variance.xform_assoc (a b c : Variance) : (a.xform b).xform c = a.xform (b.xform c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem Variance.xform_id_left (v : Variance) : Variance.covariant.xform v = v := by
  cases v <;> rfl

theorem Variance.xform_id_right (v : Variance) : v.xform Variance.covariant = v := by
  cases v <;> rfl

theorem Variance.xform_inv_left (v : Variance) : Variance.invariant.xform v = Variance.invariant := by
  cases v <;> rfl

theorem Variance.xform_biv_left (v : Variance) : Variance.bivariant.xform v = Variance.bivariant := by
  cases v <;> rfl

theorem Variance.contravariant_xform_involutive (v : Variance) :
    Variance.contravariant.xform (Variance.contravariant.xform v) = v := by
  cases v <;> rfl

theorem Variance.xform_contravariant_flips_dirs (v : Variance) :
    (Variance.contravariant.xform v).needsFwd = v.needsBwd ∧
    (Variance.contravariant.xform v).needsBwd = v.needsFwd := by
  cases v <;> exact ⟨rfl, rfl⟩

/-- `rustc`'s `Variance::xform` is monotone in BOTH arguments with respect to `le`. -/
theorem Variance.xform_mono {a1 a2 b1 b2 : Variance} (ha : a1.le a2) (hb : b1.le b2) :
    (a1.xform b1).le (a2.xform b2) := by
  cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;>
    first | rfl | exact Bool.noConfusion ha | exact Bool.noConfusion hb

theorem Variance.xform_glb_dist_left (a b c : Variance) :
    a.xform (b.glb c) = (a.xform b).glb (a.xform c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem Variance.xform_glb_dist_right_le (a b c : Variance) :
    ((a.glb b).xform c).le ((a.xform c).glb (b.xform c)) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem Variance.xform_glb_dist_right_of_ne_bivariant (a b c : Variance) (hc : c ≠ .bivariant) :
    (a.glb b).xform c = (a.xform c).glb (b.xform c) := by
  cases a <;> cases b <;> cases c
  all_goals first | rfl | exact absurd rfl hc

theorem Variance.xform_glb_dist_right_fails_at_bivariant :
    (Variance.covariant.glb Variance.contravariant).xform Variance.bivariant = Variance.invariant ∧
    (Variance.covariant.xform Variance.bivariant).glb
      (Variance.contravariant.xform Variance.bivariant) = Variance.bivariant :=
  ⟨rfl, rfl⟩

/-- Exact discrepancy witness: `rustc_type_ir::Variance::xform` is NOT commutative
    on `(invariant, bivariant)` due to the arm order `(Invariant, _) => Invariant`
    preceding `(Bivariant, _) => Bivariant` in `rustc_type_ir/src/lib.rs:321-324`. -/
theorem Variance.xform_rustc_not_comm :
    Variance.invariant.xform Variance.bivariant = Variance.invariant ∧
    Variance.bivariant.xform Variance.invariant = Variance.bivariant ∧
    Variance.invariant.xform Variance.bivariant ≠ Variance.bivariant.xform Variance.invariant := by
  refine ⟨rfl, rfl, fun h => Variance.noConfusion h⟩

/-- On all pairs not mixing `invariant` and `bivariant`, `rustc` `xform` IS commutative. -/
theorem Variance.xform_comm_unless_inv_bi (a b : Variance)
    (h1 : ¬ (a = .invariant ∧ b = .bivariant))
    (h2 : ¬ (a = .bivariant ∧ b = .invariant)) :
    a.xform b = b.xform a := by
  cases a <;> cases b
  all_goals first
    | rfl
    | exact absurd ⟨rfl, rfl⟩ h1
    | exact absurd ⟨rfl, rfl⟩ h2

theorem Variance.xformPldi11_comm (a b : Variance) : a.xformPldi11 b = b.xformPldi11 a := by
  cases a <;> cases b <;> rfl

theorem Variance.xformPldi11_assoc (a b c : Variance) :
    (a.xformPldi11 b).xformPldi11 c = a.xformPldi11 (b.xformPldi11 c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- `rustc`'s `Variance::xform` is conservatively below PLDI'11's commutative `xform`. -/
theorem Variance.xform_rustc_le_pldi11 (a b : Variance) :
    (a.xform b).le (a.xformPldi11 b) := by
  cases a <;> cases b <;> rfl

theorem Variance.potential_strict_drop {a b : Variance} (hle : a.le b) (hne : a ≠ b) :
    a.potential < b.potential := by
  cases a <;> cases b
  · exact absurd rfl hne
  · exact Bool.noConfusion hle
  · exact Bool.noConfusion hle
  · exact Nat.lt_succ_self 1
  · exact Bool.noConfusion hle
  · exact absurd rfl hne
  · exact Bool.noConfusion hle
  · exact Nat.lt_succ_self 1
  · exact Nat.lt_succ_self 0
  · exact Nat.lt_succ_self 0
  · exact absurd rfl hne
  · exact Nat.lt_trans (Nat.lt_succ_self 0) (Nat.lt_succ_self 1)
  · exact Bool.noConfusion hle
  · exact Bool.noConfusion hle
  · exact Bool.noConfusion hle
  · exact absurd rfl hne

theorem Variance.potential_le_two (v : Variance) : v.potential ≤ 2 := by
  cases v
  · exact Nat.le_succ 1
  · exact Nat.le_succ 1
  · exact Nat.zero_le 2
  · exact Nat.le_refl 2

/-!
## Part 2: Finite Fixed-Point Constraint Solver (`solve_constraints`)

Mirrors `rustc_hir_analysis::variance::{terms.rs, constraints.rs, solve.rs}` over
an indexed crate of `N` inferred type/region parameters.
Proves:
- Monotonicity of `VarianceTerm` evaluation,
- Preservation of upper-solution bounds (every valid solution `s'` satisfies `s' ≤ state`),
- Potential bound `statePotential ≤ 2 * N` and strict drop on non-fixed-point passes,
- Finite termination in at most `2 * N` passes at an exact fixed point,
- Soundness (`Satisfies`) and Least-Solution Completeness (most permissive sound assignment),
- Concrete worked witnesses (`MutualA`/`MutualB`, even contravariant cycle, odd cycle,
  and `CovariantUnsafeCell` `overridden_inferreds` constraint filtering).
-/

/-- Terms generated by `ConstraintContext` (`rustc_hir_analysis/src/variance/terms.rs:25-29`). -/
inductive VarianceTerm (n : Nat) where
  | const (v : Variance)
  | xform (t1 t2 : VarianceTerm n)
  | inferred (idx : Fin n)

/-- A single variance constraint `inferred ≤ eval(term)` (`constraints.rs:25-28`). -/
structure VarianceConstraint (n : Nat) where
  target : Fin n
  term : VarianceTerm n

/-- Assignment mapping each inferred parameter index to its current `Variance`. -/
abbrev VarState (n : Nat) := Fin n → Variance

/-- Evaluate a `VarianceTerm` under `s` (`solve.rs:129-141`). -/
noncomputable def evalTerm {n : Nat} (s : VarState n) : VarianceTerm n → Variance
  | .const v => v
  | .xform t1 t2 => (evalTerm s t1).xform (evalTerm s t2)
  | .inferred idx => s idx

/-- Pointwise order on `VarState n`: `s₁ ≤ s₂` iff `∀ i, s₁ i ≤ s₂ i`. -/
noncomputable def stateLe {n : Nat} (s1 s2 : VarState n) : Prop :=
  ∀ i : Fin n, (s1 i).le (s2 i)

theorem stateLe_refl {n : Nat} (s : VarState n) : stateLe s s :=
  fun i => Variance.le_refl (s i)

theorem stateLe_trans {n : Nat} {s1 s2 s3 : VarState n}
    (h12 : stateLe s1 s2) (h23 : stateLe s2 s3) : stateLe s1 s3 :=
  fun i => Variance.le_trans (h12 i) (h23 i)

theorem evalTerm_mono {n : Nat} {s1 s2 : VarState n} (hle : stateLe s1 s2) :
    ∀ t : VarianceTerm n, (evalTerm s1 t).le (evalTerm s2 t)
  | .const v => Variance.le_refl v
  | .xform t1 t2 => Variance.xform_mono (evalTerm_mono hle t1) (evalTerm_mono hle t2)
  | .inferred idx => hle idx

/-- Initial top assignment: every parameter starts at `bivariant` (`solve.rs:44`). -/
noncomputable def topState (n : Nat) : VarState n :=
  fun _ => .bivariant

theorem le_topState {n : Nat} (s : VarState n) : stateLe s (topState n) :=
  fun i => Variance.bivariant_top (s i)

/-- Single-index update without `Classical.decEq`. -/
noncomputable def updateState {n : Nat} (s : VarState n) (k : Fin n) (v : Variance) : VarState n :=
  fun i => if Nat.beq i.val k.val then v else s i

theorem updateState_self {n : Nat} (s : VarState n) (k : Fin n) (v : Variance) :
    updateState s k v k = v := by
  unfold updateState
  have h : Nat.beq k.val k.val = true := Nat.beq_refl k.val
  rw [h]
  rfl

theorem updateState_other {n : Nat} (s : VarState n) {k i : Fin n} (hne : i.val ≠ k.val)
    (v : Variance) : updateState s k v i = s i := by
  unfold updateState
  cases h : Nat.beq i.val k.val with
  | false => rfl
  | true =>
    have heq : i.val = k.val := Nat.eq_of_beq_eq_true h
    exact absurd heq hne

/-- Apply one constraint via `glb(eval(term), old)` (`solve.rs:68-73`). -/
noncomputable def applyConstraint {n : Nat} (c : VarianceConstraint n) (s : VarState n) :
    VarState n :=
  updateState s c.target ((evalTerm s c.term).glb (s c.target))

/-- One full sweep over a constraint list (`solve.rs:67-86`). -/
noncomputable def solvePass {n : Nat} : List (VarianceConstraint n) → VarState n → VarState n
  | [], s => s
  | c :: cs, s => solvePass cs (applyConstraint c s)

/-- Fuel-bounded Kleene / Tarski fixed-point iteration (`solve.rs:63-87`). -/
noncomputable def solveLoop {n : Nat} (cs : List (VarianceConstraint n)) :
    Nat → VarState n → VarState n
  | 0, s => s
  | k + 1, s => solveLoop cs k (solvePass cs s)

/-- `Satisfies cs s` asserts that `s` obeys every constraint `s[target] ≤ eval(term)`. -/
noncomputable def Satisfies {n : Nat} (cs : List (VarianceConstraint n)) (s : VarState n) : Prop :=
  ∀ c, c ∈ cs → (s c.target).le (evalTerm s c.term)

/-- Sum of lattice potentials across all `n` parameters. -/
noncomputable def statePotential : (n : Nat) → VarState n → Nat
  | 0, _ => 0
  | n + 1, s =>
    (s ⟨n, Nat.lt_succ_self n⟩).potential +
      statePotential n (fun i => s ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)

theorem statePotential_le (n : Nat) (s : VarState n) : statePotential n s ≤ 2 * n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ m ih =>
    unfold statePotential
    have hp : (s ⟨m, Nat.lt_succ_self m⟩).potential ≤ 2 := Variance.potential_le_two _
    have hm := ih (fun i => s ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
    have hsum : (s ⟨m, Nat.lt_succ_self m⟩).potential +
        statePotential m (fun i => s ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) ≤ 2 + 2 * m :=
      Nat.add_le_add hp hm
    have h2 : 2 + 2 * m = 2 * (m + 1) := by
      rw [Nat.mul_succ, Nat.add_comm]
    exact Nat.le_trans hsum (Nat.le_of_eq h2)

theorem statePotential_mono :
    ∀ (n : Nat) (s1 s2 : VarState n), stateLe s1 s2 → statePotential n s1 ≤ statePotential n s2
  | 0, _, _, _ => Nat.le_refl 0
  | m + 1, s1, s2, hle => by
    unfold statePotential
    have hhead_le : (s1 ⟨m, Nat.lt_succ_self m⟩).le (s2 ⟨m, Nat.lt_succ_self m⟩) :=
      hle ⟨m, Nat.lt_succ_self m⟩
    have hhead : (s1 ⟨m, Nat.lt_succ_self m⟩).potential ≤
        (s2 ⟨m, Nat.lt_succ_self m⟩).potential := by
      cases Variance.eq_or_ne (s1 ⟨m, Nat.lt_succ_self m⟩) (s2 ⟨m, Nat.lt_succ_self m⟩) with
      | inl heq => rw [heq]; exact Nat.le_refl _
      | inr hne => exact Nat.le_of_lt (Variance.potential_strict_drop hhead_le hne)
    have htail : statePotential m (fun i => s1 ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) ≤
        statePotential m (fun i => s2 ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) :=
      statePotential_mono m _ _ (fun i => hle ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
    exact Nat.add_le_add hhead htail

theorem Nat.add_lt_add_of_lt_of_le {a b c d : Nat} (hab : a < b) (hcd : c ≤ d) :
    a + c < b + d :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_right hab c) (Nat.add_le_add_left hcd b)

theorem Nat.add_lt_add_of_le_of_lt {a b c d : Nat} (hab : a ≤ b) (hcd : c < d) :
    a + c < b + d :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_left hcd a) (Nat.add_le_add_right hab d)

theorem statePotential_strict_drop_at :
    ∀ (n : Nat) (s1 s2 : VarState n) (k : Fin n),
      stateLe s1 s2 → s1 k ≠ s2 k → statePotential n s1 < statePotential n s2
  | 0, _, _, k, _, _ => absurd k.isLt (Nat.not_lt_zero k.val)
  | m + 1, s1, s2, k, hle, hne => by
    unfold statePotential
    cases Nat.lt_or_ge k.val m with
    | inl hlt =>
      have hhead_le : (s1 ⟨m, Nat.lt_succ_self m⟩).le (s2 ⟨m, Nat.lt_succ_self m⟩) :=
        hle ⟨m, Nat.lt_succ_self m⟩
      have hhead : (s1 ⟨m, Nat.lt_succ_self m⟩).potential ≤
          (s2 ⟨m, Nat.lt_succ_self m⟩).potential := by
        cases Variance.eq_or_ne (s1 ⟨m, Nat.lt_succ_self m⟩) (s2 ⟨m, Nat.lt_succ_self m⟩) with
        | inl heq => rw [heq]; exact Nat.le_refl _
        | inr hneq => exact Nat.le_of_lt (Variance.potential_strict_drop hhead_le hneq)
      have htail : statePotential m (fun i => s1 ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) <
          statePotential m (fun i => s2 ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) :=
        statePotential_strict_drop_at m _ _ ⟨k.val, hlt⟩
          (fun i => hle ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) hne
      exact Nat.add_lt_add_of_le_of_lt hhead htail
    | inr hge =>
      have hm_lt : k.val < m + 1 := k.isLt
      have hkm : k.val = m := Nat.le_antisymm (Nat.le_of_lt_succ hm_lt) hge
      have hkeq : k = ⟨m, Nat.lt_succ_self m⟩ := Fin.ext hkm
      rw [hkeq] at hne
      have hhead : (s1 ⟨m, Nat.lt_succ_self m⟩).potential <
          (s2 ⟨m, Nat.lt_succ_self m⟩).potential :=
        Variance.potential_strict_drop (hle ⟨m, Nat.lt_succ_self m⟩) hne
      have htail : statePotential m (fun i => s1 ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) ≤
          statePotential m (fun i => s2 ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) :=
        statePotential_mono m _ _ (fun i => hle ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      exact Nat.add_lt_add_of_lt_of_le hhead htail

/-- Every `applyConstraint` monotonically decreases `s` in `stateLe`. -/
theorem applyConstraint_le {n : Nat} (c : VarianceConstraint n) (s : VarState n) :
    stateLe (applyConstraint c s) s := by
  intro i
  cases hbeq : Nat.beq i.val c.target.val with
  | true =>
    have heq : i.val = c.target.val := Nat.eq_of_beq_eq_true hbeq
    have hfi : i = c.target := Fin.ext heq
    rw [hfi]
    unfold applyConstraint
    rw [updateState_self]
    exact Variance.glb_le_right _ _
  | false =>
    have hne : i.val ≠ c.target.val := by
      intro heq
      have htrue : Nat.beq i.val c.target.val = true := heq ▸ Nat.beq_refl i.val
      rw [htrue] at hbeq
      exact Bool.noConfusion hbeq
    unfold applyConstraint
    rw [updateState_other _ hne]
    exact Variance.le_refl _

theorem solvePass_le {n : Nat} : ∀ (cs : List (VarianceConstraint n)) (s : VarState n),
    stateLe (solvePass cs s) s
  | [], s => stateLe_refl s
  | c :: cs, s =>
    stateLe_trans (solvePass_le cs (applyConstraint c s)) (applyConstraint_le c s)

theorem solveLoop_le {n : Nat} (cs : List (VarianceConstraint n)) :
    ∀ (k : Nat) (s : VarState n), stateLe (solveLoop cs k s) s
  | 0, s => stateLe_refl s
  | k + 1, s => stateLe_trans (solveLoop_le cs k (solvePass cs s)) (solvePass_le cs s)

/-- Any valid solution `s_sol` (`Satisfies cs s_sol`) stays below `applyConstraint c s`
    whenever it starts below `s`. -/
theorem applyConstraint_preserves_bound {n : Nat} (c : VarianceConstraint n)
    {s s_sol : VarState n} (hc : (s_sol c.target).le (evalTerm s_sol c.term))
    (hle : stateLe s_sol s) : stateLe s_sol (applyConstraint c s) := by
  intro i
  cases hbeq : Nat.beq i.val c.target.val with
  | true =>
    have heq : i.val = c.target.val := Nat.eq_of_beq_eq_true hbeq
    have hfi : i = c.target := Fin.ext heq
    rw [hfi]
    unfold applyConstraint
    rw [updateState_self]
    have heval : (evalTerm s_sol c.term).le (evalTerm s c.term) := evalTerm_mono hle c.term
    exact Variance.le_glb (Variance.le_trans hc heval) (hle c.target)
  | false =>
    have hne : i.val ≠ c.target.val := by
      intro heq
      have htrue : Nat.beq i.val c.target.val = true := heq ▸ Nat.beq_refl i.val
      rw [htrue] at hbeq
      exact Bool.noConfusion hbeq
    unfold applyConstraint
    rw [updateState_other _ hne]
    exact hle i

theorem solvePass_preserves_bound {n : Nat} :
    ∀ (cs : List (VarianceConstraint n)) {s s_sol : VarState n},
      Satisfies cs s_sol → stateLe s_sol s → stateLe s_sol (solvePass cs s)
  | [], _, _, _, hle => hle
  | c :: cs, s, s_sol, hsat, hle => by
    have hc : (s_sol c.target).le (evalTerm s_sol c.term) :=
      hsat c (List.Mem.head cs)
    have htail : Satisfies cs s_sol :=
      fun d hd => hsat d (List.Mem.tail c hd)
    exact solvePass_preserves_bound cs htail (applyConstraint_preserves_bound c hc hle)

theorem solveLoop_preserves_bound {n : Nat} (cs : List (VarianceConstraint n)) :
    ∀ (k : Nat) {s s_sol : VarState n},
      Satisfies cs s_sol → stateLe s_sol s → stateLe s_sol (solveLoop cs k s)
  | 0, _, _, _, hle => hle
  | k + 1, _, _, hsat, hle =>
    solveLoop_preserves_bound cs k hsat (solvePass_preserves_bound cs hsat hle)

/-- Every constraint processed in `solvePass` holds at the end of the pass whenever
    `solvePass cs s` equals `s` pointwise (`∀ i, solvePass cs s i = s i`). -/
theorem applyConstraint_id_of_solvePass_id {n : Nat} (c : VarianceConstraint n)
    (cs : List (VarianceConstraint n)) (s : VarState n)
    (hfix : ∀ i, solvePass (c :: cs) s i = s i) :
    ∀ i, applyConstraint c s i = s i := by
  intro i
  have h1 : (solvePass cs (applyConstraint c s) i).le (applyConstraint c s i) :=
    solvePass_le cs (applyConstraint c s) i
  have h2 : (applyConstraint c s i).le (s i) :=
    applyConstraint_le c s i
  have heq : solvePass cs (applyConstraint c s) i = s i := hfix i
  rw [heq] at h1
  exact Variance.le_antisymm h2 h1

theorem solvePass_tail_id_of_id {n : Nat} (c : VarianceConstraint n)
    (cs : List (VarianceConstraint n)) (s : VarState n)
    (hfix : ∀ i, solvePass (c :: cs) s i = s i) :
    ∀ i, solvePass cs s i = s i := by
  intro i
  have happ : applyConstraint c s = s := funext (applyConstraint_id_of_solvePass_id c cs s hfix)
  have h := hfix i
  unfold solvePass at h
  rw [happ] at h
  exact h

theorem fixed_point_satisfies {n : Nat} :
    ∀ (cs : List (VarianceConstraint n)) (s : VarState n),
      (∀ i, solvePass cs s i = s i) → Satisfies cs s
  | [], _, _ => fun _ hmem => nomatch hmem
  | c :: cs, s, hfix => by
    intro d hd
    cases hd with
    | head _ =>
      have happ := applyConstraint_id_of_solvePass_id c cs s hfix c.target
      unfold applyConstraint at happ
      rw [updateState_self] at happ
      have hcomm : (s c.target).glb (evalTerm s c.term) = s c.target := by
        rw [Variance.glb_comm]
        exact happ
      exact (Variance.le_iff_glb_eq (s c.target) (evalTerm s c.term)).mpr hcomm
    | tail _ hmem =>
      exact fixed_point_satisfies cs s (solvePass_tail_id_of_id c cs s hfix) d hmem

/-- Constructive finite-chain witness: if `solveLoop cs k s` strictly descends for every
    step up to `k`, its potential drops by at least `k`. -/
theorem solveLoop_chain_potential_drop {n : Nat} (cs : List (VarianceConstraint n)) :
    ∀ (k : Nat) (s : VarState n),
      (∀ j, j < k → ∃ i, solvePass cs (solveLoop cs j s) i ≠ solveLoop cs j s i) →
      statePotential n (solveLoop cs k s) + k ≤ statePotential n s
  | 0, s, _ => Nat.le_refl (statePotential n s)
  | m + 1, s, hall => by
    have ih_all : ∀ j, j < m → ∃ i, solvePass cs (solveLoop cs j (solvePass cs s)) i ≠
        solveLoop cs j (solvePass cs s) i := by
      intro j hj
      have hsucc := hall (j + 1) (Nat.succ_lt_succ hj)
      have hloop : ∀ r, solveLoop cs (r + 1) s = solveLoop cs r (solvePass cs s) :=
        fun _ => rfl
      rw [hloop j] at hsucc
      exact hsucc
    have ih := solveLoop_chain_potential_drop cs m (solvePass cs s) ih_all
    have h0 : ∃ i, solvePass cs s i ≠ s i := hall 0 (Nat.zero_lt_succ m)
    rcases h0 with ⟨i0, hi0⟩
    have hdrop : statePotential n (solvePass cs s) < statePotential n s :=
      statePotential_strict_drop_at n (solvePass cs s) s i0 (solvePass_le cs s) hi0
    have hstep1 : statePotential n (solveLoop cs m (solvePass cs s)) + (m + 1) ≤
        statePotential n (solvePass cs s) + 1 := by
      have hadd := Nat.add_le_add_right ih 1
      rw [Nat.add_assoc] at hadd
      exact hadd
    have hstep2 : statePotential n (solvePass cs s) + 1 ≤ statePotential n s := hdrop
    exact Nat.le_trans hstep1 hstep2

/-- Constructive search for a differing index between two `VarState n` assignments. -/
noncomputable def findDiffAux : (m : Nat) → (n : Nat) → (m ≤ n) →
    VarState n → VarState n → Option (Fin n)
  | 0, _, _, _, _ => none
  | k + 1, n, hle, s1, s2 =>
    if (s1 ⟨k, hle⟩).beq (s2 ⟨k, hle⟩) then
      findDiffAux k n (Nat.le_of_lt hle) s1 s2
    else
      some ⟨k, hle⟩

theorem findDiffAux_some {m n : Nat} {hle : m ≤ n} {s1 s2 : VarState n} {idx : Fin n}
    (hs : findDiffAux m n hle s1 s2 = some idx) : s1 idx ≠ s2 idx := by
  induction m with
  | zero => exact absurd hs (by intro h; cases h)
  | succ k ih =>
    unfold findDiffAux at hs
    cases hbeq : (s1 ⟨k, hle⟩).beq (s2 ⟨k, hle⟩) with
    | true =>
      simp only [hbeq] at hs
      exact ih hs
    | false =>
      simp only [hbeq] at hs
      cases hs
      intro heq
      have htrue : (s1 ⟨k, hle⟩).beq (s2 ⟨k, hle⟩) = true :=
        (Variance.beq_eq_true_iff _ _).mpr heq
      rw [htrue] at hbeq
      exact Bool.noConfusion hbeq

theorem findDiffAux_none {m n : Nat} {hle : m ≤ n} {s1 s2 : VarState n}
    (hn : findDiffAux m n hle s1 s2 = none) :
    ∀ i : Fin n, i.val < m → s1 i = s2 i := by
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero i.val)
  | succ k ih =>
    intro i hi
    unfold findDiffAux at hn
    cases hbeq : (s1 ⟨k, hle⟩).beq (s2 ⟨k, hle⟩) with
    | false =>
      simp only [hbeq] at hn
      exact absurd hn (by intro h; cases h)
    | true =>
      simp only [hbeq] at hn
      cases Nat.lt_or_ge i.val k with
      | inl hlt => exact ih hn i hlt
      | inr hge =>
        have hik : i.val = k := Nat.le_antisymm (Nat.le_of_lt_succ hi) hge
        have hfi : i = ⟨k, hle⟩ := Fin.ext hik
        rw [hfi]
        exact (Variance.beq_eq_true_iff _ _).mp hbeq

/-- Constructive witness: either `s1` and `s2` agree on all indices or an explicit
    differing index exists. -/
theorem stateEqOrDiff {n : Nat} (s1 s2 : VarState n) :
    (∀ i, s1 i = s2 i) ∨ (∃ i : Fin n, s1 i ≠ s2 i) :=
  match h : findDiffAux n n (Nat.le_refl n) s1 s2 with
  | none => Or.inl (fun i => findDiffAux_none h i i.isLt)
  | some idx => Or.inr ⟨idx, findDiffAux_some h⟩

/-- Fixed-point invariance: once `solvePass cs s` is a fixed point, `solveLoop` leaves
    it unchanged for all iteration counts. -/
theorem solveLoop_stable_of_fixed {n : Nat} (cs : List (VarianceConstraint n)) (s : VarState n)
    (hfix : ∀ i, solvePass cs s i = s i) :
    ∀ k i, solveLoop cs k s i = s i
  | 0, _ => rfl
  | k + 1, i => by
    have happ : solvePass cs s = s := funext hfix
    change solveLoop cs k (solvePass cs s) i = s i
    rw [happ]
    exact solveLoop_stable_of_fixed cs s hfix k i

/-- Constructive search for the first iteration `j < k` where `solveLoop cs j s` reaches
    a fixed point, or proof that every step `j < k` strictly changed. -/
theorem findFixedPoint {n : Nat} (cs : List (VarianceConstraint n)) :
    ∀ (k : Nat) (s : VarState n),
      (∃ j : Nat, j < k ∧ ∀ i, solvePass cs (solveLoop cs j s) i = solveLoop cs j s i) ∨
      (∀ j, j < k → ∃ i, solvePass cs (solveLoop cs j s) i ≠ solveLoop cs j s i)
  | 0, _ => Or.inr (fun _ hj => absurd hj (Nat.not_lt_zero _))
  | m + 1, s =>
    match stateEqOrDiff (solvePass cs s) s with
    | Or.inl hfix => Or.inl ⟨0, Nat.zero_lt_succ m, hfix⟩
    | Or.inr ⟨i0, hne0⟩ =>
      match findFixedPoint cs m (solvePass cs s) with
      | Or.inl ⟨j, hjlt, hjfix⟩ =>
        Or.inl ⟨j + 1, Nat.succ_lt_succ hjlt, hjfix⟩
      | Or.inr hall =>
        Or.inr (fun r hr =>
          match r with
          | 0 => ⟨i0, hne0⟩
          | q + 1 => hall q (Nat.lt_of_succ_lt_succ hr))

/-- Canonical `rustc` solver running `solveLoop` from `topState n` for `2 * n` passes. -/
noncomputable def solveConstraints {n : Nat} (cs : List (VarianceConstraint n)) : VarState n :=
  solveLoop cs (2 * n) (topState n)

/-- **Theorem 2a (Finite Fixed-Point Termination at `2 * N`):**
    From `topState n` (`Bivariant` everywhere), `solveLoop` reaches an exact fixed point
    within `2 * n` passes; thus `solveConstraints cs` is a true fixed point of `solvePass`. -/
theorem solveConstraints_is_fixed_point {n : Nat} (cs : List (VarianceConstraint n)) :
    ∀ i, solvePass cs (solveConstraints cs) i = solveConstraints cs i := by
  unfold solveConstraints
  match findFixedPoint cs (2 * n + 1) (topState n) with
  | Or.inl ⟨j, hjlt, hjfix⟩ =>
    have hj2n : j ≤ 2 * n := Nat.le_of_lt_succ hjlt
    have hdiff : ∃ d, j + d = 2 * n := ⟨2 * n - j, Nat.add_sub_cancel' hj2n⟩
    rcases hdiff with ⟨d, hd⟩
    intro i
    have hcomm : ∀ a b st, solveLoop cs (a + b) st = solveLoop cs b (solveLoop cs a st) := by
      intro a b st
      induction a generalizing st with
      | zero => rw [Nat.zero_add]; rfl
      | succ a' iha =>
        rw [Nat.succ_add]
        exact iha (solvePass cs st)
    rw [← hd]
    rw [hcomm j d (topState n)]
    have hstab := solveLoop_stable_of_fixed cs (solveLoop cs j (topState n)) hjfix d
    have hfun : solveLoop cs d (solveLoop cs j (topState n)) = solveLoop cs j (topState n) :=
      funext hstab
    rw [hfun]
    exact hjfix i
  | Or.inr hall =>
    have hdrop := solveLoop_chain_potential_drop cs (2 * n + 1) (topState n) hall
    have hpot := statePotential_le n (topState n)
    have hle : statePotential n (solveLoop cs (2 * n + 1) (topState n)) + (2 * n + 1) ≤ 2 * n :=
      Nat.le_trans hdrop hpot
    have hge : 2 * n + 1 ≤ statePotential n (solveLoop cs (2 * n + 1) (topState n)) + (2 * n + 1) :=
      Nat.le_add_left (2 * n + 1) _
    have hcontra : 2 * n + 1 ≤ 2 * n := Nat.le_trans hge hle
    exact absurd hcontra (Nat.not_succ_le_self (2 * n))

/-- **Theorem 2b (Soundness & Most-Permissive Solution Completeness):**
    `solveConstraints cs` satisfies every constraint in `cs`, AND every other satisfying
    assignment `s_sol` is bounded below it (`s_sol ≤ solveConstraints cs`). -/
theorem solveConstraints_sound_and_complete {n : Nat} (cs : List (VarianceConstraint n)) :
    Satisfies cs (solveConstraints cs) ∧
    (∀ s_sol : VarState n, Satisfies cs s_sol → stateLe s_sol (solveConstraints cs)) := by
  refine ⟨fixed_point_satisfies cs (solveConstraints cs) (solveConstraints_is_fixed_point cs), ?_⟩
  intro s_sol hsat
  exact solveLoop_preserves_bound cs (2 * n) hsat (le_topState s_sol)

/-! ### 2.3 Concrete Mutually Recursive ADT Systems & `CovariantUnsafeCell` Filtering -/

/-- Mutually recursive pair from probe `a_variance_dump_and_subtyping_matrix`:
    `struct MutualA<T>(*const MutualB<T>);`
    `struct MutualB<T>(*const MutualA<T>, PhantomData<fn(T)>);`
    Index `0` = `MutualA::T`, index `1` = `MutualB::T`. -/
noncomputable def mutualABConstraints : List (VarianceConstraint 2) :=
  [ { target := ⟨0, Nat.zero_lt_succ 1⟩
      term := .xform (.const .covariant) (.inferred ⟨1, Nat.lt_succ_self 1⟩) },
    { target := ⟨1, Nat.lt_succ_self 1⟩
      term := .xform (.const .covariant) (.inferred ⟨0, Nat.zero_lt_succ 1⟩) },
    { target := ⟨1, Nat.lt_succ_self 1⟩
      term := .const .contravariant } ]

theorem mutualAB_solves_contravariant :
    solveConstraints mutualABConstraints ⟨0, Nat.zero_lt_succ 1⟩ = .contravariant ∧
    solveConstraints mutualABConstraints ⟨1, Nat.lt_succ_self 1⟩ = .contravariant :=
  ⟨rfl, rfl⟩

/-- Even contravariant cycle:
    `struct MutualCycleInvA<T>(PhantomData<fn(MutualCycleInvB<T>)>);`
    `struct MutualCycleInvB<T>(PhantomData<fn(MutualCycleInvA<T>)>, *const T);`
    Demonstrates that a 2-cycle of contravariant edges preserves `[T: -]` on `A` and
    `[T: +]` on `B` rather than collapsing to `invariant`. -/
noncomputable def mutualCycleEvenConstraints : List (VarianceConstraint 2) :=
  [ { target := ⟨0, Nat.zero_lt_succ 1⟩
      term := .xform (.const .contravariant) (.inferred ⟨1, Nat.lt_succ_self 1⟩) },
    { target := ⟨1, Nat.lt_succ_self 1⟩
      term := .xform (.const .contravariant) (.inferred ⟨0, Nat.zero_lt_succ 1⟩) },
    { target := ⟨1, Nat.lt_succ_self 1⟩
      term := .const .covariant } ]

theorem mutualCycleEven_solves_contra_cov :
    solveConstraints mutualCycleEvenConstraints ⟨0, Nat.zero_lt_succ 1⟩ = .contravariant ∧
    solveConstraints mutualCycleEvenConstraints ⟨1, Nat.lt_succ_self 1⟩ = .covariant :=
  ⟨rfl, rfl⟩

/-- Odd contravariant cycle (`struct SelfCycleOddInv<T>(PhantomData<fn(SelfCycleOddInv<T>)>, *const T);`):
    1-cycle contravariance + covariant occurrence forces `glb(+ , - x o)` -> `invariant`. -/
noncomputable def selfCycleOddConstraints : List (VarianceConstraint 1) :=
  [ { target := ⟨0, Nat.zero_lt_succ 0⟩
      term := .xform (.const .contravariant) (.inferred ⟨0, Nat.zero_lt_succ 0⟩) },
    { target := ⟨0, Nat.zero_lt_succ 0⟩
      term := .const .covariant } ]

theorem selfCycleOdd_solves_invariant :
    solveConstraints selfCycleOddConstraints ⟨0, Nat.zero_lt_succ 0⟩ = .invariant :=
  rfl

/-- Models `rustc_hir_analysis::variance::solve::solve_constraints` lang-item override
    filtering (`overridden_inferreds` + `constraints.retain(...)` added alongside
    `CovariantUnsafeCell<T>(UnsafeCell<T>)`).
    Index `0` = `UnsafeCell::T` (hardcoded `invariant`),
    Index `1` = `CovariantUnsafeCell::T` (hardcoded `covariant`). -/
noncomputable def initWithLangOverrides {n : Nat}
    (overrides : List (Fin n × Variance)) : VarState n :=
  match overrides with
  | [] => topState n
  | (idx, v) :: rest => updateState (initWithLangOverrides rest) idx v

noncomputable def filterOverridden {n : Nat} (isOverridden : Fin n → Bool)
    (cs : List (VarianceConstraint n)) : List (VarianceConstraint n) :=
  cs.filter (fun c => !isOverridden c.target)

noncomputable def solveWithOverrides {n : Nat}
    (overrides : List (Fin n × Variance))
    (isOverridden : Fin n → Bool)
    (cs : List (VarianceConstraint n)) : VarState n :=
  solveLoop (filterOverridden isOverridden cs) (2 * n) (initWithLangOverrides overrides)

noncomputable def covariantUnsafeCellOverrides : List (Fin 2 × Variance) :=
  [ (⟨0, Nat.zero_lt_succ 1⟩, .invariant),
    (⟨1, Nat.lt_succ_self 1⟩, .covariant) ]

noncomputable def covariantUnsafeCellIsOverridden : Fin 2 → Bool
  | ⟨0, _⟩ => true
  | ⟨1, _⟩ => true

/-- Field constraints emitted by walking `UnsafeCell<T>(value: T)` and
    `CovariantUnsafeCell<T>(UnsafeCell<T>)`:
    - `UnsafeCell::T` receives `covariant`
    - `CovariantUnsafeCell::T` receives `UnsafeCell::T` (`invariant`)! -/
noncomputable def covariantUnsafeCellFieldConstraints : List (VarianceConstraint 2) :=
  [ { target := ⟨0, Nat.zero_lt_succ 1⟩, term := .const .covariant },
    { target := ⟨1, Nat.lt_succ_self 1⟩, term := .inferred ⟨0, Nat.zero_lt_succ 1⟩ } ]

/-- Without `constraints.retain(...)`, `CovariantUnsafeCell<T>`'s `UnsafeCell<T>` field
    clobbers the hardcoded `covariant` seed to `invariant`! -/
theorem covariantUnsafeCell_unfiltered_clobbers_to_invariant :
    solveLoop covariantUnsafeCellFieldConstraints 4
      (initWithLangOverrides covariantUnsafeCellOverrides)
      ⟨1, Nat.lt_succ_self 1⟩ = .invariant :=
  rfl

/-- With `filterOverridden` (matching `solve.rs:56-62` on `rust-lang/rust` trunk),
    `CovariantUnsafeCell<T>` preserves its overridden `covariant` variance while
    `UnsafeCell<T>` remains `invariant`. -/
theorem covariantUnsafeCell_filtered_preserves_covariant :
    solveWithOverrides covariantUnsafeCellOverrides covariantUnsafeCellIsOverridden
      covariantUnsafeCellFieldConstraints ⟨0, Nat.zero_lt_succ 1⟩ = .invariant ∧
    solveWithOverrides covariantUnsafeCellOverrides covariantUnsafeCellIsOverridden
      covariantUnsafeCellFieldConstraints ⟨1, Nat.lt_succ_self 1⟩ = .covariant :=
  ⟨rfl, rfl⟩

/-- Constraint system for `zerocopy::PtrInner<'a, T>` and `zerocopy::Ptr<'a, T, I>`:
    - `0`: `PtrInner::'a`
    - `1`: `PtrInner::T`
    - `2`: `Ptr::'a`
    - `3`: `Ptr::T`
    - `4`: `Ptr::I`
    Fields:
    - `PtrInner` has `ptr: NonNull<T>` (`covariant` on `T`) and
      `_marker: PhantomData<&'a UnsafeCell<T>>` (`covariant` on `'a`, `invariant` on `T`).
    - `Ptr` has `ptr: PtrInner<'a, T>` (`'a ↦ PtrInner::'a`, `T ↦ PtrInner::T`) and
      `_invariants: PhantomData<I>` (`covariant` on `I`). -/
noncomputable def zerocopyPtrConstraints : List (VarianceConstraint 5) :=
  let i0 : Fin 5 := ⟨0, Nat.zero_lt_succ 4⟩
  let i1 : Fin 5 := ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 3)⟩
  let i2 : Fin 5 := ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 2))⟩
  let i3 : Fin 5 := ⟨3, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 1)))⟩
  let i4 : Fin 5 := ⟨4, Nat.lt_succ_self 4⟩
  [ -- NonNull<T>
    { target := i1, term := .const .covariant },
    -- PhantomData<&'a UnsafeCell<T>>
    { target := i0, term := .const .covariant },
    { target := i1, term := .xform (.const .covariant) (.const .invariant) },
    -- Ptr::ptr : PtrInner<'a, T>
    { target := i2, term := .xform (.const .covariant) (.inferred i0) },
    { target := i3, term := .xform (.const .covariant) (.inferred i1) },
    -- Ptr::_invariants : PhantomData<I>
    { target := i4, term := .const .covariant } ]

theorem zerocopyPtr_derived_variances :
    solveConstraints zerocopyPtrConstraints ⟨0, Nat.zero_lt_succ 4⟩ = .covariant ∧
    solveConstraints zerocopyPtrConstraints ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 3)⟩ = .invariant ∧
    solveConstraints zerocopyPtrConstraints ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 2))⟩ = .covariant ∧
    solveConstraints zerocopyPtrConstraints ⟨3, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 1)))⟩ = .invariant ∧
    solveConstraints zerocopyPtrConstraints ⟨4, Nat.lt_succ_self 4⟩ = .covariant :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-!
## Part 3: Type Syntax, Lifetime/HRTB Subtyping (`enter_forall` / `leak_check`),
## Polarity Soundness, and Double-Contravariant HRTB Flip Theorem

Mirrors `compiler/rustc_infer/src/infer/relate/higher_ranked.rs` (`enter_forall`,
`leak_check`), `region_constraints/leak_check.rs`, and `type_relating.rs` (`binders`).
-/

/-- Region expressions including De Bruijn bound vars (`for<'a>`) and universe
    placeholders introduced by `enter_forall`. -/
inductive Region where
  | static
  | dur (t : Nat)
  | bvar (idx : Nat)
  | placeholder (u : Nat)

noncomputable def Region.beq : Region → Region → Bool
  | .static, .static => true
  | .dur t1, .dur t2 => Nat.beq t1 t2
  | .bvar k1, .bvar k2 => Nat.beq k1 k2
  | .placeholder u1, .placeholder u2 => Nat.beq u1 u2
  | _, _ => false

/-- Outlives relation `r1 : r2` (`r1` lives at least as long as `r2`).
    Models `leak_check` universe constraints:
    - `'static` outlives all regions (including fresh placeholders),
    - `dur t1` outlives `dur t2` iff `t2 ≤ t1`,
    - a placeholder `placeholder u` cannot outlive any `'static`, `dur`, or distinct placeholder! -/
noncomputable def Region.outlives : Region → Region → Prop
  | .static, _ => True
  | .dur t1, .dur t2 => t2 ≤ t1
  | .placeholder u1, .placeholder u2 => u1 = u2
  | .bvar k1, .bvar k2 => k1 = k2
  | _, _ => False

theorem Region.outlives_refl (r : Region) : r.outlives r := by
  cases r
  · exact trivial
  · exact Nat.le_refl _
  · rfl
  · rfl

theorem Region.outlives_trans {r1 r2 r3 : Region}
    (h12 : r1.outlives r2) (h23 : r2.outlives r3) : r1.outlives r3 := by
  cases r1 <;> cases r2 <;> cases r3
  all_goals first
    | exact trivial
    | exact False.elim h12
    | exact False.elim h23
    | exact Nat.le_trans h23 h12
    | exact Eq.trans h12 h23

theorem Region.placeholder_not_outlives_static (u : Nat) :
    ¬ (Region.placeholder u).outlives Region.static :=
  fun h => h

theorem Region.dur_not_outlives_static (t : Nat) :
    ¬ (Region.dur t).outlives Region.static :=
  fun h => h

theorem Region.dur_not_outlives_placeholder (t u : Nat) :
    ¬ (Region.dur t).outlives (Region.placeholder u) :=
  fun h => h

theorem Region.placeholder_ne_not_outlives {u1 u2 : Nat} (hne : u1 ≠ u2) :
    ¬ (Region.placeholder u1).outlives (Region.placeholder u2) :=
  fun h => hne h

/-- Substitute De Bruijn bound region variable `k` with `rep`. -/
noncomputable def Region.substBVar (k : Nat) (rep : Region) : Region → Region
  | .static => .static
  | .dur t => .dur t
  | .placeholder u => .placeholder u
  | .bvar j => if Nat.beq j k then rep else .bvar j

/-- Whether a region is free of De Bruijn bound indices `≥ depth` and uses placeholders `< univ`. -/
noncomputable def Region.wf (univ depth : Nat) : Region → Prop
  | .static => True
  | .dur _ => True
  | .bvar j => j < depth
  | .placeholder u => u < univ

/-- Aliasing mode tag for `zerocopy`'s `Ptr<'a, T, I>`. -/
inductive ZcAliasing where
  | shared
  | exclusive

/-- Rust type expressions modeled for variance, HRTB subtyping, and `zerocopy` `Ptr`. -/
inductive Ty where
  | u8
  | ref (r : Region) (inner : Ty)
  | mutRef (r : Region) (inner : Ty)
  | unsafeCell (inner : Ty)
  | rawConst (inner : Ty)
  | rawMut (inner : Ty)
  | phantom (inner : Ty)
  | pair (fst snd : Ty)
  | fnPtr (arg ret : Ty)
  | forallFn (arg ret : Ty)
  | zcPtrInner (r : Region) (inner : Ty)
  | zcPtr (r : Region) (inner : Ty) (aliasing : ZcAliasing)
  | zcPtrBadCov (r : Region) (inner : Ty) (aliasing : ZcAliasing)

/-- Substitute De Bruijn bound region variable `k` across a `Ty` (shifting at nested `forallFn`). -/
noncomputable def Ty.substRegion (k : Nat) (rep : Region) : Ty → Ty
  | .u8 => .u8
  | .ref r t => .ref (r.substBVar k rep) (t.substRegion k rep)
  | .mutRef r t => .mutRef (r.substBVar k rep) (t.substRegion k rep)
  | .unsafeCell t => .unsafeCell (t.substRegion k rep)
  | .rawConst t => .rawConst (t.substRegion k rep)
  | .rawMut t => .rawMut (t.substRegion k rep)
  | .phantom t => .phantom (t.substRegion k rep)
  | .pair a b => .pair (a.substRegion k rep) (b.substRegion k rep)
  | .fnPtr a b => .fnPtr (a.substRegion k rep) (b.substRegion k rep)
  | .forallFn a b => .forallFn (a.substRegion (k + 1) rep) (b.substRegion (k + 1) rep)
  | .zcPtrInner r t => .zcPtrInner (r.substBVar k rep) (t.substRegion k rep)
  | .zcPtr r t al => .zcPtr (r.substBVar k rep) (t.substRegion k rep) al
  | .zcPtrBadCov r t al => .zcPtrBadCov (r.substBVar k rep) (t.substRegion k rep) al

/-- Well-formedness of `Ty` in universe `univ` at binder depth `depth`. -/
noncomputable def Ty.wf (univ depth : Nat) : Ty → Prop
  | .u8 => True
  | .ref r t => r.wf univ depth ∧ t.wf univ depth
  | .mutRef r t => r.wf univ depth ∧ t.wf univ depth
  | .unsafeCell t => t.wf univ depth
  | .rawConst t => t.wf univ depth
  | .rawMut t => t.wf univ depth
  | .phantom t => t.wf univ depth
  | .pair a b => a.wf univ depth ∧ b.wf univ depth
  | .fnPtr a b => a.wf univ depth ∧ b.wf univ depth
  | .forallFn a b => a.wf univ (depth + 1) ∧ b.wf univ (depth + 1)
  | .zcPtrInner r t => r.wf univ depth ∧ t.wf univ depth
  | .zcPtr r t _ => r.wf univ depth ∧ t.wf univ depth
  | .zcPtrBadCov r t _ => r.wf univ depth ∧ t.wf univ depth

/-- Subtyping judgment `SubTy univ t1 t2` (`t1 <: t2` in universe `univ`).
    Mirrors `TypeRelating` (`type_relating.rs`), `enter_forall` (`higher_ranked.rs`),
    and `zerocopy`'s `PtrInner`/`Ptr` variance (`['a: +, T: o, I: +]`). -/
inductive SubTy : Nat → Ty → Ty → Prop where
  | u8 {u : Nat} : SubTy u .u8 .u8
  | ref {u : Nat} {r1 r2 : Region} {t1 t2 : Ty} :
      r1.outlives r2 → SubTy u t1 t2 → SubTy u (.ref r1 t1) (.ref r2 t2)
  | mutRef {u : Nat} {r1 r2 : Region} {t1 t2 : Ty} :
      r1.outlives r2 → SubTy u t1 t2 → SubTy u t2 t1 → SubTy u (.mutRef r1 t1) (.mutRef r2 t2)
  | unsafeCell {u : Nat} {t1 t2 : Ty} :
      SubTy u t1 t2 → SubTy u t2 t1 → SubTy u (.unsafeCell t1) (.unsafeCell t2)
  | rawConst {u : Nat} {t1 t2 : Ty} :
      SubTy u t1 t2 → SubTy u (.rawConst t1) (.rawConst t2)
  | rawMut {u : Nat} {t1 t2 : Ty} :
      SubTy u t1 t2 → SubTy u t2 t1 → SubTy u (.rawMut t1) (.rawMut t2)
  | phantom {u : Nat} {t1 t2 : Ty} :
      SubTy u t1 t2 → SubTy u (.phantom t1) (.phantom t2)
  | pair {u : Nat} {a1 a2 b1 b2 : Ty} :
      SubTy u a1 a2 → SubTy u b1 b2 → SubTy u (.pair a1 b1) (.pair a2 b2)
  | fnPtr {u : Nat} {a1 a2 r1 r2 : Ty} :
      SubTy u a2 a1 → SubTy u r1 r2 → SubTy u (.fnPtr a1 r1) (.fnPtr a2 r2)
  | forallLeft {u : Nat} {a1 r1 t2 : Ty} (rep : Region) :
      rep.wf u 0 →
      SubTy u (.fnPtr (a1.substRegion 0 rep) (r1.substRegion 0 rep)) t2 →
      SubTy u (.forallFn a1 r1) t2
  | forallRight {u : Nat} {t1 a2 r2 : Ty} :
      SubTy (u + 1) t1 (.fnPtr (a2.substRegion 0 (.placeholder u)) (r2.substRegion 0 (.placeholder u))) →
      SubTy u t1 (.forallFn a2 r2)
  | zcPtrInner {u : Nat} {r1 r2 : Region} {t1 t2 : Ty} :
      r1.outlives r2 → SubTy u t1 t2 → SubTy u t2 t1 → SubTy u (.zcPtrInner r1 t1) (.zcPtrInner r2 t2)
  | zcPtr {u : Nat} {r1 r2 : Region} {t1 t2 : Ty} {al : ZcAliasing} :
      r1.outlives r2 → SubTy u t1 t2 → SubTy u t2 t1 → SubTy u (.zcPtr r1 t1 al) (.zcPtr r2 t2 al)
  | zcPtrBadCov {u : Nat} {r1 r2 : Region} {t1 t2 : Ty} {al : ZcAliasing} :
      r1.outlives r2 → SubTy u t1 t2 → SubTy u (.zcPtrBadCov r1 t1 al) (.zcPtrBadCov r2 t2 al)

noncomputable def Ty.noForall : Ty → Prop
  | .u8 => True
  | .ref _ t => t.noForall
  | .mutRef _ t => t.noForall
  | .unsafeCell t => t.noForall
  | .rawConst t => t.noForall
  | .rawMut t => t.noForall
  | .phantom t => t.noForall
  | .pair a b => a.noForall ∧ b.noForall
  | .fnPtr a b => a.noForall ∧ b.noForall
  | .forallFn _ _ => False
  | .zcPtrInner _ t => t.noForall
  | .zcPtr _ t _ => t.noForall
  | .zcPtrBadCov _ t _ => t.noForall

theorem SubTy.refl_basic : ∀ (u : Nat) (t : Ty), t.noForall → SubTy u t t
  | _, .u8, _ => SubTy.u8
  | u, .ref r t, h => SubTy.ref (Region.outlives_refl r) (SubTy.refl_basic u t h)
  | _, .forallFn _ _, h => False.elim h
  | u, .mutRef r t, h =>
    let ih := SubTy.refl_basic u t h
    SubTy.mutRef (Region.outlives_refl r) ih ih
  | u, .unsafeCell t, h =>
    let ih := SubTy.refl_basic u t h
    SubTy.unsafeCell ih ih
  | u, .rawConst t, h => SubTy.rawConst (SubTy.refl_basic u t h)
  | u, .rawMut t, h =>
    let ih := SubTy.refl_basic u t h
    SubTy.rawMut ih ih
  | u, .phantom t, h => SubTy.phantom (SubTy.refl_basic u t h)
  | u, .pair a b, h =>
    SubTy.pair (SubTy.refl_basic u a h.1) (SubTy.refl_basic u b h.2)
  | u, .fnPtr a b, h =>
    SubTy.fnPtr (SubTy.refl_basic u a h.1) (SubTy.refl_basic u b h.2)
  | u, .zcPtrInner r t, h =>
    let ih := SubTy.refl_basic u t h
    SubTy.zcPtrInner (Region.outlives_refl r) ih ih
  | u, .zcPtr r t _, h =>
    let ih := SubTy.refl_basic u t h
    SubTy.zcPtr (Region.outlives_refl r) ih ih
  | u, .zcPtrBadCov r t _, h =>
    SubTy.zcPtrBadCov (Region.outlives_refl r) (SubTy.refl_basic u t h)

/-- Polarity-indexed relation on types matching `Variance.Rel`. -/
noncomputable def RelTy (u : Nat) (v : Variance) (a b : Ty) : Prop :=
  (v.needsFwd = true → SubTy u a b) ∧ (v.needsBwd = true → SubTy u b a)

theorem RelTy.covariant_iff (u : Nat) (a b : Ty) : RelTy u .covariant a b ↔ SubTy u a b := by
  constructor
  · intro h; exact h.1 rfl
  · intro h; exact ⟨fun _ => h, fun hfalse => Bool.noConfusion hfalse⟩

theorem RelTy.contravariant_iff (u : Nat) (a b : Ty) : RelTy u .contravariant a b ↔ SubTy u b a := by
  constructor
  · intro h; exact h.2 rfl
  · intro h; exact ⟨fun hfalse => Bool.noConfusion hfalse, fun _ => h⟩

theorem RelTy.invariant_iff (u : Nat) (a b : Ty) :
    RelTy u .invariant a b ↔ SubTy u a b ∧ SubTy u b a := by
  constructor
  · intro h; exact ⟨h.1 rfl, h.2 rfl⟩
  · intro h; exact ⟨fun _ => h.1, fun _ => h.2⟩

theorem RelTy.flip_contravariant (u : Nat) (v : Variance) (a b : Ty) :
    RelTy u (Variance.contravariant.xform v) a b ↔ RelTy u v b a := by
  cases v <;> constructor <;> intro h
  · exact ⟨fun _ => h.2 rfl, fun hf => Bool.noConfusion hf⟩
  · exact ⟨fun hf => Bool.noConfusion hf, fun _ => h.1 rfl⟩
  · exact ⟨fun hf => Bool.noConfusion hf, fun _ => h.1 rfl⟩
  · exact ⟨fun _ => h.2 rfl, fun hf => Bool.noConfusion hf⟩
  · exact ⟨fun _ => h.2 rfl, fun _ => h.1 rfl⟩
  · exact ⟨fun _ => h.2 rfl, fun _ => h.1 rfl⟩
  · exact ⟨fun hf => Bool.noConfusion hf, fun hf => Bool.noConfusion hf⟩
  · exact ⟨fun hf => Bool.noConfusion hf, fun hf => Bool.noConfusion hf⟩

theorem RelTy.mono_of_le {u : Nat} {v w : Variance} {a b : Ty}
    (hle : v.le w) (h : RelTy u v a b) : RelTy u w a b := by
  cases v <;> cases w
  all_goals first
    | exact h
    | exact Bool.noConfusion hle
    | exact ⟨fun _ => h.1 rfl, fun hf => Bool.noConfusion hf⟩
    | exact ⟨fun hf => Bool.noConfusion hf, fun _ => h.2 rfl⟩
    | exact ⟨fun hf => Bool.noConfusion hf, fun hf => Bool.noConfusion hf⟩

/-- One-hole syntactic type contexts for proving general polarity soundness. -/
inductive TyCtx where
  | hole
  | refTy (r : Region) (c : TyCtx)
  | mutRefTy (r : Region) (c : TyCtx)
  | unsafeCell (c : TyCtx)
  | rawConst (c : TyCtx)
  | rawMut (c : TyCtx)
  | phantom (c : TyCtx)
  | pairL (c : TyCtx) (snd : Ty)
  | pairR (fst : Ty) (c : TyCtx)
  | fnArg (c : TyCtx) (ret : Ty)
  | fnRet (arg : Ty) (c : TyCtx)
  | zcPtrInnerTy (r : Region) (c : TyCtx)
  | zcPtrTy (r : Region) (c : TyCtx) (al : ZcAliasing)

noncomputable def TyCtx.plug : TyCtx → Ty → Ty
  | .hole, t => t
  | .refTy r c, t => .ref r (c.plug t)
  | .mutRefTy r c, t => .mutRef r (c.plug t)
  | .unsafeCell c, t => .unsafeCell (c.plug t)
  | .rawConst c, t => .rawConst (c.plug t)
  | .rawMut c, t => .rawMut (c.plug t)
  | .phantom c, t => .phantom (c.plug t)
  | .pairL c snd, t => .pair (c.plug t) snd
  | .pairR fst c, t => .pair fst (c.plug t)
  | .fnArg c ret, t => .fnPtr (c.plug t) ret
  | .fnRet arg c, t => .fnPtr arg (c.plug t)
  | .zcPtrInnerTy r c, t => .zcPtrInner r (c.plug t)
  | .zcPtrTy r c al, t => .zcPtr r (c.plug t) al

/-- Compositional variance of the hole inside `c` (exact `rustc` `xform` folding). -/
noncomputable def TyCtx.variance : TyCtx → Variance
  | .hole => .covariant
  | .refTy _ c => Variance.covariant.xform c.variance
  | .mutRefTy _ c => Variance.invariant.xform c.variance
  | .unsafeCell c => Variance.invariant.xform c.variance
  | .rawConst c => Variance.covariant.xform c.variance
  | .rawMut c => Variance.invariant.xform c.variance
  | .phantom c => Variance.covariant.xform c.variance
  | .pairL c _ => Variance.covariant.xform c.variance
  | .pairR _ c => Variance.covariant.xform c.variance
  | .fnArg c _ => Variance.contravariant.xform c.variance
  | .fnRet _ c => Variance.covariant.xform c.variance
  | .zcPtrInnerTy _ c => Variance.invariant.xform c.variance
  | .zcPtrTy _ c _ => Variance.invariant.xform c.variance

/-- Sibling types stored inside `TyCtx` (used to guarantee sibling reflexivity without `forallFn`). -/
noncomputable def TyCtx.siblingsRefl (u : Nat) : TyCtx → Prop
  | .hole => True
  | .refTy _ c => c.siblingsRefl u
  | .mutRefTy _ c => c.siblingsRefl u
  | .unsafeCell c => c.siblingsRefl u
  | .rawConst c => c.siblingsRefl u
  | .rawMut c => c.siblingsRefl u
  | .phantom c => c.siblingsRefl u
  | .pairL c snd => c.siblingsRefl u ∧ SubTy u snd snd
  | .pairR fst c => SubTy u fst fst ∧ c.siblingsRefl u
  | .fnArg c ret => c.siblingsRefl u ∧ SubTy u ret ret
  | .fnRet arg c => SubTy u arg arg ∧ c.siblingsRefl u
  | .zcPtrInnerTy _ c => c.siblingsRefl u
  | .zcPtrTy _ c _ => c.siblingsRefl u

theorem RelTy.xform_compose {u : Nat} (outer inner : Variance) (a b : Ty)
    (h : RelTy u (outer.xform inner) a b) :
    (outer = .covariant → RelTy u inner a b) ∧
    (outer = .contravariant → RelTy u inner b a) ∧
    (outer = .invariant → RelTy u inner a b ∧ RelTy u inner b a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ho; subst ho; rw [Variance.xform_id_left] at h; exact h
  · intro ho; subst ho; exact (RelTy.flip_contravariant u inner a b).mp h
  · intro ho; subst ho
    rw [Variance.xform_inv_left] at h
    have hi := (RelTy.invariant_iff u a b).mp h
    exact ⟨RelTy.mono_of_le (Variance.invariant_bottom inner) ((RelTy.invariant_iff u a b).mpr hi),
           RelTy.mono_of_le (Variance.invariant_bottom inner) ((RelTy.invariant_iff u b a).mpr ⟨hi.2, hi.1⟩)⟩

/-- **Theorem 3a (General Subtyping Polarity Soundness):**
    For ANY type context `c : TyCtx` with well-behaved siblings, relating `a` and `b`
    according to `c.variance` (`RelTy u c.variance a b`) produces `SubTy u (c.plug a) (c.plug b)`.
    Even stronger: `RelTy u v c_var` preserves both `SubTy u (c.plug a) (c.plug b)`
    and its symmetric partner when `c.variance = .invariant`. -/
theorem ctx_polarity_sound_both (u : Nat) (c : TyCtx) (a b : Ty)
    (hsib : c.siblingsRefl u) (hrel : RelTy u c.variance a b) :
    SubTy u (c.plug a) (c.plug b) ∧ (c.variance = .invariant → SubTy u (c.plug b) (c.plug a)) := by
  induction c generalizing a b with
  | hole =>
    have hsub : SubTy u a b := (RelTy.covariant_iff u a b).mp hrel
    exact ⟨hsub, fun hc => Variance.noConfusion hc⟩
  | refTy r c ih =>
    have hrel' : RelTy u c.variance a b := by
      unfold TyCtx.variance at hrel; rw [Variance.xform_id_left] at hrel; exact hrel
    have hres := ih a b hsib hrel'
    refine ⟨SubTy.ref (Region.outlives_refl r) hres.1, fun hinv => ?_⟩
    unfold TyCtx.variance at hinv; rw [Variance.xform_id_left] at hinv
    exact SubTy.ref (Region.outlives_refl r) (hres.2 hinv)
  | mutRefTy r c ih =>
    have hinv_a_b : SubTy u a b ∧ SubTy u b a := by
      unfold TyCtx.variance at hrel; rw [Variance.xform_inv_left] at hrel
      exact (RelTy.invariant_iff u a b).mp hrel
    have hrel_ab : RelTy u c.variance a b :=
      RelTy.mono_of_le (Variance.invariant_bottom c.variance)
        ((RelTy.invariant_iff u a b).mpr hinv_a_b)
    have hrel_ba : RelTy u c.variance b a :=
      RelTy.mono_of_le (Variance.invariant_bottom c.variance)
        ((RelTy.invariant_iff u b a).mpr ⟨hinv_a_b.2, hinv_a_b.1⟩)
    have h1 := (ih a b hsib hrel_ab).1
    have h2 := (ih b a hsib hrel_ba).1
    exact ⟨SubTy.mutRef (Region.outlives_refl r) h1 h2,
           fun _ => SubTy.mutRef (Region.outlives_refl r) h2 h1⟩
  | unsafeCell c ih =>
    have hinv_a_b : SubTy u a b ∧ SubTy u b a := by
      unfold TyCtx.variance at hrel; rw [Variance.xform_inv_left] at hrel
      exact (RelTy.invariant_iff u a b).mp hrel
    have hrel_ab := RelTy.mono_of_le (Variance.invariant_bottom c.variance)
      ((RelTy.invariant_iff u a b).mpr hinv_a_b)
    have hrel_ba := RelTy.mono_of_le (Variance.invariant_bottom c.variance)
      ((RelTy.invariant_iff u b a).mpr ⟨hinv_a_b.2, hinv_a_b.1⟩)
    have h1 := (ih a b hsib hrel_ab).1
    have h2 := (ih b a hsib hrel_ba).1
    exact ⟨SubTy.unsafeCell h1 h2, fun _ => SubTy.unsafeCell h2 h1⟩
  | rawConst c ih =>
    have hrel' : RelTy u c.variance a b := by
      unfold TyCtx.variance at hrel; rw [Variance.xform_id_left] at hrel; exact hrel
    have hres := ih a b hsib hrel'
    refine ⟨SubTy.rawConst hres.1, fun hinv => ?_⟩
    unfold TyCtx.variance at hinv; rw [Variance.xform_id_left] at hinv
    exact SubTy.rawConst (hres.2 hinv)
  | rawMut c ih =>
    have hinv_a_b : SubTy u a b ∧ SubTy u b a := by
      unfold TyCtx.variance at hrel; rw [Variance.xform_inv_left] at hrel
      exact (RelTy.invariant_iff u a b).mp hrel
    have hrel_ab := RelTy.mono_of_le (Variance.invariant_bottom c.variance)
      ((RelTy.invariant_iff u a b).mpr hinv_a_b)
    have hrel_ba := RelTy.mono_of_le (Variance.invariant_bottom c.variance)
      ((RelTy.invariant_iff u b a).mpr ⟨hinv_a_b.2, hinv_a_b.1⟩)
    have h1 := (ih a b hsib hrel_ab).1
    have h2 := (ih b a hsib hrel_ba).1
    exact ⟨SubTy.rawMut h1 h2, fun _ => SubTy.rawMut h2 h1⟩
  | phantom c ih =>
    have hrel' : RelTy u c.variance a b := by
      unfold TyCtx.variance at hrel; rw [Variance.xform_id_left] at hrel; exact hrel
    have hres := ih a b hsib hrel'
    refine ⟨SubTy.phantom hres.1, fun hinv => ?_⟩
    unfold TyCtx.variance at hinv; rw [Variance.xform_id_left] at hinv
    exact SubTy.phantom (hres.2 hinv)
  | pairL c snd ih =>
    have hrel' : RelTy u c.variance a b := by
      unfold TyCtx.variance at hrel; rw [Variance.xform_id_left] at hrel; exact hrel
    have hres := ih a b hsib.1 hrel'
    refine ⟨SubTy.pair hres.1 hsib.2, fun hinv => ?_⟩
    unfold TyCtx.variance at hinv; rw [Variance.xform_id_left] at hinv
    exact SubTy.pair (hres.2 hinv) hsib.2
  | pairR fst c ih =>
    have hrel' : RelTy u c.variance a b := by
      unfold TyCtx.variance at hrel; rw [Variance.xform_id_left] at hrel; exact hrel
    have hres := ih a b hsib.2 hrel'
    refine ⟨SubTy.pair hsib.1 hres.1, fun hinv => ?_⟩
    unfold TyCtx.variance at hinv; rw [Variance.xform_id_left] at hinv
    exact SubTy.pair hsib.1 (hres.2 hinv)
  | fnArg c ret ih =>
    have hrel' : RelTy u c.variance b a := by
      unfold TyCtx.variance at hrel
      exact (RelTy.flip_contravariant u c.variance a b).mp hrel
    have hres := ih b a hsib.1 hrel'
    refine ⟨SubTy.fnPtr hres.1 hsib.2, fun hinv => ?_⟩
    unfold TyCtx.variance at hinv
    have hinv' : c.variance = .invariant := by
      cases hc : c.variance <;> rw [hc] at hinv <;> first | rfl | exact Variance.noConfusion hinv
    exact SubTy.fnPtr (hres.2 hinv') hsib.2
  | fnRet arg c ih =>
    have hrel' : RelTy u c.variance a b := by
      unfold TyCtx.variance at hrel; rw [Variance.xform_id_left] at hrel; exact hrel
    have hres := ih a b hsib.2 hrel'
    refine ⟨SubTy.fnPtr hsib.1 hres.1, fun hinv => ?_⟩
    unfold TyCtx.variance at hinv; rw [Variance.xform_id_left] at hinv
    exact SubTy.fnPtr hsib.1 (hres.2 hinv)
  | zcPtrInnerTy r c ih =>
    have hinv_a_b : SubTy u a b ∧ SubTy u b a := by
      unfold TyCtx.variance at hrel; rw [Variance.xform_inv_left] at hrel
      exact (RelTy.invariant_iff u a b).mp hrel
    have hrel_ab := RelTy.mono_of_le (Variance.invariant_bottom c.variance)
      ((RelTy.invariant_iff u a b).mpr hinv_a_b)
    have hrel_ba := RelTy.mono_of_le (Variance.invariant_bottom c.variance)
      ((RelTy.invariant_iff u b a).mpr ⟨hinv_a_b.2, hinv_a_b.1⟩)
    have h1 := (ih a b hsib hrel_ab).1
    have h2 := (ih b a hsib hrel_ba).1
    exact ⟨SubTy.zcPtrInner (Region.outlives_refl r) h1 h2,
           fun _ => SubTy.zcPtrInner (Region.outlives_refl r) h2 h1⟩
  | zcPtrTy r c al ih =>
    have hinv_a_b : SubTy u a b ∧ SubTy u b a := by
      unfold TyCtx.variance at hrel; rw [Variance.xform_inv_left] at hrel
      exact (RelTy.invariant_iff u a b).mp hrel
    have hrel_ab := RelTy.mono_of_le (Variance.invariant_bottom c.variance)
      ((RelTy.invariant_iff u a b).mpr hinv_a_b)
    have hrel_ba := RelTy.mono_of_le (Variance.invariant_bottom c.variance)
      ((RelTy.invariant_iff u b a).mpr ⟨hinv_a_b.2, hinv_a_b.1⟩)
    have h1 := (ih a b hsib hrel_ab).1
    have h2 := (ih b a hsib hrel_ba).1
    exact ⟨SubTy.zcPtr (Region.outlives_refl r) h1 h2,
           fun _ => SubTy.zcPtr (Region.outlives_refl r) h2 h1⟩

theorem ctx_polarity_sound (u : Nat) (c : TyCtx) (a b : Ty)
    (hsib : c.siblingsRefl u) (hrel : RelTy u c.variance a b) :
    SubTy u (c.plug a) (c.plug b) :=
  (ctx_polarity_sound_both u c a b hsib hrel).1

/-! ### 3.1 HRTB Subtyping, Double-Contravariant Flip, and Universe Leak-Check Rejections -/

/-- The concrete higher-ranked function type `for<'a> fn(&'a u8) -> u8`. -/
noncomputable def tyHrtbFn : Ty :=
  .forallFn (.ref (.bvar 0) .u8) .u8

/-- The concrete static-argument function type `fn(&'static u8) -> u8`. -/
noncomputable def tyStaticFn : Ty :=
  .fnPtr (.ref .static .u8) .u8

/-- **Theorem 3b (HRTB Instantiation Soundness):**
    `for<'a> fn(&'a u8) -> u8 <: fn(&'static u8) -> u8`. -/
theorem hrtb_to_static_sound : SubTy 0 tyHrtbFn tyStaticFn := by
  unfold tyHrtbFn tyStaticFn
  apply SubTy.forallLeft .static trivial
  exact SubTy.fnPtr (SubTy.ref (Region.outlives_refl .static) SubTy.u8) SubTy.u8

/-- **Theorem 3c (Negative HRTB Leak-Check Rejection):**
    `¬ (fn(&'static u8) -> u8 <: for<'a> fn(&'a u8) -> u8)`.
    Models `enter_forall` creating placeholder `Region.placeholder 0` in universe `U1`
    plus contravariant flip requiring `Region.placeholder 0 : 'static`, which fails `leak_check`. -/
theorem static_to_hrtb_rejected : ¬ SubTy 0 tyStaticFn tyHrtbFn := by
  intro hsub
  unfold tyStaticFn tyHrtbFn at hsub
  cases hsub with
  | forallRight hinner =>
    cases hinner with
    | fnPtr harg _ =>
      cases harg with
      | ref hout _ =>
        exact Region.placeholder_not_outlives_static 0 hout

/-- **Theorem 3d (Double-Contravariant HRTB Flip Theorem):**
    `fn(fn(&'static u8) -> u8) -> u8 <: fn(for<'a> fn(&'a u8) -> u8) -> u8`
    is sound via `TyCtx.fnArg`, inverting polarity twice (`- x - = +`). -/
theorem double_contravariant_flip_sound :
    SubTy 0 (.fnPtr tyStaticFn .u8) (.fnPtr tyHrtbFn .u8) :=
  ctx_polarity_sound 0 (.fnArg .hole .u8) tyStaticFn tyHrtbFn
    ⟨trivial, SubTy.u8⟩ ((RelTy.contravariant_iff 0 tyStaticFn tyHrtbFn).mpr hrtb_to_static_sound)

/-- **Theorem 3e (Reverse Double-Contravariant Rejection):**
    `¬ (fn(for<'a> fn(&'a u8) -> u8) -> u8 <: fn(fn(&'static u8) -> u8) -> u8)`. -/
theorem double_flip_reverse_rejected :
    ¬ SubTy 0 (.fnPtr tyHrtbFn .u8) (.fnPtr tyStaticFn .u8) := by
  intro hsub
  cases hsub with
  | fnPtr harg _ =>
    exact static_to_hrtb_rejected harg

/-!
## Part 4: `zerocopy` `PtrInner` / `Ptr<'a, T, I>` Referent Invariance Soundness
## and Operational Aliasing-Lifetime Forgery Counterexample

Mirrors `google/zerocopy` `zerocopy/src/pointer/{inner.rs, ptr.rs}` and
`tests/ui/ptr-is-invariant-over-v.rs`.
-/

/-- **Theorem 4a (Zerocopy Lifetime Covariance):**
    `Ptr<'big, u8, al> <: Ptr<'small, u8, al>` holds whenever `'small ≤ 'big`. -/
theorem zerocopy_ptr_lifetime_covariant_ok (tBig tSmall : Nat) (hle : tSmall ≤ tBig)
    (al : ZcAliasing) :
    SubTy 0 (.zcPtr (.dur tBig) .u8 al) (.zcPtr (.dur tSmall) .u8 al) :=
  SubTy.zcPtr hle SubTy.u8 SubTy.u8

/-- **Theorem 4b (Zerocopy Referent Invariance Rejection — `Exclusive` & `Shared`):**
    Mirrors `zerocopy/tests/ui/ptr-is-invariant-over-v.rs:17-33`:
    `Ptr<'small, &'big u32, al>` is NOT a subtype of `Ptr<'small, &'small u32, al>`
    when `tSmall < tBig` for EITHER `Exclusive` OR `Shared` aliasing! -/
theorem zerocopy_ptr_referent_invariant_rejected (tBig tSmall : Nat) (hlt : tSmall < tBig)
    (al : ZcAliasing) :
    ¬ SubTy 0 (.zcPtr (.dur tSmall) (.ref (.dur tBig) .u8) al)
              (.zcPtr (.dur tSmall) (.ref (.dur tSmall) .u8) al) := by
  intro hsub
  cases hsub with
  | zcPtr _ _ hrev =>
    cases hrev with
    | ref hout _ =>
      exact Nat.not_lt_of_le hout hlt

/-! ### 4.1 Operational Heap & Region-Clock Semantics: Soundness vs. Forgery Witness -/

/-- Runtime values stored in our small heap model: scalars or references `(loc, dur)`. -/
inductive HeapVal where
  | scalar (v : Nat)
  | refVal (loc : Nat) (dur : Nat)
  | ptrLoc (loc : Nat) (outerDur : Nat)

/-- Heap maps memory locations `Nat` to `(allocDur, storedValue)`. -/
structure MemSlot where
  allocDur : Nat
  val : HeapVal

noncomputable def Heap := Nat → Option MemSlot

noncomputable def Heap.update (h : Heap) (loc : Nat) (slot : MemSlot) : Heap :=
  fun k => if Nat.beq k loc then some slot else h k

theorem Heap.update_self (h : Heap) (loc : Nat) (slot : MemSlot) :
    Heap.update h loc slot loc = some slot := by
  unfold Heap.update
  rw [Nat.beq_refl loc]
  rfl

theorem Heap.update_other (h : Heap) {loc k : Nat} (hne : k ≠ loc) (slot : MemSlot) :
    Heap.update h loc slot k = h k := by
  unfold Heap.update
  cases hbeq : Nat.beq k loc with
  | false => rfl
  | true => exact absurd (Nat.eq_of_beq_eq_true hbeq) hne

/-- Semantic type satisfaction for runtime `HeapVal` at clock time `clk`.
    Notice that for `ptr` pointing to a reference cell `slotLoc`, the inner `T` must be
    valid whenever `outerDur` is active (`clk ≤ outerDur`)! -/
noncomputable def ValWellTyped (h : Heap) (clk : Nat) : HeapVal → Ty → Prop
  | .scalar _, .u8 => True
  | .refVal loc dur, .ref (.dur rDur) inner =>
    dur = rDur ∧
    (clk ≤ dur → ∃ slot, h loc = some slot ∧ dur ≤ slot.allocDur ∧ ValWellTyped h clk slot.val inner)
  | .ptrLoc loc outerDur, .zcPtr (.dur rDur) inner _ =>
    outerDur = rDur ∧
    (clk ≤ outerDur → ∃ slot, h loc = some slot ∧ outerDur ≤ slot.allocDur ∧ ValWellTyped h clk slot.val inner)
  | .ptrLoc loc outerDur, .zcPtrBadCov (.dur rDur) inner _ =>
    outerDur = rDur ∧
    (clk ≤ outerDur → ∃ slot, h loc = some slot ∧ outerDur ≤ slot.allocDur ∧ ValWellTyped h clk slot.val inner)
  | _, _ => False

/-- Execution outcome of a small pointer-manipulation program at clock time `clk`. -/
inductive ExecResult where
  | ok (val : Nat)
  | danglingRead (loc : Nat) (clk : Nat) (allocDur : Nat)

/-- Write a `HeapVal` through a `Ptr` (`ptr.as_mut()` / `*p = newRef`) and subsequently
    read through an alias of the outer reference slot. -/
noncomputable def writeThroughPtrAndReadOuter (h : Heap) (slotLoc : Nat) (newRef : HeapVal)
    (readClk : Nat) : ExecResult :=
  match h slotLoc with
  | none => .danglingRead slotLoc readClk 0
  | some slot =>
    let h' := Heap.update h slotLoc { allocDur := slot.allocDur, val := newRef }
    match h' slotLoc with
    | some { allocDur := _, val := .refVal targetLoc _ } =>
      match h' targetLoc with
      | none => .danglingRead targetLoc readClk 0
      | some targetSlot =>
        if Nat.ble readClk targetSlot.allocDur then
          match targetSlot.val with
          | .scalar v => .ok v
          | _ => .danglingRead targetLoc readClk targetSlot.allocDur
        else
          .danglingRead targetLoc readClk targetSlot.allocDur
    | _ => .danglingRead slotLoc readClk slot.allocDur

/-- Concrete soundness theorem for lifetime covariance (`Ptr<'big, T, I> <: Ptr<'small, T, I>`):
    shortening `'big` to `'small` (`smallDur ≤ bigDur`) preserves `ValWellTyped` at every clock
    time `clk` without needing any extra hypothesis. -/
theorem ptr_lifetime_shortening_preserves_ValWellTyped (h : Heap) (clk : Nat)
    (slotLoc bigDur smallDur : Nat) (inner : Ty) (al : ZcAliasing)
    (h_le : smallDur ≤ bigDur)
    (h_wt : ValWellTyped h clk (.ptrLoc slotLoc bigDur) (.zcPtr (.dur bigDur) inner al)) :
    ValWellTyped h clk (.ptrLoc slotLoc smallDur) (.zcPtr (.dur smallDur) inner al) := by
  rcases h_wt with ⟨_, himp⟩
  refine ⟨rfl, ?_⟩
  intro hclk
  rcases himp (Nat.le_trans hclk h_le) with ⟨slot, hs, halloc, hval⟩
  exact ⟨slot, hs, Nat.le_trans h_le halloc, hval⟩

/-- **Theorem 4c (Soundness of Lifetime Covariance + Referent Invariance):**
    Shortening `'big` to `'small` on `Ptr<'a, T, I>` preserves `ValWellTyped` at every clock
    time `clk`, AND any write of a value `newRef` that is valid at the SAME invariant type
    `T = &'big u8` guarantees that reading the outer alias within `'big` (`readClk ≤ bigDur`)
    produces `.ok newVal` (never `danglingRead`)! -/
theorem ptr_lifetime_covariant_and_invariant_T_sound (h : Heap) (clk readClk : Nat)
    (bigDur smallDur slotLoc targetLoc newTargetLoc newVal : Nat)
    (h_sub : smallDur ≤ bigDur)
    (h_slot : h slotLoc = some { allocDur := bigDur, val := .refVal targetLoc bigDur })
    (h_wt_ptr : ValWellTyped h clk (.ptrLoc slotLoc bigDur) (.zcPtr (.dur bigDur) (.ref (.dur bigDur) .u8) .exclusive))
    (h_new_target : h newTargetLoc = some { allocDur := bigDur, val := .scalar newVal })
    (h_new_ne : newTargetLoc ≠ slotLoc)
    (h_clk_read : readClk ≤ bigDur) :
    ValWellTyped h clk (.ptrLoc slotLoc smallDur) (.zcPtr (.dur smallDur) (.ref (.dur bigDur) .u8) .exclusive) ∧
    writeThroughPtrAndReadOuter h slotLoc (.refVal newTargetLoc bigDur) readClk = .ok newVal := by
  refine ⟨ptr_lifetime_shortening_preserves_ValWellTyped h clk slotLoc bigDur smallDur
            (.ref (.dur bigDur) .u8) .exclusive h_sub h_wt_ptr, ?_⟩
  unfold writeThroughPtrAndReadOuter
  rw [h_slot]
  simp only
  rw [Heap.update_self]
  simp only
  rw [Heap.update_other h h_new_ne]
  rw [h_new_target]
  simp only
  have hble : Nat.ble readClk bigDur = true := Nat.ble_eq.mpr h_clk_read
  rw [hble]
  rfl

/-- **Theorem 4d (Aliasing-Lifetime Forgery Counterexample under Hypothetical Covariant `T`):**
    Models the pre-`fe70ab691` hazard if `Ptr<'a, T, I>` (`zcPtrBadCov`) were covariant in `T`:
    1. Slot `0` lives for `'big = 10`, initially holding `&'big u8` pointing to slot `1` (`allocDur = 10`).
    2. `p : PtrBadCov<'small, &'big u8, Exclusive>` (`small = 5`) points to slot `0`.
    3. Covariant coercion in `T` turns `p` into `PtrBadCov<'small, &'small u8, Exclusive>`
       (accepted by `SubTy.zcPtrBadCov` because `5 ≤ 10`!).
    4. Writing short-lived reference `y_short : &'tiny u8` (`tiny = 2`, pointing to slot `2` with
       `allocDur = 2`) through `p` coerced to `PtrBadCov<'tiny, &'tiny u8, Exclusive>` (`2 ≤ 5 ≤ 10`) succeeds under covariant `T`.
    5. Reading slot `0` through the surviving `'big` alias at clock `readClk = 5` (`5 ≤ 10`, strictly
       within `'big`'s lifetime, AFTER region `2` has expired!) hits **`ExecResult.danglingRead 2 5 2`**! -/
noncomputable def forgeryInitHeap : Heap
  | 0 => some { allocDur := 10, val := .refVal 1 10 }
  | 1 => some { allocDur := 10, val := .scalar 42 }
  | 2 => some { allocDur := 2, val := .scalar 99 }
  | _ => none

theorem ptrBadCov_coercion_accepted :
    SubTy 0 (.zcPtrBadCov (.dur 5) (.ref (.dur 10) .u8) .exclusive)
            (.zcPtrBadCov (.dur 2) (.ref (.dur 2) .u8) .exclusive) := by
  apply SubTy.zcPtrBadCov
  · exact Nat.le_trans (Nat.le_succ 2) (Nat.le_trans (Nat.le_succ 3) (Nat.le_succ 4))
  · apply SubTy.ref
    · exact Nat.le_trans (Nat.le_succ 2) (Nat.le_trans (Nat.le_succ 3) (Nat.le_trans (Nat.le_succ 4) (Nat.le_trans (Nat.le_succ 5) (Nat.le_trans (Nat.le_succ 6) (Nat.le_trans (Nat.le_succ 7) (Nat.le_trans (Nat.le_succ 8) (Nat.le_succ 9)))))))
    · exact SubTy.u8

theorem ptrBadCov_forgery_causes_dangling_read :
    writeThroughPtrAndReadOuter forgeryInitHeap 0 (.refVal 2 2) 5 = .danglingRead 2 5 2 := by
  unfold writeThroughPtrAndReadOuter forgeryInitHeap
  rfl

/-- Contrast: the real `zerocopy::Ptr` (`SubTy.zcPtr`) REJECTS that exact coercion at compile time! -/
theorem ptrReal_blocks_forgery_coercion :
    ¬ SubTy 0 (.zcPtr (.dur 5) (.ref (.dur 10) .u8) .exclusive)
              (.zcPtr (.dur 2) (.ref (.dur 2) .u8) .exclusive) := by
  intro hsub
  cases hsub with
  | zcPtr _ _ hrev =>
    cases hrev with
    | ref hout _ =>
      have hnot : ¬ (10 ≤ 2) := fun h =>
        Nat.not_lt_of_le h (Nat.lt_trans (Nat.lt_succ_self 2) (Nat.lt_trans (Nat.lt_succ_self 3) (Nat.lt_trans (Nat.lt_succ_self 4) (Nat.lt_trans (Nat.lt_succ_self 5) (Nat.lt_trans (Nat.lt_succ_self 6) (Nat.lt_trans (Nat.lt_succ_self 7) (Nat.lt_trans (Nat.lt_succ_self 8) (Nat.lt_succ_self 9))))))))
      exact hnot hout

end RustcVarianceHrtbPtr
