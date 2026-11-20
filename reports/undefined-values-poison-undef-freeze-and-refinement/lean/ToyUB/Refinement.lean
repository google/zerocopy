import ToyUB.Duplication
import ToyUB.Monotone

/-!
# Structure of refinement

Refinement (`RefinesU`, `RefinesP`) is a preorder (`refinesU_refl`, `refinesU_trans`,
`refinesP_refl`, `refinesP_trans` in `ToyUB.Lemmas`); a source that may reach UB is refined
by every target; and refinement is a congruence for every construct of the language in
both models.

Refinement is defined at the level of the model's *values*: in the undef model a target
value set must be contained in a single source value set. The tempting coarser notion that
compares only the integers a program may produce (`ObsRefinesU`) is *not* a congruence for
`let`: `x` and `freeze x` produce the same integers, but `let y := x; y + y` and
`let y := freeze x; y + y` do not.
-/

namespace Toy.UB

open Expr

/-- **Source UB permits anything (undef model).** If the source may reach UB in every
inhabited environment, every target refines it. -/
theorem refinesU_of_src_mayUB (w : Nat) {src : Expr}
    (h : ∀ ρ : Var → USet w, UInhabited ρ → MayUB (semU w ρ src)) (tgt : Expr) :
    RefinesU w tgt src :=
  fun ρ hρ => Or.inl (h ρ hρ)

/-- **Source UB permits anything (poison(+freeze) model).** If the source may reach UB in every
environment, every target refines it. -/
theorem refinesP_of_src_mayUB (w : Nat) {src : Expr}
    (h : ∀ ρ : Var → PVal w, MayUB (semP w ρ src)) (tgt : Expr) : RefinesP w tgt src :=
  fun ρ => Or.inl (h ρ)

/-- Instance: every program refines `ub` (undef model). -/
theorem refinesU_ub (w : Nat) (tgt : Expr) : RefinesU w tgt .ub :=
  refinesU_of_src_mayUB w (fun _ _ => mayUB_iff.mpr (by simp [semU])) tgt

/-- Instance: every program refines `ub` (poison(+freeze) model). -/
theorem refinesP_ub (w : Nat) (tgt : Expr) : RefinesP w tgt .ub :=
  refinesP_of_src_mayUB w (fun _ => mayUB_iff.mpr (by simp [semP])) tgt

/-! ### Congruence, undef model -/

/-- Undef-model refinement is a congruence for `+`. -/
theorem refinesU_congr_add (w : Nat) {a a' b b' : Expr} (ha : RefinesU w a' a)
    (hb : RefinesU w b' b) : RefinesU w (.add a' b') (.add a b) := by
  intro ρ hρ
  exact outRef_bind1 (ha ρ hρ) fun _ _ _ _ hA =>
    outRef_bind1 (hb ρ hρ) fun _ _ _ _ hB => outRef_singleton_val (USet.map2_mono hA hB)

/-- Undef-model refinement is a congruence for `*`. -/
theorem refinesU_congr_mul (w : Nat) {a a' b b' : Expr} (ha : RefinesU w a' a)
    (hb : RefinesU w b' b) : RefinesU w (.mul a' b') (.mul a b) := by
  intro ρ hρ
  exact outRef_bind1 (ha ρ hρ) fun _ _ _ _ hA =>
    outRef_bind1 (hb ρ hρ) fun _ _ _ _ hB => outRef_singleton_val (USet.map2_mono hA hB)

/-- Undef-model refinement is a congruence for the equality test. -/
theorem refinesU_congr_eq (w : Nat) {a a' b b' : Expr} (ha : RefinesU w a' a)
    (hb : RefinesU w b' b) : RefinesU w (.eq a' b') (.eq a b) := by
  intro ρ hρ
  exact outRef_bind1 (ha ρ hρ) fun _ _ _ _ hA =>
    outRef_bind1 (hb ρ hρ) fun _ _ _ _ hB => outRef_singleton_val (USet.map2_mono hA hB)

/-- Undef-model refinement is a congruence for `if` (condition and both branches). -/
theorem refinesU_congr_ite (w : Nat) {c c' t t' e e' : Expr} (hc : RefinesU w c' c)
    (ht : RefinesU w t' t) (he : RefinesU w e' e) : RefinesU w (.ite c' t' e') (.ite c t e) := by
  intro ρ hρ
  exact outRef_bind1 (hc ρ hρ) fun _ _ _ _ hC =>
    outRef_append (outRef_ite_branch (USet.hasNonzero_mono hC) (ht ρ hρ))
      (outRef_ite_branch (hC _) (he ρ hρ))

/-- Undef-model refinement is a congruence for `let` (bound expression and body). -/
theorem refinesU_congr_letE (w : Nat) (x : Var) {a a' b b' : Expr} (ha : RefinesU w a' a)
    (hb : RefinesU w b' b) : RefinesU w (.letE x a' b') (.letE x a b) := by
  intro ρ hρ
  refine outRef_bind1 (ha ρ hρ) fun A' A hA' _ hA => ?_
  have hinh : UInhabited (update ρ x A') := by
    intro y
    simp only [update]
    split
    · exact semU_val_nonempty w a' ρ hρ A' hA'
    · exact hρ y
  exact outRef_trans (R := USet.Sub) (fun _ _ _ h1 h2 => USet.Sub.trans h1 h2)
    (hb (update ρ x A') hinh)
    (semU_mono w b _ _ (update_sub (fun y => USet.Sub.refl (ρ y)) x hA))

/-- Undef-model refinement is a congruence for `freeze`. -/
theorem refinesU_congr_freeze (w : Nat) {a a' : Expr} (ha : RefinesU w a' a) :
    RefinesU w (.freeze a') (.freeze a) := by
  intro ρ hρ
  exact outRef_bind1 (ha ρ hρ) fun _ _ _ _ hA => freezeU_mono hA

/-! ### Congruence, poison(+freeze) model -/

/-- Poison(+freeze)-model refinement is a congruence for `+`. -/
theorem refinesP_congr_add (w : Nat) {a a' b b' : Expr} (ha : RefinesP w a' a)
    (hb : RefinesP w b' b) : RefinesP w (.add a' b') (.add a b) := by
  intro ρ
  exact outRef_bind1 (ha ρ) fun _ _ _ _ hA =>
    outRef_bind1 (hb ρ) fun _ _ _ _ hB => outRef_singleton_val (PVal.lift2_mono hA hB)

/-- Poison(+freeze)-model refinement is a congruence for `*`. -/
theorem refinesP_congr_mul (w : Nat) {a a' b b' : Expr} (ha : RefinesP w a' a)
    (hb : RefinesP w b' b) : RefinesP w (.mul a' b') (.mul a b) := by
  intro ρ
  exact outRef_bind1 (ha ρ) fun _ _ _ _ hA =>
    outRef_bind1 (hb ρ) fun _ _ _ _ hB => outRef_singleton_val (PVal.lift2_mono hA hB)

/-- Poison(+freeze)-model refinement is a congruence for the equality test. -/
theorem refinesP_congr_eq (w : Nat) {a a' b b' : Expr} (ha : RefinesP w a' a)
    (hb : RefinesP w b' b) : RefinesP w (.eq a' b') (.eq a b) := by
  intro ρ
  exact outRef_bind1 (ha ρ) fun _ _ _ _ hA =>
    outRef_bind1 (hb ρ) fun _ _ _ _ hB => outRef_singleton_val (PVal.lift2_mono hA hB)

/-- Poison(+freeze)-model refinement is a congruence for `if` (condition and both branches). -/
theorem refinesP_congr_ite (w : Nat) {c c' t t' e e' : Expr} (hc : RefinesP w c' c)
    (ht : RefinesP w t' t) (he : RefinesP w e' e) : RefinesP w (.ite c' t' e') (.ite c t e) := by
  intro ρ
  refine outRef_bind1 (hc ρ) fun c' c _ _ hcc => ?_
  cases c with
  | poison => exact Or.inl (mayUB_iff.mpr (by simp))
  | int z =>
    simp only [PVal.Refines] at hcc
    subst hcc
    dsimp only
    split
    · exact ht ρ
    · exact he ρ

/-- Poison(+freeze)-model refinement is a congruence for `let` (bound expression and body). -/
theorem refinesP_congr_letE (w : Nat) (x : Var) {a a' b b' : Expr} (ha : RefinesP w a' a)
    (hb : RefinesP w b' b) : RefinesP w (.letE x a' b') (.letE x a b) := by
  intro ρ
  refine outRef_bind1 (ha ρ) fun v' v _ _ hv => ?_
  exact outRef_trans (R := PVal.Refines) (fun _ _ _ h1 h2 => PVal.Refines.trans h1 h2)
    (hb (update ρ x v'))
    (semP_mono w b _ _ (update_refines (fun y => PVal.Refines.refl (ρ y)) x hv))

/-- Poison(+freeze)-model refinement is a congruence for `freeze`. -/
theorem refinesP_congr_freeze (w : Nat) {a a' : Expr} (ha : RefinesP w a' a) :
    RefinesP w (.freeze a') (.freeze a) := by
  intro ρ
  refine outRef_bind1 (ha ρ) fun v' v _ _ hv => ?_
  cases v with
  | poison =>
    apply outRef_of_subset PVal.Refines.refl
    intro o ho
    cases v' with
    | poison => exact ho
    | int u =>
      simp at ho
      subst ho
      simp [mem_allBV]
  | int u =>
    simp only [PVal.Refines] at hv
    subst hv
    exact outRef_refl PVal.Refines.refl _

/-! ### Observational refinement is not a congruence -/

/-- **Comparing only produced integers is not a congruence for `let` (undef model).**
For every width `w ≥ 1` and variables `x`, `y`: `x` observationally refines `freeze x`
(both produce exactly the integers in `x`'s set), but `let y := x; y + y` does not
observationally refine `let y := freeze x; y + y` (with `x ↦ {0, 1}` the former can
produce `1`, the latter only `0` or `2`). Value-level refinement correctly rejects
`freeze x → x` (`undef_remove_freeze_unsound`). -/
theorem undef_obsRefines_not_congruence_letE (w : Nat) (hw : 1 ≤ w) (x y : Var) :
    ObsRefinesU w (.var x) (.freeze (.var x)) ∧
    ¬ ObsRefinesU w (.letE y (.var x) (.add (.var y) (.var y)))
        (.letE y (.freeze (.var x)) (.add (.var y) (.var y))) := by
  constructor
  · intro ρ _
    right
    refine ⟨by simp [mayUB_iff, semU], ?_⟩
    intro z hz
    simp only [ObsU, semU, List.mem_singleton, exists_eq_left] at hz
    refine ⟨.val (USet.single z), ?_, by simp [USet.single]⟩
    simp only [semU, bind1_val_singleton, List.mem_filterMap]
    exact ⟨z, mem_allBV z, by simp [hz]⟩
  · intro h
    rcases h _ (uZeroOne_inhabited w) with hub | ⟨_, h⟩
    · rw [mayUB_iff] at hub
      simp only [semU, bind1_val_singleton] at hub
      rcases mem_bind1.mp hub with ⟨_, h⟩ | ⟨A, _, h⟩
      · rw [List.mem_filterMap] at h
        obtain ⟨v, _, hv⟩ := h
        split at hv <;> simp at hv
      · simp [bind2] at h
    · have h1 := h 1#w (by
        refine ⟨.val (USet.map2 (· + ·) (uZeroOne w x) (uZeroOne w x)),
          by simp [semU, bind2, update], ?_⟩
        simp only [USet.map2, uZeroOne, decide_eq_true_eq]
        exact ⟨0#w, 1#w, Or.inl rfl, Or.inr rfl, BitVec.zero_add _⟩)
      obtain ⟨o, ho, hz⟩ := h1
      simp only [semU, bind1_val_singleton] at ho
      rcases mem_bind1.mp ho with ⟨rfl, _⟩ | ⟨A, hA, ho⟩
      · simp at hz
      · rw [List.mem_filterMap] at hA
        obtain ⟨v, _, hv⟩ := hA
        split at hv
        · simp only [Option.some.injEq, Outcome.val.injEq] at hv
          subst hv
          simp [bind2, update] at ho
          subst ho
          simp [USet.map2, USet.single] at hz
          exact one_ne_add_self hw v hz.symm
        · simp at hv

/-- Width-`0` control: at width `0` the two `let` programs of
`undef_obsRefines_not_congruence_letE` are observationally related, so its hypothesis
`1 ≤ w` cannot be dropped. -/
theorem undef_obsRefines_letE_width_zero (x y : Var) :
    ObsRefinesU 0 (.letE y (.var x) (.add (.var y) (.var y)))
      (.letE y (.freeze (.var x)) (.add (.var y) (.var y))) := by
  intro ρ hρ
  right
  refine ⟨by simp [mayUB_iff, semU, bind2], ?_⟩
  intro z _
  obtain ⟨a, ha⟩ := hρ x
  refine ⟨.val (USet.map2 (· + ·) (USet.single a) (USet.single a)), ?_, ?_⟩
  · simp only [semU, bind1_val_singleton]
    refine mem_bind1.mpr (Or.inr ⟨USet.single a, ?_, by simp [bind2, update]⟩)
    rw [List.mem_filterMap]
    exact ⟨a, mem_allBV a, by simp [ha]⟩
  · show USet.map2 (· + ·) (USet.single a) (USet.single a) z = true
    apply decide_eq_true
    exact ⟨a, a, by simp [USet.single], by simp [USet.single],
      by rw [bv_zero_eq (v := z)]; exact bv_zero_eq⟩

end Toy.UB
