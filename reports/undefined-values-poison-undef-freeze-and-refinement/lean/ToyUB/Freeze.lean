import ToyUB.Duplication
import ToyUB.Monotone

/-!
# Laws of `freeze`

In the poison + freeze model `freeze` is the identity on non-poison values and turns
`poison` into an arbitrary but fixed integer; all uses of one frozen value (bound by `let`)
agree, while two separate `freeze` operations may choose differently. Consequently:

* inserting `freeze` is a refinement and removing it is not (but removing it from an
  operand that never yields `poison`, e.g. `freeze (freeze e) → freeze e`, is);
* `let a := freeze x; a + a` has at least one outcome and all its outcomes are even, while
  `freeze x + freeze x` can produce every integer (in particular an odd one);
* *duplicating* a `freeze` (rewriting `let a := freeze x; a + a` to
  `freeze x + freeze x`) is unsound, while *merging* two `freeze`s of the same operand
  (the reverse direction) is a refinement; replacing only *some* uses of a second `freeze`
  by a first one is unsound (`poisonFreeze_partial_merge_freeze_unsound`).

The undef model's `freeze` (pick one element of the set) satisfies the analogous
insertion/removal laws.
-/

namespace Toy.UB

open Expr

/-- **`freeze` is the identity on non-poison values.** For every width, environment and
expression `e`, if no outcome of `e` is the value `poison`, then `freeze e` has exactly the
outcomes of `e`. -/
theorem poisonFreeze_freeze_eq_self_of_no_poison (w : Nat) (ρ : Var → PVal w) (e : Expr)
    (h : Outcome.val PVal.poison ∉ semP w ρ e) : semP w ρ (.freeze e) = semP w ρ e := by
  simp only [semP]
  generalize semP w ρ e = S at h ⊢
  induction S with
  | nil => rfl
  | cons o S ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [bind1, List.flatMap_cons] at ih ⊢
    rw [ih h.2]
    cases o with
    | ub => rfl
    | val v =>
      cases v with
      | poison => exact absurd rfl h.1
      | int u => rfl

/-- `freeze` is not the identity on `poison`: `freeze x` with `x ↦ poison` has no `poison`
outcome while `x` has one (every width). -/
theorem poisonFreeze_freeze_ne_self_of_poison (w : Nat) (x : Var) :
    semP w (fun _ => .poison) (.freeze (.var x)) ≠ semP w (fun _ => .poison) (.var x) := by
  intro h
  have hmem : Outcome.val PVal.poison ∈ semP w (fun _ => .poison) (.var x) := by simp [semP]
  rw [← h] at hmem
  simp [semP] at hmem

/-- **Inserting `freeze` is sound (poison + freeze model).** For every width `w` and
expression `e`, rewriting `e` to `freeze e` is a refinement. -/
theorem poisonFreeze_insert_freeze_sound (w : Nat) (e : Expr) : RefinesP w (.freeze e) e := by
  intro ρ
  by_cases hS : Outcome.ub ∈ semP w ρ e
  · exact Or.inl (mayUB_iff.mpr hS)
  · right
    intro o ho
    simp only [semP] at ho
    rcases mem_bind1.mp ho with ⟨_, h⟩ | ⟨v, hv, ho⟩
    · exact absurd h hS
    · refine ⟨.val v, hv, ?_⟩
      cases v with
      | poison =>
        simp only [List.mem_map] at ho
        obtain ⟨u, _, rfl⟩ := ho
        simp [Outcome.LeVal, PVal.Refines]
      | int u =>
        simp only [List.mem_singleton] at ho
        subst ho
        simp [Outcome.LeVal, PVal.Refines]

/-- **Removing `freeze` is unsound (poison + freeze model).** For every width `w` and
variable `x`, rewriting `freeze x` to `x` is not a refinement: with `x ↦ poison` the target
yields `poison`, which refines no integer. -/
theorem poisonFreeze_remove_freeze_unsound (w : Nat) (x : Var) :
    ¬ RefinesP w (.var x) (.freeze (.var x)) := by
  intro h
  rcases h (fun _ => .poison) with hub | h
  · rw [mayUB_iff] at hub
    simp [semP] at hub
  · obtain ⟨o', ho', hle⟩ := h (.val .poison) (by simp [semP])
    simp only [semP, bind1_val_singleton, List.mem_map] at ho'
    obtain ⟨u, _, rfl⟩ := ho'
    simp [Outcome.LeVal, PVal.Refines] at hle

/-- **A single frozen value used twice is even.** For every width `w`, variables `x`, `a`
and environment `ρ`, every outcome of `let a := freeze x; a + a` is a non-poison integer
whose numeric value is even (no UB, no `poison`). -/
theorem poisonFreeze_let_freeze_add_self_even (w : Nat) (x a : Var) (ρ : Var → PVal w) :
    ∀ o ∈ semP w ρ (.letE a (.freeze (.var x)) (.add (.var a) (.var a))),
      ∃ v : BitVec w, o = .val (.int v) ∧ v.toNat % 2 = 0 := by
  intro o ho
  simp only [semP, bind1_val_singleton] at ho
  rcases mem_bind1.mp ho with ⟨_, h⟩ | ⟨v, hv, ho⟩
  · cases hx : ρ x <;> simp [hx] at h
  · have hint : ∃ u, v = .int u := by
      cases hx : ρ x <;> simp [hx] at hv
      · obtain ⟨u, _, hu⟩ := hv; exact ⟨u, hu.symm⟩
      · exact ⟨_, hv⟩
    obtain ⟨u, rfl⟩ := hint
    simp [bind2, update, PVal.lift2] at ho
    exact ⟨u + u, ho, toNat_add_self_mod_two u⟩

/-- **Two separate `freeze`s need not agree.** For every width `w ≥ 1` and variable `x`,
there is an environment (`x ↦ poison`) in which `freeze x + freeze x` has an odd integer
outcome. -/
theorem poisonFreeze_freeze_add_freeze_can_be_odd (w : Nat) (hw : 1 ≤ w) (x : Var) :
    ∃ ρ : Var → PVal w, ∃ v : BitVec w,
      Outcome.val (PVal.int v) ∈ semP w ρ (.add (.freeze (.var x)) (.freeze (.var x))) ∧
      v.toNat % 2 = 1 := by
  refine ⟨fun _ => .poison, 1#w, ?_, toNat_one_mod_two hw⟩
  simp only [semP, bind2, bind1_val_singleton]
  refine mem_bind1.mpr (Or.inr ⟨.int 0#w, by simp [mem_allBV], ?_⟩)
  refine mem_bind1.mpr (Or.inr ⟨.int 1#w, by simp [mem_allBV], ?_⟩)
  simp [PVal.lift2]

/-- **Duplicating a `freeze` is unsound.** For every width `w ≥ 1` and variables `x`, `a`,
rewriting `let a := freeze x; a + a` to `freeze x + freeze x` is not a refinement in the
poison + freeze model. -/
theorem poisonFreeze_duplicate_freeze_unsound (w : Nat) (hw : 1 ≤ w) (x a : Var) :
    ¬ RefinesP w (.add (.freeze (.var x)) (.freeze (.var x)))
        (.letE a (.freeze (.var x)) (.add (.var a) (.var a))) := by
  intro h
  obtain ⟨ρ, v, hodd, hv1⟩ := poisonFreeze_freeze_add_freeze_can_be_odd w hw x
  have heven := poisonFreeze_let_freeze_add_self_even w x a ρ
  rcases h ρ with hub | h
  · obtain ⟨u, hu, _⟩ := heven _ (mayUB_iff.mp hub)
    cases hu
  · obtain ⟨o', ho', hle⟩ := h _ hodd
    obtain ⟨u, rfl, hu⟩ := heven _ ho'
    simp only [Outcome.LeVal, PVal.Refines, PVal.int.injEq] at hle
    subst hle
    rw [hu] at hv1
    exact absurd hv1 (by decide)

/-- Width-`0` control: at width `0` duplicating a `freeze` is a refinement, so the
hypothesis `1 ≤ w` of `poisonFreeze_duplicate_freeze_unsound` cannot be dropped. -/
theorem poisonFreeze_duplicate_freeze_sound_width_zero (x a : Var) :
    RefinesP 0 (.add (.freeze (.var x)) (.freeze (.var x)))
      (.letE a (.freeze (.var x)) (.add (.var a) (.var a))) := by
  intro ρ
  cases h : ρ x with
  | poison => simp [semP, bind2, h, update, allBV]; decide
  | int v =>
    obtain rfl := bv_zero_eq (v := v)
    simp [semP, bind2, h, update]; decide

/-- **Merging two `freeze`s of the same operand is sound.** For every width `w`,
expression `e` and variable `a`, rewriting `freeze e + freeze e` to
`let a := freeze e; a + a` is a refinement in the poison + freeze model. -/
theorem poisonFreeze_merge_freeze_sound (w : Nat) (e : Expr) (a : Var) :
    RefinesP w (.letE a (.freeze e) (.add (.var a) (.var a))) (.add (.freeze e) (.freeze e)) := by
  intro ρ
  by_cases hF : Outcome.ub ∈ semP w ρ (.freeze e)
  · left
    rw [mayUB_iff]
    show Outcome.ub ∈ bind2 (semP w ρ (.freeze e)) (semP w ρ (.freeze e)) _
    exact ub_mem_bind1_of_ub_mem hF
  · right
    intro o ho
    have ho' : o ∈ bind1 (semP w ρ (.freeze e))
        (fun v => semP w (update ρ a v) (.add (.var a) (.var a))) := ho
    rcases mem_bind1.mp ho' with ⟨_, h⟩ | ⟨v, hv, ho⟩
    · exact absurd h hF
    · simp [semP, bind2, update] at ho
      subst ho
      refine ⟨.val (PVal.lift2 (· + ·) v v), ?_, PVal.Refines.refl _⟩
      show _ ∈ bind2 (semP w ρ (.freeze e)) (semP w ρ (.freeze e)) _
      exact mem_bind1.mpr (Or.inr ⟨v, hv, mem_bind1.mpr (Or.inr ⟨v, hv, by simp⟩)⟩)

/-- **Inserting `freeze` is sound (undef model).** For every width `w` and expression `e`,
rewriting `e` to `freeze e` is a refinement in the undef model. -/
theorem undef_insert_freeze_sound (w : Nat) (e : Expr) : RefinesU w (.freeze e) e := by
  intro ρ _
  by_cases hS : Outcome.ub ∈ semU w ρ e
  · exact Or.inl (mayUB_iff.mpr hS)
  · right
    intro o ho
    simp only [semU] at ho
    rcases mem_bind1.mp ho with ⟨_, h⟩ | ⟨A, hA, ho⟩
    · exact absurd h hS
    · refine ⟨.val A, hA, ?_⟩
      rw [List.mem_filterMap] at ho
      obtain ⟨v, _, hv⟩ := ho
      by_cases hAv : A v = true
      · simp only [hAv, ite_true, Option.some.injEq] at hv
        subst hv
        intro z hz
        simp only [USet.single, decide_eq_true_eq] at hz
        subst hz
        exact hAv
      · simp [hAv] at hv

/-- **Removing `freeze` is unsound (undef model).** For every width `w ≥ 1` and variable
`x`, rewriting `freeze x` to `x` is not a refinement in the undef model: with
`x ↦ {0, 1}` the target value set `{0, 1}` is contained in no source value set `{0}` or
`{1}`. -/
theorem undef_remove_freeze_unsound (w : Nat) (hw : 1 ≤ w) (x : Var) :
    ¬ RefinesU w (.var x) (.freeze (.var x)) := by
  intro h
  rcases h _ (uZeroOne_inhabited w) with hub | h
  · rw [mayUB_iff] at hub
    simp only [semU, bind1_val_singleton, List.mem_filterMap] at hub
    obtain ⟨v, _, hv⟩ := hub
    split at hv <;> simp at hv
  · obtain ⟨o', ho', hle⟩ := h (.val (uZeroOne w x)) (by simp [semU])
    simp only [semU, bind1_val_singleton, List.mem_filterMap] at ho'
    obtain ⟨v, _, hv⟩ := ho'
    split at hv
    · simp only [Option.some.injEq] at hv
      subst hv
      have h0 := hle 0#w (by simp [uZeroOne])
      have h1 := hle 1#w (by simp [uZeroOne])
      simp only [USet.single, decide_eq_true_eq] at h0 h1
      exact one_ne_zero_bv hw (h1.trans h0.symm)
    · simp at hv

/-- Width-`0` control: at width `0` removing `freeze` is a refinement in the undef model
(every inhabited set is the whole one-element type), so the hypothesis `1 ≤ w` of
`undef_remove_freeze_unsound` cannot be dropped. -/
theorem undef_remove_freeze_sound_width_zero (x : Var) :
    RefinesU 0 (.var x) (.freeze (.var x)) := by
  intro ρ hρ
  right
  intro o ho
  simp only [semU, List.mem_singleton] at ho
  subst ho
  obtain ⟨a, ha⟩ := hρ x
  refine ⟨.val (USet.single a), ?_, ?_⟩
  · simp only [semU, bind1_val_singleton, List.mem_filterMap]
    exact ⟨a, mem_allBV a, by simp [ha]⟩
  · intro z _
    simp only [USet.single, decide_eq_true_eq]
    rw [bv_zero_eq (v := z), bv_zero_eq (v := a)]

/-- Width-`0` control for `poisonFreeze_freeze_add_freeze_can_be_odd`: at width `0` every
integer outcome is even, so the hypothesis `1 ≤ w` cannot be dropped. -/
theorem poisonFreeze_freeze_add_freeze_even_width_zero (x : Var) (ρ : Var → PVal 0)
    (v : BitVec 0) (_ : Outcome.val (PVal.int v) ∈
      semP 0 ρ (.add (.freeze (.var x)) (.freeze (.var x)))) : v.toNat % 2 = 0 := by
  rw [bv_zero_eq (v := v)]
  rfl

/-- `freeze e` never yields `poison`. -/
theorem poison_not_mem_semP_freeze (w : Nat) (ρ : Var → PVal w) (e : Expr) :
    Outcome.val PVal.poison ∉ semP w ρ (.freeze e) := by
  intro h
  simp only [semP] at h
  rcases mem_bind1.mp h with ⟨h1, _⟩ | ⟨v, _, hv⟩
  · cases h1
  · cases v <;> simp at hv

/-- **Removing `freeze` from an operand that never yields `poison` is sound (poison +
freeze model).** For every width `w` and expression `e` such that no outcome of `e` is
`poison` in any environment, rewriting `freeze e` to `e` is a refinement. -/
theorem poisonFreeze_remove_freeze_sound_of_no_poison (w : Nat) (e : Expr)
    (h : ∀ ρ : Var → PVal w, Outcome.val PVal.poison ∉ semP w ρ e) :
    RefinesP w e (.freeze e) := by
  intro ρ
  rw [poisonFreeze_freeze_eq_self_of_no_poison w ρ e (h ρ)]
  exact outRef_refl PVal.Refines.refl _

/-- **Redundant `freeze` elimination is sound (poison + freeze model).** For every width
`w` and expression `e`, rewriting `freeze (freeze e)` to `freeze e` is a refinement. -/
theorem poisonFreeze_remove_redundant_freeze_sound (w : Nat) (e : Expr) :
    RefinesP w (.freeze e) (.freeze (.freeze e)) :=
  poisonFreeze_remove_freeze_sound_of_no_poison w (.freeze e)
    (fun ρ => poison_not_mem_semP_freeze w ρ e)

/-- **Redundant `freeze` elimination is sound (undef model).** For every width `w` and
expression `e`, rewriting `freeze (freeze e)` to `freeze e` is a refinement. -/
theorem undef_remove_redundant_freeze_sound (w : Nat) (e : Expr) :
    RefinesU w (.freeze e) (.freeze (.freeze e)) := by
  intro ρ _
  apply outRef_of_subset USet.Sub.refl
  intro o ho
  cases o with
  | ub => exact ub_mem_bind1_of_ub_mem ho
  | val B =>
    have hB : ∃ v, B = USet.single v := by
      have ho' := ho
      simp only [semU] at ho'
      rcases mem_bind1.mp ho' with ⟨h1, _⟩ | ⟨A, _, hv⟩
      · cases h1
      · rw [List.mem_filterMap] at hv
        obtain ⟨v, _, hv⟩ := hv
        split at hv
        · simp only [Option.some.injEq, Outcome.val.injEq] at hv
          exact ⟨v, hv.symm⟩
        · simp at hv
    obtain ⟨v, rfl⟩ := hB
    show _ ∈ bind1 (semU w ρ (.freeze e)) _
    refine mem_bind1.mpr (Or.inr ⟨USet.single v, ho, ?_⟩)
    rw [List.mem_filterMap]
    exact ⟨v, mem_allBV v, by simp [USet.single]⟩

/-- **A single frozen value used twice: nonempty and even.** For every width `w`,
variables `x`, `a` and environment `ρ`, `let a := freeze x; a + a` has at least one
outcome, and every outcome is a non-poison integer whose numeric value is even. -/
theorem poisonFreeze_let_freeze_add_self_nonempty_even (w : Nat) (x a : Var)
    (ρ : Var → PVal w) :
    semP w ρ (.letE a (.freeze (.var x)) (.add (.var a) (.var a))) ≠ [] ∧
    ∀ o ∈ semP w ρ (.letE a (.freeze (.var x)) (.add (.var a) (.var a))),
      ∃ v : BitVec w, o = .val (.int v) ∧ v.toNat % 2 = 0 :=
  ⟨semP_ne_nil w _ ρ, poisonFreeze_let_freeze_add_self_even w x a ρ⟩

/-- **Two separate `freeze`s of `poison` can produce every integer.** For every width
`w`, variable `x` and integer `v`, with `x ↦ poison` the program `freeze x + freeze x` has
the outcome `v` (choose `0` and `v`). -/
theorem poisonFreeze_freeze_add_freeze_all_values_of_poison (w : Nat) (x : Var)
    (v : BitVec w) :
    Outcome.val (PVal.int v) ∈
      semP w (fun _ => .poison) (.add (.freeze (.var x)) (.freeze (.var x))) := by
  simp only [semP, bind2, bind1_val_singleton]
  refine mem_bind1.mpr (Or.inr ⟨.int 0#w, List.mem_map.mpr ⟨0#w, mem_allBV 0#w, rfl⟩, ?_⟩)
  refine mem_bind1.mpr (Or.inr ⟨.int v, List.mem_map.mpr ⟨v, mem_allBV v, rfl⟩, ?_⟩)
  simp [PVal.lift2, BitVec.zero_add]

/-- **Partial merging of `freeze`s is unsound.** For every width `w ≥ 1`, in
`let b1 := freeze x; let b2 := freeze x; (b2 = b2)` (variables `x = 0`, `b1 = 1`,
`b2 = 2`), replacing only *one* of the two uses of `b2` by `b1` is not a refinement: the
source always yields `1`, while with `x ↦ poison` the target `... (b1 = b2)` may yield `0`.
(Replacing all uses of `b2` gives `b1 = b1`, which always yields `1`.) -/
theorem poisonFreeze_partial_merge_freeze_unsound (w : Nat) (hw : 1 ≤ w) :
    ¬ RefinesP w
        (.letE 1 (.freeze (.var 0)) (.letE 2 (.freeze (.var 0)) (.eq (.var 1) (.var 2))))
        (.letE 1 (.freeze (.var 0)) (.letE 2 (.freeze (.var 0)) (.eq (.var 2) (.var 2)))) := by
  intro h
  have hF : ∀ ρ' : Var → PVal w, ρ' 0 = .poison →
      semP w ρ' (.freeze (.var 0)) = (allBV w).map fun v => Outcome.val (PVal.int v) := by
    intro ρ' h0
    simp [semP, h0]
  let ρ : Var → PVal w := fun _ => .poison
  have hsrc : ∀ o ∈ semP w ρ
      (.letE 1 (.freeze (.var 0)) (.letE 2 (.freeze (.var 0)) (.eq (.var 2) (.var 2)))),
      o = .val (.int 1#w) := by
    intro o ho
    have ho1 : o ∈ bind1 (semP w ρ (.freeze (.var 0))) (fun v1 =>
        bind1 (semP w (update ρ 1 v1) (.freeze (.var 0))) (fun v2 =>
          semP w (update (update ρ 1 v1) 2 v2) (.eq (.var 2) (.var 2)))) := ho
    rw [hF ρ rfl] at ho1
    rcases mem_bind1.mp ho1 with ⟨_, hub⟩ | ⟨v1, _, ho2⟩
    · simp at hub
    · rw [hF _ (by simp [update, ρ])] at ho2
      rcases mem_bind1.mp ho2 with ⟨_, hub⟩ | ⟨v2, hv2, ho3⟩
      · simp at hub
      · simp only [List.mem_map] at hv2
        obtain ⟨u, _, hu⟩ := hv2
        cases hu
        simp [semP, bind2, update, PVal.lift2, eqBit] at ho3
        exact ho3
  have hmem : Outcome.val (PVal.int 0#w) ∈ semP w ρ
      (.letE 1 (.freeze (.var 0)) (.letE 2 (.freeze (.var 0)) (.eq (.var 1) (.var 2)))) := by
    show _ ∈ bind1 (semP w ρ (.freeze (.var 0))) (fun v1 =>
        bind1 (semP w (update ρ 1 v1) (.freeze (.var 0))) (fun v2 =>
          semP w (update (update ρ 1 v1) 2 v2) (.eq (.var 1) (.var 2))))
    rw [hF ρ rfl]
    refine mem_bind1.mpr (Or.inr ⟨.int 0#w, List.mem_map.mpr ⟨0#w, mem_allBV _, rfl⟩, ?_⟩)
    rw [hF _ (by simp [update, ρ])]
    refine mem_bind1.mpr (Or.inr ⟨.int 1#w, List.mem_map.mpr ⟨1#w, mem_allBV _, rfl⟩, ?_⟩)
    simp [semP, bind2, update, PVal.lift2, eqBit, Ne.symm (one_ne_zero_bv hw)]
  rcases h ρ with hub | h
  · cases hsrc _ (mayUB_iff.mp hub)
  · obtain ⟨o', ho', hle⟩ := h _ hmem
    rw [hsrc _ ho'] at hle
    simp only [Outcome.LeVal, PVal.Refines, PVal.int.injEq] at hle
    exact one_ne_zero_bv hw hle.symm

/-- **Escape hatch for duplicating a `freeze`: a non-poison operand.** For every width
`w`, variables `x`, `a`, and environment with `x ↦ v` (an integer, as guaranteed by a
`noundef`-style precondition), the outcomes of `freeze x + freeze x` refine those of
`let a := freeze x; a + a` (both are exactly `v + v`). -/
theorem poisonFreeze_duplicate_freeze_sound_at_int (w : Nat) (x a : Var) (ρ : Var → PVal w)
    (v : BitVec w) (hx : ρ x = .int v) :
    OutRef PVal.Refines (semP w ρ (.add (.freeze (.var x)) (.freeze (.var x))))
      (semP w ρ (.letE a (.freeze (.var x)) (.add (.var a) (.var a)))) := by
  have h1 : semP w ρ (.add (.freeze (.var x)) (.freeze (.var x))) = [.val (.int (v + v))] := by
    simp [semP, bind2, hx, PVal.lift2]
  have h2 : semP w ρ (.letE a (.freeze (.var x)) (.add (.var a) (.var a))) =
      [.val (.int (v + v))] := by
    simp [semP, bind2, hx, update, PVal.lift2]
  rw [h1, h2]
  exact outRef_refl PVal.Refines.refl _

end Toy.UB
