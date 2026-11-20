import ToyUB.Lemmas

/-!
# Equality propagation (GVN-style rewrite)

Inside `if x = y then t else e`, an optimizer may replace uses of `y` in `t` by `x`.
The rewrite is stated here in capture-free form: the target rebinds `y` to the value of
`x` in the `then`-branch, `if x = y then (let y := x; t) else e`. In both models `let y :=
x; t` gives every free use of `y` in `t` exactly what a use of `x` would give (in the undef
model a use of the rebound `y` still chooses independently from `x`'s set, like a use of
`x`).

* Poison(+freeze) model (branching on `poison` is UB): sound for all `t`, `e`, at every
  width.
* Undef model (branching on an undef value chooses nondeterministically): unsound at every
  width `≥ 1` when `x ≠ y`, witnessed by the then-branch `t = y` and else-branch `0`: the
  comparison and the later use of `x` may observe different integers. The failure depends
  on the branch: for `t = 0` or `t = x` the rewrite is sound
  (`undef_gvn_sound_examples_closed_or_x_branch`).
* Phase ordering: once the comparison is wrapped in `freeze`, the poison-model argument no
  longer applies, and the rewrite becomes unsound in the poison + freeze model
  (`poisonFreeze_gvn_after_freezing_condition_unsound`).

The rewrite is stated with `let y := x; t`, not with syntactic substitution `t[y := x]`
(which is not formalized here); the two agree for `t = y` (`semU_letE_var_var`,
`semP_letE_var_var`).
-/

namespace Toy.UB

open Expr

/-- For the `then`-branch `y`, the capture-free form `let y := x; y` has exactly the
meaning of `x` (undef model). -/
theorem semU_letE_var_var (w : Nat) (ρ : Var → USet w) (x y : Var) :
    semU w ρ (.letE y (.var x) (.var y)) = semU w ρ (.var x) := by
  simp [semU, update]

/-- For the `then`-branch `y`, the capture-free form `let y := x; y` has exactly the
meaning of `x` (poison model). -/
theorem semP_letE_var_var (w : Nat) (ρ : Var → PVal w) (x y : Var) :
    semP w ρ (.letE y (.var x) (.var y)) = semP w ρ (.var x) := by
  simp [semP, update]

/-- **Poison(+freeze) model, GVN is sound.** For every width `w`, variables `x`, `y` and expressions
`t`, `e`, rewriting `if x = y then t else e` to `if x = y then (let y := x; t) else e` is a
refinement in the poison(+freeze) model. (If either variable is `poison` the comparison is `poison`
and the source branches on it, which is UB; otherwise the `then`-branch runs only when the
two integers are equal.) -/
theorem poison_gvn_sound (w : Nat) (x y : Var) (t e : Expr) :
    RefinesP w (.ite (.eq (.var x) (.var y)) (.letE y (.var x) t) e)
      (.ite (.eq (.var x) (.var y)) t e) := by
  intro ρ
  cases hx : ρ x with
  | poison =>
    left
    rw [mayUB_iff]
    simp [semP, bind2, hx, PVal.lift2]
  | int a =>
    cases hy : ρ y with
    | poison =>
      left
      rw [mayUB_iff]
      simp [semP, bind2, hx, hy, PVal.lift2]
    | int b =>
      simp only [semP, bind2, bind1_val_singleton, hx, hy, PVal.lift2]
      split
      · rename_i hne
        have hab : a = b := by
          by_cases h : a = b
          · exact h
          · simp [eqBit, h] at hne
        subst hab
        have hupd : update ρ y (PVal.int a) = ρ := by
          funext v
          simp only [update]
          split
          · subst_vars; exact hy.symm
          · rfl
        rw [hupd]
        exact outRef_refl PVal.Refines.refl _
      · exact outRef_refl PVal.Refines.refl _

/-- The undef-model environment for the GVN counterexample: `x ↦ {0, 1}`, every other
variable `↦ {1}`. -/
def uGVN (w : Nat) (x : Var) : Var → USet w :=
  fun v => if v = x then (fun z => decide (z = 0#w ∨ z = 1#w)) else USet.single 1#w

/-- **Undef model, GVN with then-branch `y` is unsound.** For every width `w ≥ 1` and
distinct variables `x ≠ y`, rewriting `if x = y then y else 0` to `if x = y then (let y := x; y) else 0` (that is,
to `if x = y then x else 0`, see `semU_letE_var_var`) is not a refinement in the undef
model: with `x ↦ {0, 1}` and `y ↦ {1}` the comparison may succeed (choosing `x = 1`) while
the target's later use of `x` chooses `0`, so the target has the value set `{0, 1}`, which
is contained in neither source value set `{1}` nor `{0}`. -/
theorem undef_gvn_var_branch_distinct_vars_unsound (w : Nat) (hw : 1 ≤ w) (x y : Var) (hxy : x ≠ y) :
    ¬ RefinesU w (.ite (.eq (.var x) (.var y)) (.letE y (.var x) (.var y)) (.const 0))
        (.ite (.eq (.var x) (.var y)) (.var y) (.const 0)) := by
  intro h
  have hρx : uGVN w x x = fun z => decide (z = 0#w ∨ z = 1#w) := by simp [uGVN]
  have hρy : uGVN w x y = USet.single 1#w := by simp [uGVN, Ne.symm hxy]
  have hinh : UInhabited (uGVN w x) := by
    intro v
    by_cases hv : v = x
    · subst hv; exact ⟨0#w, by simp [hρx]⟩
    · exact ⟨1#w, by simp [uGVN, hv, USet.single]⟩
  have hC1 : (USet.map2 eqBit (uGVN w x x) (uGVN w x y)).HasNonzero = true := by
    apply decide_eq_true
    refine ⟨1#w, ?_, one_ne_zero_bv hw⟩
    apply decide_eq_true
    exact ⟨1#w, 1#w, by simp [hρx], by simp [hρy, USet.single], by simp [eqBit]⟩
  have hC0 : USet.map2 eqBit (uGVN w x x) (uGVN w x y) 0#w = true := by
    apply decide_eq_true
    refine ⟨0#w, 1#w, by simp [hρx], by simp [hρy, USet.single], ?_⟩
    simp [eqBit, Ne.symm (one_ne_zero_bv hw)]
  rcases h _ hinh with hub | h
  · rw [mayUB_iff] at hub
    simp only [semU, bind2, bind1_val_singleton, hC1, hC0, ite_true] at hub
    simp at hub
  · have hmem : Outcome.val (uGVN w x x) ∈ semU w (uGVN w x)
        (.ite (.eq (.var x) (.var y)) (.letE y (.var x) (.var y)) (.const 0)) := by
      simp only [semU, bind2, bind1_val_singleton, hC1, hC0, ite_true]
      simp [update]
    obtain ⟨o', ho', hle⟩ := h _ hmem
    simp only [semU, bind2, bind1_val_singleton, hC1, hC0, ite_true, List.mem_append,
      List.mem_singleton] at ho'
    rcases ho' with rfl | rfl
    · have := hle 0#w (by simp [hρx])
      rw [hρy] at this
      simp [USet.single, Ne.symm (one_ne_zero_bv hw)] at this
    · have := hle 1#w (by simp [hρx])
      simp [USet.single, one_ne_zero_bv hw] at this

/-- Width-`0` control: at width `0` the GVN rewrite is a refinement in the undef model (the
equality test then always yields `0`), so the hypothesis `1 ≤ w` of `undef_gvn_var_branch_distinct_vars_unsound`
cannot be dropped. -/
theorem undef_gvn_sound_width_zero (x y : Var) :
    RefinesU 0 (.ite (.eq (.var x) (.var y)) (.letE y (.var x) (.var y)) (.const 0))
      (.ite (.eq (.var x) (.var y)) (.var y) (.const 0)) := by
  intro ρ hρ
  have hC1 : (USet.map2 eqBit (ρ x) (ρ y)).HasNonzero = false := by
    simp only [USet.HasNonzero, decide_eq_false_iff_not, not_exists, not_and]
    intro z _ hz
    exact hz (bv_zero_eq (v := z))
  have hC0 : USet.map2 eqBit (ρ x) (ρ y) 0#0 = true := by
    obtain ⟨a, ha⟩ := hρ x
    obtain ⟨b, hb⟩ := hρ y
    apply decide_eq_true
    exact ⟨a, b, ha, hb, bv_zero_eq⟩
  simp only [semU, bind2, bind1_val_singleton, hC1, hC0]
  exact outRef_refl USet.Sub.refl _

/-- Same-variable control: when `x = y` the GVN rewrite is a refinement in the undef model
at every width, so the hypothesis `x ≠ y` of `undef_gvn_var_branch_distinct_vars_unsound` cannot be dropped. -/
theorem undef_gvn_sound_of_same_var (w : Nat) (x : Var) :
    RefinesU w (.ite (.eq (.var x) (.var x)) (.letE x (.var x) (.var x)) (.const 0))
      (.ite (.eq (.var x) (.var x)) (.var x) (.const 0)) := by
  intro ρ _
  have h : semU w ρ (.letE x (.var x) (.var x)) = semU w ρ (.var x) := semU_letE_var_var w ρ x x
  simp only [semU] at h
  simp only [semU, h]
  exact outRef_refl USet.Sub.refl _

/-- Branch dependence of `undef_gvn_var_branch_distinct_vars_unsound`: with then-branch
`0` or `x` (instead of `y`) the GVN rewrite is a refinement in the undef model at width 2
for the distinct variables `0`, `1`. -/
theorem undef_gvn_sound_examples_closed_or_x_branch :
    RefinesU 2 (.ite (.eq (.var 0) (.var 1)) (.letE 1 (.var 0) (.const 0)) (.const 0))
      (.ite (.eq (.var 0) (.var 1)) (.const 0) (.const 0)) ∧
    RefinesU 2 (.ite (.eq (.var 0) (.var 1)) (.letE 1 (.var 0) (.var 0)) (.const 0))
      (.ite (.eq (.var 0) (.var 1)) (.var 0) (.const 0)) := by
  refine ⟨fun ρ _ => outRef_refl USet.Sub.refl _, fun ρ _ => ?_⟩
  simp only [semU, bind1_val_singleton, update]
  exact outRef_refl USet.Sub.refl _

/-- **Phase ordering: GVN after freezing the comparison is unsound (poison + freeze
model).** For every width `w ≥ 1`, rewriting `if freeze (x = y) then y else 0` to
`if freeze (x = y) then (let y := x; y) else 0` (variables `x = 0`, `y = 1`) is not a
refinement: with `x ↦ poison`, `y ↦ 1`, the frozen comparison may be `1`, so the source
returns `1` or `0`, while the target may return `poison`. Compare `poison_gvn_sound`, where
the unfrozen comparison makes the source UB. -/
theorem poisonFreeze_gvn_after_freezing_condition_unsound (w : Nat) (hw : 1 ≤ w) :
    ¬ RefinesP w (.ite (.freeze (.eq (.var 0) (.var 1))) (.letE 1 (.var 0) (.var 1)) (.const 0))
        (.ite (.freeze (.eq (.var 0) (.var 1))) (.var 1) (.const 0)) := by
  intro h
  let ρ : Var → PVal w := fun v => if v = 0 then .poison else .int 1#w
  have hfr : semP w ρ (.freeze (.eq (.var 0) (.var 1))) =
      (allBV w).map fun v => Outcome.val (PVal.int v) := by
    simp [semP, bind2, ρ, PVal.lift2]
  have hsrc : ∀ o ∈ semP w ρ (.ite (.freeze (.eq (.var 0) (.var 1))) (.var 1) (.const 0)),
      ∃ u : BitVec w, o = .val (.int u) := by
    intro o ho
    have ho' : o ∈ bind1 (semP w ρ (.freeze (.eq (.var 0) (.var 1)))) (fun
        | .poison => [.ub]
        | .int z => if z ≠ 0#w then semP w ρ (.var 1) else semP w ρ (.const 0)) := ho
    rw [hfr] at ho'
    rcases mem_bind1.mp ho' with ⟨_, hub⟩ | ⟨v, hv, ho''⟩
    · simp at hub
    · simp only [List.mem_map] at hv
      obtain ⟨u, _, hu⟩ := hv
      cases hu
      dsimp only at ho''
      split at ho'' <;> simp [semP, ρ] at ho'' <;> exact ⟨_, ho''⟩
  have hmem : Outcome.val PVal.poison ∈
      semP w ρ (.ite (.freeze (.eq (.var 0) (.var 1))) (.letE 1 (.var 0) (.var 1)) (.const 0)) := by
    show _ ∈ bind1 (semP w ρ (.freeze (.eq (.var 0) (.var 1)))) _
    rw [hfr]
    refine mem_bind1.mpr (Or.inr ⟨.int 1#w, List.mem_map.mpr ⟨1#w, mem_allBV _, rfl⟩, ?_⟩)
    simp [one_ne_zero_bv hw, semP, update, ρ]
  rcases h ρ with hub | h
  · obtain ⟨u, hu⟩ := hsrc _ (mayUB_iff.mp hub)
    cases hu
  · obtain ⟨o', ho', hle⟩ := h _ hmem
    obtain ⟨u, rfl⟩ := hsrc _ ho'
    simp [Outcome.LeVal, PVal.Refines] at hle

/-- **Escape hatch for undef-model GVN: freeze the compared operand first.** For every width
`w`, rewriting `if x = y then y else 0` to `let x' := freeze x; if x' = y then x' else 0`
(variables `x = 0`, `y = 1`, `x' = 2`) is a refinement in the undef model: the frozen
operand is a single integer, so the comparison and the later use agree. (If `x'` were `y`
itself, the binder would shadow `y` and the rewrite would fail.) -/
theorem undef_gvn_with_frozen_operand_sound (w : Nat) :
    RefinesU w (.letE 2 (.freeze (.var 0)) (.ite (.eq (.var 2) (.var 1)) (.var 2) (.const 0)))
      (.ite (.eq (.var 0) (.var 1)) (.var 1) (.const 0)) := by
  intro ρ _
  right
  intro o ho
  have ho1 : o ∈ bind1 (semU w ρ (.freeze (.var 0))) (fun A =>
      semU w (update ρ 2 A) (.ite (.eq (.var 2) (.var 1)) (.var 2) (.const 0))) := ho
  rcases mem_bind1.mp ho1 with ⟨_, hub⟩ | ⟨B, hB, ho2⟩
  · simp only [semU, bind1_val_singleton, List.mem_filterMap] at hub
    obtain ⟨v, _, hv⟩ := hub
    split at hv <;> simp at hv
  · simp only [semU, bind1_val_singleton, List.mem_filterMap] at hB
    obtain ⟨v, _, hv⟩ := hB
    split at hv
    · rename_i hxv
      simp only [Option.some.injEq, Outcome.val.injEq] at hv
      subst hv
      have h21 : update ρ 2 (USet.single v) 1 = ρ 1 := by simp [update]
      have h22 : update ρ 2 (USet.single v) 2 = USet.single v := by simp [update]
      simp only [semU, bind2, bind1_val_singleton, h21, h22, List.mem_append] at ho2
      -- the source's comparison value set
      have hsrc : semU w ρ (.ite (.eq (.var 0) (.var 1)) (.var 1) (.const 0)) =
          (if (USet.map2 eqBit (ρ 0) (ρ 1)).HasNonzero then [.val (ρ 1)] else []) ++
          (if USet.map2 eqBit (ρ 0) (ρ 1) 0#w then [.val (USet.single (BitVec.ofNat w 0))] else []) := by
        simp [semU, bind2]
      rw [hsrc]
      rcases ho2 with ho2 | ho2
      · split at ho2
        · rename_i hnz
          simp only [List.mem_singleton] at ho2
          subst ho2
          simp only [USet.HasNonzero, USet.map2, USet.single, decide_eq_true_eq] at hnz
          obtain ⟨z, ⟨a, b, ha, hb, hab⟩, hz⟩ := hnz
          subst ha
          have hvb : a = b := by
            by_cases h : a = b
            · exact h
            · subst hab; simp [eqBit, h] at hz
          subst hvb
          have hnz' : (USet.map2 eqBit (ρ 0) (ρ 1)).HasNonzero = true := by
            simp only [USet.HasNonzero, USet.map2, decide_eq_true_eq]
            exact ⟨z, ⟨a, a, hxv, hb, hab⟩, hz⟩
          refine ⟨.val (ρ 1), by simp [hnz'], ?_⟩
          intro u hu
          simp only [USet.single, decide_eq_true_eq] at hu
          subst hu
          exact hb
        · simp at ho2
      · split at ho2
        · rename_i h0
          simp only [List.mem_singleton] at ho2
          subst ho2
          simp only [USet.map2, USet.single, decide_eq_true_eq] at h0
          obtain ⟨a, b, ha, hb, hab⟩ := h0
          subst ha
          have h0' : USet.map2 eqBit (ρ 0) (ρ 1) 0#w = true := by
            simp only [USet.map2, decide_eq_true_eq]
            exact ⟨a, b, hxv, hb, hab⟩
          exact ⟨.val (USet.single (BitVec.ofNat w 0)), by simp [h0'], USet.Sub.refl _⟩
        · simp at ho2
    · simp at hv

end Toy.UB
