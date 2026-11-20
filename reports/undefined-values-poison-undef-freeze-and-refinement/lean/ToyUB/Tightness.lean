import ToyUB.Refinement
import ToyUB.Freeze
import ToyUB.GVN
import ToyUB.Unswitch

/-!
# Tightness of the congruence premises

For each congruence theorem and each of its premises: a concrete width-2 instance in which
the other premises hold (by reflexivity) and the conclusion fails. The dropped premise is
always instantiated by the non-refining pair `1` (target) / `0` (source).
-/

namespace Toy.UB

open Expr

theorem not_refinesU_of_env {w : Nat} {tgt src : Expr} (ρ : Var → USet w) (hρ : UInhabited ρ)
    (h : ¬ OutRef USet.Sub (semU w ρ tgt) (semU w ρ src)) : ¬ RefinesU w tgt src :=
  fun H => h (H ρ hρ)

theorem not_refinesP_of_env {w : Nat} {tgt src : Expr} (ρ : Var → PVal w)
    (h : ¬ OutRef PVal.Refines (semP w ρ tgt) (semP w ρ src)) : ¬ RefinesP w tgt src :=
  fun H => h (H ρ)

theorem uConst0_inhabited : UInhabited (fun _ => USet.single 0#2 : Var → USet 2) :=
  fun _ => ⟨0#2, by simp [USet.single]⟩

/-- Each premise (`ha`, `hb`, in order) of `refinesU_congr_add` is needed: for each, a
width-2 instance with the other premises true and the conclusion false. -/
theorem refinesU_congr_add_premises_tight :
    (RefinesU 2 (.const 0) (.const 0) ∧ ¬ RefinesU 2 (.add (.const 1) (.const 0)) (.add (.const 0) (.const 0))) ∧
    (RefinesU 2 (.const 0) (.const 0) ∧ ¬ RefinesU 2 (.add (.const 0) (.const 1)) (.add (.const 0) (.const 0))) :=
  ⟨⟨refinesU_refl 2 _, not_refinesU_of_env (fun _ => USet.single 0#2) uConst0_inhabited (by decide)⟩, ⟨refinesU_refl 2 _, not_refinesU_of_env (fun _ => USet.single 0#2) uConst0_inhabited (by decide)⟩⟩

/-- Each premise (`ha`, `hb`, in order) of `refinesU_congr_mul` is needed: for each, a
width-2 instance with the other premises true and the conclusion false. -/
theorem refinesU_congr_mul_premises_tight :
    (RefinesU 2 (.const 1) (.const 1) ∧ ¬ RefinesU 2 (.mul (.const 1) (.const 1)) (.mul (.const 0) (.const 1))) ∧
    (RefinesU 2 (.const 1) (.const 1) ∧ ¬ RefinesU 2 (.mul (.const 1) (.const 1)) (.mul (.const 1) (.const 0))) :=
  ⟨⟨refinesU_refl 2 _, not_refinesU_of_env (fun _ => USet.single 0#2) uConst0_inhabited (by decide)⟩, ⟨refinesU_refl 2 _, not_refinesU_of_env (fun _ => USet.single 0#2) uConst0_inhabited (by decide)⟩⟩

/-- Each premise (`ha`, `hb`, in order) of `refinesU_congr_eq` is needed: for each, a
width-2 instance with the other premises true and the conclusion false. -/
theorem refinesU_congr_eq_premises_tight :
    (RefinesU 2 (.const 0) (.const 0) ∧ ¬ RefinesU 2 (.eq (.const 1) (.const 0)) (.eq (.const 0) (.const 0))) ∧
    (RefinesU 2 (.const 0) (.const 0) ∧ ¬ RefinesU 2 (.eq (.const 0) (.const 1)) (.eq (.const 0) (.const 0))) :=
  ⟨⟨refinesU_refl 2 _, not_refinesU_of_env (fun _ => USet.single 0#2) uConst0_inhabited (by decide)⟩, ⟨refinesU_refl 2 _, not_refinesU_of_env (fun _ => USet.single 0#2) uConst0_inhabited (by decide)⟩⟩

/-- Each premise (`hc`, `ht`, `he`, in order) of `refinesU_congr_ite` is needed: for each, a
width-2 instance with the other premises true and the conclusion false. -/
theorem refinesU_congr_ite_premises_tight :
    (RefinesU 2 (.const 1) (.const 1) ∧ RefinesU 2 (.const 0) (.const 0) ∧ ¬ RefinesU 2 (.ite (.const 1) (.const 1) (.const 0)) (.ite (.const 0) (.const 1) (.const 0))) ∧
    (RefinesU 2 (.const 1) (.const 1) ∧ RefinesU 2 (.const 0) (.const 0) ∧ ¬ RefinesU 2 (.ite (.const 1) (.const 1) (.const 0)) (.ite (.const 1) (.const 0) (.const 0))) ∧
    (RefinesU 2 (.const 0) (.const 0) ∧ RefinesU 2 (.const 0) (.const 0) ∧ ¬ RefinesU 2 (.ite (.const 0) (.const 0) (.const 1)) (.ite (.const 0) (.const 0) (.const 0))) :=
  ⟨⟨refinesU_refl 2 _, refinesU_refl 2 _, not_refinesU_of_env (fun _ => USet.single 0#2) uConst0_inhabited (by decide)⟩, ⟨refinesU_refl 2 _, refinesU_refl 2 _, not_refinesU_of_env (fun _ => USet.single 0#2) uConst0_inhabited (by decide)⟩, ⟨refinesU_refl 2 _, refinesU_refl 2 _, not_refinesU_of_env (fun _ => USet.single 0#2) uConst0_inhabited (by decide)⟩⟩

/-- Each premise (`ha`, `hb`, in order) of `refinesU_congr_letE` is needed: for each, a
width-2 instance with the other premises true and the conclusion false. -/
theorem refinesU_congr_letE_premises_tight :
    (RefinesU 2 (.var 0) (.var 0) ∧ ¬ RefinesU 2 (.letE 0 (.const 1) (.var 0)) (.letE 0 (.const 0) (.var 0))) ∧
    (RefinesU 2 (.const 0) (.const 0) ∧ ¬ RefinesU 2 (.letE 0 (.const 0) (.const 1)) (.letE 0 (.const 0) (.const 0))) :=
  ⟨⟨refinesU_refl 2 _, not_refinesU_of_env (fun _ => USet.single 0#2) uConst0_inhabited (by decide)⟩, ⟨refinesU_refl 2 _, not_refinesU_of_env (fun _ => USet.single 0#2) uConst0_inhabited (by decide)⟩⟩

/-- Each premise (`ha`, in order) of `refinesU_congr_freeze` is needed: for each, a
width-2 instance with the other premises true and the conclusion false. -/
theorem refinesU_congr_freeze_premises_tight :
    (¬ RefinesU 2 (.freeze (.const 1)) (.freeze (.const 0))) :=
  not_refinesU_of_env (fun _ => USet.single 0#2) uConst0_inhabited (by decide)

/-- Each premise (`ha`, `hb`, in order) of `refinesP_congr_add` is needed: for each, a
width-2 instance with the other premises true and the conclusion false. -/
theorem refinesP_congr_add_premises_tight :
    (RefinesP 2 (.const 0) (.const 0) ∧ ¬ RefinesP 2 (.add (.const 1) (.const 0)) (.add (.const 0) (.const 0))) ∧
    (RefinesP 2 (.const 0) (.const 0) ∧ ¬ RefinesP 2 (.add (.const 0) (.const 1)) (.add (.const 0) (.const 0))) :=
  ⟨⟨refinesP_refl 2 _, not_refinesP_of_env (fun _ => .int 0#2) (by decide)⟩, ⟨refinesP_refl 2 _, not_refinesP_of_env (fun _ => .int 0#2) (by decide)⟩⟩

/-- Each premise (`ha`, `hb`, in order) of `refinesP_congr_mul` is needed: for each, a
width-2 instance with the other premises true and the conclusion false. -/
theorem refinesP_congr_mul_premises_tight :
    (RefinesP 2 (.const 1) (.const 1) ∧ ¬ RefinesP 2 (.mul (.const 1) (.const 1)) (.mul (.const 0) (.const 1))) ∧
    (RefinesP 2 (.const 1) (.const 1) ∧ ¬ RefinesP 2 (.mul (.const 1) (.const 1)) (.mul (.const 1) (.const 0))) :=
  ⟨⟨refinesP_refl 2 _, not_refinesP_of_env (fun _ => .int 0#2) (by decide)⟩, ⟨refinesP_refl 2 _, not_refinesP_of_env (fun _ => .int 0#2) (by decide)⟩⟩

/-- Each premise (`ha`, `hb`, in order) of `refinesP_congr_eq` is needed: for each, a
width-2 instance with the other premises true and the conclusion false. -/
theorem refinesP_congr_eq_premises_tight :
    (RefinesP 2 (.const 0) (.const 0) ∧ ¬ RefinesP 2 (.eq (.const 1) (.const 0)) (.eq (.const 0) (.const 0))) ∧
    (RefinesP 2 (.const 0) (.const 0) ∧ ¬ RefinesP 2 (.eq (.const 0) (.const 1)) (.eq (.const 0) (.const 0))) :=
  ⟨⟨refinesP_refl 2 _, not_refinesP_of_env (fun _ => .int 0#2) (by decide)⟩, ⟨refinesP_refl 2 _, not_refinesP_of_env (fun _ => .int 0#2) (by decide)⟩⟩

/-- Each premise (`hc`, `ht`, `he`, in order) of `refinesP_congr_ite` is needed: for each, a
width-2 instance with the other premises true and the conclusion false. -/
theorem refinesP_congr_ite_premises_tight :
    (RefinesP 2 (.const 1) (.const 1) ∧ RefinesP 2 (.const 0) (.const 0) ∧ ¬ RefinesP 2 (.ite (.const 1) (.const 1) (.const 0)) (.ite (.const 0) (.const 1) (.const 0))) ∧
    (RefinesP 2 (.const 1) (.const 1) ∧ RefinesP 2 (.const 0) (.const 0) ∧ ¬ RefinesP 2 (.ite (.const 1) (.const 1) (.const 0)) (.ite (.const 1) (.const 0) (.const 0))) ∧
    (RefinesP 2 (.const 0) (.const 0) ∧ RefinesP 2 (.const 0) (.const 0) ∧ ¬ RefinesP 2 (.ite (.const 0) (.const 0) (.const 1)) (.ite (.const 0) (.const 0) (.const 0))) :=
  ⟨⟨refinesP_refl 2 _, refinesP_refl 2 _, not_refinesP_of_env (fun _ => .int 0#2) (by decide)⟩, ⟨refinesP_refl 2 _, refinesP_refl 2 _, not_refinesP_of_env (fun _ => .int 0#2) (by decide)⟩, ⟨refinesP_refl 2 _, refinesP_refl 2 _, not_refinesP_of_env (fun _ => .int 0#2) (by decide)⟩⟩

/-- Each premise (`ha`, `hb`, in order) of `refinesP_congr_letE` is needed: for each, a
width-2 instance with the other premises true and the conclusion false. -/
theorem refinesP_congr_letE_premises_tight :
    (RefinesP 2 (.var 0) (.var 0) ∧ ¬ RefinesP 2 (.letE 0 (.const 1) (.var 0)) (.letE 0 (.const 0) (.var 0))) ∧
    (RefinesP 2 (.const 0) (.const 0) ∧ ¬ RefinesP 2 (.letE 0 (.const 0) (.const 1)) (.letE 0 (.const 0) (.const 0))) :=
  ⟨⟨refinesP_refl 2 _, not_refinesP_of_env (fun _ => .int 0#2) (by decide)⟩, ⟨refinesP_refl 2 _, not_refinesP_of_env (fun _ => .int 0#2) (by decide)⟩⟩

/-- Each premise (`ha`, in order) of `refinesP_congr_freeze` is needed: for each, a
width-2 instance with the other premises true and the conclusion false. -/
theorem refinesP_congr_freeze_premises_tight :
    (¬ RefinesP 2 (.freeze (.const 1)) (.freeze (.const 0))) :=
  not_refinesP_of_env (fun _ => .int 0#2) (by decide)

/-- Premise `hbc` of `refinesU_trans` is needed: `a = b = x` satisfies `hab`, and `x` does
not refine `c = freeze x` (width 2). -/
theorem refinesU_trans_needs_hbc :
    RefinesU 2 (.var 0) (.var 0) ∧ ¬ RefinesU 2 (.var 0) (.freeze (.var 0)) :=
  ⟨refinesU_refl 2 _, undef_remove_freeze_unsound 2 (by decide) 0⟩

/-- Premise `hab` of `refinesU_trans` is needed: `b = c = freeze x` satisfies `hbc`, and
`a = x` does not refine `c` (width 2). -/
theorem refinesU_trans_needs_hab :
    RefinesU 2 (.freeze (.var 0)) (.freeze (.var 0)) ∧ ¬ RefinesU 2 (.var 0) (.freeze (.var 0)) :=
  ⟨refinesU_refl 2 _, undef_remove_freeze_unsound 2 (by decide) 0⟩

/-- Premise `hbc` of `refinesP_trans` is needed (width 2). -/
theorem refinesP_trans_needs_hbc :
    RefinesP 2 (.var 0) (.var 0) ∧ ¬ RefinesP 2 (.var 0) (.freeze (.var 0)) :=
  ⟨refinesP_refl 2 _, poisonFreeze_remove_freeze_unsound 2 0⟩

/-- Premise `hab` of `refinesP_trans` is needed (width 2). -/
theorem refinesP_trans_needs_hab :
    RefinesP 2 (.freeze (.var 0)) (.freeze (.var 0)) ∧ ¬ RefinesP 2 (.var 0) (.freeze (.var 0)) :=
  ⟨refinesP_refl 2 _, poisonFreeze_remove_freeze_unsound 2 0⟩

/-- The premise of `refinesU_of_src_mayUB` is needed: the UB-free source `freeze x` is not
refined by every target (width 2). -/
theorem refinesU_of_src_mayUB_needs_mayUB : ¬ ∀ tgt, RefinesU 2 tgt (.freeze (.var 0)) :=
  fun h => undef_remove_freeze_unsound 2 (by decide) 0 (h _)

/-- The premise of `refinesP_of_src_mayUB` is needed: the UB-free source `freeze x` is not
refined by every target (width 2). -/
theorem refinesP_of_src_mayUB_needs_mayUB : ¬ ∀ tgt, RefinesP 2 tgt (.freeze (.var 0)) :=
  fun h => poisonFreeze_remove_freeze_unsound 2 0 (h _)

/-! ### Canonical tightness statements for width and distinctness hypotheses

Each theorem below concerns one hypothesis (`1 ≤ w`, `x ≠ y`, or `c ≠ d`) of an
unsoundness result: in a concrete instance all *other* hypotheses hold and the result's
conclusion fails. (For a conclusion of the form `¬ R`, failing means `¬ ¬ R`; each is
derived from the corresponding positive control, which proves `R` itself.) -/

/-- `1 ≤ w` of `undef_obsRefines_not_congruence_letE` (its only hypothesis besides the
variables): at width `0`, `x = 0`, `y = 1`, the conclusion fails. -/
theorem undef_obsRefines_not_congruence_letE_needs_width :
    ¬ (ObsRefinesU 0 (.var 0) (.freeze (.var 0)) ∧
        ¬ ObsRefinesU 0 (.letE 1 (.var 0) (.add (.var 1) (.var 1)))
            (.letE 1 (.freeze (.var 0)) (.add (.var 1) (.var 1)))) :=
  fun ⟨_, hnot⟩ => hnot (undef_obsRefines_letE_width_zero 0 1)

/-- `1 ≤ w` of `undef_rewrite_two_mul_to_add_self_unsound`: at width `0` the conclusion fails. -/
theorem undef_rewrite_two_mul_to_add_self_unsound_needs_width :
    ¬ ¬ RefinesU 0 (.add (.var 0) (.var 0)) (.mul (.const 2) (.var 0)) :=
  fun h => h (undef_rewrite_two_mul_to_add_self_sound_width_zero 0)

/-- `1 ≤ w` of `poisonFreeze_rewrite_two_mul_to_add_self_unsound`: at width `0` the
conclusion fails. -/
theorem poisonFreeze_rewrite_two_mul_to_add_self_unsound_needs_width :
    ¬ ¬ RefinesP 0 (.add (.freeze (.var 0)) (.freeze (.var 0)))
        (.mul (.const 2) (.freeze (.var 0))) :=
  fun h => h (poisonFreeze_rewrite_two_mul_to_add_self_sound_width_zero 0)

/-- `1 ≤ w` of `undef_gvn_var_branch_distinct_vars_unsound`: at width `0` the other
hypothesis `0 ≠ 1` holds and the conclusion fails. -/
theorem undef_gvn_var_branch_distinct_vars_unsound_needs_width :
    (0 : Var) ≠ 1 ∧
    ¬ ¬ RefinesU 0 (.ite (.eq (.var 0) (.var 1)) (.letE 1 (.var 0) (.var 1)) (.const 0))
        (.ite (.eq (.var 0) (.var 1)) (.var 1) (.const 0)) :=
  ⟨by decide, fun h => h (undef_gvn_sound_width_zero 0 1)⟩

/-- `x ≠ y` of `undef_gvn_var_branch_distinct_vars_unsound`: with `x = y = 0` at width `2`
the other hypothesis `1 ≤ 2` holds and the conclusion fails. -/
theorem undef_gvn_var_branch_distinct_vars_unsound_needs_distinct :
    1 ≤ 2 ∧
    ¬ ¬ RefinesU 2 (.ite (.eq (.var 0) (.var 0)) (.letE 0 (.var 0) (.var 0)) (.const 0))
        (.ite (.eq (.var 0) (.var 0)) (.var 0) (.const 0)) :=
  ⟨by decide, fun h => h (undef_gvn_sound_of_same_var 2 0)⟩

/-- `c ≠ d` of `poison_unswitch_without_freeze_distinct_vars_unsound` (its only hypothesis):
with `c = d = 2`, `a = 1`, `b = 2`, `n = 0` at width `2` the conclusion fails. -/
theorem poison_unswitch_without_freeze_distinct_vars_unsound_needs_distinct :
    ¬ ¬ RefinesP 2
        (.ite (.var 2) (.ite (.var 2) (.const 1) (.const 0)) (.ite (.var 2) (.const 2) (.const 0)))
        (.ite (.var 2) (.ite (.var 2) (.const 1) (.const 2)) (.const 0)) :=
  fun h => h (poison_unswitch_without_freeze_sound_of_same_var 2 2 _ _ _)

/-- `1 ≤ w` of `undef_remove_freeze_unsound`: at width `0` the conclusion fails. -/
theorem undef_remove_freeze_unsound_needs_width :
    ¬ ¬ RefinesU 0 (.var 0) (.freeze (.var 0)) :=
  fun h => h (undef_remove_freeze_sound_width_zero 0)

/-- `1 ≤ w` of `poisonFreeze_freeze_add_freeze_can_be_odd`: at width `0` the conclusion
fails. -/
theorem poisonFreeze_freeze_add_freeze_can_be_odd_needs_width :
    ¬ ∃ ρ : Var → PVal 0, ∃ v : BitVec 0,
        Outcome.val (PVal.int v) ∈ semP 0 ρ (.add (.freeze (.var 0)) (.freeze (.var 0))) ∧
        v.toNat % 2 = 1 := by
  rintro ⟨ρ, v, hmem, hodd⟩
  have heven := poisonFreeze_freeze_add_freeze_even_width_zero 0 ρ v hmem
  omega

/-- `1 ≤ w` of `poisonFreeze_duplicate_freeze_unsound`: at width `0` the conclusion fails. -/
theorem poisonFreeze_duplicate_freeze_unsound_needs_width :
    ¬ ¬ RefinesP 0 (.add (.freeze (.var 0)) (.freeze (.var 0)))
        (.letE 1 (.freeze (.var 0)) (.add (.var 1) (.var 1))) :=
  fun h => h (poisonFreeze_duplicate_freeze_sound_width_zero 0 1)

/-- `he : e.FreezeFree = true` of `poison_rewrite_two_mul_to_add_self_sound_of_freezeFree`
(its only hypothesis): for `e = freeze x` at width `2` the hypothesis fails and so does the
conclusion. -/
theorem poison_rewrite_two_mul_to_add_self_needs_freezeFree :
    (Expr.freeze (.var 0)).FreezeFree = false ∧
    ¬ RefinesP 2 (.add (.freeze (.var 0)) (.freeze (.var 0))) (.mul (.const 2) (.freeze (.var 0))) :=
  ⟨by decide, poisonFreeze_rewrite_two_mul_to_add_self_unsound 2 (by decide) 0⟩

/-- The hypothesis of `poisonFreeze_freeze_eq_self_of_no_poison` (its only hypothesis):
with `e = x` and `x ↦ poison`, `e` has a `poison` outcome and the conclusion fails. -/
theorem poisonFreeze_freeze_eq_self_needs_no_poison :
    Outcome.val PVal.poison ∈ semP 2 (fun _ => .poison) (.var 0) ∧
    semP 2 (fun _ => .poison) (.freeze (.var 0)) ≠ semP 2 (fun _ => .poison) (.var 0) :=
  ⟨by decide, poisonFreeze_freeze_ne_self_of_poison 2 0⟩

/-- The hypothesis of `poisonFreeze_remove_freeze_sound_of_no_poison` (its only hypothesis):
for `e = x` some environment gives a `poison` outcome, and the conclusion fails. -/
theorem poisonFreeze_remove_freeze_needs_no_poison :
    ¬ (∀ ρ : Var → PVal 2, Outcome.val PVal.poison ∉ semP 2 ρ (.var 0)) ∧
    ¬ RefinesP 2 (.var 0) (.freeze (.var 0)) :=
  ⟨fun h => h (fun _ => .poison) (by decide), poisonFreeze_remove_freeze_unsound 2 0⟩

/-- "Never poison" is not an escape hatch for duplicating a `freeze` of a compound operand:
`e = freeze y` never yields `poison`, yet rewriting `let a := freeze e; a + a` to
`freeze e + freeze e` is not a refinement at width 2 (with `y ↦ poison` the two copies of
`e` may differ). -/
theorem poisonFreeze_duplicate_freeze_of_nonpoison_compound_unsound :
    (∀ ρ : Var → PVal 2, Outcome.val PVal.poison ∉ semP 2 ρ (.freeze (.var 1))) ∧
    ¬ RefinesP 2 (.add (.freeze (.freeze (.var 1))) (.freeze (.freeze (.var 1))))
        (.letE 5 (.freeze (.freeze (.var 1))) (.add (.var 5) (.var 5))) :=
  ⟨fun ρ => poison_not_mem_semP_freeze 2 ρ (.var 1),
    not_refinesP_of_env (fun _ => .poison) (by decide)⟩

end Toy.UB
