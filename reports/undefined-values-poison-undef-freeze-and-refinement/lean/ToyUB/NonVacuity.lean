import ToyUB.Refinement
import ToyUB.GVN
import ToyUB.Unswitch
import ToyUB.Freeze
import ToyUB.Uninit

/-!
# Non-vacuity witnesses

For every result: a concrete instance in which all of its hypotheses hold. For results
without hypotheses beyond the width and the program parameters, the witness is a concrete
instantiation.
-/

namespace Toy.UB

open Expr

/-- The premises of the transitivity theorems hold together non-trivially (width 2):
`freeze (2 * x) ⊑ 2 * x ⊑ x + x` in the undef model. -/
theorem nonvacuity_refinesU_trans :
    RefinesU 2 (.freeze (.mul (.const 2) (.var 0))) (.mul (.const 2) (.var 0)) ∧
    RefinesU 2 (.mul (.const 2) (.var 0)) (.add (.var 0) (.var 0)) :=
  ⟨undef_insert_freeze_sound 2 _, undef_rewrite_add_self_to_two_mul_sound 2 _⟩

/-- The premises of the transitivity theorems hold together non-trivially (width 2):
`freeze (2 * x) ⊑ 2 * x ⊑ x + x` in the poison model. -/
theorem nonvacuity_refinesP_trans :
    RefinesP 2 (.freeze (.mul (.const 2) (.var 0))) (.mul (.const 2) (.var 0)) ∧
    RefinesP 2 (.mul (.const 2) (.var 0)) (.add (.var 0) (.var 0)) :=
  ⟨poisonFreeze_insert_freeze_sound 2 _, poison_rewrite_add_self_to_two_mul_sound 2 _⟩

/-- A source that reaches UB in every environment (undef model, width 2): `x + ub`. -/
theorem nonvacuity_refinesU_of_src_mayUB :
    ∀ ρ : Var → USet 2, UInhabited ρ → MayUB (semU 2 ρ (.add (.var 0) .ub)) :=
  fun _ _ => mayUB_iff.mpr (by simp [semU, bind2])

/-- A source that reaches UB in every environment (poison model, width 2):
`if x then ub else ub` (UB on either branch, and UB when `x` is `poison`). -/
theorem nonvacuity_refinesP_of_src_mayUB :
    ∀ ρ : Var → PVal 2, MayUB (semP 2 ρ (.ite (.var 0) .ub .ub)) := by
  intro ρ
  rw [mayUB_iff]
  cases h : ρ 0 with
  | poison => simp [semP, h]
  | int z => by_cases hz : z = 0#2 <;> simp [semP, h, hz]

/-- Three non-trivial refining pairs (undef model, width 2), usable as the premises of
every congruence theorem: `2 * x ⊑ x + x`, `freeze y ⊑ y`, `7 ⊑ ub`. -/
theorem nonvacuity_refinesU_congr :
    RefinesU 2 (.mul (.const 2) (.var 0)) (.add (.var 0) (.var 0)) ∧
    RefinesU 2 (.freeze (.var 1)) (.var 1) ∧ RefinesU 2 (.const 7) .ub :=
  ⟨undef_rewrite_add_self_to_two_mul_sound 2 _, undef_insert_freeze_sound 2 _,
    refinesU_ub 2 _⟩

/-- Three non-trivial refining pairs (poison model, width 2), usable as the premises of
every congruence theorem: `2 * x ⊑ x + x`, `freeze y ⊑ y`, `7 ⊑ ub`. -/
theorem nonvacuity_refinesP_congr :
    RefinesP 2 (.mul (.const 2) (.var 0)) (.add (.var 0) (.var 0)) ∧
    RefinesP 2 (.freeze (.var 1)) (.var 1) ∧ RefinesP 2 (.const 7) .ub :=
  ⟨poison_rewrite_add_self_to_two_mul_sound 2 _, poisonFreeze_insert_freeze_sound 2 _,
    refinesP_ub 2 _⟩

/-- Hypotheses of `undef_obsRefines_not_congruence_letE` hold: width 2. -/
theorem nonvacuity_width_two : 1 ≤ 2 := by decide

/-- Instance of `undef_obsRefines_not_congruence_letE` at width 2 with `x = 0`, `y = 1`. -/
theorem nonvacuity_undef_obsRefines_not_congruence_letE :
    ObsRefinesU 2 (.var 0) (.freeze (.var 0)) ∧
    ¬ ObsRefinesU 2 (.letE 1 (.var 0) (.add (.var 1) (.var 1)))
        (.letE 1 (.freeze (.var 0)) (.add (.var 1) (.var 1))) :=
  undef_obsRefines_not_congruence_letE 2 (by decide) 0 1

/-- Instance of `undef_rewrite_two_mul_to_add_self_unsound` at width 2, `x = 0`. -/
theorem nonvacuity_undef_rewrite_two_mul_to_add_self_unsound :
    ¬ RefinesU 2 (.add (.var 0) (.var 0)) (.mul (.const 2) (.var 0)) :=
  undef_rewrite_two_mul_to_add_self_unsound 2 (by decide) 0

/-- Instance of `poisonFreeze_rewrite_two_mul_to_add_self_unsound` at width 2, `x = 0`. -/
theorem nonvacuity_poisonFreeze_rewrite_two_mul_to_add_self_unsound :
    ¬ RefinesP 2 (.add (.freeze (.var 0)) (.freeze (.var 0))) (.mul (.const 2) (.freeze (.var 0))) :=
  poisonFreeze_rewrite_two_mul_to_add_self_unsound 2 (by decide) 0

/-- Instance of `undef_rewrite_add_self_to_two_mul_sound` with a non-variable operand
(width 3, `e = if x then y else freeze y`). -/
theorem nonvacuity_undef_rewrite_add_self_to_two_mul_sound :
    RefinesU 3 (.mul (.const 2) (.ite (.var 0) (.var 1) (.freeze (.var 1))))
      (.add (.ite (.var 0) (.var 1) (.freeze (.var 1))) (.ite (.var 0) (.var 1) (.freeze (.var 1)))) :=
  undef_rewrite_add_self_to_two_mul_sound 3 _

/-- Instance of `poison_rewrite_add_self_to_two_mul_sound` with a nondeterministic operand
(width 3, `e = freeze x`). -/
theorem nonvacuity_poison_rewrite_add_self_to_two_mul_sound :
    RefinesP 3 (.mul (.const 2) (.freeze (.var 0))) (.add (.freeze (.var 0)) (.freeze (.var 0))) :=
  poison_rewrite_add_self_to_two_mul_sound 3 _

/-- The hypothesis of `poison_rewrite_two_mul_to_add_self_sound_of_freezeFree` holds for a
non-trivial program `if x then x + y else ub`. -/
theorem nonvacuity_freezeFree :
    (Expr.ite (.var 0) (.add (.var 0) (.var 1)) .ub).FreezeFree = true := by decide

/-- Hypotheses of `undef_gvn_var_branch_distinct_vars_unsound` hold: width 2, variables `0 ≠ 1`. -/
theorem nonvacuity_undef_gvn : 1 ≤ 2 ∧ (0 : Var) ≠ 1 := by decide

/-- Instance of `undef_gvn_var_branch_distinct_vars_unsound` at width 2, `x = 0`, `y = 1`. -/
theorem nonvacuity_undef_gvn_instance :
    ¬ RefinesU 2 (.ite (.eq (.var 0) (.var 1)) (.letE 1 (.var 0) (.var 1)) (.const 0))
        (.ite (.eq (.var 0) (.var 1)) (.var 1) (.const 0)) :=
  undef_gvn_var_branch_distinct_vars_unsound 2 (by decide) 0 1 (by decide)

/-- Instance of `poison_gvn_sound` with a `then`-branch using `y` twice and under `freeze`
(width 2). -/
theorem nonvacuity_poison_gvn_sound :
    RefinesP 2 (.ite (.eq (.var 0) (.var 1)) (.letE 1 (.var 0) (.add (.var 1) (.freeze (.var 1))))
        (.var 1))
      (.ite (.eq (.var 0) (.var 1)) (.add (.var 1) (.freeze (.var 1))) (.var 1)) :=
  poison_gvn_sound 2 0 1 _ _

/-- Hypothesis of `poison_unswitch_without_freeze_distinct_vars_unsound` holds: `2 ≠ 3`. -/
theorem nonvacuity_poison_unswitch : (2 : Var) ≠ 3 := by decide

/-- Instance of `poison_unswitch_without_freeze_distinct_vars_unsound` at width 2 with
`c = 2`, `d = 3`, branches mentioning both conditions, and else-branch `7`. -/
theorem nonvacuity_poison_unswitch_instance :
    ¬ RefinesP 2
        (.ite (.var 3) (.ite (.var 2) (.var 3) (.const 7)) (.ite (.var 2) (.add (.var 2) (.var 3)) (.const 7)))
        (.ite (.var 2) (.ite (.var 3) (.var 3) (.add (.var 2) (.var 3))) (.const 7)) :=
  poison_unswitch_without_freeze_distinct_vars_unsound 2 2 3 (by decide) _ _ 7

/-- Hypothesis and instance of `undef_unswitch_without_freeze_sound_of_ubFree` with a
compound inner condition (`if d then 1 else 0`) and a compound outer condition (`c = x`),
width 2. -/
theorem nonvacuity_undef_unswitch_of_ubFree :
    UBFreeU 2 (.ite (.var 3) (.const 1) (.const 0)) ∧
    RefinesU 2
      (.ite (.ite (.var 3) (.const 1) (.const 0))
        (.ite (.eq (.var 2) (.var 4)) (.var 3) (.freeze (.var 2)))
        (.ite (.eq (.var 2) (.var 4)) (.add (.var 2) (.var 3)) (.freeze (.var 2))))
      (.ite (.eq (.var 2) (.var 4))
        (.ite (.ite (.var 3) (.const 1) (.const 0)) (.var 3) (.add (.var 2) (.var 3)))
        (.freeze (.var 2))) :=
  ⟨ubFreeU_ite_var_const 2 3 1 0,
    undef_unswitch_without_freeze_sound_of_ubFree 2 _ _ _ _ _ (ubFreeU_ite_var_const 2 3 1 0)⟩

/-- Hypotheses and instance of `poisonFreeze_unswitch_with_freeze_sound_of_ubFree` with
compound conditions: outer `x = y`, inner `d = z` (UB-free), `t = 4`, branches `d`,
`c + d`, `freeze c` (width 2). -/
theorem nonvacuity_poisonFreeze_unswitch_of_ubFree :
    UBFreeP 2 (.eq (.var 3) (.var 5)) ∧ (Expr.eq (.var 0) (.var 1)).freeIn 4 = false ∧
    (Expr.var 3).freeIn 4 = false ∧ (Expr.add (.var 2) (.var 3)).freeIn 4 = false ∧
    (Expr.freeze (.var 2)).freeIn 4 = false ∧
    RefinesP 2
      (.letE 4 (.freeze (.eq (.var 3) (.var 5)))
        (.ite (.var 4) (.ite (.eq (.var 0) (.var 1)) (.var 3) (.freeze (.var 2)))
          (.ite (.eq (.var 0) (.var 1)) (.add (.var 2) (.var 3)) (.freeze (.var 2)))))
      (.ite (.eq (.var 0) (.var 1)) (.ite (.eq (.var 3) (.var 5)) (.var 3) (.add (.var 2) (.var 3)))
        (.freeze (.var 2))) :=
  ⟨ubFreeP_eq_var 2 3 5, by decide, by decide, by decide, by decide,
    poisonFreeze_unswitch_with_freeze_sound_of_ubFree 2 _ _ 4 _ _ _ (ubFreeP_eq_var 2 3 5)
      (by decide) (by decide) (by decide) (by decide)⟩

/-- Instance of `undef_unswitch_without_freeze_sound` where the branches mention both
conditions (width 2). -/
theorem nonvacuity_undef_unswitch :
    RefinesU 2 (.ite (.var 3) (.ite (.var 2) (.var 3) (.freeze (.var 2)))
        (.ite (.var 2) (.add (.var 2) (.var 3)) (.freeze (.var 2))))
      (.ite (.var 2) (.ite (.var 3) (.var 3) (.add (.var 2) (.var 3))) (.freeze (.var 2))) :=
  undef_unswitch_without_freeze_sound 2 2 3 _ _ _

/-- Hypotheses of `poisonFreeze_unswitch_with_freeze_sound_of_fresh` hold with branches
that mention both conditions: `c = 2`, `d = 3`, `t = 4`, `a = d`, `b = c + d`,
`e = freeze c`. -/
theorem nonvacuity_poisonFreeze_unswitch :
    (4 : Var) ≠ 2 ∧ (Expr.var 3).freeIn 4 = false ∧ (Expr.add (.var 2) (.var 3)).freeIn 4 = false ∧
    (Expr.freeze (.var 2)).freeIn 4 = false := by decide

/-- Hypothesis of `poisonFreeze_freeze_eq_self_of_no_poison` holds: `x + 1` with `x ↦ 1`
has no `poison` outcome (width 2). -/
theorem nonvacuity_freeze_eq_self :
    Outcome.val PVal.poison ∉ semP 2 (fun _ => .int 1#2) (.add (.var 0) (.const 1)) := by decide

/-- Instance of `poisonFreeze_insert_freeze_sound` and `undef_insert_freeze_sound` on a
program that may reach UB in some environments (width 2). -/
theorem nonvacuity_insert_freeze :
    RefinesP 2 (.freeze (.ite (.var 0) (.var 1) .ub)) (.ite (.var 0) (.var 1) .ub) ∧
    RefinesU 2 (.freeze (.ite (.var 0) (.var 1) .ub)) (.ite (.var 0) (.var 1) .ub) :=
  ⟨poisonFreeze_insert_freeze_sound 2 _, undef_insert_freeze_sound 2 _⟩

/-- Instance of `poisonFreeze_merge_freeze_sound` with a nondeterministic operand (width 2). -/
theorem nonvacuity_merge_freeze :
    RefinesP 2 (.letE 5 (.freeze (.freeze (.var 0))) (.add (.var 5) (.var 5)))
      (.add (.freeze (.freeze (.var 0))) (.freeze (.freeze (.var 0)))) :=
  poisonFreeze_merge_freeze_sound 2 _ 5

/-- Instance of `poison_refines_eagerUninit` with one initialised and one uninitialised
input (width 2). -/
theorem nonvacuity_poison_refines_eagerUninit :
    OutRef PVal.Refines
      (semP 2 (toPoisonEnv fun v => if v = 0 then some 1#2 else none) (.ite (.var 0) (.const 3) (.var 1)))
      ((semE 2 (fun v => if v = 0 then some 1#2 else none) (.ite (.var 0) (.const 3) (.var 1))).map
        Outcome.toP) :=
  poison_refines_eagerUninit 2 _ _

/-- Instance of the totality lemmas (width 2) on a program with branching on a frozen
value and a `ub` branch, and of the `OutRefNE` equivalence on a concrete refining pair. -/
theorem nonvacuity_semantics_total :
    semP 2 (fun _ => .poison) (.ite (.freeze (.var 0)) (.var 1) .ub) ≠ [] ∧
    semU 2 (fun _ => USet.single 0#2) (.ite (.freeze (.var 0)) (.var 1) .ub) ≠ [] ∧
    (∀ ρ : Var → PVal 2, OutRefNE PVal.Refines (semP 2 ρ (.mul (.const 2) (.var 0)))
      (semP 2 ρ (.add (.var 0) (.var 0)))) :=
  ⟨semP_ne_nil 2 _ _, semU_ne_nil 2 _ _ (fun _ => ⟨0#2, by simp [USet.single]⟩),
    (refinesP_iff_outRefNE 2 _ _).mp (poison_rewrite_add_self_to_two_mul_sound 2 (.var 0))⟩

/-- Instances of the redundant-`freeze` elimination corollaries (width 2), and the
hypothesis of `poisonFreeze_remove_freeze_sound_of_no_poison` for `e = freeze x + 1`. -/
theorem nonvacuity_remove_redundant_freeze :
    RefinesP 2 (.freeze (.var 0)) (.freeze (.freeze (.var 0))) ∧
    RefinesU 2 (.freeze (.var 0)) (.freeze (.freeze (.var 0))) ∧
    (∀ ρ : Var → PVal 2,
      Outcome.val PVal.poison ∉ semP 2 ρ (.add (.freeze (.var 0)) (.const 1))) := by
  refine ⟨poisonFreeze_remove_redundant_freeze_sound 2 _, undef_remove_redundant_freeze_sound 2 _,
    fun ρ h => ?_⟩
  have h' : Outcome.val PVal.poison ∈ bind1 (semP 2 ρ (.freeze (.var 0))) (fun u =>
      bind1 (semP 2 ρ (.const 1)) (fun v => [.val (PVal.lift2 (· + ·) u v)])) := h
  rcases mem_bind1.mp h' with ⟨h1, _⟩ | ⟨v, hv, h2⟩
  · cases h1
  · cases v with
    | poison => exact poison_not_mem_semP_freeze 2 ρ (.var 0) hv
    | int u => simp [semP, PVal.lift2] at h2

/-- Instances of both parts of `freeze-removal-unsound` (width 2, `x = 0`). -/
theorem nonvacuity_remove_freeze_unsound :
    ¬ RefinesP 2 (.var 0) (.freeze (.var 0)) ∧ ¬ RefinesU 2 (.var 0) (.freeze (.var 0)) :=
  ⟨poisonFreeze_remove_freeze_unsound 2 0, undef_remove_freeze_unsound 2 (by decide) 0⟩

/-- Membership witnesses for `frozen-value-used-twice-even`: with `x ↦ poison` (width 2),
`let a := freeze x; a + a` has the outcome `2`, and `freeze x + freeze x` has an odd
outcome. -/
theorem nonvacuity_let_freeze_mem :
    Outcome.val (PVal.int 2#2) ∈ semP 2 ρP (.letE 1 (.freeze (.var 0)) (.add (.var 1) (.var 1))) ∧
    (∃ ρ : Var → PVal 2, ∃ v : BitVec 2,
      Outcome.val (PVal.int v) ∈ semP 2 ρ (.add (.freeze (.var 0)) (.freeze (.var 0))) ∧
      v.toNat % 2 = 1) :=
  ⟨by decide, poisonFreeze_freeze_add_freeze_can_be_odd 2 (by decide) 0⟩

/-- Instance of `poisonFreeze_duplicate_freeze_unsound` (width 2, `x = 0`, `a = 1`). -/
theorem nonvacuity_duplicate_freeze_unsound :
    ¬ RefinesP 2 (.add (.freeze (.var 0)) (.freeze (.var 0)))
        (.letE 1 (.freeze (.var 0)) (.add (.var 1) (.var 1))) :=
  poisonFreeze_duplicate_freeze_unsound 2 (by decide) 0 1

/-- Witness for `poison_refines_eagerUninit_eq` in which the uninitialised input is
actually read: `let y := x; 0` with `x` uninitialised is UB eagerly and returns `0` with
poison, and the refinement holds (width 2). -/
theorem nonvacuity_poison_refines_eagerUninit_live :
    semE 2 (fun _ => none) (.letE 1 (.var 0) (.const 0)) = [.ub] ∧
    semP 2 (toPoisonEnv fun _ => none) (.letE 1 (.var 0) (.const 0)) = [.val (.int 0#2)] ∧
    OutRef (fun a b => a = b)
      (semP 2 (toPoisonEnv fun _ => none) (.letE 1 (.var 0) (.const 0)))
      ((semE 2 (fun _ => none) (.letE 1 (.var 0) (.const 0))).map Outcome.toP) := by
  decide

end Toy.UB
