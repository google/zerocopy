import ToyUB.Monotone

/-!
# Unswitching: hoisting a branch out of an `if` that might not execute it

Source: `if ec then (if ed then a else b) else e`. The unswitched target branches on the
inner condition `ed` first: `if ed then (if ec then a else e) else (if ec then b else e)`.
When `ec` is `0` the source never evaluates `ed`, but the target always does.

* Poison model (branching on `poison` is UB): the plain rewrite is unsound for distinct
  condition variables `c ≠ d`, at every width, whatever `a`, `b` are: with `c ↦ 0`,
  `d ↦ poison` the target reaches UB while the source does not.
* Undef model (branching chooses nondeterministically): the plain rewrite is sound for
  every outer condition `ec` and every inner condition `ed` that never reaches UB
  (`undef_unswitch_without_freeze_sound_of_ubFree`).
* Poison + freeze model: branching on a frozen copy of the inner condition,
  `let t := freeze ed; if t then (if ec then a else e) else (if ec then b else e)`, is
  sound provided `ed` never reaches UB and the new variable `t` is not free in `ec`, `a`,
  `b`, `e` (`poisonFreeze_unswitch_with_freeze_sound_of_ubFree`). `freeze` removes
  `poison` but not immediate UB (`semP w ρ (freeze ub) = [ub]`), so the UB-freedom of
  `ed` cannot be dropped.

The toy has no loops; "hoisting out of a loop that might run zero times" is modelled by
the enclosing `if ec`.
-/

namespace Toy.UB

open Expr

/-- `UBFreeU w e`: in the undef model, `e` reaches UB in no inhabited environment. -/
def UBFreeU (w : Nat) (e : Expr) : Prop :=
  ∀ ρ : Var → USet w, UInhabited ρ → ¬ MayUB (semU w ρ e)

/-- `UBFreeP w e`: in the poison(+freeze) model, `e` reaches UB in no environment. Branching
on a possibly-`poison` value, or `ub`, violates it; arithmetic, comparisons, `freeze` and
`let` over variables do not. -/
def UBFreeP (w : Nat) (e : Expr) : Prop :=
  ∀ ρ : Var → PVal w, ¬ MayUB (semP w ρ e)

theorem ubFreeU_var (w : Nat) (x : Var) : UBFreeU w (.var x) := fun _ _ h => by
  simp [mayUB_iff, semU] at h

theorem ubFreeP_var (w : Nat) (x : Var) : UBFreeP w (.var x) := fun _ h => by
  simp [mayUB_iff, semP] at h

theorem ubFreeP_eq_var (w : Nat) (x y : Var) : UBFreeP w (.eq (.var x) (.var y)) := fun _ h => by
  simp [mayUB_iff, semP, bind2] at h

theorem ubFreeU_ite_var_const (w : Nat) (x : Var) (m n : Nat) :
    UBFreeU w (.ite (.var x) (.const m) (.const n)) := fun ρ _ h => by
  rw [mayUB_iff] at h
  simp only [semU, bind1_val_singleton] at h
  rcases List.mem_append.mp h with h | h <;> (split at h <;> simp at h)

/-- Positive examples for `UBFreeP`: a variable, and the comparison `x = y`, never reach UB.
Negative examples: `ub` does, and so does `if x then 1 else 0` (branching on `x ↦ poison`). -/
theorem ubFreeP_examples :
    UBFreeP 2 (.var 0) ∧ UBFreeP 2 (.eq (.var 0) (.var 1)) ∧ ¬ UBFreeP 2 .ub ∧
    ¬ UBFreeP 2 (.ite (.var 0) (.const 1) (.const 0)) := by
  exact ⟨ubFreeP_var 2 0, ubFreeP_eq_var 2 0 1, fun h => h (fun _ => .poison) (by decide),
    fun h => h (fun _ => .poison) (by decide)⟩

/-- Positive example for `UBFreeU`: a variable never reaches UB; branching is not UB in the
undef model, so `if x then 1 else 0` does not either. Negative example: `ub`. -/
theorem ubFreeU_examples :
    UBFreeU 2 (.var 0) ∧ UBFreeU 2 (.ite (.var 0) (.const 1) (.const 0)) ∧ ¬ UBFreeU 2 .ub := by
  exact ⟨ubFreeU_var 2 0, ubFreeU_ite_var_const 2 0 1 0, fun h => h (fun _ => USet.single 0#2)
    (fun _ => ⟨0#2, by simp [USet.single]⟩) (by decide)⟩

/-- **Poison model, unswitching without `freeze` is unsound.** For every width `w`,
distinct condition variables `c ≠ d`, and expressions `a`, `b`, with else-branch the
literal `n`, the unswitched program is not a refinement of the source: with `c ↦ 0` and
`d ↦ poison` the source returns `n` while the target branches on `poison`. -/
theorem poison_unswitch_without_freeze_distinct_vars_unsound (w : Nat) (c d : Var) (hcd : c ≠ d)
    (a b : Expr) (n : Nat) :
    ¬ RefinesP w (.ite (.var d) (.ite (.var c) a (.const n)) (.ite (.var c) b (.const n)))
        (.ite (.var c) (.ite (.var d) a b) (.const n)) := by
  intro h
  have hc : (fun v => if v = d then PVal.poison else PVal.int 0#w : Var → PVal w) c =
      PVal.int 0#w := by simp [hcd]
  rcases h (fun v => if v = d then PVal.poison else PVal.int 0#w) with hub | h
  · rw [mayUB_iff] at hub
    simp only [semP, bind1_val_singleton, hc] at hub
    simp at hub
  · have := h .ub (by simp [semP])
    obtain ⟨o', _, hle⟩ := this
    cases o' <;> simp [Outcome.LeVal] at hle

/-- Same-variable control: when both conditions are the same variable, unswitching
without `freeze` is a refinement in the poison model, so the hypothesis `c ≠ d` of
`poison_unswitch_without_freeze_distinct_vars_unsound` cannot be dropped. -/
theorem poison_unswitch_without_freeze_sound_of_same_var (w : Nat) (c : Var) (a b e : Expr) :
    RefinesP w (.ite (.var c) (.ite (.var c) a e) (.ite (.var c) b e))
      (.ite (.var c) (.ite (.var c) a b) e) := by
  intro ρ
  cases hc : ρ c with
  | poison => left; rw [mayUB_iff]; simp [semP, hc]
  | int z =>
    simp only [semP, bind1_val_singleton, hc]
    by_cases hz : z = 0#w <;> simp [hz] <;> exact outRef_refl PVal.Refines.refl _

/-- **Undef model, unswitching without `freeze` is sound for UB-free inner conditions.**
For every width `w`, every outer condition `ec`, every inner condition `ed` that reaches
UB in no inhabited environment (`UBFreeU w ed`), and all branches `a`, `b`, `e`, the
unswitched program `if ed then (if ec then a else e) else (if ec then b else e)` refines
`if ec then (if ed then a else b) else e` in the undef model, where branching on an undef
value is a nondeterministic choice rather than UB. -/
theorem undef_unswitch_without_freeze_sound_of_ubFree (w : Nat) (ec ed a b e : Expr)
    (hed : UBFreeU w ed) :
    RefinesU w (.ite ed (.ite ec a e) (.ite ec b e)) (.ite ec (.ite ed a b) e) := by
  intro ρ hρ
  by_cases hS : MayUB (semU w ρ (.ite ec (.ite ed a b) e))
  · exact Or.inl hS
  · apply outRef_of_subset USet.Sub.refl
    intro o ho
    simp only [semU] at ho
    rcases mem_bind1.mp ho with ⟨_, hed_ub⟩ | ⟨D, hD, ho_d⟩
    · exact absurd (mayUB_iff.mpr hed_ub) (hed ρ hρ)
    · rcases List.mem_append.mp ho_d with ho_dt | ho_de
      · split at ho_dt
        · rename_i hDn
          rcases mem_bind1.mp ho_dt with ⟨_, hec_ub⟩ | ⟨C, hC, ho_c⟩
          · exact absurd (mayUB_iff.mpr (ub_mem_bind1_of_ub_mem hec_ub)) hS
          · rcases List.mem_append.mp ho_c with ho_ct | ho_ce
            · split at ho_ct
              · rename_i hCn
                simp only [semU]
                refine mem_bind1.mpr (Or.inr ⟨C, hC, List.mem_append_left _ ?_⟩)
                simp only [hCn, ite_true]
                refine mem_bind1.mpr (Or.inr ⟨D, hD, List.mem_append_left _ ?_⟩)
                simpa [hDn] using ho_ct
              · simp at ho_ct
            · split at ho_ce
              · rename_i hC0
                simp only [semU]
                refine mem_bind1.mpr (Or.inr ⟨C, hC, List.mem_append_right _ ?_⟩)
                simpa [hC0] using ho_ce
              · simp at ho_ce
        · simp at ho_dt
      · split at ho_de
        · rename_i hD0
          rcases mem_bind1.mp ho_de with ⟨_, hec_ub⟩ | ⟨C, hC, ho_c⟩
          · exact absurd (mayUB_iff.mpr (ub_mem_bind1_of_ub_mem hec_ub)) hS
          · rcases List.mem_append.mp ho_c with ho_ct | ho_ce
            · split at ho_ct
              · rename_i hCn
                simp only [semU]
                refine mem_bind1.mpr (Or.inr ⟨C, hC, List.mem_append_left _ ?_⟩)
                simp only [hCn, ite_true]
                refine mem_bind1.mpr (Or.inr ⟨D, hD, List.mem_append_right _ ?_⟩)
                simpa [hD0] using ho_ct
              · simp at ho_ct
            · split at ho_ce
              · rename_i hC0
                simp only [semU]
                refine mem_bind1.mpr (Or.inr ⟨C, hC, List.mem_append_right _ ?_⟩)
                simpa [hC0] using ho_ce
              · simp at ho_ce
        · simp at ho_de

/-- Corollary for condition variables `c`, `d` (equal or not): variables never reach UB. -/
theorem undef_unswitch_without_freeze_sound (w : Nat) (c d : Var) (a b e : Expr) :
    RefinesU w (.ite (.var d) (.ite (.var c) a e) (.ite (.var c) b e))
      (.ite (.var c) (.ite (.var d) a b) e) :=
  undef_unswitch_without_freeze_sound_of_ubFree w (.var c) (.var d) a b e (ubFreeU_var w d)

/-- Tightness of `hed` in `undef_unswitch_without_freeze_sound_of_ubFree` (it is the only
hypothesis): with `ec = 0`, `ed = ub` and constant branches, `ed` is not UB-free and the
rewrite fails at width 2 (the source never evaluates `ub`; the target does). -/
theorem undef_unswitch_without_freeze_needs_ubFree :
    ¬ UBFreeU 2 .ub ∧
    ¬ RefinesU 2 (.ite .ub (.ite (.const 0) (.const 0) (.const 0)) (.ite (.const 0) (.const 0) (.const 0)))
      (.ite (.const 0) (.ite .ub (.const 0) (.const 0)) (.const 0)) := by
  have hinh : UInhabited (fun _ => USet.single 0#2 : Var → USet 2) :=
    fun _ => ⟨0#2, by simp [USet.single]⟩
  refine ⟨fun h => h _ hinh (by decide), fun h => ?_⟩
  have h' := h _ hinh
  revert h'
  decide

/-- Boundary of the modelling (not a hypothesis of any theorem): for condition variables,
the pointwise refinement condition of `undef_unswitch_without_freeze_sound` holds even in
environments that bind some variable to the *empty* set, because then the target can have
no outcome at all and `OutRef` accepts an empty target list. `UInhabited` (part of
`RefinesU`) is what guarantees that the target has outcomes (`semU_ne_nil`). -/
theorem undef_unswitch_vars_outRef_all_envs (w : Nat) (c d : Var) (a b e : Expr)
    (ρ : Var → USet w) :
    OutRef USet.Sub
      (semU w ρ (.ite (.var d) (.ite (.var c) a e) (.ite (.var c) b e)))
      (semU w ρ (.ite (.var c) (.ite (.var d) a b) e)) := by
  by_cases hd : (ρ d).Nonempty
  · apply outRef_of_subset USet.Sub.refl
    intro o ho
    have hD : (ρ d).HasNonzero = true ∨ ρ d 0#w = true := by
      obtain ⟨z, hz⟩ := hd
      by_cases h0 : z = 0#w
      · subst h0; exact Or.inr hz
      · exact Or.inl (decide_eq_true ⟨z, hz, h0⟩)
    simp only [semU, bind1_val_singleton] at ho ⊢
    cases hCn : (ρ c).HasNonzero <;> cases hC0 : ρ c 0#w <;>
      cases hDn : (ρ d).HasNonzero <;> cases hD0 : ρ d 0#w <;>
      simp_all <;>
      first
      | (rcases ho with h | h | h | h <;> simp [h])
      | (rcases ho with h | h | h <;> simp [h])
      | (rcases ho with h | h <;> simp [h])
  · have hDn : (ρ d).HasNonzero = false := by
      simp only [USet.HasNonzero, decide_eq_false_iff_not]
      rintro ⟨z, hz, _⟩
      exact hd ⟨z, hz⟩
    have hD0 : ρ d 0#w = false := by
      cases h0 : ρ d 0#w with
      | false => rfl
      | true => exact absurd ⟨0#w, h0⟩ hd
    simp only [semU, bind1_val_singleton, hDn, hD0]
    exact outRef_nil _

/-- Width-2 environment with `d = 1` bound to the empty set and every other variable to
`{0}` (not inhabited). -/
def uEmptyD : Var → USet 2 := fun v => if v = 1 then (fun _ => false) else USet.single 0#2

/-- Boundary instance: with `d ↦ ∅` and `c ↦ {0}`, the source
`if c then (if d then 2 else 3) else 1` returns `1`, the unswitched target has no outcome,
and `OutRef` accepts the pair. -/
theorem undef_unswitch_empty_input_target_has_no_outcomes :
    ¬ UInhabited uEmptyD ∧
    semU 2 uEmptyD
      (.ite (.var 1) (.ite (.var 0) (.const 2) (.const 1)) (.ite (.var 0) (.const 3) (.const 1))) = [] ∧
    (∃ o ∈ semU 2 uEmptyD (.ite (.var 0) (.ite (.var 1) (.const 2) (.const 3)) (.const 1)),
      Outcome.LeVal USet.Sub (.val (USet.single 1#2)) o) ∧
    OutRef USet.Sub
      (semU 2 uEmptyD
        (.ite (.var 1) (.ite (.var 0) (.const 2) (.const 1)) (.ite (.var 0) (.const 3) (.const 1))))
      (semU 2 uEmptyD (.ite (.var 0) (.ite (.var 1) (.const 2) (.const 3)) (.const 1))) := by
  refine ⟨?_, ?_, by decide, by decide⟩
  · intro hinh
    obtain ⟨z, hz⟩ := hinh 1
    simp [uEmptyD] at hz
  · have h1n : (uEmptyD 1).HasNonzero = false := by decide
    have h10 : uEmptyD 1 0#2 = false := by decide
    simp [semU, bind1_val_singleton, h1n, h10]

/-- Updating a variable that is not free in `e` does not change the poison-model meaning
of `e`. -/
theorem semP_update_notFree (w : Nat) (t : Var) (v : PVal w) (e : Expr) :
    ∀ ρ : Var → PVal w, e.freeIn t = false → semP w (update ρ t v) e = semP w ρ e := by
  induction e with
  | var y =>
    intro ρ h
    simp only [Expr.freeIn, beq_eq_false_iff_ne, ne_eq] at h
    simp [semP, update, Ne.symm h]
  | const n => intro ρ _; rfl
  | add a b iha ihb =>
    intro ρ h
    simp only [Expr.freeIn, Bool.or_eq_false_iff] at h
    simp only [semP, iha ρ h.1, ihb ρ h.2]
  | mul a b iha ihb =>
    intro ρ h
    simp only [Expr.freeIn, Bool.or_eq_false_iff] at h
    simp only [semP, iha ρ h.1, ihb ρ h.2]
  | eq a b iha ihb =>
    intro ρ h
    simp only [Expr.freeIn, Bool.or_eq_false_iff] at h
    simp only [semP, iha ρ h.1, ihb ρ h.2]
  | ite c x y ihc ihx ihy =>
    intro ρ h
    simp only [Expr.freeIn, Bool.or_eq_false_iff] at h
    have hc := ihc ρ h.1.1
    have hx := ihx ρ h.1.2
    have hy := ihy ρ h.2
    simp only [semP, hc, hx, hy]
  | letE y a b iha ihb =>
    intro ρ h
    simp only [Expr.freeIn, Bool.or_eq_false_iff, Bool.and_eq_false_iff, bne_eq_false_iff_eq] at h
    simp only [semP, iha ρ h.1]
    congr 1
    funext A
    by_cases hty : t = y
    · subst hty
      have : update (update ρ t v) t A = update ρ t A := by
        funext z; simp only [update]; split <;> rfl
      rw [this]
    · have hb : b.freeIn t = false := by
        rcases h.2 with h2 | h2
        · exact absurd h2 hty
        · exact h2
      have : update (update ρ t v) y A = update (update ρ y A) t v := by
        funext z
        simp only [update]
        by_cases hzy : z = y
        · subst hzy; simp [Ne.symm hty]
        · simp [hzy]
      rw [this, ihb _ hb]
  | freeze a iha =>
    intro ρ h
    simp only [Expr.freeIn] at h
    simp only [semP, iha ρ h]
  | ub => intro ρ _; rfl

theorem semP_letE_eq {w : Nat} (ρ : Var → PVal w) (x : Var) (a b : Expr) :
    semP w ρ (.letE x a b) = bind1 (semP w ρ a) (fun v => semP w (update ρ x v) b) := rfl

theorem semP_ite_var_poison {w : Nat} {ρ : Var → PVal w} {x : Var} (t e : Expr)
    (h : ρ x = .poison) : semP w ρ (.ite (.var x) t e) = [.ub] := by
  simp [semP, h]

theorem semP_ite_var_int {w : Nat} {ρ : Var → PVal w} {x : Var} {z : BitVec w} (t e : Expr)
    (h : ρ x = .int z) :
    semP w ρ (.ite (.var x) t e) = if z ≠ 0#w then semP w ρ t else semP w ρ e := by
  simp only [semP, h, bind1_val_singleton]


/-- **Poison + freeze model, unswitching on a frozen UB-free condition is sound.** For
every width `w`, every outer condition `ec`, every inner condition `ed` that reaches UB in
no environment (`UBFreeP w ed`), and every variable `t` not free in `ec`, `a`, `b`, `e`,
the program `let t := freeze ed; if t then (if ec then a else e) else (if ec then b else e)`
refines `if ec then (if ed then a else b) else e` in the poison + freeze model. -/
theorem poisonFreeze_unswitch_with_freeze_sound_of_ubFree (w : Nat) (ec ed : Expr) (t : Var)
    (a b e : Expr) (hed : UBFreeP w ed)
    (htc : ec.freeIn t = false) (hta : a.freeIn t = false)
    (htb : b.freeIn t = false) (hte : e.freeIn t = false) :
    RefinesP w
      (.letE t (.freeze ed) (.ite (.var t) (.ite ec a e) (.ite ec b e)))
      (.ite ec (.ite ed a b) e) := by
  intro ρ
  by_cases hS : MayUB (semP w ρ (.ite ec (.ite ed a b) e))
  · exact Or.inl hS
  · apply outRef_of_subset PVal.Refines.refl
    intro o ho
    have h_ite_a : (Expr.ite ec a e).freeIn t = false := by simp [Expr.freeIn, htc, hta, hte]
    have h_ite_b : (Expr.ite ec b e).freeIn t = false := by simp [Expr.freeIn, htc, htb, hte]
    rw [semP_letE_eq] at ho
    rcases mem_bind1.mp ho with ⟨rfl, hfr_ub⟩ | ⟨vt, hvt, ho_body⟩
    · simp only [semP] at hfr_ub
      rcases mem_bind1.mp hfr_ub with ⟨_, hed_ub⟩ | ⟨vd, _, hvd_ub⟩
      · exact absurd (mayUB_iff.mpr hed_ub) (hed ρ)
      · cases vd <;> simp at hvd_ub
    · simp only [semP] at hvt
      rcases mem_bind1.mp hvt with ⟨h, _⟩ | ⟨vd, hvd, hvt_fr⟩
      · cases h
      · have hvt_int : ∃ u : BitVec w, vt = .int u ∧ (vd = .poison ∨ vd = .int u) := by
          cases vd with
          | poison =>
            simp only [List.mem_map] at hvt_fr
            obtain ⟨u, _, hu⟩ := hvt_fr
            cases hu
            exact ⟨u, rfl, Or.inl rfl⟩
          | int u =>
            simp only [List.mem_singleton, Outcome.val.injEq] at hvt_fr
            subst hvt_fr
            exact ⟨u, rfl, Or.inr rfl⟩
        obtain ⟨u, rfl, hvd_cases⟩ := hvt_int
        have ht_lookup : update ρ t (.int u) t = .int u := by simp [update]
        rw [semP_ite_var_int _ _ ht_lookup,
          semP_update_notFree w t (.int u) (.ite ec a e) ρ h_ite_a,
          semP_update_notFree w t (.int u) (.ite ec b e) ρ h_ite_b] at ho_body
        by_cases hu : u = 0#w
        · simp only [hu, ne_eq, not_true_eq_false, ite_false] at ho_body
          simp only [semP] at ho_body
          rcases mem_bind1.mp ho_body with ⟨rfl, hec_ub⟩ | ⟨vc, hvc, ho_leaf⟩
          · exact absurd (mayUB_iff.mpr (ub_mem_bind1_of_ub_mem hec_ub)) hS
          · cases vc with
            | poison =>
              exact absurd (mayUB_iff.mpr (mem_bind1.mpr (Or.inr ⟨.poison, hvc, by simp⟩))) hS
            | int z =>
              by_cases hz : z = 0#w
              · subst hz
                simp only [ne_eq, not_true_eq_false, ite_false] at ho_leaf
                simp only [semP]
                exact mem_bind1.mpr (Or.inr ⟨.int 0#w, hvc, by simp [ho_leaf]⟩)
              · simp only [ne_eq, hz, not_false_eq_true, ite_true] at ho_leaf
                rcases hvd_cases with rfl | rfl
                · exfalso
                  apply hS
                  rw [mayUB_iff]
                  simp only [semP]
                  refine mem_bind1.mpr (Or.inr ⟨.int z, hvc, ?_⟩)
                  simp only [ne_eq, hz, not_false_eq_true, ite_true]
                  exact mem_bind1.mpr (Or.inr ⟨.poison, hvd, by simp⟩)
                · subst hu
                  simp only [semP]
                  refine mem_bind1.mpr (Or.inr ⟨.int z, hvc, ?_⟩)
                  simp only [ne_eq, hz, not_false_eq_true, ite_true]
                  exact mem_bind1.mpr (Or.inr ⟨.int 0#w, hvd, by simp [ho_leaf]⟩)
        · simp only [ne_eq, hu, not_false_eq_true, ite_true] at ho_body
          simp only [semP] at ho_body
          rcases mem_bind1.mp ho_body with ⟨rfl, hec_ub⟩ | ⟨vc, hvc, ho_leaf⟩
          · exact absurd (mayUB_iff.mpr (ub_mem_bind1_of_ub_mem hec_ub)) hS
          · cases vc with
            | poison =>
              exact absurd (mayUB_iff.mpr (mem_bind1.mpr (Or.inr ⟨.poison, hvc, by simp⟩))) hS
            | int z =>
              by_cases hz : z = 0#w
              · subst hz
                simp only [ne_eq, not_true_eq_false, ite_false] at ho_leaf
                simp only [semP]
                exact mem_bind1.mpr (Or.inr ⟨.int 0#w, hvc, by simp [ho_leaf]⟩)
              · simp only [ne_eq, hz, not_false_eq_true, ite_true] at ho_leaf
                rcases hvd_cases with rfl | rfl
                · exfalso
                  apply hS
                  rw [mayUB_iff]
                  simp only [semP]
                  refine mem_bind1.mpr (Or.inr ⟨.int z, hvc, ?_⟩)
                  simp only [ne_eq, hz, not_false_eq_true, ite_true]
                  exact mem_bind1.mpr (Or.inr ⟨.poison, hvd, by simp⟩)
                · simp only [semP]
                  refine mem_bind1.mpr (Or.inr ⟨.int z, hvc, ?_⟩)
                  simp only [ne_eq, hz, not_false_eq_true, ite_true]
                  exact mem_bind1.mpr (Or.inr ⟨.int u, hvd, by simp [hu, ho_leaf]⟩)

/-- Corollary for condition variables `c`, `d` and `t ≠ c`: variables never reach UB, and
`t ≠ c` is `(var c).freeIn t = false`. -/
theorem poisonFreeze_unswitch_with_freeze_sound_of_fresh (w : Nat) (c d t : Var) (a b e : Expr)
    (htc : t ≠ c) (hta : a.freeIn t = false) (htb : b.freeIn t = false)
    (hte : e.freeIn t = false) :
    RefinesP w
      (.letE t (.freeze (.var d)) (.ite (.var t) (.ite (.var c) a e) (.ite (.var c) b e)))
      (.ite (.var c) (.ite (.var d) a b) e) :=
  poisonFreeze_unswitch_with_freeze_sound_of_ubFree w (.var c) (.var d) t a b e
    (ubFreeP_var w d) (by simp [Expr.freeIn, htc]) hta htb hte

/-- Tightness of `hed` (canonical form): with `ec = 0`, `ed = ub`, `t = 4` and constant
branches, every other hypothesis holds, `ed` is not UB-free, and the rewrite fails at width 2
(`freeze ub` is still UB, while the source never evaluates `ub`). -/
theorem poisonFreeze_unswitch_with_freeze_needs_ubFree :
    (Expr.const 0).freeIn 4 = false ∧ ¬ UBFreeP 2 .ub ∧
    ¬ RefinesP 2
      (.letE 4 (.freeze .ub)
        (.ite (.var 4) (.ite (.const 0) (.const 0) (.const 0)) (.ite (.const 0) (.const 0) (.const 0))))
      (.ite (.const 0) (.ite .ub (.const 0) (.const 0)) (.const 0)) := by
  refine ⟨by decide, fun h => h (fun _ => .poison) (by decide), fun h => ?_⟩
  have h' := h (fun _ => .int 0#2)
  revert h'
  decide

/-- Second tightness witness for `hed`, without the `ub` construct: the inner condition
`ed = if x then 1 else 0` branches on `x`, which is UB when `x ↦ poison`; `freeze` does not
help (canonical form, width 2, `ec = 0`, `t = 4`). -/
theorem poisonFreeze_unswitch_with_freeze_needs_ubFree_branch :
    (Expr.const 0).freeIn 4 = false ∧ ¬ UBFreeP 2 (.ite (.var 0) (.const 1) (.const 0)) ∧
    ¬ RefinesP 2
      (.letE 4 (.freeze (.ite (.var 0) (.const 1) (.const 0)))
        (.ite (.var 4) (.ite (.const 0) (.const 0) (.const 0)) (.ite (.const 0) (.const 0) (.const 0))))
      (.ite (.const 0) (.ite (.ite (.var 0) (.const 1) (.const 0)) (.const 0) (.const 0)) (.const 0)) := by
  refine ⟨by decide, fun h => h (fun _ => .poison) (by decide), fun h => ?_⟩
  have h' := h (fun _ => .poison)
  revert h'
  decide

/-- Tightness of `htc` (canonical form): with `t = c = 2`, `ec = var 2`, `ed = var 3`,
`a = 1`, `b = e = 0`, every other hypothesis holds and the rewrite fails at width 2
(environment `c ↦ 0`, `d ↦ 1`: the source returns `0`, the target `1`). -/
theorem poisonFreeze_unswitch_with_freeze_needs_t_not_free_in_cond :
    UBFreeP 2 (.var 3) ∧ (Expr.const 1).freeIn 2 = false ∧ (Expr.const 0).freeIn 2 = false ∧
    (Expr.var 2).freeIn 2 = true ∧
    ¬ RefinesP 2
      (.letE 2 (.freeze (.var 3))
        (.ite (.var 2) (.ite (.var 2) (.const 1) (.const 0)) (.ite (.var 2) (.const 0) (.const 0))))
      (.ite (.var 2) (.ite (.var 3) (.const 1) (.const 0)) (.const 0)) := by
  refine ⟨ubFreeP_var 2 3, by decide, by decide, by decide, ?_⟩
  intro h
  have := h (fun v => if v = 3 then .int 1#2 else .int 0#2)
  revert this
  decide

/-- Tightness of `hta` (canonical form): with `ec = var 2`, `ed = var 3`, `t = 4`, `a = t`,
`b = e = 0`, every other hypothesis holds and the rewrite fails at width 2 (environment
`c ↦ 1`, `d ↦ 1`, `t ↦ 0`: the source returns `0`, the target `1`). -/
theorem poisonFreeze_unswitch_with_freeze_needs_t_not_free_in_a :
    UBFreeP 2 (.var 3) ∧ (Expr.var 2).freeIn 4 = false ∧ (Expr.const 0).freeIn 4 = false ∧
    ¬ RefinesP 2
      (.letE 4 (.freeze (.var 3))
        (.ite (.var 4) (.ite (.var 2) (.var 4) (.const 0)) (.ite (.var 2) (.const 0) (.const 0))))
      (.ite (.var 2) (.ite (.var 3) (.var 4) (.const 0)) (.const 0)) := by
  refine ⟨ubFreeP_var 2 3, by decide, by decide, ?_⟩
  intro h
  have := h (fun v => if v = 4 then .int 0#2 else .int 1#2)
  revert this
  decide

/-- Tightness of `htb` (canonical form): with `ec = var 2`, `ed = var 3`, `t = 4`, `b = t`,
`a = e = 0`, every other hypothesis holds and the rewrite fails at width 2 (environment
`c ↦ 1`, `d ↦ 0`, `t ↦ 1`: the source returns `1`, the target `0`). -/
theorem poisonFreeze_unswitch_with_freeze_needs_t_not_free_in_b :
    UBFreeP 2 (.var 3) ∧ (Expr.var 2).freeIn 4 = false ∧ (Expr.const 0).freeIn 4 = false ∧
    ¬ RefinesP 2
      (.letE 4 (.freeze (.var 3))
        (.ite (.var 4) (.ite (.var 2) (.const 0) (.const 0)) (.ite (.var 2) (.var 4) (.const 0))))
      (.ite (.var 2) (.ite (.var 3) (.const 0) (.var 4)) (.const 0)) := by
  refine ⟨ubFreeP_var 2 3, by decide, by decide, ?_⟩
  intro h
  have := h (fun v => if v = 3 then .int 0#2 else .int 1#2)
  revert this
  decide

/-- Tightness of `hte` (canonical form): with `ec = var 2`, `ed = var 3`, `t = 4`, `e = t`,
`a = b = 0`, every other hypothesis holds and the rewrite fails at width 2 (environment
`c ↦ 0`, `d ↦ 1`, `t ↦ 0`: the source returns `0`, the target `1`). -/
theorem poisonFreeze_unswitch_with_freeze_needs_t_not_free_in_e :
    UBFreeP 2 (.var 3) ∧ (Expr.var 2).freeIn 4 = false ∧ (Expr.const 0).freeIn 4 = false ∧
    ¬ RefinesP 2
      (.letE 4 (.freeze (.var 3))
        (.ite (.var 4) (.ite (.var 2) (.const 0) (.var 4)) (.ite (.var 2) (.const 0) (.var 4))))
      (.ite (.var 2) (.ite (.var 3) (.const 0) (.const 0)) (.var 4)) := by
  refine ⟨ubFreeP_var 2 3, by decide, by decide, ?_⟩
  intro h
  have := h (fun v => if v = 3 then .int 1#2 else .int 0#2)
  revert this
  decide

end Toy.UB
