import ToyUB.Monotone

/-!
# Duplicating and merging uses: `2 * e` versus `e + e`

`e + e` evaluates `e` twice, and each evaluation is a separate use; `2 * e` evaluates it
once. Under the undef model the two uses of an undef value choose independently, so
`x + x` may be odd while `2 * x` is always even. Under the poison model a variable holds a
single value, but `e` may still be nondeterministic when it contains `freeze`.

What is proved:
* undef model, any `e`, any width: `e + e → 2 * e` is sound;
* undef model, variable `x`, width `≥ 1`: `2 * x → x + x` is unsound (width `0`: sound);
* poison model, any `e` (with or without `freeze`), any width: `e + e → 2 * e` is sound;
* poison model, freeze-free `e`, any width: `2 * e → e + e` is sound (so for freeze-free
  `e`, and in particular for a variable, both directions are sound);
* poison + freeze model, `e = freeze x`, width `≥ 1`: `2 * e → e + e` is unsound.

Escape hatches (both models, every width): binding one frozen copy,
`2 * e → let a := freeze e; a + a`, is sound for every `e`; and for inputs known to be
well defined (a singleton set, or an integer rather than `poison`) the duplicating rewrites
are sound pointwise.
-/

namespace Toy.UB

open Expr

/-- **Undef model, merging two uses is sound.** For every width `w` and every expression
`e`, rewriting `e + e` to `2 * e` is a refinement in the undef model. -/
theorem undef_rewrite_add_self_to_two_mul_sound (w : Nat) (e : Expr) :
    RefinesU w (.mul (.const 2) e) (.add e e) := by
  intro ρ _
  by_cases hS : Outcome.ub ∈ semU w ρ e
  · left
    rw [mayUB_iff]
    simp only [semU, bind2]
    exact ub_mem_bind1_of_ub_mem hS
  · right
    intro o ho
    simp only [semU, bind2, bind1_val_singleton] at ho
    rcases mem_bind1.mp ho with ⟨_, h⟩ | ⟨A, hA, ho⟩
    · exact absurd h hS
    · simp only [List.mem_singleton] at ho
      subst ho
      refine ⟨.val (USet.map2 (· + ·) A A), ?_, ?_⟩
      · simp only [semU, bind2]
        exact mem_bind1.mpr (Or.inr ⟨A, hA, mem_bind1.mpr (Or.inr ⟨A, hA, by simp⟩)⟩)
      · intro z hz
        simp only [USet.map2, USet.single, decide_eq_true_eq] at hz ⊢
        obtain ⟨a, b, ha, hb, rfl⟩ := hz
        subst ha
        exact ⟨b, b, hb, hb, (two_mul_eq_add_self b).symm⟩

/-- The undef-model environment binding every variable to `{0, 1}`. -/
def uZeroOne (w : Nat) : Var → USet w := fun _ z => decide (z = 0#w ∨ z = 1#w)

theorem uZeroOne_inhabited (w : Nat) : UInhabited (uZeroOne w) :=
  fun _ => ⟨0#w, by simp [uZeroOne]⟩

/-- **Undef model, duplicating a use is unsound.** For every width `w ≥ 1` and every
variable `x`, rewriting `2 * x` to `x + x` is not a refinement in the undef model: with
`x ↦ {0, 1}` the target may produce the odd integer `1`, which the source cannot. -/
theorem undef_rewrite_two_mul_to_add_self_unsound (w : Nat) (hw : 1 ≤ w) (x : Var) :
    ¬ RefinesU w (.add (.var x) (.var x)) (.mul (.const 2) (.var x)) := by
  intro h
  rcases h _ (uZeroOne_inhabited w) with hub | h
  · simp [mayUB_iff, semU, bind2] at hub
  · obtain ⟨o', ho', hle⟩ :=
      h (.val (USet.map2 (· + ·) (uZeroOne w x) (uZeroOne w x))) (by simp [semU, bind2])
    simp only [semU, bind2, bind1_val_singleton, List.mem_singleton] at ho'
    subst ho'
    have h1 := hle 1#w (by
      simp only [USet.map2, uZeroOne, decide_eq_true_eq]
      exact ⟨0#w, 1#w, Or.inl rfl, Or.inr rfl, BitVec.zero_add _⟩)
    simp only [USet.map2, USet.single, decide_eq_true_eq] at h1
    obtain ⟨a, b, rfl, _, hab⟩ := h1
    rw [two_mul_eq_add_self] at hab
    exact one_ne_add_self hw b hab.symm

/-- Width-`0` control: at width `0` (a single integer) rewriting `2 * x` to `x + x` *is* a
refinement, so the hypothesis `1 ≤ w` of `undef_rewrite_two_mul_to_add_self_unsound`
cannot be dropped. -/
theorem undef_rewrite_two_mul_to_add_self_sound_width_zero (x : Var) :
    RefinesU 0 (.add (.var x) (.var x)) (.mul (.const 2) (.var x)) := by
  intro ρ hρ
  right
  intro o ho
  simp only [semU, bind2, bind1_val_singleton, List.mem_singleton] at ho
  subst ho
  refine ⟨.val (USet.map2 (· * ·) (USet.single (BitVec.ofNat 0 2)) (ρ x)),
    by simp only [semU, bind2, bind1_val_singleton]; exact List.mem_singleton_self _, ?_⟩
  intro z _
  obtain ⟨a, ha⟩ := hρ x
  simp only [USet.map2, USet.single, decide_eq_true_eq]
  exact ⟨_, a, rfl, ha, by rw [bv_zero_eq (v := z), bv_zero_eq (v := _ * a)]⟩

/-- **Poison model, merging two uses is sound.** For every width `w` and every expression
`e` (which may contain `freeze`), rewriting `e + e` to `2 * e` is a refinement in the
poison model. -/
theorem poison_rewrite_add_self_to_two_mul_sound (w : Nat) (e : Expr) :
    RefinesP w (.mul (.const 2) e) (.add e e) := by
  intro ρ
  by_cases hS : Outcome.ub ∈ semP w ρ e
  · left
    rw [mayUB_iff]
    simp only [semP, bind2]
    exact ub_mem_bind1_of_ub_mem hS
  · right
    intro o ho
    simp only [semP, bind2, bind1_val_singleton] at ho
    rcases mem_bind1.mp ho with ⟨_, h⟩ | ⟨v, hv, ho⟩
    · exact absurd h hS
    · simp only [List.mem_singleton] at ho
      subst ho
      refine ⟨.val (PVal.lift2 (· + ·) v v), ?_, ?_⟩
      · simp only [semP, bind2]
        exact mem_bind1.mpr (Or.inr ⟨v, hv, mem_bind1.mpr (Or.inr ⟨v, hv, by simp⟩)⟩)
      · cases v with
        | poison => simp [Outcome.LeVal, PVal.lift2, PVal.Refines]
        | int u => simp [Outcome.LeVal, PVal.lift2, PVal.Refines, two_mul_eq_add_self]

/-- Freeze-free programs are deterministic in the poison model: exactly one outcome. -/
theorem semP_freezeFree_singleton (w : Nat) (e : Expr) (he : e.FreezeFree = true) :
    ∀ ρ : Var → PVal w, ∃ o, semP w ρ e = [o] := by
  induction e with
  | var x => intro ρ; exact ⟨_, rfl⟩
  | const n => intro ρ; exact ⟨_, rfl⟩
  | add a b iha ihb =>
    intro ρ
    simp only [FreezeFree, Bool.and_eq_true] at he
    obtain ⟨oa, hoa⟩ := iha he.1 ρ
    obtain ⟨ob, hob⟩ := ihb he.2 ρ
    simp only [semP, bind2, hoa, hob]
    cases oa <;> cases ob <;> simp
  | mul a b iha ihb =>
    intro ρ
    simp only [FreezeFree, Bool.and_eq_true] at he
    obtain ⟨oa, hoa⟩ := iha he.1 ρ
    obtain ⟨ob, hob⟩ := ihb he.2 ρ
    simp only [semP, bind2, hoa, hob]
    cases oa <;> cases ob <;> simp
  | eq a b iha ihb =>
    intro ρ
    simp only [FreezeFree, Bool.and_eq_true] at he
    obtain ⟨oa, hoa⟩ := iha he.1 ρ
    obtain ⟨ob, hob⟩ := ihb he.2 ρ
    simp only [semP, bind2, hoa, hob]
    cases oa <;> cases ob <;> simp
  | ite c t e ihc iht ihe =>
    intro ρ
    simp only [FreezeFree, Bool.and_eq_true] at he
    obtain ⟨oc, hoc⟩ := ihc he.1.1 ρ
    simp only [semP, hoc]
    cases oc with
    | ub => simp
    | val v =>
      cases v with
      | poison => simp
      | int z =>
        simp only [bind1_val_singleton]
        split
        · exact iht he.1.2 ρ
        · exact ihe he.2 ρ
  | letE x a b iha ihb =>
    intro ρ
    simp only [FreezeFree, Bool.and_eq_true] at he
    obtain ⟨oa, hoa⟩ := iha he.1 ρ
    simp only [semP, hoa]
    cases oa with
    | ub => simp
    | val v =>
      simp only [bind1_val_singleton]
      exact ihb he.2 _
  | freeze a => simp [FreezeFree] at he
  | ub => intro ρ; exact ⟨_, rfl⟩

/-- **Poison model, duplicating a use of a freeze-free expression is sound.** For every
width `w` and every freeze-free expression `e` (in particular every variable), rewriting
`2 * e` to `e + e` is a refinement in the poison model. -/
theorem poison_rewrite_two_mul_to_add_self_sound_of_freezeFree (w : Nat) (e : Expr)
    (he : e.FreezeFree = true) : RefinesP w (.add e e) (.mul (.const 2) e) := by
  intro ρ
  obtain ⟨o, ho⟩ := semP_freezeFree_singleton w e he ρ
  simp only [semP, bind2, ho, bind1_val_singleton]
  cases o with
  | ub => left; simp [mayUB_iff]
  | val v =>
    right
    intro o' ho'
    simp only [bind1_val_singleton, List.mem_singleton] at ho'
    subst ho'
    refine ⟨.val (PVal.lift2 (· * ·) (.int (BitVec.ofNat w 2)) v), List.mem_singleton_self _, ?_⟩
    cases v <;> simp [Outcome.LeVal, PVal.lift2, PVal.Refines, two_mul_eq_add_self]

/-- **Poison + freeze model, duplicating a `freeze` is unsound.** For every width `w ≥ 1`
and every variable `x`, rewriting `2 * freeze x` to `freeze x + freeze x` is not a
refinement: with `x ↦ poison` the two `freeze`s may pick `0` and `1`, giving the odd
integer `1`, while every source outcome is even. This is the counterexample showing that
the freeze-freeness hypothesis of `poison_rewrite_two_mul_to_add_self_sound_of_freezeFree`
cannot be dropped. -/
theorem poisonFreeze_rewrite_two_mul_to_add_self_unsound (w : Nat) (hw : 1 ≤ w) (x : Var) :
    ¬ RefinesP w (.add (.freeze (.var x)) (.freeze (.var x)))
        (.mul (.const 2) (.freeze (.var x))) := by
  intro h
  rcases h (fun _ => .poison) with hub | h
  · rw [mayUB_iff] at hub
    simp only [semP, bind2, bind1_val_singleton] at hub
    rcases mem_bind1.mp hub with ⟨_, h⟩ | ⟨v, _, h⟩
    · simp at h
    · simp at h
  · have hmem : Outcome.val (PVal.int 1#w) ∈
        semP w (fun _ => .poison) (.add (.freeze (.var x)) (.freeze (.var x))) := by
      simp only [semP, bind2, bind1_val_singleton]
      refine mem_bind1.mpr (Or.inr ⟨.int 0#w, by simp [mem_allBV], ?_⟩)
      refine mem_bind1.mpr (Or.inr ⟨.int 1#w, by simp [mem_allBV], ?_⟩)
      simp [PVal.lift2]
    obtain ⟨o', ho', hle⟩ := h _ hmem
    simp only [semP, bind2, bind1_val_singleton] at ho'
    rcases mem_bind1.mp ho' with ⟨rfl, _⟩ | ⟨v, hv, ho'⟩
    · simp [Outcome.LeVal] at hle
    · simp only [List.mem_map] at hv
      obtain ⟨u, _, hu⟩ := hv
      cases hu
      simp only [PVal.lift2, List.mem_singleton] at ho'
      subst ho'
      simp only [Outcome.LeVal, PVal.Refines, PVal.int.injEq] at hle
      rw [two_mul_eq_add_self] at hle
      exact one_ne_add_self hw u hle

/-- Width-`0` control: at width `0` rewriting `2 * freeze x` to `freeze x + freeze x` is a
refinement, so the hypothesis `1 ≤ w` of `poisonFreeze_rewrite_two_mul_to_add_self_unsound`
cannot be dropped. -/
theorem poisonFreeze_rewrite_two_mul_to_add_self_sound_width_zero (x : Var) :
    RefinesP 0 (.add (.freeze (.var x)) (.freeze (.var x)))
      (.mul (.const 2) (.freeze (.var x))) := by
  intro ρ
  cases h : ρ x with
  | poison => simp only [semP, bind2, bind1_val_singleton, h]; decide
  | int v =>
    obtain rfl := bv_zero_eq (v := v)
    simp only [semP, bind2, bind1_val_singleton, h]
    decide

/-- **Escape hatch (undef model): duplicate a frozen copy instead.** For every width `w`,
expression `e` and variable `a`, rewriting `2 * e` to `let a := freeze e; a + a` is a
refinement in the undef model. -/
theorem undef_rewrite_two_mul_to_let_freeze_add_self_sound (w : Nat) (e : Expr) (a : Var) :
    RefinesU w (.letE a (.freeze e) (.add (.var a) (.var a))) (.mul (.const 2) e) := by
  intro ρ _
  by_cases hS : Outcome.ub ∈ semU w ρ e
  · left
    rw [mayUB_iff]
    simp only [semU, bind2, bind1_val_singleton]
    exact ub_mem_bind1_of_ub_mem hS
  · right
    intro o ho
    have ho' : o ∈ bind1 (semU w ρ (.freeze e))
        (fun A => semU w (update ρ a A) (.add (.var a) (.var a))) := ho
    rcases mem_bind1.mp ho' with ⟨rfl, h⟩ | ⟨B, hB, ho2⟩
    · exfalso
      apply hS
      simp only [semU] at h
      rcases mem_bind1.mp h with ⟨_, h'⟩ | ⟨A, _, hA⟩
      · exact h'
      · rw [List.mem_filterMap] at hA
        obtain ⟨v, _, hv⟩ := hA
        split at hv <;> simp at hv
    · simp [semU, bind2, update] at ho2
      subst ho2
      simp only [semU] at hB
      rcases mem_bind1.mp hB with ⟨h1, _⟩ | ⟨A, hA, hB'⟩
      · cases h1
      · rw [List.mem_filterMap] at hB'
        obtain ⟨v, _, hv⟩ := hB'
        split at hv
        · rename_i hAv
          simp only [Option.some.injEq, Outcome.val.injEq] at hv
          subst hv
          refine ⟨.val (USet.map2 (· * ·) (USet.single (BitVec.ofNat w 2)) A), ?_, ?_⟩
          · simp only [semU, bind2, bind1_val_singleton]
            exact mem_bind1.mpr (Or.inr ⟨A, hA, by simp⟩)
          · intro z hz
            simp only [USet.map2, USet.single, decide_eq_true_eq] at hz ⊢
            obtain ⟨p, q, hp, hq, hpq⟩ := hz
            subst hp hq
            exact ⟨_, _, rfl, hAv, by rw [two_mul_eq_add_self]; exact hpq⟩
        · simp at hv

/-- **Escape hatch (poison + freeze model): duplicate a frozen copy instead.** For every
width `w`, expression `e` and variable `a`, rewriting `2 * e` to `let a := freeze e; a + a`
is a refinement in the poison + freeze model. -/
theorem poisonFreeze_rewrite_two_mul_to_let_freeze_add_self_sound (w : Nat) (e : Expr)
    (a : Var) : RefinesP w (.letE a (.freeze e) (.add (.var a) (.var a))) (.mul (.const 2) e) := by
  intro ρ
  by_cases hS : Outcome.ub ∈ semP w ρ e
  · left
    rw [mayUB_iff]
    simp only [semP, bind2, bind1_val_singleton]
    exact ub_mem_bind1_of_ub_mem hS
  · right
    intro o ho
    have ho' : o ∈ bind1 (semP w ρ (.freeze e))
        (fun v => semP w (update ρ a v) (.add (.var a) (.var a))) := ho
    rcases mem_bind1.mp ho' with ⟨rfl, h⟩ | ⟨v, hv, ho2⟩
    · exfalso
      apply hS
      simp only [semP] at h
      rcases mem_bind1.mp h with ⟨_, h'⟩ | ⟨v0, _, hv0⟩
      · exact h'
      · cases v0 <;> simp at hv0
    · simp [semP, bind2, update] at ho2
      subst ho2
      simp only [semP] at hv
      rcases mem_bind1.mp hv with ⟨h1, _⟩ | ⟨v0, hv0, hv⟩
      · cases h1
      · refine ⟨.val (PVal.lift2 (· * ·) (.int (BitVec.ofNat w 2)) v0), ?_, ?_⟩
        · simp only [semP, bind2, bind1_val_singleton]
          exact mem_bind1.mpr (Or.inr ⟨v0, hv0, by simp⟩)
        · cases v0 with
          | poison => simp [Outcome.LeVal, PVal.lift2, PVal.Refines]
          | int u =>
            simp at hv
            subst hv
            simp [Outcome.LeVal, PVal.lift2, PVal.Refines, two_mul_eq_add_self]

/-- **Escape hatch (undef model): a well-defined input.** For every width `w`, variable
`x` and environment binding `x` to a singleton `{v}`, the outcomes of `x + x` refine those
of `2 * x`. -/
theorem undef_rewrite_two_mul_to_add_self_sound_at_singleton (w : Nat) (x : Var)
    (ρ : Var → USet w) (v : BitVec w) (hx : ρ x = USet.single v) :
    OutRef USet.Sub (semU w ρ (.add (.var x) (.var x))) (semU w ρ (.mul (.const 2) (.var x))) := by
  have ht : semU w ρ (.add (.var x) (.var x)) = [.val (USet.map2 (· + ·) (ρ x) (ρ x))] := by
    simp [semU, bind2]
  have hs : semU w ρ (.mul (.const 2) (.var x)) =
      [.val (USet.map2 (· * ·) (USet.single (BitVec.ofNat w 2)) (ρ x))] := by
    simp [semU, bind2]
  rw [ht, hs]
  apply outRef_singleton_val
  intro z hz
  rw [hx] at hz ⊢
  simp only [USet.map2, USet.single, decide_eq_true_eq] at hz ⊢
  obtain ⟨p, q, hp, hq, hpq⟩ := hz
  subst hp hq
  exact ⟨_, _, rfl, rfl, by rw [two_mul_eq_add_self]; exact hpq⟩

/-- **Escape hatch (poison + freeze model): a non-poison input.** For every width `w`,
variable `x` and environment with `x ↦ v` (an integer), the outcomes of
`freeze x + freeze x` refine those of `2 * freeze x`. -/
theorem poisonFreeze_rewrite_two_mul_freeze_sound_at_int (w : Nat) (x : Var)
    (ρ : Var → PVal w) (v : BitVec w) (hx : ρ x = .int v) :
    OutRef PVal.Refines (semP w ρ (.add (.freeze (.var x)) (.freeze (.var x))))
      (semP w ρ (.mul (.const 2) (.freeze (.var x)))) := by
  have h1 : semP w ρ (.add (.freeze (.var x)) (.freeze (.var x))) = [.val (.int (v + v))] := by
    simp [semP, bind2, hx, PVal.lift2]
  have h2 : semP w ρ (.mul (.const 2) (.freeze (.var x))) = [.val (.int (v + v))] := by
    simp [semP, bind2, hx, PVal.lift2, two_mul_eq_add_self]
  rw [h1, h2]
  exact outRef_refl PVal.Refines.refl _

end Toy.UB
