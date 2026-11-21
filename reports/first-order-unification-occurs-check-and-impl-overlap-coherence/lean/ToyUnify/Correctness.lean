import ToyUnify.UnifyLemmas

/-!
# Soundness, idempotence, most generality, completeness and termination of `unify`

Main results:

* `unify_sound`, `unify_idempotent`: an output of `unify` is an idempotent unifier.
* `unify_mgu_factor` (with corollary `unify_moreGeneral`): every unifier `τ` of the input
  satisfies `τ ∘ σ = τ` on every term, so `σ` is most general and the factor is `τ` itself.
* `unify_complete` (with corollary `unify_eq_none_iff`): if a unifier exists, `unify` returns one;
  `none` means no unifier exists.
* `run_ne_outOfFuel_of_numVars_le`: with the occurs check on, fuel equal to the number of
  distinct variables suffices (each pass eliminates one variable from the pending equations).

The proofs use the invariant `Inv` of `ToyUnify.UnifyLemmas`: the accumulated substitution is in
solved form, and every pass preserves the solutions of the combined system `Sys`.
-/

namespace Toy.Unify

/-! ## Main statements -/

theorem unify_eq_some_iff_run {s t : Term} {σ : Subst} :
    unify s t = some σ ↔ run true (numVars [(s, t)]) [(s, t)] [] = .ok σ := by
  unfold unify
  cases run true (numVars [(s, t)]) [(s, t)] [] <;> simp [Result.toOption]

/-- In a solved substitution, no bound variable occurs in a right-hand side, so applying the
substitution to a right-hand side changes nothing. -/
theorem subst_rhs_of_solved {σ : Subst} (hrhs : ∀ p ∈ σ, ∀ q ∈ σ, q.1 ∉ p.2.vars)
    {p : Nat × Term} (hp : p ∈ σ) : subst σ p.2 = p.2 :=
  subst_eq_self_of_vars _ (fun _ hz => substVar_of_not_key (fun q hq h => hrhs p hp q hq (h ▸ hz)))

theorem sys_single_iff (τ : Subst) (s t : Term) : Sys τ [(s, t)] [] ↔ Unifies τ s t := by
  simp [Sys, Unifies]

/-- Soundness: an output of `unify` unifies the two input terms. -/
theorem unify_sound {s t : Term} {σ : Subst} (h : unify s t = some σ) : Unifies σ s t := by
  obtain ⟨⟨hnd, hrhs, _⟩, hsys⟩ := run_true_ok _ _ _ _ (unify_eq_some_iff_run.1 h) (inv_init _)
  have hself : Sys σ [] σ :=
    ⟨nofun, fun p hp => by rw [substVar_of_mem_nodup hnd hp, subst_rhs_of_solved hrhs hp]⟩
  exact (sys_single_iff σ s t).1 ((hsys σ).2 hself)

/-- Idempotence: an output of `unify` is idempotent. -/
theorem unify_idempotent {s t : Term} {σ : Subst} (h : unify s t = some σ) : Idempotent σ := by
  obtain ⟨⟨_, hrhs, _⟩, _⟩ := run_true_ok _ _ _ _ (unify_eq_some_iff_run.1 h) (inv_init _)
  intro u
  refine (subst_comp_of_vars u (fun x _ => ?_)).symm
  rcases substVar_cases σ x with ⟨q, hq, _, hx⟩ | hx
  · rw [hx, subst_rhs_of_solved hrhs hq]
  · rw [hx]
    exact hx.symm

/-- Most generality, with the factor exposed: if `unify s t = some σ` and `τ` is any unifier of
`s` and `t`, then `τ (σ u) = τ u` for every term `u`. -/
theorem unify_mgu_factor {s t : Term} {σ τ : Subst} (h : unify s t = some σ)
    (hτ : Unifies τ s t) : ∀ u : Term, subst τ (subst σ u) = subst τ u := by
  obtain ⟨_, hsys⟩ := run_true_ok _ _ _ _ (unify_eq_some_iff_run.1 h) (inv_init _)
  have hb := ((hsys τ).1 ((sys_single_iff τ s t).2 hτ)).2
  intro u
  refine (subst_comp_of_vars u (fun x _ => ?_)).symm
  rcases substVar_cases σ x with ⟨q, hq, hqx, hx⟩ | hx
  · rw [hx, ← hb q hq, hqx]
  · rw [hx]
    rfl

/-- Corollary of `unify_mgu_factor`: an output of `unify` is more general than every unifier. -/
theorem unify_moreGeneral {s t : Term} {σ τ : Subst} (h : unify s t = some σ)
    (hτ : Unifies τ s t) : MoreGeneral σ τ :=
  ⟨τ, fun u => (unify_mgu_factor h hτ u).symm⟩

/-- Completeness: if some substitution unifies `s` and `t`, then `unify s t` returns a
substitution. -/
theorem unify_complete {s t : Term} {τ : Subst} (hτ : Unifies τ s t) :
    ∃ σ, unify s t = some σ := by
  cases hr : run true (numVars [(s, t)]) [(s, t)] [] with
  | ok σ => exact ⟨σ, unify_eq_some_iff_run.2 hr⟩
  | fail => exact absurd ((sys_single_iff τ s t).2 hτ) (run_true_fail _ _ _ hr τ)
  | outOfFuel => exact absurd hr (run_true_ne_outOfFuel _ _ _ (Nat.le_refl _))

/-- Corollary of `unify_sound` and `unify_complete`: `unify` returns `none` exactly when the
terms have no unifier. -/
theorem unify_eq_none_iff (s t : Term) : unify s t = none ↔ ¬ Unifiable s t := by
  constructor
  · rintro h ⟨τ, hτ⟩
    obtain ⟨σ, hσ⟩ := unify_complete hτ
    rw [h] at hσ
    cases hσ
  · intro h
    cases hu : unify s t with
    | none => rfl
    | some σ => exact absurd ⟨σ, unify_sound hu⟩ h

/-- Termination with an explicit measure: with the occurs check on (`oc = true`), a run whose
fuel is at least the number of distinct variables of the pending equations never runs out of
fuel, whatever the initial accumulator substitution `σ` (it need not be in solved form; `step`
only writes to it). -/
theorem run_ne_outOfFuel_of_numVars_le (oc : Bool) (hoc : oc = true) (fuel : Nat)
    (eqs : List (Term × Term)) (σ : Subst) (hfuel : numVars eqs ≤ fuel) :
    run oc fuel eqs σ ≠ .outOfFuel := by
  subst hoc
  exact run_true_ne_outOfFuel fuel eqs σ hfuel

/-! ## Non-vacuity witnesses -/

/-- `unify (X, Box Y) (Box u8, X)` returns a substitution (hypothesis of `unify_sound` and
`unify_idempotent` satisfiable). -/
theorem unify_sound_nonvacuous :
    unify (pair (.var 0) (box (.var 1))) (pair (box u8) (.var 0)) =
      some [(1, u8), (0, box u8)] := by decide

/-- Hypotheses of `unify_mgu_factor` hold together: `unify` returns `[X ↦ (Y, u8)]` and
`[X ↦ (u32, u8), Y ↦ u32]` is a unifier. -/
theorem unify_mgu_factor_nonvacuous :
    unify (.var 0) (pair (.var 1) u8) = some [(0, pair (.var 1) u8)] ∧
      Unifies [(0, pair u32 u8), (1, u32)] (.var 0) (pair (.var 1) u8) := by decide

/-- Hypothesis of `unify_complete` satisfiable. -/
theorem unify_complete_nonvacuous : Unifies [(0, u8)] (pair (.var 0) u8) (pair u8 (.var 0)) := by
  decide

/-- Hypotheses of `run_ne_outOfFuel_of_numVars_le` hold together (fuel = measure = 2). -/
theorem run_ne_outOfFuel_nonvacuous :
    numVars [(pair (.var 0) (.var 1), pair (.var 1) u8)] ≤ 2 := by decide

/-! ## Tightness counterexamples -/

/-- Without `h`, `unify_sound`'s conclusion fails: `[]` is not the output on `X =? u8` and does
not unify it. -/
theorem unify_sound_needs_output : unify (.var 0) u8 ≠ some [] ∧ ¬ Unifies [] (.var 0) u8 := by
  decide

/-- Without `h`, `unify_idempotent`'s conclusion fails: `[X ↦ Box X]` is not idempotent (it is
the output of the occurs-check-free variant on `X =? Box X`, not of `unify`). -/
theorem unify_idempotent_needs_output :
    unify (.var 0) (box (.var 0)) ≠ some [(0, box (.var 0))] ∧
      ¬ Idempotent [(0, box (.var 0))] :=
  ⟨by decide, not_idempotent_example⟩

/-- Without `hτ`, the conclusions of `unify_mgu_factor` and `unify_moreGeneral` fail (instance
with one nullary constructor and one variable): `unify (X, u8) = [X ↦ u8]`, the non-unifier `[]`
does not satisfy `[] ∘ σ = []` at `X`, and `[]` is not an instance of `[X ↦ u8]`. -/
theorem unify_mgu_factor_needs_unifier :
    unify (.var 0) u8 = some [(0, u8)] ∧ ¬ Unifies [] (.var 0) u8 ∧
      subst [] (subst [(0, u8)] (.var 0)) ≠ subst [] (.var 0) ∧
      ¬ MoreGeneral [(0, u8)] [] := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  rintro ⟨ρ, hρ⟩
  have h0 := hρ (.var 0)
  simp [subst_var, substVar_cons, substVar_nil, u8, subst_con] at h0

/-- Without `h`, the conclusions of `unify_mgu_factor` and `unify_moreGeneral` fail (instance
with two variables and two nullary constructors): `[X ↦ u8, Y ↦ u8]` unifies `X =? Y` but is not
the output of `unify`, and the unifier `[X ↦ u32, Y ↦ u32]` neither factors through it nor is an
instance of it. -/
theorem unify_mgu_factor_needs_output :
    unify (.var 0) (.var 1) ≠ some [(0, u8), (1, u8)] ∧
      Unifies [(0, u32), (1, u32)] (.var 0) (.var 1) ∧
      subst [(0, u32), (1, u32)] (subst [(0, u8), (1, u8)] (.var 0)) ≠
        subst [(0, u32), (1, u32)] (.var 0) ∧
      ¬ MoreGeneral [(0, u8), (1, u8)] [(0, u32), (1, u32)] := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  rintro ⟨ρ, hρ⟩
  have h0 := hρ (.var 0)
  simp [subst_var, substVar_cons, u8, u32, subst_con] at h0

/-- Without `hτ`, `unify_complete`'s conclusion fails (instance: two nullary constructors):
`u8 =? u32` has no output. -/
theorem unify_complete_needs_unifier :
    ¬ Unifies [] u8 u32 ∧ unify u8 u32 = none ∧ ¬ ∃ σ, unify u8 u32 = some σ := by
  refine ⟨by decide, by decide, ?_⟩
  rintro ⟨σ, hσ⟩
  have h : unify u8 u32 = none := by decide
  rw [h] at hσ
  cases hσ

/-- Without `hfuel`: fuel `0` is below the measure `1` of `X =? u8`, and the run runs out. -/
theorem run_needs_fuel_bound :
    numVars [(.var 0, u8)] = 1 ∧ run true 0 [(.var 0, u8)] [] = .outOfFuel := by decide

/-- Without `hoc` (occurs check off), fuel equal to the measure can run out: on
`(X, (X, Y)) =? (Box X, (Box Y, Vec Y))` (measure 2), `X` is eliminated twice. -/
theorem run_needs_occurs_check_for_bound :
    numVars [(pair (.var 0) (pair (.var 0) (.var 1)),
        pair (box (.var 0)) (pair (box (.var 1)) (vec (.var 1))))] = 2 ∧
      run false 2 [(pair (.var 0) (pair (.var 0) (.var 1)),
        pair (box (.var 0)) (pair (box (.var 1)) (vec (.var 1))))] [] = .outOfFuel := by decide

end Toy.Unify
