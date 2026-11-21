import ToyUnify.Correctness

/-!
# The occurs check: finite terms, the occurs-check-free variant, and infinite unfoldings

* `not_unifiable_var_of_occurs`: `x =? u` with `x` occurring in `u ≠ x` has no finite unifier
  (this is what makes the occurs-check failure branch of `unify` sound).
* `unifyNoOC_returns_nonunifier_var_box`: without the occurs check, `X =? Box X` yields
  `[X ↦ Box X]`, which is not a unifier, and no finite unifier exists.
* `run_false_eq_ok_of_run_true_eq_ok`, `unifyNoOC_eq_some_of_unify_eq_some`: removing the occurs
  check changes nothing on inputs where `unify` succeeds.
* `unifyNoOC_unifies_iff_unifiable`: an output of the occurs-check-free variant is a unifier
  exactly when the input is unifiable.
* Infinite unfoldings (finite-depth approximation): `unifyNoOC_eqUpTo_of_nodup` (the cyclic
  output is a solution in the depth-indexed sense when no variable was eliminated twice), and
  `unifyNoOC_eqUpTo_fails_with_duplicate_elimination` (in general it is not).
-/

namespace Toy.Unify

/-! ## Helper lemmas -/

theorem iterSubst_con (σ : Subst) :
    ∀ (k f : Nat) (ts : List Term), iterSubst σ k (.con f ts) = .con f (ts.map (iterSubst σ k))
  | 0, f, ts => by simp [iterSubst]
  | k + 1, f, ts => by
    simp only [iterSubst, subst_con, iterSubst_con σ k, List.map_map]
    rfl

/-! ## Finite terms -/

/-- A variable does not unify (over finite terms) with a different term in which it occurs. -/
theorem not_unifiable_var_of_occurs {x : Nat} {u : Term} (hocc : occurs x u = true)
    (hne : u ≠ .var x) : ¬ Unifiable (.var x) u := by
  rintro ⟨σ, h⟩
  exact not_unifies_var_of_occurs hocc hne σ h

/-- Non-vacuity for `not_unifiable_var_of_occurs`: `X` occurs in `Box X ≠ X`. -/
theorem not_unifiable_var_of_occurs_nonvacuous :
    occurs 0 (box (.var 0)) = true ∧ box (.var 0) ≠ .var 0 := by decide

/-- Without `hocc`: `X` does not occur in `Box Y`, and `X =? Box Y` is unifiable. -/
theorem not_unifiable_var_of_occurs_needs_occurs :
    occurs 0 (box (.var 1)) = false ∧ box (.var 1) ≠ .var 0 ∧
      Unifiable (.var 0) (box (.var 1)) :=
  ⟨by decide, by decide, ⟨[(0, box (.var 1))], by decide⟩⟩

/-- Without `hne`: `X` occurs in `X`, and `X =? X` is unifiable. -/
theorem not_unifiable_var_of_occurs_needs_ne :
    occurs 0 (.var 0) = true ∧ Unifiable (.var 0) (.var 0) :=
  ⟨by decide, ⟨[], by decide⟩⟩

/-! ## Without the occurs check, the algorithm returns a non-unifier -/

/-- On `X =? Box X`, the occurs-check-free variant returns `[X ↦ Box X]`; this is not a unifier;
no finite unifier exists; and `unify` returns `none`. -/
theorem unifyNoOC_returns_nonunifier_var_box :
    unifyNoOC (.var 0) (box (.var 0)) = some [(0, box (.var 0))] ∧
      ¬ Unifies [(0, box (.var 0))] (.var 0) (box (.var 0)) ∧
      ¬ Unifiable (.var 0) (box (.var 0)) ∧
      unify (.var 0) (box (.var 0)) = none :=
  ⟨by decide, by decide, not_unifiable_var_box, by decide⟩

/-! ## Agreement on unifiable inputs -/

/-- If the run with the occurs check returns `ok σ'`, the run without it, from the same fuel,
equations and initial accumulator substitution `σ` (arbitrary; it need not be in solved form),
returns the same `ok σ'`. -/
theorem run_false_eq_ok_of_run_true_eq_ok {fuel : Nat} {eqs : List (Term × Term)}
    {σ σ' : Subst} (h : run true fuel eqs σ = .ok σ') : run false fuel eqs σ = .ok σ' := by
  induction fuel generalizing eqs σ with
  | zero =>
    unfold run at h ⊢
    rcases step_cases true eqs σ with ⟨hd, hs⟩ | ⟨hd, hs⟩ | ⟨_, _, _, _, _, _, hs⟩ |
        ⟨x, u, bs, hd, _, hs⟩
    · rw [hs] at h; cases h
    · rw [hs] at h
      rcases step_cases false eqs σ with ⟨hd', _⟩ | ⟨_, hs'⟩ | ⟨_, _, _, _, hf, _, _⟩ |
          ⟨_, _, _, hd', _, _⟩
      · rw [hd] at hd'; cases hd'
      · rw [hs']; exact h
      · cases hf
      · rw [hd] at hd'; cases hd'
    · rw [hs] at h; cases h
    · rw [hs] at h; cases h
  | succ n ih =>
    unfold run at h ⊢
    rcases step_cases true eqs σ with ⟨hd, hs⟩ | ⟨hd, hs⟩ | ⟨_, _, _, _, _, _, hs⟩ |
        ⟨x, u, bs, hd, _, hs⟩
    · rw [hs] at h; cases h
    · rw [hs] at h
      rcases step_cases false eqs σ with ⟨hd', _⟩ | ⟨_, hs'⟩ | ⟨_, _, _, _, hf, _, _⟩ |
          ⟨_, _, _, hd', _, _⟩
      · rw [hd] at hd'; cases hd'
      · rw [hs']; exact h
      · cases hf
      · rw [hd] at hd'; cases hd'
    · rw [hs] at h; cases h
    · rw [hs] at h
      rcases step_cases false eqs σ with ⟨hd', _⟩ | ⟨hd', _⟩ | ⟨_, _, _, _, hf, _, _⟩ |
          ⟨x', u', bs', hd', _, hs'⟩
      · rw [hd] at hd'; cases hd'
      · rw [hd] at hd'; cases hd'
      · cases hf
      · rw [hd] at hd'
        simp only [Option.some.injEq, List.cons.injEq, Prod.mk.injEq] at hd'
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hd'
        rw [hs']
        exact ih h

/-- Corollary: whenever `unify` succeeds, `unifyNoOC` returns the same substitution. -/
theorem unifyNoOC_eq_some_of_unify_eq_some {s t : Term} {σ : Subst} (h : unify s t = some σ) :
    unifyNoOC s t = some σ := by
  unfold unify at h
  unfold unifyNoOC
  cases hr : run true (numVars [(s, t)]) [(s, t)] [] with
  | ok σ'' =>
    rw [hr] at h
    simp only [Result.toOption, Option.some.injEq] at h
    subst h
    rw [run_false_eq_ok_of_run_true_eq_ok hr]
    rfl
  | fail => rw [hr] at h; simp [Result.toOption] at h
  | outOfFuel => rw [hr] at h; simp [Result.toOption] at h

/-- Without `h`, `unifyNoOC_eq_some_of_unify_eq_some`'s conclusion fails for an arbitrary
substitution: `[]` is the output of neither variant on `X =? u8`. -/
theorem unifyNoOC_eq_some_needs_unify_output :
    unify (.var 0) u8 ≠ some [] ∧ unifyNoOC (.var 0) u8 ≠ some [] := by decide

/-- Non-vacuity for the agreement results: `unify` succeeds on `(X, u8) =? (u32, Y)`. -/
theorem agreement_nonvacuous :
    run true (numVars [(pair (.var 0) u8, pair u32 (.var 1))])
      [(pair (.var 0) u8, pair u32 (.var 1))] [] = .ok [(1, u8), (0, u32)] := by decide

/-- Without `h`, the agreement's conclusion fails for an arbitrary `σ'`: with no fuel, both runs
on `X =? u8` run out instead of returning `ok []`. -/
theorem run_agreement_needs_run_true_ok :
    run true 0 [(.var 0, u8)] [] ≠ .ok [] ∧ run false 0 [(.var 0, u8)] [] ≠ .ok [] := by decide

/-- The converse of the agreement fails: the occurs-check-free run succeeds on `X =? Box X`
while the run with the occurs check fails. -/
theorem run_true_ne_ok_of_run_false_ok_example :
    run false 1 [(.var 0, box (.var 0))] [] = .ok [(0, box (.var 0))] ∧
      run true 1 [(.var 0, box (.var 0))] [] = .fail := by decide

/-- Characterization: an output of `unifyNoOC` is a unifier if and only if the input pair is
unifiable (so the variant errs exactly by returning a substitution on non-unifiable inputs). -/
theorem unifyNoOC_unifies_iff_unifiable {s t : Term} {σ : Subst} (h : unifyNoOC s t = some σ) :
    Unifies σ s t ↔ Unifiable s t := by
  constructor
  · exact fun hu => ⟨σ, hu⟩
  · rintro ⟨τ, hτ⟩
    obtain ⟨σ', hσ'⟩ := unify_complete hτ
    have h' := unifyNoOC_eq_some_of_unify_eq_some hσ'
    rw [h] at h'
    cases h'
    exact unify_sound hσ'

/-- Without `h`, the equivalence fails for an arbitrary substitution: `X =? u8` is unifiable but
`[]` (not the output) does not unify it. -/
theorem unifyNoOC_unifies_iff_needs_output :
    unifyNoOC (.var 0) u8 ≠ some [] ∧ ¬ (Unifies [] (.var 0) u8 ↔ Unifiable (.var 0) u8) := by
  refine ⟨by decide, fun h => ?_⟩
  have : Unifies [] (.var 0) u8 := h.2 ⟨[(0, u8)], by decide⟩
  revert this
  decide

/-- Non-vacuity for `unifyNoOC_unifies_iff_unifiable` (both a unifiable and a non-unifiable
input satisfy its hypothesis). -/
theorem unifyNoOC_unifies_iff_unifiable_nonvacuous :
    unifyNoOC (pair (.var 0) u8) (pair u32 (.var 1)) = some [(1, u8), (0, u32)] ∧
      unifyNoOC (.var 0) (box (.var 0)) = some [(0, box (.var 0))] := by decide

/-! ## Infinite unfoldings, approximated by depth -/

/-- Without `h`, `unifyNoOC_eqUpTo_of_nodup` fails for an arbitrary substitution: the empty
substitution has distinct bound variables, yet `X` and `u8` disagree at depth 1 after any number
of unfoldings. -/
theorem unifyNoOC_eqUpTo_needs_output :
    unifyNoOC (.var 0) u8 ≠ some [] ∧ (([] : Subst).map Prod.fst).Nodup ∧
      (∀ k, eqUpTo 1 (iterSubst [] k (.var 0)) (iterSubst [] k u8) = false) ∧
      ¬ (∀ n, ∃ k, eqUpTo n (iterSubst [] k (.var 0)) (iterSubst [] k u8) = true) := by
  have h0 : ∀ k t, iterSubst [] k t = t := by
    intro k
    induction k with
    | zero => intro t; rfl
    | succ k ih => intro t; simp only [iterSubst, subst_nil, ih]
  have hall : ∀ k, eqUpTo 1 (iterSubst [] k (.var 0)) (iterSubst [] k u8) = false := by
    intro k
    rw [h0, h0]
    decide
  refine ⟨by decide, by decide, hall, fun h => ?_⟩
  obtain ⟨k, hk⟩ := h 1
  rw [hall k] at hk
  cases hk

mutual
/-- Depth-indexed agreement is reflexive. -/
theorem eqUpTo_refl : ∀ (n : Nat) (t : Term), eqUpTo n t t = true
  | 0, _ => by simp [eqUpTo]
  | _ + 1, .var _ => by simp [eqUpTo]
  | n + 1, .con f ts => by
    simp only [eqUpTo, beq_self_eq_true, Bool.true_and]
    exact eqUpToList_refl n ts
/-- List companion of `eqUpTo_refl`. -/
theorem eqUpToList_refl : ∀ (n : Nat) (ts : List Term), eqUpToList n ts ts = true
  | _, [] => by simp [eqUpToList]
  | n, t :: ts => by simp [eqUpToList, eqUpTo_refl n t, eqUpToList_refl n ts]
end

mutual
/-- Depth-indexed agreement is a congruence for substitution: if `a` and `b` agree up to depth
`n`, so do `σ a` and `σ b`. -/
theorem eqUpTo_subst : ∀ {n : Nat} {a b : Term} (σ : Subst), eqUpTo n a b = true →
    eqUpTo n (subst σ a) (subst σ b) = true
  | 0, _, _, _, _ => by simp [eqUpTo]
  | _ + 1, .var x, .var y, σ, h => by
    simp only [eqUpTo, beq_iff_eq] at h
    subst h
    exact eqUpTo_refl _ _
  | _ + 1, .var _, .con _ _, _, h => by simp [eqUpTo] at h
  | _ + 1, .con _ _, .var _, _, h => by simp [eqUpTo] at h
  | n + 1, .con f ss, .con g ts, σ, h => by
    simp only [eqUpTo, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    simp only [subst, eqUpTo, beq_self_eq_true, Bool.true_and]
    exact eqUpToList_subst σ h
/-- List companion of `eqUpTo_subst`. -/
theorem eqUpToList_subst : ∀ {n : Nat} {ss ts : List Term} (σ : Subst),
    eqUpToList n ss ts = true → eqUpToList n (substList σ ss) (substList σ ts) = true
  | _, [], [], _, _ => by simp [eqUpToList, substList]
  | _, s :: ss, t :: ts, σ, h => by
    simp only [eqUpToList, Bool.and_eq_true] at h
    simp only [substList, eqUpToList, Bool.and_eq_true]
    exact ⟨eqUpTo_subst σ h.1, eqUpToList_subst σ h.2⟩
  | _, [], _ :: _, _, h => by simp [eqUpToList] at h
  | _, _ :: _, [], _, h => by simp [eqUpToList] at h
end

/-- `iterSubst σ (k + 1) t` is `σ` applied once more on the outside. -/
theorem iterSubst_succ' (σ : Subst) : ∀ (k : Nat) (t : Term),
    iterSubst σ (k + 1) t = subst σ (iterSubst σ k t)
  | 0, _ => rfl
  | k + 1, t => by
    show iterSubst σ (k + 1) (subst σ t) = subst σ (iterSubst σ k (subst σ t))
    exact iterSubst_succ' σ k (subst σ t)

/-- Agreement of the `k`-fold unfoldings up to depth `n` persists for every larger number of
unfoldings `m ≥ k`. -/
theorem eqUpTo_iterSubst_mono {n k m : Nat} {a b : Term} (σ : Subst) (hkm : k ≤ m)
    (h : eqUpTo n (iterSubst σ k a) (iterSubst σ k b) = true) :
    eqUpTo n (iterSubst σ m a) (iterSubst σ m b) = true := by
  induction m with
  | zero =>
    have : k = 0 := by omega
    subst this
    exact h
  | succ m ih =>
    rcases Nat.lt_or_ge m k with hlt | hge
    · have : k = m + 1 := by omega
      subst this
      exact h
    · rw [iterSubst_succ', iterSubst_succ']
      exact eqUpTo_subst σ (ih hge)

/-- Without `h`, `eqUpTo_subst`'s conclusion fails (instance: two nullary constructors, empty
substitution): `u8` and `u32` disagree at depth 1 before and after applying `[]`. -/
theorem eqUpTo_subst_needs_agreement :
    eqUpTo 1 u8 u32 = false ∧ eqUpTo 1 (subst [] u8) (subst [] u32) = false := by decide

/-- Non-vacuity for `eqUpTo_subst`: `Box u8` and `Box u32` agree up to depth 1 although they
differ. -/
theorem eqUpTo_subst_nonvacuous : eqUpTo 1 (box u8) (box u32) = true ∧ box u8 ≠ box u32 := by
  decide

/-- Non-vacuity for `eqUpTo_iterSubst_mono`: `k = 0 ≤ m = 3`, and the 0-fold unfoldings of
`Box u8`, `Box u32` agree up to depth 1. -/
theorem eqUpTo_iterSubst_mono_nonvacuous :
    0 ≤ 3 ∧ eqUpTo 1 (iterSubst [] 0 (box u8)) (iterSubst [] 0 (box u32)) = true := by decide

/-- Without `hkm` (instance: one binding `X ↦ u8`, `k = 1`, `m = 0`): after one unfolding `X` and
`u8` agree up to depth 1, but before it they do not. -/
theorem eqUpTo_iterSubst_mono_needs_le :
    ¬ (1 ≤ 0) ∧ eqUpTo 1 (iterSubst [(0, u8)] 1 (.var 0)) (iterSubst [(0, u8)] 1 u8) = true ∧
      eqUpTo 1 (iterSubst [(0, u8)] 0 (.var 0)) (iterSubst [(0, u8)] 0 u8) = false := by decide

/-- Without `h` (instance: two nullary constructors, empty substitution, `k = 0`, `m = 1`): `u8`
and `u32` disagree at depth 1 after 0 unfoldings (so `h` fails) and after 1 unfolding (so the
conclusion fails), while `k ≤ m` holds. -/
theorem eqUpTo_iterSubst_mono_needs_agreement :
    0 ≤ 1 ∧ eqUpTo 1 (iterSubst [] 0 u8) (iterSubst [] 0 u32) = false ∧
      eqUpTo 1 (iterSubst [] 1 u8) (iterSubst [] 1 u32) = false := by decide

mutual
theorem eq_of_forall_eqUpTo : ∀ (a b : Term), (∀ n, eqUpTo n a b = true) → a = b
  | .var x, .var y, h => by
    have := h 1
    simp only [eqUpTo, beq_iff_eq] at this
    rw [this]
  | .var _, .con _ _, h => by have := h 1; simp [eqUpTo] at this
  | .con _ _, .var _, h => by have := h 1; simp [eqUpTo] at this
  | .con f ss, .con g ts, h => by
    have h1 := h 1
    simp only [eqUpTo, Bool.and_eq_true, beq_iff_eq] at h1
    obtain ⟨rfl, _⟩ := h1
    have hl : ∀ n, eqUpToList n ss ts = true := fun n => by
      have := h (n + 1)
      simp only [eqUpTo, Bool.and_eq_true, beq_iff_eq] at this
      exact this.2
    rw [eq_of_forall_eqUpToList ss ts hl]
theorem eq_of_forall_eqUpToList : ∀ (ss ts : List Term), (∀ n, eqUpToList n ss ts = true) →
    ss = ts
  | [], [], _ => rfl
  | [], _ :: _, h => by have := h 0; simp [eqUpToList] at this
  | _ :: _, [], h => by have := h 0; simp [eqUpToList] at this
  | s :: ss, t :: ts, h => by
    have hs : ∀ n, eqUpTo n s t = true := fun n => by
      have := h n
      simp only [eqUpToList, Bool.and_eq_true] at this
      exact this.1
    have hss : ∀ n, eqUpToList n ss ts = true := fun n => by
      have := h n
      simp only [eqUpToList, Bool.and_eq_true] at this
      exact this.2
    rw [eq_of_forall_eqUpTo s t hs, eq_of_forall_eqUpToList ss ts hss]
end

/-- On finite terms, agreement at every depth is equality. -/
theorem eqUpTo_forall_iff_eq (a b : Term) : (∀ n, eqUpTo n a b = true) ↔ a = b := by
  constructor
  · exact eq_of_forall_eqUpTo a b
  · rintro rfl n
    exact eqUpTo_refl n a

/-! ## Agreement in the limit

Auxiliary development for `unifyNoOC_eqUpTo_of_nodup`. `LimEq σ a b`: for every depth some number
of unfoldings by `σ` makes `a` and `b` agree up to that depth. It is an equivalence relation and a
congruence, every pass of the algorithm preserves it backwards, and a duplicate-free output solves
its own bindings in this sense because its var-to-var bindings form chains of length at most one.
-/

mutual
theorem eqUpTo_symm : ∀ (n : Nat) (a b : Term), eqUpTo n a b = true → eqUpTo n b a = true
  | 0, _, _, _ => by simp [eqUpTo]
  | _ + 1, .var x, .var y, h => by
    simp only [eqUpTo, beq_iff_eq] at h ⊢
    exact h.symm
  | _ + 1, .var _, .con _ _, h => by simp [eqUpTo] at h
  | _ + 1, .con _ _, .var _, h => by simp [eqUpTo] at h
  | n + 1, .con f ss, .con g ts, h => by
    simp only [eqUpTo, Bool.and_eq_true, beq_iff_eq] at h ⊢
    exact ⟨h.1.symm, eqUpToList_symm n ss ts h.2⟩
theorem eqUpToList_symm : ∀ (n : Nat) (ss ts : List Term), eqUpToList n ss ts = true →
    eqUpToList n ts ss = true
  | _, [], [], _ => by simp [eqUpToList]
  | n, s :: ss, t :: ts, h => by
    simp only [eqUpToList, Bool.and_eq_true] at h ⊢
    exact ⟨eqUpTo_symm n s t h.1, eqUpToList_symm n ss ts h.2⟩
  | _, [], _ :: _, h => by simp [eqUpToList] at h
  | _, _ :: _, [], h => by simp [eqUpToList] at h
end

mutual
theorem eqUpTo_trans : ∀ (n : Nat) (a b c : Term), eqUpTo n a b = true → eqUpTo n b c = true →
    eqUpTo n a c = true
  | 0, _, _, _, _, _ => by simp [eqUpTo]
  | _ + 1, .var x, .var y, .var z, h1, h2 => by
    simp only [eqUpTo, beq_iff_eq] at h1 h2 ⊢
    exact h1.trans h2
  | _ + 1, .var _, .var _, .con _ _, _, h2 => by simp [eqUpTo] at h2
  | _ + 1, .var _, .con _ _, _, h1, _ => by simp [eqUpTo] at h1
  | _ + 1, .con _ _, .var _, _, h1, _ => by simp [eqUpTo] at h1
  | _ + 1, .con _ _, .con _ _, .var _, _, h2 => by simp [eqUpTo] at h2
  | n + 1, .con f ss, .con g ts, .con k us, h1, h2 => by
    simp only [eqUpTo, Bool.and_eq_true, beq_iff_eq] at h1 h2 ⊢
    exact ⟨h1.1.trans h2.1, eqUpToList_trans n ss ts us h1.2 h2.2⟩
theorem eqUpToList_trans : ∀ (n : Nat) (ss ts us : List Term), eqUpToList n ss ts = true →
    eqUpToList n ts us = true → eqUpToList n ss us = true
  | _, [], [], [], _, _ => by simp [eqUpToList]
  | n, s :: ss, t :: ts, u :: us, h1, h2 => by
    simp only [eqUpToList, Bool.and_eq_true] at h1 h2 ⊢
    exact ⟨eqUpTo_trans n s t u h1.1 h2.1, eqUpToList_trans n ss ts us h1.2 h2.2⟩
  | _, [], [], _ :: _, _, h2 => by simp [eqUpToList] at h2
  | _, [], _ :: _, _, h1, _ => by simp [eqUpToList] at h1
  | _, _ :: _, [], _, h1, _ => by simp [eqUpToList] at h1
  | _, _ :: _, _ :: _, [], _, h2 => by simp [eqUpToList] at h2
end

theorem eqUpToList_map_of_forall (n : Nat) (f g : Term → Term) :
    ∀ ts : List Term, (∀ t ∈ ts, eqUpTo n (f t) (g t) = true) →
      eqUpToList n (ts.map f) (ts.map g) = true
  | [], _ => by simp [eqUpToList]
  | t :: ts, h => by
    simp only [List.map_cons, eqUpToList, Bool.and_eq_true]
    exact ⟨h t List.mem_cons_self,
      eqUpToList_map_of_forall n f g ts (fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))⟩

theorem eqUpToList_iterSubst_mono {n k m : Nat} (σ : Subst) (hkm : k ≤ m) :
    ∀ ss ts : List Term, eqUpToList n (ss.map (iterSubst σ k)) (ts.map (iterSubst σ k)) = true →
      eqUpToList n (ss.map (iterSubst σ m)) (ts.map (iterSubst σ m)) = true
  | [], [], _ => by simp [eqUpToList]
  | s :: ss, t :: ts, h => by
    simp only [List.map_cons, eqUpToList, Bool.and_eq_true] at h ⊢
    exact ⟨eqUpTo_iterSubst_mono σ hkm h.1, eqUpToList_iterSubst_mono σ hkm ss ts h.2⟩
  | [], _ :: _, h => by simp [eqUpToList] at h
  | _ :: _, [], h => by simp [eqUpToList] at h

/-- Agreement in the limit: for every depth `n`, some number of unfoldings by `σ` makes `a` and
`b` agree up to depth `n`. -/
def LimEq (σ : Subst) (a b : Term) : Prop :=
  ∀ n, ∃ k, eqUpTo n (iterSubst σ k a) (iterSubst σ k b) = true

/-- List version of `LimEq` (pointwise, with one number of unfoldings per depth). -/
def LimEqList (σ : Subst) (as bs : List Term) : Prop :=
  ∀ n, ∃ k, eqUpToList n (as.map (iterSubst σ k)) (bs.map (iterSubst σ k)) = true

theorem LimEq.refl (σ : Subst) (a : Term) : LimEq σ a a := fun n => ⟨0, eqUpTo_refl n _⟩

theorem LimEq.symm {σ : Subst} {a b : Term} (h : LimEq σ a b) : LimEq σ b a := fun n => by
  obtain ⟨k, hk⟩ := h n
  exact ⟨k, eqUpTo_symm n _ _ hk⟩

theorem LimEq.trans {σ : Subst} {a b c : Term} (h1 : LimEq σ a b) (h2 : LimEq σ b c) :
    LimEq σ a c := fun n => by
  obtain ⟨k1, hk1⟩ := h1 n
  obtain ⟨k2, hk2⟩ := h2 n
  exact ⟨max k1 k2, eqUpTo_trans n _ _ _ (eqUpTo_iterSubst_mono σ (Nat.le_max_left _ _) hk1)
    (eqUpTo_iterSubst_mono σ (Nat.le_max_right _ _) hk2)⟩

theorem LimEqList.nil (σ : Subst) : LimEqList σ [] [] := fun _ => ⟨0, by simp [eqUpToList]⟩

theorem LimEqList.cons {σ : Subst} {a b : Term} {as bs : List Term} (h1 : LimEq σ a b)
    (h2 : LimEqList σ as bs) : LimEqList σ (a :: as) (b :: bs) := fun n => by
  obtain ⟨k1, hk1⟩ := h1 n
  obtain ⟨k2, hk2⟩ := h2 n
  refine ⟨max k1 k2, ?_⟩
  simp only [List.map_cons, eqUpToList, Bool.and_eq_true]
  exact ⟨eqUpTo_iterSubst_mono σ (Nat.le_max_left _ _) hk1,
    eqUpToList_iterSubst_mono σ (Nat.le_max_right _ _) as bs hk2⟩

theorem LimEq.con {σ : Subst} (f : Nat) {as bs : List Term} (h : LimEqList σ as bs) :
    LimEq σ (.con f as) (.con f bs) := fun n => by
  cases n with
  | zero => exact ⟨0, by simp [eqUpTo]⟩
  | succ n =>
    obtain ⟨k, hk⟩ := h n
    refine ⟨k, ?_⟩
    rw [iterSubst_con, iterSubst_con]
    simp only [eqUpTo, beq_self_eq_true, Bool.true_and]
    exact hk

mutual
/-- If `x` and `u` agree in the limit, substituting `u` for `x` preserves agreement in the
limit. -/
theorem limEq_subst_single {σ : Subst} {x : Nat} {u : Term} (hxu : LimEq σ (.var x) u) :
    ∀ a : Term, LimEq σ a (subst [(x, u)] a)
  | .var y => by
    show LimEq σ (.var y) (substVar [(x, u)] y)
    rw [substVar_single]
    by_cases hyx : y = x
    · subst hyx; simpa using hxu
    · simp only [hyx, ite_false]; exact LimEq.refl σ _
  | .con f as => by
    simp only [subst]
    exact LimEq.con f (limEqList_subst_single hxu as)
theorem limEqList_subst_single {σ : Subst} {x : Nat} {u : Term} (hxu : LimEq σ (.var x) u) :
    ∀ as : List Term, LimEqList σ as (substList [(x, u)] as)
  | [] => LimEqList.nil σ
  | a :: as => LimEqList.cons (limEq_subst_single hxu a) (limEqList_subst_single hxu as)
end

mutual
/-- If every binding produced by decomposition agrees in the limit, so does the equation. -/
theorem limEq_of_decomp {σ : Subst} : ∀ (s t : Term) (bs : List (Nat × Term)),
    decomp s t = some bs → (∀ p ∈ bs, LimEq σ (.var p.1) p.2) → LimEq σ s t
  | .var x, .var y, bs, h, hb => by
    by_cases hxy : x = y
    · subst hxy; exact LimEq.refl σ _
    · simp only [decomp, hxy, ite_false, Option.some.injEq] at h
      subst h
      exact hb (x, .var y) List.mem_cons_self
  | .var x, .con g ts, bs, h, hb => by
    simp only [decomp, Option.some.injEq] at h
    subst h
    exact hb (x, .con g ts) List.mem_cons_self
  | .con f ss, .var x, bs, h, hb => by
    simp only [decomp, Option.some.injEq] at h
    subst h
    exact (hb (x, .con f ss) List.mem_cons_self).symm
  | .con f ss, .con g ts, bs, h, hb => by
    by_cases hfg : f = g
    · subst hfg
      simp only [decomp, ite_true] at h
      exact LimEq.con f (limEqList_of_decompList ss ts bs h hb)
    · simp [decomp, hfg] at h
theorem limEqList_of_decompList {σ : Subst} : ∀ (ss ts : List Term) (bs : List (Nat × Term)),
    decompList ss ts = some bs → (∀ p ∈ bs, LimEq σ (.var p.1) p.2) → LimEqList σ ss ts
  | [], [], _, _, _ => LimEqList.nil σ
  | s :: ss, t :: ts, bs, h, hb => by
    cases h1 : decomp s t with
    | none => simp [decompList, h1] at h
    | some a =>
      cases h2 : decompList ss ts with
      | none => simp [decompList, h1, h2] at h
      | some b =>
        simp only [decompList, h1, h2, Option.some.injEq] at h
        subst h
        exact LimEqList.cons
          (limEq_of_decomp s t a h1 (fun p hp => hb p (List.mem_append_left _ hp)))
          (limEqList_of_decompList ss ts b h2 (fun p hp => hb p (List.mem_append_right _ hp)))
  | [], _ :: _, bs, h, _ => by simp [decompList] at h
  | _ :: _, [], bs, h, _ => by simp [decompList] at h
end

theorem limEq_of_decompAll {σ : Subst} : ∀ (eqs : List (Term × Term)) (bs : List (Nat × Term)),
    decompAll eqs = some bs → (∀ p ∈ bs, LimEq σ (.var p.1) p.2) →
      ∀ e ∈ eqs, LimEq σ e.1 e.2
  | [], _, _, _, e, he => by cases he
  | (s, t) :: es, bs, h, hb, e, he => by
    cases h1 : decomp s t with
    | none => simp [decompAll, h1] at h
    | some a =>
      cases h2 : decompAll es with
      | none => simp [decompAll, h1, h2] at h
      | some b =>
        simp only [decompAll, h1, h2, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.1 he with rfl | he
        · exact limEq_of_decomp s t a h1 (fun p hp => hb p (List.mem_append_left _ hp))
        · exact limEq_of_decompAll es b h2 (fun p hp => hb p (List.mem_append_right _ hp)) e he

/-- The combined system agrees in the limit under `σ`. -/
def LimSys (σ : Subst) (eqs : List (Term × Term)) (acc : Subst) : Prop :=
  (∀ e ∈ eqs, LimEq σ e.1 e.2) ∧ ∀ p ∈ acc, LimEq σ (.var p.1) p.2

/-- Backwards preservation: if a run without the occurs check returns `σf`, and `σf` solves its
own bindings in the limit, then every state of the run is solved in the limit by `σf`. -/
theorem run_false_ok_limSys {σf : Subst} : ∀ (fuel : Nat) (eqs : List (Term × Term)) (acc : Subst),
    run false fuel eqs acc = .ok σf → LimSys σf [] σf → LimSys σf eqs acc := by
  intro fuel
  induction fuel with
  | zero =>
    intro eqs acc h hf
    unfold run at h
    rcases step_cases false eqs acc with ⟨_, hs⟩ | ⟨hd, hs⟩ | ⟨_, _, _, _, hoc, _, _⟩ |
        ⟨_, _, _, _, _, hs⟩
    · rw [hs] at h; cases h
    · rw [hs] at h
      cases h
      exact ⟨limEq_of_decompAll eqs [] hd nofun, hf.2⟩
    · cases hoc
    · rw [hs] at h; cases h
  | succ n ih =>
    intro eqs acc h hf
    unfold run at h
    rcases step_cases false eqs acc with ⟨_, hs⟩ | ⟨hd, hs⟩ | ⟨_, _, _, _, hoc, _, _⟩ |
        ⟨x, u, bs, hd, _, hs⟩
    · rw [hs] at h; cases h
    · rw [hs] at h
      cases h
      exact ⟨limEq_of_decompAll eqs [] hd nofun, hf.2⟩
    · cases hoc
    · rw [hs] at h
      simp only at h
      obtain ⟨heqs', hacc'⟩ := ih _ _ h hf
      have hxu : LimEq σf (.var x) u := hacc' (x, u) List.mem_cons_self
      have hsx := limEq_subst_single hxu
      refine ⟨limEq_of_decompAll eqs _ hd (fun p hp => ?_), fun q hq => ?_⟩
      · rcases List.mem_cons.1 hp with rfl | hp
        · exact hxu
        · have := heqs' (elimBinding x u p) (List.mem_map_of_mem hp)
          exact (hsx (.var p.1)).trans (this.trans (hsx p.2).symm)
      · have := hacc' (q.1, subst [(x, u)] q.2)
          (List.mem_cons_of_mem _ (List.mem_map.2 ⟨q, hq, rfl⟩))
        exact this.trans (hsx q.2).symm

/-- The bound variables of a run's accumulated substitution only grow: the output's list of
bound variables ends with the initial one. -/
theorem run_ok_keys_suffix {oc : Bool} {σf : Subst} : ∀ (fuel : Nat) (eqs : List (Term × Term))
    (acc : Subst), run oc fuel eqs acc = .ok σf →
      ∃ ks, σf.map Prod.fst = ks ++ acc.map Prod.fst := by
  intro fuel
  induction fuel with
  | zero =>
    intro eqs acc h
    unfold run at h
    cases hs : step oc eqs acc with
    | done r =>
      rw [hs] at h
      simp only at h
      subst h
      exact ⟨[], (step_ok hs).1 ▸ rfl⟩
    | next eqs' acc' => rw [hs] at h; simp at h
  | succ n ih =>
    intro eqs acc h
    unfold run at h
    cases hs : step oc eqs acc with
    | done r =>
      rw [hs] at h
      simp only at h
      subst h
      exact ⟨[], (step_ok hs).1 ▸ rfl⟩
    | next eqs' acc' =>
      rw [hs] at h
      simp only at h
      obtain ⟨ks, hks⟩ := ih _ _ h
      rcases step_cases oc eqs acc with ⟨_, hs'⟩ | ⟨_, hs'⟩ | ⟨_, _, _, _, _, _, hs'⟩ |
          ⟨x, u, bs, _, _, hs'⟩
      · rw [hs'] at hs; cases hs
      · rw [hs'] at hs; cases hs
      · rw [hs'] at hs; cases hs
      · rw [hs'] at hs
        cases hs
        refine ⟨ks ++ [x], ?_⟩
        rw [hks]
        simp [elimSolved, List.map_map, Function.comp_def]

/-- Invariant of runs whose output has distinct bound variables: the bound variables of the
accumulated substitution are distinct, and a variable bound to a variable `z` occurs in no
right-hand side and in no pending equation, while `z` is not itself bound to a variable. -/
def ChainInv (eqs : List (Term × Term)) (acc : Subst) : Prop :=
  (acc.map Prod.fst).Nodup ∧ ∀ p ∈ acc, ∀ z, p.2 = .var z →
    (∀ q ∈ acc, p.1 ∉ q.2.vars) ∧ p.1 ∉ eqsVars eqs ∧ (∀ q ∈ acc, q.1 = z → ∀ w, q.2 ≠ .var w)

theorem step_false_next_chainInv {eqs eqs' : List (Term × Term)} {acc acc' : Subst}
    (h : step false eqs acc = .next eqs' acc') (hnd' : (acc'.map Prod.fst).Nodup)
    (hinv : ChainInv eqs acc) : ChainInv eqs' acc' := by
  obtain ⟨_, hB⟩ := hinv
  rcases step_cases false eqs acc with ⟨_, hs⟩ | ⟨_, hs⟩ | ⟨_, _, _, _, hoc, _, _⟩ |
      ⟨x, u, bs, hd, _, hs⟩
  · rw [hs] at h; cases h
  · rw [hs] at h; cases h
  · cases hoc
  rw [hs] at h
  cases h
  have hok := decompAll_bindingOK eqs _ hd
  have huV : ∀ z ∈ u.vars, z ∈ eqsVars eqs := (hok (x, u) List.mem_cons_self).2.1
  have hux : u ≠ .var x := (hok (x, u) List.mem_cons_self).2.2
  have hbs : ∀ b ∈ bs, BindingOK (eqsVars eqs) b := fun b hb => hok b (List.mem_cons_of_mem _ hb)
  have heqs' : ∀ z ∈ eqsVars (bs.map (elimBinding x u)),
      z ∈ eqsVars eqs ∧ (z = x → x ∈ u.vars) := by
    intro z hz
    rw [mem_eqsVars] at hz
    obtain ⟨e, he, hz⟩ := hz
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 he
    have hokb := hbs b hb
    have key : ∀ w : Term, (∀ y ∈ w.vars, y ∈ eqsVars eqs) → z ∈ (subst [(x, u)] w).vars →
        z ∈ eqsVars eqs ∧ (z = x → x ∈ u.vars) := by
      intro w hw hzw
      rcases mem_vars_subst_single hzw with ⟨hzw, hzx⟩ | hzu
      · exact ⟨hw z hzw, fun h => absurd h hzx⟩
      · exact ⟨huV z hzu, fun h => h ▸ hzu⟩
    rcases hz with hz | hz
    · exact key (.var b.1) (fun y hy => by
        simp only [Term.vars, List.mem_singleton] at hy
        exact hy ▸ hokb.1) hz
    · exact key b.2 hokb.2.1 hz
  have hvarkey : ∀ q ∈ acc, ∀ w, q.2 = .var w → q.1 ∉ eqsVars eqs :=
    fun q hq w hw => (hB q hq w hw).2.1
  refine ⟨hnd', ?_⟩
  intro p hp z hpz
  rcases mem_elimSolved hp with rfl | ⟨q0, hq0, rfl⟩
  · simp only at hpz
    have hzx : z ≠ x := fun h => hux (by rw [hpz, h])
    refine ⟨?_, ?_, ?_⟩
    · intro q hq hmem
      rcases mem_elimSolved hq with rfl | ⟨q1, _, rfl⟩
      · simp only [hpz, Term.vars, List.mem_singleton] at hmem
        exact hzx hmem.symm
      · rcases mem_vars_subst_single hmem with ⟨_, hne⟩ | hzu
        · exact hne rfl
        · simp only [hpz, Term.vars, List.mem_singleton] at hzu
          exact hzx hzu.symm
    · intro hmem
      have := (heqs' x hmem).2 rfl
      simp only [hpz, Term.vars, List.mem_singleton] at this
      exact hzx this.symm
    · intro q hq hqz w hqw
      rcases mem_elimSolved hq with rfl | ⟨q1, hq1, rfl⟩
      · exact hzx hqz.symm
      · simp only at hqz hqw
        cases hq12 : q1.2 with
        | var w1 =>
          have hz' : z ∈ eqsVars eqs := huV z (by simp [hpz, Term.vars])
          exact hvarkey q1 hq1 w1 hq12 (by rw [hqz]; exact hz')
        | con g ts => rw [hq12] at hqw; simp [subst] at hqw
  · simp only at hpz
    cases hq02 : q0.2 with
    | con g ts => rw [hq02] at hpz; simp [subst] at hpz
    | var w0 =>
      obtain ⟨hB1, hB2, hB3⟩ := hB q0 hq0 w0 hq02
      rw [hq02] at hpz
      change substVar [(x, u)] w0 = .var z at hpz
      rw [substVar_single] at hpz
      refine ⟨?_, ?_, ?_⟩
      · intro q hq hmem
        rcases mem_elimSolved hq with rfl | ⟨q1, hq1, rfl⟩
        · exact hB2 (huV _ hmem)
        · rcases mem_vars_subst_single hmem with ⟨hm, _⟩ | hzu
          · exact hB1 q1 hq1 hm
          · exact hB2 (huV _ hzu)
      · intro hmem
        exact hB2 (heqs' _ hmem).1
      · intro q hq hqz w hqw
        rcases mem_elimSolved hq with rfl | ⟨q1, hq1, rfl⟩
        · simp only at hqz hqw
          by_cases hw0 : w0 = x
          · simp only [hw0, ite_true] at hpz
            exact hux (by rw [hpz, hqz])
          · simp only [hw0, ite_false, Term.var.injEq] at hpz
            exact hw0 (hpz.trans hqz.symm)
        · simp only at hqz hqw
          cases hq12 : q1.2 with
          | con g ts => rw [hq12] at hqw; simp [subst] at hqw
          | var w1 =>
            by_cases hw0 : w0 = x
            · simp only [hw0, ite_true] at hpz
              have hz' : z ∈ eqsVars eqs := huV z (by simp [hpz, Term.vars])
              exact hvarkey q1 hq1 w1 hq12 (by rw [hqz]; exact hz')
            · simp only [hw0, ite_false, Term.var.injEq] at hpz
              exact hB3 q1 hq1 (hqz.trans hpz.symm) w1 hq12

theorem run_false_ok_chainInv {σf : Subst} (hnd : (σf.map Prod.fst).Nodup) :
    ∀ (fuel : Nat) (eqs : List (Term × Term)) (acc : Subst),
      run false fuel eqs acc = .ok σf → ChainInv eqs acc → ChainInv [] σf := by
  intro fuel
  induction fuel with
  | zero =>
    intro eqs acc h hinv
    unfold run at h
    cases hs : step false eqs acc with
    | done r =>
      rw [hs] at h
      simp only at h
      subst h
      obtain rfl := (step_ok hs).1
      exact ⟨hinv.1, fun p hp z hz =>
        ⟨(hinv.2 p hp z hz).1, by simp [eqsVars], (hinv.2 p hp z hz).2.2⟩⟩
    | next eqs' acc' => rw [hs] at h; simp at h
  | succ n ih =>
    intro eqs acc h hinv
    unfold run at h
    cases hs : step false eqs acc with
    | done r =>
      rw [hs] at h
      simp only at h
      subst h
      obtain rfl := (step_ok hs).1
      exact ⟨hinv.1, fun p hp z hz =>
        ⟨(hinv.2 p hp z hz).1, by simp [eqsVars], (hinv.2 p hp z hz).2.2⟩⟩
    | next eqs' acc' =>
      rw [hs] at h
      simp only at h
      obtain ⟨ks, hks⟩ := run_ok_keys_suffix _ _ _ h
      have hnd' : (acc'.map Prod.fst).Nodup := by
        rw [hks] at hnd
        exact (List.nodup_append.1 hnd).2.1
      exact ih _ _ h (step_false_next_chainInv hs hnd' hinv)

/-- In the output of such a run, a variable bound to a different variable `z` points to a `z`
that is not bound to a variable (other than itself). -/
theorem chainInv_short {σ : Subst} (h : ChainInv [] σ) :
    ∀ y z, substVar σ y = .var z → z ≠ y → ∀ w, substVar σ z = .var w → w = z := by
  intro y z hy hzy w hz
  rcases substVar_cases σ y with ⟨q, hq, hqy, hqv⟩ | hy'
  · rw [hy] at hqv
    rcases substVar_cases σ z with ⟨q', hq', hq'z, hq'v⟩ | hz'
    · rw [hz] at hq'v
      exact absurd hq'v.symm ((h.2 q hq z hqv.symm).2.2 q' hq' hq'z w)
    · rw [hz] at hz'
      exact Term.var.inj hz'
  · rw [hy] at hy'
    exact absurd (Term.var.inj hy') hzy

theorem iterSubst_var_fixed {σ : Subst} {y : Nat} (hy : substVar σ y = .var y) :
    ∀ k, iterSubst σ k (.var y) = .var y
  | 0 => rfl
  | k + 1 => by
    show iterSubst σ k (substVar σ y) = .var y
    rw [hy]
    exact iterSubst_var_fixed hy k

/-- Unfoldings converge when var-to-var chains have length at most one: `2n` and `2n + 1`
unfoldings agree up to depth `n`. -/
theorem eqUpTo_iterSubst_converge {σ : Subst}
    (hsh : ∀ y z, substVar σ y = .var z → z ≠ y → ∀ w, substVar σ z = .var w → w = z) :
    ∀ (n : Nat) (a : Term), eqUpTo n (iterSubst σ (2 * n) a) (iterSubst σ (2 * n + 1) a) = true := by
  intro n
  induction n with
  | zero => intro a; simp [eqUpTo]
  | succ n ih =>
    intro a
    have e1 : 2 * (n + 1) = 2 * n + 1 + 1 := by omega
    rw [e1]
    have hstep : ∀ u : Term,
        eqUpTo n (iterSubst σ (2 * n + 1) u) (iterSubst σ (2 * n + 1 + 1) u) = true := by
      intro u
      rw [iterSubst_succ' σ (2 * n) u, iterSubst_succ' σ (2 * n + 1) u]
      exact eqUpTo_subst σ (ih u)
    cases a with
    | con f as =>
      rw [iterSubst_con, iterSubst_con]
      simp only [eqUpTo, beq_self_eq_true, Bool.true_and]
      have := eqUpToList_map_of_forall n (iterSubst σ (2 * n + 1 + 1))
        (iterSubst σ (2 * n + 1 + 1 + 1)) as (fun u _ => by
          rw [iterSubst_succ' σ (2 * n + 1) u, iterSubst_succ' σ (2 * n + 1 + 1) u]
          exact eqUpTo_subst σ (hstep u))
      exact this
    | var y =>
      show eqUpTo (n + 1) (iterSubst σ (2 * n + 1) (substVar σ y))
        (iterSubst σ (2 * n + 1 + 1) (substVar σ y)) = true
      cases hy : substVar σ y with
      | con f us =>
        rw [iterSubst_con, iterSubst_con]
        simp only [eqUpTo, beq_self_eq_true, Bool.true_and]
        exact eqUpToList_map_of_forall n _ _ us (fun u _ => hstep u)
      | var z =>
        by_cases hzy : z = y
        · subst hzy
          rw [iterSubst_var_fixed hy, iterSubst_var_fixed hy]
          exact eqUpTo_refl _ _
        · show eqUpTo (n + 1) (iterSubst σ (2 * n) (substVar σ z))
            (iterSubst σ (2 * n + 1) (substVar σ z)) = true
          cases hz : substVar σ z with
          | var w =>
            have hwz := hsh y z hy hzy w hz
            subst hwz
            rw [iterSubst_var_fixed hz, iterSubst_var_fixed hz]
            exact eqUpTo_refl _ _
          | con f us =>
            rw [iterSubst_con, iterSubst_con]
            simp only [eqUpTo, beq_self_eq_true, Bool.true_and]
            exact eqUpToList_map_of_forall n _ _ us (fun u _ => ih u)

/-- Depth-indexed soundness of the occurs-check-free variant when no variable is eliminated
twice: if `unifyNoOC s t = some σ` and the left-hand variables of the returned association list
`σ` are pairwise distinct (since `step` prepends a binding at every elimination and never removes
one, this says the run eliminated no variable twice; it is a property of the list as returned,
not of the map it induces — see `dupσ_dedup_still_fails`), then for every depth `n` some number
`k` of unfoldings makes `σᵏ s` and `σᵏ t` agree up to depth `n`. -/
theorem unifyNoOC_eqUpTo_of_nodup {s t : Term} {σ : Subst} (h : unifyNoOC s t = some σ)
    (hnd : (σ.map Prod.fst).Nodup) :
    ∀ n, ∃ k, eqUpTo n (iterSubst σ k s) (iterSubst σ k t) = true := by
  have hrun : run false (numVars [(s, t)]) [(s, t)] [] = .ok σ := by
    unfold unifyNoOC at h
    cases hr : run false (numVars [(s, t)]) [(s, t)] [] <;> rw [hr] at h <;>
      simp [Result.toOption] at h
    rw [h]
  have hinv := run_false_ok_chainInv hnd _ _ _ hrun ⟨List.nodup_nil, nofun⟩
  have hconv := eqUpTo_iterSubst_converge (chainInv_short hinv)
  have hself : LimSys σ [] σ := by
    refine ⟨nofun, fun p hp n => ⟨2 * n, ?_⟩⟩
    have := hconv n (.var p.1)
    have e : iterSubst σ (2 * n + 1) (.var p.1) = iterSubst σ (2 * n) p.2 := by
      show iterSubst σ (2 * n) (substVar σ p.1) = _
      rw [substVar_of_mem_nodup hnd hp]
    rw [e] at this
    exact this
  exact (run_false_ok_limSys _ _ _ hrun hself).1 (s, t) List.mem_cons_self

/-- Non-vacuity for `unifyNoOC_eqUpTo_of_nodup` on a pair with no finite unifier: `X =? Box X`
gives `[X ↦ Box X]`, whose bound variables are distinct. -/
theorem unifyNoOC_eqUpTo_of_nodup_nonvacuous :
    unifyNoOC (.var 0) (box (.var 0)) = some [(0, box (.var 0))] ∧
      ([(0, box (.var 0))].map Prod.fst).Nodup ∧ ¬ Unifiable (.var 0) (box (.var 0)) :=
  ⟨by decide, by decide, not_unifiable_var_box⟩

/-- Left side of the duplicate-elimination example: `(X, (X, (Y, Z)))`. -/
def dupS : Term := pair (.var 0) (pair (.var 0) (pair (.var 1) (.var 2)))
/-- Right side of the duplicate-elimination example: `(Box X, (Box Y, (Vec Y, Z)))`. -/
def dupT : Term := pair (box (.var 0)) (pair (box (.var 1)) (pair (vec (.var 1)) (.var 2)))
/-- The output of `unifyNoOC dupS dupT`: `X` is bound twice. -/
def dupσ : Subst := [(1, vec (.var 1)), (0, vec (.var 1)), (0, box (vec (.var 1)))]

/-- Auxiliary computation for `unifyNoOC_eqUpTo_fails_with_duplicate_elimination`. -/
theorem dup_eqUpTo_two_false (k : Nat) :
    eqUpTo 2 (iterSubst dupσ k dupS) (iterSubst dupσ k dupT) = false := by
  cases k with
  | zero => decide
  | succ k =>
    show eqUpTo 2 (iterSubst dupσ k (subst dupσ dupS)) (iterSubst dupσ k (subst dupσ dupT)) = false
    have h1 : subst dupσ dupS = .con 4 [.con 3 [.var 1],
        .con 4 [.con 3 [.var 1], .con 4 [.con 3 [.var 1], .var 2]]] := by decide
    have h2 : subst dupσ dupT = .con 4 [.con 2 [.con 3 [.var 1]],
        .con 4 [.con 2 [.con 3 [.var 1]], .con 4 [.con 3 [.con 3 [.var 1]], .var 2]]] := by decide
    rw [h1, h2]
    simp [iterSubst_con, eqUpTo, eqUpToList]

/-- Without `hnd`, `unifyNoOC_eqUpTo_of_nodup` fails (instance: a pair with three variables and
the constructors `Box`, `Vec`, `Pair`): on `dupS =? dupT` (whose equations `X = Box X`,
`X = Box Y`, `Y = Vec Y` have no solution even in infinite trees — not proved here), the
occurs-check-free variant returns `dupσ`, which binds `X` twice; at depth 2 no number of
unfoldings makes the two sides agree (`Vec …` against `Box …` under the first component).
The first binding of `X` was rewritten from `Box X` to `Box Y` when `X ↦ Y` was eliminated, and
the solved form never re-checks it. The variable `Z` only raises the fuel `numVars` from 2 to 3;
without it the run runs out of fuel (`run_needs_occurs_check_for_bound`). -/
theorem unifyNoOC_eqUpTo_fails_with_duplicate_elimination :
    unifyNoOC dupS dupT = some dupσ ∧ dupσ.map Prod.fst = [1, 0, 0] ∧
      ¬ (dupσ.map Prod.fst).Nodup ∧
      (∀ k, eqUpTo 2 (iterSubst dupσ k dupS) (iterSubst dupσ k dupT) = false) ∧
      ¬ (∀ n, ∃ k, eqUpTo n (iterSubst dupσ k dupS) (iterSubst dupσ k dupT) = true) := by
  have hall : ∀ k, eqUpTo 2 (iterSubst dupσ k dupS) (iterSubst dupσ k dupT) = false := by
    intro k
    exact dup_eqUpTo_two_false k
  refine ⟨by decide, by decide, by decide, hall, fun h => ?_⟩
  obtain ⟨k, hk⟩ := h 2
  rw [hall k] at hk
  cases hk

/-- `dupσ` with its shadowed second binding of `X` removed. -/
def dupσDedup : Subst := [(1, vec (.var 1)), (0, vec (.var 1))]

/-- The duplicate-freeness hypothesis of `unifyNoOC_eqUpTo_of_nodup` is about the association
list as returned, not about the substitution it denotes: removing the shadowed binding from
`dupσ` gives a list with distinct left-hand variables that acts identically on every term, and
the two sides of `dupS =? dupT` still disagree at depth 2 after any number of unfoldings. So a
representation that keeps one binding per variable (a finite map, or post-hoc deduplication)
does not by itself make the occurs-check-free output a depth-indexed solution. -/
theorem dupσ_dedup_still_fails :
    (dupσDedup.map Prod.fst).Nodup ∧ (∀ t, subst dupσDedup t = subst dupσ t) ∧
      ∀ k, eqUpTo 2 (iterSubst dupσDedup k dupS) (iterSubst dupσDedup k dupT) = false := by
  have hsub : ∀ t, subst dupσDedup t = subst dupσ t := fun t =>
    subst_congr_vars t (fun x _ => by
      by_cases h1 : x = 1
      · subst h1; decide
      · by_cases h0 : x = 0
        · subst h0; decide
        · simp [dupσDedup, dupσ, substVar_cons, h0, h1, substVar_nil])
  have hiter : ∀ k t, iterSubst dupσDedup k t = iterSubst dupσ k t := by
    intro k
    induction k with
    | zero => intro t; rfl
    | succ k ih => intro t; simp only [iterSubst, hsub, ih]
  refine ⟨by decide, hsub, fun k => ?_⟩
  rw [hiter, hiter]
  exact dup_eqUpTo_two_false k

end Toy.Unify
