import ToyUnify.OccursCheck

/-!
# One-sided matching versus unification

`Matchable p t` (some `σ` with `σ p = t`, the target `t` left untouched) differs from
`Unifiable p t` in both directions; the matching algorithm `matchAlg` performs no occurs check
and is sound and complete; on a ground target the two notions coincide.
-/

namespace Toy.Unify

/-- One-sided matching: some substitution instantiates the pattern `p` to exactly the target
`t` (variables of `t` are treated as fixed). Captures selecting an impl by instantiating its
header to a given type. -/
def Matchable (p t : Term) : Prop := ∃ σ : Subst, subst σ p = t

mutual
/-- Match pattern `p` against target `t`, extending the accumulated bindings `σ`. A pattern
variable already bound must be bound to exactly `t`; there is no occurs check, and `σ` is never
applied to the target. -/
def matchAux : Term → Term → Subst → Option Subst
  | .var x, t, σ =>
    match σ.lookup x with
    | some u => if u = t then some σ else none
    | none => some ((x, t) :: σ)
  | .con f ps, .con g ts, σ => if f = g then matchList ps ts σ else none
  | .con _ _, .var _, _ => none
/-- Match argument lists pointwise (companion of `matchAux`). -/
def matchList : List Term → List Term → Subst → Option Subst
  | [], [], σ => some σ
  | p :: ps, t :: ts, σ =>
    match matchAux p t σ with
    | some σ' => matchList ps ts σ'
    | none => none
  | _, _, _ => none
end

/-- The matching algorithm, from no bindings. -/
def matchAlg (p t : Term) : Option Subst := matchAux p t []

/-! ## Definition examples -/

theorem matchable_example : Matchable (pair (.var 0) (.var 0)) (pair u8 u8) :=
  ⟨[(0, u8)], by decide⟩

theorem not_matchable_example : ¬ Matchable (pair (.var 0) (.var 0)) (pair u8 u32) := by
  rintro ⟨σ, h⟩
  simp [pair, subst_con, u8, u32] at h
  rw [h.1] at h
  simp at h

theorem matchAlg_example : matchAlg (pair (.var 0) (.var 0)) (pair u8 u8) = some [(0, u8)] := by
  decide

theorem matchAlg_none_example : matchAlg (pair (.var 0) (.var 0)) (pair u8 u32) = none := by
  decide

/-! ## Matching and unification disagree in both directions -/

/-- Unifiable but not matchable: `(X, u8)` and `(u32, Y)` unify, but no instance of `(X, u8)` is
the term `(u32, Y)` itself. -/
theorem unifiable_not_matchable :
    Unifiable (pair (.var 0) u8) (pair u32 (.var 1)) ∧
      ¬ Matchable (pair (.var 0) u8) (pair u32 (.var 1)) := by
  refine ⟨unifiable_example, ?_⟩
  rintro ⟨σ, h⟩
  simp [pair, subst_con, u8, u32] at h

/-- Matchable but not unifiable: `X` matches `Box X` (with `X ↦ Box X`, the target untouched),
but `X =? Box X` has no finite unifier. -/
theorem matchable_not_unifiable :
    Matchable (.var 0) (box (.var 0)) ∧ ¬ Unifiable (.var 0) (box (.var 0)) :=
  ⟨⟨[(0, box (.var 0))], by decide⟩, not_unifiable_var_box⟩

/-! ## Matching needs no occurs check -/

theorem lookup_cons_eq (x y : Nat) (u : Term) (σ : Subst) :
    ((x, u) :: σ).lookup y = if y = x then some u else σ.lookup y := by
  by_cases h : y = x
  · subst h; simp [List.lookup]
  · have : (y == x) = false := by simpa using h
    simp [List.lookup, this, h]

/-- `σ'` extends `σ`: every binding found in `σ` is found, unchanged, in `σ'`. -/
def LookupExt (σ σ' : Subst) : Prop := ∀ y w, σ.lookup y = some w → σ'.lookup y = some w

theorem substVar_of_lookup {σ : Subst} {y : Nat} {w : Term} (h : σ.lookup y = some w) :
    substVar σ y = w := by simp [substVar, h]

/-- An extension does not change the image of a term all of whose variables are bound. -/
theorem subst_of_lookupExt {σ σ' : Subst} (hext : LookupExt σ σ') {p : Term}
    (hb : ∀ y ∈ p.vars, (σ.lookup y).isSome) : subst σ' p = subst σ p :=
  subst_congr_vars p (fun y hy => by
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (hb y hy)
    rw [substVar_of_lookup (hext y w hw), substVar_of_lookup hw])

mutual
theorem matchAux_spec : ∀ (p t : Term) (σ σ' : Subst), matchAux p t σ = some σ' →
    LookupExt σ σ' ∧ (∀ y ∈ p.vars, (σ'.lookup y).isSome) ∧ subst σ' p = t
  | .var x, t, σ, σ', h => by
    simp only [matchAux] at h
    cases hl : σ.lookup x with
    | some u =>
      rw [hl] at h
      by_cases hut : u = t
      · simp only [hut, ite_true, Option.some.injEq] at h
        subst h hut
        exact ⟨fun _ _ h => h, fun y hy => by simp_all [Term.vars], substVar_of_lookup hl⟩
      · simp [hut] at h
    | none =>
      rw [hl] at h
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨fun y w hw => ?_, fun y hy => ?_, ?_⟩
      · rw [lookup_cons_eq]
        by_cases hyx : y = x
        · subst hyx; rw [hl] at hw; cases hw
        · simp [hyx, hw]
      · simp only [Term.vars, List.mem_singleton] at hy
        subst hy
        simp
      · exact substVar_of_lookup (by simp)
  | .con f ps, .con g ts, σ, σ', h => by
    by_cases hfg : f = g
    · subst hfg
      simp only [matchAux, ite_true] at h
      obtain ⟨hext, hb, heq⟩ := matchList_spec ps ts σ σ' h
      exact ⟨hext, fun y hy => hb y (by simpa [Term.vars] using hy), by
        simp only [subst, heq]⟩
    · simp [matchAux, hfg] at h
  | .con _ _, .var _, _, _, h => by simp [matchAux] at h
theorem matchList_spec : ∀ (ps ts : List Term) (σ σ' : Subst), matchList ps ts σ = some σ' →
    LookupExt σ σ' ∧ (∀ y ∈ Term.varsList ps, (σ'.lookup y).isSome) ∧ substList σ' ps = ts
  | [], [], σ, σ', h => by
    simp only [matchList, Option.some.injEq] at h
    subst h
    exact ⟨fun _ _ h => h, fun y hy => by simp [Term.varsList] at hy, rfl⟩
  | p :: ps, t :: ts, σ, σ', h => by
    simp only [matchList] at h
    cases h1 : matchAux p t σ with
    | none => rw [h1] at h; cases h
    | some σ1 =>
      rw [h1] at h
      simp only at h
      obtain ⟨hext1, hb1, heq1⟩ := matchAux_spec p t σ σ1 h1
      obtain ⟨hext2, hb2, heq2⟩ := matchList_spec ps ts σ1 σ' h
      refine ⟨fun y w hw => hext2 y w (hext1 y w hw), fun y hy => ?_, ?_⟩
      · simp only [Term.varsList, List.mem_append] at hy
        rcases hy with hy | hy
        · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (hb1 y hy)
          simp [hext2 y w hw]
        · exact hb2 y hy
      · simp only [substList, heq2, subst_of_lookupExt hext2 hb1, heq1]
  | [], _ :: _, _, _, h => by simp [matchList] at h
  | _ :: _, [], _, _, h => by simp [matchList] at h
end

/-- `σ` is compatible with `ρ`: every binding of `σ` agrees with `ρ`. -/
def LookupCompat (σ ρ : Subst) : Prop := ∀ y w, σ.lookup y = some w → substVar ρ y = w

mutual
theorem matchAux_complete : ∀ (p : Term) (ρ σ : Subst), LookupCompat σ ρ →
    ∃ σ', matchAux p (subst ρ p) σ = some σ' ∧ LookupCompat σ' ρ
  | .var x, ρ, σ, hc => by
    simp only [matchAux, subst]
    cases hl : σ.lookup x with
    | some u =>
      have hu := hc x u hl
      subst hu
      exact ⟨σ, by simp, hc⟩
    | none =>
      refine ⟨(x, substVar ρ x) :: σ, rfl, fun y w hw => ?_⟩
      rw [lookup_cons_eq] at hw
      by_cases hyx : y = x
      · subst hyx
        simp only [ite_true, Option.some.injEq] at hw
        exact hw
      · simp only [hyx, ite_false] at hw
        exact hc y w hw
  | .con f ps, ρ, σ, hc => by
    simp only [subst, matchAux, ite_true]
    exact matchList_complete ps ρ σ hc
theorem matchList_complete : ∀ (ps : List Term) (ρ σ : Subst), LookupCompat σ ρ →
    ∃ σ', matchList ps (substList ρ ps) σ = some σ' ∧ LookupCompat σ' ρ
  | [], _, σ, hc => ⟨σ, by simp [matchList, substList], hc⟩
  | p :: ps, ρ, σ, hc => by
    obtain ⟨σ1, h1, hc1⟩ := matchAux_complete p ρ σ hc
    obtain ⟨σ2, h2, hc2⟩ := matchList_complete ps ρ σ1 hc1
    exact ⟨σ2, by simp [substList, matchList, h1, h2], hc2⟩
end

/-- Soundness of `matchAlg` (which performs no occurs check). -/
theorem matchAlg_sound {p t : Term} {σ : Subst} (h : matchAlg p t = some σ) :
    subst σ p = t :=
  (matchAux_spec p t [] σ h).2.2

/-- Completeness of `matchAlg`: if `p` matches `t`, then `matchAlg` returns a substitution. -/
theorem matchAlg_complete {p t : Term} (h : Matchable p t) : ∃ σ, matchAlg p t = some σ := by
  obtain ⟨ρ, rfl⟩ := h
  obtain ⟨σ, hσ, _⟩ := matchAux_complete p ρ [] (fun _ _ h => by simp [List.lookup] at h)
  exact ⟨σ, hσ⟩

/-- Non-vacuity for both `matchAlg_sound` and `matchAlg_complete`: `matchAlg` succeeds on `X`
against `Box X` — the instance on which unification needs the occurs check — and `X` matches
`Box X`. -/
theorem matchAlg_nonvacuous :
    matchAlg (.var 0) (box (.var 0)) = some [(0, box (.var 0))] ∧
      Matchable (.var 0) (box (.var 0)) :=
  ⟨by decide, ⟨[(0, box (.var 0))], by decide⟩⟩

/-- The output of `matchAlg` need not be idempotent, and need not fix the target, when pattern
and target share variable names: on `X` against `Box X` it returns `[X ↦ Box X]`. -/
theorem matchAlg_output_not_idempotent_example :
    matchAlg (.var 0) (box (.var 0)) = some [(0, box (.var 0))] ∧
      ¬ Idempotent [(0, box (.var 0))] ∧
      subst [(0, box (.var 0))] (box (.var 0)) ≠ box (.var 0) :=
  ⟨by decide, not_idempotent_example, by decide⟩

/-- Without `h`, `matchAlg_sound`'s conclusion fails for an arbitrary substitution. -/
theorem matchAlg_sound_needs_output :
    matchAlg (.var 0) u8 ≠ some [] ∧ subst [] (.var 0) ≠ u8 := by decide

/-- Without `h`, `matchAlg_complete`'s conclusion fails (instance with two nullary constructors):
`u8` does not match `u32`, and `matchAlg u8 u32` returns no substitution. -/
theorem matchAlg_complete_needs_matchable :
    ¬ Matchable u8 u32 ∧ ¬ ∃ σ, matchAlg u8 u32 = some σ := by
  refine ⟨?_, ?_⟩
  · rintro ⟨σ, h⟩
    simp [u8, u32, subst_con] at h
  · rintro ⟨σ, h⟩
    have hn : matchAlg u8 u32 = none := by decide
    rw [hn] at h
    cases h

/-! ## On ground targets, matching is unification -/

/-- If the target `t` is ground, `p` matches `t` exactly when `p` and `t` unify. -/
theorem matchable_iff_unifiable_of_isGround {p t : Term} (ht : IsGround t) :
    Matchable p t ↔ Unifiable p t := by
  simp only [Matchable, Unifiable, Unifies, subst_of_isGround ht]

/-- On a ground target the two algorithms agree on success: `matchAlg p t` returns a substitution
exactly when `unify p t` does. -/
theorem matchAlg_isSome_iff_unify_isSome_of_isGround {p t : Term} (ht : IsGround t) :
    (matchAlg p t).isSome = true ↔ (unify p t).isSome = true := by
  constructor
  · intro h
    obtain ⟨σ, hσ⟩ := Option.isSome_iff_exists.1 h
    obtain ⟨τ, hτ⟩ := (matchable_iff_unifiable_of_isGround ht).1 ⟨σ, matchAlg_sound hσ⟩
    obtain ⟨σ', hσ'⟩ := unify_complete hτ
    simp [hσ']
  · intro h
    obtain ⟨σ, hσ⟩ := Option.isSome_iff_exists.1 h
    obtain ⟨σ', hσ'⟩ :=
      matchAlg_complete ((matchable_iff_unifiable_of_isGround ht).2 ⟨σ, unify_sound hσ⟩)
    simp [hσ']

/-- Without `ht`, the agreement of the two algorithms fails (instance: one variable against
`Box` of itself): `matchAlg` succeeds on `X` against `Box X`, `unify` does not. -/
theorem matchAlg_isSome_iff_unify_needs_ground :
    ¬ IsGround (box (.var 0)) ∧ (matchAlg (.var 0) (box (.var 0))).isSome = true ∧
      (unify (.var 0) (box (.var 0))).isSome = false ∧
      ¬ ((matchAlg (.var 0) (box (.var 0))).isSome = true ↔
        (unify (.var 0) (box (.var 0))).isSome = true) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro h
  have := h.1 (by decide)
  revert this
  decide

/-- Renamed apart, matching implies unification: if the pattern and the target share no variable,
a matching substitution restricted to the pattern's variables unifies them. -/
theorem unifiable_of_matchable_of_varsDisjoint {p t : Term} (hdisj : VarsDisjoint p t)
    (h : Matchable p t) : Unifiable p t := by
  obtain ⟨σ, hσ⟩ := h
  let σ' : Subst := p.vars.map (fun x => (x, substVar σ x))
  have hleft : ∀ x ∈ p.vars, substVar σ' x = substVar σ x := by
    intro x hx
    have key : ∀ vs : List Nat, x ∈ vs →
        substVar (vs.map (fun y => (y, substVar σ y))) x = substVar σ x := by
      intro vs
      induction vs with
      | nil => intro h; cases h
      | cons y ys ih =>
        intro hmem
        simp only [List.map_cons, substVar_cons]
        by_cases hxy : x = y
        · subst hxy; simp
        · simp only [hxy, ite_false]
          exact ih (by simpa [hxy] using hmem)
    exact key p.vars hx
  have hright : ∀ y ∈ t.vars, substVar σ' y = .var y := by
    intro y hy
    apply substVar_of_not_key
    intro q hq hqy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hq
    have hxy : x = y := hqy
    subst hxy
    exact hdisj x hx hy
  refine ⟨σ', ?_⟩
  unfold Unifies
  rw [subst_congr_vars p hleft, hσ, subst_eq_self_of_vars t hright]

/-- Non-vacuity for `unifiable_of_matchable_of_varsDisjoint`: `X` matches `Box Y`, with no shared
variable. -/
theorem unifiable_of_matchable_of_varsDisjoint_nonvacuous :
    VarsDisjoint (.var 0) (box (.var 1)) ∧ Matchable (.var 0) (box (.var 1)) :=
  ⟨by decide, ⟨[(0, box (.var 1))], by decide⟩⟩

/-- Without `hdisj` (instance with one variable and one unary constructor): `X` matches `Box X`
but does not unify with it. -/
theorem unifiable_of_matchable_needs_varsDisjoint :
    ¬ VarsDisjoint (.var 0) (box (.var 0)) ∧ Matchable (.var 0) (box (.var 0)) ∧
      ¬ Unifiable (.var 0) (box (.var 0)) :=
  ⟨by decide, matchable_not_unifiable.1, matchable_not_unifiable.2⟩

/-- Non-vacuity: `Vec u8` is ground. -/
theorem matchable_iff_unifiable_of_isGround_nonvacuous : IsGround (vec u8) := by decide

/-- Without `ht`, the equivalence fails (`X` against the non-ground `Box X`). -/
theorem matchable_iff_unifiable_needs_ground :
    ¬ IsGround (box (.var 0)) ∧
      ¬ (Matchable (.var 0) (box (.var 0)) ↔ Unifiable (.var 0) (box (.var 0))) := by
  refine ⟨by decide, fun hiff => ?_⟩
  exact matchable_not_unifiable.2 (hiff.1 matchable_not_unifiable.1)

/-- Groundness of the target is sufficient, not necessary, for the equivalence: for the non-ground
target `Box Y`, `X` matches `Box Y` and `X` and `Box Y` are unifiable, so the equivalence holds. -/
theorem matchable_iff_unifiable_nonGround_example :
    ¬ IsGround (box (.var 1)) ∧ Matchable (.var 0) (box (.var 1)) ∧
      Unifiable (.var 0) (box (.var 1)) ∧
      (Matchable (.var 0) (box (.var 1)) ↔ Unifiable (.var 0) (box (.var 1))) :=
  ⟨by decide, ⟨[(0, box (.var 1))], by decide⟩, ⟨[(0, box (.var 1))], by decide⟩,
    ⟨fun _ => ⟨[(0, box (.var 1))], by decide⟩, fun _ => ⟨[(0, box (.var 1))], by decide⟩⟩⟩

end Toy.Unify
