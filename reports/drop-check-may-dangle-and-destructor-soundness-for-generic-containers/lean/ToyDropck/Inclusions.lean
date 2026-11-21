import ToyDropck.Checker

/-!
# Inclusions among the checker policies

Lemmas relating the per-type judgments `dropckP pol` of different policies, lifted to the
checker over a list of locals.
-/

namespace Toy.Dropck

/-- If every lifetime of `t` satisfies `ok`, every policy accepts the drop of `t`. In particular
the ownership-recursion conjunct of the strict branch of `dropckP` never rejects once that
branch's outlives conjunct holds. -/
theorem dropckP_of_lifetimes_ok (pol : DanglePolicy) (impls : ImplTable) (ok : Nat → Bool) :
    ∀ t : Ty, (lifetimes t).all ok = true → dropckP pol impls ok t = true
  | .int, _ => rfl
  | .ref _, _ => rfl
  | .app c t, h => by
    have ht : (lifetimes t).all ok = true := by simpa [lifetimes] using h
    have ih := dropckP_of_lifetimes_ok pol impls ok t ht
    simp only [dropckP]
    split
    · cases pol <;> simp [ht, ih]
    · simp [ht, ih]

/-- Monotonicity of `dropckP` in the policy: if the `#[may_dangle]` branch of policy `p` implies
that of policy `q` (given the implication on the element type), then `dropckP p` implies
`dropckP q` on every type. -/
theorem dropckP_mono {p q : DanglePolicy} {impls : ImplTable} {ok : Nat → Bool}
    (hbranch : ∀ (c : Nat) (t : Ty), (impls c).beh.hasDrop = true →
      (impls c).decl.mayDangle = true →
      (dropckP p impls ok t = true → dropckP q impls ok t = true) →
      dropckP p impls ok (.app c t) = true → dropckP q impls ok (.app c t) = true) :
    ∀ t : Ty, dropckP p impls ok t = true → dropckP q impls ok t = true
  | .int, _ => rfl
  | .ref _, _ => rfl
  | .app c t, h => by
    have ih := dropckP_mono hbranch t
    by_cases hc : (impls c).beh.hasDrop = true ∧ (impls c).decl.mayDangle = true
    · exact hbranch c t hc.1 hc.2 ih h
    · have hc' : ((impls c).beh.hasDrop && (impls c).decl.mayDangle) = false := by
        cases h1 : (impls c).beh.hasDrop <;> cases h2 : (impls c).decl.mayDangle <;> simp_all
      simp only [dropckP, hc', Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
        Bool.or_eq_true] at h ⊢
      exact ⟨h.1, h.2.imp_right ih⟩

/-- Lifting a per-type implication between judgments to the checker over a list of locals. -/
theorem acceptsFrom_mono {p q : DanglePolicy} {impls impls' : ImplTable} {ord : List Nat}
    (h : ∀ (i : Nat) (t : Ty), dropckP p impls (outlives ord i) t = true →
      dropckP q impls' (outlives ord i) t = true) :
    ∀ (l : List (Ty × Val)) (i : Nat), acceptsFrom p impls ord i l = true →
      acceptsFrom q impls' ord i l = true
  | [], _, _ => rfl
  | (t, _) :: rest, i, hl => by
    simp only [acceptsFrom, Bool.and_eq_true, Bool.or_eq_true] at hl ⊢
    exact ⟨hl.1.imp_right (h i t), acceptsFrom_mono h rest (i + 1) hl.2⟩

/-- The strict judgment (all `#[may_dangle]` erased) implies the judgment of every policy. -/
theorem dropckP_of_strip (pol : DanglePolicy) {impls : ImplTable} {ok : Nat → Bool} :
    ∀ t : Ty, dropckP .ownsRecurse (stripDangle impls) ok t = true → dropckP pol impls ok t = true
  | .int, _ => rfl
  | .ref _, _ => rfl
  | .app c t, h => by
    have ih := dropckP_of_strip pol (impls := impls) (ok := ok) t
    simp only [dropckP, stripDangle, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
      Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
    simp only [dropckP]
    split
    · rename_i hc
      have hD : (impls c).beh.hasDrop = true := by
        cases h1 : (impls c).beh.hasDrop <;> simp_all
      have hall : (lifetimes t).all ok = true := by
        rcases h.1 with h1 | h1
        · rw [hD] at h1; cases h1
        · exact h1
      have hrec := dropckP_of_lifetimes_ok pol impls ok t hall
      cases pol <;> simp [hall, hrec]
    · simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
      exact ⟨h.1, h.2.imp_right ih⟩

/-- A type in which no type constructor has a `Drop` impl passes the `ownsRecurse` judgment for
every `ok`. -/
theorem dropckP_ownsRecurse_of_deepHasNoDrop {impls : ImplTable} {ok : Nat → Bool} :
    ∀ t : Ty, deepHasNoDrop impls t = true → dropckP .ownsRecurse impls ok t = true
  | .int, _ => rfl
  | .ref _, _ => rfl
  | .app c t, h => by
    simp only [deepHasNoDrop, Bool.and_eq_true, Bool.not_eq_true'] at h
    have ih := dropckP_ownsRecurse_of_deepHasNoDrop (impls := impls) (ok := ok) t h.2
    simp [dropckP, h.1, ih]

/-- The deep "no `Drop` impl" test implies the shallow one. -/
theorem headHasNoDrop_of_deepHasNoDrop {impls : ImplTable} :
    ∀ t : Ty, deepHasNoDrop impls t = true → headHasNoDrop impls t = true
  | .int, _ => rfl
  | .ref _, _ => rfl
  | .app c t, h => by
    simp only [deepHasNoDrop, Bool.and_eq_true] at h
    simpa [headHasNoDrop] using h.1

/-- The `deepNoDrop` judgment implies the `ownsRecurse` judgment. -/
theorem dropckP_ownsRecurse_of_deepNoDrop {impls : ImplTable} {ok : Nat → Bool} :
    ∀ t : Ty, dropckP .deepNoDrop impls ok t = true → dropckP .ownsRecurse impls ok t = true :=
  dropckP_mono fun c t hD hM _ h => by
    simp only [dropckP, hD, hM, Bool.and_self, ↓reduceIte, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact Or.inr (dropckP_ownsRecurse_of_deepHasNoDrop t h)
    · exact Or.inr (dropckP_of_lifetimes_ok _ impls ok t h)

/-- The `deepNoDrop` judgment implies the `headNoDrop` judgment. -/
theorem dropckP_headNoDrop_of_deepNoDrop {impls : ImplTable} {ok : Nat → Bool} :
    ∀ t : Ty, dropckP .deepNoDrop impls ok t = true → dropckP .headNoDrop impls ok t = true :=
  dropckP_mono fun c t hD hM _ h => by
    simp only [dropckP, hD, hM, Bool.and_self, ↓reduceIte, Bool.or_eq_true] at h ⊢
    exact h.imp_left (headHasNoDrop_of_deepHasNoDrop t)

/-- Every policy's judgment implies the `noUseSuffices` judgment. -/
theorem dropckP_noUseSuffices_of_dropckP (pol : DanglePolicy) {impls : ImplTable}
    {ok : Nat → Bool} :
    ∀ t : Ty, dropckP pol impls ok t = true → dropckP .noUseSuffices impls ok t = true :=
  dropckP_mono fun c t hD hM _ _ => by
    simp [dropckP, hD, hM]

end Toy.Dropck
