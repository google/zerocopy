import Toy.Render.Counterexamples

/-!
# Remarks on sufficiency and reader-relativity (`Toy.Render`)

Three facts cited in the non-claims of the coherence and greedy-printer results:
the hypotheses `s.subAnnotated = true` and `s.subFree = true` of the coherence
results are sufficient but not necessary for coherence, and a deletion-greedy
rendering computed against the system configuration can remain faithful for other
configurations.
-/

namespace Toy.Render

/-- The unannotated text `z - z = z` (with `z : Int`). It contains a subtraction
without a type argument. -/
def sZZSub : Stx := .eq none (.sub none (.var 2) (.var 2)) (.var 2)

/-- **Coherence without annotated subtraction (operands fix `Int`).** `sZZSub` is
neither subtraction-annotated, nor subtraction-free, nor fully annotated; it has a
declarative elaboration, and all
of its declarative elaborations at any type evaluate identically in every
environment. -/
theorem subAnnotated_not_necessary_for_coherence_int :
    sZZSub.subAnnotated = false ∧ sZZSub.subFree = false ∧ sZZSub.fullyAnnotated = false ∧
    Elabs S₀ sZZSub .prop (.eq .int (.sub .int vZ vZ) vZ) ∧
    ∀ τ t₁ t₂, Elabs S₀ sZZSub τ t₁ → Elabs S₀ sZZSub τ t₂ → ∀ ρ, eval S₀ ρ t₁ = eval S₀ ρ t₂ := by
  refine ⟨by decide, by decide, by decide,
    .eq (τ := .int) rfl (.inl rfl) (.sub rfl (.inl rfl) (.var rfl) (.var rfl)) (.var rfl), ?_⟩
  intro τ t₁ t₂ h₁ h₂
  have uniq : ∀ {τ t}, Elabs S₀ sZZSub τ t → τ = .prop ∧ t = .eq .int (.sub .int vZ vZ) vZ := by
    intro τ t h
    cases h with
    | coeIns hnat => cases hnat
    | @eq _ σ _ _ _ _ hnum _ hsub hz =>
      cases σ with
      | prop => simp [Ty.isNum] at hnum
      | nat => exact absurd hz (not_elabs_int_var_at_nat _)
      | int =>
        cases hz with
        | coeIns hzn => exact absurd hzn (not_elabs_int_var_at_nat _)
        | var hv =>
          cases hsub with
          | coeIns hsubn =>
            cases hsubn with
            | sub _ _ ha _ => exact absurd ha (not_elabs_int_var_at_nat _)
          | sub _ _ ha hb =>
            cases ha with
            | coeIns han => exact absurd han (not_elabs_int_var_at_nat _)
            | var hva =>
              cases hb with
              | coeIns hbn => exact absurd hbn (not_elabs_int_var_at_nat _)
              | var hvb => exact ⟨rfl, rfl⟩
  obtain ⟨_, rfl⟩ := uniq h₁
  obtain ⟨_, rfl⟩ := uniq h₂
  intro ρ; rfl

/-- The unannotated text `a - a = z` (with `a : Nat`, `z : Int`). -/
def sAASub : Stx := .eq none (.sub none (.var 0) (.var 0)) (.var 2)

private theorem elabs_var0_eval (S : Sig) (hv0 : S.varTy 0 = some .nat) :
    (∀ t, Elabs S (.var 0) .nat t → ∀ ρ, eval S ρ t = .nat (ρ.nat 0)) ∧
    (∀ t, Elabs S (.var 0) .int t → ∀ ρ, eval S ρ t = .int (Int.ofNat (ρ.nat 0))) := by
  refine ⟨?_, ?_⟩
  · intro t h ρ
    cases h with
    | var hv =>
      rw [hv0] at hv; cases hv
      rw [eval, evalD_eq_evalWith_const]; rfl
  · intro t h ρ
    cases h with
    | var hv => rw [hv0] at hv; cases hv
    | coeIns hn =>
      cases hn with
      | var hv =>
        rw [hv0] at hv; cases hv
        rw [eval, evalD_eq_evalWith_const]; rfl

/-- **Coherence without annotated subtraction (two distinct elaborations).** `sAASub`
is neither subtraction-annotated, nor subtraction-free, nor fully annotated; it has the two distinct declarative elaborations
`↑(a - a) = z` and `↑a - ↑a = z`, and all of its declarative elaborations evaluate
identically in every environment (truncated subtraction gives `a - a = 0` at `Nat`,
and `↑a - ↑a = 0` at `Int`). -/
theorem subAnnotated_not_necessary_for_coherence_cancel :
    sAASub.subAnnotated = false ∧ sAASub.subFree = false ∧ sAASub.fullyAnnotated = false ∧
    Elabs S₀ sAASub .prop (.eq .int (.coe (.sub .nat vA vA)) vZ) ∧
    Elabs S₀ sAASub .prop (.eq .int (.sub .int (.coe vA) (.coe vA)) vZ) ∧
    Tm.eq .int (.coe (.sub .nat vA vA)) vZ ≠ Tm.eq .int (.sub .int (.coe vA) (.coe vA)) vZ ∧
    ∀ τ t₁ t₂, Elabs S₀ sAASub τ t₁ → Elabs S₀ sAASub τ t₂ → ∀ ρ, eval S₀ ρ t₁ = eval S₀ ρ t₂ := by
  refine ⟨by decide, by decide, by decide,
    .eq (τ := .int) rfl (.inl rfl) (.coeIns (.sub rfl (.inl rfl) (.var rfl) (.var rfl))) (.var rfl),
    .eq (τ := .int) rfl (.inl rfl) (.sub rfl (.inl rfl) (.coeIns (.var rfl)) (.coeIns (.var rfl))) (.var rfl),
    by decide, ?_⟩
  have hv0 : S₀.varTy 0 = some .nat := rfl
  have hv2 : S₀.varTy 2 = some .int := rfl
  have sub_zero : ∀ t, Elabs S₀ (.sub none (.var 0) (.var 0)) .int t → ∀ ρ, eval S₀ ρ t = .int 0 := by
    intro t h ρ
    cases h with
    | sub _ _ ha hb =>
      have ea := (elabs_var0_eval S₀ hv0).2 _ ha ρ
      have eb := (elabs_var0_eval S₀ hv0).2 _ hb ρ
      rw [eval, evalD_eq_evalWith_const] at ea eb ⊢
      simp [evalWith, ea, eb, Val.toInt, Int.sub_self]
    | coeIns hn =>
      cases hn with
      | sub _ _ ha hb =>
        have ea := (elabs_var0_eval S₀ hv0).1 _ ha ρ
        have eb := (elabs_var0_eval S₀ hv0).1 _ hb ρ
        rw [eval, evalD_eq_evalWith_const] at ea eb ⊢
        simp [evalWith, ea, eb, Val.toNat, Nat.sub_self]
  have eq_eval : ∀ τ t, Elabs S₀ sAASub τ t → ∀ ρ, eval S₀ ρ t = .prop (decide (0 = ρ.int 2)) := by
    intro τ t h ρ
    cases h with
    | coeIns hnat => cases hnat
    | @eq _ σ _ _ a' b' hnum _ hsub hz =>
      cases σ with
      | prop => simp [Ty.isNum] at hnum
      | nat => exact absurd hz (not_elabs_int_var_at_nat _)
      | int =>
        have es := sub_zero a' hsub ρ
        have ez : eval S₀ ρ b' = .int (ρ.int 2) := by
          cases hz with
          | coeIns hzn => exact absurd hzn (not_elabs_int_var_at_nat _)
          | var hv =>
            rw [hv2] at hv; cases hv
            rw [eval, evalD_eq_evalWith_const]; rfl
        rw [eval, evalD_eq_evalWith_const] at es ez ⊢
        simp [evalWith, es, ez, Val.toInt]
  intro τ t₁ t₂ h₁ h₂ ρ
  rw [eq_eval τ t₁ h₁ ρ, eq_eval τ t₂ h₂ ρ]

/-- **A greedy rendering computed for `cfg0` can stay faithful for other readers.**
`ppMin cfg0 S₀ tEqAB` is faithful for every configuration (including the degenerate
ones with numeral default `Prop`), and `ppMin cfg0 S₀ tTrunc` is faithful for the
`Int`-numeral configuration, which differs from `cfg0`. -/
theorem ppMin_cfg0_tEqAB_faithful_for_all_cfg :
    WellTyped S₀ tEqAB ∧
    (∀ cfg : ElabCfg, Faithful cfg S₀ (ppMin cfg0 S₀ tEqAB) tEqAB) ∧
    cfgIntNumerals ≠ cfg0 ∧
    Faithful cfgIntNumerals S₀ (ppMin cfg0 S₀ tTrunc) tTrunc := by
  refine ⟨by decide, ?_, by decide, by decide⟩
  intro ⟨nd, rl⟩
  cases nd <;> cases rl <;> decide

end Toy.Render
