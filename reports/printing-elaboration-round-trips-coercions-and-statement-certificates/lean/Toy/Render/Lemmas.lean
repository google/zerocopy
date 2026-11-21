import Toy.Render.Defs

/-!
# Auxiliary lemmas (`Toy.Render`)

Structural lemmas about printing, elaboration and evaluation used by the proofs
in `Toy.Render.Statements`. None of them is a result card.
-/

namespace Toy.Render

/-! ## `coerceTo` -/

theorem coerceTo_self (exp : Option Ty) (t : Tm) (τ : Ty)
    (hexp : exp = none ∨ exp = some τ) : coerceTo exp (t, τ) = some (t, τ) := by
  rcases hexp with rfl | rfl <;> simp [coerceTo]

/-- `Tm.isCoe t`: the head constructor of `t` is a coercion. -/
def Tm.isCoe : Tm → Bool
  | .coe _ => true
  | _ => false

/-- Two successful repairs with the same result come from the same input, provided
neither input term is itself a coercion. -/
theorem coerceTo_inj (exp : Option Ty) (x y : Tm) (σ τ : Ty) (r : Tm × Ty)
    (hx : x.isCoe = false) (hy : y.isCoe = false)
    (h1 : coerceTo exp (x, σ) = some r) (h2 : coerceTo exp (y, τ) = some r) :
    x = y ∧ σ = τ := by
  cases exp with
  | none =>
    simp only [coerceTo] at h1 h2
    obtain rfl := Option.some.inj h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    exact ⟨h2.1.symm, h2.2.symm⟩
  | some ε =>
    simp only [coerceTo] at h1 h2
    by_cases hσ : σ = ε <;> by_cases hτ : τ = ε <;> simp only [hσ, hτ, ↓reduceIte] at h1 h2
    · obtain rfl := Option.some.inj h1
      simp only [Option.some.injEq, Prod.mk.injEq] at h2
      exact ⟨h2.1.symm, hσ.trans hτ.symm⟩
    · split at h2
      · obtain rfl := Option.some.inj h1
        simp only [Option.some.injEq, Prod.mk.injEq] at h2
        rw [← h2.1] at hx; simp [Tm.isCoe] at hx
      · simp at h2
    · split at h1
      · obtain rfl := Option.some.inj h1
        simp only [Option.some.injEq, Prod.mk.injEq] at h2
        rw [h2.1] at hy; simp [Tm.isCoe] at hy
      · simp at h1
    · split at h1 <;> split at h2
      · rename_i h1' h2'
        obtain rfl := Option.some.inj h1
        simp only [Option.some.injEq, Prod.mk.injEq, Tm.coe.injEq] at h2
        exact ⟨h2.1.symm, h1'.1.trans h2'.1.symm⟩
      all_goals simp at h1 h2

/-- With the same source type, a successful repair determines its input term. -/
theorem coerceTo_inj_sameTy (exp : Option Ty) (x y : Tm) (σ : Ty) (r : Tm × Ty)
    (h1 : coerceTo exp (x, σ) = some r) (h2 : coerceTo exp (y, σ) = some r) : x = y := by
  cases exp with
  | none =>
    simp only [coerceTo] at h1 h2
    obtain rfl := Option.some.inj h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    exact h2.1.symm
  | some ε =>
    simp only [coerceTo] at h1 h2
    by_cases hσ : σ = ε <;> simp only [hσ, ↓reduceIte] at h1 h2
    · obtain rfl := Option.some.inj h1
      simp only [Option.some.injEq, Prod.mk.injEq] at h2
      exact h2.1.symm
    · split at h1
      · rename_i hh
        simp only [hh, and_self, ↓reduceIte] at h2
        obtain rfl := Option.some.inj h1
        simp only [Option.some.injEq, Prod.mk.injEq, Tm.coe.injEq] at h2
        exact h2.1.symm
      · simp at h1

theorem coerceTo_some_ty (σ τ ρ : Ty) (u t : Tm)
    (hc : coerceTo (some σ) (u, ρ) = some (t, τ)) : τ = σ := by
  simp only [coerceTo] at hc
  split at hc
  · rename_i heq; cases hc; exact heq
  · split at hc
    · rename_i hni; cases hc; exact hni.2.symm
    · simp at hc

/-! ## Elaboration returns the expected type -/

theorem elabE_some_exp_ty (cfg : ElabCfg) (S : Sig) (σ τ : Ty) (s : Stx) (t : Tm)
    (h : elabE cfg S (some σ) s = some (t, τ)) : τ = σ := by
  cases s with
  | var x =>
    simp only [elabE] at h
    split at h
    · exact coerceTo_some_ty σ τ _ _ t h
    · simp at h
  | num n =>
    simp only [elabE] at h
    split at h
    · exact coerceTo_some_ty σ τ _ _ t h
    · simp at h
  | const c =>
    simp only [elabE] at h
    split at h
    · exact coerceTo_some_ty σ τ _ _ t h
    · simp at h
  | add oτ a b | sub oτ a b | eq oτ a b =>
    simp only [elabE] at h
    split at h
    · split at h
      · exact coerceTo_some_ty σ τ _ _ t h
      · simp at h
    · simp at h
  | iff a b | and a b =>
    simp only [elabE] at h
    split at h
    · exact coerceTo_some_ty σ τ _ _ t h
    · simp at h
  | asc e ρ =>
    simp only [elabE] at h
    split at h
    · exact coerceTo_some_ty σ τ _ _ t h
    · simp at h
  | coe e =>
    simp only [elabE] at h
    split at h
    · exact coerceTo_some_ty σ τ _ _ t h
    · simp at h

/-! ## The explicit printer -/

theorem elabE_ppExplicit (cfg : ElabCfg) (S : Sig) (t : Tm) (p : Path) (τ : Ty)
    (exp : Option Ty) (hty : tyOf S t = some τ) (hexp : exp = none ∨ exp = some τ) :
    elabE cfg S exp (ppMask (fun _ _ => true) p t) = some (t, τ) := by
  induction t generalizing p τ exp with
  | var x σ =>
    simp only [tyOf] at hty; split at hty <;> simp at hty
    rcases hty with rfl; rename_i hv
    simp [ppMask, elabE, hv, coerceTo_self _ _ _ hexp]
  | lit σ n =>
    simp only [tyOf] at hty; split at hty <;> simp at hty
    rcases hty with rfl; rename_i hn
    simp only [ppMask, elabE, numOnly, hn, ↓reduceIte, Option.getD_some, coerceTo]
    exact coerceTo_self _ _ _ hexp
  | add σ a b iha ihb =>
    simp only [tyOf] at hty; split at hty <;> simp at hty
    rcases hty with rfl; rename_i h; rcases h with ⟨hn, ha, hb⟩
    simp [ppMask, elabE, hn, iha (0 :: p) σ (some σ) ha (.inr rfl),
      ihb (1 :: p) σ (some σ) hb (.inr rfl), coerceTo_self _ _ _ hexp]
  | sub σ a b iha ihb =>
    simp only [tyOf] at hty; split at hty <;> simp at hty
    rcases hty with rfl; rename_i h; rcases h with ⟨hn, ha, hb⟩
    simp [ppMask, elabE, hn, iha (0 :: p) σ (some σ) ha (.inr rfl),
      ihb (1 :: p) σ (some σ) hb (.inr rfl), coerceTo_self _ _ _ hexp]
  | eq σ a b iha ihb =>
    simp only [tyOf] at hty; split at hty <;> simp at hty
    rcases hty with rfl; rename_i h; rcases h with ⟨hn, ha, hb⟩
    simp [ppMask, elabE, hn, iha (0 :: p) σ (some σ) ha (.inr rfl),
      ihb (1 :: p) σ (some σ) hb (.inr rfl), coerceTo_self _ _ _ hexp]
  | iff a b iha ihb =>
    simp only [tyOf] at hty; split at hty <;> simp at hty
    rcases hty with rfl; rename_i h; rcases h with ⟨ha, hb⟩
    simp [ppMask, elabE, iha (0 :: p) .prop (some .prop) ha (.inr rfl),
      ihb (1 :: p) .prop (some .prop) hb (.inr rfl), coerceTo_self _ _ _ hexp]
  | and a b iha ihb =>
    simp only [tyOf] at hty; split at hty <;> simp at hty
    rcases hty with rfl; rename_i h; rcases h with ⟨ha, hb⟩
    simp [ppMask, elabE, iha (0 :: p) .prop (some .prop) ha (.inr rfl),
      ihb (1 :: p) .prop (some .prop) hb (.inr rfl), coerceTo_self _ _ _ hexp]
  | coe a iha =>
    simp only [tyOf] at hty; split at hty <;> simp at hty
    rcases hty with rfl; rename_i ha
    simp [ppMask, elabE, iha (0 :: p) .nat (some .nat) ha (.inr rfl), coerceTo_self _ _ _ hexp]
  | const c =>
    simp only [tyOf] at hty
    simp [ppMask, elabE, hty, coerceTo_self _ _ _ hexp]

theorem ppExplicit_fullyAnnotated (p : Path) (t : Tm) :
    (ppMask (fun _ _ => true) p t).fullyAnnotated = true := by
  induction t generalizing p with
  | var _ _ | lit _ _ | const _ => rfl
  | add _ a b iha ihb => simp [ppMask, Stx.fullyAnnotated, iha (0 :: p), ihb (1 :: p)]
  | sub _ a b iha ihb => simp [ppMask, Stx.fullyAnnotated, iha (0 :: p), ihb (1 :: p)]
  | eq _ a b iha ihb => simp [ppMask, Stx.fullyAnnotated, iha (0 :: p), ihb (1 :: p)]
  | iff a b iha ihb => simp [ppMask, Stx.fullyAnnotated, iha (0 :: p), ihb (1 :: p)]
  | and a b iha ihb => simp [ppMask, Stx.fullyAnnotated, iha (0 :: p), ihb (1 :: p)]
  | coe a iha => simp [ppMask, Stx.fullyAnnotated, iha (0 :: p)]

/-! ## Agreement on fully annotated text -/

theorem elabE_eq_cfg0_of_fullyAnnotated (cfg : ElabCfg) (S : Sig) (s : Stx) (exp : Option Ty)
    (hs : s.fullyAnnotated = true) : elabE cfg S exp s = elabE cfg0 S exp s := by
  induction s generalizing exp with
  | var _ | const _ => rfl
  | num _ => simp [Stx.fullyAnnotated] at hs
  | add oτ a b iha ihb =>
    cases oτ with
    | none => simp [Stx.fullyAnnotated] at hs
    | some τ =>
      simp only [Stx.fullyAnnotated, Option.isSome_some, Bool.true_and, Bool.and_eq_true] at hs
      simp [elabE, iha _ hs.1, ihb _ hs.2]
  | sub oτ a b iha ihb =>
    cases oτ with
    | none => simp [Stx.fullyAnnotated] at hs
    | some τ =>
      simp only [Stx.fullyAnnotated, Option.isSome_some, Bool.true_and, Bool.and_eq_true] at hs
      simp [elabE, iha _ hs.1, ihb _ hs.2]
  | eq oτ a b iha ihb =>
    cases oτ with
    | none => simp [Stx.fullyAnnotated] at hs
    | some τ =>
      simp only [Stx.fullyAnnotated, Option.isSome_some, Bool.true_and, Bool.and_eq_true] at hs
      simp [elabE, iha _ hs.1, ihb _ hs.2]
  | iff a b iha ihb =>
    simp only [Stx.fullyAnnotated, Bool.and_eq_true] at hs
    simp [elabE, iha _ hs.1, ihb _ hs.2]
  | and a b iha ihb =>
    simp only [Stx.fullyAnnotated, Bool.and_eq_true] at hs
    simp [elabE, iha _ hs.1, ihb _ hs.2]
  | coe e ihe =>
    simp only [Stx.fullyAnnotated] at hs
    simp [elabE, ihe _ hs]
  | asc e τ ihe =>
    by_cases hn : ∃ n, e = .num n
    · rcases hn with ⟨n, rfl⟩
      cases τ <;> simp [elabE, numOnly, Ty.isNum, coerceTo, cfg0]
      · cases cfg.numDefault <;> simp
    · have hfa : e.fullyAnnotated = true := by
        cases e <;> simp_all [Stx.fullyAnnotated]
      simp only [elabE, ihe (some τ) hfa]

/-! ## The default printer -/

theorem ppMask_false_irrel (p q : Path) (t : Tm) :
    ppMask (fun _ _ => false) p t = ppMask (fun _ _ => false) q t := by
  induction t generalizing p q with
  | var _ _ | lit _ _ | const _ => rfl
  | add _ a b iha ihb => simp only [ppMask, iha (0 :: p) (0 :: q), ihb (1 :: p) (1 :: q)]
  | sub _ a b iha ihb => simp only [ppMask, iha (0 :: p) (0 :: q), ihb (1 :: p) (1 :: q)]
  | eq _ a b iha ihb => simp only [ppMask, iha (0 :: p) (0 :: q), ihb (1 :: p) (1 :: q)]
  | iff a b iha ihb => simp only [ppMask, iha (0 :: p) (0 :: q), ihb (1 :: p) (1 :: q)]
  | and a b iha ihb => simp only [ppMask, iha (0 :: p) (0 :: q), ihb (1 :: p) (1 :: q)]
  | coe a iha => simp only [ppMask, iha (0 :: p) (0 :: q)]

theorem ppDefault_annCount_zero (p : Path) (t : Tm) :
    (ppMask (fun _ _ => false) p t).annCount = 0 := by
  induction t generalizing p with
  | var _ _ | lit _ _ | const _ => rfl
  | add _ a b iha ihb => simp [ppMask, Stx.annCount, iha (0 :: p), ihb (1 :: p)]
  | sub _ a b iha ihb => simp [ppMask, Stx.annCount, iha (0 :: p), ihb (1 :: p)]
  | eq _ a b iha ihb => simp [ppMask, Stx.annCount, iha (0 :: p), ihb (1 :: p)]
  | iff a b iha ihb => simp [ppMask, Stx.annCount, iha (0 :: p), ihb (1 :: p)]
  | and a b iha ihb => simp [ppMask, Stx.annCount, iha (0 :: p), ihb (1 :: p)]
  | coe a iha => simp [ppMask, iha (0 :: p)]

theorem ppDefault_coerceTo (exp : Option Ty) (u t' : Tm) (σ τ : Ty)
    (hc : coerceTo exp (u, σ) = some (t', τ)) :
    ppMask (fun _ _ => false) [] t' = ppMask (fun _ _ => false) [] u := by
  cases exp with
  | none => cases hc; rfl
  | some ρ =>
    simp only [coerceTo] at hc
    split at hc
    · cases hc; rfl
    · split at hc
      · cases hc; simp only [ppMask, Bool.false_eq_true, ↓reduceIte, ppMask_false_irrel [0] []]
      · simp at hc

/-! ## Default recoverability -/

theorem hint_ppDefault (S : Sig) (p : Path) (t : Tm) :
    hint S (ppMask (fun _ _ => false) p t) = dh S t := by
  induction t generalizing p with
  | var _ _ | lit _ _ | const _ => rfl
  | add _ a b iha ihb => simp [ppMask, hint, dh, iha, ihb]
  | sub _ a b iha ihb => simp [ppMask, hint, dh, iha, ihb]
  | eq _ a b _ _ => simp [ppMask, hint, dh]
  | iff a b _ _ => simp [ppMask, hint, dh]
  | and a b _ _ => simp [ppMask, hint, dh]
  | coe a iha => simp [ppMask, dh, iha]

theorem numOnly_getD_isNum (e : Option Ty) (d : Ty) (hd : d.isNum = true) :
    ((numOnly e).getD d).isNum = true := by
  cases e with
  | none => simpa [numOnly] using hd
  | some τ =>
    simp only [numOnly]
    split
    · simpa
    · simpa using hd

/-- A repair that returns a coercion inserted it: the input was not a coercion, the
expected type was `Int` and the input type was `Nat`. -/
theorem coerceTo_eq_coe (e : Option Ty) (y x : Tm) (ρ τ : Ty) (hy : y.isCoe = false)
    (h : coerceTo e (y, ρ) = some (.coe x, τ)) :
    e = some .int ∧ x = y ∧ ρ = .nat ∧ τ = .int := by
  cases e with
  | none =>
    simp only [coerceTo, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.1] at hy; simp [Tm.isCoe] at hy
  | some ε =>
    simp only [coerceTo] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [h.1] at hy; simp [Tm.isCoe] at hy
    · split at h
      · rename_i hh
        simp only [Option.some.injEq, Prod.mk.injEq, Tm.coe.injEq] at h
        exact ⟨by rw [hh.2], h.1.symm, hh.1, h.2.symm⟩
      · simp at h

/-- Elaborating default text never yields a coercion at the root unless the expected
type is `Int`, and never yields a doubled coercion. -/
theorem elabE_ppDefault_coe (cfg : ElabCfg) (S : Sig) (t : Tm) :
    ∀ (p : Path) (e : Option Ty) (x : Tm) (τ : Ty),
      elabE cfg S e (ppMask (fun _ _ => false) p t) = some (.coe x, τ) →
        e = some .int ∧ x.isCoe = false := by
  induction t with
  | coe a iha =>
    intro p e x τ h
    simp only [ppMask, Bool.false_eq_true, ↓reduceIte] at h
    exact iha _ _ _ _ h
  | var y σ =>
    intro p e x τ h
    simp only [ppMask, elabE] at h
    split at h
    · obtain ⟨he, rfl, -, -⟩ := coerceTo_eq_coe _ _ _ _ _ rfl h
      exact ⟨he, rfl⟩
    · simp at h
  | lit σ n =>
    intro p e x τ h
    simp only [ppMask, Bool.false_eq_true, ↓reduceIte, elabE] at h
    split at h
    · obtain ⟨he, rfl, -, -⟩ := coerceTo_eq_coe _ _ _ _ _ rfl h
      exact ⟨he, rfl⟩
    · simp at h
  | const c =>
    intro p e x τ h
    simp only [ppMask, elabE] at h
    split at h
    · obtain ⟨he, rfl, -, -⟩ := coerceTo_eq_coe _ _ _ _ _ rfl h
      exact ⟨he, rfl⟩
    · simp at h
  | add σ a b _ _ | sub σ a b _ _ | eq σ a b _ _ =>
    intro p e x τ h
    simp only [ppMask, Bool.false_eq_true, ↓reduceIte, elabE] at h
    split at h
    · split at h
      · obtain ⟨he, rfl, -, -⟩ := coerceTo_eq_coe _ _ _ _ _ rfl h
        exact ⟨he, rfl⟩
      · simp at h
    · simp at h
  | iff a b _ _ | and a b _ _ =>
    intro p e x τ h
    simp only [ppMask, elabE] at h
    split at h
    · obtain ⟨he, rfl, -, -⟩ := coerceTo_eq_coe _ _ _ _ _ rfl h
      exact ⟨he, rfl⟩
    · simp at h

theorem tyMatches_some (σ τ : Ty) (h : tyMatches (some σ) τ = true) : τ = σ := by
  simp [tyMatches] at h; exact h.symm

/-- Soundness of `defRec`: a default-recoverable term's default text elaborates
(at the expected type `e`) to the term, repaired by `coerceTo e`. -/
theorem defRec_sound (S : Sig) (t : Tm) :
    ∀ (p : Path) (e w : Option Ty), defRec S e w t = true →
      ∃ σ, tyMatches w σ = true ∧
        elabE cfg0 S e (ppMask (fun _ _ => false) p t) = coerceTo e (t, σ) := by
  induction t with
  | var x τ =>
    intro p e w h
    simp only [defRec, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨τ, h.2, by simp [ppMask, elabE, h.1]⟩
  | lit τ n =>
    intro p e w h
    simp only [defRec, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hτ, hw⟩ := h
    refine ⟨τ, hw, ?_⟩
    have hn : ((numOnly e).getD Ty.nat).isNum = true := numOnly_getD_isNum e .nat rfl
    simp only [ppMask, Bool.false_eq_true, ↓reduceIte, elabE, cfg0]
    rw [← hτ] at hn ⊢
    simp [hn]
  | add τ a b iha ihb =>
    intro p e w h
    simp only [defRec, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hτ, hn⟩, ha⟩, hb⟩, hw⟩ := h
    obtain ⟨σa, hσa, ea⟩ := iha (0 :: p) _ _ ha
    obtain ⟨σb, hσb, eb⟩ := ihb (1 :: p) _ _ hb
    rw [tyMatches_some _ _ hσa, coerceTo_self _ _ _ (.inr rfl)] at ea
    rw [tyMatches_some _ _ hσb, coerceTo_self _ _ _ (.inr rfl)] at eb
    refine ⟨τ, hw, ?_⟩
    simp only [ppMask, Bool.false_eq_true, ↓reduceIte, elabE, Option.getD_none,
      hint_ppDefault, ← hτ, hn, ea, eb]
  | sub τ a b iha ihb =>
    intro p e w h
    simp only [defRec, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hτ, hn⟩, ha⟩, hb⟩, hw⟩ := h
    obtain ⟨σa, hσa, ea⟩ := iha (0 :: p) _ _ ha
    obtain ⟨σb, hσb, eb⟩ := ihb (1 :: p) _ _ hb
    rw [tyMatches_some _ _ hσa, coerceTo_self _ _ _ (.inr rfl)] at ea
    rw [tyMatches_some _ _ hσb, coerceTo_self _ _ _ (.inr rfl)] at eb
    refine ⟨τ, hw, ?_⟩
    simp only [ppMask, Bool.false_eq_true, ↓reduceIte, elabE, Option.getD_none,
      hint_ppDefault, ← hτ, hn, ea, eb]
  | eq τ a b iha ihb =>
    intro p e w h
    simp only [defRec, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hτ, hn⟩, ha⟩, hb⟩, hw⟩ := h
    obtain ⟨σa, hσa, ea⟩ := iha (0 :: p) _ _ ha
    obtain ⟨σb, hσb, eb⟩ := ihb (1 :: p) _ _ hb
    rw [tyMatches_some _ _ hσa, coerceTo_self _ _ _ (.inr rfl)] at ea
    rw [tyMatches_some _ _ hσb, coerceTo_self _ _ _ (.inr rfl)] at eb
    refine ⟨.prop, hw, ?_⟩
    have hτ' : τ = (joinH (dh S a) (dh S b)).getD cfg0.numDefault := hτ
    simp only [ppMask, Bool.false_eq_true, ↓reduceIte, elabE, Option.getD_none,
      hint_ppDefault, ← hτ', hn, ea, eb]
  | iff a b iha ihb =>
    intro p e w h
    simp only [defRec, Bool.and_eq_true] at h
    obtain ⟨⟨ha, hb⟩, hw⟩ := h
    obtain ⟨σa, hσa, ea⟩ := iha (0 :: p) _ _ ha
    obtain ⟨σb, hσb, eb⟩ := ihb (1 :: p) _ _ hb
    rw [tyMatches_some _ _ hσa, coerceTo_self _ _ _ (.inr rfl)] at ea
    rw [tyMatches_some _ _ hσb, coerceTo_self _ _ _ (.inr rfl)] at eb
    exact ⟨.prop, hw, by simp only [ppMask, elabE, ea, eb]⟩
  | and a b iha ihb =>
    intro p e w h
    simp only [defRec, Bool.and_eq_true] at h
    obtain ⟨⟨ha, hb⟩, hw⟩ := h
    obtain ⟨σa, hσa, ea⟩ := iha (0 :: p) _ _ ha
    obtain ⟨σb, hσb, eb⟩ := ihb (1 :: p) _ _ hb
    rw [tyMatches_some _ _ hσa, coerceTo_self _ _ _ (.inr rfl)] at ea
    rw [tyMatches_some _ _ hσb, coerceTo_self _ _ _ (.inr rfl)] at eb
    exact ⟨.prop, hw, by simp only [ppMask, elabE, ea, eb]⟩
  | coe a iha =>
    intro p e w h
    simp only [defRec, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨he, hw⟩, ha⟩ := h
    obtain ⟨σa, hσa, ea⟩ := iha (0 :: p) _ _ ha
    rw [tyMatches_some _ _ hσa] at ea
    subst he
    refine ⟨.int, hw, ?_⟩
    simp only [ppMask, Bool.false_eq_true, ↓reduceIte, ea]
    simp [coerceTo]
  | const c =>
    intro p e w h
    simp only [defRec] at h
    split at h
    · rename_i τ hc
      exact ⟨τ, h, by simp [ppMask, elabE, hc]⟩
    · simp at h

/-- Completeness of `defRec`: if the default text of `t` elaborates at `e` to the
repair of `t` at some type admitted by `w`, then `t` passes `defRec S e w`. -/
theorem defRec_complete (S : Sig) (t : Tm) :
    ∀ (p : Path) (e w : Option Ty) (σ : Ty) (r : Tm × Ty), tyMatches w σ = true →
      coerceTo e (t, σ) = some r →
      elabE cfg0 S e (ppMask (fun _ _ => false) p t) = some r → defRec S e w t = true := by
  induction t with
  | var x τ =>
    intro p e w σ r hw hc h
    simp only [ppMask, elabE] at h
    split at h
    · rename_i τ' hv
      obtain ⟨h1, h2⟩ := coerceTo_inj _ _ _ _ _ _ rfl rfl h hc
      cases h1
      subst h2
      simp [defRec, hv, hw]
    · simp at h
  | lit τ n =>
    intro p e w σ r hw hc h
    simp only [ppMask, Bool.false_eq_true, ↓reduceIte, elabE] at h
    split at h
    · obtain ⟨h1, h2⟩ := coerceTo_inj _ _ _ _ _ _ rfl rfl h hc
      cases h1
      simp only [defRec, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨rfl, h2 ▸ hw⟩
    · simp at h
  | add τ a b iha ihb =>
    intro p e w σ r hw hc h
    simp only [ppMask, Bool.false_eq_true, ↓reduceIte, elabE, Option.getD_none,
      hint_ppDefault] at h
    split at h
    · rename_i hn
      split at h
      · rename_i a' σa b' σb ha hb
        obtain ⟨h1, h2⟩ := coerceTo_inj _ _ _ _ _ _ rfl rfl h hc
        simp only [Tm.add.injEq] at h1
        obtain ⟨hτ, rfl, rfl⟩ := h1
        have hσa := elabE_some_exp_ty _ _ _ _ _ _ ha
        have hσb := elabE_some_exp_ty _ _ _ _ _ _ hb
        subst hσa hσb
        rw [hτ] at ha hb hn h2
        have da := iha (0 :: p) (some τ) (some τ) τ (a', τ) (by simp [tyMatches])
          (coerceTo_self _ _ _ (.inr rfl)) ha
        have db := ihb (1 :: p) (some τ) (some τ) τ (b', τ) (by simp [tyMatches])
          (coerceTo_self _ _ _ (.inr rfl)) hb
        simp only [defRec, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨⟨⟨hτ.symm, hn⟩, da⟩, db⟩, h2 ▸ hw⟩
      · simp at h
    · simp at h
  | sub τ a b iha ihb =>
    intro p e w σ r hw hc h
    simp only [ppMask, Bool.false_eq_true, ↓reduceIte, elabE, Option.getD_none,
      hint_ppDefault] at h
    split at h
    · rename_i hn
      split at h
      · rename_i a' σa b' σb ha hb
        obtain ⟨h1, h2⟩ := coerceTo_inj _ _ _ _ _ _ rfl rfl h hc
        simp only [Tm.sub.injEq] at h1
        obtain ⟨hτ, rfl, rfl⟩ := h1
        have hσa := elabE_some_exp_ty _ _ _ _ _ _ ha
        have hσb := elabE_some_exp_ty _ _ _ _ _ _ hb
        subst hσa hσb
        rw [hτ] at ha hb hn h2
        have da := iha (0 :: p) (some τ) (some τ) τ (a', τ) (by simp [tyMatches])
          (coerceTo_self _ _ _ (.inr rfl)) ha
        have db := ihb (1 :: p) (some τ) (some τ) τ (b', τ) (by simp [tyMatches])
          (coerceTo_self _ _ _ (.inr rfl)) hb
        simp only [defRec, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨⟨⟨hτ.symm, hn⟩, da⟩, db⟩, h2 ▸ hw⟩
      · simp at h
    · simp at h
  | eq τ a b iha ihb =>
    intro p e w σ r hw hc h
    simp only [ppMask, Bool.false_eq_true, ↓reduceIte, elabE, Option.getD_none,
      hint_ppDefault] at h
    split at h
    · rename_i hn
      split at h
      · rename_i a' σa b' σb ha hb
        obtain ⟨h1, h2⟩ := coerceTo_inj _ _ _ _ _ _ rfl rfl h hc
        simp only [Tm.eq.injEq] at h1
        obtain ⟨hτ, rfl, rfl⟩ := h1
        have hσa := elabE_some_exp_ty _ _ _ _ _ _ ha
        have hσb := elabE_some_exp_ty _ _ _ _ _ _ hb
        subst hσa hσb
        rw [hτ] at ha hb hn
        have da := iha (0 :: p) (some τ) (some τ) τ (a', τ) (by simp [tyMatches])
          (coerceTo_self _ _ _ (.inr rfl)) ha
        have db := ihb (1 :: p) (some τ) (some τ) τ (b', τ) (by simp [tyMatches])
          (coerceTo_self _ _ _ (.inr rfl)) hb
        simp only [defRec, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨⟨⟨hτ.symm, hn⟩, da⟩, db⟩, h2 ▸ hw⟩
      · simp at h
    · simp at h
  | iff a b iha ihb =>
    intro p e w σ r hw hc h
    simp only [ppMask, elabE] at h
    split at h
    · rename_i a' σa b' σb ha hb
      obtain ⟨h1, h2⟩ := coerceTo_inj _ _ _ _ _ _ rfl rfl h hc
      simp only [Tm.iff.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      have hσa := elabE_some_exp_ty _ _ _ _ _ _ ha
      have hσb := elabE_some_exp_ty _ _ _ _ _ _ hb
      subst hσa hσb
      have da := iha (0 :: p) (some .prop) (some .prop) .prop _ (by simp [tyMatches])
        (coerceTo_self _ _ _ (.inr rfl)) ha
      have db := ihb (1 :: p) (some .prop) (some .prop) .prop _ (by simp [tyMatches])
        (coerceTo_self _ _ _ (.inr rfl)) hb
      simp only [defRec, Bool.and_eq_true]
      exact ⟨⟨da, db⟩, h2 ▸ hw⟩
    · simp at h
  | and a b iha ihb =>
    intro p e w σ r hw hc h
    simp only [ppMask, elabE] at h
    split at h
    · rename_i a' σa b' σb ha hb
      obtain ⟨h1, h2⟩ := coerceTo_inj _ _ _ _ _ _ rfl rfl h hc
      simp only [Tm.and.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      have hσa := elabE_some_exp_ty _ _ _ _ _ _ ha
      have hσb := elabE_some_exp_ty _ _ _ _ _ _ hb
      subst hσa hσb
      have da := iha (0 :: p) (some .prop) (some .prop) .prop _ (by simp [tyMatches])
        (coerceTo_self _ _ _ (.inr rfl)) ha
      have db := ihb (1 :: p) (some .prop) (some .prop) .prop _ (by simp [tyMatches])
        (coerceTo_self _ _ _ (.inr rfl)) hb
      simp only [defRec, Bool.and_eq_true]
      exact ⟨⟨da, db⟩, h2 ▸ hw⟩
    · simp at h
  | coe a iha =>
    intro p e w σ r hw hc h
    simp only [ppMask, Bool.false_eq_true, ↓reduceIte] at h
    cases e with
    | none =>
      simp only [coerceTo] at hc
      obtain rfl := Option.some.inj hc
      exact absurd (elabE_ppDefault_coe cfg0 S a _ _ _ _ h).1 (by simp)
    | some ε =>
      simp only [coerceTo] at hc
      split at hc
      · rename_i hσ
        obtain rfl := Option.some.inj hc
        obtain ⟨hε, -⟩ := elabE_ppDefault_coe cfg0 S a _ _ _ _ h
        cases hε
        subst hσ
        have da := iha (0 :: p) (some .int) (some .nat) .nat _ (by simp [tyMatches])
          (by simp [coerceTo]) h
        simp only [defRec, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨trivial, hw⟩, da⟩
      · split at hc
        · obtain rfl := Option.some.inj hc
          have := (elabE_ppDefault_coe cfg0 S a _ _ _ _ h).2
          simp [Tm.isCoe] at this
        · simp at hc
  | const c =>
    intro p e w σ r hw hc h
    simp only [ppMask, elabE] at h
    split at h
    · rename_i τ hct
      obtain ⟨-, h2⟩ := coerceTo_inj _ _ _ _ _ _ rfl rfl h hc
      simp [defRec, hct, h2, hw]
    · simp at h

/-! ## Annotation-free text -/

theorem ppDefault_elabE_of_annotationFree (cfg : ElabCfg) (S : Sig) (s : Stx)
    (exp : Option Ty) (t' : Tm) (τ : Ty)
    (hs : s.annCount = 0) (h : elabE cfg S exp s = some (t', τ)) :
    ppMask (fun _ _ => false) [] t' = s := by
  induction s generalizing exp t' τ with
  | var x =>
    simp only [elabE] at h
    match hv : S.varTy x with
    | none => simp [hv] at h
    | some _ =>
      simp only [hv] at h
      rw [ppDefault_coerceTo _ _ _ _ _ h]; rfl
  | num n =>
    simp only [elabE] at h
    by_cases hnum : ((numOnly exp).getD cfg.numDefault).isNum = true
    · simp only [hnum, ↓reduceIte] at h
      rw [ppDefault_coerceTo _ _ _ _ _ h]; rfl
    · simp [hnum] at h
  | const c =>
    simp only [elabE] at h
    match hc : S.constTy c with
    | none => simp [hc] at h
    | some _ =>
      simp only [hc] at h
      rw [ppDefault_coerceTo _ _ _ _ _ h]; rfl
  | asc _ _ | coe _ => simp [Stx.annCount] at hs
  | add oτ a b iha ihb =>
    cases oτ with
    | some _ => simp [Stx.annCount] at hs
    | none =>
      simp only [Stx.annCount, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Nat.zero_add,
        Nat.add_eq_zero_iff] at hs
      simp only [elabE, Option.getD_none] at h
      let σ := opType cfg (joinH (hint S a) (hint S b)) exp
      by_cases hnum : σ.isNum = true
      · simp only [σ, hnum, ↓reduceIte] at h
        match ha : elabE cfg S (some σ) a, hb : elabE cfg S (some σ) b with
        | some ⟨a', _⟩, some ⟨b', _⟩ =>
          simp only [σ] at ha hb
          simp only [ha, hb] at h
          rw [ppDefault_coerceTo _ _ _ _ _ h]
          simp only [ppMask, Bool.false_eq_true, ↓reduceIte, ppMask_false_irrel [0] [],
            ppMask_false_irrel [1] [], iha _ _ _ hs.1 ha, ihb _ _ _ hs.2 hb]
        | none, _ => simp [σ, ha] at h
        | some _, none => simp [σ, ha, hb] at h
      · simp [σ, hnum] at h
  | sub oτ a b iha ihb =>
    cases oτ with
    | some _ => simp [Stx.annCount] at hs
    | none =>
      simp only [Stx.annCount, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Nat.zero_add,
        Nat.add_eq_zero_iff] at hs
      simp only [elabE, Option.getD_none] at h
      let σ := opType cfg (joinH (hint S a) (hint S b)) exp
      by_cases hnum : σ.isNum = true
      · simp only [σ, hnum, ↓reduceIte] at h
        match ha : elabE cfg S (some σ) a, hb : elabE cfg S (some σ) b with
        | some ⟨a', _⟩, some ⟨b', _⟩ =>
          simp only [σ] at ha hb
          simp only [ha, hb] at h
          rw [ppDefault_coerceTo _ _ _ _ _ h]
          simp only [ppMask, Bool.false_eq_true, ↓reduceIte, ppMask_false_irrel [0] [],
            ppMask_false_irrel [1] [], iha _ _ _ hs.1 ha, ihb _ _ _ hs.2 hb]
        | none, _ => simp [σ, ha] at h
        | some _, none => simp [σ, ha, hb] at h
      · simp [σ, hnum] at h
  | eq oτ a b iha ihb =>
    cases oτ with
    | some _ => simp [Stx.annCount] at hs
    | none =>
      simp only [Stx.annCount, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Nat.zero_add,
        Nat.add_eq_zero_iff] at hs
      simp only [elabE, Option.getD_none] at h
      let σ := (joinH (hint S a) (hint S b)).getD cfg.numDefault
      by_cases hnum : σ.isNum = true
      · simp only [σ, hnum, ↓reduceIte] at h
        match ha : elabE cfg S (some σ) a, hb : elabE cfg S (some σ) b with
        | some ⟨a', _⟩, some ⟨b', _⟩ =>
          simp only [σ] at ha hb
          simp only [ha, hb] at h
          rw [ppDefault_coerceTo _ _ _ _ _ h]
          simp only [ppMask, Bool.false_eq_true, ↓reduceIte, ppMask_false_irrel [0] [],
            ppMask_false_irrel [1] [], iha _ _ _ hs.1 ha, ihb _ _ _ hs.2 hb]
        | none, _ => simp [σ, ha] at h
        | some _, none => simp [σ, ha, hb] at h
      · simp [σ, hnum] at h
  | iff a b iha ihb =>
    simp only [Stx.annCount, Nat.add_eq_zero_iff] at hs
    simp only [elabE] at h
    match ha : elabE cfg S (some .prop) a, hb : elabE cfg S (some .prop) b with
    | some ⟨a', _⟩, some ⟨b', _⟩ =>
      simp only [ha, hb] at h
      rw [ppDefault_coerceTo _ _ _ _ _ h]
      simp only [ppMask, ppMask_false_irrel [0] [], ppMask_false_irrel [1] [],
        iha _ _ _ hs.1 ha, ihb _ _ _ hs.2 hb]
    | none, _ => simp [ha] at h
    | some _, none => simp [ha, hb] at h
  | and a b iha ihb =>
    simp only [Stx.annCount, Nat.add_eq_zero_iff] at hs
    simp only [elabE] at h
    match ha : elabE cfg S (some .prop) a, hb : elabE cfg S (some .prop) b with
    | some ⟨a', _⟩, some ⟨b', _⟩ =>
      simp only [ha, hb] at h
      rw [ppDefault_coerceTo _ _ _ _ _ h]
      simp only [ppMask, ppMask_false_irrel [0] [], ppMask_false_irrel [1] [],
        iha _ _ _ hs.1 ha, ihb _ _ _ hs.2 hb]
    | none, _ => simp [ha] at h
    | some _, none => simp [ha, hb] at h


/-! ## δ-unfolding -/

theorem evalWith_substConst (k : Nat → Val) (ρ : Env) (c : Nat) (b t : Tm) :
    evalWith k ρ (substConst c b t) =
      evalWith (fun c' => if c' = c then evalWith k ρ b else k c') ρ t := by
  induction t with
  | var _ _ | lit _ _ => rfl
  | const c' => by_cases h : c' = c <;> simp [substConst, evalWith, h]
  | add τ x y ihx ihy => cases τ <;> simp [substConst, evalWith, ihx, ihy]
  | sub τ x y ihx ihy => cases τ <;> simp [substConst, evalWith, ihx, ihy]
  | eq τ x y ihx ihy => cases τ <;> simp [substConst, evalWith, ihx, ihy]
  | iff x y ihx ihy => simp [substConst, evalWith, ihx, ihy]
  | and x y ihx ihy => simp [substConst, evalWith, ihx, ihy]
  | coe x ih => simp [substConst, evalWith, ih]

theorem evalD_eq_evalWith_const (D : List Def) (ρ : Env) (t : Tm) :
    evalD D ρ t = evalWith (fun c => evalD D ρ (.const c)) ρ t := by
  cases D <;> rfl

theorem evalD_eq_unfoldDefs (D : List Def) (ρ : Env) (t : Tm) :
    evalD D ρ t = evalD [] ρ (unfoldDefs D t) := by
  induction D generalizing t with
  | nil => rfl
  | cons d D ih =>
    rw [unfoldDefs, ← ih, evalD_eq_evalWith_const D ρ (substConst d.name d.body t),
      evalWith_substConst]
    simp only [evalD, ← evalD_eq_evalWith_const D ρ d.body]


/-! ## Soundness of the deterministic elaborators -/

theorem coerceTo_sound (S : Sig) (s : Stx) (exp : Option Ty) (u t : Tm) (σ τ : Ty)
    (hel : Elabs S s σ u) (hty : tyOf S u = some σ)
    (hc : coerceTo exp (u, σ) = some (t, τ)) : Elabs S s τ t ∧ tyOf S t = some τ := by
  cases exp with
  | none => cases hc; exact ⟨hel, hty⟩
  | some ρ =>
    simp only [coerceTo] at hc
    split at hc
    · cases hc; exact ⟨hel, hty⟩
    · split at hc
      · rename_i hni
        rcases hni with ⟨rfl, rfl⟩
        cases hc
        exact ⟨.coeIns hel, by simp [tyOf, hty]⟩
      · simp at hc

theorem option_getD_eq_or (o : Option Ty) (d : Ty) :
    o = none ∨ o = some (o.getD d) := by
  cases o <;> simp


theorem elabE_sound_aux (cfg : ElabCfg) (S : Sig) (exp : Option Ty) (s : Stx) (t : Tm) (τ : Ty)
    (h : elabE cfg S exp s = some (t, τ)) : Elabs S s τ t ∧ tyOf S t = some τ := by
  induction s generalizing exp t τ with
  | var x =>
    simp only [elabE] at h
    match hv : S.varTy x with
    | none => simp [hv] at h
    | some σ =>
      simp only [hv] at h
      exact coerceTo_sound S _ exp _ t σ τ (.var hv) (by simp [tyOf, hv]) h
  | num n =>
    simp only [elabE] at h
    by_cases hn : ((numOnly exp).getD cfg.numDefault).isNum = true
    · simp only [hn, ↓reduceIte] at h
      exact coerceTo_sound S _ exp _ t _ τ (.num hn) (by simp [tyOf, hn]) h
    · simp [hn] at h
  | const c =>
    simp only [elabE] at h
    match hc : S.constTy c with
    | none => simp [hc] at h
    | some σ =>
      simp only [hc] at h
      exact coerceTo_sound S _ exp _ t σ τ (.const hc) (by simp [tyOf, hc]) h
  | add oτ a b iha ihb =>
    simp only [elabE] at h
    let σ := oτ.getD (opType cfg (joinH (hint S a) (hint S b)) exp)
    by_cases hn : σ.isNum = true
    · simp only [σ, hn, ↓reduceIte] at h
      match ha : elabE cfg S (some σ) a, hb : elabE cfg S (some σ) b with
      | some ⟨a', σa⟩, some ⟨b', σb⟩ =>
        simp only [σ] at ha hb
        simp only [ha, hb] at h
        rcases elabE_some_exp_ty cfg S σ σa a a' ha with rfl
        rcases elabE_some_exp_ty cfg S σ σb b b' hb with rfl
        have ⟨hela, htya⟩ := iha _ _ _ ha
        have ⟨helb, htyb⟩ := ihb _ _ _ hb
        exact coerceTo_sound S _ exp _ t σ τ (.add hn (option_getD_eq_or oτ _) hela helb)
          (by simp [tyOf, hn, htya, htyb]) h
      | none, _ => simp [σ, ha] at h
      | some _, none => simp [σ, ha, hb] at h
    · simp [σ, hn] at h
  | sub oτ a b iha ihb =>
    simp only [elabE] at h
    let σ := oτ.getD (opType cfg (joinH (hint S a) (hint S b)) exp)
    by_cases hn : σ.isNum = true
    · simp only [σ, hn, ↓reduceIte] at h
      match ha : elabE cfg S (some σ) a, hb : elabE cfg S (some σ) b with
      | some ⟨a', σa⟩, some ⟨b', σb⟩ =>
        simp only [σ] at ha hb
        simp only [ha, hb] at h
        rcases elabE_some_exp_ty cfg S σ σa a a' ha with rfl
        rcases elabE_some_exp_ty cfg S σ σb b b' hb with rfl
        have ⟨hela, htya⟩ := iha _ _ _ ha
        have ⟨helb, htyb⟩ := ihb _ _ _ hb
        exact coerceTo_sound S _ exp _ t σ τ (.sub hn (option_getD_eq_or oτ _) hela helb)
          (by simp [tyOf, hn, htya, htyb]) h
      | none, _ => simp [σ, ha] at h
      | some _, none => simp [σ, ha, hb] at h
    · simp [σ, hn] at h
  | eq oτ a b iha ihb =>
    simp only [elabE] at h
    let σ := oτ.getD ((joinH (hint S a) (hint S b)).getD cfg.numDefault)
    by_cases hn : σ.isNum = true
    · simp only [σ, hn, ↓reduceIte] at h
      match ha : elabE cfg S (some σ) a, hb : elabE cfg S (some σ) b with
      | some ⟨a', σa⟩, some ⟨b', σb⟩ =>
        simp only [σ] at ha hb
        simp only [ha, hb] at h
        rcases elabE_some_exp_ty cfg S σ σa a a' ha with rfl
        rcases elabE_some_exp_ty cfg S σ σb b b' hb with rfl
        have ⟨hela, htya⟩ := iha _ _ _ ha
        have ⟨helb, htyb⟩ := ihb _ _ _ hb
        exact coerceTo_sound S _ exp _ t .prop τ (.eq hn (option_getD_eq_or oτ _) hela helb)
          (by simp [tyOf, hn, htya, htyb]) h
      | none, _ => simp [σ, ha] at h
      | some _, none => simp [σ, ha, hb] at h
    · simp [σ, hn] at h
  | iff a b iha ihb =>
    simp only [elabE] at h
    match ha : elabE cfg S (some .prop) a, hb : elabE cfg S (some .prop) b with
    | some ⟨a', σa⟩, some ⟨b', σb⟩ =>
      simp only [ha, hb] at h
      rcases elabE_some_exp_ty cfg S .prop σa a a' ha with rfl
      rcases elabE_some_exp_ty cfg S .prop σb b b' hb with rfl
      have ⟨hela, htya⟩ := iha _ _ _ ha
      have ⟨helb, htyb⟩ := ihb _ _ _ hb
      exact coerceTo_sound S _ exp _ t .prop τ (.iff hela helb) (by simp [tyOf, htya, htyb]) h
    | none, _ => simp [ha] at h
    | some _, none => simp [ha, hb] at h
  | and a b iha ihb =>
    simp only [elabE] at h
    match ha : elabE cfg S (some .prop) a, hb : elabE cfg S (some .prop) b with
    | some ⟨a', σa⟩, some ⟨b', σb⟩ =>
      simp only [ha, hb] at h
      rcases elabE_some_exp_ty cfg S .prop σa a a' ha with rfl
      rcases elabE_some_exp_ty cfg S .prop σb b b' hb with rfl
      have ⟨hela, htya⟩ := iha _ _ _ ha
      have ⟨helb, htyb⟩ := ihb _ _ _ hb
      exact coerceTo_sound S _ exp _ t .prop τ (.and hela helb) (by simp [tyOf, htya, htyb]) h
    | none, _ => simp [ha] at h
    | some _, none => simp [ha, hb] at h
  | asc e σ ihe =>
    simp only [elabE] at h
    match he : elabE cfg S (some σ) e with
    | none => simp [he] at h
    | some ⟨e', σe⟩ =>
      simp only [he] at h
      have hσe : σe = σ := elabE_some_exp_ty cfg S σ σe e e' he
      subst hσe
      have ⟨hele, htye⟩ := ihe _ _ _ he
      exact coerceTo_sound S _ exp _ t _ τ (.asc hele) htye h
  | coe e ihe =>
    simp only [elabE] at h
    match he : elabE cfg S (some .nat) e with
    | none => simp [he] at h
    | some ⟨e', σe⟩ =>
      simp only [he] at h
      rcases elabE_some_exp_ty cfg S .nat σe e e' he with rfl
      have ⟨hele, htye⟩ := ihe _ _ _ he
      exact coerceTo_sound S _ exp _ t .int τ (.coe hele) (by simp [tyOf, htye]) h


/-! ## Coherence of declarative elaboration -/

/-- The joint invariant behind both coherence theorems, for syntax in which every
subtraction carries an explicit type argument: two elaborations at the same type
evaluate identically, and an elaboration at `Int` evaluates to the cast of any
elaboration at `Nat`. Stated for an arbitrary interpretation `k` of names. -/
theorem elabs_coh_aux (S : Sig) (k : Nat → Val) (ρ : Env) (s : Stx)
    (hs : s.subAnnotated = true) :
    (∀ τ t₁ t₂, Elabs S s τ t₁ → Elabs S s τ t₂ → evalWith k ρ t₁ = evalWith k ρ t₂) ∧
    (∀ t₁ t₂, Elabs S s .int t₁ → Elabs S s .nat t₂ →
      evalWith k ρ t₁ = .int (Int.ofNat (evalWith k ρ t₂).toNat)) := by
  induction s with
  | var x =>
    have same : ∀ τ t₁ t₂, Elabs S (.var x) τ t₁ → Elabs S (.var x) τ t₂ →
        evalWith k ρ t₁ = evalWith k ρ t₂ := by
      intro τ t₁ t₂ h₁ h₂
      cases h₁ with
      | var hv₁ =>
        cases h₂ with
        | var _ => rfl
        | coeIns h₂' => cases h₂' with | var hv₂ => rw [hv₁] at hv₂; cases hv₂
      | coeIns h₁' =>
        cases h₁' with
        | var hv₁ =>
          cases h₂ with
          | var hv₂ => rw [hv₁] at hv₂; cases hv₂
          | coeIns h₂' => cases h₂' with | var _ => rfl
    refine ⟨same, ?_⟩
    intro t₁ t₂ h₁ h₂
    cases h₁ with
    | var hv₁ => cases h₂ with | var hv₂ => rw [hv₁] at hv₂; cases hv₂
    | coeIns h₁' => simp only [evalWith, same _ _ _ h₁' h₂]
  | num n =>
    have same : ∀ τ t₁ t₂, Elabs S (.num n) τ t₁ → Elabs S (.num n) τ t₂ →
        evalWith k ρ t₁ = evalWith k ρ t₂ := by
      intro τ t₁ t₂ h₁ h₂
      cases h₁ with
      | num _ =>
        cases h₂ with
        | num _ => rfl
        | coeIns h₂' => cases h₂' with | num _ => rfl
      | coeIns h₁' =>
        cases h₁' with
        | num _ =>
          cases h₂ with
          | num _ => rfl
          | coeIns h₂' => cases h₂' with | num _ => rfl
    refine ⟨same, ?_⟩
    intro t₁ t₂ h₁ h₂
    cases h₁ with
    | num _ => cases h₂ with | num _ => rfl
    | coeIns h₁' => simp only [evalWith, same _ _ _ h₁' h₂]
  | const c =>
    have same : ∀ τ t₁ t₂, Elabs S (.const c) τ t₁ → Elabs S (.const c) τ t₂ →
        evalWith k ρ t₁ = evalWith k ρ t₂ := by
      intro τ t₁ t₂ h₁ h₂
      cases h₁ with
      | const hv₁ =>
        cases h₂ with
        | const _ => rfl
        | coeIns h₂' => cases h₂' with | const hv₂ => rw [hv₁] at hv₂; cases hv₂
      | coeIns h₁' =>
        cases h₁' with
        | const hv₁ =>
          cases h₂ with
          | const hv₂ => rw [hv₁] at hv₂; cases hv₂
          | coeIns h₂' => cases h₂' with | const _ => rfl
    refine ⟨same, ?_⟩
    intro t₁ t₂ h₁ h₂
    cases h₁ with
    | const hv₁ => cases h₂ with | const hv₂ => rw [hv₁] at hv₂; cases hv₂
    | coeIns h₁' => simp only [evalWith, same _ _ _ h₁' h₂]
  | add oτ a b iha ihb =>
    simp only [Stx.subAnnotated, Bool.and_eq_true] at hs
    obtain ⟨sa, ca⟩ := iha hs.1
    obtain ⟨sb, cb⟩ := ihb hs.2
    have same : ∀ τ t₁ t₂, Elabs S (.add oτ a b) τ t₁ → Elabs S (.add oτ a b) τ t₂ →
        evalWith k ρ t₁ = evalWith k ρ t₂ := by
      intro τ t₁ t₂ h₁ h₂
      cases h₁ with
      | add hn₁ _ ha₁ hb₁ =>
        cases h₂ with
        | add _ _ ha₂ hb₂ => simp only [evalWith, sa _ _ _ ha₁ ha₂, sb _ _ _ hb₁ hb₂]
        | coeIns h₂' =>
          cases h₂' with
          | add _ _ ha₂ hb₂ =>
            simp only [evalWith, ca _ _ ha₁ ha₂, cb _ _ hb₁ hb₂, Val.toInt, Val.toNat]
            simp only [Val.int.injEq, Int.ofNat_eq_natCast]; omega
      | coeIns h₁' =>
        cases h₁' with
        | add _ _ ha₁ hb₁ =>
          cases h₂ with
          | add _ _ ha₂ hb₂ =>
            simp only [evalWith, ca _ _ ha₂ ha₁, cb _ _ hb₂ hb₁, Val.toInt, Val.toNat]
            simp only [Val.int.injEq, Int.ofNat_eq_natCast]; omega
          | coeIns h₂' =>
            cases h₂' with
            | add _ _ ha₂ hb₂ => simp only [evalWith, sa _ _ _ ha₁ ha₂, sb _ _ _ hb₁ hb₂]
    refine ⟨same, ?_⟩
    intro t₁ t₂ h₁ h₂
    cases h₁ with
    | add _ _ ha₁ hb₁ =>
      cases h₂ with
      | add _ _ ha₂ hb₂ =>
        simp only [evalWith, ca _ _ ha₁ ha₂, cb _ _ hb₁ hb₂, Val.toInt, Val.toNat]
        simp only [Val.int.injEq, Int.ofNat_eq_natCast]; omega
    | coeIns h₁' => simp only [evalWith, same _ _ _ h₁' h₂]
  | sub oτ a b iha ihb =>
    simp only [Stx.subAnnotated, Bool.and_eq_true] at hs
    obtain ⟨⟨hsome, hsa⟩, hsb⟩ := hs
    obtain ⟨sa, _⟩ := iha hsa
    obtain ⟨sb, _⟩ := ihb hsb
    have same : ∀ τ t₁ t₂, Elabs S (.sub oτ a b) τ t₁ → Elabs S (.sub oτ a b) τ t₂ →
        evalWith k ρ t₁ = evalWith k ρ t₂ := by
      intro τ t₁ t₂ h₁ h₂
      cases h₁ with
      | sub _ ho₁ ha₁ hb₁ =>
        cases h₂ with
        | sub _ _ ha₂ hb₂ => simp only [evalWith, sa _ _ _ ha₁ ha₂, sb _ _ _ hb₁ hb₂]
        | coeIns h₂' =>
          cases h₂' with
          | sub _ ho₂ _ _ =>
            rcases ho₁ with rfl | rfl <;> rcases ho₂ with h | h <;> simp_all
      | coeIns h₁' =>
        cases h₁' with
        | sub _ ho₁ ha₁ hb₁ =>
          cases h₂ with
          | sub _ ho₂ _ _ =>
            rcases ho₁ with rfl | rfl <;> rcases ho₂ with h | h <;> simp_all
          | coeIns h₂' =>
            cases h₂' with
            | sub _ _ ha₂ hb₂ => simp only [evalWith, sa _ _ _ ha₁ ha₂, sb _ _ _ hb₁ hb₂]
    refine ⟨same, ?_⟩
    intro t₁ t₂ h₁ h₂
    cases h₁ with
    | sub _ ho₁ _ _ =>
      cases h₂ with
      | sub _ ho₂ _ _ => rcases ho₁ with rfl | rfl <;> rcases ho₂ with h | h <;> simp_all
    | coeIns h₁' => simp only [evalWith, same _ _ _ h₁' h₂]
  | eq oτ a b iha ihb =>
    simp only [Stx.subAnnotated, Bool.and_eq_true] at hs
    obtain ⟨sa, ca⟩ := iha hs.1
    obtain ⟨sb, cb⟩ := ihb hs.2
    refine ⟨?_, ?_⟩
    · intro τ t₁ t₂ h₁ h₂
      cases h₁ with
      | @eq _ σ₁ _ _ a₁ b₁ hn₁ _ ha₁ hb₁ =>
        cases h₂ with
        | @eq _ σ₂ _ _ a₂ b₂ hn₂ _ ha₂ hb₂ =>
          cases σ₁ <;> cases σ₂ <;> simp [Ty.isNum] at hn₁ hn₂
          · simp only [evalWith, sa _ _ _ ha₁ ha₂, sb _ _ _ hb₁ hb₂]
          · simp only [evalWith, ca _ _ ha₂ ha₁, cb _ _ hb₂ hb₁, Val.toInt, Val.toNat]
            simp only [Int.ofNat.injEq]; congr 1
          · simp only [evalWith, ca _ _ ha₁ ha₂, cb _ _ hb₁ hb₂, Val.toInt, Val.toNat]
            simp only [Int.ofNat.injEq]; congr 1
          · simp only [evalWith, sa _ _ _ ha₁ ha₂, sb _ _ _ hb₁ hb₂]
      | coeIns h₁' => cases h₁'
    · intro t₁ t₂ h₁ h₂
      cases h₂
  | iff a b iha ihb =>
    simp only [Stx.subAnnotated, Bool.and_eq_true] at hs
    obtain ⟨sa, _⟩ := iha hs.1
    obtain ⟨sb, _⟩ := ihb hs.2
    refine ⟨?_, ?_⟩
    · intro τ t₁ t₂ h₁ h₂
      cases h₁ with
      | iff ha₁ hb₁ =>
        cases h₂ with
        | iff ha₂ hb₂ => simp only [evalWith, sa _ _ _ ha₁ ha₂, sb _ _ _ hb₁ hb₂]
      | coeIns h₁' => cases h₁'
    · intro t₁ t₂ h₁ h₂
      cases h₂
  | and a b iha ihb =>
    simp only [Stx.subAnnotated, Bool.and_eq_true] at hs
    obtain ⟨sa, _⟩ := iha hs.1
    obtain ⟨sb, _⟩ := ihb hs.2
    refine ⟨?_, ?_⟩
    · intro τ t₁ t₂ h₁ h₂
      cases h₁ with
      | and ha₁ hb₁ =>
        cases h₂ with
        | and ha₂ hb₂ => simp only [evalWith, sa _ _ _ ha₁ ha₂, sb _ _ _ hb₁ hb₂]
      | coeIns h₁' => cases h₁'
    · intro t₁ t₂ h₁ h₂
      cases h₂
  | asc e σ ihe =>
    simp only [Stx.subAnnotated] at hs
    obtain ⟨se, _⟩ := ihe hs
    have same : ∀ τ t₁ t₂, Elabs S (.asc e σ) τ t₁ → Elabs S (.asc e σ) τ t₂ →
        evalWith k ρ t₁ = evalWith k ρ t₂ := by
      intro τ t₁ t₂ h₁ h₂
      cases h₁ with
      | asc he₁ =>
        cases h₂ with
        | asc he₂ => exact se _ _ _ he₁ he₂
        | coeIns h₂' => cases h₂'
      | coeIns h₁' =>
        cases h₁' with
        | asc he₁ =>
          cases h₂ with
          | coeIns h₂' => cases h₂' with | asc he₂ => simp only [evalWith, se _ _ _ he₁ he₂]
    refine ⟨same, ?_⟩
    intro t₁ t₂ h₁ h₂
    cases h₁ with
    | asc _ => cases h₂
    | coeIns h₁' => simp only [evalWith, same _ _ _ h₁' h₂]
  | coe e ihe =>
    simp only [Stx.subAnnotated] at hs
    obtain ⟨se, _⟩ := ihe hs
    refine ⟨?_, ?_⟩
    · intro τ t₁ t₂ h₁ h₂
      cases h₁ with
      | coe he₁ =>
        cases h₂ with
        | coe he₂ => simp only [evalWith, se _ _ _ he₁ he₂]
        | coeIns h₂' => cases h₂'
      | coeIns h₁' => cases h₁'
    · intro t₁ t₂ h₁ h₂
      cases h₂

/-! ## Hints of masked renderings -/

/-- `HintLe h σ`: the hint `h` is at most `σ` in the order `none < Nat < Int`. -/
def HintLe (h : Option Ty) (σ : Ty) : Prop :=
  h = none ∨ h = some σ ∨ (h = some .nat ∧ σ = .int)

theorem joinH_hintLe (h1 h2 : Option Ty) (σ : Ty) (hσ : σ.isNum = true)
    (a : HintLe h1 σ) (b : HintLe h2 σ) : HintLe (joinH h1 h2) σ := by
  unfold HintLe at *
  cases σ <;> rcases a with rfl | rfl | ⟨rfl, ha⟩ <;> rcases b with rfl | rfl | ⟨rfl, hb⟩ <;>
    simp_all [joinH, Ty.max, Ty.isNum]

theorem joinH_some_right (h : Option Ty) (σ : Ty) (hσ : σ.isNum = true) (a : HintLe h σ) :
    joinH h (some σ) = some σ := by
  unfold HintLe at a
  cases σ <;> rcases a with rfl | rfl | ⟨rfl, ha⟩ <;> simp_all [joinH, Ty.max, Ty.isNum]

theorem joinH_some_left (h : Option Ty) (σ : Ty) (hσ : σ.isNum = true) (a : HintLe h σ) :
    joinH (some σ) h = some σ := by
  unfold HintLe at a
  cases σ <;> rcases a with rfl | rfl | ⟨rfl, ha⟩ <;> simp_all [joinH, Ty.max, Ty.isNum]

/-- Replacing operand hints by `some σ` (each one either unchanged or raised to `σ`)
changes their join at most to `some σ`. -/
theorem joinH_raise (ha hb ha' hb' : Option Ty) (σ : Ty) (hσ : σ.isNum = true)
    (la : HintLe ha σ) (lb : HintLe hb σ)
    (ra : ha' = ha ∨ ha' = some σ) (rb : hb' = hb ∨ hb' = some σ) :
    joinH ha' hb' = joinH ha hb ∨ joinH ha' hb' = some σ := by
  rcases ra with rfl | rfl <;> rcases rb with rfl | rfl
  · exact .inl rfl
  · exact .inr (joinH_some_right _ _ hσ la)
  · exact .inr (joinH_some_left _ _ hσ lb)
  · exact .inr (joinH_some_left _ _ hσ (.inr (.inl rfl)))

theorem opType_some_of (cfg : ElabCfg) (h exp : Option Ty) (σ : Ty) (hσ : σ.isNum = true)
    (hl : HintLe h σ) (H : opType cfg h exp = σ) : opType cfg (some σ) exp = σ := by
  rcases cfg with ⟨d, rl⟩
  cases rl
  · rfl
  · simp only [opType] at H ⊢
    generalize numOnly exp = o at H ⊢
    unfold HintLe at hl
    cases σ <;> rcases hl with rfl | rfl | ⟨rfl, hl⟩ <;> rcases o with _ | ⟨_ | _ | _⟩ <;>
      simp_all [joinH, Ty.max, Ty.isNum]

theorem opType_raise (cfg : ElabCfg) (ha hb ha' hb' exp : Option Ty) (σ : Ty)
    (hσ : σ.isNum = true) (la : HintLe ha σ) (lb : HintLe hb σ)
    (ra : ha' = ha ∨ ha' = some σ) (rb : hb' = hb ∨ hb' = some σ)
    (H : opType cfg (joinH ha hb) exp = σ) : opType cfg (joinH ha' hb') exp = σ := by
  rcases joinH_raise ha hb ha' hb' σ hσ la lb ra rb with h | h
  · rw [h, H]
  · rw [h]; exact opType_some_of cfg _ exp σ hσ (joinH_hintLe _ _ _ hσ la lb) H

theorem eqType_raise (d : Ty) (ha hb ha' hb' : Option Ty) (σ : Ty)
    (hσ : σ.isNum = true) (la : HintLe ha σ) (lb : HintLe hb σ)
    (ra : ha' = ha ∨ ha' = some σ) (rb : hb' = hb ∨ hb' = some σ)
    (H : (joinH ha hb).getD d = σ) : (joinH ha' hb').getD d = σ := by
  rcases joinH_raise ha hb ha' hb' σ hσ la lb ra rb with h | h
  · rw [h, H]
  · rw [h]; rfl

/-- The hint of any rendering of a well-typed term is at most the term's type. -/
theorem hint_ppMask_le (S : Sig) (m : Mask) (x : Tm) :
    ∀ (p : Path) (σ : Ty), tyOf S x = some σ → HintLe (hint S (ppMask m p x)) σ := by
  induction x with
  | var y τ =>
    intro p σ h
    simp only [tyOf] at h; split at h <;> simp at h
    subst h; rename_i hv
    exact .inr (.inl (by simp [ppMask, hint, hv]))
  | lit τ n =>
    intro p σ h
    simp only [tyOf] at h; split at h <;> simp at h
    subst h
    simp only [ppMask]; split
    · exact .inr (.inl rfl)
    · exact .inl rfl
  | add τ a b iha ihb | sub τ a b iha ihb =>
    intro p σ h
    simp only [tyOf] at h; split at h <;> simp at h
    subst h; rename_i hh; obtain ⟨hn, ha, hb⟩ := hh
    simp only [ppMask]; split
    · exact .inr (.inl rfl)
    · exact joinH_hintLe _ _ _ hn (iha _ _ ha) (ihb _ _ hb)
  | eq τ a b _ _ =>
    intro p σ h
    simp only [tyOf] at h; split at h <;> simp at h
    subst h; exact .inr (.inl rfl)
  | iff a b _ _ | and a b _ _ =>
    intro p σ h
    simp only [tyOf] at h; split at h <;> simp at h
    subst h; exact .inr (.inl rfl)
  | coe a iha =>
    intro p σ h
    simp only [tyOf] at h; split at h <;> simp at h
    subst h; rename_i ha
    simp only [ppMask]; split
    · exact .inr (.inl rfl)
    · rcases iha (0 :: p) _ ha with h | h | ⟨_, h⟩
      · exact .inl h
      · exact .inr (.inr ⟨h, rfl⟩)
      · cases h
  | const c =>
    intro p σ h
    simp only [tyOf] at h
    exact .inr (.inl (by simp [ppMask, hint, h]))

/-- A text announcing no type cannot elaborate at expected `Int` to an inserted
coercion: unannotated numerals and operator trees take the expected type. -/
theorem elabE_int_not_coe_of_hint_none (cfg : ElabCfg) (S : Sig) (r : Stx) (X : Tm) (τ : Ty)
    (hh : hint S r = none) (h : elabE cfg S (some .int) r = some (.coe X, τ)) : False := by
  cases r with
  | var y =>
    simp only [hint] at hh
    simp [elabE, hh] at h
  | num n =>
    simp [elabE, numOnly, Ty.isNum, coerceTo] at h
  | add oτ a b | sub oτ a b =>
    cases oτ with
    | some _ => simp [hint] at hh
    | none =>
      simp only [hint] at hh
      have hop : opType cfg (joinH (hint S a) (hint S b)) (some .int) = .int := by
        rw [hh]; rcases cfg with ⟨d, rl⟩; cases rl <;> rfl
      simp only [elabE, Option.getD_none, hop] at h
      split at h
      · split at h
        · simp [coerceTo] at h
        · simp at h
      · simp at h
  | eq _ _ _ | iff _ _ | and _ _ | asc _ _ | coe _ => simp [hint] at hh
  | const c =>
    simp only [hint] at hh
    simp [elabE, hh] at h

theorem opType_int_nat (cfg : ElabCfg) (h : Option Ty) (H : opType cfg h (some .int) = .nat) :
    opType cfg h (some .nat) = .nat := by
  rcases cfg with ⟨d, rl⟩
  cases rl <;> rcases h with _ | ⟨_ | _ | _⟩ <;>
    simp_all [opType, numOnly, joinH, Ty.isNum, Ty.max]

/-- For a rendering of a `Nat`-typed term, an inserted coercion requires expected
type `Int`. -/
theorem elabE_natTm_coe_exp (cfg : ElabCfg) (S : Sig) (m : Mask) (p : Path) (a : Tm)
    (exp : Option Ty) (X : Tm) (τ : Ty) (hty : tyOf S a = some .nat)
    (h : elabE cfg S exp (ppMask m p a) = some (.coe X, τ)) : exp = some .int := by
  cases a with
  | var y σ =>
    simp only [ppMask, elabE] at h
    split at h
    · exact (coerceTo_eq_coe _ _ _ _ _ rfl h).1
    · simp at h
  | lit σ n =>
    simp only [tyOf] at hty; split at hty <;> simp at hty
    subst hty
    simp only [ppMask] at h
    split at h
    · simp [elabE, numOnly, Ty.isNum, coerceTo] at h
      exact (coerceTo_eq_coe _ _ _ _ _ rfl h).1
    · simp only [elabE] at h
      split at h
      · exact (coerceTo_eq_coe _ _ _ _ _ rfl h).1
      · simp at h
  | add σ x y | sub σ x y =>
    simp only [ppMask] at h
    generalize (if m p .typeArg = true then some σ else none) = oτ at h
    simp only [elabE] at h
    split at h
    · split at h
      · exact (coerceTo_eq_coe _ _ _ _ _ rfl h).1
      · simp at h
    · simp at h
  | const c =>
    simp only [ppMask, elabE] at h
    split at h
    · exact (coerceTo_eq_coe _ _ _ _ _ rfl h).1
    · simp at h
  | eq _ _ _ | iff _ _ | and _ _ | coe _ =>
    simp only [tyOf] at hty; split at hty <;> simp at hty

/-- Shifting the expected type from `Int` to `Nat` for a `Nat`-typed term whose
rendering was read with an inserted coercion. -/
theorem elabE_shift_int_nat (cfg : ElabCfg) (S : Sig) (m : Mask) (p : Path) (a : Tm)
    (hty : tyOf S a = some .nat)
    (h : elabE cfg S (some .int) (ppMask m p a) = some (.coe a, .int)) :
    elabE cfg S (some .nat) (ppMask m p a) = some (a, .nat) := by
  cases a with
  | var y σ =>
    simp only [tyOf] at hty; split at hty <;> simp at hty
    subst hty; rename_i hv
    simp [ppMask, elabE, hv, coerceTo]
  | lit σ n =>
    simp only [tyOf] at hty; split at hty <;> simp at hty
    subst hty
    simp only [ppMask] at h ⊢
    split
    · simp [elabE, numOnly, Ty.isNum, coerceTo]
    · rename_i hm
      simp [hm, elabE, numOnly, Ty.isNum, coerceTo] at h
  | add σ x y =>
    simp only [tyOf] at hty; split at hty <;> simp at hty
    subst hty
    have ho : (if m p .typeArg = true then some Ty.nat else none) = none ∨
        (if m p .typeArg = true then some Ty.nat else none) = some .nat := by
      split <;> simp
    simp only [ppMask] at h ⊢
    generalize (if m p .typeArg = true then some Ty.nat else none) = oτ at h ho ⊢
    simp only [elabE] at h ⊢
    split at h
    · rename_i hn
      split at h
      · rename_i x' σx y' σy hx hy
        obtain ⟨-, h2, h3, -⟩ := coerceTo_eq_coe _ _ _ _ _ rfl h
        simp only [Tm.add.injEq] at h2
        obtain ⟨hτ, rfl, rfl⟩ := h2
        have hτ' : oτ.getD
            (opType cfg (joinH (hint S (ppMask m (0 :: p) x)) (hint S (ppMask m (1 :: p) y)))
              (some .nat)) = .nat := by
          rcases ho with rfl | rfl
          · simp only [Option.getD_none] at hτ ⊢
            exact opType_int_nat _ _ hτ.symm
          · rfl
        rw [← hτ] at hx hy
        rw [hτ']
        simp [Ty.isNum, hx, hy, coerceTo]
      · simp at h
    · simp at h
  | sub σ x y =>
    simp only [tyOf] at hty; split at hty <;> simp at hty
    subst hty
    have ho : (if m p .typeArg = true then some Ty.nat else none) = none ∨
        (if m p .typeArg = true then some Ty.nat else none) = some .nat := by
      split <;> simp
    simp only [ppMask] at h ⊢
    generalize (if m p .typeArg = true then some Ty.nat else none) = oτ at h ho ⊢
    simp only [elabE] at h ⊢
    split at h
    · rename_i hn
      split at h
      · rename_i x' σx y' σy hx hy
        obtain ⟨-, h2, h3, -⟩ := coerceTo_eq_coe _ _ _ _ _ rfl h
        simp only [Tm.sub.injEq] at h2
        obtain ⟨hτ, rfl, rfl⟩ := h2
        have hτ' : oτ.getD
            (opType cfg (joinH (hint S (ppMask m (0 :: p) x)) (hint S (ppMask m (1 :: p) y)))
              (some .nat)) = .nat := by
          rcases ho with rfl | rfl
          · simp only [Option.getD_none] at hτ ⊢
            exact opType_int_nat _ _ hτ.symm
          · rfl
        rw [← hτ] at hx hy
        rw [hτ']
        simp [Ty.isNum, hx, hy, coerceTo]
      · simp at h
    · simp at h
  | const c =>
    simp only [tyOf] at hty
    simp [ppMask, elabE, hty, coerceTo]
  | eq _ _ _ | iff _ _ | and _ _ | coe _ =>
    simp only [tyOf] at hty; split at hty <;> simp at hty

theorem elabE_add_inv (cfg : ElabCfg) (S : Sig) (exp oτ : Option Ty) (A B : Stx) (τ : Ty)
    (a b : Tm) (r : Tm × Ty) (h : elabE cfg S exp (.add oτ A B) = some r)
    (hc : coerceTo exp (.add τ a b, τ) = some r) :
    oτ.getD (opType cfg (joinH (hint S A) (hint S B)) exp) = τ ∧
      elabE cfg S (some τ) A = some (a, τ) ∧ elabE cfg S (some τ) B = some (b, τ) := by
  simp only [elabE] at h
  split at h
  · split at h
    · rename_i a' σa b' σb ha hb
      obtain ⟨h1, h2⟩ := coerceTo_inj _ _ _ _ _ _ rfl rfl h hc
      simp only [Tm.add.injEq] at h1
      obtain ⟨hτ, rfl, rfl⟩ := h1
      have hσa := elabE_some_exp_ty _ _ _ _ _ _ ha
      have hσb := elabE_some_exp_ty _ _ _ _ _ _ hb
      subst hσa hσb
      rw [hτ] at ha hb
      exact ⟨hτ, ha, hb⟩
    · simp at h
  · simp at h

theorem elabE_add_build (cfg : ElabCfg) (S : Sig) (exp oτ : Option Ty) (A B : Stx) (τ : Ty)
    (a b : Tm) (hτ : oτ.getD (opType cfg (joinH (hint S A) (hint S B)) exp) = τ)
    (hn : τ.isNum = true) (ha : elabE cfg S (some τ) A = some (a, τ))
    (hb : elabE cfg S (some τ) B = some (b, τ)) :
    elabE cfg S exp (.add oτ A B) = coerceTo exp (.add τ a b, τ) := by
  simp only [elabE, hτ, hn, ↓reduceIte, ha, hb]

theorem elabE_sub_inv (cfg : ElabCfg) (S : Sig) (exp oτ : Option Ty) (A B : Stx) (τ : Ty)
    (a b : Tm) (r : Tm × Ty) (h : elabE cfg S exp (.sub oτ A B) = some r)
    (hc : coerceTo exp (.sub τ a b, τ) = some r) :
    oτ.getD (opType cfg (joinH (hint S A) (hint S B)) exp) = τ ∧
      elabE cfg S (some τ) A = some (a, τ) ∧ elabE cfg S (some τ) B = some (b, τ) := by
  simp only [elabE] at h
  split at h
  · split at h
    · rename_i a' σa b' σb ha hb
      obtain ⟨h1, h2⟩ := coerceTo_inj _ _ _ _ _ _ rfl rfl h hc
      simp only [Tm.sub.injEq] at h1
      obtain ⟨hτ, rfl, rfl⟩ := h1
      have hσa := elabE_some_exp_ty _ _ _ _ _ _ ha
      have hσb := elabE_some_exp_ty _ _ _ _ _ _ hb
      subst hσa hσb
      rw [hτ] at ha hb
      exact ⟨hτ, ha, hb⟩
    · simp at h
  · simp at h

theorem elabE_sub_build (cfg : ElabCfg) (S : Sig) (exp oτ : Option Ty) (A B : Stx) (τ : Ty)
    (a b : Tm) (hτ : oτ.getD (opType cfg (joinH (hint S A) (hint S B)) exp) = τ)
    (hn : τ.isNum = true) (ha : elabE cfg S (some τ) A = some (a, τ))
    (hb : elabE cfg S (some τ) B = some (b, τ)) :
    elabE cfg S exp (.sub oτ A B) = coerceTo exp (.sub τ a b, τ) := by
  simp only [elabE, hτ, hn, ↓reduceIte, ha, hb]

theorem elabE_eq_inv (cfg : ElabCfg) (S : Sig) (exp oτ : Option Ty) (A B : Stx) (τ : Ty)
    (a b : Tm) (r : Tm × Ty) (h : elabE cfg S exp (.eq oτ A B) = some r)
    (hc : coerceTo exp (.eq τ a b, .prop) = some r) :
    oτ.getD ((joinH (hint S A) (hint S B)).getD cfg.numDefault) = τ ∧
      elabE cfg S (some τ) A = some (a, τ) ∧ elabE cfg S (some τ) B = some (b, τ) := by
  simp only [elabE] at h
  split at h
  · split at h
    · rename_i a' σa b' σb ha hb
      obtain ⟨h1, -⟩ := coerceTo_inj _ _ _ _ _ _ rfl rfl h hc
      simp only [Tm.eq.injEq] at h1
      obtain ⟨hτ, rfl, rfl⟩ := h1
      have hσa := elabE_some_exp_ty _ _ _ _ _ _ ha
      have hσb := elabE_some_exp_ty _ _ _ _ _ _ hb
      subst hσa hσb
      rw [hτ] at ha hb
      exact ⟨hτ, ha, hb⟩
    · simp at h
  · simp at h

theorem elabE_eq_build (cfg : ElabCfg) (S : Sig) (exp oτ : Option Ty) (A B : Stx) (τ : Ty)
    (a b : Tm) (hτ : oτ.getD ((joinH (hint S A) (hint S B)).getD cfg.numDefault) = τ)
    (hn : τ.isNum = true) (ha : elabE cfg S (some τ) A = some (a, τ))
    (hb : elabE cfg S (some τ) B = some (b, τ)) :
    elabE cfg S exp (.eq oτ A B) = coerceTo exp (.eq τ a b, .prop) := by
  simp only [elabE, hτ, hn, ↓reduceIte, ha, hb]

theorem elabE_iff_inv (cfg : ElabCfg) (S : Sig) (exp : Option Ty) (A B : Stx)
    (a b : Tm) (r : Tm × Ty) (h : elabE cfg S exp (.iff A B) = some r)
    (hc : coerceTo exp (.iff a b, .prop) = some r) :
    elabE cfg S (some .prop) A = some (a, .prop) ∧ elabE cfg S (some .prop) B = some (b, .prop) := by
  simp only [elabE] at h
  split at h
  · rename_i a' σa b' σb ha hb
    obtain ⟨h1, -⟩ := coerceTo_inj _ _ _ _ _ _ rfl rfl h hc
    simp only [Tm.iff.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    have hσa := elabE_some_exp_ty _ _ _ _ _ _ ha
    have hσb := elabE_some_exp_ty _ _ _ _ _ _ hb
    subst hσa hσb
    exact ⟨ha, hb⟩
  · simp at h

theorem elabE_and_inv (cfg : ElabCfg) (S : Sig) (exp : Option Ty) (A B : Stx)
    (a b : Tm) (r : Tm × Ty) (h : elabE cfg S exp (.and A B) = some r)
    (hc : coerceTo exp (.and a b, .prop) = some r) :
    elabE cfg S (some .prop) A = some (a, .prop) ∧ elabE cfg S (some .prop) B = some (b, .prop) := by
  simp only [elabE] at h
  split at h
  · rename_i a' σa b' σb ha hb
    obtain ⟨h1, -⟩ := coerceTo_inj _ _ _ _ _ _ rfl rfl h hc
    simp only [Tm.and.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    have hσa := elabE_some_exp_ty _ _ _ _ _ _ ha
    have hσb := elabE_some_exp_ty _ _ _ _ _ _ hb
    subst hσa hσb
    exact ⟨ha, hb⟩
  · simp at h

/-! ## Monotonicity of correct annotation -/

/-- The induction behind `faithful_ppMask_mono`: if the rendering of a well-typed `x`
under `m` elaborates (at `exp`) to the repair of `x`, so does its rendering under
any larger mask `m'`, and the announced hint is unchanged or raised to the type of
`x`. -/
theorem ppMask_mono_aux (cfg : ElabCfg) (S : Sig) (m m' : Mask)
    (hle : ∀ p k, m p k = true → m' p k = true) (x : Tm) :
    ∀ (p : Path) (exp : Option Ty) (σ : Ty) (r : Tm × Ty), tyOf S x = some σ →
      coerceTo exp (x, σ) = some r → elabE cfg S exp (ppMask m p x) = some r →
      elabE cfg S exp (ppMask m' p x) = some r ∧
        (hint S (ppMask m' p x) = hint S (ppMask m p x) ∨ hint S (ppMask m' p x) = some σ) := by
  induction x with
  | var y τ =>
    intro p exp σ r _ _ h
    exact ⟨by simpa only [ppMask] using h, .inl rfl⟩
  | const c =>
    intro p exp σ r _ _ h
    exact ⟨by simpa only [ppMask] using h, .inl rfl⟩
  | lit τ n =>
    intro p exp σ r hty hc h
    simp only [tyOf] at hty; split at hty <;> simp at hty
    subst hty; rename_i hn
    by_cases hm : m p .numType = true
    · have hm' := hle _ _ hm
      exact ⟨by simpa [ppMask, hm, hm'] using h, .inl (by simp [ppMask, hm, hm'])⟩
    · have h0 : elabE cfg S exp (.num n) = some r := by simpa [ppMask, hm] using h
      by_cases hm' : m' p .numType = true
      · simp only [elabE] at h0
        split at h0
        · have hinner : elabE cfg S (some τ) (.num n) = some (.lit τ n, τ) := by
            simp [elabE, numOnly, hn, coerceTo]
          refine ⟨?_, .inr (by simp [ppMask, hm', hint])⟩
          simp only [ppMask, hm', ↓reduceIte]
          rw [elabE, hinner]
          exact hc
        · simp at h0
      · exact ⟨by simpa [ppMask, hm'] using h0, .inl (by simp [ppMask, hm, hm'])⟩
  | add τ a b iha ihb =>
    intro p exp σ r hty hc h
    simp only [tyOf] at hty; split at hty <;> simp at hty
    subst hty; rename_i hh; obtain ⟨hn, hta, htb⟩ := hh
    have la := hint_ppMask_le S m a (0 :: p) τ hta
    have lb := hint_ppMask_le S m b (1 :: p) τ htb
    simp only [ppMask] at h ⊢
    obtain ⟨hτ, ha, hb⟩ := elabE_add_inv _ _ _ _ _ _ _ _ _ _ h hc
    obtain ⟨ha', hra⟩ := iha (0 :: p) (some τ) τ (a, τ) hta (coerceTo_self _ _ _ (.inr rfl)) ha
    obtain ⟨hb', hrb⟩ := ihb (1 :: p) (some τ) τ (b, τ) htb (coerceTo_self _ _ _ (.inr rfl)) hb
    by_cases hm' : m' p .typeArg = true
    · refine ⟨?_, .inr (by simp [hint, hm'])⟩
      rw [elabE_add_build _ _ _ _ _ _ _ _ _ (by simp [hm']) hn ha' hb']
      exact hc
    · have hm : m p .typeArg = false := by
        cases hmv : m p .typeArg
        · rfl
        · exact absurd (hle _ _ hmv) hm'
      simp only [hm, hm', Bool.false_eq_true, ↓reduceIte, Option.getD_none] at hτ ⊢
      refine ⟨?_, ?_⟩
      · rw [elabE_add_build _ _ _ _ _ _ _ _ _
          (by simpa using opType_raise cfg _ _ _ _ exp τ hn la lb hra hrb hτ) hn ha' hb']
        exact hc
      · simp only [hint]
        exact joinH_raise _ _ _ _ τ hn la lb hra hrb
  | sub τ a b iha ihb =>
    intro p exp σ r hty hc h
    simp only [tyOf] at hty; split at hty <;> simp at hty
    subst hty; rename_i hh; obtain ⟨hn, hta, htb⟩ := hh
    have la := hint_ppMask_le S m a (0 :: p) τ hta
    have lb := hint_ppMask_le S m b (1 :: p) τ htb
    simp only [ppMask] at h ⊢
    obtain ⟨hτ, ha, hb⟩ := elabE_sub_inv _ _ _ _ _ _ _ _ _ _ h hc
    obtain ⟨ha', hra⟩ := iha (0 :: p) (some τ) τ (a, τ) hta (coerceTo_self _ _ _ (.inr rfl)) ha
    obtain ⟨hb', hrb⟩ := ihb (1 :: p) (some τ) τ (b, τ) htb (coerceTo_self _ _ _ (.inr rfl)) hb
    by_cases hm' : m' p .typeArg = true
    · refine ⟨?_, .inr (by simp [hint, hm'])⟩
      rw [elabE_sub_build _ _ _ _ _ _ _ _ _ (by simp [hm']) hn ha' hb']
      exact hc
    · have hm : m p .typeArg = false := by
        cases hmv : m p .typeArg
        · rfl
        · exact absurd (hle _ _ hmv) hm'
      simp only [hm, hm', Bool.false_eq_true, ↓reduceIte, Option.getD_none] at hτ ⊢
      refine ⟨?_, ?_⟩
      · rw [elabE_sub_build _ _ _ _ _ _ _ _ _
          (by simpa using opType_raise cfg _ _ _ _ exp τ hn la lb hra hrb hτ) hn ha' hb']
        exact hc
      · simp only [hint]
        exact joinH_raise _ _ _ _ τ hn la lb hra hrb
  | eq τ a b iha ihb =>
    intro p exp σ r hty hc h
    simp only [tyOf] at hty; split at hty <;> simp at hty
    subst hty; rename_i hh; obtain ⟨hn, hta, htb⟩ := hh
    have la := hint_ppMask_le S m a (0 :: p) τ hta
    have lb := hint_ppMask_le S m b (1 :: p) τ htb
    simp only [ppMask] at h ⊢
    obtain ⟨hτ, ha, hb⟩ := elabE_eq_inv _ _ _ _ _ _ _ _ _ _ h hc
    obtain ⟨ha', hra⟩ := iha (0 :: p) (some τ) τ (a, τ) hta (coerceTo_self _ _ _ (.inr rfl)) ha
    obtain ⟨hb', hrb⟩ := ihb (1 :: p) (some τ) τ (b, τ) htb (coerceTo_self _ _ _ (.inr rfl)) hb
    refine ⟨?_, .inl rfl⟩
    by_cases hm' : m' p .typeArg = true
    · rw [elabE_eq_build _ _ _ _ _ _ _ _ _ (by simp [hm']) hn ha' hb']
      exact hc
    · have hm : m p .typeArg = false := by
        cases hmv : m p .typeArg
        · rfl
        · exact absurd (hle _ _ hmv) hm'
      simp only [hm, hm', Bool.false_eq_true, ↓reduceIte, Option.getD_none] at hτ ⊢
      rw [elabE_eq_build _ _ _ _ _ _ _ _ _
        (by simpa using eqType_raise _ _ _ _ _ τ hn la lb hra hrb hτ) hn ha' hb']
      exact hc
  | iff a b iha ihb =>
    intro p exp σ r hty hc h
    simp only [tyOf] at hty; split at hty <;> simp at hty
    subst hty; rename_i hh; obtain ⟨hta, htb⟩ := hh
    simp only [ppMask] at h ⊢
    obtain ⟨ha, hb⟩ := elabE_iff_inv _ _ _ _ _ _ _ _ h hc
    obtain ⟨ha', -⟩ := iha (0 :: p) (some .prop) .prop _ hta (coerceTo_self _ _ _ (.inr rfl)) ha
    obtain ⟨hb', -⟩ := ihb (1 :: p) (some .prop) .prop _ htb (coerceTo_self _ _ _ (.inr rfl)) hb
    refine ⟨?_, .inl rfl⟩
    simp only [elabE, ha', hb']
    exact hc
  | and a b iha ihb =>
    intro p exp σ r hty hc h
    simp only [tyOf] at hty; split at hty <;> simp at hty
    subst hty; rename_i hh; obtain ⟨hta, htb⟩ := hh
    simp only [ppMask] at h ⊢
    obtain ⟨ha, hb⟩ := elabE_and_inv _ _ _ _ _ _ _ _ h hc
    obtain ⟨ha', -⟩ := iha (0 :: p) (some .prop) .prop _ hta (coerceTo_self _ _ _ (.inr rfl)) ha
    obtain ⟨hb', -⟩ := ihb (1 :: p) (some .prop) .prop _ htb (coerceTo_self _ _ _ (.inr rfl)) hb
    refine ⟨?_, .inl rfl⟩
    simp only [elabE, ha', hb']
    exact hc
  | coe a iha =>
    intro p exp σ r hty hc h
    simp only [tyOf] at hty; split at hty <;> simp at hty
    subst hty; rename_i hta
    simp only [ppMask] at h ⊢
    by_cases hm : m p .coercion = true
    · have hm' := hle _ _ hm
      simp only [hm, hm', ↓reduceIte] at h ⊢
      simp only [elabE] at h
      split at h
      · rename_i e' σe he
        have he' := coerceTo_inj_sameTy _ _ _ _ _ h hc
        simp only [Tm.coe.injEq] at he'
        subst he'
        have hσe := elabE_some_exp_ty _ _ _ _ _ _ he
        subst hσe
        obtain ⟨he2, -⟩ := iha (0 :: p) (some .nat) .nat _ hta (coerceTo_self _ _ _ (.inr rfl)) he
        refine ⟨?_, .inl rfl⟩
        simp only [elabE, he2]
        exact hc
      · simp at h
    · simp only [hm, Bool.false_eq_true, ↓reduceIte] at h ⊢
      -- the expected type must be `Int`, and `r` is the coercion of `a`
      have hexp : exp = some .int := by
        cases exp with
        | none =>
          simp only [coerceTo] at hc
          obtain rfl := Option.some.inj hc
          exact absurd (elabE_natTm_coe_exp cfg S m _ a none a .int hta h) (by simp)
        | some ε =>
          simp only [coerceTo] at hc
          split at hc
          · rename_i hε; rw [hε]
          · split at hc
            · rename_i hh; simp at hh
            · simp at hc
      subst hexp
      have hr : r = (.coe a, .int) := by
        simp [coerceTo] at hc; exact hc.symm
      subst hr
      by_cases hm' : m' p .coercion = true
      · simp only [hm', ↓reduceIte]
        have hs := elabE_shift_int_nat cfg S m _ a hta h
        obtain ⟨hs2, -⟩ := iha (0 :: p) (some .nat) .nat _ hta (coerceTo_self _ _ _ (.inr rfl)) hs
        refine ⟨?_, .inr rfl⟩
        simp [elabE, hs2, coerceTo]
      · simp only [hm', Bool.false_eq_true, ↓reduceIte]
        obtain ⟨h2, hr2⟩ := iha (0 :: p) (some .int) .nat _ hta (by simp [coerceTo]) h
        refine ⟨h2, .inl ?_⟩
        rcases hr2 with e | e
        · exact e
        · rw [e]
          rcases hint_ppMask_le S m a (0 :: p) .nat hta with e0 | e0 | ⟨_, e0⟩
          · exact absurd h (fun h' => elabE_int_not_coe_of_hint_none cfg S _ a .int e0 h')
          · exact e0.symm
          · cases e0

theorem faithful_ppMask_mono_aux (cfg : ElabCfg) (S : Sig) (t : Tm) (m m' : Mask)
    (hle : ∀ p k, m p k = true → m' p k = true)
    (hf : elabWith cfg S (ppMask m [] t) = some t) : elabWith cfg S (ppMask m' [] t) = some t := by
  simp only [elabWith, Option.map_eq_some_iff] at hf ⊢
  obtain ⟨⟨u, τ⟩, he, hu⟩ := hf
  simp only at hu
  subst hu
  have hty := (elabE_sound_aux cfg S none _ _ _ he).2
  obtain ⟨he', -⟩ := ppMask_mono_aux cfg S m m' hle u [] none τ (u, τ) hty rfl he
  exact ⟨(u, τ), he', rfl⟩

/-! ## The deletion-greedy printer -/

theorem ppMask_congr (m m' : Mask) (t : Tm) :
    ∀ p, (∀ q ∈ annPos p t, m q.1 q.2 = m' q.1 q.2) → ppMask m p t = ppMask m' p t := by
  induction t with
  | var _ _ | const _ => intro p _; rfl
  | lit τ n =>
    intro p h
    have := h (p, .numType) (by simp [annPos])
    simp only [ppMask, this]
  | add τ a b iha ihb | sub τ a b iha ihb | eq τ a b iha ihb =>
    intro p h
    have h0 := h (p, .typeArg) (by simp [annPos])
    have ha := iha (0 :: p) (fun q hq => h q (by simp [annPos, hq]))
    have hb := ihb (1 :: p) (fun q hq => h q (by simp [annPos, hq]))
    simp only [ppMask, h0, ha, hb]
  | iff a b iha ihb | and a b iha ihb =>
    intro p h
    have ha := iha (0 :: p) (fun q hq => h q (by simp [annPos, hq]))
    have hb := ihb (1 :: p) (fun q hq => h q (by simp [annPos, hq]))
    simp only [ppMask, ha, hb]
  | coe a iha =>
    intro p h
    have h0 := h (p, .coercion) (by simp [annPos])
    have ha := iha (0 :: p) (fun q hq => h q (by simp [annPos, hq]))
    simp only [ppMask, h0, ha]

theorem ppMask_maskOf_annPos (t : Tm) :
    ppMask (maskOf (annPos [] t)) [] t = ppExplicit t :=
  ppMask_congr _ _ t [] (fun q hq => by simp [maskOf, hq])

theorem maskOf_nil : maskOf [] = fun _ _ => false := by
  funext p k; simp [maskOf]

/-- The step function of `minMask`. -/
def greedyStep (cfg : ElabCfg) (S : Sig) (t : Tm) (M : List (Path × AnnKind))
    (q : Path × AnnKind) : List (Path × AnnKind) :=
  if faithfulB cfg S (ppMask (maskOf (M.erase q)) [] t) t then M.erase q else M

theorem minMask_eq_foldl (cfg : ElabCfg) (S : Sig) (t : Tm) :
    minMask cfg S t = (annPos [] t).foldl (greedyStep cfg S t) (annPos [] t) := rfl

theorem faithfulB_iff (cfg : ElabCfg) (S : Sig) (r : Stx) (t : Tm) :
    faithfulB cfg S r t = true ↔ Faithful cfg S r t := by
  simp [faithfulB, Faithful]

theorem foldl_greedy_faithful (cfg : ElabCfg) (S : Sig) (t : Tm) :
    ∀ (L M : List (Path × AnnKind)), Faithful cfg S (ppMask (maskOf M) [] t) t →
      Faithful cfg S (ppMask (maskOf (L.foldl (greedyStep cfg S t) M)) [] t) t := by
  intro L
  induction L with
  | nil => intro M h; exact h
  | cons q L ih =>
    intro M h
    simp only [List.foldl]
    apply ih
    unfold greedyStep
    split
    · rename_i hb; exact (faithfulB_iff _ _ _ _).mp hb
    · exact h

theorem foldl_greedy_sublist (cfg : ElabCfg) (S : Sig) (t : Tm) :
    ∀ (L M : List (Path × AnnKind)), (L.foldl (greedyStep cfg S t) M).Sublist M := by
  intro L
  induction L with
  | nil => intro M; exact List.Sublist.refl M
  | cons q L ih =>
    intro M
    simp only [List.foldl]
    refine (ih _).trans ?_
    unfold greedyStep
    split
    · exact List.erase_sublist
    · exact List.Sublist.refl M

theorem foldl_erase_append (L M : List (Path × AnnKind)) :
    L.foldl (fun M q => M.erase q) (L ++ M) = M := by
  induction L with
  | nil => rfl
  | cons q L ih => simp [List.foldl, List.erase_cons_head, ih]

theorem foldl_greedy_all (cfg : ElabCfg) (S : Sig) (t : Tm)
    (hall : ∀ M : List (Path × AnnKind), Faithful cfg S (ppMask (maskOf M) [] t) t) :
    ∀ (L M : List (Path × AnnKind)),
      L.foldl (greedyStep cfg S t) M = L.foldl (fun M q => M.erase q) M := by
  intro L
  induction L with
  | nil => intro M; rfl
  | cons q L ih =>
    intro M
    simp only [List.foldl]
    rw [ih]
    unfold greedyStep
    simp only [(faithfulB_iff _ _ _ _).mpr (hall _), ↓reduceIte]

/-! ### Annotation positions are distinct -/

theorem annPos_suffix (t : Tm) : ∀ p, ∀ q ∈ annPos p t, ∃ r, q.1 = r ++ p := by
  induction t with
  | var _ _ | const _ => intro p q hq; simp [annPos] at hq
  | lit _ _ =>
    intro p q hq; simp only [annPos, List.mem_singleton] at hq; subst hq; exact ⟨[], rfl⟩
  | add _ a b iha ihb | sub _ a b iha ihb | eq _ a b iha ihb =>
    intro p q hq
    simp only [annPos, List.mem_cons, List.mem_append] at hq
    rcases hq with rfl | hq | hq
    · exact ⟨[], rfl⟩
    · obtain ⟨r, hr⟩ := iha _ q hq; exact ⟨r ++ [0], by simp [hr]⟩
    · obtain ⟨r, hr⟩ := ihb _ q hq; exact ⟨r ++ [1], by simp [hr]⟩
  | iff a b iha ihb | and a b iha ihb =>
    intro p q hq
    simp only [annPos, List.mem_append] at hq
    rcases hq with hq | hq
    · obtain ⟨r, hr⟩ := iha _ q hq; exact ⟨r ++ [0], by simp [hr]⟩
    · obtain ⟨r, hr⟩ := ihb _ q hq; exact ⟨r ++ [1], by simp [hr]⟩
  | coe a iha =>
    intro p q hq
    simp only [annPos, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact ⟨[], rfl⟩
    · obtain ⟨r, hr⟩ := iha _ q hq; exact ⟨r ++ [0], by simp [hr]⟩

theorem append_cons_inj (r r' p : Path) (i j : Nat) (h : r ++ i :: p = r' ++ j :: p) :
    i = j := by
  have hl : r.length = r'.length := by
    have := congrArg List.length h
    simp only [List.length_append, List.length_cons] at this
    omega
  have := (List.append_inj h hl).2
  simp only [List.cons.injEq] at this
  exact this.1

theorem annPos_not_self (t : Tm) (p : Path) (i : Nat) (k : AnnKind) :
    (p, k) ∉ annPos (i :: p) t := by
  intro h
  obtain ⟨r, hr⟩ := annPos_suffix t (i :: p) _ h
  have := congrArg List.length hr
  simp only [List.length_append, List.length_cons] at this
  omega

theorem annPos_disjoint (a b : Tm) (p : Path) :
    ∀ q, q ∈ annPos (0 :: p) a → q ∉ annPos (1 :: p) b := by
  intro q ha hb
  obtain ⟨r, hr⟩ := annPos_suffix a _ q ha
  obtain ⟨r', hr'⟩ := annPos_suffix b _ q hb
  have := append_cons_inj r r' p 0 1 (hr.symm.trans hr')
  omega

theorem annPos_nodup (t : Tm) : ∀ p, (annPos p t).Nodup := by
  induction t with
  | var _ _ | const _ => intro p; simp [annPos]
  | lit _ _ => intro p; simp [annPos]
  | add _ a b iha ihb | sub _ a b iha ihb | eq _ a b iha ihb =>
    intro p
    simp only [annPos, List.nodup_cons, List.mem_append, not_or, List.nodup_append]
    refine ⟨⟨annPos_not_self a p 0 _, annPos_not_self b p 1 _⟩, iha _, ihb _, ?_⟩
    intro x hx y hy hxy
    subst hxy
    exact annPos_disjoint a b p x hx hy
  | iff a b iha ihb | and a b iha ihb =>
    intro p
    simp only [annPos, List.nodup_append]
    refine ⟨iha _, ihb _, ?_⟩
    intro x hx y hy hxy
    subst hxy
    exact annPos_disjoint a b p x hx hy
  | coe a iha =>
    intro p
    simp only [annPos, List.nodup_cons]
    exact ⟨annPos_not_self a p 0 _, iha _⟩

/-! ### Local minimality -/

theorem maskOf_mono (A B : List (Path × AnnKind)) (h : ∀ x, x ∈ A → x ∈ B) :
    ∀ p k, maskOf A p k = true → maskOf B p k = true := by
  intro p k hk
  simp only [maskOf, decide_eq_true_eq] at hk ⊢
  exact h _ hk

/-- The invariant of the deletion-greedy fold: every visited position that is still
kept cannot be dropped without losing faithfulness. -/
theorem foldl_greedy_kept (cfg : ElabCfg) (S : Sig) (t : Tm) :
    ∀ (L M : List (Path × AnnKind)) (V : List (Path × AnnKind)), M.Nodup →
      (∀ q ∈ V, q ∈ M → ¬ Faithful cfg S (ppMask (maskOf (M.erase q)) [] t) t) →
      ∀ q ∈ V ++ L, q ∈ L.foldl (greedyStep cfg S t) M →
        ¬ Faithful cfg S (ppMask (maskOf ((L.foldl (greedyStep cfg S t) M).erase q)) [] t) t := by
  intro L
  induction L with
  | nil =>
    intro M V _ hV q hq hqM
    simp only [List.append_nil] at hq
    exact hV q hq hqM
  | cons q₀ L ih =>
    intro M V hnd hV q hq hqM
    simp only [List.foldl] at hqM ⊢
    have hsub : (greedyStep cfg S t M q₀).Sublist M := by
      unfold greedyStep; split
      · exact List.erase_sublist
      · exact List.Sublist.refl M
    have hnd' : (greedyStep cfg S t M q₀).Nodup := hnd.sublist hsub
    refine ih (greedyStep cfg S t M q₀) (V ++ [q₀]) hnd' ?_ q (by simpa using hq) hqM
    intro q' hq' hq'M hf
    -- erasing from the smaller list gives a sub-mask of erasing from `M`
    have hle : ∀ x, x ∈ (greedyStep cfg S t M q₀).erase q' → x ∈ M.erase q' := by
      intro x hx
      rw [hnd'.mem_erase_iff] at hx
      rw [hnd.mem_erase_iff]
      exact ⟨hx.1, hsub.subset hx.2⟩
    simp only [List.mem_append, List.mem_singleton] at hq'
    rcases hq' with hq' | rfl
    · exact hV q' hq' (hsub.subset hq'M)
        (faithful_ppMask_mono_aux cfg S t _ _ (maskOf_mono _ _ hle) hf)
    · unfold greedyStep at hq'M hf
      split at hq'M
      · rename_i hb
        rw [hnd.mem_erase_iff] at hq'M
        exact hq'M.1 rfl
      · rename_i hb
        simp only [hb] at hf
        exact hb ((faithfulB_iff _ _ _ _).mpr hf)

/-! ## Syntax classes -/

theorem subAnnotated_of_subFree (s : Stx) (hs : s.subFree = true) : s.subAnnotated = true := by
  induction s with
  | var _ | num _ | const _ => rfl
  | sub _ _ _ _ _ => simp [Stx.subFree] at hs
  | add _ a b iha ihb | eq _ a b iha ihb | iff a b iha ihb | and a b iha ihb =>
    simp only [Stx.subFree, Bool.and_eq_true] at hs
    simp [Stx.subAnnotated, iha hs.1, ihb hs.2]
  | asc e _ ihe | coe e ihe =>
    simp only [Stx.subFree] at hs
    simp [Stx.subAnnotated, ihe hs]

theorem subAnnotated_of_fullyAnnotated (s : Stx) (hs : s.fullyAnnotated = true) :
    s.subAnnotated = true := by
  induction s with
  | var _ | num _ | const _ => rfl
  | add _ a b iha ihb | eq _ a b iha ihb =>
    simp only [Stx.fullyAnnotated, Bool.and_eq_true] at hs
    simp [Stx.subAnnotated, iha hs.1.2, ihb hs.2]
  | sub oτ a b iha ihb =>
    simp only [Stx.fullyAnnotated, Bool.and_eq_true] at hs
    simp [Stx.subAnnotated, hs.1.1, iha hs.1.2, ihb hs.2]
  | iff a b iha ihb | and a b iha ihb =>
    simp only [Stx.fullyAnnotated, Bool.and_eq_true] at hs
    simp [Stx.subAnnotated, iha hs.1, ihb hs.2]
  | coe e ihe =>
    simp only [Stx.fullyAnnotated] at hs
    simp [Stx.subAnnotated, ihe hs]
  | asc e _ ihe =>
    by_cases hn : ∃ n, e = .num n
    · obtain ⟨n, rfl⟩ := hn; rfl
    · have he : e.fullyAnnotated = true := by
        cases e <;> simp_all [Stx.fullyAnnotated]
      simp [Stx.subAnnotated, ihe he]

end Toy.Render
