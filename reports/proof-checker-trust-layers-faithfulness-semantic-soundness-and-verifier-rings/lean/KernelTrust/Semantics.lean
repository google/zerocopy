/-
  Toy.KernelTrust.Semantics

  Reference semantics (classical truth tables) and semantic soundness of a rule
  table, `SemSound R`.  The reference semantics is the *trust root* of the
  semantic layer: everything "semantic" in this package is relative to
  `evalForm`.
-/
import KernelTrust.Logic

namespace Toy.KernelTrust

/-- A valuation assigns a truth value to every propositional variable. -/
abbrev Valuation := Nat → Bool

/-- The reference semantics: classical two-valued truth-table evaluation. -/
def evalForm (v : Valuation) : Form → Bool
  | .var i    => v i
  | .bot      => false
  | .imp a b  => (!evalForm v a) || evalForm v b
  | .conj a b => evalForm v a && evalForm v b
  | .disj a b => evalForm v a || evalForm v b

/-- All formulas of a context are true under `v`. -/
def evalCtx (v : Valuation) : Ctx → Bool
  | []      => true
  | ψ :: Γ  => evalForm v ψ && evalCtx v Γ

/-- Semantic validity of a sequent: every valuation that satisfies `Γ`
satisfies `φ`. -/
def SemValid (Γ : Ctx) (φ : Form) : Prop :=
  ∀ v : Valuation, evalCtx v Γ = true → evalForm v φ = true

/-- Semantic soundness of a rule table: every sequent derivable from `R` is
semantically valid.  This is a property of the *rules*, independent of any
checker. -/
def SemSound (R : RuleSet) : Prop :=
  ∀ Γ φ, Derivable R Γ φ → SemValid Γ φ

/-- Syntactic consistency of a rule table: `⊥` is not derivable from no
hypotheses. -/
def Consistent (R : RuleSet) : Prop := ¬ Derivable R [] .bot

theorem evalCtx_mem {v : Valuation} {Γ : Ctx} {φ : Form}
    (hctx : evalCtx v Γ = true) (hmem : φ ∈ Γ) : evalForm v φ = true := by
  induction Γ with
  | nil => cases hmem
  | cons ψ rest ih =>
    simp only [evalCtx, Bool.and_eq_true] at hctx
    cases List.mem_cons.mp hmem with
    | inl heq => subst heq; exact hctx.1
    | inr htl => exact ih hctx.2 htl

/-- `⊥` is never semantically valid from no hypotheses. -/
theorem not_semValid_nil_bot : ¬ SemValid [] .bot := by
  intro h
  have hv := h (fun _ => false) rfl
  simp [evalForm] at hv

/-- A semantically sound rule table is consistent. -/
theorem SemSound.consistent {R : RuleSet} (h : SemSound R) : Consistent R :=
  fun hd => not_semValid_nil_bot (h [] .bot hd)

/-- **The standard rules are semantically sound** for the truth-table
semantics (textbook soundness of natural deduction, by induction on
derivations). -/
theorem stdRules_semSound : SemSound stdRules := by
  intro Γ φ hderiv
  induction hderiv with
  | hyp hmem =>
    intro v hctx
    exact evalCtx_mem hctx hmem
  | @step Γ r σ hr _ ih =>
    intro v hctx
    simp only [stdRules, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · -- impIntro
      simp only [instPat, evalForm, Bool.or_eq_true, Bool.not_eq_true']
      cases hv0 : evalForm v (substLookup σ 0)
      · left; rfl
      · right
        have hprem := ih { addedHyps := [.pvar 0], goal := .pvar 1 } (by simp) v
          (by simp [instPat, evalCtx, hv0, hctx])
        simpa [instPat] using hprem
    · -- impElim
      have h1 := ih { addedHyps := [], goal := .imp (.pvar 0) (.pvar 1) } (by simp) v
        (by simpa using hctx)
      have h2 := ih { addedHyps := [], goal := .pvar 0 } (by simp) v
        (by simpa using hctx)
      simp only [instPat, evalForm, Bool.or_eq_true, Bool.not_eq_true'] at h1 h2 ⊢
      rw [h2] at h1
      simpa using h1
    · -- conjIntro
      have h1 := ih { addedHyps := [], goal := .pvar 0 } (by simp) v (by simpa using hctx)
      have h2 := ih { addedHyps := [], goal := .pvar 1 } (by simp) v (by simpa using hctx)
      simp_all [instPat, evalForm]
    · -- conjElimL
      have h1 := ih { addedHyps := [], goal := .conj (.pvar 0) (.pvar 1) } (by simp) v
        (by simpa using hctx)
      simp only [instPat, evalForm, Bool.and_eq_true] at h1 ⊢
      exact h1.1
    · -- conjElimR
      have h1 := ih { addedHyps := [], goal := .conj (.pvar 0) (.pvar 1) } (by simp) v
        (by simpa using hctx)
      simp only [instPat, evalForm, Bool.and_eq_true] at h1 ⊢
      exact h1.2
    · -- disjIntroL
      have h1 := ih { addedHyps := [], goal := .pvar 0 } (by simp) v (by simpa using hctx)
      simp only [instPat] at h1
      simp [instPat, evalForm, h1]
    · -- disjIntroR
      have h1 := ih { addedHyps := [], goal := .pvar 1 } (by simp) v (by simpa using hctx)
      simp only [instPat] at h1
      simp [instPat, evalForm, h1]
    · -- disjElim
      have hdisj := ih { addedHyps := [], goal := .disj (.pvar 0) (.pvar 1) } (by simp) v
        (by simpa using hctx)
      simp only [instPat, evalForm, Bool.or_eq_true] at hdisj
      rcases hdisj with ha | hb
      · have hL := ih { addedHyps := [.pvar 0], goal := .pvar 2 } (by simp) v
          (by simp [instPat, evalCtx, ha, hctx])
        simpa [instPat] using hL
      · have hR := ih { addedHyps := [.pvar 1], goal := .pvar 2 } (by simp) v
          (by simp [instPat, evalCtx, hb, hctx])
        simpa [instPat] using hR
    · -- botElim
      have hbot := ih { addedHyps := [], goal := .bot } (by simp) v (by simpa using hctx)
      simp [instPat, evalForm] at hbot

/-- The standard rules are consistent. -/
theorem stdRules_consistent : Consistent stdRules := stdRules_semSound.consistent

/-- `badRules` derives `⊥` from no hypotheses:
`⊢ ⊥ → ⊤` (two `impIntro`s), hence `⊢ ⊤ → ⊥` by the converse rule, and
`⊢ ⊤`, hence `⊢ ⊥` by `impElim`. -/
theorem badRules_derives_bot : Derivable badRules [] .bot := by
  have hTop : Derivable badRules [] Form.top :=
    ex_derivable_top_pos.mono_rules stdRules_sub_badRules
  have h1 : Derivable badRules [] (.imp .bot Form.top) :=
    Derivable.step (R := badRules) (Γ := [])
      { name := "impIntro"
        premises := [{ addedHyps := [.pvar 0], goal := .pvar 1 }]
        conclusion := .imp (.pvar 0) (.pvar 1) }
      [.bot, Form.top] (by decide)
      (by
        intro p hp
        simp only [List.mem_singleton] at hp
        subst hp
        exact hTop.mono (by intro x hx; cases hx))
  have h2 : Derivable badRules [] (.imp Form.top .bot) :=
    Derivable.step (R := badRules) (Γ := []) converseImpRule [.bot, Form.top] (by decide)
      (by
        intro p hp
        simp only [converseImpRule, List.mem_singleton] at hp
        subst hp
        exact h1)
  exact Derivable.step (R := badRules) (Γ := [])
    { name := "impElim"
      premises := [{ addedHyps := [], goal := .imp (.pvar 0) (.pvar 1) },
                   { addedHyps := [], goal := .pvar 0 }]
      conclusion := .pvar 1 }
    [Form.top, .bot] (by decide)
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact h2
      · exact hTop)

/-- `badRules` derives *every* formula from no hypotheses (via `botElim`,
rule 8, applied to `badRules_derives_bot`). -/
theorem badRules_derives_every_formula (φ : Form) : Derivable badRules [] φ :=
  Derivable.step (R := badRules) (Γ := [])
    { name := "botElim", premises := [{ addedHyps := [], goal := .bot }], conclusion := .pvar 0 }
    [φ] (by decide)
    (by
      intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      exact badRules_derives_bot)

/-! ## Examples for the definitions above -/

/-- Positive example (`evalForm`): `⊥ → ⊥` is true under every valuation. -/
theorem ex_evalForm_top_pos (v : Valuation) : evalForm v Form.top = true := rfl

/-- Negative example (`evalForm`): `⊥` is false under every valuation. -/
theorem ex_evalForm_bot_neg (v : Valuation) : evalForm v .bot ≠ true := by
  simp [evalForm]

/-- Positive example (`evalCtx`): the empty context is satisfied by every
valuation. -/
theorem ex_evalCtx_nil_pos (v : Valuation) : evalCtx v [] = true := rfl

/-- Negative example (`evalCtx`): a context containing `⊥` is satisfied by no
valuation. -/
theorem ex_evalCtx_bot_neg (v : Valuation) (Γ : Ctx) : evalCtx v (.bot :: Γ) = false := by
  simp [evalCtx, evalForm]

/-- Positive example (`SemValid`): `⊢ ⊥ → ⊥` is valid. -/
theorem ex_semValid_top_pos : SemValid [] Form.top := fun _ _ => rfl

/-- Positive example (`SemValid`): Peirce's law is valid in the (classical)
reference semantics, although it is not intuitionistically derivable; the
package never claims completeness of `stdRules`. -/
theorem ex_semValid_peirce_pos :
    SemValid [] (.imp (.imp (.imp (.var 0) (.var 1)) (.var 0)) (.var 0)) := by
  intro v _
  simp only [evalForm]
  cases v 0 <;> cases v 1 <;> rfl

/-- Negative example (`SemValid`): `⊢ p₀` is not valid. -/
theorem ex_semValid_var_neg : ¬ SemValid [] (.var 0) := by
  intro h
  have hv := h (fun _ => false) rfl
  simp [evalForm] at hv

/-- Positive example (`SemSound`, `Consistent`): the standard rules. -/
theorem ex_semSound_stdRules_pos : SemSound stdRules ∧ Consistent stdRules :=
  ⟨stdRules_semSound, stdRules_consistent⟩

/-- Negative example (`SemSound`, `Consistent`): `badRules` is inconsistent,
hence not semantically sound. -/
theorem ex_semSound_badRules_neg : ¬ SemSound badRules ∧ ¬ Consistent badRules :=
  ⟨fun h => h.consistent badRules_derives_bot, fun h => h badRules_derives_bot⟩

/-- Positive example (`SemSound`): the empty rule table is semantically sound
(only hypotheses are derivable). -/
theorem ex_semSound_empty_pos : SemSound [] := by
  intro Γ φ h v hctx
  cases h with
  | hyp hmem => exact evalCtx_mem hctx hmem
  | step r σ hr _ => cases hr

/-- A one-rule table that concludes *any* implication from nothing.  It is the
package's example of a rule table that is consistent but not semantically
sound. -/
def anyImpRules : RuleSet :=
  [ { name := "anyImp", premises := [], conclusion := .imp (.pvar 0) (.pvar 1) } ]

/-- Everything `anyImpRules` derives is a hypothesis or an implication. -/
theorem anyImpRules_derives_hyp_or_imp {Γ : Ctx} {φ : Form}
    (h : Derivable anyImpRules Γ φ) : φ ∈ Γ ∨ ∃ a b, φ = .imp a b := by
  cases h with
  | hyp hmem => exact .inl hmem
  | step r σ hr _ =>
    simp only [anyImpRules, List.mem_singleton] at hr
    subst hr
    exact .inr ⟨_, _, rfl⟩

/-- Negative example separating `Consistent` from `SemSound`: `anyImpRules` is
consistent (it cannot derive `⊥`) but not semantically sound (it derives
`⊢ (⊥ → ⊥) → ⊥`).  So `Consistent R` is strictly weaker than `SemSound R`. -/
theorem ex_consistent_not_semSound_anyImpRules :
    Consistent anyImpRules ∧ ¬ SemSound anyImpRules := by
  constructor
  · intro h
    rcases anyImpRules_derives_hyp_or_imp h with hmem | ⟨a, b, hab⟩
    · cases hmem
    · cases hab
  · intro hs
    have hd : Derivable anyImpRules [] (.imp Form.top .bot) :=
      Derivable.step (R := anyImpRules) (Γ := [])
        { name := "anyImp", premises := [], conclusion := .imp (.pvar 0) (.pvar 1) }
        [Form.top, .bot] (by decide) (by intro p hp; cases hp)
    have hv := hs [] _ hd (fun _ => false) rfl
    simp [evalForm, Form.top] at hv

end Toy.KernelTrust
