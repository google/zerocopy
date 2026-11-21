/-
Transparency of a new symbol, modeled as explicit definability: the symbol can
be replaced by an old-language definiens. Main result: the easy direction of
Beth's definability theorem (Padoa's method). If the new function symbol is
explicitly definable in `T'`, any two models of `T'` that agree on the old
symbols (same carrier) are equal. Consequently a symbol characterized only by
axioms that admit two lawful interpretations over one old structure cannot be
unfolded to any old-language definiens.
-/
import Toy.Extension.DefinitionalExamples
import Toy.Extension.Axiomatic

namespace Toy.Extension

variable {L : Sig}

/-- The sentence `∀ y x̄, (c(x̄) = y ↔ θ(y, x̄))` for a candidate old-language
definiens `θ` of the new function symbol `c` of `L.addFn k`. Variable `0` of
`θ` is the value `y`; variables `1, …, k` are the arguments. -/
def fnDefiningSentence {k : Nat} (θ : Formula L (k + 1)) : Sentence (L.addFn k) :=
  Formula.closeAll (k + 1)
    (.iff (.eq (.app (none : (L.addFn k).Fn) (fun i => .var i.succ)) (.var ⟨0, Nat.succ_pos k⟩))
      (θ.map (SigHom.inclFn L k)))

/-- The new function symbol of `L.addFn k` is explicitly definable in `T'`:
some old-language formula `θ` defines its graph in every model of `T'`. -/
def FnExplicitlyDefinable {k : Nat} (T' : Theory (L.addFn k)) : Prop :=
  ∃ θ : Formula L (k + 1), Entails T' (fnDefiningSentence θ)

/-- In a model of the defining sentence of `θ`, the new symbol's value at `a` is
`b` iff `θ` holds of `b, a` in the reduct. -/
theorem fn_eq_iff_of_models_fnDefiningSentence {k : Nat} {β : Type} (θ : Formula L (k + 1))
    (S : Str (L.addFn k) β) (h : S.Models (fnDefiningSentence θ)) (a : Fin k → β) (b : β) :
    S.fn none a = b ↔ Sat (S.reduct (SigHom.inclFn L k)) (scons b a) θ := by
  have h1 := (sat_closeAll S (k + 1) _).1 h (scons b a)
  have h2 := (sat_iff _ _ _ _).1 h1
  rw [sat_map] at h2
  exact h2

/-- **Main result (Padoa's method).** If the new function symbol is explicitly
definable in `T'`, then any two models of `T'` on the same carrier whose
reducts to the old language coincide are equal. -/
theorem fnExplicitlyDefinable_expansion_unique {k : Nat} (T' : Theory (L.addFn k))
    (hdef : FnExplicitlyDefinable T') {β : Type} (S₁ S₂ : Str (L.addFn k) β)
    (h₁ : S₁.ModelsTh T') (h₂ : S₂.ModelsTh T')
    (hred : S₁.reduct (SigHom.inclFn L k) = S₂.reduct (SigHom.inclFn L k)) :
    S₁ = S₂ := by
  obtain ⟨θ, hθ⟩ := hdef
  have hfn : S₁.fn none = S₂.fn none := by
    funext a
    have e1 := (fn_eq_iff_of_models_fnDefiningSentence θ S₁ (hθ β S₁ h₁) a (S₁.fn none a)).1 rfl
    rw [hred] at e1
    exact ((fn_eq_iff_of_models_fnDefiningSentence θ S₂ (hθ β S₂ h₂) a (S₁.fn none a)).2 e1).symm
  have e : (S₁.reduct (SigHom.inclFn L k)).withFn (k := k) (S₁.fn none) =
      (S₂.reduct (SigHom.inclFn L k)).withFn (k := k) (S₂.fn none) := by rw [hred, hfn]
  exact (withFn_reduct S₁).symm.trans (e.trans (withFn_reduct S₂))

/-- Positive example (`FnExplicitlyDefinable`): a symbol introduced by an
explicit definition `c(x̄) := e(x̄)` is explicitly definable in the
definitional extension, by `θ(y, x̄) := (y = e(x̄))`. -/
theorem defnFn_theory_fnExplicitlyDefinable (T : Theory L) {k : Nat} (e : Term L k) :
    FnExplicitlyDefinable (k := k) ((Defn.fn k e).theory T) := by
  refine ⟨.eq (.var ⟨0, Nat.succ_pos k⟩) (e.rename Fin.succ), ?_⟩
  intro β S hS
  have hax : S.Models (Defn.fn k e).defAxiom := hS _ (Or.inr (List.Mem.head _))
  have hax' := (sat_closeAll S k _).1 hax
  refine (sat_closeAll S (k + 1) _).2 (fun w => ?_)
  refine (sat_iff _ _ _ _).2 ?_
  rw [sat_map]
  have hv : S.fn none (fun j => w j.succ) = (e.map (SigHom.inclFn L k)).eval S (fun j => w j.succ) :=
    hax' (fun j => w j.succ)
  rw [eval_map] at hv
  have hr : (e.rename Fin.succ).eval (S.reduct (SigHom.inclFn L k)) w =
      e.eval (S.reduct (SigHom.inclFn L k)) (fun j => w j.succ) := eval_rename _ _ _ e
  show S.fn none (fun j => w j.succ) = w ⟨0, Nat.succ_pos k⟩ ↔
    w ⟨0, Nat.succ_pos k⟩ = (e.rename Fin.succ).eval (S.reduct (SigHom.inclFn L k)) w
  rw [hr, ← hv]
  exact eq_comm

/-! ### The axiomatized constant of `P c` is not explicitly definable -/

/-- The `{P}`-structure on `Bool` with `P` everywhere true, expanded by `c = true`. -/
def pcModelTrue : Str (LP.addFn 0) Bool := (pStr (fun _ : Bool => True)).withFn (fun _ => true)

/-- The same structure expanded by `c = false`. -/
def pcModelFalse : Str (LP.addFn 0) Bool := (pStr (fun _ : Bool => True)).withFn (fun _ => false)

/-- Two lawful interpretations of `c` for the axiom `P c` over one old
structure: both satisfy `P c`, they have the same reduct, and they differ.
This is also the canonical counterexample for the hypothesis `hdef` of
`fnExplicitlyDefinable_expansion_unique` (all other hypotheses hold and the
conclusion fails). -/
theorem axPc_two_lawful_interpretations :
    pcModelTrue.ModelsTh (Theory.ofList [axPc]) ∧ pcModelFalse.ModelsTh (Theory.ofList [axPc]) ∧
    pcModelTrue.reduct (SigHom.inclFn LP 0) = pcModelFalse.reduct (SigHom.inclFn LP 0) ∧
    pcModelTrue ≠ pcModelFalse := by
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, rfl, fun h => ?_⟩
  · cases hφ with
    | head => trivial
    | tail _ h => cases h
  · cases hφ with
    | head => trivial
    | tail _ h => cases h
  · have := congrArg (fun S : Str (LP.addFn 0) Bool => S.fn none (fun i => i.elim0)) h
    exact absurd this (by decide)

/-- The constant `c` characterized only by the axiom `P c` is not explicitly
definable: no old-language formula `θ(y)` satisfies `P c ⊨ ∀ y, (c = y ↔ θ(y))`. -/
theorem axPc_not_fnExplicitlyDefinable :
    ¬ FnExplicitlyDefinable (k := 0) (Theory.ofList [axPc]) := by
  intro hdef
  obtain ⟨h1, h2, hred, hne⟩ := axPc_two_lawful_interpretations
  exact hne (fnExplicitlyDefinable_expansion_unique _ hdef _ _ h1 h2 hred)

/-! ### Remaining tightness counterexamples and non-vacuity -/

/-- `h₁` and `h₂` of `fnExplicitlyDefinable_expansion_unique` are tight: for the
definitional extension by `two := succ (succ zero)` (explicitly definable), the
canonical expansion of `natStr` and the expansion interpreting `two` as `3`
have the same reduct and differ; the second is not a model. Both orders are
recorded. -/
theorem fnExplicitlyDefinable_expansion_unique_ce_model :
    FnExplicitlyDefinable (k := 0) (dTwo.theory (Theory.empty : Theory NSig)) ∧
    ¬ (natStr.withFn (fun _ : Fin 0 → Nat => 3)).ModelsTh (dTwo.theory (Theory.empty : Theory NSig)) ∧
    (dTwo.expand natStr).ModelsTh (dTwo.theory (Theory.empty : Theory NSig)) ∧
    (natStr.withFn (fun _ : Fin 0 → Nat => 3)).reduct (SigHom.inclFn NSig 0) =
      (dTwo.expand natStr).reduct dTwo.incl ∧
    natStr.withFn (fun _ : Fin 0 → Nat => 3) ≠ dTwo.expand natStr ∧
    dTwo.expand natStr ≠ natStr.withFn (fun _ : Fin 0 → Nat => 3) := by
  have hne := defExt_expansion_unique_ce_axiom.2
  refine ⟨defnFn_theory_fnExplicitlyDefinable _ _, fun h => ?_, defExt_theory_has_model, rfl,
    hne, fun h => hne h.symm⟩
  exact dTwo_three_not_models_defAxiom (h _ (Or.inr (List.Mem.head _)))

/-- `hred` of `fnExplicitlyDefinable_expansion_unique` is tight: the canonical
expansions of `natStr` and of `natStr2` are both models of the definitional
extension by `two`, their reducts differ, and they differ. -/
theorem fnExplicitlyDefinable_expansion_unique_ce_reduct :
    FnExplicitlyDefinable (k := 0) (dTwo.theory (Theory.empty : Theory NSig)) ∧
    (dTwo.expand natStr2).ModelsTh (dTwo.theory (Theory.empty : Theory NSig)) ∧
    (dTwo.expand natStr).ModelsTh (dTwo.theory (Theory.empty : Theory NSig)) ∧
    (dTwo.expand natStr2).reduct dTwo.incl ≠ (dTwo.expand natStr).reduct dTwo.incl ∧
    dTwo.expand natStr2 ≠ dTwo.expand natStr := by
  refine ⟨defnFn_theory_fnExplicitlyDefinable _ _,
    ((defExt_expansions_eq_expand Theory.empty dTwo natStr2 (modelsTh_empty _)) _).2 rfl |>.2,
    defExt_theory_has_model, defExt_expansion_unique_ce_reduct.2.1, defExt_expansion_unique_ce_reduct.2.2⟩

/-- Non-vacuity for `fnExplicitlyDefinable_expansion_unique`: the definitional
extension of the empty theory by `two` is explicitly definable and has a model
(take `S₁ = S₂` that model). -/
theorem fnExplicitlyDefinable_nonvacuity :
    FnExplicitlyDefinable (k := 0) (dTwo.theory (Theory.empty : Theory NSig)) ∧
    (dTwo.expand natStr).ModelsTh (dTwo.theory (Theory.empty : Theory NSig)) :=
  ⟨defnFn_theory_fnExplicitlyDefinable _ _, defExt_theory_has_model⟩

end Toy.Extension
