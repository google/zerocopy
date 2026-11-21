/-
Scope examples for the explicit-definability and stored-syntax results:
`FnExplicitlyDefinable` holds vacuously for a theory with no model; on a
satisfiable theory it gives uniqueness of expansions but neither
conservativity nor the expansion property over the empty base theory; and
reinterpreting a referenced symbol can leave a truth value unchanged.
-/
import Toy.Extension.Transparency

namespace Toy.Extension

variable {L : Sig}

/-- `FnExplicitlyDefinable` holds for every theory that has no model on any
carrier: the old-language formula `falsum` serves as a definiens. -/
theorem fnExplicitlyDefinable_of_no_model {k : Nat} (T' : Theory (L.addFn k))
    (hno : ∀ (β : Type) (S : Str (L.addFn k) β), ¬ S.ModelsTh T') :
    FnExplicitlyDefinable T' :=
  ⟨Formula.falsum, fun β S hS => (hno β S hS).elim⟩

/-- Instance of `fnExplicitlyDefinable_of_no_model`: the theory `{falsum}` over
`{P}` plus a fresh constant has no model and satisfies `FnExplicitlyDefinable`. -/
theorem falsum_theory_fnExplicitlyDefinable_no_model :
    FnExplicitlyDefinable (k := 0) (Theory.ofList [Formula.falsum] : Theory (LP.addFn 0)) ∧
    ¬ ∃ (β : Type) (S : Str (LP.addFn 0) β),
      S.ModelsTh (Theory.ofList [Formula.falsum] : Theory (LP.addFn 0)) := by
  have hno : ∀ (β : Type) (S : Str (LP.addFn 0) β),
      ¬ S.ModelsTh (Theory.ofList [Formula.falsum] : Theory (LP.addFn 0)) :=
    fun _ _ hS => hS _ (List.Mem.head _)
  exact ⟨fnExplicitlyDefinable_of_no_model _ hno, fun ⟨β, S, hS⟩ => hno β S hS⟩

/-- The theory over `{P}` plus a fresh constant `c` whose single axiom is the
defining sentence `∀ y, (c = y ↔ y = y)` of the old-language formula `y = y`. -/
def singletonDefTheory : Theory (LP.addFn 0) :=
  Theory.ofList [fnDefiningSentence (L := LP) (k := 0) (.eq (.var 0) (.var 0))]

/-- The old-language sentence `∀ x y, x = y` ("at most one element"). -/
def atMostOneElt : Sentence LP := .all (.all (.eq (.var 0) (.var 1)))

/-- Explicit definability gives uniqueness of expansions, not conservativity:
`singletonDefTheory` explicitly defines `c` and has a model (on `Unit`), but
it entails the old-language sentence `∀ x y, x = y`, which the empty
`{P}`-theory does not entail (two-element countermodel on `Bool`). So it is
neither conservative over the empty theory nor has the expansion property
over it. -/
theorem fnExplicitlyDefinable_satisfiable_not_conservative :
    FnExplicitlyDefinable (k := 0) singletonDefTheory ∧
    ((pStr (fun _ : Unit => False)).withFn (fun _ => ())).ModelsTh singletonDefTheory ∧
    Entails singletonDefTheory (atMostOneElt.map (SigHom.inclFn LP 0)) ∧
    ¬ Entails (Theory.empty : Theory LP) atMostOneElt ∧
    ¬ Conservative (SigHom.inclFn LP 0) Theory.empty singletonDefTheory ∧
    ¬ ExpansionProperty (SigHom.inclFn LP 0) Theory.empty singletonDefTheory := by
  have hdef : FnExplicitlyDefinable (k := 0) singletonDefTheory :=
    ⟨.eq (.var 0) (.var 0), fun _ _ hS => hS _ (List.Mem.head _)⟩
  have hsat : ((pStr (fun _ : Unit => False)).withFn (fun _ => ())).ModelsTh
      singletonDefTheory := by
    intro φ hφ
    cases hφ with
    | head =>
      refine (sat_closeAll _ 1 _).2 (fun _ => ?_)
      exact ⟨fun _ => rfl, fun _ => rfl⟩
    | tail _ h => cases h
  have hent : Entails singletonDefTheory (atMostOneElt.map (SigHom.inclFn LP 0)) := by
    intro β S hS
    have hm : S.Models (fnDefiningSentence (L := LP) (k := 0) (.eq (.var 0) (.var 0))) :=
      hS _ (List.Mem.head _)
    have hc : ∀ b : β, S.fn none noVars = b := fun b =>
      (fn_eq_iff_of_models_fnDefiningSentence _ S hm noVars b).2 rfl
    intro a b
    exact (hc b).symm.trans (hc a)
  have hnot : ¬ Entails (Theory.empty : Theory LP) atMostOneElt := by
    intro h
    have hf : false = true := h Bool (pStr (fun _ : Bool => True)) (modelsTh_empty _) true false
    exact absurd hf (by decide)
  have hnc : ¬ Conservative (SigHom.inclFn LP 0) Theory.empty singletonDefTheory :=
    fun hc => hnot (hc atMostOneElt hent)
  exact ⟨hdef, hsat, hent, hnot, hnc,
    fun hexp => hnc (expansionProperty_implies_conservative _ _ _ hexp)⟩

/-- Reinterpreting a referenced symbol need not change a truth value: the
stored sentence `∃ x, P x` is true on `Bool` both when `P` is `(· = true)` and
when `P` is `(· = false)`, and these two structures differ. -/
theorem reinterpreted_symbol_need_not_flip_truth :
    pStr (fun b : Bool => b = true) ≠ pStr (fun b : Bool => b = false) ∧
    (pStr (fun b : Bool => b = true)).Models existsP ∧
    (pStr (fun b : Bool => b = false)).Models existsP := by
  refine ⟨fun h => ?_, ⟨true, rfl⟩, ⟨false, rfl⟩⟩
  have := congrArg (fun S : Str LP Bool => S.rel PRel.P (fun _ => true)) h
  simp only [pStr] at this
  have htf : true = false := of_eq_true this.symm
  exact Bool.noConfusion htf

end Toy.Extension
