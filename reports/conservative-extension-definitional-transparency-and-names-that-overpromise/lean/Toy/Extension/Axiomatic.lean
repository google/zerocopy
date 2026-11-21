/-
Axiomatic extensions: fresh symbols characterized only by axioms ("axiomatized
symbols"). This models unchecked first-order axioms about a new symbol; it is
not a model of Lean's `opaque` keyword or of `@[irreducible]` definitions.
Main results: the expansion property implies conservativity; a natural
axiomatic extension is not conservative; with empty carriers even an axiom-free
fresh constant is not conservative; an axiomatized symbol is a loose
specification (its consequences are the facts true under every lawful
interpretation).
-/
import Toy.Extension.Definitional

namespace Toy.Extension

/-! ### A one-predicate language -/

/-- The single relation symbol `P`. -/
inductive PRel | P
  deriving DecidableEq

/-- The language `{P}`: one unary relation symbol and no function symbols. -/
abbrev LP : Sig := ⟨Empty, PRel, fun e => e.elim, fun _ => 1⟩

/-- The `{P}`-structure on `β` interpreting `P` by `p`. -/
def pStr {β : Type} (p : β → Prop) : Str LP β where
  fn := fun e => e.elim
  rel := fun _ args => p (args ⟨0, Nat.zero_lt_one⟩)

/-- The fresh constant `c` of `LP.addFn 0`. -/
def tC {n : Nat} : Term (LP.addFn 0) n := .app (none : (LP.addFn 0).Fn) (fun i => i.elim0)

/-- The axiom `P c`. -/
def axPc : Sentence (LP.addFn 0) := .rel PRel.P (fun _ => tC)

/-- The old-language sentence `∃ x, P x`. -/
def existsP : Sentence LP := .ex (.rel PRel.P (fun _ => .var 0))

/-- The old-language sentence `∀ x, P x`. -/
def forallP : Sentence LP := .all (.rel PRel.P (fun _ => .var 0))

/-- The sentence `∃ x, x = x` ("the carrier is nonempty") over any signature. -/
def existsEq {L : Sig} : Sentence L := .ex (.eq (.var 0) (.var 0))

/-- Positive example (`Conservative`, `Entails`): the trivial extension of
`{P}` by nothing new (identity morphism) is conservative over every theory. -/
def SigHom.id (L : Sig) : SigHom L L := ⟨fun f => f, fun r => r, fun _ => rfl, fun _ => rfl⟩

theorem reduct_id {L : Sig} {β : Type} (S : Str L β) : S.reduct (SigHom.id L) = S := rfl

theorem conservative_id {L : Sig} (T : Theory L) : Conservative (SigHom.id L) T (T.map (SigHom.id L)) := by
  intro φ h β S hS
  have := h β S ((modelsTh_map _ S T).2 hS)
  exact (models_map _ S φ).1 this

/-! ### Expansion property and conservativity -/

/-- **Main result.** If every model of `T` expands (same carrier, old symbols
unchanged) to a model of `T'`, then `T'` is conservative over `T`. -/
theorem expansionProperty_implies_conservative {L L' : Sig} (ι : SigHom L L')
    (T : Theory L) (T' : Theory L') (hexp : ExpansionProperty ι T T') :
    Conservative ι T T' := by
  intro φ h β S hS
  obtain ⟨S', hred, hS'⟩ := hexp β S hS
  exact hred ▸ (models_map ι S' φ).1 (h β S' hS')

/-! ### A natural non-conservative axiomatic extension -/

/-- **Main result (counterexample).** The axiomatic extension of the empty `{P}`-theory by a fresh
constant `c` with axiom `P c` entails the old-language sentence `∃ x, P x`,
which the empty theory does not entail; so it is not conservative, and it
does not have the expansion property. -/
theorem axiom_P_c_not_conservative :
    Entails (Theory.ofList [axPc]) (existsP.map (SigHom.inclFn LP 0)) ∧
    ¬ Entails (Theory.empty : Theory LP) existsP ∧
    ¬ Conservative (SigHom.inclFn LP 0) Theory.empty (Theory.ofList [axPc]) ∧
    ¬ ExpansionProperty (SigHom.inclFn LP 0) Theory.empty (Theory.ofList [axPc]) := by
  have h1 : Entails (Theory.ofList [axPc]) (existsP.map (SigHom.inclFn LP 0)) := by
    intro β S hS
    exact ⟨tC.eval S noVars, hS axPc (List.Mem.head _)⟩
  have h2 : ¬ Entails (Theory.empty : Theory LP) existsP := by
    intro h
    obtain ⟨_, ha⟩ := h Unit (pStr (fun _ => False)) (modelsTh_empty _)
    exact ha
  refine ⟨h1, h2, fun hc => h2 (hc existsP h1), ?_⟩
  intro hexp
  obtain ⟨S', hred, hS'⟩ := hexp Unit (pStr (fun _ => False)) (modelsTh_empty _)
  have hP := hS' axPc (List.Mem.head _)
  have := congrArg (fun S : Str LP Unit => S.rel PRel.P (fun _ => tC.eval S' noVars)) hred
  simp only at this
  have hP' : (S'.reduct (SigHom.inclFn LP 0)).rel PRel.P (fun _ => tC.eval S' noVars) := hP
  rw [this] at hP'
  exact hP'

/-- `hexp` in `expansionProperty_implies_conservative` is tight: the extension
by `P c` has neither the expansion property nor conservativity (a
one-predicate language, a one-point countermodel). -/
theorem expansionProperty_implies_conservative_ce :
    ¬ ExpansionProperty (SigHom.inclFn LP 0) Theory.empty (Theory.ofList [axPc]) ∧
    ¬ Conservative (SigHom.inclFn LP 0) Theory.empty (Theory.ofList [axPc]) :=
  ⟨axiom_P_c_not_conservative.2.2.2, axiom_P_c_not_conservative.2.2.1⟩

/-- Non-vacuity for `expansionProperty_implies_conservative`: adding a fresh
0-ary relation symbol (a propositional constant) with no axioms has the
expansion property, even over empty carriers. -/
theorem expansionProperty_nonvacuity :
    ExpansionProperty (SigHom.inclRel LP 0) Theory.empty Theory.empty :=
  fun _ S _ => ⟨S.withRel (fun _ => True), rfl, modelsTh_empty _⟩

/-! ### Empty carriers: a fresh constant without axioms (proved) -/

/-- **Main result (counterexample).** With empty carriers allowed, adding one fresh constant with
no axioms at all to the empty `{P}`-theory (a language with no closed terms)
is not conservative: the extension entails `∃ x, x = x`, and the empty
structure refutes it. -/
theorem fresh_constant_not_conservative_with_empty_carriers :
    Entails (Theory.empty : Theory (LP.addFn 0)) (existsEq.map (SigHom.inclFn LP 0)) ∧
    ¬ Entails (Theory.empty : Theory LP) existsEq ∧
    ¬ Conservative (SigHom.inclFn LP 0) Theory.empty Theory.empty := by
  have h1 : Entails (Theory.empty : Theory (LP.addFn 0)) (existsEq.map (SigHom.inclFn LP 0)) :=
    fun β S _ => ⟨tC.eval S noVars, rfl⟩
  have h2 : ¬ Entails (Theory.empty : Theory LP) existsEq := by
    intro h
    obtain ⟨a, _⟩ := h Empty (pStr (fun _ => False)) (modelsTh_empty _)
    exact a.elim
  exact ⟨h1, h2, fun hc => h2 (hc existsEq h1)⟩

/-- Positive control for `fresh_constant_not_conservative_with_empty_carriers`:
if `T` entails that the carrier is nonempty, adding a fresh constant with no
axioms is conservative (for any signature). The converse is
`fresh_constant_conservative_iff_entails_nonempty`. -/
theorem fresh_constant_conservative_of_nonempty_models {L : Sig} (T : Theory L)
    (hne : Entails T existsEq) :
    Conservative (SigHom.inclFn L 0) T (T.map (SigHom.inclFn L 0)) := by
  intro φ h β S hS
  obtain ⟨a, _⟩ := hne β S hS
  have hS' : (S.withFn (fun _ : Fin 0 → β => a)).ModelsTh (T.map (SigHom.inclFn L 0)) :=
    (modelsTh_map _ _ T).2 hS
  exact (models_map _ _ φ).1 (h β _ hS')

/-- Characterization behind the positive control: for any signature `L` and
theory `T`, adding a fresh constant with no axioms is conservative iff `T`
entails `∃ x, x = x`. -/
theorem fresh_constant_conservative_iff_entails_nonempty {L : Sig} (T : Theory L) :
    Conservative (SigHom.inclFn L 0) T (T.map (SigHom.inclFn L 0)) ↔ Entails T existsEq :=
  ⟨fun hc => hc existsEq fun _ S _ =>
    ⟨(Term.app (none : (L.addFn 0).Fn) (fun i => i.elim0)).eval S noVars, rfl⟩,
   fresh_constant_conservative_of_nonempty_models T⟩

/-! ### A non-injective signature morphism -/

/-- Two propositional symbols `a`, `b`. -/
inductive ABRel | a | b
  deriving DecidableEq

/-- The language `{a, b}` of two 0-ary relation symbols. -/
abbrev LAB : Sig := ⟨Empty, ABRel, fun e => e.elim, fun _ => 0⟩

/-- The language with one 0-ary relation symbol. -/
abbrev LUnit : Sig := ⟨Empty, Unit, fun e => e.elim, fun _ => 0⟩

/-- The non-injective morphism identifying `a` and `b`. -/
def ιCollapse : SigHom LAB LUnit := ⟨id, fun _ => (), fun e => e.elim, fun _ => rfl⟩

/-- The sentence `a ↔ b`. -/
def abIff : Sentence LAB :=
  Formula.iff (.rel ABRel.a (fun i => i.elim0)) (.rel ABRel.b (fun i => i.elim0))

/-- The `{a, b}`-structure on `Unit` with `a` true and `b` false. -/
def abStr : Str LAB Unit := ⟨fun e => e.elim, fun r _ => match r with | .a => True | .b => False⟩

/-- Along a non-injective morphism, even the empty theory over the larger
language is neither conservative over nor expansion-complete for the empty
theory: it entails the translation of `a ↔ b`, and the structure with `a` true
and `b` false has no expansion. -/
theorem noninjective_hom_empty_theories_not_conservative :
    Entails (Theory.empty : Theory LUnit) (abIff.map ιCollapse) ∧
    ¬ Entails (Theory.empty : Theory LAB) abIff ∧
    ¬ Conservative ιCollapse Theory.empty Theory.empty ∧
    ¬ ExpansionProperty ιCollapse Theory.empty Theory.empty := by
  have h1 : Entails (Theory.empty : Theory LUnit) (abIff.map ιCollapse) :=
    fun _ _ _ => ⟨fun h => h, fun h => h⟩
  have h2 : ¬ Entails (Theory.empty : Theory LAB) abIff :=
    fun h => (h Unit abStr (modelsTh_empty _)).1 trivial
  refine ⟨h1, h2, fun hc => h2 (hc _ h1), fun hexp => ?_⟩
  obtain ⟨S', hred, _⟩ := hexp Unit abStr (modelsTh_empty _)
  have ha := congrArg (fun S : Str LAB Unit => S.rel ABRel.a (fun i => i.elim0)) hred
  have hb := congrArg (fun S : Str LAB Unit => S.rel ABRel.b (fun i => i.elim0)) hred
  simp only [Str.reduct, ιCollapse, abStr] at ha hb
  exact (hb ▸ ha ▸ trivial : False)

/-! ### Axiomatized symbols are loose specifications -/

/-- **Main result.** For a fresh `k`-ary function symbol characterized only by
axioms `A`, a sentence `ψ` follows from `T + A` iff `ψ` holds in every
expansion `S.withFn g` of every model `S` of `T` by every interpretation `g`
of the new symbol that satisfies `A` ("lawful interpretations"). -/
theorem axExt_entails_iff_lawful_interpretations {L : Sig} {k : Nat}
    (T : Theory L) (A : Theory (L.addFn k)) (ψ : Sentence (L.addFn k)) :
    Entails ((T.map (SigHom.inclFn L k)).union A) ψ ↔
      ∀ (β : Type) (S : Str L β), S.ModelsTh T →
        ∀ g : (Fin k → β) → β, (S.withFn g).ModelsTh A → (S.withFn g).Models ψ := by
  constructor
  · intro h β S hS g hA
    exact h β (S.withFn g) ((modelsTh_union _ _ _).2 ⟨(modelsTh_map _ _ _).2 hS, hA⟩)
  · intro h β S' hS'
    obtain ⟨hT, hA⟩ := (modelsTh_union _ _ _).1 hS'
    have h1 := h β (S'.reduct (SigHom.inclFn L k)) ((modelsTh_map _ _ _).1 hT)
      (S'.fn (none : Option L.Fn))
    have heq : (S'.reduct (SigHom.inclFn L k)).withFn (S'.fn (none : Option L.Fn)) = S' :=
      withFn_reduct S'
    exact heq ▸ h1 (heq.symm ▸ hA)

/-- Non-vacuity for `axExt_entails_iff_lawful_interpretations`: the axiom
`P c` has a lawful interpretation (one point, `P` true, `c` that point). -/
theorem axExt_lawful_interpretation_exists :
    ((pStr (fun _ : Unit => True)).withFn (fun _ : Fin 0 → Unit => ())).ModelsTh
      (((Theory.empty : Theory LP).map (SigHom.inclFn LP 0)).union (Theory.ofList [axPc])) := by
  rintro φ (⟨ψ, hψ, _⟩ | hφ)
  · exact hψ.elim
  · cases hφ with
    | head => trivial
    | tail _ h => cases h

/-- "Nothing more" (first-order instance): from `P c` alone one cannot derive
`∀ x, P x`; the lawful interpretation on `Bool` with `P = (· = true)` and
`c = true` refutes it. -/
theorem axExt_does_not_entail_unforced_fact :
    ¬ Entails (Theory.ofList [axPc]) (forallP.map (SigHom.inclFn LP 0)) := by
  intro h
  have hm : ((pStr (fun b : Bool => b = true)).withFn (fun _ : Fin 0 → Bool => true)).ModelsTh
      (Theory.ofList [axPc]) := by
    intro φ hφ
    cases hφ with
    | head => rfl
    | tail _ h => cases h
  have hf : false = true := h Bool _ hm false
  exact absurd hf (by decide)

end Toy.Extension
