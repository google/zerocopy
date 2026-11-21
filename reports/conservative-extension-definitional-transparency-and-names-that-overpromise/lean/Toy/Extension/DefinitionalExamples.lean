/-
Concrete instances for the definitional-extension results: a signature with `zero`, `succ`, `≤`, the
standard structure on `Nat`, a defined constant `two := succ (succ zero)` and a
defined relation `isSucc x :↔ ∃ y, x = succ y`. Positive and negative examples
of the definitions, tightness counterexamples and non-vacuity witnesses.
-/
import Toy.Extension.Definitional

namespace Toy.Extension

/-- Function symbols `zero` (arity 0) and `succ` (arity 1). -/
inductive NFn | zero | succ
  deriving DecidableEq

/-- One binary relation symbol `le`. -/
inductive NRel | le
  deriving DecidableEq

/-- Arities of `NFn`. -/
def NFn.arity : NFn → Nat
  | .zero => 0
  | .succ => 1

/-- The signature `{zero, succ, le}`. -/
abbrev NSig : Sig := ⟨NFn, NRel, NFn.arity, fun _ => 2⟩

/-- The standard structure on `Nat`. -/
def natStr : Str NSig Nat where
  fn := fun f => match f with
    | .zero => fun _ => 0
    | .succ => fun a => a ⟨0, Nat.zero_lt_one⟩ + 1
  rel := fun r => match r with
    | .le => fun a => a ⟨0, by decide⟩ ≤ a ⟨1, by decide⟩

/-- A nonstandard structure on `Nat` where `succ` adds two. -/
def natStr2 : Str NSig Nat where
  fn := fun f => match f with
    | .zero => fun _ => 0
    | .succ => fun a => a ⟨0, Nat.zero_lt_one⟩ + 2
  rel := fun r => match r with
    | .le => fun a => a ⟨0, by decide⟩ ≤ a ⟨1, by decide⟩

/-- The term `zero`. -/
def tZero {n : Nat} : Term NSig n := .app NFn.zero (fun i => i.elim0)

/-- The term `succ t`. -/
def tSucc {n : Nat} (t : Term NSig n) : Term NSig n := .app NFn.succ (fun _ => t)

/-- The explicit definition `two := succ (succ zero)` (a constant: arity 0). -/
def dTwo : Defn NSig := .fn 0 (tSucc (tSucc tZero))

/-- The explicit definition `isSucc x :↔ ∃ y, x = succ y` (inside the
quantifier, variable `1` is `x` and variable `0` is `y`). -/
def dIsSucc : Defn NSig := .rel 1 (.ex (.eq (.var 1) (tSucc (.var 0))))

/-- The new constant `two` as a term of the extended language. -/
def tTwoNew : Term dTwo.sig 0 := .app (none : (NSig.addFn 0).Fn) (fun i => i.elim0)

/-- The sentence `two = succ (succ zero)` of the extended language. -/
def psiTwo : Sentence dTwo.sig := .eq tTwoNew ((tSucc (tSucc tZero)).map dTwo.incl)

/-- The sentence `∀ z, isSucc (succ z)` of the extended language. -/
def psiIsSucc : Sentence dIsSucc.sig :=
  .all (.rel (none : (NSig.addRel 1).Rel)
    (fun _ => .app (NFn.succ : (NSig.addRel 1).Fn) (fun _ => .var 0)))

/-! ### Positive and negative examples of the definitions -/

/-- Positive example (`Defn.expand`, `Defn.defAxiom`): the canonical expansion
satisfies the defining axiom of `two`. -/
theorem dTwo_expand_models_defAxiom : (dTwo.expand natStr).Models dTwo.defAxiom := rfl

/-- Negative example (`Defn.defAxiom`): interpreting `two` as `3` violates the
defining axiom. -/
theorem dTwo_three_not_models_defAxiom :
    ¬ (natStr.withFn (fun _ : Fin 0 → Nat => 3)).Models (dTwo.defAxiom) := by
  intro h
  have h' : (3 : Nat) = 2 := h
  exact absurd h' (by decide)

/-- Positive example (`Defn.expand` for a relation): the canonical expansion
satisfies the defining axiom of `isSucc`. -/
theorem dIsSucc_expand_models_defAxiom : (dIsSucc.expand natStr).Models dIsSucc.defAxiom := by
  refine (sat_closeAll (L := NSig.addRel 1) (dIsSucc.expand natStr) 1 _).2 ?_
  intro v
  refine (sat_iff _ _ _ _).2 ?_
  refine Iff.trans ?_ (sat_map _ _ _ _).symm
  exact Iff.rfl

/-- Positive example (`Defn.unfold`): unfolding `two` replaces it by its definiens. -/
theorem dTwo_unfold_psiTwo :
    dTwo.unfold psiTwo = .eq (tSucc (tSucc tZero)) (tSucc (tSucc tZero)) := by decide

/-- Positive example (`Defn.unfold`, capture avoidance): unfolding
`∀ z, isSucc (succ z)` gives `∀ z, ∃ y, succ z = succ y`, with the argument's
variable shifted under the definiens' quantifier. -/
theorem dIsSucc_unfold_psiIsSucc :
    dIsSucc.unfold psiIsSucc = .all (.ex (.eq (tSucc (.var 1)) (tSucc (.var 0)))) := by decide

/-- Negative example (`Defn.unfold`): the unfolding is not the variable-capturing
naive substitution `∀ z, ∃ y, succ y = succ y`. -/
theorem dIsSucc_unfold_not_capturing :
    dIsSucc.unfold psiIsSucc ≠ .all (.ex (.eq (tSucc (.var 0)) (tSucc (.var 0)))) := by decide

/-- Positive example (`Sig.addFn`, `Str.withFn`, `Str.reduct`): expanding and
then taking the reduct returns the original structure. -/
theorem natStr_withFn_reduct :
    (natStr.withFn (fun _ : Fin 0 → Nat => 7)).reduct (SigHom.inclFn NSig 0) = natStr := rfl

/-- Negative example (`Str.reduct`): reducts remember the old symbols, so an
expansion of `natStr2` is not an expansion of `natStr`. -/
theorem natStr2_withFn_reduct_ne :
    (natStr2.withFn (fun _ : Fin 0 → Nat => 7)).reduct (SigHom.inclFn NSig 0) ≠ natStr := by
  intro h
  have := congrArg (fun S : Str NSig Nat => S.fn NFn.succ (fun _ => 0)) h
  exact absurd this (by decide)

/-! ### Tightness counterexamples (canonical form) -/

/-- `hS` in `defExt_expansions_eq_expand` is tight: for `T = {⊥}` (no models)
and `S = natStr`, the characterization fails at `S' = dTwo.expand natStr`. -/
theorem defExt_expansions_eq_expand_ce_not_model :
    ¬ natStr.ModelsTh (Theory.ofList [Formula.falsum]) ∧
    ¬ (∀ S' : Str dTwo.sig Nat,
        (S'.reduct dTwo.incl = natStr ∧ S'.ModelsTh (dTwo.theory (Theory.ofList [Formula.falsum])))
          ↔ S' = dTwo.expand natStr) := by
  refine ⟨fun h => h Formula.falsum (List.Mem.head _), fun h => ?_⟩
  have hm := ((h (dTwo.expand natStr)).2 rfl).2
  exact hm (Formula.falsum.map dTwo.incl) (Or.inl ⟨Formula.falsum, List.Mem.head _, rfl⟩)

/-- `hred` in `defExt_expansion_unique_of_axiom` is tight: the canonical
expansion of `natStr2` satisfies the defining axiom but is not the canonical
expansion of `natStr`. -/
theorem defExt_expansion_unique_ce_reduct :
    (dTwo.expand natStr2).Models dTwo.defAxiom ∧
    (dTwo.expand natStr2).reduct dTwo.incl ≠ natStr ∧
    dTwo.expand natStr2 ≠ dTwo.expand natStr := by
  refine ⟨rfl, natStr2_withFn_reduct_ne' , ?_⟩
  intro h
  have := congrArg (fun S : Str dTwo.sig Nat => S.fn (some NFn.succ) (fun _ => 0)) h
  exact absurd this (by decide)
where
  natStr2_withFn_reduct_ne' : (dTwo.expand natStr2).reduct dTwo.incl ≠ natStr := by
    intro h
    have := congrArg (fun S : Str NSig Nat => S.fn NFn.succ (fun _ => 0)) h
    exact absurd this (by decide)

/-- `hax` in `defExt_expansion_unique_of_axiom` is tight: interpreting `two`
as `3` gives an expansion of `natStr` that is not the canonical one. -/
theorem defExt_expansion_unique_ce_axiom :
    (natStr.withFn (fun _ : Fin 0 → Nat => 3)).reduct dTwo.incl = natStr ∧
    natStr.withFn (fun _ : Fin 0 → Nat => 3) ≠ dTwo.expand natStr := by
  refine ⟨rfl, fun h => ?_⟩
  have := congrArg (fun S : Str dTwo.sig Nat => S.fn none (fun i => i.elim0)) h
  exact absurd this (by decide)

/-- Negative example (`Defn.unfold`, `Defn.defAxiom`): with `two` interpreted as
`3` (defining axiom violated), the sentence `two = succ (succ zero)` is false
while its unfolding is true. This is the canonical counterexample showing that
the hypothesis `hax` of `defExt_unfold_equiv_of_axiom` cannot be dropped. -/
theorem defExt_unfold_equiv_ce_axiom :
    ¬ (Sat (natStr.withFn (fun _ : Fin 0 → Nat => 3)) noVars psiTwo ↔
       Sat (natStr.withFn (fun _ : Fin 0 → Nat => 3)) noVars ((dTwo.unfold psiTwo).map dTwo.incl)) := by
  intro h
  have h2 : Sat (natStr.withFn (fun _ : Fin 0 → Nat => 3)) noVars ((dTwo.unfold psiTwo).map dTwo.incl) := by
    rw [dTwo_unfold_psiTwo]; rfl
  have h3 : (3 : Nat) = 2 := h.2 h2
  exact absurd h3 (by decide)

/-! ### Non-vacuity witnesses -/

/-- Non-vacuity for `defExt_expansions_eq_expand`: `natStr` is a model of the
empty theory. -/
theorem defExt_expansions_eq_expand_nonvacuity : natStr.ModelsTh (Theory.empty : Theory NSig) :=
  modelsTh_empty _

/-- Non-vacuity for `defExt_expansion_unique_of_axiom` (and an instance in
which both sides of `models_defAxiom_iff_unfold_preserves_sat` hold): the
canonical expansion is an expansion of `natStr` satisfying the defining axiom. -/
theorem defExt_axiom_nonvacuity :
    (dTwo.expand natStr).reduct dTwo.incl = natStr ∧ (dTwo.expand natStr).Models dTwo.defAxiom :=
  ⟨rfl, rfl⟩

/-- Non-vacuity for `defExt_conservative`: the definitional extension of the
empty theory by `two` has a model. -/
theorem defExt_theory_has_model :
    (dTwo.expand natStr).ModelsTh (dTwo.theory (Theory.empty : Theory NSig)) := by
  rintro φ (⟨ψ, hψ, _⟩ | hφ)
  · exact hψ.elim
  · cases hφ with
    | head => rfl
    | tail _ h => cases h

/-! ### Delta-conversion examples -/

instance : DecidableEq dTwo.sig.Fn := inferInstanceAs (DecidableEq (Option NFn))
instance : DecidableEq dTwo.sig.Rel := inferInstanceAs (DecidableEq NRel)

/-- The sentence `two = two` of the extended language. -/
def psiTwoRefl : Sentence dTwo.sig := .eq tTwoNew tTwoNew

/-- Delta-conversion is sound in the canonical expansion and unsound once `two`
is interpreted as `3`: there, the sentences `two = succ (succ zero)` and
`two = two` have different truth values. -/
theorem dTwo_deltaConv_sound_and_unsound :
    (Sat (dTwo.expand natStr) noVars psiTwo ↔ Sat (dTwo.expand natStr) noVars psiTwoRefl) ∧
    ¬ (Sat (natStr.withFn (fun _ : Fin 0 → Nat => 3)) noVars psiTwo ↔
       Sat (natStr.withFn (fun _ : Fin 0 → Nat => 3)) noVars psiTwoRefl) := by
  refine ⟨⟨fun _ => rfl, fun _ => rfl⟩, fun h => ?_⟩
  have h3 : (3 : Nat) = 2 := h.2 rfl
  exact absurd h3 (by decide)

/-- Positive and negative example (`Defn.DeltaConv`): `two = succ (succ zero)` and
`two = two` are delta-convertible for `two := succ (succ zero)` although they
are different sentences; `two = succ (succ zero)` and `falsum` are not
delta-convertible. -/
theorem dTwo_deltaConv_examples :
    dTwo.DeltaConv psiTwo psiTwoRefl ∧ psiTwo ≠ psiTwoRefl ∧
    ¬ dTwo.DeltaConv psiTwo Formula.falsum := by
  refine ⟨by decide, fun h => ?_, by decide⟩
  exact dTwo_deltaConv_sound_and_unsound.2 (h ▸ Iff.rfl)

/-- For one fixed formula, unfolding can preserve truth without the defining
axiom: with `two` interpreted as `3` (axiom violated), the sentence `tru` and
its unfolding have the same truth value. So the quantification over all
formulas in `models_defAxiom_iff_unfold_preserves_sat` matters. -/
theorem unfold_preserves_tru_without_defAxiom :
    ¬ (natStr.withFn (fun _ : Fin 0 → Nat => 3)).Models dTwo.defAxiom ∧
    (Sat (natStr.withFn (fun _ : Fin 0 → Nat => 3)) noVars Formula.tru ↔
     Sat (natStr.withFn (fun _ : Fin 0 → Nat => 3)) noVars ((dTwo.unfold Formula.tru).map dTwo.incl)) :=
  ⟨dTwo_three_not_models_defAxiom, Iff.rfl⟩

end Toy.Extension
