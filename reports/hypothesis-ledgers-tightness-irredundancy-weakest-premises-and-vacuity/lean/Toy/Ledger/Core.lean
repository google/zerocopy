/-!
# Hypothesis ledgers: core definitions

A theorem of the shape "for every model `x`, if every hypothesis `H i x` holds then `C x`"
is often published together with a *hypothesis ledger*: each hypothesis is labelled
`tight` (there is a model in which every *other* hypothesis holds and the conclusion fails),
`harmless`, or `unknown`, and the theorem comes with a *non-vacuity witness* (a model in
which all hypotheses hold).

This file fixes the vocabulary used to say exactly what such labels mean. Everything is a
toy, Mathlib-free formal theory: a model type `M`, a hypothesis family `H : ι → M → Prop`
indexed by an arbitrary type `ι` (the usual `Fin m` is one instance), and a conclusion
`C : M → Prop`. Each property is a separate named `Prop`, so theorems name exactly the
properties they use.

Scope of the model. The family `H` is *non-dependent*: every `H j x` is a proposition about
`x` alone, meaningful whether or not the other hypotheses hold. A Lean theorem whose later
binders mention proofs of earlier ones (`(h₁ : H₁ x) → (h₂ : H₂ x h₁) → C x`) fits this
theory only after `H₂` is made into a predicate on `x` alone, and the choice of that
predicate changes which hypotheses are tight (see the non-claims of the cards).
-/

namespace Toy.Ledger

universe u v w

section Basic

variable {M : Type u} {ι : Type v}

/-- The theorem itself: every model satisfying all hypotheses satisfies the conclusion.
Captures "the hypotheses `H` suffice for `C` over the model type `M`". -/
def Sufficient (H : ι → M → Prop) (C : M → Prop) : Prop :=
  ∀ x, (∀ i, H i x) → C x

/-- Hypothesis `i` is *tight*: some model satisfies every hypothesis other than `i` and
violates the conclusion. Captures the ledger label "`tight`, witnessed by a model in which
all other hypotheses hold and the conclusion fails". When the theorem holds, this says that
dropping `H i` alone breaks it (`tightAt_iff_not_sufficient_without`). When the theorem
fails, every hypothesis is tight (`irredundant_of_not_sufficient`). It says nothing about
which other premises could replace `H i`. -/
def TightAt (H : ι → M → Prop) (C : M → Prop) (i : ι) : Prop :=
  ∃ x, (∀ j, j ≠ i → H j x) ∧ ¬ C x

/-- Every hypothesis is tight. Captures a complete all-`tight` ledger. It does not include
`Sufficient H C`: every false theorem is irredundant (`irredundant_of_not_sufficient`). -/
def Irredundant (H : ι → M → Prop) (C : M → Prop) : Prop :=
  ∀ i, TightAt H C i

/-- Some model satisfies all hypotheses. Captures a non-vacuity witness, that is,
satisfiability of the antecedent; read as a property of an arbitrary family `G`, it is
plain *satisfiability* of `G`. It does not mention the conclusion, so it is not the
"every subformula affects the truth value" notion of vacuity used in temporal-logic model
checking. -/
def NonVacuous (H : ι → M → Prop) : Prop :=
  ∃ x, ∀ i, H i x

/-- Global necessity of hypothesis `i`: every model of the conclusion satisfies `H i`.
Captures the everyday reading "`H i` is necessary for `C`". -/
def NecessaryAt (H : ι → M → Prop) (C : M → Prop) (i : ι) : Prop :=
  ∀ x, C x → H i x

/-- Necessity of hypothesis `i` relative to the other hypotheses: wherever the other
hypotheses and the conclusion hold, `H i` holds. Captures "`H i` cannot be replaced by a
strictly weaker premise while keeping the other hypotheses", where a premise is an
*arbitrary* predicate on `M`, which may mention the conclusion or variables that `H i`
does not mention (made precise by `unweakenableAt_characterizations_of_sufficient`). -/
def UnweakenableAt (H : ι → M → Prop) (C : M → Prop) (i : ι) : Prop :=
  ∀ x, (∀ j, j ≠ i → H j x) → C x → H i x

/-- Full logical independence of the hypotheses: every truth pattern `s : ι → Bool` of the
hypotheses is realized by some model. For `ι = Fin m` these are the `2^m` patterns. -/
def Independent (H : ι → M → Prop) : Prop :=
  ∀ s : ι → Bool, ∃ x, ∀ i, (H i x ↔ s i = true)

/-- The classical one-model-per-axiom independence witness for hypothesis `i`: a model
violating `H i` and satisfying every other hypothesis. It does not mention the conclusion. -/
def IsolatingAt (H : ι → M → Prop) (i : ι) : Prop :=
  ∃ x, ¬ H i x ∧ ∀ j, j ≠ i → H j x

/-- The subfamily of `H` selected by `S`, indexed by the subtype `{j // S j}`. -/
def restrict (S : ι → Prop) (H : ι → M → Prop) : Subtype S → M → Prop :=
  fun j => H j.1

/-- A family is *minimally unsatisfiable* when it is unsatisfiable (`¬ NonVacuous G`) and
every proper subfamily (one omitting at least one member) is satisfiable. Captures the
notion of a minimal unsatisfiable subset (MUS) of a constraint set. -/
def MinimalUnsatisfiable {κ : Type w} (G : κ → M → Prop) : Prop :=
  ¬ NonVacuous G ∧ ∀ S : κ → Prop, (∃ k, ¬ S k) → NonVacuous (restrict S G)

/-- The family `{H i | i : ι} ∪ {¬ C}`, indexed by `Option ι` (`none` is the negated
conclusion). The theorem holds exactly when this family is unsatisfiable. -/
def withNegatedConclusion (H : ι → M → Prop) (C : M → Prop) : Option ι → M → Prop
  | none => fun x => ¬ C x
  | some i => H i

/-- Sufficiency relative to a class of models `P` (the "intended" or reference class). -/
def SufficientIn (P : M → Prop) (H : ι → M → Prop) (C : M → Prop) : Prop :=
  ∀ x, P x → (∀ i, H i x) → C x

/-- Tightness relative to a class of models `P`: the witness must lie in `P`. -/
def TightIn (P : M → Prop) (H : ι → M → Prop) (C : M → Prop) (i : ι) : Prop :=
  ∃ x, P x ∧ (∀ j, j ≠ i → H j x) ∧ ¬ C x

/-- Non-vacuity relative to a class of models `P`: some model in `P` satisfies all
hypotheses. -/
def NonVacuousIn (P : M → Prop) (H : ι → M → Prop) : Prop :=
  ∃ x, P x ∧ ∀ i, H i x

/-- Hypothesis `i` is *harmless* relative to `P`: it holds throughout the class `P`, so
over `P` it can be dropped without changing anything. This is pointwise truth on `P`; it
does not model changes of signature (extra binders, instance arguments). -/
def HarmlessIn (P : M → Prop) (H : ι → M → Prop) (i : ι) : Prop :=
  ∀ x, P x → H i x

/-- Replace hypothesis `i` of `H` by the premise `H'`, keeping the others. Defined
propositionally, so no decidable equality on `ι` is needed. -/
def replaceAt (H : ι → M → Prop) (i : ι) (H' : M → Prop) : ι → M → Prop :=
  fun j x => (j = i → H' x) ∧ (j ≠ i → H j x)

/-- The weakest premise that can stand in place of hypothesis `i`: "if the other hypotheses
hold then the conclusion holds" (a relative pseudo-complement, or weakest sufficient
condition, of `C` with respect to the other hypotheses). -/
def WeakestPremise (H : ι → M → Prop) (C : M → Prop) (i : ι) : M → Prop :=
  fun x => (∀ j, j ≠ i → H j x) → C x

@[simp] theorem replaceAt_self (H : ι → M → Prop) (i : ι) (H' : M → Prop) (x : M) :
    replaceAt H i H' i x ↔ H' x :=
  ⟨fun h => h.1 rfl, fun h => ⟨fun _ => h, fun hne => absurd rfl hne⟩⟩

theorem replaceAt_of_ne (H : ι → M → Prop) {i j : ι} (H' : M → Prop) (hj : j ≠ i) (x : M) :
    replaceAt H i H' j x ↔ H j x :=
  ⟨fun h => h.2 hj, fun h => ⟨fun he => absurd he hj, fun _ => h⟩⟩

/-- With decidable equality on `ι`, `replaceAt` agrees with the `if`-then-`else` form. -/
theorem replaceAt_iff_ite [DecidableEq ι] (H : ι → M → Prop) (i : ι) (H' : M → Prop)
    (j : ι) (x : M) : replaceAt H i H' j x ↔ (if j = i then H' else H j) x := by
  by_cases h : j = i
  · subst h; simp
  · simp [h, replaceAt_of_ne H H' h]

end Basic

/-! ## Small index types for examples -/

/-- Index type for families of two hypotheses. -/
inductive Two where
  | h1
  | h2
  deriving DecidableEq, Repr

/-- Index type for families of three hypotheses. -/
inductive Three where
  | h1
  | h2
  | h3
  deriving DecidableEq, Repr

/-- The one-hypothesis family consisting of `A`. -/
def single {M : Type u} (A : M → Prop) : Unit → M → Prop :=
  fun _ => A

/-- The two-hypothesis family `[A, B]`. -/
def pair {M : Type u} (A B : M → Prop) : Two → M → Prop
  | .h1 => A
  | .h2 => B

/-- The three-hypothesis family `[A, B, D]`. -/
def triple {M : Type u} (A B D : M → Prop) : Three → M → Prop
  | .h1 => A
  | .h2 => B
  | .h3 => D

section IndexLemmas

variable {M : Type u}

@[simp] theorem single_apply (A : M → Prop) (j : Unit) : single A j = A := rfl
@[simp] theorem pair_h1 (A B : M → Prop) : pair A B .h1 = A := rfl
@[simp] theorem pair_h2 (A B : M → Prop) : pair A B .h2 = B := rfl
@[simp] theorem triple_h1 (A B D : M → Prop) : triple A B D .h1 = A := rfl
@[simp] theorem triple_h2 (A B D : M → Prop) : triple A B D .h2 = B := rfl
@[simp] theorem triple_h3 (A B D : M → Prop) : triple A B D .h3 = D := rfl

@[simp] theorem Two.forall_iff {P : Two → Prop} : (∀ j, P j) ↔ P .h1 ∧ P .h2 :=
  ⟨fun h => ⟨h .h1, h .h2⟩, fun ⟨a, b⟩ j => by cases j <;> assumption⟩

@[simp] theorem Two.exists_iff {P : Two → Prop} : (∃ j, P j) ↔ P .h1 ∨ P .h2 :=
  ⟨fun ⟨j, hj⟩ => by cases j <;> simp_all, fun h => h.elim (⟨_, ·⟩) (⟨_, ·⟩)⟩

@[simp] theorem Three.forall_iff {P : Three → Prop} :
    (∀ j, P j) ↔ P .h1 ∧ P .h2 ∧ P .h3 :=
  ⟨fun h => ⟨h .h1, h .h2, h .h3⟩, fun ⟨a, b, c⟩ j => by cases j <;> assumption⟩

@[simp] theorem Unit.forall_iff' {P : Unit → Prop} : (∀ j, P j) ↔ P () :=
  ⟨fun h => h (), fun h j => by cases j; exact h⟩

end IndexLemmas

end Toy.Ledger
