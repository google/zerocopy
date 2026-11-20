/-!
# Predicate transformers and relational semantics: definitions

A toy model of weakest-precondition semantics over an arbitrary state type `σ`.

* A *predicate* is a function `σ → Prop`; a *predicate transformer* maps postconditions to
  preconditions.
* A *relational program* is a relation `R : σ → σ → Prop` ("`s'` is a possible final state from
  initial state `s`") together with a predicate `term : σ → Prop`, the *non-abortion domain*
  ("from `s` the program does not abort or possibly diverge").  `term s` does not by itself
  promise a final state: at a state in `term` with no `R`-successor the program is
  *miraculous*.  Guaranteed normal termination in some final state is `term s` together with
  `∃ s', R s s'` (see `TotalOn`).

Every law a verification framework might demand of a `wp` is a separate named `Prop`, so that
theorems can name exactly the laws they use.

Predicates are compared extensionally: with `propext` and `funext`, two predicates that hold
of the same states are equal, so every transformer (being a function) automatically respects
logical equivalence of postconditions.  No separate congruence law is needed or stated.
-/

namespace Toy.PredTrans

universe u

/-- A state predicate: a property of states, used for pre- and postconditions. -/
abbrev Pred (σ : Type u) : Type u := σ → Prop

/-- A predicate transformer: maps a postcondition to a precondition.  This is the type of a
candidate weakest-precondition semantics `wp c : Transformer σ` of a single program `c`. -/
abbrev Transformer (σ : Type u) : Type u := Pred σ → Pred σ

/-- A binary relation on states.  `R s s'` reads "`s'` is a possible final state of the program
started in `s`".  A relation may be nondeterministic (several `s'`), partial (no `s'`), or
both. -/
abbrev Rel (σ : Type u) : Type u := σ → σ → Prop

variable {σ : Type u}

/-! ## Semantics: from relations to transformers -/

/-- `wlp R Q s` holds when every possible final state from `s` satisfies `Q`.

Two readings of this transformer are standard and both are covered:
* the *weakest liberal precondition* (partial correctness) of the relation `R`; here a state
  with no `R`-successor models guaranteed divergence, and `wlp R Q` holds there for every `Q`
  (including `False`);
* the *demonic update* `[R]` of the refinement calculus, i.e. the total-correctness `wp` of
  the never-aborting program with outcome relation `R` (`wlp R = wp R (fun _ => True)`,
  `wlp_eq_wp_true`); here a state with no `R`-successor is a miracle.

A paired `(wp, wlp)` semantics of a possibly aborting program is not modeled. -/
def wlp (R : Rel σ) : Transformer σ := fun Q s => ∀ s', R s s' → Q s'

/-- Weakest precondition (total correctness) of the relational program `(R, term)`: the
program started in `s` does not abort (`term s`) and every possible final state satisfies `Q`.
States outside `term` model abortion or possible divergence: there `wp R term Q` is false for
every `Q`, whatever `R` says.  `term s` alone does not guarantee a final state: if `s` has no
`R`-successor, `wp R term Q s` holds for every `Q` (a miracle).  In refinement-calculus
notation `wp R term` is the assertion followed by the demonic update, `{term} ; [R]`. -/
def wp (R : Rel σ) (term : Pred σ) : Transformer σ := fun Q s => term s ∧ wlp R Q s

/-! ## Healthiness laws, each a separate proposition -/

/-- Monotonicity: a weaker postcondition has a weaker precondition. -/
def Monotone (T : Transformer σ) : Prop :=
  ∀ P Q : Pred σ, (∀ t, P t → Q t) → ∀ s, T P s → T Q s

/-- Universal conjunctivity: `T` distributes over the conjunction of *every* family of
postconditions indexed by a type in the universe of the state type, including the empty
family (whose conjunction is the everywhere-true predicate) and infinite families.  The
universe restriction loses nothing: `conjAll_iff_set`, `conjAll_arbitrary_sort`. -/
def ConjAll (T : Transformer σ) : Prop :=
  ∀ (ι : Type u) (Q : ι → Pred σ) (s : σ), T (fun t => ∀ i, Q i t) s ↔ ∀ i, T (Q i) s

/-- Positive conjunctivity: `T` distributes over the conjunction of every *nonempty* family
of postconditions (finite or infinite) indexed by a type in the universe of the state type.
Unlike `ConjAll`, this does not force `T (fun _ => True)` to hold.  The universe restriction
loses nothing: `conjNonempty_iff_set`, `conjNonempty_arbitrary_sort`. -/
def ConjNonempty (T : Transformer σ) : Prop :=
  ∀ (ι : Type u) (Q : ι → Pred σ), Nonempty ι →
    ∀ s : σ, T (fun t => ∀ i, Q i t) s ↔ ∀ i, T (Q i) s

/-- Binary conjunctivity: `T (P ∧ Q) = T P ∧ T Q`.  This is the conjunctivity law of
Dijkstra's original healthiness conditions.  It gives conjunctivity over every *nonempty*
finite list of postconditions; the empty list needs `TopPreserving` in addition
(`conjList_of_conjBin_of_topPreserving`). -/
def ConjBin (T : Transformer σ) : Prop :=
  ∀ (P Q : Pred σ) (s : σ), T (fun t => P t ∧ Q t) s ↔ T P s ∧ T Q s

/-- Strictness, also called the law of the excluded miracle: no state can establish the
unsatisfiable postcondition, `T False = False`. -/
def Strict (T : Transformer σ) : Prop := ∀ s, ¬ T (fun _ => False) s

/-- Top preservation: the trivial postcondition is established from every state,
`T True = True`.  For a `wp` this says the program never aborts or diverges. -/
def TopPreserving (T : Transformer σ) : Prop := ∀ s, T (fun _ => True) s

/-- An increasing `Nat`-indexed chain of predicates: `Q 0 ⊆ Q 1 ⊆ Q 2 ⊆ ⋯`. -/
def Chain (Q : Nat → Pred σ) : Prop := ∀ n s, Q n s → Q (n + 1) s

/-- ω-continuity, *one-sided form*: if `T` establishes the union of an increasing chain, it
already establishes some member of the chain.

This is only the upper half of the usual continuity equation
`T (⋃ₙ Qₙ) = ⋃ₙ T Qₙ`; the other inclusion is an instance of `Monotone`.  The two-sided
equation is equivalent to `Monotone T ∧ OmegaContinuous T` (`omegaContinuous_two_sided_iff`).
On its own the one-sided law does **not** imply monotonicity: every antitone transformer
satisfies it, for example pointwise negation (`omegaContinuous_negT_not_monotone`).  Every use
in this package pairs it with a law that implies monotonicity (`ConjBin`, or being a `wp`),
where the one-sided and two-sided forms coincide. -/
def OmegaContinuous (T : Transformer σ) : Prop :=
  ∀ Q : Nat → Pred σ, Chain Q → ∀ s, T (fun t => ∃ n, Q n t) s → ∃ n, T (Q n) s

/-- A directed family of predicates, indexed by a type in the universe of the state type:
nonempty, and any two members are contained in a third. -/
def Directed {ι : Type u} (Q : ι → Pred σ) : Prop :=
  Nonempty ι ∧ ∀ i j, ∃ k, (∀ s, Q i s → Q k s) ∧ (∀ s, Q j s → Q k s)

/-- Continuity over directed families, one-sided form: if `T` establishes the union of a
directed family, it already establishes some member.  Every increasing chain is directed, so
this implies `OmegaContinuous` (`omegaContinuous_of_dirContinuous`).  Like
`OmegaContinuous`, it does not by itself imply monotonicity. -/
def DirContinuous (T : Transformer σ) : Prop :=
  ∀ (ι : Type u) (Q : ι → Pred σ), Directed Q →
    ∀ s, T (fun t => ∃ i, Q i t) s → ∃ i, T (Q i) s

/-! ## From transformers back to relations -/

/-- The relation read off from a transformer: `s'` is a possible outcome from `s` exactly when
`s'` satisfies every postcondition that `T` establishes from `s`.  Equivalently, for monotone
`T` (classically), `T` cannot guarantee from `s` that the final state differs from `s'`
(`relOf_iff_not_avoids_of_monotone`). -/
def relOf (T : Transformer σ) : Rel σ := fun s s' => ∀ Q : Pred σ, T Q s → Q s'

/-- The non-abortion domain read off from a transformer: the states from which `T`
establishes the trivial postcondition.  For `wp R term` this is `term` (`termOf_wp`).  It
includes miraculous states (states with no possible outcome), so it is not "the states from
which a final state is guaranteed" unless `T` is strict. -/
def termOf (T : Transformer σ) : Pred σ := T (fun _ => True)

/-! ## Properties of relational programs -/

/-- The image of `s` under `R` is finite: all `R`-successors of `s` occur in one list.
This is the model of *bounded nondeterminism* at `s`.  It bounds the set of final states of
the input/output relation, not the branching of any operational transition system. -/
def FiniteImage (R : Rel σ) (s : σ) : Prop := ∃ l : List σ, ∀ s', R s s' → s' ∈ l

/-- `R` has at least one successor at every state satisfying `term`: the program has no
*miracle* (a non-aborting start state with no possible outcome). -/
def TotalOn (R : Rel σ) (term : Pred σ) : Prop := ∀ s, term s → ∃ s', R s s'

/-- Chaos normal form of a relational program: every state outside `term` is related to every
state.  ("An aborting program may do anything.")  Among all pairs `(R, term)` with the same
`wp`, exactly one is in this form (`conjNonempty_iff_exists_unique_chaosNormal_wp`). -/
def ChaosNormal (R : Rel σ) (term : Pred σ) : Prop := ∀ s, ¬ term s → ∀ s', R s s'

/-- Refinement of transformers: `RefinedBy T₁ T₂` ("`T₁ ⊑ T₂`") holds when every
precondition/postcondition guarantee offered by `T₁` is also offered by `T₂`.  This is the
total-correctness refinement order of the refinement calculus. -/
def RefinedBy (T₁ T₂ : Transformer σ) : Prop := ∀ Q s, T₁ Q s → T₂ Q s

/-- The countable-state hypothesis: the state type injects into `Nat`.  Finite and empty
state types satisfy it. -/
def CountableState (σ : Type u) : Prop := ∃ f : σ → Nat, ∀ x y, f x = f y → x = y

/-- The continuum-state hypothesis: the state type injects into the type `Nat → Bool` of
infinite bit sequences (cardinality at most that of the continuum).  Every countable state
type satisfies it (`continuumState_of_countableState`), and so does `Nat → Bool` itself, which
is not countable. -/
def ContinuumState (σ : Type u) : Prop :=
  ∃ f : σ → Nat → Bool, ∀ x y, f x = f y → x = y

/-- The finite-state hypothesis: all states occur in one list.  The empty state type
satisfies it. -/
def FiniteState (σ : Type u) : Prop := ∃ l : List σ, ∀ x : σ, x ∈ l

/-! ## Program algebra on relations -/

/-- Relational (sequential) composition: first `R₁`, then `R₂`. -/
def comp (R₁ R₂ : Rel σ) : Rel σ := fun s s'' => ∃ s', R₁ s s' ∧ R₂ s' s''

/-- Non-abortion domain of a sequential composition: the first program does not abort and the
second does not abort from any possible intermediate state.  Definitionally this is
`wp R₁ t₁ t₂` (`seqTerm_eq_wp`); it is named separately only for readability. -/
def seqTerm (R₁ : Rel σ) (t₁ t₂ : Pred σ) : Pred σ := fun s => t₁ s ∧ ∀ s', R₁ s s' → t₂ s'

/-- Union of relations: demonic (adversarial) choice between two programs. -/
def union (R₁ R₂ : Rel σ) : Rel σ := fun s s' => R₁ s s' ∨ R₂ s s'

/-! ## Angelic/demonic normal form for monotone transformers -/

/-- The transformer of a *multirelation* `A`: from `s` the angel picks a set `P` of states with
`A s P`, then the demon picks a final state in `P`.  `Q` is established when the angel has a
choice all of whose outcomes satisfy `Q`. -/
def angelicDemonic (A : σ → Pred σ → Prop) : Transformer σ :=
  fun Q s => ∃ P, A s P ∧ ∀ t, P t → Q t

/-- The multirelation read off from a transformer: `P` is available at `s` when `T`
establishes `P` from `s`. -/
def multirelOf (T : Transformer σ) : σ → Pred σ → Prop := fun s P => T P s

/-- Up-closure of a multirelation: any superset of an available set is available. -/
def UpClosed (A : σ → Pred σ → Prop) : Prop :=
  ∀ s (P P' : Pred σ), A s P → (∀ t, P t → P' t) → A s P'

end Toy.PredTrans
