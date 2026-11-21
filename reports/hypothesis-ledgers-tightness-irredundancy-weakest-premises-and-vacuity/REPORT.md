# Hypothesis ledgers: tightness, irredundancy, weakest premises, and vacuity

## Summary

This package is a Lean 4 mechanization (core Lean, no Mathlib) of the vocabulary used to say what a *hypothesis ledger* asserts. A theorem has the shape "for every model `x`, if every hypothesis `H i x` holds then `C x`" (`Sufficient H C`); its ledger labels each hypothesis, and comes with a *non-vacuity witness*. In this package: hypothesis `i` is **tight** (`TightAt H C i`) when some model satisfies every *other* hypothesis and violates `C`; the family is **irredundant** when every hypothesis is tight; it is **non-vacuous** when some model satisfies all hypotheses; hypothesis `i` is **necessary** when every model of `C` satisfies it, and **unweakenable** when it holds wherever the other hypotheses and `C` hold; the **weakest premise** for `i` is "if the other hypotheses hold then `C`". All 28 results below are kernel-checked; no declaration uses `sorry`, and the only axioms that occur are `propext`, `Classical.choice` and `Quot.sound`.

One sentence per result, with its key hypotheses (`H : ι → M → Prop` is a hypothesis family over a model type `M`, `C : M → Prop` a conclusion, `i : ι` an index; the running examples are concrete families over `Nat`, `Nat × Nat`, `Fin 3`, `Bool × Bool` and `Unit`):

1. **tightAt_iff_witness_violates_exactly_i_of_sufficient.** If the hypotheses `H` suffice for `C`, then every model that satisfies every hypothesis other than `i` and violates `C` also violates `H i`, and hypothesis `i` is tight exactly when some model satisfies every other hypothesis and violates both `H i` and `C`.
2. **tightAt_iff_not_sufficient_without.** For any `H`, `C` and `i`, with no sufficiency assumption: hypothesis `i` is tight exactly when the family with `H i` deleted is not sufficient for `C`.
3. **irredundant_iff_no_proper_subfamily_sufficient.** For any `H` and `C`: every hypothesis is tight exactly when no proper subfamily of `H` (one omitting at least one hypothesis, possibly many) is sufficient for `C`.
4. **sufficient_irredundant_nonVacuous_iff_minimalUnsatisfiable.** For any `H` and `C`: the theorem holds, every hypothesis is tight and the hypotheses are jointly satisfiable exactly when the family `{H i | i}` together with `¬ C` is minimally unsatisfiable.
5. **irredundance_independence_isolation_countermodels.** Irredundancy, full independence and isolation are distinct: `x ≥ 1, x ≤ 1 ⊢ x = 1` over `Nat` is sufficient, irredundant and non-vacuous but not independent; two coordinate bits over `Bool × Bool` with the conclusion `True` are sufficient, non-vacuous and independent, and no hypothesis is tight; and `x ≥ 1, x ≤ 1 ⊢ x ≤ 1` over `Nat` is sufficient and non-vacuous, and its hypothesis `x ≥ 1` has an isolating model but is not tight.
6. **isolatingAt_of_tightAt_of_sufficient.** If the hypotheses `H` suffice for `C` and hypothesis `i` is tight, then hypothesis `i` has an isolating model (one violating `H i` and satisfying every other hypothesis).
7. **unweakenableAt_of_necessaryAt.** If every model of `C` satisfies `H i` (global necessity), then `H i` holds wherever the other hypotheses and `C` hold (unweakenability).
8. **tight_necessary_unweakenable_six_combinations.** At hypothesis `h1` of sufficient, non-vacuous two-hypothesis instances over `Nat` or `Nat × Nat`, all six combinations of (tight, necessary, unweakenable) compatible with 'necessary implies unweakenable' occur: TNU `x ≥ 1, x ≤ 1 ⊢ x = 1`; not-T NU `x = 1, x = 1 ⊢ x = 1`; T not-N not-U `x ≤ 1, y ≤ 1 ⊢ x + y ≤ 2`; not-T not-N not-U `x ≥ 1, x ≤ 1 ⊢ x ≤ 1`; T not-N U `x = 0, y = 0 ⊢ x = y`; not-T not-N U `x = 0, (x = 0 ∧ y = 0) ⊢ x = y`.
9. **unweakenableAt_and_not_tightAt_iff_entailed_by_others_of_sufficient.** If the hypotheses `H` suffice for `C`, then hypothesis `i` is unweakenable and not tight exactly when the other hypotheses entail `H i`.
10. **weakestPremise_is_weakest_replacement.** For any `H`, `C` and `i`: replacing `H i` by a premise `H'` keeps sufficiency exactly when `H'` implies `WeakestPremise H C i` ('if the other hypotheses hold then `C`'); that premise is itself a valid replacement; the theorem holds exactly when `H i` implies it; and `i` is not tight exactly when it holds at every model.
11. **unweakenableAt_characterizations_of_sufficient.** If the hypotheses `H` suffice for `C`, then hypothesis `i` is unweakenable exactly when `H i` agrees with `WeakestPremise H C i` wherever the other hypotheses hold, exactly when every weakening of `H i` that keeps the theorem true agrees with `H i` wherever the other hypotheses hold, and exactly when `H i` agrees with `C` wherever the other hypotheses hold.
12. **irredundant_sufficient_subfamilies_of_sizes_two_and_one.** Over the vocabulary `x ≤ 1, y ≤ 1, x + y ≤ 2` on `Nat × Nat` with the conclusion `x + y ≤ 2`, both the subfamily `{x ≤ 1, y ≤ 1}` and the subfamily `{x + y ≤ 2}` are sufficient, irredundant and non-vacuous.
13. **subfamily_eq_of_sufficient_of_irredundant_superfamily.** If the subfamily of a vocabulary `H` selected by `S` is sufficient for `C`, the subfamily selected by `T` is irredundant for `C`, and `S ⊆ T`, then `S = T`.
14. **irredundant_vacuous_and_nonvacuous_tightless.** On `Fin 3`, `x = 1, x = 2 ⊢ False` is sufficient and irredundant but vacuous (and its family with the negated conclusion is not minimally unsatisfiable); over `Unit`, `True ⊢ True` is sufficient and non-vacuous but its hypothesis is not tight.
15. **not_valid_of_tightAt.** If hypothesis `i` is tight for `C`, then `C` is not valid over the model type.
16. **schematic_ledger_irredundant_nonvacuous.** The schema `P ∨ C, ¬ P ⊢ C` is sufficient for every instantiation of `P` and `C` over every model type, yet its instance with `P x := (x.1 = true)` and `C x := (x.2 = true)` over `Bool × Bool` is irredundant and non-vacuous.
17. **not_single_entails_of_irredundant_of_exists_other.** If every hypothesis of `H` is tight for `C` and some hypothesis other than `i` exists, then `H i` alone does not entail `C` over the whole model type.
18. **sufficientIn_antitone_and_tightIn_monotone.** For classes of models `P ⊆ Q`: sufficiency over `Q` gives sufficiency over `P`, and for every index, tightness over `P` gives tightness over `Q`.
19. **tightIn_all_models_harmlessIn_bounded.** For `x ≥ 1, x ≤ 1 ⊢ x = 1`, which holds over all naturals and over the class `x ≤ 1` and is non-vacuous over that class, the hypothesis `x ≤ 1` is tight over all naturals, harmless over the class, and not tight over the class.
20. **not_harmlessIn_of_tightIn_of_sufficientIn.** If the hypotheses `H` suffice for `C` over a class `P` and hypothesis `i` is tight over `P`, then `H i` is not harmless over `P`.
21. **sufficient_conjunction_iff_each_and_tightAt_conjunction_iff_some.** For a fixed family `H`: a hypothesis is tight for `C₁ ∧ C₂` exactly when it is tight for `C₁` or for `C₂`; for any family of conclusions `D k`, `H` suffices for all of them exactly when it suffices for each, and a hypothesis is tight for their conjunction exactly when it is tight for some `D k`.
22. **tight_for_conjunction_not_for_conjunct.** In `x ≤ 1, y ≤ 1 ⊢ x ≤ 1 ∧ y ≤ 1` over `Nat × Nat` (jointly satisfiable hypotheses that suffice for the conjunction), the hypothesis `x ≤ 1` is tight for the conjunction, the hypotheses suffice for the conjunct `y ≤ 1`, and `x ≤ 1` is not tight for `y ≤ 1`.
23. **check_of_cell_empty.** For any table, property `Q` and cell `(r, k)`: if the cell has no model, the ✓ at `(r, k)` holds.
24. **all_checks_with_every_cell_empty.** In the table over `Nat` with every cell empty, every cell carries a ✓ even for the unsatisfiable property `False`, and no ✓ is informative.
25. **classify_sound.** For every finite list `univ`, `Bool`-valued table, `Bool`-valued property and cell, the verdict of `classify` satisfies: if its status is `witnessedOnUniv`, the model it carries lies in the cell and has the property, and every member of `univ` in the cell has the property; if `emptyOnUniv`, no member of `univ` is in the cell; if `foundCounterexample`, the model it carries lies in the cell and lacks the property.
26. **classify_complete.** If the list `univ` lists every model, the status of `classify` for a cell of a `Bool`-valued table is `witnessedOnUniv` exactly when the cell carries an informative ✓, `emptyOnUniv` exactly when it carries a ✓ and has no model, and `foundCounterexample` exactly when it carries no ✓.
27. **auditLedger_sound.** For every finite list `univ`, `Bool`-valued hypotheses `H` indexed by `Fin m` and `Bool`-valued conclusion `C`, every model shown in the summary of `auditLedger univ H C` is genuine over the whole model type (a counterexample, tightness witness, satisfying model or weakening witness, as labelled), and every `noWitness` entry asserts the corresponding universal property restricted to the members of `univ`.
28. **auditLedger_complete.** If the list `univ` lists every model, then for `Bool`-valued hypotheses `H` indexed by `Fin m` and `Bool`-valued conclusion `C`, each entry of the summary of `auditLedger univ H C` is `noWitness` exactly when the corresponding property holds over the whole model type: sufficiency, non-tightness of `i`, unsatisfiability of the hypotheses, unweakenability of `i`.

Every hypothesis of every result is `tight` in the ledger sense used here (a kernel-checked counterexample theorem, in a stated witness class, in which all the other hypotheses hold and the conclusion fails), and every result has a kernel-checked non-vacuity witness (for the concrete-instance results, the statement itself). What each result does *not* establish is listed first under **Boundaries**; read it before relying on a result.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

## Applicability

### Model fidelity

This is a toy, generic formal theory; it is not a mechanization of any particular prover's statement language or of any particular published ledger. A *model type* `M` is an arbitrary Lean type. A *hypothesis family* is `H : ι → M → Prop` for an arbitrary index type `ι` (the index types used are `Unit`, the two- and three-element types `Two` and `Three`, `Fin m`, `Nat`, `Option ι` and subtypes; no decidable equality on `ι` is assumed by the general results). A *conclusion* is `C : M → Prop`. "The theorem" means the semantic statement `Sufficient H C` over `M`, not a proof object.

The definitions are meant to capture: the ledgers that accompany published formal results (a label per hypothesis and a non-vacuity witness); the classical notions they are often conflated with (Hilbert-style independence of an axiom, full independence, global necessity, inclusion-minimality, minimal unsatisfiable subsets, subset-minimal abductive explanations, weakest sufficient conditions, antecedent-failure vacuity); ✓ entries of soundness tables; and a small executable audit over a finite list of models. Known gaps:

- **Non-dependent hypotheses.** Each `H j x` is a proposition about `x` alone. A Lean theorem whose later binders mention proofs of earlier ones fits this theory after each such hypothesis is turned into a predicate on `x`, and the choice of predicate changes which hypotheses are tight (non-claims of results 1 and 2).
- **Semantic, not syntactic.** Tightness, necessity and unweakenability are statements about models, not about proofs. Their relation to unused-argument linters is a separate `derived (modeling bridge)` claim (result 2, **Modeling bridge** below).
- **`HarmlessIn` is pointwise truth on a class.** Changes of signature (extra binders, instance arguments) are not modeled.
- **Vacuity.** `NonVacuous H` is satisfiability of the antecedent. The "every subformula affects the truth value" notion from temporal-logic model checking and the "antecedent always holds" check are different notions (result 14).
- **Executable procedures.** `classify` and `auditLedger` take `Bool`-valued predicates and a finite list `univ : List M`. Every model a verdict carries is genuine over the whole model type for every `univ` (results 25 and 27); the verdicts that carry no model, and the ✓ part of `witnessedOnUniv`, speak about the members of `univ`, and become statements about the whole model type when `univ` lists every model (results 26 and 28).
- **Classical logic.** Several proofs use excluded middle (recorded per result in the non-claims and per theorem under **Evidence**); no axioms beyond the standard `propext`, `Classical.choice`, `Quot.sound` occur.

Proved model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about specific published theorems, proof assistants, linters, model checkers or soundness tables. Every connection to such systems is stated separately as `derived (modeling bridge)`, with its reasoning.

### Relationship of the subjects

The Lean 4 toolchain release in `REPORT.json` is the checker of every theorem. The other subjects are prior art: papers, a book, and source files at fixed commits of `leanprover/lean4`, `leanprover-community/batteries` and `leanprover-community/mathlib4`. Each card states which passage it relates to and how; no result depends on them, and nothing is imported from Mathlib or Batteries.

### Lean version and project

Lean 4 `v4.34.1` (`leanprover/lean4`, tag `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`), core Lean with no Mathlib, no Batteries and no `[[require]]`. The Lake project is `lean/` (package `hypothesis_ledgers`, one library `Toy`). Modules: `Toy/Ledger/Core.lean` (definitions), `Examples.lean` (running examples and definition tests), `Witnesses.lean` (what `tight` and all-`tight` ledgers mean), `Strength.lean` (tight, necessary, unweakenable; weakest premises), `Families.lean` (non-uniqueness, vacuity, depth, restated conclusions), `Classes.lean` (reference classes, conjunctions), `Tables.lean` (empty table cells, the classifier `classify`), `Audit.lean` (the ledger audit `auditLedger`), `SupportingLemmas.lean` (supporting lemmas for the ledger of result 11 and for the comparison with Beatty and Bryant's antecedent check on results 14 and 23). All results are in the namespace `Toy.Ledger`.

## Findings

### Reading conventions

- Statements are quoted verbatim from the Lean sources, each fence starting with its `file:line` range; a quote may stop before the proof (`:= …`). Where a card adds a rendering with definitions replaced by their bodies, that rendering is a Lean term that elaborates in the theorem's context (after its leading binders) and is definitionally equal to the rest of the statement.
- In a hypothesis ledger, **tight** means: the named counterexample is a kernel-checked theorem stating that all the other hypotheses hold and the conclusion fails, for an instance in the stated witness class. It shows that the hypothesis cannot be dropped within that class. It does not show that the hypothesis is necessary for the conclusion or cannot be weakened (result 8).
- A **non-vacuity witness** is a kernel-checked theorem stating that all hypotheses of the result hold for a concrete instance (for a result without hypotheses, that both sides of each equivalence hold, or that the concrete instance is as stated).
- `Basis: execution (Lean kernel check)` marks kernel-checked statements. Claims about real systems are separate and marked `Basis: derived (modeling bridge)`.

### Definitions

Core vocabulary (`lean/Toy/Ledger/Core.lean`; the section variables are `{M : Type u} {ι : Type v}`), verbatim:

```lean
-- lean/Toy/Ledger/Core.lean:33-34
def Sufficient (H : ι → M → Prop) (C : M → Prop) : Prop :=
  ∀ x, (∀ i, H i x) → C x
-- lean/Toy/Ledger/Core.lean:42-43
def TightAt (H : ι → M → Prop) (C : M → Prop) (i : ι) : Prop :=
  ∃ x, (∀ j, j ≠ i → H j x) ∧ ¬ C x
-- lean/Toy/Ledger/Core.lean:47-48
def Irredundant (H : ι → M → Prop) (C : M → Prop) : Prop :=
  ∀ i, TightAt H C i
-- lean/Toy/Ledger/Core.lean:55-56
def NonVacuous (H : ι → M → Prop) : Prop :=
  ∃ x, ∀ i, H i x
-- lean/Toy/Ledger/Core.lean:60-61
def NecessaryAt (H : ι → M → Prop) (C : M → Prop) (i : ι) : Prop :=
  ∀ x, C x → H i x
-- lean/Toy/Ledger/Core.lean:68-69
def UnweakenableAt (H : ι → M → Prop) (C : M → Prop) (i : ι) : Prop :=
  ∀ x, (∀ j, j ≠ i → H j x) → C x → H i x
-- lean/Toy/Ledger/Core.lean:73-74
def Independent (H : ι → M → Prop) : Prop :=
  ∀ s : ι → Bool, ∃ x, ∀ i, (H i x ↔ s i = true)
-- lean/Toy/Ledger/Core.lean:78-79
def IsolatingAt (H : ι → M → Prop) (i : ι) : Prop :=
  ∃ x, ¬ H i x ∧ ∀ j, j ≠ i → H j x
-- lean/Toy/Ledger/Core.lean:82-83
def restrict (S : ι → Prop) (H : ι → M → Prop) : Subtype S → M → Prop :=
  fun j => H j.1
-- lean/Toy/Ledger/Core.lean:88-89
def MinimalUnsatisfiable {κ : Type w} (G : κ → M → Prop) : Prop :=
  ¬ NonVacuous G ∧ ∀ S : κ → Prop, (∃ k, ¬ S k) → NonVacuous (restrict S G)
-- lean/Toy/Ledger/Core.lean:93-95
def withNegatedConclusion (H : ι → M → Prop) (C : M → Prop) : Option ι → M → Prop
  | none => fun x => ¬ C x
  | some i => H i
-- lean/Toy/Ledger/Core.lean:98-99
def SufficientIn (P : M → Prop) (H : ι → M → Prop) (C : M → Prop) : Prop :=
  ∀ x, P x → (∀ i, H i x) → C x
-- lean/Toy/Ledger/Core.lean:102-103
def TightIn (P : M → Prop) (H : ι → M → Prop) (C : M → Prop) (i : ι) : Prop :=
  ∃ x, P x ∧ (∀ j, j ≠ i → H j x) ∧ ¬ C x
-- lean/Toy/Ledger/Core.lean:107-108
def NonVacuousIn (P : M → Prop) (H : ι → M → Prop) : Prop :=
  ∃ x, P x ∧ ∀ i, H i x
-- lean/Toy/Ledger/Core.lean:113-114
def HarmlessIn (P : M → Prop) (H : ι → M → Prop) (i : ι) : Prop :=
  ∀ x, P x → H i x
-- lean/Toy/Ledger/Core.lean:118-119
def replaceAt (H : ι → M → Prop) (i : ι) (H' : M → Prop) : ι → M → Prop :=
  fun j x => (j = i → H' x) ∧ (j ≠ i → H j x)
-- lean/Toy/Ledger/Core.lean:124-125
def WeakestPremise (H : ι → M → Prop) (C : M → Prop) (i : ι) : M → Prop :=
  fun x => (∀ j, j ≠ i → H j x) → C x
```

Table cells and the classifier (`lean/Toy/Ledger/Tables.lean`; section variables `{M : Type u} {R : Type v} {K : Type w}`), verbatim:

```lean
-- lean/Toy/Ledger/Tables.lean:27-28
def Check (cell : R → K → M → Prop) (Q : M → Prop) (r : R) (k : K) : Prop :=
  ∀ x, cell r k x → Q x
-- lean/Toy/Ledger/Tables.lean:32-33
def InformativeCheck (cell : R → K → M → Prop) (Q : M → Prop) (r : R) (k : K) : Prop :=
  Check cell Q r k ∧ ∃ x, cell r k x
-- lean/Toy/Ledger/Tables.lean:89
def liftPred {M : Type u} (q : M → Bool) : M → Prop := fun x => q x = true
-- lean/Toy/Ledger/Tables.lean:92-94
def liftTable {M : Type u} {R : Type v} {K : Type w} (cell : R → K → M → Bool) :
    R → K → M → Prop :=
  fun r k x => cell r k x = true
-- lean/Toy/Ledger/Tables.lean:96-97
theorem find?_eq_none_apply {α : Type u} {p : α → Bool} {l : List α}
    (h : l.find? p = none) {x : α} (hx : x ∈ l) : p x = false := by
-- lean/Toy/Ledger/Tables.lean:105-109
inductive CellVerdict {M : Type u} (univ : List M) (cell q : M → Bool) : Type u where
  | witnessedOnUniv (w : M) (hw : cell w = true ∧ q w = true)
      (hall : ∀ x, x ∈ univ → cell x = true → q x = true)
  | emptyOnUniv (hempty : ∀ x, x ∈ univ → cell x = false)
  | foundCounterexample (x : M) (hx : cell x = true ∧ q x = false)
-- lean/Toy/Ledger/Tables.lean:112-116
inductive CellStatus where
  | witnessedOnUniv
  | emptyOnUniv
  | foundCounterexample
  deriving DecidableEq, Repr
-- lean/Toy/Ledger/Tables.lean:123-127
def CellVerdict.status {univ : List M} {cell q : M → Bool} :
    CellVerdict univ cell q → CellStatus
  | .witnessedOnUniv .. => .witnessedOnUniv
  | .emptyOnUniv .. => .emptyOnUniv
  | .foundCounterexample .. => .foundCounterexample
-- lean/Toy/Ledger/Tables.lean:130-134
def CellVerdict.witness? {univ : List M} {cell q : M → Bool} :
    CellVerdict univ cell q → Option M
  | .witnessedOnUniv w .. => some w
  | .emptyOnUniv .. => none
  | .foundCounterexample x .. => some x
-- lean/Toy/Ledger/Tables.lean:137-154
def classifyCell (univ : List M) (cell q : M → Bool) : CellVerdict univ cell q :=
  match hf : univ.find? (fun x => cell x && !q x) with
  | some x => .foundCounterexample x (by
      have := List.find?_some hf
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
      exact this)
  | none =>
    match hw : univ.find? cell with
    | some w =>
      .witnessedOnUniv w ⟨List.find?_some hw, by
          have := find?_eq_none_apply hf (List.mem_of_find?_eq_some hw)
          simp [List.find?_some hw] at this
          exact this⟩
        (fun x hx hc => by
          have := find?_eq_none_apply hf hx
          simp [hc] at this
          exact this)
    | none => .emptyOnUniv (fun x hx => find?_eq_none_apply hw hx)
-- lean/Toy/Ledger/Tables.lean:162-167
def CellVerdict.Sound {univ : List M} {cell q : M → Bool} :
    CellVerdict univ cell q → Prop
  | .witnessedOnUniv w .. =>
      liftPred cell w ∧ liftPred q w ∧ ∀ x, x ∈ univ → liftPred cell x → liftPred q x
  | .emptyOnUniv .. => ∀ x, x ∈ univ → ¬ liftPred cell x
  | .foundCounterexample x .. => liftPred cell x ∧ ¬ liftPred q x
-- lean/Toy/Ledger/Tables.lean:171-172
theorem CellVerdict.sound {univ : List M} {cell q : M → Bool} (v : CellVerdict univ cell q) :
    v.Sound := by
-- lean/Toy/Ledger/Tables.lean:157-159
def classify (univ : List M) (cell : R → K → M → Bool) (q : M → Bool) (r : R) (k : K) :
    CellVerdict univ (cell r k) q :=
  classifyCell univ (cell r k) q
```

The ledger audit (`lean/Toy/Ledger/Audit.lean`; section variables `{M : Type u} {m : Nat}`), verbatim. Each search function scans `univ` with `List.find?` for the shown predicate; the first two lines of each are quoted (the rest builds the evidence the constructors carry):

```lean
-- lean/Toy/Ledger/Audit.lean:30-33
inductive Shown (M : Type u) where
  | noWitness
  | witness (x : M)
  deriving DecidableEq, Repr
-- lean/Toy/Ledger/Audit.lean:37-42
structure LedgerSummary (M : Type u) where
  sufficiency : Shown M
  tightness : List (Shown M)
  nonvacuity : Shown M
  weakening : List (Shown M)
  deriving DecidableEq, Repr
-- lean/Toy/Ledger/Audit.lean:49
def liftH (H : Fin m → M → Bool) : Fin m → M → Prop := fun i x => H i x = true
-- lean/Toy/Ledger/Audit.lean:52
def allB (H : Fin m → M → Bool) (x : M) : Bool := decide (∀ j, H j x = true)
-- lean/Toy/Ledger/Audit.lean:55-56
def othersB (H : Fin m → M → Bool) (i : Fin m) (x : M) : Bool :=
  decide (∀ j, j ≠ i → H j x = true)
-- lean/Toy/Ledger/Audit.lean:59-61
inductive SuffVerdict (univ : List M) (H : Fin m → M → Bool) (C : M → Bool) : Type u where
  | holdsOnUniv (h : ∀ x, x ∈ univ → allB H x = true → C x = true)
  | foundCounterexample (x : M) (hx : allB H x = true ∧ C x = false)
-- lean/Toy/Ledger/Audit.lean:64-67
inductive TightVerdict (univ : List M) (H : Fin m → M → Bool) (C : M → Bool) (i : Fin m) :
    Type u where
  | foundTightWitness (x : M) (hx : othersB H i x = true ∧ C x = false)
  | noTightWitnessOnUniv (h : ∀ x, x ∈ univ → othersB H i x = true → C x = true)
-- lean/Toy/Ledger/Audit.lean:70-72
inductive VacVerdict (univ : List M) (H : Fin m → M → Bool) : Type u where
  | foundSatisfyingModel (x : M) (hx : allB H x = true)
  | unsatisfiableOnUniv (h : ∀ x, x ∈ univ → allB H x = false)
-- lean/Toy/Ledger/Audit.lean:75-78
inductive WeakVerdict (univ : List M) (H : Fin m → M → Bool) (C : M → Bool) (i : Fin m) :
    Type u where
  | noWeakeningOnUniv (h : ∀ x, x ∈ univ → othersB H i x = true → C x = true → H i x = true)
  | foundWeakeningWitness (x : M) (hx : othersB H i x = true ∧ C x = true ∧ H i x = false)
-- lean/Toy/Ledger/Audit.lean:81-85
structure LedgerReport (univ : List M) (H : Fin m → M → Bool) (C : M → Bool) : Type u where
  sufficiency : SuffVerdict univ H C
  tightness : (i : Fin m) → TightVerdict univ H C i
  nonvacuity : VacVerdict univ H
  weakening : (i : Fin m) → WeakVerdict univ H C i
-- lean/Toy/Ledger/Audit.lean:88-90
def auditSufficiency (univ : List M) (H : Fin m → M → Bool) (C : M → Bool) :
    SuffVerdict univ H C :=
  match hf : univ.find? (fun x => allB H x && !C x) with
-- lean/Toy/Ledger/Audit.lean:101-103
def auditTightness (univ : List M) (H : Fin m → M → Bool) (C : M → Bool) (i : Fin m) :
    TightVerdict univ H C i :=
  match hf : univ.find? (fun x => othersB H i x && !C x) with
-- lean/Toy/Ledger/Audit.lean:114-116
def auditNonVacuity (univ : List M) (H : Fin m → M → Bool) : VacVerdict univ H :=
  match hf : univ.find? (fun x => allB H x) with
  | some x => .foundSatisfyingModel x (List.find?_some hf)
-- lean/Toy/Ledger/Audit.lean:120-122
def auditWeakening (univ : List M) (H : Fin m → M → Bool) (C : M → Bool) (i : Fin m) :
    WeakVerdict univ H C i :=
  match hf : univ.find? (fun x => othersB H i x && C x && !H i x) with
-- lean/Toy/Ledger/Audit.lean:133-138
def auditLedger (univ : List M) (H : Fin m → M → Bool) (C : M → Bool) :
    LedgerReport univ H C where
  sufficiency := auditSufficiency univ H C
  tightness := auditTightness univ H C
  nonvacuity := auditNonVacuity univ H
  weakening := auditWeakening univ H C
-- lean/Toy/Ledger/Audit.lean:143-146
def SuffVerdict.shown {univ : List M} {H : Fin m → M → Bool} {C : M → Bool} :
    SuffVerdict univ H C → Shown M
  | .holdsOnUniv .. => .noWitness
  | .foundCounterexample x .. => .witness x
-- lean/Toy/Ledger/Audit.lean:149-152
def TightVerdict.shown {univ : List M} {H : Fin m → M → Bool} {C : M → Bool} {i : Fin m} :
    TightVerdict univ H C i → Shown M
  | .foundTightWitness x .. => .witness x
  | .noTightWitnessOnUniv .. => .noWitness
-- lean/Toy/Ledger/Audit.lean:155-157
def VacVerdict.shown {univ : List M} {H : Fin m → M → Bool} : VacVerdict univ H → Shown M
  | .foundSatisfyingModel x .. => .witness x
  | .unsatisfiableOnUniv .. => .noWitness
-- lean/Toy/Ledger/Audit.lean:160-163
def WeakVerdict.shown {univ : List M} {H : Fin m → M → Bool} {C : M → Bool} {i : Fin m} :
    WeakVerdict univ H C i → Shown M
  | .noWeakeningOnUniv .. => .noWitness
  | .foundWeakeningWitness x .. => .witness x
-- lean/Toy/Ledger/Audit.lean:166-171
def LedgerReport.summary {univ : List M} {H : Fin m → M → Bool} {C : M → Bool}
    (r : LedgerReport univ H C) : LedgerSummary M where
  sufficiency := r.sufficiency.shown
  tightness := (List.finRange m).map fun i => (r.tightness i).shown
  nonvacuity := r.nonvacuity.shown
  weakening := (List.finRange m).map fun i => (r.weakening i).shown
```

Each core definition has a proved intended positive example and a proved intended negative example (all in `lean/Toy/Ledger/Examples.lean` unless noted):

| Definition | Meant to capture | Positive example | Negative example |
| :--- | :--- | :--- | :--- |
| `Sufficient` | the theorem holds over `M` | `sufficient_pin` | `not_sufficient_single_le_one` |
| `TightAt` | ledger label `tight` | `tightAt_pin_h1`, `tightAt_pin_h2` | `not_tightAt_pinWeak_h1` |
| `Irredundant` | an all-`tight` ledger | `irredundant_pin` | `not_irredundant_dup` |
| `NonVacuous` | non-vacuity witness (satisfiable antecedent) | `nonVacuous_pin` | `not_nonVacuous_vac` |
| `NecessaryAt` | "`H i` is necessary for `C`" | `necessaryAt_pin_h1` | `not_necessaryAt_sum_h1` |
| `UnweakenableAt` | "`H i` cannot be weakened" (arbitrary premises) | `unweakenableAt_pin_h1` | `not_unweakenableAt_sum_h1` |
| `Independent` | all truth patterns realized | `independent_bits` | `not_independent_pin` |
| `IsolatingAt` | one-model-per-axiom independence | `isolatingAt_pin_h1` | `not_isolatingAt_dup_h1` |
| `restrict` | a subfamily | `sufficient_restrict_sumVocab_h1h2` | `not_sufficient_restrict_sumVocab_h1` |
| `MinimalUnsatisfiable`, `withNegatedConclusion` | minimal unsatisfiable subset of `{H i} ∪ {¬ C}` | `minimalUnsatisfiable_pin` | `not_minimalUnsatisfiable_vac` |
| `SufficientIn` | theorem over a reference class | `sufficientIn_bounded_single` | `not_sufficientIn_true_single` |
| `TightIn` | tightness with witness in a class | `tightIn_true_pin_h2` | `not_tightIn_bounded_pin_h2` |
| `NonVacuousIn` | non-vacuity with witness in a class | `nonVacuousIn_bounded_pin` | `not_nonVacuousIn_zeroClass_pin` |
| `HarmlessIn` | ledger label `harmless` (pointwise on a class) | `harmlessIn_bounded_pin_h2` | `not_harmlessIn_true_pin_h2` |
| `replaceAt` | replacing one hypothesis | `sufficient_replaceAt_sum_h1_by_sumC`; `replaceAt_self`, `replaceAt_of_ne`, `replaceAt_iff_ite` (Core.lean) | `not_sufficient_replaceAt_sum_h1_by_true` |
| `WeakestPremise` | weakest replacement premise | `weakestPremise_sum_h1_at_2_0` | `not_weakestPremise_sum_h1_at_5_0` |
| `Check`, `InformativeCheck` | ✓ entry; ✓ with a model in the cell (Tables.lean) | `informativeCheck_demo_h1_h1` | `not_check_demo_h1_h2`; `check_not_informative_demo_h2_h1` |
| `classify` | finite cell classifier (Tables.lean) | `classify_demo` | `classify_witnessedOnUniv_without_check` |
| `auditLedger` | finite ledger audit (Audit.lean) | `auditLedger_pin`, `auditLedger_sum`, `auditLedger_dup`, `auditLedger_vac`, `auditLedger_schema` | `auditLedger_false_theorem_tight_entry_reuses_counterexample`, `auditLedger_complete_ce_incomplete_univ` |

For `classify` and `auditLedger` the "negative" entries show what the procedures do not certify (a verdict over an incomplete list; a tightness entry reused from a counterexample when the theorem fails).

The definition tests named in the table, verbatim, in table order:

```lean
-- lean/Toy/Ledger/Examples.lean:70
theorem sufficient_pin : Sufficient pinH pinC := by
-- lean/Toy/Ledger/Examples.lean:75
theorem not_sufficient_single_le_one : ¬ Sufficient (single fun x : Nat => x ≤ 1) pinC := by
-- lean/Toy/Ledger/Examples.lean:82
theorem tightAt_pin_h1 : TightAt pinH pinC .h1 :=
-- lean/Toy/Ledger/Examples.lean:85
theorem tightAt_pin_h2 : TightAt pinH pinC .h2 :=
-- lean/Toy/Ledger/Examples.lean:88
theorem not_tightAt_pinWeak_h1 : ¬ TightAt pinH pinWeakC .h1 := by
-- lean/Toy/Ledger/Examples.lean:95
theorem irredundant_pin : Irredundant pinH pinC := by
-- lean/Toy/Ledger/Examples.lean:101
theorem not_irredundant_dup : ¬ Irredundant dupH pinC := by
-- lean/Toy/Ledger/Examples.lean:109
theorem nonVacuous_pin : NonVacuous pinH :=
-- lean/Toy/Ledger/Examples.lean:112
theorem not_nonVacuous_vac : ¬ NonVacuous vacH := by
-- lean/Toy/Ledger/Examples.lean:120
theorem necessaryAt_pin_h1 : NecessaryAt pinH pinC .h1 := by
-- lean/Toy/Ledger/Examples.lean:125
theorem not_necessaryAt_sum_h1 : ¬ NecessaryAt sumH sumC .h1 := by
-- lean/Toy/Ledger/Examples.lean:132
theorem unweakenableAt_pin_h1 : UnweakenableAt pinH pinC .h1 := by
-- lean/Toy/Ledger/Examples.lean:137
theorem not_unweakenableAt_sum_h1 : ¬ UnweakenableAt sumH sumC .h1 := by
-- lean/Toy/Ledger/Examples.lean:144
theorem independent_bits : Independent bitsH := by
-- lean/Toy/Ledger/Examples.lean:148
theorem not_independent_pin : ¬ Independent pinH := by
-- lean/Toy/Ledger/Examples.lean:156
theorem isolatingAt_pin_h1 : IsolatingAt pinH .h1 :=
-- lean/Toy/Ledger/Examples.lean:159
theorem not_isolatingAt_dup_h1 : ¬ IsolatingAt dupH .h1 := by
-- lean/Toy/Ledger/Examples.lean:166-167
theorem sufficient_restrict_sumVocab_h1h2 :
    Sufficient (restrict (fun j => j ≠ .h3) sumVocab) sumC := by
-- lean/Toy/Ledger/Examples.lean:174-175
theorem not_sufficient_restrict_sumVocab_h1 :
    ¬ Sufficient (restrict (fun j => j = .h1) sumVocab) sumC := by
-- lean/Toy/Ledger/Examples.lean:182
theorem minimalUnsatisfiable_pin : MinimalUnsatisfiable (withNegatedConclusion pinH pinC) := by
-- lean/Toy/Ledger/Examples.lean:212
theorem not_minimalUnsatisfiable_vac : ¬ MinimalUnsatisfiable (withNegatedConclusion vacH falseC) := by
-- lean/Toy/Ledger/Examples.lean:223
theorem sufficientIn_bounded_single : SufficientIn bounded (single fun x : Nat => 1 ≤ x) pinC := by
-- lean/Toy/Ledger/Examples.lean:229
theorem not_sufficientIn_true_single : ¬ SufficientIn trueC (single fun x : Nat => 1 ≤ x) pinC := by
-- lean/Toy/Ledger/Examples.lean:234
theorem tightIn_true_pin_h2 : TightIn trueC pinH pinC .h2 :=
-- lean/Toy/Ledger/Examples.lean:237
theorem not_tightIn_bounded_pin_h2 : ¬ TightIn bounded pinH pinC .h2 := by
-- lean/Toy/Ledger/Examples.lean:256
theorem nonVacuousIn_bounded_pin : NonVacuousIn bounded pinH :=
-- lean/Toy/Ledger/Examples.lean:259
theorem not_nonVacuousIn_zeroClass_pin : ¬ NonVacuousIn zeroClass pinH := by
-- lean/Toy/Ledger/Examples.lean:244
theorem harmlessIn_bounded_pin_h2 : HarmlessIn bounded pinH .h2 := by
-- lean/Toy/Ledger/Examples.lean:248
theorem not_harmlessIn_true_pin_h2 : ¬ HarmlessIn trueC pinH .h2 := by
-- lean/Toy/Ledger/Examples.lean:267
theorem sufficient_replaceAt_sum_h1_by_sumC : Sufficient (replaceAt sumH .h1 sumC) sumC :=
-- lean/Toy/Ledger/Core.lean:127-128
@[simp] theorem replaceAt_self (H : ι → M → Prop) (i : ι) (H' : M → Prop) (x : M) :
    replaceAt H i H' i x ↔ H' x :=
-- lean/Toy/Ledger/Core.lean:131-132
theorem replaceAt_of_ne (H : ι → M → Prop) {i j : ι} (H' : M → Prop) (hj : j ≠ i) (x : M) :
    replaceAt H i H' j x ↔ H j x :=
-- lean/Toy/Ledger/Core.lean:136-137
theorem replaceAt_iff_ite [DecidableEq ι] (H : ι → M → Prop) (i : ι) (H' : M → Prop)
    (j : ι) (x : M) : replaceAt H i H' j x ↔ (if j = i then H' else H j) x := by
-- lean/Toy/Ledger/Examples.lean:270
theorem not_sufficient_replaceAt_sum_h1_by_true : ¬ Sufficient (replaceAt sumH .h1 trueC) sumC := by
-- lean/Toy/Ledger/Examples.lean:280-281
theorem weakestPremise_sum_h1_at_2_0 :
    WeakestPremise sumH sumC .h1 (2, 0) ∧ ¬ sumH .h1 (2, 0) := by
-- lean/Toy/Ledger/Examples.lean:285
theorem not_weakestPremise_sum_h1_at_5_0 : ¬ WeakestPremise sumH sumC .h1 (5, 0) := by
-- lean/Toy/Ledger/Tables.lean:54
theorem informativeCheck_demo_h1_h1 : InformativeCheck demoTable evenQ .h1 .h1 :=
-- lean/Toy/Ledger/Tables.lean:57
theorem not_check_demo_h1_h2 : ¬ Check demoTable evenQ .h1 .h2 := by
-- lean/Toy/Ledger/Tables.lean:63-64
theorem check_not_informative_demo_h2_h1 :
    Check demoTable evenQ .h2 .h1 ∧ ¬ InformativeCheck demoTable evenQ .h2 .h1 :=
-- lean/Toy/Ledger/Tables.lean:260-268
theorem classify_demo :
    ((classify (List.finRange 4) demoTableB evenB .h1 .h1).status,
      (classify (List.finRange 4) demoTableB evenB .h1 .h1).witness?) =
        (.witnessedOnUniv, some 2) ∧
    ((classify (List.finRange 4) demoTableB evenB .h1 .h2).status,
      (classify (List.finRange 4) demoTableB evenB .h1 .h2).witness?) =
        (.foundCounterexample, some 3) ∧
    (classify (List.finRange 4) demoTableB evenB .h2 .h1).status = .emptyOnUniv ∧
    (classify (List.finRange 4) demoTableB evenB .h2 .h2).status = .emptyOnUniv := by
-- lean/Toy/Ledger/Tables.lean:297-299
theorem classify_witnessedOnUniv_without_check :
    (classify [2] twoThreeTableB evenB () ()).status = .witnessedOnUniv ∧
      ¬ Check (liftTable twoThreeTableB) (liftPred evenB) () () := by
-- lean/Toy/Ledger/Audit.lean:397-400
theorem auditLedger_pin :
    (auditLedger (List.finRange 4) pinHB pinCB).summary =
      { sufficiency := .noWitness, tightness := [.witness 0, .witness 2],
        nonvacuity := .witness 1, weakening := [.noWitness, .noWitness] } := by
-- lean/Toy/Ledger/Audit.lean:406-409
theorem auditLedger_sum :
    (auditLedger grid3 sumHB sumCB).summary =
      { sufficiency := .noWitness, tightness := [.witness (2, 1), .witness (1, 2)],
        nonvacuity := .witness (0, 0), weakening := [.witness (2, 0), .witness (0, 2)] } := by
-- lean/Toy/Ledger/Audit.lean:415-418
theorem auditLedger_dup :
    (auditLedger (List.finRange 4) dupHB pinCB).summary =
      { sufficiency := .noWitness, tightness := [.noWitness, .noWitness],
        nonvacuity := .witness 1, weakening := [.noWitness, .noWitness] } := by
-- lean/Toy/Ledger/Audit.lean:424-427
theorem auditLedger_vac :
    (auditLedger (List.finRange 3) vacHB (fun _ => false)).summary =
      { sufficiency := .noWitness, tightness := [.witness 2, .witness 1],
        nonvacuity := .noWitness, weakening := [.noWitness, .noWitness] } := by
-- lean/Toy/Ledger/Audit.lean:434-438
theorem auditLedger_schema :
    (auditLedger bools2 schemaHB (fun p => p.2)).summary =
      { sufficiency := .noWitness, tightness := [.witness (false, false), .witness (true, false)],
        nonvacuity := .witness (false, true),
        weakening := [.noWitness, .witness (true, true)] } := by
-- lean/Toy/Ledger/Audit.lean:469-472
theorem auditLedger_false_theorem_tight_entry_reuses_counterexample :
    (auditLedger [false, true] (fun (_ : Fin 1) (_ : Bool) => true) (fun b => b)).summary =
      { sufficiency := .witness false, tightness := [.witness false],
        nonvacuity := .witness false, weakening := [.noWitness] } := by
-- lean/Toy/Ledger/Audit.lean:478-488
theorem auditLedger_complete_ce_incomplete_univ :
    ¬ (((auditLedger ([] : List (Fin 4)) pinHB (fun _ => false)).summary.sufficiency =
          .noWitness ↔ Sufficient (liftH pinHB) (liftPred (fun _ : Fin 4 => false))) ∧
        (∀ i : Fin 2,
          (auditLedger ([] : List (Fin 4)) pinHB (fun _ => false)).summary.tightness[i.val]? =
            some .noWitness ↔ ¬ TightAt (liftH pinHB) (liftPred (fun _ : Fin 4 => false)) i) ∧
        ((auditLedger ([] : List (Fin 4)) pinHB (fun _ => false)).summary.nonvacuity =
          .noWitness ↔ ¬ NonVacuous (liftH pinHB)) ∧
        (∀ i : Fin 2,
          (auditLedger ([] : List (Fin 4)) pinHB (fun _ => false)).summary.weakening[i.val]? =
            some .noWitness ↔ UnweakenableAt (liftH pinHB) (liftPred (fun _ : Fin 4 => false)) i)) := by
```

### Running examples

The index types and family constructors (`lean/Toy/Ledger/Core.lean`), verbatim: `pair A B` is the family `[A, B]` indexed by `Two` (indices `h1`, `h2`); `single A` and `triple A B D` are the one- and three-member families indexed by `Unit` and `Three`.

```lean
-- lean/Toy/Ledger/Core.lean:147-150
inductive Two where
  | h1
  | h2
  deriving DecidableEq, Repr
-- lean/Toy/Ledger/Core.lean:153-157
inductive Three where
  | h1
  | h2
  | h3
  deriving DecidableEq, Repr
-- lean/Toy/Ledger/Core.lean:160-161
def single {M : Type u} (A : M → Prop) : Unit → M → Prop :=
  fun _ => A
-- lean/Toy/Ledger/Core.lean:164-166
def pair {M : Type u} (A B : M → Prop) : Two → M → Prop
  | .h1 => A
  | .h2 => B
-- lean/Toy/Ledger/Core.lean:169-172
def triple {M : Type u} (A B D : M → Prop) : Three → M → Prop
  | .h1 => A
  | .h2 => B
  | .h3 => D
```

The concrete families and conclusions, verbatim:

```lean
-- lean/Toy/Ledger/Examples.lean:18
def pinH : Two → Nat → Prop := pair (fun x => 1 ≤ x) (fun x => x ≤ 1)
-- lean/Toy/Ledger/Examples.lean:21
def pinC : Nat → Prop := fun x => x = 1
-- lean/Toy/Ledger/Examples.lean:24
def pinWeakC : Nat → Prop := fun x => x ≤ 1
-- lean/Toy/Ledger/Examples.lean:27
def sumH : Two → Nat × Nat → Prop := pair (fun p => p.1 ≤ 1) (fun p => p.2 ≤ 1)
-- lean/Toy/Ledger/Examples.lean:30
def sumC : Nat × Nat → Prop := fun p => p.1 + p.2 ≤ 2
-- lean/Toy/Ledger/Examples.lean:33
def dupH : Two → Nat → Prop := pair (fun x => x = 1) (fun x => x = 1)
-- lean/Toy/Ledger/Examples.lean:36
def eqH : Two → Nat × Nat → Prop := pair (fun p => p.1 = 0) (fun p => p.2 = 0)
-- lean/Toy/Ledger/Examples.lean:39
def eqC : Nat × Nat → Prop := fun p => p.1 = p.2
-- lean/Toy/Ledger/Examples.lean:42
def entH : Two → Nat × Nat → Prop := pair (fun p => p.1 = 0) (fun p => p.1 = 0 ∧ p.2 = 0)
-- lean/Toy/Ledger/Examples.lean:45
def vacH : Two → Fin 3 → Prop := pair (fun x => x = 1) (fun x => x = 2)
-- lean/Toy/Ledger/Examples.lean:48
def falseC {M : Type u} : M → Prop := fun _ => False
-- lean/Toy/Ledger/Examples.lean:51
def trueC {M : Type u} : M → Prop := fun _ => True
-- lean/Toy/Ledger/Examples.lean:54
def bitsH : Two → Bool × Bool → Prop := pair (fun p => p.1 = true) (fun p => p.2 = true)
-- lean/Toy/Ledger/Examples.lean:57-58
def schemaH {M : Type u} (P C : M → Prop) : Two → M → Prop :=
  pair (fun x => P x ∨ C x) (fun x => ¬ P x)
-- lean/Toy/Ledger/Examples.lean:62-63
def sumVocab : Three → Nat × Nat → Prop :=
  triple (fun p => p.1 ≤ 1) (fun p => p.2 ≤ 1) (fun p => p.1 + p.2 ≤ 2)
-- lean/Toy/Ledger/Examples.lean:66
def bounded : Nat → Prop := fun x => x ≤ 1
-- lean/Toy/Ledger/Examples.lean:254
def zeroClass : Nat → Prop := fun x => x = 0
-- lean/Toy/Ledger/Witnesses.lean:117
def topH : Unit → Unit → Prop := single fun _ => True
-- lean/Toy/Ledger/Witnesses.lean:187
def geH : Nat → Nat → Prop := fun i x => i ≤ x
-- lean/Toy/Ledger/Families.lean:104-105
def intVocab : Three → Int × Int → Prop :=
  triple (fun p => p.1 = 0) (fun p => p.2 = 0) (fun p => p.1 = 0 ∧ p.2 = 0)
-- lean/Toy/Ledger/Families.lean:108
def intC : Int × Int → Prop := fun p => p.1 + p.2 = 0
-- lean/Toy/Ledger/Families.lean:278-279
def orSchemaH {M : Type u} (P C : M → Prop) : Two → M → Prop :=
  pair (fun x => P x ∨ C x) (fun x => ¬ P x ∨ C x)
-- lean/Toy/Ledger/Families.lean:348
def hatchH : Two → Fin 3 → Prop := pair (fun x => x ≠ 2) (fun x => x = 1 ∨ x = 2)
-- lean/Toy/Ledger/Families.lean:351
def hatchC : Fin 3 → Prop := fun x => x = 1
-- lean/Toy/Ledger/Strength.lean:247
def flipH : Unit → Bool → Prop := single fun b => b = true
-- lean/Toy/Ledger/Strength.lean:250
def flipC : Bool → Prop := fun b => b = false
-- lean/Toy/Ledger/Tables.lean:46-49
def demoTable : Two → Two → Nat → Prop
  | .h1, .h1 => fun x => x = 2
  | .h1, .h2 => fun x => x = 3
  | .h2, _ => fun _ => False
-- lean/Toy/Ledger/Tables.lean:52
def evenQ : Nat → Prop := fun x => x % 2 = 0
-- lean/Toy/Ledger/Tables.lean:77
def emptyTable : Bool → Bool → Nat → Prop := fun _ _ _ => False
```

`Bool`-valued instances on which `classify` and `auditLedger` are run (results 25–28), verbatim. `demoTableB` and `evenB` are the counterparts of `demoTable` and `evenQ` on `Fin 4`; `pinHB`, `pinCB` and `dupHB` are the counterparts of `pinH`, `pinC` and `dupH` on `Fin 4`; `sumHB` and `sumCB` are the counterparts of `sumH` and `sumC` on `Fin 3 × Fin 3`, with sums computed in `Nat`; `vacHB` is the counterpart of `vacH` on `Fin 3`; `schemaHB` is the instance of `schemaH` used in result 16 (first bit `P`, second bit `C`) on `Bool × Bool`. In each two-member family, index `0 : Fin 2` is the first hypothesis and `1` the second. The lists `grid3` (first coordinate major) and `bools2` list every element of their types (`mem_grid3`, `mem_bools2`); `List.find?` scans them in the order shown.

```lean
-- lean/Toy/Ledger/Tables.lean:250-253
def demoTableB : Two → Two → Fin 4 → Bool
  | .h1, .h1 => fun x => decide (x.val = 2)
  | .h1, .h2 => fun x => decide (x.val = 3)
  | .h2, _ => fun _ => false
-- lean/Toy/Ledger/Tables.lean:256
def evenB : Fin 4 → Bool := fun x => decide (x.val % 2 = 0)
-- lean/Toy/Ledger/Audit.lean:356-357
def pinHB : Fin 2 → Fin 4 → Bool :=
  fun i x => if i = 0 then decide (1 ≤ x.val) else decide (x.val ≤ 1)
-- lean/Toy/Ledger/Audit.lean:360
def pinCB : Fin 4 → Bool := fun x => decide (x.val = 1)
-- lean/Toy/Ledger/Audit.lean:363-364
def sumHB : Fin 2 → Fin 3 × Fin 3 → Bool :=
  fun i p => if i = 0 then decide (p.1.val ≤ 1) else decide (p.2.val ≤ 1)
-- lean/Toy/Ledger/Audit.lean:367
def sumCB : Fin 3 × Fin 3 → Bool := fun p => decide (p.1.val + p.2.val ≤ 2)
-- lean/Toy/Ledger/Audit.lean:370-371
def grid3 : List (Fin 3 × Fin 3) :=
  (List.finRange 3).flatMap fun a => (List.finRange 3).map fun b => (a, b)
-- lean/Toy/Ledger/Audit.lean:373
theorem mem_grid3 (p : Fin 3 × Fin 3) : p ∈ grid3 := by
-- lean/Toy/Ledger/Audit.lean:378
def dupHB : Fin 2 → Fin 4 → Bool := fun _ x => decide (x.val = 1)
-- lean/Toy/Ledger/Audit.lean:381-382
def vacHB : Fin 2 → Fin 3 → Bool :=
  fun i x => if i = 0 then decide (x.val = 1) else decide (x.val = 2)
-- lean/Toy/Ledger/Audit.lean:385
def schemaHB : Fin 2 → Bool × Bool → Bool := fun i p => if i = 0 then p.1 || p.2 else !p.1
-- lean/Toy/Ledger/Audit.lean:388
def bools2 : List (Bool × Bool) := [(false, false), (false, true), (true, false), (true, true)]
-- lean/Toy/Ledger/Audit.lean:390
theorem mem_bools2 (p : Bool × Bool) : p ∈ bools2 := by
```

### Result cards

Each card gives the kind, tier and depth label, the plain claim, the verbatim Lean statement, a rendering with key definitions replaced by their bodies (for the general results), the hypothesis ledger with the verbatim counterexample statements, the non-vacuity witness, prior art and the design question. Non-claims are under **Boundaries**.

#### 1. `tightAt_iff_witness_violates_exactly_i_of_sufficient`

- **Kind:** characterization · **Tier:** T0 · **Depth:** shallow
- **Plain claim:** Suppose the hypotheses H suffice for C. Then (1) every model that satisfies every hypothesis other than i and violates C also violates H i, so it violates H i and no other hypothesis; and (2) hypothesis i is tight (some model satisfies every other hypothesis and violates C) exactly when some model satisfies every other hypothesis and violates both H i and C.

**Lean statement** (`tightAt_iff_witness_violates_exactly_i_of_sufficient`, verbatim):

```lean
-- lean/Toy/Ledger/Witnesses.lean:25-28
theorem tightAt_iff_witness_violates_exactly_i_of_sufficient
    {H : ι → M → Prop} {C : M → Prop} (hs : Sufficient H C) (i : ι) :
    (∀ x, (∀ j, j ≠ i → H j x) → ¬ C x → ¬ H i x) ∧
    (TightAt H C i ↔ ∃ x, (∀ j, j ≠ i → H j x) ∧ ¬ H i x ∧ ¬ C x) := by
```

Unfolded statement of `tightAt_iff_witness_violates_exactly_i_of_sufficient` (key definitions replaced by their bodies; this Lean term elaborates in the theorem's context and is definitionally equal to the rest of the statement):

```lean
(∀ x, (∀ j, H j x) → C x) → ∀ i : ι,
  (∀ x, (∀ j, j ≠ i → H j x) → ¬ C x → ¬ H i x) ∧
  ((∃ x, (∀ j, j ≠ i → H j x) ∧ ¬ C x) ↔ ∃ x, (∀ j, j ≠ i → H j x) ∧ ¬ H i x ∧ ¬ C x)
```

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample(s) | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hs : Sufficient H C` | Without sufficiency a tightness witness may satisfy H i itself (it is then a counterexample to the theorem, not a witness about H i). | tight | `tightAt_iff_witness_violates_exactly_i_ce_not_sufficient` | a one-hypothesis family over Unit, True ⊢ False (the theorem is false) |

Counterexample statements (verbatim; each states that the other hypotheses hold and the conclusion fails):

```lean
-- lean/Toy/Ledger/Witnesses.lean:125-128
theorem tightAt_iff_witness_violates_exactly_i_ce_not_sufficient :
    ¬ ((∀ x, (∀ j, j ≠ () → topH j x) → ¬ falseC x → ¬ topH () x) ∧
        (TightAt topH falseC () ↔
          ∃ x, (∀ j, j ≠ () → topH j x) ∧ ¬ topH () x ∧ ¬ falseC x)) := by
```

**Non-vacuity witness:** x ≥ 1, x ≤ 1 ⊢ x = 1 over Nat is sufficient; h1 (x ≥ 1) is tight with witness x = 0, which satisfies x ≤ 1 and violates x ≥ 1 and x = 1. (`tightAt_iff_witness_violates_exactly_i_nonvacuity`)

```lean
-- lean/Toy/Ledger/Witnesses.lean:135-137
theorem tightAt_iff_witness_violates_exactly_i_nonvacuity :
    Sufficient pinH pinC ∧ TightAt pinH pinC .h1 ∧
      ((∀ j, j ≠ Two.h1 → pinH j 0) ∧ ¬ pinH .h1 0 ∧ ¬ pinC 0) :=
```

**Prior art:**

- David Hilbert, The Foundations of Geometry, authorized translation by E. J. Townsend, Open Court, 1902 (Project Gutenberg eBook #17384), Chapter II, sections 10-12; section 12: 'In order to demonstrate the independence of the axiom of Archimedes, we must produce a geometry in which all of the axioms are fulfilled with the exception of the one in question.' Hilbert's independence of an axiom does not mention a conclusion (it is IsolatingAt here); TightAt is relative to a conclusion.
- No specific prior source; an elementary consequence of the definitions, restated in this package's vocabulary.

**Design question.** Given a theorem that holds, what exactly does a 'tight' entry in its hypothesis ledger assert about the witness model?

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims**, result 1.

#### 2. `tightAt_iff_not_sufficient_without`

- **Kind:** characterization · **Tier:** T0 · **Depth:** shallow
- **Plain claim:** For any hypothesis family H, conclusion C and index i, hypothesis i is tight exactly when the family with H i deleted (indexed by {j // j ≠ i}) is not sufficient for C. No assumption that the full family is sufficient is used.

**Lean statement** (`tightAt_iff_not_sufficient_without`, verbatim):

```lean
-- lean/Toy/Ledger/Witnesses.lean:36-37
theorem tightAt_iff_not_sufficient_without (H : ι → M → Prop) (C : M → Prop) (i : ι) :
    TightAt H C i ↔ ¬ Sufficient (restrict (fun j => j ≠ i) H) C :=
```

Unfolded statement of `tightAt_iff_not_sufficient_without` (key definitions replaced by their bodies; this Lean term elaborates in the theorem's context and is definitionally equal to the rest of the statement):

```lean
(∃ x, (∀ j, j ≠ i → H j x) ∧ ¬ C x) ↔ ¬ ∀ x, (∀ j : {j // j ≠ i}, H j.1 x) → C x
```

**Hypothesis ledger.**

No hypotheses: the statement holds for all values of its parameters.

**Non-vacuity witness:** x ≥ 1, x ≤ 1 ⊢ x = 1 over Nat, i = h1: both sides hold (deleting x ≥ 1 leaves x ≤ 1, which does not give x = 1). (`tightAt_iff_not_sufficient_without_nonvacuity`)

```lean
-- lean/Toy/Ledger/Witnesses.lean:142-143
theorem tightAt_iff_not_sufficient_without_nonvacuity :
    TightAt pinH pinC .h1 ∧ ¬ Sufficient (restrict (fun j => j ≠ Two.h1) pinH) pinC := by
```

**Prior art:**

- No specific prior source; an elementary consequence of the definitions, restated in this package's vocabulary.
- Lean 4 core unused-variables linter (option linter.unusedVariables), leanprover/lean4 commit 5045d0056413266e57c625dcd7c365b10e377c52 (the v4.34.1 toolchain), src/Lean/Linter/UnusedVariables.lean: 'reports any local variables that are never referred to, using information from the info tree'. Batteries environment linter unusedArguments, leanprover-community/batteries commit 4a314aed8362bd744e129ac93e4174b288811db6, Batteries/Tactic/Lint/Misc.lean: checks whether each argument occurs in the elaborated value or type, skipping declarations that contain sorry. Both are syntactic, proof-relative checks (their relation to this result is a prose argument: derived, modeling bridge).

**Design question.** Is 'tight' the same as 'the theorem fails without this hypothesis'? (Yes, relative to the stated model type: TightAt H C i holds exactly when the family without H i is not sufficient. Reference point.)

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims**, result 2.

#### 3. `irredundant_iff_no_proper_subfamily_sufficient`

- **Kind:** characterization · **Tier:** T0 · **Depth:** shallow
- **Plain claim:** For any hypothesis family H and conclusion C, every hypothesis is tight exactly when no proper subfamily of H (one omitting at least one hypothesis, possibly many) is sufficient for C. So one single-deletion witness per hypothesis certifies that no deletion of a nonempty set of hypotheses keeps C.

**Lean statement** (`irredundant_iff_no_proper_subfamily_sufficient`, verbatim):

```lean
-- lean/Toy/Ledger/Witnesses.lean:55-56
theorem irredundant_iff_no_proper_subfamily_sufficient (H : ι → M → Prop) (C : M → Prop) :
    Irredundant H C ↔ ∀ S : ι → Prop, (∃ i, ¬ S i) → ¬ Sufficient (restrict S H) C :=
```

Unfolded statement of `irredundant_iff_no_proper_subfamily_sufficient` (key definitions replaced by their bodies; this Lean term elaborates in the theorem's context and is definitionally equal to the rest of the statement):

```lean
(∀ i, ∃ x, (∀ j, j ≠ i → H j x) ∧ ¬ C x) ↔
  ∀ S : ι → Prop, (∃ i, ¬ S i) → ¬ ∀ x, (∀ j : Subtype S, H j.1 x) → C x
```

**Hypothesis ledger.**

No hypotheses: the statement holds for all values of its parameters.

**Non-vacuity witness:** x ≥ 1, x ≤ 1 ⊢ x = 1: sufficient and irredundant; the empty subfamily is not sufficient. (`irredundant_iff_no_proper_subfamily_sufficient_nonvacuity`)

```lean
-- lean/Toy/Ledger/Witnesses.lean:165-167
theorem irredundant_iff_no_proper_subfamily_sufficient_nonvacuity :
    Sufficient pinH pinC ∧ Irredundant pinH pinC ∧
      ¬ Sufficient (restrict (fun _ => False) pinH) pinC := by
```

**Prior art:**

- Mathlib (leanprover-community/mathlib4 commit 3eae40f5eb25c5934211edf662d3b24c5afbe47a): Mathlib/Order/Minimal.lean line 348, Set.minimal_iff_forall_sdiff_singleton (for a predicate P on sets that is closed under supersets, Minimal P s <-> P s and no s \ {{x}} with x in s satisfies P); line 300, Minimal.eq_of_superset (Minimal P s -> P t -> t ⊆ s -> s = t); Mathlib/Order/Antichain.lean line 313, setOfPred_minimal_antichain (the minimal elements of a predicate form an antichain). These are the order-theoretic forms of the statements here, with P = sufficiency of a subfamily.
- Sven Ove Hansson, "Kernel contraction", Journal of Symbolic Logic 59(3):845-859, 1994, DOI 10.2307/2275912. Kernel contraction acts on the alpha-kernels of a belief base B, its inclusion-minimal subsets implying alpha (definition as restated in Renata Wassermann, "Local Diagnosis", arXiv:cs/0003051, 2000, Definition 1). A sufficient, irredundant subfamily of a vocabulary is the analogue of an alpha-kernel, with implication read semantically over the model type.
- Alexey Ignatiev, Nina Narodytska, Joao Marques-Silva, "Abduction-Based Explanations for Machine Learning Models", Proceedings of the AAAI Conference on Artificial Intelligence 33(01):1511-1519, 2019, DOI 10.1609/aaai.v33i01.33011511. Definition 1: the explanations are the subsets S of the hypotheses H with F ∧ S consistent and F ∧ S entailing E; subset-minimal and cardinality-minimal explanations are distinguished.
- Mark H. Liffiton, Karem A. Sakallah, "Algorithms for Computing Minimal Unsatisfiable Subsets of Constraints", Journal of Automated Reasoning 40(1):1-33, 2008 (online 2007), DOI 10.1007/s10817-007-9084-z. Abstract: a sound and complete algorithm 'for producing all MUSes of an unsatisfiable constraint system'; complete results can be intractably large.

**Design question.** For a theorem that holds, does an all-tight ledger certify that its hypothesis set is minimal, and in what sense? (Inclusion-minimal among sufficient subfamilies; not minimum-size, not unique.)

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims**, result 3.

#### 4. `sufficient_irredundant_nonVacuous_iff_minimalUnsatisfiable`

- **Kind:** characterization · **Tier:** T0 · **Depth:** shallow
- **Plain claim:** For any H and C: the theorem holds, every hypothesis is tight, and the hypotheses are jointly satisfiable exactly when the family {H i | i} together with the negated conclusion ¬ C is minimally unsatisfiable (unsatisfiable, and every proper subfamily satisfiable). Deleting H i corresponds to tightness of i and deleting ¬ C to non-vacuity.

**Lean statement** (`sufficient_irredundant_nonVacuous_iff_minimalUnsatisfiable`, verbatim):

```lean
-- lean/Toy/Ledger/Witnesses.lean:67-70
theorem sufficient_irredundant_nonVacuous_iff_minimalUnsatisfiable
    (H : ι → M → Prop) (C : M → Prop) :
    (Sufficient H C ∧ Irredundant H C ∧ NonVacuous H) ↔
      MinimalUnsatisfiable (withNegatedConclusion H C) := by
```

Unfolded statement of `sufficient_irredundant_nonVacuous_iff_minimalUnsatisfiable` (`Sufficient`, `Irredundant`, `TightAt`, `NonVacuous`, `MinimalUnsatisfiable` and `restrict` replaced by their definitions; `withNegatedConclusion` kept; this Lean term elaborates in the theorem's context and is definitionally equal to the rest of the statement):

```lean
((∀ x, (∀ i, H i x) → C x) ∧ (∀ i, ∃ x, (∀ j, j ≠ i → H j x) ∧ ¬ C x) ∧ ∃ x, ∀ i, H i x) ↔
  (¬ ∃ x, ∀ k, withNegatedConclusion H C k x) ∧
    ∀ S : Option ι → Prop, (∃ k, ¬ S k) → ∃ x, ∀ k : Subtype S, withNegatedConclusion H C k.1 x
```

**Hypothesis ledger.**

No hypotheses: the statement holds for all values of its parameters.

**Non-vacuity witness:** x ≥ 1, x ≤ 1 ⊢ x = 1: both sides hold. (`sufficient_irredundant_nonVacuous_iff_minimalUnsatisfiable_nonvacuity`)

```lean
-- lean/Toy/Ledger/Witnesses.lean:217-219
theorem sufficient_irredundant_nonVacuous_iff_minimalUnsatisfiable_nonvacuity :
    (Sufficient pinH pinC ∧ Irredundant pinH pinC ∧ NonVacuous pinH) ∧
      MinimalUnsatisfiable (withNegatedConclusion pinH pinC) :=
```

**Prior art:**

- Mark H. Liffiton, Karem A. Sakallah, "Algorithms for Computing Minimal Unsatisfiable Subsets of Constraints", Journal of Automated Reasoning 40(1):1-33, 2008 (online 2007), DOI 10.1007/s10817-007-9084-z. Abstract: a sound and complete algorithm 'for producing all MUSes of an unsatisfiable constraint system'; complete results can be intractably large.
- Alexey Ignatiev, Nina Narodytska, Joao Marques-Silva, "Abduction-Based Explanations for Machine Learning Models", Proceedings of the AAAI Conference on Artificial Intelligence 33(01):1511-1519, 2019, DOI 10.1609/aaai.v33i01.33011511. Definition 1: the explanations are the subsets S of the hypotheses H with F ∧ S consistent and F ∧ S entailing E; subset-minimal and cardinality-minimal explanations are distinguished.

**Design question.** Which standard object is a sufficient, irredundant ledger together with a non-vacuity witness equivalent to? (A minimal unsatisfiable family: the hypotheses plus the negated conclusion.)

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims**, result 4.

#### 5. `irredundance_independence_isolation_countermodels`

- **Kind:** counterexample · **Tier:** T1 · **Depth:** shallow
- **Plain claim:** Irredundancy, full independence and isolation are distinct: x ≥ 1, x ≤ 1 ⊢ x = 1 over Nat is sufficient, irredundant and non-vacuous but not independent; two independent coordinate bits over Bool × Bool with the valid conclusion True are sufficient and non-vacuous and have no tight hypothesis; and x ≥ 1, x ≤ 1 ⊢ x ≤ 1 is sufficient and non-vacuous, and its hypothesis x ≥ 1 has an isolating model but is not tight.

**Lean statement** (`irredundance_independence_isolation_countermodels`, verbatim):

```lean
-- lean/Toy/Ledger/Witnesses.lean:239-244
theorem irredundance_independence_isolation_countermodels :
    (Sufficient pinH pinC ∧ Irredundant pinH pinC ∧ NonVacuous pinH ∧ ¬ Independent pinH) ∧
    (Sufficient bitsH trueC ∧ NonVacuous bitsH ∧ Independent bitsH ∧
      ∀ i, ¬ TightAt bitsH trueC i) ∧
    (Sufficient pinH pinWeakC ∧ NonVacuous pinH ∧ IsolatingAt pinH .h1 ∧
      ¬ TightAt pinH pinWeakC .h1) := by
```

Definitions used: `pinH`, `pinC`, `pinWeakC`, `bitsH`, `trueC` (quoted under **Running examples** and **Definitions**).

**Hypothesis ledger.**

No hypotheses: the statement is about concrete instances.

**Non-vacuity witness:** Each of the three instances is proved sufficient and non-vacuous inside the statement. (`irredundance_independence_isolation_countermodels`)

**Prior art:**

- David Hilbert, The Foundations of Geometry, authorized translation by E. J. Townsend, Open Court, 1902 (Project Gutenberg eBook #17384), Chapter II, sections 10-12; section 12: 'In order to demonstrate the independence of the axiom of Archimedes, we must produce a geometry in which all of the axioms are fulfilled with the exception of the one in question.' Hilbert's independence of an axiom does not mention a conclusion (it is IsolatingAt here); TightAt is relative to a conclusion.

**Design question.** Can classical axiom-independence arguments (one model per axiom) stand in for a tightness ledger, or vice versa? (Not in general.)

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims**, result 5.

#### 6. `isolatingAt_of_tightAt_of_sufficient`

- **Kind:** theorem · **Tier:** T0 · **Depth:** shallow
- **Plain claim:** If the hypotheses H suffice for C and hypothesis i is tight, then hypothesis i has an isolating model (one violating H i and satisfying every other hypothesis).

**Lean statement** (`isolatingAt_of_tightAt_of_sufficient`, verbatim):

```lean
-- lean/Toy/Ledger/Witnesses.lean:106-107
theorem isolatingAt_of_tightAt_of_sufficient {H : ι → M → Prop} {C : M → Prop} {i : ι}
    (hs : Sufficient H C) (ht : TightAt H C i) : IsolatingAt H i :=
```

Unfolded statement of `isolatingAt_of_tightAt_of_sufficient` (key definitions replaced by their bodies; this Lean term elaborates in the theorem's context and is definitionally equal to the rest of the statement):

```lean
(∀ x, (∀ j, H j x) → C x) → (∃ x, (∀ j, j ≠ i → H j x) ∧ ¬ C x) →
  ∃ x, ¬ H i x ∧ ∀ j, j ≠ i → H j x
```

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample(s) | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hs : Sufficient H C` | Lets the tightness witness be shown to violate H i. | tight | `isolatingAt_of_tightAt_ce_not_sufficient` | a one-hypothesis family over Unit, True ⊢ False (the theorem is false) |
| `ht : TightAt H C i` | Supplies the witness. | tight | `isolatingAt_of_tightAt_ce_not_tight` | duplicated hypotheses x = 1, x = 1 ⊢ x = 1 over Nat, i = h1 |

Counterexample statements (verbatim; each states that the other hypotheses hold and the conclusion fails):

```lean
-- lean/Toy/Ledger/Witnesses.lean:264-265
theorem isolatingAt_of_tightAt_ce_not_sufficient :
    TightAt topH falseC () ∧ ¬ IsolatingAt topH () := by
-- lean/Toy/Ledger/Witnesses.lean:272-273
theorem isolatingAt_of_tightAt_ce_not_tight :
    Sufficient dupH pinC ∧ ¬ IsolatingAt dupH .h1 := by
```

**Non-vacuity witness:** x ≥ 1, x ≤ 1 ⊢ x = 1 over Nat is sufficient, and h1 (x ≥ 1) is tight. (`isolatingAt_of_tightAt_of_sufficient_nonvacuity`)

```lean
-- lean/Toy/Ledger/Witnesses.lean:279-280
theorem isolatingAt_of_tightAt_of_sufficient_nonvacuity :
    Sufficient pinH pinC ∧ TightAt pinH pinC .h1 :=
```

**Prior art:**

- David Hilbert, The Foundations of Geometry, authorized translation by E. J. Townsend, Open Court, 1902 (Project Gutenberg eBook #17384), Chapter II, sections 10-12; section 12: 'In order to demonstrate the independence of the axiom of Archimedes, we must produce a geometry in which all of the axioms are fulfilled with the exception of the one in question.' Hilbert's independence of an axiom does not mention a conclusion (it is IsolatingAt here); TightAt is relative to a conclusion.

**Design question.** When the theorem holds, does a tightness ledger yield the classical one-model-per-axiom independence witnesses? (Yes, one per tight hypothesis. Reference point.)

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims**, result 6.

#### 7. `unweakenableAt_of_necessaryAt`

- **Kind:** theorem · **Tier:** T0 · **Depth:** definitional
- **Plain claim:** If every model of the conclusion C satisfies hypothesis H i (global necessity), then H i holds wherever the other hypotheses and C hold (necessity relative to the other hypotheses).

**Lean statement** (`unweakenableAt_of_necessaryAt`, verbatim):

```lean
-- lean/Toy/Ledger/Strength.lean:24-25
theorem unweakenableAt_of_necessaryAt {H : ι → M → Prop} {C : M → Prop} {i : ι}
    (h : NecessaryAt H C i) : UnweakenableAt H C i :=
```

Unfolded statement of `unweakenableAt_of_necessaryAt` (key definitions replaced by their bodies; this Lean term elaborates in the theorem's context and is definitionally equal to the rest of the statement):

```lean
(∀ x, C x → H i x) → ∀ x, (∀ j, j ≠ i → H j x) → C x → H i x
```

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample(s) | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `h : NecessaryAt H C i` | The premise being weakened to its relative form. | tight | `unweakenableAt_of_necessaryAt_ce_not_necessary` | x ≤ 1, y ≤ 1 ⊢ x + y ≤ 2 over Nat × Nat, i = h1 |

Counterexample statements (verbatim; each states that the other hypotheses hold and the conclusion fails):

```lean
-- lean/Toy/Ledger/Strength.lean:91
theorem unweakenableAt_of_necessaryAt_ce_not_necessary : ¬ UnweakenableAt sumH sumC .h1 :=
```

**Non-vacuity witness:** x ≥ 1, x ≤ 1 ⊢ x = 1: x ≥ 1 is necessary for x = 1. (`unweakenableAt_of_necessaryAt_nonvacuity`)

```lean
-- lean/Toy/Ledger/Strength.lean:95
theorem unweakenableAt_of_necessaryAt_nonvacuity : NecessaryAt pinH pinC .h1 :=
```

**Prior art:**

- No specific prior source; an elementary consequence of the definitions, restated in this package's vocabulary.

**Design question.** Which of the readings 'necessary' and 'cannot be weakened' implies the other? (Necessary implies cannot be weakened; not conversely. Reference point.)

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims**, result 7.

#### 8. `tight_necessary_unweakenable_six_combinations`

- **Kind:** counterexample · **Tier:** T1 · **Depth:** shallow
- **Plain claim:** In sufficient, non-vacuous two-hypothesis instances over Nat or Nat × Nat, all six combinations of (tight, necessary, unweakenable) at a hypothesis that are compatible with 'necessary implies unweakenable' occur: TNU (x ≥ 1, x ≤ 1 ⊢ x = 1), not-T NU (x = 1, x = 1 ⊢ x = 1), T not-N not-U (x ≤ 1, y ≤ 1 ⊢ x + y ≤ 2), not-T not-N not-U (x ≥ 1, x ≤ 1 ⊢ x ≤ 1), T not-N U (x = 0, y = 0 ⊢ x = y), not-T not-N U (x = 0, (x = 0 ∧ y = 0) ⊢ x = y).

**Lean statement** (`tight_necessary_unweakenable_six_combinations`, verbatim):

```lean
-- lean/Toy/Ledger/Strength.lean:107-120
theorem tight_necessary_unweakenable_six_combinations :
    (Sufficient pinH pinC ∧ NonVacuous pinH ∧
      TightAt pinH pinC .h1 ∧ NecessaryAt pinH pinC .h1 ∧ UnweakenableAt pinH pinC .h1) ∧
    (Sufficient dupH pinC ∧ NonVacuous dupH ∧
      ¬ TightAt dupH pinC .h1 ∧ NecessaryAt dupH pinC .h1 ∧ UnweakenableAt dupH pinC .h1) ∧
    (Sufficient sumH sumC ∧ NonVacuous sumH ∧
      TightAt sumH sumC .h1 ∧ ¬ NecessaryAt sumH sumC .h1 ∧ ¬ UnweakenableAt sumH sumC .h1) ∧
    (Sufficient pinH pinWeakC ∧ NonVacuous pinH ∧
      ¬ TightAt pinH pinWeakC .h1 ∧ ¬ NecessaryAt pinH pinWeakC .h1 ∧
      ¬ UnweakenableAt pinH pinWeakC .h1) ∧
    (Sufficient eqH eqC ∧ NonVacuous eqH ∧
      TightAt eqH eqC .h1 ∧ ¬ NecessaryAt eqH eqC .h1 ∧ UnweakenableAt eqH eqC .h1) ∧
    (Sufficient entH eqC ∧ NonVacuous entH ∧
      ¬ TightAt entH eqC .h1 ∧ ¬ NecessaryAt entH eqC .h1 ∧ UnweakenableAt entH eqC .h1) := by
```

Definitions used: `pinH`, `pinC`, `pinWeakC`, `dupH`, `sumH`, `sumC`, `eqH`, `eqC`, `entH` (quoted under **Running examples** and **Definitions**).

**Hypothesis ledger.**

No hypotheses: the statement is about concrete instances.

**Non-vacuity witness:** Each instance is proved sufficient and non-vacuous inside the statement. (`tight_necessary_unweakenable_six_combinations`)

**Prior art:**

- No specific prior source; an elementary consequence of the definitions, restated in this package's vocabulary.

**Design question.** When a ledger says 'tight' for a theorem that holds, may a reader infer that the hypothesis is necessary or cannot be weakened? (No.)

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims**, result 8.

#### 9. `unweakenableAt_and_not_tightAt_iff_entailed_by_others_of_sufficient`

- **Kind:** characterization · **Tier:** T0 · **Depth:** shallow
- **Plain claim:** Suppose the hypotheses H suffice for C. Then hypothesis i is unweakenable and not tight exactly when the other hypotheses entail H i.

**Lean statement** (`unweakenableAt_and_not_tightAt_iff_entailed_by_others_of_sufficient`, verbatim):

```lean
-- lean/Toy/Ledger/Strength.lean:30-32
theorem unweakenableAt_and_not_tightAt_iff_entailed_by_others_of_sufficient
    {H : ι → M → Prop} {C : M → Prop} (hs : Sufficient H C) (i : ι) :
    (UnweakenableAt H C i ∧ ¬ TightAt H C i) ↔ ∀ x, (∀ j, j ≠ i → H j x) → H i x :=
```

Unfolded statement of `unweakenableAt_and_not_tightAt_iff_entailed_by_others_of_sufficient` (key definitions replaced by their bodies; this Lean term elaborates in the theorem's context and is definitionally equal to the rest of the statement):

```lean
(∀ x, (∀ j, H j x) → C x) → ∀ i : ι,
  ((∀ x, (∀ j, j ≠ i → H j x) → C x → H i x) ∧ ¬ (∃ x, (∀ j, j ≠ i → H j x) ∧ ¬ C x)) ↔
    ∀ x, (∀ j, j ≠ i → H j x) → H i x
```

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample(s) | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hs : Sufficient H C` | Used for the right-to-left direction (an entailed hypothesis is not tight); without it that direction fails on the counterexample. | tight | `unweakenableAt_and_not_tightAt_iff_entailed_ce_not_sufficient` | a one-hypothesis family over Unit, True ⊢ False (the theorem is false) |

Counterexample statements (verbatim; each states that the other hypotheses hold and the conclusion fails):

```lean
-- lean/Toy/Ledger/Strength.lean:169-171
theorem unweakenableAt_and_not_tightAt_iff_entailed_ce_not_sufficient :
    ¬ ((UnweakenableAt topH falseC () ∧ ¬ TightAt topH falseC ()) ↔
        ∀ x, (∀ j, j ≠ () → topH j x) → topH () x) := by
```

**Non-vacuity witness:** x = 0, (x = 0 ∧ y = 0) ⊢ x = y over Nat × Nat is sufficient, and at h1 the left side holds (unweakenable and not tight); by the result the right side holds there too. (`unweakenableAt_and_not_tightAt_iff_entailed_nonvacuity`)

```lean
-- lean/Toy/Ledger/Strength.lean:178-179
theorem unweakenableAt_and_not_tightAt_iff_entailed_nonvacuity :
    Sufficient entH eqC ∧ (UnweakenableAt entH eqC .h1 ∧ ¬ TightAt entH eqC .h1) := by
```

**Prior art:**

- No specific prior source; an elementary consequence of the definitions, restated in this package's vocabulary.

**Design question.** For a theorem that holds, when is a hypothesis that is not tight still impossible to weaken? (Exactly when the other hypotheses entail it.)

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims**, result 9.

#### 10. `weakestPremise_is_weakest_replacement`

- **Kind:** characterization · **Tier:** T0 · **Depth:** shallow
- **Plain claim:** For any hypothesis family H, conclusion C and index i: (1) replacing H i by a premise H' keeps sufficiency exactly when H' implies WeakestPremise H C i ('if the other hypotheses hold then C'); (2) WeakestPremise H C i is itself a valid replacement; (3) the original theorem holds exactly when H i implies it; (4) hypothesis i is not tight exactly when WeakestPremise H C i holds at every model.

**Lean statement** (`weakestPremise_is_weakest_replacement`, verbatim):

```lean
-- lean/Toy/Ledger/Strength.lean:45-51
theorem weakestPremise_is_weakest_replacement
    (H : ι → M → Prop) (C : M → Prop) (i : ι) :
    (∀ H' : M → Prop,
      Sufficient (replaceAt H i H') C ↔ ∀ x, H' x → WeakestPremise H C i x) ∧
    Sufficient (replaceAt H i (WeakestPremise H C i)) C ∧
    (Sufficient H C ↔ ∀ x, H i x → WeakestPremise H C i x) ∧
    ((∀ x, WeakestPremise H C i x) ↔ ¬ TightAt H C i) := by
```

Unfolded statement of `weakestPremise_is_weakest_replacement` (key definitions replaced by their bodies; this Lean term elaborates in the theorem's context and is definitionally equal to the rest of the statement):

```lean
(∀ H' : M → Prop,
    (∀ x, (∀ j, (j = i → H' x) ∧ (j ≠ i → H j x)) → C x) ↔
      ∀ x, H' x → (∀ j, j ≠ i → H j x) → C x) ∧
  (∀ x, (∀ j, (j = i → ((∀ k, k ≠ i → H k x) → C x)) ∧ (j ≠ i → H j x)) → C x) ∧
  ((∀ x, (∀ j, H j x) → C x) ↔ ∀ x, H i x → (∀ j, j ≠ i → H j x) → C x) ∧
  ((∀ x, (∀ j, j ≠ i → H j x) → C x) ↔ ¬ ∃ x, (∀ j, j ≠ i → H j x) ∧ ¬ C x)
```

**Hypothesis ledger.**

No hypotheses: the statement holds for all values of its parameters.

**Non-vacuity witness:** x ≤ 1, y ≤ 1 ⊢ x + y ≤ 2: replacing x ≤ 1 by x + y ≤ 2 keeps sufficiency; h1 is tight; the weakest premise holds at (2, 0), where x ≤ 1 fails. (`weakestPremise_sum_nonvacuity`)

```lean
-- lean/Toy/Ledger/Strength.lean:198-200
theorem weakestPremise_sum_nonvacuity :
    Sufficient (replaceAt sumH .h1 sumC) sumC ∧ TightAt sumH sumC .h1 ∧
      WeakestPremise sumH sumC .h1 (2, 0) ∧ ¬ sumH .h1 (2, 0) :=
```

**Prior art:**

- Fangzhen Lin, "On strongest necessary and weakest sufficient conditions", Artificial Intelligence 128(1-2):143-159, 2001, DOI 10.1016/S0004-3702(01)00070-4: weakest sufficient conditions (WSC). As restated in Kaile Su, Abdul Sattar, Guanfeng Lv, Yan Zhang, "Variable Forgetting in Reasoning about Knowledge", Journal of Artificial Intelligence Research 35:677-716, 2009, DOI 10.1613/jair.2750, Definition 5 and Proposition 6, the WSC is characterized as 'forall(V - V')(theta => alpha)'. With the unrestricted vocabulary (V' = V) the WSC of C under background theta is theta => C, which is WeakestPremise here (theta = the other hypotheses).
- Mathlib (leanprover-community/mathlib4 commit 3eae40f5eb25c5934211edf662d3b24c5afbe47a): Mathlib/Order/Heyting/Basic.lean line 98, GeneralizedHeytingAlgebra.le_himp_iff (a ≤ b ⇨ c <-> a ⊓ b ≤ c); the first conjunct is this adjunction for predicates on M, with b = the other hypotheses and c = C.

**Design question.** What is the weakest premise that can replace one hypothesis while the others are kept, and how does it relate to tightness?

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims**, result 10.

#### 11. `unweakenableAt_characterizations_of_sufficient`

- **Kind:** characterization · **Tier:** T0 · **Depth:** shallow
- **Plain claim:** Suppose the hypotheses H suffice for C. Then hypothesis i is unweakenable exactly when (1) H i agrees with WeakestPremise H C i wherever the other hypotheses hold; exactly when (2) every weakening H' of H i that keeps the theorem true agrees with H i wherever the other hypotheses hold; and exactly when (3) H i agrees with C wherever the other hypotheses hold.

**Lean statement** (`unweakenableAt_characterizations_of_sufficient`, verbatim):

```lean
-- lean/Toy/Ledger/Strength.lean:69-76
theorem unweakenableAt_characterizations_of_sufficient
    {H : ι → M → Prop} {C : M → Prop} (hs : Sufficient H C) (i : ι) :
    (UnweakenableAt H C i ↔
      ∀ x, (∀ j, j ≠ i → H j x) → (H i x ↔ WeakestPremise H C i x)) ∧
    (UnweakenableAt H C i ↔
      ∀ H' : M → Prop, (∀ x, H i x → H' x) → Sufficient (replaceAt H i H') C →
        ∀ x, (∀ j, j ≠ i → H j x) → H' x → H i x) ∧
    (UnweakenableAt H C i ↔ ∀ x, (∀ j, j ≠ i → H j x) → (H i x ↔ C x)) := by
```

Unfolded statement of `unweakenableAt_characterizations_of_sufficient` (key definitions replaced by their bodies; this Lean term elaborates in the theorem's context and is definitionally equal to the rest of the statement):

```lean
(∀ x, (∀ j, H j x) → C x) → ∀ i : ι,
  ((∀ x, (∀ j, j ≠ i → H j x) → C x → H i x) ↔
      ∀ x, (∀ j, j ≠ i → H j x) → (H i x ↔ ((∀ j, j ≠ i → H j x) → C x))) ∧
  ((∀ x, (∀ j, j ≠ i → H j x) → C x → H i x) ↔
      ∀ H' : M → Prop, (∀ x, H i x → H' x) →
        (∀ x, (∀ j, (j = i → H' x) ∧ (j ≠ i → H j x)) → C x) →
          ∀ x, (∀ j, j ≠ i → H j x) → H' x → H i x) ∧
  ((∀ x, (∀ j, j ≠ i → H j x) → C x → H i x) ↔
      ∀ x, (∀ j, j ≠ i → H j x) → (H i x ↔ C x))
```

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample(s) | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hs : Sufficient H C` | Used by each characterization. Without it each characterization can fail: on True ⊢ False over Unit the first and the third fail (unweakenableAt_first_characterization_fails_true_false, unweakenableAt_third_characterization_fails_true_false), and on b = true ⊢ b = false over Bool the second fails (unweakenableAt_iff_weakenings_ce_not_sufficient). | tight | `unweakenableAt_characterizations_ce_not_sufficient`, `unweakenableAt_iff_weakenings_ce_not_sufficient` | True ⊢ False over Unit, a one-hypothesis family (the theorem is false; unweakenableAt_characterizations_ce_not_sufficient refutes the conjunction of the three characterizations, through the failure of the first, unweakenableAt_true_false_disagrees; the first and the third also fail separately, unweakenableAt_first_characterization_fails_true_false and unweakenableAt_third_characterization_fails_true_false), and b = true ⊢ b = false over Bool, a one-hypothesis family (the theorem is false; the second characterization fails, while the first holds, unweakenableAt_first_characterization_holds_flip) |

Counterexample statements (verbatim; each states that the other hypotheses hold and the conclusion fails):

```lean
-- lean/Toy/Ledger/Strength.lean:231-238
theorem unweakenableAt_characterizations_ce_not_sufficient :
    ¬ ((UnweakenableAt topH falseC () ↔
          ∀ x, (∀ j, j ≠ () → topH j x) → (topH () x ↔ WeakestPremise topH falseC () x)) ∧
        (UnweakenableAt topH falseC () ↔
          ∀ H' : Unit → Prop, (∀ x, topH () x → H' x) → Sufficient (replaceAt topH () H') falseC →
            ∀ x, (∀ j, j ≠ () → topH j x) → H' x → topH () x) ∧
        (UnweakenableAt topH falseC () ↔
          ∀ x, (∀ j, j ≠ () → topH j x) → (topH () x ↔ falseC x))) :=
-- lean/Toy/Ledger/Strength.lean:257-260
theorem unweakenableAt_iff_weakenings_ce_not_sufficient :
    ¬ (UnweakenableAt flipH flipC () ↔
        ∀ H' : Bool → Prop, (∀ x, flipH () x → H' x) → Sufficient (replaceAt flipH () H') flipC →
          ∀ x, (∀ j, j ≠ () → flipH j x) → H' x → flipH () x) := by
```

Supporting statements cited in this ledger, verbatim: `unweakenableAt_true_false_disagrees` (from which `unweakenableAt_characterizations_ce_not_sufficient` is derived: on True ⊢ False the left side of the first characterization holds and its right side fails), the failures of the first and of the third characterization on True ⊢ False, each stated on its own, and the first characterization holding on b = true ⊢ b = false:

```lean
-- lean/Toy/Ledger/Strength.lean:222-224
theorem unweakenableAt_true_false_disagrees :
    UnweakenableAt topH falseC () ∧
      ¬ ∀ x, (∀ j, j ≠ () → topH j x) → (topH () x ↔ WeakestPremise topH falseC () x) := by
-- lean/Toy/Ledger/SupportingLemmas.lean:26-28
theorem unweakenableAt_first_characterization_fails_true_false :
    ¬ (UnweakenableAt topH falseC () ↔
        ∀ x, (∀ j, j ≠ () → topH j x) → (topH () x ↔ WeakestPremise topH falseC () x)) :=
-- lean/Toy/Ledger/SupportingLemmas.lean:34-36
theorem unweakenableAt_third_characterization_fails_true_false :
    ¬ (UnweakenableAt topH falseC () ↔
        ∀ x, (∀ j, j ≠ () → topH j x) → (topH () x ↔ falseC x)) := by
-- lean/Toy/Ledger/Strength.lean:273-275
theorem unweakenableAt_first_characterization_holds_flip :
    UnweakenableAt flipH flipC () ↔
      ∀ x, (∀ j, j ≠ () → flipH j x) → (flipH () x ↔ WeakestPremise flipH flipC () x) := by
```

**Non-vacuity witness:** x ≥ 1, x ≤ 1 ⊢ x = 1 is sufficient and h1 is unweakenable. (`unweakenableAt_characterizations_nonvacuity`)

```lean
-- lean/Toy/Ledger/Strength.lean:242-243
theorem unweakenableAt_characterizations_nonvacuity :
    Sufficient pinH pinC ∧ UnweakenableAt pinH pinC .h1 :=
```

**Prior art:**

- Fangzhen Lin, "On strongest necessary and weakest sufficient conditions", Artificial Intelligence 128(1-2):143-159, 2001, DOI 10.1016/S0004-3702(01)00070-4: weakest sufficient conditions (WSC). As restated in Kaile Su, Abdul Sattar, Guanfeng Lv, Yan Zhang, "Variable Forgetting in Reasoning about Knowledge", Journal of Artificial Intelligence Research 35:677-716, 2009, DOI 10.1613/jair.2750, Definition 5 and Proposition 6, the WSC is characterized as 'forall(V - V')(theta => alpha)'. With the unrestricted vocabulary (V' = V) the WSC of C under background theta is theta => C, which is WeakestPremise here (theta = the other hypotheses). Neither source defines UnweakenableAt or characterizes it; that notion and its three characterizations are stated here.

**Design question.** When a theorem holds, what exactly does 'this hypothesis cannot be weakened' mean?

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims**, result 11.

#### 12. `irredundant_sufficient_subfamilies_of_sizes_two_and_one`

- **Kind:** counterexample · **Tier:** T0 · **Depth:** shallow
- **Plain claim:** Over the vocabulary x ≤ 1, y ≤ 1, x + y ≤ 2 on Nat × Nat and the conclusion x + y ≤ 2, both the two-member subfamily {x ≤ 1, y ≤ 1} and the one-member subfamily {x + y ≤ 2} are sufficient, irredundant and non-vacuous.

**Lean statement** (`irredundant_sufficient_subfamilies_of_sizes_two_and_one`, verbatim):

```lean
-- lean/Toy/Ledger/Families.lean:73-80
theorem irredundant_sufficient_subfamilies_of_sizes_two_and_one :
    (∀ j, j ≠ Three.h3 ↔ (j = .h1 ∨ j = .h2)) ∧
    Sufficient (restrict (fun j => j ≠ Three.h3) sumVocab) sumC ∧
    Irredundant (restrict (fun j => j ≠ Three.h3) sumVocab) sumC ∧
    NonVacuous (restrict (fun j => j ≠ Three.h3) sumVocab) ∧
    Sufficient (restrict (fun j => j = Three.h3) sumVocab) sumC ∧
    Irredundant (restrict (fun j => j = Three.h3) sumVocab) sumC ∧
    NonVacuous (restrict (fun j => j = Three.h3) sumVocab) := by
```

Definitions used: `sumVocab`, `sumC`, `restrict` (quoted under **Running examples** and **Definitions**).

**Hypothesis ledger.**

No hypotheses: the statement is about concrete instances.

**Non-vacuity witness:** Both subfamilies are proved non-vacuous (witness (0, 0)) inside the statement. (`irredundant_sufficient_subfamilies_of_sizes_two_and_one`)

**Prior art:**

- Thomas Eiter, Georg Gottlob, "The complexity of logic-based abduction", Journal of the ACM 42(1):3-42, 1995, DOI 10.1145/200836.200838. Abstract: candidate abductive explanations 'are usually subjected to minimality criteria such as subset-minimality, minimal cardinality, minimal weight, or minimality under prioritization of individual hypotheses'.
- Alexey Ignatiev, Nina Narodytska, Joao Marques-Silva, "Abduction-Based Explanations for Machine Learning Models", Proceedings of the AAAI Conference on Artificial Intelligence 33(01):1511-1519, 2019, DOI 10.1609/aaai.v33i01.33011511. Definition 1: the explanations are the subsets S of the hypotheses H with F ∧ S consistent and F ∧ S entailing E; subset-minimal and cardinality-minimal explanations are distinguished.
- Mark H. Liffiton, Karem A. Sakallah, "Algorithms for Computing Minimal Unsatisfiable Subsets of Constraints", Journal of Automated Reasoning 40(1):1-33, 2008 (online 2007), DOI 10.1007/s10817-007-9084-z. Abstract: a sound and complete algorithm 'for producing all MUSes of an unsatisfiable constraint system'; complete results can be intractably large.

**Design question.** Does 'every hypothesis is tight' single out a unique or smallest sufficient hypothesis set? (No.)

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims**, result 12.

#### 13. `subfamily_eq_of_sufficient_of_irredundant_superfamily`

- **Kind:** theorem · **Tier:** T0 · **Depth:** shallow
- **Plain claim:** Let S and T select subfamilies of a vocabulary H. If the subfamily selected by S is sufficient for C, the subfamily selected by T is irredundant for C, and S ⊆ T, then S = T. In particular, of two sufficient, irredundant subfamilies, neither strictly contains the other.

**Lean statement** (`subfamily_eq_of_sufficient_of_irredundant_superfamily`, verbatim):

```lean
-- lean/Toy/Ledger/Families.lean:27-30
theorem subfamily_eq_of_sufficient_of_irredundant_superfamily
    {H : ι → M → Prop} {C : M → Prop} {S T : ι → Prop}
    (hS : Sufficient (restrict S H) C) (hT : Irredundant (restrict T H) C)
    (hST : ∀ i, S i → T i) : S = T := by
```

Unfolded statement of `subfamily_eq_of_sufficient_of_irredundant_superfamily` (key definitions replaced by their bodies; this Lean term elaborates in the theorem's context and is definitionally equal to the rest of the statement):

```lean
(∀ x, (∀ j : Subtype S, H j.1 x) → C x) →
  (∀ k : Subtype T, ∃ x, (∀ j : Subtype T, j ≠ k → H j.1 x) ∧ ¬ C x) →
    (∀ i, S i → T i) → S = T
```

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample(s) | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hS : Sufficient (restrict S H) C` | Rules out a model that satisfies every member selected by S and violates C; the proof applies it to the tightness witness that hT supplies at an index selected by T and not by S. | tight | `subfamily_eq_ce_not_sufficient` | x ≥ 1, x ≤ 1 ⊢ x = 1 over Nat with S = {x ≥ 1} (irredundant, non-vacuous, not sufficient) and T = both hypotheses |
| `hT : Irredundant (restrict T H) C` | Supplies, for an index selected by T and not by S, a model that satisfies every other member selected by T and violates C. | tight | `subfamily_eq_ce_not_irredundant` | the valid conclusion True over Nat, S = the empty family, T = {True} |
| `hST : ∀ i, S i → T i` | Embeds S into T, so that a model satisfying every member selected by T except one index outside S satisfies every member selected by S. | tight | `subfamily_eq_ce_not_contained` | duplicated hypotheses x = 1, x = 1 ⊢ x = 1 over Nat, S = {h2}, T = {h1} |

Counterexample statements (verbatim; each states that the other hypotheses hold and the conclusion fails):

```lean
-- lean/Toy/Ledger/Families.lean:157-164
theorem subfamily_eq_ce_not_sufficient :
    Irredundant (restrict (fun _ : Two => True) pinH) pinC ∧
      (∀ i : Two, (fun j => j = Two.h1) i → (fun _ => True) i) ∧
      (fun j : Two => j = Two.h1) ≠ (fun _ => True) ∧
      Sufficient (restrict (fun _ : Two => True) pinH) pinC ∧
      Irredundant (restrict (fun j : Two => j = Two.h1) pinH) pinC ∧
      NonVacuous (restrict (fun j : Two => j = Two.h1) pinH) ∧
      ¬ Sufficient (restrict (fun j : Two => j = Two.h1) pinH) pinC := by
-- lean/Toy/Ledger/Families.lean:188-191
theorem subfamily_eq_ce_not_irredundant :
    Sufficient (restrict (fun _ : Unit => False) (single (trueC (M := Nat)))) trueC ∧
      (∀ i : Unit, (fun _ => False) i → (fun _ => True) i) ∧
      (fun _ : Unit => False) ≠ (fun _ => True) :=
-- lean/Toy/Ledger/Families.lean:197-200
theorem subfamily_eq_ce_not_contained :
    Sufficient (restrict (fun j => j = Two.h2) dupH) pinC ∧
      Irredundant (restrict (fun j => j = Two.h1) dupH) pinC ∧
      (fun j => j = Two.h2) ≠ (fun j => j = Two.h1) := by
```

**Non-vacuity witness:** S = T = {x ≤ 1, y ≤ 1} within the vocabulary x ≤ 1, y ≤ 1, x + y ≤ 2 and the conclusion x + y ≤ 2. (`subfamily_eq_nonvacuity`)

```lean
-- lean/Toy/Ledger/Families.lean:210-213
theorem subfamily_eq_nonvacuity :
    Sufficient (restrict (fun j => j ≠ Three.h3) sumVocab) sumC ∧
      Irredundant (restrict (fun j => j ≠ Three.h3) sumVocab) sumC ∧
      (∀ i, (fun j => j ≠ Three.h3) i → (fun j => j ≠ Three.h3) i) :=
```

**Prior art:**

- Mathlib (leanprover-community/mathlib4 commit 3eae40f5eb25c5934211edf662d3b24c5afbe47a): Mathlib/Order/Minimal.lean line 348, Set.minimal_iff_forall_sdiff_singleton (for a predicate P on sets that is closed under supersets, Minimal P s <-> P s and no s \ {{x}} with x in s satisfies P); line 300, Minimal.eq_of_superset (Minimal P s -> P t -> t ⊆ s -> s = t); Mathlib/Order/Antichain.lean line 313, setOfPred_minimal_antichain (the minimal elements of a predicate form an antichain). These are the order-theoretic forms of the statements here, with P = sufficiency of a subfamily.
- Sven Ove Hansson, "Kernel contraction", Journal of Symbolic Logic 59(3):845-859, 1994, DOI 10.2307/2275912. Kernel contraction acts on the alpha-kernels of a belief base B, its inclusion-minimal subsets implying alpha (definition as restated in Renata Wassermann, "Local Diagnosis", arXiv:cs/0003051, 2000, Definition 1). A sufficient, irredundant subfamily of a vocabulary is the analogue of an alpha-kernel, with implication read semantically over the model type.
- Mark H. Liffiton, Karem A. Sakallah, "Algorithms for Computing Minimal Unsatisfiable Subsets of Constraints", Journal of Automated Reasoning 40(1):1-33, 2008 (online 2007), DOI 10.1007/s10817-007-9084-z. Abstract: a sound and complete algorithm 'for producing all MUSes of an unsatisfiable constraint system'; complete results can be intractably large.

**Design question.** Can an irredundant hypothesis set strictly contain a sufficient hypothesis set (in particular, another sufficient, irredundant one)? (No.)

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims**, result 13.

#### 14. `irredundant_vacuous_and_nonvacuous_tightless`

- **Kind:** counterexample · **Tier:** T1 · **Depth:** shallow
- **Plain claim:** A complete tightness ledger does not certify non-vacuity, and non-vacuity certifies no tightness: on Fin 3, x = 1, x = 2 ⊢ False is sufficient and irredundant but vacuous (so its family with the negated conclusion is not minimally unsatisfiable); over Unit, True ⊢ True is sufficient and non-vacuous but its only hypothesis is not tight.

**Lean statement** (`irredundant_vacuous_and_nonvacuous_tightless`, verbatim):

```lean
-- lean/Toy/Ledger/Families.lean:223-226
theorem irredundant_vacuous_and_nonvacuous_tightless :
    (Sufficient vacH falseC ∧ Irredundant vacH falseC ∧ ¬ NonVacuous vacH ∧
      ¬ MinimalUnsatisfiable (withNegatedConclusion vacH falseC)) ∧
    (Sufficient topH trueC ∧ NonVacuous topH ∧ ∀ i, ¬ TightAt topH trueC i) := by
```

Definitions used: `vacH`, `falseC`, `topH`, `trueC` (quoted under **Running examples** and **Definitions**).

**Hypothesis ledger.**

No hypotheses: the statement is about concrete instances.

**Non-vacuity witness:** Both instances are concrete; the second is non-vacuous (witness ()). The first is vacuous by design. (`irredundant_vacuous_and_nonvacuous_tightless`)

**Prior art:**

- Ilan Beer, Shoham Ben-David, Cindy Eisner, Yoav Rodeh, "Efficient Detection of Vacuity in Temporal Model Checking", Formal Methods in System Design 18(2):141-163, 2001, DOI 10.1023/A:1008779610539. Abstract: an implication can be 'trivially valid because the pre-condition of the implication is not satisfiable' (antecedent failure), called vacuity; an 'interesting witness' is a non-trivial example of validity. Conference version: "Efficient detection of vacuity in ACTL formulas", CAV 1997, LNCS vol. 1254, pp. 279-290, DOI 10.1007/3-540-63166-6_28.
- Orna Kupferman, Moshe Y. Vardi, "Vacuity detection in temporal model checking", International Journal on Software Tools for Technology Transfer 4(2):224-233, 2003, DOI 10.1007/s100090100062. Abstract: vacuity checks 'whether all the subformulas of the specification affect its truth value in the system'; interesting witnesses. Earlier version: CHARME 1999, LNCS vol. 1703, pp. 82-98, DOI 10.1007/3-540-48153-2_8.
- Derek L. Beatty, Randal E. Bryant, "Formally verifying a microprocessor using a simulation methodology", Proceedings of the 31st Design Automation Conference (DAC 1994), pp. 596-602, DOI 10.1145/196244.196575: 'One of the principal dangers of formal verification is what we have called antecedent failure'; footnote 10: 'Techniques that are based entirely on pure logic, such as HOL, are especially prone to it.' Their remedy is 'to check that the antecedent is, in fact, always true'. On a nonempty set of models or states this is a stronger requirement than NonVacuous (one model of the antecedent): it implies NonVacuous there (nonVacuous_of_forall_of_nonempty), and not conversely (nonVacuous_pin_antecedent_not_everywhere). Without nonemptiness it does not imply NonVacuous: over the empty model type the antecedent True holds at every model, vacuously, and is not satisfiable (antecedent_everywhere_not_nonVacuous_empty).

**Design question.** Does a complete tightness ledger make a non-vacuity witness redundant, or the reverse? (Neither.)

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims**, result 14.

#### 15. `not_valid_of_tightAt`

- **Kind:** theorem · **Tier:** T0 · **Depth:** definitional
- **Plain claim:** If hypothesis i is tight for C, then C is not valid over the model type (some model violates C).

**Lean statement** (`not_valid_of_tightAt`, verbatim):

```lean
-- lean/Toy/Ledger/Families.lean:42-43
theorem not_valid_of_tightAt {H : ι → M → Prop} {C : M → Prop} {i : ι}
    (h : TightAt H C i) : ¬ ∀ x, C x :=
```

Unfolded statement of `not_valid_of_tightAt` (key definitions replaced by their bodies; this Lean term elaborates in the theorem's context and is definitionally equal to the rest of the statement):

```lean
(∃ x, (∀ j, j ≠ i → H j x) ∧ ¬ C x) → ¬ ∀ x, C x
```

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample(s) | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `h : TightAt H C i` | Supplies a model violating C. | tight | `not_valid_of_tightAt_ce_not_tight` | the valid conclusion True over Unit |

Counterexample statements (verbatim; each states that the other hypotheses hold and the conclusion fails):

```lean
-- lean/Toy/Ledger/Families.lean:240
theorem not_valid_of_tightAt_ce_not_tight : ¬ ¬ ∀ x : Unit, trueC x :=
```

**Non-vacuity witness:** h1 of x ≥ 1, x ≤ 1 ⊢ x = 1 is tight. (`not_valid_of_tightAt_nonvacuity`)

```lean
-- lean/Toy/Ledger/Families.lean:244
theorem not_valid_of_tightAt_nonvacuity : TightAt pinH pinC .h1 :=
```

**Positive control** (a nearby setting where the conclusion fails): `not_valid_of_tightAt_ce_not_tight`, quoted in the ledger above.

**Prior art:**

- No specific prior source; an elementary consequence of the definitions, restated in this package's vocabulary.

**Design question.** What does a single tight entry certify about the conclusion? (That it is not valid over the model type. Reference point.)

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims**, result 15.

#### 16. `schematic_ledger_irredundant_nonvacuous`

- **Kind:** counterexample · **Tier:** T1 · **Depth:** shallow
- **Plain claim:** The schema P ∨ C, ¬ P ⊢ C is sufficient for every instantiation of the predicates P and C over every model type N : Type u; yet for P x := (x.1 = true) and C x := (x.2 = true) over Bool × Bool both hypotheses are tight and the family is non-vacuous.

**Lean statement** (`schematic_ledger_irredundant_nonvacuous`, verbatim):

```lean
-- lean/Toy/Ledger/Families.lean:262-266
theorem schematic_ledger_irredundant_nonvacuous :
    (∀ (N : Type u) (P C : N → Prop), Sufficient (schemaH P C) C) ∧
    Irredundant (schemaH (fun p : Bool × Bool => p.1 = true) (fun p => p.2 = true))
      (fun p => p.2 = true) ∧
    NonVacuous (schemaH (fun p : Bool × Bool => p.1 = true) (fun p => p.2 = true)) := by
```

Definitions used: `schemaH` (quoted under **Running examples** and **Definitions**).

**Hypothesis ledger.**

No hypotheses: the statement is about concrete instances.

**Non-vacuity witness:** (false, true) satisfies both hypotheses of the Bool × Bool instance. (`schematic_ledger_irredundant_nonvacuous`)

**Prior art:**

- No specific prior source; an elementary consequence of the definitions, restated in this package's vocabulary.

**Design question.** Does a sufficient, irredundant, non-vacuous ledger certify that a theorem is deep or non-trivial? (No.)

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims**, result 16.

#### 17. `not_single_entails_of_irredundant_of_exists_other`

- **Kind:** theorem · **Tier:** T0 · **Depth:** definitional
- **Plain claim:** If every hypothesis of H is tight for C and some hypothesis other than i exists, then hypothesis i alone does not entail C over the whole model type.

**Lean statement** (`not_single_entails_of_irredundant_of_exists_other`, verbatim):

```lean
-- lean/Toy/Ledger/Families.lean:60-61
theorem not_single_entails_of_irredundant_of_exists_other {H : ι → M → Prop} {C : M → Prop}
    {i : ι} (hirr : Irredundant H C) (hother : ∃ j, j ≠ i) : ¬ ∀ x, H i x → C x :=
```

Unfolded statement of `not_single_entails_of_irredundant_of_exists_other` (key definitions replaced by their bodies; this Lean term elaborates in the theorem's context and is definitionally equal to the rest of the statement):

```lean
(∀ k, ∃ x, (∀ j, j ≠ k → H j x) ∧ ¬ C x) → (∃ j, j ≠ i) → ¬ ∀ x, H i x → C x
```

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample(s) | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hirr : Irredundant H C` | Makes the other hypothesis j tight; a tightness witness for j satisfies H i and violates C. | tight | `not_single_entails_ce_not_irredundant` | x = 1, True ⊢ x = 1 over Nat |
| `hother : ∃ j, j ≠ i` | Supplies the other index j. | tight | `not_single_entails_ce_single_hypothesis` | the one-hypothesis family x = 1 ⊢ x = 1 over Nat |

Counterexample statements (verbatim; each states that the other hypotheses hold and the conclusion fails):

```lean
-- lean/Toy/Ledger/Families.lean:332-333
theorem not_single_entails_ce_not_irredundant :
    (∃ j, j ≠ Two.h1) ∧ ∀ x, pair pinC trueC .h1 x → pinC x :=
-- lean/Toy/Ledger/Families.lean:339-340
theorem not_single_entails_ce_single_hypothesis :
    Irredundant (single pinC) pinC ∧ ∀ x, single pinC () x → pinC x :=
```

**Non-vacuity witness:** x ≥ 1, x ≤ 1 ⊢ x = 1 is irredundant and has two hypotheses. (`not_single_entails_nonvacuity`)

```lean
-- lean/Toy/Ledger/Families.lean:344
theorem not_single_entails_nonvacuity : Irredundant pinH pinC ∧ ∃ j, j ≠ Two.h1 :=
```

**Positive control** (a nearby setting where the conclusion fails): `not_single_entails_ce_single_hypothesis`, quoted in the ledger above.

**Prior art:**

- No specific prior source; an elementary consequence of the definitions, restated in this package's vocabulary.

**Design question.** In a ledger with at least two hypotheses, all tight, can one hypothesis alone entail the conclusion over the model type? (No; it can still agree with the conclusion wherever another hypothesis holds.)

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims**, result 17.

#### 18. `sufficientIn_antitone_and_tightIn_monotone`

- **Kind:** theorem · **Tier:** T0 · **Depth:** definitional
- **Plain claim:** Let P ⊆ Q be classes of models. Then sufficiency over Q gives sufficiency over P, and for every index i, tightness of i over P gives tightness of i over Q.

**Lean statement** (`sufficientIn_antitone_and_tightIn_monotone`, verbatim):

```lean
-- lean/Toy/Ledger/Classes.lean:40-42
theorem sufficientIn_antitone_and_tightIn_monotone {P Q : M → Prop} {H : ι → M → Prop}
    {C : M → Prop} (hPQ : ∀ x, P x → Q x) :
    (SufficientIn Q H C → SufficientIn P H C) ∧ (∀ i, TightIn P H C i → TightIn Q H C i) :=
```

Unfolded statement of `sufficientIn_antitone_and_tightIn_monotone` (key definitions replaced by their bodies; this Lean term elaborates in the theorem's context and is definitionally equal to the rest of the statement):

```lean
(∀ x, P x → Q x) →
  ((∀ x, Q x → (∀ j, H j x) → C x) → ∀ x, P x → (∀ j, H j x) → C x) ∧
    ∀ i, (∃ x, P x ∧ (∀ j, j ≠ i → H j x) ∧ ¬ C x) → ∃ x, Q x ∧ (∀ j, j ≠ i → H j x) ∧ ¬ C x
```

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample(s) | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hPQ : ∀ x, P x → Q x` | Orients the transfer. | tight | `sufficientIn_antitone_ce_not_subclass`, `tightIn_monotone_ce_not_subclass` | P = all naturals, Q = x ≤ 1 (P ⊄ Q): x ≥ 1 ⊢ x = 1 holds over Q but not over P (first conjunct fails); in x ≥ 1, x ≤ 1 ⊢ x = 1, x ≤ 1 is tight over P but not over Q (second conjunct fails) |

Counterexample statements (verbatim; each states that the other hypotheses hold and the conclusion fails):

```lean
-- lean/Toy/Ledger/Classes.lean:100-104
theorem sufficientIn_antitone_ce_not_subclass :
    ¬ ((SufficientIn bounded (single fun x : Nat => 1 ≤ x) pinC →
          SufficientIn trueC (single fun x : Nat => 1 ≤ x) pinC) ∧
        (∀ i, TightIn trueC (single fun x : Nat => 1 ≤ x) pinC i →
          TightIn bounded (single fun x : Nat => 1 ≤ x) pinC i)) :=
-- lean/Toy/Ledger/Classes.lean:110-112
theorem tightIn_monotone_ce_not_subclass :
    ¬ ((SufficientIn bounded pinH pinC → SufficientIn trueC pinH pinC) ∧
        (∀ i, TightIn trueC pinH pinC i → TightIn bounded pinH pinC i)) :=
```

**Non-vacuity witness:** x ≤ 1 is a subclass of all naturals; x ≥ 1, x ≤ 1 ⊢ x = 1 holds over all naturals and x ≥ 1 is tight over the subclass (witness 0). (`sufficientIn_antitone_nonvacuity`)

```lean
-- lean/Toy/Ledger/Classes.lean:118-119
theorem sufficientIn_antitone_nonvacuity :
    (∀ x, bounded x → trueC x) ∧ SufficientIn trueC pinH pinC ∧ TightIn bounded pinH pinC .h1 :=
```

**Prior art:**

- No specific prior source; an elementary consequence of the definitions, restated in this package's vocabulary.

**Design question.** When the reference class is shrunk or enlarged, which ledger labels survive? (Sufficiency survives shrinking; tightness and non-vacuity witnesses survive enlarging.)

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims**, result 18.

#### 19. `tightIn_all_models_harmlessIn_bounded`

- **Kind:** counterexample · **Tier:** T1 · **Depth:** shallow
- **Plain claim:** For x ≥ 1, x ≤ 1 ⊢ x = 1, which holds over all naturals and over the class x ≤ 1 and is non-vacuous over that class (witness 1): hypothesis x ≤ 1 is tight over all naturals (witness 2, outside the class), harmless over the class, and not tight over the class.

**Lean statement** (`tightIn_all_models_harmlessIn_bounded`, verbatim):

```lean
-- lean/Toy/Ledger/Classes.lean:139-143
theorem tightIn_all_models_harmlessIn_bounded :
    SufficientIn trueC pinH pinC ∧ SufficientIn bounded pinH pinC ∧
      NonVacuousIn bounded pinH ∧
      TightIn trueC pinH pinC .h2 ∧ HarmlessIn bounded pinH .h2 ∧
      ¬ TightIn bounded pinH pinC .h2 :=
```

Definitions used: `pinH`, `pinC`, `trueC`, `bounded` (quoted under **Running examples** and **Definitions**).

**Hypothesis ledger.**

No hypotheses: the statement is about concrete instances.

**Non-vacuity witness:** The statement includes NonVacuousIn bounded pinH (witness 1, which lies in the class). (`tightIn_all_models_harmlessIn_bounded`)

**Prior art:**

- No specific prior source; an elementary consequence of the definitions, restated in this package's vocabulary.

**Design question.** For a theorem that holds over a class and over a subclass on which it is non-vacuous, can one hypothesis be 'tight' over the class and 'harmless' over the subclass? (Yes.)

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims**, result 19.

#### 20. `not_harmlessIn_of_tightIn_of_sufficientIn`

- **Kind:** theorem · **Tier:** T0 · **Depth:** shallow
- **Plain claim:** If the hypotheses H suffice for C over the class P and hypothesis i is tight over P, then H i is not harmless over P.

**Lean statement** (`not_harmlessIn_of_tightIn_of_sufficientIn`, verbatim):

```lean
-- lean/Toy/Ledger/Classes.lean:54-56
theorem not_harmlessIn_of_tightIn_of_sufficientIn {P : M → Prop} {H : ι → M → Prop}
    {C : M → Prop} {i : ι} (hs : SufficientIn P H C) (ht : TightIn P H C i) :
    ¬ HarmlessIn P H i :=
```

Unfolded statement of `not_harmlessIn_of_tightIn_of_sufficientIn` (key definitions replaced by their bodies; this Lean term elaborates in the theorem's context and is definitionally equal to the rest of the statement):

```lean
(∀ x, P x → (∀ j, H j x) → C x) → (∃ x, P x ∧ (∀ j, j ≠ i → H j x) ∧ ¬ C x) →
  ¬ ∀ x, P x → H i x
```

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample(s) | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hs : SufficientIn P H C` | A harmless tight hypothesis would make the tightness witness a counterexample. | tight | `not_harmlessIn_ce_not_sufficientIn` | True ⊢ False over Unit with P = all models (the theorem is false) |
| `ht : TightIn P H C i` | Supplies a model of P on which H i must fail. | tight | `not_harmlessIn_ce_not_tightIn` | True ⊢ True over Unit with P = all models |

Counterexample statements (verbatim; each states that the other hypotheses hold and the conclusion fails):

```lean
-- lean/Toy/Ledger/Classes.lean:150-151
theorem not_harmlessIn_ce_not_sufficientIn :
    TightIn trueC topH falseC () ∧ HarmlessIn trueC topH () :=
-- lean/Toy/Ledger/Classes.lean:156-157
theorem not_harmlessIn_ce_not_tightIn :
    SufficientIn trueC topH trueC ∧ HarmlessIn trueC topH () :=
```

**Non-vacuity witness:** x ≥ 1, x ≤ 1 ⊢ x = 1 over all naturals, i = h2 (tight, witness 2). (`not_harmlessIn_nonvacuity`)

```lean
-- lean/Toy/Ledger/Classes.lean:161-162
theorem not_harmlessIn_nonvacuity :
    SufficientIn trueC pinH pinC ∧ TightIn trueC pinH pinC .h2 :=
```

**Positive control** (a nearby setting where the conclusion fails): `not_harmlessIn_ce_not_sufficientIn`, quoted in the ledger above.

**Prior art:**

- No specific prior source; an elementary consequence of the definitions, restated in this package's vocabulary.

**Design question.** Relative to one reference class over which the theorem holds, can a hypothesis be both 'tight' and 'harmless'? (No.)

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims**, result 20.

#### 21. `sufficient_conjunction_iff_each_and_tightAt_conjunction_iff_some`

- **Kind:** characterization · **Tier:** T0 · **Depth:** shallow
- **Plain claim:** For a fixed hypothesis family H: (1) for any conclusions C₁, C₂ and index i, hypothesis i is tight for C₁ ∧ C₂ exactly when it is tight for C₁ or for C₂; (2) for any family of conclusions D : κ → M → Prop, H suffices for all of them exactly when it suffices for each; (3) for any such family and index i, hypothesis i is tight for the conjunction of all D k exactly when it is tight for some D k.

**Lean statement** (`sufficient_conjunction_iff_each_and_tightAt_conjunction_iff_some`, verbatim):

```lean
-- lean/Toy/Ledger/Classes.lean:68-75
theorem sufficient_conjunction_iff_each_and_tightAt_conjunction_iff_some
    (H : ι → M → Prop) :
    (∀ (C₁ C₂ : M → Prop) (i : ι),
      TightAt H (fun x => C₁ x ∧ C₂ x) i ↔ TightAt H C₁ i ∨ TightAt H C₂ i) ∧
    (∀ {κ : Type w} (D : κ → M → Prop),
      Sufficient H (fun x => ∀ k, D k x) ↔ ∀ k, Sufficient H (D k)) ∧
    (∀ {κ : Type w} (D : κ → M → Prop) (i : ι),
      TightAt H (fun x => ∀ k, D k x) i ↔ ∃ k, TightAt H (D k) i) := by
```

Unfolded statement of `sufficient_conjunction_iff_each_and_tightAt_conjunction_iff_some` (key definitions replaced by their bodies; this Lean term elaborates in the theorem's context and is definitionally equal to the rest of the statement):

```lean
(∀ (C₁ C₂ : M → Prop) (i : ι),
    (∃ x, (∀ j, j ≠ i → H j x) ∧ ¬ (C₁ x ∧ C₂ x)) ↔
      (∃ x, (∀ j, j ≠ i → H j x) ∧ ¬ C₁ x) ∨ ∃ x, (∀ j, j ≠ i → H j x) ∧ ¬ C₂ x) ∧
  (∀ {κ : Type w} (D : κ → M → Prop),
    (∀ x, (∀ j, H j x) → ∀ k, D k x) ↔ ∀ k, ∀ x, (∀ j, H j x) → D k x) ∧
  (∀ {κ : Type w} (D : κ → M → Prop) (i : ι),
    (∃ x, (∀ j, j ≠ i → H j x) ∧ ¬ ∀ k, D k x) ↔ ∃ k, ∃ x, (∀ j, j ≠ i → H j x) ∧ ¬ D k x)
```

**Hypothesis ledger.**

No hypotheses: the statement holds for all values of its parameters.

**Non-vacuity witness:** x ≤ 1, y ≤ 1 over Nat × Nat: x ≤ 1 is tight for x ≤ 1 ∧ y ≤ 1 and for x ≤ 1; with D := the hypotheses themselves, sufficiency and tightness hold on both sides of (2) and (3). (`sufficient_conjunction_nonvacuity`)

```lean
-- lean/Toy/Ledger/Classes.lean:194-197
theorem sufficient_conjunction_nonvacuity :
    TightAt sumH (fun p => p.1 ≤ 1 ∧ p.2 ≤ 1) .h1 ∧ TightAt sumH (fun p => p.1 ≤ 1) .h1 ∧
      Sufficient sumH (fun p => ∀ k : Two, sumH k p) ∧ (∀ k, Sufficient sumH (sumH k)) ∧
      TightAt sumH (fun p => ∀ k : Two, sumH k p) .h1 ∧ TightAt sumH (sumH .h1) .h1 :=
```

**Prior art:**

- No specific prior source; an elementary consequence of the definitions, restated in this package's vocabulary.

**Design question.** If a theorem's conclusion is a conjunction, how does its ledger relate to the ledgers of the conjuncts?

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims**, result 21.

#### 22. `tight_for_conjunction_not_for_conjunct`

- **Kind:** counterexample · **Tier:** T1 · **Depth:** shallow
- **Plain claim:** In x ≤ 1, y ≤ 1 ⊢ x ≤ 1 ∧ y ≤ 1 over Nat × Nat: the hypotheses are jointly satisfiable (witness (0, 0)) and suffice for the conjunction, hypothesis x ≤ 1 is tight for the conjunction, the hypotheses suffice for the conjunct y ≤ 1, and x ≤ 1 is not tight for y ≤ 1.

**Lean statement** (`tight_for_conjunction_not_for_conjunct`, verbatim):

```lean
-- lean/Toy/Ledger/Classes.lean:180-183
theorem tight_for_conjunction_not_for_conjunct :
    NonVacuous sumH ∧ Sufficient sumH (fun p => p.1 ≤ 1 ∧ p.2 ≤ 1) ∧
      TightAt sumH (fun p => p.1 ≤ 1 ∧ p.2 ≤ 1) .h1 ∧
      Sufficient sumH (fun p => p.2 ≤ 1) ∧ ¬ TightAt sumH (fun p => p.2 ≤ 1) .h1 := by
```

Definitions used: `sumH` (quoted under **Running examples** and **Definitions**).

**Hypothesis ledger.**

No hypotheses: the statement is about concrete instances.

**Non-vacuity witness:** The statement includes NonVacuous sumH (witness (0, 0)). (`tight_for_conjunction_not_for_conjunct`)

**Prior art:**

- No specific prior source; an elementary consequence of the definitions, restated in this package's vocabulary.

**Design question.** Can a ledger computed for a conjunction be read as the ledger of each conjunct? (No: a hypothesis tight for C₁ ∧ C₂ need not be tight for C₂.)

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims**, result 22.

#### 23. `check_of_cell_empty`

- **Kind:** theorem · **Tier:** T0 · **Depth:** definitional
- **Plain claim:** For any table, property Q and cell (r, k): if the cell has no model, the ✓ at (r, k) holds.

**Lean statement** (`check_of_cell_empty`, verbatim):

```lean
-- lean/Toy/Ledger/Tables.lean:36-37
theorem check_of_cell_empty {cell : R → K → M → Prop} {Q : M → Prop} {r : R} {k : K}
    (h : ∀ x, ¬ cell r k x) : Check cell Q r k :=
```

Unfolded statement of `check_of_cell_empty` (key definitions replaced by their bodies; this Lean term elaborates in the theorem's context and is definitionally equal to the rest of the statement):

```lean
(∀ x, ¬ cell r k x) → ∀ x, cell r k x → Q x
```

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample(s) | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `h : ∀ x, ¬ cell r k x` | Emptiness of the cell. | tight | `check_of_cell_empty_ce_nonempty` | the nonempty cell {3} of a 2×2 table over Nat with the property 'even' |

Counterexample statements (verbatim; each states that the other hypotheses hold and the conclusion fails):

```lean
-- lean/Toy/Ledger/Tables.lean:69
theorem check_of_cell_empty_ce_nonempty : ¬ Check demoTable evenQ .h1 .h2 :=
```

**Non-vacuity witness:** Cell (h2, h1) of demoTable is empty. (`check_of_cell_empty_nonvacuity`)

```lean
-- lean/Toy/Ledger/Tables.lean:73
theorem check_of_cell_empty_nonvacuity : ∀ x, ¬ demoTable .h2 .h1 x :=
```

**Prior art:**

- Ilan Beer, Shoham Ben-David, Cindy Eisner, Yoav Rodeh, "Efficient Detection of Vacuity in Temporal Model Checking", Formal Methods in System Design 18(2):141-163, 2001, DOI 10.1023/A:1008779610539. Abstract: an implication can be 'trivially valid because the pre-condition of the implication is not satisfiable' (antecedent failure), called vacuity; an 'interesting witness' is a non-trivial example of validity. Conference version: "Efficient detection of vacuity in ACTL formulas", CAV 1997, LNCS vol. 1254, pp. 279-290, DOI 10.1007/3-540-63166-6_28.
- Derek L. Beatty, Randal E. Bryant, "Formally verifying a microprocessor using a simulation methodology", Proceedings of the 31st Design Automation Conference (DAC 1994), pp. 596-602, DOI 10.1145/196244.196575: 'One of the principal dangers of formal verification is what we have called antecedent failure'; footnote 10: 'Techniques that are based entirely on pure logic, such as HOL, are especially prone to it.' Their remedy is 'to check that the antecedent is, in fact, always true'. On a nonempty set of models or states this is a stronger requirement than NonVacuous (one model of the antecedent): it implies NonVacuous there (nonVacuous_of_forall_of_nonempty), and not conversely (nonVacuous_pin_antecedent_not_everywhere). Without nonemptiness it does not imply NonVacuous: over the empty model type the antecedent True holds at every model, vacuously, and is not satisfiable (antecedent_everywhere_not_nonVacuous_empty).

**Design question.** Does a ✓ in a soundness table show that its cell is inhabited? (No: every empty cell carries a ✓. Reference point.)

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims**, result 23.

#### 24. `all_checks_with_every_cell_empty`

- **Kind:** counterexample · **Tier:** T0 · **Depth:** definitional
- **Plain claim:** In the table over Nat with every cell empty, every cell carries a ✓ even for the unsatisfiable property False, and no ✓ is informative.

**Lean statement** (`all_checks_with_every_cell_empty`, verbatim):

```lean
-- lean/Toy/Ledger/Tables.lean:81-83
theorem all_checks_with_every_cell_empty :
    (∀ r k, Check emptyTable falseC r k) ∧ (∀ r k, ¬ InformativeCheck emptyTable falseC r k) ∧
      ¬ ∃ x : Nat, falseC x :=
```

Definitions used: `emptyTable`, `falseC`, `Check`, `InformativeCheck` (quoted under **Running examples** and **Definitions**).

**Hypothesis ledger.**

No hypotheses: the statement is about concrete instances.

**Non-vacuity witness:** The table and property are concrete. (`all_checks_with_every_cell_empty`)

**Prior art:**

- Ilan Beer, Shoham Ben-David, Cindy Eisner, Yoav Rodeh, "Efficient Detection of Vacuity in Temporal Model Checking", Formal Methods in System Design 18(2):141-163, 2001, DOI 10.1023/A:1008779610539. Abstract: an implication can be 'trivially valid because the pre-condition of the implication is not satisfiable' (antecedent failure), called vacuity; an 'interesting witness' is a non-trivial example of validity. Conference version: "Efficient detection of vacuity in ACTL formulas", CAV 1997, LNCS vol. 1254, pp. 279-290, DOI 10.1007/3-540-63166-6_28.

**Design question.** What extra information distinguishes informative ✓ entries from ✓ entries on empty cells? (A model in the cell, or an explicit 'empty' mark; over a finite list of models, classify computes one or the other.)

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims**, result 24.

#### 25. `classify_sound`

- **Kind:** theorem · **Tier:** T1 · **Depth:** shallow
- **Plain claim:** For any finite list univ : List M, Bool-valued table cell : R → K → M → Bool, Bool-valued property q : M → Bool and cell (r, k), the verdict classify univ cell q r k satisfies, read through liftTable and liftPred: if its status is witnessedOnUniv, its witness? is some w with w in the cell and q w, and q holds on every member of univ in the cell; if its status is emptyOnUniv, its witness? is none and no member of univ is in the cell; if its status is foundCounterexample, its witness? is some x with x in the cell and not q x.

**Lean statement** (`classify_sound`, verbatim):

```lean
-- lean/Toy/Ledger/Tables.lean:186-195
theorem classify_sound (univ : List M) (cell : R → K → M → Bool) (q : M → Bool)
    (r : R) (k : K) :
    ((classify univ cell q r k).status = .witnessedOnUniv →
      ∃ w, (classify univ cell q r k).witness? = some w ∧ liftTable cell r k w ∧
        liftPred q w ∧ ∀ x, x ∈ univ → liftTable cell r k x → liftPred q x) ∧
    ((classify univ cell q r k).status = .emptyOnUniv →
      (classify univ cell q r k).witness? = none ∧ ∀ x, x ∈ univ → ¬ liftTable cell r k x) ∧
    ((classify univ cell q r k).status = .foundCounterexample →
      ∃ x, (classify univ cell q r k).witness? = some x ∧ liftTable cell r k x ∧
        ¬ liftPred q x) := by
```

Unfolded statement of `classify_sound` (`liftTable` and `liftPred` replaced by their definitions; this Lean term elaborates in the theorem's context and is definitionally equal to the rest of the statement):

```lean
((classify univ cell q r k).status = .witnessedOnUniv →
  ∃ w, (classify univ cell q r k).witness? = some w ∧ cell r k w = true ∧
    q w = true ∧ ∀ x, x ∈ univ → cell r k x = true → q x = true) ∧
((classify univ cell q r k).status = .emptyOnUniv →
  (classify univ cell q r k).witness? = none ∧ ∀ x, x ∈ univ → ¬ cell r k x = true) ∧
((classify univ cell q r k).status = .foundCounterexample →
  ∃ x, (classify univ cell q r k).witness? = some x ∧ cell r k x = true ∧
    ¬ q x = true)
```

**Hypothesis ledger.**

No hypotheses: the statement holds for all values of its parameters.

**Non-vacuity witness:** classify_demo exhibits all three statuses on a 2×2 table over Fin 4. (`classify_demo`)

```lean
-- lean/Toy/Ledger/Tables.lean:260-268
theorem classify_demo :
    ((classify (List.finRange 4) demoTableB evenB .h1 .h1).status,
      (classify (List.finRange 4) demoTableB evenB .h1 .h1).witness?) =
        (.witnessedOnUniv, some 2) ∧
    ((classify (List.finRange 4) demoTableB evenB .h1 .h2).status,
      (classify (List.finRange 4) demoTableB evenB .h1 .h2).witness?) =
        (.foundCounterexample, some 3) ∧
    (classify (List.finRange 4) demoTableB evenB .h2 .h1).status = .emptyOnUniv ∧
    (classify (List.finRange 4) demoTableB evenB .h2 .h2).status = .emptyOnUniv := by
```

**Prior art:**

- Harsh Raju Chamarthi, Panagiotis Manolios, "Automated Specification Analysis Using an Interactive Theorem Prover", Formal Methods in Computer-Aided Design (FMCAD 2011), pp. 46-53 (author's version: https://www.ccs.neu.edu/home/harshrc/pub/fmcad11.pdf), Section II: assignments of a formula with hypotheses hyp1, ..., hypn are classified as 'vacuous' (not satisfying all hypotheses), 'counterexamples' (satisfying the hypotheses but not the conclusion), or 'witnesses' (satisfying the hypotheses and the conclusion).
- Ilan Beer, Shoham Ben-David, Cindy Eisner, Yoav Rodeh, "Efficient Detection of Vacuity in Temporal Model Checking", Formal Methods in System Design 18(2):141-163, 2001, DOI 10.1023/A:1008779610539. Abstract: an implication can be 'trivially valid because the pre-condition of the implication is not satisfiable' (antecedent failure), called vacuity; an 'interesting witness' is a non-trivial example of validity. Conference version: "Efficient detection of vacuity in ACTL formulas", CAV 1997, LNCS vol. 1254, pp. 279-290, DOI 10.1007/3-540-63166-6_28.

**Design question.** Which verdicts of a finite cell classifier can be trusted without knowing that its list of models is complete? (The returned witnesses and counterexamples.)

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims**, result 25.

#### 26. `classify_complete`

- **Kind:** theorem · **Tier:** T1 · **Depth:** shallow
- **Plain claim:** For any list univ : List M that lists every model, any Bool-valued table cell : R → K → M → Bool, Bool-valued property q : M → Bool and cell (r, k), the status of classify univ cell q r k is witnessedOnUniv exactly when the cell carries an informative ✓ (InformativeCheck (liftTable cell) (liftPred q) r k), emptyOnUniv exactly when it carries a ✓ and has no model, and foundCounterexample exactly when it carries no ✓.

**Lean statement** (`classify_complete`, verbatim):

```lean
-- lean/Toy/Ledger/Tables.lean:212-219
theorem classify_complete (univ : List M) (hu : ∀ x, x ∈ univ) (cell : R → K → M → Bool)
    (q : M → Bool) (r : R) (k : K) :
    ((classify univ cell q r k).status = .witnessedOnUniv ↔
        InformativeCheck (liftTable cell) (liftPred q) r k) ∧
    ((classify univ cell q r k).status = .emptyOnUniv ↔
        Check (liftTable cell) (liftPred q) r k ∧ ∀ x, ¬ liftTable cell r k x) ∧
    ((classify univ cell q r k).status = .foundCounterexample ↔
        ¬ Check (liftTable cell) (liftPred q) r k) := by
```

Unfolded statement of `classify_complete` (`InformativeCheck`, `Check`, `liftTable` and `liftPred` replaced by their definitions; this Lean term elaborates in the theorem's context and is definitionally equal to the rest of the statement):

```lean
((classify univ cell q r k).status = .witnessedOnUniv ↔
    (∀ x, cell r k x = true → q x = true) ∧ ∃ x, cell r k x = true) ∧
((classify univ cell q r k).status = .emptyOnUniv ↔
    (∀ x, cell r k x = true → q x = true) ∧ ∀ x, ¬ cell r k x = true) ∧
((classify univ cell q r k).status = .foundCounterexample ↔
    ¬ (∀ x, cell r k x = true → q x = true))
```

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample(s) | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hu : ∀ x, x ∈ univ` | Turns the verdicts over univ into verdicts over the whole model type. | tight | `classify_complete_ce_incomplete_univ` | the empty list over Fin 4 and the cell {3} with the property 'even' |

Counterexample statements (verbatim; each states that the other hypotheses hold and the conclusion fails):

```lean
-- lean/Toy/Ledger/Tables.lean:274-282
theorem classify_complete_ce_incomplete_univ :
    ¬ (((classify ([] : List (Fin 4)) demoTableB evenB .h1 .h2).status = .witnessedOnUniv ↔
          InformativeCheck (liftTable demoTableB) (liftPred evenB) .h1 .h2) ∧
        ((classify ([] : List (Fin 4)) demoTableB evenB .h1 .h2).status = .emptyOnUniv ↔
          Check (liftTable demoTableB) (liftPred evenB) .h1 .h2 ∧
            ∀ x, ¬ liftTable demoTableB .h1 .h2 x) ∧
        ((classify ([] : List (Fin 4)) demoTableB evenB .h1 .h2).status =
            .foundCounterexample ↔
          ¬ Check (liftTable demoTableB) (liftPred evenB) .h1 .h2)) := by
```

**Non-vacuity witness:** List.finRange 4 lists every element of Fin 4. (`classify_complete_nonvacuity`)

```lean
-- lean/Toy/Ledger/Tables.lean:288
theorem classify_complete_nonvacuity : ∀ x : Fin 4, x ∈ List.finRange 4 :=
```

**Prior art:**

- Harsh Raju Chamarthi, Panagiotis Manolios, "Automated Specification Analysis Using an Interactive Theorem Prover", Formal Methods in Computer-Aided Design (FMCAD 2011), pp. 46-53 (author's version: https://www.ccs.neu.edu/home/harshrc/pub/fmcad11.pdf), Section II: assignments of a formula with hypotheses hyp1, ..., hypn are classified as 'vacuous' (not satisfying all hypotheses), 'counterexamples' (satisfying the hypotheses but not the conclusion), or 'witnesses' (satisfying the hypotheses and the conclusion).
- Ilan Beer, Shoham Ben-David, Cindy Eisner, Yoav Rodeh, "Efficient Detection of Vacuity in Temporal Model Checking", Formal Methods in System Design 18(2):141-163, 2001, DOI 10.1023/A:1008779610539. Abstract: an implication can be 'trivially valid because the pre-condition of the implication is not satisfiable' (antecedent failure), called vacuity; an 'interesting witness' is a non-trivial example of validity. Conference version: "Efficient detection of vacuity in ACTL formulas", CAV 1997, LNCS vol. 1254, pp. 279-290, DOI 10.1007/3-540-63166-6_28.

**Design question.** When can a finite classifier's 'empty' and ✓ verdicts be read as statements about the whole model type? (When its list contains every model.)

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims**, result 26.

#### 27. `auditLedger_sound`

- **Kind:** theorem · **Tier:** T1 · **Depth:** shallow
- **Plain claim:** For any finite list univ : List M, Bool-valued hypotheses H : Fin m → M → Bool and conclusion C : M → Bool, every entry of (auditLedger univ H C).summary means the following, read through liftH and liftPred: a sufficiency entry witness x is a counterexample to the theorem; a tightness entry witness x at index i is a tightness witness for i; a non-vacuity entry witness x satisfies all hypotheses; a weakening entry witness x at i satisfies the other hypotheses and C and violates H i. A noWitness entry asserts the corresponding universal property restricted to the members of univ: the theorem, non-tightness of i, unsatisfiability of the hypotheses, or unweakenability of i.

**Lean statement** (`auditLedger_sound`, verbatim):

```lean
-- lean/Toy/Ledger/Audit.lean:310-325
theorem auditLedger_sound (univ : List M) (H : Fin m → M → Bool) (C : M → Bool) :
    (∀ x, (auditLedger univ H C).summary.sufficiency = .witness x →
      (∀ i, liftH H i x) ∧ ¬ liftPred C x) ∧
    ((auditLedger univ H C).summary.sufficiency = .noWitness →
      ∀ x, x ∈ univ → (∀ i, liftH H i x) → liftPred C x) ∧
    (∀ (i : Fin m) x, (auditLedger univ H C).summary.tightness[i.val]? = some (.witness x) →
      (∀ j, j ≠ i → liftH H j x) ∧ ¬ liftPred C x) ∧
    (∀ i : Fin m, (auditLedger univ H C).summary.tightness[i.val]? = some .noWitness →
      ∀ x, x ∈ univ → (∀ j, j ≠ i → liftH H j x) → liftPred C x) ∧
    (∀ x, (auditLedger univ H C).summary.nonvacuity = .witness x → ∀ i, liftH H i x) ∧
    ((auditLedger univ H C).summary.nonvacuity = .noWitness →
      ∀ x, x ∈ univ → ¬ ∀ i, liftH H i x) ∧
    (∀ (i : Fin m) x, (auditLedger univ H C).summary.weakening[i.val]? = some (.witness x) →
      (∀ j, j ≠ i → liftH H j x) ∧ liftPred C x ∧ ¬ liftH H i x) ∧
    (∀ i : Fin m, (auditLedger univ H C).summary.weakening[i.val]? = some .noWitness →
      ∀ x, x ∈ univ → (∀ j, j ≠ i → liftH H j x) → liftPred C x → liftH H i x) := by
```

Unfolded statement of `auditLedger_sound` (`liftH` and `liftPred` replaced by their definitions; this Lean term elaborates in the theorem's context and is definitionally equal to the rest of the statement):

```lean
(∀ x, (auditLedger univ H C).summary.sufficiency = .witness x →
  (∀ i, H i x = true) ∧ ¬ C x = true) ∧
((auditLedger univ H C).summary.sufficiency = .noWitness →
  ∀ x, x ∈ univ → (∀ i, H i x = true) → C x = true) ∧
(∀ (i : Fin m) x, (auditLedger univ H C).summary.tightness[i.val]? = some (.witness x) →
  (∀ j, j ≠ i → H j x = true) ∧ ¬ C x = true) ∧
(∀ i : Fin m, (auditLedger univ H C).summary.tightness[i.val]? = some .noWitness →
  ∀ x, x ∈ univ → (∀ j, j ≠ i → H j x = true) → C x = true) ∧
(∀ x, (auditLedger univ H C).summary.nonvacuity = .witness x → ∀ i, H i x = true) ∧
((auditLedger univ H C).summary.nonvacuity = .noWitness →
  ∀ x, x ∈ univ → ¬ ∀ i, H i x = true) ∧
(∀ (i : Fin m) x, (auditLedger univ H C).summary.weakening[i.val]? = some (.witness x) →
  (∀ j, j ≠ i → H j x = true) ∧ C x = true ∧ ¬ H i x = true) ∧
(∀ i : Fin m, (auditLedger univ H C).summary.weakening[i.val]? = some .noWitness →
  ∀ x, x ∈ univ → (∀ j, j ≠ i → H j x = true) → C x = true → H i x = true)
```

**Hypothesis ledger.**

No hypotheses: the statement holds for all values of its parameters.

**Non-vacuity witness:** auditLedger_running_examples records five finite runs whose summaries contain both entry kinds (witness and noWitness) for tightness, non-vacuity and weakening, and noWitness sufficiency entries; a sufficiency entry witness x occurs in auditLedger_false_theorem_tight_entry_reuses_counterexample. (`auditLedger_running_examples`)

```lean
-- lean/Toy/Ledger/Audit.lean:446-462
theorem auditLedger_running_examples :
    (auditLedger (List.finRange 4) pinHB pinCB).summary =
      { sufficiency := .noWitness, tightness := [.witness 0, .witness 2],
        nonvacuity := .witness 1, weakening := [.noWitness, .noWitness] } ∧
    (auditLedger grid3 sumHB sumCB).summary =
      { sufficiency := .noWitness, tightness := [.witness (2, 1), .witness (1, 2)],
        nonvacuity := .witness (0, 0), weakening := [.witness (2, 0), .witness (0, 2)] } ∧
    (auditLedger (List.finRange 4) dupHB pinCB).summary =
      { sufficiency := .noWitness, tightness := [.noWitness, .noWitness],
        nonvacuity := .witness 1, weakening := [.noWitness, .noWitness] } ∧
    (auditLedger (List.finRange 3) vacHB (fun _ => false)).summary =
      { sufficiency := .noWitness, tightness := [.witness 2, .witness 1],
        nonvacuity := .noWitness, weakening := [.noWitness, .noWitness] } ∧
    (auditLedger bools2 schemaHB (fun p => p.2)).summary =
      { sufficiency := .noWitness, tightness := [.witness (false, false), .witness (true, false)],
        nonvacuity := .witness (false, true),
        weakening := [.noWitness, .witness (true, true)] } :=
```

**Prior art:**

- Harsh Raju Chamarthi, Panagiotis Manolios, "Automated Specification Analysis Using an Interactive Theorem Prover", Formal Methods in Computer-Aided Design (FMCAD 2011), pp. 46-53 (author's version: https://www.ccs.neu.edu/home/harshrc/pub/fmcad11.pdf), Section II: assignments of a formula with hypotheses hyp1, ..., hypn are classified as 'vacuous' (not satisfying all hypotheses), 'counterexamples' (satisfying the hypotheses but not the conclusion), or 'witnesses' (satisfying the hypotheses and the conclusion).
- Ilan Beer, Shoham Ben-David, Cindy Eisner, Yoav Rodeh, "Efficient Detection of Vacuity in Temporal Model Checking", Formal Methods in System Design 18(2):141-163, 2001, DOI 10.1023/A:1008779610539. Abstract: an implication can be 'trivially valid because the pre-condition of the implication is not satisfiable' (antecedent failure), called vacuity; an 'interesting witness' is a non-trivial example of validity. Conference version: "Efficient detection of vacuity in ACTL formulas", CAV 1997, LNCS vol. 1254, pp. 279-290, DOI 10.1007/3-540-63166-6_28.
- Orna Kupferman, Moshe Y. Vardi, "Vacuity detection in temporal model checking", International Journal on Software Tools for Technology Transfer 4(2):224-233, 2003, DOI 10.1007/s100090100062. Abstract: vacuity checks 'whether all the subformulas of the specification affect its truth value in the system'; interesting witnesses. Earlier version: CHARME 1999, LNCS vol. 1703, pp. 82-98, DOI 10.1007/3-540-48153-2_8.

**Design question.** Which parts of an executable ledger audit can be trusted without knowing that its list of models is complete? (Every model it shows.)

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims**, result 27.

#### 28. `auditLedger_complete`

- **Kind:** theorem · **Tier:** T1 · **Depth:** shallow
- **Plain claim:** For any list univ : List M that lists every model, any Bool-valued hypotheses H : Fin m → M → Bool and conclusion C : M → Bool, the summary of auditLedger univ H C satisfies: the sufficiency entry is noWitness exactly when Sufficient (liftH H) (liftPred C); the tightness entry at i is noWitness exactly when ¬ TightAt (liftH H) (liftPred C) i; the non-vacuity entry is noWitness exactly when ¬ NonVacuous (liftH H); the weakening entry at i is noWitness exactly when UnweakenableAt (liftH H) (liftPred C) i.

**Lean statement** (`auditLedger_complete`, verbatim):

```lean
-- lean/Toy/Ledger/Audit.lean:338-346
theorem auditLedger_complete (univ : List M) (hu : ∀ x, x ∈ univ) (H : Fin m → M → Bool)
    (C : M → Bool) :
    ((auditLedger univ H C).summary.sufficiency = .noWitness ↔
      Sufficient (liftH H) (liftPred C)) ∧
    (∀ i : Fin m, (auditLedger univ H C).summary.tightness[i.val]? = some .noWitness ↔
      ¬ TightAt (liftH H) (liftPred C) i) ∧
    ((auditLedger univ H C).summary.nonvacuity = .noWitness ↔ ¬ NonVacuous (liftH H)) ∧
    (∀ i : Fin m, (auditLedger univ H C).summary.weakening[i.val]? = some .noWitness ↔
      UnweakenableAt (liftH H) (liftPred C) i) := by
```

Unfolded statement of `auditLedger_complete` (`Sufficient`, `TightAt`, `NonVacuous`, `UnweakenableAt`, `liftH` and `liftPred` replaced by their definitions; this Lean term elaborates in the theorem's context and is definitionally equal to the rest of the statement):

```lean
((auditLedger univ H C).summary.sufficiency = .noWitness ↔
  ∀ x, (∀ i, H i x = true) → C x = true) ∧
(∀ i : Fin m, (auditLedger univ H C).summary.tightness[i.val]? = some .noWitness ↔
  ¬ ∃ x, (∀ j, j ≠ i → H j x = true) ∧ ¬ C x = true) ∧
((auditLedger univ H C).summary.nonvacuity = .noWitness ↔ ¬ ∃ x, ∀ i, H i x = true) ∧
(∀ i : Fin m, (auditLedger univ H C).summary.weakening[i.val]? = some .noWitness ↔
  ∀ x, (∀ j, j ≠ i → H j x = true) → C x = true → H i x = true)
```

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample(s) | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hu : ∀ x, x ∈ univ` | Turns the verdicts over univ into verdicts over the whole model type. | tight | `auditLedger_complete_ce_incomplete_univ` | the empty list over Fin 4 with x ≥ 1, x ≤ 1 ⊢ False |

Counterexample statements (verbatim; each states that the other hypotheses hold and the conclusion fails):

```lean
-- lean/Toy/Ledger/Audit.lean:478-488
theorem auditLedger_complete_ce_incomplete_univ :
    ¬ (((auditLedger ([] : List (Fin 4)) pinHB (fun _ => false)).summary.sufficiency =
          .noWitness ↔ Sufficient (liftH pinHB) (liftPred (fun _ : Fin 4 => false))) ∧
        (∀ i : Fin 2,
          (auditLedger ([] : List (Fin 4)) pinHB (fun _ => false)).summary.tightness[i.val]? =
            some .noWitness ↔ ¬ TightAt (liftH pinHB) (liftPred (fun _ : Fin 4 => false)) i) ∧
        ((auditLedger ([] : List (Fin 4)) pinHB (fun _ => false)).summary.nonvacuity =
          .noWitness ↔ ¬ NonVacuous (liftH pinHB)) ∧
        (∀ i : Fin 2,
          (auditLedger ([] : List (Fin 4)) pinHB (fun _ => false)).summary.weakening[i.val]? =
            some .noWitness ↔ UnweakenableAt (liftH pinHB) (liftPred (fun _ : Fin 4 => false)) i)) := by
```

**Non-vacuity witness:** List.finRange 4 lists every element of Fin 4. (`auditLedger_complete_nonvacuity`)

```lean
-- lean/Toy/Ledger/Audit.lean:496
theorem auditLedger_complete_nonvacuity : ∀ x : Fin 4, x ∈ List.finRange 4 :=
```

**Prior art:**

- Harsh Raju Chamarthi, Panagiotis Manolios, "Automated Specification Analysis Using an Interactive Theorem Prover", Formal Methods in Computer-Aided Design (FMCAD 2011), pp. 46-53 (author's version: https://www.ccs.neu.edu/home/harshrc/pub/fmcad11.pdf), Section II: assignments of a formula with hypotheses hyp1, ..., hypn are classified as 'vacuous' (not satisfying all hypotheses), 'counterexamples' (satisfying the hypotheses but not the conclusion), or 'witnesses' (satisfying the hypotheses and the conclusion).
- Ilan Beer, Shoham Ben-David, Cindy Eisner, Yoav Rodeh, "Efficient Detection of Vacuity in Temporal Model Checking", Formal Methods in System Design 18(2):141-163, 2001, DOI 10.1023/A:1008779610539. Abstract: an implication can be 'trivially valid because the pre-condition of the implication is not satisfiable' (antecedent failure), called vacuity; an 'interesting witness' is a non-trivial example of validity. Conference version: "Efficient detection of vacuity in ACTL formulas", CAV 1997, LNCS vol. 1254, pp. 279-290, DOI 10.1007/3-540-63166-6_28.
- Orna Kupferman, Moshe Y. Vardi, "Vacuity detection in temporal model checking", International Journal on Software Tools for Technology Transfer 4(2):224-233, 2003, DOI 10.1007/s100090100062. Abstract: vacuity checks 'whether all the subformulas of the specification affect its truth value in the system'; interesting witnesses. Earlier version: CHARME 1999, LNCS vol. 1703, pp. 82-98, DOI 10.1007/3-540-48153-2_8.

**Design question.** When can the 'no witness' entries of an executable ledger audit be read as statements about the whole model type? (When its list contains every model.)

Basis: execution (Lean kernel check).

Non-claims: see **Boundaries → Non-claims**, result 28.

### Modeling bridge

The following claims connect the formal statements to practice. None is a theorem.

1. **Reading a published ledger in this vocabulary.** For a theorem with parameters `p` and `Prop`-valued hypotheses `h₁ … hₘ`, take `M` to be the type of parameter tuples, `H j` the `j`-th hypothesis as a predicate on `M`, and `C` the conclusion. A ledger entry `tight` for `hⱼ`, backed by a counterexample theorem whose instance lies in a witness class `W`, is then `TightIn W H C j`, hence `TightAt H C j` (result 18 with `Q` the class of all models, and `tightIn_true_iff`); a non-vacuity theorem is `NonVacuous H`. The cards of this package are read this way.
   Basis: derived (modeling bridge). Reasoning: unfolding the definitions of `TightIn`, `TightAt` and `NonVacuous` against the meaning of a counterexample theorem; this requires every hypothesis to be a predicate on the parameters, which fails for dependent binders until a predicate is chosen (non-claims of results 1 and 2).
2. **Unused-argument linters.** A proof term that never uses hypothesis `i` (in a declaration transitively free of `sorryAx`, with standard axioms, and with curried, non-dependent `Prop` binders) yields a proof with `H i` deleted, so `i` is not tight (result 2). The converse fails in general (not proved here), so a linter can indicate that a hypothesis is not tight and does not certify tightness.
   Basis: derived (modeling bridge). Reasoning: the stated proof term proves `Sufficient` of the restricted family by the soundness of the kernel for the intended reading; result 2 converts this into `¬ TightAt`. The linter sources are cited on result 2.
3. **Vacuity in model checking.** Antecedent failure (Beer et al.) is the failure of `NonVacuous`; Kupferman–Vardi vacuity of the implication from the conjoined hypotheses to `C` corresponds to `NonVacuous H ∧ Irredundant H C` (not proved here); on a nonempty set of models or states, Beatty–Bryant's check that the antecedent always holds is stronger than `NonVacuous` (`nonVacuous_of_forall_of_nonempty`, `nonVacuous_pin_antecedent_not_everywhere`); without nonemptiness it does not imply `NonVacuous` (`antecedent_everywhere_not_nonVacuous_empty`, over the empty model type).
   Basis: derived (modeling bridge). Reasoning: the cited abstracts and passages define these notions for temporal formulas and simulation runs; the correspondence reads a run or state as a model of `M` (results 14, 27, 28).
4. **Minimal unsatisfiable subsets and abductive explanations.** For a finite constraint set, `MinimalUnsatisfiable` is the MUS notion of Liffiton and Sakallah, and a sufficient, irredundant, non-vacuous subfamily of a vocabulary is a subset-minimal abductive explanation in the sense of Ignatiev et al. (Definition 1) with an empty background theory.
   Basis: derived (modeling bridge). Reasoning: comparison of the definitions as quoted on results 3, 4 and 12; result 4 is the kernel-checked form of the correspondence inside the model.
5. **Soundness tables.** A cell of a soundness table is a class of models, a ✓ is `Check`, and a ✓ with an exhibited model is `InformativeCheck`; an all-✓ table can have every cell empty (results 23, 24).
   Basis: derived (modeling bridge). Reasoning: reading a table entry "every model in this cell has property `Q`" as a universally quantified implication.

### Auxiliary lemmas cited by name

Package-local declarations that the cards, the modeling bridge and **Boundaries** cite by name and that are not quoted elsewhere in this report, verbatim, grouped by source file. Each is kernel-checked in the same build as the results; their statement and closure hashes are recorded in `audit/statements.json` and listed under **Evidence**.

`lean/Toy/Ledger/Witnesses.lean`:

```lean
-- lean/Toy/Ledger/Witnesses.lean:45-46
theorem irredundant_of_not_sufficient {H : ι → M → Prop} {C : M → Prop}
    (hns : ¬ Sufficient H C) : Irredundant H C := fun _ =>
-- lean/Toy/Ledger/Witnesses.lean:153-156
theorem irredundant_dup_true_false :
    ¬ Sufficient (pair (trueC (M := Unit)) trueC) falseC ∧
      Irredundant (pair (trueC (M := Unit)) trueC) falseC ∧
      NonVacuous (pair (trueC (M := Unit)) trueC) :=
-- lean/Toy/Ledger/Witnesses.lean:175-177
theorem dup_each_not_tight_but_both_needed :
    Sufficient dupH pinC ∧ (∀ i, ¬ TightAt dupH pinC i) ∧
      ¬ Sufficient (restrict (fun _ => False) dupH) pinC := by
-- lean/Toy/Ledger/Witnesses.lean:192-195
theorem geH_sufficient_no_irredundant_sufficient_subfamily :
    Sufficient geH falseC ∧ (∀ i, ¬ TightAt geH falseC i) ∧
      ∀ S : Nat → Prop,
        ¬ (Sufficient (restrict S geH) falseC ∧ Irredundant (restrict S geH) falseC) := by
-- lean/Toy/Ledger/Witnesses.lean:226-228
theorem isolatingAt_sufficient_not_tightAt_pinWeak :
    Sufficient pinH pinWeakC ∧ NonVacuous pinH ∧ IsolatingAt pinH .h1 ∧
      ¬ TightAt pinH pinWeakC .h1 := by
-- lean/Toy/Ledger/Witnesses.lean:254-255
theorem isolatingAt_every_index_not_irredundant_pinWeak :
    Sufficient pinH pinWeakC ∧ (∀ i, IsolatingAt pinH i) ∧ ¬ Irredundant pinH pinWeakC := by
```

`lean/Toy/Ledger/Strength.lean`:

```lean
-- lean/Toy/Ledger/Strength.lean:156-157
theorem tight_combinations_in_irredundant_families :
    Irredundant pinH pinC ∧ Irredundant sumH sumC ∧ Irredundant eqH eqC := by
-- lean/Toy/Ledger/Strength.lean:186-188
theorem not_tightAt_not_entailed_by_others_pinWeak :
    Sufficient pinH pinWeakC ∧ ¬ TightAt pinH pinWeakC .h1 ∧
      ¬ ∀ x, (∀ j, j ≠ Two.h1 → pinH j x) → pinH .h1 x := by
-- lean/Toy/Ledger/Strength.lean:208-211
theorem sumH_h1_weakenable_but_not_within_first_coordinate :
    ¬ UnweakenableAt sumH sumC .h1 ∧
      ∀ A : Nat → Prop, (∀ x, x ≤ 1 → A x) →
        Sufficient (replaceAt sumH .h1 (fun p => A p.1)) sumC → ∀ x, A x → x ≤ 1 := by
```

`lean/Toy/Ledger/Families.lean`:

```lean
-- lean/Toy/Ledger/Families.lean:52-53
theorem not_tightAt_of_ne_of_single_entails {H : ι → M → Prop} {C : M → Prop} {i j : ι}
    (hi : ∀ x, H i x → C x) (hj : j ≠ i) : ¬ TightAt H C j :=
-- lean/Toy/Ledger/Families.lean:115-122
theorem irredundant_sufficient_subfamilies_no_candidate_equals_conclusion :
    (∀ j, ¬ ∀ p, intVocab j p ↔ intC p) ∧
    Sufficient (restrict (fun j => j ≠ Three.h3) intVocab) intC ∧
    Irredundant (restrict (fun j => j ≠ Three.h3) intVocab) intC ∧
    NonVacuous (restrict (fun j => j ≠ Three.h3) intVocab) ∧
    Sufficient (restrict (fun j => j = Three.h3) intVocab) intC ∧
    Irredundant (restrict (fun j => j = Three.h3) intVocab) intC ∧
    NonVacuous (restrict (fun j => j = Three.h3) intVocab) := by
-- lean/Toy/Ledger/Families.lean:250-251
theorem tightAt_pinWeak_h2_conclusion_valid_on_bounded :
    TightAt pinH pinWeakC .h2 ∧ ∀ x, bounded x → pinWeakC x :=
-- lean/Toy/Ledger/Families.lean:285-293
theorem or_schema_irredundant_nonvacuous_necessary_unweakenable :
    (∀ (N : Type u) (P C : N → Prop), Sufficient (orSchemaH P C) C) ∧
    Irredundant (orSchemaH (fun p : Bool × Bool => p.1 = true) (fun p => p.2 = true))
      (fun p => p.2 = true) ∧
    NonVacuous (orSchemaH (fun p : Bool × Bool => p.1 = true) (fun p => p.2 = true)) ∧
    (∀ i, NecessaryAt (orSchemaH (fun p : Bool × Bool => p.1 = true) (fun p => p.2 = true))
      (fun p => p.2 = true) i) ∧
    (∀ i, UnweakenableAt (orSchemaH (fun p : Bool × Bool => p.1 = true) (fun p => p.2 = true))
      (fun p => p.2 = true) i) := by
-- lean/Toy/Ledger/Families.lean:316
theorem not_tightAt_of_ne_ce_not_entails : Two.h2 ≠ Two.h1 ∧ TightAt pinH pinC .h2 :=
-- lean/Toy/Ledger/Families.lean:322-323
theorem not_tightAt_of_ne_ce_same_index :
    (∀ x, single pinC () x → pinC x) ∧ TightAt (single pinC) pinC () :=
-- lean/Toy/Ledger/Families.lean:327
theorem not_tightAt_of_ne_nonvacuity : (∀ x, dupH .h1 x → pinC x) ∧ Two.h2 ≠ Two.h1 :=
-- lean/Toy/Ledger/Families.lean:357-359
theorem irredundant_hypothesis_restates_conclusion_within_other :
    Sufficient hatchH hatchC ∧ Irredundant hatchH hatchC ∧ NonVacuous hatchH ∧
      ∀ x, hatchH .h1 x → (hatchH .h2 x ↔ hatchC x) := by
```

`lean/Toy/Ledger/Classes.lean`:

```lean
-- lean/Toy/Ledger/Classes.lean:27-28
theorem tightIn_true_iff (H : ι → M → Prop) (C : M → Prop) (i : ι) :
    TightIn (fun _ => True) H C i ↔ TightAt H C i :=
-- lean/Toy/Ledger/Classes.lean:48-49
theorem nonVacuousIn_monotone {P Q : M → Prop} {H : ι → M → Prop}
    (hPQ : ∀ x, P x → Q x) : NonVacuousIn P H → NonVacuousIn Q H :=
-- lean/Toy/Ledger/Classes.lean:126-129
theorem nonVacuousIn_not_antitone :
    (∀ x, zeroClass x → bounded x) ∧ SufficientIn bounded pinH pinC ∧
      NonVacuousIn bounded pinH ∧ SufficientIn zeroClass pinH pinC ∧
      ¬ NonVacuousIn zeroClass pinH :=
-- lean/Toy/Ledger/Classes.lean:168-170
theorem tightIn_harmlessIn_not_exhaustive :
    SufficientIn trueC pinH pinWeakC ∧ ¬ TightIn trueC pinH pinWeakC .h1 ∧
      ¬ HarmlessIn trueC pinH .h1 :=
-- lean/Toy/Ledger/Classes.lean:207-214
theorem unweakenable_for_conjunction_not_for_conjuncts :
    Sufficient (single fun x : Nat => x = 1) (fun x => 1 ≤ x ∧ x ≤ 1) ∧
      NecessaryAt (single fun x : Nat => x = 1) (fun x => 1 ≤ x ∧ x ≤ 1) () ∧
      UnweakenableAt (single fun x : Nat => x = 1) (fun x => 1 ≤ x ∧ x ≤ 1) () ∧
      Sufficient (single fun x : Nat => x = 1) (fun x => 1 ≤ x) ∧
      ¬ UnweakenableAt (single fun x : Nat => x = 1) (fun x => 1 ≤ x) () ∧
      Sufficient (single fun x : Nat => x = 1) (fun x => x ≤ 1) ∧
      ¬ UnweakenableAt (single fun x : Nat => x = 1) (fun x => x ≤ 1) () := by
```

`lean/Toy/Ledger/Tables.lean`:

```lean
-- lean/Toy/Ledger/Tables.lean:292
def twoThreeTableB : Unit → Unit → Fin 4 → Bool := fun _ _ x => decide (x.val = 2 ∨ x.val = 3)
```

`lean/Toy/Ledger/SupportingLemmas.lean`:

```lean
-- lean/Toy/Ledger/SupportingLemmas.lean:44-45
theorem nonVacuous_of_forall_of_nonempty {M : Type u} {ι : Type v} [hne : Nonempty M]
    {H : ι → M → Prop} (h : ∀ x, ∀ i, H i x) : NonVacuous H :=
-- lean/Toy/Ledger/SupportingLemmas.lean:51-52
theorem nonVacuous_pin_antecedent_not_everywhere :
    NonVacuous pinH ∧ ¬ ∀ x, ∀ i, pinH i x := by
-- lean/Toy/Ledger/SupportingLemmas.lean:59-61
theorem antecedent_everywhere_not_nonVacuous_empty :
    (∀ x : Empty, ∀ i, single (fun (_ : Empty) => True) i x) ∧
      ¬ NonVacuous (single (fun (_ : Empty) => True)) :=
```

## Boundaries

### Non-claims (read these first)

**Result 1 (`tightAt_iff_witness_violates_exactly_i_of_sufficient`):**

- Does not say that H i is necessary for C (NecessaryAt) or cannot be weakened (UnweakenableAt); see tight_necessary_unweakenable_six_combinations.
- Speaks about the model type over which TightAt is evaluated; for a reference class see the relativized results (sufficientIn_antitone_and_tightIn_monotone).
- Does not say that the witness is unique or canonical, or that it violates C 'because of' H i in any causal sense.
- Without sufficiency the conclusion can fail: tightAt_iff_witness_violates_exactly_i_ce_not_sufficient proves that the conjunction of the two parts fails for True ⊢ False over Unit, where the only model is a tightness witness and satisfies H i.
- The model treats hypotheses as a non-dependent family H : ι → M → Prop. A Lean theorem whose later binders mention proofs of earlier ones, (h₁ : H₁ x) → (h₂ : H₂ x h₁) → C x, must first be turned into such a family, and the choice changes the ledger: with H₂' x := ∃ h₁ : H₁ x, H₂ x h₁ the other hypothesis entails H₁, so H₁ is not tight whenever the theorem holds (unweakenableAt_and_not_tightAt_iff_entailed_by_others_of_sufficient, right to left); with H₂' x := ∀ h₁ : H₁ x, H₂ x h₁, H₂' holds wherever H₁ fails, so H₁ is tight as soon as some model violates both H₁ and C (not proved here).
- Uses classical logic: the proof uses Classical.em (j = i) for an arbitrary index type ι (no decidable equality on ι is assumed).

**Result 2 (`tightAt_iff_not_sufficient_without`):**

- Does not say that the full family is sufficient; when it is not, every hypothesis is tight (irredundant_of_not_sufficient).
- Concerns deleting H i alone. Non-tight hypotheses cannot in general be deleted together: in x = 1, x = 1 ⊢ x = 1 neither hypothesis is tight, yet the empty family is not sufficient (dup_each_not_tight_but_both_needed). An infinite sufficient family need not contain any sufficient, irredundant subfamily (geH_sufficient_no_irredundant_sufficient_subfamily: the hypotheses i ≤ x for all i : Nat suffice for False).
- Says nothing about replacing H i by a weaker premise (see weakestPremise_is_weakest_replacement).
- Uses classical logic (the right side is a negated universal).
- Relation to syntactic linters (derived, modeling bridge; not proved here). Consider a Lean declaration whose proof is transitively free of sorryAx and depends on no axioms beyond propext, Classical.choice and Quot.sound, and whose hypotheses are curried, non-dependent Prop binders over the model variable (no later binder and not the conclusion mentions the proof of hypothesis i). If its elaborated proof term never uses hypothesis i, the same term proves the statement with hypothesis i deleted, that is, the family without H i is sufficient, so i is not tight by this result. The converse does not hold (not proved here): a proof may use a hypothesis that is not tight. An unused-argument report is therefore evidence about one proof of one statement: it can indicate that a hypothesis is not tight, and it does not certify tightness. The sorry checks of Lean's linter.unusedVariables and of Batteries' unusedArguments look for sorry syntactically in the declaration itself, so a declaration that calls a sorry-tainted lemma passes them without meeting the condition above.
- The model treats hypotheses as a non-dependent family H : ι → M → Prop. A Lean theorem whose later binders mention proofs of earlier ones, (h₁ : H₁ x) → (h₂ : H₂ x h₁) → C x, must first be turned into such a family, and the choice changes the ledger: with H₂' x := ∃ h₁ : H₁ x, H₂ x h₁ the other hypothesis entails H₁, so H₁ is not tight whenever the theorem holds (unweakenableAt_and_not_tightAt_iff_entailed_by_others_of_sufficient, right to left); with H₂' x := ∀ h₁ : H₁ x, H₂ x h₁, H₂' holds wherever H₁ fails, so H₁ is tight as soon as some model violates both H₁ and C (not proved here).

**Result 3 (`irredundant_iff_no_proper_subfamily_sufficient`):**

- Irredundance does not include sufficiency: every false theorem is irredundant, even with duplicated trivial hypotheses (irredundant_of_not_sufficient; irredundant_dup_true_false: True, True ⊢ False over Unit is irredundant and non-vacuous). Inclusion-minimality among sufficient families needs Sufficient H C in addition.
- Inclusion-minimal is not minimum-size and not unique: a different, smaller sufficient family over the same vocabulary may exist (irredundant_sufficient_subfamilies_of_sizes_two_and_one), also when no candidate hypothesis is equivalent to the conclusion (irredundant_sufficient_subfamilies_no_candidate_equals_conclusion).
- Non-tight hypotheses cannot in general be deleted together: in x = 1, x = 1 ⊢ x = 1 neither hypothesis is tight, yet the empty family is not sufficient (dup_each_not_tight_but_both_needed). An infinite sufficient family need not contain any sufficient, irredundant subfamily (geH_sufficient_no_irredundant_sufficient_subfamily: the hypotheses i ≤ x for all i : Nat suffice for False).
- Minimality is with respect to deleting hypotheses; it says nothing about replacing hypotheses by weaker ones (see the unweakenability results).
- Does not imply non-vacuity: a vacuous family can be sufficient and irredundant (irredundant_vacuous_and_nonvacuous_tightless).
- Does not imply that the family is independent in the all-truth-patterns sense (irredundance_independence_isolation_countermodels).

**Result 4 (`sufficient_irredundant_nonVacuous_iff_minimalUnsatisfiable`):**

- The non-vacuity conjunct cannot be dropped: x = 1, x = 2 ⊢ False on Fin 3 is sufficient and irredundant, but its family with the negated conclusion is not minimally unsatisfiable (irredundant_vacuous_and_nonvacuous_tightless).
- A minimal unsatisfiable subset extracted from a larger unsatisfiable pool H₀ ∪ {¬ C} need not contain ¬ C: for x = 1, x = 2 ⊢ False on Fin 3 the family stays unsatisfiable after deleting ¬ C (not_minimalUnsatisfiable_vac); such a subset certifies inconsistency of H₀, not a minimal premise set for C.
- Within a larger vocabulary the minimally unsatisfiable family need not be unique: irredundant_sufficient_subfamilies_of_sizes_two_and_one gives two sufficient, irredundant, non-vacuous subfamilies of x ≤ 1, y ≤ 1, x + y ≤ 2 for the conclusion x + y ≤ 2 ({x ≤ 1, y ≤ 1} and {x + y ≤ 2}), so by this result each of them together with ¬ C is minimally unsatisfiable. This result fixes the family; it does not choose it.
- Says nothing about the size or difficulty of the theorem.

**Result 5 (`irredundance_independence_isolation_countermodels`):**

- Shows that neither irredundancy nor full independence implies the other in general (the first two instances); it does not say that they are unrelated within every restricted class of instances.
- Isolation (Hilbert-style independence of one axiom from the others) does not mention the conclusion and so does not certify tightness for any particular theorem.
- Isolation at every index does not give irredundancy either: in x ≥ 1, x ≤ 1 ⊢ x ≤ 1 both hypotheses have isolating models and x ≥ 1 is not tight (isolatingAt_every_index_not_irredundant_pinWeak).

**Result 6 (`isolatingAt_of_tightAt_of_sufficient`):**

- The converse fails: an isolated hypothesis need not be tight (isolatingAt_sufficient_not_tightAt_pinWeak).
- Every tightness witness is an isolating model (tightAt_iff_witness_violates_exactly_i_of_sufficient, first part); this card states the existence of one.
- Does not give full independence (all truth patterns).

**Result 7 (`unweakenableAt_of_necessaryAt`):**

- By tight_necessary_unweakenable_six_combinations, every combination of tight, necessary and unweakenable that is consistent with this implication occurs at a hypothesis of a sufficient, non-vacuous instance; hence no other implication among the three properties holds in every sufficient, non-vacuous instance, and tightness neither implies nor is implied by necessity or by unweakenability.
- The converse fails: x = 0, y = 0 ⊢ x = y has x = 0 unweakenable but not necessary (tight_necessary_unweakenable_six_combinations).
- UnweakenableAt quantifies over arbitrary premises (predicates on M), which may mention the conclusion or variables that H i does not mention; under sufficiency it says that H i agrees with C wherever the other hypotheses hold (unweakenableAt_characterizations_of_sufficient, third part). So 'not unweakenable' does not mean that H i can be weakened within its own variables: in x ≤ 1, y ≤ 1 ⊢ x + y ≤ 2 the hypothesis x ≤ 1 can be replaced by x + y ≤ 2, but every premise on x alone that is implied by x ≤ 1 and keeps the theorem already implies x ≤ 1 (sumH_h1_weakenable_but_not_within_first_coordinate).

**Result 8 (`tight_necessary_unweakenable_six_combinations`):**

- 'Tight' does not mean 'necessary' or 'cannot be weakened' (third instance: tight, neither necessary nor unweakenable), and duplicated hypotheses are necessary yet not tight (second instance).
- The instances are two-hypothesis toys; the result shows non-implication, and says nothing about frequency in practice.
- The three non-tight combinations cannot occur in an irredundant family (by the definition of Irredundant); the three tight combinations do occur in irredundant families (tight_combinations_in_irredundant_families: x ≥ 1, x ≤ 1 ⊢ x = 1; x ≤ 1, y ≤ 1 ⊢ x + y ≤ 2; x = 0, y = 0 ⊢ x = y).
- UnweakenableAt quantifies over arbitrary premises (predicates on M), which may mention the conclusion or variables that H i does not mention; under sufficiency it says that H i agrees with C wherever the other hypotheses hold (unweakenableAt_characterizations_of_sufficient, third part). So 'not unweakenable' does not mean that H i can be weakened within its own variables: in x ≤ 1, y ≤ 1 ⊢ x + y ≤ 2 the hypothesis x ≤ 1 can be replaced by x + y ≤ 2, but every premise on x alone that is implied by x ≤ 1 and keeps the theorem already implies x ≤ 1 (sumH_h1_weakenable_but_not_within_first_coordinate).

**Result 9 (`unweakenableAt_and_not_tightAt_iff_entailed_by_others_of_sufficient`):**

- Non-tightness alone does not give entailment by the other hypotheses: in x ≥ 1, x ≤ 1 ⊢ x ≤ 1 the hypothesis x ≥ 1 is not tight and not entailed by x ≤ 1 (not_tightAt_not_entailed_by_others_pinWeak).
- Without sufficiency the equivalence fails (unweakenableAt_and_not_tightAt_iff_entailed_ce_not_sufficient).
- UnweakenableAt quantifies over arbitrary premises (predicates on M), which may mention the conclusion or variables that H i does not mention; under sufficiency it says that H i agrees with C wherever the other hypotheses hold (unweakenableAt_characterizations_of_sufficient, third part). So 'not unweakenable' does not mean that H i can be weakened within its own variables: in x ≤ 1, y ≤ 1 ⊢ x + y ≤ 2 the hypothesis x ≤ 1 can be replaced by x + y ≤ 2, but every premise on x alone that is implied by x ≤ 1 and keeps the theorem already implies x ≤ 1 (sumH_h1_weakenable_but_not_within_first_coordinate).

**Result 10 (`weakestPremise_is_weakest_replacement`):**

- Characterizes replacing one hypothesis while the others are kept; simultaneous replacement of several hypotheses is not characterized.
- The weakest premise may mention the conclusion and the variables of the other hypotheses; it is not the weakest premise within a restricted vocabulary (sumH_h1_weakenable_but_not_within_first_coordinate).
- Classical logic: in the proof (lean/Toy/Ledger/Strength.lean, lines 52-62) conjuncts 1 and 2 are proved without classical reasoning; the left-to-right direction of conjunct 3 (Sufficient H C → ∀ x, H i x → WeakestPremise H C i x) uses Classical.em (j = i) for an arbitrary index type ι, and conjunct 4, which equates validity of WeakestPremise H C i with ¬ TightAt H C i, uses Classical.byContradiction. The axiom record under Evidence is for the theorem as a whole. That conjunct 3 has no constructive proof for an arbitrary ι is not proved here.

**Result 11 (`unweakenableAt_characterizations_of_sufficient`):**

- The weakenings in the second characterization are claimed to agree with H i wherever the other hypotheses hold; nothing is claimed outside that region. That they can differ from H i there is not proved here (for instance, in x = 0, y = 0 ⊢ x = y over Nat × Nat the premise x = 0 ∨ y ≠ 0 is a weakening of x = 0 that keeps the theorem true and differs from x = 0 at (1, 1); not proved here).
- UnweakenableAt quantifies over arbitrary premises (predicates on M), which may mention the conclusion or variables that H i does not mention; under sufficiency it says that H i agrees with C wherever the other hypotheses hold (unweakenableAt_characterizations_of_sufficient, third part). So 'not unweakenable' does not mean that H i can be weakened within its own variables: in x ≤ 1, y ≤ 1 ⊢ x + y ≤ 2 the hypothesis x ≤ 1 can be replaced by x + y ≤ 2, but every premise on x alone that is implied by x ≤ 1 and keeps the theorem already implies x ≤ 1 (sumH_h1_weakenable_but_not_within_first_coordinate).
- Simultaneous weakening of several hypotheses is not characterized.
- Uses classical logic: the proof uses the third conjunct of weakestPremise_is_weakest_replacement, whose left-to-right direction uses Classical.em (j = i) for an arbitrary index type ι.

**Result 12 (`irredundant_sufficient_subfamilies_of_sizes_two_and_one`):**

- Here one candidate equals the conclusion; distinct-size sufficient, irredundant subfamilies also occur when no candidate is equivalent to the conclusion ({x = 0, y = 0} and {x = 0 ∧ y = 0} for x + y = 0 over Int × Int, irredundant_sufficient_subfamilies_no_candidate_equals_conclusion).
- Shows non-uniqueness and that size is not determined; says nothing about how to find a smallest subfamily.

**Result 13 (`subfamily_eq_of_sufficient_of_irredundant_superfamily`):**

- Without the sufficiency of S, an irredundant family can strictly contain another irredundant family: {x ≥ 1} ⊂ {x ≥ 1, x ≤ 1} for x = 1 over Nat (subfamily_eq_ce_not_sufficient).
- T is not assumed sufficient; its sufficiency follows from the conclusion S = T.
- Irredundance does not include sufficiency: every false theorem is irredundant, even with duplicated trivial hypotheses (irredundant_of_not_sufficient; irredundant_dup_true_false: True, True ⊢ False over Unit is irredundant and non-vacuous). The content of this result comes from hS.
- The antichain property does not give uniqueness or minimum size (irredundant_sufficient_subfamilies_of_sizes_two_and_one).

**Result 14 (`irredundant_vacuous_and_nonvacuous_tightless`):**

- Does not say that vacuity and tightness are unrelated within a restricted class of theorems.
- NonVacuous H is satisfiability of the antecedent; it does not mention C. Kupferman and Vardi's vacuity (every subformula affects the truth value), applied to the implication from the conjunction of the hypotheses to C, also asks that each hypothesis matter, which corresponds to NonVacuous H ∧ Irredundant H C (derived, modeling bridge; not proved here); under that reading the second instance, True ⊢ True, counts as vacuous.
- Beatty and Bryant's check against antecedent failure asks that the antecedent always hold on the states considered. When the set of states considered is nonempty this is stronger than NonVacuous (one model of the antecedent): it implies NonVacuous (nonVacuous_of_forall_of_nonempty), and not conversely (nonVacuous_pin_antecedent_not_everywhere). Without nonemptiness it does not imply NonVacuous: over the empty model type the antecedent True holds at every model, vacuously, and is not satisfiable (antecedent_everywhere_not_nonVacuous_empty).

**Result 15 (`not_valid_of_tightAt`):**

- Says nothing about the hypotheses beyond the existence of a model violating C; in particular it does not certify non-vacuity or depth.
- Invalidity over the model type does not prevent C from holding throughout an intended class: in x ≥ 1, x ≤ 1 ⊢ x ≤ 1 the hypothesis x ≤ 1 is tight over Nat, and the conclusion holds throughout the class x ≤ 1 (tightAt_pinWeak_h2_conclusion_valid_on_bounded).

**Result 16 (`schematic_ledger_irredundant_nonvacuous`):**

- 'Depth' and 'non-triviality' are not formalized; the formal proxy is sufficiency uniform in the predicates (a schema).
- Adding necessity and unweakenability of every hypothesis does not certify depth either: the schema P ∨ C, ¬ P ∨ C ⊢ C is sufficient for every instantiation, and its Bool × Bool instance is irredundant, non-vacuous, and every hypothesis is necessary and unweakenable (or_schema_irredundant_nonvacuous_necessary_unweakenable).
- Does not say that every irredundant, non-vacuous ledger belongs to a propositional schema.

**Result 17 (`not_single_entails_of_irredundant_of_exists_other`):**

- A hypothesis of an irredundant two-hypothesis family can still agree with the conclusion wherever another hypothesis holds: x ≠ 2, (x = 1 ∨ x = 2) ⊢ x = 1 over Fin 3 is sufficient, irredundant and non-vacuous, and on the region x ≠ 2 the second hypothesis is equivalent to the conclusion (irredundant_hypothesis_restates_conclusion_within_other).
- For a false theorem the statement is uninformative: every hypothesis is tight (irredundant_of_not_sufficient), and no hypothesis set entails C.
- The helper not_tightAt_of_ne_of_single_entails (if H i entails C then no j ≠ i is tight) is used in the proof and needs no assumption on the number of hypotheses.

**Result 18 (`sufficientIn_antitone_and_tightIn_monotone`):**

- The reverse transfers fail: a theorem over a subclass need not hold over the superclass (sufficientIn_antitone_ce_not_subclass), and a tightness witness for the superclass need not lie in the subclass (tightIn_monotone_ce_not_subclass; tightIn_all_models_harmlessIn_bounded).
- Non-vacuity transfers in the same direction as tightness, from P up to Q (nonVacuousIn_monotone), and not, in general, from Q down to P: a theorem that is non-vacuous over Q can be vacuous over a subclass (nonVacuousIn_not_antitone).
- Ledger labels are relative to a stated class; this result does not choose the class.

**Result 19 (`tightIn_all_models_harmlessIn_bounded`):**

- Within one class over which the theorem holds, 'tight' and 'harmless' exclude each other (not_harmlessIn_of_tightIn_of_sufficientIn); over a class where the theorem fails a hypothesis can be both (not_harmlessIn_ce_not_sufficientIn).
- 'Tight' and 'harmless' are not exhaustive: in x ≥ 1, x ≤ 1 ⊢ x ≤ 1 over all naturals the hypothesis x ≥ 1 is neither (tightIn_harmlessIn_not_exhaustive).
- HarmlessIn is pointwise truth on the class; it does not model signature changes such as extra binders or instance arguments.

**Result 20 (`not_harmlessIn_of_tightIn_of_sufficientIn`):**

- Uses classical excluded middle on j = i for an arbitrary index type.
- Exclusive but not exhaustive: a hypothesis can be neither tight nor harmless (tightIn_harmlessIn_not_exhaustive).
- Relative to one fixed class; across a class and a subclass both labels can apply (tightIn_all_models_harmlessIn_bounded).
- HarmlessIn is pointwise truth on the class; it does not model signature changes such as extra binders or instance arguments.

**Result 21 (`sufficient_conjunction_iff_each_and_tightAt_conjunction_iff_some`):**

- Uses classical logic (De Morgan for a negated conjunction and a negated universal).
- A ledger computed for a conjunction overstates per-conjunct tightness (tight_for_conjunction_not_for_conjunct).
- Unweakenability does not pass from a conjunction to its conjuncts: with the single hypothesis x = 1 over Nat, the hypothesis is necessary and unweakenable for 1 ≤ x ∧ x ≤ 1 but unweakenable for neither conjunct (unweakenable_for_conjunction_not_for_conjuncts).

**Result 22 (`tight_for_conjunction_not_for_conjunct`):**

- A summary 'under x ≤ 1, y ≤ 1' of the conjunct y ≤ 1 alone over-reads the ledger of the conjunction.

**Result 23 (`check_of_cell_empty`):**

- Says nothing about nonempty cells.

**Result 24 (`all_checks_with_every_cell_empty`):**

- Does not say that tables in practice have empty cells; it shows that an all-✓ table is compatible with every cell being empty.

**Result 25 (`classify_sound`):**

- A witnessedOnUniv verdict does not give a ✓ when univ omits models: over univ = [2] the cell {2, 3} on Fin 4 is classified witnessedOnUniv for 'even', although 3 is in the cell and odd (classify_witnessedOnUniv_without_check). Over the whole model type such a verdict certifies that the cell contains a model with the property; it does not certify the ✓.
- An emptyOnUniv verdict does not show that the cell is empty outside univ.
- The verdict type carries its evidence, so the corresponding guarantee holds for every verdict value, whether or not it was computed by classify (CellVerdict.sound); the proof does not inspect classify. Depth is labelled shallow for that reason.
- Concerns enumeration over a finite list; makes no efficiency claim.

**Result 26 (`classify_complete`):**

- Is stated for Bool-valued tables over a model type that some finite list enumerates; it neither establishes nor refutes the corresponding claims for model types that no finite list enumerates. Proved model–system relation: none proved.
- Says nothing about tables whose cells are given as arbitrary Prop-valued predicates.

**Result 27 (`auditLedger_sound`):**

- When the theorem fails, tightness entries may reuse the theorem's counterexample: for the single trivial hypothesis true and the conclusion b = true over [false, true], the sufficiency entry and the tightness entry are both witness false (auditLedger_false_theorem_tight_entry_reuses_counterexample), and that tightness witness satisfies H i. When the theorem holds, every tightness witness violates H i (tightAt_iff_witness_violates_exactly_i_of_sufficient, first part).
- noWitness tightness entries for several hypotheses do not license deleting them together: auditLedger_dup reports noWitness for both hypotheses of x = 1, x = 1 ⊢ x = 1, yet deleting both breaks the theorem (dup_each_not_tight_but_both_needed).
- A weakening witness x shows that H i is not unweakenable over the whole model type; when the theorem holds, the premise H i ∨ C, which holds at x where H i fails, is then a strictly weaker valid replacement (by parts 1 and 3 of weakestPremise_is_weakest_replacement). It does not show that H i can be weakened within its own variables (sumH_h1_weakenable_but_not_within_first_coordinate).
- The non-vacuity entry concerns satisfiability of the hypotheses; it is not the 'every subformula matters' notion of vacuity from temporal-logic model checking (see irredundant_vacuous_and_nonvacuous_tightless).
- noWitness entries are relative to univ; over an incomplete list they can be wrong for the whole model type (auditLedger_complete_ce_incomplete_univ).
- The verdict constructors carry their evidence, so the guarantee holds by construction (depth shallow).

**Result 28 (`auditLedger_complete`):**

- When the theorem fails, tightness entries may reuse the theorem's counterexample: for the single trivial hypothesis true and the conclusion b = true over [false, true], the sufficiency entry and the tightness entry are both witness false (auditLedger_false_theorem_tight_entry_reuses_counterexample), and that tightness witness satisfies H i. When the theorem holds, every tightness witness violates H i (tightAt_iff_witness_violates_exactly_i_of_sufficient, first part).
- noWitness tightness entries for several hypotheses do not license deleting them together: auditLedger_dup reports noWitness for both hypotheses of x = 1, x = 1 ⊢ x = 1, yet deleting both breaks the theorem (dup_each_not_tight_but_both_needed).
- A weakening witness x shows that H i is not unweakenable over the whole model type; when the theorem holds, the premise H i ∨ C, which holds at x where H i fails, is then a strictly weaker valid replacement (by parts 1 and 3 of weakestPremise_is_weakest_replacement). It does not show that H i can be weakened within its own variables (sumH_h1_weakenable_but_not_within_first_coordinate).
- The non-vacuity entry concerns satisfiability of the hypotheses; it is not the 'every subformula matters' notion of vacuity from temporal-logic model checking (see irredundant_vacuous_and_nonvacuous_tightless).
- Is stated for Bool-valued, non-dependent hypothesis families indexed by Fin m over a model type that some finite list enumerates; it neither establishes nor refutes the corresponding claims for Prop-valued families, for other index types, or for model types that no finite list enumerates. Proved model–system relation: none proved.
- The lists used in auditLedger_running_examples (List.finRange 4, grid3, List.finRange 3, bools2) list every model (List.mem_finRange, mem_grid3, mem_bools2), so this result applies to each run.

### Attractive stronger conclusions that are not established

- "Tight" means necessary, or cannot be weakened: refuted by `tight_necessary_unweakenable_six_combinations` (result 8).
- An all-`tight` ledger certifies sufficiency: refuted by `irredundant_of_not_sufficient` and `irredundant_dup_true_false` (every false theorem is irredundant).
- An all-`tight` ledger singles out a unique or minimum-size hypothesis set: refuted by `irredundant_sufficient_subfamilies_of_sizes_two_and_one` and `irredundant_sufficient_subfamilies_no_candidate_equals_conclusion`.
- An all-`tight` ledger certifies non-vacuity, or a non-vacuity witness certifies tightness: refuted by `irredundant_vacuous_and_nonvacuous_tightless` (result 14).
- Hypotheses that are not tight can be deleted together: refuted by `dup_each_not_tight_but_both_needed`.
- Every sufficient family contains a sufficient, irredundant subfamily: refuted for infinite families by `geH_sufficient_no_irredundant_sufficient_subfamily`.
- One isolating model per hypothesis (Hilbert-style independence) certifies tightness: refuted by `irredundance_independence_isolation_countermodels` and `isolatingAt_every_index_not_irredundant_pinWeak`.
- A sufficient, irredundant, non-vacuous ledger (even with every hypothesis necessary and unweakenable) certifies depth: refuted by `schematic_ledger_irredundant_nonvacuous` and `or_schema_irredundant_nonvacuous_necessary_unweakenable`.
- A ledger computed for a conjunction is a ledger for each conjunct: refuted by `tight_for_conjunction_not_for_conjunct` and, for unweakenability, `unweakenable_for_conjunction_not_for_conjuncts`.
- Ledger labels transfer between a class and a subclass in both directions: refuted by `sufficientIn_antitone_ce_not_subclass`, `tightIn_monotone_ce_not_subclass`, `nonVacuousIn_not_antitone` and `tightIn_all_models_harmlessIn_bounded`.
- `tight` and `harmless` are exhaustive: refuted by `tightIn_harmlessIn_not_exhaustive`.
- "Not unweakenable" means the hypothesis can be weakened within its own variables: refuted by `sumH_h1_weakenable_but_not_within_first_coordinate`.
- Non-tightness gives entailment by the other hypotheses: refuted by `not_tightAt_not_entailed_by_others_pinWeak`.
- Verdicts of `classify` or `auditLedger` over an incomplete list are correct for the whole model type: refuted by `classify_complete_ce_incomplete_univ`, `classify_witnessedOnUniv_without_check` and `auditLedger_complete_ce_incomplete_univ`.
- Unused-argument linters certify tightness: not established (modeling bridge 2; the converse direction is not proved here).

### Escape hatches

Results 15, 17 and 20 have negated conclusions; their positive controls (nearby settings where the conclusion fails) are named on their cards. For every result with hypotheses and every one of its hypotheses, the counterexample named in the ledger is an instance, in the stated witness class, where the other hypotheses hold and the conclusion fails; so no hypothesis can be dropped from any of these results:

- Result 1 (`tightAt_iff_witness_violates_exactly_i_of_sufficient`): `hs` → `tightAt_iff_witness_violates_exactly_i_ce_not_sufficient`.
- Result 6 (`isolatingAt_of_tightAt_of_sufficient`): `hs` → `isolatingAt_of_tightAt_ce_not_sufficient`; `ht` → `isolatingAt_of_tightAt_ce_not_tight`.
- Result 7 (`unweakenableAt_of_necessaryAt`): `h` → `unweakenableAt_of_necessaryAt_ce_not_necessary`.
- Result 9 (`unweakenableAt_and_not_tightAt_iff_entailed_by_others_of_sufficient`): `hs` → `unweakenableAt_and_not_tightAt_iff_entailed_ce_not_sufficient`.
- Result 11 (`unweakenableAt_characterizations_of_sufficient`): `hs` → `unweakenableAt_characterizations_ce_not_sufficient`, `unweakenableAt_iff_weakenings_ce_not_sufficient`.
- Result 13 (`subfamily_eq_of_sufficient_of_irredundant_superfamily`): `hS` → `subfamily_eq_ce_not_sufficient`; `hT` → `subfamily_eq_ce_not_irredundant`; `hST` → `subfamily_eq_ce_not_contained`.
- Result 15 (`not_valid_of_tightAt`): `h` → `not_valid_of_tightAt_ce_not_tight`.
- Result 17 (`not_single_entails_of_irredundant_of_exists_other`): `hirr` → `not_single_entails_ce_not_irredundant`; `hother` → `not_single_entails_ce_single_hypothesis`.
- Result 18 (`sufficientIn_antitone_and_tightIn_monotone`): `hPQ` → `sufficientIn_antitone_ce_not_subclass`, `tightIn_monotone_ce_not_subclass`.
- Result 20 (`not_harmlessIn_of_tightIn_of_sufficientIn`): `hs` → `not_harmlessIn_ce_not_sufficientIn`; `ht` → `not_harmlessIn_ce_not_tightIn`.
- Result 23 (`check_of_cell_empty`): `h` → `check_of_cell_empty_ce_nonempty`.
- Result 26 (`classify_complete`): `hu` → `classify_complete_ce_incomplete_univ`.
- Result 28 (`auditLedger_complete`): `hu` → `auditLedger_complete_ce_incomplete_univ`.

### Hypotheses with `unknown` tightness

None: every hypothesis of every result is `tight`, with a kernel-checked counterexample.

### Disproved or dropped draft statements

No draft statement was disproved, and none is left `unknown`. Two statements in the Lean sources were considered as separate results and are not published as such:

- `not_tightAt_of_ne_of_single_entails` (`lean/Toy/Ledger/Families.lean`, line 52: if `H i` alone entails `C`, no `j ≠ i` is tight) is the helper lemma of result 17; its counterexamples `not_tightAt_of_ne_ce_not_entails`, `not_tightAt_of_ne_ce_same_index` and non-vacuity witness `not_tightAt_of_ne_nonvacuity` remain in the sources.
- `auditLedger_running_examples` (`lean/Toy/Ledger/Audit.lean`, line 446) collects five `decide` runs of `auditLedger`; it is the non-vacuity witness of result 27.

## Evidence

### Kernel-check record

Observed on 2026-11-21 with `leanprover/lean4:v4.34.1` (GitHub `leanprover/lean4`, tag `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`, read from the GitHub API on 2026-11-21), core Lean with no other libraries. A fresh copy of `lean/` was built with `lake build` with Lake's artifact cache disabled (`LAKE_ARTIFACT_CACHE=false`, `LAKE_RESTORE_ARTIFACTS=false`), so every proof was re-elaborated and kernel-checked. An audit program then ran `Lean.collectAxioms` on every declaration of the library `Toy` (614 declarations, recorded in `audit/axioms.json`): no declaration depends on `sorryAx`, and the only axioms that occur are `propext`, `Classical.choice` and `Quot.sound`. No Lean source contains `sorry`, `admit`, `native_decide`, `implemented_by`, `@[extern]`, `unsafe`, or an `axiom` or `opaque` declaration.

**What is hashed** (recorded in `audit/statements.json`, recomputed by `support/revalidate.py`): the *statement hash* is the SHA-256 of the UTF-8 text of Lean's `repr` of the declaration's type; the *closure hash* is the SHA-256 of the newline-joined, sorted list of entries `name : repr(type)` (followed by ` := repr(value)` for constants that are not theorems) for every constant of the library `Toy` reachable from the type through types, definition values and inductive constructors (theorem bodies excluded); the number in parentheses is the number of entries.

Per theorem (role: `R` main result, `CE` tightness counterexample, `NV` non-vacuity witness, `PC` positive control; numbers are result numbers):

| Theorem | Role | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `tightAt_iff_witness_violates_exactly_i_of_sufficient` | R1 | Classical.choice, Quot.sound, propext | `baf70ed23468f47ddd2c6d413b45fde8e98548e9f98621808f69b4a0786b346c` | `d2843b2580d7640f6501a796cb9d8dd76fd915076f04648658089b9a183deec3` (2) |
| `tightAt_iff_witness_violates_exactly_i_ce_not_sufficient` | CE1 | none | `932c5cb503aa48879f398d8d4e241272097e726515447e7b1f98102c65e7e3f9` | `24ee00d90beda61455fa6abf6ec217aae2ce69684595a9b1963fc19b7c11c9af` (4) |
| `tightAt_iff_witness_violates_exactly_i_nonvacuity` | NV1 | Quot.sound, propext | `aa88200da2658c69bd4a73a8d9c96b15b01b595741c1c7d9c9943973d8ff89a9` | `11936fbe0ea80243160ab8686c22297ac020a6a5f8cd75c8a44f8664a6df8eed` (11) |
| `tightAt_iff_not_sufficient_without` | R2 | Classical.choice, Quot.sound, propext | `1eaf415c50d71b17ee85db792e64a0ad6e9cd2faa7c17f57bdd6fc50d3f120c9` | `49f6dc5aec77901c55fc6b293e0bc3a60b1dfba8fde618c35200afda03982c41` (3) |
| `tightAt_iff_not_sufficient_without_nonvacuity` | NV2 | propext | `7b6f357dd9cb577b0be77f86ad54397a70198915460c215d2787a86532ab17df` | `2766c98461a9388e6636eb2152ad2a90797bad195c0102d9ee35f58ec117c3d3` (12) |
| `irredundant_iff_no_proper_subfamily_sufficient` | R3 | Classical.choice, Quot.sound, propext | `632b03102dc54616ec841f0b3654ef8a5f586b98ef16a39fc14c5f805b970ea1` | `a2d32d178499715887d0943e546cd4bb28b26ae20fecf2117ec5a2f091d8fb5d` (4) |
| `irredundant_iff_no_proper_subfamily_sufficient_nonvacuity` | NV3 | Quot.sound, propext | `a6c9c034ca25d0d158aff427aabc620a2529f3cc746afbfceac29e6c9438669e` | `b41cfd9675ef0a0cba13a9591c22ced324c3af334a69473f1f37f6c54d9f8053` (13) |
| `sufficient_irredundant_nonVacuous_iff_minimalUnsatisfiable` | R4 | Classical.choice, Quot.sound, propext | `ec0ed581c08d82694a4a200b83902057eef5e9504a34137d4274cafdc818bc0f` | `5db1c515d191dba7e85e1d11f11264df6b7a0735ff0f3c8907d873040e808818` (8) |
| `sufficient_irredundant_nonVacuous_iff_minimalUnsatisfiable_nonvacuity` | NV4 | Quot.sound, propext | `c123050d7db22d2f1dff2ffbc7bbb3fe6752ed839b9c62d3df824963bb9b4ecf` | `595367627ffb7cc4f32b254678829413f1d49d138d73b5014b85c31f36958e62` (17) |
| `irredundance_independence_isolation_countermodels` | R5 NV5 | Quot.sound, propext | `6696a8ddafea56ff29ab70e2c5e01d382c11887f30c093fb182e73183243bded` | `c28ef2c2f0f649931d3aac8056ba576e11fdc5e5660a601177dbe5aac5f9d5e7` (18) |
| `isolatingAt_of_tightAt_of_sufficient` | R6 | Classical.choice, Quot.sound, propext | `d90dc997f6aec9b6452b68f8f6b2f6fb5471bb943d089ed18e2060a88be289f4` | `24a3f52ac558eb4dd190ab07d0b281d8c390498336fad6b6afe9d3de7092be9e` (3) |
| `isolatingAt_of_tightAt_ce_not_sufficient` | CE6 | none | `4a7f385c9ec25c5c59ea468a3e404a5ee20e646d489407d0c7e1c2c98d946436` | `32762a0dbab77ceb34e5c3c4b4fdab49241a2575917c603e8ca892f976361255` (5) |
| `isolatingAt_of_tightAt_ce_not_tight` | CE6 | propext | `3e038945242bf1d4d0fe269389492e0ae1982321e361c415d8a6053f67014afe` | `410e895e3061bea820651ce20aa6cc25e78a29a466b17b74e840b4ba12505941` (11) |
| `isolatingAt_of_tightAt_of_sufficient_nonvacuity` | NV6 | Quot.sound, propext | `872e2dc6e0963991eb4be3a34e63f7af2fb6af2eb66b7e9f0a42ae63a1968334` | `11936fbe0ea80243160ab8686c22297ac020a6a5f8cd75c8a44f8664a6df8eed` (11) |
| `unweakenableAt_of_necessaryAt` | R7 | none | `ad3cf276944de8eae8c0fc26b57cd25ddd35578a13a73461d5d47e0a8b66cdc4` | `a1705334643e09184b9175dd963c388f87699ea1cd0d0061d452a36636039f28` (2) |
| `unweakenableAt_of_necessaryAt_ce_not_necessary` | CE7 | Quot.sound, propext | `d38e6e72441b830fd67bb4240c8a3ac1f7d6d32903d0cdb2a211e11d13625f75` | `7a6f352976a19d440a805e295acb242d886806b64dd7f8fc1220ae45aa930285` (10) |
| `unweakenableAt_of_necessaryAt_nonvacuity` | NV7 | Quot.sound, propext | `80d3c7f0210609a0ef6eb0320bc9fa89786c5418dba269e3f36cbc7812b9ea43` | `290d69b33fed578a2183dc9027dadcd50de2bec27c921b0345d6e972c40ba496` (10) |
| `tight_necessary_unweakenable_six_combinations` | R8 NV8 | Quot.sound, propext | `db428cddc68e7ca04846336c9cab3a1199ada7e4fa10ae2ec079dfa4fd4bf850` | `aeb33c801f586fb2f8c87942f10669751b650697aa8e8755efac30b125189c3e` (21) |
| `unweakenableAt_and_not_tightAt_iff_entailed_by_others_of_sufficient` | R9 | Classical.choice, Quot.sound, propext | `534985ab72adc636354b4b4164ac0b05070a0e7f3b82482d765bc597dbcb1633` | `a148b9ace6424f23e3a305016cf0ae6ffc8dda30755c47ff1eab15ad01f3bfa0` (3) |
| `unweakenableAt_and_not_tightAt_iff_entailed_ce_not_sufficient` | CE9 | none | `491e0f8c1129316809d883f3d32c7762484951c63889c8a4895c3f37231aa28d` | `ec66c3eb40046f1da58dfb0f30d088877384cf8d73b122709f33f38ada376802` (5) |
| `unweakenableAt_and_not_tightAt_iff_entailed_nonvacuity` | NV9 | Quot.sound, propext | `fcc6b3ffb23a4df73c6d283c2facc748fbf58bc109cf3843e2a4e5ff9d6bf8b1` | `cde3f1d97efb0b72b6a6d0d69ad828288cf005e9c0ee3cde1c1efe2a5bab262e` (12) |
| `weakestPremise_is_weakest_replacement` | R10 | Classical.choice, Quot.sound, propext | `19322e5bf146b3843df27212b5cb651e1e94c5438b7f0eace44014702b607c5a` | `5577ae22d73788e11a6e99a4380a44ce665230e7631b60092daf55bd55222945` (4) |
| `weakestPremise_sum_nonvacuity` | NV10 | Quot.sound, propext | `ab537e1adc050f7d78ddb7d1ec394269efe48ce8215155bb87f7b85131940faa` | `99b379e89abd4382ecdcc170a2df2bbec800b41076971cb815307eb469a8d276` (13) |
| `unweakenableAt_characterizations_of_sufficient` | R11 | Classical.choice, Quot.sound, propext | `3bafdac356162a1c669e8e6f8d3f11e29c1927f03f38107d6a88943d38b7b22a` | `5d4129eb632835710bd4e43f131a7ced3410db7874d53d10c05bc610b53aa29b` (4) |
| `unweakenableAt_characterizations_ce_not_sufficient` | CE11 | none | `722e7489b84c2152d0fbbeb4d36ef96bda37db5689c16bf469a9660dbd4c1d8b` | `37b9adc42a585bd01fec15726cb5308519438f9298c454b352de2d39885b7435` (7) |
| `unweakenableAt_iff_weakenings_ce_not_sufficient` | CE11 | propext | `3e00be85b41ba8b7ba238b8afccb4fdd151abcc0c934ec65645e4ed3ad6b7cf2` | `9c5240cc223637ff9a3fefaacdfd2402c8fca57fe7b30b4aca15c0598263e437` (6) |
| `unweakenableAt_characterizations_nonvacuity` | NV11 | Quot.sound, propext | `ffbe339554ea55e900491e3fd94e9a55fde26d86ca5631cc5118d6a2bb7ea51f` | `5aa87f6cd49f7b5006caeee2bf2a1a1d077f1078aa74d89278d7f83b4013cffa` (11) |
| `irredundant_sufficient_subfamilies_of_sizes_two_and_one` | R12 NV12 | Quot.sound, propext | `23dc0786317a83596cc6db84d144022322e91ae2c6439d9b8257ad3aa2dab478` | `af2277043159240c3c2092498bb5dbdc9de70eb5c623caa3deae4689bc24dd29` (15) |
| `subfamily_eq_of_sufficient_of_irredundant_superfamily` | R13 | Classical.choice, Quot.sound, propext | `5188de72d544e97b2cf3a81a1f7ab481decd77e39816c74582365ca7eeb7549a` | `a2d32d178499715887d0943e546cd4bb28b26ae20fecf2117ec5a2f091d8fb5d` (4) |
| `subfamily_eq_ce_not_sufficient` | CE13 | Quot.sound, propext | `f8935a27150f26d04054e928870ae252509f35791b5e0e47cf83bc90b10b2638` | `a030e99b4028b40903921140771c0eec5eb5419b272e77eb7873b967c7146322` (14) |
| `subfamily_eq_ce_not_irredundant` | CE13 | none | `6af167969e1813b281963d260d561f56e7901d09e864a84e1550f7e8da7841d3` | `213fc0db6a62eaa9e24d1e273470ca08403cb8bd4a1290cdef39562b54680c57` (4) |
| `subfamily_eq_ce_not_contained` | CE13 | propext | `86df678a342aab3acf695a69a56a676418e3f17eccf2487db0910d588aca401f` | `cb6b6779872be600dee239f9d3fce66fb449cb934844dee0d305d108245c268c` (13) |
| `subfamily_eq_nonvacuity` | NV13 | Quot.sound, propext | `e35e94bd62100979f86edf3e23b9d5f74f5cf759a560cd7815b77c84d70f1cdc` | `ed5e6a39c5735bb29e907cc756d354a1f6fc481290321bc6b9b367ffe6cc45d7` (14) |
| `irredundant_vacuous_and_nonvacuous_tightless` | R14 NV14 | propext | `f939619adf23103eab0ef0bcb959da7e969321c0f3fe8c2f670a061c0dcf9f50` | `fa138a5414ca8acd109866fa21b0baed4607ca1187882c4467b0b61394d96e57` (21) |
| `not_valid_of_tightAt` | R15 | none | `9808e6cbe9c636abcb1fef1252631d2893648bec1d0de643c25ef8851f936f70` | `66872f8da15c2de87890aacbbdcd1a51debe6d0532c389b5ae405fbbdc76a3b8` (1) |
| `not_valid_of_tightAt_ce_not_tight` | CE15 PC15 | none | `3accad8fb25347d95f1c5099d24f501c2782211a4f34ef46772ed54d16f12d11` | `e7164623dcef5a9df9bf1333c6d25195df0eb26ef35924b813d1f815b9a526d9` (1) |
| `not_valid_of_tightAt_nonvacuity` | NV15 | propext | `0be9971cdc951deff367c4ef73d1605cecc086f6c3b4d2d644b5d641ff41f0dd` | `c5dc8f232e6f8759523814c8700baf11d737f0b82d907a0c4b28ecdef7d685ac` (10) |
| `schematic_ledger_irredundant_nonvacuous` | R16 NV16 | Quot.sound, propext | `be54bbd616752ca837960d17d41cb77da0e91c1acba347df24de81f940cdcb7c` | `02a6cba0d329b38fecec591871b35c006e7774741904a6ad975754f7c0e53b9d` (12) |
| `not_single_entails_of_irredundant_of_exists_other` | R17 | none | `cd420614989105bb577841e22914a723eeb408ef64d497193647873b7a035db3` | `2ebd9ca60046f2a82f793fcdb79aa73002aa7eeac02bbd180f098d72d308819f` (2) |
| `not_single_entails_ce_not_irredundant` | CE17 | propext | `c7d5d2843c0ab1602cde8b6394863ba06647f66849e23fda8c4449f9eb49b5ff` | `4f20db6cbc10551d9701bb4b9ae765445d883bec74d8121b3fc2bfd659306ab9` (9) |
| `not_single_entails_ce_single_hypothesis` | CE17 PC17 | propext | `4c8e3006f401368f2b4d0f15c5ce7d3df10b87d1b1565552d534ec09a991f419` | `4b705a191284d249b31ecc95dfe1cddcf84dab9b53a06b0bdc1aa5449be8caf3` (4) |
| `not_single_entails_nonvacuity` | NV17 | propext | `ef4c2ab73bd8174bd2bebc3c5f884b3e0595c970e997b73362f5356186c0821b` | `e91200d39e9cd21bdfeba6e0a0b491448a48d31cb365f7285dbb6892342597f0` (11) |
| `sufficientIn_antitone_and_tightIn_monotone` | R18 | none | `cac12efd349b11297b74e7290461c8e614ff541c505f4bd5ce789643125b47f2` | `6f0f3c104048caf6e66625cbbbd851ad626351e33f9668558ff332263bcbb5d9` (2) |
| `sufficientIn_antitone_ce_not_subclass` | CE18 | Quot.sound, propext | `681cef28fc45614d1a3894f78e3ff4ac20aca53ec33b0e4249be6593d191446d` | `8d86d31bb6d68b3d88aebc3e443d18679db473f9fe41d687891453ddb19da9ec` (6) |
| `tightIn_monotone_ce_not_subclass` | CE18 | Quot.sound, propext | `40fc82b054df090c5db08646ad024d12706ae00ae29706427db650e7cf9d5be4` | `d9336f6deffd2fbdb4c4d905f0af42ea593d05609d679963c38823830a181355` (13) |
| `sufficientIn_antitone_nonvacuity` | NV18 | Quot.sound, propext | `9ece5568da5052a35e33c2775b79e1eba5f278a4dc6707d7cb7eed3c440118ea` | `d9336f6deffd2fbdb4c4d905f0af42ea593d05609d679963c38823830a181355` (13) |
| `tightIn_all_models_harmlessIn_bounded` | R19 NV19 | Quot.sound, propext | `cd07af63172ea42c3b4a07f685fde3267624e349d842a4417f1fabf854e8d24d` | `8cf8ad1d54e8cb7b6a29e448fe08269f41b2157089c374c653b7f292c8eefeca` (15) |
| `not_harmlessIn_of_tightIn_of_sufficientIn` | R20 | Classical.choice, Quot.sound, propext | `b72fa685f6807b6a3c6244bbdd75085eb87b4f779f9de849b5629c7641795404` | `fb2eb993e34a9886cbaae1ad9128d5a74f9231285274b1f244e406fe5aa3b2c7` (3) |
| `not_harmlessIn_ce_not_sufficientIn` | CE20 PC20 | none | `c559031e5b80b506a43c821798aac736bc5611a709e6657adb5bd1c7a2ec5682` | `ce8ce5828528d70f3b5919d649277133c8d9aa6bfa59255c589554b29abe8e14` (6) |
| `not_harmlessIn_ce_not_tightIn` | CE20 | none | `1a27b81c7608ff6374057a7f8639b144d98fec5e2ef185fc3d826f05d8d1a6f1` | `23905fdf83a771e95f2c97e71e1e091e0c9c6d59db12a2c8fc5b76f79f19bd9d` (5) |
| `not_harmlessIn_nonvacuity` | NV20 | Quot.sound, propext | `abd4c3a525d8305c6ddfbebc4388fb748d9016aba49595b1dae7aa98b798820c` | `5b6d7ce5b0140c5853ccf21bc40a2bd23b7dc5b222906a221eac86bce7aadc71` (12) |
| `sufficient_conjunction_iff_each_and_tightAt_conjunction_iff_some` | R21 | Classical.choice, Quot.sound, propext | `3d158d79c4b8ebe75fbe35abaefcd156cf2266f9a8524c460287f464ec659226` | `d2843b2580d7640f6501a796cb9d8dd76fd915076f04648658089b9a183deec3` (2) |
| `sufficient_conjunction_nonvacuity` | NV21 | propext | `4500436905fabb99c49f5b4b57cb0c31d9b7dc481d6193af0732204bb9eb9ab6` | `9a2d4e9ee571bc9bf721cf2c4a9e4aab52aadf658016a86e645d15b000cb1c4d` (10) |
| `tight_for_conjunction_not_for_conjunct` | R22 NV22 | propext | `3d3bcdf762f7ec74576992afdfe3bd182564efcfd866f126168c6c54320f8e6b` | `baac77704768d5d68160cb06c5f35903a02343b74e05988116e15d4669c9088f` (11) |
| `check_of_cell_empty` | R23 | none | `8f1033205833993bcf75d6402284edc152e44d62e9f9d8bae9f7104475f1759f` | `c9854a16015e17ec23ef5170275bfed297acfaff54e53cdd1440f7645c99b397` (1) |
| `check_of_cell_empty_ce_nonempty` | CE23 | propext | `04e167559f155fad9adead3d6d18c4f48ac3b45291e0b60ff57e62b5b342981a` | `f35071e125855dc6f3908082c7075d49cc0628ab72fe4f89784ec9dc81bea0ac` (9) |
| `check_of_cell_empty_nonvacuity` | NV23 | none | `77a7c38888a60e854d8b5013ad3daae2df5d3186ae37f96717d022fc63146c4e` | `e7f408201394f807a9f4f0f7325df8aba5bfdceed7baebc38f30facd2bdafc59` (7) |
| `all_checks_with_every_cell_empty` | R24 NV24 | none | `8fac2674a7dab98b3d4cd8c3be9b4373bc8269ab55c6bacf187eac54be3d9c76` | `b1e3a56bc0840e39bbe34fbf9725b157d0ae3ae75d8b184ed6728a5436810f66` (4) |
| `classify_sound` | R25 | Quot.sound, propext | `edad09cad64b3e7ce51dcf80a475fcdd08646a1c45e0279447d54a981be85806` | `86f108c4f9bd03797a84c1ac74c5c13e1b12ceb6531487aacd3a5ea05237d210` (22) |
| `classify_demo` | NV25 | Quot.sound, propext | `9f9a83122ce6dad03003f8641d1b8a86270d3015a429e3836337a49e25f9c68c` | `8cc370838441f18c0791004a97170c9a695034ab9f210dafe01d09be6a2c99d5` (28) |
| `classify_complete` | R26 | Quot.sound, propext | `2380bd9c4d26f41a55d816cd630ef9848d00154157b0e82578f746cbb0bd1c77` | `f6d3557a64efc5ffe27fd5f9ba143fb6fa4be32e8a00318aaa511987df5279d7` (23) |
| `classify_complete_ce_incomplete_univ` | CE26 | Quot.sound, propext | `449fa20a76441a2b4df849867305b01859cd2930bbd069580574304156692f24` | `b7221055527e54e025e005a59fabe19755f9b3acc736220cee7c99edfa4e7d04` (31) |
| `classify_complete_nonvacuity` | NV26 | propext | `e44f993a05dc3742ffb22180e9102b8fc0cc6e726595855ea7a75b096a30e927` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `auditLedger_sound` | R27 | Quot.sound, propext | `8ef93bafb6bca6a44357da3829b9c87e7a11c949263ad285585e577d5f3f756d` | `933eb7c3778fb92339e096eb96f6b7c3fa2e9abbab990812273ca0e05503a0c3` (62) |
| `auditLedger_running_examples` | NV27 | Quot.sound, propext | `d3a14c8907ed6556685cd2d3dcf3015cb9214f9c517110cd31a57044a8c21ed6` | `4f368e01f350ba2a538041bbd6ffdd88b806ec6ccd2df0715a0d74f603f3c79a` (66) |
| `auditLedger_complete` | R28 | Quot.sound, propext | `8c218cd70e74c66405faf905b9a9d166230652444e8da142d3493e7c50340f46` | `25908d9ce3048e45683ba331d5ea0ab4fb800a60dbfd5d953dc153b2bf09573a` (66) |
| `auditLedger_complete_ce_incomplete_univ` | CE28 | Quot.sound, propext | `62e71740aa33b873ab5853b01d5deac33f1d03b63a7b174cb3355bb732e8ca76` | `021325c18ae9a2f29ca2ec3adb2a7731c6152e79e17e3dbc48ea6146181d8823` (68) |
| `auditLedger_complete_nonvacuity` | NV28 | propext | `e44f993a05dc3742ffb22180e9102b8fc0cc6e726595855ea7a75b096a30e927` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |

Other package-local declarations named in this report: definitions, definition tests, auxiliary lemmas and the supporting lemmas of `SupportingLemmas.lean`. Each is listed in `results.json` under `lean_names` of the result shown (the first result whose card or non-claims name it), so its hashes are recorded in `audit/statements.json` and recomputed by `support/revalidate.py`:

| Declaration | Listed under | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `Sufficient` | result 1 | none | `76e4ce2cfbcc7e2d0dc79c8f4270b1526e16e68041186382a2498ec393debda7` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `TightAt` | result 1 | none | `48369bc6185940affcd876a098dc0afdd44cf0d69515f19260393dec22aeb7ce` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `NecessaryAt` | result 1 | none | `48369bc6185940affcd876a098dc0afdd44cf0d69515f19260393dec22aeb7ce` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `UnweakenableAt` | result 1 | none | `48369bc6185940affcd876a098dc0afdd44cf0d69515f19260393dec22aeb7ce` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `IsolatingAt` | result 1 | none | `621092b15851f98b0fe8e5749ab7fe38f179162f623c1a2b1e797a850f6a097c` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `pinH` | result 1 | none | `f8ecdfea9bd9e65d346edad5d258fa37f4d889ee433bb9e8a63c5ea878ee08c1` | `5aec7548b993a5b704c981ed8b5f155e8a8a7951c09f100c7d32354dc3926f05` (3) |
| `pinC` | result 1 | none | `e5fe6cb42329f6d21f9f0d4e2df65ebc736c04091cc1984c7175afe68616ec8c` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `falseC` | result 1 | none | `f698023e7f4ba63354c07f05835c77c58ca4ba77711cbcb470c8fb92e1735b9c` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `sufficient_pin` | result 1 | Quot.sound, propext | `18b0da4f03fc20a269283be62bfeacc4601ad59f105fbc29e2042216ff5102f1` | `bf56f3d37b2bb5a0a5dcb806b68f6345b211ca85538bc44a0e5bc246e8de7f80` (10) |
| `not_sufficient_single_le_one` | result 1 | Quot.sound, propext | `014ab7921b898ed7cfe641f00452b6879c2aea3461e0592656ea83a166cd7c99` | `3b4a1fa5033224d234e517f7c557596aba9bfbd08b622d1bfdedd64b7b0c06ec` (3) |
| `tightAt_pin_h1` | result 1 | propext | `0be9971cdc951deff367c4ef73d1605cecc086f6c3b4d2d644b5d641ff41f0dd` | `c5dc8f232e6f8759523814c8700baf11d737f0b82d907a0c4b28ecdef7d685ac` (10) |
| `tightAt_pin_h2` | result 1 | propext | `8451f569b1c39544956a130afaaf572fe49dd802336665f53f175b9fd12ac26b` | `c5dc8f232e6f8759523814c8700baf11d737f0b82d907a0c4b28ecdef7d685ac` (10) |
| `not_tightAt_pinWeak_h1` | result 1 | propext | `608963a6741081fbed4601027a927ba4b8694956e33e9783121bafb4bb68f7de` | `2949c28f45be674e8ee4312d0c6ee977511cec0a0379d24e06a60d1cb00c8a4d` (10) |
| `topH` | result 1 | none | `78c8689a978897421bdf962391e50ad896f62a33a1efa05a3407f9e6d5c694c1` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `restrict` | result 2 | none | `c8cb742e5ab9e7e085075c703d42c53ed356c1e243d7f4adc94052b23dbbea70` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `sufficient_restrict_sumVocab_h1h2` | result 2 | Quot.sound, propext | `4001368702c7a1cd88d6563b680e1f213c7bfc19e85ee55e2780c38a4d7c39b2` | `cfb30ca509d822d6f4217caae2599c5348a26896d617597bc8f9d60240dd4a7f` (12) |
| `not_sufficient_restrict_sumVocab_h1` | result 2 | propext | `1fb7531af8431d6f05d72cfb4098b45b95f5a8f7c2877cd3ddf5cc886972135c` | `cfb30ca509d822d6f4217caae2599c5348a26896d617597bc8f9d60240dd4a7f` (12) |
| `irredundant_of_not_sufficient` | result 2 | Classical.choice, Quot.sound, propext | `2b31a0a1fa73ffde608aae6d2c8116281d2466e53a0bd9b7571b5e57820b8777` | `daa4ab2cce34e0df5451ebfe41cb384487d963281f6506ef90f6ae3d00f9e907` (3) |
| `dup_each_not_tight_but_both_needed` | result 2 | propext | `10b928629dd77066bcdad148e4ae517e36dee01478486eef99f36dcb92b70b40` | `8c7f01f2996e705778435cc9735728859302b5d7cae0209578c90f036e799975` (12) |
| `geH` | result 2 | none | `2fb278b5e81f71acc7a3d7d89584c37cb41164fe77eca535951e8b0c3dbaa361` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `geH_sufficient_no_irredundant_sufficient_subfamily` | result 2 | Classical.choice, Quot.sound, propext | `4b581abb21303b293374e975d4d90cb222c8367fc0abe7d3faf7203f1b4f54f0` | `efd126f39cf917792b97473ca29d1471c1d6a33eb6d0ea22e6393e80afd23a4b` (6) |
| `Irredundant` | result 3 | none | `76e4ce2cfbcc7e2d0dc79c8f4270b1526e16e68041186382a2498ec393debda7` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `single` | result 3 | none | `a6dc9cd62b2c56e70efa4cd7e49809e89b8a792e62c2fcac1d91ea7c94d3e479` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `irredundant_pin` | result 3 | propext | `55d2aa87cd64931bd71e72dabfae520459a9d9a4618911cd0c0c696768fc5dc3` | `e91200d39e9cd21bdfeba6e0a0b491448a48d31cb365f7285dbb6892342597f0` (11) |
| `not_irredundant_dup` | result 3 | propext | `eee3074ad29c69d8e11f95b8bf65a9e4d9628f109e52303601557a2425839d9e` | `adacc7a55c3d8f40ff33e4a0869cba2bc9772a8fb9c3e66a26d61a109856c178` (11) |
| `irredundant_dup_true_false` | result 3 | none | `5ae7b308b00e702c91ac1776851a23869fb87117a9bb50255131c2c5b3f8f9c1` | `584923409e791abc2a5f7950be37f99b148ce88715cba0b435301a7a9acbb774` (13) |
| `irredundant_sufficient_subfamilies_no_candidate_equals_conclusion` | result 3 | Quot.sound, propext | `9ae018c308ce57693d59baf106eac1d93bc7d22edc5a25f54f87520c241c240b` | `e222c4c1421f236bfe7c997f4206c8952105b1e8ba2799497aba3c47dd23474c` (15) |
| `NonVacuous` | result 4 | none | `79c12f5db2e9ac8210ef7a961a84785c8ae07d1ba51634c5f2a39db67c639a0c` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `MinimalUnsatisfiable` | result 4 | none | `403162cbacea3ac0c2746c8b12b21cb6d2e0d2bf19b526436ce25d1ba07a88a5` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `withNegatedConclusion` | result 4 | none | `69d23dabe489bdee6b36d556ad6752bba0237982a217d58281ecc8424def16ba` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `nonVacuous_pin` | result 4 | Quot.sound, propext | `f8b596b6db3d07f488cd2ccc1f0c19751e97d22fffc0b17c194acbb52d11c983` | `6bbee75dc960d5c939888f646b1088e89b93107bd0157b08eebe5c196aedb24f` (9) |
| `not_nonVacuous_vac` | result 4 | propext | `4085cc23c2906ee8fa5bda42fd24d1f205412519bd06c6fd8b9ffa67284433ad` | `40c77401188d2cb1b92e8ccfcc56f470e87900d97d5c4e2b53a9692c60080e20` (10) |
| `minimalUnsatisfiable_pin` | result 4 | Quot.sound, propext | `6a5252b3f8094cf17bd1e0143652a8b712c6f40ec04e2cd298cf1683beb2c69e` | `afba907d4f6638f83d9607ba53484f00076a15edb33bf98e005489f5cb60f90f` (14) |
| `not_minimalUnsatisfiable_vac` | result 4 | propext | `e4b2d314846fa9f551cb6145731ff4772ae35ae73f3aa5618dee7beb9ec569ef` | `8b2183a934befa51ac13c8da241354bbcbf4dfe44232b299689b3f044288cb22` (15) |
| `Independent` | result 5 | none | `79c12f5db2e9ac8210ef7a961a84785c8ae07d1ba51634c5f2a39db67c639a0c` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `pinWeakC` | result 5 | none | `e5fe6cb42329f6d21f9f0d4e2df65ebc736c04091cc1984c7175afe68616ec8c` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `trueC` | result 5 | none | `f698023e7f4ba63354c07f05835c77c58ca4ba77711cbcb470c8fb92e1735b9c` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `bitsH` | result 5 | none | `127722aeb15822615b75fd1370f49fc9ed9fe3ccfd662aba6dc287cf2aab7616` | `5aec7548b993a5b704c981ed8b5f155e8a8a7951c09f100c7d32354dc3926f05` (3) |
| `independent_bits` | result 5 | propext | `5cc6ede9272f89e5125d5be70c9f2bf33b53b4e80983e20bf08b532dc3e1731b` | `96efbb631c73dfbfd48debbc58aa2c0335c130691d8ea0bc28e457a4dd395159` (9) |
| `not_independent_pin` | result 5 | Quot.sound, propext | `212a7b5e0f509f9f3748e23183750c33b6cd9cbc90c8671c589f0656731b1d60` | `f095a7f8412ab40d2c55fdb31a64a8abf93c5cedfba6f313568e01d2a2ee203d` (9) |
| `isolatingAt_pin_h1` | result 5 | propext | `34993f36e386346b50967300ad8d46d2b389d2cc98c70ecf09438f7f1013be5a` | `f1811d646d7c9f255068af3b81e3e7fc6219248dc5cffbbd8aad762d28b6edeb` (9) |
| `not_isolatingAt_dup_h1` | result 5 | propext | `cd103629e0f026ddfc10f0c20927fa236307c7389008cb237952a595f76afa23` | `68c6fadb49619a751f6e7417b4ec9df03300aa38b8c7aacb2a6bfb5e7f420801` (9) |
| `isolatingAt_every_index_not_irredundant_pinWeak` | result 5 | Quot.sound, propext | `2348aac4cedaad11eea9aa3392288e48816ab10d454349c3f5b40f77774272f7` | `d0363e464bd46c8d37ed625a947e2a45a46c16863fb5652773c25d83c03aae6d` (13) |
| `dupH` | result 6 | none | `f8ecdfea9bd9e65d346edad5d258fa37f4d889ee433bb9e8a63c5ea878ee08c1` | `5aec7548b993a5b704c981ed8b5f155e8a8a7951c09f100c7d32354dc3926f05` (3) |
| `isolatingAt_sufficient_not_tightAt_pinWeak` | result 6 | Quot.sound, propext | `84db91ea69a32e5da916880e2d40afd161deabb626a390c819f80c7009f45f56` | `4a2894b2274e905ff739ba97f94e1c986083d293a575eff81fa5db1f3b74a1b4` (13) |
| `sumH` | result 7 | none | `e6515faf9ada5b98b0f9ea711e0540503da7c2b896644e98f86eb60d1bbb5560` | `5aec7548b993a5b704c981ed8b5f155e8a8a7951c09f100c7d32354dc3926f05` (3) |
| `sumC` | result 7 | none | `464336f836b487a60ed29913e96455c254836c65e2534e29e791bafca19a9c68` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `necessaryAt_pin_h1` | result 7 | Quot.sound, propext | `80d3c7f0210609a0ef6eb0320bc9fa89786c5418dba269e3f36cbc7812b9ea43` | `290d69b33fed578a2183dc9027dadcd50de2bec27c921b0345d6e972c40ba496` (10) |
| `not_necessaryAt_sum_h1` | result 7 | Quot.sound, propext | `d5e6baa732685eec43961b25673fd4673bcc47ac88235ad7ce1bca422a8df15c` | `f3bcee50b97242e3f648796a6d880a317f50cb56e436fd83f1e05f9b6383053c` (10) |
| `unweakenableAt_pin_h1` | result 7 | Quot.sound, propext | `10ddb89bdd64912cfecef89b27a067653cdc0ebf34ba1aa4626ba6d980cfe9a9` | `2a21d740444431ab0496c3127a2eb63eb0b84afb1a60d3a7c5b9e1b3f63ad112` (10) |
| `not_unweakenableAt_sum_h1` | result 7 | Quot.sound, propext | `d38e6e72441b830fd67bb4240c8a3ac1f7d6d32903d0cdb2a211e11d13625f75` | `7a6f352976a19d440a805e295acb242d886806b64dd7f8fc1220ae45aa930285` (10) |
| `sumH_h1_weakenable_but_not_within_first_coordinate` | result 7 | Quot.sound, propext | `dfdea9b67500a63feb1ddc2dd97169001b4baadfe4333e51aa3b6050c14c56f8` | `29d68af9e15ad41fc8916996479da3550f2478e720fef0b5f652f4ec72ee7905` (12) |
| `eqH` | result 8 | none | `e6515faf9ada5b98b0f9ea711e0540503da7c2b896644e98f86eb60d1bbb5560` | `5aec7548b993a5b704c981ed8b5f155e8a8a7951c09f100c7d32354dc3926f05` (3) |
| `eqC` | result 8 | none | `464336f836b487a60ed29913e96455c254836c65e2534e29e791bafca19a9c68` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `entH` | result 8 | none | `e6515faf9ada5b98b0f9ea711e0540503da7c2b896644e98f86eb60d1bbb5560` | `5aec7548b993a5b704c981ed8b5f155e8a8a7951c09f100c7d32354dc3926f05` (3) |
| `tight_combinations_in_irredundant_families` | result 8 | propext | `0613856e296bcc7229a0c921d681f1429e785cc78cfa64e5ac4241af67397355` | `0507f2dca90a27a6d09f1abb761d8f86790b067537893d31f80ee8540f3ecf6f` (15) |
| `not_tightAt_not_entailed_by_others_pinWeak` | result 9 | Quot.sound, propext | `d8a312ad0532db0c0dbea6bf60fac140e87428e5216e298b678c2681d7e8c34d` | `80b659635ab5a62cde455aa52caaf7a42105f0727a5bfeac515b6055768ea4fc` (11) |
| `replaceAt` | result 10 | none | `0e6161d67c6b8fc5de6bfea91c14bb014a7e955837997bebeb6f1d8b63a64bef` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `WeakestPremise` | result 10 | none | `a5e33a8e27653456ea53a0c325f3f840e1818e543e0a434a56f399195ed81d29` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `replaceAt_self` | result 10 | none | `bc8af7b562a169ebda1fe15a667001b27f4d114e2051a10d58030aaae5f768cf` | `3c9b785316788b1cf32491424596166978200c53ec4a65b7d6fe1b3340f414ee` (1) |
| `replaceAt_of_ne` | result 10 | none | `1ab73ce8655913542d0cd594a5f33f0d19965ca0612477caa0100ba4d8368114` | `3c9b785316788b1cf32491424596166978200c53ec4a65b7d6fe1b3340f414ee` (1) |
| `replaceAt_iff_ite` | result 10 | propext | `b7bc37bfc72494459d68c4d7c74db7deefafad8fae05f109db284dd51f880c0f` | `3c9b785316788b1cf32491424596166978200c53ec4a65b7d6fe1b3340f414ee` (1) |
| `sufficient_replaceAt_sum_h1_by_sumC` | result 10 | none | `3976ad651a5c5ff33edf2757d05e17d22f5ded687c2712403ea3ebb2194f5491` | `2c0f2b150697cf7970682354a1d34273bdfec453f9a718a203460b8d04260905` (11) |
| `not_sufficient_replaceAt_sum_h1_by_true` | result 10 | propext | `8031e0cb8897afc4f849568c7acf4515d161f0d9b8bea328ee1aa8fa67b6f3e2` | `53bf6049f01db5e6940733bcaa2b5765eb2453a748d4b1ded9822bb9ff22c0df` (12) |
| `weakestPremise_sum_h1_at_2_0` | result 10 | Quot.sound, propext | `a8edb8a1c1203bfd32492999492e0b45fb138b1488796ea6d03f11b4fcd62f2f` | `6dc0ef0f618123e2072ea2c89fd024d5e4da21c12a6f3c854e5c4b0d2184f4df` (10) |
| `not_weakestPremise_sum_h1_at_5_0` | result 10 | propext | `3c53469bf13d51e3bc680bd027396ad3f2e137b9d5e96f0a9c9424511a0d4454` | `6dc0ef0f618123e2072ea2c89fd024d5e4da21c12a6f3c854e5c4b0d2184f4df` (10) |
| `unweakenableAt_true_false_disagrees` | result 11 | none | `1f29715fee0e6c29e8fdc2ddba772f46014bd85dc89f701649242c53dcb88e30` | `a1bbfae4d6cfab002bc0638d0a022889e7e82edcfa3fff578638a6083bd9f0b6` (5) |
| `flipH` | result 11 | none | `00f9c33d5e1bd23e3bee042757d3e2a079b497a2b5dd1469183b13033d89622b` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `flipC` | result 11 | none | `1b3fab044317b44442da6f0e43afba8fa4e0aaa49dfe9128de0abc9eee0fe5a1` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `unweakenableAt_first_characterization_holds_flip` | result 11 | propext | `3b139963b4254887cd215f0fed3923fea106c3a6f9ba4ef0f3ec24a6e48e6f70` | `da92117f91aeb87fa004d80f684f3e4e92950161999c80a0c232ea6fa5ee1ae6` (5) |
| `unweakenableAt_first_characterization_fails_true_false` | result 11 | none | `1c8dc2b0da2912dce11fe4396b4045ec70b689737410ac3893693e982edaf3dc` | `a1bbfae4d6cfab002bc0638d0a022889e7e82edcfa3fff578638a6083bd9f0b6` (5) |
| `unweakenableAt_third_characterization_fails_true_false` | result 11 | none | `694c4f08aa27bc78b15d6ac0acc78dc50e9ec3cfb34a58f3ea89039b673e851a` | `a806b3c65c3f93cd414dca6a3ced3dfba64bc716e87bba775fdbf4b0cb8f9b6a` (4) |
| `Three` | result 12 | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `triple` | result 12 | none | `635e515c67bc195c137598e549186f0b0bca803b441d939630b6d42ee1c8d979` | `bef8d3cadd15e8dc00c6f75abee93469984b2f9e19a28bac2b1f8ec665a959cc` (4) |
| `sumVocab` | result 12 | none | `f6b3139584e0e6e15e40661bea50bc48c4b50b971bbf37f04fa965a321129291` | `bef8d3cadd15e8dc00c6f75abee93469984b2f9e19a28bac2b1f8ec665a959cc` (4) |
| `intVocab` | result 12 | none | `2c09ef3bcb0e30fcf4eca7359138502e53a4c0849e591e07a3ee7fcac0e7fd56` | `bef8d3cadd15e8dc00c6f75abee93469984b2f9e19a28bac2b1f8ec665a959cc` (4) |
| `intC` | result 12 | none | `e79ef2f348d1cb58ba51178001d10be615e42413b190521410d4e182931f4139` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Two` | result 13 | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `vacH` | result 14 | propext | `5ba46efc675f3af08064bcf64f6fe843932aa3df68f1de4928610894527fd76b` | `5aec7548b993a5b704c981ed8b5f155e8a8a7951c09f100c7d32354dc3926f05` (3) |
| `nonVacuous_of_forall_of_nonempty` | result 14 | none | `2221ad6bef173f2952ae6bebab70c59270c1a134d72b9e46359d0afe7caa7242` | `19ff06e2fe2322c9c22073cce57a524cf1a1a05353e920b21418954a50cf7b75` (1) |
| `nonVacuous_pin_antecedent_not_everywhere` | result 14 | Quot.sound, propext | `45c46e3683e6b3b13cab5e02569c3da71421ac58ff273a2c911f3b3236e43af1` | `6bbee75dc960d5c939888f646b1088e89b93107bd0157b08eebe5c196aedb24f` (9) |
| `antecedent_everywhere_not_nonVacuous_empty` | result 14 | none | `3d831d7e31e789de5198aadfb36ad42386b90a687b7cf90ebe5a40b97042f980` | `b37db6bcfd06ae698e90da3426e8b271b79c9492f32d5d8ae42c7e5ba7aca633` (2) |
| `tightAt_pinWeak_h2_conclusion_valid_on_bounded` | result 15 | propext | `43dd6bc468ddb50b43bc28cda918a1f080a573748834f1a2a683aa5fc65e392a` | `7711ca45bc9974f93be2a68b8f0704151626209d1ce5182f2527041f6306f4b1` (11) |
| `schemaH` | result 16 | none | `519f78cdef4d877fc923aa266b27213d0792bcd700b4e48bee0760cb7370baac` | `5aec7548b993a5b704c981ed8b5f155e8a8a7951c09f100c7d32354dc3926f05` (3) |
| `orSchemaH` | result 16 | none | `519f78cdef4d877fc923aa266b27213d0792bcd700b4e48bee0760cb7370baac` | `5aec7548b993a5b704c981ed8b5f155e8a8a7951c09f100c7d32354dc3926f05` (3) |
| `or_schema_irredundant_nonvacuous_necessary_unweakenable` | result 16 | Quot.sound, propext | `28bdcc5c78543de2fd73997890dc6ca20bfc9ff0bd38c8e8f93c4293ddbb5712` | `3cd73d4cff819b1baff7e4c0053cced862ea994ad5bf91c46e474d46cbd8cac0` (14) |
| `pair` | result 17 | none | `039cc8f6fa6aa7ce229545572a22061a6b9f839d63a78ba794b2f2f6fe8a4c5e` | `5aec7548b993a5b704c981ed8b5f155e8a8a7951c09f100c7d32354dc3926f05` (3) |
| `not_tightAt_of_ne_of_single_entails` | result 17 | none | `62fb098c0cc54076161b2f2f96ebd3e72118e9340f09ee940b7380c0acbcc3d7` | `66872f8da15c2de87890aacbbdcd1a51debe6d0532c389b5ae405fbbdc76a3b8` (1) |
| `not_tightAt_of_ne_ce_not_entails` | result 17 | propext | `36a307de2c464ea15579f42a065123543914e409d90fc95922e48ffaf08e4511` | `c5dc8f232e6f8759523814c8700baf11d737f0b82d907a0c4b28ecdef7d685ac` (10) |
| `not_tightAt_of_ne_ce_same_index` | result 17 | propext | `4781f71f6f1d05b92040f88f9c56857d30606a84f451dc23c91255caca7e5aa6` | `9844ae9f4a29d783ea0809f0e2cfd26b85e920fe0713ee9a5b1e25a588432747` (3) |
| `not_tightAt_of_ne_nonvacuity` | result 17 | propext | `18814da9156a6702a01acf4c46e70e0dbf86639cf3f9e01db82355aade7528b5` | `b924eb0b3838e6dfc04faf87866ca79b2fa235e09607ea97795efa7aa3d06e15` (9) |
| `hatchH` | result 17 | propext | `5ba46efc675f3af08064bcf64f6fe843932aa3df68f1de4928610894527fd76b` | `5aec7548b993a5b704c981ed8b5f155e8a8a7951c09f100c7d32354dc3926f05` (3) |
| `hatchC` | result 17 | propext | `aebf9535cdc81cbac3be3fe80f1d7f887fbd1fb2e11f70e6d7045dee4dac3607` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `irredundant_hypothesis_restates_conclusion_within_other` | result 17 | propext | `a3fc402db187b0439b0d36a71259fb470940e531eff4b21c567330be495c7c94` | `b98dcf6f69cfdbf3bc931d617bfb543f70f7b8e557efc12f2c10d52a8c3abe82` (14) |
| `SufficientIn` | result 18 | none | `a2cf3f83cee88d94d66fc7932faa12da816eab005fb43b22b8d98d39bffe2552` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `TightIn` | result 18 | none | `50e7ffbef82e68321c3e6bfab0803209288187aa6c1cc365246c4fce3ef791d1` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `bounded` | result 18 | none | `e5fe6cb42329f6d21f9f0d4e2df65ebc736c04091cc1984c7175afe68616ec8c` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `sufficientIn_bounded_single` | result 18 | Quot.sound, propext | `0452b68b50d9884b67173646fbff41aa2537ce4f2583360d9abd369f9c52a8c3` | `c6c5b876f67bea1bf874a6550b7612317f010d72219ec5541b3711ea6fda1244` (4) |
| `not_sufficientIn_true_single` | result 18 | Quot.sound, propext | `4aa3d49b2b2dab0298e4401bb7bec55ca927082e8a44e98a4131d2ccf8f9fcb1` | `467896e0c4f2ec7d8abe109ae52509c05c6edf72508f8d98c3a0d66845d79457` (4) |
| `tightIn_true_pin_h2` | result 18 | propext | `eb6193e29d81d3be7feea61b2d17ca5aadbc7263c3a9ffc3292ffff506da5359` | `aaadf1a8605ab56e607f6fd05cfc8c9a6a19d2817ffb92872c4ebe4d90d7b207` (11) |
| `not_tightIn_bounded_pin_h2` | result 18 | Quot.sound, propext | `f75e74e5b98400f198528728782f6ce8729385c74ed8ec243c983663475872ae` | `3ec21bbfda9db7fccc74a17e29b638fe843fa35ab094ba2631158974cfabe877` (11) |
| `tightIn_true_iff` | result 18 | none | `6be613d22cc3d0e441e9fbdc3f2c8a15a0ffb26f55235e1662e6299bc3a81737` | `3c8c9c6d302814d073113a19a315a52dcccc56a616b5bb2896858c24172638a1` (2) |
| `nonVacuousIn_monotone` | result 18 | none | `67d23bdaba742ebbf0ab3c03d0782c9fb84c8135802ebe61bd817b3a66a8c600` | `5151c5da0cc4980a65df00b8379e20d3c6fba3eae54cd0014eca69489243ecf4` (1) |
| `nonVacuousIn_not_antitone` | result 18 | Quot.sound, propext | `3531b6286eb0aad5fa602956d3918c57b899ff34fba65c405e6e91d103f55a9f` | `9ca70f243fd0cee86650d14f96b9555cfe6a1e0e9ebc9031e37f54985b498768` (13) |
| `NonVacuousIn` | result 19 | none | `7f73c2a55f3dd62e61f5b2bba97ad83e761f3610fde7225b15e3e035b44c8ed9` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `HarmlessIn` | result 19 | none | `5a756acf595c115edbf82de2da3656e2fa3486e730214f000064db05f318fd8d` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `harmlessIn_bounded_pin_h2` | result 19 | none | `624c8602d9e8f75b6934c21d1bc6ecbd06f56a7af12d5c00b0c0879c56bea697` | `40cc00302231f87ec52ce1350575733062fc105787cb55331d229410a9524c65` (10) |
| `not_harmlessIn_true_pin_h2` | result 19 | propext | `ff9cd800eda3a20046fe44044e160fef35def2d7075be418cbd581637f93399b` | `4c5bbcfa69ff0754232293b3071cd9c9cf92b41c8520020b38e466e76ae2c3da` (10) |
| `zeroClass` | result 19 | none | `e5fe6cb42329f6d21f9f0d4e2df65ebc736c04091cc1984c7175afe68616ec8c` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `nonVacuousIn_bounded_pin` | result 19 | Quot.sound, propext | `2136ba1fd0736ab64a995c0c19f76057ecdb68e21fb7ce0196f298e884b297d5` | `08f445ba411712a56246949b7ce3d7ea288adddfc9cfa57a32ec8e4578753ac3` (10) |
| `not_nonVacuousIn_zeroClass_pin` | result 19 | propext | `29bba47cc1ca19e52dd6c0a2506302018edd9bdc0273b695b4a3d8fb6b31d3ce` | `aca8afb920fe15f32885f1f5b53710ba723ab5879178df7ab92fe8122f64fab3` (10) |
| `tightIn_harmlessIn_not_exhaustive` | result 19 | Quot.sound, propext | `365ef91bc8bacecd64cf4b0656aeeb7188af010c729c31c882d2e03a11e74a31` | `710c0b2babe71de8244d9426c6e36e83292e0c92b94665e3c2e510208f2eaa72` (13) |
| `unweakenable_for_conjunction_not_for_conjuncts` | result 21 | Classical.choice, Quot.sound, propext | `3efb5db9687aeca3c3cf9ac6c16a906bef5d1323559014b953c53309651b1dcd` | `5fdea21a656c4aff1acc2063a453c1d05e0d2178be57913c0d45aabe271015ea` (4) |
| `Check` | result 23 | none | `ff4336d41b7d46c819828c62a26e9b319d9991f897ef8a22167e86437c766841` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `demoTable` | result 23 | none | `ec9479aca44c00b5e1bafb62aa290a2183512193d073e783e22a3c36f985e4fc` | `5aec7548b993a5b704c981ed8b5f155e8a8a7951c09f100c7d32354dc3926f05` (3) |
| `evenQ` | result 23 | none | `e5fe6cb42329f6d21f9f0d4e2df65ebc736c04091cc1984c7175afe68616ec8c` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `informativeCheck_demo_h1_h1` | result 23 | none | `eb38a22bf177b2baa5aa87c74e89c04fd9fee55aa2706a24b4fc49c4462b3eff` | `33e2b2cc6bfed56991dc6f070da8cccd377722886815d714508e472a1635c569` (10) |
| `not_check_demo_h1_h2` | result 23 | propext | `04e167559f155fad9adead3d6d18c4f48ac3b45291e0b60ff57e62b5b342981a` | `f35071e125855dc6f3908082c7075d49cc0628ab72fe4f89784ec9dc81bea0ac` (9) |
| `check_not_informative_demo_h2_h1` | result 23 | none | `6c449d3994c300b2afa0cdf04617cc5940f25b86dfb7f17ac5a67a4fcb26bd58` | `33e2b2cc6bfed56991dc6f070da8cccd377722886815d714508e472a1635c569` (10) |
| `InformativeCheck` | result 24 | none | `ff4336d41b7d46c819828c62a26e9b319d9991f897ef8a22167e86437c766841` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `emptyTable` | result 24 | none | `498183848f4b46ebd118278bf37618d0b880148fbef694c9d168999ec768fc60` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `classify` | result 24 | Quot.sound, propext | `0d89e2c9dd1b99694b6e04ed66d5f82b41401e2bde1656da0da5c49144b24467` | `9745640ae6550da63957875a55746612e7800b1cfaa67a972bb63100b50619de` (4) |
| `liftPred` | result 25 | none | `d4146b2c23b1413cbea06ba12627b85d291d9578d90e89a0a9193ef0251033d0` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `liftTable` | result 25 | none | `f2fc87356adaa954ecc435816f1954f234606c46784fb677c9552d64ec4359e3` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `find?_eq_none_apply` | result 25 | Quot.sound, propext | `4e30a85499fb0afeb32867eb224504416aec978d108a49a10c688ea83ed6b888` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `CellVerdict` | result 25 | none | `b809569ffe3278b8e94ae7c5f8b7c154351ea453be0b29e32ed21acd16067c31` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `CellStatus` | result 25 | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `CellVerdict.status` | result 25 | none | `7c3176553ce9c716e3257740a47bbd576fd3b6038ed65b2eb2d5873adf49351a` | `95adeaaa4391176c07df2aa293ac0afa8b2f2b74aa398037c28f006e65e5ebef` (8) |
| `CellVerdict.witness?` | result 25 | none | `0e0ed97d9dd9d6fadb96b4859c6502a1dc2d4d430d62074f5212e31ca3ddd94f` | `9745640ae6550da63957875a55746612e7800b1cfaa67a972bb63100b50619de` (4) |
| `classifyCell` | result 25 | Quot.sound, propext | `58a30dca357dd3c3695dcfca5a83504a7ea8442b2fe05b06b0c2444c2e4fcd75` | `9745640ae6550da63957875a55746612e7800b1cfaa67a972bb63100b50619de` (4) |
| `CellVerdict.Sound` | result 25 | none | `cd48448ecad95be9c53bef6aeefe798df0805502544cdbb88b4fe0a132309edf` | `9745640ae6550da63957875a55746612e7800b1cfaa67a972bb63100b50619de` (4) |
| `CellVerdict.sound` | result 25 | propext | `ce4bd78c6ad906338aecc0b8bec939164c3c2743b4627135a0da7ecb726fc2cd` | `4af1254c35583d087fb9576541985589ee83e5b7c84f142564c1085807c16814` (9) |
| `demoTableB` | result 25 | none | `4693de141b6b7051881380c05be4ab0485f91be4ade1703c4995db055d6f9bfc` | `5aec7548b993a5b704c981ed8b5f155e8a8a7951c09f100c7d32354dc3926f05` (3) |
| `evenB` | result 25 | none | `3364c0ab7aeae735930b16d6adc0d62ddee2dc413f900badf8f352551c740731` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `twoThreeTableB` | result 25 | none | `6c282814a4f40fe8210c8d8efb12542bbe93115fd80bcaef9edae5248eba87bc` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `classify_witnessedOnUniv_without_check` | result 25 | Quot.sound, propext | `b1ff3d9d738c83207cfade250c7b5704ee56a03a33f44a70fbbe6a1475389998` | `337f3edd590ff5cdf8f174f49cebf88dc0f7f38cb95e26aef8a31c7ed3b795cf` (24) |
| `Shown` | result 27 | none | `cc9d16898c0f9a59074680a4114d5ef38f69c2b587d437120917db53df22e783` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `LedgerSummary` | result 27 | none | `cc9d16898c0f9a59074680a4114d5ef38f69c2b587d437120917db53df22e783` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `liftH` | result 27 | none | `3dd06673d5cac6c36013778f3d6dec351ecb4e4c3e87436a176925f6eb0eacac` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `allB` | result 27 | none | `516ff7d6080dfffae45b7c7d8c074310ffa631dc4241c67da5d763e306dcf729` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `othersB` | result 27 | none | `bfe85a83885f7ec4b7ee87da5466f968add4e34e36ceedef7cd2e0be0fffe3d1` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `SuffVerdict` | result 27 | none | `2e170f46208cf67a410be951c7dea584c13848b1ff4a8c15292abc505adf7877` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `TightVerdict` | result 27 | none | `cf72fb4753d088475681d5833c1f668c8f96a45c782ed56ddc82289692f2ba2b` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `VacVerdict` | result 27 | none | `f0013d9aaef916872c900951b408e9ca209d0eb7c182fbcf1733f28d8e5a8f15` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `WeakVerdict` | result 27 | none | `cf72fb4753d088475681d5833c1f668c8f96a45c782ed56ddc82289692f2ba2b` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `LedgerReport` | result 27 | none | `2e170f46208cf67a410be951c7dea584c13848b1ff4a8c15292abc505adf7877` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `auditSufficiency` | result 27 | Quot.sound, propext | `0f9f166aa2db80ba13ced658aaeaf78013b286f478c237e67bd5e1fce161d7b2` | `9f3dc08726c2dbb34973ce8611e1ca72faabe1a3bee036040fc5dfaea10a51dc` (4) |
| `auditTightness` | result 27 | Quot.sound, propext | `3cc88028f3f3fa1e4fc4e5c9a8b4d3d22b69fdf3abbe8d414987da6f6d76d640` | `46410a139a2b61428fba47bd3e088f72f986cfabd12198f906d24cc3ec43ccaf` (4) |
| `auditNonVacuity` | result 27 | Quot.sound, propext | `09a4ae02d2ae518472ada784f576b9acfe2fc74282a7770121d5e5c182152143` | `49c3d9dfc2b60daf0ef12915322b8511cbef8b04250b7c922d4526d8a8871c03` (4) |
| `auditWeakening` | result 27 | Quot.sound, propext | `47707e6d8142570d4961efac37c2f6028b50453ef1aa5d481baa8573cb18976a` | `f7486211c0c2a3db64af669d296c90e4ace121674559779fa257f22bebd4d7a8` (4) |
| `auditLedger` | result 27 | Quot.sound, propext | `27f50a1553946c71cc9380510cb05fe68927b1aa89c1c8ce9f1c8cb6c98cb66e` | `ab9bf6c90ffa67fc4245fa0ab7adc24389b1749ecef6825b79a54d136b6f9a89` (16) |
| `SuffVerdict.shown` | result 27 | none | `a70cd04afeb8b8a3f531ae51d871b10431ab13342fddc59bbe82e6b881483558` | `c0557990e0e7fc26f9e49bf7c7f85c8407f7a6ea2efb8eea0217f5edfaf89047` (7) |
| `TightVerdict.shown` | result 27 | none | `78f6ef4ca2213ae3beaa665919d18f7b5e2568f7b207a10b16f9c1d106fa49da` | `1c2b509c5e7599c35f119fce0337e84fce1b68d5b5508530a4b836994aa32c99` (7) |
| `VacVerdict.shown` | result 27 | none | `ad3e0af76ec82efe0014e908f96b453b2955dd86b13aca6652e53b367692c19d` | `4034fcf0626fa9039757d0ea2590bbf890580135b6cd96f36d639d933d982d81` (7) |
| `WeakVerdict.shown` | result 27 | none | `d4b2118b5192503154bb63201d6bf220076fdc8fb9ec5eba0b823a5be01614ac` | `212349f355dd8aacee43cffc06f3920cfc4ac77e7b70bcc80235efef016dca4d` (7) |
| `LedgerReport.summary` | result 27 | none | `ee96851f2507252a2068ee2ea1369cca5bccc0a7dfe4c65dbbe5ec202ad0a006` | `8cddaaa85ebe5ededf5ab8a11724215209237ed5af11086416e7835b26e36770` (21) |
| `pinHB` | result 27 | propext | `ded40ecffdce40df67497c76648dca4132fdd6cf7395015a60f0c9516c5061dd` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `pinCB` | result 27 | none | `3364c0ab7aeae735930b16d6adc0d62ddee2dc413f900badf8f352551c740731` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `sumHB` | result 27 | propext | `a1882e17fab6f8f45717ecd93cfbc4b37f5d4f7d930caa29b5a4515bdbc3a13b` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `sumCB` | result 27 | none | `d8b873f87ac9a32e77b5269ef450d868363bc31e59b807617db2bbf64ffafafa` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `grid3` | result 27 | none | `499ef3f4f76a45d965df62595fa8d000c60b5dccc9629970bc980fb2098e481b` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `dupHB` | result 27 | none | `ded40ecffdce40df67497c76648dca4132fdd6cf7395015a60f0c9516c5061dd` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `vacHB` | result 27 | propext | `4a382b9c58b7d57e4ad0b03e5d7bde9bcd9d2440ebee7ba701801bcfed43d1db` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `schemaHB` | result 27 | propext | `8ddc168e947d338c402ab1a08ac37ab7cb66757d07f2942758e62503e5abe6e5` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `bools2` | result 27 | none | `a1a08240497eec6f6cd61727fd410af87fc1a12886ac595a9ebc2de5bd0d1368` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `auditLedger_pin` | result 27 | Quot.sound, propext | `3c5286c978cada92c6ddee2930277bb84fdc40adab132b466f55ef5ed809a29f` | `8764834673afefd0e1eca3413f4b8fbfd0c1f492cc74575e5bf8b47935314b59` (59) |
| `auditLedger_sum` | result 27 | Quot.sound, propext | `be7ce4b666fa3f9a388af9028354a0057e6e8961a879c093625ef1a5b50492bd` | `b6ca19e6a1ce230b059d5c59cca2c3a941251ee75dc8468c973c6f3069944615` (60) |
| `auditLedger_dup` | result 27 | Quot.sound, propext | `c8ec70385805c3baf0c46f40c24c0189238cdf54074d293bfb3e1b9f7d23c038` | `223558b90b2c0822395219fb810d67fb7142bebc5b9180dbfc21bf33cb1ce39e` (58) |
| `auditLedger_vac` | result 27 | Quot.sound, propext | `c0d6eb7df19914a9effa9d233a168d6eb6ae67685c32f50639af11c78387dc09` | `e65f031e84b1b6e84ef7076360a3957db5682d871551e0d032292ccc066c70b1` (58) |
| `auditLedger_schema` | result 27 | Quot.sound, propext | `2352f9eecffb22b519688710c202747166efef91b02baacd8395175d8e9f0c87` | `af9a228c22f61c611f2b3aa0eb033e484b4046bcc62a1d9c3fac30c9051cb6ec` (59) |
| `auditLedger_false_theorem_tight_entry_reuses_counterexample` | result 27 | Quot.sound, propext | `fc4dc1f2fb63c9eab2469f01c8bfeca90c6e457b96a2377d5ba500759fe92d36` | `b17b01497dc64de585bebced471ded3b9c3f29ff427de3ec82a84fecb9168d04` (56) |
| `mem_grid3` | result 28 | Quot.sound, propext | `f7b6b74394dfc077193599e6069b72761df49317e12f6d11d0c2b9605759834f` | `52020dcf71f81c5e43bb29b863c0bd2369f1f9a45a507d2a40ae74e6f562423d` (1) |
| `mem_bools2` | result 28 | propext | `f416eafe765c8916ff629a858756721a97a7dd3f79a16cec4d45ef062878f6db` | `b2585e1f7f0ab0d15d8069a8249de47f0b43d3f56d9e19b2017ed3f617b48b27` (1) |

### Primary sources

Bibliographic identities (DOI → title, authors, venue, volume, pages) were checked against Crossref on 2026-11-21; GitHub commits were checked with the GitHub API; the arXiv record and the author's version of the FMCAD 2011 paper were opened. The quoted passages in the cards were read in the sources named there (full texts, abstracts, the authors' versions, or the files at the cited commits).

- D. Hilbert, *The Foundations of Geometry*, authorized translation by E. J. Townsend, Open Court, Chicago, 1902; Project Gutenberg eBook #17384, https://www.gutenberg.org/ebooks/17384. Chapter II, sections 10–12 (results 1, 5, 6).
- S. O. Hansson, "Kernel contraction", *Journal of Symbolic Logic* 59(3):845–859, 1994. doi:10.2307/2275912 (results 3, 13); alpha-kernels as restated in R. Wassermann, "Local Diagnosis", arXiv:cs/0003051, 2000, Definition 1.
- T. Eiter, G. Gottlob, "The complexity of logic-based abduction", *Journal of the ACM* 42(1):3–42, 1995. doi:10.1145/200836.200838 (result 12).
- M. H. Liffiton, K. A. Sakallah, "Algorithms for Computing Minimal Unsatisfiable Subsets of Constraints", *Journal of Automated Reasoning* 40(1):1–33, 2008 (online 2007). doi:10.1007/s10817-007-9084-z (results 3, 4, 12, 13).
- A. Ignatiev, N. Narodytska, J. Marques-Silva, "Abduction-Based Explanations for Machine Learning Models", *Proceedings of the AAAI Conference on Artificial Intelligence* 33(01):1511–1519, 2019. doi:10.1609/aaai.v33i01.33011511, Definition 1 (results 3, 4, 12).
- F. Lin, "On strongest necessary and weakest sufficient conditions", *Artificial Intelligence* 128(1–2):143–159, 2001. doi:10.1016/S0004-3702(01)00070-4 (results 10, 11).
- K. Su, A. Sattar, G. Lv, Y. Zhang, "Variable Forgetting in Reasoning about Knowledge", *Journal of Artificial Intelligence Research* 35:677–716, 2009. doi:10.1613/jair.2750, Definition 5 and Proposition 6 (results 10, 11).
- I. Beer, S. Ben-David, C. Eisner, Y. Rodeh, "Efficient Detection of Vacuity in Temporal Model Checking", *Formal Methods in System Design* 18(2):141–163, 2001. doi:10.1023/A:1008779610539; conference version "Efficient detection of vacuity in ACTL formulas", CAV 1997, LNCS 1254, pp. 279–290, doi:10.1007/3-540-63166-6_28 (results 14, 23–28).
- O. Kupferman, M. Y. Vardi, "Vacuity detection in temporal model checking", *International Journal on Software Tools for Technology Transfer* 4(2):224–233, 2003. doi:10.1007/s100090100062; earlier version CHARME 1999, LNCS 1703, pp. 82–98, doi:10.1007/3-540-48153-2_8 (results 14, 27, 28).
- D. L. Beatty, R. E. Bryant, "Formally verifying a microprocessor using a simulation methodology", *Proceedings of the 31st Design Automation Conference* (DAC 1994), pp. 596–602. doi:10.1145/196244.196575 (results 14, 23).
- H. R. Chamarthi, P. Manolios, "Automated Specification Analysis Using an Interactive Theorem Prover", *Proceedings of the International Conference on Formal Methods in Computer-Aided Design* (FMCAD 2011), FMCAD Inc., 2011, ISBN 978-0-9835678-1-3, pp. 46–53 (dblp record conf/fmcad/ChamarthiM11); author's version https://www.ccs.neu.edu/home/harshrc/pub/fmcad11.pdf, Section II (results 25–28).
- `leanprover/lean4` commit `5045d0056413266e57c625dcd7c365b10e377c52` (tag `v4.34.1`), `src/Lean/Linter/UnusedVariables.lean` (result 2).
- `leanprover-community/batteries` commit `4a314aed8362bd744e129ac93e4174b288811db6`, `Batteries/Tactic/Lint/Misc.lean` (`unusedArguments`) (result 2).
- `leanprover-community/mathlib4` commit `3eae40f5eb25c5934211edf662d3b24c5afbe47a`: `Mathlib/Order/Minimal.lean` lines 300 and 348, `Mathlib/Order/Antichain.lean` line 313 (results 3, 13), `Mathlib/Order/Heyting/Basic.lean` line 98 (result 10). Cited for comparison; this package does not use Mathlib.

Two of these sources have no DOI or other immutable identifier, and are recorded in `REPORT.json` with the strongest identity available. Hilbert's 1902 translation predates DOIs; it is identified by its Project Gutenberg eBook number, #17384, which identifies the eBook rather than a fixed revision of its files; no content hash is recorded for it. For the FMCAD 2011 paper dblp lists no DOI (for the paper or for its proceedings volume), and the top results of a Crossref bibliographic search for its title and authors did not include it; it is identified by its venue, pages, the proceedings ISBN and its dblp record. The quoted passage was read in the author's version at the URL above; no content hash of that file is recorded, so a later change of the file at that URL would not be detectable from this report.

## Revalidation

Requirements: `elan` (the Lean toolchain manager, so that `lake` uses the toolchain pinned in `lean/lean-toolchain`, `leanprover/lean4:v4.34.1`) and `python3`. The Lean project has no dependencies.

Primary check, run from the package directory:

```sh
python3 support/revalidate.py .
```

`support/revalidate.py` never modifies the package: it copies `lean/` to a temporary directory and there (1) runs `lake build`; (2) scans every Lean source for `sorry`, `admit`, `native_decide` and `axiom` declarations; (3) runs a generated Lean program that calls `Lean.collectAxioms` on every declaration of the library `Toy` and fails if any axiom other than `propext`, `Classical.choice`, `Quot.sound` occurs; and (4) for every Lean name referenced by `results.json` or recorded in `audit/statements.json`, recomputes the statement hash and the closure hash exactly as described under **Evidence** and compares them with `audit/statements.json`. It prints `REVALIDATED` and exits with status 0 exactly when all checks pass.

Manual spot check of axioms, from the package directory:

```sh
cd lean
lake build
cat > /tmp/LedgerAxiomCheck.lean <<'EOF'
import Toy
#print axioms Toy.Ledger.tightAt_iff_witness_violates_exactly_i_of_sufficient
#print axioms Toy.Ledger.weakestPremise_is_weakest_replacement
#print axioms Toy.Ledger.unweakenableAt_characterizations_of_sufficient
#print axioms Toy.Ledger.check_of_cell_empty
#print axioms Toy.Ledger.auditLedger_complete
EOF
lake env lean /tmp/LedgerAxiomCheck.lean
```

The output lists, per theorem, the axioms recorded in the table under **Evidence** (for `check_of_cell_empty`: none).

A passing run establishes that the recorded statements still build and kernel-check with the recorded axioms under the pinned toolchain. Under a different toolchain the statement hashes may change even when the mathematics does not (they hash Lean's `repr` of terms); in that case compare the statements in `lean/Toy/Ledger/` with the ones quoted under **Findings** by reading them. The modeling-bridge claims are not revalidated by any command.
