# Predicate-transformer healthiness laws and relational semantics (Lean 4, toy model)

## Summary

This package is a Lean 4 mechanization (core library only) of which healthiness laws on a predicate transformer `T : (σ → Prop) → (σ → Prop)` force it to be the weakest precondition of a relational program (a relation `R` between start and final states, possibly nondeterministic, together with a non-abortion predicate `term`), and of what the other classical laws (strictness, ω-continuity, monotonicity, refinement, program algebra) mean relationally. All eleven results below are kernel-checked; their axiom footprints are at most `propext`, `Classical.choice`, `Quot.sound` and are recorded per theorem under Evidence.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

- **Result 1 (`wlp-characterization`).** On any state type, a predicate transformer `T` distributes over the conjunction of every family of postconditions, including the empty family and infinite families (`ConjAll`), if and only if `T = wlp (relOf T)`, where `relOf T s s'` holds iff `s'` satisfies every postcondition `T` establishes from `s`; and `relOf (wlp R) = R`, so the representing relation is unique.
- **Result 2 (`wp-characterization`).** On any state type, `T` distributes over the conjunction of every nonempty family of postconditions (`ConjNonempty`) if and only if `T = wp (relOf T) (termOf T)` with `termOf T = T (fun _ => True)`; two relational programs have the same `wp` if and only if their non-abortion predicates are equal and their relations agree on non-aborting start states (so the relation is not unique outside the non-abortion predicate).
- **Result 3 (`strict-iff-no-miracle`).** `wp R term` satisfies the law of the excluded miracle if and only if every start state in `term` has at least one `R`-successor; the proof uses classical logic, which the statement implies.
- **Result 4 (`omega-continuity-iff-bounded-nondeterminism`).** On any state type (no countability assumption), `wp R term` is ω-continuous in the one-sided sense over increasing `Nat`-indexed chains if and only if every start state in `term` has a finite `R`-image (all successors lie in one list); the forward direction is proved with choice and the backward direction implies the limited principle of omniscience.
- **Result 5 (`finitary-laws-not-relational`).** On the infinite state type `Nat`, the transformer `eventually` ("the postcondition holds of all but finitely many numbers") is monotone, binary conjunctive, top preserving and strict, yet it is not ω-continuous, not positively conjunctive, and neither `wlp R` nor `wp R term` for any `R` and `term`.
- **Result 6 (`refinement-correspondence`).** `wp R₁ t₁` is refined by `wp R₂ t₂` (pointwise implication) if and only if `t₁` is included in `t₂` and every `R₂`-outcome of a start state in `t₁` is an `R₁`-outcome, with no normal form assumed; if `(R₁, t₁)` is in chaos normal form the second condition may be replaced by global inclusion of `R₂` in `R₁` (this form needs classical logic).
- **Result 7 (`wp-algebra`).** The `wp` of a relational composition with non-abortion predicate `seqTerm R₁ t₁ t₂` (the first program does not abort and the second does not abort from any reachable intermediate state) is the composition of the `wp`s; the `wp` of a union of relations with the conjunction of the non-abortion predicates is the pointwise conjunction of the `wp`s; likewise for `wlp`.
- **Result 8 (`monotone-angelic-demonic-normal-form`).** A transformer is monotone if and only if it equals the angelic choice of demonic updates given by its own multirelation (`T = angelicDemonic (multirelOf T)`), and `multirelOf (angelicDemonic A) = A` if and only if `A` is up-closed; this is near-definitional and carries no information beyond monotonicity.
- **Result 9a (`finite-state-binary-conjunctivity-suffices`).** On a finite state type, every binary conjunctive transformer is conjunctive over all nonempty families (classical logic is used, and the statement implies it).
- **Result 9b (`continuum-state-continuity-forces-conjunctivity`).** On a state type that injects into `Nat → Bool` (every countable type, and the uncountable `Nat → Bool` itself), every binary conjunctive and ω-continuous transformer is conjunctive over all nonempty families; whether the hypothesis on the state type can be dropped is unknown.
- **Result 9c (`directed-continuity-forces-conjunctivity`).** On every state type, every binary conjunctive transformer that is continuous over nonempty directed families is conjunctive over all nonempty families.

Every result has non-claims that rule out tempting stronger readings; they are listed first under **Boundaries**, per result. Each result's hypothesis ledger under **Findings** states which hypotheses are necessary (with a Lean counterexample), harmless, or of unknown necessity. Everything here is about a toy model with one state type and extensional predicates; nothing is claimed about a particular verification framework until its own definitions are checked against these (see **Applicability**).

Design question informed: *which laws must a verification framework demand of a weakest-precondition transformer so that every admitted transformer is the `wp` of some relational (possibly nondeterministic, possibly aborting) program, without excluding honest programs?* Answer within this model: demand conjunctivity over all nonempty families (result 2); adding the empty family gives exactly the `wlp`s (result 1). Monotonicity, binary conjunctivity, strictness and top preservation together are not enough on an infinite state type (result 5). Strictness excludes exactly the miracles (result 3) and ω-continuity excludes exactly unbounded nondeterminism on non-aborting states (result 4); both are optional laws. Binary conjunctivity does suffice on a finite state type (result 9a), together with ω-continuity on state types that inject into `Nat → Bool` (result 9b), and together with continuity over directed families on every state type (result 9c). Monotonicity alone characterizes the larger class of angelic/demonic choices (result 8).

## Applicability

### Model fidelity

This is a **toy model**, not a mirror of any production verification framework. It is meant to capture the weakest-precondition semantics used by Dijkstra-style program calculi, the refinement calculus, and verification frameworks that assign each program a transformer on postconditions: a program is modeled by a relation `R : σ → σ → Prop` (possible final states) and a predicate `term : σ → Prop` (start states from which it does not abort), with `wp R term Q s = term s ∧ ∀ s', R s s' → Q s'`. `wlp R` has two readings, both covered: the partial-correctness weakest liberal precondition of `R`, and the total-correctness demonic update `[R] = wp R (fun _ => True)` of a never-aborting program.

Known gaps between the model and real systems:

- One state type for both initial and final states; relations from states to states; a single postcondition. No return values, exceptional exits, heaps, step counting, loops, recursion or fixed points.
- `term` is coarse: "not in `term`" covers abortion, certain divergence and possible divergence alike, and `term` includes miraculous states (no successor). A paired `(wp, wlp)` semantics of a possibly aborting program is not modeled.
- Predicates and transformers are compared extensionally (`propext`, `funext`); no computational content is claimed, and "relational" says nothing about computability or expressibility in a programming language.
- `OmegaContinuous` and `DirContinuous` are one-sided (upper) continuity laws; on their own they do not imply monotonicity.
- Universe: `σ : Type u` is universe-polymorphic; index families in `ConjAll`, `ConjNonempty` and `DirContinuous` range over `Type u`, which loses nothing (`conjAll_iff_set`, `conjNonempty_iff_set`, `conjAll_arbitrary_sort`, `conjNonempty_arbitrary_sort`).

Any claim about a real framework is a separate modeling-bridge claim, labeled `derived (modeling bridge)` under Findings, and is not established by the kernel check.

### Toolchain and project

- Lean `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`), core library only: no Mathlib, no `Std` import, no `[[require]]` dependencies.
- Lake project `lean/` (`lakefile.toml`, package `toy_predtrans`, one `[[lean_lib]]` `ToyPredTrans`), namespace `Toy.PredTrans`, modules `Defs` (definitions), `Basic` (implications between laws; laws of `wlp`/`wp`), `Programs` (example programs; positive and negative examples for every definition), `Witnesses` (tightness counterexamples, non-vacuity theorems, positive controls, logical-strength witnesses), `Algebra`, `MonotoneNormalForm`, `SmallStateSpaces`, `Main` (results 1-4 and the first statement of result 6), `Corollaries`. No counterexample, non-vacuity theorem or positive control imports `Main`.

### Subjects and their relationship

`REPORT.json` lists the Lean toolchain release, which kernel-checked every theorem here, and the primary sources of the known results restated (papers, two Archive of Formal Proofs entries, a Coq development, and a Mathlib file at pinned revisions). The sources are prior art only: the Lean project does not import or mirror any of them, and the correspondence between a source's statement and a Lean theorem here is stated per card under **Prior art**, with the extent to which the source was read. One toolchain source file (`src/Std/Do/PredTrans.lean`) was examined for the modeling-bridge remark only.

## Findings

### Setting and definitions

Basis: execution (Lean kernel check) for every named positive and negative example; the "meant to capture" column is the intended reading, not a kernel-checked claim.

`σ : Type u` is the type of states. All definitions are in `ToyPredTrans/Defs.lean`.

```lean
abbrev Pred  (σ : Type u) : Type u := σ → Prop               -- state predicates
abbrev Transformer (σ : Type u) : Type u := Pred σ → Pred σ   -- predicate transformers
abbrev Rel   (σ : Type u) : Type u := σ → σ → Prop            -- R s s' : s' is a possible final state from s
```

Predicates are compared extensionally (`propext`, `funext`): a transformer is a function, so it
automatically respects logical equivalence of postconditions. No congruence law is stated.

#### Semantics

| Definition | Lean | Meant to capture | Positive example (proved) | Negative example (proved) |
|---|---|---|---|---|
| `wlp R` | `fun Q s => ∀ s', R s s' → Q s'` | two readings, both covered: the partial-correctness weakest liberal precondition of `R` (a state without successors models guaranteed divergence), and the total-correctness demonic update `[R] = wp R True` of a never-aborting program (a state without successors is a miracle) | `wlp_skipR`, `wlp_stepR_pos` | `not_wlp_stepR_eq_one` |
| `wp R term` | `fun Q s => term s ∧ wlp R Q s` | total-correctness weakest precondition of the program with outcome relation `R` and *non-abortion domain* `term`; `term s` does not by itself promise a final state (at a state in `term` without successors the program is miraculous) | `wp_predR_example` | `not_wp_predR_zero` (contrast `wlp_predR_zero`) |

In the notation of the refinement calculus, `wlp R` is the demonic update `[R]` and `wp R term`
is the assertion followed by the demonic update, `{term} ; [R]`. A paired `(wp, wlp)` semantics
of a possibly aborting program is not modeled.

#### Laws (each a separate `Prop`)

| Law | Lean (unfolded) | Positive example | Negative example |
|---|---|---|---|
| `Monotone T` | `∀ P Q, (∀ t, P t → Q t) → ∀ s, T P s → T Q s` | `monotone_wp`, `monotone_angelic` | `not_monotone_negT` |
| `ConjAll T` | `∀ (ι : Type u) (Q : ι → Pred σ) (s : σ), T (fun t => ∀ i, Q i t) s ↔ ∀ i, T (Q i) s` | `conjAll_wlp` | `not_conjAll_abortT`, `not_conjAll_eventually` |
| `ConjNonempty T` | `∀ (ι : Type u) (Q : ι → Pred σ), Nonempty ι → ∀ s, T (fun t => ∀ i, Q i t) s ↔ ∀ i, T (Q i) s` | `conjNonempty_wp`, `conjNonempty_abortT` | `not_conjNonempty_eventually`, `not_conjNonempty_angelic` |
| `ConjBin T` | `∀ P Q s, T (fun t => P t ∧ Q t) s ↔ T P s ∧ T Q s` (binary, i.e. nonempty finite, conjunctivity) | `conjBin_wp`, `conjBin_eventually` | `not_conjBin_angelic` |
| `Strict T` | `∀ s, ¬ T (fun _ => False) s` | `strict_wp_skipR`, `strict_eventually` | `not_strict_wlp_emptyR` |
| `TopPreserving T` | `∀ s, T (fun _ => True) s` | `topPreserving_wlp`, `topPreserving_eventually` | `not_topPreserving_abortT` |
| `Chain Q` | `∀ n s, Q n s → Q (n + 1) s` (for `Q : Nat → Pred σ`) | `chain_le` | `not_chain_eq` |
| `OmegaContinuous T` | `∀ Q : Nat → Pred σ, Chain Q → ∀ s, T (fun t => ∃ n, Q n t) s → ∃ n, T (Q n) s` (one-sided) | `omegaContinuous_wp_skipR`, `omegaContinuous_wlp_stepR`, `omegaContinuous_wp_emptyR` | `not_omegaContinuous_wlp_havocR_nat`, `not_omegaContinuous_eventually` |
| `Directed Q` | `Nonempty ι ∧ ∀ i j, ∃ k, (∀ s, Q i s → Q k s) ∧ (∀ s, Q j s → Q k s)` (for `Q : ι → Pred σ`, `ι : Type u`) | `directed_le` | `not_directed_eq`, `not_directed_empty` |
| `DirContinuous T` | `∀ (ι : Type u) (Q : ι → Pred σ), Directed Q → ∀ s, T (fun t => ∃ i, Q i t) s → ∃ i, T (Q i) s` (one-sided) | `dirContinuous_wp_skipR`, `dirContinuous_angelic` | `not_dirContinuous_eventually`, `not_dirContinuous_wlp_havocR_nat` |

Remarks on the forms chosen (all proved in `Basic` unless noted):

- The laws are stated pointwise; `strict_iff_eq`, `topPreserving_iff_eq`, `conjBin_iff_eq`,
  `conjAll_iff_eq` show each is equivalent to the familiar equation between predicates.
- `ConjAll` and `ConjNonempty` quantify over index types in the universe of the state type. This
  loses nothing: `conjAll_iff_set` and `conjNonempty_iff_set` show they are equivalent to
  distributing over the intersection of an arbitrary (nonempty) *set* of predicates, and
  `conjAll_arbitrary_sort`, `conjNonempty_arbitrary_sort` give conjunctivity over families indexed
  by any `Sort`.
- `ConjBin` gives conjunctivity over every *nonempty* finite list; the empty list needs
  `TopPreserving` as well (`conjList_of_conjBin_of_topPreserving`).
- **`OmegaContinuous` and `DirContinuous` are one-sided.** They are only the upper half of the usual
  continuity equation `T (⋃ₙ Qₙ) = ⋃ₙ T Qₙ`. `omegaContinuous_two_sided_iff` shows the two-sided
  equation over chains is equivalent to `Monotone T ∧ OmegaContinuous T`. On their own, the
  one-sided laws do **not** imply monotonicity: pointwise negation satisfies both
  (`omegaContinuous_negT_not_monotone`, `dirContinuous_negT`). Every result of this package pairs
  them with a law that implies monotonicity (`ConjBin`, or being a `wp`), where the one-sided and
  two-sided forms coincide. `DirContinuous` implies `OmegaContinuous`
  (`omegaContinuous_of_dirContinuous`). The restriction to chains matters:
  `not_continuous_on_arbitrary_families_stepR_canonical`.
- Derivable laws, never listed as separate hypotheses:
  `ConjAll → ConjNonempty` (`conjNonempty_of_conjAll`), `ConjNonempty → ConjBin`
  (`conjBin_of_conjNonempty`), `ConjBin → Monotone` (`monotone_of_conjBin`),
  `ConjAll ↔ ConjNonempty ∧ TopPreserving` (`conjAll_iff_conjNonempty_and_topPreserving`),
  `ConjBin ∧ TopPreserving →` conjunctivity over every finite list.

#### From transformers back to relations

| Definition | Lean | Meant to capture | Positive | Negative |
|---|---|---|---|---|
| `relOf T` | `fun s s' => ∀ Q, T Q s → Q s'` | `s'` is a possible outcome from `s`: `s'` satisfies every postcondition `T` establishes from `s` (the intersection of the established postconditions). For monotone `T` this agrees, classically, with "`T` cannot guarantee from `s` that the final state differs from `s'`" (`relOf_iff_not_avoids_of_monotone`) | `relOf_wlp_skipR` | `wlp_relOf_eventually_ne` (with `relOf_eventually`) |
| `termOf T` | `T (fun _ => True)` | the non-abortion domain; for `wp R term` it is `term` (`termOf_wp`); it includes miraculous states (`termOf_wlp_emptyR_no_outcome`) | `termOf_wp`, `termOf_wp_predR_one` | `not_termOf_wp_predR_zero` |

#### Properties of relational programs and of state types

| Definition | Lean | Meant to capture | Positive | Negative |
|---|---|---|---|---|
| `FiniteImage R s` | `∃ l : List σ, ∀ s', R s s' → s' ∈ l` | bounded nondeterminism at `s` (finitely many final states; not the branching of an operational semantics) | `finiteImage_stepR`, `finiteImage_skipR`, `finiteImage_emptyR` | `not_finiteImage_havocR_nat` |
| `TotalOn R term` | `∀ s, term s → ∃ s', R s s'` | no miracle: every non-aborting start state has an outcome | `totalOn_predR_posP` | `not_totalOn_predR_true` |
| `ChaosNormal R term` | `∀ s, ¬ term s → ∀ s', R s s'` | normal form: an aborting start state is related to every state | `chaosNormal_of_forall_term`, `chaosNormal_havocR`, `chaosNormal_chaos` | `not_chaosNormal_predR_posP` |
| `RefinedBy T₁ T₂` | `∀ Q s, T₁ Q s → T₂ Q s` | `T₁ ⊑ T₂`: `T₂` offers every guarantee `T₁` offers (total-correctness refinement order) | `abortT_refinedBy`, `refinedBy_havocR_stepR` | `not_refinedBy_stepR_havocR` |
| `CountableState σ` | `∃ f : σ → Nat, ∀ x y, f x = f y → x = y` | the state type is countable (finite and empty included) | `countableState_nat`, `countableState_bool` | `not_countableState_nat_to_bool` |
| `ContinuumState σ` | `∃ f : σ → Nat → Bool, ∀ x y, f x = f y → x = y` | the state type has at most the cardinality of the continuum; every countable type qualifies (`continuumState_of_countableState`) | `continuumState_nat_to_bool`, `continuumState_nat` | `not_continuumState_pred_nat_to_bool` |
| `FiniteState σ` | `∃ l : List σ, ∀ x, x ∈ l` | the state type is finite (empty included) | `finiteState_bool` | `not_finiteState_nat` |

#### Program algebra and multirelations

| Definition | Lean | Meant to capture | Positive | Negative |
|---|---|---|---|---|
| `comp R₁ R₂` | `fun s s'' => ∃ s', R₁ s s' ∧ R₂ s' s''` | sequential composition of relations | `comp_stepR_example` | `not_comp_stepR_example` |
| `seqTerm R₁ t₁ t₂` | `fun s => t₁ s ∧ ∀ s', R₁ s s' → t₂ s'` | non-abortion domain of a sequential composition; definitionally `wp R₁ t₁ t₂` (`seqTerm_eq_wp`) | `seqTerm_example` | `not_seqTerm_example` |
| `union R₁ R₂` | `fun s s' => R₁ s s' ∨ R₂ s s'` | demonic choice | `union_example` | `not_union_example` |
| `angelicDemonic A` | `fun Q s => ∃ P, A s P ∧ ∀ t, P t → Q t` (for `A : σ → Pred σ → Prop`) | angel picks an available set, demon picks a state in it | `wp_eq_angelicDemonic`, `eventually_eq_angelicDemonic`, `angelic_eq_angelicDemonic` | `negT_ne_angelicDemonic` |
| `multirelOf T` | `fun s P => T P s` | the multirelation of a transformer | `multirelOf_wlp_skipR` | `not_multirelOf_wlp_skipR_example` |
| `UpClosed A` | `∀ s P P', A s P → (∀ t, P t → P' t) → A s P'` | supersets of available sets are available | `upClosed_contains` | `not_upClosed_singleton` |

#### Example programs and transformers (`Programs`, `Witnesses`)

```lean
def skipR  : Rel σ   := fun s s' => s' = s                       -- skip
def havocR : Rel σ   := fun _ _ => True                           -- any final state
def emptyR : Rel σ   := fun _ _ => False                          -- no final state: magic as a demonic update,
                                                                  -- guaranteed divergence under partial correctness
def stepR  : Rel Nat := fun s s' => s' = s + 1 ∨ s' = s + 2       -- add one or two
def predR  : Rel Nat := fun s s' => s = s' + 1                    -- decrement; 0 has no successor
def posP   : Pred Nat := fun s => s ≠ 0
def zeroHavocR : Rel Nat := fun s s' => s = 0 ∨ s' = s            -- anything at 0, skip elsewhere
def abortT : Transformer σ := fun _ _ => False                          -- = wp R (fun _ => False)
def eventually : Transformer Nat := fun Q _ => ∃ N, ∀ n, N ≤ n → Q n    -- Q holds of all but finitely many n
def fromN (N : Nat) : Transformer Nat := fun Q _ => ∀ n, N ≤ n → Q n    -- = wlp (fun _ s' => N ≤ s')
def angelic : Transformer σ := fun Q _ => ∃ x, Q x                      -- angelic havoc
def negT : Transformer σ := fun Q s => ¬ Q s                            -- negation
def constT (P : Pred σ) : Transformer σ := fun _ s => P s               -- = wp emptyR P
def orT (B : Prop) : Transformer Unit := fun Q _ => Q () ∨ B            -- used by the logical-strength witnesses
```

### How classical logic appears in the hypothesis ledgers

Lean's logic includes excluded middle and the axiom of choice. So the necessity of classical reasoning for a statement cannot be shown by a Lean countermodel: any Lean proof that the statement fails while its other hypotheses hold would be a proof of `False`. Where a ledger below marks **classical logic** (or a non-constructive principle) as `tight`, the cited witness is instead a theorem of the form *"the statement, restricted to the one-point state type `Unit`, implies excluded middle `∀ P : Prop, P ∨ ¬ P`"* (or the limited principle of omniscience, LPO: every `f : Nat → Bool` either takes the value `true` somewhere or is `false` everywhere), proved **without** `Classical.choice`. In plain words: in any constructive setting where excluded middle (or LPO) fails, the statement fails too, because the parametric family used in the witness (for example `orT B := fun Q _ => Q () ∨ B` with an undecided proposition `B`) satisfies the other hypotheses there. `#print axioms` reports no axiom at all for each such witness except `lem_of_chaosNormal_unique_of_wp_eq`, which uses only `propext` and `Quot.sound`. Where a ledger marks classical logic `harmless`, the statement is proved here without `Classical.choice`, and `audit/axioms.json` records that footprint.

Depth labels: *definitional* = unfolding plus a quantifier exchange; *shallow* = a short direct argument with one idea; *substantive* = needs a construction and a multi-step argument (here: textbook level, tens to a few hundred lines).

### Result cards

#### Result 1 — `wlp-characterization`

- **Lean:** `conjAll_iff_eq_wlp_relOf`, `relOf_wlp` (namespace `Toy.PredTrans`).
- **Kind:** characterization. **Tier:** T0 — The correspondence between universally conjunctive predicate transformers and relations (demonic updates) is textbook material and is mechanized in Isabelle/HOL (Struth 2018); restated here with the inverse map relOf exposed.

Statement, as printed by `#check` on the built library:

```lean
@conjAll_iff_eq_wlp_relOf : ∀ {σ : Type u_1} (T : Transformer σ), ConjAll T ↔ T = wlp (relOf T)
@relOf_wlp : ∀ {σ : Type u_1} (R : Rel σ), relOf (wlp R) = R
```

Unfolded (`ConjAll`, `wlp`, `relOf`):

```lean
(∀ (ι : Type u) (Q : ι → σ → Prop) (s : σ), T (fun t => ∀ i, Q i t) s ↔ ∀ i, T (Q i) s)
  ↔ T = fun Q s => ∀ s', (∀ P, T P s → P s') → Q s'

(fun s s' => ∀ Q, (∀ t, R s t → Q t) → Q s') = R
```

**Plain claim.** For any state type, a predicate transformer T distributes over the conjunction of every family of postconditions - including the empty family and infinite families - if and only if T = wlp (relOf T), where relOf T s s' holds iff s' satisfies every postcondition that T establishes from s; and relOf (wlp R) = R, so the representing relation is unique.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| the empty family is included in ConjAll | forces T True = True, which every wlp satisfies; without it the class is that of the wp characterization. The witnesses are positively conjunctive and not the wlp of any relation. | tight: counterexample `abortT_conjNonempty_not_wlp`, `wp_predR_posP_conjNonempty_not_wlp` |
| infinite families are included in ConjAll | finite conjunctivity (binary conjunctivity plus top preservation) admits transformers that are not the wlp of any relation | tight: counterexample `eventually_finitary_laws_not_relational` |
| index types range over the universe of the state type | keeps ConjAll a statement about one universe; it loses nothing, since it is equivalent to distributing over arbitrary sets of predicates (conjAll_iff_set) and gives conjunctivity over families indexed by any Sort (conjAll_arbitrary_sort) | harmless |
| extensional equality of transformers | T = wlp R is equality of functions, obtained from propext and funext | harmless |
| classical logic | not needed: with relOf defined as the intersection of the established postconditions, both statements are proved from propext and Quot.sound alone, without Classical.choice: audit/axioms.json records exactly [Quot.sound, propext] for conjAll_iff_eq_wlp_relOf and for relOf_wlp. The negated reading of relOf (not T (fun t => t != s') s) agrees with relOf only for monotone transformers and only classically (relOf_iff_not_avoids_of_monotone). | harmless |

**Depth.** shallow.

**Non-vacuity witness.** ConjAll (wlp stepR) holds for the two-way choice on Nat and ConjAll eventually fails, so both sides of the equivalence occur; relOf_wlp_skipR is a concrete instance of the inverse equation. (`conjAll_wlp_stepR_and_not_conjAll_eventually`, `relOf_wlp_skipR`)

**Companions and corollaries (proved in the package).** `wlp_injective`, `conjAll_iff_exists_unique_wlp`, `conjAll_iff_set`, `conjAll_arbitrary_sort`, `relOf_iff_not_avoids_of_monotone`.

**Prior art.**

- R.-J. Back and J. von Wright, 'Refinement Calculus: A Systematic Introduction', Springer, 1998, doi:10.1007/978-1-4612-1674-2 (located only: table of contents and chapter abstracts; section 26.1 'Universally Conjunctive Predicate Transformers'; theorem statements and numbers not seen at the source)
- E. Sekerinski and T. Zhang, 'A Normal Form for Multi-Exit Statements', author-hosted manuscript dated December 2011, https://www.cas.mcmaster.ca/~emil/pubs/SekerinskiZhang11NormalFormMultiExit.pdf (URL resolved on 2026-11-20; SHA-256 of the PDF file not recorded) (blank 'Submitted to' line; it cites a 2013 paper of the same authors, so the text was revised after 2013; venue not verified) (content seen: Theorem 15 - 'Let S be an universally conjunctive indexed predicate transformer. There exists a unique indexed relation R such that S = [R]' - a generalization to indexed transformers)
- G. Struth, 'Transformer Semantics', Archive of Formal Proofs, 11 December 2018, https://isa-afp.org/entries/Transformer_Semantics.html; theory Kleisli_Transformers.thy as mirrored in isabelle-prover/mirror-afp-devel at commit 523cdc72b5ae4a91c9ab8e1025d4a30b40472720 (content seen: lemmas rfb_Inf_pres (Inf-preserving forward boxes), rfb_surj (every Inf-preserving transformer is a forward box of a relation) and rfb_inj (the map is injective); partial correctness only)
- Mathlib (leanprover-community/mathlib4, commit 5f78f9ce46fc85fa3cb45561d47b489c4c98cd04), file Mathlib/Basic/Rel.lean (content seen: SetRel.core, the relational wlp, with core_inter, core_univ, core_id, core_comp; no converse)
- B. Jonsson and A. Tarski, 'Boolean Algebras with Operators. Part I', American Journal of Mathematics 73(4):891-939, 1951, doi:10.2307/2372123, and 'Boolean Algebras with Operators' [Part II], American Journal of Mathematics 74(1):127-162, 1952, doi:10.2307/2372074; P. Blackburn, M. de Rijke, Y. Venema, 'Modal Logic', Cambridge University Press, 2001, doi:10.1017/CBO9781107050884 (bibliographic records verified; cited for the lineage in algebraic modal logic, where completely multiplicative operators on a powerset algebra correspond to Kripke relations; the specific passages were not read)
- No Lean 4 formalization of the converse direction was found (best-effort search; absence not established). For the positively conjunctive case in a return-value setting see Maillard et al. 2019 on the wp-characterization card.

**Design question informed.** Which laws must a verification framework demand of a weakest-precondition transformer so that every admitted transformer is the wp of some relational (possibly nondeterministic, possibly aborting) program, without excluding honest programs? Answer for partial correctness (or for never-aborting programs under total correctness): demand conjunctivity over arbitrary families, not the binary law.

**Non-claims:** see Boundaries, result 1.

**Scope witnesses cited in the non-claims (proved in the package; statements printed under Evidence).** `not_disjBin_wlp_stepR`.

Basis: execution (Lean kernel check) — `conjAll_iff_eq_wlp_relOf` (axioms: `Quot.sound`, `propext`); `relOf_wlp` (axioms: `Quot.sound`, `propext`).

#### Result 2 — `wp-characterization`

- **Lean:** `conjNonempty_iff_eq_wp_relOf_termOf`, `relOf_wp`, `wp_eq_wp_iff` (namespace `Toy.PredTrans`).
- **Kind:** characterization. **Tier:** T0 — The normal form 'assertion followed by demonic update' of positively conjunctive predicate transformers is textbook material (and appears as a Galois-connection statement in Maillard et al. 2019); the exact uniqueness statement and the explicit chaos normal form are spelled out here.

Statement, as printed by `#check` on the built library:

```lean
@conjNonempty_iff_eq_wp_relOf_termOf : ∀ {σ : Type u_1} (T : Transformer σ),
  ConjNonempty T ↔ T = wp (relOf T) (termOf T)
@relOf_wp : ∀ {σ : Type u_1} (R : Rel σ) (term : Pred σ), relOf (wp R term) = fun s s' => term s → R s s'
@wp_eq_wp_iff : ∀ {σ : Type u_1} (R R' : Rel σ) (term term' : Pred σ),
  wp R term = wp R' term' ↔ term = term' ∧ ∀ (s : σ), term s → ∀ (s' : σ), R s s' ↔ R' s s'
```

Unfolded (`ConjNonempty`, `wp`, `wlp`, `relOf`, `termOf`):

```lean
(∀ (ι : Type u) (Q : ι → σ → Prop), Nonempty ι →
    ∀ s, T (fun t => ∀ i, Q i t) s ↔ ∀ i, T (Q i) s)
  ↔ T = fun Q s => T (fun _ => True) s ∧ ∀ s', (∀ P, T P s → P s') → Q s'

(fun s s' => ∀ Q, (term s ∧ ∀ t, R s t → Q t) → Q s') = fun s s' => term s → R s s'

(fun Q s => term s ∧ ∀ s', R s s' → Q s') = (fun Q s => term' s ∧ ∀ s', R' s s' → Q s')
  ↔ term = term' ∧ ∀ s, term s → ∀ s', (R s s' ↔ R' s s')
```

**Plain claim.** For any state type, a predicate transformer T distributes over the conjunction of every nonempty family of postconditions if and only if T = wp (relOf T) (termOf T), where termOf T = T True and relOf T s s' holds iff s' satisfies every postcondition T establishes from s; two relational programs have the same wp if and only if their non-abortion predicates are equal and their relations agree on non-aborting start states; and relOf (wp R term) is R made chaotic outside term.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| infinite nonempty families are included in ConjNonempty | binary conjunctivity admits transformers that are not the wp of any relational program | tight: counterexample `eventually_finitary_laws_not_relational` |
| conjunctivity rather than monotonicity | angelic choice is monotone, strict, top preserving and omega-continuous but not a wp; a non-monotone transformer is not a wp either | tight: counterexample `angelic_laws_not_wp`, `negT_not_monotone_not_wp` |
| uniqueness of the relation only on non-aborting start states (wp_eq_wp_iff) | wp R term ignores R outside term, so R is not determined there: two different relations have the same wp | tight: counterexample `wp_same_with_different_relations` |
| index types range over the universe of the state type | keeps ConjNonempty a statement about one universe; it loses nothing, since it is equivalent to distributing over arbitrary nonempty sets of predicates (conjNonempty_iff_set) and gives conjunctivity over nonempty families indexed by any Sort (conjNonempty_arbitrary_sort) | harmless |
| extensional equality of transformers | T = wp R term is equality of functions, obtained from propext and funext | harmless |
| classical logic (the three main statements) | not needed: all three statements are proved from propext and Quot.sound alone, without Classical.choice: audit/axioms.json records exactly [Quot.sound, propext] for conjNonempty_iff_eq_wp_relOf_termOf, relOf_wp and wp_eq_wp_iff | harmless |
| classical logic (chaos-normal-form corollaries relOf_wp_of_chaosNormal and chaosNormal_unique_of_wp_eq) | needed: each corollary, restricted to the one-point state type, implies excluded middle, by proofs that use no axiom beyond propext and Quot.sound (no choice). Lean's logic is classical, so no countermodel can be exhibited inside Lean; this reverse implication is the witness. | tight (logical-strength witness): `lem_of_relOf_wp_of_chaosNormal`, `lem_of_chaosNormal_unique_of_wp_eq` |

**Depth.** shallow.

**Non-vacuity witness.** ConjNonempty (wp predR posP) holds for the partial decrement on Nat and ConjNonempty eventually fails, so both sides of the equivalence occur; wp_same_with_different_relations exhibits two different relations satisfying both sides of wp_eq_wp_iff. (`conjNonempty_wp_predR_posP_and_not_conjNonempty_eventually`, `wp_same_with_different_relations`)

**Companions and corollaries (proved in the package).** `conjNonempty_iff_exists_wp`, `relOf_wp_of_chaosNormal`, `chaosNormal_unique_of_wp_eq`, `conjNonempty_iff_exists_unique_chaosNormal_wp`, `conjNonempty_iff_set`, `conjNonempty_arbitrary_sort`, `chaosNormal_relOf_termOf_of_monotone`, `termOf_wp`, `wp_chaos_eq`, `wp_restrict_eq`.

**Prior art.**

- R.-J. Back and J. von Wright, 'Refinement Calculus: A Systematic Introduction', Springer, 1998, doi:10.1007/978-1-4612-1674-2 (located only: table of contents and chapter abstracts; section 26.2 'Conjunctive Predicate Transformers'; theorem statements and numbers not seen at the source)
- E. Sekerinski and T. Zhang, 'A Normal Form for Multi-Exit Statements', author-hosted manuscript dated December 2011, https://www.cas.mcmaster.ca/~emil/pubs/SekerinskiZhang11NormalFormMultiExit.pdf (URL resolved on 2026-11-20; SHA-256 of the PDF file not recorded) (blank 'Submitted to' line; it cites a 2013 paper of the same authors, so the text was revised after 2013; venue not verified) (content seen: Theorem 17 - 'Let S be an arbitrary positively conjunctive predicate transformer. Then there exists a unique predicate p and a unique indexed relation R such that S = {p};[R]'. Caveat: the uniqueness of R is asserted without a normalization condition and is false as stated in the setting of this package (wp_same_with_different_relations); the proof given there establishes p = tr S and the existence of R via Theorem 15, and contains no argument for the uniqueness of R. The manuscript reports that its results were checked in Isabelle/HOL; that formalization was not inspected.)
- K. Maillard, D. Ahman, R. Atkey, G. Martinez, C. Hritcu, E. Rivas, E. Tanter, 'Dijkstra monads for all', Proceedings of the ACM on Programming Languages 3(ICFP), article 104, 2019, doi:10.1145/3341708 (preprint arXiv:1903.01237) (content seen in the preprint, section 4.1: PrePost A = P x (A -> P); the maps (pre, post) |-> (fun p => pre /\ forall a, post a -> p a) and w |-> (w (fun a => True), fun a => forall p, w p -> p a) form a Galois connection that 'exhibits PrePost A as the submonad of W^Pure A of conjunctive predicate transformers, i.e., predicate transformers w commuting with non-empty conjunctions/intersections'. Their second component is the relOf of this package. The setting is a precondition plus a postcondition on a return value, not a state-to-state relation. Section 5 reports a Coq implementation of the specification monads of section 4.1; the Coq files were not inspected.)
- P. Guerreiro, 'Another characterization of weakest preconditions', in International Symposium on Programming, LNCS 137, Springer, 1982, pp. 164-177, doi:10.1007/3-540-11494-7_12 (content seen: abstract - relational model with explicit non-termination; healthiness properties characterized by properties of the relations)
- V. Preoteasa, 'Formalization of Refinement Calculus for Reactive Systems', Archive of Formal Proofs, 8 October 2014, https://isa-afp.org/entries/RefinementReactive.html; theory Refinement.thy as mirrored in isabelle-prover/mirror-afp-devel at commit 523cdc72b5ae4a91c9ab8e1025d4a30b40472720 (content seen: definitions conjunctive (all sets) and sconjunctive (nonempty sets); demonic update conjunctive, assertion sconjunctive; the converse representation theorem was not found there)

**Design question informed.** Which laws must a verification framework demand of a weakest-precondition transformer so that every admitted transformer is the wp of some relational (possibly nondeterministic, possibly aborting) program, without excluding honest programs? Answer for total correctness: demand conjunctivity over all nonempty families.

**Non-claims:** see Boundaries, result 2.

**Scope witnesses cited in the non-claims (proved in the package; statements printed under Evidence).** `termOf_wlp_emptyR_no_outcome`, `constT_conjNonempty_not_strict_not_topPreserving`, `havocR_nat_conjAll_strict_not_omegaContinuous`, `chaosNormal_not_preserved_by_comp`.

Basis: execution (Lean kernel check) — `conjNonempty_iff_eq_wp_relOf_termOf` (axioms: `Quot.sound`, `propext`); `relOf_wp` (axioms: `Quot.sound`, `propext`); `wp_eq_wp_iff` (axioms: `Quot.sound`, `propext`).

#### Result 3 — `strict-iff-no-miracle`

- **Lean:** `strict_wp_iff_totalOn` (namespace `Toy.PredTrans`).
- **Kind:** characterization. **Tier:** T0 — Standard reading of the law of the excluded miracle as excluding partial relations; the wlp case is mechanized in Isabelle/HOL (Struth 2018, rfb_zero_pres2).

Statement, as printed by `#check` on the built library:

```lean
@strict_wp_iff_totalOn : ∀ {σ : Type u_1} (R : Rel σ) (term : Pred σ), Strict (wp R term) ↔ TotalOn R term
```

Unfolded (`Strict`, `wp`, `wlp`, `TotalOn`):

```lean
(∀ s, ¬ (term s ∧ ∀ s', R s s' → False)) ↔ ∀ s, term s → ∃ s', R s s'
```

**Plain claim.** wp R term satisfies the law of the excluded miracle (wp R term False = False) if and only if every start state in term has at least one R-successor.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| totality is required only on non-aborting start states | outside term, wp R term is false whatever R is; the witness is strict although R is not total | tight: counterexample `strict_wp_without_total_relation` |
| classical logic | needed: the statement (and its wlp corollary), restricted to the one-point state type, implies excluded middle by a proof that uses no axiom at all. Lean's logic is classical, so no countermodel can be exhibited inside Lean; this reverse implication is the witness. | tight (logical-strength witness): `lem_of_strict_wp_iff_totalOn`, `lem_of_strict_wlp_iff` |

**Depth.** definitional.

**Non-vacuity witness.** The partial decrement with non-abortion predicate 'nonzero' is strict and total on it; with the everywhere-true predicate it is neither. (`strict_wp_both_sides_occur`)

**Companions and corollaries (proved in the package).** `strict_wlp_iff`.

**Prior art.**

- E. W. Dijkstra, 'Guarded commands, nondeterminacy and formal derivation of programs', Communications of the ACM 18(8):453-457, 1975, doi:10.1145/360933.360975 (content seen in the archive transcription of EWD 472: the law of the excluded miracle wp(S, F) = F is the first of four properties of wp)
- E. W. Dijkstra, 'A Discipline of Programming', Prentice-Hall, 1976 (content seen in a scanned copy: ch. 3 'The Characterization of Semantics', Property 1, the law of the excluded miracle)
- G. Nelson, 'A generalization of Dijkstra's calculus', ACM Transactions on Programming Languages and Systems 11(4):517-561, 1989, doi:10.1145/69558.69559 (content seen: abstract - the law of the excluded miracle is dropped; technical-report version (SRC Research Report 16) - the law excludes partial commands)
- C. Morgan, 'The specification statement', ACM Transactions on Programming Languages and Systems 10(3):403-419, 1988, doi:10.1145/44501.44503 (content seen: abstract - miracles appear as program fragments violating the law of the excluded miracle)
- J. M. Morris, 'A theoretical basis for stepwise refinement and the programming calculus', Science of Computer Programming 9(3):287-306, 1987, doi:10.1016/0167-6423(87)90011-6 (bibliographic record verified; an early refinement-calculus source; text not read)
- G. Struth, 'Transformer Semantics', Archive of Formal Proofs, 11 December 2018, https://isa-afp.org/entries/Transformer_Semantics.html; theory Kleisli_Transformers.thy as mirrored in isabelle-prover/mirror-afp-devel at commit 523cdc72b5ae4a91c9ab8e1025d4a30b40472720 (content seen: lemma rfb_zero_pres2, 'fb_R R {} = - Domain R': the forward box of a relation at the empty set is the complement of its domain, i.e. the wlp case of this result)
- E. Sekerinski and T. Zhang, 'A Normal Form for Multi-Exit Statements', author-hosted manuscript dated December 2011, https://www.cas.mcmaster.ca/~emil/pubs/SekerinskiZhang11NormalFormMultiExit.pdf (URL resolved on 2026-11-20; SHA-256 of the PDF file not recorded) (blank 'Submitted to' line; it cites a 2013 paper of the same authors, so the text was revised after 2013; venue not verified) (content seen: section 7 calculates the enabledness domain en[R] as the disjunction over exits of dom(R_x), and for {p};[R] obtains p => (disjunction of dom(R_x)) as a feasibility condition)

**Design question informed.** Which laws must a verification framework demand of a weakest-precondition transformer so that every admitted transformer is the wp of some relational (possibly nondeterministic, possibly aborting) program, without excluding honest programs? Strictness excludes exactly the miraculous programs (useful as specifications, not executable); it should be a separate, optional law.

**Non-claims:** see Boundaries, result 3.

**Scope witnesses cited in the non-claims (proved in the package; statements printed under Evidence).** `termOf_wlp_emptyR_no_outcome`.

Basis: execution (Lean kernel check) — `strict_wp_iff_totalOn` (axioms: `Classical.choice`, `Quot.sound`, `propext`).

#### Result 4 — `omega-continuity-iff-bounded-nondeterminism`

- **Lean:** `omegaContinuous_wp_iff_finiteImage_on_term` (namespace `Toy.PredTrans`).
- **Kind:** characterization. **Tier:** T0 — Both directions are classical: continuity of wp for boundedly nondeterministic mechanisms and its failure for unbounded choice (Dijkstra 1976, ch. 9; the title of EWD 675 states the equivalence; Plotkin 1980 and Wand 1977 in the strict setting on a countable state set). Restated here for an arbitrary pair (R, term) over an arbitrary state type; that no countability of the state type is needed follows from the fact that an infinite set has a countably infinite subset (using choice).

Statement, as printed by `#check` on the built library:

```lean
@omegaContinuous_wp_iff_finiteImage_on_term : ∀ {σ : Type u_1} (R : Rel σ) (term : Pred σ),
  OmegaContinuous (wp R term) ↔ ∀ (s : σ), term s → FiniteImage R s
```

Unfolded (`OmegaContinuous`, `Chain`, `wp`, `wlp`, `FiniteImage`):

```lean
(∀ Q : Nat → σ → Prop, (∀ n s, Q n s → Q (n + 1) s) →
    ∀ s, (term s ∧ ∀ s', R s s' → ∃ n, Q n s') → ∃ n, term s ∧ ∀ s', R s s' → Q n s')
  ↔ ∀ s, term s → ∃ l : List σ, ∀ s', R s s' → s' ∈ l
```

**Plain claim.** For any state type, wp R term is omega-continuous (establishing the union of an increasing Nat-indexed chain of postconditions implies establishing one member) if and only if every start state in term has a finite R-image, i.e. all its successors lie in one list. No countability or other hypothesis on the state type is needed.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| finiteness is required only on non-aborting start states | outside term, wp R term is false whatever R is; the witnesses are omega-continuous although the image at an aborting state is infinite (one with a non-degenerate non-abortion predicate) | tight: counterexample `omegaContinuous_wp_partial_infinite_image_outside_term`, `omegaContinuous_wp_with_infinite_image_outside_term` |
| chains rather than arbitrary countable families in OmegaContinuous | for the two-way choice every image is finite and wp is omega-continuous, yet the same implication for arbitrary Nat-indexed families fails | tight: counterexample `not_continuous_on_arbitrary_families_stepR_canonical` |
| a non-constructive principle (backward direction: finite image implies omega-continuity) | needed: the backward direction, restricted to the one-point state type, implies the limited principle of omniscience by a proof that uses no axiom, so it is not constructively provable. Reason: FiniteImage gives a list containing every successor without deciding which list members are successors. Lean's logic is classical, so no countermodel can be exhibited inside Lean; this reverse implication is the witness. | tight (logical-strength witness): `lpo_of_finiteImage_imp_omegaContinuous_wp` |
| axiom of choice (forward direction: omega-continuity implies finite image) | used to extract an injective sequence from an image contained in no list; whether the forward direction needs choice (or excluded middle) was not determined | unknown |

**Depth.** substantive.

**Non-vacuity witness.** The two-way choice on Nat is omega-continuous with finite images and havoc on Nat is neither; with the partial non-abortion predicate 'nonzero', zeroHavocR satisfies both sides and havoc fails both. (`omegaContinuous_wp_both_sides_occur`, `omegaContinuous_wp_partial_both_sides_occur`)

**Companions and corollaries (proved in the package).** `omegaContinuous_wlp_iff`, `omegaContinuous_two_sided_iff`.

**Prior art.**

- E. W. Dijkstra, 'A Discipline of Programming', Prentice-Hall, 1976 (content seen in a scanned copy: ch. 9 'On Nondeterminacy Being Bounded', Property 5 = continuity over omega-chains, and 'set x to any positive integer' contradicts it)
- E. W. Dijkstra and A. J. M. van Gasteren, 'A simple fixpoint argument without the restriction to continuity', Acta Informatica 23(1):1-7, 1986, doi:10.1007/BF00268074 (content seen: abstract - unbounded nondeterminacy amounts to the introduction of noncontinuous predicate transformers)
- E. W. Dijkstra, 'The Equivalence of Bounded Nondeterminacy and Continuity' (EWD 675, 1978), in Selected Writings on Computing: A Personal Perspective, Springer, 1982, pp. 358-359, doi:10.1007/978-1-4612-5695-3_65 (bibliographic record verified; the title states the equivalence; text not read)
- G. D. Plotkin, 'Dijkstra's predicate transformers and Smyth's powerdomains', in Abstract Software Specifications, LNCS 86, Springer, 1980, pp. 527-553, doi:10.1007/3-540-10007-5_48 (content seen in the author's scan: denumerable state set; strict, continuous, multiplicative transformers; a finitary transition relation gives continuity; Lemma 5.6; Theorem 5.9)
- M. Wand, 'A characterization of weakest preconditions', Journal of Computer and System Sciences 15(2):209-212, 1977, doi:10.1016/S0022-0000(77)80006-8 (content seen: abstract only - a map on sets of states is the wp of a mechanism of bounded nondeterminacy iff it is strict, preserves binary intersections and is continuous over directed sets; for countable state sets omega-chains suffice)
- K. R. Apt and G. D. Plotkin, 'Countable nondeterminism and random assignment', Journal of the ACM 33(4):724-767, 1986, doi:10.1145/6490.6494 (content seen: abstract - countable nondeterminism results in a lack of continuity)
- R.-J. Back and J. von Wright, 'Refinement Calculus: A Systematic Introduction', Springer, 1998, doi:10.1007/978-1-4612-1674-2 (located only: table of contents and chapter abstracts; ch. 22 'Continuity and Executable Statements' and section 26.5; theorem statements and numbers not seen at the source)
- M. B. Smyth, 'Power domains and predicate transformers: A topological view', in Automata, Languages and Programming (ICALP 1983), LNCS 154, Springer, 1983, pp. 662-675, doi:10.1007/BFb0036946 (bibliographic record verified; topological treatment of the correspondence between power domains and predicate transformers, per its title; text not read)
- M. Bonsangue and J. N. Kok, 'Isomorphisms between predicate and state transformers', in Mathematical Foundations of Computer Science 1993, LNCS 711, Springer, 1993, pp. 301-310, doi:10.1007/3-540-57182-5_22 (content seen: abstract - isomorphisms between state transformers on the Hoare, Smyth and Plotkin power domains and continuous, monotonic and unrestricted predicate transformers)

**Design question informed.** Which laws must a verification framework demand of a weakest-precondition transformer so that every admitted transformer is the wp of some relational (possibly nondeterministic, possibly aborting) program, without excluding honest programs? Demanding omega-continuity of every wp is exactly demanding bounded nondeterminism on the non-aborting states; a framework that wants 'choose any natural number' must not demand it.

**Non-claims:** see Boundaries, result 4.

**Scope witnesses cited in the non-claims (proved in the package; statements printed under Evidence).** `omegaContinuous_wp_emptyR`, `omegaContinuous_negT_not_monotone`, `havocR_nat_conjAll_strict_not_omegaContinuous`.

Basis: execution (Lean kernel check) — `omegaContinuous_wp_iff_finiteImage_on_term` (axioms: `Classical.choice`, `Quot.sound`, `propext`).

#### Result 5 — `finitary-laws-not-relational`

- **Lean:** `eventually_finitary_laws_not_relational` (namespace `Toy.PredTrans`).
- **Kind:** counterexample. **Tier:** T1 — In algebraic modal logic the separation between finitely and completely multiplicative operators on an infinite powerset algebra (for example via the cofinite filter) is classical; no source stating the example for predicate transformers was located, and no mechanization was found.

Statement, as printed by `#check` on the built library:

```lean
eventually_finitary_laws_not_relational : Monotone eventually ∧
  ConjBin eventually ∧
    TopPreserving eventually ∧
      Strict eventually ∧
        ¬OmegaContinuous eventually ∧
          ¬ConjNonempty eventually ∧ (¬∃ R, eventually = wlp R) ∧ ¬∃ R term, eventually = wp R term
```

Here `eventually : Transformer Nat` is `fun Q _ => ∃ N, ∀ n, N ≤ n → Q n` ("`Q` holds of all
but finitely many numbers"; the start state is ignored). The laws are unfolded in the
definitions table above.

**Plain claim.** On the state type Nat, the transformer 'the postcondition holds of all but finitely many numbers' is monotone, binary conjunctive (hence conjunctive over every finite list), top preserving and strict, yet it is not omega-continuous, not positively conjunctive, not wlp R for any relation R and not wp R term for any R and term.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| the state type is infinite | on a finite state type every binary conjunctive transformer is positively conjunctive (conjNonempty_of_conjBin_of_finiteState), contradicting the conjunct 'not positively conjunctive'; so no such example exists there. By the wp characterization, that class is then exactly the wp's (conjBin_iff_exists_wp_of_finiteState), and with top preservation exactly the wlp's (conjBin_topPreserving_iff_exists_wlp_of_finiteState). The second witness shows the infinite state type Nat with a binary conjunctive transformer that is not positively conjunctive. | tight: counterexample `conjNonempty_of_conjBin_of_finiteState`, `eventually_infinite_conjBin_not_conjNonempty` |
| on a state type injecting into Nat -> Bool (in particular Nat): the transformer is not omega-continuous | on such a state type binary conjunctivity plus omega-continuity forces positive conjunctivity (conjNonempty_of_conjBin_of_omegaContinuous_of_continuumState), so every example there must fail omega-continuity; eventually does | tight: counterexample `conjNonempty_of_conjBin_of_omegaContinuous_of_continuumState`, `not_omegaContinuous_eventually` |
| on any state type: the transformer is not continuous over directed families | on every state type binary conjunctivity plus continuity over directed families forces positive conjunctivity (conjNonempty_of_conjBin_of_dirContinuous), so every example must fail directed continuity; eventually does | tight: counterexample `conjNonempty_of_conjBin_of_dirContinuous`, `eventually_conjBin_not_dirContinuous_not_conjNonempty` |

**Depth.** shallow.

**Non-vacuity witness.** The statement is itself a concrete instance; eventually_conjList shows conjunctivity over every finite list. (`eventually_conjList`)

**Positive control.** With the threshold fixed, `fromN N` is a `wlp` (`fromN_eq_wlp`); `eventually` is the angelic choice of the `fromN N` (`eventually_iff_exists_fromN`); on a finite state type no such example exists, because binary conjunctivity already forces positive conjunctivity there (`conjNonempty_of_conjBin_of_finiteState`).

**Companions and corollaries (proved in the package).** `finitary_laws_do_not_imply_relational`, `eventually_conjList`, `eventually_ne_wp`, `eventually_ne_wlp`, `conjBin_iff_exists_wp_of_finiteState`, `conjBin_topPreserving_iff_exists_wlp_of_finiteState`, `conjBin_omegaContinuous_iff_wp_finiteImage_of_continuumState`, `exists_wp_of_conjBin_of_dirContinuous`.

**Prior art.**

- No source stating this example for predicate transformers was located. Sources examined for it: Dijkstra 1975 and 1976; Back and von Wright 1998 (table of contents and chapter abstracts); Plotkin 1980; Wand 1977 (abstract); the Sekerinski-Zhang manuscript; the Isabelle/HOL Archive of Formal Proofs entries 'Transformer Semantics' and 'Formalization of Refinement Calculus for Reactive Systems'; Mathlib's SetRel; Maillard et al. 2019.
- B. Jonsson and A. Tarski, 'Boolean Algebras with Operators. Part I', American Journal of Mathematics 73(4):891-939, 1951, doi:10.2307/2372123, and 'Boolean Algebras with Operators' [Part II], American Journal of Mathematics 74(1):127-162, 1952, doi:10.2307/2372074; P. Blackburn, M. de Rijke, Y. Venema, 'Modal Logic', Cambridge University Press, 2001, doi:10.1017/CBO9781107050884 (bibliographic records verified; cited for the lineage in algebraic modal logic in which finitely multiplicative (normal) modal operators on an infinite powerset algebra need not be completely multiplicative, i.e. need not come from a Kripke relation; the specific passages were not read)
- M. Wand, 'A characterization of weakest preconditions', Journal of Computer and System Sciences 15(2):209-212, 1977, doi:10.1016/S0022-0000(77)80006-8 (content seen: abstract only - with strictness and continuity over directed sets the binary law characterizes wp; for countable state sets omega-chains suffice; this bounds how far the present example may be read)

**Design question informed.** Which laws must a verification framework demand of a weakest-precondition transformer so that every admitted transformer is the wp of some relational (possibly nondeterministic, possibly aborting) program, without excluding honest programs? A framework that demands only binary conjunctivity (plus strictness, top preservation, monotonicity) admits transformers on infinite state types that no relational program has.

**Non-claims:** see Boundaries, result 5.

**Scope witnesses cited in the non-claims (proved in the package; statements printed under Evidence).** `not_disjBin_eventually`.

Basis: execution (Lean kernel check) — `eventually_finitary_laws_not_relational` (axioms: `Quot.sound`, `propext`).

#### Result 6 — `refinement-correspondence`

- **Lean:** `refinedBy_wp_iff`, `refinedBy_wp_iff_of_chaosNormal` (namespace `Toy.PredTrans`).
- **Kind:** characterization. **Tier:** T0 — The criterion is mechanized in Isabelle/HOL (Preoteasa 2014, lemma assert_demonic_refinement) and, with return values, in Coq (Alpuim and Swierstra 2018, Theorem soundness); the chaos-normal-form corollary is spelled out here.

Statement, as printed by `#check` on the built library:

```lean
@refinedBy_wp_iff : ∀ {σ : Type u_1} (R₁ R₂ : Rel σ) (t₁ t₂ : Pred σ),
  RefinedBy (wp R₁ t₁) (wp R₂ t₂) ↔ (∀ (s : σ), t₁ s → t₂ s) ∧ ∀ (s : σ), t₁ s → ∀ (s' : σ), R₂ s s' → R₁ s s'
@refinedBy_wp_iff_of_chaosNormal : ∀ {σ : Type u_1} {R₁ R₂ : Rel σ} {t₁ t₂ : Pred σ},
  ChaosNormal R₁ t₁ → (RefinedBy (wp R₁ t₁) (wp R₂ t₂) ↔ (∀ (s : σ), t₁ s → t₂ s) ∧ ∀ (s s' : σ), R₂ s s' → R₁ s s')
```

Unfolded left side (`RefinedBy`, `wp`, `wlp`):
`∀ Q s, (t₁ s ∧ ∀ s', R₁ s s' → Q s') → (t₂ s ∧ ∀ s', R₂ s s' → Q s')`;
`ChaosNormal R₁ t₁` unfolds to `∀ s, ¬ t₁ s → ∀ s', R₁ s s'`.

**Plain claim.** wp R1 t1 is refined by wp R2 t2 (every guarantee of the first is a guarantee of the second) if and only if t1 is included in t2 and, on start states in t1, every R2-outcome is an R1-outcome; no normal form is assumed. If moreover (R1, t1) is in chaos normal form, the second condition may be replaced by the global inclusion of R2 in R1.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| (refinedBy_wp_iff) relation inclusion is restricted to non-aborting start states of the refined program | outside t1 the first program guarantees nothing, so nothing constrains R2 there: abort, presented with the empty relation, is refined by havoc although havoc's relation is not included in the empty one | tight: counterexample `refinedBy_wp_without_global_relation_inclusion` |
| (both statements) inclusion of non-abortion predicates | relation inclusion alone does not give refinement, even for pairs in chaos normal form | tight: counterexample `relation_inclusion_without_term_inclusion_not_refinedBy` |
| (refinedBy_wp_iff_of_chaosNormal) ChaosNormal R1 t1 | without it the global form fails: the witness is not in chaos normal form, refinement holds, and the global criterion fails | tight: counterexample `refinedBy_wp_global_inclusion_needs_chaosNormal` |
| (refinedBy_wp_iff) classical logic | not needed: refinedBy_wp_iff is proved using no axiom at all: audit/axioms.json records an empty axiom list for it | harmless |
| (refinedBy_wp_iff_of_chaosNormal) classical logic | needed: the global form, restricted to the one-point state type, implies excluded middle by a proof that uses no axiom. Lean's logic is classical, so no countermodel can be exhibited inside Lean; this reverse implication is the witness. | tight (logical-strength witness): `lem_of_refinedBy_wp_iff_of_chaosNormal` |

**Depth.** shallow.

**Non-vacuity witness.** havoc on Nat is refined by the two-way choice and not conversely; with the partial non-abortion predicate 'nonzero', the partial decrement is refined by the total-domain decrement and not conversely; the chaos normal form of the partial decrement satisfies all hypotheses and both sides of the global form. (`refinedBy_wp_both_sides_occur`, `refinedBy_wp_partial_both_sides_occur`, `refinedBy_wp_chaosNormal_partial_nonvacuous`)

**Companions and corollaries (proved in the package).** `refinedBy_wlp_iff`.

**Prior art.**

- V. Preoteasa, 'Formalization of Refinement Calculus for Reactive Systems', Archive of Formal Proofs, 8 October 2014, https://isa-afp.org/entries/RefinementReactive.html; theory Refinement.thy as mirrored in isabelle-prover/mirror-afp-devel at commit 523cdc72b5ae4a91c9ab8e1025d4a30b40472720 (content seen: lemma assert_demonic_refinement, '({.p.} o [:r:] <= {.p'.} o [:r':]) = (p <= p' and (forall x. p x --> r' x <= r x))')
- J. Alpuim and W. Swierstra, 'Embedding the refinement calculus in Coq', Science of Computer Programming 164:37-48, 2018, doi:10.1016/j.scico.2017.04.003; Coq development https://github.com/jalpuim/dtp-refinement at commit a29203b823d0399657c3f5edca3b8a105797260b, file Refinement.v (content seen: Theorem soundness, '(pt1 refines pt2 -> forall P, semantics pt1 P subset semantics pt2 P) * ((forall P, ...) -> pt1 refines pt2)', for specifications with a precondition and a postcondition that may depend on the proof of the precondition and on a return value; constructive Coq)
- R.-J. Back and J. von Wright, 'Refinement Calculus: A Systematic Introduction', Springer, 1998, doi:10.1007/978-1-4612-1674-2 (located only: table of contents and chapter abstracts; ch. 17 'Correctness and Refinement of Statements' and section 27.4 'Refining Conjunctive Specifications'; theorem statements and numbers not seen at the source)
- G. Nelson, 'A generalization of Dijkstra's calculus', ACM Transactions on Programming Languages and Systems 11(4):517-561, 1989, doi:10.1145/69558.69559 (content seen in the technical-report version, SRC Research Report 16: an approximation order defined from wp and wlp jointly; contrast for the order used here)
- M. M. Bonsangue and J. N. Kok, 'The weakest precondition calculus: Recursion and duality', Formal Aspects of Computing 6:788-800, 1994, doi:10.1007/BF01213603 (content seen: abstract - compares a refinement ordering defined by Back, a deadlock ordering and an approximation ordering of Nelson, and relates predicate transformers to Smyth and Egli-Milner power domains)
- J. M. Morris, 'A theoretical basis for stepwise refinement and the programming calculus', Science of Computer Programming 9(3):287-306, 1987, doi:10.1016/0167-6423(87)90011-6 (bibliographic record verified; an early refinement-calculus source; text not read)

**Design question informed.** Which laws must a verification framework demand of a weakest-precondition transformer so that every admitted transformer is the wp of some relational (possibly nondeterministic, possibly aborting) program, without excluding honest programs? How a refinement order on wp's translates to relational programs, and which normalization makes it a plain inclusion.

**Non-claims:** see Boundaries, result 6.

**Scope witnesses cited in the non-claims (proved in the package; statements printed under Evidence).** `relational_criterion_fails_off_wp`.

Basis: execution (Lean kernel check) — `refinedBy_wp_iff` (axioms: none); `refinedBy_wp_iff_of_chaosNormal` (axioms: `Classical.choice`, `Quot.sound`, `propext`).

#### Result 7 — `wp-algebra`

- **Lean:** `wp_comp`, `wlp_comp`, `wp_union`, `wlp_union` (namespace `Toy.PredTrans`).
- **Kind:** theorem. **Tier:** T0 — The defining equations of sequential composition and demonic choice in relational predicate-transformer semantics; all four are mechanized in Isabelle/HOL (Preoteasa 2014).

Statement, as printed by `#check` on the built library:

```lean
@wp_comp : ∀ {σ : Type u_1} (R₁ R₂ : Rel σ) (t₁ t₂ : Pred σ),
  wp (comp R₁ R₂) (seqTerm R₁ t₁ t₂) = fun Q => wp R₁ t₁ (wp R₂ t₂ Q)
@wlp_comp : ∀ {σ : Type u_1} (R₁ R₂ : Rel σ), wlp (comp R₁ R₂) = fun Q => wlp R₁ (wlp R₂ Q)
@wp_union : ∀ {σ : Type u_1} (R₁ R₂ : Rel σ) (t₁ t₂ Q : Pred σ) (s : σ),
  wp (union R₁ R₂) (fun s => t₁ s ∧ t₂ s) Q s ↔ wp R₁ t₁ Q s ∧ wp R₂ t₂ Q s
@wlp_union : ∀ {σ : Type u_1} (R₁ R₂ : Rel σ) (Q : Pred σ) (s : σ), wlp (union R₁ R₂) Q s ↔ wlp R₁ Q s ∧ wlp R₂ Q s
```

Unfolded auxiliary definitions: `comp R₁ R₂ s s'' = ∃ s', R₁ s s' ∧ R₂ s' s''`,
`union R₁ R₂ s s' = R₁ s s' ∨ R₂ s s'`, and `seqTerm R₁ t₁ t₂ s = t₁ s ∧ ∀ s', R₁ s s' → t₂ s'`,
which is definitionally `wp R₁ t₁ t₂ s` (`seqTerm_eq_wp`, proved by `rfl`).

**Plain claim.** The wp of a relational composition, with non-abortion predicate 'the first program does not abort and the second does not abort from any reachable intermediate state' (seqTerm R1 t1 t2, which is by definition wp R1 t1 t2), is the composition of the wp's; the wp of a union of relations, with the conjunction of the non-abortion predicates, is the pointwise conjunction of the wp's; likewise for wlp.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| the composite's non-abortion predicate is seqTerm, not that of the first component | the second program must not abort from any reachable intermediate state | tight: counterexample `wp_comp_first_term_wrong` |
| the composite's non-abortion predicate is seqTerm, not the conjunction of the components' predicates | the second program's predicate must hold at the intermediate states, not at the start state | tight: counterexample `wp_comp_conj_term_wrong` |
| a demonic choice's non-abortion predicate is the conjunction, not the disjunction, of the components' predicates | a demonic choice aborts wherever either alternative may abort | tight: counterexample `wp_union_disj_term_wrong` |

**Depth.** definitional.

**Non-vacuity witness.** From 0, the two-way choice followed by the partial decrement does not abort and ends in a state at most 1. (`wp_comp_example`)

**Companions and corollaries (proved in the package).** `wlp_iUnion`, `wp_skipR_true`, `wlp_emptyR`, `seqTerm_eq_wp`.

**Prior art.**

- E. W. Dijkstra, 'Guarded commands, nondeterminacy and formal derivation of programs', Communications of the ACM 18(8):453-457, 1975, doi:10.1145/360933.360975 (content seen in the archive transcription of EWD 472: the syntactic equation wp(S1;S2, R) = wp(S1, wp(S2, R)) for guarded commands; no relational model)
- V. Preoteasa, 'Formalization of Refinement Calculus for Reactive Systems', Archive of Formal Proofs, 8 October 2014, https://isa-afp.org/entries/RefinementReactive.html; theory Refinement.thy as mirrored in isabelle-prover/mirror-afp-devel at commit 523cdc72b5ae4a91c9ab8e1025d4a30b40472720 (content seen: demonic_demonic, '[:r:] o [:r':] = [:r OO r':]' (line 53); assert_demonic_comp, '{.p.} o [:r:] o {.p'.} o [:r':] = {.x. p x and (forall y. r x y --> p' y).} o [:r OO r':]' (lines 56-57); an unnamed lemma '[:r:] inf [:r':] = [:r sup r':]' (line 108); spec_demonic_choice, '({.p.} o [:r:]) inf ({.p'.} o [:r':]) = ({.p inf p'.} o [:r sup r':])' (line 111))
- G. Struth, 'Transformer Semantics', Archive of Formal Proofs, 11 December 2018, https://isa-afp.org/entries/Transformer_Semantics.html; theory Kleisli_Transformers.thy as mirrored in isabelle-prover/mirror-afp-devel at commit 523cdc72b5ae4a91c9ab8e1025d4a30b40472720 (content seen: rfb_comp_pres (line 545), rfb_Id_pres (line 548), rfb_Sup_dual_var (line 565), rfb_zero_pres (line 580); partial correctness only)
- Mathlib (leanprover-community/mathlib4, commit 5f78f9ce46fc85fa3cb45561d47b489c4c98cd04), file Mathlib/Basic/Rel.lean (content seen: SetRel.core_comp, 'core (R o S) u = core R (core S u)' (line 345), and core_id (line 342))
- K. Maillard, D. Ahman, R. Atkey, G. Martinez, C. Hritcu, E. Rivas, E. Tanter, 'Dijkstra monads for all', Proceedings of the ACM on Programming Languages 3(ICFP), article 104, 2019, doi:10.1145/3341708 (preprint arXiv:1903.01237) (content seen in the preprint, section 4.1: bind of the PrePost monad, '<(pre /\ forall a. post a => pre' a), fun b => exists a. post a /\ post' a b>', i.e. seqTerm and relational composition in a return-value setting)
- J. Alpuim and W. Swierstra, 'Embedding the refinement calculus in Coq', Science of Computer Programming 164:37-48, 2018, doi:10.1016/j.scico.2017.04.003; Coq development https://github.com/jalpuim/dtp-refinement at commit a29203b823d0399657c3f5edca3b8a105797260b, file Refinement.v (content seen: SeqPT, whose precondition is the precondition of the first statement together with the second's precondition at every intermediate state)

**Design question informed.** Reference point: the transformer-level and relation-level program algebras agree for sequencing and demonic choice.

**Non-claims:** see Boundaries, result 7.

**Scope witnesses cited in the non-claims (proved in the package; statements printed under Evidence).** `chaosNormal_not_preserved_by_comp`.

Basis: execution (Lean kernel check) — `wp_comp` (axioms: `Quot.sound`, `propext`); `wlp_comp` (axioms: `Quot.sound`, `propext`); `wp_union` (axioms: none); `wlp_union` (axioms: none).

#### Result 8 — `monotone-angelic-demonic-normal-form`

- **Lean:** `monotone_iff_eq_angelicDemonic_multirelOf`, `multirelOf_angelicDemonic_eq_iff` (namespace `Toy.PredTrans`).
- **Kind:** characterization. **Tier:** T0 — The angelic-update/demonic-update normal form of monotonic predicate transformers and the correspondence with up-closed multirelations are textbook material.

Statement, as printed by `#check` on the built library:

```lean
@monotone_iff_eq_angelicDemonic_multirelOf : ∀ {σ : Type u_1} (T : Transformer σ),
  Monotone T ↔ T = angelicDemonic (multirelOf T)
@multirelOf_angelicDemonic_eq_iff : ∀ {σ : Type u_1} (A : σ → Pred σ → Prop),
  multirelOf (angelicDemonic A) = A ↔ UpClosed A
```

Unfolded (`Monotone`, `angelicDemonic`, `multirelOf`, `UpClosed`):

```lean
(∀ P Q, (∀ t, P t → Q t) → ∀ s, T P s → T Q s) ↔ T = fun Q s => ∃ P, T P s ∧ ∀ t, P t → Q t

(fun s P => ∃ P', A s P' ∧ ∀ t, P' t → P t) = A
  ↔ ∀ s P P', A s P → (∀ t, P t → P' t) → A s P'
```

**Plain claim.** A predicate transformer is monotone if and only if it is an angelic choice of demonic updates, T Q s iff there is a set P available at s all of whose members satisfy Q, where one may take 'P is available at s' to mean T P s (the multirelation multirelOf T); and multirelOf recovers a multirelation A from its transformer angelicDemonic A if and only if A is up-closed, giving a one-to-one correspondence between monotone transformers and up-closed multirelations. Non-up-closed multirelations can induce the same transformer as an up-closed one.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| monotonicity (first statement) | every transformer of the angelic/demonic form is monotone; negation is not monotone and is not of that form | tight: counterexample `negT_not_monotone_not_angelicDemonic` |
| up-closure (second statement) | multirelOf returns an up-closed multirelation, so a multirelation that is not up-closed is not recovered from its transformer | tight: counterexample `not_upClosed_not_recovered_by_multirelOf` |

**Depth.** definitional.

**Non-vacuity witness.** eventually is monotone and equal to the transformer of its multirelation, negation is neither; 'all sets containing the current state' is up-closed and recovered, the singleton multirelation is neither; eventually and every wp are exhibited with explicit multirelations. (`monotone_angelicDemonic_both_sides_occur`, `multirelOf_angelicDemonic_both_sides_occur`, `eventually_eq_angelicDemonic`, `wp_eq_angelicDemonic`)

**Companions and corollaries (proved in the package).** `monotone_angelicDemonic`, `monotone_iff_exists_angelicDemonic`, `upClosed_multirelOf_iff`, `angelicDemonic_not_injective`, `upClosed_not_unique_among_all`.

**Prior art.**

- R.-J. Back and J. von Wright, 'Refinement Calculus: A Systematic Introduction', Springer, 1998, doi:10.1007/978-1-4612-1674-2 (located only: ch. 13 'Statements', section 13.3 'Statements and Monotonic Predicate Transformers'; content seen: abstract of ch. 15 'Choice Semantics' - statements interpreted as functions mapping each initial state to a set of predicates over the final state space, equivalent to the predicate transformer semantics; the chapter body and theorem numbers not seen)
- E. Sekerinski and T. Zhang, 'A Normal Form for Multi-Exit Statements', author-hosted manuscript dated December 2011, https://www.cas.mcmaster.ca/~emil/pubs/SekerinskiZhang11NormalFormMultiExit.pdf (URL resolved on 2026-11-20; SHA-256 of the PDF file not recorded) (blank 'Submitted to' line; it cites a 2013 paper of the same authors, so the text was revised after 2013; venue not verified) (content seen: Theorem 13, every monotonic indexed predicate transformer is {r};[R], stated there to generalize the single-exit theorem of Back and von Wright; its introduction credits von Wright 1994 with a normal form relying on angelic and demonic updates)
- J. von Wright, 'The lattice of data refinement', Acta Informatica 31(2):105-135, 1994, doi:10.1007/BF01192157 (bibliographic record verified; credited by Sekerinski and Zhang with an angelic/demonic normal form; text not read)
- R. Parikh, 'Propositional game logic', 24th Annual Symposium on Foundations of Computer Science (FOCS 1983), pp. 195-200, doi:10.1109/SFCS.1983.47; R. Parikh, 'The Logic of Games and its Applications', North-Holland Mathematics Studies, 1985, pp. 111-139, doi:10.1016/S0304-0208(08)73078-0 (bibliographic records verified; credited by Furusawa and Struth (arXiv:1501.05147, section 15) with having noticed 'a duality between up-closed multirelations and sets of isotone predicate transformers'; Parikh's texts not read)
- H. Furusawa and G. Struth, 'Taming Multirelations', ACM Transactions on Computational Logic 17(4), 2016, doi:10.1145/2964907 (preprint arXiv:1501.05147) (content seen in the preprint: algebra of multirelations, including up-closed multirelations, with the attribution to Parikh quoted above)
- I. Rewitzky, 'Binary Multirelations', in Theory and Applications of Relational Structures as Knowledge Instruments, LNCS 2929, Springer, 2003, pp. 256-271, doi:10.1007/978-3-540-24615-2_12 (content seen: abstract - binary multirelations and monotone unary operators are intertranslatable)
- I. Rewitzky and C. Brink, 'Monotone Predicate Transformers as Up-Closed Multirelations', in Relations and Kleene Algebra in Computer Science, LNCS 4136, Springer, 2006, pp. 311-327, doi:10.1007/11828563_21 (content seen: abstract - monotone predicate transformers are up-closed multirelations)
- T. Altenkirch, N. Ghani, P. Hancock, C. McBride, P. Morris, 'Indexed containers', Journal of Functional Programming 25, article e5, 2015, doi:10.1017/S095679681500009X (bibliographic record verified; an author draft cites the monotonic normal form as Back and von Wright 'Thm 13.10'; the published version and the book page were not read, so that theorem number is not relied on)
- K. Maillard, D. Ahman, R. Atkey, G. Martinez, C. Hritcu, E. Rivas, E. Tanter, 'Dijkstra monads for all', Proceedings of the ACM on Programming Languages 3(ICFP), article 104, 2019, doi:10.1145/3341708 (preprint arXiv:1903.01237) (content seen in the preprint: the specification monad W^Pure of monotonic predicate transformers)

**Design question informed.** Reference point: demanding only monotonicity admits exactly the angelic/demonic games, a strictly larger class than relational programs.

**Non-claims:** see Boundaries, result 8.

Basis: execution (Lean kernel check) — `monotone_iff_eq_angelicDemonic_multirelOf` (axioms: `Quot.sound`, `propext`); `multirelOf_angelicDemonic_eq_iff` (axioms: `Quot.sound`, `propext`).

#### Result 9a — `finite-state-binary-conjunctivity-suffices`

- **Lean:** `conjNonempty_of_conjBin_of_finiteState` (namespace `Toy.PredTrans`).
- **Kind:** theorem. **Tier:** T0 — Elementary: on a finite state type every intersection of predicates is, extensionally, a finite one, the standard observation that a finitely multiplicative operator on a finite Boolean algebra is completely multiplicative. No specific source passage was read.

Statement, as printed by `#check` on the built library:

```lean
@conjNonempty_of_conjBin_of_finiteState : ∀ {σ : Type u_1},
  FiniteState σ → ∀ {T : Transformer σ}, ConjBin T → ConjNonempty T
```

Unfolded hypotheses: `FiniteState σ := ∃ l : List σ, ∀ x, x ∈ l` (the empty type
qualifies) and `ConjBin T := ∀ P Q s, T (fun t => P t ∧ Q t) s ↔ T P s ∧ T Q s`; the conclusion
`ConjNonempty T` is unfolded in the definitions table.

**Plain claim.** On a finite state type (all states in one list), every binary conjunctive predicate transformer is conjunctive over all nonempty families.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| FiniteState | reduces any intersection of postconditions to a finite one; on Nat, eventually is binary conjunctive and not positively conjunctive | tight: counterexample `eventually_infinite_conjBin_not_conjNonempty` |
| ConjBin | monotonicity is not enough, even on a finite state type | tight: counterexample `angelic_finiteState_monotone_not_conjNonempty` |
| classical logic | needed: the statement, restricted to the one-point state type, implies excluded middle by a proof that uses no axiom. Lean's logic is classical, so no countermodel can be exhibited inside Lean; this reverse implication is the witness. | tight (logical-strength witness): `lem_of_conjNonempty_of_conjBin_of_finiteState` |

**Depth.** shallow.

**Non-vacuity witness.** Bool is finite and the wlp of skip on Bool is binary conjunctive. (`finiteState_conjBin_nonvacuous`)

**Companions and corollaries (proved in the package).** `conjBin_iff_exists_wp_of_finiteState`, `conjBin_topPreserving_iff_exists_wlp_of_finiteState`, `kernel_established_of_list`.

**Prior art.**

- No source stating this exact result for predicate transformers was located; the sources examined are those listed on the finitary-laws-not-relational card.
- B. Jonsson and A. Tarski, 'Boolean Algebras with Operators. Part I', American Journal of Mathematics 73(4):891-939, 1951, doi:10.2307/2372123, and 'Boolean Algebras with Operators' [Part II], American Journal of Mathematics 74(1):127-162, 1952, doi:10.2307/2372074; P. Blackburn, M. de Rijke, Y. Venema, 'Modal Logic', Cambridge University Press, 2001, doi:10.1017/CBO9781107050884 (bibliographic records verified; context: operators on finite Boolean algebras; the specific passages were not read)

**Design question informed.** Which laws must a verification framework demand of a weakest-precondition transformer so that every admitted transformer is the wp of some relational (possibly nondeterministic, possibly aborting) program, without excluding honest programs? For finite-state models the binary law is adequate.

**Non-claims:** see Boundaries, result 9a.

**Scope witnesses cited in the non-claims (proved in the package; statements printed under Evidence).** `relOf_eventually_finite_not_conjNonempty`, `abortT_finiteState_conjBin_not_conjAll`.

Basis: execution (Lean kernel check) — `conjNonempty_of_conjBin_of_finiteState` (axioms: `Classical.choice`, `Quot.sound`, `propext`).

#### Result 9b — `continuum-state-continuity-forces-conjunctivity`

- **Lean:** `conjNonempty_of_conjBin_of_omegaContinuous_of_continuumState` (namespace `Toy.PredTrans`).
- **Kind:** theorem. **Tier:** T2 — Wand 1977 and Plotkin 1980 (Lemma 5.6, Theorem 5.9) characterize strict, binary-meet-preserving, continuous maps on a countable state set; the statement here drops strictness and extends the state types from countable ones to those that inject into Nat -> Bool (cardinality at most that of the continuum). No source stating that generalization for predicate transformers was read; it is not claimed novel.

Statement, as printed by `#check` on the built library:

```lean
@conjNonempty_of_conjBin_of_omegaContinuous_of_continuumState : ∀ {σ : Type u_1},
  ContinuumState σ → ∀ {T : Transformer σ}, ConjBin T → OmegaContinuous T → ConjNonempty T
```

Unfolded hypothesis on the state type:
`ContinuumState σ := ∃ f : σ → Nat → Bool, ∀ x y, f x = f y → x = y`. `OmegaContinuous` is the
one-sided law over increasing `Nat`-indexed chains (definitions table).

**Plain claim.** On a state type that injects into Nat -> Bool - in particular on every countable state type, and on the uncountable type Nat -> Bool itself - every predicate transformer that is binary conjunctive and omega-continuous is conjunctive over all nonempty families. Strictness and top preservation are not assumed.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| ContinuumState (the state type injects into Nat -> Bool) | lets the state type be coded by bit sequences, so that omega-continuity bounds the splitting of the tree of 'positive' prefixes. Necessity is unknown: it is not necessary for countable state types or for Nat -> Bool (both satisfy it), and no counterexample on a larger state type is given. (Informal remark, not formalized and not checked against a source: a counterexample would yield a countably complete non-principal ultrafilter, so it cannot be constructed without large-cardinal assumptions.) With continuity over directed families no hypothesis on the state type is needed (directed-continuity-forces-conjunctivity). | unknown |
| ConjBin | monotonicity plus omega-continuity is not enough | tight: counterexample `angelic_continuum_omegaContinuous_not_conjNonempty`, `angelic_countable_omegaContinuous_not_conjNonempty` |
| OmegaContinuous | binary conjunctivity alone is not enough on an infinite state type | tight: counterexample `eventually_continuum_conjBin_not_conjNonempty`, `eventually_countable_conjBin_not_conjNonempty` |
| classical logic | needed: the statement (and already its countable special case), restricted to the one-point state type, implies excluded middle by a proof that uses no axiom. Lean's logic is classical, so no countermodel can be exhibited inside Lean; this reverse implication is the witness. | tight (logical-strength witness): `lem_of_conjNonempty_of_conjBin_of_omegaContinuous_of_continuumState`, `lem_of_conjNonempty_of_conjBin_of_omegaContinuous_of_countable` |

**Depth.** substantive.

**Non-vacuity witness.** Nat -> Bool injects into itself, is not countable, and the wp of skip on it is binary conjunctive and omega-continuous; Nat is countable and the wlp of the two-way choice is binary conjunctive and omega-continuous. (`continuum_conjBin_omegaContinuous_nonvacuous`, `countable_conjBin_omegaContinuous_nonvacuous`)

**Companions and corollaries (proved in the package).** `conjNonempty_of_conjBin_of_omegaContinuous_of_countable`, `continuumState_of_countableState`, `conjBin_omegaContinuous_iff_wp_finiteImage_of_continuumState`, `strict_conjBin_omegaContinuous_iff_wp_finiteImage_totalOn_of_continuumState`, `nat_to_bool_uncountable_conjBin_omegaContinuous_conjNonempty`.

**Prior art.**

- M. Wand, 'A characterization of weakest preconditions', Journal of Computer and System Sciences 15(2):209-212, 1977, doi:10.1016/S0022-0000(77)80006-8 (content seen: abstract only - a map on sets of states is the wp of a mechanism of bounded nondeterminacy iff it is strict, preserves binary intersections and is continuous over directed sets; for countable state sets the continuity condition may be weakened to omega-chains)
- G. D. Plotkin, 'Dijkstra's predicate transformers and Smyth's powerdomains', in Abstract Software Specifications, LNCS 86, Springer, 1980, pp. 527-553, doi:10.1007/3-540-10007-5_48 (content seen in the author's scan: denumerable state set; strict, continuous, multiplicative transformers; Lemma 5.6 (a strict, continuous, multiplicative map has a finite non-empty set of minimal elements); Theorem 5.9)
- E. W. Dijkstra, 'A Discipline of Programming', Prentice-Hall, 1976 (content seen in a scanned copy: ch. 3 Properties 1-4 and ch. 9 Property 5, the healthiness conditions combined here)
- M. B. Smyth, 'Power domains and predicate transformers: A topological view', in Automata, Languages and Programming (ICALP 1983), LNCS 154, Springer, 1983, pp. 662-675, doi:10.1007/BFb0036946 (bibliographic record verified; topological generalization of the power-domain view of predicate transformers, per its title; text not read)

**Design question informed.** Which laws must a verification framework demand of a weakest-precondition transformer so that every admitted transformer is the wp of some relational (possibly nondeterministic, possibly aborting) program, without excluding honest programs? Binary conjunctivity is adequate when paired with omega-continuity on a state space that injects into Nat -> Bool (in particular a countable one), and then it excludes unbounded nondeterminism.

**Non-claims:** see Boundaries, result 9b.

Basis: execution (Lean kernel check) — `conjNonempty_of_conjBin_of_omegaContinuous_of_continuumState` (axioms: `Classical.choice`, `Quot.sound`, `propext`).

#### Result 9c — `directed-continuity-forces-conjunctivity`

- **Lean:** `conjNonempty_of_conjBin_of_dirContinuous` (namespace `Toy.PredTrans`).
- **Kind:** theorem. **Tier:** T0 — Wand 1977 (abstract) characterizes the wp's of boundedly nondeterministic mechanisms on an arbitrary state set by strictness, binary intersections and continuity over directed sets; the statement here is the conjunctivity half of that characterization with strictness dropped.

Statement, as printed by `#check` on the built library:

```lean
@conjNonempty_of_conjBin_of_dirContinuous : ∀ {σ : Type u_1} {T : Transformer σ},
  ConjBin T → DirContinuous T → ConjNonempty T
```

Unfolded hypothesis:
`DirContinuous T := ∀ (ι : Type u) (Q : ι → Pred σ), Directed Q → ∀ s,
T (fun t => ∃ i, Q i t) s → ∃ i, T (Q i) s`, where
`Directed Q := Nonempty ι ∧ ∀ i j, ∃ k, (∀ s, Q i s → Q k s) ∧ (∀ s, Q j s → Q k s)`.
No hypothesis on the state type.

**Plain claim.** On every state type, every predicate transformer that is binary conjunctive and continuous over directed families (if it establishes the union of a nonempty directed family of postconditions, it establishes some member) is conjunctive over all nonempty families. Strictness and top preservation are not assumed.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| ConjBin | monotonicity plus directed continuity is not enough | tight: counterexample `angelic_dirContinuous_monotone_not_conjNonempty` |
| DirContinuous | binary conjunctivity alone is not enough | tight: counterexample `eventually_conjBin_not_dirContinuous_not_conjNonempty` |
| classical logic | needed: the statement, restricted to the one-point state type, implies excluded middle by a proof that uses no axiom. Lean's logic is classical, so no countermodel can be exhibited inside Lean; this reverse implication is the witness. | tight (logical-strength witness): `lem_of_conjNonempty_of_conjBin_of_dirContinuous` |

**Depth.** shallow.

**Non-vacuity witness.** On (Nat -> Bool) -> Bool, which does not inject into Nat -> Bool (so the continuum-state result does not apply), the wp of skip is binary conjunctive and continuous over directed families. (`conjBin_dirContinuous_nonvacuous_beyond_continuum`)

**Companions and corollaries (proved in the package).** `exists_wp_of_conjBin_of_dirContinuous`, `omegaContinuous_of_dirContinuous`, `finiteImage_on_term_of_dirContinuous_wp`.

**Prior art.**

- M. Wand, 'A characterization of weakest preconditions', Journal of Computer and System Sciences 15(2):209-212, 1977, doi:10.1016/S0022-0000(77)80006-8 (content seen: abstract only - strict, binary-intersection-preserving maps continuous over directed sets are exactly the wp's of mechanisms of bounded nondeterminacy)

**Design question informed.** Which laws must a verification framework demand of a weakest-precondition transformer so that every admitted transformer is the wp of some relational (possibly nondeterministic, possibly aborting) program, without excluding honest programs? On an arbitrary state space, binary conjunctivity plus continuity over directed families already forces positive conjunctivity, so it admits only relational transformers, and those are boundedly nondeterministic on their non-aborting states (finiteImage_on_term_of_dirContinuous_wp).

**Non-claims:** see Boundaries, result 9c.

**Scope witnesses cited in the non-claims (proved in the package; statements printed under Evidence).** `dirContinuous_negT`.

Basis: execution (Lean kernel check) — `conjNonempty_of_conjBin_of_dirContinuous` (axioms: `Classical.choice`, `Quot.sound`, `propext`).

### Modeling bridge

Basis: derived (modeling bridge) + source (`leanprover/lean4` at commit `5045d0056413266e57c625dcd7c365b10e377c52`, file `src/Std/Do/PredTrans.lean`, SHA-256 `f85424f0a6eb31a008e71b3686ffc69454ca5e0582aaec6832c76f0c3d77f8e9`, lines 48-49 and 63-70). None of this is kernel-checked.

- **Reading result 5 for a framework.** If a framework's transformer type is exactly the functions `(σ → Prop) → (σ → Prop)` satisfying some subset of monotonicity, binary conjunctivity, strictness and top preservation, and `σ` is infinite with an injection from `Nat`, then a transformer of the shape of `eventually` is admitted and is not the `wp` of any relational program. Reasoning: `eventually` satisfies those four laws and is no `wp` (result 5); whether the framework's own type is of that shape must be checked against its definitions. For finite state spaces, or with ω-continuity on spaces that inject into `Nat → Bool`, or with directed continuity, results 9a-9c show the binary law suffices.
- **Lean's `Std.Do` predicate transformers.** In the source above, `structure PredTrans (ps : PostShape) (α : Type u)` bundles a function `trans : PostCond α ps → Assertion ps` with exactly one law, `conjunctiveRaw : PredTrans.Conjunctive trans`, where `def PredTrans.Conjunctive (t : PostCond α ps → Assertion ps) : Prop := ∀ Q₁ Q₂, t (Q₁ ∧ₚ Q₂) ⊣⊢ₛ t Q₁ ∧ t Q₂`, i.e. binary conjunctivity; monotonicity is derived (`PredTrans.Conjunctive.mono`). By analogy with result 5 one expects this type to have inhabitants with no relational reading when the return-value type `α` is infinite. This is an expectation by analogy only: postconditions there carry exception components and assertions live in a state-indexed logic, and no such inhabitant has been constructed or checked against the `Std.Do` definitions.

## Boundaries

### Non-claims (per result)

Each list states what the result does **not** show. Names in parentheses are proved scope witnesses in the package. Those not named in any other field of `results.json` are listed per result there under `scope_witnesses_lean`, and their exact statements are printed under Evidence, "Statements of the scope witnesses cited in the non-claims, as printed by Lean".

**Result 1 — `wlp-characterization`.**

1. Does not say binary or finite conjunctivity suffices; it does not (see finitary-laws-not-relational).
2. Says nothing about termination: wlp R holds at a state without R-successors for every postcondition, and a universally conjunctive transformer need not be strict.
3. Two readings are covered and must not be conflated: wlp R as the partial-correctness weakest liberal precondition (a state without successors models guaranteed divergence) and wlp R as the total-correctness demonic update [R] = wp R True of a never-aborting program (a state without successors is a miracle). A paired (wp, wlp) semantics of a possibly aborting program is not modeled; in such a semantics wlp is not determined by wp.
4. Does not imply binary disjunctivity: wlp R distributes over disjunction only when every state has at most one R-successor; for the nondeterministic two-way choice it fails (not_disjBin_wlp_stepR).
5. relOf T is an arbitrary relation; nothing says it is computable, total, finitely branching, or denoted by a program of any particular language.
6. Equality is extensional equality of functions on predicates; nothing is claimed about syntactic or intensional identity.
7. One state type only; relations between different input and output state types are not formalized.
8. Toy model: one state type for both initial and final states, relations from states to states, a single postcondition; no return values, exceptional exits, heaps, step counting, loops or recursion; predicates and transformers are compared extensionally. Nothing is claimed about a particular verification framework until its own definitions are checked against these.

**Result 2 — `wp-characterization`.**

1. The relation is not unique: only its restriction to non-aborting start states is (wp_same_with_different_relations). Statements of this normal form that speak of 'the' relation presuppose a normalization; the one produced by relOf is the chaos normal form.
2. term (and termOf T = T True) is the non-abortion domain, not the set of states from which a final state is guaranteed: a miraculous state, with no R-successor, satisfies termOf (termOf_wlp_emptyR_no_outcome). Guaranteed normal termination in some final state is term together with TotalOn (see strict-iff-no-miracle).
3. term merges abortion, certain divergence and possible divergence: a program that may either diverge or return from s has the same wp at s as one that aborts. Equality of wp is not equality of operational behaviour from aborting states; in a paired (wp, wlp) semantics, wp alone does not determine wlp there.
4. Does not imply binary disjunctivity: wp R term distributes over disjunction only when every non-aborting state has at most one R-successor.
5. The class contains miracles and aborts on purpose; positive conjunctivity implies neither strictness nor top preservation (constT_conjNonempty_not_strict_not_topPreserving), nor omega-continuity (havocR_nat_conjAll_strict_not_omegaContinuous: havoc on Nat is universally conjunctive, hence positively conjunctive, and not omega-continuous).
6. The chaos normal form produced by relOf is not preserved by sequential composition (chaosNormal_not_preserved_by_comp).
7. No angelic nondeterminism: angelic choice is outside the class.
8. Does not say binary conjunctivity suffices; see the finite-state, continuum-state and directed-continuity results for when it does.
9. Toy model: one state type for both initial and final states, relations from states to states, a single postcondition; no return values, exceptional exits, heaps, step counting, loops or recursion; predicates and transformers are compared extensionally. Nothing is claimed about a particular verification framework until its own definitions are checked against these.

**Result 3 — `strict-iff-no-miracle`.**

1. Strictness alone implies no conjunctivity: eventually is strict and not a wp.
2. Strictness is what makes term mean 'terminates in some final state': without it, term s also holds at miraculous states (termOf_wlp_emptyR_no_outcome).
3. Under the partial-correctness reading of wlp, failure of strictness at a state without successors models guaranteed divergence (for example 'while true do skip'), not an infeasible miracle; strict_wlp_iff is about the demonic-update reading as much as about the wlp reading.
4. 'No miracle' is not 'implementable': the relation may still be uncomputable or unboundedly nondeterministic.
5. Nothing is said about the relation outside the non-abortion predicate.
6. Toy model: one state type for both initial and final states, relations from states to states, a single postcondition; no return values, exceptional exits, heaps, step counting, loops or recursion; predicates and transformers are compared extensionally. Nothing is claimed about a particular verification framework until its own definitions are checked against these.

**Result 4 — `omega-continuity-iff-bounded-nondeterminism`.**

1. Finite does not mean uniformly bounded: image sizes may grow without bound across states.
2. FiniteImage bounds the set of final states of the input/output relation, not the branching of an operational transition system: infinitely many execution paths with finitely many final states still give an omega-continuous wp; no operational semantics (and no Konig's lemma) is formalized.
3. Miracles are omega-continuous: a state in term with an empty R-image has a finite image (omegaContinuous_wp_emptyR). Omega-continuity implies neither strictness nor feasibility.
4. Nothing is constrained about R outside term: an omega-continuous wp R term may have infinite images at aborting states (omegaContinuous_wp_partial_infinite_image_outside_term).
5. OmegaContinuous is the one-sided upward (or-) continuity law for increasing chains. On its own it admits non-monotone transformers such as pointwise negation (omegaContinuous_negT_not_monotone); for monotone transformers, such as every wp, it coincides with the two-sided equation (omegaContinuous_two_sided_iff). Downward (and-) continuity over decreasing chains already holds for every wp, as a case of positive conjunctivity.
6. Omega-continuity is not necessary for being a wp: havoc on Nat is universally conjunctive and strict but not omega-continuous (havocR_nat_conjAll_strict_not_omegaContinuous).
7. Omega-continuity alone does not make a transformer relational: angelic choice is omega-continuous and not a wp.
8. Nothing is proved about loops, recursion or fixed points; the role of continuity in computing the wp of a loop is not formalized.
9. Only Nat-indexed chains are used here; continuity over directed families is defined (DirContinuous) and used only in directed-continuity-forces-conjunctivity.
10. Toy model: one state type for both initial and final states, relations from states to states, a single postcondition; no return values, exceptional exits, heaps, step counting, loops or recursion; predicates and transformers are compared extensionally. Nothing is claimed about a particular verification framework until its own definitions are checked against these.

**Result 5 — `finitary-laws-not-relational`.**

1. The example is not omega-continuous, so it does not show that Dijkstra's list (strict, monotone, binary conjunctive, continuous) fails to characterize wp; on state types that inject into Nat -> Bool that list does characterize the boundedly nondeterministic, miracle-free wp's (strict_conjBin_omegaContinuous_iff_wp_finiteImage_totalOn_of_continuumState), and with continuity over directed families the binary law suffices on every state type.
2. Whether a binary conjunctive, omega-continuous transformer that is not a wp exists on some state type that does not inject into Nat -> Bool is left open. (Informal remark, not formalized and not checked against a source: such an example would yield a countably complete non-principal ultrafilter, so it cannot be constructed without large-cardinal assumptions.)
3. Does not show that adding binary disjunctivity (T (P or Q) = T P or T Q, Dijkstra's law for deterministic mechanisms) would make the finitary laws sufficient: eventually is not binary disjunctive (not_disjBin_eventually), so this example says nothing about that longer list. (Informal remark, not formalized: membership in a non-principal ultrafilter on Nat satisfies all those laws and is not relational.)
4. No general statement about 'every finitary law' is made; exactly the listed laws (and conjunctivity over finite lists) are shown insufficient.
5. The example is not meaningless: it is an angelic choice of a threshold followed by a demonic choice (eventually_eq_angelicDemonic, eventually_iff_exists_fromN). It lies outside relational semantics only.
6. Nothing is claimed about any particular verification framework; whether a framework's own transformer type admits an analogous inhabitant must be checked against its definitions.
7. Toy model: one state type for both initial and final states, relations from states to states, a single postcondition; no return values, exceptional exits, heaps, step counting, loops or recursion; predicates and transformers are compared extensionally. Nothing is claimed about a particular verification framework until its own definitions are checked against these.

**Result 6 — `refinement-correspondence`.**

1. Refinement here is pointwise implication of wp (the total-correctness refinement order of the refinement calculus); it is not Nelson's approximation order defined from wp and wlp jointly, not an Egli-Milner order, and not trace refinement, simulation, or data refinement.
2. A refinement may delete all outcomes: a miracle refines everything, so 'refines' does not imply 'implementable'.
3. The relational criterion applies to wp-transformers only. For arbitrary transformers, inclusion of termOf and reverse inclusion of relOf on termOf do not imply refinement: magic (the demonic update of the empty relation) and eventually have the same termOf and relOf, yet magic is not refined by eventually (relational_criterion_fails_off_wp).
4. The global inclusion form needs the refined pair in chaos normal form (refinedBy_wp_global_inclusion_needs_chaosNormal), and classical logic; the restricted form needs neither.
5. Toy model: one state type for both initial and final states, relations from states to states, a single postcondition; no return values, exceptional exits, heaps, step counting, loops or recursion; predicates and transformers are compared extensionally. Nothing is claimed about a particular verification framework until its own definitions are checked against these.

**Result 7 — `wp-algebra`.**

1. seqTerm is not an independent construction: seqTerm R1 t1 t2 is definitionally wp R1 t1 t2 (seqTerm_eq_wp).
2. No loops, recursion, guards or angelic choice are treated.
3. The chaos normal form is not preserved by composition (chaosNormal_not_preserved_by_comp).
4. A demonic choice aborts wherever either alternative may abort.
5. Toy model: one state type for both initial and final states, relations from states to states, a single postcondition; no return values, exceptional exits, heaps, step counting, loops or recursion; predicates and transformers are compared extensionally. Nothing is claimed about a particular verification framework until its own definitions are checked against these.

**Result 8 — `monotone-angelic-demonic-normal-form`.**

1. Near-definitional: the multirelation of T is T itself with its arguments swapped; the statement carries no information beyond monotonicity.
2. Uniqueness holds only among up-closed multirelations: an up-closed multirelation and a non-up-closed one can induce the same transformer (upClosed_not_unique_among_all, angelicDemonic_not_injective).
3. Does not say monotone transformers have relational semantics: angelic choice and eventually do not.
4. No game semantics is formalized; 'angel' and 'demon' are readings of the existential and universal quantifiers.
5. Toy model: one state type for both initial and final states, relations from states to states, a single postcondition; no return values, exceptional exits, heaps, step counting, loops or recursion; predicates and transformers are compared extensionally. Nothing is claimed about a particular verification framework until its own definitions are checked against these.

**Result 9a — `finite-state-binary-conjunctivity-suffices`.**

1. Finiteness must hold of the whole state type, not merely of a program's reachable states or of the relation read off by relOf: relOf eventually is the empty relation, yet eventually is not positively conjunctive (relOf_eventually_finite_not_conjNonempty).
2. Nothing for infinite state types; there the conclusion fails (finitary-laws-not-relational).
3. The conclusion is positive conjunctivity (the wp class), not universal conjunctivity (the wlp class): abort on the one-point state type is binary conjunctive and not universally conjunctive (abortT_finiteState_conjBin_not_conjAll). No strictness or top preservation is obtained.
4. Toy model: one state type for both initial and final states, relations from states to states, a single postcondition; no return values, exceptional exits, heaps, step counting, loops or recursion; predicates and transformers are compared extensionally. Nothing is claimed about a particular verification framework until its own definitions are checked against these.

**Result 9b — `continuum-state-continuity-forces-conjunctivity`.**

1. ContinuumState is a sufficient hypothesis whose necessity is unknown (not proved tight). State types that do not inject into Nat -> Bool, such as (Nat -> Bool) -> Bool, are outside this theorem's hypotheses; no counterexample on them is claimed.
2. Uncountable state types are not excluded: Nat -> Bool is covered (nat_to_bool_uncountable_conjBin_omegaContinuous_conjNonempty), so countability is not necessary. The countable special case conjNonempty_of_conjBin_of_omegaContinuous_of_countable is kept as a corollary for alignment with Wand 1977 and Plotkin 1980; its hypothesis CountableState is known to be stronger than necessary.
3. OmegaContinuous is the one-sided law of the definitions; here ConjBin implies monotonicity, so it coincides with two-sided omega-continuity.
4. The conclusion is conjunctivity over nonempty families, not over all families.
5. Via the wp and continuity characterizations the representing program is boundedly nondeterministic on its non-aborting states (conjBin_omegaContinuous_iff_wp_finiteImage_of_continuumState), so this route never yields unbounded nondeterminism.
6. Toy model: one state type for both initial and final states, relations from states to states, a single postcondition; no return values, exceptional exits, heaps, step counting, loops or recursion; predicates and transformers are compared extensionally. Nothing is claimed about a particular verification framework until its own definitions are checked against these.

**Result 9c — `directed-continuity-forces-conjunctivity`.**

1. DirContinuous is a stronger hypothesis than OmegaContinuous (omegaContinuous_of_dirContinuous); this result does not remove the hypothesis on the state type from the omega-continuous version.
2. Like OmegaContinuous, DirContinuous is one-sided and does not by itself imply monotonicity (dirContinuous_negT).
3. The conclusion is conjunctivity over nonempty families, not over all families; strictness and top preservation are not obtained.
4. Only one direction of a directed analogue of omega-continuity-iff-bounded-nondeterminism is stated: a directed-continuous wp has finite images on its non-aborting states (finiteImage_on_term_of_dirContinuous_wp); the converse is not stated here.
5. Toy model: one state type for both initial and final states, relations from states to states, a single postcondition; no return values, exceptional exits, heaps, step counting, loops or recursion; predicates and transformers are compared extensionally. Nothing is claimed about a particular verification framework until its own definitions are checked against these.

### Boundaries common to all results

- **Toy model.** One state type; relations from states to states; one postcondition; no return
  values, exceptional exits, heaps, or step counting.
- **`term` is coarse.** "Not in `term`" covers abortion, certain divergence and possible
  divergence alike; the model cannot tell them apart. `term` is the non-abortion domain and
  includes miraculous states.
- **Classical and extensional.** Transformers and predicates are compared extensionally. Results
  1 and 2 (main statements) and the restricted refinement criterion do not need classical logic;
  results 3, 9a, 9b, 9c, the chaos-normal-form corollaries and the global refinement criterion
  provably do (they imply excluded middle); result 4's backward direction implies the limited
  principle of omniscience and its forward direction is proved with choice. No computational
  content is claimed.
- **No iteration.** Loops, recursion and fixed points are not modeled.
- **Unknown.** Whether the hypothesis on the state type in result 9b can be dropped (it is
  satisfied by every countable state type and by `Nat → Bool`; a counterexample would need a
  state type that does not inject into `Nat → Bool`); whether result 4's forward direction needs
  choice.
- **Relational means relational.** "Is the `wp` of a relational program" says nothing about
  computability or about expressibility in a given programming language.
- **One-sided continuity.** `OmegaContinuous` and `DirContinuous` alone do not imply
  monotonicity.

### Escape hatches

Result 5 is the package's negative result (a counterexample showing that a list of laws does not force relational semantics). It is defeated, and relational semantics is recovered, by any of the following, each proved in the package:

- a **finite** state type: binary conjunctivity then implies positive conjunctivity (result 9a), hence `wp` form (`conjBin_iff_exists_wp_of_finiteState`), and with top preservation `wlp` form (`conjBin_topPreserving_iff_exists_wlp_of_finiteState`);
- adding **ω-continuity** on a state type that injects into `Nat → Bool`, including `Nat` itself (result 9b; `conjBin_omegaContinuous_iff_wp_finiteImage_of_continuumState`); `eventually` fails ω-continuity (`not_omegaContinuous_eventually`);
- adding **continuity over directed families** on any state type (result 9c; `exists_wp_of_conjBin_of_dirContinuous`); `eventually` fails it (`eventually_conjBin_not_dirContinuous_not_conjNonempty`);
- demanding **conjunctivity over all nonempty families** instead of the binary law (result 2).

Not an escape hatch as far as this package shows: adding binary disjunctivity. `eventually` is not binary disjunctive (`not_disjBin_eventually`), so result 5 says nothing about that longer list; an informal, unformalized remark in result 5's non-claims indicates it would not suffice either.

### Hypotheses of unknown tightness

- **Result 4**, forward direction (ω-continuity implies finite image): the proof uses the axiom of choice to extract an injective sequence from an image contained in no list; whether choice or excluded middle is needed for this direction is **unknown**. (The backward direction provably needs a non-constructive principle: it implies LPO, `lpo_of_finiteImage_imp_omegaContinuous_wp`.)
- **Result 9b**, `ContinuumState σ`: whether the hypothesis on the state type can be dropped is **unknown**. It is satisfied by every countable type and by `Nat → Bool`; a counterexample would need a state type that does not inject into `Nat → Bool`. An informal remark, not formalized and not checked against a source, suggests such a counterexample would yield a countably complete non-principal ultrafilter. With directed continuity instead of ω-continuity no hypothesis on the state type is needed (result 9c).

### Not covered by the package

- The converse of `finiteImage_on_term_of_dirContinuous_wp`: only "a directed-continuous `wp` has finite images on its non-aborting states" is stated; the other direction of a directed analogue of result 4 is not stated here.
- Loops, recursion and fixed points; the role of continuity in computing the `wp` of a loop.
- Paired `(wp, wlp)` semantics, return values, exceptional postconditions, and relations between different input and output state types.

### Disproved or dropped statements

None. Every statement referenced in `results.json` is proved exactly as stated, and no result was removed from the package.

## Evidence

### Kernel-check record

- **Toolchain:** `leanprover/lean4:v4.34.1`, GitHub repository `leanprover/lean4`, tag `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52` (tag commit read from the GitHub API; the local toolchain reports the same commit in `lean --version`).
- **Build:** `lake build` of a fresh copy of `lean/` succeeds with no warnings and no `sorry`.
- **Declaration sweep (`audit/axioms.json`):** 300 non-internal declarations of the `ToyPredTrans` modules audited with `Lean.collectAxioms`; no `axiom` or `opaque` declarations; no `sorry`, `admit`, `native_decide`, `implemented_by`, `@[extern]`, `unsafe` or `debug.skipKernelTC` in the sources. Footprints: 147 declarations use no axiom, 125 use exactly `propext` and `Quot.sound`, 28 use `propext`, `Classical.choice` and `Quot.sound`.
- **Statement hashes (`audit/statements.json`):** 76 declarations referenced by the cards (results, counterexamples, logical-strength witnesses, non-vacuity witnesses, positive controls). `statement_sha256` is the SHA-256 of `toString (repr ci.type)`; `closure_sha256` is the SHA-256 of the newline-joined, sorted list of entries `name : repr type [:= repr value]` for every package constant reachable from the statement's type (values are included for definitions, not for theorems). A changed definition therefore changes the closure hash of every statement that mentions it.
- **Observation date:** 2026-11-20 (build, audit, DOI and commit checks).

### Axiom footprints of the main theorems

| Result | Theorem | Axioms |
|---|---|---|
| 1 | `conjAll_iff_eq_wlp_relOf` | `Quot.sound`, `propext` |
| 1 | `relOf_wlp` | `Quot.sound`, `propext` |
| 2 | `conjNonempty_iff_eq_wp_relOf_termOf` | `Quot.sound`, `propext` |
| 2 | `relOf_wp` | `Quot.sound`, `propext` |
| 2 | `wp_eq_wp_iff` | `Quot.sound`, `propext` |
| 3 | `strict_wp_iff_totalOn` | `Classical.choice`, `Quot.sound`, `propext` |
| 4 | `omegaContinuous_wp_iff_finiteImage_on_term` | `Classical.choice`, `Quot.sound`, `propext` |
| 5 | `eventually_finitary_laws_not_relational` | `Quot.sound`, `propext` |
| 6 | `refinedBy_wp_iff` | none |
| 6 | `refinedBy_wp_iff_of_chaosNormal` | `Classical.choice`, `Quot.sound`, `propext` |
| 7 | `wp_comp` | `Quot.sound`, `propext` |
| 7 | `wlp_comp` | `Quot.sound`, `propext` |
| 7 | `wp_union` | none |
| 7 | `wlp_union` | none |
| 8 | `monotone_iff_eq_angelicDemonic_multirelOf` | `Quot.sound`, `propext` |
| 8 | `multirelOf_angelicDemonic_eq_iff` | `Quot.sound`, `propext` |
| 9a | `conjNonempty_of_conjBin_of_finiteState` | `Classical.choice`, `Quot.sound`, `propext` |
| 9b | `conjNonempty_of_conjBin_of_omegaContinuous_of_continuumState` | `Classical.choice`, `Quot.sound`, `propext` |
| 9c | `conjNonempty_of_conjBin_of_dirContinuous` | `Classical.choice`, `Quot.sound`, `propext` |

These match the ledgers: results 1 and 2 and `refinedBy_wp_iff` use no `Classical.choice` (`harmless` rows); the theorems whose ledgers mark classical logic `tight` use it.

### Hashed declarations

| Declaration | Card role (result, role) | Axioms | Closure size | `statement_sha256` | `closure_sha256` |
|---|---|---|---:|---|---|
| `abortT_conjNonempty_not_wlp` | 1 tightness | none | 7 | `4e60d000cc820afdd144a39861204ca27635e094dff93838491b76fde244e28c` | `ce6a76e292055a9cc3a91b3dba7bd6301468ef5e1129ac25266eb8eb1270a7ed` |
| `angelic_continuum_omegaContinuous_not_conjNonempty` | 9b tightness | `Quot.sound`, `propext` | 8 | `1cfdf78d43187d41b76e19b7fab39fa95b6591a302acc1df13a309ca75f255b2` | `8966d6c006916e34eebf09426641b383f9d78cb5ece5aff76dd83633a03accbf` |
| `angelic_countable_omegaContinuous_not_conjNonempty` | 9b tightness | `Quot.sound`, `propext` | 8 | `d49eb5a1cc0d6b3e4982534d958d7d0a1af9aa90e917c51f92209c821abd07d1` | `a694f1627a7b6ce6ce67378d555f8685223019c82a7aedf24098e84d0126685e` |
| `angelic_dirContinuous_monotone_not_conjNonempty` | 9c tightness | `Quot.sound`, `propext` | 7 | `5b4c029ba3a59df95aa61fcbc15001c377834b92616d8524f12128655e12d5a4` | `3906194deb96c07d4ac52567efdb6a22f282150d2a51164941d5929bd247a2e2` |
| `angelic_finiteState_monotone_not_conjNonempty` | 9a tightness | `Quot.sound`, `propext` | 6 | `74d3ba69cbc50afe84cb41cd01afae9e9c1fdba8353e56b82da4b5cae8ff6cab` | `87aca355f6c90f0d2c3bf1d5c957e720956260d00e1af7794270ff0750575bd2` |
| `angelic_laws_not_wp` | 2 tightness | `Quot.sound`, `propext` | 11 | `5bf2d1bb33b93791864ccac732bf6a7372ea407f3863df46cf88afe5d7134361` | `4d2595c21cd67ab53d795fa40698bfc5b109cacfd8a24bb377156dcda3fb5b1f` |
| `conjAll_iff_eq_wlp_relOf` | 1 main | `Quot.sound`, `propext` | 6 | `6dac3b5e854e008b4e7e0552e4601a70656e3be79f638fa990e6ce5e6bd74c6b` | `c4888aff831377c391f8f9b139b47c963335b3c9a7237a935df786dffc6c6af8` |
| `conjAll_wlp_stepR_and_not_conjAll_eventually` | 1 non-vacuity | `Quot.sound`, `propext` | 7 | `07c57873cf43c030cf94c40db4419ac1479fa76c19a783fe07be1e1958d48044` | `263fe949e6a762ff505a258aeeba9904520dc569c7d47d48cf91fa6a3fcc0def` |
| `conjBin_dirContinuous_nonvacuous_beyond_continuum` | 9c non-vacuity | `Classical.choice`, `Quot.sound`, `propext` | 10 | `5ba226bb147692b851f0168cc7c0802d173e1c15dba57afe09ac1d5748ea809d` | `9ba8889b0595d304f2b350d4936c12a284f4e2eeb4b133b89c868e59f969c32d` |
| `conjNonempty_iff_eq_wp_relOf_termOf` | 2 main | `Quot.sound`, `propext` | 8 | `ce0b792b1902912f315af8e0e80b7fd20aa4d529e2a5ab058390bccc40e0fe45` | `a5c05d1fafcdcaca0f2ceb725fc31bf9f9ffa585f72e7a5cd80caed382ca8e2e` |
| `conjNonempty_of_conjBin_of_dirContinuous` | 5 tightness; 9c main | `Classical.choice`, `Quot.sound`, `propext` | 6 | `17e75ee475242c9dd5d7e536108c298bd7e2a60e096e6b00dbfc3763797ccd8d` | `f2a651c164170b4d693896ad28fc7be4c175594ba66738a29ac9ba739e4a9f07` |
| `conjNonempty_of_conjBin_of_finiteState` | 5 tightness; 5 positive control; 9a main | `Classical.choice`, `Quot.sound`, `propext` | 5 | `16c3f9c0f18c08af322262f8f35438a499b0c96c564cd16dd68342b95f832e73` | `9cc1e90d5bd4aa97fb15e78c30b733917cc744805b3416f66e36bb54e809d8eb` |
| `conjNonempty_of_conjBin_of_omegaContinuous_of_continuumState` | 5 tightness; 9b main | `Classical.choice`, `Quot.sound`, `propext` | 7 | `464466ab00e0596ca12e078284dd6407817bcb4eaa093da41970ed84f87f1bf5` | `dd51bf798cca499c62b9504c07a19a39bdac30de87f7e83c6ed53afa7ec91468` |
| `conjNonempty_wp_predR_posP_and_not_conjNonempty_eventually` | 2 non-vacuity | `Quot.sound`, `propext` | 9 | `a10c095409c9f50d7e3e0dfae262208b5fd08f6a9cb2fb73d8af757a607a951a` | `2797aac064a782ec460a016071b6d774dd85bb35bcac72fa7f467b3093ea6546` |
| `continuum_conjBin_omegaContinuous_nonvacuous` | 9b non-vacuity | `Classical.choice`, `Quot.sound`, `propext` | 11 | `986ebfb0585268f18d59e29178ff3f9f842d0487771a1b48adf8afcfc3066ea0` | `13d4b2be8644c37f35d1ca2f1ed5052418c9b3faa82dae11454e54165d5d3002` |
| `countable_conjBin_omegaContinuous_nonvacuous` | 9b non-vacuity | `Quot.sound`, `propext` | 9 | `3d8f75ac5f3fc646afe306442f56bba8732ecda2ec0e282be9095a8f4673b912` | `8a9dbb7dd9679b243abe62c51c9cee2c27d3d414a79bd05d48057300e2db9896` |
| `eventually_conjBin_not_dirContinuous_not_conjNonempty` | 5 tightness; 9c tightness | `Quot.sound`, `propext` | 7 | `98970ec554fa9c6f2a33f42564fb96bbf01f4457cf9588584e9424d7d223a2b0` | `a3fe1edf6b6b770a6a381944b7830aa26e120a6b6d69ca6d1f2c2624935f3791` |
| `eventually_conjList` | 5 non-vacuity | `Quot.sound`, `propext` | 3 | `d6abb076e6e5dec60bab1d56a28032914d556ab68b13d57e7fd0bd60d8fb06f0` | `648da457a87771d8f960266fe5b0c688dfd54bd708e4e04f82d93ada9ace8395` |
| `eventually_continuum_conjBin_not_conjNonempty` | 9b tightness | `Quot.sound`, `propext` | 6 | `561e409926c5f9d23709bebac33557f0f076c1cd78ca223002808897bae55a24` | `05c08b4a4612213a46227123f41737aa944c6c383b5e10642a3a797ce0727a06` |
| `eventually_countable_conjBin_not_conjNonempty` | 9b tightness | `Quot.sound`, `propext` | 6 | `65d99112cfaff32e43b08c1cb3160ecfa4da36e4f14d94ed07cf4e78903347da` | `8fb240a05ce313873028f4af3ec7d43b3fe33b74c50e2bf0460012f5a447fddb` |
| `eventually_eq_angelicDemonic` | 8 non-vacuity | `Quot.sound`, `propext` | 4 | `0683d83a714699006315ac67cb5bdc541cec6594e34e801bf7e0dcf50694fd31` | `de99fc595b939be7010cf8dc3d979cfc69a4eba53431814074e43a3ded8ff048` |
| `eventually_finitary_laws_not_relational` | 1 tightness; 2 tightness; 5 main | `Quot.sound`, `propext` | 13 | `d229f8c2b498c82e6a6176fee3e9f6c6b41a7b724cdf9e871a93ccd17ebb51e2` | `6321174334d6f436cfff7fe306dccc3e5d47c750d51c7b018a7e2954b856c8fd` |
| `eventually_iff_exists_fromN` | 5 positive control | none | 4 | `ced0eb1496c1ccbdd416ef3959ae44d1729ab8c031ac58c404ba409507be38a0` | `b6410ab1391590da6b30479c2193fa546b47cd9dc740446309e772ae5bdd8b39` |
| `eventually_infinite_conjBin_not_conjNonempty` | 5 tightness; 9a tightness | `Quot.sound`, `propext` | 6 | `968546a5ec2dddb2d259f76b19719f43a982688a28d0b6abb8d160c3ad1c8515` | `0b93e0dd1810aa4ec0d7a48011af0fb5aed647c41663b04874d3a6e9734dd145` |
| `finiteState_conjBin_nonvacuous` | 9a non-vacuity | `Quot.sound`, `propext` | 7 | `8109adfa6bbad86c0d272bd100ad99e0cff33245f0efcfbc84f473703e9d97f5` | `5ccce8e6998ef2f42480b36ca2b9fd41056743ceec4b9e3d6a59eaa250824bdd` |
| `fromN_eq_wlp` | 5 positive control | `Quot.sound`, `propext` | 5 | `ad22647c9c335e8c768fb94c6d6342f63715366d02f1eba5b6e3d8cade436c43` | `8bd45e4e7432b4dc553e1b3a2d4da0f852ba04ba88d7a3f540e7cf635584746e` |
| `lem_of_chaosNormal_unique_of_wp_eq` | 2 tightness | `Quot.sound`, `propext` | 6 | `0f09eb77e1b2af1670bbf125d33f0287dc7c27506129352da2dd37e0d7ddba5d` | `91d5d7fbc6e8407070bce34427ef3ed9d9c777f87b61ddaffd260a5f76d5a61b` |
| `lem_of_conjNonempty_of_conjBin_of_dirContinuous` | 9c tightness | none | 6 | `fe8e20d71ee1ee6ad3ca945c3253317da8016ccbecc7f875ee7fd6d5ad69debc` | `f2a651c164170b4d693896ad28fc7be4c175594ba66738a29ac9ba739e4a9f07` |
| `lem_of_conjNonempty_of_conjBin_of_finiteState` | 9a tightness | none | 5 | `dd5207f15e3245b33a2509ed4fc6715ee46e789946872964dbeb8c826e63d964` | `9cc1e90d5bd4aa97fb15e78c30b733917cc744805b3416f66e36bb54e809d8eb` |
| `lem_of_conjNonempty_of_conjBin_of_omegaContinuous_of_continuumState` | 9b tightness | none | 7 | `36d5c41ef8ddb71e7e302ceab5367b64c3b22eb44c493415bb51786e2015e036` | `dd51bf798cca499c62b9504c07a19a39bdac30de87f7e83c6ed53afa7ec91468` |
| `lem_of_conjNonempty_of_conjBin_of_omegaContinuous_of_countable` | 9b tightness | none | 7 | `70b382ec80db42e42a3275da83b4a09d90f4d37161a077e00814352785ecbe48` | `02ca2eebaa7701378e3d2d3c4f5513c77bc7528689f1d0eeffd20f5198da40d4` |
| `lem_of_refinedBy_wp_iff_of_chaosNormal` | 6 tightness | none | 7 | `3895b203327c4f35330c88a03c2e5fade237e9215ab86340e377991353d52d8a` | `9455bf21b590f537a799f8cc7c2dea2074b2830795d64afaf6ccff5ce7b5f139` |
| `lem_of_relOf_wp_of_chaosNormal` | 2 tightness | none | 7 | `3c415ae47e56bcafc6e3de6d78d60c57a8c5db1cd528b74962d04cba3df06576` | `a2505456660a883733c9f130eb560c42e3f11a8a7c2be9cc38fada225461d262` |
| `lem_of_strict_wlp_iff` | 3 tightness | none | 5 | `f40c58824e96dd909df082777632d808cd27ad3a6d67bbddfc6bfc00f8ec388b` | `1a3eff61817c11a95503f61ca155ff085c065b72ce3054d68f07cb8d47c65605` |
| `lem_of_strict_wp_iff_totalOn` | 3 tightness | none | 7 | `2c8eaea9da82a16811f6d01775fa0cb103a102a2bdf8fe3f118b4d703395069c` | `bb32657a5e88f5adb2045245ba8e3613ee7cc869b043c9613e59cb71c90772f7` |
| `lpo_of_finiteImage_imp_omegaContinuous_wp` | 4 tightness | none | 8 | `2fc746f85d4bbfdff8e59c9cbec1a1d6a72141396497b41ad5f87a02249c127a` | `c93a690c9f271f5d77fa9411964c5977f907e8a5b27a3d4e2d126a7b8c480505` |
| `monotone_angelicDemonic_both_sides_occur` | 8 non-vacuity | `Quot.sound`, `propext` | 7 | `8bb2a4887386548ea125e7aa445312299f3172c33b48ca906dfa039a71bdf42c` | `967cc7aa602138ef835bff8f42f0652a154c9739e56f503c3aed13cf196a096b` |
| `monotone_iff_eq_angelicDemonic_multirelOf` | 8 main | `Quot.sound`, `propext` | 5 | `7b918928d0de355d84b65d6beb1ce3eaa0942b80e50c976cac05c329972dfd79` | `8c4c6ac9ca8703806267c8140445625c4c7d026a5e9fd31a4802161d85fd0a74` |
| `multirelOf_angelicDemonic_both_sides_occur` | 8 non-vacuity | `Quot.sound`, `propext` | 5 | `5288836593fa6f7f5eda7e77ee9487ad42a584b2c44279c789563b70c6f9db19` | `60024ce1886a4892e0517ffa7a847da519b274914fd0f6a943a96630803b7393` |
| `multirelOf_angelicDemonic_eq_iff` | 8 main | `Quot.sound`, `propext` | 5 | `5fb490e9612bae12062ef570fbd1e9da35f91f954b21c12d28f4579aff77bfb3` | `60024ce1886a4892e0517ffa7a847da519b274914fd0f6a943a96630803b7393` |
| `negT_not_monotone_not_angelicDemonic` | 8 tightness | none | 5 | `d253d99364c74108ec0ac20031fd14caea90546c11f42e423f77e1183ab069c9` | `e4e684a627b66961aab0d9a02dd9436907b64dbe0f8026e6e13ab0507c01a7b1` |
| `negT_not_monotone_not_wp` | 2 tightness | none | 7 | `9e55e8ef0c5dea3506bb82416a9e3941de004800da2cb272913deb4b740361e6` | `cab1d736f3779c1b9421586fc7f6bd9483ab8f50b7b7e8dd6823311165b23889` |
| `not_continuous_on_arbitrary_families_stepR_canonical` | 4 tightness | `Quot.sound`, `propext` | 9 | `687eb48817cf113a2bfd8385ae540413bf6278fe15c8ad1ce17dc186430402dc` | `f7fe718725312a477069da40e9faa9b60cc9209eff1299ee609b455d1c680891` |
| `not_omegaContinuous_eventually` | 5 tightness | `Quot.sound`, `propext` | 5 | `4a1c88716749b6d59c29f878b33f40f6fd4b4177fb50a77bfd5cceb8ccc856ef` | `69b9b1a5debd27df6e6b38d48fd03057c38419151056f46ae79458ddcd3bfa4f` |
| `not_upClosed_not_recovered_by_multirelOf` | 8 tightness | `Quot.sound`, `propext` | 5 | `837df33f9cd7703071b7e14eb8c0aca1e6eac3ce54486e929fa4207c55b351bd` | `60024ce1886a4892e0517ffa7a847da519b274914fd0f6a943a96630803b7393` |
| `omegaContinuous_wp_both_sides_occur` | 4 non-vacuity | `Quot.sound`, `propext` | 10 | `5322a4249c0ec8f95362b9b47d9200499a38fb28e92425e8a3dd8f82b2db20ff` | `62f4090e0683cf385fc68eb2b5b01e41639af0628fe80afd2202c103b127118b` |
| `omegaContinuous_wp_iff_finiteImage_on_term` | 4 main | `Classical.choice`, `Quot.sound`, `propext` | 8 | `3b5d253d7cbcc48597b85b08a2de4cac97390dd05ea72340ae531576f654eb44` | `c93a690c9f271f5d77fa9411964c5977f907e8a5b27a3d4e2d126a7b8c480505` |
| `omegaContinuous_wp_partial_both_sides_occur` | 4 non-vacuity | `Quot.sound`, `propext` | 11 | `b61afc4a9635610a46ea720f77546291900e370e47399d411c85fc757f61d2f8` | `581c71b049ee5be8420279007fb79013b87813e5dc2857cc60232b6ef801554f` |
| `omegaContinuous_wp_partial_infinite_image_outside_term` | 4 tightness | `Quot.sound`, `propext` | 10 | `15171eababd4cd3111e2373303621a1d8a7db7b32b8e61eaccaa496f658e5025` | `3c30257bea9dc95572e71f9601295b73306883ec1f0f3fa68bd8c14609d2ea17` |
| `omegaContinuous_wp_with_infinite_image_outside_term` | 4 tightness | `Quot.sound`, `propext` | 9 | `08370e7b59870ea4ab40d2f4cba1d24e76bf12d04d7824e755f7574440b1de4d` | `e1017dca63198fcda2c9e14c05357563c8870bc96e72448101564edeb8b1da14` |
| `refinedBy_wp_both_sides_occur` | 6 non-vacuity | `Quot.sound`, `propext` | 8 | `b7319bfc36ab878f201e275d1575f246cb7d141a794b52e122d9447ed8fe28c8` | `050a820ef90ad6412a9b43e971ce4601befaf74ae10a1d0d1358569f82be15d0` |
| `refinedBy_wp_chaosNormal_partial_nonvacuous` | 6 non-vacuity | none | 9 | `dc9d11e2510bd5a7f8d9e95941329a682eb351012f9026ef0b6b5f85900cd2a3` | `f776f788741a4432ecfe93b9fb3e1a06396bb8955d16a7dece2a1bb6086f49e0` |
| `refinedBy_wp_global_inclusion_needs_chaosNormal` | 6 tightness | none | 9 | `9b93627e0939a7ae019198f5c72aad1aa9133cae15b7619ff8ea945eee87f777` | `3d5a140cd98a68faf3b587daf448f26311914b6748d0c7bb04f97232800e48f9` |
| `refinedBy_wp_iff` | 6 main | none | 6 | `e654c7545e897877565601fb450ecfd7a1beadde79038dd9bd31d02cf2d8d60b` | `5ed5eb88d542cc04cfde54bc33baa6e188d87ab4eeff9ca5875ac7caa4cb5bde` |
| `refinedBy_wp_iff_of_chaosNormal` | 6 main | `Classical.choice`, `Quot.sound`, `propext` | 7 | `07b16aa72af236766244013feb0c6a95fe884ebd4efc0716c251e06092f2506c` | `9455bf21b590f537a799f8cc7c2dea2074b2830795d64afaf6ccff5ce7b5f139` |
| `refinedBy_wp_partial_both_sides_occur` | 6 non-vacuity | none | 8 | `90144140646f90886d099860e9079d35f92e77b0f007ad6f0f0739703c2cb0b2` | `f81443cb9975e29e56f6e487533a33b6af260fccb8ae55d2fc7b615ffcc425c6` |
| `refinedBy_wp_without_global_relation_inclusion` | 6 tightness | none | 8 | `40cd6fa3c062e939c9921fd0d1aadd8d7ea97928c1562c943f72310a4feb9988` | `e10df583f5f8aee4ae1291d611f53bfb7c7b16534236199fb9ce80c02ef9baf6` |
| `relOf_wlp` | 1 main | `Quot.sound`, `propext` | 5 | `f2a4be4a8f9df496208a68462205a52c312f01f3e02ca2dc80dfaf8afbedbdd5` | `537022bc3de982fece4533ca5ecbd9fd6d18a62312f7dc26b910b73ce899ad95` |
| `relOf_wlp_skipR` | 1 non-vacuity | `Quot.sound`, `propext` | 6 | `6ab26828f62dc33b4196d48e915c7134500203aa37d3f54a558954098ca10ff2` | `840f5feeb98975a5aff31032d3e46e28c962df975041d8d5a731c9106bfaa0e2` |
| `relOf_wp` | 2 main | `Quot.sound`, `propext` | 6 | `907a1e409de290ed7543069c16ea8a46b566dc4651f5f9ff51f1d4381ccdd176` | `77b332297a2282b0e46cef4ff73f75fc000c367ecb2e0bd502ba402a769317b0` |
| `relation_inclusion_without_term_inclusion_not_refinedBy` | 6 tightness | none | 8 | `65b38ccddf411d2716e55e43fe661c84d758be336843298b0a3e3b382673c254` | `afb6e8d08617e78570750782fdd9fc8b9d2daca1df7e3f389fcd6798a19a6378` |
| `strict_wp_both_sides_occur` | 3 non-vacuity | `Quot.sound`, `propext` | 9 | `0cd1b7df3db5cd41d48d3b05eca50dd7ca27d81504e3cdc50e751df8487927ba` | `6f589e5624f577552417ef8447b63ddf519945ba50aec9cd511e6725f9816f2e` |
| `strict_wp_iff_totalOn` | 3 main | `Classical.choice`, `Quot.sound`, `propext` | 7 | `ab7ced7ebe0c13a2727b89e85ce5bd223bae9e7757dda4e51634ea2d4e57e84e` | `bb32657a5e88f5adb2045245ba8e3613ee7cc869b043c9613e59cb71c90772f7` |
| `strict_wp_without_total_relation` | 3 tightness | `Quot.sound`, `propext` | 8 | `5669aa031c8cbbad8abdcb25a8ffd00a818d3c1991a9cb4c0814fe9184994c1a` | `a619559baffd017cf795826568963bca6234f30ee73aafff6cd6d875bdcfb184` |
| `wlp_comp` | 7 main | `Quot.sound`, `propext` | 5 | `9d7536cbcfcf0ddde580dca5ecd5388a27b87d2d1fe201e0418863972ceed99a` | `e20ca68c7afef0c5829e8658b2a00fbed206751b62e4b3272f84ee7a27b176b9` |
| `wlp_union` | 7 main | none | 5 | `e6abdd0aaee5d632d66f123787d3845289d6e75dbe6a868a849ab5c2426b666f` | `274b02d3e8d878ca2c5f4dbd729aa1c0e13dc7b0201d95f5391c3235d874291c` |
| `wp_comp` | 7 main | `Quot.sound`, `propext` | 7 | `6fff36d7577e008fe18a6e52ea2a408a0f4ddec6a66d1422eeb9a12b41a6b6c9` | `d80c454618e642b950b82a9003c6b0c9564e7f1049c51dececf055f85aa937e8` |
| `wp_comp_conj_term_wrong` | 7 tightness | `Quot.sound`, `propext` | 8 | `671804fd03e802f95e4444b0ce911999c5df9841e6ba2a9da7fb14bdddb35f89` | `a0471301120b59e2877398037c765462b49c48a2e1cb0903df64136a4e6b7a75` |
| `wp_comp_example` | 7 non-vacuity | `Quot.sound`, `propext` | 10 | `f57747fa9c5e54c856889b8ca835c2a2dedc601205849b84de1bb613d1c07e67` | `4bb286a5f622a2f6f456eb490b93e5cd5a7faeb08c5b22baf7c2bf74762b4008` |
| `wp_comp_first_term_wrong` | 7 tightness | none | 7 | `4b45ded9003fba83453ecebfa7e6c08c1b8cdb20a613ba5760181fdfb7aeb93d` | `7d71989ed624d8bf66f07753d1ee65e7a9fd7a1c6c7e8d06ccd4fc67c15f4c2f` |
| `wp_eq_angelicDemonic` | 8 non-vacuity | `Quot.sound`, `propext` | 6 | `574d5d6b9618d8436cf44f20d5ae143a6f23fed73474a091e6e60ffe4225312c` | `23d74582ccb7c44a0a1d6104f240a061a734be78c4200745ba7df7b30986c201` |
| `wp_eq_wp_iff` | 2 main | `Quot.sound`, `propext` | 5 | `8257650ae71cb20ab0d1cb3c5a97ef7e2ba35e8a83ea87195e21f6f00a2d7076` | `467ffe37883c861b69506d8a9d833c685b570a13d78e877ff80fab8e94ef4920` |
| `wp_predR_posP_conjNonempty_not_wlp` | 1 tightness | none | 8 | `216cdb78f1ed23a81d576acb51a9a99610f35e12f4fbd13ea9d666eb5b6324a6` | `1ed59f1b856f5a86bbe5ca6244661a6524a7e44861a421dd26e2f31dcba668d1` |
| `wp_same_with_different_relations` | 2 tightness; 2 non-vacuity | `Quot.sound`, `propext` | 7 | `c5ec6374ec97bab349f2d6ad6d5b5aab909e3e0a646f5852bd8fdca02824e915` | `addbb55623c4593e54c0190253ba9019f35010b896d25912b49fea4fe527165a` |
| `wp_union` | 7 main | none | 6 | `557f6c8cb0612139a4f797a1d69d247e1a79c54184d1dbce84469923bb0d341a` | `e8eb2ffd6d29d5aa90f5853aa2fd7e4c3909dce3d52d95e585f8296d4316eb07` |
| `wp_union_disj_term_wrong` | 7 tightness | none | 7 | `82e0ec3b64fe97ea569069ff91eb610bf5511800cc3dfa7672956fbe0b3e15c7` | `631a8267fe7c34bc28a36206f9a5a3bf8b74921329e864b906a8c82f14b950f2` |

### Statements of all referenced declarations, as printed by Lean

Output of `#check @name` (with `open Toy.PredTrans`) on the built library, for every declaration named in the `lean`, `corollaries_lean`, `nonvacuity_witness_lean` and `positive_control_lean` fields and the hypothesis `counterexample` fields of `results.json` (main results, counterexamples, witnesses, controls, corollaries), unedited. The declarations in the `scope_witnesses_lean` fields are printed in the next subsection.

```lean
@conjAll_iff_eq_wlp_relOf : ∀ {σ : Type u_1} (T : Transformer σ), ConjAll T ↔ T = wlp (relOf T)
@relOf_wlp : ∀ {σ : Type u_1} (R : Rel σ), relOf (wlp R) = R
@conjNonempty_iff_eq_wp_relOf_termOf : ∀ {σ : Type u_1} (T : Transformer σ),
  ConjNonempty T ↔ T = wp (relOf T) (termOf T)
@relOf_wp : ∀ {σ : Type u_1} (R : Rel σ) (term : Pred σ), relOf (wp R term) = fun s s' => term s → R s s'
@wp_eq_wp_iff : ∀ {σ : Type u_1} (R R' : Rel σ) (term term' : Pred σ),
  wp R term = wp R' term' ↔ term = term' ∧ ∀ (s : σ), term s → ∀ (s' : σ), R s s' ↔ R' s s'
@strict_wp_iff_totalOn : ∀ {σ : Type u_1} (R : Rel σ) (term : Pred σ), Strict (wp R term) ↔ TotalOn R term
@omegaContinuous_wp_iff_finiteImage_on_term : ∀ {σ : Type u_1} (R : Rel σ) (term : Pred σ),
  OmegaContinuous (wp R term) ↔ ∀ (s : σ), term s → FiniteImage R s
eventually_finitary_laws_not_relational : Monotone eventually ∧
  ConjBin eventually ∧
    TopPreserving eventually ∧
      Strict eventually ∧
        ¬OmegaContinuous eventually ∧
          ¬ConjNonempty eventually ∧ (¬∃ R, eventually = wlp R) ∧ ¬∃ R term, eventually = wp R term
@refinedBy_wp_iff : ∀ {σ : Type u_1} (R₁ R₂ : Rel σ) (t₁ t₂ : Pred σ),
  RefinedBy (wp R₁ t₁) (wp R₂ t₂) ↔ (∀ (s : σ), t₁ s → t₂ s) ∧ ∀ (s : σ), t₁ s → ∀ (s' : σ), R₂ s s' → R₁ s s'
@refinedBy_wp_iff_of_chaosNormal : ∀ {σ : Type u_1} {R₁ R₂ : Rel σ} {t₁ t₂ : Pred σ},
  ChaosNormal R₁ t₁ → (RefinedBy (wp R₁ t₁) (wp R₂ t₂) ↔ (∀ (s : σ), t₁ s → t₂ s) ∧ ∀ (s s' : σ), R₂ s s' → R₁ s s')
@wp_comp : ∀ {σ : Type u_1} (R₁ R₂ : Rel σ) (t₁ t₂ : Pred σ),
  wp (comp R₁ R₂) (seqTerm R₁ t₁ t₂) = fun Q => wp R₁ t₁ (wp R₂ t₂ Q)
@wlp_comp : ∀ {σ : Type u_1} (R₁ R₂ : Rel σ), wlp (comp R₁ R₂) = fun Q => wlp R₁ (wlp R₂ Q)
@wp_union : ∀ {σ : Type u_1} (R₁ R₂ : Rel σ) (t₁ t₂ Q : Pred σ) (s : σ),
  wp (union R₁ R₂) (fun s => t₁ s ∧ t₂ s) Q s ↔ wp R₁ t₁ Q s ∧ wp R₂ t₂ Q s
@wlp_union : ∀ {σ : Type u_1} (R₁ R₂ : Rel σ) (Q : Pred σ) (s : σ), wlp (union R₁ R₂) Q s ↔ wlp R₁ Q s ∧ wlp R₂ Q s
@monotone_iff_eq_angelicDemonic_multirelOf : ∀ {σ : Type u_1} (T : Transformer σ),
  Monotone T ↔ T = angelicDemonic (multirelOf T)
@multirelOf_angelicDemonic_eq_iff : ∀ {σ : Type u_1} (A : σ → Pred σ → Prop),
  multirelOf (angelicDemonic A) = A ↔ UpClosed A
@conjNonempty_of_conjBin_of_finiteState : ∀ {σ : Type u_1},
  FiniteState σ → ∀ {T : Transformer σ}, ConjBin T → ConjNonempty T
@conjNonempty_of_conjBin_of_omegaContinuous_of_continuumState : ∀ {σ : Type u_1},
  ContinuumState σ → ∀ {T : Transformer σ}, ConjBin T → OmegaContinuous T → ConjNonempty T
@conjNonempty_of_conjBin_of_dirContinuous : ∀ {σ : Type u_1} {T : Transformer σ},
  ConjBin T → DirContinuous T → ConjNonempty T
abortT_conjNonempty_not_wlp : ConjNonempty abortT ∧ Strict abortT ∧ ¬∃ R, abortT = wlp R
wp_predR_posP_conjNonempty_not_wlp : ConjNonempty (wp predR posP) ∧ ¬∃ R, wp predR posP = wlp R
conjAll_wlp_stepR_and_not_conjAll_eventually : ConjAll (wlp stepR) ∧ ¬ConjAll eventually
@relOf_wlp_skipR : ∀ {σ : Type u_1}, relOf (wlp skipR) = skipR
angelic_laws_not_wp : Monotone angelic ∧
  Strict angelic ∧ TopPreserving angelic ∧ OmegaContinuous angelic ∧ ¬∃ R term, angelic = wp R term
negT_not_monotone_not_wp : ¬Monotone negT ∧ ¬∃ R term, negT = wp R term
wp_same_with_different_relations : wp (fun s s' => posP s → predR s s') posP = wp predR posP ∧
  (fun s s' => posP s → predR s s') ≠ predR
lem_of_relOf_wp_of_chaosNormal : (∀ (R : Rel Unit) (term : Pred Unit), ChaosNormal R term → relOf (wp R term) = R) →
  ∀ (P : Prop), P ∨ ¬P
lem_of_chaosNormal_unique_of_wp_eq : (∀ {R R' : Rel Unit} {t t' : Pred Unit},
    ChaosNormal R t → ChaosNormal R' t' → wp R t = wp R' t' → R = R' ∧ t = t') →
  ∀ (P : Prop), P ∨ ¬P
conjNonempty_wp_predR_posP_and_not_conjNonempty_eventually : ConjNonempty (wp predR posP) ∧ ¬ConjNonempty eventually
strict_wp_without_total_relation : Strict (wp predR posP) ∧ ¬∀ (s : Nat), ∃ s', predR s s'
lem_of_strict_wp_iff_totalOn : (∀ (R : Rel Unit) (term : Pred Unit), Strict (wp R term) ↔ TotalOn R term) →
  ∀ (P : Prop), P ∨ ¬P
lem_of_strict_wlp_iff : (∀ (R : Rel Unit), Strict (wlp R) ↔ ∀ (s : Unit), ∃ s', R s s') → ∀ (P : Prop), P ∨ ¬P
strict_wp_both_sides_occur : (Strict (wp predR posP) ∧ TotalOn predR posP) ∧
  ¬Strict (wp predR fun x => True) ∧ ¬TotalOn predR fun x => True
omegaContinuous_wp_partial_infinite_image_outside_term : OmegaContinuous (wp zeroHavocR posP) ∧
  (∀ (s : Nat), posP s → FiniteImage zeroHavocR s) ∧ ¬FiniteImage zeroHavocR 0
omegaContinuous_wp_with_infinite_image_outside_term : OmegaContinuous (wp havocR fun x => False) ∧
  ∀ (s : Nat), ¬FiniteImage havocR s
not_continuous_on_arbitrary_families_stepR_canonical : (∀ (s : Nat), True → FiniteImage stepR s) ∧
  OmegaContinuous (wp stepR fun x => True) ∧
    ¬∀ (Q : Nat → Pred Nat) (s : Nat),
        wp stepR (fun x => True) (fun t => ∃ n, Q n t) s → ∃ n, wp stepR (fun x => True) (Q n) s
lpo_of_finiteImage_imp_omegaContinuous_wp : (∀ (R : Rel Unit) (term : Pred Unit),
    (∀ (s : Unit), term s → FiniteImage R s) → OmegaContinuous (wp R term)) →
  ∀ (f : Nat → Bool), (∃ k, f k = true) ∨ ∀ (k : Nat), f k = false
omegaContinuous_wp_both_sides_occur : (OmegaContinuous (wp stepR fun x => True) ∧
    ∀ (s : Nat), True → FiniteImage stepR s) ∧
  ¬OmegaContinuous (wp havocR fun x => True) ∧ ¬∀ (s : Nat), True → FiniteImage havocR s
omegaContinuous_wp_partial_both_sides_occur : (OmegaContinuous (wp zeroHavocR posP) ∧
    ∀ (s : Nat), posP s → FiniteImage zeroHavocR s) ∧
  ¬OmegaContinuous (wp havocR posP) ∧ ¬∀ (s : Nat), posP s → FiniteImage havocR s
eventually_infinite_conjBin_not_conjNonempty : ¬FiniteState Nat ∧ ConjBin eventually ∧ ¬ConjNonempty eventually
not_omegaContinuous_eventually : ¬OmegaContinuous eventually
eventually_conjBin_not_dirContinuous_not_conjNonempty : ConjBin eventually ∧
  ¬DirContinuous eventually ∧ ¬ConjNonempty eventually
eventually_conjList : ∀ (l : List (Pred Nat)) (s : Nat),
  eventually (fun t => ∀ (Q : Pred Nat), Q ∈ l → Q t) s ↔ ∀ (Q : Pred Nat), Q ∈ l → eventually Q s
fromN_eq_wlp : ∀ (N : Nat), fromN N = wlp fun x s' => N ≤ s'
eventually_iff_exists_fromN : ∀ (Q : Pred Nat) (s : Nat), eventually Q s ↔ ∃ N, fromN N Q s
refinedBy_wp_without_global_relation_inclusion : RefinedBy (wp emptyR fun x => False) (wp havocR fun x => True) ∧
  ¬∀ (s s' : Unit), havocR s s' → emptyR s s'
relation_inclusion_without_term_inclusion_not_refinedBy : (ChaosNormal havocR fun x => True) ∧
  (ChaosNormal havocR fun x => False) ∧
    (∀ (s s' : Unit), havocR s s' → havocR s s') ∧ ¬RefinedBy (wp havocR fun x => True) (wp havocR fun x => False)
refinedBy_wp_global_inclusion_needs_chaosNormal : (¬ChaosNormal emptyR fun x => False) ∧
  RefinedBy (wp emptyR fun x => False) (wp havocR fun x => True) ∧
    ¬((∀ (s : Unit), (fun x => False) s → (fun x => True) s) ∧ ∀ (s s' : Unit), havocR s s' → emptyR s s')
lem_of_refinedBy_wp_iff_of_chaosNormal : (∀ {R₁ R₂ : Rel Unit} {t₁ t₂ : Pred Unit},
    ChaosNormal R₁ t₁ →
      (RefinedBy (wp R₁ t₁) (wp R₂ t₂) ↔ (∀ (s : Unit), t₁ s → t₂ s) ∧ ∀ (s s' : Unit), R₂ s s' → R₁ s s')) →
  ∀ (P : Prop), P ∨ ¬P
refinedBy_wp_both_sides_occur : RefinedBy (wp havocR fun x => True) (wp stepR fun x => True) ∧
  ¬RefinedBy (wp stepR fun x => True) (wp havocR fun x => True)
refinedBy_wp_partial_both_sides_occur : (RefinedBy (wp predR posP) (wp predR fun x => True) ∧
    (∀ (s : Nat), posP s → (fun x => True) s) ∧ ∀ (s : Nat), posP s → ∀ (s' : Nat), predR s s' → predR s s') ∧
  ¬RefinedBy (wp predR fun x => True) (wp predR posP) ∧
    ¬((∀ (s : Nat), (fun x => True) s → posP s) ∧
        ∀ (s : Nat), (fun x => True) s → ∀ (s' : Nat), predR s s' → predR s s')
refinedBy_wp_chaosNormal_partial_nonvacuous : ChaosNormal (fun s s' => posP s → predR s s') posP ∧
  RefinedBy (wp (fun s s' => posP s → predR s s') posP) (wp predR fun x => True) ∧
    (∀ (s : Nat), posP s → (fun x => True) s) ∧ ∀ (s s' : Nat), predR s s' → (fun s s' => posP s → predR s s') s s'
wp_comp_first_term_wrong : (wp (comp skipR skipR) fun x => True) ≠ fun Q =>
  wp skipR (fun x => True) (wp skipR (fun x => False) Q)
wp_comp_conj_term_wrong : (wp (comp stepR skipR) fun s => True ∧ s = 0) ≠ fun Q =>
  wp stepR (fun x => True) (wp skipR (fun s => s = 0) Q)
wp_union_disj_term_wrong : ¬∀ (Q : Pred Unit) (s : Unit),
    wp (union skipR skipR) (fun s => (fun x => True) s ∨ (fun x => False) s) Q s ↔
      wp skipR (fun x => True) Q s ∧ wp skipR (fun x => False) Q s
wp_comp_example : wp (comp stepR predR) (seqTerm stepR (fun x => True) posP) (fun n => n ≤ 1) 0
negT_not_monotone_not_angelicDemonic : ¬Monotone negT ∧ ¬∃ A, negT = angelicDemonic A
not_upClosed_not_recovered_by_multirelOf : (¬UpClosed fun s P => P = fun t => t = s) ∧
  multirelOf (angelicDemonic fun s P => P = fun t => t = s) ≠ fun s P => P = fun t => t = s
monotone_angelicDemonic_both_sides_occur : (Monotone eventually ∧ eventually = angelicDemonic (multirelOf eventually)) ∧
  ¬Monotone negT ∧ negT ≠ angelicDemonic (multirelOf negT)
multirelOf_angelicDemonic_both_sides_occur : ((UpClosed fun s P => P s) ∧
    multirelOf (angelicDemonic fun s P => P s) = fun s P => P s) ∧
  (¬UpClosed fun s P => P = fun t => t = s) ∧
    multirelOf (angelicDemonic fun s P => P = fun t => t = s) ≠ fun s P => P = fun t => t = s
eventually_eq_angelicDemonic : eventually = angelicDemonic fun x P => ∃ N, P = fun n => N ≤ n
@wp_eq_angelicDemonic : ∀ {σ : Type u_1} (R : Rel σ) (term : Pred σ),
  wp R term = angelicDemonic fun s P => term s ∧ P = R s
angelic_finiteState_monotone_not_conjNonempty : FiniteState Bool ∧ Monotone angelic ∧ ¬ConjNonempty angelic
lem_of_conjNonempty_of_conjBin_of_finiteState : (FiniteState Unit →
    ∀ {T : Transformer Unit}, ConjBin T → ConjNonempty T) →
  ∀ (B : Prop), B ∨ ¬B
finiteState_conjBin_nonvacuous : FiniteState Bool ∧ ConjBin (wlp skipR)
angelic_continuum_omegaContinuous_not_conjNonempty : ContinuumState Bool ∧
  Monotone angelic ∧ OmegaContinuous angelic ∧ ¬ConjNonempty angelic
angelic_countable_omegaContinuous_not_conjNonempty : CountableState Bool ∧
  Monotone angelic ∧ OmegaContinuous angelic ∧ ¬ConjNonempty angelic
eventually_continuum_conjBin_not_conjNonempty : ContinuumState Nat ∧ ConjBin eventually ∧ ¬ConjNonempty eventually
eventually_countable_conjBin_not_conjNonempty : CountableState Nat ∧ ConjBin eventually ∧ ¬ConjNonempty eventually
lem_of_conjNonempty_of_conjBin_of_omegaContinuous_of_continuumState : (ContinuumState Unit →
    ∀ {T : Transformer Unit}, ConjBin T → OmegaContinuous T → ConjNonempty T) →
  ∀ (B : Prop), B ∨ ¬B
lem_of_conjNonempty_of_conjBin_of_omegaContinuous_of_countable : (CountableState Unit →
    ∀ {T : Transformer Unit}, ConjBin T → OmegaContinuous T → ConjNonempty T) →
  ∀ (B : Prop), B ∨ ¬B
continuum_conjBin_omegaContinuous_nonvacuous : ContinuumState (Nat → Bool) ∧
  ¬CountableState (Nat → Bool) ∧ ConjBin (wp skipR fun x => True) ∧ OmegaContinuous (wp skipR fun x => True)
countable_conjBin_omegaContinuous_nonvacuous : CountableState Nat ∧ ConjBin (wlp stepR) ∧ OmegaContinuous (wlp stepR)
angelic_dirContinuous_monotone_not_conjNonempty : Monotone angelic ∧ DirContinuous angelic ∧ ¬ConjNonempty angelic
lem_of_conjNonempty_of_conjBin_of_dirContinuous : (∀ {T : Transformer Unit},
    ConjBin T → DirContinuous T → ConjNonempty T) →
  ∀ (B : Prop), B ∨ ¬B
conjBin_dirContinuous_nonvacuous_beyond_continuum : ¬ContinuumState ((Nat → Bool) → Bool) ∧
  ConjBin (wp skipR fun x => True) ∧ DirContinuous (wp skipR fun x => True)
@wlp_injective : ∀ {σ : Type u_1} {R R' : Rel σ}, wlp R = wlp R' → R = R'
@conjAll_iff_exists_unique_wlp : ∀ {σ : Type u_1} (T : Transformer σ),
  ConjAll T ↔ ∃ R, T = wlp R ∧ ∀ (R' : Rel σ), T = wlp R' → R' = R
@conjAll_iff_set : ∀ {σ : Type u_1} (T : Transformer σ),
  ConjAll T ↔ ∀ (F : Pred σ → Prop) (s : σ), T (fun t => ∀ (Q : Pred σ), F Q → Q t) s ↔ ∀ (Q : Pred σ), F Q → T Q s
@conjAll_arbitrary_sort : ∀ {σ : Type u_1} {T : Transformer σ},
  ConjAll T → ∀ (ι : Sort u_2) (Q : ι → Pred σ) (s : σ), T (fun t => ∀ (i : ι), Q i t) s ↔ ∀ (i : ι), T (Q i) s
@relOf_iff_not_avoids_of_monotone : ∀ {σ : Type u_1} {T : Transformer σ},
  Monotone T → ∀ (s s' : σ), relOf T s s' ↔ ¬T (fun t => t ≠ s') s
@conjNonempty_iff_exists_wp : ∀ {σ : Type u_1} (T : Transformer σ), ConjNonempty T ↔ ∃ R term, T = wp R term
@relOf_wp_of_chaosNormal : ∀ {σ : Type u_1} {R : Rel σ} {term : Pred σ}, ChaosNormal R term → relOf (wp R term) = R
@chaosNormal_unique_of_wp_eq : ∀ {σ : Type u_1} {R R' : Rel σ} {term term' : Pred σ},
  ChaosNormal R term → ChaosNormal R' term' → wp R term = wp R' term' → R = R' ∧ term = term'
@conjNonempty_iff_exists_unique_chaosNormal_wp : ∀ {σ : Type u_1} (T : Transformer σ),
  ConjNonempty T ↔
    ∃ R term,
      ChaosNormal R term ∧
        T = wp R term ∧ ∀ (R' : Rel σ) (term' : Pred σ), ChaosNormal R' term' → T = wp R' term' → R' = R ∧ term' = term
@conjNonempty_iff_set : ∀ {σ : Type u_1} (T : Transformer σ),
  ConjNonempty T ↔
    ∀ (F : Pred σ → Prop),
      (∃ Q, F Q) → ∀ (s : σ), T (fun t => ∀ (Q : Pred σ), F Q → Q t) s ↔ ∀ (Q : Pred σ), F Q → T Q s
@conjNonempty_arbitrary_sort : ∀ {σ : Type u_1} {T : Transformer σ},
  ConjNonempty T →
    ∀ (ι : Sort u_2) (Q : ι → Pred σ), Nonempty ι → ∀ (s : σ), T (fun t => ∀ (i : ι), Q i t) s ↔ ∀ (i : ι), T (Q i) s
@chaosNormal_relOf_termOf_of_monotone : ∀ {σ : Type u_1} {T : Transformer σ},
  Monotone T → ChaosNormal (relOf T) (termOf T)
@termOf_wp : ∀ {σ : Type u_1} (R : Rel σ) (term : Pred σ), termOf (wp R term) = term
@wp_chaos_eq : ∀ {σ : Type u_1} (R : Rel σ) (term : Pred σ), wp (fun s s' => term s → R s s') term = wp R term
@wp_restrict_eq : ∀ {σ : Type u_1} (R : Rel σ) (term : Pred σ), wp (fun s s' => term s ∧ R s s') term = wp R term
@strict_wlp_iff : ∀ {σ : Type u_1} (R : Rel σ), Strict (wlp R) ↔ ∀ (s : σ), ∃ s', R s s'
@omegaContinuous_wlp_iff : ∀ {σ : Type u_1} (R : Rel σ), OmegaContinuous (wlp R) ↔ ∀ (s : σ), FiniteImage R s
@omegaContinuous_two_sided_iff : ∀ {σ : Type u_1} (T : Transformer σ),
  (∀ (Q : Nat → Pred σ), Chain Q → ∀ (s : σ), T (fun t => ∃ n, Q n t) s ↔ ∃ n, T (Q n) s) ↔
    Monotone T ∧ OmegaContinuous T
finitary_laws_do_not_imply_relational : ¬∀ (T : Transformer Nat),
    Monotone T → ConjBin T → TopPreserving T → Strict T → ∃ R term, T = wp R term
eventually_ne_wp : ∀ (R : Rel Nat) (term : Pred Nat), eventually ≠ wp R term
eventually_ne_wlp : ∀ (R : Rel Nat), eventually ≠ wlp R
@conjBin_iff_exists_wp_of_finiteState : ∀ {σ : Type u_1},
  FiniteState σ → ∀ (T : Transformer σ), ConjBin T ↔ ∃ R term, T = wp R term
@conjBin_topPreserving_iff_exists_wlp_of_finiteState : ∀ {σ : Type u_1},
  FiniteState σ → ∀ (T : Transformer σ), ConjBin T ∧ TopPreserving T ↔ ∃ R, T = wlp R
@conjBin_omegaContinuous_iff_wp_finiteImage_of_continuumState : ∀ {σ : Type u_1},
  ContinuumState σ →
    ∀ (T : Transformer σ), ConjBin T ∧ OmegaContinuous T ↔ ∃ R term, T = wp R term ∧ ∀ (s : σ), term s → FiniteImage R s
@exists_wp_of_conjBin_of_dirContinuous : ∀ {σ : Type u_1} {T : Transformer σ},
  ConjBin T → DirContinuous T → ∃ R term, T = wp R term
@refinedBy_wlp_iff : ∀ {σ : Type u_1} (R₁ R₂ : Rel σ), RefinedBy (wlp R₁) (wlp R₂) ↔ ∀ (s s' : σ), R₂ s s' → R₁ s s'
@wlp_iUnion : ∀ {σ : Type u_1} {ι : Sort u_2} (R : ι → Rel σ) (Q : Pred σ) (s : σ),
  wlp (fun s s' => ∃ i, R i s s') Q s ↔ ∀ (i : ι), wlp (R i) Q s
@wp_skipR_true : ∀ {σ : Type u_1}, (wp skipR fun x => True) = fun Q => Q
@wlp_emptyR : ∀ {σ : Type u_1} (Q : Pred σ) (s : σ), wlp emptyR Q s
@seqTerm_eq_wp : ∀ {σ : Type u_1} (R₁ : Rel σ) (t₁ t₂ : Pred σ), seqTerm R₁ t₁ t₂ = wp R₁ t₁ t₂
@monotone_angelicDemonic : ∀ {σ : Type u_1} (A : σ → Pred σ → Prop), Monotone (angelicDemonic A)
@monotone_iff_exists_angelicDemonic : ∀ {σ : Type u_1} (T : Transformer σ), Monotone T ↔ ∃ A, T = angelicDemonic A
@upClosed_multirelOf_iff : ∀ {σ : Type u_1} (T : Transformer σ), UpClosed (multirelOf T) ↔ Monotone T
angelicDemonic_not_injective : ∃ A A', A ≠ A' ∧ angelicDemonic A = angelicDemonic A'
upClosed_not_unique_among_all : (UpClosed fun s P => P s) ∧
  (¬UpClosed fun s P => P = fun t => t = s) ∧
    (angelicDemonic fun s P => P s) = angelicDemonic fun s P => P = fun t => t = s
@kernel_established_of_list : ∀ {σ : Type u_1} {T : Transformer σ},
  ConjBin T →
    ∀ (s : σ) (l : List σ),
      T (fun x => (∀ (Q : Pred σ), T Q s → Q x) ∨ x ∈ l) s → T (fun x => ∀ (Q : Pred σ), T Q s → Q x) s
@conjNonempty_of_conjBin_of_omegaContinuous_of_countable : ∀ {σ : Type u_1},
  CountableState σ → ∀ {T : Transformer σ}, ConjBin T → OmegaContinuous T → ConjNonempty T
@continuumState_of_countableState : ∀ {σ : Type u_1}, CountableState σ → ContinuumState σ
@strict_conjBin_omegaContinuous_iff_wp_finiteImage_totalOn_of_continuumState : ∀ {σ : Type u_1},
  ContinuumState σ →
    ∀ (T : Transformer σ),
      Strict T ∧ ConjBin T ∧ OmegaContinuous T ↔
        ∃ R term, T = wp R term ∧ (∀ (s : σ), term s → FiniteImage R s) ∧ TotalOn R term
nat_to_bool_uncountable_conjBin_omegaContinuous_conjNonempty : ¬CountableState (Nat → Bool) ∧
  ∀ (T : Transformer (Nat → Bool)), ConjBin T → OmegaContinuous T → ConjNonempty T
@omegaContinuous_of_dirContinuous : ∀ {σ : Type u_1} {T : Transformer σ}, DirContinuous T → OmegaContinuous T
@finiteImage_on_term_of_dirContinuous_wp : ∀ {σ : Type u_1} {R : Rel σ} {term : Pred σ},
  DirContinuous (wp R term) → ∀ (s : σ), term s → FiniteImage R s
```

### Statements of the scope witnesses cited in the non-claims, as printed by Lean

These 12 theorems are the proved scope witnesses cited in parentheses in the non-claims (Boundaries) that are not named in any other field of `results.json`; each card lists its own under `scope_witnesses_lean`. They kernel-check in the same build and are covered by the declaration sweep in `audit/axioms.json` (footprints below), but they are not among the 76 statement-hashed declarations, which are the results, counterexamples, non-vacuity witnesses and positive controls. The example programs and transformers they mention (`abortT`, `constT`, `negT`, `havocR`, `stepR`, `emptyR`, `eventually`) are unfolded under Setting and definitions.

| Declaration | Cited in | Axioms |
|---|---|---|
| `abortT_finiteState_conjBin_not_conjAll` | result 9a, non-claim 3 | `Quot.sound`, `propext` |
| `chaosNormal_not_preserved_by_comp` | result 2, non-claim 6; result 7, non-claim 3 | none |
| `constT_conjNonempty_not_strict_not_topPreserving` | result 2, non-claim 5 | `Quot.sound`, `propext` |
| `dirContinuous_negT` | result 9c, non-claim 2 | none |
| `havocR_nat_conjAll_strict_not_omegaContinuous` | result 2, non-claim 5; result 4, non-claim 6 | `Quot.sound`, `propext` |
| `not_disjBin_eventually` | result 5, non-claim 3 | `Quot.sound`, `propext` |
| `not_disjBin_wlp_stepR` | result 1, non-claim 4 | `Quot.sound`, `propext` |
| `omegaContinuous_negT_not_monotone` | result 4, non-claim 5 | none |
| `omegaContinuous_wp_emptyR` | result 4, non-claim 3 | none |
| `relOf_eventually_finite_not_conjNonempty` | result 9a, non-claim 1 | `Quot.sound`, `propext` |
| `relational_criterion_fails_off_wp` | result 6, non-claim 3 | `Quot.sound`, `propext` |
| `termOf_wlp_emptyR_no_outcome` | result 2, non-claim 2; result 3, non-claim 2 | none |

Output of `#check @name` (with `open Toy.PredTrans`) on the built library, unedited.

```lean
abortT_finiteState_conjBin_not_conjAll : FiniteState Unit ∧ ConjBin abortT ∧ ¬ConjAll abortT
chaosNormal_not_preserved_by_comp : (ChaosNormal havocR fun x => False) ∧
  (ChaosNormal emptyR fun x => True) ∧ ¬ChaosNormal (comp havocR emptyR) (seqTerm havocR (fun x => False) fun x => True)
constT_conjNonempty_not_strict_not_topPreserving : ConjNonempty (constT fun b => b = true) ∧
  ¬Strict (constT fun b => b = true) ∧ ¬TopPreserving (constT fun b => b = true)
@dirContinuous_negT : ∀ {σ : Type u_1}, DirContinuous negT
havocR_nat_conjAll_strict_not_omegaContinuous : ConjAll (wlp havocR) ∧
  Strict (wlp havocR) ∧ ¬OmegaContinuous (wlp havocR)
not_disjBin_eventually : eventually (fun n => n % 2 = 0 ∨ n % 2 = 1) 0 ∧
  ¬eventually (fun n => n % 2 = 0) 0 ∧ ¬eventually (fun n => n % 2 = 1) 0
not_disjBin_wlp_stepR : wlp stepR (fun n => n = 1 ∨ n = 2) 0 ∧
  ¬wlp stepR (fun n => n = 1) 0 ∧ ¬wlp stepR (fun n => n = 2) 0
omegaContinuous_negT_not_monotone : OmegaContinuous negT ∧ ¬Monotone negT
@omegaContinuous_wp_emptyR : ∀ {σ : Type u_1} (term : Pred σ), OmegaContinuous (wp emptyR term)
relOf_eventually_finite_not_conjNonempty : (∀ (s : Nat), FiniteImage (relOf eventually) s) ∧ ¬ConjNonempty eventually
relational_criterion_fails_off_wp : (∀ (s : Nat), termOf (wlp emptyR) s → termOf eventually s) ∧
  (∀ (s : Nat), termOf (wlp emptyR) s → ∀ (s' : Nat), relOf eventually s s' → relOf (wlp emptyR) s s') ∧
    ¬RefinedBy (wlp emptyR) eventually
termOf_wlp_emptyR_no_outcome : termOf (wlp emptyR) () ∧ ¬∃ s', emptyR () s'
```

### Definitions, as printed by Lean

Output of `#print` on the built library, unedited. (`#print` elides the type of the bound function in `CountableState` and `ContinuumState`; it is `σ → Nat` and `σ → Nat → Bool`.)

```lean
@[reducible] def Toy.PredTrans.Pred.{u} : Type u → Type u :=
fun σ => σ → Prop
@[reducible] def Toy.PredTrans.Transformer.{u} : Type u → Type u :=
fun σ => Pred σ → Pred σ
@[reducible] def Toy.PredTrans.Rel.{u} : Type u → Type u :=
fun σ => σ → σ → Prop
def Toy.PredTrans.wlp.{u} : {σ : Type u} → Rel σ → Transformer σ :=
fun {σ} R Q s => ∀ (s' : σ), R s s' → Q s'
def Toy.PredTrans.wp.{u} : {σ : Type u} → Rel σ → Pred σ → Transformer σ :=
fun {σ} R term Q s => term s ∧ wlp R Q s
def Toy.PredTrans.Monotone.{u} : {σ : Type u} → Transformer σ → Prop :=
fun {σ} T => ∀ (P Q : Pred σ), (∀ (t : σ), P t → Q t) → ∀ (s : σ), T P s → T Q s
def Toy.PredTrans.ConjAll.{u} : {σ : Type u} → Transformer σ → Prop :=
fun {σ} T => ∀ (ι : Type u) (Q : ι → Pred σ) (s : σ), T (fun t => ∀ (i : ι), Q i t) s ↔ ∀ (i : ι), T (Q i) s
def Toy.PredTrans.ConjNonempty.{u} : {σ : Type u} → Transformer σ → Prop :=
fun {σ} T =>
  ∀ (ι : Type u) (Q : ι → Pred σ), Nonempty ι → ∀ (s : σ), T (fun t => ∀ (i : ι), Q i t) s ↔ ∀ (i : ι), T (Q i) s
def Toy.PredTrans.ConjBin.{u} : {σ : Type u} → Transformer σ → Prop :=
fun {σ} T => ∀ (P Q : Pred σ) (s : σ), T (fun t => P t ∧ Q t) s ↔ T P s ∧ T Q s
def Toy.PredTrans.Strict.{u} : {σ : Type u} → Transformer σ → Prop :=
fun {σ} T => ∀ (s : σ), ¬T (fun x => False) s
def Toy.PredTrans.TopPreserving.{u} : {σ : Type u} → Transformer σ → Prop :=
fun {σ} T => ∀ (s : σ), T (fun x => True) s
def Toy.PredTrans.Chain.{u} : {σ : Type u} → (Nat → Pred σ) → Prop :=
fun {σ} Q => ∀ (n : Nat) (s : σ), Q n s → Q (n + 1) s
def Toy.PredTrans.OmegaContinuous.{u} : {σ : Type u} → Transformer σ → Prop :=
fun {σ} T => ∀ (Q : Nat → Pred σ), Chain Q → ∀ (s : σ), T (fun t => ∃ n, Q n t) s → ∃ n, T (Q n) s
def Toy.PredTrans.Directed.{u} : {σ ι : Type u} → (ι → Pred σ) → Prop :=
fun {σ ι} Q => Nonempty ι ∧ ∀ (i j : ι), ∃ k, (∀ (s : σ), Q i s → Q k s) ∧ ∀ (s : σ), Q j s → Q k s
def Toy.PredTrans.DirContinuous.{u} : {σ : Type u} → Transformer σ → Prop :=
fun {σ} T => ∀ (ι : Type u) (Q : ι → Pred σ), Directed Q → ∀ (s : σ), T (fun t => ∃ i, Q i t) s → ∃ i, T (Q i) s
def Toy.PredTrans.relOf.{u} : {σ : Type u} → Transformer σ → Rel σ :=
fun {σ} T s s' => ∀ (Q : Pred σ), T Q s → Q s'
def Toy.PredTrans.termOf.{u} : {σ : Type u} → Transformer σ → Pred σ :=
fun {σ} T => T fun x => True
def Toy.PredTrans.FiniteImage.{u} : {σ : Type u} → Rel σ → σ → Prop :=
fun {σ} R s => ∃ l, ∀ (s' : σ), R s s' → s' ∈ l
def Toy.PredTrans.TotalOn.{u} : {σ : Type u} → Rel σ → Pred σ → Prop :=
fun {σ} R term => ∀ (s : σ), term s → ∃ s', R s s'
def Toy.PredTrans.ChaosNormal.{u} : {σ : Type u} → Rel σ → Pred σ → Prop :=
fun {σ} R term => ∀ (s : σ), ¬term s → ∀ (s' : σ), R s s'
def Toy.PredTrans.RefinedBy.{u} : {σ : Type u} → Transformer σ → Transformer σ → Prop :=
fun {σ} T₁ T₂ => ∀ (Q : Pred σ) (s : σ), T₁ Q s → T₂ Q s
def Toy.PredTrans.CountableState.{u} : Type u → Prop :=
fun σ => ∃ f, ∀ (x y : σ), f x = f y → x = y
def Toy.PredTrans.ContinuumState.{u} : Type u → Prop :=
fun σ => ∃ f, ∀ (x y : σ), f x = f y → x = y
def Toy.PredTrans.FiniteState.{u} : Type u → Prop :=
fun σ => ∃ l, ∀ (x : σ), x ∈ l
def Toy.PredTrans.comp.{u} : {σ : Type u} → Rel σ → Rel σ → Rel σ :=
fun {σ} R₁ R₂ s s'' => ∃ s', R₁ s s' ∧ R₂ s' s''
def Toy.PredTrans.seqTerm.{u} : {σ : Type u} → Rel σ → Pred σ → Pred σ → Pred σ :=
fun {σ} R₁ t₁ t₂ s => t₁ s ∧ ∀ (s' : σ), R₁ s s' → t₂ s'
def Toy.PredTrans.union.{u} : {σ : Type u} → Rel σ → Rel σ → Rel σ :=
fun {σ} R₁ R₂ s s' => R₁ s s' ∨ R₂ s s'
def Toy.PredTrans.angelicDemonic.{u} : {σ : Type u} → (σ → Pred σ → Prop) → Transformer σ :=
fun {σ} A Q s => ∃ P, A s P ∧ ∀ (t : σ), P t → Q t
def Toy.PredTrans.multirelOf.{u} : {σ : Type u} → Transformer σ → σ → Pred σ → Prop :=
fun {σ} T s P => T P s
def Toy.PredTrans.UpClosed.{u} : {σ : Type u} → (σ → Pred σ → Prop) → Prop :=
fun {σ} A => ∀ (s : σ) (P P' : Pred σ), A s P → (∀ (t : σ), P t → P' t) → A s P'
def Toy.PredTrans.eventually : Transformer Nat :=
fun Q x => ∃ N, ∀ (n : Nat), N ≤ n → Q n
def Toy.PredTrans.orT : Prop → Transformer Unit :=
fun B Q x => Q () ∨ B
```

### Primary sources

Bibliographic data below were checked against publisher, DBLP or Crossref records. "Content
seen" means the cited passage was read at the source (or in the publisher's abstract or table of
contents); "located only" means the source and the relevant chapter or section were confirmed
but the theorem statement itself was not read; "bibliographic only" means only the record was
verified.

| Source | Used for | Status |
|---|---|---|
| E. W. Dijkstra, "Guarded commands, nondeterminacy and formal derivation of programs", *CACM* 18(8):453–457, 1975, doi:10.1145/360933.360975 | the four properties of `wp` (excluded miracle, monotonicity, binary conjunctivity, disjunctivity for deterministic mechanisms); the syntactic composition equation; no continuity property, no relational model | content seen (archive transcription of EWD 472) |
| E. W. Dijkstra, *A Discipline of Programming*, Prentice-Hall, 1976 | ch. 3 (Properties 1–4); ch. 9 (Property 5, continuity over ω-chains; unbounded choice contradicts it) | content seen (scanned copy; formula typography not re-checked against print) |
| E. W. Dijkstra, "The Equivalence of Bounded Nondeterminacy and Continuity" (EWD 675, 1978), in *Selected Writings on Computing: A Personal Perspective*, Springer, 1982, pp. 358–359, doi:10.1007/978-1-4612-5695-3_65 | title states result 4's equivalence | bibliographic only |
| E. W. Dijkstra, A. J. M. van Gasteren, *Acta Informatica* 23(1):1–7, 1986, doi:10.1007/BF00268074 | unbounded nondeterminacy amounts to noncontinuous predicate transformers | content seen (abstract) |
| R.-J. Back, J. von Wright, *Refinement Calculus: A Systematic Introduction*, Springer, 1998, doi:10.1007/978-1-4612-1674-2 | §26.1, §26.2, §26.5, ch. 22, ch. 13, ch. 17, §27.4 (located only); ch. 15 "Choice Semantics" (abstract seen) | located only / abstract of ch. 15 seen; no theorem number is cited |
| E. Sekerinski, T. Zhang, "A Normal Form for Multi-Exit Statements" (author-hosted manuscript dated December 2011, revised after 2013; venue not verified), <https://www.cas.mcmaster.ca/~emil/pubs/SekerinskiZhang11NormalFormMultiExit.pdf> (URL resolved on 2026-11-20; SHA-256 of the PDF file not recorded) | Theorems 13, 15, 17 (normal forms `{r};[R]`, `[R]`, `{p};[R]`); Theorem 17 asserts uniqueness of `R` without a normalization condition, false as stated here and not argued in its proof; §7 enabledness and feasibility; reports an Isabelle/HOL check (not inspected) | content seen (author-hosted PDF) |
| K. Maillard et al., "Dijkstra monads for all", *PACMPL* 3(ICFP), article 104, 2019, doi:10.1145/3341708 (arXiv:1903.01237) | §4.1: `PrePost` ↔ positively conjunctive `W^Pure` Galois connection (result 2, return-value setting); `bind` of `PrePost` (result 7); `W^Pure` monotonic (result 8); §5 reports a Coq implementation of §4.1 | content seen (preprint); Coq files not inspected |
| J. Alpuim, W. Swierstra, "Embedding the refinement calculus in Coq", *Sci. Comput. Program.* 164:37–48, 2018, doi:10.1016/j.scico.2017.04.003; `jalpuim/dtp-refinement` at `a29203b823d0399657c3f5edca3b8a105797260b`, `Refinement.v` | `Theorem soundness` (relational refinement criterion ⇔ pointwise implication of semantics, with return values; result 6); `SeqPT` (result 7) | content seen (source file) |
| V. Preoteasa, "Formalization of Refinement Calculus for Reactive Systems", *AFP*, 2014; `Refinement.thy` (mirror-afp-devel `523cdc72b5ae4a91c9ab8e1025d4a30b40472720`) | `conjunctive`, `sconjunctive`; `assert_demonic_refinement` (result 6); `demonic_demonic`, `assert_demonic_comp`, unnamed `[:r:] ⊓ [:r':] = [:r ⊔ r':]`, `spec_demonic_choice` (result 7) | content seen (theory source) |
| G. Struth, "Transformer Semantics", *AFP*, 2018; `Kleisli_Transformers.thy` (same mirror commit) | `rfb_Inf_pres`, `rfb_surj`, `rfb_inj` (result 1); `rfb_zero_pres2` (result 3); `rfb_comp_pres`, `rfb_Id_pres`, `rfb_Sup_dual_var`, `rfb_zero_pres` (result 7); partial correctness only | content seen (theory source) |
| Mathlib, commit `5f78f9ce46fc85fa3cb45561d47b489c4c98cd04`, `Mathlib/Basic/Rel.lean` | `SetRel.core` with `core_inter`, `core_univ`, `core_id`, `core_comp`; no converse | content seen (source file) |
| G. Nelson, "A generalization of Dijkstra's calculus", *ACM TOPLAS* 11(4):517–561, 1989, doi:10.1145/69558.69559 | drops excluded miracle; partial commands; approximation order from `wp` and `wlp` jointly | content seen (abstract; technical-report version SRC-16) |
| C. Morgan, "The specification statement", *ACM TOPLAS* 10(3):403–419, 1988, doi:10.1145/44501.44503 | miracles admitted | content seen (abstract) |
| J. M. Morris, "A theoretical basis for stepwise refinement and the programming calculus", *Sci. Comput. Program.* 9(3):287–306, 1987, doi:10.1016/0167-6423(87)90011-6 | early refinement-calculus source | bibliographic only |
| G. D. Plotkin, "Dijkstra's predicate transformers and Smyth's powerdomains", LNCS 86, Springer, 1980, pp. 527–553, doi:10.1007/3-540-10007-5_48 | denumerable state set; Lemma 5.6; Theorem 5.9 | content seen (author's scan; some formulas illegible) |
| M. Wand, "A characterization of weakest preconditions", *JCSS* 15(2):209–212, 1977, doi:10.1016/S0022-0000(77)80006-8 | strict + binary intersections + directed continuity ⇔ bounded nondeterminacy; ω-chains for countable `S` | content seen (abstract only) |
| K. R. Apt, G. D. Plotkin, *JACM* 33(4):724–767, 1986, doi:10.1145/6490.6494 | countable nondeterminism loses continuity | content seen (abstract) |
| M. B. Smyth, "Power domains and predicate transformers: A topological view", ICALP 1983, LNCS 154, pp. 662–675, doi:10.1007/BFb0036946 | topological power-domain view | bibliographic only |
| M. Bonsangue, J. N. Kok, "Isomorphisms between predicate and state transformers", MFCS 1993, LNCS 711, pp. 301–310, doi:10.1007/3-540-57182-5_22 | isomorphisms between power-domain state transformers and continuous/monotonic/unrestricted predicate transformers | content seen (abstract) |
| M. M. Bonsangue, J. N. Kok, *Formal Aspects of Computing* 6:788–800, 1994, doi:10.1007/BF01213603 | Back's refinement order vs. Nelson's approximation order; Smyth and Egli–Milner power domains | content seen (abstract) |
| P. Guerreiro, "Another characterization of weakest preconditions", LNCS 137, 1982, pp. 164–177, doi:10.1007/3-540-11494-7_12 | relational model with explicit non-termination | content seen (abstract) |
| B. Jónsson, A. Tarski, "Boolean Algebras with Operators", Parts I and II, *Amer. J. Math.* 73(4):891–939, 1951, doi:10.2307/2372123, and 74(1):127–162, 1952, doi:10.2307/2372074; P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*, CUP, 2001, doi:10.1017/CBO9781107050884 | algebraic modal logic lineage of results 1, 5, 9a | bibliographic only |
| R. Parikh, FOCS 1983, pp. 195–200, doi:10.1109/SFCS.1983.47; North-Holland Mathematics Studies, 1985, pp. 111–139, doi:10.1016/S0304-0208(08)73078-0 | duality of up-closed multirelations and isotone predicate transformers, as credited by Furusawa and Struth | bibliographic only |
| H. Furusawa, G. Struth, "Taming Multirelations", *ACM TOCL* 17(4), 2016, doi:10.1145/2964907 (arXiv:1501.05147) | multirelation algebra; attribution to Parikh | content seen (preprint) |
| J. von Wright, "The lattice of data refinement", *Acta Informatica* 31(2):105–135, 1994, doi:10.1007/BF01192157 | angelic/demonic normal form, as credited by Sekerinski and Zhang | bibliographic only |
| I. Rewitzky, LNCS 2929, 2003, pp. 256–271, doi:10.1007/978-3-540-24615-2_12; I. Rewitzky, C. Brink, LNCS 4136, 2006, pp. 311–327, doi:10.1007/11828563_21 | multirelations and monotone operators; monotone predicate transformers as up-closed multirelations | content seen (abstracts) |
| T. Altenkirch, N. Ghani, P. Hancock, C. McBride, P. Morris, "Indexed containers", *JFP* 25, e5, 2015, doi:10.1017/S095679681500009X | an author draft cites B&vW "Thm 13.10" | bibliographic record verified; theorem number not relied on |
| S. Foster, J. Baxter, A. Cavalcanti, J. Woodcock, F. Zeyda, "Unifying semantic foundations for automated verification tools in Isabelle/UTP", *Sci. Comput. Program.* 197:102510, 2020, doi:10.1016/j.scico.2020.102510; S. Foster, F. Zeyda, J. Woodcock, "Isabelle/UTP: A Mechanised Theory Engineering Framework", UTP 2014, LNCS 8963, 2015, pp. 21–41, doi:10.1007/978-3-319-14806-9_2 | relational (design) semantics with healthiness conditions, mechanized | bibliographic only (context; not used for any card) |
| R. J. R. Back, J. von Wright, "Refinement concepts formalised in higher order logic", *Formal Aspects of Computing* 2(1):247–272, 1990, doi:10.1007/BF01888227; J.-R. Abrial, *The B-Book*, CUP, 1996, doi:10.1017/CBO9780511624162 | early mechanization of the refinement calculus; generalized substitutions | bibliographic only (context; not used for any card) |
| C. A. R. Hoare, "Some Properties of Predicate Transformers", *JACM* 25(3):461–480, 1978, doi:10.1145/322077.322088; E. W. Dijkstra, C. S. Scholten, *Predicate Calculus and Program Semantics*, Springer, 1990, doi:10.1007/978-1-4612-3228-5; W. H. Hesselink, *Programs, Recursion and Unbounded Choice*, CUP, 1992, doi:10.1017/CBO9780511569784 | healthiness properties; paired `wp`/`wlp` calculus; unbounded choice | abstract / located only; **not** cited for any relational characterization |

Mechanizations: result 1 is mechanized in Isabelle/HOL (Struth); results 6 and 7 in Isabelle/HOL
(Preoteasa) and result 6 with return values in Coq (Alpuim and Swierstra); for result 2 in a
return-value setting a Coq implementation is reported (Maillard et al., §5; not inspected). No
Lean 4 formalization of the converse directions of results 1 and 2 was found (best-effort search;
absence not established).

Re-checked on 2026-11-20 for this report: the Crossref records of the DOIs listed in `REPORT.json` (titles and venues match), and the existence of the pinned commits `523cdc72b5ae4a91c9ab8e1025d4a30b40472720` (`isabelle-prover/mirror-afp-devel`), `a29203b823d0399657c3f5edca3b8a105797260b` (`jalpuim/dtp-refinement`) and `5f78f9ce46fc85fa3cb45561d47b489c4c98cd04` (`leanprover-community/mathlib4`) via the GitHub API; and that the author-hosted URL of the Sekerinski and Zhang manuscript (<https://www.cas.mcmaster.ca/~emil/pubs/SekerinskiZhang11NormalFormMultiExit.pdf>) resolves (HTTP 200) to a text whose title, authors, date line 'December 2011' and Theorems 13, 15 and 17 match the citations above. Only a text rendering of that PDF was retrieved, not the file bytes, so no SHA-256 of the PDF is recorded; the manuscript has no DOI or immutable revision and is therefore not listed in `REPORT.json`. Passage-level content claims are as recorded per citation ("content seen", "located only", "bibliographic only").

## Revalidation

Requires `elan` with `leanprover/lean4:v4.34.1` and `python3`. Work on a scratch copy so no build artifacts enter the package tree. From the package directory:

```bash
WORK="$(mktemp -d)"
cp -R lean "$WORK/lean"
cp -R results.json audit "$WORK/"
cd "$WORK/lean"

# 1. Build under the pinned toolchain (expect success, no warnings).
lake build

# 2. Names referenced by the cards (expect 76 lines).
python3 - <<'EOF'
import json
R = json.load(open('../results.json'))
names = set()
for r in R:
    names |= set(r['lean']) | set(r.get('nonvacuity_witness_lean', [])) | set(r.get('positive_control_lean', []))
    for h in r['hypotheses']:
        names |= set(h.get('counterexample', []))
open('card_names.txt', 'w').write('\n'.join(sorted(names)) + '\n')
EOF
```

3. Save the following as `RevalidationAudit.lean` in `$WORK/lean` and run `lake env lean RevalidationAudit.lean > audit_output.json`:

```lean
import Lean
import ToyPredTrans
open Lean Elab Command

/-! Revalidation audit: axioms of every declaration of the library, and the statement and
definition-closure text of every declaration named in `results.json`. -/

private def inLib (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => (`ToyPredTrans).isPrefixOf env.header.moduleNames[idx.toNat]!
  | none => false

private partial def closure (env : Environment) (todo : List Name) (acc : NameSet) : NameSet :=
  match todo with
  | [] => acc
  | n :: rest =>
    if acc.contains n || !inLib env n then closure env rest acc else
    let acc := acc.insert n
    match env.find? n with
    | none => closure env rest acc
    | some ci =>
      let cs := ci.type.getUsedConstants.toList ++
        (match ci.value? (allowOpaque := true) with
         | some v => if ci.isTheorem then [] else v.getUsedConstants.toList
         | none => []) ++
        (match ci with
         | .inductInfo iv => iv.ctors
         | _ => [])
      closure env (cs ++ rest) acc

#eval show CommandElabM Unit from do
  let env ← getEnv
  let names ← (do
    let txt ← IO.FS.readFile "card_names.txt"
    pure ((txt.splitOn "\n").filter (· ≠ "") |>.map String.toName))
  let mut decls : Array Json := #[]
  for (n, ci) in env.constants.toList do
    if inLib env n && !n.isInternal then
      let axs ← collectAxioms n
      let kind := match ci with
        | .axiomInfo _ => "axiom" | .opaqueInfo _ => "opaque" | .thmInfo _ => "theorem"
        | .defnInfo _ => "def" | _ => "other"
      decls := decls.push (Json.mkObj [("name", toJson n.toString), ("kind", toJson kind),
        ("axioms", toJson (axs.map Name.toString))])
  let mut stmts : Array Json := #[]
  for n in names do
    match env.find? n with
    | none => stmts := stmts.push (Json.mkObj [("name", toJson n.toString), ("missing", toJson true)])
    | some ci =>
      let cl := closure env ci.type.getUsedConstants.toList {}
      let clTxt := cl.toList.map (fun c =>
        match env.find? c with
        | some cc => c.toString ++ " : " ++ toString (repr cc.type) ++
            (match cc.value? (allowOpaque := true) with
             | some v => if cc.isTheorem then "" else " := " ++ toString (repr v)
             | none => "")
        | none => c.toString)
      stmts := stmts.push (Json.mkObj [("name", toJson n.toString),
        ("type_repr", toJson (toString (repr ci.type))),
        ("closure", toJson (clTxt.toArray.qsort (· < ·)))])
  IO.println ((Json.mkObj [("decls", Json.arr decls), ("stmts", Json.arr stmts)]).compress)
```

4. Compare with the recorded audit in the copied `audit/` directory:

```bash
python3 - audit_output.json .. <<'EOF'
import hashlib, json, sys

# Arguments: <audit_output.json> <package_dir>
out = json.load(open(sys.argv[1]))
pkg = sys.argv[2]
allowed = {"propext", "Classical.choice", "Quot.sound"}
ax_rec = json.load(open(f"{pkg}/audit/axioms.json"))["declarations"]
st_rec = json.load(open(f"{pkg}/audit/statements.json"))["statements"]
ax_now = {d["name"]: sorted(d["axioms"]) for d in out["decls"]}
bad = [d["name"] for d in out["decls"] if set(d["axioms"]) - allowed or d["kind"] in ("axiom", "opaque")]
st_now = {}
missing = []
for s in out["stmts"]:
    if s.get("missing"):
        missing.append(s["name"])
        continue
    st_now[s["name"]] = {
        "statement_sha256": hashlib.sha256(s["type_repr"].encode()).hexdigest(),
        "closure_sha256": hashlib.sha256("\n".join(s["closure"]).encode()).hexdigest(),
        "closure_size": len(s["closure"]),
    }
print("declarations audited:", len(ax_now))
print("disallowed axioms or axiom/opaque declarations:", bad)
print("axioms match audit/axioms.json:", ax_now == ax_rec)
print("missing card names:", missing)
print("statement hashes match audit/statements.json:", st_now == st_rec, f"({len(st_now)} hashed)")
EOF
```

Expected output: `declarations audited: 300`, an empty list of disallowed axioms, `axioms match audit/axioms.json: True`, no missing card names, and `statement hashes match audit/statements.json: True (76 hashed)`.

What these checks establish: that the Lean statements and definitions are unchanged and kernel-check with the recorded axioms under this toolchain. They do not re-verify the prose: after any change to a definition or statement, re-read the affected cards (plain claim, hypothesis ledger, non-claims) against the new `#check` output. For a different Lean version, rebuild first; statement hashes depend on `repr` output and may change across toolchains even when the mathematics is unchanged.
