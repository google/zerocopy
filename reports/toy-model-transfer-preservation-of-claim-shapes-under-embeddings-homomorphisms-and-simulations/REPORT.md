# Transfer of claim shapes from a model to a system along embeddings, homomorphisms and simulations

## Summary

This package is a Lean 4 formalization (core Lean, no Mathlib) of which claim shapes transfer from a model to a system when a relation between them is proved, in which direction and for which truth value, and of what can be said when no relation is proved. It covers three settings.

- **Maps between relational structures** with one binary relation R, one unary predicate P and equality. For each of seven syntactic classes of first-order formulas with parameters (quantifier-free, universal, existential, ∀∃, ∃∀, positive, positive existential), each of four map kinds (homomorphism, strong homomorphism, embedding, surjective homomorphism) and each of the two directions, the Boolean table `licensedB` is true exactly when every formula of the class transfers along every map of that kind in that direction. Each of its 9 licensed cells is proved by a preservation theorem (the quantifier-free cells and the easy directions of the Łoś–Tarski, Lyndon and homomorphism preservation theorems); each of its 47 unlicensed cells is refuted by one of 13 named countermodels on structures with one or two elements. A cell is unlicensed exactly when there are a formula of the class (with parameters), a structure at the known end with an environment at which the formula holds, and two maps of that kind (not necessarily distinct), neither an isomorphism, such that the formula holds at the other end of one map and fails at the other end of the other map, each time evaluated at a compatible environment: for a forward cell, the image h ∘ e of the source environment e; for a backward cell, a source environment e that h sends to the known target environment b pointwise (h (e i) = b i for every i). The table is also re-indexed by orientation (a map from model to system, or from system to model) and by truth value.
- **Simulations between unlabelled transition systems.** Suppose a relation S from a concrete system C to an abstract system A relates every initial concrete state to some initial abstract state and matches every concrete step from a related pair by zero or more abstract steps (a forward simulation). Then an invariant of every reachable abstract state transfers down as an existential pullback (every reachable concrete state is related to some abstract state satisfying it), and, if every abstract state related to a bad concrete state is bad, every reachable bad concrete state is related to a reachable bad abstract state. Reachable abstract bugs transfer down when the converse relation is a forward simulation from A to C and every concrete state related to a bad abstract state is bad. Suppose that S relates every initial concrete state to some initial abstract state; that S matches every concrete step from an S-related pair by one abstract step (lock-step, card 15), or by one abstract step or by no abstract step with a strict decrease of a measure μ(c, a) in a well-founded relation (card 17); and that every reachable state of A terminates in the universal sense: it is accessible for the converse step relation, so no run from it is infinite (`Terminates.no_infinite_run`). Then every reachable state of C terminates in the same sense. Countermodels show that, under a forward simulation, the universal pullback can fail, an abstract bug need not have a concrete counterpart, termination need not transfer when concrete steps may be matched by no abstract step, and weak termination (reaching some state with no successor) need not transfer even along a lock-step simulation (`weak_termination_does_not_transfer_down_lockstep`).
- **No relation.** For a class KM of models, a class KS of systems and a sentence φ, the statement 'for every model T in KM and every system R in KS, if φ holds in T then φ holds in R' is true exactly when φ is unsatisfiable in KM or valid in KS; the corresponding statements for falsity transfer and for refutation are characterized in the same form, each by a disjunction of a condition on KM and a condition on KS (card 18).

Every result is a kernel-checked theorem about this toy model.

An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.

**Scope.** Model–system relation: none proved. The structures, formulas and transition systems are abstract toy definitions, and no embedding, homomorphism, abstraction or simulation between them and any real model, modelling formalism, verification tool or system is defined or proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any particular modelling formalism, verification tool or real system. Inside the package, a relation between a model and a system (an embedding, a homomorphism of a stated kind, or a forward simulation in a stated direction) is always a hypothesis of a theorem. Each connection to verification practice is a separate claim labelled `Basis: derived (modeling bridge)`, with its reasoning.

What each result does *not* show is listed under **Boundaries**, first subsection (**Non-claims**), card by card; read the non-claims of a card together with its plain claim. Every package identifier named in this report is quoted verbatim, with its `file:line` range, under **Applicability → Definitions** (definitions), **Findings** (card statements) or **Findings → Auxiliary statements cited by name**.

Results (plain-language claims, verbatim from `results.json`):

1. **`univ-preserved-to-substructure-along-embedding`** (theorem, T0, shallow). For structures A, B and a map h : A → B that is injective and preserves and reflects R and P (an embedding: A is isomorphic via h to the induced substructure of B on the image of h), every universal formula φ (a possibly empty ∀-prefix over a quantifier-free matrix; negation and equality allowed) that holds in B under the environment h ∘ e holds in A under e.
2. **`exist-preserved-to-extension-along-embedding`** (theorem, T0, shallow). For structures A, B and a map h : A → B that is injective and preserves and reflects R and P (an embedding, so B is an extension of A), every existential formula φ (a possibly empty ∃-prefix over a quantifier-free matrix; negation and equality allowed) that holds in A under e holds in B under h ∘ e.
3. **`positive-existential-preserved-forward-along-homomorphism`** (theorem, T0, shallow). For structures A, B and a map h : A → B that preserves R and P (a homomorphism; not necessarily injective, surjective or reflecting), every positive existential formula φ (no negation and no ∀; ∃ may occur under ∧ and ∨) that holds in A under e holds in B under h ∘ e.
4. **`positive-preserved-forward-along-surjective-homomorphism`** (theorem, T0, shallow). For structures A, B and a map h : A → B that is surjective and preserves R and P (a surjective homomorphism; reflection not required), every positive formula φ (no negation; both quantifiers and equality allowed, quantifiers may occur under ∧ and ∨) that holds in A under e holds in B under h ∘ e.
5. **`five-unlicensed-transfers-countermodels`** (counterexample, T0, definitional). Five transfers fail, each on structures with at most two elements, checked by evaluation: (1) ∀x ∃y, R x y holds in the 2-cycle `S2Cyc` and fails in its one-element induced substructure `S1N`; (2) ∃x, P x holds in `S2NP` and fails in its one-element induced substructure `S1N`; (3) ∀x, P x holds in `S1P` and fails in its two-element extension `S2PN`; (4) ∃x, ¬ P x holds in `S1N` and fails in `S1P` after the bijective homomorphism `raiseP`; (5) ∀x ∀y, R x y → x = y holds in `S2E` and fails in `S2R01` after the bijective homomorphism `addEdge`. Each theorem also states the class memberships and map laws that hold in its instance.
6. **`transfer-matrix-boolean-table-agrees-with-preservation`** (characterization, T1, substantive). For each of the seven syntactic classes (quantifier-free, universal, existential, ∀∃, ∃∀, positive, positive existential), each of the four map kinds (homomorphism, strong homomorphism, embedding, surjective homomorphism) and each direction (forward from source to target, backward from target to source), the Boolean table `licensedB` is true exactly when every formula of the class (with parameters) transfers along every map of that kind in that direction (`licensedB_iff`); every one of the 56 cells is decided by a licensing theorem or a named countermodel (`cell_status`). For every class except the quantifier-free one, the same table is exact for sentences (`licensedB_iff_preservesSent_of_ne_qf`, hypothesis c ≠ qf). A formula that belongs to some class licensed for (k, d) transfers along every k-map in direction d (`transfer_of_licensedForB`, hypothesis licensedForB φ k d = true).
7. **`model-embeds-into-system-counterexamples-and-witnesses-transfer`** (theorem, T0, shallow). Let h : M → S be an embedding of a model M into a system S (M is isomorphic via h to the induced substructure of S on the image of h). Then a universal formula that fails in M under e fails in S under h ∘ e, and an existential formula that holds in M under e holds in S under h ∘ e. Model truth of a universal formula does not in general determine its truth in S: the model `S1P` satisfies ∀x, P x and has two non-surjective embeddings, into `S2PP`, where the sentence holds, and into `S2PN`, where it fails.
8. **`system-embeds-into-model-universal-proofs-transfer-counterexamples-may-be-spurious`** (theorem, T0, shallow). Let h : S → M be an embedding of a system S into a model M (M extends S by extra elements and agrees with S on the atomic facts about S's elements). Then a universal formula that holds in M under h ∘ e holds in S under e. Model counterexamples to universal formulas, and model witnesses to existential formulas, may be spurious: ∀x, P x fails in the model `S2PN` and holds in the system `S1P` embedded by `inclPN`; ∃x, P x holds in the model `S2NP` and fails in the system `S1N` embedded by `inclNP`.
9. **`forward-simulation-relates-reachable-states`** (theorem, T0, shallow). If S relates every initial concrete state to some initial abstract state (`SimInit`) and matches every concrete step from an S-related pair by zero or more abstract steps ending in an S-related pair (`SimStepStar`), then every reachable concrete state is S-related to some reachable abstract state.
10. **`safety-invariant-transfers-down-as-existential-pullback`** (theorem, T0, shallow). Under `SimInit` and `SimStepStar`, if an invariant I holds on every reachable abstract state, then every reachable concrete state c satisfies the existential pullback: some abstract state a with S c a satisfies I.
11. **`strong-pullback-fails-with-unreachable-related-abstract-state`** (counterexample, T0, definitional). In a forward simulation from the one-state `tsHalt` to `tsBoolHalt` (abstract `true` unreachable) with S total, the invariant I a := a = false holds on every reachable abstract state, yet the reachable concrete state is S-related to an abstract state violating I: the universal pullback {c | ∀ a, S c a → I a} fails, while the existential pullback holds.
12. **`bugs-transfer-up-along-forward-simulation`** (theorem, T0, shallow). Under `SimInit` and `SimStepStar`, if every abstract state S-related to a bad concrete state is bad (hbad), then every reachable bad concrete state is S-related to a reachable bad abstract state.
13. **`spurious-abstract-counterexample-under-forward-simulation`** (counterexample, T0, definitional). `relHaltTwoStep` is a forward simulation from the one-state `tsHalt` to `tsTwoStep` (false → true); related states agree on badness (`badNone`, `badTrue`: no concrete state is bad, the abstract state `true` is bad); the converse relation relates initial states but does not match the abstract step false → true. The abstract system reaches its bad state, while no reachable concrete state is bad and no concrete state is related to the abstract bad state.
14. **`abstract-bugs-transfer-down-along-converse-simulation`** (theorem, T0, definitional). If the converse relation (a ↦ c when S c a) relates every initial abstract state to an initial concrete state and matches every abstract step from a related pair by zero or more concrete steps (a forward simulation from A to C), and every concrete state S-related to a bad abstract state is bad, then every reachable bad abstract state is S-related to a reachable bad concrete state. S itself is not assumed to be a forward simulation from C to A.
15. **`termination-transfers-down-along-lockstep-simulation`** (theorem, T0, shallow). If S relates every initial concrete state to some initial abstract state (`SimInit`) and matches every concrete step from an S-related pair by a single abstract step (`SimStepLock`: one step, the matching successor need not be unique), and every reachable state of A terminates (accessible for the converse step relation), then every reachable state of C terminates.
16. **`stuttering-simulation-does-not-transfer-termination`** (counterexample, T0, definitional). From the one-state self-loop `tsLoop` to the one-state halting `tsHalt`, the total relation relates initial states and matches the concrete step by zero abstract steps (`SimStepStutter`, hence also `SimStepStar`) but is not lock-step; every reachable abstract state terminates; the reachable concrete state does not (¬ AllRunsFinite tsLoop), and the concrete system has an explicit infinite run from a reachable state.
17. **`well-founded-simulation-criterion-transfers-termination`** (theorem, T0, substantive). If S relates every initial concrete state to some initial abstract state (`SimInit`), every concrete step from an S-related pair is matched either by one abstract step or by no abstract step with a strict decrease of a measure μ(c, a) in a well-founded relation lt (`SimStepWF`), and every reachable state of A terminates (accessible for the converse step relation), then every reachable state of C terminates.
18. **`no-relation-transfer-iff-decided-by-model-or-system-class`** (characterization, T0, definitional). Let KM be a class of models, KS a class of systems and φ a sentence, with no map between model and system assumed. The statement 'for every model T in KM and every system R in KS, if φ holds in T then φ holds in R' is true exactly when φ is unsatisfiable in KM or valid in KS (`unrelated_truth_transfer_iff`). The statement 'for every model T in KM and every system R in KS, if φ fails in T then φ fails in R' is true exactly when φ is valid in KM or unsatisfiable in KS (`unrelated_falsity_transfer_iff`). The statement 'for every model T in KM and every system R in KS, if φ holds in T then φ fails in R' (reading a model result as a refutation) is true exactly when φ is unsatisfiable in KM or unsatisfiable in KS (`unrelated_refutation_licensed_iff`); for KM = KS = K, the statement 'for every T and every R in K, if φ holds in T then φ fails in R' is true exactly when φ is unsatisfiable in K (`unrelated_refutation_licensed_iff_unsat_same_class`). In each statement both quantifiers range over the whole implication: it says that for each model T of KM in which the premise holds, the conclusion holds in every system of KS. If φ holds in some model of KM and KS contains both a system satisfying φ and one falsifying it, then there is a model T of KM satisfying φ such that KS contains a system satisfying φ and a system falsifying φ, so this model result is consistent with both system outcomes (`unrelated_model_result_consistent_with_both`).
19. **`unlicensed-cell-admits-both-outcomes-along-non-isomorphisms`** (characterization, T1, shallow). For every class c, map kind k and direction d, the cell (c, k, d) is unlicensed in the transfer table exactly when it admits both outcomes along non-isomorphisms (`bothOutcomesNonIso_iff_unlicensed`): there is a formula φ of class c (with parameters), a structure at the known end with an environment at which φ holds, and two k-maps, neither an isomorphism, such that φ holds at the other end of one and fails at the other end of the other. For a forward cell the known end is the source A with environment e, and φ is evaluated in each target at h ∘ e. For a backward cell the known end is the target B with environment b; each of the two maps h comes with a source environment e that it sends to b pointwise (h (e i) = b i for every i), and φ is evaluated in the source at that e. The two maps need not be distinct: in `both_eq` both outcomes use the map `collapse`, with two different source environments. Unlicensed does not mean that nothing transfers: model-side falsity is licensed while model-side truth is not for exactly seven (kind, orientation, class) triples (`falsity_licensed_where_truth_unlicensed_iff`), and some unlicensed cells contain proper subclasses that transfer (`unlicensed_cells_contain_transferring_subclasses`).
20. **`exact-licences-per-map-kind-and-orientation`** (characterization, T0, shallow). For every map kind k, orientation o (h : model → system, or h : system → model) and class c: model-side truth of class-c formulas (with parameters, the environment pushed along h) is licensed for the system along every k-map in orientation o exactly when c ∈ truthList k o, and model-side falsity exactly when c ∈ falsityList k o. Model to system: embedding — truth [qf, exist, posExist], falsity [qf, univ]; strong homomorphism and homomorphism — truth [posExist], falsity []; surjective homomorphism — truth [pos, posExist], falsity []. System to model: embedding — truth [qf, univ], falsity [qf, exist, posExist]; strong homomorphism and homomorphism — truth [], falsity [posExist]; surjective homomorphism — truth [], falsity [pos, posExist].

## Applicability

**Model fidelity.** All definitions are toy models written for this package; none is a production definition of an existing tool or formalism. They are meant to capture the logical core of a common step in verification: a property is established for a model (a test model, an abstraction, an under-approximation, a finite-state model) and is then read as a statement about the system it models. Components and known gaps:

- *Structures and formulas.* A structure (`Str`) is a carrier in `Type`, which may be empty, with one binary relation R and one unary predicate P. Formulas (`Fml`) are first-order formulas over R, P and equality with negation, ∧, ∨, ∀ and ∃, written with de Bruijn indices; `Sat` is the usual satisfaction relation. Not modelled: further relation or predicate symbols, function symbols and constants, several sorts, the nullary atoms ⊤ and ⊥ (so there are no quantifier-free sentences), and properties beyond first-order logic, such as reachability of unbounded length.
- *Claim shapes.* Seven syntactic classes (`Cls`): quantifier-free, universal, existential, ∀∃ and ∃∀ (prenex, with possibly empty prefixes), positive and positive existential (not prenex: quantifiers may occur under ∧ and ∨). Membership is syntactic: a formula that is merely logically equivalent to a class member is not covered.
- *Relations between structures.* Four map kinds (`MapKind`): homomorphisms (`IsHom`), strong homomorphisms (`IsStrongHom`: preserve and reflect R and P; usage of the term varies in the literature), embeddings (`IsEmbedding`) and surjective homomorphisms (`IsSurjHom`); two directions (`Dir`) and two orientations (`Orient`). Transfer is for formulas with parameters: along h : A → B, an environment e of A becomes h ∘ e. Not modelled as columns of the table: isomorphisms, elementary embeddings, surjective strong homomorphisms, partial maps, relations that are not functions, and Galois connections.
- *Transition systems.* A transition system (`TS`) is a state type, a step relation and an initial-state predicate, without labels, traces, fairness or acceptance conditions. Safety is a predicate on single reachable states (`Reach`); termination is accessibility for the converse step relation (`Terminates`, `AllRunsFinite`); weak termination is `WeaklyTerminates`. The simulation laws (`SimInit`, `SimStepStar`, `SimStepLock`, `SimStepStutter`, `SimStepWF`) require matching from every related pair, reachable or not. Not modelled: labelled traces, backward simulations in the sense of Lynch and Vaandrager (1995, §3.3), matching by several abstract steps together with a measure, and liveness properties other than termination.
- *No relation.* Classes of models and of systems are predicates on structures; validity and unsatisfiability in a class are `ValidIn` and `UnsatIn`.

**Model–system relation: none proved.** No embedding, homomorphism, abstraction or simulation relating the toy definitions to any real model, modelling formalism, verification tool or system is defined or proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any particular modelling formalism, verification tool or real system. The relations the package studies (maps of the four kinds, forward simulations) relate toy structures or toy transition systems to each other, and they appear as hypotheses of theorems. Each connection this report draws between a theorem and verification practice is a separate claim, labelled `Basis: derived (modeling bridge)` in the card it belongs to, with its reasoning.

**Toolchain.** Lean `leanprover/lean4:v4.34.1` (commit `5045d0056413266e57c625dcd7c365b10e377c52`), core library with no Mathlib, no `Std` import and no other Lake dependency. The Lake package `toy_model_transfer` in `lean/` has one library, `ToyTransfer`, with the modules `Basic`, `Maps`, `Preservation`, `FinModels`, `Countermodels`, `Matrix`, `Direction`, `Simulation`, `SimCountermodels`, `Disclaimer`, `Examples` and `Unfolded`; every declaration lives in the namespace `Toy.Transfer`. Proofs use classical logic where needed; the axiom audit under **Evidence** lists the axioms of each declaration.

**Subjects.** `REPORT.json` lists the Lean toolchain, which checks every proof; the cited works that have a DOI, each identified by its DOI (among them the books of Hodges 1993 and of Chang and Keisler 1990 and the proceedings paper of Floyd 1967); Łoś (1955), identified by its EuDML record; Sternagel and Thiemann (2010), an Archive of Formal Proofs entry for which no DOI was found at Crossref, identified by its entry page; and the two source repositories consulted at fixed commits for prior-art comparison (Mathlib's model-theory library and CompCert's `common/Smallstep.v`). None of the cited works is formalized here, and the package depends on none of them; each card's prior-art entries state what was taken from each source. Milner (1971), a proceedings paper for which no DOI was found at Crossref, is not listed in `REPORT.json`; its bibliographic record is under **Evidence → Primary sources**.

**Conventions.** Formulas use de Bruijn indices: inside a quantifier, index `0` is the bound variable (so under `∀x ∀y`, `y` is `0` and `x` is `1`). Sentences are `Fml 0`, evaluated in the empty environment `Fin.elim0`. Transfer is for formulas with parameters: along `h : A → B`, the source environment `e` becomes `h ∘ e`. Direction `fwd` means from the source `A` to the target `B`; `bwd` from `B` back to `A`. Carriers may be empty. There are no nullary atoms, hence no quantifier-free sentences. The universal, existential, `∀∃` and `∃∀` classes are prenex; the positive and positive existential classes are not.

### Definitions (verbatim)

The package definitions used by the card statements; every further package declaration named in this report is quoted under **Findings → Auxiliary statements cited by name**. Each block quotes the source verbatim; its first line gives the file (relative to `lean/`) and the line range; definition bodies are quoted in full. In `ToyTransfer/Maps.lean` (section `Laws`) and `ToyTransfer/Preservation.lean` the section variables `{A B : Str}` are in scope; in the `FinLaws` section of `ToyTransfer/Maps.lean`, `{m k : Nat} {M : FinStr m} {N : FinStr k} {h : Fin m → Fin k}`. Theorem proofs are elided as `:= …`.

#### Structures and formulas

```lean
-- ToyTransfer/Basic.lean:23-26
structure Str where
  carrier : Type
  R : carrier → carrier → Prop
  P : carrier → Prop

-- ToyTransfer/Basic.lean:31-39
inductive Fml : Nat → Type where
  | rel {n : Nat} : Fin n → Fin n → Fml n
  | pred {n : Nat} : Fin n → Fml n
  | eq {n : Nat} : Fin n → Fin n → Fml n
  | neg {n : Nat} : Fml n → Fml n
  | and {n : Nat} : Fml n → Fml n → Fml n
  | or {n : Nat} : Fml n → Fml n → Fml n
  | all {n : Nat} : Fml (n + 1) → Fml n
  | ex {n : Nat} : Fml (n + 1) → Fml n

-- ToyTransfer/Basic.lean:42
def Fml.imp {n : Nat} (φ ψ : Fml n) : Fml n := .or (.neg φ) ψ

-- ToyTransfer/Basic.lean:46-48
def Env.cons {α : Type} {n : Nat} (a : α) (e : Fin n → α) : Fin (n + 1) → α
  | ⟨0, _⟩ => a
  | ⟨i + 1, hi⟩ => e ⟨i, Nat.lt_of_succ_lt_succ hi⟩

-- ToyTransfer/Basic.lean:51-59
def Sat (M : Str) : {n : Nat} → Fml n → (Fin n → M.carrier) → Prop
  | _, .rel i j, e => M.R (e i) (e j)
  | _, .pred i, e => M.P (e i)
  | _, .eq i j, e => e i = e j
  | _, .neg φ, e => ¬ Sat M φ e
  | _, .and φ ψ, e => Sat M φ e ∧ Sat M ψ e
  | _, .or φ ψ, e => Sat M φ e ∨ Sat M ψ e
  | _, .all φ, e => ∀ a : M.carrier, Sat M φ (Env.cons a e)
  | _, .ex φ, e => ∃ a : M.carrier, Sat M φ (Env.cons a e)

-- ToyTransfer/Basic.lean:62
def SatS (M : Str) (φ : Fml 0) : Prop := Sat M φ Fin.elim0
```

Examples: `sat_pos_example`, `sat_neg_example`, `satS_pos_example`, `satS_neg_example`, `env_cons_example`, `emptyStr_example` (empty carrier admitted), `exSelfEq_valid_iff_nonempty_carriers`.

#### Syntactic classes

```lean
-- ToyTransfer/Basic.lean:80-86
inductive IsQF {n : Nat} : Fml n → Prop where
  | rel (i j : Fin n) : IsQF (.rel i j)
  | pred (i : Fin n) : IsQF (.pred i)
  | eq (i j : Fin n) : IsQF (.eq i j)
  | neg {φ : Fml n} : IsQF φ → IsQF (.neg φ)
  | and {φ ψ : Fml n} : IsQF φ → IsQF ψ → IsQF (.and φ ψ)
  | or {φ ψ : Fml n} : IsQF φ → IsQF ψ → IsQF (.or φ ψ)

-- ToyTransfer/Basic.lean:101-108
inductive IsEqFree : {n : Nat} → Fml n → Prop where
  | rel {n : Nat} (i j : Fin n) : IsEqFree (.rel i j)
  | pred {n : Nat} (i : Fin n) : IsEqFree (.pred i)
  | neg {n : Nat} {φ : Fml n} : IsEqFree φ → IsEqFree (.neg φ)
  | and {n : Nat} {φ ψ : Fml n} : IsEqFree φ → IsEqFree ψ → IsEqFree (.and φ ψ)
  | or {n : Nat} {φ ψ : Fml n} : IsEqFree φ → IsEqFree ψ → IsEqFree (.or φ ψ)
  | all {n : Nat} {φ : Fml (n + 1)} : IsEqFree φ → IsEqFree (.all φ)
  | ex {n : Nat} {φ : Fml (n + 1)} : IsEqFree φ → IsEqFree (.ex φ)

-- ToyTransfer/Basic.lean:112-114
inductive IsUniv : {n : Nat} → Fml n → Prop where
  | qf {n : Nat} {φ : Fml n} : IsQF φ → IsUniv φ
  | all {n : Nat} {φ : Fml (n + 1)} : IsUniv φ → IsUniv (.all φ)

-- ToyTransfer/Basic.lean:118-120
inductive IsExist : {n : Nat} → Fml n → Prop where
  | qf {n : Nat} {φ : Fml n} : IsQF φ → IsExist φ
  | ex {n : Nat} {φ : Fml (n + 1)} : IsExist φ → IsExist (.ex φ)

-- ToyTransfer/Basic.lean:123-125
inductive IsAE : {n : Nat} → Fml n → Prop where
  | exist {n : Nat} {φ : Fml n} : IsExist φ → IsAE φ
  | all {n : Nat} {φ : Fml (n + 1)} : IsAE φ → IsAE (.all φ)

-- ToyTransfer/Basic.lean:128-130
inductive IsEA : {n : Nat} → Fml n → Prop where
  | univ {n : Nat} {φ : Fml n} : IsUniv φ → IsEA φ
  | ex {n : Nat} {φ : Fml (n + 1)} : IsEA φ → IsEA (.ex φ)

-- ToyTransfer/Basic.lean:134-141
inductive IsPos : {n : Nat} → Fml n → Prop where
  | rel {n : Nat} (i j : Fin n) : IsPos (.rel i j)
  | pred {n : Nat} (i : Fin n) : IsPos (.pred i)
  | eq {n : Nat} (i j : Fin n) : IsPos (.eq i j)
  | and {n : Nat} {φ ψ : Fml n} : IsPos φ → IsPos ψ → IsPos (.and φ ψ)
  | or {n : Nat} {φ ψ : Fml n} : IsPos φ → IsPos ψ → IsPos (.or φ ψ)
  | all {n : Nat} {φ : Fml (n + 1)} : IsPos φ → IsPos (.all φ)
  | ex {n : Nat} {φ : Fml (n + 1)} : IsPos φ → IsPos (.ex φ)

-- ToyTransfer/Basic.lean:145-151
inductive IsPosExist : {n : Nat} → Fml n → Prop where
  | rel {n : Nat} (i j : Fin n) : IsPosExist (.rel i j)
  | pred {n : Nat} (i : Fin n) : IsPosExist (.pred i)
  | eq {n : Nat} (i j : Fin n) : IsPosExist (.eq i j)
  | and {n : Nat} {φ ψ : Fml n} : IsPosExist φ → IsPosExist ψ → IsPosExist (.and φ ψ)
  | or {n : Nat} {φ ψ : Fml n} : IsPosExist φ → IsPosExist ψ → IsPosExist (.or φ ψ)
  | ex {n : Nat} {φ : Fml (n + 1)} : IsPosExist φ → IsPosExist (.ex φ)
```

Examples: `isQF_examples`, `isEqFree_examples`, `isUniv_examples`, `isExist_examples`, `isAE_examples`, `isEA_examples`, `isPos_examples`, `isPosExist_examples`, `posExist_not_subset_exist`, `no_qf_sentences`.

#### Map laws and map kinds

```lean
-- ToyTransfer/Maps.lean:16
def PreservesR (h : A.carrier → B.carrier) : Prop := ∀ a b, A.R a b → B.R (h a) (h b)

-- ToyTransfer/Maps.lean:19
def PreservesP (h : A.carrier → B.carrier) : Prop := ∀ a, A.P a → B.P (h a)

-- ToyTransfer/Maps.lean:22
def ReflectsR (h : A.carrier → B.carrier) : Prop := ∀ a b, B.R (h a) (h b) → A.R a b

-- ToyTransfer/Maps.lean:25
def ReflectsP (h : A.carrier → B.carrier) : Prop := ∀ a, B.P (h a) → A.P a

-- ToyTransfer/Maps.lean:28-30
structure IsHom (h : A.carrier → B.carrier) : Prop where
  presR : PreservesR h
  presP : PreservesP h

-- ToyTransfer/Maps.lean:39-43
structure IsStrongHom (h : A.carrier → B.carrier) : Prop where
  presR : PreservesR h
  presP : PreservesP h
  reflR : ReflectsR h
  reflP : ReflectsP h

-- ToyTransfer/Maps.lean:51-56
structure IsEmbedding (h : A.carrier → B.carrier) : Prop where
  inj : Function.Injective h
  presR : PreservesR h
  presP : PreservesP h
  reflR : ReflectsR h
  reflP : ReflectsP h

-- ToyTransfer/Maps.lean:59-62
structure IsSurjHom (h : A.carrier → B.carrier) : Prop where
  surj : Function.Surjective h
  presR : PreservesR h
  presP : PreservesP h

-- ToyTransfer/Maps.lean:65-67
def IsIso (h : A.carrier → B.carrier) : Prop :=
  Function.Injective h ∧ Function.Surjective h ∧ PreservesR h ∧ PreservesP h ∧
    ReflectsR h ∧ ReflectsP h

-- ToyTransfer/Maps.lean:84-89
inductive MapKind where
  | hom
  | strong
  | emb
  | surj
  deriving DecidableEq, Repr

-- ToyTransfer/Maps.lean:92-96
def MapKind.Holds : MapKind → {A B : Str} → (A.carrier → B.carrier) → Prop
  | .hom, _, _, h => IsHom h
  | .strong, _, _, h => IsStrongHom h
  | .emb, _, _, h => IsEmbedding h
  | .surj, _, _, h => IsSurjHom h
```

Examples: `preservesR_examples`, `preservesP_examples`, `reflectsR_examples`, `reflectsP_examples`, `isHom_examples`, `isStrongHom_examples`, `isEmbedding_examples`, `isSurjHom_examples`, `isIso_examples`, `mapKind_holds_examples`, `injective_hom_not_embedding_example`; the identity is a map of every kind (`MapKind.holds_id`).

#### Directions, classes, transfer

```lean
-- ToyTransfer/Maps.lean:116-119
inductive Dir where
  | fwd
  | bwd
  deriving DecidableEq, Repr

-- ToyTransfer/Maps.lean:123-125
def Dir.Transfer : Dir → Prop → Prop → Prop
  | .fwd, p, q => p → q
  | .bwd, p, q => q → p

-- ToyTransfer/Maps.lean:128-136
inductive Cls where
  | qf
  | univ
  | exist
  | ae
  | ea
  | pos
  | posExist
  deriving DecidableEq, Repr

-- ToyTransfer/Maps.lean:139-146
def Cls.Mem : Cls → {n : Nat} → Fml n → Prop
  | .qf, _, φ => IsQF φ
  | .univ, _, φ => IsUniv φ
  | .exist, _, φ => IsExist φ
  | .ae, _, φ => IsAE φ
  | .ea, _, φ => IsEA φ
  | .pos, _, φ => IsPos φ
  | .posExist, _, φ => IsPosExist φ

-- ToyTransfer/Maps.lean:149-156
def Cls.test : Cls → {n : Nat} → Fml n → Bool
  | .qf, _, φ => φ.qfB
  | .univ, _, φ => φ.univB
  | .exist, _, φ => φ.existB
  | .ae, _, φ => φ.aeB
  | .ea, _, φ => φ.eaB
  | .pos, _, φ => φ.posB
  | .posExist, _, φ => φ.posExistB

-- ToyTransfer/Maps.lean:175-178
def Preserves (c : Cls) (k : MapKind) (d : Dir) : Prop :=
  ∀ (A B : Str) (h : A.carrier → B.carrier), k.Holds h →
    ∀ (n : Nat) (φ : Fml n), c.Mem φ → ∀ e : Fin n → A.carrier,
      d.Transfer (Sat A φ e) (Sat B φ (h ∘ e))

-- ToyTransfer/Maps.lean:182-184
def PreservesSent (c : Cls) (k : MapKind) (d : Dir) : Prop :=
  ∀ (A B : Str) (h : A.carrier → B.carrier), k.Holds h →
    ∀ φ : Fml 0, c.Mem φ → d.Transfer (SatS A φ) (SatS B φ)
```

Examples: `dir_transfer_examples`, `cls_test_examples`, `preserves_examples`, `preservesSent_examples`; `Cls.test_iff`, `Preserves.toSent`.

#### Finite structures, maps and formulas used by the countermodels

```lean
-- ToyTransfer/Maps.lean:223-225
structure FinStr (k : Nat) where
  r : Fin k → Fin k → Bool
  p : Fin k → Bool

-- ToyTransfer/Maps.lean:228-231
@[reducible] def FinStr.toStr {k : Nat} (M : FinStr k) : Str where
  carrier := Fin k
  R a b := M.r a b = true
  P a := M.p a = true

-- ToyTransfer/FinModels.lean:15
def S1P : FinStr 1 := ⟨fun _ _ => false, fun _ => true⟩

-- ToyTransfer/FinModels.lean:17
def S1N : FinStr 1 := ⟨fun _ _ => false, fun _ => false⟩

-- ToyTransfer/FinModels.lean:19
def S1R : FinStr 1 := ⟨fun _ _ => true, fun _ => false⟩

-- ToyTransfer/FinModels.lean:21
def S2PN : FinStr 2 := ⟨fun _ _ => false, fun a => a.val == 0⟩

-- ToyTransfer/FinModels.lean:23
def S2NP : FinStr 2 := ⟨fun _ _ => false, fun a => a.val == 1⟩

-- ToyTransfer/FinModels.lean:25
def S2E : FinStr 2 := ⟨fun _ _ => false, fun _ => false⟩

-- ToyTransfer/FinModels.lean:27
def S2Cyc : FinStr 2 := ⟨fun a b => a.val != b.val, fun _ => false⟩

-- ToyTransfer/FinModels.lean:29
def S2R01 : FinStr 2 := ⟨fun a b => a.val == 0 && b.val == 1, fun _ => false⟩

-- ToyTransfer/FinModels.lean:31
def S2PP : FinStr 2 := ⟨fun _ _ => false, fun _ => true⟩

-- ToyTransfer/FinModels.lean:34
def S2Loop1 : FinStr 2 := ⟨fun _ b => b.val == 1, fun _ => false⟩

-- ToyTransfer/FinModels.lean:38
def S3E : FinStr 3 := ⟨fun _ _ => false, fun _ => false⟩

-- ToyTransfer/FinModels.lean:43
def inclPN : S1P.toStr.carrier → S2PN.toStr.carrier := fun _ => 0

-- ToyTransfer/FinModels.lean:45
def inclNP : S1N.toStr.carrier → S2NP.toStr.carrier := fun _ => 0

-- ToyTransfer/FinModels.lean:47
def inclCyc : S1N.toStr.carrier → S2Cyc.toStr.carrier := fun _ => 0

-- ToyTransfer/FinModels.lean:49
def raiseP : S1N.toStr.carrier → S1P.toStr.carrier := id

-- ToyTransfer/FinModels.lean:51
def lowerP : S1P.toStr.carrier → S1N.toStr.carrier := id

-- ToyTransfer/FinModels.lean:53
def raiseR : S1N.toStr.carrier → S1R.toStr.carrier := id

-- ToyTransfer/FinModels.lean:55
def lowerR : S1R.toStr.carrier → S1N.toStr.carrier := id

-- ToyTransfer/FinModels.lean:57
def addEdge : S2E.toStr.carrier → S2R01.toStr.carrier := id

-- ToyTransfer/FinModels.lean:59
def collapse : S2E.toStr.carrier → S1N.toStr.carrier := fun _ => 0

-- ToyTransfer/FinModels.lean:62
def inclPP : S1P.toStr.carrier → S2PP.toStr.carrier := fun _ => 0

-- ToyTransfer/FinModels.lean:64
def inclP1 : S1P.toStr.carrier → S2NP.toStr.carrier := fun _ => 1

-- ToyTransfer/FinModels.lean:66
def inclN1 : S1N.toStr.carrier → S2PN.toStr.carrier := fun _ => 1

-- ToyTransfer/FinModels.lean:68
def collapseTo1 : S2E.toStr.carrier → S2PN.toStr.carrier := fun _ => 1

-- ToyTransfer/FinModels.lean:70
def inclLoop : S1R.toStr.carrier → S2Loop1.toStr.carrier := fun _ => 1

-- ToyTransfer/FinModels.lean:72
def inclNoLoop : S1N.toStr.carrier → S2Loop1.toStr.carrier := fun _ => 0

-- ToyTransfer/FinModels.lean:74
def inclE23 : S2E.toStr.carrier → S3E.toStr.carrier := fun a => ⟨a.val, Nat.lt_succ_of_lt a.isLt⟩

-- ToyTransfer/FinModels.lean:76
def squashPP : S2PP.toStr.carrier → S1P.toStr.carrier := fun _ => 0

-- ToyTransfer/Countermodels.lean:175
def squashP : S2NP.toStr.carrier → S1P.toStr.carrier := fun _ => 0

-- ToyTransfer/FinModels.lean:81
def allP : Fml 0 := .all (.pred 0)

-- ToyTransfer/FinModels.lean:83
def exP : Fml 0 := .ex (.pred 0)

-- ToyTransfer/FinModels.lean:85
def allExR : Fml 0 := .all (.ex (.rel 1 0))

-- ToyTransfer/FinModels.lean:87
def exNotP : Fml 0 := .ex (.neg (.pred 0))

-- ToyTransfer/FinModels.lean:89
def allRImpEq : Fml 0 := .all (.all (Fml.imp (.rel 1 0) (.eq 1 0)))

-- ToyTransfer/FinModels.lean:91
def exExNeq : Fml 0 := .ex (.ex (.neg (.eq 1 0)))

-- ToyTransfer/FinModels.lean:93
def allAllEq : Fml 0 := .all (.all (.eq 1 0))

-- ToyTransfer/FinModels.lean:95
def allNotRxx : Fml 0 := .all (.neg (.rel 0 0))

-- ToyTransfer/FinModels.lean:97
def allNotP : Fml 0 := .all (.neg (.pred 0))

-- ToyTransfer/FinModels.lean:99
def allRxx : Fml 0 := .all (.rel 0 0)

-- ToyTransfer/FinModels.lean:101
def exRxx : Fml 0 := .ex (.rel 0 0)

-- ToyTransfer/FinModels.lean:103
def exNotRxx : Fml 0 := .ex (.neg (.rel 0 0))

-- ToyTransfer/FinModels.lean:105
def atMostOneNotP : Fml 0 := .all (.all (.or (.eq 1 0) (.or (.pred 1) (.pred 0))))

-- ToyTransfer/FinModels.lean:107
def exPAndExP : Fml 0 := .and (.ex (.pred 0)) (.ex (.pred 0))

-- ToyTransfer/FinModels.lean:109
def P0 : Fml 1 := .pred 0

-- ToyTransfer/FinModels.lean:111
def notP0 : Fml 1 := .neg (.pred 0)

-- ToyTransfer/FinModels.lean:113
def eq01 : Fml 2 := .eq 0 1

-- ToyTransfer/FinModels.lean:115
def neq01 : Fml 2 := .neg (.eq 0 1)

-- ToyTransfer/FinModels.lean:118
def env1 {α : Type} (a : α) : Fin 1 → α := Env.cons a Fin.elim0

-- ToyTransfer/FinModels.lean:120
def env2 {α : Type} (a b : α) : Fin 2 → α := Env.cons a (Env.cons b Fin.elim0)

-- ToyTransfer/Countermodels.lean:178
def allExP : Fml 0 := .all (.ex (.pred 0))

-- ToyTransfer/Examples.lean:16
def emptyStr : Str := ⟨Empty, fun _ _ => False, fun _ => False⟩

-- ToyTransfer/Examples.lean:26
def exSelfEq : Fml 0 := .ex (.eq 0 0)

-- ToyTransfer/Examples.lean:45
def exAllR : Fml 0 := .ex (.all (.rel 1 0))

-- ToyTransfer/Examples.lean:132
def contra : Fml 0 := .ex (.and (.pred 0) (.neg (.pred 0)))

-- ToyTransfer/Matrix.lean:313
def exclMid : Fml 0 := .all (.or (.pred 0) (.neg (.pred 0)))
```

Satisfaction and every map law are decidable on `FinStr` tables, so all countermodels are checked by `decide`. Every structure here has one to three elements.

#### Transfer table

```lean
-- ToyTransfer/Matrix.lean:17-23
def licensedB : Cls → MapKind → Dir → Bool
  | .qf, .emb, _ => true
  | .univ, .emb, .bwd => true
  | .exist, .emb, .fwd => true
  | .posExist, _, .fwd => true
  | .pos, .surj, .fwd => true
  | _, _, _ => false

-- ToyTransfer/Matrix.lean:280
def allCls : List Cls := [.qf, .univ, .exist, .ae, .ea, .pos, .posExist]

-- ToyTransfer/Matrix.lean:283-284
def licensedForB {n : Nat} (φ : Fml n) (k : MapKind) (d : Dir) : Bool :=
  allCls.any (fun c => c.test φ && licensedB c k d)
```

Examples: `licensedB_examples`, `licensedForB_examples`.

#### Transition systems

```lean
-- ToyTransfer/Simulation.lean:17-20
structure TS where
  St : Type
  step : St → St → Prop
  init : St → Prop

-- ToyTransfer/Simulation.lean:23-25
inductive Reach (T : TS) : T.St → Prop where
  | init {s : T.St} : T.init s → Reach T s
  | step {s t : T.St} : Reach T s → T.step s t → Reach T t

-- ToyTransfer/Simulation.lean:28-30
inductive Star {α : Type} (r : α → α → Prop) : α → α → Prop where
  | refl (a : α) : Star r a a
  | tail {a b c : α} : Star r a b → r b c → Star r a c

-- ToyTransfer/Simulation.lean:40-41
def SimInit (C A : TS) (S : C.St → A.St → Prop) : Prop :=
  ∀ c, C.init c → ∃ a, A.init a ∧ S c a

-- ToyTransfer/Simulation.lean:45-46
def SimStepStar (C A : TS) (S : C.St → A.St → Prop) : Prop :=
  ∀ c c' a, C.step c c' → S c a → ∃ a', Star A.step a a' ∧ S c' a'

-- ToyTransfer/Simulation.lean:51-52
def SimStepLock (C A : TS) (S : C.St → A.St → Prop) : Prop :=
  ∀ c c' a, C.step c c' → S c a → ∃ a', A.step a a' ∧ S c' a'

-- ToyTransfer/Simulation.lean:55-56
def SimStepStutter (C A : TS) (S : C.St → A.St → Prop) : Prop :=
  ∀ c c' a, C.step c c' → S c a → (∃ a', A.step a a' ∧ S c' a') ∨ S c' a

-- ToyTransfer/Simulation.lean:60-62
def SimStepWF (C A : TS) (S : C.St → A.St → Prop) {W : Type} (lt : W → W → Prop)
    (μ : C.St → A.St → W) : Prop :=
  ∀ c c' a, C.step c c' → S c a → (∃ a', A.step a a' ∧ S c' a') ∨ (S c' a ∧ lt (μ c' a) (μ c a))

-- ToyTransfer/Simulation.lean:84
def Terminates (T : TS) (s : T.St) : Prop := Acc (fun y x => T.step x y) s

-- ToyTransfer/Simulation.lean:88
def AllRunsFinite (T : TS) : Prop := ∀ s, Reach T s → Terminates T s

-- ToyTransfer/Simulation.lean:124
def WeaklyTerminates (T : TS) (s : T.St) : Prop := ∃ t, Star T.step s t ∧ ∀ u, ¬ T.step t u

-- ToyTransfer/SimCountermodels.lean:14
def tsLoop : TS := ⟨Unit, fun _ _ => True, fun _ => True⟩

-- ToyTransfer/SimCountermodels.lean:16
def tsHalt : TS := ⟨Unit, fun _ _ => False, fun _ => True⟩

-- ToyTransfer/SimCountermodels.lean:18
def tsTwoStep : TS := ⟨Bool, fun a b => a = false ∧ b = true, fun a => a = false⟩

-- ToyTransfer/SimCountermodels.lean:20
def tsBoolHalt : TS := ⟨Bool, fun _ _ => False, fun a => a = false⟩

-- ToyTransfer/SimCountermodels.lean:294
def tsUnreachLoop : TS := ⟨Bool, fun a b => a = true ∧ b = true, fun a => a = false⟩

-- ToyTransfer/SimCountermodels.lean:418
def tsLoopOrHalt : TS := ⟨Bool, fun a _ => a = false, fun a => a = false⟩

-- ToyTransfer/SimCountermodels.lean:232
def tsBranch3 : TS := ⟨Fin 3, fun a b => a = 0 ∧ (b = 1 ∨ b = 2), fun a => a = 0⟩

-- ToyTransfer/SimCountermodels.lean:234
def tsLine2 : TS := ⟨Fin 2, fun c c' => c = 0 ∧ c' = 1, fun c => c = 0⟩

-- ToyTransfer/SimCountermodels.lean:236
def relSameIndex : tsLine2.St → tsBranch3.St → Prop := fun c a => c.val = a.val

-- ToyTransfer/SimCountermodels.lean:167
def relHaltTwoStep : tsHalt.St → tsTwoStep.St → Prop := fun _ a => a = false

-- ToyTransfer/SimCountermodels.lean:169
def badNone : tsHalt.St → Prop := fun _ => False

-- ToyTransfer/SimCountermodels.lean:171
def badTrue : tsTwoStep.St → Prop := fun a => a = true
```

Examples: `reach_examples`, `star_examples`, `simInit_examples`, `simStepStar_examples`, `simStepLock_examples`, `simStepStutter_examples`, `simStepWF_examples`, `terminates_examples`, `allRunsFinite_examples`, `weaklyTerminates_examples`; `SimStepLock.toStar`, `SimStepStutter.toStar`, `SimStepWF.toStutter`, `Terminates.no_infinite_run`, `terminates_iff_no_infinite_run`.

#### No relation, both outcomes, licences

```lean
-- ToyTransfer/Disclaimer.lean:28
def ValidIn (K : Str → Prop) (φ : Fml 0) : Prop := ∀ M, K M → SatS M φ

-- ToyTransfer/Disclaimer.lean:31
def UnsatIn (K : Str → Prop) (φ : Fml 0) : Prop := ∀ M, K M → ¬ SatS M φ

-- ToyTransfer/Disclaimer.lean:106-114
def BothOutcomesNonIso (c : Cls) (k : MapKind) : Dir → Prop
  | .fwd => ∃ (A : Str) (n : Nat) (φ : Fml n) (e : Fin n → A.carrier), c.Mem φ ∧ Sat A φ e ∧
      (∃ (B : Str) (h : A.carrier → B.carrier), k.Holds h ∧ ¬ IsIso h ∧ Sat B φ (h ∘ e)) ∧
      (∃ (B : Str) (h : A.carrier → B.carrier), k.Holds h ∧ ¬ IsIso h ∧ ¬ Sat B φ (h ∘ e))
  | .bwd => ∃ (B : Str) (n : Nat) (φ : Fml n) (b : Fin n → B.carrier), c.Mem φ ∧ Sat B φ b ∧
      (∃ (A : Str) (h : A.carrier → B.carrier) (e : Fin n → A.carrier),
        k.Holds h ∧ ¬ IsIso h ∧ (∀ i, h (e i) = b i) ∧ Sat A φ e) ∧
      (∃ (A : Str) (h : A.carrier → B.carrier) (e : Fin n → A.carrier),
        k.Holds h ∧ ¬ IsIso h ∧ (∀ i, h (e i) = b i) ∧ ¬ Sat A φ e)

-- ToyTransfer/Disclaimer.lean:321-326
inductive Orient where
  /-- `h : model → system` (e.g. the model embeds into the system). -/
  | modelToSystem
  /-- `h : system → model` (e.g. the system embeds into the model). -/
  | systemToModel
  deriving DecidableEq, Repr

-- ToyTransfer/Disclaimer.lean:332-336
def TruthLicensed (c : Cls) (k : MapKind) : Orient → Prop
  | .modelToSystem => ∀ (M S : Str) (h : M.carrier → S.carrier), k.Holds h →
      ∀ (n : Nat) (φ : Fml n), c.Mem φ → ∀ e : Fin n → M.carrier, Sat M φ e → Sat S φ (h ∘ e)
  | .systemToModel => ∀ (S M : Str) (h : S.carrier → M.carrier), k.Holds h →
      ∀ (n : Nat) (φ : Fml n), c.Mem φ → ∀ e : Fin n → S.carrier, Sat M φ (h ∘ e) → Sat S φ e

-- ToyTransfer/Disclaimer.lean:340-346
def FalsityLicensed (c : Cls) (k : MapKind) : Orient → Prop
  | .modelToSystem => ∀ (M S : Str) (h : M.carrier → S.carrier), k.Holds h →
      ∀ (n : Nat) (φ : Fml n), c.Mem φ → ∀ e : Fin n → M.carrier,
        ¬ Sat M φ e → ¬ Sat S φ (h ∘ e)
  | .systemToModel => ∀ (S M : Str) (h : S.carrier → M.carrier), k.Holds h →
      ∀ (n : Nat) (φ : Fml n), c.Mem φ → ∀ e : Fin n → S.carrier,
        ¬ Sat M φ (h ∘ e) → ¬ Sat S φ e

-- ToyTransfer/Disclaimer.lean:349-357
def truthList : MapKind → Orient → List Cls
  | .emb, .modelToSystem => [.qf, .exist, .posExist]
  | .strong, .modelToSystem => [.posExist]
  | .hom, .modelToSystem => [.posExist]
  | .surj, .modelToSystem => [.pos, .posExist]
  | .emb, .systemToModel => [.qf, .univ]
  | .strong, .systemToModel => []
  | .hom, .systemToModel => []
  | .surj, .systemToModel => []

-- ToyTransfer/Disclaimer.lean:360-368
def falsityList : MapKind → Orient → List Cls
  | .emb, .modelToSystem => [.qf, .univ]
  | .strong, .modelToSystem => []
  | .hom, .modelToSystem => []
  | .surj, .modelToSystem => []
  | .emb, .systemToModel => [.qf, .exist, .posExist]
  | .strong, .systemToModel => [.posExist]
  | .hom, .systemToModel => [.posExist]
  | .surj, .systemToModel => [.pos, .posExist]
```

Examples: `validIn_examples`, `unsatIn_examples`, `bothOutcomesNonIso_examples`, `truthLicensed_examples`, `falsityLicensed_examples`.

### Equivalent forms of key definitions

Each block quotes an `↔` lemma of `ToyTransfer/Unfolded.lean`; its right-hand side spells the definition out.

Equivalent form of `Preserves` (forward), by the iff lemma `preserves_fwd_iff`:

```lean
-- ToyTransfer/Unfolded.lean:13-17
theorem preserves_fwd_iff (c : Cls) (k : MapKind) :
    Preserves c k .fwd ↔
      ∀ (A B : Str) (h : A.carrier → B.carrier), k.Holds h →
        ∀ (n : Nat) (φ : Fml n), c.Mem φ → ∀ e : Fin n → A.carrier,
          Sat A φ e → Sat B φ (h ∘ e) := …
```

Equivalent form of `Preserves` (backward), by the iff lemma `preserves_bwd_iff`:

```lean
-- ToyTransfer/Unfolded.lean:20-24
theorem preserves_bwd_iff (c : Cls) (k : MapKind) :
    Preserves c k .bwd ↔
      ∀ (A B : Str) (h : A.carrier → B.carrier), k.Holds h →
        ∀ (n : Nat) (φ : Fml n), c.Mem φ → ∀ e : Fin n → A.carrier,
          Sat B φ (h ∘ e) → Sat A φ e := …
```

Equivalent form of `IsEmbedding`, by the iff lemma `isEmbedding_iff`:

```lean
-- ToyTransfer/Unfolded.lean:27-31
theorem isEmbedding_iff {A B : Str} (h : A.carrier → B.carrier) :
    IsEmbedding h ↔
      (∀ a a', h a = h a' → a = a') ∧ (∀ a b, A.R a b → B.R (h a) (h b)) ∧
      (∀ a, A.P a → B.P (h a)) ∧ (∀ a b, B.R (h a) (h b) → A.R a b) ∧
      (∀ a, B.P (h a) → A.P a) := …
```

Equivalent form of `IsSurjHom`, by the iff lemma `isSurjHom_iff`:

```lean
-- ToyTransfer/Unfolded.lean:35-37
theorem isSurjHom_iff {A B : Str} (h : A.carrier → B.carrier) :
    IsSurjHom h ↔
      (∀ b, ∃ a, h a = b) ∧ (∀ a b, A.R a b → B.R (h a) (h b)) ∧ (∀ a, A.P a → B.P (h a)) := …
```

Equivalent form of `IsIso`, by the iff lemma `isIso_iff`:

```lean
-- ToyTransfer/Unfolded.lean:66-70
theorem isIso_iff {A B : Str} (h : A.carrier → B.carrier) :
    IsIso h ↔
      (∀ a a', h a = h a' → a = a') ∧ (∀ b, ∃ a, h a = b) ∧
      (∀ a b, A.R a b → B.R (h a) (h b)) ∧ (∀ a, A.P a → B.P (h a)) ∧
      (∀ a b, B.R (h a) (h b) → A.R a b) ∧ (∀ a, B.P (h a) → A.P a) := …
```

Equivalent form of the licensed cells of `licensedB`, by the iff lemma `licensedB_eq_true_iff`:

```lean
-- ToyTransfer/Unfolded.lean:41-45
theorem licensedB_eq_true_iff (c : Cls) (k : MapKind) (d : Dir) :
    licensedB c k d = true ↔
      (c = .qf ∧ k = .emb) ∨ (c = .univ ∧ k = .emb ∧ d = .bwd) ∨
      (c = .exist ∧ k = .emb ∧ d = .fwd) ∨ (c = .posExist ∧ d = .fwd) ∨
      (c = .pos ∧ k = .surj ∧ d = .fwd) := …
```

Equivalent form of `AllRunsFinite`, by the iff lemma `allRunsFinite_iff`:

```lean
-- ToyTransfer/Unfolded.lean:48-49
theorem allRunsFinite_iff (T : TS) :
    AllRunsFinite T ↔ ∀ s, Reach T s → Acc (fun y x => T.step x y) s := …
```

Equivalent form of `SimStepWF`, by the iff lemma `simStepWF_iff`:

```lean
-- ToyTransfer/Unfolded.lean:52-56
theorem simStepWF_iff (C A : TS) (S : C.St → A.St → Prop) {W : Type} (lt : W → W → Prop)
    (μ : C.St → A.St → W) :
    SimStepWF C A S lt μ ↔
      ∀ c c' a, C.step c c' → S c a →
        (∃ a', A.step a a' ∧ S c' a') ∨ (S c' a ∧ lt (μ c' a) (μ c a)) := …
```

Equivalent form of `BothOutcomesNonIso` (forward), by the iff lemma `bothOutcomesNonIso_fwd_iff`:

```lean
-- ToyTransfer/Unfolded.lean:59-63
theorem bothOutcomesNonIso_fwd_iff (c : Cls) (k : MapKind) :
    BothOutcomesNonIso c k .fwd ↔
      ∃ (A : Str) (n : Nat) (φ : Fml n) (e : Fin n → A.carrier), c.Mem φ ∧ Sat A φ e ∧
        (∃ (B : Str) (h : A.carrier → B.carrier), k.Holds h ∧ ¬ IsIso h ∧ Sat B φ (h ∘ e)) ∧
        (∃ (B : Str) (h : A.carrier → B.carrier), k.Holds h ∧ ¬ IsIso h ∧ ¬ Sat B φ (h ∘ e)) := …
```

## Findings

The 20 results are presented as cards, after two tables that summarize cards 6 and 19. Each card gives the plain claim; the kind and tier; the Lean statement, quoted verbatim with its `file:line` range; the hypothesis ledger, with the tightness status of each hypothesis, the counterexample theorem and the class of the witness; the depth; a non-vacuity witness, or the reason none is needed; positive controls for the counterexample cards; prior art; the design question it informs; and the basis of each claim. The non-claims of each card are under **Boundaries → Non-claims**.

### The transfer matrix

Rows: claim classes. Columns: map kind × direction. ✓ cells name the theorem that proves the cell (all fully proved; non-vacuous by `licensed_cells_nonvacuous`); ✗ cells name the countermodel that refutes the cell (helper refutation lemmas in `ToyTransfer/Matrix.lean` derive the cell from the countermodel). The agreement of `licensedB` with this table is `licensedB_iff`, proved arm by arm in `cell_status`. Transfer is for formulas with parameters; for the six rows other than `qf` the table is also exact for sentences (`licensedB_iff_preservesSent_of_ne_qf`).

| class | hom fwd | hom bwd | strong fwd | strong bwd | emb fwd | emb bwd | surj fwd | surj bwd |
|---|---|---|---|---|---|---|---|---|
| `qf` | ✗ `notP0_not_preserved_by_surjHom` | ✗ `P0_not_reflected_by_surjHom` | ✗ `neq_not_preserved_by_strongHom` | ✗ `eq_not_reflected_by_strongHom` | ✓ `preserves_qf_emb` | ✓ `preserves_qf_emb` | ✗ `notP0_not_preserved_by_surjHom` | ✗ `P0_not_reflected_by_surjHom` |
| `univ` | ✗ `allP_not_preserved_to_extension` | ✗ `allAllEq_not_reflected_by_strongHom` | ✗ `allP_not_preserved_to_extension` | ✗ `allAllEq_not_reflected_by_strongHom` | ✗ `allP_not_preserved_to_extension` | ✓ `preserves_univ_emb_bwd` | ✗ `allRImpEq_not_preserved_by_surjHom` | ✗ `allP_not_reflected_by_surjHom` |
| `exist` | ✗ `exNotP_not_preserved_by_hom` | ✗ `exP_not_preserved_to_substructure` | ✗ `exExNeq_not_preserved_by_strongHom` | ✗ `exP_not_preserved_to_substructure` | ✓ `preserves_exist_emb_fwd` | ✗ `exP_not_preserved_to_substructure` | ✗ `exNotP_not_preserved_by_hom` | ✗ `exP_not_reflected_by_surjHom` |
| `ae` | ✗ `allP_not_preserved_to_extension` | ✗ `allExR_not_preserved_to_substructure` | ✗ `allP_not_preserved_to_extension` | ✗ `allExR_not_preserved_to_substructure` | ✗ `allP_not_preserved_to_extension` | ✗ `allExR_not_preserved_to_substructure` | ✗ `allRImpEq_not_preserved_by_surjHom` | ✗ `allP_not_reflected_by_surjHom` |
| `ea` | ✗ `allP_not_preserved_to_extension` | ✗ `exP_not_preserved_to_substructure` | ✗ `allP_not_preserved_to_extension` | ✗ `exP_not_preserved_to_substructure` | ✗ `allP_not_preserved_to_extension` | ✗ `exP_not_preserved_to_substructure` | ✗ `allRImpEq_not_preserved_by_surjHom` | ✗ `exP_not_reflected_by_surjHom` |
| `pos` | ✗ `allP_not_preserved_to_extension` | ✗ `exP_not_preserved_to_substructure` | ✗ `allP_not_preserved_to_extension` | ✗ `exP_not_preserved_to_substructure` | ✗ `allP_not_preserved_to_extension` | ✗ `exP_not_preserved_to_substructure` | ✓ `preserves_pos_surj_fwd` | ✗ `exP_not_reflected_by_surjHom` |
| `posExist` | ✓ `preserves_posExist_fwd` | ✗ `exP_not_preserved_to_substructure` | ✓ `preserves_posExist_fwd` | ✗ `exP_not_preserved_to_substructure` | ✓ `preserves_posExist_fwd` | ✗ `exP_not_preserved_to_substructure` | ✓ `preserves_posExist_fwd` | ✗ `exP_not_reflected_by_surjHom` |

A ✗ countermodel stated for a smaller map kind also refutes the larger kinds containing it (every embedding is a strong homomorphism, and every strong or surjective homomorphism is a homomorphism: `IsEmbedding.toStrongHom`, `IsStrongHom.toHom`, `IsSurjHom.toHom`).

Licensed classes per column: hom fwd, strong fwd: positive existential; emb fwd: quantifier-free, existential, positive existential; emb bwd: quantifier-free, universal; surj fwd: positive, positive existential; hom bwd, strong bwd, surj bwd: none.

### Both outcomes in every unlicensed cell

For each unlicensed cell, the witness lemma used in `bothOutcomesNonIso_of_unlicensed` (two maps of the cell's kind, neither an isomorphism, with opposite outcomes at the same known fact; in a backward cell each map comes with a source environment that it sends to the known target environment, and the two maps may be the same map, as in `both_eq`).

| class | hom fwd | hom bwd | strong fwd | strong bwd | emb fwd | emb bwd | surj fwd | surj bwd |
|---|---|---|---|---|---|---|---|---|
| `qf` | `both_notP0` | `both_P0` | `both_neq` | `both_eq` | licensed | licensed | `both_notP0` | `both_P0` |
| `univ` | `both_allP` | `both_atMostOneNotP` | `both_allP` | `both_atMostOneNotP` | `both_allP` | licensed | `both_allRImpEq` | `both_allP_surj` |
| `exist` | `both_exNotP` | `both_exP_sub` | `both_exExNeq` | `both_exP_sub` | licensed | `both_exP_sub` | `both_exNotP` | `both_exP_surj` |
| `ae` | `both_allP` | `both_allExR` | `both_allP` | `both_allExR` | `both_allP` | `both_allExR` | `both_allRImpEq` | `both_allP_surj` |
| `ea` | `both_allP` | `both_exP_sub` | `both_allP` | `both_exP_sub` | `both_allP` | `both_exP_sub` | `both_allRImpEq` | `both_exP_surj` |
| `pos` | `both_allP` | `both_exP_sub` | `both_allP` | `both_exP_sub` | `both_allP` | `both_exP_sub` | licensed | `both_exP_surj` |
| `posExist` | licensed | `both_exP_sub` | licensed | `both_exP_sub` | licensed | `both_exP_sub` | licensed | `both_exP_surj` |

### 1. `univ-preserved-to-substructure-along-embedding`

**Plain claim.** For structures A, B and a map h : A → B that is injective and preserves and reflects R and P (an embedding: A is isomorphic via h to the induced substructure of B on the image of h), every universal formula φ (a possibly empty ∀-prefix over a quantifier-free matrix; negation and equality allowed) that holds in B under the environment h ∘ e holds in A under e.

**Kind / tier.** theorem / T0. The easy direction of the Łoś–Tarski preservation theorem (Hodges 1993, Corollary 2.4.2(a)), restated for formulas with parameters in this signature; a mechanized version for arbitrary first-order languages exists in Mathlib (`IsUniversal.realize_embedding`).

**Lean statement.**

```lean
-- ToyTransfer/Preservation.lean:53-57
theorem univ_preserved_to_substructure_of_embedding (h : A.carrier → B.carrier)
    (hinj : Function.Injective h) (hpR : PreservesR h) (hpP : PreservesP h)
    (hrR : ReflectsR h) (hrP : ReflectsP h)
    {n : Nat} {φ : Fml n} (hφ : IsUniv φ) (e : Fin n → A.carrier) :
    Sat B φ (h ∘ e) → Sat A φ e := …
```

**Hypotheses.**

| hypothesis | purpose | tightness | counterexample | witness class |
|---|---|---|---|---|
| `hφ : IsUniv φ` | restricts to the class that transfers from a structure to its induced substructures | tight | `exP_not_preserved_to_substructure` | ∃x, P x; an embedding of a one-element into a two-element structure |
| `hinj : Function.Injective h` | used for equality atoms | tight | `allAllEq_not_reflected_by_strongHom` | ∀x ∀y, x = y; a non-injective strong homomorphism from a two-element onto a one-element structure |
| `hpR : PreservesR h` | used for negated R-atoms in the matrix | tight | `allNotRxx_reflection_fails_without_presR` | ∀x, ¬ R x x; a bijection between one-element structures satisfying the other four laws |
| `hpP : PreservesP h` | used for negated P-atoms in the matrix | tight | `allNotP_reflection_fails_without_presP` | ∀x, ¬ P x; a bijection between one-element structures satisfying the other four laws |
| `hrR : ReflectsR h` | used for positive R-atoms | tight | `allRxx_reflection_fails_without_reflR` | ∀x, R x x; a bijection between one-element structures satisfying the other four laws |
| `hrP : ReflectsP h` | used for positive P-atoms | tight | `allP_not_reflected_by_surjHom` | ∀x, P x; a bijective homomorphism between one-element structures that reflects R but not P |

**Depth.** shallow.

**Non-vacuity.** `inclCyc` embeds the one-element structure `S1N` into the 2-cycle `S2Cyc`; the universal sentence ∀x, ¬ R x x holds in `S2Cyc`. (`univ_preserved_to_substructure_nonvacuous`)

**Prior art.**

- J. Łoś, 'On the extending of models (I)', Fundamenta Mathematicae 42(1) (1955) 38–54 (bibliographic data verified at https://eudml.org/doc/213372; the paper itself was not opened). Cited, with Tarski 1954, for the Łoś–Tarski preservation theorem, whose statement was verified as Rossman 2008, Theorem 1.1 and footnote 1.
- A. Tarski, 'Contributions to the theory of models. I' and 'II', Indagationes Mathematicae (Proceedings) 57 (1954) 572–581 and 582–588, DOIs 10.1016/S1385-7258(54)50074-0 and 10.1016/S1385-7258(54)50075-2 (bibliographic data verified via Crossref; the papers were not opened).
- B. Rossman, 'Homomorphism preservation theorems', J. ACM 55(3), Article 15, 15:1–15:53 (2008), DOI 10.1145/1379759.1379763 (author PDF checked): Theorem 1.1 (Łoś–Tarski: preservation under embeddings iff equivalent to an existential formula; footnote 1: an embedding is an isomorphism onto an induced substructure, and the dual form is preservation under induced substructures iff universal), Theorem 1.2 (Lyndon's positivity theorem: surjective homomorphisms, positive formulas), Theorem 1.3 (homomorphism preservation theorem: homomorphisms, existential-positive formulas), Theorems 1.4 and 1.5 (Łoś–Tarski and Lyndon fail over finite structures; p. 3 attributes 1.4 to Tait 1959 and Gurevich–Shelah via Gurevich 1984, and 1.5 to Ajtai–Gurevich 1987 and Stolboushkin 1995), Theorem 1.7 (finite homomorphism preservation for sentences), Lemma 2.3 (the easy direction), §2.1.1 (structures have non-empty universes; substructure versus induced substructure), Remark 2.1 (formulas are not required to be prenex).
- W. Hodges, Model Theory, Cambridge University Press 1993 (Encyclopedia of Mathematics and its Applications 42), DOI 10.1017/CBO9780511551574 (bibliographic data verified via Crossref), checked in the publisher's reading sample: §1.2 (an embedding is an injective homomorphism with ā ∈ R^A ⇔ fā ∈ R^B), §2.4 'Maps and the formulas they preserve' (∀1 and ∃1 formulas, not required to be prenex), Theorem 2.4.1 (∃1 formulas are preserved by embeddings), Corollary 2.4.2(a) (∀1 formulas are preserved in substructures), Theorem 2.4.3 ((a) positive existential formulas are preserved by homomorphisms; (b) positive formulas by surjective homomorphisms).
- C. C. Chang and H. J. Keisler, Model Theory, 3rd ed., North-Holland 1990 (Studies in Logic 73), DOI 10.1016/S0049-237X(08)X7004-1 (Crossref record of the 1990 Elsevier volume with ISBN 978-0-444-88054-3, whose chapter records include the preface to the third edition; the record itself lists no authors). The publisher's table of contents lists §3.2 'Applications of elementary chains' and §5.2 'Preservation theorems'; which theorem appears under which number was not verified at the source.
- W. W. Tait, 'A counterexample to a conjecture of Scott and Suppes', J. Symbolic Logic 24(1) (1959) 15–16, DOI 10.2307/2964569 (verified: a sentence preserved under subsystems of finite systems that is not equivalent over finite systems to a universal sentence).
- Y. Gurevich, 'Toward logic tailored for computational complexity', Computation and Proof Theory, Lecture Notes in Mathematics, Springer 1984, 175–216, DOI 10.1007/BFb0099486 (bibliographic data verified via Crossref, except the series volume number; cited as reported by Rossman 2008, p. 3, for the rediscovery of the finite failure of Łoś–Tarski).
- Mathlib (Lean 4), file Mathlib/ModelTheory/Complexity.lean at commit 3eae40f5eb25c5934211edf662d3b24c5afbe47a of leanprover-community/mathlib4 (checked): prenex `IsUniversal` and `IsExistential` (lines 330, 342) and `IsQF.realize_embedding`, `IsUniversal.realize_embedding`, `IsExistential.realize_embedding` (lines 374, 387, 398), `Theory.IsUniversal.models_of_embedding` (line 418), for arbitrary first-order languages. The ModelTheory directory at that commit has no positive or positive existential classes and no preservation results for homomorphisms beyond atomic formulas.

**Design question.** A result proved about a model is routinely read as evidence about the system it models. Which claim shapes transfer, along which proved relation between model and system, in which direction, and for which truth value? Here: when the model is isomorphic to an induced substructure of the system, universal claims true in the system hold in the model; equivalently, a universal counterexample found in the model refutes the system's universal claim (`univ_counterexample_transfers_along_model_embedding`).

Basis: execution (Lean kernel check) for every statement quoted in this card, each a theorem checked by the Lean kernel with the axioms recorded under **Evidence**.

Basis: derived (modeling bridge) for the reading of this card in terms of real models and systems. Reading the two structures as a model and a system is an interpretation, not part of the theorem. The theorem applies to a real model–system pair once both are represented as `Str` values (one binary relation, one unary predicate, equality), the stated map laws are proved for a map between the two representations, and the claim is written as a formula of the stated class; this package carries out none of these steps for any real pair.

**Non-claims.** See **Boundaries → Non-claims → 1.** Read them together with the plain claim.

### 2. `exist-preserved-to-extension-along-embedding`

**Plain claim.** For structures A, B and a map h : A → B that is injective and preserves and reflects R and P (an embedding, so B is an extension of A), every existential formula φ (a possibly empty ∃-prefix over a quantifier-free matrix; negation and equality allowed) that holds in A under e holds in B under h ∘ e.

**Kind / tier.** theorem / T0. The easy direction of the existential form of the Łoś–Tarski theorem (Hodges 1993, Theorem 2.4.1), restated for formulas with parameters; mechanized in Mathlib (`IsExistential.realize_embedding`).

**Lean statement.**

```lean
-- ToyTransfer/Preservation.lean:70-74
theorem exist_preserved_to_extension_of_embedding (h : A.carrier → B.carrier)
    (hinj : Function.Injective h) (hpR : PreservesR h) (hpP : PreservesP h)
    (hrR : ReflectsR h) (hrP : ReflectsP h)
    {n : Nat} {φ : Fml n} (hφ : IsExist φ) (e : Fin n → A.carrier) :
    Sat A φ e → Sat B φ (h ∘ e) := …
```

**Hypotheses.**

| hypothesis | purpose | tightness | counterexample | witness class |
|---|---|---|---|---|
| `hφ : IsExist φ` | restricts to the class that transfers to extensions | tight | `allP_not_preserved_to_extension` | ∀x, P x; an embedding of a one-element into a two-element structure |
| `hinj : Function.Injective h` | used for negated equality atoms | tight | `exExNeq_not_preserved_by_strongHom` | ∃x ∃y, ¬ x = y; a non-injective strong homomorphism from a two-element onto a one-element structure |
| `hpR : PreservesR h` | used for positive R-atoms | tight | `exRxx_transfer_fails_without_presR` | ∃x, R x x; a bijection between one-element structures satisfying the other four laws |
| `hpP : PreservesP h` | used for positive P-atoms | tight | `exP_transfer_fails_without_presP` | ∃x, P x; a bijection between one-element structures satisfying the other four laws |
| `hrR : ReflectsR h` | used for negated R-atoms | tight | `exNotRxx_transfer_fails_without_reflR` | ∃x, ¬ R x x; a bijection between one-element structures satisfying the other four laws |
| `hrP : ReflectsP h` | used for negated P-atoms | tight | `exNotP_not_preserved_by_hom` | ∃x, ¬ P x; a bijective homomorphism between one-element structures that reflects R but not P |

**Depth.** shallow.

**Non-vacuity.** `inclPN` embeds `S1P` into `S2PN`; ∃x, P x holds in `S1P`. (`exist_preserved_to_extension_nonvacuous`)

**Prior art.**

- J. Łoś, 'On the extending of models (I)', Fundamenta Mathematicae 42(1) (1955) 38–54 (bibliographic data verified at https://eudml.org/doc/213372; the paper itself was not opened). Cited, with Tarski 1954, for the Łoś–Tarski preservation theorem, whose statement was verified as Rossman 2008, Theorem 1.1 and footnote 1.
- A. Tarski, 'Contributions to the theory of models. I' and 'II', Indagationes Mathematicae (Proceedings) 57 (1954) 572–581 and 582–588, DOIs 10.1016/S1385-7258(54)50074-0 and 10.1016/S1385-7258(54)50075-2 (bibliographic data verified via Crossref; the papers were not opened).
- B. Rossman, 'Homomorphism preservation theorems', J. ACM 55(3), Article 15, 15:1–15:53 (2008), DOI 10.1145/1379759.1379763 (author PDF checked): Theorem 1.1 (Łoś–Tarski: preservation under embeddings iff equivalent to an existential formula; footnote 1: an embedding is an isomorphism onto an induced substructure, and the dual form is preservation under induced substructures iff universal), Theorem 1.2 (Lyndon's positivity theorem: surjective homomorphisms, positive formulas), Theorem 1.3 (homomorphism preservation theorem: homomorphisms, existential-positive formulas), Theorems 1.4 and 1.5 (Łoś–Tarski and Lyndon fail over finite structures; p. 3 attributes 1.4 to Tait 1959 and Gurevich–Shelah via Gurevich 1984, and 1.5 to Ajtai–Gurevich 1987 and Stolboushkin 1995), Theorem 1.7 (finite homomorphism preservation for sentences), Lemma 2.3 (the easy direction), §2.1.1 (structures have non-empty universes; substructure versus induced substructure), Remark 2.1 (formulas are not required to be prenex).
- W. Hodges, Model Theory, Cambridge University Press 1993 (Encyclopedia of Mathematics and its Applications 42), DOI 10.1017/CBO9780511551574 (bibliographic data verified via Crossref), checked in the publisher's reading sample: §1.2 (an embedding is an injective homomorphism with ā ∈ R^A ⇔ fā ∈ R^B), §2.4 'Maps and the formulas they preserve' (∀1 and ∃1 formulas, not required to be prenex), Theorem 2.4.1 (∃1 formulas are preserved by embeddings), Corollary 2.4.2(a) (∀1 formulas are preserved in substructures), Theorem 2.4.3 ((a) positive existential formulas are preserved by homomorphisms; (b) positive formulas by surjective homomorphisms).
- W. W. Tait, 'A counterexample to a conjecture of Scott and Suppes', J. Symbolic Logic 24(1) (1959) 15–16, DOI 10.2307/2964569 (verified: a sentence preserved under subsystems of finite systems that is not equivalent over finite systems to a universal sentence).
- Y. Gurevich, 'Toward logic tailored for computational complexity', Computation and Proof Theory, Lecture Notes in Mathematics, Springer 1984, 175–216, DOI 10.1007/BFb0099486 (bibliographic data verified via Crossref, except the series volume number; cited as reported by Rossman 2008, p. 3, for the rediscovery of the finite failure of Łoś–Tarski).
- Mathlib (Lean 4), file Mathlib/ModelTheory/Complexity.lean at commit 3eae40f5eb25c5934211edf662d3b24c5afbe47a of leanprover-community/mathlib4 (checked): prenex `IsUniversal` and `IsExistential` (lines 330, 342) and `IsQF.realize_embedding`, `IsUniversal.realize_embedding`, `IsExistential.realize_embedding` (lines 374, 387, 398), `Theory.IsUniversal.models_of_embedding` (line 418), for arbitrary first-order languages. The ModelTheory directory at that commit has no positive or positive existential classes and no preservation results for homomorphisms beyond atomic formulas.

**Design question.** Which claims about a model hold in a system that extends it? Existential claims (witnesses described by an ∃-prefix over a quantifier-free condition, for example a bounded-length configuration exhibited in the model) found in the model hold in every extension: model witnesses are system witnesses when the model is isomorphic to an induced substructure of the system. Reachability of unbounded length is not expressed by any formula of this syntax (a standard fact, not proved here) and is not covered.

Basis: execution (Lean kernel check) for every statement quoted in this card, each a theorem checked by the Lean kernel with the axioms recorded under **Evidence**.

Basis: derived (modeling bridge) for the reading of this card in terms of real models and systems. Reading the two structures as a model and a system is an interpretation, not part of the theorem. The theorem applies to a real model–system pair once both are represented as `Str` values (one binary relation, one unary predicate, equality), the stated map laws are proved for a map between the two representations, and the claim is written as a formula of the stated class; this package carries out none of these steps for any real pair.

**Non-claims.** See **Boundaries → Non-claims → 2.** Read them together with the plain claim.

### 3. `positive-existential-preserved-forward-along-homomorphism`

**Plain claim.** For structures A, B and a map h : A → B that preserves R and P (a homomorphism; not necessarily injective, surjective or reflecting), every positive existential formula φ (no negation and no ∀; ∃ may occur under ∧ and ∨) that holds in A under e holds in B under h ∘ e.

**Kind / tier.** theorem / T0. The easy direction of the homomorphism preservation theorem (Hodges 1993, Theorem 2.4.3(a); Rossman 2008, Lemma 2.3), restated for formulas with parameters.

**Lean statement.**

```lean
-- ToyTransfer/Preservation.lean:86-89
theorem posExist_preserved_forward_of_hom (h : A.carrier → B.carrier)
    (hpR : PreservesR h) (hpP : PreservesP h)
    {n : Nat} {φ : Fml n} (hφ : IsPosExist φ) (e : Fin n → A.carrier) :
    Sat A φ e → Sat B φ (h ∘ e) := …
```

**Hypotheses.**

| hypothesis | purpose | tightness | counterexample | witness class |
|---|---|---|---|---|
| `hφ : IsPosExist φ` | excludes negation and ∀ | tight | `exNotP_not_preserved_by_hom`, `allP_not_preserved_to_extension` | ∃x, ¬ P x along a bijective homomorphism of one-element structures (negation); ∀x, P x along an embedding (universal quantifier) |
| `hpR : PreservesR h` | used for R-atoms | tight | `exRxx_transfer_fails_without_presR` | ∃x, R x x; a bijection between one-element structures preserving P |
| `hpP : PreservesP h` | used for P-atoms | tight | `exP_transfer_fails_without_presP` | ∃x, P x; a bijection between one-element structures preserving R |

**Depth.** shallow.

**Non-vacuity.** `squashP` maps `S2NP` onto `S1P`; it is a homomorphism that is neither injective nor reflects P; ∃x, P x holds in `S2NP`. (`posExist_preserved_forward_nonvacuous`)

**Prior art.**

- B. Rossman, 'Homomorphism preservation theorems', J. ACM 55(3), Article 15, 15:1–15:53 (2008), DOI 10.1145/1379759.1379763 (author PDF checked): Theorem 1.1 (Łoś–Tarski: preservation under embeddings iff equivalent to an existential formula; footnote 1: an embedding is an isomorphism onto an induced substructure, and the dual form is preservation under induced substructures iff universal), Theorem 1.2 (Lyndon's positivity theorem: surjective homomorphisms, positive formulas), Theorem 1.3 (homomorphism preservation theorem: homomorphisms, existential-positive formulas), Theorems 1.4 and 1.5 (Łoś–Tarski and Lyndon fail over finite structures; p. 3 attributes 1.4 to Tait 1959 and Gurevich–Shelah via Gurevich 1984, and 1.5 to Ajtai–Gurevich 1987 and Stolboushkin 1995), Theorem 1.7 (finite homomorphism preservation for sentences), Lemma 2.3 (the easy direction), §2.1.1 (structures have non-empty universes; substructure versus induced substructure), Remark 2.1 (formulas are not required to be prenex).
- W. Hodges, Model Theory, Cambridge University Press 1993 (Encyclopedia of Mathematics and its Applications 42), DOI 10.1017/CBO9780511551574 (bibliographic data verified via Crossref), checked in the publisher's reading sample: §1.2 (an embedding is an injective homomorphism with ā ∈ R^A ⇔ fā ∈ R^B), §2.4 'Maps and the formulas they preserve' (∀1 and ∃1 formulas, not required to be prenex), Theorem 2.4.1 (∃1 formulas are preserved by embeddings), Corollary 2.4.2(a) (∀1 formulas are preserved in substructures), Theorem 2.4.3 ((a) positive existential formulas are preserved by homomorphisms; (b) positive formulas by surjective homomorphisms).
- R. C. Lyndon, 'Properties preserved under homomorphism', Pacific J. Math. 9(1) (1959) 143–154, DOI 10.2140/pjm.1959.9.143 (bibliographic data verified; the paper was not opened; its theorem, as stated in Rossman 2008, Theorem 1.2, is the converse for surjective homomorphisms: a formula preserved under surjective homomorphisms is equivalent to a positive one).

**Design question.** Which claims survive any structure-preserving abstraction that may merge elements and add facts? Positive existential claims of the source hold in the target of every homomorphism.

Basis: execution (Lean kernel check) for every statement quoted in this card, each a theorem checked by the Lean kernel with the axioms recorded under **Evidence**.

Basis: derived (modeling bridge) for the reading of this card in terms of real models and systems. Reading the two structures as a model and a system is an interpretation, not part of the theorem. The theorem applies to a real model–system pair once both are represented as `Str` values (one binary relation, one unary predicate, equality), the stated map laws are proved for a map between the two representations, and the claim is written as a formula of the stated class; this package carries out none of these steps for any real pair.

**Non-claims.** See **Boundaries → Non-claims → 3.** Read them together with the plain claim.

### 4. `positive-preserved-forward-along-surjective-homomorphism`

**Plain claim.** For structures A, B and a map h : A → B that is surjective and preserves R and P (a surjective homomorphism; reflection not required), every positive formula φ (no negation; both quantifiers and equality allowed, quantifiers may occur under ∧ and ∨) that holds in A under e holds in B under h ∘ e.

**Kind / tier.** theorem / T0. The easy direction of Lyndon's positivity theorem (Hodges 1993, Theorem 2.4.3(b)), restated for formulas with parameters.

**Lean statement.**

```lean
-- ToyTransfer/Preservation.lean:106-109
theorem pos_preserved_forward_of_surjHom (h : A.carrier → B.carrier)
    (hsurj : Function.Surjective h) (hpR : PreservesR h) (hpP : PreservesP h)
    {n : Nat} {φ : Fml n} (hφ : IsPos φ) (e : Fin n → A.carrier) :
    Sat A φ e → Sat B φ (h ∘ e) := …
```

**Hypotheses.**

| hypothesis | purpose | tightness | counterexample | witness class |
|---|---|---|---|---|
| `hφ : IsPos φ` | excludes negation | tight | `exNotP_not_preserved_by_hom` | ∃x, ¬ P x; a bijective homomorphism between one-element structures |
| `hsurj : Function.Surjective h` | used for ∀ | tight | `allP_not_preserved_to_extension` | ∀x, P x; a non-surjective embedding of a one-element into a two-element structure |
| `hpR : PreservesR h` | used for R-atoms | tight | `exRxx_transfer_fails_without_presR` | ∃x, R x x; a bijection between one-element structures preserving P |
| `hpP : PreservesP h` | used for P-atoms | tight | `exP_transfer_fails_without_presP` | ∃x, P x; a bijection between one-element structures preserving R |

**Depth.** shallow.

**Non-vacuity.** `squashP` maps `S2NP` onto `S1P`; the positive sentence ∀x ∃y, P y (not positive existential) holds in `S2NP`. (`pos_preserved_forward_nonvacuous`)

**Prior art.**

- R. C. Lyndon, 'Properties preserved under homomorphism', Pacific J. Math. 9(1) (1959) 143–154, DOI 10.2140/pjm.1959.9.143 (bibliographic data verified; the paper was not opened; its theorem, as stated in Rossman 2008, Theorem 1.2, is the converse for surjective homomorphisms: a formula preserved under surjective homomorphisms is equivalent to a positive one).
- B. Rossman, 'Homomorphism preservation theorems', J. ACM 55(3), Article 15, 15:1–15:53 (2008), DOI 10.1145/1379759.1379763 (author PDF checked): Theorem 1.1 (Łoś–Tarski: preservation under embeddings iff equivalent to an existential formula; footnote 1: an embedding is an isomorphism onto an induced substructure, and the dual form is preservation under induced substructures iff universal), Theorem 1.2 (Lyndon's positivity theorem: surjective homomorphisms, positive formulas), Theorem 1.3 (homomorphism preservation theorem: homomorphisms, existential-positive formulas), Theorems 1.4 and 1.5 (Łoś–Tarski and Lyndon fail over finite structures; p. 3 attributes 1.4 to Tait 1959 and Gurevich–Shelah via Gurevich 1984, and 1.5 to Ajtai–Gurevich 1987 and Stolboushkin 1995), Theorem 1.7 (finite homomorphism preservation for sentences), Lemma 2.3 (the easy direction), §2.1.1 (structures have non-empty universes; substructure versus induced substructure), Remark 2.1 (formulas are not required to be prenex).
- W. Hodges, Model Theory, Cambridge University Press 1993 (Encyclopedia of Mathematics and its Applications 42), DOI 10.1017/CBO9780511551574 (bibliographic data verified via Crossref), checked in the publisher's reading sample: §1.2 (an embedding is an injective homomorphism with ā ∈ R^A ⇔ fā ∈ R^B), §2.4 'Maps and the formulas they preserve' (∀1 and ∃1 formulas, not required to be prenex), Theorem 2.4.1 (∃1 formulas are preserved by embeddings), Corollary 2.4.2(a) (∀1 formulas are preserved in substructures), Theorem 2.4.3 ((a) positive existential formulas are preserved by homomorphisms; (b) positive formulas by surjective homomorphisms).
- M. Ajtai and Y. Gurevich, 'Monotone versus positive', J. ACM 34(4) (1987) 1004–1015, DOI 10.1145/31846.31852 (bibliographic data and abstract verified via Crossref): the abstract answers negatively whether a first-order formula that is semantically monotone in a predicate symbol P on finite structures is necessarily equivalent on finite structures to a first-order formula with only positive occurrences of P; it does not mention Lyndon's theorem. Cited for the failure of Lyndon's theorem over finite structures as reported by Rossman 2008, Theorem 1.5 and p. 3.
- A. P. Stolboushkin, 'Finitely monotone properties', Proc. 10th IEEE Symposium on Logic in Computer Science (LICS 1995), 324–330, DOI 10.1109/LICS.1995.523267 (bibliographic data verified via Crossref): a simpler counterexample, per Rossman 2008, p. 3.

**Design question.** Orientation matters. If h : model → system is a surjective homomorphism (the system is a homomorphic image of a finer model: elements may be merged and facts added), positive truths of the model hold in the system. If instead the model is a quotient-like abstraction of the system (h : system → model surjective), it is positive falsities of the model that transfer to the system (`licences_exact`, falsity list for surjective homomorphisms, system-to-model).

Basis: execution (Lean kernel check) for every statement quoted in this card, each a theorem checked by the Lean kernel with the axioms recorded under **Evidence**.

Basis: derived (modeling bridge) for the reading of this card in terms of real models and systems. Reading the two structures as a model and a system is an interpretation, not part of the theorem. The theorem applies to a real model–system pair once both are represented as `Str` values (one binary relation, one unary predicate, equality), the stated map laws are proved for a map between the two representations, and the claim is written as a formula of the stated class; this package carries out none of these steps for any real pair.

**Non-claims.** See **Boundaries → Non-claims → 4.** Read them together with the plain claim.

### 5. `five-unlicensed-transfers-countermodels`

**Plain claim.** Five transfers fail, each on structures with at most two elements, checked by evaluation: (1) ∀x ∃y, R x y holds in the 2-cycle `S2Cyc` and fails in its one-element induced substructure `S1N`; (2) ∃x, P x holds in `S2NP` and fails in its one-element induced substructure `S1N`; (3) ∀x, P x holds in `S1P` and fails in its two-element extension `S2PN`; (4) ∃x, ¬ P x holds in `S1N` and fails in `S1P` after the bijective homomorphism `raiseP`; (5) ∀x ∀y, R x y → x = y holds in `S2E` and fails in `S2R01` after the bijective homomorphism `addEdge`. Each theorem also states the class memberships and map laws that hold in its instance.

**Kind / tier.** counterexample / T0. Standard textbook countermodels, each on structures with at most two elements; a highlighted subset of the thirteen countermodels of the transfer matrix (`transfer-matrix-boolean-table-agrees-with-preservation`).

**Lean statement.**

```lean
-- ToyTransfer/Countermodels.lean:37-40
theorem allExR_not_preserved_to_substructure :
    IsAE allExR ∧ IsPos allExR ∧ ¬ IsUniv allExR ∧ ¬ IsExist allExR ∧
    IsEmbedding inclCyc ∧
    Sat S2Cyc.toStr allExR (inclCyc ∘ Fin.elim0) ∧ ¬ Sat S1N.toStr allExR Fin.elim0 := …

-- ToyTransfer/Countermodels.lean:29-32
theorem exP_not_preserved_to_substructure :
    IsExist exP ∧ IsAE exP ∧ IsEA exP ∧ IsPos exP ∧ IsPosExist exP ∧ ¬ IsUniv exP ∧
    IsEmbedding inclNP ∧
    Sat S2NP.toStr exP (inclNP ∘ Fin.elim0) ∧ ¬ Sat S1N.toStr exP Fin.elim0 := …

-- ToyTransfer/Countermodels.lean:21-24
theorem allP_not_preserved_to_extension :
    IsUniv allP ∧ IsAE allP ∧ IsEA allP ∧ IsPos allP ∧ ¬ IsExist allP ∧ ¬ IsPosExist allP ∧
    IsEmbedding inclPN ∧ ¬ Function.Surjective inclPN ∧
    Sat S1P.toStr allP Fin.elim0 ∧ ¬ Sat S2PN.toStr allP (inclPN ∘ Fin.elim0) := …

-- ToyTransfer/Countermodels.lean:45-48
theorem exNotP_not_preserved_by_hom :
    IsExist exNotP ∧ IsAE exNotP ∧ IsEA exNotP ∧ ¬ IsPos exNotP ∧ ¬ IsPosExist exNotP ∧
    IsSurjHom raiseP ∧ Function.Injective raiseP ∧ ReflectsR raiseP ∧ ¬ ReflectsP raiseP ∧
    Sat S1N.toStr exNotP Fin.elim0 ∧ ¬ Sat S1P.toStr exNotP (raiseP ∘ Fin.elim0) := …

-- ToyTransfer/Countermodels.lean:54-57
theorem allRImpEq_not_preserved_by_surjHom :
    IsUniv allRImpEq ∧ IsAE allRImpEq ∧ IsEA allRImpEq ∧ ¬ IsPos allRImpEq ∧
    IsSurjHom addEdge ∧ Function.Injective addEdge ∧ ReflectsP addEdge ∧ ¬ ReflectsR addEdge ∧
    Sat S2E.toStr allRImpEq Fin.elim0 ∧ ¬ Sat S2R01.toStr allRImpEq (addEdge ∘ Fin.elim0) := …
```

**Hypotheses.**

None: the statement is a concrete instance.

**Depth.** definitional.

**Non-vacuity.** Not applicable: each theorem is a concrete instance.

**Positive controls** (nearby settings, with stronger hypotheses, where the transfer does hold): `univ_preserved_to_substructure_of_embedding`, `exist_preserved_to_extension_of_embedding`, `posExist_preserved_forward_of_hom`, `pos_preserved_forward_of_surjHom`.

**Prior art.**

- W. Hodges, Model Theory, Cambridge University Press 1993 (Encyclopedia of Mathematics and its Applications 42), DOI 10.1017/CBO9780511551574 (bibliographic data verified via Crossref), checked in the publisher's reading sample: §1.2 (an embedding is an injective homomorphism with ā ∈ R^A ⇔ fā ∈ R^B), §2.4 'Maps and the formulas they preserve' (∀1 and ∃1 formulas, not required to be prenex), Theorem 2.4.1 (∃1 formulas are preserved by embeddings), Corollary 2.4.2(a) (∀1 formulas are preserved in substructures), Theorem 2.4.3 ((a) positive existential formulas are preserved by homomorphisms; (b) positive formulas by surjective homomorphisms).
- B. Rossman, 'Homomorphism preservation theorems', J. ACM 55(3), Article 15, 15:1–15:53 (2008), DOI 10.1145/1379759.1379763 (author PDF checked): Theorem 1.1 (Łoś–Tarski: preservation under embeddings iff equivalent to an existential formula; footnote 1: an embedding is an isomorphism onto an induced substructure, and the dual form is preservation under induced substructures iff universal), Theorem 1.2 (Lyndon's positivity theorem: surjective homomorphisms, positive formulas), Theorem 1.3 (homomorphism preservation theorem: homomorphisms, existential-positive formulas), Theorems 1.4 and 1.5 (Łoś–Tarski and Lyndon fail over finite structures; p. 3 attributes 1.4 to Tait 1959 and Gurevich–Shelah via Gurevich 1984, and 1.5 to Ajtai–Gurevich 1987 and Stolboushkin 1995), Theorem 1.7 (finite homomorphism preservation for sentences), Lemma 2.3 (the easy direction), §2.1.1 (structures have non-empty universes; substructure versus induced substructure), Remark 2.1 (formulas are not required to be prenex).

**Design question.** Each unlicensed transfer that readers commonly assume (universal claims to extensions, existential claims to substructures, negated claims along homomorphisms, universal implications along surjective homomorphisms) has a two-element countermodel.

Basis: execution (Lean kernel check) for every statement quoted in this card, each a theorem checked by the Lean kernel with the axioms recorded under **Evidence**.

Basis: derived (modeling bridge) for the reading of this card in terms of real models and systems. A countermodel shows that the hypotheses it states do not suffice in general: no argument that uses those hypotheses alone can establish the transfer for every formula of the class. It does not show that the transfer fails for a particular real model and system; this package represents no real model or system.

**Non-claims.** See **Boundaries → Non-claims → 5.** Read them together with the plain claim.

### 6. `transfer-matrix-boolean-table-agrees-with-preservation`

**Plain claim.** For each of the seven syntactic classes (quantifier-free, universal, existential, ∀∃, ∃∀, positive, positive existential), each of the four map kinds (homomorphism, strong homomorphism, embedding, surjective homomorphism) and each direction (forward from source to target, backward from target to source), the Boolean table `licensedB` is true exactly when every formula of the class (with parameters) transfers along every map of that kind in that direction (`licensedB_iff`); every one of the 56 cells is decided by a licensing theorem or a named countermodel (`cell_status`). For every class except the quantifier-free one, the same table is exact for sentences (`licensedB_iff_preservesSent_of_ne_qf`, hypothesis c ≠ qf). A formula that belongs to some class licensed for (k, d) transfers along every k-map in direction d (`transfer_of_licensedForB`, hypothesis licensedForB φ k d = true).

**Kind / tier.** characterization / T1. Folklore made precise: which classes each map kind preserves is textbook material for the licensed cells (Hodges 1993, §2.4), and Mathlib mechanizes the embedding cells for prenex classes; a complete 7 × 8 table in which every unlicensed cell has a mechanized countermodel was not found in the sources checked (Mathlib's ModelTheory, Hodges §2.4, Rossman 2008).

**Lean statement.**

```lean
-- ToyTransfer/Matrix.lean:237-238
theorem licensedB_iff (c : Cls) (k : MapKind) (d : Dir) :
    licensedB c k d = true ↔ Preserves c k d := …

-- ToyTransfer/Matrix.lean:167-168
theorem cell_status : ∀ (c : Cls) (k : MapKind) (d : Dir),
    (licensedB c k d = true ∧ Preserves c k d) ∨ (licensedB c k d = false ∧ ¬ Preserves c k d) := …

-- ToyTransfer/Matrix.lean:248-249
theorem licensedB_iff_preservesSent_of_ne_qf (c : Cls) (k : MapKind) (d : Dir) (hc : c ≠ .qf) :
    licensedB c k d = true ↔ PreservesSent c k d := …

-- ToyTransfer/Matrix.lean:288-291
theorem transfer_of_licensedForB {n : Nat} (φ : Fml n) (k : MapKind) (d : Dir)
    (hl : licensedForB φ k d = true) :
    ∀ (A B : Str) (h : A.carrier → B.carrier), k.Holds h →
      ∀ e : Fin n → A.carrier, d.Transfer (Sat A φ e) (Sat B φ (h ∘ e)) := …
```

**Hypotheses.**

| hypothesis | purpose | tightness | counterexample | witness class |
|---|---|---|---|---|
| `hl : licensedForB φ k d = true (transfer_of_licensedForB)` | the table licenses some class containing φ | tight | `transfer_of_licensedForB_needs_licence` | ∀x, P x along an embedding of a one-element into a two-element structure |
| `hc : c ≠ .qf (licensedB_iff_preservesSent_of_ne_qf)` | excludes the quantifier-free row, which has no sentences | tight | `licensedB_iff_preservesSent_needs_ne_qf` | the quantifier-free row for homomorphisms, forward: unlicensed, yet sentence-level transfer holds vacuously |

**Depth.** substantive. Each cell is shallow; the content is the completeness of the table: 9 licensed cells, each proved by an easy preservation theorem, and 47 unlicensed cells, each refuted by one of 13 countermodels, plus the sentence-level version for six rows.

**Non-vacuity.** Every licensed cell has an instance with the premise true (`licensed_cells_nonvacuous`); `preserves_examples` and `preservesSent_examples` exhibit a licensed and an unlicensed cell; `transfer_of_licensedForB_nonvacuous` exhibits ∃x, P x licensed forward along embeddings with its premise true at the source of `inclPN`. (`licensed_cells_nonvacuous`, `preserves_examples`, `preservesSent_examples`, `transfer_of_licensedForB_nonvacuous`)

**Prior art.**

- W. Hodges, Model Theory, Cambridge University Press 1993 (Encyclopedia of Mathematics and its Applications 42), DOI 10.1017/CBO9780511551574 (bibliographic data verified via Crossref), checked in the publisher's reading sample: §1.2 (an embedding is an injective homomorphism with ā ∈ R^A ⇔ fā ∈ R^B), §2.4 'Maps and the formulas they preserve' (∀1 and ∃1 formulas, not required to be prenex), Theorem 2.4.1 (∃1 formulas are preserved by embeddings), Corollary 2.4.2(a) (∀1 formulas are preserved in substructures), Theorem 2.4.3 ((a) positive existential formulas are preserved by homomorphisms; (b) positive formulas by surjective homomorphisms).
- B. Rossman, 'Homomorphism preservation theorems', J. ACM 55(3), Article 15, 15:1–15:53 (2008), DOI 10.1145/1379759.1379763 (author PDF checked): Theorem 1.1 (Łoś–Tarski: preservation under embeddings iff equivalent to an existential formula; footnote 1: an embedding is an isomorphism onto an induced substructure, and the dual form is preservation under induced substructures iff universal), Theorem 1.2 (Lyndon's positivity theorem: surjective homomorphisms, positive formulas), Theorem 1.3 (homomorphism preservation theorem: homomorphisms, existential-positive formulas), Theorems 1.4 and 1.5 (Łoś–Tarski and Lyndon fail over finite structures; p. 3 attributes 1.4 to Tait 1959 and Gurevich–Shelah via Gurevich 1984, and 1.5 to Ajtai–Gurevich 1987 and Stolboushkin 1995), Theorem 1.7 (finite homomorphism preservation for sentences), Lemma 2.3 (the easy direction), §2.1.1 (structures have non-empty universes; substructure versus induced substructure), Remark 2.1 (formulas are not required to be prenex).
- Mathlib (Lean 4), file Mathlib/ModelTheory/Complexity.lean at commit 3eae40f5eb25c5934211edf662d3b24c5afbe47a of leanprover-community/mathlib4 (checked): prenex `IsUniversal` and `IsExistential` (lines 330, 342) and `IsQF.realize_embedding`, `IsUniversal.realize_embedding`, `IsExistential.realize_embedding` (lines 374, 387, 398), `Theory.IsUniversal.models_of_embedding` (line 418), for arbitrary first-order languages. The ModelTheory directory at that commit has no positive or positive existential classes and no preservation results for homomorphisms beyond atomic formulas.
- C. C. Chang and H. J. Keisler, Model Theory, 3rd ed., North-Holland 1990 (Studies in Logic 73), DOI 10.1016/S0049-237X(08)X7004-1 (Crossref record of the 1990 Elsevier volume with ISBN 978-0-444-88054-3, whose chapter records include the preface to the third edition; the record itself lists no authors). The publisher's table of contents lists §3.2 'Applications of elementary chains' and §5.2 'Preservation theorems'; which theorem appears under which number was not verified at the source.

**Design question.** Given a proved relation between model and system (a map of one of the four kinds, in one of the two orientations), which claim shapes established on one side are licensed on the other? The table answers this for syntactic classes, with a refuting countermodel for every unlicensed cell.

Basis: execution (Lean kernel check) for every statement quoted in this card, each a theorem checked by the Lean kernel with the axioms recorded under **Evidence**.

Basis: derived (modeling bridge) for the reading of this card in terms of real models and systems. Reading the two structures as a model and a system is an interpretation, not part of the theorem. The theorem applies to a real model–system pair once both are represented as `Str` values (one binary relation, one unary predicate, equality), the stated map laws are proved for a map between the two representations, and the claim is written as a formula of the stated class; this package carries out none of these steps for any real pair.

**Non-claims.** See **Boundaries → Non-claims → 6.** Read them together with the plain claim.

### 7. `model-embeds-into-system-counterexamples-and-witnesses-transfer`

**Plain claim.** Let h : M → S be an embedding of a model M into a system S (M is isomorphic via h to the induced substructure of S on the image of h). Then a universal formula that fails in M under e fails in S under h ∘ e, and an existential formula that holds in M under e holds in S under h ∘ e. Model truth of a universal formula does not in general determine its truth in S: the model `S1P` satisfies ∀x, P x and has two non-surjective embeddings, into `S2PP`, where the sentence holds, and into `S2PN`, where it fails.

**Kind / tier.** theorem / T0. Contrapositive readings of the two easy Łoś–Tarski directions (Hodges 1993, Theorem 2.4.1 and Corollary 2.4.2) for the model-embeds-into-system orientation, with one concrete countermodel; the two transfer theorems are one-line repackagings of `univ_preserved_to_substructure_of_embedding` and `exist_preserved_to_extension_of_embedding`.

**Lean statement.**

```lean
-- ToyTransfer/Direction.lean:33-36
theorem univ_counterexample_transfers_along_model_embedding {M S : Str}
    (h : M.carrier → S.carrier) (hemb : IsEmbedding h)
    {n : Nat} {φ : Fml n} (hφ : IsUniv φ) (e : Fin n → M.carrier) :
    ¬ Sat M φ e → ¬ Sat S φ (h ∘ e) := …

-- ToyTransfer/Direction.lean:43-46
theorem exist_witness_transfers_along_model_embedding {M S : Str}
    (h : M.carrier → S.carrier) (hemb : IsEmbedding h)
    {n : Nat} {φ : Fml n} (hφ : IsExist φ) (e : Fin n → M.carrier) :
    Sat M φ e → Sat S φ (h ∘ e) := …

-- ToyTransfer/Direction.lean:53-58
theorem allP_truth_in_model_undetermined_in_system_along_embedding :
    IsUniv allP ∧ Sat S1P.toStr allP Fin.elim0 ∧
    IsEmbedding inclPP ∧ ¬ Function.Surjective inclPP ∧
      Sat S2PP.toStr allP (inclPP ∘ Fin.elim0) ∧
    IsEmbedding inclPN ∧ ¬ Function.Surjective inclPN ∧
      ¬ Sat S2PN.toStr allP (inclPN ∘ Fin.elim0) := …
```

**Hypotheses.**

| hypothesis | purpose | tightness | counterexample | witness class |
|---|---|---|---|---|
| `hemb : IsEmbedding h (both transfer theorems)` | induced substructure; reflection of R and P is used | tight | `allRxx_reflection_fails_without_reflR`, `exNotRxx_transfer_fails_without_reflR` | an injective, surjective homomorphism of one-element structures that adds the loop R 0 0 (does not reflect R): ∀x, R x x fails in the model and holds in the system; ∃x, ¬ R x x holds in the model and fails in the system |
| `hφ : IsUniv φ (univ_counterexample_transfers_along_model_embedding)` | restricts to universal formulas | tight | `exP_not_preserved_to_substructure` | ∃x, P x fails in the model `S1N` and holds in the system `S2NP` it embeds into |
| `hφ : IsExist φ (exist_witness_transfers_along_model_embedding)` | restricts to existential formulas | tight | `allP_not_preserved_to_extension` | ∀x, P x holds in the model `S1P` and fails in the system `S2PN` it embeds into |

**Depth.** shallow.

**Non-vacuity.** ∀x, P x fails in the model `S1N`, which embeds into `S2NP`; ∃x, P x holds in the model `S1P`, which embeds into `S2PN`. (`model_embeds_into_system_nonvacuous`)

**Prior art.**

- W. Hodges, Model Theory, Cambridge University Press 1993 (Encyclopedia of Mathematics and its Applications 42), DOI 10.1017/CBO9780511551574 (bibliographic data verified via Crossref), checked in the publisher's reading sample: §1.2 (an embedding is an injective homomorphism with ā ∈ R^A ⇔ fā ∈ R^B), §2.4 'Maps and the formulas they preserve' (∀1 and ∃1 formulas, not required to be prenex), Theorem 2.4.1 (∃1 formulas are preserved by embeddings), Corollary 2.4.2(a) (∀1 formulas are preserved in substructures), Theorem 2.4.3 ((a) positive existential formulas are preserved by homomorphisms; (b) positive formulas by surjective homomorphisms).
- B. Rossman, 'Homomorphism preservation theorems', J. ACM 55(3), Article 15, 15:1–15:53 (2008), DOI 10.1145/1379759.1379763 (author PDF checked): Theorem 1.1 (Łoś–Tarski: preservation under embeddings iff equivalent to an existential formula; footnote 1: an embedding is an isomorphism onto an induced substructure, and the dual form is preservation under induced substructures iff universal), Theorem 1.2 (Lyndon's positivity theorem: surjective homomorphisms, positive formulas), Theorem 1.3 (homomorphism preservation theorem: homomorphisms, existential-positive formulas), Theorems 1.4 and 1.5 (Łoś–Tarski and Lyndon fail over finite structures; p. 3 attributes 1.4 to Tait 1959 and Gurevich–Shelah via Gurevich 1984, and 1.5 to Ajtai–Gurevich 1987 and Stolboushkin 1995), Theorem 1.7 (finite homomorphism preservation for sentences), Lemma 2.3 (the easy direction), §2.1.1 (structures have non-empty universes; substructure versus induced substructure), Remark 2.1 (formulas are not required to be prenex).
- P. W. O'Hearn, 'Incorrectness logic', Proc. ACM Program. Lang. 4(POPL) (2020), DOI 10.1145/3371078 (bibliographic data verified; content not checked). Cited as a program logic for under-approximate reasoning about bugs, a different formalism.

**Design question.** When every model element and every atomic fact about it is present in the system, with no extra facts among model elements (an embedding), which model results carry over? Model counterexamples to universal claims and model witnesses to existential claims are system counterexamples and witnesses; a model proof of a universal claim does not in general establish that claim for the system.

Basis: execution (Lean kernel check) for every statement quoted in this card, each a theorem checked by the Lean kernel with the axioms recorded under **Evidence**.

Basis: derived (modeling bridge) for the reading of this card in terms of real models and systems. This is the first-order analogue of under-approximate bug finding. A model that keeps some of a system's elements together with exactly the system's atomic facts among them is an induced substructure, and `univ_counterexample_transfers_along_model_embedding` and `exist_witness_transfers_along_model_embedding` say that its counterexamples to universal formulas and its witnesses to existential formulas are the system's. The theorems assume models whose atomic facts agree with the system's on the model's elements. A model that also drops atomic facts about retained elements is related to the system by an injective homomorphism that does not reflect R or P, and so is not an embedding (an instance: `injective_hom_not_embedding_example`); neither transfer is claimed for such models, and both fail in general (`allRxx_reflection_fails_without_reflR`, `exNotRxx_transfer_fails_without_reflR`). Reading the two structures as a model and a system is an interpretation, not part of the theorem. The theorem applies to a real model–system pair once both are represented as `Str` values (one binary relation, one unary predicate, equality), the stated map laws are proved for a map between the two representations, and the claim is written as a formula of the stated class; this package carries out none of these steps for any real pair.

**Non-claims.** See **Boundaries → Non-claims → 7.** Read them together with the plain claim.

### 8. `system-embeds-into-model-universal-proofs-transfer-counterexamples-may-be-spurious`

**Plain claim.** Let h : S → M be an embedding of a system S into a model M (M extends S by extra elements and agrees with S on the atomic facts about S's elements). Then a universal formula that holds in M under h ∘ e holds in S under e. Model counterexamples to universal formulas, and model witnesses to existential formulas, may be spurious: ∀x, P x fails in the model `S2PN` and holds in the system `S1P` embedded by `inclPN`; ∃x, P x holds in the model `S2NP` and fails in the system `S1N` embedded by `inclNP`.

**Kind / tier.** theorem / T0. The easy direction of Łoś–Tarski (Hodges 1993, Corollary 2.4.2(a)) read in the system-embeds-into-model orientation; the transfer theorem is a one-line repackaging of `univ_preserved_to_substructure_of_embedding`; the two countermodels are reused from the transfer matrix.

**Lean statement.**

```lean
-- ToyTransfer/Direction.lean:82-85
theorem univ_truth_transfers_down_from_model_extension {S M : Str}
    (h : S.carrier → M.carrier) (hemb : IsEmbedding h)
    {n : Nat} {φ : Fml n} (hφ : IsUniv φ) (e : Fin n → S.carrier) :
    Sat M φ (h ∘ e) → Sat S φ e := …

-- ToyTransfer/Direction.lean:92-94
theorem model_counterexample_may_be_spurious_in_model_extension :
    IsUniv allP ∧ IsEmbedding inclPN ∧
    ¬ Sat S2PN.toStr allP (inclPN ∘ Fin.elim0) ∧ Sat S1P.toStr allP Fin.elim0 := …

-- ToyTransfer/Direction.lean:100-102
theorem model_witness_may_be_spurious_in_model_extension :
    IsExist exP ∧ IsEmbedding inclNP ∧
    Sat S2NP.toStr exP (inclNP ∘ Fin.elim0) ∧ ¬ Sat S1N.toStr exP Fin.elim0 := …
```

**Hypotheses.**

| hypothesis | purpose | tightness | counterexample | witness class |
|---|---|---|---|---|
| `hemb : IsEmbedding h (univ_truth_transfers_down_from_model_extension)` | induced substructure | tight | `allRxx_reflection_fails_without_reflR` | the system `S1N` mapped into the model `S1R` by an injective homomorphism that does not reflect R: ∀x, R x x holds in the model and fails in the system |
| `hφ : IsUniv φ (univ_truth_transfers_down_from_model_extension)` | restricts to universal formulas | tight | `exP_not_preserved_to_substructure` | ∃x, P x holds in the model `S2NP` and fails in the system `S1N` |

**Depth.** shallow.

**Non-vacuity.** `inclCyc` embeds the system `S1N` into the model `S2Cyc`, where ∀x, ¬ R x x holds. (`univ_preserved_to_substructure_nonvacuous`)

**Prior art.**

- W. Hodges, Model Theory, Cambridge University Press 1993 (Encyclopedia of Mathematics and its Applications 42), DOI 10.1017/CBO9780511551574 (bibliographic data verified via Crossref), checked in the publisher's reading sample: §1.2 (an embedding is an injective homomorphism with ā ∈ R^A ⇔ fā ∈ R^B), §2.4 'Maps and the formulas they preserve' (∀1 and ∃1 formulas, not required to be prenex), Theorem 2.4.1 (∃1 formulas are preserved by embeddings), Corollary 2.4.2(a) (∀1 formulas are preserved in substructures), Theorem 2.4.3 ((a) positive existential formulas are preserved by homomorphisms; (b) positive formulas by surjective homomorphisms).
- J. Łoś, 'On the extending of models (I)', Fundamenta Mathematicae 42(1) (1955) 38–54 (bibliographic data verified at https://eudml.org/doc/213372; the paper itself was not opened). Cited, with Tarski 1954, for the Łoś–Tarski preservation theorem, whose statement was verified as Rossman 2008, Theorem 1.1 and footnote 1.
- A. Tarski, 'Contributions to the theory of models. I' and 'II', Indagationes Mathematicae (Proceedings) 57 (1954) 572–581 and 582–588, DOIs 10.1016/S1385-7258(54)50074-0 and 10.1016/S1385-7258(54)50075-2 (bibliographic data verified via Crossref; the papers were not opened).
- E. M. Clarke, O. Grumberg, D. E. Long, 'Model checking and abstraction', ACM TOPLAS 16(5) (1994) 1512–1542, DOI 10.1145/186025.186051 (author PDF checked): abstractions are given by surjections from concrete to abstract states (p. 1513), and ∀CTL* properties true of the abstract model hold of the concrete one (Theorem 5.6). Different formalism: a surjective state abstraction of a Kripke structure, not a first-order embedding.
- C. Loiseaux, S. Graf, J. Sifakis, A. Bouajjani, S. Bensalem, 'Property preserving abstractions for the verification of concurrent systems', Formal Methods in System Design 6(1) (1995) 11–44, DOI 10.1007/BF01384313 (abstract checked): simulations parameterized by Galois connections (α, γ) preserve fragments of the branching-time μ-calculus. Different formalism: Galois-connection abstractions, not first-order embeddings.
- D. Dams, R. Gerth, O. Grumberg, 'Abstract interpretation of reactive systems', ACM TOPLAS 19(2) (1997) 253–291, DOI 10.1145/244795.244800 (first part of the abstract checked): abstract interpretation extended to existential and universal reactive properties. Different formalism, not first-order embeddings.
- P. Cousot, R. Cousot, 'Abstract interpretation: a unified lattice model for static analysis of programs by construction or approximation of fixpoints', POPL 1977, 238–252, DOI 10.1145/512950.512973 (bibliographic data verified; content not checked). Cited as the origin of Galois-connection over-approximation, a different formalism from first-order embeddings.
- E. Clarke, O. Grumberg, S. Jha, Y. Lu, H. Veith, 'Counterexample-guided abstraction refinement', CAV 2000, Lecture Notes in Computer Science, Springer, 154–169, DOI 10.1007/10722167_15 (PDF checked; series volume number not verified): over-approximating abstract models may produce spurious counterexamples, and an abstract counterexample is checked for a corresponding concrete path (Lemma 1); the check concerns one abstract path, not a converse simulation.

**Design question.** When the model extends the system (more elements, same atomic facts about the system's elements), universal claims proved for the model hold for the system, while model counterexamples must be checked against the system.

Basis: execution (Lean kernel check) for every statement quoted in this card, each a theorem checked by the Lean kernel with the axioms recorded under **Evidence**.

Basis: derived (modeling bridge) for the reading of this card in terms of real models and systems. This mirrors over-approximating verification (Clarke, Grumberg and Long 1994; Clarke et al. 2000) in shape: universal model proofs transfer to the system, and model counterexamples must be checked against it. The analogy is one of shape: the cited verification frameworks abstract by surjections or by Galois connections, which are not embeddings, so the theorem does not apply to them as stated; for surjective homomorphisms from system to model, `licences_exact` gives the classes whose model-side falsity is licensed. Reading the two structures as a model and a system is an interpretation, not part of the theorem. The theorem applies to a real model–system pair once both are represented as `Str` values (one binary relation, one unary predicate, equality), the stated map laws are proved for a map between the two representations, and the claim is written as a formula of the stated class; this package carries out none of these steps for any real pair.

**Non-claims.** See **Boundaries → Non-claims → 8.** Read them together with the plain claim.

### 9. `forward-simulation-relates-reachable-states`

**Plain claim.** If S relates every initial concrete state to some initial abstract state (`SimInit`) and matches every concrete step from an S-related pair by zero or more abstract steps ending in an S-related pair (`SimStepStar`), then every reachable concrete state is S-related to some reachable abstract state.

**Kind / tier.** theorem / T0. The basic property of forward simulations; it follows from Lynch and Vaandrager 1995, Lemma 3.8, together with the start condition.

**Lean statement.**

```lean
-- ToyTransfer/Simulation.lean:131-133
theorem reach_related_of_forward_simulation {C A : TS} {S : C.St → A.St → Prop}
    (hi : SimInit C A S) (hs : SimStepStar C A S) :
    ∀ c, Reach C c → ∃ a, S c a ∧ Reach A a := …
```

**Hypotheses.**

| hypothesis | purpose | tightness | counterexample | witness class |
|---|---|---|---|---|
| `hi : SimInit C A S` | starts the induction on reachability | tight | `forward_simulation_needs_init` | the empty relation between one-state systems |
| `hs : SimStepStar C A S` | carries the relation along concrete steps | tight | `forward_simulation_needs_step_matching` | a two-state concrete system whose second state is related to nothing |

**Depth.** shallow.

**Non-vacuity.** `tsTwoStep` (false → true) into `tsBoolHalt` (no steps) with S _ a := a = false: the concrete step is matched by zero abstract steps. (`forward_simulation_nonvacuous`)

**Prior art.**

- N. Lynch, F. Vaandrager, 'Forward and backward simulations, Part I: untimed systems', Information and Computation 121(2) (1995) 214–233, DOI 10.1006/inco.1995.1134 (report version checked): forward simulations between labelled automata (§3.2: start states related; every step matched by a possibly empty sequence of steps with the same external behaviour), proved sound for trace inclusion. The paper has no separate lemma that reachable states are related; it follows from its Lemma 3.8 and the start condition. Its backward simulations (§3.3) go from the implementation to the specification and match steps backward in time; they are not the converse relation used here.
- R. Milner, 'An algebraic definition of simulation between programs', Proc. IJCAI 1971, 481–489 (bibliographic data verified via DBLP and the first page of the proceedings PDF; content not checked). Cited as the original notion of simulation.

**Design question.** Forward simulation is the relation along which safety facts move between an abstract model and a concrete system; in this package both safety transfers along it (`invariant_transfers_down_of_forward_simulation`, `bug_transfers_up_of_forward_simulation`) are proved from this lemma.

Basis: execution (Lean kernel check) for every statement quoted in this card, each a theorem checked by the Lean kernel with the axioms recorded under **Evidence**.

Basis: derived (modeling bridge) for the reading of this card in terms of real models and systems. Reading C as a concrete system and A as an abstract model is an interpretation, not part of the theorem. The theorem applies to a real system and model once both are represented as unlabelled transition systems (`TS`: a state type, a step relation, an initial-state predicate) and the stated simulation laws are proved for a relation between the two representations; this package carries out none of these steps for any real pair.

**Non-claims.** See **Boundaries → Non-claims → 9.** Read them together with the plain claim.

### 10. `safety-invariant-transfers-down-as-existential-pullback`

**Plain claim.** Under `SimInit` and `SimStepStar`, if an invariant I holds on every reachable abstract state, then every reachable concrete state c satisfies the existential pullback: some abstract state a with S c a satisfies I.

**Kind / tier.** theorem / T0. Immediate corollary of `reach_related_of_forward_simulation`; the standard 'proofs transfer down' direction of forward simulation.

**Lean statement.**

```lean
-- ToyTransfer/Simulation.lean:147-150
theorem invariant_transfers_down_of_forward_simulation {C A : TS} {S : C.St → A.St → Prop}
    (hi : SimInit C A S) (hs : SimStepStar C A S) (I : A.St → Prop)
    (hI : ∀ a, Reach A a → I a) :
    ∀ c, Reach C c → ∃ a, S c a ∧ I a := …
```

**Hypotheses.**

| hypothesis | purpose | tightness | counterexample | witness class |
|---|---|---|---|---|
| `hi : SimInit C A S` | via `reach_related_of_forward_simulation` | tight | `forward_simulation_needs_init` | the empty relation between one-state systems, with I := True |
| `hs : SimStepStar C A S` | via `reach_related_of_forward_simulation` | tight | `forward_simulation_needs_step_matching` | a two-state concrete system whose second state is related to nothing, with I := True |
| `hI : ∀ a, Reach A a → I a` | the abstract invariant | tight | `invariant_transfer_needs_abstract_invariant` | I := False on one-state systems |

**Depth.** shallow.

**Non-vacuity.** `tsTwoStep` into `tsBoolHalt`, S _ a := a = false, I a := a = false. (`forward_simulation_nonvacuous`)

**Prior art.**

- N. Lynch, F. Vaandrager, 'Forward and backward simulations, Part I: untimed systems', Information and Computation 121(2) (1995) 214–233, DOI 10.1006/inco.1995.1134 (report version checked): forward simulations between labelled automata (§3.2: start states related; every step matched by a possibly empty sequence of steps with the same external behaviour), proved sound for trace inclusion. The paper has no separate lemma that reachable states are related; it follows from its Lemma 3.8 and the start condition. Its backward simulations (§3.3) go from the implementation to the specification and match steps backward in time; they are not the converse relation used here.
- M. Abadi, L. Lamport, 'The existence of refinement mappings', Theoretical Computer Science 82(2) (1991) 253–284, DOI 10.1016/0304-3975(91)90224-P (bibliographic data verified; the abstract was not accessible; per the authors' publication-page commentary, the paper shows that refinement mappings exist once history and prophecy variables are added, under stated hypotheses). Different formalism: state machines with stuttering and liveness.

**Design question.** Proofs transfer down: an invariant proved for an abstract model yields, for the concrete system, the pulled-back property 'related to some state satisfying I'.

Basis: execution (Lean kernel check) for every statement quoted in this card, each a theorem checked by the Lean kernel with the axioms recorded under **Evidence**.

Basis: derived (modeling bridge) for the reading of this card in terms of real models and systems. Reading C as a concrete system and A as an abstract model is an interpretation, not part of the theorem. The theorem applies to a real system and model once both are represented as unlabelled transition systems (`TS`: a state type, a step relation, an initial-state predicate) and the stated simulation laws are proved for a relation between the two representations; this package carries out none of these steps for any real pair.

**Non-claims.** See **Boundaries → Non-claims → 10.** Read them together with the plain claim.

### 11. `strong-pullback-fails-with-unreachable-related-abstract-state`

**Plain claim.** In a forward simulation from the one-state `tsHalt` to `tsBoolHalt` (abstract `true` unreachable) with S total, the invariant I a := a = false holds on every reachable abstract state, yet the reachable concrete state is S-related to an abstract state violating I: the universal pullback {c | ∀ a, S c a → I a} fails, while the existential pullback holds.

**Kind / tier.** counterexample / T0. A two-state countermodel to a common over-reading.

**Lean statement.**

```lean
-- ToyTransfer/SimCountermodels.lean:68-74
theorem strong_pullback_fails_with_unreachable_related_state :
    SimInit tsHalt tsBoolHalt (fun _ _ => True) ∧
    SimStepStar tsHalt tsBoolHalt (fun _ _ => True) ∧
    (∀ a, Reach tsBoolHalt a → a = false) ∧
    Reach tsHalt () ∧
    ¬ (∀ a, (fun (_ : Unit) (_ : Bool) => True) () a → a = false) ∧
    (∃ a, (fun (_ : Unit) (_ : Bool) => True) () a ∧ a = false) := …
```

**Hypotheses.**

None: the statement is a concrete instance.

**Depth.** definitional.

**Non-vacuity.** Not applicable: a concrete instance.

**Positive controls** (nearby settings, with stronger hypotheses, where the transfer does hold): `invariant_transfers_down_of_forward_simulation`, `strong_pullback_of_functional_simulation`, `reach_restricted_simulation_gives_strong_pullback`.

**Prior art.**

- M. Abadi, L. Lamport, 'The existence of refinement mappings', Theoretical Computer Science 82(2) (1991) 253–284, DOI 10.1016/0304-3975(91)90224-P (bibliographic data verified; the abstract was not accessible; per the authors' publication-page commentary, the paper shows that refinement mappings exist once history and prophecy variables are added, under stated hypotheses). Different formalism: state machines with stuttering and liveness.

**Design question.** Shows why the transferred safety property must be read as 'related to some good abstract state', not 'all related abstract states are good', unless S is functional or restricted to reachable abstract states.

Basis: execution (Lean kernel check) for every statement quoted in this card, each a theorem checked by the Lean kernel with the axioms recorded under **Evidence**.

Basis: derived (modeling bridge) for the reading of this card in terms of real models and systems. A countermodel shows that the hypotheses it states do not suffice in general: no argument that uses those hypotheses alone can establish the transfer. It does not show that the transfer fails for a particular real system and model; this package represents no real system or model.

**Non-claims.** See **Boundaries → Non-claims → 11.** Read them together with the plain claim.

### 12. `bugs-transfer-up-along-forward-simulation`

**Plain claim.** Under `SimInit` and `SimStepStar`, if every abstract state S-related to a bad concrete state is bad (hbad), then every reachable bad concrete state is S-related to a reachable bad abstract state.

**Kind / tier.** theorem / T0. Direct corollary of `reach_related_of_forward_simulation` with the bad-state hypothesis.

**Lean statement.**

```lean
-- ToyTransfer/Simulation.lean:158-161
theorem bug_transfers_up_of_forward_simulation {C A : TS} {S : C.St → A.St → Prop}
    (hi : SimInit C A S) (hs : SimStepStar C A S) (BadC : C.St → Prop) (BadA : A.St → Prop)
    (hbad : ∀ c a, S c a → BadC c → BadA a) :
    ∀ c, Reach C c → BadC c → ∃ a, S c a ∧ Reach A a ∧ BadA a := …
```

**Hypotheses.**

| hypothesis | purpose | tightness | counterexample | witness class |
|---|---|---|---|---|
| `hi : SimInit C A S` | via `reach_related_of_forward_simulation` | tight | `forward_simulation_needs_init` | the empty relation between one-state systems, BadC = BadA := True |
| `hs : SimStepStar C A S` | via `reach_related_of_forward_simulation` | tight | `forward_simulation_needs_step_matching` | a two-state concrete system whose second state is related to nothing, BadC = BadA := True |
| `hbad : ∀ c a, S c a → BadC c → BadA a` | related states agree on badness, in this direction | tight | `bug_transfer_needs_bad_compatibility` | one-state systems with BadC := True and BadA := False |

**Depth.** shallow.

**Non-vacuity.** The identity relation on `tsTwoStep` with BadC = BadA := (· = true): the bad state `true` is reachable and the initial state is not bad. (`bug_transfer_up_nonvacuous`)

**Prior art.**

- N. Lynch, F. Vaandrager, 'Forward and backward simulations, Part I: untimed systems', Information and Computation 121(2) (1995) 214–233, DOI 10.1006/inco.1995.1134 (report version checked): forward simulations between labelled automata (§3.2: start states related; every step matched by a possibly empty sequence of steps with the same external behaviour), proved sound for trace inclusion. The paper has no separate lemma that reachable states are related; it follows from its Lemma 3.8 and the start condition. Its backward simulations (§3.3) go from the implementation to the specification and match steps backward in time; they are not the converse relation used here.

**Design question.** Bugs transfer up: if the relation relates every concrete initial state to an abstract initial state, matches every concrete step from a related pair by zero or more abstract steps, and relates bad concrete states to bad abstract states (every abstract state related to a bad concrete state is bad), then every reachable concrete bug is related to a reachable abstract bug.

Basis: execution (Lean kernel check) for every statement quoted in this card, each a theorem checked by the Lean kernel with the axioms recorded under **Evidence**.

Basis: derived (modeling bridge) for the reading of this card in terms of real models and systems. Reading C as a concrete system and A as an abstract model is an interpretation, not part of the theorem. The theorem applies to a real system and model once both are represented as unlabelled transition systems (`TS`: a state type, a step relation, an initial-state predicate) and the stated simulation laws are proved for a relation between the two representations; this package carries out none of these steps for any real pair.

**Non-claims.** See **Boundaries → Non-claims → 12.** Read them together with the plain claim.

### 13. `spurious-abstract-counterexample-under-forward-simulation`

**Plain claim.** `relHaltTwoStep` is a forward simulation from the one-state `tsHalt` to `tsTwoStep` (false → true); related states agree on badness (`badNone`, `badTrue`: no concrete state is bad, the abstract state `true` is bad); the converse relation relates initial states but does not match the abstract step false → true. The abstract system reaches its bad state, while no reachable concrete state is bad and no concrete state is related to the abstract bad state.

**Kind / tier.** counterexample / T0. A two-state instance of the spurious counterexamples of abstraction refinement (Clarke et al. 2000).

**Lean statement.**

```lean
-- ToyTransfer/SimCountermodels.lean:178-186
theorem spurious_abstract_counterexample :
    SimInit tsHalt tsTwoStep relHaltTwoStep ∧ SimStepStar tsHalt tsTwoStep relHaltTwoStep ∧
    (∀ c a, relHaltTwoStep c a → (badNone c ↔ badTrue a)) ∧
    SimInit tsTwoStep tsHalt (fun a c => relHaltTwoStep c a) ∧
    ¬ SimStepStar tsTwoStep tsHalt (fun a c => relHaltTwoStep c a) ∧
    Reach tsTwoStep true ∧ badTrue true ∧
    (∀ c, Reach tsHalt c → ¬ badNone c) ∧
    (∀ c, ¬ relHaltTwoStep c true) ∧
    ¬ (∃ c, relHaltTwoStep c true ∧ Reach tsHalt c ∧ badNone c) := …
```

**Hypotheses.**

None: the statement is a concrete instance.

**Depth.** definitional.

**Non-vacuity.** Not applicable: a concrete instance.

**Positive controls** (nearby settings, with stronger hypotheses, where the transfer does hold): `bug_transfers_down_of_converse_simulation`.

**Prior art.**

- E. Clarke, O. Grumberg, S. Jha, Y. Lu, H. Veith, 'Counterexample-guided abstraction refinement', CAV 2000, Lecture Notes in Computer Science, Springer, 154–169, DOI 10.1007/10722167_15 (PDF checked; series volume number not verified): over-approximating abstract models may produce spurious counterexamples, and an abstract counterexample is checked for a corresponding concrete path (Lemma 1); the check concerns one abstract path, not a converse simulation.

**Design question.** Forward simulation alone does not transfer abstract counterexamples: this instance satisfies it, and its abstract counterexample has no concrete counterpart. Further arguments that do transfer an abstract counterexample include a converse simulation (`bug_transfers_down_of_converse_simulation`) and concretization of the individual trace (Clarke et al. 2000; not formalized here).

Basis: execution (Lean kernel check) for every statement quoted in this card, each a theorem checked by the Lean kernel with the axioms recorded under **Evidence**.

Basis: derived (modeling bridge) for the reading of this card in terms of real models and systems. A countermodel shows that the hypotheses it states do not suffice in general: no argument that uses those hypotheses alone can establish the transfer. It does not show that the transfer fails for a particular real system and model; this package represents no real system or model. The instance has the shape of the spurious abstract counterexamples that counterexample-guided abstraction refinement (Clarke et al. 2000) detects by checking an abstract counterexample against the concrete system; that check is not formalized here.

**Non-claims.** See **Boundaries → Non-claims → 13.** Read them together with the plain claim.

### 14. `abstract-bugs-transfer-down-along-converse-simulation`

**Plain claim.** If the converse relation (a ↦ c when S c a) relates every initial abstract state to an initial concrete state and matches every abstract step from a related pair by zero or more concrete steps (a forward simulation from A to C), and every concrete state S-related to a bad abstract state is bad, then every reachable bad abstract state is S-related to a reachable bad concrete state. S itself is not assumed to be a forward simulation from C to A.

**Kind / tier.** theorem / T0. Instance of `bug_transfers_up_of_forward_simulation` with the roles of the two systems exchanged.

**Lean statement.**

```lean
-- ToyTransfer/Simulation.lean:172-175
theorem bug_transfers_down_of_converse_simulation {C A : TS} {S : C.St → A.St → Prop}
    (hi : SimInit A C (fun a c => S c a)) (hs : SimStepStar A C (fun a c => S c a))
    (BadC : C.St → Prop) (BadA : A.St → Prop) (hbad : ∀ c a, S c a → BadA a → BadC c) :
    ∀ a, Reach A a → BadA a → ∃ c, S c a ∧ Reach C c ∧ BadC c := …
```

**Hypotheses.**

| hypothesis | purpose | tightness | counterexample | witness class |
|---|---|---|---|---|
| `hi : SimInit A C (fun a c => S c a)` | starts the induction on abstract reachability | tight | `converse_simulation_needs_init` | the empty relation between one-state systems |
| `hs : SimStepStar A C (fun a c => S c a)` | carries the converse relation along abstract steps | tight | `spurious_abstract_counterexample` | a one-state concrete system and a two-state abstract system whose step is not matched |
| `hbad : ∀ c a, S c a → BadA a → BadC c` | related states agree on badness, in this direction | tight | `converse_simulation_needs_bad_compatibility` | one-state systems with BadA := True and BadC := False |

**Depth.** definitional. The proof is `bug_transfers_up_of_forward_simulation` applied with the systems exchanged.

**Non-vacuity.** The identity relation on `tsTwoStep`, read in both directions, with BadC = BadA := (· = true). (`converse_simulation_nonvacuous`)

**Prior art.**

- N. Lynch, F. Vaandrager, 'Forward and backward simulations, Part I: untimed systems', Information and Computation 121(2) (1995) 214–233, DOI 10.1006/inco.1995.1134 (report version checked): forward simulations between labelled automata (§3.2: start states related; every step matched by a possibly empty sequence of steps with the same external behaviour), proved sound for trace inclusion. The paper has no separate lemma that reachable states are related; it follows from its Lemma 3.8 and the start condition. Its backward simulations (§3.3) go from the implementation to the specification and match steps backward in time; they are not the converse relation used here.
- E. Clarke, O. Grumberg, S. Jha, Y. Lu, H. Veith, 'Counterexample-guided abstraction refinement', CAV 2000, Lecture Notes in Computer Science, Springer, 154–169, DOI 10.1007/10722167_15 (PDF checked; series volume number not verified): over-approximating abstract models may produce spurious counterexamples, and an abstract counterexample is checked for a corresponding concrete path (Lemma 1); the check concerns one abstract path, not a converse simulation.

**Design question.** Abstract counterexamples transfer down when the concrete system can match every abstract behaviour (a completeness property); this is a sufficient condition, and it is not necessary (`abstract_bug_transfer_without_converse_step_matching`).

Basis: execution (Lean kernel check) for every statement quoted in this card, each a theorem checked by the Lean kernel with the axioms recorded under **Evidence**.

Basis: derived (modeling bridge) for the reading of this card in terms of real models and systems. Reading C as a concrete system and A as an abstract model is an interpretation, not part of the theorem. The theorem applies to a real system and model once both are represented as unlabelled transition systems (`TS`: a state type, a step relation, an initial-state predicate) and the stated simulation laws are proved for a relation between the two representations; this package carries out none of these steps for any real pair.

**Non-claims.** See **Boundaries → Non-claims → 14.** Read them together with the plain claim.

### 15. `termination-transfers-down-along-lockstep-simulation`

**Plain claim.** If S relates every initial concrete state to some initial abstract state (`SimInit`) and matches every concrete step from an S-related pair by a single abstract step (`SimStepLock`: one step, the matching successor need not be unique), and every reachable state of A terminates (accessible for the converse step relation), then every reachable state of C terminates.

**Kind / tier.** theorem / T0. Lock-step forward simulation transfers termination down; mechanized in CompCert (`forward_simulation_step`, preservation of silent divergence) for labelled small-step semantics.

**Lean statement.**

```lean
-- ToyTransfer/Simulation.lean:224-226
theorem allRunsFinite_transfers_down_of_lockstep {C A : TS} {S : C.St → A.St → Prop}
    (hi : SimInit C A S) (hs : SimStepLock C A S) (hA : AllRunsFinite A) :
    AllRunsFinite C := …
```

**Hypotheses.**

| hypothesis | purpose | tightness | counterexample | witness class |
|---|---|---|---|---|
| `hi : SimInit C A S` | relates reachable concrete states to reachable abstract states | tight | `termination_transfer_needs_init` | the empty relation from a one-state self-loop to a one-state halting system |
| `hs : SimStepLock C A S` | every concrete step forces an abstract step | tight | `stuttering_simulation_does_not_transfer_termination` | a stuttering (zero-step) simulation from a one-state self-loop to a one-state halting system |
| `hA : AllRunsFinite A` | abstract termination | tight | `termination_transfer_needs_abstract_termination` | the total relation between two one-state self-loops |

**Depth.** shallow.

**Non-vacuity.** The identity relation on `tsTwoStep`. (`lockstep_nonvacuous`)

**Prior art.**

- X. Leroy, 'A formally verified compiler back-end', J. Automated Reasoning 43(4) (2009) 363–446, DOI 10.1007/s10817-009-9155-4 (bibliographic data verified), and the CompCert development, file common/Smallstep.v at commit 2685140bf72c959446981fb99b5e44a8975021bc of AbsInt/CompCert (checked): `fsim_properties` (line 566; a well-founded order, and each step matched by a non-empty sequence of steps or by a possibly empty sequence with a decrease), `forward_simulation_step` (line 727, lock-step), `forward_simulation_opt` (line 752, zero or one step with a decreasing natural-number measure), `simulation_forever_silent` (line 972, infinite silent runs are preserved). Different formalism: labelled small-step semantics with traces; divergence is coinductive rather than `Acc`.
- C. Sternagel, R. Thiemann, 'Abstract Rewriting', Archive of Formal Proofs, June 2010, https://isa-afp.org/entries/Abstract-Rewriting.html (entry page and its bibliographic record verified; no DOI was found for the entry at Crossref; development version checked at the AFP mirror, Abstract_Rewriting.thy, at a revision that was not recorded): strong normalization defined as the absence of infinite chains (`SN_on`), with `SN_iff_wf` and `SN_on_conv_accp` relating it to well-foundedness and accessibility (the Isabelle counterpart of `terminates_iff_no_infinite_run`).

**Design question.** Termination proved for an abstract model transfers to the concrete system when every concrete step is matched by an abstract step.

Basis: execution (Lean kernel check) for every statement quoted in this card, each a theorem checked by the Lean kernel with the axioms recorded under **Evidence**.

Basis: derived (modeling bridge) for the reading of this card in terms of real models and systems. Reading C as a concrete system and A as an abstract model is an interpretation, not part of the theorem. The theorem applies to a real system and model once both are represented as unlabelled transition systems (`TS`: a state type, a step relation, an initial-state predicate) and the stated simulation laws are proved for a relation between the two representations; this package carries out none of these steps for any real pair.

**Non-claims.** See **Boundaries → Non-claims → 15.** Read them together with the plain claim.

### 16. `stuttering-simulation-does-not-transfer-termination`

**Plain claim.** From the one-state self-loop `tsLoop` to the one-state halting `tsHalt`, the total relation relates initial states and matches the concrete step by zero abstract steps (`SimStepStutter`, hence also `SimStepStar`) but is not lock-step; every reachable abstract state terminates; the reachable concrete state does not (¬ AllRunsFinite tsLoop), and the concrete system has an explicit infinite run from a reachable state.

**Kind / tier.** counterexample / T0. The standard one-state countermodel: stuttering matching lets a concrete loop simulate a halted abstract state.

**Lean statement.**

```lean
-- ToyTransfer/SimCountermodels.lean:281-285
theorem stuttering_simulation_does_not_transfer_termination :
    SimInit tsLoop tsHalt (fun _ _ => True) ∧ SimStepStutter tsLoop tsHalt (fun _ _ => True) ∧
    SimStepStar tsLoop tsHalt (fun _ _ => True) ∧ ¬ SimStepLock tsLoop tsHalt (fun _ _ => True) ∧
    AllRunsFinite tsHalt ∧ ¬ AllRunsFinite tsLoop ∧
    (∃ f : Nat → tsLoop.St, Reach tsLoop (f 0) ∧ ∀ i, tsLoop.step (f i) (f (i + 1))) := …
```

**Hypotheses.**

None: the statement is a concrete instance.

**Depth.** definitional.

**Non-vacuity.** Not applicable: a concrete instance.

**Positive controls** (nearby settings, with stronger hypotheses, where the transfer does hold): `allRunsFinite_transfers_down_of_lockstep`, `allRunsFinite_transfers_down_of_wf_simulation`.

**Prior art.**

- K. S. Namjoshi, 'A simple characterization of stuttering bisimulation', FSTTCS 1997, Lecture Notes in Computer Science 1346, 284–296, DOI 10.1007/BFb0058037 (PDF checked): well-founded bisimulation, a symmetric relation with a rank function S × S × S → W into a well-founded set and three matching clauses (a step, a stutter of the first state with a rank decrease, or a step of the second state with a rank decrease), is sound and complete for stuttering bisimulation (Theorems 1 and 2). Different formalism: symmetric bisimulation on labelled transition systems; the criterion here is one-sided.
- M. C. Browne, E. M. Clarke, O. Grumberg, 'Characterizing finite Kripke structures in propositional temporal logic', Theoretical Computer Science 59(1–2) (1988) 115–131, DOI 10.1016/0304-3975(88)90098-9 (bibliographic data verified; content not checked). Cited as the origin of stuttering equivalence.

**Design question.** Does a stuttering simulation, which satisfies the simulation hypotheses of the safety transfers (`invariant_transfers_down_of_forward_simulation`, `bug_transfers_up_of_forward_simulation`; see `SimStepStutter.toStar`), also transfer termination? Not in general: in this countermodel the relation is a stuttering simulation and every reachable abstract state terminates, the reachable concrete state does not terminate, and for this relation no well-founded measure satisfies `SimStepWF` (`stuttering_countermodel_admits_no_wf_measure`).

Basis: execution (Lean kernel check) for every statement quoted in this card, each a theorem checked by the Lean kernel with the axioms recorded under **Evidence**.

Basis: derived (modeling bridge) for the reading of this card in terms of real models and systems. A countermodel shows that the hypotheses it states do not suffice in general: no argument that uses those hypotheses alone can establish the transfer. It does not show that the transfer fails for a particular real system and model; this package represents no real system or model.

**Non-claims.** See **Boundaries → Non-claims → 16.** Read them together with the plain claim.

### 17. `well-founded-simulation-criterion-transfers-termination`

**Plain claim.** If S relates every initial concrete state to some initial abstract state (`SimInit`), every concrete step from an S-related pair is matched either by one abstract step or by no abstract step with a strict decrease of a measure μ(c, a) in a well-founded relation lt (`SimStepWF`), and every reachable state of A terminates (accessible for the converse step relation), then every reachable state of C terminates.

**Kind / tier.** theorem / T0. The well-founded simulation criterion for termination; mechanized in CompCert for labelled small-step semantics (`fsim_properties` with a well-founded order, `forward_simulation_opt`, `simulation_forever_silent`).

**Lean statement.**

```lean
-- ToyTransfer/Simulation.lean:256-259
theorem allRunsFinite_transfers_down_of_wf_simulation {C A : TS} {S : C.St → A.St → Prop}
    {W : Type} (lt : W → W → Prop) (hwf : WellFounded lt) (μ : C.St → A.St → W)
    (hi : SimInit C A S) (hs : SimStepWF C A S lt μ) (hA : AllRunsFinite A) :
    AllRunsFinite C := …
```

**Hypotheses.**

| hypothesis | purpose | tightness | counterexample | witness class |
|---|---|---|---|---|
| `hwf : WellFounded lt` | stuttering steps cannot repeat forever | tight | `wf_simulation_needs_wellFounded` | the total relation on Unit as the measure order, in the stuttering countermodel |
| `hi : SimInit C A S` | relates reachable concrete states to reachable abstract states | tight | `termination_transfer_needs_init` | the empty relation from a self-loop to a halting system |
| `hs : SimStepWF C A S lt μ` | each concrete step is an abstract step or a measured stutter | tight | `wf_simulation_needs_measure_decrease` | the stuttering countermodel with a constant measure into Unit; for that relation every measure into every well-founded order fails `SimStepWF` (`stuttering_countermodel_admits_no_wf_measure`) |
| `hA : AllRunsFinite A` | abstract termination | tight | `termination_transfer_needs_abstract_termination` | the total relation between two self-loops |

**Depth.** substantive. Nested well-founded inductions, on abstract accessibility and on the measure.

**Non-vacuity.** `tsTwoStep` into `tsBoolHalt` with S _ a := a = false and measure 1 at `false`, 0 at `true`: a genuine stutter with a measure decrease. (`wf_simulation_nonvacuous`)

**Prior art.**

- X. Leroy, 'A formally verified compiler back-end', J. Automated Reasoning 43(4) (2009) 363–446, DOI 10.1007/s10817-009-9155-4 (bibliographic data verified), and the CompCert development, file common/Smallstep.v at commit 2685140bf72c959446981fb99b5e44a8975021bc of AbsInt/CompCert (checked): `fsim_properties` (line 566; a well-founded order, and each step matched by a non-empty sequence of steps or by a possibly empty sequence with a decrease), `forward_simulation_step` (line 727, lock-step), `forward_simulation_opt` (line 752, zero or one step with a decreasing natural-number measure), `simulation_forever_silent` (line 972, infinite silent runs are preserved). Different formalism: labelled small-step semantics with traces; divergence is coinductive rather than `Acc`.
- K. S. Namjoshi, 'A simple characterization of stuttering bisimulation', FSTTCS 1997, Lecture Notes in Computer Science 1346, 284–296, DOI 10.1007/BFb0058037 (PDF checked): well-founded bisimulation, a symmetric relation with a rank function S × S × S → W into a well-founded set and three matching clauses (a step, a stutter of the first state with a rank decrease, or a step of the second state with a rank decrease), is sound and complete for stuttering bisimulation (Theorems 1 and 2). Different formalism: symmetric bisimulation on labelled transition systems; the criterion here is one-sided.
- P. Manolios, K. Namjoshi, R. Sumners, 'Linking theorem proving and model-checking with well-founded bisimulation', CAV 1999, Lecture Notes in Computer Science, Springer, 369–379, DOI 10.1007/3-540-48683-6_32 (technical-report version checked; series volume number not verified): well-founded equivalence bisimulations with a rank function S × S → W, on transition systems whose transition relation must be left total (Definition 1), so no run ends. Different formalism.
- R. W. Floyd, 'Assigning meanings to programs', Mathematical Aspects of Computer Science, Proc. Symposia in Applied Mathematics 19, AMS 1967, 19–32, DOI 10.1090/psapm/019/0235771 (bibliographic data verified via Crossref and the ACM Turing Award bibliography; content not checked). Cited as the origin of well-founded ranking arguments for termination.
- C. Sternagel, R. Thiemann, 'Abstract Rewriting', Archive of Formal Proofs, June 2010, https://isa-afp.org/entries/Abstract-Rewriting.html (entry page and its bibliographic record verified; no DOI was found for the entry at Crossref; development version checked at the AFP mirror, Abstract_Rewriting.thy, at a revision that was not recorded): strong normalization defined as the absence of infinite chains (`SN_on`), with `SN_iff_wf` and `SN_on_conv_accp` relating it to well-foundedness and accessibility (the Isabelle counterpart of `terminates_iff_no_infinite_run`).

**Design question.** When a concrete system refines an abstract one with internal steps (stuttering), termination transfers down if every stutter decreases a well-founded measure.

Basis: execution (Lean kernel check) for every statement quoted in this card, each a theorem checked by the Lean kernel with the axioms recorded under **Evidence**.

Basis: derived (modeling bridge) for the reading of this card in terms of real models and systems. Reading C as a concrete system and A as an abstract model is an interpretation, not part of the theorem. The theorem applies to a real system and model once both are represented as unlabelled transition systems (`TS`: a state type, a step relation, an initial-state predicate) and the stated simulation laws are proved for a relation between the two representations; this package carries out none of these steps for any real pair.

**Non-claims.** See **Boundaries → Non-claims → 17.** Read them together with the plain claim.

### 18. `no-relation-transfer-iff-decided-by-model-or-system-class`

**Plain claim.** Let KM be a class of models, KS a class of systems and φ a sentence, with no map between model and system assumed. The statement 'for every model T in KM and every system R in KS, if φ holds in T then φ holds in R' is true exactly when φ is unsatisfiable in KM or valid in KS (`unrelated_truth_transfer_iff`). The statement 'for every model T in KM and every system R in KS, if φ fails in T then φ fails in R' is true exactly when φ is valid in KM or unsatisfiable in KS (`unrelated_falsity_transfer_iff`). The statement 'for every model T in KM and every system R in KS, if φ holds in T then φ fails in R' (reading a model result as a refutation) is true exactly when φ is unsatisfiable in KM or unsatisfiable in KS (`unrelated_refutation_licensed_iff`); for KM = KS = K, the statement 'for every T and every R in K, if φ holds in T then φ fails in R' is true exactly when φ is unsatisfiable in K (`unrelated_refutation_licensed_iff_unsat_same_class`). In each statement both quantifiers range over the whole implication: it says that for each model T of KM in which the premise holds, the conclusion holds in every system of KS. If φ holds in some model of KM and KS contains both a system satisfying φ and one falsifying it, then there is a model T of KM satisfying φ such that KS contains a system satisfying φ and a system falsifying φ, so this model result is consistent with both system outcomes (`unrelated_model_result_consistent_with_both`).

**Kind / tier.** characterization / T0. Elementary predicate-logic facts, stated for satisfaction of sentences; they do not use the structure of formulas.

**Lean statement.**

```lean
-- ToyTransfer/Disclaimer.lean:38-39
theorem unrelated_truth_transfer_iff (KM KS : Str → Prop) (φ : Fml 0) :
    (∀ T R, KM T → KS R → SatS T φ → SatS R φ) ↔ (UnsatIn KM φ ∨ ValidIn KS φ) := …

-- ToyTransfer/Disclaimer.lean:52-53
theorem unrelated_falsity_transfer_iff (KM KS : Str → Prop) (φ : Fml 0) :
    (∀ T R, KM T → KS R → ¬ SatS T φ → ¬ SatS R φ) ↔ (ValidIn KM φ ∨ UnsatIn KS φ) := …

-- ToyTransfer/Disclaimer.lean:67-68
theorem unrelated_refutation_licensed_iff (KM KS : Str → Prop) (φ : Fml 0) :
    (∀ T R, KM T → KS R → SatS T φ → ¬ SatS R φ) ↔ (UnsatIn KM φ ∨ UnsatIn KS φ) := …

-- ToyTransfer/Disclaimer.lean:82-83
theorem unrelated_refutation_licensed_iff_unsat_same_class (K : Str → Prop) (φ : Fml 0) :
    (∀ T R, K T → K R → SatS T φ → ¬ SatS R φ) ↔ UnsatIn K φ := …

-- ToyTransfer/Disclaimer.lean:89-92
theorem unrelated_model_result_consistent_with_both (KM KS : Str → Prop) (φ : Fml 0)
    (hsatM : ∃ T, KM T ∧ SatS T φ) (hsatS : ∃ R, KS R ∧ SatS R φ)
    (hnvS : ∃ R, KS R ∧ ¬ SatS R φ) :
    ∃ T, KM T ∧ SatS T φ ∧ (∃ R, KS R ∧ SatS R φ) ∧ (∃ R, KS R ∧ ¬ SatS R φ) := …
```

**Hypotheses.**

| hypothesis | purpose | tightness | counterexample | witness class |
|---|---|---|---|---|
| `hsatM : ∃ T, KM T ∧ SatS T φ (consistency form; the iff statements have no hypotheses)` | the model result is possible | tight | `consistent_with_both_needs_model_satisfiable` | KM := structures falsifying ∃x, P x |
| `hsatS : ∃ R, KS R ∧ SatS R φ (consistency form)` | some system agrees | tight | `consistent_with_both_needs_system_satisfiable` | KS := structures falsifying ∃x, P x |
| `hnvS : ∃ R, KS R ∧ ¬ SatS R φ (consistency form)` | some system disagrees | tight | `consistent_with_both_needs_system_not_valid` | KS := structures satisfying ∃x, P x |

**Depth.** definitional.

**Non-vacuity.** Over all structures (KM = KS), ∃x, P x is neither valid nor unsatisfiable and none of the three transfers is licensed (`unrelated_nonvacuous`); with KM = all structures and KS = the structures with non-empty carrier, for every model T of KM and every system R of KS, truth of ∃x, x = x in T implies its truth in R, because the system class decides it, although ∃x, x = x is neither valid nor unsatisfiable over all structures (`unrelated_two_class_example`). (`unrelated_nonvacuous`, `unrelated_two_class_example`)

**Prior art.**

- No specific prior statement of the characterizations located; elementary consequence of the definitions.
- B. Rossman, 'Homomorphism preservation theorems', J. ACM 55(3), Article 15, 15:1–15:53 (2008), DOI 10.1145/1379759.1379763 (author PDF checked): Theorem 1.1 (Łoś–Tarski: preservation under embeddings iff equivalent to an existential formula; footnote 1: an embedding is an isomorphism onto an induced substructure, and the dual form is preservation under induced substructures iff universal), Theorem 1.2 (Lyndon's positivity theorem: surjective homomorphisms, positive formulas), Theorem 1.3 (homomorphism preservation theorem: homomorphisms, existential-positive formulas), Theorems 1.4 and 1.5 (Łoś–Tarski and Lyndon fail over finite structures; p. 3 attributes 1.4 to Tait 1959 and Gurevich–Shelah via Gurevich 1984, and 1.5 to Ajtai–Gurevich 1987 and Stolboushkin 1995), Theorem 1.7 (finite homomorphism preservation for sentences), Lemma 2.3 (the easy direction), §2.1.1 (structures have non-empty universes; substructure versus induced substructure), Remark 2.1 (formulas are not required to be prenex).

**Design question.** What does a model result license about a system when no relation between them is proved? For a model class KM and a system class KS, a transfer statement over every model of KM and every system of KS holds exactly when the model class or the system class settles φ in the way given by the three characterizations.

Basis: execution (Lean kernel check) for every statement quoted in this card, each a theorem checked by the Lean kernel with the axioms recorded under **Evidence**.

Basis: derived (modeling bridge) for the reading of this card in terms of real models and systems. A scope statement should name the proved model–system relation, or say that the results neither establish nor refute the corresponding system claims. Reasoning: reading a model result as a refutation of the system claim is the refutation statement of this card, and `unrelated_refutation_licensed_iff` shows that it holds exactly when φ is unsatisfiable in KM or unsatisfiable in KS; for a sentence that is satisfiable in KM and satisfiable in KS it does not hold, so such a reading is unlicensed. Whether a particular disclaimer wording is read as such a refutation is a question about readers, which this package does not examine. Reading KM and KS as the possible models and systems is an interpretation: the characterizations apply to real models and systems once each is represented as a `Str` value and the claim as a sentence.

**Non-claims.** See **Boundaries → Non-claims → 18.** Read them together with the plain claim.

### 19. `unlicensed-cell-admits-both-outcomes-along-non-isomorphisms`

**Plain claim.** For every class c, map kind k and direction d, the cell (c, k, d) is unlicensed in the transfer table exactly when it admits both outcomes along non-isomorphisms (`bothOutcomesNonIso_iff_unlicensed`): there is a formula φ of class c (with parameters), a structure at the known end with an environment at which φ holds, and two k-maps, neither an isomorphism, such that φ holds at the other end of one and fails at the other end of the other. For a forward cell the known end is the source A with environment e, and φ is evaluated in each target at h ∘ e. For a backward cell the known end is the target B with environment b; each of the two maps h comes with a source environment e that it sends to b pointwise (h (e i) = b i for every i), and φ is evaluated in the source at that e. The two maps need not be distinct: in `both_eq` both outcomes use the map `collapse`, with two different source environments. Unlicensed does not mean that nothing transfers: model-side falsity is licensed while model-side truth is not for exactly seven (kind, orientation, class) triples (`falsity_licensed_where_truth_unlicensed_iff`), and some unlicensed cells contain proper subclasses that transfer (`unlicensed_cells_contain_transferring_subclasses`).

**Kind / tier.** characterization / T1. Folklore ('an unlicensed preservation cell carries no guarantee') made precise and corrected; not found mechanized in the sources checked.

**Lean statement.**

```lean
-- ToyTransfer/Disclaimer.lean:311-312
theorem bothOutcomesNonIso_iff_unlicensed (c : Cls) (k : MapKind) (d : Dir) :
    BothOutcomesNonIso c k d ↔ licensedB c k d = false := …

-- ToyTransfer/Disclaimer.lean:404-409
theorem falsity_licensed_where_truth_unlicensed_iff (k : MapKind) (o : Orient) (c : Cls) :
    (¬ TruthLicensed c k o ∧ FalsityLicensed c k o) ↔
      (k, o, c) ∈ [(.emb, .modelToSystem, .univ), (.emb, .systemToModel, .exist),
        (.emb, .systemToModel, .posExist), (.strong, .systemToModel, .posExist),
        (.hom, .systemToModel, .posExist), (.surj, .systemToModel, .pos),
        (.surj, .systemToModel, .posExist)] := …

-- ToyTransfer/Disclaimer.lean:418-428
theorem unlicensed_cells_contain_transferring_subclasses :
    (licensedB .univ .emb .fwd = false ∧ (∀ {n} (φ : Fml n), IsQF φ → IsUniv φ) ∧
      Preserves .qf .emb .fwd) ∧
    (licensedB .exist .emb .bwd = false ∧ (∀ {n} (φ : Fml n), IsQF φ → IsExist φ) ∧
      Preserves .qf .emb .bwd) ∧
    (licensedB .ae .emb .fwd = false ∧ (∀ {n} (φ : Fml n), IsExist φ → IsAE φ) ∧
      Preserves .exist .emb .fwd) ∧
    (licensedB .ea .emb .bwd = false ∧ (∀ {n} (φ : Fml n), IsUniv φ → IsEA φ) ∧
      Preserves .univ .emb .bwd) ∧
    (licensedB .pos .hom .fwd = false ∧ (∀ {n} (φ : Fml n), IsPosExist φ → IsPos φ) ∧
      Preserves .posExist .hom .fwd) := …
```

**Hypotheses.**

None (the statement has no hypotheses).

**Depth.** shallow. 47 per-cell witnesses checked by evaluation, grouped into 13 witness lemmas, plus the converse from `licensedB_iff`.

**Non-vacuity.** `bothOutcomesNonIso_examples`: the universal/embedding/forward cell admits both outcomes; the universal/embedding/backward cell does not. (`bothOutcomesNonIso_examples`)

**Prior art.**

- W. Hodges, Model Theory, Cambridge University Press 1993 (Encyclopedia of Mathematics and its Applications 42), DOI 10.1017/CBO9780511551574 (bibliographic data verified via Crossref), checked in the publisher's reading sample: §1.2 (an embedding is an injective homomorphism with ā ∈ R^A ⇔ fā ∈ R^B), §2.4 'Maps and the formulas they preserve' (∀1 and ∃1 formulas, not required to be prenex), Theorem 2.4.1 (∃1 formulas are preserved by embeddings), Corollary 2.4.2(a) (∀1 formulas are preserved in substructures), Theorem 2.4.3 ((a) positive existential formulas are preserved by homomorphisms; (b) positive formulas by surjective homomorphisms).

**Design question.** What may a reader conclude from an unlicensed cell? That the transfer is not guaranteed: for some formula of the class, genuine (non-isomorphism) maps of that kind lead to both outcomes. Not that the claim is refuted, and not that every formula of the class fails to transfer.

Basis: execution (Lean kernel check) for every statement quoted in this card, each a theorem checked by the Lean kernel with the axioms recorded under **Evidence**.

Basis: derived (modeling bridge) for the reading of this card in terms of real models and systems. Reading the two structures as a model and a system is an interpretation, not part of the theorem. The theorem applies to a real model–system pair once both are represented as `Str` values (one binary relation, one unary predicate, equality), the stated map laws are proved for a map between the two representations, and the claim is written as a formula of the stated class; this package carries out none of these steps for any real pair.

**Non-claims.** See **Boundaries → Non-claims → 19.** Read them together with the plain claim.

### 20. `exact-licences-per-map-kind-and-orientation`

**Plain claim.** For every map kind k, orientation o (h : model → system, or h : system → model) and class c: model-side truth of class-c formulas (with parameters, the environment pushed along h) is licensed for the system along every k-map in orientation o exactly when c ∈ truthList k o, and model-side falsity exactly when c ∈ falsityList k o. Model to system: embedding — truth [qf, exist, posExist], falsity [qf, univ]; strong homomorphism and homomorphism — truth [posExist], falsity []; surjective homomorphism — truth [pos, posExist], falsity []. System to model: embedding — truth [qf, univ], falsity [qf, exist, posExist]; strong homomorphism and homomorphism — truth [], falsity [posExist]; surjective homomorphism — truth [], falsity [pos, posExist].

**Kind / tier.** characterization / T0. A re-indexing of the transfer matrix by orientation (model-to-system or system-to-model) and truth value; the licensed cells are the easy preservation theorems (Hodges 1993, §2.4).

**Lean statement.**

```lean
-- ToyTransfer/Disclaimer.lean:394-395
theorem licences_exact (k : MapKind) (o : Orient) (c : Cls) :
    (TruthLicensed c k o ↔ c ∈ truthList k o) ∧ (FalsityLicensed c k o ↔ c ∈ falsityList k o) := …
```

**Hypotheses.**

None (the statement has no hypotheses).

**Depth.** shallow.

**Non-vacuity.** `truthLicensed_examples` and `falsityLicensed_examples` exhibit a licensed and an unlicensed entry of each list. (`truthLicensed_examples`, `falsityLicensed_examples`)

**Prior art.**

- W. Hodges, Model Theory, Cambridge University Press 1993 (Encyclopedia of Mathematics and its Applications 42), DOI 10.1017/CBO9780511551574 (bibliographic data verified via Crossref), checked in the publisher's reading sample: §1.2 (an embedding is an injective homomorphism with ā ∈ R^A ⇔ fā ∈ R^B), §2.4 'Maps and the formulas they preserve' (∀1 and ∃1 formulas, not required to be prenex), Theorem 2.4.1 (∃1 formulas are preserved by embeddings), Corollary 2.4.2(a) (∀1 formulas are preserved in substructures), Theorem 2.4.3 ((a) positive existential formulas are preserved by homomorphisms; (b) positive formulas by surjective homomorphisms).
- B. Rossman, 'Homomorphism preservation theorems', J. ACM 55(3), Article 15, 15:1–15:53 (2008), DOI 10.1145/1379759.1379763 (author PDF checked): Theorem 1.1 (Łoś–Tarski: preservation under embeddings iff equivalent to an existential formula; footnote 1: an embedding is an isomorphism onto an induced substructure, and the dual form is preservation under induced substructures iff universal), Theorem 1.2 (Lyndon's positivity theorem: surjective homomorphisms, positive formulas), Theorem 1.3 (homomorphism preservation theorem: homomorphisms, existential-positive formulas), Theorems 1.4 and 1.5 (Łoś–Tarski and Lyndon fail over finite structures; p. 3 attributes 1.4 to Tait 1959 and Gurevich–Shelah via Gurevich 1984, and 1.5 to Ajtai–Gurevich 1987 and Stolboushkin 1995), Theorem 1.7 (finite homomorphism preservation for sentences), Lemma 2.3 (the easy direction), §2.1.1 (structures have non-empty universes; substructure versus induced substructure), Remark 2.1 (formulas are not required to be prenex).

**Design question.** For each proved map between model and system, which model-side truths and which model-side falsities may be asserted of the system?

Basis: execution (Lean kernel check) for every statement quoted in this card, each a theorem checked by the Lean kernel with the axioms recorded under **Evidence**.

Basis: derived (modeling bridge) for the reading of this card in terms of real models and systems. Reading the two structures as a model and a system is an interpretation, not part of the theorem. The theorem applies to a real model–system pair once both are represented as `Str` values (one binary relation, one unary predicate, equality), the stated map laws are proved for a map between the two representations, and the claim is written as a formula of the stated class; this package carries out none of these steps for any real pair.

**Non-claims.** See **Boundaries → Non-claims → 20.** Read them together with the plain claim.

### Auxiliary statements cited by name

Every package declaration that is named above, or that occurs in a quoted statement, and is not quoted in a card or in the definitions is quoted here.

#### `sat_pos_example`

```lean
-- ToyTransfer/Examples.lean:37
theorem sat_pos_example : Sat S2Cyc.toStr allExR Fin.elim0 := …
```

#### `sat_neg_example`

```lean
-- ToyTransfer/Examples.lean:38
theorem sat_neg_example : ¬ Sat S1N.toStr allExR Fin.elim0 := …
```

#### `satS_pos_example`

```lean
-- ToyTransfer/Examples.lean:39
theorem satS_pos_example : SatS S1P.toStr allP := …
```

#### `satS_neg_example`

```lean
-- ToyTransfer/Examples.lean:40
theorem satS_neg_example : ¬ SatS S2PN.toStr allP := …
```

#### `env_cons_example`

```lean
-- ToyTransfer/Examples.lean:34
theorem env_cons_example : Env.cons (5 : Nat) (env1 7) 0 = 5 ∧ Env.cons (5 : Nat) (env1 7) 1 = 7 := …
```

#### `emptyStr_example`

```lean
-- ToyTransfer/Examples.lean:19
theorem emptyStr_example : SatS emptyStr allP ∧ ¬ SatS emptyStr exP := …
```

#### `exSelfEq_valid_iff_nonempty_carriers`

```lean
-- ToyTransfer/Examples.lean:30-31
theorem exSelfEq_valid_iff_nonempty_carriers :
    ¬ ValidIn (fun _ => True) exSelfEq ∧ ValidIn (fun M => Nonempty M.carrier) exSelfEq := …
```

#### `isQF_examples`

```lean
-- ToyTransfer/Examples.lean:47
theorem isQF_examples : IsQF notP0 ∧ ¬ IsQF allP ∧ ¬ IsQF exP := …
```

#### `isEqFree_examples`

```lean
-- ToyTransfer/Examples.lean:78
theorem isEqFree_examples : IsEqFree notP0 ∧ IsEqFree allP ∧ ¬ IsEqFree neq01 := …
```

#### `isUniv_examples`

```lean
-- ToyTransfer/Examples.lean:48
theorem isUniv_examples : IsUniv allRImpEq ∧ ¬ IsUniv exP ∧ ¬ IsUniv allExR := …
```

#### `isExist_examples`

```lean
-- ToyTransfer/Examples.lean:49-50
theorem isExist_examples :
    IsExist exExNeq ∧ ¬ IsExist allP ∧ ¬ IsExist exAllR ∧ ¬ IsExist exPAndExP := …
```

#### `isAE_examples`

```lean
-- ToyTransfer/Examples.lean:51
theorem isAE_examples : IsAE allExR ∧ ¬ IsAE exAllR := …
```

#### `isEA_examples`

```lean
-- ToyTransfer/Examples.lean:52
theorem isEA_examples : IsEA exAllR ∧ ¬ IsEA allExR := …
```

#### `isPos_examples`

```lean
-- ToyTransfer/Examples.lean:53
theorem isPos_examples : IsPos allExR ∧ ¬ IsPos exNotP := …
```

#### `isPosExist_examples`

```lean
-- ToyTransfer/Examples.lean:54-55
theorem isPosExist_examples :
    IsPosExist exP ∧ IsPosExist exPAndExP ∧ ¬ IsPosExist allP ∧ ¬ IsPosExist exNotP := …
```

#### `posExist_not_subset_exist`

```lean
-- ToyTransfer/Examples.lean:61-62
theorem posExist_not_subset_exist :
    IsPosExist exPAndExP ∧ ¬ IsExist exPAndExP ∧ ¬ IsAE exPAndExP ∧ ¬ IsEA exPAndExP := …
```

#### `no_qf_sentences`

```lean
-- ToyTransfer/Basic.lean:90
theorem no_qf_sentences : ∀ φ : Fml 0, ¬ IsQF φ := …
```

#### `preservesR_examples`

```lean
-- ToyTransfer/Examples.lean:83
theorem preservesR_examples : PreservesR inclCyc ∧ ¬ PreservesR lowerR := …
```

#### `preservesP_examples`

```lean
-- ToyTransfer/Examples.lean:84
theorem preservesP_examples : PreservesP raiseP ∧ ¬ PreservesP lowerP := …
```

#### `reflectsR_examples`

```lean
-- ToyTransfer/Examples.lean:85
theorem reflectsR_examples : ReflectsR inclCyc ∧ ¬ ReflectsR raiseR := …
```

#### `reflectsP_examples`

```lean
-- ToyTransfer/Examples.lean:86
theorem reflectsP_examples : ReflectsP inclPN ∧ ¬ ReflectsP raiseP := …
```

#### `isHom_examples`

```lean
-- ToyTransfer/Examples.lean:87
theorem isHom_examples : IsHom squashP ∧ ¬ IsHom lowerP := …
```

#### `isStrongHom_examples`

```lean
-- ToyTransfer/Examples.lean:88
theorem isStrongHom_examples : IsStrongHom collapse ∧ ¬ IsStrongHom raiseP := …
```

#### `isEmbedding_examples`

```lean
-- ToyTransfer/Examples.lean:89
theorem isEmbedding_examples : IsEmbedding inclCyc ∧ ¬ IsEmbedding collapse := …
```

#### `isSurjHom_examples`

```lean
-- ToyTransfer/Examples.lean:90
theorem isSurjHom_examples : IsSurjHom squashP ∧ ¬ IsSurjHom inclPN := …
```

#### `isIso_examples`

```lean
-- ToyTransfer/Examples.lean:91-93
theorem isIso_examples :
    IsIso (A := S1P.toStr) (B := S1P.toStr) id ∧ ¬ IsIso raiseP ∧ ¬ IsIso inclPN ∧
    ¬ IsIso collapse := …
```

#### `mapKind_holds_examples`

```lean
-- ToyTransfer/Examples.lean:94
theorem mapKind_holds_examples : MapKind.Holds .strong collapse ∧ ¬ MapKind.Holds .emb collapse := …
```

#### `injective_hom_not_embedding_example`

```lean
-- ToyTransfer/Examples.lean:99-100
theorem injective_hom_not_embedding_example :
    IsHom raiseR ∧ Function.Injective raiseR ∧ ¬ IsEmbedding raiseR := …
```

#### `MapKind.holds_id`

```lean
-- ToyTransfer/Maps.lean:107
theorem MapKind.holds_id (k : MapKind) (A : Str) : k.Holds (A := A) (B := A) id := …
```

#### `dir_transfer_examples`

```lean
-- ToyTransfer/Examples.lean:109
theorem dir_transfer_examples : Dir.Transfer .bwd True False ∧ ¬ Dir.Transfer .fwd True False := …
```

#### `cls_test_examples`

```lean
-- ToyTransfer/Examples.lean:56
theorem cls_test_examples : Cls.test .ae allExR = true ∧ Cls.test .univ allExR = false := …
```

#### `preserves_examples`

```lean
-- ToyTransfer/Examples.lean:114
theorem preserves_examples : Preserves .posExist .hom .fwd ∧ ¬ Preserves .univ .emb .fwd := …
```

#### `preservesSent_examples`

```lean
-- ToyTransfer/Examples.lean:117
theorem preservesSent_examples : PreservesSent .posExist .hom .fwd ∧ ¬ PreservesSent .univ .emb .fwd := …
```

#### `Cls.test_iff`

```lean
-- ToyTransfer/Maps.lean:158
theorem Cls.test_iff (c : Cls) {n : Nat} (φ : Fml n) : c.test φ = true ↔ c.Mem φ := …
```

#### `Preserves.toSent`

```lean
-- ToyTransfer/Maps.lean:187-188
theorem Preserves.toSent {c : Cls} {k : MapKind} {d : Dir} (hp : Preserves c k d) :
    PreservesSent c k d := …
```

#### `licensedB_examples`

```lean
-- ToyTransfer/Examples.lean:120
theorem licensedB_examples : licensedB .univ .emb .bwd = true ∧ licensedB .univ .emb .fwd = false := …
```

#### `licensedForB_examples`

```lean
-- ToyTransfer/Examples.lean:123
theorem licensedForB_examples : licensedForB exP .emb .fwd = true ∧ licensedForB allP .emb .fwd = false := …
```

#### `reach_examples`

```lean
-- ToyTransfer/Examples.lean:247
theorem reach_examples : Reach tsTwoStep true ∧ ¬ Reach tsBoolHalt true := …
```

#### `star_examples`

```lean
-- ToyTransfer/Examples.lean:250
theorem star_examples : Star tsTwoStep.step false true ∧ ¬ Star tsBoolHalt.step false true := …
```

#### `simInit_examples`

```lean
-- ToyTransfer/Examples.lean:259-260
theorem simInit_examples :
    SimInit tsTwoStep tsTwoStep (fun c a => c = a) ∧ ¬ SimInit tsHalt tsHalt (fun _ _ => False) := …
```

#### `simStepStar_examples`

```lean
-- ToyTransfer/Examples.lean:263-265
theorem simStepStar_examples :
    SimStepStar tsLoop tsHalt (fun _ _ => True) ∧
    ¬ SimStepStar tsTwoStep tsHalt (fun c _ => c = false) := …
```

#### `simStepLock_examples`

```lean
-- ToyTransfer/Examples.lean:270-272
theorem simStepLock_examples :
    SimStepLock tsTwoStep tsTwoStep (fun c a => c = a) ∧
    ¬ SimStepLock tsLoop tsHalt (fun _ _ => True) := …
```

#### `simStepStutter_examples`

```lean
-- ToyTransfer/Examples.lean:275-277
theorem simStepStutter_examples :
    SimStepStutter tsLoop tsHalt (fun _ _ => True) ∧
    ¬ SimStepStutter tsTwoStep tsBoolHalt (fun c a => c = a) := …
```

#### `simStepWF_examples`

```lean
-- ToyTransfer/Examples.lean:283-286
theorem simStepWF_examples :
    SimStepWF tsTwoStep tsBoolHalt (fun _ a => a = false) (· < ·)
      (fun (c : Bool) (_ : Bool) => if c then 0 else 1) ∧
    ¬ SimStepWF tsLoop tsHalt (fun _ _ => True) (fun (x y : Nat) => x < y) (fun _ _ => 0) := …
```

#### `terminates_examples`

```lean
-- ToyTransfer/Examples.lean:292
theorem terminates_examples : Terminates tsHalt () ∧ ¬ Terminates tsLoop () := …
```

#### `allRunsFinite_examples`

```lean
-- ToyTransfer/Examples.lean:295
theorem allRunsFinite_examples : AllRunsFinite tsTwoStep ∧ ¬ AllRunsFinite tsLoop := …
```

#### `weaklyTerminates_examples`

```lean
-- ToyTransfer/Examples.lean:298
theorem weaklyTerminates_examples : WeaklyTerminates tsHalt () ∧ ¬ WeaklyTerminates tsLoop () := …
```

#### `SimStepLock.toStar`

```lean
-- ToyTransfer/Simulation.lean:64-65
theorem SimStepLock.toStar {C A : TS} {S : C.St → A.St → Prop} (hs : SimStepLock C A S) :
    SimStepStar C A S := …
```

#### `SimStepStutter.toStar`

```lean
-- ToyTransfer/Simulation.lean:69-70
theorem SimStepStutter.toStar {C A : TS} {S : C.St → A.St → Prop} (hs : SimStepStutter C A S) :
    SimStepStar C A S := …
```

#### `SimStepWF.toStutter`

```lean
-- ToyTransfer/Simulation.lean:75-77
theorem SimStepWF.toStutter {C A : TS} {S : C.St → A.St → Prop} {W : Type}
    {lt : W → W → Prop} {μ : C.St → A.St → W} (hs : SimStepWF C A S lt μ) :
    SimStepStutter C A S := …
```

#### `Terminates.no_infinite_run`

```lean
-- ToyTransfer/Simulation.lean:91-92
theorem Terminates.no_infinite_run {T : TS} {s : T.St} (hs : Terminates T s) :
    ¬ ∃ f : Nat → T.St, f 0 = s ∧ ∀ i, T.step (f i) (f (i + 1)) := …
```

#### `terminates_iff_no_infinite_run`

```lean
-- ToyTransfer/Simulation.lean:106-107
theorem terminates_iff_no_infinite_run (T : TS) (s : T.St) :
    Terminates T s ↔ ¬ ∃ f : Nat → T.St, f 0 = s ∧ ∀ i, T.step (f i) (f (i + 1)) := …
```

#### `validIn_examples`

```lean
-- ToyTransfer/Examples.lean:142
theorem validIn_examples : ValidIn (fun _ => True) exclMid ∧ ¬ ValidIn (fun _ => True) exP := …
```

#### `unsatIn_examples`

```lean
-- ToyTransfer/Examples.lean:145
theorem unsatIn_examples : UnsatIn (fun _ => True) contra ∧ ¬ UnsatIn (fun _ => True) exP := …
```

#### `bothOutcomesNonIso_examples`

```lean
-- ToyTransfer/Examples.lean:126-127
theorem bothOutcomesNonIso_examples :
    BothOutcomesNonIso .univ .emb .fwd ∧ ¬ BothOutcomesNonIso .univ .emb .bwd := …
```

#### `truthLicensed_examples`

```lean
-- ToyTransfer/Examples.lean:148-149
theorem truthLicensed_examples :
    TruthLicensed .exist .emb .modelToSystem ∧ ¬ TruthLicensed .univ .emb .modelToSystem := …
```

#### `falsityLicensed_examples`

```lean
-- ToyTransfer/Examples.lean:153-154
theorem falsityLicensed_examples :
    FalsityLicensed .univ .emb .modelToSystem ∧ ¬ FalsityLicensed .exist .emb .modelToSystem := …
```

#### `licensed_cells_nonvacuous`

```lean
-- ToyTransfer/Examples.lean:328-339
theorem licensed_cells_nonvacuous :
    (Cls.Mem .qf notP0 ∧ MapKind.Holds .emb inclNP ∧ Sat S1N.toStr notP0 (env1 0)) ∧
    (Cls.Mem .qf notP0 ∧ MapKind.Holds .emb inclNP ∧ Sat S2NP.toStr notP0 (inclNP ∘ env1 0)) ∧
    (Cls.Mem .univ allNotRxx ∧ MapKind.Holds .emb inclCyc ∧
      Sat S2Cyc.toStr allNotRxx (inclCyc ∘ Fin.elim0)) ∧
    (Cls.Mem .exist exP ∧ MapKind.Holds .emb inclPN ∧ Sat S1P.toStr exP Fin.elim0) ∧
    (Cls.Mem .posExist exP ∧ MapKind.Holds .hom squashP ∧ Sat S2NP.toStr exP Fin.elim0) ∧
    (Cls.Mem .posExist exSelfEq ∧ MapKind.Holds .strong collapse ∧
      Sat S2E.toStr exSelfEq Fin.elim0) ∧
    (Cls.Mem .posExist exP ∧ MapKind.Holds .emb inclPN ∧ Sat S1P.toStr exP Fin.elim0) ∧
    (Cls.Mem .posExist exP ∧ MapKind.Holds .surj squashP ∧ Sat S2NP.toStr exP Fin.elim0) ∧
    (Cls.Mem .pos allExP ∧ MapKind.Holds .surj squashP ∧ Sat S2NP.toStr allExP Fin.elim0) := …
```

#### `notP0_not_preserved_by_surjHom`

```lean
-- ToyTransfer/Countermodels.lean:63-65
theorem notP0_not_preserved_by_surjHom :
    IsQF notP0 ∧ IsSurjHom raiseP ∧ Function.Injective raiseP ∧
    Sat S1N.toStr notP0 (env1 0) ∧ ¬ Sat S1P.toStr notP0 (raiseP ∘ env1 0) := …
```

#### `P0_not_reflected_by_surjHom`

```lean
-- ToyTransfer/Countermodels.lean:99-102
theorem P0_not_reflected_by_surjHom :
    IsQF P0 ∧ IsUniv P0 ∧ IsExist P0 ∧ IsAE P0 ∧ IsEA P0 ∧ IsPos P0 ∧ IsPosExist P0 ∧
    IsSurjHom raiseP ∧ Function.Injective raiseP ∧
    Sat S1P.toStr P0 (raiseP ∘ env1 0) ∧ ¬ Sat S1N.toStr P0 (env1 0) := …
```

#### `neq_not_preserved_by_strongHom`

```lean
-- ToyTransfer/Countermodels.lean:70-73
theorem neq_not_preserved_by_strongHom :
    IsQF neq01 ∧ IsStrongHom collapse ∧ Function.Surjective collapse ∧
    ¬ Function.Injective collapse ∧
    Sat S2E.toStr neq01 (env2 0 1) ∧ ¬ Sat S1N.toStr neq01 (collapse ∘ env2 0 1) := …
```

#### `eq_not_reflected_by_strongHom`

```lean
-- ToyTransfer/Countermodels.lean:84-87
theorem eq_not_reflected_by_strongHom :
    IsQF eq01 ∧ IsPos eq01 ∧ IsPosExist eq01 ∧
    IsStrongHom collapse ∧ Function.Surjective collapse ∧ ¬ Function.Injective collapse ∧
    Sat S1N.toStr eq01 (collapse ∘ env2 0 1) ∧ ¬ Sat S2E.toStr eq01 (env2 0 1) := …
```

#### `preserves_qf_emb`

```lean
-- ToyTransfer/Matrix.lean:27
theorem preserves_qf_emb (d : Dir) : Preserves .qf .emb d := …
```

#### `allAllEq_not_reflected_by_strongHom`

```lean
-- ToyTransfer/Countermodels.lean:91-94
theorem allAllEq_not_reflected_by_strongHom :
    IsUniv allAllEq ∧ IsAE allAllEq ∧ IsEA allAllEq ∧ IsPos allAllEq ∧
    IsStrongHom collapse ∧ Function.Surjective collapse ∧ ¬ Function.Injective collapse ∧
    Sat S1N.toStr allAllEq (collapse ∘ Fin.elim0) ∧ ¬ Sat S2E.toStr allAllEq Fin.elim0 := …
```

#### `preserves_univ_emb_bwd`

```lean
-- ToyTransfer/Matrix.lean:34
theorem preserves_univ_emb_bwd : Preserves .univ .emb .bwd := …
```

#### `allP_not_reflected_by_surjHom`

```lean
-- ToyTransfer/Countermodels.lean:114-118
theorem allP_not_reflected_by_surjHom :
    IsUniv allP ∧ IsAE allP ∧ IsEA allP ∧ IsPos allP ∧
    IsSurjHom raiseP ∧ Function.Injective raiseP ∧
    PreservesR raiseP ∧ PreservesP raiseP ∧ ReflectsR raiseP ∧ ¬ ReflectsP raiseP ∧
    Sat S1P.toStr allP (raiseP ∘ Fin.elim0) ∧ ¬ Sat S1N.toStr allP Fin.elim0 := …
```

#### `exExNeq_not_preserved_by_strongHom`

```lean
-- ToyTransfer/Countermodels.lean:77-80
theorem exExNeq_not_preserved_by_strongHom :
    IsExist exExNeq ∧ IsAE exExNeq ∧ IsEA exExNeq ∧
    IsStrongHom collapse ∧ Function.Surjective collapse ∧ ¬ Function.Injective collapse ∧
    Sat S2E.toStr exExNeq Fin.elim0 ∧ ¬ Sat S1N.toStr exExNeq (collapse ∘ Fin.elim0) := …
```

#### `preserves_exist_emb_fwd`

```lean
-- ToyTransfer/Matrix.lean:38
theorem preserves_exist_emb_fwd : Preserves .exist .emb .fwd := …
```

#### `exP_not_reflected_by_surjHom`

```lean
-- ToyTransfer/Countermodels.lean:106-109
theorem exP_not_reflected_by_surjHom :
    IsExist exP ∧ IsAE exP ∧ IsEA exP ∧ IsPos exP ∧ IsPosExist exP ∧
    IsSurjHom raiseP ∧ Function.Injective raiseP ∧
    Sat S1P.toStr exP (raiseP ∘ Fin.elim0) ∧ ¬ Sat S1N.toStr exP Fin.elim0 := …
```

#### `preserves_pos_surj_fwd`

```lean
-- ToyTransfer/Matrix.lean:46
theorem preserves_pos_surj_fwd : Preserves .pos .surj .fwd := …
```

#### `preserves_posExist_fwd`

```lean
-- ToyTransfer/Matrix.lean:42
theorem preserves_posExist_fwd (k : MapKind) : Preserves .posExist k .fwd := …
```

#### `IsEmbedding.toStrongHom`

```lean
-- ToyTransfer/Maps.lean:69-70
theorem IsEmbedding.toStrongHom {h : A.carrier → B.carrier} (hh : IsEmbedding h) :
    IsStrongHom h := …
```

#### `IsStrongHom.toHom`

```lean
-- ToyTransfer/Maps.lean:72
theorem IsStrongHom.toHom {h : A.carrier → B.carrier} (hh : IsStrongHom h) : IsHom h := …
```

#### `IsSurjHom.toHom`

```lean
-- ToyTransfer/Maps.lean:78
theorem IsSurjHom.toHom {h : A.carrier → B.carrier} (hh : IsSurjHom h) : IsHom h := …
```

#### `bothOutcomesNonIso_of_unlicensed`

```lean
-- ToyTransfer/Disclaimer.lean:240-241
theorem bothOutcomesNonIso_of_unlicensed : ∀ (c : Cls) (k : MapKind) (d : Dir),
    licensedB c k d = false → BothOutcomesNonIso c k d := …
```

#### `both_eq`

```lean
-- ToyTransfer/Disclaimer.lean:204-205
theorem both_eq {c : Cls} {k : MapKind} (hc : c.Mem eq01) (hk₁ : k.Holds collapse)
    (hk₂ : k.Holds collapse) : BothOutcomesNonIso c k .bwd := …
```

#### `both_notP0`

```lean
-- ToyTransfer/Disclaimer.lean:169-170
theorem both_notP0 {c : Cls} {k : MapKind} (hc : c.Mem notP0) (hk₁ : k.Holds raiseR)
    (hk₂ : k.Holds raiseP) : BothOutcomesNonIso c k .fwd := …
```

#### `both_P0`

```lean
-- ToyTransfer/Disclaimer.lean:219-220
theorem both_P0 {c : Cls} {k : MapKind} (hc : c.Mem P0) (hk₁ : k.Holds squashP)
    (hk₂ : k.Holds raiseP) : BothOutcomesNonIso c k .bwd := …
```

#### `both_neq`

```lean
-- ToyTransfer/Disclaimer.lean:176-177
theorem both_neq {c : Cls} {k : MapKind} (hc : c.Mem neq01) (hk₁ : k.Holds inclE23)
    (hk₂ : k.Holds collapse) : BothOutcomesNonIso c k .fwd := …
```

#### `both_allP`

```lean
-- ToyTransfer/Disclaimer.lean:149-150
theorem both_allP {c : Cls} {k : MapKind} (hc : c.Mem allP) (hk₁ : k.Holds inclPP)
    (hk₂ : k.Holds inclPN) : BothOutcomesNonIso c k .fwd := …
```

#### `both_atMostOneNotP`

```lean
-- ToyTransfer/Disclaimer.lean:212-213
theorem both_atMostOneNotP {c : Cls} {k : MapKind} (hc : c.Mem atMostOneNotP)
    (hk₁ : k.Holds inclN1) (hk₂ : k.Holds collapseTo1) : BothOutcomesNonIso c k .bwd := …
```

#### `both_allRImpEq`

```lean
-- ToyTransfer/Disclaimer.lean:163-164
theorem both_allRImpEq {c : Cls} {k : MapKind} (hc : c.Mem allRImpEq) (hk₁ : k.Holds collapse)
    (hk₂ : k.Holds addEdge) : BothOutcomesNonIso c k .fwd := …
```

#### `both_allP_surj`

```lean
-- ToyTransfer/Disclaimer.lean:234-235
theorem both_allP_surj {c : Cls} {k : MapKind} (hc : c.Mem allP) (hk₁ : k.Holds squashPP)
    (hk₂ : k.Holds raiseP) : BothOutcomesNonIso c k .bwd := …
```

#### `both_exNotP`

```lean
-- ToyTransfer/Disclaimer.lean:156-157
theorem both_exNotP {c : Cls} {k : MapKind} (hc : c.Mem exNotP) (hk₁ : k.Holds raiseR)
    (hk₂ : k.Holds raiseP) : BothOutcomesNonIso c k .fwd := …
```

#### `both_exP_sub`

```lean
-- ToyTransfer/Disclaimer.lean:189-190
theorem both_exP_sub {c : Cls} {k : MapKind} (hc : c.Mem exP) (hk₁ : k.Holds inclP1)
    (hk₂ : k.Holds inclNP) : BothOutcomesNonIso c k .bwd := …
```

#### `both_exExNeq`

```lean
-- ToyTransfer/Disclaimer.lean:182-183
theorem both_exExNeq {c : Cls} {k : MapKind} (hc : c.Mem exExNeq) (hk₁ : k.Holds inclE23)
    (hk₂ : k.Holds collapse) : BothOutcomesNonIso c k .fwd := …
```

#### `both_exP_surj`

```lean
-- ToyTransfer/Disclaimer.lean:227-228
theorem both_exP_surj {c : Cls} {k : MapKind} (hc : c.Mem exP) (hk₁ : k.Holds squashP)
    (hk₂ : k.Holds raiseP) : BothOutcomesNonIso c k .bwd := …
```

#### `both_allExR`

```lean
-- ToyTransfer/Disclaimer.lean:196-197
theorem both_allExR {c : Cls} {k : MapKind} (hc : c.Mem allExR) (hk₁ : k.Holds inclLoop)
    (hk₂ : k.Holds inclNoLoop) : BothOutcomesNonIso c k .bwd := …
```

#### `allNotRxx_reflection_fails_without_presR`

```lean
-- ToyTransfer/Countermodels.lean:125-128
theorem allNotRxx_reflection_fails_without_presR :
    IsUniv allNotRxx ∧ Function.Injective lowerR ∧ Function.Surjective lowerR ∧
    ¬ PreservesR lowerR ∧ PreservesP lowerR ∧ ReflectsR lowerR ∧ ReflectsP lowerR ∧
    Sat S1N.toStr allNotRxx (lowerR ∘ Fin.elim0) ∧ ¬ Sat S1R.toStr allNotRxx Fin.elim0 := …
```

#### `allNotP_reflection_fails_without_presP`

```lean
-- ToyTransfer/Countermodels.lean:132-135
theorem allNotP_reflection_fails_without_presP :
    IsUniv allNotP ∧ Function.Injective lowerP ∧ Function.Surjective lowerP ∧
    PreservesR lowerP ∧ ¬ PreservesP lowerP ∧ ReflectsR lowerP ∧ ReflectsP lowerP ∧
    Sat S1N.toStr allNotP (lowerP ∘ Fin.elim0) ∧ ¬ Sat S1P.toStr allNotP Fin.elim0 := …
```

#### `allRxx_reflection_fails_without_reflR`

```lean
-- ToyTransfer/Countermodels.lean:139-142
theorem allRxx_reflection_fails_without_reflR :
    IsUniv allRxx ∧ IsPos allRxx ∧ Function.Injective raiseR ∧ Function.Surjective raiseR ∧
    PreservesR raiseR ∧ PreservesP raiseR ∧ ¬ ReflectsR raiseR ∧ ReflectsP raiseR ∧
    Sat S1R.toStr allRxx (raiseR ∘ Fin.elim0) ∧ ¬ Sat S1N.toStr allRxx Fin.elim0 := …
```

#### `univ_preserved_to_substructure_nonvacuous`

```lean
-- ToyTransfer/Countermodels.lean:182-183
theorem univ_preserved_to_substructure_nonvacuous :
    IsUniv allNotRxx ∧ IsEmbedding inclCyc ∧ Sat S2Cyc.toStr allNotRxx (inclCyc ∘ Fin.elim0) := …
```

#### `exRxx_transfer_fails_without_presR`

```lean
-- ToyTransfer/Countermodels.lean:148-152
theorem exRxx_transfer_fails_without_presR :
    IsExist exRxx ∧ IsPosExist exRxx ∧ IsPos exRxx ∧
    Function.Injective lowerR ∧ Function.Surjective lowerR ∧
    ¬ PreservesR lowerR ∧ PreservesP lowerR ∧ ReflectsR lowerR ∧ ReflectsP lowerR ∧
    Sat S1R.toStr exRxx Fin.elim0 ∧ ¬ Sat S1N.toStr exRxx (lowerR ∘ Fin.elim0) := …
```

#### `exP_transfer_fails_without_presP`

```lean
-- ToyTransfer/Countermodels.lean:157-161
theorem exP_transfer_fails_without_presP :
    IsExist exP ∧ IsPosExist exP ∧ IsPos exP ∧
    Function.Injective lowerP ∧ Function.Surjective lowerP ∧
    PreservesR lowerP ∧ ¬ PreservesP lowerP ∧ ReflectsR lowerP ∧ ReflectsP lowerP ∧
    Sat S1P.toStr exP Fin.elim0 ∧ ¬ Sat S1N.toStr exP (lowerP ∘ Fin.elim0) := …
```

#### `exNotRxx_transfer_fails_without_reflR`

```lean
-- ToyTransfer/Countermodels.lean:165-168
theorem exNotRxx_transfer_fails_without_reflR :
    IsExist exNotRxx ∧ Function.Injective raiseR ∧ Function.Surjective raiseR ∧
    PreservesR raiseR ∧ PreservesP raiseR ∧ ¬ ReflectsR raiseR ∧ ReflectsP raiseR ∧
    Sat S1N.toStr exNotRxx Fin.elim0 ∧ ¬ Sat S1R.toStr exNotRxx (raiseR ∘ Fin.elim0) := …
```

#### `exist_preserved_to_extension_nonvacuous`

```lean
-- ToyTransfer/Countermodels.lean:187-188
theorem exist_preserved_to_extension_nonvacuous :
    IsExist exP ∧ IsEmbedding inclPN ∧ Sat S1P.toStr exP Fin.elim0 := …
```

#### `posExist_preserved_forward_nonvacuous`

```lean
-- ToyTransfer/Countermodels.lean:193-195
theorem posExist_preserved_forward_nonvacuous :
    IsPosExist exP ∧ PreservesR squashP ∧ PreservesP squashP ∧
    ¬ Function.Injective squashP ∧ ¬ ReflectsP squashP ∧ Sat S2NP.toStr exP Fin.elim0 := …
```

#### `pos_holds_in_full_one_point`

```lean
-- ToyTransfer/Examples.lean:67-68
theorem pos_holds_in_full_one_point {n : Nat} {φ : Fml n} (hφ : IsPos φ)
    (e : Fin n → S1Full.toStr.carrier) : Sat S1Full.toStr φ e := …
```

#### `pos_preserved_forward_nonvacuous`

```lean
-- ToyTransfer/Countermodels.lean:199-201
theorem pos_preserved_forward_nonvacuous :
    IsPos allExP ∧ ¬ IsPosExist allExP ∧ Function.Surjective squashP ∧ PreservesR squashP ∧
    PreservesP squashP ∧ ¬ ReflectsP squashP ∧ Sat S2NP.toStr allExP Fin.elim0 := …
```

#### `transfer_of_licensedForB_needs_licence`

```lean
-- ToyTransfer/Matrix.lean:307-309
theorem transfer_of_licensedForB_needs_licence :
    licensedForB allP .emb .fwd = false ∧ MapKind.Holds .emb inclPN ∧
    Sat S1P.toStr allP Fin.elim0 ∧ ¬ Sat S2PN.toStr allP (inclPN ∘ Fin.elim0) := …
```

#### `licensedB_iff_preservesSent_needs_ne_qf`

```lean
-- ToyTransfer/Matrix.lean:273-274
theorem licensedB_iff_preservesSent_needs_ne_qf :
    licensedB .qf .hom .fwd = false ∧ PreservesSent .qf .hom .fwd := …
```

#### `transfer_of_licensedForB_nonvacuous`

```lean
-- ToyTransfer/Matrix.lean:299-301
theorem transfer_of_licensedForB_nonvacuous :
    licensedForB exP .emb .fwd = true ∧ MapKind.Holds .emb inclPN ∧
    Sat S1P.toStr exP Fin.elim0 := …
```

#### `licensedForB_incomplete`

```lean
-- ToyTransfer/Matrix.lean:319-322
theorem licensedForB_incomplete :
    licensedForB exclMid .hom .fwd = false ∧
    ∀ (A B : Str) (h : A.carrier → B.carrier), IsHom h →
      Sat A exclMid Fin.elim0 → Sat B exclMid (h ∘ Fin.elim0) := …
```

#### `preservesSent_qf`

```lean
-- ToyTransfer/Matrix.lean:267
theorem preservesSent_qf (k : MapKind) (d : Dir) : PreservesSent .qf k d := …
```

#### `qf_sat_iff_of_strongHom_of_eqFree`

```lean
-- ToyTransfer/Preservation.lean:31-34
theorem qf_sat_iff_of_strongHom_of_eqFree (h : A.carrier → B.carrier)
    (hpR : PreservesR h) (hpP : PreservesP h) (hrR : ReflectsR h) (hrP : ReflectsP h)
    {n : Nat} {φ : Fml n} (hφ : IsQF φ) (hef : IsEqFree φ) (e : Fin n → A.carrier) :
    Sat A φ e ↔ Sat B φ (h ∘ e) := …
```

#### `model_embeds_into_system_nonvacuous`

```lean
-- ToyTransfer/Direction.lean:72-74
theorem model_embeds_into_system_nonvacuous :
    IsUniv allP ∧ IsEmbedding inclNP ∧ ¬ Sat S1N.toStr allP Fin.elim0 ∧
    IsExist exP ∧ IsEmbedding inclPN ∧ Sat S1P.toStr exP Fin.elim0 := …
```

#### `qf_sat_iff_of_embedding_laws`

```lean
-- ToyTransfer/Preservation.lean:16-20
theorem qf_sat_iff_of_embedding_laws (h : A.carrier → B.carrier)
    (hinj : Function.Injective h) (hpR : PreservesR h) (hpP : PreservesP h)
    (hrR : ReflectsR h) (hrP : ReflectsP h)
    {n : Nat} {φ : Fml n} (hφ : IsQF φ) (e : Fin n → A.carrier) :
    Sat A φ e ↔ Sat B φ (h ∘ e) := …
```

#### `allP_in_nonempty_model_gives_exP_in_system`

```lean
-- ToyTransfer/Direction.lean:64-66
theorem allP_in_nonempty_model_gives_exP_in_system {M S : Str} (m₀ : M.carrier)
    (h : M.carrier → S.carrier) (hemb : IsEmbedding h) :
    SatS M allP → SatS S exP := …
```

#### `forward_simulation_needs_init`

```lean
-- ToyTransfer/SimCountermodels.lean:84-92
theorem forward_simulation_needs_init :
    ¬ SimInit tsHalt tsHalt (fun _ _ => False) ∧
    SimStepStar tsHalt tsHalt (fun _ _ => False) ∧
    (∀ a, Reach tsHalt a → True) ∧
    (∀ (c a : Unit), (fun (_ _ : Unit) => False) c a → True → True) ∧
    Reach tsHalt () ∧
    ¬ (∃ a, (fun (_ _ : Unit) => False) () a ∧ Reach tsHalt a) ∧
    ¬ (∃ a, (fun (_ _ : Unit) => False) () a ∧ True) ∧
    ¬ (∃ a, (fun (_ _ : Unit) => False) () a ∧ Reach tsHalt a ∧ True) := …
```

#### `forward_simulation_needs_step_matching`

```lean
-- ToyTransfer/SimCountermodels.lean:100-108
theorem forward_simulation_needs_step_matching :
    SimInit tsTwoStep tsHalt (fun c _ => c = false) ∧
    ¬ SimStepStar tsTwoStep tsHalt (fun c _ => c = false) ∧
    (∀ a, Reach tsHalt a → True) ∧
    (∀ (c : Bool) (a : Unit), (fun (c : Bool) (_ : Unit) => c = false) c a → True → True) ∧
    Reach tsTwoStep true ∧
    ¬ (∃ a, (fun (c : Bool) (_ : Unit) => c = false) true a ∧ Reach tsHalt a) ∧
    ¬ (∃ a, (fun (c : Bool) (_ : Unit) => c = false) true a ∧ True) ∧
    ¬ (∃ a, (fun (c : Bool) (_ : Unit) => c = false) true a ∧ Reach tsHalt a ∧ True) := …
```

#### `forward_simulation_nonvacuous`

```lean
-- ToyTransfer/SimCountermodels.lean:143-147
theorem forward_simulation_nonvacuous :
    SimInit tsTwoStep tsBoolHalt (fun _ a => a = false) ∧
    SimStepStar tsTwoStep tsBoolHalt (fun _ a => a = false) ∧
    (∀ a, Reach tsBoolHalt a → a = false) ∧
    Reach tsTwoStep true := …
```

#### `invariant_transfer_needs_abstract_invariant`

```lean
-- ToyTransfer/SimCountermodels.lean:119-122
theorem invariant_transfer_needs_abstract_invariant :
    SimInit tsHalt tsHalt (fun _ _ => True) ∧ SimStepStar tsHalt tsHalt (fun _ _ => True) ∧
    ¬ (∀ a, Reach tsHalt a → False) ∧
    Reach tsHalt () ∧ ¬ (∃ a, (fun (_ _ : Unit) => True) () a ∧ False) := …
```

#### `strong_pullback_of_functional_simulation`

```lean
-- ToyTransfer/Simulation.lean:182-185
theorem strong_pullback_of_functional_simulation {C A : TS} {S : C.St → A.St → Prop}
    (hi : SimInit C A S) (hs : SimStepStar C A S) (hfun : ∀ c a a', S c a → S c a' → a = a')
    (I : A.St → Prop) (hI : ∀ a, Reach A a → I a) :
    ∀ c, Reach C c → ∀ a, S c a → I a := …
```

#### `reach_restricted_simulation_gives_strong_pullback`

```lean
-- ToyTransfer/Simulation.lean:194-199
theorem reach_restricted_simulation_gives_strong_pullback {C A : TS} {S : C.St → A.St → Prop}
    (hi : SimInit C A S) (hs : SimStepStar C A S) :
    SimInit C A (fun c a => S c a ∧ Reach A a) ∧
    SimStepStar C A (fun c a => S c a ∧ Reach A a) ∧
    ∀ (I : A.St → Prop), (∀ a, Reach A a → I a) →
      ∀ c, Reach C c → ∀ a, (S c a ∧ Reach A a) → I a := …
```

#### `functional_simulation_example`

```lean
-- ToyTransfer/Examples.lean:303-308
theorem functional_simulation_example :
    SimInit tsTwoStep tsBoolHalt (fun _ a => a = false) ∧
    SimStepStar tsTwoStep tsBoolHalt (fun _ a => a = false) ∧
    (∀ (c : Bool) (a a' : Bool), (fun (_ a : Bool) => a = false) c a →
      (fun (_ a : Bool) => a = false) c a' → a = a') ∧
    (∀ a, Reach tsBoolHalt a → a = false) := …
```

#### `reach_restriction_repairs_strong_pullback_countermodel`

```lean
-- ToyTransfer/Examples.lean:314-315
theorem reach_restriction_repairs_strong_pullback_countermodel :
    ∀ a, ((fun (_ : Unit) (_ : Bool) => True) () a ∧ Reach tsBoolHalt a) → a = false := …
```

#### `bug_transfer_needs_bad_compatibility`

```lean
-- ToyTransfer/SimCountermodels.lean:130-134
theorem bug_transfer_needs_bad_compatibility :
    SimInit tsHalt tsHalt (fun _ _ => True) ∧ SimStepStar tsHalt tsHalt (fun _ _ => True) ∧
    ¬ (∀ (c a : Unit), (fun (_ _ : Unit) => True) c a → True → False) ∧
    Reach tsHalt () ∧ True ∧
    ¬ (∃ a, (fun (_ _ : Unit) => True) () a ∧ Reach tsHalt a ∧ False) := …
```

#### `bug_transfer_up_nonvacuous`

```lean
-- ToyTransfer/SimCountermodels.lean:154-158
theorem bug_transfer_up_nonvacuous :
    SimInit tsTwoStep tsTwoStep (fun c a => c = a) ∧
    SimStepStar tsTwoStep tsTwoStep (fun c a => c = a) ∧
    (∀ (c a : Bool), c = a → c = true → a = true) ∧
    Reach tsTwoStep true ∧ tsTwoStep.init false ∧ ¬ (false = true) := …
```

#### `abstract_bug_transfer_without_converse_step_matching`

```lean
-- ToyTransfer/SimCountermodels.lean:243-249
theorem abstract_bug_transfer_without_converse_step_matching :
    SimInit tsLine2 tsBranch3 relSameIndex ∧ SimStepStar tsLine2 tsBranch3 relSameIndex ∧
    SimInit tsBranch3 tsLine2 (fun a c => relSameIndex c a) ∧
    (∀ (c : Fin 2) (a : Fin 3), relSameIndex c a → (a = 1 ↔ c = 1)) ∧
    (∀ a : Fin 3, Reach tsBranch3 a → a = 1 →
      ∃ c : Fin 2, relSameIndex c a ∧ Reach tsLine2 c ∧ c = 1) ∧
    ¬ SimStepStar tsBranch3 tsLine2 (fun a c => relSameIndex c a) := …
```

#### `converse_simulation_needs_init`

```lean
-- ToyTransfer/SimCountermodels.lean:198-203
theorem converse_simulation_needs_init :
    ¬ SimInit tsHalt tsHalt (fun (_ _ : Unit) => False) ∧
    SimStepStar tsHalt tsHalt (fun (_ _ : Unit) => False) ∧
    (∀ (c a : Unit), (fun (_ _ : Unit) => False) c a → True → True) ∧
    Reach tsHalt () ∧ True ∧
    ¬ (∃ c, (fun (_ _ : Unit) => False) c () ∧ Reach tsHalt c ∧ True) := …
```

#### `converse_simulation_needs_bad_compatibility`

```lean
-- ToyTransfer/SimCountermodels.lean:211-215
theorem converse_simulation_needs_bad_compatibility :
    SimInit tsHalt tsHalt (fun _ _ => True) ∧ SimStepStar tsHalt tsHalt (fun _ _ => True) ∧
    ¬ (∀ (c a : Unit), (fun (_ _ : Unit) => True) c a → True → False) ∧
    Reach tsHalt () ∧ True ∧
    ¬ (∃ c, (fun (_ _ : Unit) => True) c () ∧ Reach tsHalt c ∧ False) := …
```

#### `converse_simulation_nonvacuous`

```lean
-- ToyTransfer/SimCountermodels.lean:222-225
theorem converse_simulation_nonvacuous :
    SimInit tsTwoStep tsTwoStep (fun a c => c = a) ∧
    SimStepStar tsTwoStep tsTwoStep (fun a c => c = a) ∧
    (∀ (c a : Bool), c = a → a = true → c = true) ∧ Reach tsTwoStep true := …
```

#### `termination_transfer_needs_init`

```lean
-- ToyTransfer/SimCountermodels.lean:321-326
theorem termination_transfer_needs_init :
    ¬ SimInit tsLoop tsHalt (fun _ _ => False) ∧
    SimStepLock tsLoop tsHalt (fun _ _ => False) ∧
    SimStepWF tsLoop tsHalt (fun _ _ => False) (fun (_ _ : Unit) => False) (fun _ _ => ()) ∧
    WellFounded (fun (_ _ : Unit) => False) ∧
    AllRunsFinite tsHalt ∧ ¬ AllRunsFinite tsLoop := …
```

#### `termination_transfer_needs_abstract_termination`

```lean
-- ToyTransfer/SimCountermodels.lean:337-341
theorem termination_transfer_needs_abstract_termination :
    SimInit tsLoop tsLoop (fun _ _ => True) ∧ SimStepLock tsLoop tsLoop (fun _ _ => True) ∧
    SimStepWF tsLoop tsLoop (fun _ _ => True) (fun (_ _ : Unit) => False) (fun _ _ => ()) ∧
    WellFounded (fun (_ _ : Unit) => False) ∧
    ¬ AllRunsFinite tsLoop := …
```

#### `lockstep_nonvacuous`

```lean
-- ToyTransfer/SimCountermodels.lean:394-396
theorem lockstep_nonvacuous :
    SimInit tsTwoStep tsTwoStep (fun c a => c = a) ∧
    SimStepLock tsTwoStep tsTwoStep (fun c a => c = a) ∧ AllRunsFinite tsTwoStep := …
```

#### `lockstep_termination_transfer_is_about_reachable_states`

```lean
-- ToyTransfer/SimCountermodels.lean:301-304
theorem lockstep_termination_transfer_is_about_reachable_states :
    SimInit tsUnreachLoop tsHalt (fun c _ => c = false) ∧
    SimStepLock tsUnreachLoop tsHalt (fun c _ => c = false) ∧
    AllRunsFinite tsHalt ∧ AllRunsFinite tsUnreachLoop ∧ ¬ Terminates tsUnreachLoop true := …
```

#### `weak_termination_does_not_transfer_down_lockstep`

```lean
-- ToyTransfer/SimCountermodels.lean:424-430
theorem weak_termination_does_not_transfer_down_lockstep :
    SimInit tsLoop tsLoopOrHalt (fun _ a => a = false) ∧
    SimStepLock tsLoop tsLoopOrHalt (fun _ a => a = false) ∧
    SimStepWF tsLoop tsLoopOrHalt (fun _ a => a = false) (fun (_ _ : Unit) => False)
      (fun _ _ => ()) ∧
    (∀ a, Reach tsLoopOrHalt a → WeaklyTerminates tsLoopOrHalt a) ∧
    Reach tsLoop () ∧ ¬ WeaklyTerminates tsLoop () := …
```

#### `stuttering_countermodel_admits_no_wf_measure`

```lean
-- ToyTransfer/SimCountermodels.lean:383-385
theorem stuttering_countermodel_admits_no_wf_measure {W : Type} (lt : W → W → Prop)
    (hwf : WellFounded lt) (μ : tsLoop.St → tsHalt.St → W) :
    ¬ SimStepWF tsLoop tsHalt (fun _ _ => True) lt μ := …
```

#### `wf_simulation_needs_measure_decrease`

```lean
-- ToyTransfer/SimCountermodels.lean:364-368
theorem wf_simulation_needs_measure_decrease :
    SimInit tsLoop tsHalt (fun _ _ => True) ∧
    WellFounded (fun (_ _ : Unit) => False) ∧
    ¬ SimStepWF tsLoop tsHalt (fun _ _ => True) (fun (_ _ : Unit) => False) (fun _ _ => ()) ∧
    AllRunsFinite tsHalt ∧ ¬ AllRunsFinite tsLoop := …
```

#### `wf_simulation_needs_wellFounded`

```lean
-- ToyTransfer/SimCountermodels.lean:350-354
theorem wf_simulation_needs_wellFounded :
    SimInit tsLoop tsHalt (fun _ _ => True) ∧
    SimStepWF tsLoop tsHalt (fun _ _ => True) (fun (_ _ : Unit) => True) (fun _ _ => ()) ∧
    ¬ WellFounded (fun (_ _ : Unit) => True) ∧
    AllRunsFinite tsHalt ∧ ¬ AllRunsFinite tsLoop := …
```

#### `wf_simulation_nonvacuous`

```lean
-- ToyTransfer/SimCountermodels.lean:405-409
theorem wf_simulation_nonvacuous :
    SimInit tsTwoStep tsBoolHalt (fun _ a => a = false) ∧
    SimStepWF tsTwoStep tsBoolHalt (fun _ a => a = false) (· < ·)
      (fun (c : Bool) (_ : Bool) => if c then 0 else 1) ∧
    WellFounded (fun (x y : Nat) => x < y) ∧ AllRunsFinite tsBoolHalt := …
```

#### `consistent_with_both_needs_model_satisfiable`

```lean
-- ToyTransfer/Examples.lean:210-214
theorem consistent_with_both_needs_model_satisfiable :
    ¬ (∃ T, (fun M => ¬ SatS M exP) T ∧ SatS T exP) ∧
    (∃ R, (fun _ => True) R ∧ SatS R exP) ∧ (∃ R, (fun _ => True) R ∧ ¬ SatS R exP) ∧
    ¬ (∃ T, (fun M => ¬ SatS M exP) T ∧ SatS T exP ∧
      (∃ R, (fun _ => True) R ∧ SatS R exP) ∧ (∃ R, (fun _ => True) R ∧ ¬ SatS R exP)) := …
```

#### `consistent_with_both_needs_system_satisfiable`

```lean
-- ToyTransfer/Examples.lean:221-227
theorem consistent_with_both_needs_system_satisfiable :
    (∃ T, (fun _ => True) T ∧ SatS T exP) ∧
    ¬ (∃ R, (fun M => ¬ SatS M exP) R ∧ SatS R exP) ∧
    (∃ R, (fun M => ¬ SatS M exP) R ∧ ¬ SatS R exP) ∧
    ¬ (∃ T, (fun _ => True) T ∧ SatS T exP ∧
      (∃ R, (fun M => ¬ SatS M exP) R ∧ SatS R exP) ∧
      (∃ R, (fun M => ¬ SatS M exP) R ∧ ¬ SatS R exP)) := …
```

#### `consistent_with_both_needs_system_not_valid`

```lean
-- ToyTransfer/Examples.lean:234-240
theorem consistent_with_both_needs_system_not_valid :
    (∃ T, (fun _ => True) T ∧ SatS T exP) ∧
    (∃ R, (fun M => SatS M exP) R ∧ SatS R exP) ∧
    ¬ (∃ R, (fun M => SatS M exP) R ∧ ¬ SatS R exP) ∧
    ¬ (∃ T, (fun _ => True) T ∧ SatS T exP ∧
      (∃ R, (fun M => SatS M exP) R ∧ SatS R exP) ∧
      (∃ R, (fun M => SatS M exP) R ∧ ¬ SatS R exP)) := …
```

#### `unrelated_nonvacuous`

```lean
-- ToyTransfer/Examples.lean:163-167
theorem unrelated_nonvacuous :
    (∃ M, (fun _ => True) M ∧ SatS M exP) ∧ (∃ M, (fun _ => True) M ∧ ¬ SatS M exP) ∧
    ¬ (∀ T R, (fun _ => True) T → (fun _ => True) R → SatS T exP → SatS R exP) ∧
    ¬ (∀ T R, (fun _ => True) T → (fun _ => True) R → ¬ SatS T exP → ¬ SatS R exP) ∧
    ¬ (∀ T R, (fun _ => True) T → (fun _ => True) R → SatS T exP → ¬ SatS R exP) := …
```

#### `unrelated_two_class_example`

```lean
-- ToyTransfer/Examples.lean:178-181
theorem unrelated_two_class_example :
    (∀ T R, (fun _ => True) T → (fun M : Str => Nonempty M.carrier) R →
      SatS T exSelfEq → SatS R exSelfEq) ∧
    ¬ ValidIn (fun _ => True) exSelfEq ∧ ¬ UnsatIn (fun _ => True) exSelfEq := …
```

#### `narrow_scope_readings_differ_from_unrelated_transfer`

```lean
-- ToyTransfer/Examples.lean:193-199
theorem narrow_scope_readings_differ_from_unrelated_transfer :
    ((ValidIn (fun _ => True) exP → ValidIn (fun _ => True) exP) ∧
      ¬ (UnsatIn (fun _ => True) exP ∨ ValidIn (fun _ => True) exP)) ∧
    ((UnsatIn (fun _ => True) exP → UnsatIn (fun _ => True) exP) ∧
      ¬ (ValidIn (fun _ => True) exP ∨ UnsatIn (fun _ => True) exP)) ∧
    ((ValidIn (fun _ => True) exP → UnsatIn (fun _ => True) exP) ∧
      ¬ (UnsatIn (fun _ => True) exP ∨ UnsatIn (fun _ => True) exP)) := …
```

#### `S1Full`

```lean
-- ToyTransfer/FinModels.lean:36
def S1Full : FinStr 1 := ⟨fun _ _ => true, fun _ => true⟩
```

## Boundaries

### Non-claims

Read the non-claims of a card together with its plain claim. Non-claims shared by several cards are repeated in each card that they bear on.

#### 1. Non-claims of `univ-preserved-to-substructure-along-embedding`

- Does not state the converse (Łoś–Tarski: a formula preserved under induced substructures is equivalent to a universal one; Rossman 2008, Theorem 1.1 and footnote 1). The converse is not formalized here; over finite structures it fails (Tait 1959; Rossman 2008, Theorem 1.4) (not proved here).
- Does not say that universal formulas transfer from a structure to its extensions; that direction fails (`allP_not_preserved_to_extension`).
- Each of the five laws of an embedding is used: for each law there is an instance satisfying the other four laws in which some universal sentence fails to transfer (see the hypothesis table). In particular an injective homomorphism (which need not reflect R or P) and a strong homomorphism (which need not be injective) do not suffice.
- Classes are syntactic: a formula that is merely logically equivalent to a universal formula is not covered.
- Structures may have empty carriers (`emptyStr`), unlike the classical convention of non-empty domains (Rossman 2008, §2.1.1). The statement quantifies over all structures, empty or not, so it also holds when structures are restricted to non-empty ones. Facts about validity do depend on the convention: `∃x, x = x` is not valid over all structures but is valid over the non-empty ones (`exSelfEq_valid_iff_nonempty_carriers`).
- Model–system relation for this package itself: none proved. The structures (one binary relation R, one unary predicate P, equality), formulas and transition systems are abstract toy definitions; these results neither establish nor refute the corresponding claims about any particular modelling formalism, verification tool or real system. Connections to verification practice are separate claims of the kind 'derived (modeling bridge)'.

#### 2. Non-claims of `exist-preserved-to-extension-along-embedding`

- Does not say that existential formulas transfer from a structure to its induced substructures; that direction fails (`exP_not_preserved_to_substructure`).
- Does not state the converse (Łoś–Tarski: a formula preserved under embeddings is equivalent to an existential one; Rossman 2008, Theorem 1.1). The converse is not formalized here; over finite structures it fails (Tait 1959; Gurevich 1984; Rossman 2008, Theorem 1.4) (not proved here).
- Each of the five laws of an embedding is used (see the hypothesis table); an injective homomorphism or a strong homomorphism does not suffice.
- The universal, existential, ∀∃ and ∃∀ classes are prenex, while the positive and positive existential classes allow quantifiers under ∧ and ∨. So a positive existential formula need not be existential in the prenex sense: `posExist_not_subset_exist` exhibits `(∃x, P x) ∧ (∃y, P y)`. Hodges (1993, §2.4) and Rossman (2008, Remark 2.1) use non-prenex classes. Classes are syntactic: a formula that is merely logically equivalent to a class member is not covered.
- Structures may have empty carriers (`emptyStr`), unlike the classical convention of non-empty domains (Rossman 2008, §2.1.1). The statement quantifies over all structures, empty or not, so it also holds when structures are restricted to non-empty ones. Facts about validity do depend on the convention: `∃x, x = x` is not valid over all structures but is valid over the non-empty ones (`exSelfEq_valid_iff_nonempty_carriers`).
- Model–system relation for this package itself: none proved. The structures (one binary relation R, one unary predicate P, equality), formulas and transition systems are abstract toy definitions; these results neither establish nor refute the corresponding claims about any particular modelling formalism, verification tool or real system. Connections to verification practice are separate claims of the kind 'derived (modeling bridge)'.

#### 3. Non-claims of `positive-existential-preserved-forward-along-homomorphism`

- Does not state the converse, the homomorphism preservation theorem (a formula preserved under homomorphisms is equivalent to an existential-positive one; Rossman 2008, Theorem 1.3). That theorem is not formalized here. Unlike Łoś–Tarski and Lyndon's theorem, it remains true over finite structures for sentences (Rossman 2008, Theorem 1.7) (not proved here).
- Lyndon's positivity theorem (Lyndon 1959; Rossman 2008, Theorem 1.2) is the converse for surjective homomorphisms and positive formulas (`positive-preserved-forward-along-surjective-homomorphism`), not the converse of this statement.
- Does not say that positive existential formulas transfer backward along homomorphisms (`exP_not_preserved_to_substructure`).
- The universal, existential, ∀∃ and ∃∀ classes are prenex, while the positive and positive existential classes allow quantifiers under ∧ and ∨. So a positive existential formula need not be existential in the prenex sense: `posExist_not_subset_exist` exhibits `(∃x, P x) ∧ (∃y, P y)`. Hodges (1993, §2.4) and Rossman (2008, Remark 2.1) use non-prenex classes. Classes are syntactic: a formula that is merely logically equivalent to a class member is not covered.
- The syntax has no nullary atoms ⊤ and ⊥ (positive formulas in the classical theorems may use them), so there are no quantifier-free sentences (`no_qf_sentences`), and no positive formula is unsatisfiable: every positive formula holds in the one-element structure where R and P hold everywhere (`pos_holds_in_full_one_point`).
- Structures may have empty carriers (`emptyStr`), unlike the classical convention of non-empty domains (Rossman 2008, §2.1.1). The statement quantifies over all structures, empty or not, so it also holds when structures are restricted to non-empty ones. Facts about validity do depend on the convention: `∃x, x = x` is not valid over all structures but is valid over the non-empty ones (`exSelfEq_valid_iff_nonempty_carriers`).
- Model–system relation for this package itself: none proved. The structures (one binary relation R, one unary predicate P, equality), formulas and transition systems are abstract toy definitions; these results neither establish nor refute the corresponding claims about any particular modelling formalism, verification tool or real system. Connections to verification practice are separate claims of the kind 'derived (modeling bridge)'.

#### 4. Non-claims of `positive-preserved-forward-along-surjective-homomorphism`

- Does not state the converse, Lyndon's positivity theorem (a formula preserved under surjective homomorphisms is equivalent to a positive one; Lyndon 1959; Rossman 2008, Theorem 1.2). It is not formalized here; over finite structures it fails (Ajtai and Gurevich 1987; Stolboushkin 1995; Rossman 2008, Theorem 1.5) (not proved here).
- Does not say that positive formulas transfer backward along surjective homomorphisms (`exP_not_reflected_by_surjHom`).
- The syntax has no nullary atoms ⊤ and ⊥ (positive formulas in the classical theorems may use them), so there are no quantifier-free sentences (`no_qf_sentences`), and no positive formula is unsatisfiable: every positive formula holds in the one-element structure where R and P hold everywhere (`pos_holds_in_full_one_point`).
- Structures may have empty carriers (`emptyStr`), unlike the classical convention of non-empty domains (Rossman 2008, §2.1.1). The statement quantifies over all structures, empty or not, so it also holds when structures are restricted to non-empty ones. Facts about validity do depend on the convention: `∃x, x = x` is not valid over all structures but is valid over the non-empty ones (`exSelfEq_valid_iff_nonempty_carriers`).
- Model–system relation for this package itself: none proved. The structures (one binary relation R, one unary predicate P, equality), formulas and transition systems are abstract toy definitions; these results neither establish nor refute the corresponding claims about any particular modelling formalism, verification tool or real system. Connections to verification practice are separate claims of the kind 'derived (modeling bridge)'.

#### 5. Non-claims of `five-unlicensed-transfers-countermodels`

- Each countermodel refutes uniform transfer of its class along its map kind in the stated direction; it does not say that no formula of the class transfers (for example, quantifier-free formulas are universal and do transfer along embeddings in both directions, `unlicensed_cells_contain_transferring_subclasses`).
- These are five of the thirteen countermodels used by the transfer matrix; the matrix card states which cells each refutes.
- Model–system relation for this package itself: none proved. The structures (one binary relation R, one unary predicate P, equality), formulas and transition systems are abstract toy definitions; these results neither establish nor refute the corresponding claims about any particular modelling formalism, verification tool or real system. Connections to verification practice are separate claims of the kind 'derived (modeling bridge)'.

#### 6. Non-claims of `transfer-matrix-boolean-table-agrees-with-preservation`

- The table is about uniform transfer of a whole syntactic class. A `false` verdict for a class does not refute transfer of an individual formula: `licensedForB` is sound but not complete (`licensedForB_incomplete`, the valid ∀x, P x ∨ ¬ P x along homomorphisms), and unlicensed cells can contain subclasses that transfer (`unlicensed_cells_contain_transferring_subclasses`).
- Transfer is stated for formulas with parameters: along h : A → B the environment e of A becomes h ∘ e, and in the system-to-model reading the model side is evaluated at image environments h ∘ e, not at arbitrary model environments. There are no quantifier-free sentences (`no_qf_sentences`), so the quantifier-free row is witnessed by formulas with one or two free variables; restricted to sentences, quantifier-free transfer holds vacuously in every cell (`preservesSent_qf`). For the other six rows the same table is exact for sentences (`licensedB_iff_preservesSent_of_ne_qf`).
- Strong homomorphisms license the same cells as homomorphisms because the signature includes equality: a non-injective strong homomorphism does not preserve `¬ x = y` (`neq_not_preserved_by_strongHom`) and does not reflect `x = y` (`eq_not_reflected_by_strongHom`). On equality-free quantifier-free formulas, strong homomorphisms do preserve and reflect satisfaction (`qf_sat_iff_of_strongHom_of_eqFree`). An equality-free version of the whole table is not formalized. 'Strong homomorphism' means `IsStrongHom` (preserves and reflects R and P); usage of the term varies in the literature.
- The universal, existential, ∀∃ and ∃∀ classes are prenex, while the positive and positive existential classes allow quantifiers under ∧ and ∨. So a positive existential formula need not be existential in the prenex sense: `posExist_not_subset_exist` exhibits `(∃x, P x) ∧ (∃y, P y)`. Hodges (1993, §2.4) and Rossman (2008, Remark 2.1) use non-prenex classes. Classes are syntactic: a formula that is merely logically equivalent to a class member is not covered.
- Prenex classes allow empty prefixes, so every quantifier-free formula is universal and existential, and every universal or existential formula is ∀∃ and ∃∀. The ∀∃ and ∃∀ rows are therefore refuted partly by purely universal or purely existential sentences; the table makes no separate claim about strictly alternating formulas.
- The syntax has no nullary atoms ⊤ and ⊥ (positive formulas in the classical theorems may use them), so there are no quantifier-free sentences (`no_qf_sentences`), and no positive formula is unsatisfiable: every positive formula holds in the one-element structure where R and P hold everywhere (`pos_holds_in_full_one_point`).
- Structures may have empty carriers (`emptyStr`), unlike the classical convention of non-empty domains (Rossman 2008, §2.1.1). Every refuting instance in the table uses structures with one or two elements, and the licensed cells hold for all structures, so the table is unchanged if structures are restricted to non-empty ones (derived from the definitions of the countermodel structures; not stated as a separate theorem).
- The formalization covers the signature with one binary relation, one unary predicate and equality; a general finite relational signature, isomorphisms, elementary embeddings and surjective strong homomorphisms are not formalized as columns (not proved here).
- The converse preservation theorems (Łoś–Tarski, Lyndon, the homomorphism preservation theorem) are not formalized; the table concerns syntactic classes, not classes closed under logical equivalence.
- Model–system relation for this package itself: none proved. The structures (one binary relation R, one unary predicate P, equality), formulas and transition systems are abstract toy definitions; these results neither establish nor refute the corresponding claims about any particular modelling formalism, verification tool or real system. Connections to verification practice are separate claims of the kind 'derived (modeling bridge)'.

#### 7. Non-claims of `model-embeds-into-system-counterexamples-and-witnesses-transfer`

- An under-approximating model obtained by deleting R-edges or P-facts on retained elements is related to the system by an injective homomorphism that does not reflect R or P, which is not an embedding (`injective_hom_not_embedding_example`); for such models neither transfer is claimed, and both fail in general (`allRxx_reflection_fails_without_reflR`, `exNotRxx_transfer_fails_without_reflR`).
- `allP_truth_in_model_undetermined_in_system_along_embedding` concerns the single sentence ∀x, P x. Model truth of other universal formulas can transfer: quantifier-free formulas transfer along embeddings in both directions (`qf_sat_iff_of_embedding_laws`), and valid sentences hold in every system. Model truth of a universal sentence can also license different claims about the system: for a non-empty model, ∀x, P x in M gives ∃x, P x in S (`allP_in_nonempty_model_gives_exP_in_system`).
- Does not say that universal truths or existential falsities of the model transfer to the system in this orientation (`allP_not_preserved_to_extension`, `exP_not_preserved_to_substructure`).
- Model–system relation for this package itself: none proved. The structures (one binary relation R, one unary predicate P, equality), formulas and transition systems are abstract toy definitions; these results neither establish nor refute the corresponding claims about any particular modelling formalism, verification tool or real system. Connections to verification practice are separate claims of the kind 'derived (modeling bridge)'.

#### 8. Non-claims of `system-embeds-into-model-universal-proofs-transfer-counterexamples-may-be-spurious`

- Over-approximations used in model checking and abstract interpretation (state-merging quotients, predicate abstraction, relation-widening) are in general not embeddings: they are not injective or do not reflect R and P. This statement says nothing about them; for surjective homomorphisms from system to model, the classes whose model-side falsity is licensed are exactly the positive and positive existential ones (`licences_exact`).
- Does not say that model counterexamples are always spurious; it says that the embedding does not exclude spurious ones.
- Model–system relation for this package itself: none proved. The structures (one binary relation R, one unary predicate P, equality), formulas and transition systems are abstract toy definitions; these results neither establish nor refute the corresponding claims about any particular modelling formalism, verification tool or real system. Connections to verification practice are separate claims of the kind 'derived (modeling bridge)'.

#### 9. Non-claims of `forward-simulation-relates-reachable-states`

- Does not say that every abstract state related to a reachable concrete state is reachable (`strong_pullback_fails_with_unreachable_related_state`).
- `SimStepStar` (like every matching law here) requires matching from every `S`-related pair, reachable or not; a weaker law restricted to reachable pairs is not formalized.
- Transition systems are unlabelled (states, a step relation, initial states); safety means a single-state invariant on reachable states. Trace properties of labelled systems are not formalized.
- Model–system relation for this package itself: none proved. The structures (one binary relation R, one unary predicate P, equality), formulas and transition systems are abstract toy definitions; these results neither establish nor refute the corresponding claims about any particular modelling formalism, verification tool or real system. Connections to verification practice are separate claims of the kind 'derived (modeling bridge)'.

#### 10. Non-claims of `safety-invariant-transfers-down-as-existential-pullback`

- The conclusion is the existential pullback, not the universal pullback {c | ∀ a, S c a → I a}, which can fail (`strong_pullback_fails_with_unreachable_related_state`). The universal pullback does hold when S relates each concrete state to at most one abstract state (`strong_pullback_of_functional_simulation`) or after restricting S to reachable abstract states (`reach_restricted_simulation_gives_strong_pullback`).
- `SimStepStar` (like every matching law here) requires matching from every `S`-related pair, reachable or not; a weaker law restricted to reachable pairs is not formalized.
- Transition systems are unlabelled (states, a step relation, initial states); safety means a single-state invariant on reachable states. Trace properties of labelled systems are not formalized.
- Model–system relation for this package itself: none proved. The structures (one binary relation R, one unary predicate P, equality), formulas and transition systems are abstract toy definitions; these results neither establish nor refute the corresponding claims about any particular modelling formalism, verification tool or real system. Connections to verification practice are separate claims of the kind 'derived (modeling bridge)'.

#### 11. Non-claims of `strong-pullback-fails-with-unreachable-related-abstract-state`

- Escape hatches (proved): the universal pullback holds when S relates each concrete state to at most one abstract state, for example the graph of a refinement mapping (`strong_pullback_of_functional_simulation`, instance `functional_simulation_example`), and when S is replaced by S c a ∧ Reach A a, which is again a forward simulation (`reach_restricted_simulation_gives_strong_pullback`, applied to this countermodel in `reach_restriction_repairs_strong_pullback_countermodel`).
- Transition systems are unlabelled (states, a step relation, initial states); safety means a single-state invariant on reachable states. Trace properties of labelled systems are not formalized.
- Model–system relation for this package itself: none proved. The structures (one binary relation R, one unary predicate P, equality), formulas and transition systems are abstract toy definitions; these results neither establish nor refute the corresponding claims about any particular modelling formalism, verification tool or real system. Connections to verification practice are separate claims of the kind 'derived (modeling bridge)'.

#### 12. Non-claims of `bugs-transfer-up-along-forward-simulation`

- Does not say that abstract bugs are concrete bugs; that direction fails under forward simulation alone (`spurious_abstract_counterexample`).
- `SimStepStar` (like every matching law here) requires matching from every `S`-related pair, reachable or not; a weaker law restricted to reachable pairs is not formalized.
- Transition systems are unlabelled (states, a step relation, initial states); safety means a single-state invariant on reachable states. Trace properties of labelled systems are not formalized.
- Model–system relation for this package itself: none proved. The structures (one binary relation R, one unary predicate P, equality), formulas and transition systems are abstract toy definitions; these results neither establish nor refute the corresponding claims about any particular modelling formalism, verification tool or real system. Connections to verification practice are separate claims of the kind 'derived (modeling bridge)'.

#### 13. Non-claims of `spurious-abstract-counterexample-under-forward-simulation`

- Shows that forward simulation alone, even with bad-state agreement in both directions, does not make an abstract counterexample a concrete one. It does not characterize which additional property makes it one: a converse simulation suffices (`bug_transfers_down_of_converse_simulation`) but is not necessary (`abstract_bug_transfer_without_converse_step_matching`); in practice a single abstract counterexample trace can be checked for a concrete counterpart (Clarke et al. 2000, Lemma 1), which is not formalized here.
- Transition systems are unlabelled (states, a step relation, initial states); safety means a single-state invariant on reachable states. Trace properties of labelled systems are not formalized.
- Model–system relation for this package itself: none proved. The structures (one binary relation R, one unary predicate P, equality), formulas and transition systems are abstract toy definitions; these results neither establish nor refute the corresponding claims about any particular modelling formalism, verification tool or real system. Connections to verification practice are separate claims of the kind 'derived (modeling bridge)'.

#### 14. Non-claims of `abstract-bugs-transfer-down-along-converse-simulation`

- This is a sufficient condition, and it is not necessary: `abstract_bug_transfer_without_converse_step_matching` gives a forward simulation in which every reachable abstract bug has a reachable concrete counterpart although the converse relation does not match an abstract step.
- 'Converse simulation' here means a forward simulation from A to C. It is not the backward simulation of Lynch and Vaandrager (1995, §3.3), which goes from the implementation to the specification and matches steps backward in time.
- When S is also a forward simulation from C to A, S is a two-way simulation; that case is not separately formalized.
- `SimStepStar` (like every matching law here) requires matching from every `S`-related pair, reachable or not; a weaker law restricted to reachable pairs is not formalized.
- Transition systems are unlabelled (states, a step relation, initial states); safety means a single-state invariant on reachable states. Trace properties of labelled systems are not formalized.
- Model–system relation for this package itself: none proved. The structures (one binary relation R, one unary predicate P, equality), formulas and transition systems are abstract toy definitions; these results neither establish nor refute the corresponding claims about any particular modelling formalism, verification tool or real system. Connections to verification practice are separate claims of the kind 'derived (modeling bridge)'.

#### 15. Non-claims of `termination-transfers-down-along-lockstep-simulation`

- The conclusion is about reachable states: an unreachable concrete state may start an infinite run (`lockstep_termination_transfer_is_about_reachable_states`).
- `AllRunsFinite` is universal termination from reachable states: every reachable state is accessible for the converse step relation, equivalently (`terminates_iff_no_infinite_run`, classical) no infinite run starts there. Weak termination (some run ends) does not transfer down, even along lock-step simulation (`weak_termination_does_not_transfer_down_lockstep`). Fair termination and other liveness properties are not formalized.
- `SimStepLock` requires matching from every S-related pair, reachable or not.
- Transition systems are unlabelled (states, a step relation, initial states); safety means a single-state invariant on reachable states. Trace properties of labelled systems are not formalized.
- Model–system relation for this package itself: none proved. The structures (one binary relation R, one unary predicate P, equality), formulas and transition systems are abstract toy definitions; these results neither establish nor refute the corresponding claims about any particular modelling formalism, verification tool or real system. Connections to verification practice are separate claims of the kind 'derived (modeling bridge)'.

#### 16. Non-claims of `stuttering-simulation-does-not-transfer-termination`

- Safety facts still transfer along this relation: it satisfies `SimInit` and `SimStepStar`, which are all the hypotheses of `reach_related_of_forward_simulation` and the simulation hypotheses of `invariant_transfers_down_of_forward_simulation` and `bug_transfers_up_of_forward_simulation`; those two theorems therefore apply to this relation for every invariant I that holds on every reachable abstract state (their hypothesis hI) and for every pair of bad-state predicates that satisfies their hypothesis hbad. The countermodel concerns the transfer of termination.
- The repair is a measure that decreases on stuttering steps (`allRunsFinite_transfers_down_of_wf_simulation`). For this relation no such measure exists: for every type W, every well-founded relation lt on W and every measure μ, `SimStepWF` fails (`stuttering_countermodel_admits_no_wf_measure`, derived from `allRunsFinite_transfers_down_of_wf_simulation` and this countermodel). The tightness theorem `wf_simulation_needs_measure_decrease` shows the failure for one constant measure into `Unit`.
- Transition systems are unlabelled (states, a step relation, initial states); safety means a single-state invariant on reachable states. Trace properties of labelled systems are not formalized.
- Model–system relation for this package itself: none proved. The structures (one binary relation R, one unary predicate P, equality), formulas and transition systems are abstract toy definitions; these results neither establish nor refute the corresponding claims about any particular modelling formalism, verification tool or real system. Connections to verification practice are separate claims of the kind 'derived (modeling bridge)'.

#### 17. Non-claims of `well-founded-simulation-criterion-transfers-termination`

- `SimStepWF` allows zero or one abstract step per concrete step; matching by several abstract steps (as in CompCert's `fsim_properties`) is not formalized. The measure need not decrease on non-stuttering steps.
- The criterion is sufficient; no completeness result is claimed.
- `AllRunsFinite` is universal termination from reachable states: every reachable state is accessible for the converse step relation, equivalently (`terminates_iff_no_infinite_run`, classical) no infinite run starts there. Weak termination (some run ends) does not transfer down, even along lock-step simulation (`weak_termination_does_not_transfer_down_lockstep`). Fair termination and other liveness properties are not formalized.
- `SimStepWF` requires matching from every S-related pair, reachable or not.
- Transition systems are unlabelled (states, a step relation, initial states); safety means a single-state invariant on reachable states. Trace properties of labelled systems are not formalized.
- Model–system relation for this package itself: none proved. The structures (one binary relation R, one unary predicate P, equality), formulas and transition systems are abstract toy definitions; these results neither establish nor refute the corresponding claims about any particular modelling formalism, verification tool or real system. Connections to verification practice are separate claims of the kind 'derived (modeling bridge)'.

#### 18. Non-claims of `no-relation-transfer-iff-decided-by-model-or-system-class`

- The characterizations depend on KM, KS and φ, not on a particular model or system. When the system class decides φ (ValidIn KS φ or UnsatIn KS φ), the system claim holds or fails for every system of KS regardless of the model.
- The characterizations are about statements that quantify over every model of KM and every system of KS at once. They are not about the narrow-scope statement 'if φ holds in every model of KM then φ holds in every system of KS' (ValidIn KM φ → ValidIn KS φ), nor its falsity and refutation analogues, which are different statements: for KM = KS = all structures and φ = ∃x, P x each narrow-scope implication holds while the right-hand side of the corresponding characterization fails (`narrow_scope_readings_differ_from_unrelated_transfer`).
- The same-class form allows the model and the system to be the same structure (T = R). If models and systems are known to come from different classes, use the two-class statements: then a refutation is licensed whenever φ is unsatisfiable in the system class, even if φ is satisfiable in the model class.
- Says nothing about structures related by a map; for those, see the transfer matrix and `licences_exact`.
- Structures may have empty carriers (`emptyStr`), unlike the classical convention of non-empty domains (Rossman 2008, §2.1.1). The statement quantifies over all structures, empty or not, so it also holds when structures are restricted to non-empty ones. Facts about validity do depend on the convention: `∃x, x = x` is not valid over all structures but is valid over the non-empty ones (`exSelfEq_valid_iff_nonempty_carriers`).
- Model–system relation for this package itself: none proved. The structures (one binary relation R, one unary predicate P, equality), formulas and transition systems are abstract toy definitions; these results neither establish nor refute the corresponding claims about any particular modelling formalism, verification tool or real system. Connections to verification practice are separate claims of the kind 'derived (modeling bridge)'.

#### 19. Non-claims of `unlicensed-cell-admits-both-outcomes-along-non-isomorphisms`

- The witnesses concern one formula per cell. An unlicensed cell does not mean that no formula of the class transfers, nor that the class carries no information: falsity can transfer in the same direction (`falsity_licensed_where_truth_unlicensed_iff`), and proper subclasses can transfer (`unlicensed_cells_contain_transferring_subclasses`, for example quantifier-free formulas inside the universal/embedding/forward cell).
- Excluding isomorphisms rules out the trivial agreeing witness (the identity map, `MapKind.holds_id`); the witnesses are otherwise small (one to three elements) and all have non-empty carriers.
- Transfer is stated for formulas with parameters: along h : A → B the environment e of A becomes h ∘ e, and in the system-to-model reading the model side is evaluated at image environments h ∘ e, not at arbitrary model environments. There are no quantifier-free sentences (`no_qf_sentences`), so the quantifier-free row is witnessed by formulas with one or two free variables; restricted to sentences, quantifier-free transfer holds vacuously in every cell (`preservesSent_qf`). For the other six rows the same table is exact for sentences (`licensedB_iff_preservesSent_of_ne_qf`).
- Model–system relation for this package itself: none proved. The structures (one binary relation R, one unary predicate P, equality), formulas and transition systems are abstract toy definitions; these results neither establish nor refute the corresponding claims about any particular modelling formalism, verification tool or real system. Connections to verification practice are separate claims of the kind 'derived (modeling bridge)'.

#### 20. Non-claims of `exact-licences-per-map-kind-and-orientation`

- Transfer is stated for formulas with parameters: along h : A → B the environment e of A becomes h ∘ e, and in the system-to-model reading the model side is evaluated at image environments h ∘ e, not at arbitrary model environments. There are no quantifier-free sentences (`no_qf_sentences`), so the quantifier-free row is witnessed by formulas with one or two free variables; restricted to sentences, quantifier-free transfer holds vacuously in every cell (`preservesSent_qf`). For the other six rows the same table is exact for sentences (`licensedB_iff_preservesSent_of_ne_qf`).
- Strong homomorphisms license the same cells as homomorphisms because the signature includes equality: a non-injective strong homomorphism does not preserve `¬ x = y` (`neq_not_preserved_by_strongHom`) and does not reflect `x = y` (`eq_not_reflected_by_strongHom`). On equality-free quantifier-free formulas, strong homomorphisms do preserve and reflect satisfaction (`qf_sat_iff_of_strongHom_of_eqFree`). An equality-free version of the whole table is not formalized. 'Strong homomorphism' means `IsStrongHom` (preserves and reflects R and P); usage of the term varies in the literature.
- The universal, existential, ∀∃ and ∃∀ classes are prenex, while the positive and positive existential classes allow quantifiers under ∧ and ∨. So a positive existential formula need not be existential in the prenex sense: `posExist_not_subset_exist` exhibits `(∃x, P x) ∧ (∃y, P y)`. Hodges (1993, §2.4) and Rossman (2008, Remark 2.1) use non-prenex classes. Classes are syntactic: a formula that is merely logically equivalent to a class member is not covered.
- Structures may have empty carriers (`emptyStr`), unlike the classical convention of non-empty domains (Rossman 2008, §2.1.1). Every refuting instance in the table uses structures with one or two elements, and the licensed cells hold for all structures, so the table is unchanged if structures are restricted to non-empty ones (derived from the definitions of the countermodel structures; not stated as a separate theorem).
- `.posExist` is listed separately from `.exist` because the positive existential class is not contained in the prenex existential class (`posExist_not_subset_exist`).
- Model–system relation for this package itself: none proved. The structures (one binary relation R, one unary predicate P, equality), formulas and transition systems are abstract toy definitions; these results neither establish nor refute the corresponding claims about any particular modelling formalism, verification tool or real system. Connections to verification practice are separate claims of the kind 'derived (modeling bridge)'.

### Escape hatches

No result has the kind `impossibility`. The four counterexample cards (5, 11, 13, 16) each come with proved positive controls, which are the escape hatches: the strengthened hypotheses under which the refuted transfer does hold.

- Card 5 (`five-unlicensed-transfers-countermodels`): restricting to the class and map kind of a licensed cell restores the transfer (`univ_preserved_to_substructure_of_embedding`, `exist_preserved_to_extension_of_embedding`, `posExist_preserved_forward_of_hom`, `pos_preserved_forward_of_surjHom`).
- Card 11 (`strong-pullback-fails-with-unreachable-related-abstract-state`): for a forward simulation S (`SimInit`, `SimStepStar`) and an invariant I of every reachable abstract state, the universal pullback holds when S relates each concrete state to at most one abstract state (`strong_pullback_of_functional_simulation`), and it holds for the restricted relation S c a ∧ Reach A a, which is again a forward simulation (`reach_restricted_simulation_gives_strong_pullback`).
- Card 13 (`spurious-abstract-counterexample-under-forward-simulation`): a forward simulation from A to C by the converse relation, together with agreement on badness in that direction, transfers reachable abstract bugs down (`bug_transfers_down_of_converse_simulation`); this sufficient condition is not necessary (`abstract_bug_transfer_without_converse_step_matching`).
- Card 16 (`stuttering-simulation-does-not-transfer-termination`): given `SimInit` and termination of every reachable abstract state, lock-step matching (`allRunsFinite_transfers_down_of_lockstep`) or a matching whose stuttering steps decrease a measure in a well-founded relation (`allRunsFinite_transfers_down_of_wf_simulation`) transfers termination down; for the relation of the countermodel no such measure exists (`stuttering_countermodel_admits_no_wf_measure`).
- Unlicensed cells (cards 6 and 19): a `false` verdict concerns uniform transfer of a whole class. Model-side falsity can be licensed where model-side truth is not (`falsity_licensed_where_truth_unlicensed_iff`), proper subclasses can transfer (`unlicensed_cells_contain_transferring_subclasses`), and `licensedForB` is sound but not complete (`licensedForB_incomplete`).
- No relation (card 18): the characterizations assume no map between model and system; with a proved map, the transfer matrix and `licences_exact` apply instead.

### Tightness status

All 47 recorded (hypothesis, theorem) rows of the 20 cards are `tight`; each names a proved counterexample theorem in which every other hypothesis of that theorem holds and the conclusion fails, and records the class of the witness. No hypothesis is recorded as `harmless` or `unknown`.

### Not examined

- A general finite relational signature, function symbols, constants and several sorts; the nullary atoms ⊤ and ⊥.
- Isomorphisms, elementary embeddings and surjective strong homomorphisms as columns of the transfer matrix; an equality-free version of the whole table.
- The converse preservation theorems (Łoś–Tarski, Lyndon, the homomorphism preservation theorem) and their behaviour over finite structures; classes closed under logical equivalence.
- Properties beyond first-order logic, such as reachability of unbounded length.
- Labelled transition systems and trace properties; backward simulations in the sense of Lynch and Vaandrager (1995, §3.3); two-way simulations as a separate case; matching laws restricted to reachable pairs; matching by several abstract steps together with a measure; completeness of the well-founded simulation criterion; fair termination and liveness properties other than termination.
- Any real model, modelling formalism, verification tool or system (model–system relation: none proved).

### Disproved or dropped statements

None. Every statement recorded for this package is proved as stated; no statement was found false and none was dropped.

## Evidence

**Kernel check.** Basis: execution (Lean kernel check). The library builds with `lake build` under `leanprover/lean4:v4.34.1` (commit `5045d0056413266e57c625dcd7c365b10e377c52`) with no errors and no warnings, from a clean copy with Lake's artifact cache disabled, so every proof is re-elaborated and kernel-checked. The Lean sources contain no `sorry`, `admit`, `native_decide`, `implemented_by`, `@[extern]`, `unsafe` or `debug.skipKernelTC`, and no `axiom` or `opaque` declarations. Countermodels on finite structures are checked by `decide` (kernel evaluation, not `native_decide`) or by short direct proofs. An axiom audit with `Lean.collectAxioms` over all 889 declarations of the library's modules finds no axioms other than `propext`, `Classical.choice` and `Quot.sound`; the per-declaration record is `audit/axioms.json`.

**Statement and closure hashes.** For every Lean name referenced by a card (`lean`, `lean_names`, tightness counterexamples, non-vacuity witnesses, positive controls), `audit/statements.json` records the SHA-256 of the statement (the Lean `repr` of its type) and of its definition closure (the sorted list of `name : type := value` for every package constant reachable from the statement, theorem bodies excluded), together with the closure size. For a definition listed by name, the statement hash covers its type, and its body is covered by the closure hash of every listed theorem whose statement reaches it. A change to a definition or statement changes these hashes; `support/revalidate.py` recomputes and compares all of them (see **Revalidation**). The table lists all 307 hashed names (namespace `Toy.Transfer` omitted) with their axioms.

| Lean name | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :-- | :-- | :-- | :-- |
| `abstract_bug_transfer_without_converse_step_matching` | propext | `12b21da721c71631ae1d8375570314112040be1492e175f7a01ec0d27439e096` | `22a05ce33cf5fe6a440850ba772db20a462abad4c50ad60511f8c52f0142177e` (18) |
| `addEdge` | none | `b14704490442c7f8f6d3f43bb36858ddaf8cbf579bc3c866b278c5abb86766cf` | `0a7241505b50937b3188b5ed35d4e24e01dc820c21717b5a584962a0951fd969` (10) |
| `allAllEq` | propext | `364749a860fdcb74a6ae74e9261055ee7a53ccbb6ad484bdbbd10b2397801c26` | `614a9c50d70973cf92e7ab3d8ad00e40c6d0698e4239c43e2ac4a9851f4c4116` (9) |
| `allAllEq_not_reflected_by_strongHom` | Quot.sound, propext | `d4414ff4d405ef602621f55711591f181f077d8900acea54a7ef9879a1d446ec` | `fa1b0163f676aab9291929d137ec5bc09bf7b326e97c93e8b567f4b81ccd25d7` (68) |
| `allCls` | none | `33ece7d0674ddc502a7d2588b732a6fa620b39841bf9f590081f36223f50bbcb` | `3cd4a32094555e6610bdf997172395d3538eb679eed60eb09315f8ceef607b4b` (8) |
| `allExP` | propext | `364749a860fdcb74a6ae74e9261055ee7a53ccbb6ad484bdbbd10b2397801c26` | `614a9c50d70973cf92e7ab3d8ad00e40c6d0698e4239c43e2ac4a9851f4c4116` (9) |
| `allExR` | propext | `364749a860fdcb74a6ae74e9261055ee7a53ccbb6ad484bdbbd10b2397801c26` | `614a9c50d70973cf92e7ab3d8ad00e40c6d0698e4239c43e2ac4a9851f4c4116` (9) |
| `allExR_not_preserved_to_substructure` | Quot.sound, propext | `b4e8083cfc43239b7ddeb0b6bc40107b64a3b84db963555718b3e31cf8c4ee1c` | `813bd50c91ff8110c3b17abe11b9e505bd4f4b041cdb1e1bf6f224375e094450` (65) |
| `allNotP` | propext | `364749a860fdcb74a6ae74e9261055ee7a53ccbb6ad484bdbbd10b2397801c26` | `614a9c50d70973cf92e7ab3d8ad00e40c6d0698e4239c43e2ac4a9851f4c4116` (9) |
| `allNotP_reflection_fails_without_presP` | Quot.sound, propext | `a11d75299bfc3c9657c305ad1826e3517ad4415e512220f0bf290d29ceb7edbb` | `6cdf389c5bfa00f456b9dbfeb07a9db9a810764df90bb21e7cd4b139ca5f1d6b` (48) |
| `allNotRxx` | propext | `364749a860fdcb74a6ae74e9261055ee7a53ccbb6ad484bdbbd10b2397801c26` | `614a9c50d70973cf92e7ab3d8ad00e40c6d0698e4239c43e2ac4a9851f4c4116` (9) |
| `allNotRxx_reflection_fails_without_presR` | Quot.sound, propext | `edd70cec9fcc1e8ab8c136c208150ba3d98d888fdd51c1a538d333c1d70d3761` | `f7ccbc0883ca21b77594c8f3a947020358258c7dc24ecbc9ab396d38b6024556` (48) |
| `allP` | propext | `364749a860fdcb74a6ae74e9261055ee7a53ccbb6ad484bdbbd10b2397801c26` | `614a9c50d70973cf92e7ab3d8ad00e40c6d0698e4239c43e2ac4a9851f4c4116` (9) |
| `allP_in_nonempty_model_gives_exP_in_system` | propext | `52f4e08770200c65eb36f88d2bef129c5b177a1c449f427c85346f7108253212` | `97b051462d24d936fd43022b9b5235e5dd0d6f57fe074e9a4aa00e26cca621d8` (34) |
| `allP_not_preserved_to_extension` | Quot.sound, propext | `10cc5bdf2711716dee69006caae3e357c92f612d065e20826c1a2fa7a4c07658` | `becc78eac7698567e1f271598e2cba5f19fc372efa18fe183ad1ed0b634d31a9` (75) |
| `allP_not_reflected_by_surjHom` | Quot.sound, propext | `7393ae996771e6e150bb376c097658e38c7f3e7762e8aa1bf762ceb3174df665` | `115af1dccdbb2fc2b02c3af6d991841e1cd0cbd68dad9e5f495415ad2f794f64` (67) |
| `allP_truth_in_model_undetermined_in_system_along_embedding` | Quot.sound, propext | `f150476774d329301587716600fa14762ec4e0b739cbf3c9b56dbe0ecd7b6259` | `4730de92de54351e2beda5768e4790e4795789c3e5b1d272f0e6506590d2fae7` (53) |
| `allRImpEq` | propext | `364749a860fdcb74a6ae74e9261055ee7a53ccbb6ad484bdbbd10b2397801c26` | `614a9c50d70973cf92e7ab3d8ad00e40c6d0698e4239c43e2ac4a9851f4c4116` (9) |
| `allRImpEq_not_preserved_by_surjHom` | Quot.sound, propext | `f111a2e3e49dc30fe84514cf1e0c0d94dbe562cd7db9dd13035579a530020ff6` | `b7e46ae652824e975016281a3d2b1fd4ee2e27ca0d7a64a5b174e124d0540dc5` (68) |
| `AllRunsFinite` | none | `b1ef87a8d6c6a5104d447d2dd5f86db8aab400ed0f07aff2dbd4ea751c8d9a7c` | `52c59e58bca2a41c44a01701b22c3939e615998e01b38d553889d965fec6bf2e` (2) |
| `allRunsFinite_examples` | none | `cccabc4bbdd0083fc5bd2f554da67274e6740e22db66c683701ea0b37f7eb5a1` | `c191d97656629819bd257ef884c5cd100b119ef21e9a3edfb6f6083afa2e65a1` (12) |
| `allRunsFinite_iff` | none | `f2a7fc356e76ca3a61da3b3b44bf856e3c608993a1a3a49bbafa128e22fa3767` | `9e3cf3d7b27cf81d86614eeda255ef30b3fd74d3f3823f8d453f288031fc717c` (10) |
| `allRunsFinite_transfers_down_of_lockstep` | none | `f2d0c0a7495551be4c698fa02ac15ac0d8570a31921252b8ae7c9c9a65cd0b55` | `646f16fd017585048b9e83fe07d1a356524c6f4646f72090790ce18e4f8af2fa` (12) |
| `allRunsFinite_transfers_down_of_wf_simulation` | none | `a0aac0e2304b537ef9b54fdfa5c9fdc06c4312fae3908a1732a7cd0cfa9e9f00` | `5e348081db79f3c602dd663fdb462c839e44620a4a695b69ab2db2b56ccff63e` (12) |
| `allRxx` | propext | `364749a860fdcb74a6ae74e9261055ee7a53ccbb6ad484bdbbd10b2397801c26` | `614a9c50d70973cf92e7ab3d8ad00e40c6d0698e4239c43e2ac4a9851f4c4116` (9) |
| `allRxx_reflection_fails_without_reflR` | Quot.sound, propext | `4934b1821bb3006b7c527a4692b6d6a159233399d6e32fb478b34fcc06f6ab59` | `51a94b78510fac1f26fb62cd07329ab00c075101ebe73fa5fa36551d5a205a6e` (56) |
| `atMostOneNotP` | propext | `364749a860fdcb74a6ae74e9261055ee7a53ccbb6ad484bdbbd10b2397801c26` | `614a9c50d70973cf92e7ab3d8ad00e40c6d0698e4239c43e2ac4a9851f4c4116` (9) |
| `badNone` | none | `93db199d680da3a5880b5be98ec429fc73fe9c04719aadffccdf1180a0c1417d` | `2e170fa3ba38edff083533271f6426f39a1e9f8c413589af99405220fb5edf14` (4) |
| `badTrue` | none | `39a04b326e21e0ce02c78ed49c65e29427ecb5f92b1d01d423bbd60c541c49c0` | `729b4b8a388e42d03ca7dafb4a1acf54017badb6a38de2a8276baf37d70ef066` (4) |
| `both_allExR` | Quot.sound, propext | `44cc6aa3c0aa6a1aa2fd74437b696ac2d9a301b81da8769f73f4660e3dc3eb4d` | `af290800ec4c1aafa4c6de88874bffd48b9018f5833ce905d8f34bf23ae43907` (112) |
| `both_allP` | Quot.sound, propext | `6871d089fb9f2e58279846f07ca96dbde3f6f398575dd7163e52c511910aa591` | `77d0bbde3625a41d4ad428cd79c31517506b3b32b4427600812ab6d55b1957b9` (112) |
| `both_allP_surj` | Quot.sound, propext | `6cccff9629a81282680e6d73222680349ed56aebdb24ee529b95b1d04bd6e4b7` | `d899b433c74a204297971c688dfffc38f1c9134c5f5e56678eddfc2e2cb8df40` (111) |
| `both_allRImpEq` | Quot.sound, propext | `489e884004515ad9c32bd45e882f8bffb191cf736205c5fdcbf1a7907be95f05` | `4ef42d558fc179ff8c93916ca4d08248ce700bce524df275827dca4f9996beaa` (113) |
| `both_atMostOneNotP` | Quot.sound, propext | `6f1b575c46576930e03e9f494d1112fd754f2c582c97fc5d4385758d06f66488` | `a983128ef45969d8b619f97f7df692ad213f2d59d459b94ef0d641a42fb7e64b` (112) |
| `both_eq` | Quot.sound, propext | `30a3a55a4297393103a0e1ccc7844bf876d90135b37b440c0b5b78eb2b468e11` | `d0c0b95655228a448f61e05398f4ed9c3d515defb6a53bd0acfb46bcbda916a9` (110) |
| `both_exExNeq` | Quot.sound, propext | `194d32a7b8696d50e9c8c53ba5661e8d2f1b5b5b73f9fc1ae012653ef29ddf48` | `5efdd210735df3c01a7c85e90b69ab2258932d502d89dd558245a9a825383f2a` (113) |
| `both_exNotP` | Quot.sound, propext | `1ee2ea95f0c933ec0859fd6979ec6afba5d173cb0b4c5db00f049b674061760d` | `b57cfcc84c15f8185d55b81984d8eb627bbe07af3ea1791d8e7761f3d7cddd89` (111) |
| `both_exP_sub` | Quot.sound, propext | `5761066414d115915c12ffef29bd754ac98e44f2044a633308560e0929a5f538` | `54d8eb34a5a744fe1211225d25db1e4360349a77169161eda28ff84a76905fcb` (112) |
| `both_exP_surj` | Quot.sound, propext | `70cd83d7f64989f5fff005d0649bf26f47881b0c76655e70c55ca18c36325473` | `f77ce76ae0ff1890701693b57f0c0e4d9f5e8f728cdf46685f3b1dc10bb8e4e4` (112) |
| `both_neq` | Quot.sound, propext | `ed31bd7ff8085307463e98f87166c2534cc4754588636842820e5d4f0bcf8c27` | `b84fc4ef7a3674f5ce1746a3121063f237241aa4cbddbed325bd5af8c0acbf32` (113) |
| `both_notP0` | Quot.sound, propext | `b4d914a015574eca7ac43f7bbc48785f5f8cd41023b7541f61b5ce6d459db006` | `1801bf6e6bfe97827ba7bfcb99efbf5fc60fa66ce9429292cedbbc855ca1d58e` (111) |
| `both_P0` | Quot.sound, propext | `6867250b71576fb84c14b3a17ae4105b01658bbf6321bd7e8ac7f6978f147842` | `7ace1219988e3fb85d63392ce348909eacf4f4161015d986aae1b09beceb4bcd` (112) |
| `BothOutcomesNonIso` | none | `079f35086c5828551e392f89ace2a292beefe5efb982edaa65af406a820820c0` | `7ad5717e1655e6a8703fa09758238cd55fae6c5d98777bd6467fe749000ca7c2` (16) |
| `bothOutcomesNonIso_examples` | Quot.sound, propext | `7dcc4f1b0abebf9a344fe0dcf798a9aa44c59bf3ada12ea61ffd86d55a738526` | `e7cfbc605a972017f15d224edc97b88db3c8b0a7ef956f123eeb243011f2512f` (99) |
| `bothOutcomesNonIso_fwd_iff` | none | `a0ec048d206abf164e9db239e959a549e32b829f4a7c8314083ae2a69589f0ff` | `e7cfbc605a972017f15d224edc97b88db3c8b0a7ef956f123eeb243011f2512f` (99) |
| `bothOutcomesNonIso_iff_unlicensed` | Quot.sound, propext | `761c8df0adbdc3bdaba8517ba6d10d6fafee97f2dd5c74b04156c1be961c8d51` | `ea459fefabb619685e6c46a4fc1477b31d98c7168698dc050ec5faceaf933d07` (109) |
| `bothOutcomesNonIso_of_unlicensed` | Quot.sound, propext | `68074fc2e50c7a47832a8a9209ac7f096d2165ed6d2cff7a1ce0fe9e621c55ed` | `ea459fefabb619685e6c46a4fc1477b31d98c7168698dc050ec5faceaf933d07` (109) |
| `bug_transfer_needs_bad_compatibility` | none | `95f86229f7285750d3b1a21cba02fa884dd6109b5df53dad584ea27cbdfa4bd8` | `73af523f56362bf2291eeb4fdde668ff1867538e8c6099ee42d7b1dae75343d5` (14) |
| `bug_transfer_up_nonvacuous` | none | `e05c08408e28abb11edef9c10a922c39a98f25b43205573b91b6655f2665b3fd` | `9f029bc777f20bc7c146eca866f755f36876252bd886c8f04cbc30a7679ceb28` (14) |
| `bug_transfers_down_of_converse_simulation` | none | `5897d4eacb5ccb8976bed99385e4fce3a6c571763fd42bf7240a96451bedaa86` | `309918752c0f3215b497f71ed27f9c7503d727edc26ab2e35ece2003aff96750` (13) |
| `bug_transfers_up_of_forward_simulation` | none | `cfd85757bee771250b54ca019ea59853ff2b158a51b6bf925bfadf7e063eb082` | `309918752c0f3215b497f71ed27f9c7503d727edc26ab2e35ece2003aff96750` (13) |
| `cell_status` | Quot.sound, propext | `248153aab223f056dbf7694c8ea256940672c7d8de4a8196663b7bc725f7db9c` | `37b83992d457fc177ee20bcc21eea03b1416f1741e58a7145d0b1d83c6b1f907` (109) |
| `Cls` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Cls.Mem` | none | `b8d675502a84c9710b4de55c22d4bc206d2383c98a3d93ecd75ade3bc39a4404` | `05e811960355c91bd60c5b8ceac1324b1db110e57e70ff0d0d44a601d2183496` (17) |
| `Cls.test` | none | `76a4d2f233ed821c93a37a5de36dd23aed21596d0670fe74015918ff0b95915d` | `05e811960355c91bd60c5b8ceac1324b1db110e57e70ff0d0d44a601d2183496` (17) |
| `Cls.test_iff` | propext | `d9c6205529ecff4466c559cc3055b3dc6ffedd6ebc97e36576e87bbaaa68281a` | `3b553d98f59c9b365b9ac6238e43c69941c7e743f8c00a68f8cba48174ed750a` (78) |
| `cls_test_examples` | propext | `a61c63c49046e3dffdd1541585706ba0d784fa988e5ebd53eb6b2521421b8e79` | `b0bf5b5da723dbd189861976f42aec03506165d6a81f881fb29a46307e928b80` (45) |
| `collapse` | propext | `85b0cc2477a19c564aac40aa9023024e27cf08b462615d39d81775b419ddaba0` | `f013b07dfe1978bc5a0707be79722c4cfd25de1ccbd703c008afab50d0307ca3` (10) |
| `collapseTo1` | propext | `1c64383bad868ce68c0d4763b0ffbe436da448de624cdf2f68bb66e72253b564` | `a4dad95beb48231785cff3ad4c82fc50c4ea980f43d7fd4a723dd2bacbe9655e` (10) |
| `consistent_with_both_needs_model_satisfiable` | Quot.sound, propext | `2c1fb2ddb39e6cd725c0606bacd9b49704311bea032398960653ca0f66583380` | `96cfd94d7cd83c8fca385a93e87d5f61423cbcdf62ca4603dbc271cb24be33dd` (27) |
| `consistent_with_both_needs_system_not_valid` | Quot.sound, propext | `0011cd8fea83c368da716dbdaf44cbee2016e02591a4d2a14d328c073aaa4e21` | `96cfd94d7cd83c8fca385a93e87d5f61423cbcdf62ca4603dbc271cb24be33dd` (27) |
| `consistent_with_both_needs_system_satisfiable` | Quot.sound, propext | `593ef781bb709c62dc6021bc2466efd496a530053166f82a0ce15d92c8d1b3cd` | `96cfd94d7cd83c8fca385a93e87d5f61423cbcdf62ca4603dbc271cb24be33dd` (27) |
| `contra` | propext | `364749a860fdcb74a6ae74e9261055ee7a53ccbb6ad484bdbbd10b2397801c26` | `614a9c50d70973cf92e7ab3d8ad00e40c6d0698e4239c43e2ac4a9851f4c4116` (9) |
| `converse_simulation_needs_bad_compatibility` | none | `d7537b5058019d2f9c2874c4f89b0439bce0c73164bc85de36d82400067c01c0` | `73af523f56362bf2291eeb4fdde668ff1867538e8c6099ee42d7b1dae75343d5` (14) |
| `converse_simulation_needs_init` | none | `cca66692c8b8dcdbe549b7bd21460610b8181c5b2bbc935bd5430100538d4308` | `73af523f56362bf2291eeb4fdde668ff1867538e8c6099ee42d7b1dae75343d5` (14) |
| `converse_simulation_nonvacuous` | none | `a8a5315c84e266aab5ae9be7b18da97f41b55bad9be5a51fd5718578112b4ac4` | `9f029bc777f20bc7c146eca866f755f36876252bd886c8f04cbc30a7679ceb28` (14) |
| `Dir` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Dir.Transfer` | none | `077ac1fabc03338b15fa6b6afbb9abe273809cbd2725eee28a596058dc954f4b` | `66a8ee1974f3d1aa78e8f9047e304d7b59d8b502a9cd09f73c55bc44625706ba` (3) |
| `dir_transfer_examples` | none | `951a82c086597efd824075fa9b071471f3de91db75900c733c31434952e24eda` | `ee099b279f9ae1637b80f3b38358706ac890a0dcefe0810140081fffe0ec967e` (7) |
| `emptyStr` | none | `85b0afbfb804c31034943262f19e807975324867cb9b16dd421d1bbd5d9729e4` | `9beb07b05f5e7ceee218ed212519064cd609610026994226e03a83fc00c8481e` (2) |
| `emptyStr_example` | propext | `74bc27980ef8ab5de84dee2d7f62f37073b25bed468256bc91579adca5c962d0` | `e1c71c4c9c085c056fb608ff65d3663a68fa79e00384c62d1e55135d9f44b2ba` (29) |
| `Env.cons` | none | `99db90a930a1d5756973d67b2550450c1a78f06d35224c391063c9e854c79251` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `env1` | none | `58a717cfb6c7821e779524d85b04516f0e754926bb34942c135d2f13cb864174` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `env2` | none | `be8cc9b6b234a3a417e5d4cc6580c0377a02e1da37bed595967ef9d18acece44` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `env_cons_example` | propext | `f29a553c14cc5718f4b2f3708ec41cf871a0947de476d8870a2c207990663f67` | `d93ed930441487b86097edcbb171a5524251543154416e46f81add67c166c8e1` (3) |
| `eq01` | propext | `c1da11f6da1e1c33d7c9cca840dd315c1592783d5a142c4bb023bae7cd31ee27` | `614a9c50d70973cf92e7ab3d8ad00e40c6d0698e4239c43e2ac4a9851f4c4116` (9) |
| `eq_not_reflected_by_strongHom` | Quot.sound, propext | `2c66992bd5b221ee1a3f229cea41cb834483ca41697a8f6aaed5d8b8984ad342` | `1a5f4cfa6dde1ce936c8984392e71a933c627a2600cfcb1cb3cb390b93a9f7a3` (64) |
| `exAllR` | propext | `364749a860fdcb74a6ae74e9261055ee7a53ccbb6ad484bdbbd10b2397801c26` | `614a9c50d70973cf92e7ab3d8ad00e40c6d0698e4239c43e2ac4a9851f4c4116` (9) |
| `exclMid` | propext | `364749a860fdcb74a6ae74e9261055ee7a53ccbb6ad484bdbbd10b2397801c26` | `614a9c50d70973cf92e7ab3d8ad00e40c6d0698e4239c43e2ac4a9851f4c4116` (9) |
| `exExNeq` | propext | `364749a860fdcb74a6ae74e9261055ee7a53ccbb6ad484bdbbd10b2397801c26` | `614a9c50d70973cf92e7ab3d8ad00e40c6d0698e4239c43e2ac4a9851f4c4116` (9) |
| `exExNeq_not_preserved_by_strongHom` | Quot.sound, propext | `92cedfa621ce94861bde6e797f8cf8c070cefa6ef0c7738423d1711783666d74` | `533020e0df2ff79266309e69da813c5ed2a2e051a48ffb63c333708de183ec35` (60) |
| `exist_preserved_to_extension_nonvacuous` | Quot.sound, propext | `173214028fce77ae0d8a989fc4cd8de04099162d7e73c10b20231d2fb6dffe71` | `4898111ed572d8b20a5e6b0b69c02c73d6e8102e83264668861cac5fb57cc483` (51) |
| `exist_preserved_to_extension_of_embedding` | Quot.sound | `4e2297224ecd80031ac76cdb8c406ade2305f607b0e7faada4bd9535e3982aaf` | `07cdc6c914d37430aa8ce6edef6739e5992279963e7f3e7635da0a26b94de283` (38) |
| `exist_witness_transfers_along_model_embedding` | Quot.sound | `e84534b085840c9cb0b6ef6ef343683d6dba2d043417bd0df486dfe3cee3b1cc` | `7f3d251646b3ee0cb62ffd0960d14ce16afaf2ac94c386f6ce870fccc4dfb38e` (40) |
| `exNotP` | propext | `364749a860fdcb74a6ae74e9261055ee7a53ccbb6ad484bdbbd10b2397801c26` | `614a9c50d70973cf92e7ab3d8ad00e40c6d0698e4239c43e2ac4a9851f4c4116` (9) |
| `exNotP_not_preserved_by_hom` | Quot.sound, propext | `7b6df36003520e0628fb5db0e981e992dde1e775c2e3a96b929d191bd7df4186` | `1fa0433637761246b82df479af2d1f11129eea735236dc7ef5ec57c6270a2762` (74) |
| `exNotRxx` | propext | `364749a860fdcb74a6ae74e9261055ee7a53ccbb6ad484bdbbd10b2397801c26` | `614a9c50d70973cf92e7ab3d8ad00e40c6d0698e4239c43e2ac4a9851f4c4116` (9) |
| `exNotRxx_transfer_fails_without_reflR` | Quot.sound, propext | `c3eb1d7fa31ced1c474259eca3aa5699b34694553692c4958c9bf5283d1d9388` | `18c0db0a21db9706afa8e2e7f8a2cfb846540b28664f5f55f781e89f573b975d` (48) |
| `exP` | propext | `364749a860fdcb74a6ae74e9261055ee7a53ccbb6ad484bdbbd10b2397801c26` | `614a9c50d70973cf92e7ab3d8ad00e40c6d0698e4239c43e2ac4a9851f4c4116` (9) |
| `exP_not_preserved_to_substructure` | Quot.sound, propext | `e2c4e4933ece9706526e6e45081a6787080f2b27135b544f9bb89e76d693d0b7` | `a013864e6b174ea7e42d8eecb907e69d8a2a5c07600de6aabae3a9d67350a5b4` (75) |
| `exP_not_reflected_by_surjHom` | Quot.sound, propext | `c7df4fb3971aa733a7c68bd92e1336240718177f24606f5257e48c9cffc7003a` | `885598c0aa87f864806ccc106be17e7fb75172f37934b84cdff964a5e67a9582` (72) |
| `exP_transfer_fails_without_presP` | Quot.sound, propext | `0c7f438eb80339211ed91274a881dba55e0bd6035769572c4441a23306c3f72e` | `d8f5a5eed9e3151d0e8f1388d79c5a58230a3e1433fcfb8930bb1e2661c26b03` (63) |
| `exPAndExP` | propext | `364749a860fdcb74a6ae74e9261055ee7a53ccbb6ad484bdbbd10b2397801c26` | `614a9c50d70973cf92e7ab3d8ad00e40c6d0698e4239c43e2ac4a9851f4c4116` (9) |
| `exRxx` | propext | `364749a860fdcb74a6ae74e9261055ee7a53ccbb6ad484bdbbd10b2397801c26` | `614a9c50d70973cf92e7ab3d8ad00e40c6d0698e4239c43e2ac4a9851f4c4116` (9) |
| `exRxx_transfer_fails_without_presR` | Quot.sound, propext | `595bbde10051e1b7273c2959470af76ee8941e8d21d274a9a3b229652451d927` | `685e47a732af103a8fe387bf8aa69b7a9c9a8610ae96a927606a638a614dce1c` (63) |
| `exSelfEq` | propext | `364749a860fdcb74a6ae74e9261055ee7a53ccbb6ad484bdbbd10b2397801c26` | `614a9c50d70973cf92e7ab3d8ad00e40c6d0698e4239c43e2ac4a9851f4c4116` (9) |
| `exSelfEq_valid_iff_nonempty_carriers` | propext | `567f213f215e81a424a9d28d593bd8d05d044f323ae176fe1d22c6b198c42ad2` | `6195f2bdb66be3c2e5ff4aede7e81f8b9ddf7a60a14a0f050d2f963166583320` (28) |
| `falsity_licensed_where_truth_unlicensed_iff` | Classical.choice, Quot.sound, propext | `d235c6fd81990167296da5286f3aa0cbe9eb419ca9d5ef517a8eb3fc36e0be94` | `c177e182f12f7c2e143c0e584363669497660a2e29bdcc90dca1f1a88fdaa882` (99) |
| `FalsityLicensed` | none | `8ee0e61c755a8d8b410ddef83fe4b2b78d9c52c43b5227b5cb2be25aea1c624d` | `d89a0678af1b3a93120bf7501b8b969163b03b62033edd8c5fb5078bbaacb413` (16) |
| `falsityLicensed_examples` | Classical.choice, Quot.sound, propext | `7279a2422c03472c522be0cfafb80c03b1c7ca55f547c174e4031a628d2e3562` | `0f6dbdf89f83b350d51eb2863dd0e758bcdf900a62a9d6a1e4b824489fea2357` (98) |
| `falsityList` | none | `40bffe4ca27799f7ef8f7c4ea589d2c6f00cc428ffb53513f43ab340b19eba3f` | `d89a0678af1b3a93120bf7501b8b969163b03b62033edd8c5fb5078bbaacb413` (16) |
| `FinStr` | none | `9d3e5c159e7bd8d8fa6d9b48c99d7d17450f9751e4d83c0afeae73dd28cf2963` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `FinStr.toStr` | none | `0b93b54efd0d84555a6f54f0beb9f42b85010398d55c7c0f69e445e8276b285b` | `e9b4e400acce9c669b310c2ac4675678830b0b5a06e168f12a021c0ee1fd6fe2` (4) |
| `Fml` | none | `b498a83bffa811939db9bac842ed9cbfbf16318b6215d8cb89ef8de6e66b0605` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Fml.imp` | none | `ad3cd341ce4ef35ed95b9a77d8de220390803ed5deb5745fcc9db414668ebb7a` | `614a9c50d70973cf92e7ab3d8ad00e40c6d0698e4239c43e2ac4a9851f4c4116` (9) |
| `forward_simulation_needs_init` | none | `ce73b8339d025ae1a516c9728e341fd2c14ed4295e554d4e29cc201ea01ebba5` | `73af523f56362bf2291eeb4fdde668ff1867538e8c6099ee42d7b1dae75343d5` (14) |
| `forward_simulation_needs_step_matching` | none | `591eff6d0126225de92f1fce53a0bff1cd6d3a38b581cb39023aef07a9fa5344` | `1d6c31c6ca2c6736736d64818103d7b078e63d934d1e5a68da2b1cfba8d400a5` (15) |
| `forward_simulation_nonvacuous` | none | `9f8ef6c26df9517ede053865f0ff13fb42bdc2be2dfab8588e398c4538c586d6` | `3d08236a9e7d20ee5ca20b21ba2393db54bdef29631267f5f1af70a97e276f40` (15) |
| `functional_simulation_example` | none | `ee4e9e3a7e5d2e7837837ac051f16ae47bc0d1f44e6498479ab2c3d67e74cf54` | `3d08236a9e7d20ee5ca20b21ba2393db54bdef29631267f5f1af70a97e276f40` (15) |
| `inclCyc` | propext | `7c9947d0dfaba6430c6b39e9e33fb0d5e52529bd66d25c4207fc92d0c1a182dc` | `1bf0b27375726b363aae933a1ca2262ce909ae11900474fdc8bbe21612d55158` (10) |
| `inclE23` | none | `b2691510d1eea53023a2667256b9ce6a2b1c5a0e6d131938c2adbdb0a4cebcbe` | `7e0533717fb53b07eaca1d212ebfdd852d55367d505ec35c2787b7f5e4f14b09` (10) |
| `inclLoop` | propext | `dfbe2026cc8ec166d75517147aea799b1533574feb4b11519a485d3a8ca3e391` | `b5e3106d06d835515c7e39a1c5f945b43b7f0700368645766a7d3540b5197591` (10) |
| `inclN1` | propext | `cdc012effbf05867e0814bb38faf793d60944a0e50b6e3ac8139aa2ff0c0a58c` | `a4e3d1eca81058c55ed7d2b0189c9f34a3def183583f294987bf95eb5fb4292a` (10) |
| `inclNoLoop` | propext | `e86c566b519e4dd2f8a07d772e131ac59a93200221e305062e20b023540537eb` | `dbedd8e8eebb4025264626b686097abdbd17e20d74be0443528ac6e7587a3d91` (10) |
| `inclNP` | propext | `98ebf98e53535608c49f8de72283796fc8bf3f2caac7cbc0513f21e0dda89251` | `79909cbb96e9680ec7c08cdca92c16b12f72078386777859bbe21ebf7e875595` (10) |
| `inclP1` | propext | `dbfc1a2fc2c6ade1ec090483901edccbf6c770b044cfcefae140e6dc38cf862c` | `ff0960e94926809fca6e0f70c9cb0306c5eac0b433e22ad894f095ffbdc1c3f4` (10) |
| `inclPN` | propext | `ce351715d35bfe5760c6eae86a04f4586a6d1217d326f2ef0e19464d05dd5406` | `f6000e012932fe22be03c8ba1112047e432a689ef8faab3dd56ac205436d9d56` (10) |
| `inclPP` | propext | `f8cc6fc729a32642f20edd05b2433f27f1d3b712b5f48dd777012688bd6f01be` | `73516c22f7887fe8fa6748b88077c0d0147d33b25b0ff3b7d64b4e7e7c941fcf` (10) |
| `injective_hom_not_embedding_example` | none | `9cb73a4cae45b353197a732b27fea8357e7793428ef36dab296144524a9d3e22` | `6396d1ecf7ea77c1d0a6eec6f31730d1856005e4c3e4045af9ddfde36c84ed58` (21) |
| `invariant_transfer_needs_abstract_invariant` | none | `8c0a2708960ee3edcb45a20e4f56dd3dce1bdb929202d992cfcc68189de3b82f` | `73af523f56362bf2291eeb4fdde668ff1867538e8c6099ee42d7b1dae75343d5` (14) |
| `invariant_transfers_down_of_forward_simulation` | none | `45c6c325b65ad61fee655695aeda497c864b1c0a8183a220f741a13c635c234b` | `309918752c0f3215b497f71ed27f9c7503d727edc26ab2e35ece2003aff96750` (13) |
| `IsAE` | none | `13dff23805625dbd8604310f6c4f2d412da43e6d2a7fef30bb8e07a7c74ba0e6` | `614a9c50d70973cf92e7ab3d8ad00e40c6d0698e4239c43e2ac4a9851f4c4116` (9) |
| `isAE_examples` | propext | `93e2e9cb5b05e4e1b6da7e15e5c91aebc578be100f38533541b3d7971f01024d` | `56a7ea00f11288a93b5664922ceee43952ff64ca9ce3537d28453e82226f2290` (26) |
| `IsEA` | none | `13dff23805625dbd8604310f6c4f2d412da43e6d2a7fef30bb8e07a7c74ba0e6` | `614a9c50d70973cf92e7ab3d8ad00e40c6d0698e4239c43e2ac4a9851f4c4116` (9) |
| `isEA_examples` | propext | `2977c31d03e2239edb66f480a5d470f4bf8fc579321e13d5c12d34141a492978` | `f25cb1481403632d54a8ff8f2a13a68f11791d66f310e0ff61eea4e06e9862ce` (26) |
| `IsEmbedding` | none | `1e373025f9b3d871b35c6b6938aaf3c324c8023f77e6d6ec3f9ce8b927f21bab` | `55170613223aeae0f6d19abf0468c5eae833876691eb2d3edeba3e6ed82c7baa` (3) |
| `IsEmbedding.toStrongHom` | none | `fbc45cc11e60a4ba2e5d1228d3d06b47b694415295a8e269c52280a0ff551eb3` | `e200807c738e70d8b59e3b299ea0cc18fbe4bfbf689d59b6ba176fdd376efa45` (13) |
| `isEmbedding_examples` | propext | `323fd65f52589c12da75bcd5c0440d15be50a887d4f9cbc721a1025bcf0aefa9` | `5964803267bf52010d3fac93df8549a0351eccffeb9e65a60e2e503dbd4cf932` (23) |
| `isEmbedding_iff` | none | `7129926ae3833c94e6084db75953dff5cb131ce8e9972060f85b618a20b55dee` | `6462022c2e99e03d2173c965ee03037e66e6c077b29dfaa41507c44237a7d308` (11) |
| `IsEqFree` | none | `13dff23805625dbd8604310f6c4f2d412da43e6d2a7fef30bb8e07a7c74ba0e6` | `614a9c50d70973cf92e7ab3d8ad00e40c6d0698e4239c43e2ac4a9851f4c4116` (9) |
| `isEqFree_examples` | propext | `fae7fda362b44b6a0a232741a5825cbae186d3b8ccf511b2906b310197d4f9c5` | `72c437045810cd6bce0add290e1de1911a04e96565b8f1e09a4686717c23e3a0` (22) |
| `IsExist` | none | `13dff23805625dbd8604310f6c4f2d412da43e6d2a7fef30bb8e07a7c74ba0e6` | `614a9c50d70973cf92e7ab3d8ad00e40c6d0698e4239c43e2ac4a9851f4c4116` (9) |
| `isExist_examples` | propext | `b74394d9f793a85c2a19168ca8bd037b96e624f3dcb8a51f5f7eec6e99ae9724` | `a6f9431402e3bce0feb9476cb22dd498767bc697a2dec31723d2e87016062588` (26) |
| `IsHom` | none | `1e373025f9b3d871b35c6b6938aaf3c324c8023f77e6d6ec3f9ce8b927f21bab` | `55170613223aeae0f6d19abf0468c5eae833876691eb2d3edeba3e6ed82c7baa` (3) |
| `isHom_examples` | propext | `780c2caede3891ae2c5e638e1ac48c42633c688f4dcd380351d113f6e22be9ea` | `6351506806d3b82eda8172aac1272a2d594998ef507d64e8c258508a040e75d0` (20) |
| `IsIso` | none | `1e373025f9b3d871b35c6b6938aaf3c324c8023f77e6d6ec3f9ce8b927f21bab` | `55170613223aeae0f6d19abf0468c5eae833876691eb2d3edeba3e6ed82c7baa` (3) |
| `isIso_examples` | Quot.sound, propext | `e70385b1d94082ff5d8f19a0acb67fc366a08810a0909ac245bc0b97be086737` | `a6349dad1db0f1dda85804a7ed388c1097b4c698802aae464005374e277949c1` (24) |
| `isIso_iff` | none | `a91a94eb95191bfa83038ce456fca67b0955d05e99c0bc0621e58c1bf8d8ac7b` | `125e0d2d18bf3ad04321fe67c802943632aec9d711bad210161b4e4dffc059f4` (10) |
| `IsPos` | none | `13dff23805625dbd8604310f6c4f2d412da43e6d2a7fef30bb8e07a7c74ba0e6` | `614a9c50d70973cf92e7ab3d8ad00e40c6d0698e4239c43e2ac4a9851f4c4116` (9) |
| `isPos_examples` | propext | `ebf8a41a45d4b34808f0a09b194323e50a47799f99bc8f8c90ffb5ed6ee4c10a` | `9bbf428e72e1b6acbf8249ef7eed7a5372075257af944463a95e248b68c7c844` (21) |
| `IsPosExist` | none | `13dff23805625dbd8604310f6c4f2d412da43e6d2a7fef30bb8e07a7c74ba0e6` | `614a9c50d70973cf92e7ab3d8ad00e40c6d0698e4239c43e2ac4a9851f4c4116` (9) |
| `isPosExist_examples` | propext | `f2b2774441324c29001b9a3c49fc6fcc9aff0047f70300e1d11be35a97d916ee` | `97b59301c32827fe29ac1d78fc65988c501b6b66b77ecd778d1569c46874ecd3` (21) |
| `IsQF` | none | `13dff23805625dbd8604310f6c4f2d412da43e6d2a7fef30bb8e07a7c74ba0e6` | `614a9c50d70973cf92e7ab3d8ad00e40c6d0698e4239c43e2ac4a9851f4c4116` (9) |
| `isQF_examples` | propext | `fd6062ca83c4de74c07617954bc16f0fa2936556d21dc0b8b4571a6a26c3fab8` | `2a44d627a112d39a0392fb416ad0c46948c7671e14a7712833f1e874d35501f4` (20) |
| `IsStrongHom` | none | `1e373025f9b3d871b35c6b6938aaf3c324c8023f77e6d6ec3f9ce8b927f21bab` | `55170613223aeae0f6d19abf0468c5eae833876691eb2d3edeba3e6ed82c7baa` (3) |
| `IsStrongHom.toHom` | none | `892fcac2377cedc4d5ed77cc03b17320d93f5c459b85b929b442444e39e3cbe3` | `936fb46712b201d4df57a28ecc8159624b93bc9187182cd714e45cd11cdc87e9` (13) |
| `isStrongHom_examples` | propext | `0810f5348e288386858d67d9ed786c9f3ad14819501c2aa6bff96dd622ff94d3` | `738ebeeb838dc2943a90cbe9435ff8a1e586c998cd4f35d9dfe585dd092dcb85` (22) |
| `IsSurjHom` | none | `1e373025f9b3d871b35c6b6938aaf3c324c8023f77e6d6ec3f9ce8b927f21bab` | `55170613223aeae0f6d19abf0468c5eae833876691eb2d3edeba3e6ed82c7baa` (3) |
| `IsSurjHom.toHom` | none | `e739fb3a0900a917c8f3bdf19956dc8856e5f4b5b66637ea5b0c771306b5df0a` | `e6f29c1d5a0f2a329587726dc25cc7edbf4a2de2676bb072cae17f90b563eeee` (11) |
| `isSurjHom_examples` | Quot.sound, propext | `10ba8b05be749a87abe841d246a2602371e20a030a73de51a98c73524f721306` | `0f0b657e4156bcddce8ff05cec335232c855f67cfa1f4928fdd9611e42560835` (21) |
| `isSurjHom_iff` | none | `7576254ea0fd7717bd41006e58517c5d79ff8d2b360983862251c649aa228e40` | `3780a12efdb0947af0e004d65227257855632dbeb13469e3b2ef2a6ed870f1cd` (9) |
| `IsUniv` | none | `13dff23805625dbd8604310f6c4f2d412da43e6d2a7fef30bb8e07a7c74ba0e6` | `614a9c50d70973cf92e7ab3d8ad00e40c6d0698e4239c43e2ac4a9851f4c4116` (9) |
| `isUniv_examples` | propext | `6b58bd22208cba68b2c7b84f9a934a367057b932c640308cce102af26b870449` | `91e9f1e59f9c331d97ab24e16491ea92fadaea73a570b38311dca004b37b98a4` (25) |
| `licences_exact` | Classical.choice, Quot.sound, propext | `c80db045adb9a63469e7ed35f0e45805ad2fadf8ee61b90835ec5372b23cfe41` | `29afdcefd2485ecdad07e5d31436d48fcce916eb5a3fc51a63826f91c62331f0` (102) |
| `licensed_cells_nonvacuous` | Quot.sound, propext | `2e042c266fe4c6e95a6e6dc98ee574bb4f9b9871e795ed0666e0cdb2fe360aee` | `990683f1741ce72c7d51d2cb1599a8c113f0a22428f00027535d4ebd486b5cc6` (118) |
| `licensedB` | propext | `03059f39a4c39d5514fee62d38f7b5cdd9d6d7b0026333ed0d22234c579bff8b` | `7ad5717e1655e6a8703fa09758238cd55fae6c5d98777bd6467fe749000ca7c2` (16) |
| `licensedB_eq_true_iff` | propext | `cf78eacdf1bb45acf9ac5ab1eea586b80fcaca1334de630ae60ef908b00bcd1f` | `1c8e18e9f9bd2d58a547e1a555b772c528e8213b8d0d5dda9a105567632912ac` (32) |
| `licensedB_examples` | propext | `33cd3a91d387787f9e270a293a8ffedaba61961808f8f8c467ae1af3fb429289` | `1c8e18e9f9bd2d58a547e1a555b772c528e8213b8d0d5dda9a105567632912ac` (32) |
| `licensedB_iff` | Quot.sound, propext | `23f9331cc46954aca948b48586b3873b26d09a20e4e40367af1b2a730d0afe6d` | `37b83992d457fc177ee20bcc21eea03b1416f1741e58a7145d0b1d83c6b1f907` (109) |
| `licensedB_iff_preservesSent_needs_ne_qf` | propext | `bc03949ce68e92cd778cdf731cef5fac53cff0a34c7a03fef26009006141a00b` | `63812a55b2fd61be85a6ed77e5f3e5fdd3fd5adc2cc86f4dc7617e9df0b7b039` (110) |
| `licensedB_iff_preservesSent_of_ne_qf` | Quot.sound, propext | `ac5ac51b4032d3151a5ce79fd592315f32236c9664fae5a9c05d77bc72b29068` | `63812a55b2fd61be85a6ed77e5f3e5fdd3fd5adc2cc86f4dc7617e9df0b7b039` (110) |
| `licensedForB` | propext | `393d08dcfec07196bb18ad025da2f67bd51ed5258c1541f54fb339fe84939517` | `0b131be678808e9ad1276b3bcf3ad57891a043dd710ea5a210e58adb59036417` (17) |
| `licensedForB_examples` | propext | `0588bbb5a75a560a453a566ae70c041a26bbb404e12f2027f0923ea470037295` | `d93ffadd1d2171265834558f511222ecbe1a99554a71294b3f1d584fd52e3617` (70) |
| `licensedForB_incomplete` | Classical.choice, Quot.sound, propext | `7ac8c00e135eecbfc7c39f11110adfae739c76d61de74e410866a26e3439a255` | `b0478ef3628dad2544c1545789f92c011dab717302bd0bcef491708ceae828c8` (83) |
| `lockstep_nonvacuous` | none | `faf9fd3ff9c45b7649ee0577eb93620e879f7a1348d5f2e05711a9ee30aeb703` | `871188c6b46ca1c621dc5c48d01b43a1e0b33391b6e197a6a18da889856aea69` (13) |
| `lockstep_termination_transfer_is_about_reachable_states` | none | `a7d51f26c60dadb991ad992cbe22b2c4836f7f6ae99dd2004780503d82ae9263` | `094a3e9d1cdee2626504d1cc6d460283164d396f70d4045adc31427839c40481` (14) |
| `lowerP` | none | `baa2ddfdcd1044ec2f4037ab3d4c61ce8a1d2bcf90b16228ae52e68a641a0eff` | `c7a8e96916a52a65486f66923f53757876f882e2f2e0e80e545cfbe24b2b3fe1` (10) |
| `lowerR` | none | `46b2a6bb4773b657a7ec0a42ab16cf515fafaa73a7b043f07f46088bae085981` | `e4c6d6facfed4a843dd88801c4238dab254233d24baeb40c5861e8a9172091c2` (10) |
| `MapKind` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `MapKind.Holds` | none | `ec18b4c3115f82113704e23e193b716d416983ed91b81b49863ddb22105771b5` | `45a733e9bf7235051e7a4e4f4f58f9427269f58d70cc0af6b04ee6f233c3c202` (8) |
| `MapKind.holds_id` | none | `27d50f11e2b31194d5f4ec3be222f9348a9065845a2384b2c327f7c812f790ce` | `96b29e507161c44924610447961dc38399a1f10f3872a37a15cd46115af17564` (26) |
| `mapKind_holds_examples` | Quot.sound, propext | `575c4acf9a03a6843361b794442ab6a6edfe20a7456c7901ce216e74d52afc51` | `c1e8d11d2d6f4aa2622d33ba5d375b40b048c200473125f653cde1edd48d7fbc` (35) |
| `model_counterexample_may_be_spurious_in_model_extension` | Quot.sound, propext | `1219310ff4f1fbe1a9ecb76fd532acaa454561733b8072339d875f8a1d2b3d94` | `cd75294fd727280bf4981cfcdbeaaadc9e004ef2a4a458dd3f93fa0fc79b3b88` (51) |
| `model_embeds_into_system_nonvacuous` | Quot.sound, propext | `1354a8766817dd35c6615197d6b75f79bb04492cb5fe313b229312ffa20273ba` | `2682bd70f96820a2d2910a66057b62c0dac2471375323d44dcdb37de904dfc73` (58) |
| `model_witness_may_be_spurious_in_model_extension` | Quot.sound, propext | `52e8c7afebb6a46e0aca77e08a79aea0d081015b464d667fde1a5afc4fb91de2` | `672f5bfa1afc2486534e36c52ebaf6ff789c43d0423337782ee3fdf783bb7d5b` (51) |
| `narrow_scope_readings_differ_from_unrelated_transfer` | Quot.sound, propext | `44ff1ba5a4aa29cc699c134f7cbf120ba0a2b7f753d38c141e0cccf4e8fe74a8` | `8da4e137aff6a5dc913c0b74f4620e89151908784d14bda5ed5020412e89e0f6` (29) |
| `neq01` | propext | `c1da11f6da1e1c33d7c9cca840dd315c1592783d5a142c4bb023bae7cd31ee27` | `614a9c50d70973cf92e7ab3d8ad00e40c6d0698e4239c43e2ac4a9851f4c4116` (9) |
| `neq_not_preserved_by_strongHom` | Quot.sound, propext | `d518840b88463456bad8bfb9b76d61eb01c1616e629c37e3b77628d3410d5bc7` | `dff4919ed6ea06fc549a3c6f60a87e7a4b3a0c6f232b3fe802bf621453bc7839` (49) |
| `no_qf_sentences` | none | `07d374cd5eccbeadd98cbffe0d9f5a45e3af9758a188d3371174e3f218e3f2aa` | `9a8518c9b7dde768309d416f5a4debe4edd7ffc5dd9ad3805617b8d7c771c338` (16) |
| `notP0` | propext | `6c4b204fcb0774c5f4967f065ef5d0496fedae915388dfbdb5d2d62f60d72cb8` | `614a9c50d70973cf92e7ab3d8ad00e40c6d0698e4239c43e2ac4a9851f4c4116` (9) |
| `notP0_not_preserved_by_surjHom` | Quot.sound, propext | `bf0aa1988d29734769df426cc73379d508ad61579b067b75786a608535ace873` | `a40be3f8fe0127e3a5a1a983c273151ce6a4fcc509546f4493bf061845e64e08` (46) |
| `Orient` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `P0` | propext | `6c4b204fcb0774c5f4967f065ef5d0496fedae915388dfbdb5d2d62f60d72cb8` | `614a9c50d70973cf92e7ab3d8ad00e40c6d0698e4239c43e2ac4a9851f4c4116` (9) |
| `P0_not_reflected_by_surjHom` | Quot.sound, propext | `b6a680c3ff43a4c4f368e3cdcb8da7b9f2eeb162b3d7a85b746631c61ced8a70` | `2774f568e7135c4e06541a4d433f437a9157bd19c326fe89468cd6fd96d0e102` (73) |
| `pos_holds_in_full_one_point` | propext | `450952fb9113934db61898796a7b3f60ec719c2ac0a5e52a8a41b4227ddf1640` | `df52dda28e5d54e8fc2f3fa5985d5e782d1330d70f45eaaab2804eeea401e40b` (38) |
| `pos_preserved_forward_nonvacuous` | Quot.sound, propext | `dee6b1e6b78f0aff46d721e9ee5e9db3bf8d7bf672b0db08b492f00ad497d09d` | `7d6b13cd5c91ef0f23d1209c639ac1ef259f17d2252e7e01c7374617fd5d2882` (53) |
| `pos_preserved_forward_of_surjHom` | Quot.sound | `147714df0676d9d5ecffce9db835f33dedd4509804d3e02e4e93e400ec9787f5` | `a377517b0b12b0e82c0e0d321d72893973847c438d94a173e6d722a3e2336e06` (34) |
| `posExist_not_subset_exist` | propext | `81ebca5e302cdeaa8e6f2968b84bb5e70b93e2fae47e2d416601508412147567` | `75eccc56d3f5351cbfca2bb1ae6a4777095d544596d945df4bbd502c8c21422b` (37) |
| `posExist_preserved_forward_nonvacuous` | Quot.sound, propext | `22a778b0bf26432b6078b3312c85a1fb0ddefc0629d3c2efa8eafe5956bbdf11` | `2199a2f15d5b45b9aeaa47778c37e38af9fe2475918faf898ad2b0d43cd036f2` (45) |
| `posExist_preserved_forward_of_hom` | Quot.sound | `ddec5b042a9ac0629c2a2f10b1080c002450faba6b80a66a7283db63e78ccb3f` | `9924b4d63a88d7dcd6d3578cb89ee8707d6f6d47248124f547ec9eddabf91a8b` (33) |
| `Preserves` | none | `a556d5110ed6bdd30eafb789d34773a803348ba186ae09ae86e74f681edbdb91` | `7ad5717e1655e6a8703fa09758238cd55fae6c5d98777bd6467fe749000ca7c2` (16) |
| `Preserves.toSent` | Quot.sound, propext | `d8beff95fbdc8b5a767052f42c8f1959e100150c2fa9a13bf6d73c0896e0fc22` | `abcb818a91ca9d3bb110b685046098f655132d1a16830ae4bc703753f275b168` (101) |
| `preserves_bwd_iff` | none | `d1691414e6c345d8a2734be90b92f784c8347222099c5985dc769b15fa578b3e` | `69649c270d2a58d1a8f7964265362fb584bd4d292401b2cdf85bd4df59cab8bf` (99) |
| `preserves_examples` | Quot.sound, propext | `1c579f8919b81684474b6122d21854758b346a1e5d21c5cf4903479c75c8c30b` | `69649c270d2a58d1a8f7964265362fb584bd4d292401b2cdf85bd4df59cab8bf` (99) |
| `preserves_exist_emb_fwd` | Quot.sound | `928ab2913311307537cf6e9fef9052486893d4a3db43239463406919fa2f2657` | `69649c270d2a58d1a8f7964265362fb584bd4d292401b2cdf85bd4df59cab8bf` (99) |
| `preserves_fwd_iff` | none | `b3c542c281b1a8988f83f7ea54cfe8df14eece6d4166930d3621f52ff3314336` | `69649c270d2a58d1a8f7964265362fb584bd4d292401b2cdf85bd4df59cab8bf` (99) |
| `preserves_pos_surj_fwd` | Quot.sound | `0f39e44ab8995f1a41a589b9bbd698ffca48385401786cabc000dde88343ec4c` | `69649c270d2a58d1a8f7964265362fb584bd4d292401b2cdf85bd4df59cab8bf` (99) |
| `preserves_posExist_fwd` | Quot.sound | `0bbd3649906a931ad8c3f599dd7c6e8f7557bc88c0ce043e31e4a7497b36abb2` | `69649c270d2a58d1a8f7964265362fb584bd4d292401b2cdf85bd4df59cab8bf` (99) |
| `preserves_qf_emb` | none | `352806983ed58422b7ef756652d0fd0d0da4fcb80fd827a2ca7af144272760cd` | `69649c270d2a58d1a8f7964265362fb584bd4d292401b2cdf85bd4df59cab8bf` (99) |
| `preserves_univ_emb_bwd` | Quot.sound | `56bc7f54911023d62ede5de5503478c6c1337fd2236161d31fba99ade98bb69c` | `69649c270d2a58d1a8f7964265362fb584bd4d292401b2cdf85bd4df59cab8bf` (99) |
| `PreservesP` | none | `1e373025f9b3d871b35c6b6938aaf3c324c8023f77e6d6ec3f9ce8b927f21bab` | `55170613223aeae0f6d19abf0468c5eae833876691eb2d3edeba3e6ed82c7baa` (3) |
| `preservesP_examples` | none | `d9d9459c97d2b211bb74133d20950416c8fd59df4f873da4b109a1e5cfe10aa4` | `07a7c22e60e1f016381dca1bd15959bfdd39b2e97fd14f7433b3d2a77cc08b4d` (14) |
| `PreservesR` | none | `1e373025f9b3d871b35c6b6938aaf3c324c8023f77e6d6ec3f9ce8b927f21bab` | `55170613223aeae0f6d19abf0468c5eae833876691eb2d3edeba3e6ed82c7baa` (3) |
| `preservesR_examples` | propext | `3953e83b8a13011544c6d7c61d2fb691c08d77ea3e71d4df8dd128b17df5e1c9` | `26fa931956ec36a893c01939cab2f6bfed121c9cf910e8133ca1a31194250cfd` (16) |
| `PreservesSent` | none | `a556d5110ed6bdd30eafb789d34773a803348ba186ae09ae86e74f681edbdb91` | `7ad5717e1655e6a8703fa09758238cd55fae6c5d98777bd6467fe749000ca7c2` (16) |
| `preservesSent_examples` | Quot.sound, propext | `8c5f983210dd68cf9f0e0934f398c70f56d630e9cddefa6b39a08985b7469181` | `0761cb200987a70c4529dab21d9197839d070f989bd504254250f5a011446aa9` (100) |
| `preservesSent_qf` | none | `954584b295e8524d85351374ab0d4a8cbece4c77d1305e2fe2a23b2e54d06d61` | `0761cb200987a70c4529dab21d9197839d070f989bd504254250f5a011446aa9` (100) |
| `qf_sat_iff_of_embedding_laws` | none | `b774fac3cfb28f97554946678077fe61663b2d76ae017d44038987f84ed6caf2` | `5b2ca3fb75211710dadd91dd4d6bccc29ddfa14fcdccbec14d90a1c8848106ee` (35) |
| `qf_sat_iff_of_strongHom_of_eqFree` | none | `7efa5eca37d43b5c6b588b6e70a14d40ffec2e332450d0fbdbf2b1ebc1c3e286` | `717ff1118bd0d6534fd7797f719d4565a0f59bc0c6b4e701364975b686224ede` (43) |
| `raiseP` | none | `e91a3b9d1c377e1f93fd3a3cc27813bb09e5b604c1b139f685156b420b537a92` | `c7a8e96916a52a65486f66923f53757876f882e2f2e0e80e545cfbe24b2b3fe1` (10) |
| `raiseR` | none | `024666b30c7475e7d47cbc28cebdfcdcd5d99b8bb251ff66d98de114963ed4bc` | `e4c6d6facfed4a843dd88801c4238dab254233d24baeb40c5861e8a9172091c2` (10) |
| `Reach` | none | `e8af3018a7f4c8a075ecaecf455c4d6db16a1fa7d69ee31061a5d7162579f9fd` | `631230881b753d8abd2fed12e445358b09b73218ff74c0de88e75bd3e00677ab` (3) |
| `reach_examples` | none | `0ed8cfcdea5815786c2d1ed8a270f3e1d2a988029985143b4dfd7b518b6c4672` | `a0ae0b0f74ba2be9f2eebeec929576548eab3fd98daea8d156cd9b54a281b0b9` (10) |
| `reach_related_of_forward_simulation` | none | `c31109bf58728cc737299a7238c0d0fc1c574bc18bccff2d5afbab118eb42861` | `309918752c0f3215b497f71ed27f9c7503d727edc26ab2e35ece2003aff96750` (13) |
| `reach_restricted_simulation_gives_strong_pullback` | none | `b40644d9fe5e3cefda18bcf17fb6577eb5e8c5b39d51a8a1569909e8f0fc2e6c` | `309918752c0f3215b497f71ed27f9c7503d727edc26ab2e35ece2003aff96750` (13) |
| `reach_restriction_repairs_strong_pullback_countermodel` | none | `2dce2128dc1cc2fbc341366200b479bec861362470689e8680cfb92d66e15a75` | `81308fc03468961447272eeb55780bc75c446162a7e8c0b8b5c95f8c20007c72` (9) |
| `ReflectsP` | none | `1e373025f9b3d871b35c6b6938aaf3c324c8023f77e6d6ec3f9ce8b927f21bab` | `55170613223aeae0f6d19abf0468c5eae833876691eb2d3edeba3e6ed82c7baa` (3) |
| `reflectsP_examples` | propext | `71f14a97f24b81fc1efa81a667e0bf4b574193c011fe10dcf55330cd48354757` | `1021a0e6d871cbc44c39507a54bd4988198901f42b2f3da57f6391a6678611b8` (16) |
| `ReflectsR` | none | `1e373025f9b3d871b35c6b6938aaf3c324c8023f77e6d6ec3f9ce8b927f21bab` | `55170613223aeae0f6d19abf0468c5eae833876691eb2d3edeba3e6ed82c7baa` (3) |
| `reflectsR_examples` | propext | `1a3003faa8409702c9fc2176ce9d44e717d4df07e8ceb3a592b7cade0292299b` | `fb03b5547be772aef80ac7ec9b6466abe00c65875ca39cf6da4bc73daec91ac3` (16) |
| `relHaltTwoStep` | none | `3e97bb315dfaf623b03a8fa7ccd321c245912857f20e007b3602c30d9232705a` | `ce478e7bbae4d624ab4c77669fa0b24c67052928b974257c7cd30e383b36806a` (5) |
| `relSameIndex` | propext | `87b6c8931ecea5ebbbc86e3f6dd67520fb28050d6922cfaf2eff78fb4115a3be` | `de219230c10d99db05e221f21637cb7dff9566085d399e628d2bf3165056936d` (7) |
| `S1Full` | none | `09a9ddf55250906fc32d6ba28cf90e96045cd6f269806ff7a936e819ac7f203c` | `ad43ae50d817f6379ddd4fbd6760483c9324985cbae75d03444276765721329f` (2) |
| `S1N` | none | `09a9ddf55250906fc32d6ba28cf90e96045cd6f269806ff7a936e819ac7f203c` | `ad43ae50d817f6379ddd4fbd6760483c9324985cbae75d03444276765721329f` (2) |
| `S1P` | none | `09a9ddf55250906fc32d6ba28cf90e96045cd6f269806ff7a936e819ac7f203c` | `ad43ae50d817f6379ddd4fbd6760483c9324985cbae75d03444276765721329f` (2) |
| `S1R` | none | `09a9ddf55250906fc32d6ba28cf90e96045cd6f269806ff7a936e819ac7f203c` | `ad43ae50d817f6379ddd4fbd6760483c9324985cbae75d03444276765721329f` (2) |
| `S2Cyc` | none | `66d5e4f3439c197ad061c6a80ed266a0ff9496783e43412fbeba2105a20eacba` | `ad43ae50d817f6379ddd4fbd6760483c9324985cbae75d03444276765721329f` (2) |
| `S2E` | none | `66d5e4f3439c197ad061c6a80ed266a0ff9496783e43412fbeba2105a20eacba` | `ad43ae50d817f6379ddd4fbd6760483c9324985cbae75d03444276765721329f` (2) |
| `S2Loop1` | none | `66d5e4f3439c197ad061c6a80ed266a0ff9496783e43412fbeba2105a20eacba` | `ad43ae50d817f6379ddd4fbd6760483c9324985cbae75d03444276765721329f` (2) |
| `S2NP` | none | `66d5e4f3439c197ad061c6a80ed266a0ff9496783e43412fbeba2105a20eacba` | `ad43ae50d817f6379ddd4fbd6760483c9324985cbae75d03444276765721329f` (2) |
| `S2PN` | none | `66d5e4f3439c197ad061c6a80ed266a0ff9496783e43412fbeba2105a20eacba` | `ad43ae50d817f6379ddd4fbd6760483c9324985cbae75d03444276765721329f` (2) |
| `S2PP` | none | `66d5e4f3439c197ad061c6a80ed266a0ff9496783e43412fbeba2105a20eacba` | `ad43ae50d817f6379ddd4fbd6760483c9324985cbae75d03444276765721329f` (2) |
| `S2R01` | none | `66d5e4f3439c197ad061c6a80ed266a0ff9496783e43412fbeba2105a20eacba` | `ad43ae50d817f6379ddd4fbd6760483c9324985cbae75d03444276765721329f` (2) |
| `S3E` | none | `515b608c8fe0a751f444073178581bc31ae2a25904255948a33f9d5cfc1fd88c` | `ad43ae50d817f6379ddd4fbd6760483c9324985cbae75d03444276765721329f` (2) |
| `Sat` | none | `5e2602b990a28493486dd981aa8639cd63beb548136106b145a0f2d7d84434c8` | `01f0fcd20f33c1ee99eb24943f03a8cdc25de8cfbac0d6deb00195eac1024664` (12) |
| `sat_neg_example` | Quot.sound, propext | `02bd96dd43b34824fec2b9cd9e3f263fff0636a3a1f10271c491497cb6aff38c` | `cc2ab10a72514ebe2ddb1030876b2df18a3680d9c14b796b1c43e56a199c322f` (32) |
| `sat_pos_example` | Quot.sound, propext | `25b8e85e5b6ba2cf034d2733cf25626475856fa0d896363e0be9828b79ce303a` | `ecc953f19b4dfdbdddfe673a5d6503603d77c3ae2efff22c23efce18102ea73c` (32) |
| `SatS` | none | `df1ed8a2ce69d630e39128f467dce6407d73b7836cff201f459c657f2434e456` | `91727f2a28b6f061623db4f433c8d5d2e92a8d44680acf4038776835d9dcab51` (11) |
| `satS_neg_example` | Quot.sound, propext | `9855b0d17bdbe0df92e657a317a2f56df7d9bbebe459affe4067e11ca9347dd3` | `98080af2990cab08181e3278276f18cb597bd8fd3f980b8c0ec4d7917050e300` (33) |
| `satS_pos_example` | Quot.sound, propext | `c863587d7f0c72bf21f5a420cb5089128be764904523cd057ee0378c808286c8` | `6fd2ad0b3bc726ea192ac4f39e6f359139e25b7e281f82cd491700e615705dde` (33) |
| `SimInit` | none | `7d0e2e63ebb938046e4b496df68214d14f530c1a69cb3a9178cf52ec95ea2e20` | `631230881b753d8abd2fed12e445358b09b73218ff74c0de88e75bd3e00677ab` (3) |
| `simInit_examples` | none | `ffd09a4caa89e4c0f5b675c735b904297f9f9723cae7bafd1dc5358f89436269` | `e50c72a80f56683c1668fc1090b974aa6ae30ca43e802c8076940bb441ef56fa` (7) |
| `SimStepLock` | none | `7d0e2e63ebb938046e4b496df68214d14f530c1a69cb3a9178cf52ec95ea2e20` | `631230881b753d8abd2fed12e445358b09b73218ff74c0de88e75bd3e00677ab` (3) |
| `SimStepLock.toStar` | none | `e93a37930ea290d3e336d0ac3f4b26630b269a3c69b5886693ea8f4bab0c1bd1` | `b6dbcd325f0f4970c224ad70ba12f6ca4d140be91ffe167cd86aa919b7891ff6` (9) |
| `simStepLock_examples` | none | `342a712f9b38bf6049e1f4f21fd9be4983dc98a65bfeda5ab3262f52abf2e208` | `c9ceea4ab87f7bed551cc6715421807d5bf5ca7314f482c04b7c3fb18378bc2c` (8) |
| `SimStepStar` | none | `7d0e2e63ebb938046e4b496df68214d14f530c1a69cb3a9178cf52ec95ea2e20` | `631230881b753d8abd2fed12e445358b09b73218ff74c0de88e75bd3e00677ab` (3) |
| `simStepStar_examples` | none | `c78c1f5154af158d8cd2814e97fb2dc378d6583ebe3f6a2c512c83f1bf47eae2` | `35f51ab262377b9cdc29be41fdf8a71b15cc939a3bb491e55af4922ddecc7541` (11) |
| `SimStepStutter` | none | `7d0e2e63ebb938046e4b496df68214d14f530c1a69cb3a9178cf52ec95ea2e20` | `631230881b753d8abd2fed12e445358b09b73218ff74c0de88e75bd3e00677ab` (3) |
| `SimStepStutter.toStar` | none | `9c8783df11ee539aac795e1b3003b5cbd6d28bdf572d66fc4cf0f44378b1c536` | `8da9a0823f6cb3ff25462cf3489a62925c022f90179a9153a5e72751485dec31` (9) |
| `simStepStutter_examples` | none | `b2801738d345fa56e9b23cffd21d76feb07fa0c64189ac290de55a38ef534c24` | `202c6a68d7443dc1d745bb8c68cd16cf3a4d91b9fddd0eb74ba87f804d3b0859` (9) |
| `SimStepWF` | none | `387dcc4a9b3dfb2ea03295e69dd0e55edd97db9417fffdcb9dfdb868da5ea51e` | `631230881b753d8abd2fed12e445358b09b73218ff74c0de88e75bd3e00677ab` (3) |
| `SimStepWF.toStutter` | none | `c0a7e2922420a2a3429e62a40052fcc6c29c5fd50818e4fd3f35571c36b9ba2b` | `b365a16f295a97868d9a0f2d80f2af85204a40f6cfcd69a108c9002275f8760e` (6) |
| `simStepWF_examples` | none | `0048cd53a2e2d66b919270c4184d3f0430e242467f7ff818bfacc23b0472e69a` | `5ec1d1d1af7a939fd1ec6da21e3664406e05ff16077e00406885da08085494d5` (9) |
| `simStepWF_iff` | none | `ed3b63eb8c9cb3bc7469697b81ea390302fba24f024ff48d1b0664712072ea87` | `f493677f9df85e63cdb496f493067521d9cc99d632601b32d8e3ba3fbb6c40ef` (5) |
| `spurious_abstract_counterexample` | none | `ee50bda949c76c2244847f5cd78d5115c5fd1b846fff72df69febda77a328507` | `5e8f9b072fc285f72200c905143a7185ea086be290efd23224ff7a6337cbf606` (18) |
| `squashP` | propext | `1e3fb3c67a0264fcd2bb340f69fa2e8d5a96fab8ee401d76b63c04fdd273b29a` | `ff0960e94926809fca6e0f70c9cb0306c5eac0b433e22ad894f095ffbdc1c3f4` (10) |
| `squashPP` | propext | `f0788f81622d80562d5ec208b4859442f6a1b981ae8ddbbe73339254ca936586` | `73516c22f7887fe8fa6748b88077c0d0147d33b25b0ff3b7d64b4e7e7c941fcf` (10) |
| `Star` | none | `8ba4445f5329daa638cb5d39d9720188603d0e522b12f445701e440d6d1c90bd` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `star_examples` | none | `0e055a78f7e72dff3f4e9f0bbb104549440fd2d389aadeeb28ea21dde5b1b585` | `d566bb8d7878e0a6b670f8dc791372af29860c72c68de5da6a9c476342fbbd57` (9) |
| `Str` | none | `8c2dfcd107aac381cf7fdb44dab35e922e30295bb40e848486da26728ca08152` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `strong_pullback_fails_with_unreachable_related_state` | none | `af8d661e2179afe349f93c0fd6a7c464cb7cb670c7347f050e4d1edb2b1edf87` | `d48c523702a7456620794e7ec36942fc97789cd1b147cb082e36f04f52c056e2` (15) |
| `strong_pullback_of_functional_simulation` | none | `0d0aa045c6519f5a89696221ede3826ad56ffe9804ead99a9d6fa4cf56efe6d0` | `309918752c0f3215b497f71ed27f9c7503d727edc26ab2e35ece2003aff96750` (13) |
| `stuttering_countermodel_admits_no_wf_measure` | none | `8ce9324f7f86790d7c811f8fbeefba06788b8394d396e2d1649141981ce11e40` | `0d6b0b7c67db975ee35f2499d5e60c043ae57499fa7ef74a02683c8c0332c280` (7) |
| `stuttering_simulation_does_not_transfer_termination` | none | `64841ac39114c8db5defca513ea9724ddb45f45e737312af974858bfb1369c58` | `8712fd092d9c87d7a18475bd8dc92c9518d22a8b03c5c7cf6b4723666960a2b1` (19) |
| `Terminates` | none | `a4588a7bd434480f33b31131a10422378684e5e990b05ab8ad7b24131dc3b0eb` | `631230881b753d8abd2fed12e445358b09b73218ff74c0de88e75bd3e00677ab` (3) |
| `Terminates.no_infinite_run` | none | `553dc9464e6215c8633cbc78232f97f924e2d56c50a4983b2f678f7c8394e6d3` | `e598e4fee845aeab2a65f4ca3ad8d5ed3a122e11a3838f580f0b05da5ff4f071` (5) |
| `terminates_examples` | none | `41c9bc86e82958bcee1e958c82c233d91e9cf1dbcaa7ad59edf0a109f4e63c88` | `38287598a197160572e76d580ed400f5e141008e86f3753b421d9d554cf51a90` (7) |
| `terminates_iff_no_infinite_run` | Classical.choice, Quot.sound, propext | `f8aee712522cb632c854db4a9e17c2f3b136fb2b60c6d430d57917d942790325` | `e598e4fee845aeab2a65f4ca3ad8d5ed3a122e11a3838f580f0b05da5ff4f071` (5) |
| `termination_transfer_needs_abstract_termination` | none | `93873f054f4d1f8749567611be6db87105a1331b445e975f9da511d964e7ea8a` | `a16886d16da11f2016279392fb42a13d5e6ea9bc6cb371bc92f5c99d092c8524` (14) |
| `termination_transfer_needs_init` | none | `02cafedd5e22bfc7badaa8754d39a91504ab4aaf35fe7b82384aca5deac661ca` | `acfc6f42799e8b56be9d04dd3eb6218503ffcb4618855f1b653797da1ac9855a` (15) |
| `transfer_of_licensedForB` | Quot.sound, propext | `c43cba711b2657b9cb6b8c54d2ce4306bfeb679f5ec1ddd285b6a9d88b3bfe94` | `a79588f3e5a34ac389566e43f0a8ecbfbc4e6eb3d9fbcf152aab52fba96a068b` (93) |
| `transfer_of_licensedForB_needs_licence` | Quot.sound, propext | `c2c41b5ae1bce6cf454d3df2a8ca85ffa5e4cbed1c321d0db8b5d281b26ac89e` | `27a67923413c9c083c050f0da4cb4f6726e389c91ab6b2923ed2fcaf1efb822a` (102) |
| `transfer_of_licensedForB_nonvacuous` | Quot.sound, propext | `b750354d013237681b2dfa381a97eaeff3e4a563636b84712d363345da85ffec` | `023a657c38067f98444f4cb9c3dfe5326f607d0bdd3164b6fefe01a9a9158cc1` (102) |
| `TruthLicensed` | none | `8ee0e61c755a8d8b410ddef83fe4b2b78d9c52c43b5227b5cb2be25aea1c624d` | `d89a0678af1b3a93120bf7501b8b969163b03b62033edd8c5fb5078bbaacb413` (16) |
| `truthLicensed_examples` | Classical.choice, Quot.sound, propext | `0aee55cfd38c0bd2a9d6c1afb99fbfb2deb660d6da06f8173e1398ad8f5b1015` | `61a0c097a9e6ebc3bfdfde8cb3b772a5382552dc79d0097c3aae8f23b78633b2` (98) |
| `truthList` | none | `40bffe4ca27799f7ef8f7c4ea589d2c6f00cc428ffb53513f43ab340b19eba3f` | `d89a0678af1b3a93120bf7501b8b969163b03b62033edd8c5fb5078bbaacb413` (16) |
| `TS` | none | `8c2dfcd107aac381cf7fdb44dab35e922e30295bb40e848486da26728ca08152` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `tsBoolHalt` | none | `a0b64087147c0469296e362c930cf3aee45c45488c902c3ea3639b35197e4a01` | `52c59e58bca2a41c44a01701b22c3939e615998e01b38d553889d965fec6bf2e` (2) |
| `tsBranch3` | propext | `a0b64087147c0469296e362c930cf3aee45c45488c902c3ea3639b35197e4a01` | `52c59e58bca2a41c44a01701b22c3939e615998e01b38d553889d965fec6bf2e` (2) |
| `tsHalt` | none | `a0b64087147c0469296e362c930cf3aee45c45488c902c3ea3639b35197e4a01` | `52c59e58bca2a41c44a01701b22c3939e615998e01b38d553889d965fec6bf2e` (2) |
| `tsLine2` | propext | `a0b64087147c0469296e362c930cf3aee45c45488c902c3ea3639b35197e4a01` | `52c59e58bca2a41c44a01701b22c3939e615998e01b38d553889d965fec6bf2e` (2) |
| `tsLoop` | none | `a0b64087147c0469296e362c930cf3aee45c45488c902c3ea3639b35197e4a01` | `52c59e58bca2a41c44a01701b22c3939e615998e01b38d553889d965fec6bf2e` (2) |
| `tsLoopOrHalt` | none | `a0b64087147c0469296e362c930cf3aee45c45488c902c3ea3639b35197e4a01` | `52c59e58bca2a41c44a01701b22c3939e615998e01b38d553889d965fec6bf2e` (2) |
| `tsTwoStep` | none | `a0b64087147c0469296e362c930cf3aee45c45488c902c3ea3639b35197e4a01` | `52c59e58bca2a41c44a01701b22c3939e615998e01b38d553889d965fec6bf2e` (2) |
| `tsUnreachLoop` | none | `a0b64087147c0469296e362c930cf3aee45c45488c902c3ea3639b35197e4a01` | `52c59e58bca2a41c44a01701b22c3939e615998e01b38d553889d965fec6bf2e` (2) |
| `univ_counterexample_transfers_along_model_embedding` | Quot.sound | `e75316e3bbf1077009e463c1a5849276c3a2fdcec2b8a72fda0d45c5bdaf6880` | `b2ce23cd7086f1c6b703d31bb848dfaf1925ea6a2d5cc0b3eee7278baffb8501` (40) |
| `univ_preserved_to_substructure_nonvacuous` | Quot.sound, propext | `2098c31ac1af422f07665069605eaa43a4c7bfe1af0ec9176dc0f7d7067b8d28` | `7bc15d4948d0ec41199b391f1af7176ecc29d0393f3c5642231aeea2ed8fb122` (51) |
| `univ_preserved_to_substructure_of_embedding` | Quot.sound | `1264568d737438ab40ff43908e63f410bfdfa7b09131b90d1220e20f2096af46` | `3e7283fe414e71b46134d12097b1eb0cb63026fa100816b9b43cc4cdd59ff323` (38) |
| `univ_truth_transfers_down_from_model_extension` | Quot.sound | `c352088325f262ee5c096872c5a301ab08503aae1104a13bdc2d0f19d79f1815` | `b2ce23cd7086f1c6b703d31bb848dfaf1925ea6a2d5cc0b3eee7278baffb8501` (40) |
| `unlicensed_cells_contain_transferring_subclasses` | Quot.sound, propext | `0871ea026a5de406ed996846743f2d37423d39e69ba3513748f5dd4cd683f926` | `37b83992d457fc177ee20bcc21eea03b1416f1741e58a7145d0b1d83c6b1f907` (109) |
| `unrelated_falsity_transfer_iff` | Classical.choice, Quot.sound, propext | `6609343449c69d9d88666d4b51bbade30b3698bdf8f91940ca2fefb587c6b7a3` | `c17efe6f62c576e91898d3f050cdba076420ce607b14887d8bcd64a83ed15f32` (27) |
| `unrelated_model_result_consistent_with_both` | none | `fa2b1393c645dc9dd0ca2535ae721784238fba44ae500813bc0d6359cb7e3604` | `b21a6063ea4793dfea31c696bfa1f6da91b0163501004285b75615b47b2a4baa` (25) |
| `unrelated_nonvacuous` | Quot.sound, propext | `ec8bbcaa8d38bfe087c13aef7f5c56d07e2d086e03876084895dcad1c5a64781` | `96cfd94d7cd83c8fca385a93e87d5f61423cbcdf62ca4603dbc271cb24be33dd` (27) |
| `unrelated_refutation_licensed_iff` | Classical.choice, Quot.sound, propext | `f42f7b38ca9dcc556e02ebb3c8add45a3efb55066d7c81e62e7816b0fc2018ae` | `0bd133b828aea9fd37e913a2f2f67efd7ab308fb86f053df9632aa148df001b8` (26) |
| `unrelated_refutation_licensed_iff_unsat_same_class` | Classical.choice, Quot.sound, propext | `b346ef1ae6f83aa9071e0284a11d24d59d4c1551a7a6f6de245af48c43471b1d` | `0bd133b828aea9fd37e913a2f2f67efd7ab308fb86f053df9632aa148df001b8` (26) |
| `unrelated_truth_transfer_iff` | Classical.choice, Quot.sound, propext | `8e2a44b513b0146e85b0c2ac5ebdfdd7bda3df11228ce093b1210bbccf64b181` | `c17efe6f62c576e91898d3f050cdba076420ce607b14887d8bcd64a83ed15f32` (27) |
| `unrelated_two_class_example` | Classical.choice, Quot.sound, propext | `e2e76bc445f1ff9b6adcbfbda0db257d3986e09a9805a81fbd9178a046709b2a` | `8d4e41ae13b1725a52ece00aa18b71bd36cf1e7b0aa02f42809c36a8b5232dbf` (29) |
| `UnsatIn` | none | `233172b594296f988397610d06c7524a41bf68eb1d4a89f126e5d2f97dd653c9` | `91727f2a28b6f061623db4f433c8d5d2e92a8d44680acf4038776835d9dcab51` (11) |
| `unsatIn_examples` | Quot.sound, propext | `d9383453168079e428333b1f3f2b1cc726ffe0b6292dd7fb5229424adafef8ac` | `cbd06aca3946ad33291aaf8423ada657490a8a2fa747f33fde92aad141b82d1e` (30) |
| `ValidIn` | none | `233172b594296f988397610d06c7524a41bf68eb1d4a89f126e5d2f97dd653c9` | `91727f2a28b6f061623db4f433c8d5d2e92a8d44680acf4038776835d9dcab51` (11) |
| `validIn_examples` | Classical.choice, Quot.sound, propext | `400a3c643e3d2a1d61117207bde26a3659c6541999a4f4233224895c19aae542` | `cafe34cf48ca3b819ceb36fa986cd9e904809c71454bac045c000b13cba63bfe` (30) |
| `weak_termination_does_not_transfer_down_lockstep` | none | `429a0820d7cb2b75eaef42b38221924970630b240b85e3889ce7168d120a78b5` | `81f24e52a889b5b723220068ecf0b766eeadbbcd123a7a1f98d7fbfe99b24221` (17) |
| `WeaklyTerminates` | none | `a4588a7bd434480f33b31131a10422378684e5e990b05ab8ad7b24131dc3b0eb` | `631230881b753d8abd2fed12e445358b09b73218ff74c0de88e75bd3e00677ab` (3) |
| `weaklyTerminates_examples` | none | `0912d30145c2cde72d55ff77c58925dd980792d5dbbdc8f14b2a0c7343701edd` | `ce7a77d95aa18738e6da5c509aec0108857e4144a19c8d9cfb99bfe0520d7e2f` (10) |
| `wf_simulation_needs_measure_decrease` | none | `e6d7ce540a58fbbcbfcf18b968a952f906b3b7fa40c1d781d28bbd8ca1b91fe5` | `e19ddf4402907a1fbd9323032013c568eb30ccc0a7ccabe8ea86381af07c0368` (14) |
| `wf_simulation_needs_wellFounded` | none | `0944f4abb6148997ee02ca907e6062f8ed01f660fd9e9e33f8870c8dd92e16f9` | `e19ddf4402907a1fbd9323032013c568eb30ccc0a7ccabe8ea86381af07c0368` (14) |
| `wf_simulation_nonvacuous` | none | `a6c39b814c373534a749735d8a2f9a293335dcc28b98c6b29dcae9c5d19273ad` | `b9be9b65b1c80edea7f5e796e02c7c908bcbf5e1d576edaf8d6c52d07c536700` (14) |

**Toolchain.** Lean `leanprover/lean4:v4.34.1`, tag commit `5045d0056413266e57c625dcd7c365b10e377c52` of the repository `leanprover/lean4`; core library, no Mathlib. The pinned toolchain is recorded in `lean/lean-toolchain`.

**Primary sources.** Each entry gives the bibliographic record, the identifier (DOI, stable URL or repository commit) and what was checked at the source; the cards that cite it are listed in brackets. For card 18 no specific prior statement of the characterizations was located; they are elementary consequences of the definitions.

- M. Abadi, L. Lamport, 'The existence of refinement mappings', Theoretical Computer Science 82(2) (1991) 253–284, DOI 10.1016/0304-3975(91)90224-P (bibliographic data verified; the abstract was not accessible; per the authors' publication-page commentary, the paper shows that refinement mappings exist once history and prophecy variables are added, under stated hypotheses). Different formalism: state machines with stuttering and liveness. [cards 10, 11]
- M. Ajtai and Y. Gurevich, 'Monotone versus positive', J. ACM 34(4) (1987) 1004–1015, DOI 10.1145/31846.31852 (bibliographic data and abstract verified via Crossref): the abstract answers negatively whether a first-order formula that is semantically monotone in a predicate symbol P on finite structures is necessarily equivalent on finite structures to a first-order formula with only positive occurrences of P; it does not mention Lyndon's theorem. Cited for the failure of Lyndon's theorem over finite structures as reported by Rossman 2008, Theorem 1.5 and p. 3. [cards 4]
- M. C. Browne, E. M. Clarke, O. Grumberg, 'Characterizing finite Kripke structures in propositional temporal logic', Theoretical Computer Science 59(1–2) (1988) 115–131, DOI 10.1016/0304-3975(88)90098-9 (bibliographic data verified; content not checked). Cited as the origin of stuttering equivalence. [cards 16]
- C. C. Chang and H. J. Keisler, Model Theory, 3rd ed., North-Holland 1990 (Studies in Logic 73), DOI 10.1016/S0049-237X(08)X7004-1 (Crossref record of the 1990 Elsevier volume with ISBN 978-0-444-88054-3, whose chapter records include the preface to the third edition; the record itself lists no authors). The publisher's table of contents lists §3.2 'Applications of elementary chains' and §5.2 'Preservation theorems'; which theorem appears under which number was not verified at the source. [cards 1, 6]
- E. M. Clarke, O. Grumberg, D. E. Long, 'Model checking and abstraction', ACM TOPLAS 16(5) (1994) 1512–1542, DOI 10.1145/186025.186051 (author PDF checked): abstractions are given by surjections from concrete to abstract states (p. 1513), and ∀CTL* properties true of the abstract model hold of the concrete one (Theorem 5.6). Different formalism: a surjective state abstraction of a Kripke structure, not a first-order embedding. [cards 8]
- E. Clarke, O. Grumberg, S. Jha, Y. Lu, H. Veith, 'Counterexample-guided abstraction refinement', CAV 2000, Lecture Notes in Computer Science, Springer, 154–169, DOI 10.1007/10722167_15 (PDF checked; series volume number not verified): over-approximating abstract models may produce spurious counterexamples, and an abstract counterexample is checked for a corresponding concrete path (Lemma 1); the check concerns one abstract path, not a converse simulation. [cards 8, 13, 14]
- P. Cousot, R. Cousot, 'Abstract interpretation: a unified lattice model for static analysis of programs by construction or approximation of fixpoints', POPL 1977, 238–252, DOI 10.1145/512950.512973 (bibliographic data verified; content not checked). Cited as the origin of Galois-connection over-approximation, a different formalism from first-order embeddings. [cards 8]
- D. Dams, R. Gerth, O. Grumberg, 'Abstract interpretation of reactive systems', ACM TOPLAS 19(2) (1997) 253–291, DOI 10.1145/244795.244800 (first part of the abstract checked): abstract interpretation extended to existential and universal reactive properties. Different formalism, not first-order embeddings. [cards 8]
- R. W. Floyd, 'Assigning meanings to programs', Mathematical Aspects of Computer Science, Proc. Symposia in Applied Mathematics 19, AMS 1967, 19–32, DOI 10.1090/psapm/019/0235771 (bibliographic data verified via Crossref and the ACM Turing Award bibliography; content not checked). Cited as the origin of well-founded ranking arguments for termination. [cards 17]
- Y. Gurevich, 'Toward logic tailored for computational complexity', Computation and Proof Theory, Lecture Notes in Mathematics, Springer 1984, 175–216, DOI 10.1007/BFb0099486 (bibliographic data verified via Crossref, except the series volume number; cited as reported by Rossman 2008, p. 3, for the rediscovery of the finite failure of Łoś–Tarski). [cards 1, 2]
- W. Hodges, Model Theory, Cambridge University Press 1993 (Encyclopedia of Mathematics and its Applications 42), DOI 10.1017/CBO9780511551574 (bibliographic data verified via Crossref), checked in the publisher's reading sample: §1.2 (an embedding is an injective homomorphism with ā ∈ R^A ⇔ fā ∈ R^B), §2.4 'Maps and the formulas they preserve' (∀1 and ∃1 formulas, not required to be prenex), Theorem 2.4.1 (∃1 formulas are preserved by embeddings), Corollary 2.4.2(a) (∀1 formulas are preserved in substructures), Theorem 2.4.3 ((a) positive existential formulas are preserved by homomorphisms; (b) positive formulas by surjective homomorphisms). [cards 1, 2, 3, 4, 5, 6, 7, 8, 19, 20]
- X. Leroy, 'A formally verified compiler back-end', J. Automated Reasoning 43(4) (2009) 363–446, DOI 10.1007/s10817-009-9155-4 (bibliographic data verified), and the CompCert development, file common/Smallstep.v at commit 2685140bf72c959446981fb99b5e44a8975021bc of AbsInt/CompCert (checked): `fsim_properties` (line 566; a well-founded order, and each step matched by a non-empty sequence of steps or by a possibly empty sequence with a decrease), `forward_simulation_step` (line 727, lock-step), `forward_simulation_opt` (line 752, zero or one step with a decreasing natural-number measure), `simulation_forever_silent` (line 972, infinite silent runs are preserved). Different formalism: labelled small-step semantics with traces; divergence is coinductive rather than `Acc`. [cards 15, 17]
- C. Loiseaux, S. Graf, J. Sifakis, A. Bouajjani, S. Bensalem, 'Property preserving abstractions for the verification of concurrent systems', Formal Methods in System Design 6(1) (1995) 11–44, DOI 10.1007/BF01384313 (abstract checked): simulations parameterized by Galois connections (α, γ) preserve fragments of the branching-time μ-calculus. Different formalism: Galois-connection abstractions, not first-order embeddings. [cards 8]
- J. Łoś, 'On the extending of models (I)', Fundamenta Mathematicae 42(1) (1955) 38–54 (bibliographic data verified at https://eudml.org/doc/213372; the paper itself was not opened). Cited, with Tarski 1954, for the Łoś–Tarski preservation theorem, whose statement was verified as Rossman 2008, Theorem 1.1 and footnote 1. [cards 1, 2, 8]
- N. Lynch, F. Vaandrager, 'Forward and backward simulations, Part I: untimed systems', Information and Computation 121(2) (1995) 214–233, DOI 10.1006/inco.1995.1134 (report version checked): forward simulations between labelled automata (§3.2: start states related; every step matched by a possibly empty sequence of steps with the same external behaviour), proved sound for trace inclusion. The paper has no separate lemma that reachable states are related; it follows from its Lemma 3.8 and the start condition. Its backward simulations (§3.3) go from the implementation to the specification and match steps backward in time; they are not the converse relation used here. [cards 9, 10, 12, 14]
- R. C. Lyndon, 'Properties preserved under homomorphism', Pacific J. Math. 9(1) (1959) 143–154, DOI 10.2140/pjm.1959.9.143 (bibliographic data verified; the paper was not opened; its theorem, as stated in Rossman 2008, Theorem 1.2, is the converse for surjective homomorphisms: a formula preserved under surjective homomorphisms is equivalent to a positive one). [cards 3, 4]
- P. Manolios, K. Namjoshi, R. Sumners, 'Linking theorem proving and model-checking with well-founded bisimulation', CAV 1999, Lecture Notes in Computer Science, Springer, 369–379, DOI 10.1007/3-540-48683-6_32 (technical-report version checked; series volume number not verified): well-founded equivalence bisimulations with a rank function S × S → W, on transition systems whose transition relation must be left total (Definition 1), so no run ends. Different formalism. [cards 17]
- Mathlib (Lean 4), file Mathlib/ModelTheory/Complexity.lean at commit 3eae40f5eb25c5934211edf662d3b24c5afbe47a of leanprover-community/mathlib4 (checked): prenex `IsUniversal` and `IsExistential` (lines 330, 342) and `IsQF.realize_embedding`, `IsUniversal.realize_embedding`, `IsExistential.realize_embedding` (lines 374, 387, 398), `Theory.IsUniversal.models_of_embedding` (line 418), for arbitrary first-order languages. The ModelTheory directory at that commit has no positive or positive existential classes and no preservation results for homomorphisms beyond atomic formulas. [cards 1, 2, 6]
- R. Milner, 'An algebraic definition of simulation between programs', Proc. IJCAI 1971, 481–489 (bibliographic data verified via DBLP and the first page of the proceedings PDF; content not checked). Cited as the original notion of simulation. [cards 9]
- K. S. Namjoshi, 'A simple characterization of stuttering bisimulation', FSTTCS 1997, Lecture Notes in Computer Science 1346, 284–296, DOI 10.1007/BFb0058037 (PDF checked): well-founded bisimulation, a symmetric relation with a rank function S × S × S → W into a well-founded set and three matching clauses (a step, a stutter of the first state with a rank decrease, or a step of the second state with a rank decrease), is sound and complete for stuttering bisimulation (Theorems 1 and 2). Different formalism: symmetric bisimulation on labelled transition systems; the criterion here is one-sided. [cards 16, 17]
- P. W. O'Hearn, 'Incorrectness logic', Proc. ACM Program. Lang. 4(POPL) (2020), DOI 10.1145/3371078 (bibliographic data verified; content not checked). Cited as a program logic for under-approximate reasoning about bugs, a different formalism. [cards 7]
- B. Rossman, 'Homomorphism preservation theorems', J. ACM 55(3), Article 15, 15:1–15:53 (2008), DOI 10.1145/1379759.1379763 (author PDF checked): Theorem 1.1 (Łoś–Tarski: preservation under embeddings iff equivalent to an existential formula; footnote 1: an embedding is an isomorphism onto an induced substructure, and the dual form is preservation under induced substructures iff universal), Theorem 1.2 (Lyndon's positivity theorem: surjective homomorphisms, positive formulas), Theorem 1.3 (homomorphism preservation theorem: homomorphisms, existential-positive formulas), Theorems 1.4 and 1.5 (Łoś–Tarski and Lyndon fail over finite structures; p. 3 attributes 1.4 to Tait 1959 and Gurevich–Shelah via Gurevich 1984, and 1.5 to Ajtai–Gurevich 1987 and Stolboushkin 1995), Theorem 1.7 (finite homomorphism preservation for sentences), Lemma 2.3 (the easy direction), §2.1.1 (structures have non-empty universes; substructure versus induced substructure), Remark 2.1 (formulas are not required to be prenex). [cards 1, 2, 3, 4, 5, 6, 7, 18, 20]
- C. Sternagel, R. Thiemann, 'Abstract Rewriting', Archive of Formal Proofs, June 2010, https://isa-afp.org/entries/Abstract-Rewriting.html (entry page and its bibliographic record verified; no DOI was found for the entry at Crossref; development version checked at the AFP mirror, Abstract_Rewriting.thy, at a revision that was not recorded): strong normalization defined as the absence of infinite chains (`SN_on`), with `SN_iff_wf` and `SN_on_conv_accp` relating it to well-foundedness and accessibility (the Isabelle counterpart of `terminates_iff_no_infinite_run`). [cards 15, 17]
- A. P. Stolboushkin, 'Finitely monotone properties', Proc. 10th IEEE Symposium on Logic in Computer Science (LICS 1995), 324–330, DOI 10.1109/LICS.1995.523267 (bibliographic data verified via Crossref): a simpler counterexample, per Rossman 2008, p. 3. [cards 4]
- W. W. Tait, 'A counterexample to a conjecture of Scott and Suppes', J. Symbolic Logic 24(1) (1959) 15–16, DOI 10.2307/2964569 (verified: a sentence preserved under subsystems of finite systems that is not equivalent over finite systems to a universal sentence). [cards 1, 2]
- A. Tarski, 'Contributions to the theory of models. I' and 'II', Indagationes Mathematicae (Proceedings) 57 (1954) 572–581 and 582–588, DOIs 10.1016/S1385-7258(54)50074-0 and 10.1016/S1385-7258(54)50075-2 (bibliographic data verified via Crossref; the papers were not opened). [cards 1, 2, 8]

**Observation date.** The build, the axiom audit and the hashes above were produced on 2026-11-21; the bibliographic data and source passages cited in the prior-art entries were checked on the same date. The Lean toolchain commit was read from the GitHub API record of the tag `v4.34.1` of `leanprover/lean4`.

## Revalidation

Requirements: `elan` (which installs the toolchain pinned in `lean/lean-toolchain`) and `python3`. From the package directory:

```sh
python3 support/revalidate.py .
```

The script copies `lean/` to a temporary directory and runs `lake build`; scans the Lean sources for `sorry`, `admit`, `native_decide` and `axiom` declarations; runs a generated Lean program that computes, with `Lean.collectAxioms`, the axioms of every declaration of the library (allowed: `propext`, `Classical.choice`, `Quot.sound`); and recomputes, for every Lean name referenced by `results.json` and every name in `audit/statements.json`, the SHA-256 of the statement (the `repr` of its type) and of its definition closure (types and values of every package constant reachable from the statement, theorem bodies excluded), comparing them with `audit/statements.json`. It prints `REVALIDATED` on success. The package itself is not modified.

A shorter check of the build and of the axioms of every referenced declaration, with `lake` and no Python:

```sh
cd lean
lake build
lake env lean RevalidationAudit.lean
```

`lean/RevalidationAudit.lean` (outside the library target, so `lake build` does not build it) imports `ToyTransfer` and runs `#print axioms` for every Lean name referenced by `results.json`; each output line must list a subset of `propext`, `Classical.choice` and `Quot.sound`, or report that the declaration depends on no axioms.

A passing run establishes that the recorded statements are kernel-checked under the pinned toolchain with the standard axioms and that their statements and definition closures are unchanged. It does not re-establish the modeling bridges, which are argued in prose, and it says nothing about any real model or system. A failed hash comparison means that a statement or a definition it reaches has changed, and the corresponding card must be re-examined.
