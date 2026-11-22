# Tulip: A Denotationally-Based Program Logic for Higher-Order Store, Its Guarded-Domain-Theoretic Lineage, and the Boundary with Operational Step-Indexed Logics

## Summary

Tulip (Aagaard, Sterling, Birkedal; MFPS XXXIX, ENTICS vol. 3, 2023; `arXiv:2308.02906v2`) is a guarded higher-order separation logic whose predicates range over the **typed denotations** of a monadic System F with recursive types and general references (written F^ref_μ below), interpreted in a model built inside impredicative guarded dependent type theory (iGDTT). Operational step-indexed logics such as Iris instead range over **raw untyped expressions** equipped with a small-step relation. What a later reader should retain:

1. **How the recursive world equation is solved.** Tulip reuses the Sterling–Gratzer–Birkedal model: the poset of worlds and the semantic types are defined together by the guarded domain equation `W = ℕ ⇀fin ▶S_p`, `S_p = [W, Set]`, `S_ℓ = [W, Type]`, solved with the Löb fixed point `gfix : (▶A → A) → A` on universes. The later modality `▶` of the metalanguage replaces explicit step indices, and impredicativity of `Set` is what makes `S_p` cartesian closed and the store-passing monad `(TA)w = ∀w′≥w. tH w′ → L ∃w″≥w′. tH w″ × A w″` definable. Earlier solutions of the same equation shape (Birkedal–Reus–Schwinghammer–Støvring–Thamsborg–Yang, POPL 2011; Birkedal–Møgelberg–Schwinghammer–Støvring, LICS 2011 / LMCS 2012) take predicates over *syntactic values* and define computation by an operational `step` relation.
2. **Why congruence under binders is not a proof rule.** The logic is interpreted in a BI-hyperdoctrine `B^(−) : S_ℓ^op → Poset` (in the sense of Biering–Birkedal–Torp-Smith). Terms denote base morphisms, propositions denote fibre elements, substitution is reindexing, and the weakest precondition is a natural transformation `wp_A : B^A × TA → B` on denotations. Judgementally equal terms therefore yield the *same* fibre element, including when the rewrite happens under `λ` or in a `let`/bind body; Tulip has no β rule for `wp` because the two propositions are convertible. In Iris the corresponding facts are separate rules: `WP-BIND` for evaluation contexts `K` (in the Coq development, any `K` satisfying the `LanguageCtx` laws `fill_not_val`, `fill_step`, `fill_step_inv`) and a `▷`-guarded pure-step rule `WP-λ`; neither applies under a binder.
3. **The invariance is with respect to an intensional equational theory, not contextual equivalence.** Tulip's equations expose abstract steps (`unfold (fold u) ≡ step; ret u`, `set u v; get u ≡ step; set u v; ret v`) and its store is global (allocation is observable). The authors state that equational reasoning "is limited by the intensionality" of the model.
4. **Adequacy is not part of the Tulip paper.** Its results are soundness of the rules in the model (Theorem 4.24) and consistency (Corollary 4.26), both "stated internally to iGDTT". The paper defines no operational semantics, and neither it nor the Sterling–Gratzer–Birkedal paper states a theorem connecting `wp`, or equality of denotations, to executions or to contextual equivalence. Iris, by contrast, states adequacy of weakest preconditions against all thread-pool reductions (Theorems 6 and 7 of *Iris from the ground up*). Adequacy for guarded denotational models exists for smaller languages (Møgelberg–Paviotti for FPC; Frumin–Timany–Birkedal for a PCF-like language with effects), which indicates the shape a Tulip adequacy proof would take but does not supply it.
5. **Where operational approaches are ahead.** Tulip is sequential, deterministic, typed, and restricted to one resource (partial heaps): no interleaving, invariants, or higher-order ghost state; no untyped or byte-addressed memory; no local store or deallocation; no refinement judgement between different languages; no implementation (equality reflection makes definitional equality undecidable) and no machine-checked formalisation is reported. Iris is parameterised by an arbitrary expression/state/step relation, is formalised in Coq, and covers concurrency.
6. **Toy mechanisation.** A Mathlib-free Lean `v4.34.1` development under `lean/` (results labelled `[kernel-checked proof]` `[toy model]`) builds a `Nat`-indexed BI algebra with a later modality, the indexed BI algebra over types and functions, a typed λ-calculus with binders and a step-counting denotation, and an operational step-indexed weakest precondition on the same closed terms. It proves (a) that convertible terms and substitutions induce equal fibre elements and equal `wp`, including under `λ` and under the bind binder, using only functoriality of reindexing, the substitution lemma and Beck–Chevalley/Frobenius-style laws; and (b) that the operational bind rule is a theorem under explicit context-lifting laws, that the context `λ_. •` violates those laws, and that the bind rule's conclusion is false for it.

**Model–system relation: none proved.** The Lean development is a small synthetic model written for this report. It has no store, no recursive types, no polymorphism, no recursively defined worlds and no divergence; it is not a formalisation of Tulip, of iGDTT, or of Iris, and no theorem relates it to any of them.

## Applicability

**Subjects and how they relate.** The report concerns one primary subject interpreted through its cited lineage and compared against one operational logic:

| Subject | Role in this report | Examined text |
|---|---|---|
| Aagaard, Sterling, Birkedal, *A denotationally-based program logic for higher-order store* | Primary subject | arXiv `2308.02906v2` PDF (21 pages, ENTICS layout), read in full |
| Sterling, Gratzer, Birkedal, *Denotational semantics of general store and polymorphism* | The denotational model Tulip extends (Tulip reference [46]) | arXiv `2210.02169v2`; introduction, §§1.1–1.3, Lemma 5.7, §6 |
| Biering, Birkedal, Torp-Smith, *BI-hyperdoctrines, higher-order separation logic, and abstraction* | Definition of BI-hyperdoctrine (Tulip reference [8]) | Journal identity verified by DOI metadata; definitions read from the authors' technical report ITU-TR-2005-69 (July 2005), §5 |
| Birkedal, Møgelberg, Schwinghammer, Støvring, *First steps in synthetic guarded domain theory: step-indexing in the topos of trees* | Synthetic guarded domain theory; the operational version of the world equation (Tulip reference [11]) | arXiv `1208.3596v2` (the LMCS article), §§2, 3, 5 |
| Birkedal, Reus, Schwinghammer, Støvring, Thamsborg, Yang, *Step-indexed Kripke models over recursive worlds* | Metric-space solution of the world equation for an operational model | Author-hosted POPL 2011 PDF, §§1–2 |
| Jung, Krebbers, Jourdan, Bizjak, Birkedal, Dreyer, *Iris from the ground up* | Operational comparator (Tulip reference [30]) | Author-hosted JFP PDF, §§2, 6, 7, 8.3 |
| Iris Coq development, tag `iris-4.3.0` | Exact context-lifting laws used by `wp_bind` | `iris/program_logic/language.v` lines 46–55; `iris/program_logic/weakestpre.v` lines 277–278 |
| Møgelberg, Paviotti, *Denotational semantics of recursive types in synthetic guarded domain theory* | Adequacy for a guarded denotational model (FPC) | arXiv `1805.00289v2`, abstract and introduction |
| Frumin, Timany, Birkedal, *Modular denotational semantics for effects with guarded interaction trees* | Adequacy and bind rule for a guarded denotational model inside Iris | arXiv `2307.08514v2`, abstract, §§2, 4–7, 10 |
| Lean 4 `v4.34.1` | Proof kernel for the toy model | Toolchain used to build and audit `lean/` |

**Versions.** The arXiv record lists v1 (5 Aug 2023, 56 KB) and v2 (17 Nov 2023, 350 KB). Only v2 was read. Statements here are about v2 and are not claimed for v1.

**Limitation on one identity.** The typeset ACM TOPLAS article of Biering–Birkedal–Torp-Smith was not obtained. Definitions attributed to that work are quoted from the 2005 technical report with the same authors and title; the journal version may differ in numbering or wording.

**Scope of the comparison.** Findings about "operational logics" are established for Iris as presented in the 2018 JFP article and for the two Coq definitions listed above. They are not established for other operational frameworks. Statements about relational (simulation or bisimulation) frameworks are explicitly marked as derived and are not backed by an examined relational development.

**Adjacent packages whose material is not duplicated here.**

- `iris-adequacy-transfinite-liveness-simuliris-and-lean-separation-logic` covers Iris's Coq adequacy theorems (`wp_strong_adequacy_gen`, `twp_total`), the `ectx_lifting.v` head-step lifting obligations, Transfinite Iris, and the Simuliris/Tree Borrows contextual-refinement replay. This report quotes only the JFP rule statements and the `LanguageCtx` class needed for the comparison, and does not examine Simuliris.
- `lean-separation-logics-iris-and-virtual-isa-verification` and `meta-free-reflective-separation-logic-framing-view-pcms-and-step-index-free-adequacy` cover Lean-native separation-logic substrates and step-index-free adequacy.
- `fuel-step-indexing-clocks-and-tcb-recursion` and `fuel-indexed-and-coinductive-weakest-preconditions-for-partial-correctness` cover explicit fuel/step indices and their relation to coinductive weakest preconditions.
- `bisimulation-up-to-techniques-compatibility-and-the-weak-up-to-pitfall` covers up-to-context techniques, where closure under contexts appears as a compatibility obligation.
- `abramsky-honda-mccusker-general-references-laird-control-murawski-tzevelekos-nominal-games-dreyer-neis-birkedal-and-abadi-plotkin-layout-randomization` covers game-semantic and Kripke-relational accounts of what contexts with higher-order state can observe.
- `modular-verification-contextual-refinement-and-separate-compilation`, `semantic-typing-encapsulated-unsafe-code-and-adequacy`, and `universal-properties-observational-refinement-and-end-to-end-system-binding` cover contextual refinement, semantic typing adequacy, and end-to-end observational anchoring.

**Model–system relation: none proved.** Everything under `lean/` characterises the toy definitions in that directory only.

## Findings

### 1. Bibliographic identity and the paper's own claims

Basis: documentation (arXiv record, episciences record, DOI metadata, the v2 PDF).

- Authors: Frederik Lerbjerg Aagaard, Jonathan Sterling, Lars Birkedal (Aarhus University). Venue: *Electronic Notes in Theoretical Informatics and Computer Science*, Volume 3, Proceedings of MFPS XXXIX, article `entics:12232`, DOI `10.46298/entics.12232`.
- The abstract states two differences from operationally-based program logics: predicates range over the meanings of typed terms rather than over the raw code of untyped terms, and they are automatically invariant under the equational congruence of higher-order store, "which applies even underneath a binder"; as a result, "pure" proof steps that conventionally require focusing the Hoare triple on an operational redex "are replaced by a simple equational rewrite".
- The stated main result is "the soundness of Tulip, which we establish by constructing a BI-hyperdoctrine over the denotational semantics of F^ref_μ in an impredicative version of synthetic guarded domain theory."
- The evaluation is one worked example (append on heap-allocated linked lists, Theorem 3.3). The authors' own assessment is modest: the proof "is very similar to the one in Iris", "although some steps are perhaps slightly simpler as they use equational reasoning rather than explicit rules for reduction in weakest preconditions."

Disagreements among sources, preserved:

- **Publication date.** The v2 PDF footer reads "Published November 15, 2023"; the episciences page, the DOI metadata, and the arXiv journal reference read November 23, 2023.
- **Abstract wording.** The arXiv and episciences abstracts say predicates range over "the meanings of typed terms"; the v2 PDF abstract says "the meanings of typed terms in an arbitrary model".
- **Title casing.** arXiv/episciences: "A denotationally-based program logic for higher-order store"; PDF title: "A Denotationally-based Program Logic for Higher-order Store".
- **Status of the underlying model paper.** Tulip cites Sterling–Gratzer–Birkedal as "(2022). Unpublished manuscript"; the arXiv record of that paper shows v2 dated 12 Apr 2023 and no journal reference as observed.

### 2. The object language and its equational theory

Basis: normative (the paper is the defining text of the logic; §2.1 and Appendix A).

- Two kinds of types, program types (`p`) and logical types (`ℓ`), because "one impredicative universe cannot contain another"; the type `prop` of propositions is a logical type that is not a program type.
- Program types are closed under functions, products, inductive types, `∀`, `∃`, recursive types `μα.A`, reference types `ref A`, and a computational monad `T` "governing both state and general recursion". `unfold` is effectful: `unfold u : T A[μα.A/α]`.
- Functions and products "satisfy the full universal properties of exponentials and cartesian products up to judgmental equality"; the monad satisfies the three monad laws (Appendix A.1).
- A primitive `step : T ()` is "a 'no-op' instruction witnessing the guarded or intensional nature of our denotational semantics". The store and recursion equations are:
  - `unfold (fold u) ≡ step; ret u` and `x ← unfold u; ret (fold x) ≡ step; ret u`;
  - `set u v; get u ≡ step; set u v; ret v`;
  - `(x ← new u; set x v; w) ≡ (x ← new v; w)`; `set u v; set u w ≡ set u w`; `(x ← get u; set u x; w) ≡ (x ← get u; w)`; reads of two cells commute;
  - rules (not displayed in the paper) "that commute step past all primitive effects".
- Remark 2.2: "ours is a theory of higher-order global store rather than higher-order local store in the sense that allocations are not hidden but rather have a globally observable effect."
- Recursive functions are derived from recursive types and satisfy `(rec f(x) in e) x ≡ step; e[rec f(x) in e / f]`.

### 3. The logic

Basis: normative (§2.2).

- Judgemental equality "is respected by all judgments and preserved by all operations". Propositional equality is related to it by the Lawvere rule and by equality reflection (`⊤ ⊢ u =_A v` gives `u ≡ v`). The paper notes that the Lawvere rule "entails all important properties of equality, including congruence for all constructs of Tulip and its F^ref_μ substrate."
- Intuitionistic higher-order logic over logical types; affine separation logic with unit `⊤`, `∗`, `−∗`, and a persistence modality `□`.
- Later modality with `φ ⊢ ▷φ`, `▷φ ∧ ▷ψ ⊢ ▷(φ ∧ ψ)`, `▷φ ∗ ▷ψ ⊢ ▷(φ ∗ ψ)`, `φ −∗ ψ ⊢ ▷φ −∗ ▷ψ`, `▷□φ ⊣⊢ □▷φ`, and Löb induction `▷φ ⇒ φ ⊢ φ`.
- Two rules tie program steps to `▷`: **fold equality** (`φ ⊢ ▷(u = v)` iff `φ ⊢ fold u = fold v`) and **step equality** (`φ ⊢ ▷(u = v)` iff `φ ⊢ step; u = step; v`). The paper describes this as "an abstract form of step-indexing: operations that semantically involve unfolding a recursive domain equation leave behind abstract steps that can be used to advance in time in relation to the later modality."
- Weakest-precondition rules: `wp-wand`, `wp-val`, `wp-bind` (`wp e₁ {x. wp e₂ {y. φ}} ⊢ wp (x ← e₁; e₂) {y. φ}`), `wp-get` (`∃x. [ℓ ↪ x] ∗ ▷([ℓ ↪ x] −∗ φ) ⊢ wp (get ℓ) {x. φ}`), `wp-set`, `wp-new`, `wp-step` (`▷φ ⊢ wp step {_. φ}`), and the derived `wp-rec`. Hoare triples are encoded as `□(φ −∗ wp e {x. ψ})`.
- The paper's comparison with Iris's rules: the first four entailments "are exactly the same as the corresponding rules in Iris"; `wp-set` and `wp-new` lack the later modality that Iris's rules carry, "because every operation in Iris takes a step, but in our semantics, only operations that semantically correspond to unfolding a recursive domain equation do"; and "whilst Iris has a rule for β-reduction of functions, we do not ... rather than having a rule stating that `wp (e[v/x]) {y. φ} ⊢ wp ((λx. e) v) {y. φ}`, the two propositions are actually convertible."

### 4. How the model solves the higher-order-store domain equation without syntactic step indices

Basis: normative for the construction (§4.1–§4.2 of the Tulip paper); documentation for the lineage; derived for the comparison paragraph.

**Metalanguage.** iGDTT is "roughly the extension of extensional guarded dependent type theory by additional (impredicative) universe structure": predicative universes `Type₀ : Type₁ : …`, and impredicative `Set, Prop : Type₀` with `Prop ⊆ Set` and `Prop` not an element of `Set`. Every universe is closed under a later modality `▶` with `next`, presented with delayed substitutions, and a Löb recursor `gfix : (▶A → A) → A` with `gfix f = f (next (gfix f))`.

**Guarded domains.** A guarded domain is an algebra `ϑ_X : ▶X → X`. Each universe `U` is one (`ϑ_U` sends `A : ▶U` to `▶[Z ← A].Z`), which is what allows domain equations to be solved as fixed points on universes. The guarded lift is `LA = gfix(λX. A + ϑ_U X) = A + ▶LA`.

**Models and consistency.** Theorem 4.5 (attributed to Sterling–Gratzer–Birkedal): for a separated intuitionistic well-founded poset `(O, ≤, ≺)` in a realizability topos `S`, internal presheaves `[O^op, S]` model iGDTT, with `Set` and `Prop` interpreted by Hofmann–Streicher liftings of modest sets and `¬¬`-closed propositions and with `(▶A)u = lim_{v≺u} A v`. The simplest instance is the topos of trees constructed internally to the effective topos. Corollary 4.7: iGDTT is consistent.

**Worlds and types.** With finite maps defined constructively (Definitions 4.9–4.10), the paper solves

```text
W = ℕ ⇀fin ▶S_p        S_p = [W, Set]        S_ℓ = [W, Type]
```

"A world [is] a finite mapping from memory locations to delayed semantic program types, which are defined to be Set-valued co-presheaves on the poset of semantic worlds." The paper states that "the impredicativity of Set is essential for `S_p` to be cartesian closed and therefore capable of modelling function types": exponentials of co-presheaves are sets of `W`-indexed natural transformations, and `W` is not `Set`-small.

**Type formers.** `μF = gfix(ϑ ∘ ▶F)`; `ref A w = { ℓ ∈ |w| | w ℓ = next A }`; `(TA)w = ∀w′≥w. tH w′ → L ∃w″≥w′. tH w″ × A w″`, where `tH w` is the type of total heaps at `w` and heaplets are `H(w⁻, w⁺) = ∏_{l∈|w⁻|} ▶[Z ← w⁻ l].Z w⁺` (values are stored under `▶`). Consequently `set` "returns immediately in the guarded lift monad via the unit `η`, whereas `get` takes a single step via the `▶`-algebra map `ϑ`", which is what the `step` in `get-after-set` and the `▷` in `wp-get` record.

**Lineage of the same equation.**

- Sterling–Gratzer–Birkedal explain why a denotational version needed impredicativity: the standard indexed state monad `(TA)w = ∏_{w′≥w} H w′ → ∑_{w″≥w′} H w″ × A w″` "runs into obvious size problems", a problem "side-stepped in operational models, where `U` is replaced by a set of predicates on syntactical expressions"; "operational methods worked ... only because the set of predicates is a complete lattice". Their solution replaces `∏/∑` by `∀/∃` in an impredicative universe.
- Birkedal–Møgelberg–Schwinghammer–Støvring, §3, construct "a model of a programming language with higher-order store and recursive types entirely inside the internal logic" of the topos of trees `S`, with `T̂ = μX. ▶((ℕ →fin X) →mon P(Value))`, `W = ℕ →fin T̂`, `T = W →mon P(Value)`. `Value` is a set of *syntactic* values, the reduction relation `step` "is defined on untyped configurations", and computation is specified by a guarded predicate `eval(t, s, Q) ⇔ (t ∈ Value ∧ Q(t, s)) ∨ (∃t₁ s₁. step((t,s),(t₁,s₁)) ∧ ▷ eval(t₁, s₁, Q))`: "we postulate that one evaluation step in the programming language actually takes one unit of time in the sense of the internal logic." Viewed externally this is "a standard, step-indexed model" (Proposition 3.6).
- Birkedal–Reus–Schwinghammer–Støvring–Thamsborg–Yang solve `T̂ ≅ ½ · ((ℕ ⇀fin T̂) →mon Pred(V))` in complete bounded ultrametric spaces by the America–Rutten theorem, with `UPred(Val) = { p ⊆ ℕ × Val | ∀(k, v) ∈ p. ∀j ≤ k. (j, v) ∈ p }`, and stress that the recipe "is not tied to domain theory and denotational semantics, but it can also be used with operational semantics".
- The two presentations are the same mathematics: BMSS Proposition 5.1 gives an equivalence between the total objects of `S` and bisected complete bounded ultrametric spaces, under which `▶` corresponds to scaling distances by ½ (except on the empty space).

**Derived reading.** "Without syntax-level step-indexing" has a precise and limited meaning. (i) Indices never appear in Tulip's statements: recursion in worlds, types and programs is handled by `▶` and `gfix` of the metalanguage. (ii) Programs denote elements of `TA` built from the guarded lift, not sets of syntactic values indexed by a reduction relation; no `step` relation on syntax exists in the paper. (iii) Step-indexing does not disappear: it resurfaces as the `step` instruction in the equational theory and `▷` in the logic, attached only to `get`, `unfold` and recursive calls rather than to every reduction.

### 5. The BI-hyperdoctrine

Basis: normative (Tulip §4.2.3–§4.4); documentation (Biering–Birkedal–Torp-Smith technical report §5).

**Definition used.** In the technical report, a first-order hyperdoctrine over a category `C` with finite products is a functor `P : C^op → Poset` whose fibres are Heyting algebras and whose reindexing maps are Heyting homomorphisms, with an equality predicate satisfying `⊤ ≤ P(Δ_X)(A) iff =_X ≤ A`, and with left and right adjoints `(∃X)_Γ ⊣ P(π) ⊣ (∀X)_Γ` to reindexing along projections that "are natural in `Γ`" (the commuting squares usually called the Beck–Chevalley condition; the report does not use that name). A *BI hyperdoctrine* additionally has BI-algebra fibres and BI-homomorphic reindexing, a cartesian closed base, and a BI algebra `B` with a natural bijection `Θ_X : Obj(P(X)) ≃ C(X, B)`. Example 2 of the report: any complete BI algebra `B` gives a BI hyperdoctrine over `Set` with `P(X) = B^X`, reindexing by composition, and quantifiers by joins and meets. Theorem 3 of the report: if the subobject hyperdoctrine of a topos is a BI hyperdoctrine, its BI structure is trivial (`φ ∗ ψ ↔ φ ∧ ψ`) — the reason predicates must be valued in a separate object `B` rather than in the subobject classifier.

**Tulip's instance.**

- `Prop_W w = [w ↓ W, Prop]` is the Hofmann–Streicher lifting of `Prop` into `S_ℓ`; `B = [pH, Prop_W]` is the internal poset of `Prop_W`-valued co-presheaves on the partial commutative monoid `pH` of partial heaps under its extension order.
- Lemma 4.18 / Corollary 4.19: `Prop_W` and `B` are complete Heyting algebras in `S_ℓ`; the proof notes that internal quantification over a lifted universe "automatically satisfies the appropriate Beck–Chevalley conditions when externalized".
- Constructions 4.20–4.21: the BI structure `(∗, −∗)` on `B` is the Day convolution of the promonoidal structure induced by the partial multiplication on `pH`.
- `□` is reindexing along `h ↦ ∅`; `▷` is pointwise; points-to is representable: `h ⊨ [ℓ ↪ a] ⇔ {ℓ ↦ next a} ≤ h`.
- `wp` is, for each semantic program type `A`, "a natural transformation `wp_A : B^A × TA → B`"; its forcing clause quantifies over every larger world, every frame `h_f`, and every total heap `h_t = h_f · h`, and requires the lifted computation `u w′ h_t` to return only configurations that satisfy the postcondition and leave the frame intact.
- Interpretation of judgements (§4.2.4): elements `Ξ | Γ ⊢ a : A` are elements `⟦a⟧ : ∏_ξ ⟦Γ⟧ξ → ⟦A⟧ξ`; propositions are predicates `⟦φ⟧ : ∏_ξ B^{⟦Γ⟧ξ}`; entailments are inequalities in `B^{⟦Γ⟧ξ}`.
- Theorem 4.24 (Soundness): derivable entailments hold as inequalities. Proof as given: "Since `B^•` is a BI-hyperdoctrine, all the specified rules of higher-order separation logic are valid, and the rules for the modalities follow similarly. What remains is to verify rules for weakest preconditions; we show just one illustrative case" (Lemma 4.25, the `get` rule, via two layers of Kripke–Joyal translation). Corollary 4.26 (Consistency): not `⊤ ≤ ⊥`.

### 6. Why congruence under binders falls out of the hyperdoctrine, and what the operational side must add

Basis: normative (Tulip rules); documentation (Iris article, BMSS, Frumin–Timany–Birkedal); source (Iris Coq files); derived (the structural explanation).

**Denotational side (derived from Finding 5).**

1. A proposition in context `Γ` is an element of the fibre over `⟦Γ⟧`. It has no access to the syntax of the terms substituted into it, only to the base morphisms they denote.
2. Substitution `φ[a/x]` is reindexing along `⟨id, ⟦a⟧⟩`. Reindexing is a function of the base morphism, so `⟦a⟧ = ⟦a′⟧` gives `φ[a/x] = φ[a′/x]` for every `φ`, with no side condition on `φ`.
3. Binders are interpreted by universal properties of the base category. `λ` is the exponential transpose in the cartesian closed `S_ι`, a bijection on hom-sets natural in `Γ`; so equal bodies give equal abstractions (the ξ rule), and β and η hold as equalities of morphisms. The body of `x ← u; v` is handled by the strength of `T`.
4. Quantifiers are adjoints to weakening and commute with reindexing (Beck–Chevalley), so substitution passes under `∀x`/`∃x` without a syntactic capture argument; Frobenius reciprocity for `∃` against `∧` and `∗` is what lets a quantifier be moved across a conjunct that does not mention the bound variable.
5. `wp_A` is a natural transformation on `TA`. `wp e {x. φ}` therefore depends on `e` only through `⟦e⟧ : ⟦Γ⟧ → T⟦A⟧`, and inherits invariance under every equation of the object language, wherever in `e` the rewrite occurs.

Tulip still has a rule named `wp-bind`, but it concerns the monadic sequencing `x ← e₁; e₂`, carries no evaluation-context side condition, and corresponds to Kleisli composition in the model.

**Operational side.**

- Iris (JFP 2018, §6.1): expressions `e`, values `v`, evaluation contexts `K ::= • | K(e) | v(K) | assert(K) | ref(K) | !K | K ← e | v ← K | CAS(…) | …`. No production places the hole under `λ`. Head reduction is lifted to thread-local reduction "using evaluation contexts".
- `wp e {Φ}` is defined as a guarded fixed point over the reduction relation: either `e` is a value satisfying `Φ`, or `e` is reducible and every successor satisfies the weakest precondition under `▷`. "This 'ties' the steps of the program to the step-indices implicit in the logic, by adding another `▷` for every program step."
- Fig. 13 gives `WP-BIND`: `wp e {v. wp K[v] {Φ}} ⊢ wp K[e] {Φ}` and `WP-λ`: `▷ wp e[v/x] {Φ} ⊢ wp (λx.e)v {Φ}`. `WP-WAND` and `WP-BIND` are proved by Löb induction.
- In the generic version (§7.3) weakest preconditions are "parameterized by a language, which consists of" expressions, values, states and a per-thread step relation. In the Coq development at tag `iris-4.3.0`, the bind lemma is stated for any `K` with a `LanguageCtx` instance:

```text
Class LanguageCtx {Λ : language} (K : expr Λ → expr Λ) := {
  fill_not_val e : to_val e = None → to_val (K e) = None;
  fill_step e1 σ1 κ e2 σ2 efs :
    prim_step e1 σ1 κ e2 σ2 efs → prim_step (K e1) σ1 κ (K e2) σ2 efs;
  fill_step_inv e1' σ1 κ e2 σ2 efs :
    to_val e1' = None → prim_step (K e1') σ1 κ e2 σ2 efs →
    ∃ e2', e2 = K e2' ∧ prim_step e1' σ1 κ e2' σ2 efs }.

Lemma wp_bind K `{!LanguageCtx K} s E e Φ :
  WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }} ⊢ WP K e @ s; E {{ Φ }}.
```

- The same lemma appears when the *model* is synthetic but computation is still operational: BMSS Proposition 3.2 states that `eval(E[t], s, Q)` holds iff `eval(t, s, λ(v₁, s₁). eval(E[v₁], s₁, Q))`, "for all evaluation contexts `E`".
- It also appears when the *programs* are denotations but the weakest precondition is defined over a reduction relation on those denotations: in Frumin–Timany–Birkedal, "homomorphisms play the role of evaluation contexts" (Lemmas 4.3–4.4 state that homomorphisms preserve and reflect reductions), the rule `wp-hom` is the bind rule, and continuation-independence of effects "is crucial for proving Lemma 4.4"; restricting to such effects "preclude[s] us from modeling call/cc, but allows us to use the bind rule".

**Derived conclusion.** The dividing line is not "denotational versus operational syntax" but *what the weakest precondition is a function of*. If it is a function of the denotation (Tulip), invariance under the equational theory is inherited and no context law is needed. If it is defined by recursion over a step relation — on raw syntax (Iris, BMSS §3) or on denotations (guarded interaction trees) — a bind rule exists only for contexts that are uniform with respect to that relation, and reasoning under a binder needs a separate argument. Tulip's own statement of the contrast: "In a conventional operationally-based program logic, equational reasoning is rather only applicable within the focus of a Hoare triple and is moreover limited to operational head reduction and cannot occur under binders, etc."

For relational frameworks (simulations, bisimulations, logical relations over a labelled transition system) the analogous statement — that closure under program contexts is a per-construct compatibility obligation rather than a consequence of the definition — is a derived expectation from the same structure; no relational development was examined for this report.

### 7. Toy mechanisation: automatic congruence versus explicit context laws

Basis: execution (Lean `v4.34.1` kernel, build and axiom audit recorded under **Evidence**) and derived (the reading of each theorem). All results in this finding are `[kernel-checked proof]` `[toy model]`. **Model–system relation: none proved.**

**What is modelled.**

- `lean/Toy/BI.lean`: a separation algebra given by a ternary relation `join` with unit; step-indexed propositions `SProp S` (families `Nat → S.M → Prop` down-closed in the index); connectives `∧ ∨ ⇒ ∀ ∃ emp ∗ −∗ ▷`; the finite-step ultrametric relation `distLt n φ ψ` (agreement at all indices below `n`).
- `lean/Toy/Hyperdoctrine.lean`: the fibre `Pred S Γ = Γ → SProp S` over a type `Γ`, reindexing by precomposition, quantifiers along projections, an equality predicate.
- `lean/Toy/Syntax.lean`: an intrinsically typed λ-calculus with types `nat`, `A → B`, `comp A`; terms `var`, `lit`, `lam`, `app`, `ret`, `bind`, `tick`; renaming and simultaneous substitution; a denotation with `⟦comp A⟧ = Nat × ⟦A⟧` (a tick count and a result); and an equational theory `Conv` containing β, η, the three monad laws, commutation of `tick` with `bind`, and congruence for every term former including `lam` and the body of `bind`.
- `lean/Toy/Logic.lean`: predicates in context as fibre elements over semantic environments, substitution as reindexing along the denotation of a substitution, and `wp e Φ` defined from the denotation of `e` by `wpSem (k, a) Φ = ▷ᵏ (Φ a)`.
- `lean/Toy/Operational.lean`: an abstract operational language (expressions, Boolean value test, step relation), a step-indexed operational weakest precondition `wpo` that consumes one index per step and whose postconditions range over raw expressions, the three context laws of Finding 6 as a structure `CtxLaws`, and the instance given by call-by-name reduction on the closed terms of `Syntax.lean`.
- `lean/Toy/Adequacy.lean`: soundness of operational steps with respect to the denotation.

**(a) Automatic substitution and binder congruence.**

| Theorem | Statement (informal) |
|---|---|
| `Pred.reidx_id`, `Pred.reidx_comp` | Reindexing is strictly functorial. |
| `Pred.reidx_and`, `reidx_imp`, `reidx_sep`, `reidx_wand`, `reidx_later` | Reindexing preserves every connective and `▷` (it is a BI-algebra homomorphism). |
| `Pred.ex_adj`, `Pred.all_adj` | `∃ ⊣ π* ⊣ ∀`. |
| `Pred.beck_chevalley_ex`, `Pred.beck_chevalley_all` | Reindexing commutes with both quantifiers. |
| `Pred.frobenius_and`, `Pred.frobenius_sep` | `∃x.(φ ∧ π*ψ) = (∃x.φ) ∧ ψ` and `∃x.(φ ∗ π*ψ) = (∃x.φ) ∗ ψ`. |
| `Pred.lawvere_eq` | `⊤ ≤ Δ*(A)` iff `=_X ≤ A`. |
| `Tm.eval_sub`, `Sub.den_comp` | Syntactic substitution denotes reindexing; composition of substitutions denotes composition. |
| `Conv.sound` | Convertible terms denote the same function of the environment. The `lam` and `bind` cases are congruence under a binder. |
| `substP_congr`, `subst1_congr` | If `u ≡ v` then `φ[u/x] = φ[v/x]` as fibre elements, for every `φ`. |
| `substP_forallT`, `substP_existsT`, `substP_wp` | `(∀x.φ)[σ] = ∀x.φ[σ↑]`, likewise `∃`, and `(wp e Φ)[σ] = wp (e[σ]) (Φ[σ↑])`. |
| `wp_congr` | If `e ≡ e′` then `wp e Φ = wp e′ Φ` for every `Φ`. |
| `wp_beta` | `wp ((λx.b) a) Φ = wp (b[a/x]) Φ` — an equality, not a rule with a `▷`. |
| `wp_ret_lam_congr`, `wp_bind_body_congr` | Rewriting under `λ` inside a returned closure, or in the body of a bind, leaves `wp` unchanged. |
| `wpSem_ret`, `wpSem_bind`, `wpSem_tick`, `wpSem_frame`, `wpSem_wand` | Toy analogues of `wp-val`, `wp-bind` (an equality), `wp-step` (`▷ wp ⊢ wp (tick …)`), framing, and `wp-wand`. |

No theorem in this group has a hypothesis about evaluation contexts. `wp_congr` is a one-line consequence of `Conv.sound`; the content is in `Conv.sound` and the substitution lemma.

**Supporting facts about `▷` and the ultrametric.** `SProp.later_intro`, `later_and`, `later_sep`, `later_wand` (the four later rules listed in Finding 3), `SProp.loeb` and `SProp.loeb_internal` (`(▷φ ⇒ φ) ⊢ φ`), `SProp.later_bot_not_bot` (`▷⊥ ⊬ ⊥`), `SProp.later_ex_of_inhabited` (`▷∃ ⊢ ∃▷` needs an inhabitant), `SProp.later_contractive`, `SProp.guarded_fixpoint_unique`, and `SProp.gfix_unfold` (every contractive map on `SProp S` has a fixed point, built as the diagonal of its finite approximants). `sep_ne_and` exhibits a separation algebra (naturals under addition) in which `φ ∧ φ ⊬ φ ∗ φ`, so the BI structure is not the cartesian one.

**(b) The operational contrast.**

| Theorem | Statement (informal) |
|---|---|
| `wpo_bind` | For languages `L₁`, `L₂` and `K : L₁.Expr → L₂.Expr` satisfying `CtxLaws`, `wpo L₁ n e (fun v m => wpo L₂ m (K v) Φ) → wpo L₂ n (K e) Φ` for all `n`, `e`, `Φ`. |
| `appCtx_laws`, `wpo_bind_app` | The application context `• a` satisfies `CtxLaws`, so the bind rule holds for it. |
| `lamCtx_not_ctxLaws` | The context `λ_. •` does not satisfy `CtxLaws`: `(λx.x) 0` steps to `0`, but `λ_. (λx.x) 0` is a value and does not step (`fill_step` fails). |
| `wpo_bind_fails_under_lam` | There is a postcondition `Φ` for which the premise of the bind rule holds for `λ_. •` at `e = (λx.x) 0`, `n = 1`, and its conclusion is false. |
| `operational_predicate_distinguishes` | A predicate on raw closed terms holds of `λ_. 0` and fails of `λ_. (λx.x) 0`. |
| `lamCtx_conv`, `denotational_predicate_cannot_distinguish`, `wp_agrees_under_lam` | The same two terms are convertible (β under the binder), no predicate on denotations separates them, and the denotational `wp` of the two returned closures is equal for every postcondition. |

The witness postcondition in `wpo_bind_fails_under_lam` is the syntactic predicate "is the term `λ_. 0`". This matches the observation in the Tulip introduction that "a predicate on raw syntax need not even be invariant under α-equivalence" while "a predicate on denotations is automatically invariant under the entire equational theory of the language"; it does not show that every behavioural postcondition would fail.

**Soundness half of adequacy for the toy.** `Step.sound` and `Steps.sound`: each operational step leaves a non-computation denotation unchanged and, at computation type, preserves the result and lowers the tick count by at most one. `Steps.ret_sound`: if a closed computation reduces to `ret v`, the result component of its denotation is the denotation of `v`. The converse direction (from the denotation to operational termination) is not mechanised.

### 8. The equational theory is intensional

Basis: normative (Tulip §2.1.2, §5.3); documentation (Sterling–Gratzer–Birkedal §6).

- Reads and unfoldings leave `step` behind (Finding 2), so `set u v; get u` and `set u v; ret v` are *not* equal in the theory; they differ by one `step`.
- Allocation is observable. Sterling–Gratzer–Birkedal: "Ours is a model of global state and allocation: thus the denotations of `(r ← new 5; ret ())` and `ret ()` are distinct", and "it is not possible in our model to exhibit a correspondence between two programs that allocate differently, even if this does not affect their observable behavior"; swapping independent allocations and dropping inactive ones are listed as future work.
- Tulip §5.3: "conventional operationally-based program logics do not use equational reasoning at all: our logic, in contrast, allows some equational reasoning but it is limited by the intensionality of Sterling et al.'s model", with making the model "less intensional" proposed as future work.

Derived: "automatically invariant under the equational congruence" should be read with the equational congruence being this intensional theory. It is strictly finer than contextual equivalence for any notion of observation that ignores abstract steps or unreachable allocations.

### 9. Adequacy: what is and is not established

Basis: normative/documentation (texts cited); derived (the gap analysis).

**Established in the Tulip paper.** Theorem 4.24 and Corollary 4.26, introduced by "The following results are stated internally to iGDTT", together with the remark in §1.2: "Because iGDTT itself is sound, it follows that our logic is sound." These say that the rules are valid in the model and that the model is not degenerate.

**Not present in the Tulip paper.** A small-step or big-step semantics for F^ref_μ; any statement of the form "if `⊤ ⊢ wp e {φ}` then every execution of `e` is safe and ends in a value satisfying `φ`"; any statement relating judgemental or propositional equality to contextual equivalence. The word "adequacy" does not occur in the v2 text, and "operational semantics" occurs only in the abstract and introduction, describing other logics.

**Not supplied by the underlying model paper.** Sterling–Gratzer–Birkedal use "globally adequate" for a property of models of guarded type theory ("the global points of ℕ are the actual natural numbers"), not for computational adequacy of the store model against an operational semantics.

**The operational comparator.** *Iris from the ground up*, Theorem 6: if `True ⊢ wp e {φ}` for a first-order `φ` and `(e, σ) →*_tp (e′₁ … e′ₙ, σ′)`, then every `e′ᵢ` is a value or reducible, and if the main thread `e′₁` is a value `v` then `φ(v)`. Theorem 7 generalises this to an arbitrary language and state interpretation. The connection to executions is the stated purpose: "to demonstrate that our weakest preconditions actually make the expected statements about program executions".

**Adequacy for neighbouring guarded denotational models.**

- Møgelberg–Paviotti (FPC, in guarded dependent type theory): "The denotational semantics is intensional in the sense that it counts the number of unfold-fold reductions"; the operational semantics must count the same reductions, and the exact correspondence uses a step-synchronised relation: "The adequacy theorem states that `M ⇒ᵏ ⟨⟩` if and only if `⟦M⟧ = δᵏ⟦⟨⟩⟧`", proved by "a logical relation between syntax and semantics" whose recursive-type case "is simply a guarded recursive type". A second relation on global (clock-quantified) denotations relates computations that differ only in step count and is sound for contextual equivalence.
- Frumin–Timany–Birkedal (a PCF-like language with effects, in Iris): Theorem 5.1 (Soundness) `(e₁, σ₁) → (e₂, σ₂)` implies `(⟦e₁⟧, σ₁) ⇝* (⟦e₂⟧, σ₂)`; Theorem 7.1 (Adequacy) if `⊢ e : Nat` and `(⟦e⟧, σ) ⇝* (Ret(n), σ′)` then `(e, σ) →* (n, σ′)`, proved "using a logical relation defined using the separation logic" and Iris's own adequacy theorem.

**Derived gap analysis.** To state for Tulip what Iris's Theorem 6 states, three ingredients absent from the paper would be needed: an operational semantics for monadic F^ref_μ whose step counting matches the placement of `step`; a logical relation between that syntax and the world-indexed model at all types including `ref`, `μ`, `∀` and `∃`; and an externalisation of the iGDTT-internal statement to a statement about ordinary executions. Whether these go through for the full language is not established by any source examined here.

### 10. Structural boundaries where operational logics outperform Tulip

Basis: normative/documentation where quoted; derived where marked.

**Concurrency and interleaving.** The Tulip introduction lists "the combination of general references, polymorphism, and concurrency" among the questions denotational methods have historically failed to answer simply. §5.1: Iris, the Verified Software Toolchain and TaDA incorporate "constructs such as invariants and higher-order ghost state which are critical for reasoning about concurrent programs. For the sake of simplicity, we have restricted our attention to a fixed notion of resource (partial heaps)", with parity left to future work. Derived: the monad `T` is a store-passing function into a guarded lift; it has no thread pool and no interleaving, so there is nothing for an invariant to protect. Iris's language has `fork` and `CAS`, a thread-pool reduction that "is an interleaving semantics", rules `WP-FORK` and invariant opening around atomic expressions, and an adequacy theorem quantified over all interleavings.

**Non-determinism.** Derived: `(TA)w` assigns to each heap one element of `L(…)`, and `L A = A + ▶LA` has no branching, so the model is deterministic. On the operational side BMSS §3.6 remark that their deterministic choice was "for simplicity" and that a non-deterministic language needs only an `eval` predicate that quantifies universally over steps and rules out errors explicitly; Iris's weakest precondition already quantifies over all successors.

**Untyped and low-level memory.** Derived from §4.2: a world maps each location to a delayed *semantic program type*, and `ref A w` is the set of locations whose world entry equals `next A`. Locations have no arithmetic and no byte representation, a cell cannot be reinterpreted at another type, and there is no deallocation (global store, Remark 2.2). The paper notes that "the state of the art in denotational semantics for local store is currently restricted to references of ground type". An operational logic parameterised by arbitrary `Expr`, `Val`, `State` and step relation, with a user-chosen state interpretation `S : State → iProp` (Iris §7.3), places no such typing requirement on memory; that parameterisation is the hook through which machine states, byte-addressed memories and foreign-function boundaries can be given a program logic. No such low-level instantiation was examined for this report.

**Cross-language correspondence.** Derived: Tulip's logic is unary and its equality relates two terms of the same type in the same equational theory. It has no judgement relating a program in one language to a program in another, which is the basic shape of a compiler-correctness simulation. Sterling–Gratzer–Birkedal add a relational layer inside the type theory (the "logical relations as types" principle, combining "weak bisimulation for computation steps with parametricity"), which Tulip does not import; Frumin–Timany–Birkedal state that a theory of weak bisimilarity for guarded interaction trees "is still an open question, complicated by issues with step-indices".

**Executability, tooling and mechanisation.** §5.3: "Another question is how Tulip can be implemented in a practical tool. Currently, definitional and logical equality coincide due to equality reflection, which leads the former to become undecidable." The paper reports no machine-checked formalisation. Iris: "All results in this paper, including adequacy and soundness of Iris as well as the derived constructions like weakest preconditions and invariants, have been formalized using Coq." A counterpoint from the lineage: Møgelberg–Paviotti show that a guarded denotational semantics can be executed inside type theory with a time-out and agrees with the operational semantics on Boolean programs, so non-executability is a property of Tulip as published, not of the guarded denotational approach.

**Where Tulip is ahead (for balance).** Typed predicates: a postcondition over `A → T B` is a predicate on semantic functions, not on closure syntax. Equational rewriting anywhere in a term, including under binders, at no proof cost. Fewer `▷` obligations: only `get`, `unfold`, recursion and explicit `step` consume a later. A modular semantic construction (Day convolution over a partial commutative monoid in a presheaf model) rather than a logic-specific fixed point over syntax.

## Boundaries

**Model–system relation: none proved.** The Lean development under `lean/` is a toy. In particular:

- **Known not to apply.** The toy has no heap, no points-to assertion, no `new`/`get`/`set`, no recursive or polymorphic types, no world-indexed presheaves and no recursively defined worlds; it therefore does not model the higher-order-store domain equation at all. Its base category is Lean's `Type` with functions, and its step indices are explicit natural numbers rather than a synthetic `▶`. Its BI algebra is non-affine with an explicit `emp`, whereas Tulip's logic is affine with unit `⊤`; the persistence modality is omitted. `⟦comp A⟧ = Nat × ⟦A⟧` contains only terminating computations, so partial correctness and total correctness coincide in the toy and Löb induction is never needed for a toy program. `Conv` has no equality reflection.
- **Known not to apply.** `wpo` is a unary, index-explicit predicate with progress and one index per step. It is not Iris's weakest precondition: it has no state, state interpretation, update modality, mask, fork, or ghost resource. `CtxLaws` mirrors the three fields of Iris's `LanguageCtx` without states, observations or forked threads.
- **Attractive stronger reading ruled out.** `wpo_bind_fails_under_lam` uses a syntactic postcondition. It shows that an operational weakest precondition with postconditions over raw expressions cannot have a bind rule for `λ_. •`; it does not show failure for postconditions restricted to behavioural (extensional) properties, and it does not show that operational logics cannot reason under binders by other means, such as a separately proved logical relation.
- **Attractive stronger reading ruled out.** `Step.sound`/`Steps.sound` are the easy half of an adequacy argument for the toy. The toy proves no computational adequacy, no statement relating `wp` to `wpo`, and nothing about contextual equivalence.

About the examined literature:

- **Not examined.** arXiv v1 of the Tulip paper; the typeset TOPLAS version of the BI-hyperdoctrine paper; the full model construction of Sterling–Gratzer–Birkedal beyond the passages listed under **Applicability**; the Iris Coq development beyond the two cited definitions; Simuliris and other relational operational frameworks; Paviotti–Møgelberg–Birkedal (*A model of PCF in guarded type theory*) and Bizjak–Birkedal (*On models of higher-order separation logic*), whose bibliographic metadata was verified but whose text was not read; work published after the Tulip paper that may extend it.
- **Unknown.** Whether a computational adequacy theorem for the Tulip model, a concurrent extension, a machine-checked formalisation, or a decidable-equality variant exists elsewhere. Whether the equational theory is complete for the model. Whether the ingredients listed in Finding 9 go through for full F^ref_μ.
- **Unsupported (stated by the paper).** Concurrency, invariants and higher-order ghost state; resources other than partial heaps; local store; an implementation with decidable definitional equality.
- **Known not to apply.** Tulip's invariance under its equational theory does not give invariance under contextual equivalence (Finding 8). Soundness and consistency (Theorem 4.24, Corollary 4.26) do not give an execution-level safety statement (Finding 9).

Stronger conclusions the evidence does not establish:

- That denotational program logics make evaluation-context reasoning unnecessary in general. Guarded interaction trees are denotational and still need a bind rule restricted to homomorphisms and continuation-independent effects (Finding 6).
- That Tulip removes step-indexing. It relocates it to `step` in the equational theory and `▷` in the logic (Findings 3 and 4).
- That Tulip proofs are substantially shorter than Iris proofs. The only reported comparison is one example, described by the authors as "perhaps slightly simpler".
- That the per-construct compatibility burden attributed to simulation frameworks in Finding 6 has been checked against any such framework.

## Evidence

All web evidence was acquired on 2026-11-22.

### Primary and lineage sources

| # | Work | Identity (verified) | Text examined; SHA-256 of the fetched file |
|---|---|---|---|
| 1 | F. L. Aagaard, J. Sterling, L. Birkedal, *A denotationally-based program logic for higher-order store* | arXiv `2308.02906v2` (v1 2023-08-05, v2 2023-11-17); ENTICS vol. 3, Proc. MFPS XXXIX, `entics:12232`; DOI `10.46298/entics.12232`; `https://arxiv.org/abs/2308.02906v2` | `https://arxiv.org/pdf/2308.02906v2`, 21 pages, `d49e526ae4675630e883ec328fb8582458ac2049f13ce476dece23da39c0eb29` |
| 2 | J. Sterling, D. Gratzer, L. Birkedal, *Denotational semantics of general store and polymorphism* | arXiv `2210.02169v2` (v1 2022-10-05, v2 2023-04-12) | `https://arxiv.org/pdf/2210.02169`, `2b89def097c1c8752bb8a2b8be8217fee3b20e3f385df08f4a09655c8c99dde9` |
| 3 | B. Biering, L. Birkedal, N. Torp-Smith, *BI-hyperdoctrines, higher-order separation logic, and abstraction* | ACM TOPLAS 29(5), article 24, 2007; DOI `10.1145/1275497.1275499` | Technical report ITU-TR-2005-69 (July 2005), `https://cs.au.dk/~birke/papers/ITU-TR-2005-69.pdf`, `9e796e8a2ebd44d5c0b7816775d57c88d5ae78334dee03c0f23196461ad0f5e8` |
| 4 | L. Birkedal, R. E. Møgelberg, J. Schwinghammer, K. Støvring, *First steps in synthetic guarded domain theory: step-indexing in the topos of trees* | LICS 2011, pp. 55–64, DOI `10.1109/LICS.2011.16`; LMCS 8(4:1), 2012, DOI `10.2168/LMCS-8(4:1)2012`; arXiv `1208.3596v2` | `https://arxiv.org/pdf/1208.3596`, 45 pages, `95e56891d8e11804e5f3ffc6c5a3ae6a96bda728c130b73d4fcb382751444a3e` |
| 5 | L. Birkedal, B. Reus, J. Schwinghammer, K. Støvring, J. Thamsborg, H. Yang, *Step-indexed Kripke models over recursive worlds* | POPL 2011, pp. 119–132; DOI `10.1145/1926385.1926401` | `https://cs.au.dk/~birke/papers/step-recworld-conf.pdf`, `80d3dc0f8dae9cb8abe2af10106dac25f8ea4706069d4bcf73a66fe1804da529` |
| 6 | R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal, D. Dreyer, *Iris from the ground up: A modular foundation for higher-order concurrent separation logic* | Journal of Functional Programming 28, e20, 2018; DOI `10.1017/S0956796818000151` | `https://people.mpi-sws.org/~dreyer/papers/iris-ground-up/paper.pdf`, 60 pages, `3354466a1872726a91d927ea7daaa905333f06bbfc0c376cccb2cfdcabad3d80` |
| 7 | Iris Coq development | `https://gitlab.mpi-sws.org/iris/iris`, tag `iris-4.3.0`, commit `3d176f124f708e7325a362722c3d2b3957e3675d` | `iris/program_logic/language.v` (`3bc0025d1f9ac5dc6e5f39689ab09511395b6558bbaa9e4a18610e01370ab440`), lines 46–55; `iris/program_logic/weakestpre.v` (`dc0e2948b7465159097f9522476156936f6fb1b23481b63c0282338d01a53623`), lines 277–278 |
| 8 | R. E. Møgelberg, M. Paviotti, *Denotational semantics of recursive types in synthetic guarded domain theory* | LICS 2016, pp. 317–326, DOI `10.1145/2933575.2934516`; extended version arXiv `1805.00289v2` | `https://arxiv.org/pdf/1805.00289v2`, 48 pages, `0fbfd92c66af5d2f7526969021904438152b3c9b06fe3459050adfdc0f4bae7b` |
| 9 | D. Frumin, A. Timany, L. Birkedal, *Modular denotational semantics for effects with guarded interaction trees* | Proc. ACM Program. Lang. 8(POPL), pp. 332–361, 2024; DOI `10.1145/3632854`; arXiv `2307.08514v2` | `https://arxiv.org/pdf/2307.08514`, `40d999b3e15d69b89037aac819d1b088daf7f806ea3ba26fbc32c82bb508325a` |

Metadata verified, text not examined: M. Paviotti, R. E. Møgelberg, L. Birkedal, *A model of PCF in guarded type theory*, ENTCS 319 (MFPS XXXI), pp. 333–349, 2015, DOI `10.1016/j.entcs.2015.12.020`; A. Bizjak, L. Birkedal, *On models of higher-order separation logic*, ENTCS 336, pp. 57–78, 2018, DOI `10.1016/j.entcs.2018.03.016`.

How identities were verified: arXiv identifiers, versions, dates and author lists from the arXiv abstract page and the arXiv export API; DOIs, venues, volumes and pages from the DOI registry metadata service (`https://api.crossref.org/works/<doi>`) and, for source 1, the episciences article page `https://entics.episciences.org/12232`; the Iris tag-to-commit mapping from the GitLab tags API. The SHA-256 values identify the bytes fetched on the acquisition date; arXiv may regenerate PDFs, so a differing hash for an arXiv PDF does not by itself indicate different content.

Locations of the key quotations in source 1 (v2 PDF page labels `1–n`): abstract and §1.2 (pp. 1–1, 1–2); rules of §2.1.2 (p. 1–4); Lawvere rule and equality reflection (p. 1–5); later modality rules (p. 1–6); weakest-precondition rules and the comparison with Iris (pp. 1–6, 1–7); Theorem 3.3 (p. 1–8); Theorem 4.5 and the world equation (pp. 1–11, 1–12); `B`, `Prop_W` and the interpretation of judgements (p. 1–13); `wp` forcing clause (p. 1–15); Theorem 4.24, Lemma 4.25, Corollary 4.26 (pp. 1–15, 1–16); §5 (pp. 1–16, 1–17); Lemma 4.18 proof (p. 1–21).

### Lean kernel audit

Toolchain: `leanprover/lean4:v4.34.1` (`lean/lean-toolchain`); no dependencies (`lean/lakefile.toml` declares only the library `Toy`). Source files: `lean/Toy.lean`, `lean/Toy/BI.lean`, `lean/Toy/Hyperdoctrine.lean`, `lean/Toy/Syntax.lean`, `lean/Toy/Logic.lean`, `lean/Toy/Operational.lean`, `lean/Toy/Adequacy.lean`, and the audit driver `lean/Audit.lean`. The sources contain no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe` or `partial` declarations. The complete recorded output of the audit run is `lean/audit/axioms.txt`.

Recorded run (2026-11-22), executed in a scratch copy of `lean/` after deleting any previous build directory:

```console
$ lake build
Build completed successfully (9 jobs).
$ lake env lean Audit.lean
```

`#print axioms` output for all 59 audited theorems, which include every theorem named in Finding 7 (verbatim axiom lists; `—` abbreviates the line `does not depend on any axioms`):

**BI algebra, later modality, ultrametric (`Toy/BI.lean`)**

| Theorem | `#print axioms` |
|---|---|
| `Toy.SProp.imp_adj` | — |
| `Toy.SProp.wand_adj` | — |
| `Toy.SProp.sep_assoc` | — |
| `Toy.SProp.later_intro` | — |
| `Toy.SProp.later_and` | — |
| `Toy.SProp.later_sep` | — |
| `Toy.SProp.later_wand` | — |
| `Toy.SProp.later_bot_not_bot` | — |
| `Toy.SProp.later_ex_of_inhabited` | — |
| `Toy.SProp.loeb` | — |
| `Toy.SProp.loeb_internal` | — |
| `Toy.SProp.later_contractive` | — |
| `Toy.SProp.guarded_fixpoint_unique` | `[propext, Quot.sound]` |
| `Toy.SProp.gfix_unfold` | `[propext, Quot.sound]` |
| `Toy.sep_ne_and` | `[propext, Quot.sound]` |

**Indexed BI algebra laws (`Toy/Hyperdoctrine.lean`)**

| Theorem | `#print axioms` |
|---|---|
| `Toy.Pred.reidx_id` | — |
| `Toy.Pred.reidx_comp` | — |
| `Toy.Pred.reidx_and` | — |
| `Toy.Pred.reidx_imp` | — |
| `Toy.Pred.reidx_sep` | — |
| `Toy.Pred.reidx_wand` | — |
| `Toy.Pred.reidx_later` | — |
| `Toy.Pred.ex_adj` | — |
| `Toy.Pred.all_adj` | — |
| `Toy.Pred.beck_chevalley_ex` | — |
| `Toy.Pred.beck_chevalley_all` | — |
| `Toy.Pred.frobenius_and` | `[propext, Quot.sound]` |
| `Toy.Pred.frobenius_sep` | `[propext, Quot.sound]` |
| `Toy.Pred.lawvere_eq` | — |

**Substitution lemma and equational soundness (`Toy/Syntax.lean`)**

| Theorem | `#print axioms` |
|---|---|
| `Toy.Tm.eval_sub` | `[Quot.sound]` |
| `Toy.Sub.den_comp` | `[Quot.sound]` |
| `Toy.Conv.sound` | `[propext, Quot.sound]` |

**(a) Automatic substitution and binder congruence; `wp` rules (`Toy/Logic.lean`)**

| Theorem | `#print axioms` |
|---|---|
| `Toy.substP_comp` | `[Quot.sound]` |
| `Toy.substP_congr` | `[propext, Quot.sound]` |
| `Toy.subst1_congr` | `[propext, Quot.sound]` |
| `Toy.substP_forallT` | `[Quot.sound]` |
| `Toy.substP_existsT` | `[Quot.sound]` |
| `Toy.substP_wp` | `[Quot.sound]` |
| `Toy.wp_congr` | `[propext, Quot.sound]` |
| `Toy.wp_beta` | `[propext, Quot.sound]` |
| `Toy.wp_ret_lam_congr` | `[propext, Quot.sound]` |
| `Toy.wp_bind_body_congr` | `[propext, Quot.sound]` |
| `Toy.wpSem_ret` | `[propext, Quot.sound]` |
| `Toy.wpSem_bind` | `[propext, Quot.sound]` |
| `Toy.wpSem_tick` | `[propext, Quot.sound]` |
| `Toy.wpSem_frame` | — |
| `Toy.wpSem_wand` | — |

**(b) Operational contrast (`Toy/Operational.lean`)**

| Theorem | `#print axioms` |
|---|---|
| `Toy.wpo_bind` | — |
| `Toy.appCtx_laws` | — |
| `Toy.wpo_bind_app` | — |
| `Toy.lamCtx_not_ctxLaws` | — |
| `Toy.wpo_bind_fails_under_lam` | — |
| `Toy.operational_predicate_distinguishes` | — |
| `Toy.lamCtx_conv` | — |
| `Toy.denotational_predicate_cannot_distinguish` | `[propext, Quot.sound]` |
| `Toy.wp_agrees_under_lam` | `[propext, Quot.sound]` |

**Soundness half of adequacy (`Toy/Adequacy.lean`)**

| Theorem | `#print axioms` |
|---|---|
| `Toy.Step.sound` | `[propext, Quot.sound]` |
| `Toy.Steps.sound` | `[propext, Quot.sound]` |
| `Toy.Steps.ret_sound` | `[propext, Quot.sound]` |

Totals: 59 theorems audited; 33 depend on no axioms; the remaining 26 depend only on `propext` and/or `Quot.sound` (propositional and function extensionality, used for equalities between fibre elements and between denotations). `Classical.choice` is not used anywhere. The operational theorems of group (b) (`wpo_bind`, `appCtx_laws`, `wpo_bind_app`, `lamCtx_not_ctxLaws`, `wpo_bind_fails_under_lam`, `operational_predicate_distinguishes`) depend on no axioms.

## Revalidation

1. **Rebuild and axiom-check the toy model** (cheapest check of Finding 7). From a copy of the package's `lean/` directory, so that no build directory is created inside the corpus:

   ```console
   cp -r lean /tmp/tulip-toy && cd /tmp/tulip-toy
   lake build
   lake env lean Audit.lean
   ```

   Expected: `lake build` prints `Build completed successfully (9 jobs).` with no warnings or errors, and the second command prints 59 lines, each either `does not depend on any axioms` or an axiom list that is a subset of `[propext, Quot.sound]`, identical to the lines recorded in `lean/audit/axioms.txt`. A passing run establishes only that the toy theorems are kernel-checked; it says nothing about Tulip or Iris.
2. **Version drift of the primary subject.** Open `https://arxiv.org/abs/2308.02906`. If a version later than v2 is listed, re-read §2.2.5 (the comparison with Iris's rules), §4.4 (Theorem 4.24, Corollary 4.26) and §5 before relying on Findings 3, 9 and 10.
3. **Adequacy status** (Finding 9). Search the v2 text for "adequa" (no occurrence) and for "operational semantics" (two occurrences, both in the abstract and introduction). To learn whether the gap has since been closed, search for later work by the same authors on program logics over synthetic guarded domain theory; this requires new research and is not a mechanical check.
4. **Context-lifting laws** (Finding 6). At the cited Iris tag, check that `Class LanguageCtx` in `iris/program_logic/language.v` still has exactly the fields `fill_not_val`, `fill_step`, `fill_step_inv` and that `wp_bind` in `iris/program_logic/weakestpre.v` still takes a `LanguageCtx K` instance. For a different Iris revision, diff those two declarations.
5. **Identity checks.** Resolve each DOI in the table above through the DOI registry and compare title, authors and venue; recompute the SHA-256 of the non-arXiv PDFs.
