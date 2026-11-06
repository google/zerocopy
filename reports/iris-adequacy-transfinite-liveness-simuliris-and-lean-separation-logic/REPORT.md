# Iris Adequacy, Transfinite Liveness, Simuliris Tree Borrows Replay, Lean Separation Logic, and Modular State-Alias Effects

## Summary

This report synthesizes seven primary-source and mechanically replayed investigations covering step-indexed and transfinite Iris adequacy, Rocq and Lean 4 separation-logic substrates (`iris/iris` `8e49095`, `leanprover-community/iris-lean` `81bc350`), Simuliris and Tree Borrows refinement replay (`simuliris` `e3abfcdc`), resource-algebra and lifetime logic interfaces (`Core.v`, `lft_contexts.v`, `bor_lemmas.v`, RefinedRust/Lithium `shim.v`, Actris `channel.v`, Steel `Steel.Memory.fsti`, Pulse `PulseCore.HeapSig.fsti`, VST `shares.v`), and algebraic-effect equational reasoning over heap and alias structure (`Effects.lean`, POPL 2025):

1. **Iris adequacy and resource interfaces (`iris/iris` `8e490956795f2ca9bcd2cfbc0fc65c3dc4bdce77`)**: In `iris/program_logic/adequacy.v` (`lines 150–176`, `314–364`), `wp_strong_adequacy_gen` connects an initial configuration and a step-indexed ghost-resource setup to pure meta-level facts (`φ`) after `n` steps without exposing internal ghost names or propositions (`iProp Σ`) in the conclusion. `twp_total` (`total_adequacy.v:63–72`) establishes single-thread termination (`sn erased_step`), not fair concurrent liveness. All Iris adequacy conclusions remain conditional on the step relation (`prim_step`), stuckness mode (`NotStuck` vs. `MaybeStuck`), state interpretation (`state_interp`), and ghost-allocation obligations.
2. **Core Iris mechanisms for Rust and Aeneas-targeted separation logic (`iris/iris` `8e49095`, `2026-09-27`)**: Across `iris/bi/interface.v`, `iris/algebra/{cmra.v,ofe.v}`, `iris/base_logic/lib/{own.v,invariants.v,fancy_updates.v,ghost_map.v,gen_heap.v}`, and `iris_heap_lang`, Iris separates the assertion signature (BI), composable ghost state (CMRA/OFE), step-indexed persistence/later (`□`, `▷`), mask-indexed invariant opening (`|={E1,E2}=>`), and concrete points-to/ghost-map libraries from any particular operational language. Pure functional translations such as Aeneas LLBC-to-Lean elimination remove spatial reasoning along the happy path, whereas interior mutability, raw-pointer splits, concurrent ghost protocols, or lower-level semantic bridges require explicit resource-logic layers.
3. **`iris-lean` adequacy and MiniRust formalization status (`leanprover-community/iris-lean` `81bc350bc469a4a3a7a42bc22bc88e5bf0c927d0`, `minirust` `631ef8c4da8e7ae853a6c0fb4fe4ddba5f3f725b`)**: At `81bc350`, `iris-lean` provides the BI interface (`src/Iris/BI/`), OFE/COFE (`src/Iris/Algebra/OFE.lean`), `CMRA`/`UCMRA` (`src/Iris/Algebra/CMRA.lean`), `GenHeap` (`src/Iris/Algebra/HeapView.lean`), step-indexed `UPred M` (`src/Iris/BaseLogic/UPred.lean`), and the MoSeL proof mode (`src/Iris/ProofMode/`), with zero `sorry` or custom `axiom` declarations across its 51 Lean files. It does **not** yet include `program_logic`, `WP`, `fancy_updates`, invariants, or adequacy theorems; an executable 6-case Lean 4.28.0 harness (`support/iris_notstuck_adequacy_and_ub_encoding.lean`) proves `wp_not_stuck_adequacy` and demonstrates how encoding undefined behavior as a Stuck state yields `¬ IsUB e' σ'`, whereas encoding UB as a silent/diverging step (`steps_to_self_is_not_stuck`) or using `MaybeStuck` (`wp_maybe_stuck_vacuous_on_ub`) silently accepts UB. Meanwhile, upstream `minirust` (`631ef8c`) is a prose/literate `.md` specification without `.v` or `.lean` mechanization, and its companion `mini-rust-formal` repository (`28c4565`) is an incomplete Coq snapshot containing `Admitted` lemmas.
4. **Transfinite Iris existential and liveness boundary (`iris/transfinite` `dde9f199bc09dc5242e3547be7c5049030f4c451`, LiveActris `eb12dbba4beae14da8a466468ff963c27d589ca2`, Trillium `d8bc4d31f929b9f5b9ef20a5943c9c923e8844c7`)**: Replacing `nat` step indices with ordinal-indexed `oofe`/`oupred` (`transfinite/algebra/ofe.v:25–56`, `base_logic/oupred.v:17–49`) eliminates finite-step truncation so `twp_adequacy` (`program_logic/total_adequacy.v:66–77`) proves unbounded `eventually` progress (`rtc erased_step`) when given a transfinite induction principle (`Stepidx.wf`) and an existential-Witness extraction property (`siProp_witness`). However, `siProp_witness` is neither constructive nor automatic: `base_logic/siProp.v:343–349` proves it incompatible with standard `later_exists`, and `oupred.v:875–927` derives it only by importing classical `Epsilon`/`Choice` (`ClassicalEpsilon`). LiveActris (`session.v:261–307`) layers dual send/receive obligations (`r !<<v>> { P }`) to prevent send-wait deadlocks, and Trillium (`fairness/adequacy.v:69–111`, `fairness/fair_termination.v:8–39`) relates infinite program traces to fair model traces, requiring separate trace-fairness hypotheses before yielding termination.
5. **Simuliris and Tree Borrows kernel replay (`simuliris` `e3abfcdce1aa4e26f1398e3efebad5258ddcc11c`)**: A native Rocq 9.0.0 / `coqchk` replay of Simuliris's Tree Borrows mechanized formalization (`theories/tree_borrows/`) compiled 49 target `.vo` units and verified all 9 closed contextual refinement and adequacy theorems (`target_red_adequacy` through `disabled_Write_Ref_Ctx_Refinement`) under `-R theories simuliris -no-stdlib -o -disallow-sprop`, reporting zero axioms (`support/actual-results.json`). During replay, two distinct verification hazards were diagnosed and recorded with reproducible artifacts: (a) running `coq_makefile` without `-R theories simuliris` compiles modules under top-level logical names that `coqchk` rejects when checking `simuliris.*` imports (`support/binding-failure-artifacts/`), and (b) passing physical `.vo` paths instead of logical module paths to `coqchk` silently checks 0 targets while exiting with status 0 (`support/audit-command-flags.json`).
6. **Resource algebras, lifetimes, and automation (`lambda-rust-coq` `ab0dc7a0`, RefinedRust `artifact.tar.gz`, Actris `b4ffef53`, F* `e2b5042f`, VST `3c37c2e2`)**: Comparative source inspection across `Core.v` (Iris discrete/step-indexed RA axioms), `lft_contexts.v` and `bor_lemmas.v` (RustBelt lifetime token intersection, borrow splitting, and reborrowing), RefinedRust `shim.v` (Lithium goal-directed `liRStep`/`FindDirect` automation classes), Actris `channel.v` (session-type `irec_end`/`isend_end` protocols), Steel `Steel.Memory.fsti` and Pulse `PulseCore.HeapSig.fsti` (affine `slprop`/`vprop` ghost updates without general step-indexed impredicative invariants), and VST `shares.v` (boolean-tree fractional shares) maps the exact algebraic obligations needed for borrow splitting, reborrowing, and ghost-state updates.
7. **Modular algebraic-effect semantics for state and aliasing (`Effects.lean`, POPL 2025 DOI `10.1145/3704850`)**: Replaying the 959-line Lean 4 artifact (`support/Effects.lean`, zero `sorry`, standard axioms `propext` and `Quot.sound` only) confirms that encoding global versus local state and explicit location-aliasing equivalence classes as second-order algebraic theories (`GlobalStateTheory`, `LocalStateTheory`, `EquivTheory`) enables equational program equivalences (`swap`, `drop_write_read`, `comm_write_diff`) and normal-form syntax (`StateNF`), while explicitly omitting separation-logic frame rules, concurrent interference, and raw byte/pointer arithmetic.

---

## Applicability

The findings in this report apply to the following pinned repositories, commits, and formalization boundaries:

| Subject / Component | Repository / Source | Pinned Revision / Identity | Scope & Boundary |
|---|---|---|---|
| Iris (Rocq) | `iris/iris` (`gitlab.mpi-sws.org/iris/iris`) | `8e490956795f2ca9bcd2cfbc0fc65c3dc4bdce77` (observed `2026-09-27` / `2026-10-14`) | `adequacy.v`, `total_adequacy.v`, `weakestpre.v`, `twp.v`, `ectx_lifting.v`, `cmra.v`, `ofe.v`, `own.v`, `invariants.v`, `fancy_updates.v`, `ghost_map.v`, `gen_heap.v`, `iris_heap_lang` |
| `iris-lean` | `leanprover-community/iris-lean` | `81bc350bc469a4a3a7a42bc22bc88e5bf0c927d0` (Lean `v4.28.0`) | 51 `.lean` files (`Algebra`, `BI`, `BaseLogic/UPred.lean`, `ProofMode`, `Std`, `Instances`); excludes `program_logic`, `WP`, `fancy_updates`, invariants, and adequacy |
| MiniRust specification | `minirust/minirust` | `631ef8c4da8e7ae853a6c0fb4fe4ddba5f3f725b` | Literate `.md` specification only; zero `.v` or `.lean` mechanized proof files |
| `mini-rust-formal` | `OliverBrotchie/mini-rust-formal` | `28c4565e109030f698702be76554892421265008` | External Coq 8.17 development (12 `.v` files) containing incomplete `Admitted` proofs |
| Transfinite Iris | `iris/transfinite` (`gitlab.mpi-sws.org/iris/transfinite`) | `dde9f199bc09dc5242e3547be7c5049030f4c451` | Ordinal-indexed OFE/UPred (`oofe`, `oupred.v`), `siProp_witness` classical choice requirement, `total_adequacy.v` |
| LiveActris | `iris/live_actris` (`gitlab.mpi-sws.org/iris/live_actris`) | `eb12dbba4beae14da8a466468ff963c27d589ca2` | Fair/live session-type obligations (`session.v`, `adequacy.v`) over Transfinite Iris |
| Trillium | `iris/trillium` (`gitlab.mpi-sws.org/iris/trillium`) | `d8bc4d31f929b9f5b9ef20a5943c9c923e8844c7` | Trace refinement (`program_logic/adequacy.v`) and fair-termination connection (`fairness/adequacy.v`, `fairness/fair_termination.v`) |
| Simuliris / Tree Borrows | `simuliris` (`support/inputs/simuliris.tar.gz`) | `e3abfcdce1aa4e26f1398e3efebad5258ddcc11c` (`sha256: bff93f5f81d18fd1ee376c637ba642b52072ce47f781da77ba89aa6d1d05025b`) | Checked under Rocq 9.0.0 (`coq-iris 4.3.0`, `coq-stdpp 1.11.0`); covers 9 selected Tree Borrows contextual refinement and adequacy theorems |
| LambdaRust / RustBelt | `iris/lambda-rust` (`gitlab.mpi-sws.org/iris/lambda-rust`) | `ab0dc7a087efdec7f64da1ef1ca5b32333915a78` | Lifetime intersections, borrow splitting, and reborrowing in `theories/lifetime/{lft_contexts.v,model/bor_lemmas.v}` |
| RefinedRust 2026 artifact | `zenodo.org/records/21636474` (`artifact.tar.gz`) | `sha256: 34573bac60de68c3597c23136cd5221a7129f89a24b69340f8e361750f331d53` | Lithium goal-directed automation classes (`lithium/theories/base/shim.v`) |
| Actris | `iris/actris` (`gitlab.mpi-sws.org/iris/actris`) | `b4ffef53dc00072a60e2a898119fc7a7c6670080` | Dependent separation-logic session channels (`theories/channel/channel.v`) |
| F* Steel & PulseCore | `FStarLang/FStar` | `e2b5042ffd8272ad6287e4ad8748d8e52dadd93d` | `Steel.Memory.fsti` and `pulse/lib/core/PulseCore.HeapSig.fsti` |
| Princeton VST | `PrincetonUniversity/VST` | `3c37c2e2b574e23aee8fdd1684aa0ffed227491e` | Fractional tree-share model (`veric/shares.v`) |
| Modular State-Alias Effects | `Effects.lean` (`zenodo.org/records/13919529`, POPL 2025 DOI `10.1145/3704850`) | `Effects.lean` (`sha256: b0daecbd4023ab10134f92be267c1edddfb37b7938c7e9045a28c7d416a9f08f`) | Replayed under Lean 4.34.1 (`leanprover/lean4:v4.34.1`); single-file second-order algebraic theory formalization |

---

## Findings

### 1. Step-Indexed Iris Adequacy, Total WP, and Resource Interfaces (`iris/iris` `8e49095`)

**Basis: source (`iris/program_logic/adequacy.v`, `total_adequacy.v`, `weakestpre.v`, `twp.v`, `ectx_lifting.v`, `iris_heap_lang/adequacy.v`).**

#### 1.1 Partial-Correctness and Strong Adequacy (`adequacy.v`)
In `iris/program_logic/adequacy.v:150–176`, `wp_strong_adequacy_gen` establishes that for a step-index bound `n`, an initial thread pool `es`, and initial physical state `σ1`, if a proof allocates ghost state and provides:
- the initial state interpretation `state_interp σ1 nt`,
- weakest preconditions `([∗ list] e;Φ ∈ es;Φs, WP e @ s; ⊤ {{ Φ }})`, and
- a closing view shift from the post-state resources after `n` steps to a pure meta-level proposition `⌜ φ ⌝` under the empty mask `∅`,

then `φ` holds in the ambient meta-logic (Rocq `Prop`) for any execution trace of length `n` reaching `es'` and `σ2`. All internal ghost names, camera elements, invariants, and `iProp Σ` assertions are eliminated at this boundary.

Specifically:
- `adequate` (`adequacy.v:25–29`) bundles two conclusions for all reachable configurations `(t2, σ2)` from `([e1], σ1)`:
  1. if the main thread reaches a value `of_val v2`, then `φ v2 σ2` holds; and
  2. if stuckness `s = NotStuck`, every thread `e2 ∈ t2` is either a value (`is_Some (to_val e2)`) or reducible (`reducible e2 σ2`).
- `wp_adequacy` (`adequacy.v:314–327`) and `wp_invariance` (`adequacy.v:343–356`) specialize `wp_strong_adequacy_gen` to single-postcondition value safety and step-indexed state invariants, respectively.
- `heap_adequacy` (`iris_heap_lang/adequacy.v:14–31`) instantiates `wp_adequacy` for HeapLang by initializing `gen_heap_init σ` and `proph_map_init κs σ.(used_proph_id)`.

#### 1.2 Total Weakest Preconditions (`twp.v`, `total_adequacy.v`)
In `iris/program_logic/twp.v:56–77`, `twp_pre` defines the inductive (non-later-guarded) total weakest precondition fixpoint: a non-value step takes an unguarded mask-preserving update `|={E}=>` across all successor configurations rather than guarding the continuation behind `▷`. Consequently:
- `twp_wp_step` (`twp.v:194–201`) embeds `TWP` into step-indexed `WP`.
- `twp_total` (`total_adequacy.v:63–72`) proves `sn erased_step ([e], σ)`, i.e., strong normalization of single-thread execution where the operational semantics does not spawn concurrent threads (`efs = []`). It does not establish fair concurrent liveness across interleaved threads.

#### 1.3 Operational Lifting Obligations (`ectx_lifting.v`)
In `iris/program_logic/ectx_lifting.v:23–41`, lifting a head step (`head_step`) to a WP proof obligation requires two distinct conditions when `s = NotStuck`:
1. `head_reducible e1 σ1` (progress from the current physical state), and
2. universal quantification over all possible `head_step e1 σ1 κ e2 σ2 efs` transitions, updating `state_interp` and proving `WP` for `e2` and all forked threads `efs`.

If an operational semantics omits an undefined behavior case from `head_step` without marking it as a value, `head_reducible` fails unless the proof discharges that the UB side condition cannot occur.

---

### 2. Core Iris Mechanisms for Rust and Aeneas Separation Logic (`iris/iris` `8e49095`)

**Basis: source (`iris/bi/`, `iris/algebra/`, `iris/base_logic/lib/`, `iris_heap_lang/`) and comparative synthesis (`support/iris-concepts-for-rust-aeneas-separation-logic/concept-map.json`, `support/iris-concepts-for-rust-aeneas-separation-logic/source-map.json`).**

| Iris Layer & Primary Source | Core Mathematical Mechanism | Role in Rust / Low-Level Verification | When Needed Beyond Pure Functional (Aeneas LLBC) Translation |
|---|---|---|---|
| **BI (`iris/bi/interface.v`, `derived_connectives.v`, `big_op.v`)** | Bunched Implications (`∗`, `-∗`, `<pers>`, `▷`, `<absorb>`) and iterated separating conjunctions (`[∗ list]`, `[∗ map]`, `[∗ set]`) | Modular framing over disjoint heap locations, slices, and ghost permissions | Safe Rust value-level borrowing is handled purely by Aeneas backward functions; BI framing is needed when reasoning directly over raw pointers, aliased heap fragments, or concurrentghost resources |
| **OFE / CMRA (`iris/algebra/ofe.v`, `cmra.v`, `auth.v`, `excl.v`, `frac.v`, `agree.v`, `gmap.v`, `csum.v`, `sts.v`)** | Step-indexed metric spaces (`equivI`, `dist`), cameras with step-indexed validity (`✓{n}`), cores (`pcore`), and frame-preserving updates (`x ~~>: P`) | Encoding exclusive ownership (`exclR`), fractional shares (`fracR`), authoritative state vs. local fragments (`authR`), and state-transition systems | Needed whenever ghost protocol state or shared interior-mutable permissions cannot be represented as a single functional state value |
| **Base Logic (`iris/base_logic/lib/own.v`, `fancy_updates.v`, `invariants.v`, `later_credits.v`)** | Ghost ownership `own γ a`, mask-changing updates `\|={E1,E2}=>`, impredicative invariants `inv N P` (`inv_acc`), and later-credit elimination (`£ n` / `lc_fupd_elim_later`) | Sharing state across unknown aliases or threads under a protocol invariant `N` while preventing re-entrancy double-opening via mask `E` | Essential for `UnsafeCell`, atomics, lock-free structures, and re-entrant callback protocols |
| **State Libraries (`iris/base_logic/lib/ghost_map.v`, `gen_heap.v`, `proph_map.v`, `na_invariants.v`)** | Authoritative map `ghost_map_auth γ q m` + points-to `k ↪[γ]{dq} v` (`DfracOwn`, `DfracDiscarded`, `DfracBoth`); prophecy resolution (`proph_map`); thread-local non-atomic invariants (`na_inv`) | Points-to ownership with discardable read-only sharing (`DfracDiscarded`), single-thread `Cell`/`RefCell` non-atomic invariants, and future-dependent mutable-borrow resolution (`proph`) | Needed when modeling raw memory heaps, persistent read-only sharing without lifetime bounds, or prophecy-based borrow resolution |

---

### 3. `iris-lean` (`81bc350`) Adequacy Gap and MiniRust Mechanization Survey

**Basis: source and executable Lean 4 replay (`support/iris_notstuck_adequacy_and_ub_encoding.lean`, `support/iris_notstuck_adequacy_and_ub_encoding.eval.json`, `support/authenticated-selected-identities.json`, `support/independent-import-graph.json`).**

#### 3.1 `iris-lean` Inventory at `81bc350bc469a4a3a7a42bc22bc88e5bf0c927d0`
Direct inspection of all 51 `.lean` files in `leanprover-community/iris-lean` (`81bc350`, targeting `leanprover/lean4:v4.28.0`) confirms:
- **Implemented modules**:
  - `src/Iris/BI/` (`Interface.lean`, `DerivedLaws.lean`, `Extensions.lean`, `BigOp.lean`, `Instances.lean`): full BI typeclass hierarchy (`BIBase`, `BI`, `BIAffine`, `BIPersistentlyImpl`, `BILaterContractive`).
  - `src/Iris/Algebra/` (`OFE.lean`, `CMRA.lean`, `Updates.lean`, `LocalUpdates.lean`, `Auth.lean`, `Excl.lean`, `Frac.lean`, `Agree.lean`, `DFrac.lean`, `GMap.lean`, `GenMap.lean`, `Heap.lean`, `HeapView.lean`, `LeibnizSet.lean`, `View.lean`): OFE/COFE, CMRA/UCMRA, authoritative cameras, fractional/discardable fractions, and generic heap views (`HeapView`).
  - `src/Iris/BaseLogic/UPred.lean`: uniform step-indexed predicates `UPred M` with `ownM`, `bupd` (`|==> P`), `later`, and `persistently`.
  - `src/Iris/ProofMode/`: MoSeL tactical proof mode (`istart`, `iintro`, `isplitL`/`isplitR`, `iexact`, `ihave`, `icases`, `iapply`).
- **Soundness hygiene**: Zero occurrences of `sorry`, `axiom`, `unsafe`, or `implemented_by` in `src/` (`support/independent-import-graph.json`).
- **Absent at `81bc350`**: `iris-lean` does **not** yet contain `fupd` (`fancy_updates`), impredicative invariants (`inv`), global ghost-name allocation (`gMap` functor / `iProp Σ`), weakest preconditions (`WP`/`TWP`), or any adequacy theorem.

#### 3.2 Executable Lean 4 Adequacy and UB-Encoding Harness (`support/iris_notstuck_adequacy_and_ub_encoding.lean`)
To evaluate how `NotStuck` adequacy interacts with operational encodings of undefined behavior in Lean 4 on top of `iris-lean`, `support/iris_notstuck_adequacy_and_ub_encoding.lean` mechanizes a step-indexed operational semantics (`Language`), stuckness flag (`Stuckness.NotStuck` vs. `MaybeStuck`), step-indexed WP over `UPred M`, and six machine-checked theorems (`support/iris_notstuck_adequacy_and_ub_encoding.eval.json`, exit code `0`, zero `sorry`, standard axioms `[propext, Classical.choice, Quot.sound]`):

| Theorem in `support/iris_notstuck_adequacy_and_ub_encoding.lean` | Statement & Verified Finding |
|---|---|
| `wp_step_adequacy` | Single-step preservation of `NotStuck` WP under valid ghost resource `✓{n} r` and state interpretation |
| `wp_not_stuck_adequacy` | Multi-step (`Steps n e σ e' σ'`) adequacy: if `WP NotStuck e Φ` holds at step index `n` with initial valid resource `✓{n} r`, then `(e', σ')` is `NotStuckState` (either `toVal e' ≠ none` or `Reduces e' σ'`) |
| `not_stuck_excludes_ub_when_ub_is_stuck` | When the operational semantics models every UB state (`IsUB e' σ'`) as having `toVal e' = none` and `¬ Reduces e' σ'`, `wp_not_stuck_adequacy` implies `¬ IsUB e' σ'` for all `n`-step reachable states |
| `steps_to_self_is_not_stuck` | **Hazard 1 (Silent/looping UB)**: If an operational semantics models UB via a stuttering self-loop (`Step e_ub σ e_ub σ`), then `Reduces e_ub σ` is trivially true and `NotStuckState` fails to exclude UB |
| `wp_maybe_stuck_vacuous_on_ub` | **Hazard 2 (`MaybeStuck` mode)**: Under `Stuckness.MaybeStuck`, a stuck non-value UB configuration `(e_ub, σ)` with zero outgoing steps vacuously satisfies `WP MaybeStuck e_ub Φ` |
| `ub_exclusion_iff_stuck_encoding` | Exact equivalence characterization: `NotStuck` adequacy excludes `IsUB` across all reachable states if and only if every reachable `IsUB` configuration is neither a value nor reducible |

#### 3.3 MiniRust Formalization Status (`minirust` `631ef8c`, `mini-rust-formal` `28c4565`)
- **Upstream `minirust/minirust` (`631ef8c4da8e7ae853a6c0fb4fe4ddba5f3f725b`)**: Contains 48 Markdown files specifying MiniRust syntax, places, values, memory interface, Tree Borrows/Stacked Borrows interface, and well-formedness in pseudocode/Rust-like spec notation (`spec/`). It contains **zero** `.v` (Rocq) or `.lean` (Lean) files.
- **External `OliverBrotchie/mini-rust-formal` (`28c4565e109030f698702be76554892421265008`)**: An independent 2023 Coq 8.17 prototype (`src/`, 12 `.v` files) translating a fragment of early MiniRust; it contains explicit `Admitted` proofs (e.g., in `src/ty.v` and `src/well_formed.v`) and does not connect to Iris or `iris-lean`.

---

### 4. Transfinite Iris, Existential Witness Extraction, and Fair Liveness (`iris/transfinite` `dde9f19`, LiveActris `eb12dbb`, Trillium `d8bc4d3`)

**Basis: source (`support/transfinite-iris-existential-and-liveness-boundary-dde9f19/source-identities.json`, `support/transfinite-iris-existential-and-liveness-boundary-dde9f19/coverage.json`).**

#### 4.1 Ordinal-Indexed Step Indexing (`oofe`, `oupred.v`)
Standard Iris indexes propositions over `nat`, which suffices for safety (`∀ n, ...` after `n` steps) and single-thread deterministic/finite-branching `TWP`, but cannot express unbounded liveness under finitely branching nondeterminism or fair scheduling where lookahead exceeds any fixed finite `n`.
In `iris/transfinite` (`dde9f199bc09dc5242e3547be7c5049030f4c451`):
- `theories/algebra/ofe.v:25–56` generalizes step indices from `nat` to an arbitrary transfinite step-index type `SI : stepidx` equipped with a well-founded strict ordering (`Stepidx.lt`, `Stepidx.wf`).
- `theories/base_logic/oupred.v:17–49` defines ordinal-indexed uniform predicates `ouPred (SI : stepidx) (M : uora SI)` with downward closure along `Stepidx.le`.

#### 4.2 The Existential Witness Extraction Boundary (`siProp_witness` and Classical Choice)
To extract a concrete operational step or witness from a step-indexed existential `∃ x, P x` during transfinite adequacy induction, Transfinite Iris requires the witness property `siProp_witness` (`theories/base_logic/siProp.v:324–335`):
$$\left(\forall \alpha,\ (\exists x,\ P(x))(\alpha)\right) \implies \exists x,\ \forall \alpha,\ P(x)(\alpha)$$
Inspection of `siProp.v` and `oupred.v` establishes two critical boundaries:
1. **Incompatibility with `later_exists` (`siProp.v:343–349`)**: `siProp_witness_later_exists_false` proves that if `siProp_witness` holds and the step-index type `SI` is limit-closed, then the standard Iris law `▷ (∃ x, P x) ⊢ ◇ ∃ x, ▷ P x` (`later_exists`) is **refutable** for infinite types.
2. **Reliance on Classical Choice (`oupred.v:875–927`)**: `oupred.v` imports `Coq.Logic.ClassicalEpsilon` (`line 2`) and proves `ouPred_witness` (`lines 891–927`) using Hilbert's epsilon operator (`constructive_indefinite_description` / `excluded_middle_informative`) and transfinite cardinality bounds (`stepidx_Next`). Thus, transfinite total adequacy in `theories/program_logic/total_adequacy.v:66–77` (`twp_adequacy` proving `eventually (λ '(t2, σ2), ∃ v2, t2 = of_val v2 :: _ ∧ φ v2)`) depends on classical axioms beyond constructive Rocq/Lean kernels.

#### 4.3 LiveActris and Trillium Fair-Termination Boundaries
- **LiveActris (`iris/live_actris` `eb12dbba4beae14da8a466468ff963c27d589ca2`)**: Built on Transfinite Iris (`opam:14–18`), `theories/channel/session.v:261–307` defines live session types where send (`r !<< x .. y >> v { P }`) is a **dual obligation** (`iProto_DualObligation`) rather than a mere permission, preventing cyclic send-wait deadlocks. `theories/channel/adequacy.v:15–56` proves `twp_adequacy` (`eventually ...`) for closed HeapLang session programs, inheriting Transfinite Iris's classical `oupred` witness assumptions.
- **Trillium (`iris/trillium` `d8bc4d31f929b9f5b9ef20a5943c9c923e8844c7`)**:
  - `theories/program_logic/adequacy.v:159–215` proves trace-refinement adequacy (`wp_strong_adequacy`) relating finite execution prefixes `trace_steps` to model traces `mtrace` via `continued_simulation`.
  - `theories/fairness/adequacy.v:69–111` lifts finite simulations to infinite executions (`simulation_inf_exec`), and `theories/fairness/fair_termination.v:8–39` (`fair_termination`) proves that if the model relation is well-founded under fair steps and the execution trace satisfies `fair_ex`, then the program trace cannot diverge (`terminating_trace`). Fairness of the scheduler (`fair_ex`) is an **external hypothesis** on the execution trace, not discharged by the program logic itself.

---

### 5. Simuliris and Tree Borrows Kernel Replay (`simuliris` `e3abfcdc`)

**Basis: native Rocq 9.0.0 build and `coqchk` replay (`support/actual-results.json`, `support/REPLAY.md`, `support/independent-review.md`, `support/audit-checker-driver-status.json`, `support/audit-command-flags.json`, `support/corrected-mapping-regression.json`, `support/namespace-rebuild-bindings.json`).**

#### 5.1 Verified Tree Borrows Contextual Refinement and Adequacy Theorems
Using pinned upstream archives (`support/inputs/simuliris.tar.gz` at `e3abfcdce1aa4e26f1398e3efebad5258ddcc11c`, `coq-iris 4.3.0`, `coq-stdpp 1.11.0`, Rocq `9.0.0`, OCaml `4.14.2`), all 49 `.vo` compilation units in the dependency closure of `theories/tree_borrows/examples/protected/mixed_protected_unprotected.v` were compiled (`support/logs/generic-corrected.stdout`, `support/logs/tree-borrows-core.stdout`, `support/logs/sequential-read-reordering.stdout`, `support/logs/protected-and-unprotected-examples.stdout`) and kernel-audited with `coqchk -R theories simuliris -no-stdlib -o -disallow-sprop` (`support/logs/recursive-native-checker.stdout`, exit `0`, 132 total modules checked in closure, `Axioms: <none>`):

| # | Selected Theorem | Source File & Line (`simuliris` `e3abfcdc`) | Verified Statement / Role |
|---|---|---|---|
| 1 | `target_red_adequacy` | `theories/simulation/sls.v:113` | Adequacy of the Simuliris simulation logic for target reductions (`target_red`) |
| 2 | `sim_expr_adequacy` | `theories/simulation/simulation.v:306` | Expression-level simulation adequacy connecting `sim_expr` to closed behavioral refinement |
| 3 | `prog_rel_adequacy` | `theories/simulation/behavior.v:383` | Whole-program relational adequacy (`prog_rel` implies `ctx_refines` under closed contexts) |
| 4 | `open_prog_rel_adequacy` | `theories/simulation/behavior.v:418` | Open-program relational adequacy under arbitrary well-typed linking contexts |
| 5 | `typed_progs_are_related` | `theories/tree_borrows/logical_state.v:1239` | Fundamental theorem of the Tree Borrows logical relation: syntactically well-typed expressions refine themselves (`log_rel`) |
| 6 | `Frozen_Read_Ref_Ctx_Refinement` | `theories/tree_borrows/examples/no_protector/frozen_read_ref.v:53` | Contextual refinement moving a read across an unknown call for a `Frozen` reference without protector |
| 7 | `Reserved_Reorder_Read_Write_Activated_Ref_Ctx_Refinement` | `theories/tree_borrows/examples/no_protector/reserved_reorder_read_write_activated_ref.v:107` | Contextual refinement reordering a read and write on an activated `Reserved` reference |
| 8 | `Active_Write_Overwrite_Protected_Ref_Ctx_Refinement` | `theories/tree_borrows/examples/protected/active_write_overwrite_protected_ref.v:106` | Contextual refinement eliminating an overwritten write on a function-entry `Protected` `Active` reference |
| 9 | `disabled_Write_Ref_Ctx_Refinement` | `theories/tree_borrows/examples/protected/mixed_protected_unprotected.v:185` | Contextual refinement for mixed protected and unprotected references when an unprotected alias becomes `Disabled` |

Additionally, three audit harness modules (`PlannedAuditFramework.v`, `PlannedAuditResources.v`, `PlannedAuditExamples.v` in `support/checked-project/`) that explicitly `@Check` and reference these theorems were compiled and verified by `coqchk` (`support/logs/audit-PlannedAuditFramework.stdout`, `support/logs/audit-PlannedAuditResources.stdout`, `support/logs/audit-PlannedAuditExamples.stdout`), confirming zero axioms across all 9 theorems (`support/actual-results.json`).

#### 5.2 Diagnosed Rocq Build-Flag and `coqchk` Silent-Skip Hazards
The replay isolated two subtle verification pitfalls documented in `support/audit-command-flags.json`, `support/audit-checker-driver-status.json`, and `support/corrected-mapping-regression.json`:
1. **Missing `-R theories simuliris` in `coq_makefile` (`support/binding-failure-artifacts/`, `support/logs/binding-failure-diagnosis.stderr`)**: When `coq_makefile` is invoked without `-R theories simuliris` (as in the initial command template in `support/historical-plan/BUILD-AND-AUDIT-COMMANDS.md`), Rocq compiles individual files using flat top-level logical module names (`values`, `language`, `satisfiable`) while internal `From simuliris Require Import ...` directives resolve against the pre-installed opam package or fail at `coqchk` time with:
   `File "theories_logic_satisfiable.vo" has been bound to qualify "theories_logic_satisfiable" instead of "simuliris.logic.satisfiable"`.
   Passing `-R theories simuliris` to `coq_makefile` (`support/logs/corrected-makefile-generation.stdout`) binds every `.vo` to its canonical `simuliris.*` logical path (`support/namespace-rebuild-bindings.json`).
2. **Silent zero-module check when passing `.vo` file paths to `coqchk` (`support/audit-command-flags.json`)**: In Rocq 9.0.0, passing physical paths such as `theories/simulation/sls.vo` to `coqchk -R theories simuliris` causes `coqchk` to treat arguments with `.vo` extensions or `/` separators as load-path additions rather than target modules to verify—printing an empty module summary (`Modules were successfully checked` with 0 modules) and exiting `0`! `coqchk` must be invoked with logical module names (`simuliris.simulation.sls`, `simuliris.tree_borrows.logical_state`, etc.), which checks all 132 transitive modules (`support/checker-loaded-paths.json`).

---

### 6. Comparative Resource Algebras, Lifetime Logics, and Automation Interfaces (`2026`)

**Basis: source (`support/resource-algebra-lifetime-and-automation-2026/source-evidence.json`, `support/resource-algebra-lifetime-and-automation-2026/coverage.json`).**

| System & Inspected File | Algebraic / Logical Primitive | Key Operations & Invariants | Architectural Trade-off for Rust / Low-Level Verification |
|---|---|---|---|
| **Iris CMRA (`iris/algebra/cmra.v` / `Core.v` in `ab0dc7a0`)** | Step-indexed camera `(A, equiv, dist, pcore, op, validN)` | Associativity, commutativity, `cmra_pcore_l`, `cmra_extend` (step-indexed decomposition), frame-preserving updates `x ~~>: P` | Full generality for higher-order ghost state and step-indexed invariants; requires OFE metric bookkeeping when step-indexing is nontrivial |
| **LambdaRust Lifetimes (`theories/lifetime/lft_contexts.v`, `model/bor_lemmas.v` at `ab0dc7a0`)** | Lifetime tokens `[κ]q`, lifetime inclusion `κ ⊑ κ'`, full borrow `&{κ} P`, fractured borrow `&{κ,q} α` | `lft_intersect_acc` combines `[κ1]q1` and `[κ2]q2` into `[κ1 ⊓ κ2]q` plus a restoration wand; `bor_sep` splits `&{κ}(P ∗ Q) ⊣⊢ &{κ}P ∗ &{κ}Q`; `bor_shorten` and `rebor` handle subtyping and nested reborrows | Decouples borrow lifetimes from syntactic lexical scopes via fractional lifetime tokens; `bor_sep` requires non-atomic borrow invariants and later credits / step-indexing |
| **RefinedRust / Lithium (`lithium/theories/base/shim.v` in `artifact.tar.gz`)** | Goal-directed separation-logic interpreter (`liRStep`, `liToSyntax`, `FindDirect`, `Subsume`) | Deterministic syntax-directed proof search driven by typeclass instances (`MustHave`, `FindDirect`) rather than backtracking `iAssumption` | Predictable, fast VC discharge for ownership types; requires explicit typeclass rules for every new resource predicate and coercion |
| **Actris (`theories/channel/channel.v` at `b4ffef53`)** | Dependent session protocol `iProto Σ` (`<! x .. y > MSG v {{ P }}; prot`, `<? x .. y > MSG v {{ Q }}; prot`) | `isend_end` / `irec_end` transfer ownership of spatial resources `P` across message passing using dual ghost-channel endpoints | Demonstrates how Iris ghost state encodes bidirectional protocol state machines; partial-correctness Actris does not prevent deadlock without LiveActris obligations |
| **F* Steel & PulseCore (`Steel.Memory.fsti`, `PulseCore.HeapSig.fsti` at `e2b5042f`)** | Affine separation-logic propositions (`slprop` / `vprop`) with PCM-backed ghost references | `interp : slprop -> mem -> prop`, `equiv`, `star`, `emp`, frame-preserving PCM updates, and stratified invariant signatures (`box`/`iref`) | Directly embedded in dependent type theory with SMT discharge of pure side conditions; avoids general step-indexed impredicative invariants via universe/level stratification |
| **Princeton VST (`veric/shares.v` at `3c37c2e2`)** | Canonical boolean binary trees (`Share.t`) with `glb`, `lub`, `comp`, and ` readable_share` / `writable_share` | Disjoint join `sepalg.join a b c` (`a ⊓ b = bot`, `a ⊔ b = c`), infinite splittability (`split`), and decidable equality | Clean, step-index-free fractional ownership for C memory permissions; lacks built-in temporal lifetime tokens without an external lifetime algebra |

---

### 7. Modular Algebraic-Effect Semantics for State and Aliasing (`Effects.lean`, POPL 2025)

**Basis: source and Lean 4.34.1 replay (`support/Effects.lean`, `support/lean.log`, `support/theorem-excerpts.txt`, `support/modular-semantics-state-alias-effects-popl2025/source-evidence.json`, DOI `10.1145/3704850`).**

#### 7.1 Second-Order Algebraic Theories of State and Aliasing
The POPL 2025 artifact (`support/Effects.lean`, 959 lines, replayed under Lean `4.34.1` with zero `sorry` and only `propext` and `Quot.sound` in `#print axioms`) formalizes imperative state and dynamic allocation via second-order algebraic theories (`SOTheory`):
1. **`GlobalStateTheory` (`Effects.lean:382–436`)**: Parameterized by a fixed finite register/location type `Loc` and value type `Val`, with operations `get(l)` and `put(l, v)` and the three Plotkin–Power state equations (`get_get`, `put_get`, `put_put`, `put_put_diff`).
2. **`LocalStateTheory` (`Effects.lean:458–534`)**: Adds dynamic allocation `new(v; x. t[x])` as a variable-binding (second-order) operation alongside `get` and `put`, governed by commutation and fresh-location equations (`new_get`, `new_put`, `new_new_comm`, `new_dead`).
3. **`EquivTheory` and Aliased State (`Effects.lean:536–712`)**: Rather than assuming syntactic variable distinctness implies non-aliasing (`x ≠ y ⟹ l_x ≠ l_y`), `EquivTheory` explicitly tracks an equivalence relation (`eqv` / `neqv`) over location variables in the algebraic theory. Read-over-write commutation (`put(x, v); get(y) = get(y); put(x, v)`) is guarded by an explicit `neqv(x, y)` premise (`Effects.lean:648–685`).

#### 7.2 Normal Forms and Verified Program Equivalences
- **Normal-form syntax (`StateNF`, `Effects.lean:740–835`)**: `Effects.lean` defines a canonical normal form for state computations (reading all locations, branching on values, and writing final values) and proves completeness of normalization (`nf_sound`, `nf_complete`).
- **Concrete program equivalences (`Effects.lean:870–959`, `support/theorem-excerpts.txt`)**:
  - `swap`: swapping two locations via a temporary or overwrite sequence reduces to identical normal forms under distinctness (`neqv`).
  - `drop_write_read`: dead writes overwritten before observation are equationally eliminated.
  - `comm_write_diff`: writes to provably non-aliased locations commute.
- **Architectural boundary relative to separation logic**: The algebraic-effect approach treats aliasing via explicit case-splitting (`eqv` vs. `neqv`) over a finite set of in-scope location variables and proves two computations observationally equivalent (`≃`), whereas separation logic (`∗`) bakes disjointness into spatial conjunction to avoid $O(2^k)$ alias case-splits across large frames. Consequently, `Effects.lean` is well-suited for local compiler peephole/register-promotion equivalences on small variable sets, not for framing over unbounded heap structures or concurrent shared memory.

---

## Boundaries

1. **`iris-lean` (`81bc350`) vs. Rocq Iris (`8e49095`)**: `iris-lean` at `81bc350` mechanizes the BI interface, OFE/CMRA algebras (`Auth`, `Excl`, `Frac`, `DFrac`, `GMap`, `HeapView`), `UPred`, and the MoSeL proof mode in Lean 4, but does not include `fupd`, invariants, `WP`/`TWP`, or adequacy. The Lean 4 adequacy proofs in `support/iris_notstuck_adequacy_and_ub_encoding.lean` are standalone mechanized theorems developed for this investigation rather than upstream `iris-lean` modules.
2. **Transfinite Iris Classicality**: `twp_adequacy` in `iris/transfinite` (`dde9f19`) and `iris/live_actris` (`eb12dbb`) relies on `ouPred_witness`, which uses classical indefinite description (`ClassicalEpsilon`) and is provably incompatible with `later_exists` on infinite types (`siProp_witness_later_exists_false`). It cannot be imported into a purely constructive kernel without classical choice axioms.
3. **Trillium Fairness Premise**: Trillium's `fair_termination` (`d8bc4d3`) proves termination only for execution traces that satisfy the external `fair_ex` predicate; it does not prove that an OS or language runtime implements a fair scheduler.
4. **Simuliris Tree Borrows Scope**: The 9 kernel-replayed theorems in `simuliris` (`e3abfcdc`) verify contextual refinements and logical-relation adequacy for Simuliris's idealized λ-calculus model with Tree Borrows tags and protectors (`theories/tree_borrows/`). They do not mechanize full production `rustc` MIR or LLVM IR lowering.
5. **MiniRust Status**: Upstream `minirust` (`631ef8c`) contains only Markdown specification files; `OliverBrotchie/mini-rust-formal` (`28c4565`) is an incomplete external Coq 8.17 prototype with `Admitted` lemmas.
6. **Algebraic State-Alias Effects (`Effects.lean`)**: Formalizes terminating first-order/local-allocation state equations without general recursion, concurrency, pointer arithmetic, or separation-logic framing.

---

## Evidence

All primary-source extracts, build logs, kernel-checker outputs, and Lean/Rocq artifacts are preserved in `support/`:

- **Iris Adequacy & Concepts (`iris/iris` `8e49095`)**:
  - `support/iris-adequacy-resource-interface-8e49095/source-evidence.json`, `support/iris-adequacy-resource-interface-8e49095/coverage.json`, `support/iris-adequacy-resource-interface-8e49095/lean-iris-source-lead.md`
  - `support/iris-concepts-for-rust-aeneas-separation-logic/concept-map.json`, `support/iris-concepts-for-rust-aeneas-separation-logic/source-map.json`
- **`iris-lean` (`81bc350`) & MiniRust Survey**:
  - `support/iris_notstuck_adequacy_and_ub_encoding.lean` and `support/iris_notstuck_adequacy_and_ub_encoding.eval.json` (also in `support/iris-lean-81bc350-notstuck-adequacy-and-minirust-formalization-survey/`)
  - `support/authenticated-selected-identities.json` and `support/independent-import-graph.json`
- **Transfinite Iris, LiveActris, and Trillium**:
  - `support/transfinite-iris-existential-and-liveness-boundary-dde9f19/source-identities.json` and `support/transfinite-iris-existential-and-liveness-boundary-dde9f19/coverage.json`
- **Simuliris Tree Borrows Kernel Replay (`e3abfcdc`)**:
  - `support/actual-results.json`, `support/REPLAY.md`, `support/independent-review.md`, `support/independent-review.json`, `support/verify_package.py`
  - Diagnostic receipts: `support/audit-checker-driver-status.json`, `support/audit-command-flags.json`, `support/checker-loaded-paths.json`, `support/controller-import-diagnostic.json`, `support/copied-project-file-manifest.json`, `support/corrected-mapping-regression.json`, `support/loaded-object-stability.json`, `support/namespace-rebuild-bindings.json`, `support/public-path-projection.json`, `support/source-check-input.sha256`, `support/verifier-schema-diagnosis.json`
  - Build/check logs and checked project: `support/logs/`, `support/checked-project/`, `support/binding-failure-artifacts/`, `support/inputs/`, `support/parent-runtime-receipts/`, `support/observed-controllers/`, `support/historical-plan/`
- **Resource Algebras, Lifetimes, and Automation (`2026`)**:
  - `support/resource-algebra-lifetime-and-automation-2026/source-evidence.json` and `support/resource-algebra-lifetime-and-automation-2026/coverage.json`
- **Modular Semantics of State & Aliasing (`POPL 2025`)**:
  - `support/Effects.lean`, `support/lean.log`, `support/theorem-excerpts.txt`, `support/UPSTREAM-LICENSE` (also in `support/modular-semantics-state-alias-effects-popl2025/source-evidence.json`, `support/modular-semantics-state-alias-effects-popl2025/package-manifest.json`, `support/modular-semantics-state-alias-effects-popl2025/coverage.json`)

---

## Revalidation

1. **Lean 4 `NotStuck` Adequacy & UB-Encoding Harness (`iris-lean` `81bc350`)**:
   - Run `lean support/iris_notstuck_adequacy_and_ub_encoding.lean` inside a Lean `v4.28.0` environment with `iris-lean` `81bc350bc469a4a3a7a42bc22bc88e5bf0c927d0` on `LEAN_PATH`, and verify exit code `0` and `#print axioms` matching `support/iris_notstuck_adequacy_and_ub_encoding.eval.json`.
2. **Simuliris Tree Borrows Kernel Replay (`simuliris` `e3abfcdc`)**:
   - Follow `support/REPLAY.md` or run `python3 support/verify_package.py`:
     - Generate `Makefile.rocq` with `coq_makefile -f _CoqProject -R theories simuliris -o Makefile.rocq`.
     - Build the selected targets and `PlannedAudit*.v` harnesses under Rocq `9.0.0` (`coq-iris 4.3.0`, `coq-stdpp 1.11.0`).
     - Run `coqchk -R theories simuliris -no-stdlib -o -disallow-sprop simuliris.simulation.sls simuliris.simulation.simulation simuliris.simulation.behavior simuliris.tree_borrows.logical_state simuliris.tree_borrows.examples.no_protector.frozen_read_ref simuliris.tree_borrows.examples.no_protector.reserved_reorder_read_write_activated_ref simuliris.tree_borrows.examples.protected.active_write_overwrite_protected_ref simuliris.tree_borrows.examples.protected.mixed_protected_unprotected PlannedAuditFramework PlannedAuditResources PlannedAuditExamples` and confirm 132+ modules checked with `Axioms: <none>`.
3. **Modular State-Alias Effects (`Effects.lean`)**:
   - Verify `sha256sum support/Effects.lean` equals `b0daecbd4023ab10134f92be267c1edddfb37b7938c7e9045a28c7d416a9f08f`, then run `lean support/Effects.lean` (Lean `v4.34.1`) and confirm exit code `0` with only `propext` and `Quot.sound` in `#print axioms` (`support/lean.log`).
4. **Upstream Source & Pin Verification**:
   - Re-verify the Git commit and blob hashes recorded in `support/iris-adequacy-resource-interface-8e49095/source-evidence.json`, `support/transfinite-iris-existential-and-liveness-boundary-dde9f19/source-identities.json`, and `support/resource-algebra-lifetime-and-automation-2026/source-evidence.json`.
