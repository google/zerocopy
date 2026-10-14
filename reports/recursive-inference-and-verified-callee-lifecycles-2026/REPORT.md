# Recursive inference and verified-callee lifecycles: RustHorn, Stainless and SAW

## Summary

These systems automate different interfaces. RustHorn reduces a safe ownership discipline to recursive constrained Horn clauses; Stainless generates refinement and termination conditions for a Scala subset; SAW symbolically executes selected MIR functions against specifications and can reuse their verified contracts as overrides. A solver result, an inferred model, a proved semantic rule and a reusable callee contract have different trust and coverage obligations.

The inspected implementations make those distinctions concrete. RustHorn's current crate is pinned to a 2022 rustc nightly. Stainless's default SMT result is separate from its System FR calculus foundation and optional Rocq translation. SAW records both `SpecProved` and `SpecAdmitted`, and a proved caller may depend on an admitted callee. Dependency closure and safety-check configuration therefore belong in a certificate, not just its top-level success status.

## Applicability

Source pins are RustHorn `4823f8f9c8e9e1deca71fdffe3c38061ae519c52`, Stainless `399c34a06df8e88679f0985131e8a59a28ab9b3f`, and SAW `27a7ae98256544b55a7a3ce4ce620c1a7889713b`. Stainless's Inox gitlink is `37db954531a653a0ba00aedcbff5b9735f532055`; its full solver implementation was not audited.

System FR is distinguished at the paper-linked `oopsla2019` revision `325bd745404f5425fba3cc53d053b7f363e7076d` and current source `90300f26953caaf5a703089680ad5c14aadb8ad9`. The paper is arXiv `1904.03482v2`, March 24, 2020, SHA-256 `8499729820596e04495868975bf5da7aecee2e8d2c555f1eae2d8570538bf280`. The RustHorn paper is the author-hosted ESOP full version, including its explicit note recommending the newer TOPLAS version, SHA-256 `0bcf21029350d89ec36ead06489a5eef681af5d3308c31ea90a33fff9fe32ef9`. The theorem identification below applies to these observed bytes, not a substituted later paper.

No RustHorn, Stainless, Inox, SAW or solver was built or executed. Source examples are documented verification inputs, not replayed successes. This report adds Stainless as an R047 comparison candidate; it does not replace a separate Flux/Thrust comparison.

## Findings

### F1. RustHorn recursion and genericity have a concrete extraction boundary

Basis: source + documentation.

The current `rust-horn` crate README documents support for recursion and recursive types, but lists loops, arrays/vectors/slices and function pointers as unsupported. It requires `rustc 1.60.0-nightly (17d29dcdc 2022-01-21)`; `rust-toolchain.toml` selects `nightly-2022-01-22` with rustc-dev and LLVM tooling. Repository HEAD in 2024 is not evidence of compatibility with current rustc.

`src/analyze.rs:analyze_fun` reads `tcx.optimized_mir`, pairs the body with `generic_args: fun_ty.substs_of_fun_ty()`, and builds predicates for entry and switch pivots. `analyze/data.rs` substitutes those generic arguments into local, operand and field types. `gather_conds_from_fun` creates a callee predicate application and queues the function type; `analyze` starts at `main`, drains requested callees and caches generated function definitions by their represented names. Recursive calls therefore become recursive predicates, rather than being unfolded to a fixed execution depth.

`represent.rs` includes substituted arguments in predicate names and encodes algebraic data types, including type parameters. This is real generic/recursive representation support, not merely a syntax claim. It does not establish Rust-wide generic dictionary, const-generic, dynamic-dispatch or GAT closure. These interfaces depend on the accepted optimized MIR and selected instantiations. The theorem in F2 concerns a simpler formal calculus, not this whole rustc pipeline.

The current driver's result is an SMT-LIB file: `main.rs:drive_rust_horn` analyzes and writes `rep_summary`; `represent.rs` emits predicate declarations, universally quantified clauses, an assertion excluding a failing `main` and `check-sat`. The inspected Makefile's `try` target generates files for examples; it does not invoke a CHC solver. Thus the exporter itself does not return an independently checked solver certificate. `get_drop_def` remains `unimplemented!`; that is a source limitation for queued custom-drop definitions, not an observed runtime panic or a statement that every drop in the abstract model is unsupported.

### F2. RustHorn's prophecy encoding and theorem do not justify unsafe libraries

Basis: documentation + source + derived.

The paper's COR translation represents a mutable reference by its current value and a prophecy of the value returned when borrowing ends. Ownership restrictions let the functional encoding omit an explicit shared heap. Recursive functions generate CHCs whose predicates describe input/output relations. The paper's Theorem 1 equates the concrete input/output relation and the least CHC model for a well-typed COR program and a simple function; that function has no lifetime parameters or reference-typed input/output. The result describes terminating computations, not termination or arbitrary Rust UB freedom.

The current source retains the same useful mechanism: mutable-reference decomposition and equations connect transferred future values; `Cond::Call` composes function relations. A CHC solver may infer a relational invariant/model satisfying these clauses. Inference is the search procedure; correctness requires that the found model satisfies the actual exported clauses and that the translation's ownership assumptions hold. The current driver's solver-certificate path was not established merely from its emission of `check-sat`.

Unsafe implementations break the automatic premise that typed ownership is faithfully represented by the functional encoding. Their contracts need a separate semantic justification for validity, aliasing, allocation, layout and library invariants, with a bridge showing that the functional relation exposed to clients is sound. That is the role an unsafe-library resource proof can play; the CHC theorem does not supply it. This boundary is a research conclusion, not a demand to prove every library before comparing the technique.

### F3. Stainless separates semantic typing, inference and current SMT acceptance

Basis: documentation + source.

System FR's paper Theorem 5.1 proves soundness of bidirectional typing conditional on semantic validity of generated equality/verification conditions. It formalizes a call-by-value calculus with polymorphism, dependent refinements and recursive types; it does not directly model mutable effects or Rust memory. At the linked 2019 source pin, `Reducibility.v:reducibility_lemma` jointly proves typing yields open reducibility, semantic subtyping, and equality yields observational equivalence. At the current formalization pin, `ReducibilityDefinition.v` interprets an expression as reduction to a value in its type denotation; `ReducibilityLemmas.v:reducible_normalizing` requires a valid interpretation and semantic membership and concludes call-by-value normalization. These are actual formal endpoints, not a theorem about all current Stainless frontend transformations.

Current Stainless documents Scala as its input. `MeasureInference.scala` attempts termination-measure inference and reports unknown/no guarantee when the termination pipeline cannot infer one. `RecursionProcessor.scala` checks recursive call relations for a structural decrease. This is distinct from automatically synthesizing all functional contracts or heap invariants. The System FR paper itself focuses on an unfolding-based verifier without general invariant inference.

Current mutable reasoning has concrete interfaces beyond that pure foundation. The `FirstClassHeap.scala` example expresses heap snapshots/projections and frame claims; `OpaqueEffects.scala` expresses reads/modifies boundaries. `EffectsChecker` rejects prohibited effects and notes that extern functions on mutable types are treated as impure unless annotated pure. `GhostChecker` rejects ghost functions with effects on non-ghost state and ghost information escaping into executable contexts. These checks are relevant frontend mechanisms, but are not Rust borrowing/provenance proofs.

`VerificationChecker.scala` turns unsatisfiability of a negated ordinary VC into `VCStatus.Valid`; counterexample models yield `Invalid`, and unknown, timeout, cancellation, crashes and unsupported cases remain distinct. Satisfiability and precondition-consistency checks use different polarity, so the solver word “sat” does not have one global meaning. The default route trusts the selected frontend transformations, VC encoding and solver interface. A Rust-oriented frontend would need a faithful source/heap/effect encoding and resource-law justification for its trusted abstractions; sharing Scala contract syntax would not establish that bridge.

### F4. Stainless's optional Rocq route is not an admission-free acceptance path

Basis: source.

`CoqVerificationChecher.scala` translates the program, emits per-function files and invokes `CoqIO.coqc`. `CoqEncoder.makeFilePerFunction` calls `transformFunctionsInOrder(d, true)` for dependencies; the `true` mode emits `Admit Obligations.` before proving the target. Mutual recursion is explicitly unsupported by that translation. An admitted dependency is not discharged by the target function's successful proof.

More consequentially, `slc-lib/Lib.v` declares `unsupported : False`, with `magic` eliminating that axiom. `CoqEncoder` translates `Assume` using `magic` and falls back to `magic` for unsupported expressions after a warning. Its imported library therefore permits evidence to depend on an inconsistency; actual theorem assumption closure is essential. This is a source-defined escape hatch in this optional route, not a conclusion about System FR's formalization or the default SMT checker.

`CoqIO.coqc` waits for the process's exit value but classifies a file as valid when captured output is empty; the inspected implementation does not branch on that exit value. It parses error/timeout text otherwise. These facts make an unqualified “Coq Valid” inadequate as a robust certificate acceptance policy. No operational failure was induced here, and no exploit or blanket unsoundness result for Stainless is claimed.

### F5. SAW verifies implementations before reusable overrides, but also admits specs

Basis: source.

`Crucible/MIR/Builtins.hs:mir_verify` builds a method specification from setup commands, prepares the prestate and assumptions, looks up the selected MIR CFG, symbolically executes it, matches the poststate and collects safety/specification obligations. `verifyObligations` proves each implication from pre-assumptions to an assertion through the chosen proof script; invalid or unfinished proof results fail. On success, it creates a `ProvedSpec` with `SpecProved`, per-VC theorem summaries/dependencies, solver statistics and supplied-spec dependencies.

By contrast, `mir_unsafe_assume_spec` constructs the setup specification and immediately creates `SpecAdmitted`, without simulating the implementation or discharging the resulting obligations. `Common/MethodSpec.hs:ProvedSpec` records both statuses; its type name alone is not a proof distinction. During caller simulation, overrides are registered from each object's method specification. The ordinary override exchange asserts its applicability/preconditions and assumes its postconditions; the implementation justification has to come from the object's proof and dependencies.

The documented `overrides.saw` lifecycle first verifies `g`, then verifies `f` using that returned contract; it also supplies separately verified even/odd precondition cases for the same callee. `overrides-unsafe.saw` instead admits `g` before verifying `f`. The caller can therefore have `SpecProved` while depending on `SpecAdmitted`. Accepted reuse needs transitive spec and theorem closure, with any admitted leaves explicitly represented as assumptions.

`verifyPoststate` additionally consults `rwSkipSafetyProofs`: when enabled it clears obligations generated during symbolic execution before checking specified postconditions. The source calls this generally unsound. This option must be excluded or explicitly scoped before claiming simulated safety; “verified postcondition” does not by itself establish safety under every configuration.

### F6. Equivalence against independent specifications has a concrete scope

Basis: source + documentation + derived.

The Salsa20 tutorial compares MIR behavior to Cryptol functions through preconditions, points-to specifications, returned values and expected memory contents. This is a useful independent functional specification interface. It is not equivalence of all source effects, allocation histories, provenance or timing merely because equal outputs are specified. The configuration must identify selected MIR instantiations, memory footprint, permitted aliasing, platform word sizes and environmental effects.

The pinned `salsa20-reference.saw` actually obtains `quarter_round_ov` with `mir_unsafe_assume_spec`; its corresponding `mir_verify` line is commented out. Later `rounds` contracts depend on that object and `apply_keystream` depends on the `rounds` contracts. Source presence of a complete-looking cryptographic script thus does not establish an entirely verified callee chain. No tutorial or zerocopy execution was replayed here.

SAW's reusable contract lifecycle answers the previously unexamined compositional subquestion of R053. Applying it to zerocopy would require extraction of the exact source instantiations, contracts with byte validity and alias/frame premises, an explicit accepted MIR memory-model scope, and dependency/status review. The implementation of that application is future engineering; actual acceptance and coverage measurements need experiments.

### F7. Shared result vocabulary and integration decision

Basis: derived from F1–F6.

| Result/interface | What it contributes | What must accompany it |
| --- | --- | --- |
| RustHorn exported CHCs | Recursive relational verification problem | Accepted MIR/substitutions, safe ownership premises, solver/model validation and unsafe-library contract justification |
| Stainless inferred measure and valid SMT VCs | Candidate termination argument and discharged encoded obligations | Checked functions, extraction/effect rules, solver/configuration and unsupported/unknown outcomes |
| System FR semantic theorem | Typing-to-reducibility foundation for the stated calculus | Semantically valid VCs and calculus/frontend relationship |
| Stainless optional Rocq result | Generated proof attempt | Admission and `unsupported` axiom closure, dependencies, actual exit status; no unconditional acceptance |
| SAW SpecProved | Discharged symbolic implementation obligations against a setup contract | Complete VC/spec dependencies, safety-check options and frontend/memory correspondence |
| SAW SpecAdmitted | Assumed contract usable by callers | Explicit trusted leaf; never relabeled as implementation proof |

This comparison establishes mechanisms and constraints. Building a Rust frontend for Stainless, a CHC model checker/certificate bridge, a source-to-MIR correspondence layer or a zerocopy SAW harness is future work. Comparative inference coverage, actual current-build compatibility, annotation cost and prover/runtime cost were not measured.

## Boundaries

- **Not examined:** full solver/proof-term closure, current builds or tutorial execution, a Rust frontend for Stainless, solver certificate export/validation for every RustHorn backend, or actual zerocopy equivalence checks.
- **Unsupported in named interfaces:** RustHorn's README feature exclusions and custom-drop placeholder; mutual recursion in Stainless's optional Rocq translation. No feature parity with Rust verifiers is inferred.
- **Known not to establish:** `SpecProved` alone does not close admitted dependencies, and an optional Rocq success does not remove the listed axioms/admissions. System FR's pure normalization theorem does not establish mutation/resource correctness.
- **Unknown:** complete supported RustHorn genericity and effects beyond inspected substituted instances; exact existing zerocopy acceptance under SAW. A failed paper GET was resolved using exact arXiv v2; it was not treated as absence of foundations.

## Evidence

Primary source: [RustHorn pin](https://github.com/hopv/Rust-horn/tree/4823f8f9c8e9e1deca71fdffe3c38061ae519c52), `rust-horn/{README.md,rust-toolchain.toml,Makefile}`, `src/{main,analyze,represent,types,util}.rs`, `src/analyze/data.rs`, and recursive list example. Primary paper: [ESOP full version](https://shiatsumat.github.io/papers/esop2020-rust-horn.pdf), §3 Theorem 1; observed hash under Applicability.

Primary source: [Stainless pin](https://github.com/epfl-lara/stainless/tree/399c34a06df8e88679f0985131e8a59a28ab9b3f), `core/src/main/scala/stainless/verification/{VerificationChecker,CoqVerificationChecher,CoqEncoder,CoqIO}.scala`; `extraction/imperative/{EffectsChecker,GhostChecker}.scala`; `termination/{MeasureInference,RecursionProcessor}.scala`; `slc-lib/Lib.v`; `frontends/benchmarks/full-imperative/valid/{FirstClassHeap,OpaqueEffects}.scala`. [System FR paper v2](https://arxiv.org/pdf/1904.03482v2), Theorem 5.1 and §6; [paper-linked formalization](https://github.com/epfl-lara/SystemFR/tree/325bd745404f5425fba3cc53d053b7f363e7076d), `Reducibility.v:190–215`, `Typing.v`; [current formalization](https://github.com/epfl-lara/SystemFR/tree/90300f26953caaf5a703089680ad5c14aadb8ad9), `SmallStep.v`, `ReducibilityDefinition.v`, `ReducibilityLemmas.v:157–165`, `ErasedFix.v`, `ErasedPolymorphism.v`.

Primary source: [SAW pin](https://github.com/GaloisInc/saw-script/tree/27a7ae98256544b55a7a3ce4ce620c1a7889713b), `saw-central/src/SAWCentral/Crucible/MIR/Builtins.hs:870–992,1497–1602,1730–1766`; `Common/MethodSpec.hs:503–550`; `doc/rust-verification-with-saw/{overrides-and-compositional-verification.md,prerequisites.md}`, `code/{overrides.saw,overrides-unsafe.saw}`, `code/salsa20/salsa20-reference.saw`. `source-identities.json` preserves narrow blob identities; upstream source remains authoritative and is not mirrored in this package.

## Revalidation

For RustHorn, preserve the compiler revision and instantiated MIR, inspect emitted clauses, then separately validate the solver result/model for those clauses. Keep recursion and custom-drop support distinct. For Stainless, preserve selected extraction/verification mode; audit System FR correspondence separately from default SMT acceptance; reject unexpected Rocq admissions/false axioms for a closed-proof policy and inspect actual process status.

For SAW, record every specification object's proof method and dependencies, every VC theorem summary and dependencies, and safety-obligation configuration. Replay the callee implementation before using its contract when a closed chain is required. Compare against an independently stated specification with the exact memory/effect domain, and make the source-to-MIR premise explicit before applying the result to Rust source.

*Authored by an AI agent acting on joshlf's behalf.*
