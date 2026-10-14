# RefinedC/Lithium and CN: ownership automation and result interfaces

## Summary

RefinedC's reusable mechanism is an extensible semantic ownership type with proof-producing Lithium automation over Caesium. CN instead provides a constrained ownership specification language used by static resource inference, runtime instrumentation and test-input generation. Those interfaces can share specifications without making their outputs equivalent forms of evidence.

At the inspected CN revision, the optional resource-inference proof-log export generates a theorem ending in `Admitted`. The exported relation checks selected resource-inference steps, not whole-program safety. Consequently, neither an export flag nor a successful static-verifier exit is sufficient evidence of an independently checked, admission-free program certificate.

## Applicability

Source observations concern RefinedC `2e89846baeaa7f65cbe17e3ae7297a8ed5b4feca` and CN `b4a2f009234d9c80380dbf95a9b2325e36a4705d` (tree `ed4c238beed80859f5d02b35e2d1afbed9a0ff78`). CN's `cn.opam` dependency `cerberus-lib.dev#c8c085d` resolves to Cerberus `c8c085d4714ae17095b2e1202fa33c5545d98df1`, tree `49bbaa33463aec6786c31a084031e2abe521aecb`. RefinedC's README names a different Cerberus revision, `f11e6b335a687c1b77539f7e5695607d09dfc3ea`; these configurations are not equated.

The RefinedC source's `coq-lithium.opam` requires Coq 9.1.0, Rocq-Iris `dev.2026-09-10.3.b3495ef9` or `dev`, stdpp-unstable, Dune ≥3.21.0 and record-update 0.3.6. This is dependency declaration evidence, not a fully locked or locally replayed build. No RefinedC, CN, Fulminate or Bennet execution was performed. Paper kernel theorems and current implementation paths are explicitly distinguished below.

## Findings

### F1. RefinedC types expose ownership laws rather than just refinement formulas

Basis: source.

`theories/typing/type.v:type` contains location ownership `ty_own : own_state → loc → iProp Σ`, value ownership `ty_own_val`, an operation/layout compatibility predicate, an update from full ownership to persistent shared ownership, alignment and size laws, and rules for extracting a value with points-to ownership and reconstructing location ownership. The `Own`/`Shr` interface is semantic evidence about allocation contents and permitted sharing; its `Shr` state is not a Rust lifetime borrow.

`typing/function.v:fn_params` supplies argument types, a resource precondition, an existential result witness type and a result type/resource postcondition. `typed_function` universally quantifies refinement parameters and requires a persistent proof for every argument/local-location vector. Its initial resource bundle includes typed argument locations, uninitialized local storage and the precondition, then proves a typed statement body. This supports modular extension by proving new semantic type and instruction rules, rather than inserting unverified solver axioms.

`typing/adequacy.v:refinedc_adequacy` requires a `typePreG` instance with invariants, authoritative heap ownership, allocation metadata/aliveness maps and a function table. It also requires valid initial global-block allocation and a logical initialization proof supplying every thread main as a function pointer with a precondition `P`. For every finite `nsteps` execution in `c_lang`, it concludes `not_stuck` for each resulting thread. This theorem is source-model safety. It is not a C compiler theorem, a termination claim, or a result for arbitrary unverified callers.

### F2. Lithium automation constructs logical evidence and exposes unresolved goals

Basis: source + documentation + derived.

`lithium/definitions.v:limodal` records a modality with wand monotonicity, introduction and binding laws. Automation instances are accompanied by lemmas proved in the resource logic. `lithium/interpreter.v:liStep` tries extension hooks, separation/conjunction/wand rules, existential instantiation, pure side conditions, context search, case analysis, persistence, modalities and accumulation. For example, `liExtensible` refines a proved `tac_apply_i2p` lemma and solves its typeclass premise; it does not return a solver Boolean as a proof of any arbitrary proposition.

The framework permits user-supplied rules and heuristics, but the corresponding proof obligations still need completion. `FAQ.md` recommends stepping `liRStep`, inspecting `liShow` and enabling typeclass debugging when automation gets stuck. It also explains existential-instantiation guidance and why simplification rules should normally be equivalences to avoid losing provability. A remaining goal is incomplete verification; it is not a counterexample or a proof that the input is unsafe. A completed theorem may still rely on admissions or imported assumptions, so the chosen theorem closure must be audited.

Caesium locations are provenance/address pairs (`caesium/loc.v:prov/loc`), with bytes, layouts, allocation metadata and aliveness modeled separately. The selected/default configuration has `enforce_alignment := true`; a separately supplied no-alignment configuration changes that semantic premise. Pointer offset constructors in `caesium/lang.v` explicitly contain alignment TODOs, illustrating why the configuration switch is not a proof that every pointer operation checks alignment. This model and its extensions need operation-specific comparison with Rust provenance, typed validity and borrowing; no C/Rust memory-model identity is asserted.

### F3. CN inference and diagnostics are a separate acceptance interface

Basis: source + documentation.

CN's published kernel operates on annotated, let-normalized Core. Its soundness appendix Theorem 1 proves resource-term progress/preservation with unchanged frame heaps; Theorems 2 and 3 prove program progress and preservation. The latter assume exhaustive computational patterns and correctly annotated top-level functions. The logical entailment relation and frontend generation remain premises of application; the paper theorem is not a theorem about every line of the current OCaml checker.

In current `bin/verify.ml`, `Check.time_check_c_functions` checks the selected `(skip, only)` functions, reports type errors and exits according to those errors. The successful result therefore needs a checked-function set and option configuration, not just a project name. `resourceInference.ml` matches available resources to predicate requests, uses subsumption, unfolds or packs where permitted, and tracks consumption and resulting context. Failure creates a `Missing_resource` diagnostic with requests, situation, model and context. This is inference of resource access/instantiation within supplied specifications; it is not evidence of arbitrary contract or loop-invariant synthesis.

`solver.ml:provable_or_unknown` asks whether assumptions together with the negated goal are unsatisfiable. `Unsat` returns `True`, `Sat` returns `False` with a model, and `Unknown` is retained internally. The public `provable` interface maps `Unknown` to `False`. This prevents unknown from being accepted as a proof, but it means a failed entailment request is not necessarily a demonstrated semantic falsity. A displayed SMT model or missing-resource error is not automatically a replayed C counterexample.

### F4. Testing specifications preserves a different evidence boundary

Basis: documentation + source + derived.

Fulminate translates CN specifications to C runtime assertions. Its restricted binding discipline makes ownership predicates executable, with runtime ghost state representing ownership transfer. The POPL 2025 paper's Theorem 3.4 relates initial resource-passing and instrumented configurations; Theorem 3.5 proves a step bisimulation for related configurations, and Corollary 3.6 gives equivalent ownership-check failures. The relation maps each owned address to its owning stack depth. These endpoints concern a small C-like language and are distinguished from the full C instrumentation. They are mechanism theorems, not universal program verification from passing tests.

Current `doc/README-FULMINATE.md` documents `cn instrument` producing an instrumented `.exec.c` and specification `.cn.h/.cn.c` files. `lib/fulminate/fulminate.ml` identifies AIL loads, stores, compound stores and other accesses for instrumentation. The current Bennet `synthesize` pipeline first replaces raw frontend predicate definitions with well-typed normalized definitions, then transforms through generation stages with an ownership abstract domain always included. It can choose a symbolic generation path or further concrete code-generation stages. The comment explains a real representation requirement: raw `ArrayShift` indices may lack the type invariants needed by later SMT pruning.

Thus static proof, instrumented runtime checking, and generation of precondition-satisfying test inputs form complementary workflows. Passing tests covers executed inputs, paths and instrumentation; generator construction alone does not prove that every input is generated. This investigation measured neither test coverage nor runtime overhead, and does not transfer paper benchmark measurements to the pinned current implementation.

### F5. Current proof-log and interactive-lemma exports are not whole-program certificates

Basis: source.

`lib/prooflog.ml` logs two classes of events: `PredicateRequest` with input/output contexts and nested steps, and `UnfoldResources`. `coq/Reasoning/ResourceInference.v:prooflog_valid` is `List.Forall log_entry_valid`. The inspected rule checks context preservation, resource removal, predicate subsumption and pointer/argument equalities for a selected inference step. No inspected theorem identifies this relation with program operational safety or a complete checker-run certificate.

`bin/common.ml` exports the MuCore file and optional log after verification; `--coq-check-proof-log` controls whether it emits a proof attempt. `lib/pp_mucore_coq.ml:coq_inference_proof` emits `resource_inference_steps_valid`, invokes `prove_log_entry_list_valid` and then emits `Admitted.`. The sample usage in `ProofAutomation.v` ends with `Qed`, but that comment is not the current exporter output. This source contradiction must remain visible. Even if a selected proof attempt could finish all goals, the generated command accepts an admission and should not be accepted as a closed certificate without inspecting or replacing its termination command and replaying the result.

CN's interactive lemma export is another interface. `lemmata_lean.ml` imports `CN_Lib`, its Iris/fixpoint library and parameter instances, then generates lemma specifications. It explicitly marks `Each` unsupported in this Lean translation. The supplied Lean heap library defines `Ptr := Int` and `Val := Option Int`, with multi-byte integer ownership constructed from byte predicates and numerical bounds. The Rocq lemma library separately admits `int_to_bytes`. These files establish useful abstract lemma meanings, but their definitions are not themselves proofs of correspondence to the active Cerberus memory implementation. Generated statements require user proofs, dependency closure and a bridge for their intended application.

### F6. Transferable architecture and a precise acceptance record

Basis: derived from F1–F5.

For Anneal, the transferable pieces are semantic ownership interfaces with proved extension laws; deterministic resource-request diagnostics; specifications with an executable fragment; and logs that can be checked independently for a precisely defined relation. A result record should contain the source/model/compiler identities, options, checked function set, contract and resource-law dependencies, result category, and either a proof with its axiom closure or a concrete test trace. Unknown entailment, automation failure, an unsupported export construct, a witnessed failing test and a completed proof should remain distinct.

This comparison answers the architectural research questions with known limitations. Implementing Rust lifetime/provenance semantics, proving a source/extraction bridge, repairing an exporter for accepted certificates, and measuring annotation/runtime cost are future work. Full replay of current CN proof logs and RefinedC theorem assumptions remains an unperformed validation task, not a prerequisite invented for the architectural comparison.

## Boundaries

- **Not examined:** full tool builds, end-to-end certificates, runtime tests, annotation/cost measurements, all Cerberus memory configurations, or every Lithium extension.
- **Unknown:** complete proof-term assumption closure, coverage of proof logs across current checker operations, and correspondence of the interactive lemma models to the current backend. Failed GETs for guessed `pipeline.ml`/`run.ml` paths did not establish absence; actual `bin/common.ml` was inspected.
- **Unsupported at the inspected interface:** `Each` in CN's Lean lemma translation. This is not a global CN unsupported claim.
- **Known limitation:** generated proof-log admission and the Rocq lemma byte-conversion admission prevent treating the named exports as independently established, admission-free evidence. They do not negate the separate paper kernel theorem, static inference implementation or testing mechanism.
- **Environmental premise:** these are C frameworks. Rust borrowing, source UB, type validity, trait/library invariants and target effects need a Rust-specific interpretation and correspondence argument.

## Evidence

Source: [RefinedC pin](https://gitlab.mpi-sws.org/iris/refinedc/-/tree/2e89846baeaa7f65cbe17e3ae7297a8ed5b4feca), `theories/typing/{type,function,adequacy}.v`; `theories/lithium/{definitions,interpreter}.v`; `theories/caesium/{loc,byte,lang}.v`, `config/{selected_config,default_config,no_align_config}.v`; `coq-lithium.opam`, README and FAQ.

Source: [CN pin](https://github.com/rems-project/cn/tree/b4a2f009234d9c80380dbf95a9b2325e36a4705d), `cn.opam`; `bin/verify.ml:78–124`, `bin/common.ml:192–216`; `lib/resourceInference.ml:predicate_request/fail_missing_resource`; `lib/solver.ml:1490–1539`; `lib/prooflog.ml`; `lib/pp_mucore_coq.ml:2296–2329`; `coq/Reasoning/{ResourceInference,ProofAutomation}.v`; `coq/CN_Lemmas/CN_Lib_Iris.v:26–39`; `lib/lemmata_lean.ml`; `lean/CN_Lib/CN_Lib/CN_Lib_Iris.lean:20–93`; `lib/testGeneration/bennet/bennet.ml:normalize_prog5_defs/synthesize`; `lib/fulminate/fulminate.ml`; `doc/README-FULMINATE.md`. `source-identities.json` records narrow source identities without mirroring source.

Documentation: [RefinedC PLDI 2021 paper](https://plv.mpi-sws.org/refinedc/paper.pdf), SHA-256 `80d43dea0e754222a6aa851c884b4d2aee59d288a0237409952e45941104c9e0`; [CN POPL 2023 paper](https://www.cl.cam.ac.uk/~cp526/popl23.pdf), SHA-256 `c8704536456f4b6bb564ecd709c2f77e90d6fd659532e68f2e083a6c9a1140c8`; [soundness appendix](https://www.cs.ox.ac.uk/people/christopher.pulte/popl23_soundness.pdf), SHA-256 `feb882a6e2cbde9e6cdb120319e06527e90e9399842a01d81b5450acd64e275d`; [Fulminate POPL 2025](https://www.cl.cam.ac.uk/users/pes20/cn-testing-popl2025.pdf), DOI `10.1145/3704879`, SHA-256 `347d79ce5a1c2d4fdb12412446ff69a02bd41990e91cd1ca9e40976d746b7954`; [Bennet author paper](https://zain-k-aamer.com/papers/bennet.pdf), SHA-256 `d479fda5d808f07d6a3eb4193c0dacfe503c098dd4fedf15b7dc43f6d943a521`. The Bennet PDF is identified by observed bytes; no stronger immutable paper version is inferred.

## Revalidation

Inspect the chosen model/configuration and function-selection flags before interpreting results. Replay the exact logical theorem and its assumptions for RefinedC. For CN, capture static result category and solver unknowns; verify the exported command text and check its theorem's assumptions rather than relying on the export option name. Establish what the log relation certifies and what checker operations it omits.

For runtime claims, compile and execute the generated instrumentation with a recorded compiler, input set and effect environment. Keep those traces separate from static proof. For a Rust adaptation, prove the ownership/lifetime/provenance interpretation and source correspondence separately from automation and testing.

*Authored by an AI agent acting on joshlf's behalf.*
