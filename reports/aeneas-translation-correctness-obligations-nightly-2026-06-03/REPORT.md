# Aeneas translation-correctness obligations at nightly-2026.06.03

## Summary

At `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, the ordinary Aeneas pipeline does not turn a successful Rust-to-Lean run into a self-certifying proof that the generated Lean has the same semantics as the Rust source. It consumes Charon LLBC, performs substantial LLBC preprocessing and symbolic execution, constructs and rewrites a pure intermediate program, and finally prints backend code. The generated Lean can then be checked by Lean and used in machine-checked proofs, but that target-side checking establishes facts about the generated Lean definitions and their assumptions. A Rust-level theorem additionally needs a justified source-to-target correspondence.

The pinned implementation contains useful correctness defenses, but they have narrower jobs. It rejects LLBC that was not produced with Charon's Aeneas preset, records many translation failures and returns a nonzero process status when registered errors remain, and offers `-checks` for expensive interpreter invariants. Those mechanisms can detect configuration mistakes, unsupported inputs, and translator bugs. They are not semantic-preservation certificates. In particular, `Config.sanity_checks` defaults to `false`, and the separate generated-pure-code type-checking switch, `Config.type_check_pure_code`, also defaults to `false` with the source comment `TODO: fix the bugs and reactivate`. The `-checks` CLI option sets `sanity_checks`; it does not enable that separate pure-code checker.

For an Anneal proof that is intended to justify a property of Rust, the translation-correctness obligation therefore spans at least five boundaries:

1. **Rust → LLBC:** Charon/rustc extraction and Charon's transformations must represent the relevant Rust behavior faithfully.
2. **LLBC → Aeneas pure program:** Aeneas's pre-passes, symbolic interpreter, symbolic-to-pure translation, and pure micro-passes must preserve the behavior on which the proof relies.
3. **Models and opaque definitions:** Aeneas builtins, standard-library models, user external models, and any unresolved opaque assumptions must have semantics strong enough for the Rust-level claim.
4. **Coverage and failure:** every relevant source behavior must reach the proof model; partial output from a run with registered errors must not be mistaken for complete successful translation.
5. **Pure program → checked proof:** extraction must print the intended target program, the generated Lean must actually be accepted by the selected Lean environment, and the final theorem must be proved without unintended assumptions.

Aeneas's pinned documentation calls the translation “Sound” and the README points to the ICFP 2022 Aeneas formalization and an ICFP 2024 proof about symbolic borrow checking. Those publications are important evidence, but this report deliberately does **not** treat those citations as a blanket proof that the exact 2026 executable, all of its passes, every external model, and every Anneal input satisfy the five obligations above. The neighboring #3720 item on formal results from the Aeneas papers should establish the exact theorems and their applicability to this implementation separately.

No fresh Charon, Aeneas, Lean, or Rust execution was performed. The report reconstructs the operational proof obligations from the exact pinned implementation and its documentation, while using existing exact-revision reports in this corpus to avoid duplicating the translation, external-model, resource-semantics, and proof-tool inventories.

## Applicability

The primary subject is Aeneas release `nightly-2026.06.03`, commit `ac9f1bc5262a5e4ff1e24ca78617121382202727`, which is the Aeneas revision selected by the Anneal state examined for this corpus. The paired LLBC producer is Charon `a535e914f74db4fd9e6be7048f4233270d8945c0`, version `0.1.210`. This report assumes that exact pairing; it does not infer that an adjacent Aeneas or Charon revision has the same checks or correctness boundary.

The report concerns the ordinary functional Aeneas translation, with the Lean backend as the proof-facing target relevant to Anneal. Some implementation findings, such as LLBC preprocessing, symbolic execution, accumulated errors, and optional interpreter invariants, are shared by the other extraction backends. Claims about what Lean checks apply specifically to the Lean output path.

“Translation correctness” here means the justification needed to carry a theorem proved about generated target code back to the corresponding Rust behavior. It is intentionally distinct from three neighboring questions:

- whether Aeneas's generated Lean functions have the shapes documented elsewhere in this corpus;
- what exact theorems the Aeneas papers prove and how mechanized they are; and
- whether the ordinary Aeneas functional model has semantics for general unsafe Rust.

The first is already covered by the Rust-to-Lean and architecture reports. The second remains the separate “Formal results from Aeneas papers” inventory item. The third is covered in part by the resource-semantics and separation-logic reports and is especially important for Anneal, but it is not re-litigated here.

## Findings

### A successful target proof is conditional on the translation relation

The proof-facing Lean interface operates on generated Lean functions. The existing pinned WP report shows that `Aeneas.Std.WP.spec` and `step` reason about those target computations; Aeneas does not emit a Rust-to-Lean equivalence theorem for each translated function. Lean can therefore establish a theorem such as a `WP.spec` fact about the generated definition while knowing nothing intrinsically about the Rust syntax or LLBC from which that definition came.

This is not a defect in Lean. It is a boundary between two proof obligations. Lean checks the theorem that it is given over the target definitions. A separate argument must justify using that theorem as a theorem about the Rust program. The correctness of Charon extraction, Aeneas translation, and any semantic models is part of that argument.

Basis: pinned Aeneas **source** + existing exact-revision corpus evidence + **derived** source-to-target proof boundary.

### Aeneas checks the LLBC production mode, not Rust-to-LLBC semantic equivalence

The pinned CLI loads a serialized `.llbc` file and rejects it if the recorded Charon options do not say `preset = Aeneas`. This is a valuable compatibility guard: the Aeneas pipeline depends on the transformations selected by `charon cargo --preset=aeneas`, so accepting arbitrary Charon output would violate an implementation precondition.

The guard does not establish that the LLBC faithfully represents the Rust source. By the time Aeneas runs, Rust source and rustc execution are upstream of its input boundary. The Aeneas executable does not re-run rustc or compare LLBC behavior with the source. A Rust-level theorem must therefore inherit or separately establish the correctness of the Rust → rustc MIR/Charon → LLBC path for the behaviors it uses.

This obligation is particularly important when Charon intentionally transforms or erases information. Aeneas can be correct with respect to the LLBC it received while an end-to-end Rust claim is still unjustified if the relevant source meaning was lost or changed before that boundary.

Basis: **source** + **derived** boundary consequence.

### The LLBC-to-target path contains semantic transformations, not just serialization

Aeneas does substantial work between LLBC loading and Lean printing. `PrePasses.apply_passes` rewrites the LLBC before symbolic execution. The pinned pass sequence includes closure-lifetime repair, body-region erasure, conversion of an unreachable intrinsic to an explicit undefined-behavior abort, loop normalization, removal of storage/borrow scaffolding, panic simplification, global-access decomposition, and several crate-level simplifications. Later stages symbolically execute function bodies, translate the symbolic result into Aeneas's pure IR, run a substantial pure micro-pass pipeline, decompose loops, and finally extract backend syntax.

Each successful transformation adds an implementation-level semantic-preservation obligation. An internal invariant can show that a transformed state is structurally admissible without showing that it denotes the same source behavior. Similarly, a well-typed final Lean term can still encode the wrong value if a preceding translator pass has a semantic bug.

For Anneal, this means that “Lean accepted the generated file” and “the generated theorem is proved” are necessary target-side checks, but they do not by themselves validate successful execution of the entire source-to-target compiler chain.

Basis: pinned `PrePasses.ml`, `Translate.ml`, and the previously preserved architecture report — **source** + **derived** obligation.

### `-checks` enables expensive interpreter invariants, not a semantic-preservation proof

`Config.ml` documents `sanity_checks` as checks “performed at every evaluation step,” expensive enough to cause an approximately 100× slowdown, and useful for catching mistakes early. The value defaults to `false`. `Main.ml` exposes `-checks`, which sets this flag.

At this revision, `Invariants.check_invariants` conditionally checks five classes of interpreter state:

- the loans/borrows relation;
- borrowed-value invariants;
- typing invariants;
- symbolic-value invariants; and
- uniqueness of abstraction IDs.

`Translate.check_fun_decl_vars_are_well_bound` is also gated by `Config.sanity_checks` and checks free/bound-variable discipline in translated pure functions.

These are strong engineering checks on internal representation consistency. They are not a theorem that an evaluation step preserves LLBC semantics or that the emitted pure function refines the Rust source. Even a run with `-checks` can only establish the properties encoded by those checkers, assuming the checker implementations themselves are correct.

The default-off status also matters operationally. A default successful Aeneas invocation does not imply that these expensive invariant checks ran.

Basis: **source**.

### The separate pure-IR type checker is disabled at this pin

The pinned source defines a second switch, `Config.type_check_pure_code`, under the comment:

`For sanity check: type check the generated pure code (activates checks in several places). TODO: fix the bugs and reactivate`

It is initialized to `false`. `SymbolicToPureTypes.type_check_texpr` invokes `PureTypeCheck.check_texpr` only when that switch is true. `PureTypeCheck.ml` contains real structural checks—for example, application input/output types and lambda binder/body types—but also contains unfinished branches marked `TODO` for several qualifier cases.

The `-checks` option in `Main.ml` sets `sanity_checks`, not `type_check_pure_code`; the pinned CLI source exposes no corresponding option there for this separate flag. Thus `-checks` should not be described as “type-check all generated Aeneas pure code.” The implementation has a pure-IR checker, but this release deliberately leaves its main guard off.

This fact does **not** imply that generated Lean is ill-typed. Lean can independently reject ill-typed emitted code when the generated project is actually checked. The narrower conclusion is that successful Aeneas execution does not itself include this internal pure-IR type-checking stage at the pinned configuration.

Basis: **source**.

### Recoverable failures protect diagnostics, but consumers must preserve fail-closed status

Aeneas often recovers from declaration-local failures so it can continue translating independent definitions and emit useful diagnostics. `PrePasses.apply_passes` can replace a failing body with `ErrorBody`; `Translate.translate_function_to_pure` catches `CFailure` and can return `None`; analogous translation loops can omit globals or other declarations after a registered failure.

The top-level error discipline is what prevents that recovery from becoming success by default. `Errors.push_error` retains registered errors, and `Main.ml` computes `has_errors` from `Errors.error_list` and exits with status 1 if any remain.

The proof obligation for an integrator is therefore two-part:

1. treat a nonzero Aeneas result as a failed translation even if useful target files were emitted; and
2. account for the relevant source/LLBC declarations rather than inferring completeness from the existence of a crate-level Lean file.

If an integration discards the process status or fails to notice that a relevant declaration disappeared, it can create a fail-open proof pipeline even though Aeneas itself recorded the translation error.

Conversely, a zero exit status establishes only that no registered error remained. It is not evidence that no successful translator step contained a semantic bug.

Basis: **source** + **derived** integration requirement.

### Backend compilation is a separate validation stage

The Aeneas CLI path examined here translates and extracts target files; it does not invoke Lean as part of `aeneas -backend lean`. The pinned README gives separate instructions for putting generated Lean files in a Lean/Lake package and making the Aeneas package available.

A robust Lean consumer therefore has another explicit validation obligation after Aeneas exits successfully: the exact generated Lean must be elaborated/compiled in the intended Lean environment. That target check catches malformed syntax, ill-typed output, unresolved names, and invalid proof terms that reach Lean.

It still does not prove source-target equivalence. Lean is checking the target program and theorem under the target environment's declarations and assumptions. It has no implicit knowledge that the definition was generated faithfully from a particular Rust item.

Basis: **source** + upstream **documentation** + **derived** proof boundary.

### External models and opaque definitions introduce independent semantic assumptions

The pinned external-model machinery can replace a Rust identity with a target-side model based on name patterns and metadata. Existing exact-revision research in this corpus establishes that those registrations can filter type parameters and trait clauses, adjust failure/lifting behavior, and otherwise change the semantic interface presented to generated code. The same report establishes an opaque-definition path whose extraction can introduce assumed declarations until the consumer supplies a concrete model.

Matching a name and type shape is not a refinement theorem. If a Rust-level proof uses a modeled operation, the proof inherits an obligation that the model has the relevant Rust semantics. If generated Lean depends on an unresolved opaque assumption, the final theorem is conditional on that assumption unless the integration supplies and justifies a definition/specification that closes it.

A translation-correctness argument must therefore inventory semantic models and assumptions, not only translated function bodies. This is especially significant for library-heavy code: successful translation can intentionally route behavior through trusted backend models rather than through a translated Rust implementation.

Basis: existing exact-revision external-model report grounded in pinned **source** + **derived** obligation.

### Internal builtins are part of the trusted translation semantics too

`src/llbc/Builtin.ml` defines operations whose behavior is handled specially inside Aeneas. Its own comments discuss the engineering burden of concrete builtin evaluation and the possibility of replacing some hard-coded implementations with modeled bodies.

These internal semantic builtins are distinct from the Lean external-model registry, but the correctness obligation is analogous: a Rust-level argument depends on the special interpreter behavior matching the operation it represents. A complete trust analysis must account for both categories rather than treating “generated code contains no external axiom for this call” as proof that the call's semantics came directly from translated Rust.

Basis: **source** + **derived** trust-boundary analysis.

### The documentation's soundness claim is stronger than the executable's local checks

The pinned `documentation/aeneas-overview.md` describes the generated code as faithfully modeling the original Rust semantics and labels this property “Sound.” The pinned README separately says that “The translation has been formalized” in the ICFP 2022 Aeneas work and that there is a proof, published at ICFP 2024, that Aeneas's symbolic execution correctly implements a borrow checker.

Those statements are evidence that Aeneas's design is intended to carry a formal soundness argument; they should not be replaced by the weaker claim that Aeneas is merely an unverified code generator. At the same time, the executable mechanisms above are not themselves a proof that every line of the exact 2026 implementation refines the formal model. The runtime checks catch selected internal inconsistencies, and the generated Lean proves target-level properties.

For this corpus, the correct boundary is therefore explicit: **do not infer exact theorem-to-implementation coverage from the documentation citation alone, and do not infer absence of a formal argument merely because the executable emits no certificate.** The separate paper-results item must recover the exact formal results, assumptions, mechanization status, source calculus, and correspondence—if any—to this pinned codebase.

Basis: upstream **documentation** + pinned **source** + **derived** applicability boundary.

### The ordinary functional backend's advertised domain limits the correctness claim

The exact-revision resource-semantics report establishes that the ordinary functional model intentionally erases or abstracts resources such as ordinary reference identity and Box allocation identity, while raw-pointer dereference is unsupported at this pin. The Aeneas documentation describes the functional translation in terms of a supported safe-Rust subset and ongoing work for unsafe/concurrent semantics.

A translation-correctness proof can be sound for that intended subset without justifying a theorem about arbitrary unsafe Rust. For Anneal, which ultimately targets unsafe-code reasoning, the domain obligation is therefore as important as pass correctness: before lifting a Lean theorem back to Rust, establish that the source behavior being reasoned about actually lies in the semantics provided by the selected translation/model path.

Failing closed on an unsupported raw-pointer dereference is useful evidence; it does not make the functional translation a semantics for all other unsafe operations by implication.

Basis: existing exact-revision resource-semantics report grounded in pinned **source** and **documentation** + **derived** applicability requirement.

### A practical Anneal ledger should keep the obligations separate

For a Rust-level result, later Anneal work should be able to answer each of these questions independently:

1. **Input identity:** Which exact Rust/rustc, Charon, Aeneas, Lean, and model-library revisions produced and checked the artifact?
2. **Source coverage:** Which Rust items and behaviors are intended to be covered, and did Charon preserve them in LLBC without a recorded extraction failure?
3. **Translation coverage:** Did Aeneas successfully translate every required LLBC declaration, with zero registered errors and no relevant declaration silently outside the selected translation set?
4. **Domain:** Are the operations in the claimed theorem within the semantics supported by the selected Aeneas translation/model path?
5. **Translator justification:** What formal result, validation evidence, or explicit trust assumption justifies the Charon and Aeneas transformations used for those operations?
6. **Model justification:** Which builtins, standard-library models, external models, opaque declarations, or axioms does the generated target program depend on, and what justifies them?
7. **Target validation:** Was the exact generated Lean accepted under the exact intended environment?
8. **Proof assumptions:** Does the final Lean theorem depend only on intended axioms/opaque declarations, and does its statement actually imply the desired Rust-level property once the preceding correspondence assumptions are supplied?

These are not eight independent claims that Aeneas promises to prove automatically. They are a decomposition of the end-to-end obligation. Keeping them separate prevents a strong result in one layer—such as a kernel-checked Lean theorem—from obscuring an unverified assumption in another layer.

Basis: **derived** synthesis of the pinned pipeline and neighboring exact-revision reports.

## Boundaries

- No fresh Charon, Aeneas, Lean, Lake, or Rust execution was performed.
- This report does not determine the exact formal theorem statements, proof artifacts, mechanization status, trusted base, or implementation-correspondence argument in the ICFP 2022 or ICFP 2024 Aeneas work. That is the adjacent “Formal results from Aeneas papers” inventory item.
- The report does not claim that Aeneas is unsound. It identifies what the exact executable checks locally and which additional correspondence assumptions are needed before a target theorem is used as a Rust theorem.
- `-checks` being optional does not show that ordinary translation is incorrect. It shows only that the expensive invariant checker is not part of a default run.
- `Config.type_check_pure_code = false` does not show that emitted Lean is ill-typed. It shows that this internal pure-IR checker is not enabled at the pinned release. A separate Lean build can provide target-language checking.
- A zero Aeneas exit status means no registered errors remained under the observed error discipline; it is not a semantic-preservation certificate.
- A nonzero run can still leave useful partial output. Such output is diagnostic/research material, not evidence of complete successful translation.
- The report does not inventory every internal assertion, sanity check, micro-pass, builtin, standard-library model, or unsupported Rust feature. Separate reports in this corpus cover several of those subjects in detail.
- It does not establish that all unsupported or approximated semantics are reported as errors rather than warnings. The supported/unsupported failure-matrix report is the better authority for that inventory.
- It does not analyze the developing separation-logic path as a replacement correctness basis for unsafe Rust; that work has its own exact-status report.
- It does not infer that the formal results cited by the README apply unchanged to later or earlier Aeneas revisions.

## Evidence

**Primary Aeneas subject.** `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`).

- `README.md`, blob `f331650bd4291d27ba6cee736ce51cf31da9cac1`: LLBC/Charon usage boundary; separate Lean-project setup; backend overview; “Formalization” section linking the ICFP 2022 functional-translation work and ICFP 2024 symbolic borrow-checking work.
- `documentation/aeneas-overview.md`, blob `439076012c1ba93c7ec1bf25aca42e0f1ec14756`: descriptive “Sound” claim that generated code faithfully models original Rust semantics and the ownership-driven/modular translation model.
- `src/Main.ml`, blob `b3f373f8c449eeae0f9a50bb0ce2d2963903eddc`: `-checks`; serialized LLBC loading; `--preset=aeneas` guard; translation dispatch; accumulated-error handling; final nonzero exit on registered errors.
- `src/Config.ml`, blob `99a9eba5ae67dde20dbfd8d835cdc2900fc60355`: `sanity_checks = false`; `type_check_pure_code = false` with the “fix the bugs and reactivate” comment; default recoverable-error configuration.
- `src/interp/Invariants.ml`, blob `3b67d1e21b165013ed503a3b8b9ceb5ca636a2a4`: interpreter invariant checks for loan/borrow relationships, borrowed values, typing, symbolic values, and abstraction-ID uniqueness, all gated by `Config.sanity_checks` at the top-level checker.
- `src/Translate.ml`, blob `8376e580b542bf3ee28cc9e3d4c170a17b23d379`: well-bound-variable sanity check gated by `Config.sanity_checks`; symbolic/pure translation staging; recoverable `CFailure` handling for functions and other declarations.
- `src/symbolic/SymbolicToPureTypes.ml`, blob `d35b6d67a65af220fdb56614ab1b51edc029b06f`: `type_check_texpr` calls the internal pure type checker only when `Config.type_check_pure_code` is true.
- `src/pure/PureTypeCheck.ml`, blob `e9a07a43c2b77a1f71ca894af824ad23497e7fe0`: structural pure-expression type checking, including application and lambda checks, plus unfinished `TODO` branches for some qualifiers.
- `src/PrePasses.ml`, blob `dc0ab803c26dafb14caf0da1bcc73e3499716835`: semantic/representational LLBC pre-pass pipeline and failure recovery to an error body while retaining a registered error.
- `src/Errors.ml`, blob `c135674b8601786616c6c20ad81ec388bb8cbfea`: accumulated error list, recoverable `CFailure`, and internal sanity-check failure machinery.
- `src/pure/PureMicroPasses.ml`, blob `e0662ab3153f3c401b44cbe6c0cad4e17157f063`: the pure-IR transformation stage between initial symbolic-to-pure translation and extraction.
- `src/extract/Extract.ml`, blob `52754e4fdb25b50fce63abe2d2184751d69632e8`: final backend extraction and opaque-declaration qualification/assumption path.
- `src/llbc/Builtin.ml`, blob `fec847925d30e0236f4bd5a83b18b270577f7918`: Aeneas-internal semantic builtins and comments about hard-coded concrete evaluation versus modeled bodies.

**Paired Charon subject.** `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, version `0.1.210`. The paired revision is relevant because Aeneas's source boundary begins at serialized LLBC produced by Charon; the exact Charon representation and source-extraction behavior are covered by dedicated reports in this corpus rather than repeated here.

**Related current reference packages used to establish neighboring boundaries.** `reports/aeneas-architecture-translation-pipeline-nightly-2026-06-03` preserves the exact executable staging and accumulated-error behavior as durable ready work; the currently published `reports/aeneas-rust-to-lean-translation-nightly-2026-06-03`, `reports/aeneas-external-models-nightly-2026-06-03`, `reports/aeneas-resource-semantics-nightly-2026-06-03`, and `reports/aeneas-wp-proof-tools-nightly-2026-06-03` preserve the target translation shape, model/opaque trust boundary, safe-functional resource boundary, and proof-facing Lean interface respectively.

No evidence acquired for this report is fresh **execution**.

## Revalidation

For a future Aeneas revision, revalidate the correctness boundary before assuming that a previously justified integration still applies:

1. Resolve the exact Aeneas revision, paired Charon revision, and target Lean toolchain.
2. Inspect `src/Main.ml` for the LLBC input contract, Charon-preset guard, `-checks` wiring, translation dispatch, and final accumulated-error exit policy.
3. Inspect `src/Config.ml` for the defaults of `sanity_checks`, `type_check_pure_code`, and error-recovery settings. If `type_check_pure_code` is enabled or removed, follow every caller to determine what target IR is now checked.
4. Diff `src/interp/Invariants.ml` to recover what `-checks` actually validates. Do not assume the invariant set or its cost remains unchanged.
5. Diff `PrePasses.apply_passes`, `Translate.translate_crate_to_pure`, the symbolic-to-pure conversion, `PureMicroPasses`, and extraction. New or reordered semantic transformations create new correspondence obligations even when generated syntax looks similar.
6. Inspect the builtin and external-model mechanisms for new assumed or specially implemented operations. Record any opaque declarations that can enter the Lean environment.
7. Re-read the README/formalization documentation. If a new mechanized semantics, proof-producing translator, translation-validation pass, or theorem-to-implementation link has appeared, preserve that evidence rather than carrying forward this report's trust decomposition unchanged.
8. Separately revalidate the formal papers/results against the exact implementation. A documentation citation is not enough to establish that correspondence.

On a surface that can execute the toolchain, add a narrow validation fixture with: one clean supported function, one input that triggers a recoverable Aeneas translation failure while leaving another declaration translatable, and one function depending on an external model. Run the clean case with and without `-checks`, preserve Aeneas exit status and emitted files, and build the exact generated Lean project. The failure case should establish that partial output does not become a zero-status translation. The external-model case should make the target assumption/model dependency visible.

Those probes test fail-closed integration and target well-formedness. They still do not establish semantic preservation. Revalidating that stronger property requires the separate formal-result/implementation-correspondence analysis described above.