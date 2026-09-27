# Aeneas architecture and translation pipeline at nightly-2026.06.03

## Summary

At `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, Aeneas is a staged compiler from Charon's serialized LLBC to a proof-assistant program. The normal path is not a direct LLBC-to-Lean printer. It is:

`Charon --preset=aeneas` → serialized LLBC → Aeneas LLBC pre-passes → translation context → symbolic execution → Aeneas pure functional IR → pure-IR micro-passes and loop decomposition → backend extraction.

The Lean, F*, Coq, and HOL4 backends share the symbolic and pure translation machinery, but the pipeline is not completely backend-neutral. Command-line setup changes several translation and micro-pass options before translation, and backend extraction imposes additional representation and file-layout choices.

The symbolic interpreter is also the core of Aeneas's separate `-borrow-check` mode. Normal translation invokes it with synthesis enabled and converts the resulting symbolic AST to pure code; borrow-check mode invokes the same interpreter with synthesis disabled and emits no proof-assistant translation.

Failures are recoverable internally by default so Aeneas can continue diagnosing or translating independent declarations. Pre-pass failures can replace one function body with an error body, and function/type/trait translation catches `CFailure` around individual declarations. This recovery is **not** a successful whole-crate result: registered errors are retained globally, and the CLI exits with status 1 if any error was recorded. The existence of generated files therefore does not establish successful translation. A consumer such as Anneal must use process/error status plus coverage accounting, not generated-file presence alone.

No fresh Aeneas, Charon, Lean, F*, Coq, or HOL4 execution was performed. The report reconstructs the exact pipeline from pinned source and upstream documentation. Separate reports in this corpus cover value/borrow translation, external models, proof tooling, Charon compatibility, and resource-semantics boundaries in more detail.

## Applicability

The primary subject is Aeneas release `nightly-2026.06.03` at `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`. Its source and release machinery pair it with Charon `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, version `0.1.210`, using Rust toolchain `nightly-2026-05-31`.

The normal input discussed here is one `.llbc` crate loaded by the Aeneas CLI. The pinned README tells users to produce it with `charon cargo --preset=aeneas`; `src/Main.ml` independently rejects an input whose serialized Charon options do not record the Aeneas preset. This report describes the Aeneas-side architecture after that LLBC boundary. Charon's own rustc integration, source coverage, LLBC schemas, and version compatibility have separate reports.

Aeneas supports several output backends at this revision: Lean, F*, Coq, and HOL4. The shared stages described below apply to normal translation unless a finding says otherwise. Backend-specific emitted syntax and library models are outside the report except where they change pipeline structure.

The report distinguishes two CLI modes:

- **translation mode**, selected with `-backend`, runs the full pipeline and writes target-language files;
- **borrow-check mode**, selected with `-borrow-check`, reuses the symbolic interpreter but does not synthesize or extract target code.

The implementation defaults matter to some findings. In particular, `Config.parallel` is true, `Config.fail_hard` is false, `Config.warnings_as_errors` is false, and `Config.drop_as_no_op` is true. `-abort-on-error`, `-warnings-as-errors`, `-sequential`, and `-eval-drops` change those defaults. These are exact source facts for this revision, not stable Aeneas interface guarantees.

## Findings

### The executable accepts serialized LLBC, not Rust source

`src/Main.ml` parses exactly one input file, loads it with `crate_of_json_file`, clears Charon's `short_names` field to make later printing more deterministic, and checks that the serialized crate says it was generated with Charon's Aeneas preset. The README gives the corresponding producer command, `charon cargo --preset=aeneas`, followed by `aeneas -backend ... LLBC_FILE`.

The architectural boundary is therefore explicit: Charon owns Rust/rustc extraction into LLBC; Aeneas starts from a serialized LLBC crate. Aeneas can inspect the LLBC, preprocess it, interpret it symbolically, and extract proof-assistant code, but this executable path does not re-run rustc or recover Rust information absent from its input.

Basis: **source** + upstream **documentation**.

### A fixed LLBC normalization stage runs before either translation or borrow checking

After loading and validating the crate, `Main.ml` calls `PrePasses.apply_passes` before choosing translation or borrow-check mode. `PrePasses.ml` first applies a crate-wide normalization for rustc's array `Default` implementations. It then applies a fixed sequence to each function body:

1. repair closure lifetimes;
2. erase body regions that are not needed at function-call boundaries;
3. replace `core::intrinsics::unreachable` calls with `Abort UndefinedBehavior`;
4. normalize loops;
5. remove useless joins;
6. remove shallow-borrow/storage-live/dead machinery;
7. decompose string borrows;
8. simplify panic forms;
9. decompose global accesses; and
10. refresh statement IDs.

After the per-function sequence, additional crate-level passes strip unnecessary target suffixes, filter marker traits and type aliases, replace statics, remove vtables, rename type variables, and simplify trait calls.

These are semantic and representational preprocessing steps, not merely pretty-printing. For example, `erase_body_regions` deliberately removes some region information before symbolic execution, and `remove_unreachable` changes a particular intrinsic call into Aeneas's explicit undefined-behavior abort form. A later consumer cannot assume the symbolic interpreter sees raw serialized LLBC unchanged.

Basis: **source**.

### A pre-pass failure degrades one body but records a whole-run error

Each per-function pre-pass is wrapped in recovery. If a pass raises `CFailure`, Aeneas records an error saying that the function body is being ignored and replaces the body with `ErrorBody`, then continues processing the crate. This makes later diagnostics and independent translation possible without requiring immediate process termination.

That local recovery does not erase the failure. `Errors.push_error` appends registered errors to a global error list, and `Main.ml` exits with status 1 after processing whenever that list is nonempty. `-abort-on-error` changes recovery further by making registered errors abort immediately.

For pipeline consumers, the distinction is important: Aeneas may produce output after a declaration has failed, but the run is still unsuccessful. Generated output must not be interpreted as proof that every relevant input declaration was modeled.

Basis: **source** + **derived** implication for consumers.

### The translation context is the bridge from LLBC identities to all later stages

`translate_crate_to_pure` begins by computing one translation context and then uses that context while translating types, globals, function signatures, functions, traits, and trait implementations. The same context carries the crate and declaration information used by name matching, builtin/model lookup, type analysis, and later extraction naming.

This shared context is why external-model recognition and declaration selection are not independent post-processing steps. Builtin and external mappings can affect which declarations are treated as translated definitions versus references to target-side models, while the pure translation still retains LLBC-derived declaration identities for cross-references.

Basis: **source**; the interaction with standard-library/external mappings is also documented in the separate external-model report.

### Transparent function bodies go through symbolic execution before pure translation

For a function with a structured body, `translate_function_to_symbolics` invokes `evaluate_function_symbolic` with `synthesize = true`. The result consists of symbolic input values plus a synthesized symbolic AST. `translate_function_to_pure_aux` then turns that symbolic result into Aeneas's pure representation, including forward and backward functions.

A `TargetDispatchBody` is a special path: Aeneas does not run the symbolic interpreter. It creates symbolic input placeholders and a `TargetDispatch` symbolic node directly. Other non-translatable/opaque body forms yield no symbolic body and are represented downstream as opaque declarations.

Thus “Aeneas translation” has at least three materially different body paths: interpreted structured bodies, directly synthesized target-dispatch bodies, and opaque/non-translatable bodies. Treating every output declaration as the result of symbolic execution would be incorrect.

Basis: **source**.

### Types, globals, signatures, functions, traits, and impls have separate translation steps

`translate_crate_to_pure` does not process the crate as one undifferentiated AST transformation. It:

- translates type declarations;
- translates global declarations separately from their initializer bodies;
- computes pure signatures for the selected functions;
- computes builtin-function signatures;
- translates function bodies;
- translates trait declarations; and
- translates trait implementations.

Global initializer bodies are function bodies and are translated with ordinary functions later. Function signatures are computed for the crate before function bodies are translated, so body translation can call other functions through known translated signatures.

This staging creates multiple completeness boundaries. A body can fail even when its signature translated; a global declaration can fail independently; trait declaration or implementation translation can fail independently. An end-to-end coverage claim must therefore account for more than the presence of one generated module or one translated entry function.

Basis: **source** + **derived** completeness implication.

### Per-declaration recovery lets translation continue, but the CLI still fails the run

The normal function translator catches `CFailure` around a function and returns `None`; analogous loops around globals, traits, and trait impls filter out declarations whose translation raises `CFailure`. The source explicitly says this behavior lets compilation make progress. Transparent functions are processed separately from opaque ones and may be processed in parallel.

The recovery boundary is diagnostic/engineering convenience, not a success policy. Errors raised through the recoverable error machinery remain in `Errors.error_list`, and `Main.ml` exits 1 if that list is nonempty. A caller that ignores the process result and consumes whatever files happened to be emitted can therefore fail open even though Aeneas itself reports failure.

Basis: **source** + **derived** consumer requirement.

### Pure-IR micro-passes form another substantial stage before backend printing

After initial pure translation, Aeneas runs `PureMicroPasses.apply_passes_to_pure_fun_translations`. The pass set performs representation-changing simplifications such as pretty-name recovery, metadata removal, monadic-assert introduction, lambda and let simplification, beta reduction, Box-function elimination, trait-call simplification, loop input/output analysis, loop decomposition preparation, aggregate simplification, and array/slice-update normalization. It then decomposes loops, can introduce fuel, adds final type annotations, and computes reducibility metadata.

Several micro-passes are configuration-gated. For example, decomposition of monadic lets and nested patterns, introduction of `massert`, and lifting pure calls to monadic calls depend on `Config` flags. `Main.ml` changes some of those flags after backend selection: Lean enables `merge_let_app_decompose_tuple` and `lift_pure_function_calls`; Coq enables decomposition of monadic and nested let patterns; F* disables `intro_massert`.

The common symbolic semantics therefore feeds a configurable pure-IR normalization layer before backend syntax is emitted. The final pure program is not simply a backend-independent frozen IR printed four different ways.

Basis: **source**.

### Parallelism is an implementation strategy inside translation, not a different semantic mode

Parallel execution is enabled by default. Before body translation, transparent functions are sorted by decreasing LLBC function size and processed through `parallel_filter_map`; opaque functions and transparent functions are handled in separate groups. Pure micro-passes similarly process opaque and transparent translations in parallel with domain-local fresh-variable generators.

The source contains explicit race-avoidance machinery for shared diagnostic data and fresh-variable generation. It also clears LLBC `short_names` before translation “to make printing more deterministic.” These details show that deterministic output is a design concern, but source inspection alone does not establish byte-for-byte determinism across parallel and sequential runs. That remains an execution question.

Basis: **source**; the final limitation is **derived**.

### Borrow-check mode reuses the symbolic interpreter without code synthesis

`BorrowCheck.borrow_check_crate` computes the same style of translation context and visits structured function bodies. For each one it calls `evaluate_function_symbolic` with `synthesize = false`. It returns no translated crate and writes no proof-assistant program.

Normal translation instead calls the same symbolic interpreter with `synthesize = true` and consumes the synthesized symbolic AST. Aeneas's standalone borrow checker and functional translator are therefore two modes over a shared symbolic-execution engine, not unrelated validation and compilation implementations.

This also means that “Aeneas accepted it in `-borrow-check` mode” and “Aeneas generated a backend model for it” are distinct observations. Translation adds pure-AST conversion, micro-passes, extraction, and backend constraints that borrow-check mode does not exercise.

Basis: **source**.

### Backend extraction is a separate final stage over the translated crate

`translate_crate` first calls `translate_crate_to_pure`; only after that succeeds as far as recoverable errors permit does it call `extract_translated_crate`. Extraction constructs target-language names and files from the pure declarations and dispatches through backend-specific printers.

With `-split-files`, extraction separates types, functions, and opaque/external declarations. For Lean, external function templates are generated as `FunsExternal_Template.lean`, while generated code imports a user-maintained `FunsExternal.lean`. Type-side external templates use the analogous scheme. The normal generated function module contains translated functions, trait implementations, and globals. Optional Lean-specific output can also include a library entry point and Lake project scaffolding.

This is another boundary a consumer must model explicitly: an unresolved opaque definition can require a hand-written or standard-library model even when the LLBC and pure translation stages otherwise succeeded.

Basis: **source** + upstream **documentation**.

### The pipeline's error model supports recovery without making partial output authoritative

Three source facts combine into the important operational rule:

1. `fail_hard` defaults to false, so many errors raise recoverable `CFailure` rather than immediately terminating the process;
2. several pipeline stages catch those failures and continue with missing declarations or error bodies; and
3. the top-level command tests the accumulated error list and exits 1 if any registered error remains.

Aeneas is therefore intentionally capable of producing useful partial artifacts while reporting an unsuccessful translation. For Anneal, the safe integration rule is to treat the Aeneas run result and explicit declaration/coverage accounting as part of the verification boundary. A generated Lean file by itself is not evidence of complete or successful translation.

Basis: **source** + **derived** integration consequence.

## Boundaries

- No fresh Charon, Aeneas, Lean, F*, Coq, or HOL4 execution was performed. This report does not establish runtime behavior not fixed by the inspected source.
- This report reconstructs pipeline architecture. It does not prove that Aeneas's symbolic execution or functionalization is semantically correct with respect to Rust or LLBC. Published formal results require a separate theorem-to-implementation applicability analysis.
- The detailed semantics of references, backward functions, scalar/result modeling, traits, and raw pointers are covered in `aeneas-rust-to-lean-translation-nightly-2026-06-03`; this report does not duplicate that inventory.
- External and standard-library model lookup is covered in `aeneas-external-models-nightly-2026-06-03`.
- The resource/ownership information preserved or erased by the functional model is covered in `aeneas-resource-semantics-nightly-2026-06-03`.
- The WP/specification and proof-tactic layer is covered in `aeneas-wp-proof-tools-nightly-2026-06-03`.
- Charon/Aeneas revision coupling and LLBC compatibility are covered in `aeneas-charon-compatibility-nightly-2026-06-03`; this report assumes the pinned LLBC producer rather than re-establishing compatibility.
- Source inspection shows explicit parallel execution and some determinism-oriented precautions, but it does not establish byte-identical output between parallel runs, sequential runs, hosts, or filesystems.
- The report does not inventory every micro-pass precondition or prove that individual micro-passes preserve semantics.
- `drop_as_no_op` is true by default at this revision and `-eval-drops` changes that setting. This report records the architecture and configuration point but does not establish the semantic adequacy of either drop treatment.
- Aeneas's README says the current functional model targets a subset of safe Rust and that unsafe/concurrent support is under development. This report does not reinterpret that statement as a complete supported-Rust matrix.
- The generated backend project/file layout is described only far enough to locate the extraction boundary. Exact Lean package anatomy and generated-source stability remain separate research subjects.

## Evidence

**Source — Aeneas primary revision.** `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`.

- `src/Main.ml`, blob `b3f373f8c449eeae0f9a50bb0ce2d2963903eddc`: CLI modes and backend flags; LLBC loading; `--preset=aeneas` enforcement; pre-pass invocation; translation versus borrow-check dispatch; final accumulated-error exit status.
- `src/PrePasses.ml`, blob `dc0ab803c26dafb14caf0da1bcc73e3499716835`: `apply_passes`, the fixed LLBC pre-pass sequence, per-function failure recovery to `ErrorBody`, and crate-wide post-passes.
- `src/Translate.ml`, blob `8376e580b542bf3ee28cc9e3d4c170a17b23d379`: `translate_function_to_symbolics`, `translate_function_to_pure`, `translate_crate_to_pure`, per-declaration recovery, parallel body translation, pure micro-pass invocation, and `translate_crate`'s translation-then-extraction structure.
- `src/TranslateCore.ml`, blob `55e2abe89a5a519013347635bfb96669e2d73d38`: translation-context utilities and LLBC-derived name/model lookup used by later stages.
- `src/BorrowCheck.ml`, blob `eaa294db179d74efd99f01ed2e69a5e54c6b6a30`: borrow-check mode's direct use of `evaluate_function_symbolic` with synthesis disabled.
- `src/Config.ml`, blob `99a9eba5ae67dde20dbfd8d835cdc2900fc60355`: backend/configuration state, defaults for parallelism, error recovery, pure-code checks, drop treatment, and backend-sensitive translation options.
- `src/Errors.ml`, blob `c135674b8601786616c6c20ad81ec388bb8cbfea`: accumulated error state, recoverable `CFailure`, `fail_hard`, and warning/error behavior.
- `src/pure/PureMicroPasses.ml`, blob `e0662ab3153f3c401b44cbe6c0cad4e17157f063`: ordered pure-IR pass pipeline, configuration-gated passes, loop decomposition, parallel post-processing, final annotations, and reducibility computation.
- `src/symbolic/SymbolicToPure.ml`, blob `95ba91f539e48009efa420dfa956c4c55581cb3a`: symbolic-AST to pure-AST translation implementation used by `Translate.ml`.
- `src/symbolic/SymbolicToPureTypes.ml`, blob `d35b6d67a65af220fdb56614ab1b51edc029b06f`: pure signature decomposition and forward/backward type translation used before body translation.
- `src/pure/Pure.ml`, blob `acde8579d6861a08efae086c72f3156283110342`: the pure intermediate representation consumed by micro-passes and extraction.
- `src/extract/Extract.ml`, blob `52754e4fdb25b50fce63abe2d2184751d69632e8`: generic backend extraction primitives used after pure translation.
- `src/extract/ExtractTypes.ml`, blob `371717638f4298cc9c488b31a597608f9bf5089c`: backend type/declaration rendering used by extraction.
- `src/llbc/LlbcOfJson.ml`, blob `4007be2f7e77c20babd765802e6742307d6128a3`: serialized LLBC input parser.

**Documentation — same Aeneas revision.** `README.md`, blob `f331650bd4291d27ba6cee736ce51cf31da9cac1`, documents the Charon → LLBC → Aeneas workflow, supported output backends, the `--preset=aeneas` producer command, split-file external-model workflow, and the stated safe-Rust/unsafe/concurrency boundary. `documentation/aeneas-overview.md`, blob `439076012c1ba93c7ec1bf25aca42e0f1ec14756`, provides proof-engineer-oriented conceptual guidance; implementation source controls where its simplifications differ from exact generated shape.

**Related corpus evidence.** The reports `aeneas-rust-to-lean-translation-nightly-2026-06-03`, `aeneas-external-models-nightly-2026-06-03`, `aeneas-resource-semantics-nightly-2026-06-03`, `aeneas-wp-proof-tools-nightly-2026-06-03`, and `aeneas-charon-compatibility-nightly-2026-06-03` provide the detailed semantic and compatibility evidence intentionally not repeated here.

No evidence acquired for this report is fresh **execution**.

## Revalidation

For a future Aeneas revision, the cheapest architecture check is a source-directed pipeline diff before running broad examples:

1. Resolve the exact Aeneas revision and its paired Charon revision/toolchain.
2. Inspect `src/Main.ml` from LLBC load through `PrePasses.apply_passes` and the translation/borrow-check dispatch. Check whether the Aeneas-preset guard and final accumulated-error exit rule still exist.
3. Diff `PrePasses.apply_passes` to identify any new, removed, or reordered LLBC transformations and any change to failure recovery.
4. Diff `Translate.translate_function_to_symbolics`, `translate_crate_to_pure`, and `translate_crate` to check the symbolic-execution boundary, declaration staging, recoverable failure behavior, and pure-to-extraction handoff.
5. Diff `PureMicroPasses.passes` and `apply_passes_to_pure_fun_translations`, together with backend option setup in `Main.ml`/`Config.ml`, to determine whether the supposedly shared pure pipeline became more or less backend-dependent.
6. Diff `BorrowCheck.borrow_check_crate` to verify whether borrow-check mode still reuses the symbolic interpreter without synthesis.
7. Diff the extraction entry path and split-file handling to recover any changed backend/project boundary.

On a capable execution surface, add one narrow end-to-end probe with three variants: a clean supported function, a function that triggers one recoverable translation error while another function remains translatable, and the clean input under `-borrow-check`. Preserve the exact `.llbc`, command lines, exit codes, stdout/stderr, and emitted files. Run the translation once in default parallel mode and once with `-sequential`. This probe cheaply checks the two most integration-sensitive claims: partial artifacts do not turn an erroring run into success, and borrow-check mode remains distinct from target-code generation. Comparing the two successful translation trees can also test determinism, but a matching specimen establishes only that fixture/configuration, not general deterministic output.