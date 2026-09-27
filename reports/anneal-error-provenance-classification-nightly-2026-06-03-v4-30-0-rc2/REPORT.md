# Distinguishing user errors from unsupported translation and tool failures

## Summary

At the exact toolchain revisions selected by current Anneal, there is no single exit code, severity field, or diagnostic string that reliably answers the cross-layer question “is this the user's error, an unsupported translation, or a tool failure?” The useful evidence is layer-specific.

The strongest discriminator in the inspected pipeline is Charon's own process-level enum. At `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, the driver maps `RustcError` to exit 2, `CharonError` and serialization failure to exit 1, and caught Charon panics to 101. This separates a rustc-side failure from a Charon-side panic, but it is not a complete provenance taxonomy. `RustcError` covers fatal rustc failures generally, not only invalid user Rust. Exit 1 conflates registered Charon translation failures with output serialization failure. Charon also continues after registered translation errors by default and may serialize a partial artifact while exiting successfully unless strict error policy is enabled.

Rustc JSON gives one stronger internal signal: `Bug` and `DelayedBug` serialize with level `error: internal compiler error`, whereas ordinary source errors serialize as `error`. Even there, rustc's `Fatal` category also serializes as `error`, and the source documents `Fatal` as including configuration errors, internal overflows, and some file-operation failures. An `error` diagnostic is therefore not automatically a user-program error.

Aeneas has less machine-readable separation. At `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, command-line/configuration failures, unsupported translation cases, and registered internal failures can all lead to exit 1. Its error machinery does preserve useful semantic clues: source spans; implementation emitter file/line when `-print-error-emitters` is enabled; and explicit internal-error text from `sanity_check` / `internal_error` (“Internal error, please file an issue”). But these are diagnostic facts, not a stable typed public protocol. Aeneas can also emit placeholder `sorry`/`admit` text while registering an error and ultimately exiting 1, so the existence of generated Lean is not evidence of successful translation.

Lean's batch frontend has the same broad limitation. `lean --json` provides structured position, severity, message kind, and rendered data, but `MessageSeverity` is only information/warning/error. The shell exits 1 when frontend elaboration returns no environment, and it also uses exit 1 for command-line/input/setup failures. Neither the exit code nor the generic severity distinguishes a proof/program error from every tool/configuration failure. Message kinds can refine specific diagnostics when known, but there is no generic “user versus tool” bit in the inspected protocol.

For Anneal, the robust model is therefore **provenance plus failure class**, not a binary user/tool label inferred from status alone. Preserve which stage produced the failure; use that stage's strongest structured discriminator; record whether the failure had an original-user-source span, generated-source span, or no source span; distinguish explicit internal/panic/serialization/infrastructure signals from unsupported-translation signals; and leave ambiguous cases explicitly ambiguous. A future public Anneal diagnostic API should assign its own stable classification after consuming these facts rather than exposing upstream exit codes as if they formed one coherent taxonomy.

No fresh tool execution was performed for this report. The conclusions are pinned source semantics plus current reference-corpus synthesis.

## Applicability

The pipeline facts are pinned to:

- `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, the rustc nightly used by the selected Charon toolchain;
- `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, Charon 0.1.210;
- `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, Aeneas `nightly-2026.06.03`;
- `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, Lean `v4.30.0-rc2`;
- current Anneal authority `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`.

“User error” in this report means a failure whose primary cause is an invalid or unproved user input under the intended supported semantics: for example, Rust that does not type-check or a Lean proof obligation that does not elaborate. “Unsupported translation” means the input may be valid at its source layer, but the selected Charon/Aeneas pipeline does not model or translate the construct. “Tool failure” means a compiler/translator panic, internal invariant failure, serialization/infrastructure failure, or analogous failure of the tool itself. “Configuration/invocation failure” is kept separate because upstream tools often report it through the same channels as one or both of the preceding categories.

The report does not prescribe Anneal's final UX labels. It identifies which distinctions the selected upstream revisions can and cannot support.

The current Anneal V2 binary on `main` does not yet implement the Rust→Charon→Aeneas→Lean verification pipeline. Its current command is `setup`, and its archive-reuse test invokes Lean directly. Historical V1 had diagnostic mapping and stricter Charon invocation; those files are used only as historical evidence about previously explored integration choices, not as current V2 behavior.

## Findings

### Exit status is a stage-local fact, not a universal classification

The first rule is negative but operationally important: do not translate a generic nonzero process status directly into `UserError`.

At different layers, status 1 means different things. Aeneas uses it for invalid CLI combinations, bad or missing LLBC input, registered translation errors, and other failures. Lean uses 1 both for ordinary frontend failure and for shell/input problems. Charon uses 1 for both `CharonError` and serialization failure. Only Charon's 101 panic status has a narrow tool-crash meaning at the inspected revision.

A stable Anneal record should therefore first identify the producer:

```text
stage = rustc | charon | aeneas | lean | anneal
```

and only then interpret status, structured diagnostics, stderr, and preserved artifacts according to that stage.

Basis: **source** across the pinned Charon, Aeneas, and Lean entry points.

### Charon exposes four process-level failure variants, but two share exit code 1

`charon/src/bin/charon-driver/main.rs` defines:

- `CharonError(usize)`;
- `RustcError`;
- `Panic`;
- `Serialize`.

Its display strings and exit mapping are explicit:

- `RustcError` → “Code failed to compile” → exit 2;
- `CharonError(_)` → “Charon failed to translate this code” → exit 1;
- `Serialize` → “Could not serialize output file” → exit 1;
- caught panic → “Compilation panicked” → exit 101.

This is useful evidence. Exit 2 localizes the failure to the rustc-driver side rather than an ordinary completed Charon translation. Exit 101 is strong evidence of a Charon/rustc-integration crash. But exit 1 alone cannot tell unsupported translation from serialization/infrastructure failure; the variant-specific diagnostic text or a more structured wrapper is required.

Basis: **source** in pinned `charon/src/bin/charon-driver/main.rs`.

### Charon's `RustcError` is broader than “bad user Rust”

`run_compiler_with_callbacks` maps a caught rustc fatal error to `CharonFailure::RustcError`. The Charon driver also uses `RustcError` when the translation callback never produced a translation context.

The paired rustc source makes the ambiguity concrete. `rustc_errors::Level` distinguishes:

- `Error`: an error in code being compiled;
- `Bug`: an internal compiler error;
- `Fatal`: an immediate-abort error used for configuration errors, internal overflows, and some file-operation errors;
- `DelayedBug`: an internal bug that may become an ICE if no other errors appear.

JSON serialization preserves a useful but incomplete distinction: `Bug` and `DelayedBug` become level `error: internal compiler error`; `Fatal` and ordinary `Error` both become level `error`.

Thus a Charon exit 2 plus rustc JSON can identify an explicit rustc ICE reliably when that diagnostic is present. It cannot conclude that every remaining `error` is caused by the user's Rust source. Some fatal configuration or I/O failures use the same level.

Basis: **source** in Charon's driver and pinned `compiler/rustc_errors/src/lib.rs` / `json.rs`.

### Charon-native translation failures are not equivalent to invalid Rust

Charon has many source paths that register or raise errors for inputs rustc can accept. Examples at the selected revision include messages such as “Unsupported alias type,” “Unsupported type: infer type,” unsupported clauses, unsupported constants, and unsupported transformation combinations.

Those failures describe the translator's current domain, not a Rust language rejection. If Anneal reports them as ordinary user compiler errors, it hides an important distinction: the user's program may be legal Rust while the verification translator lacks support.

The safest default classification for a Charon translation diagnostic is therefore `unsupported-or-translation-failure` unless the specific error has a stronger known category. Source correspondence can still point at the responsible Rust construct without blaming the source language.

Basis: **source** in pinned Charon translation modules plus the existing `charon-support-and-unsoundness-nightly-2026-06-03` corpus report.

### Charon can succeed as a process while carrying translation errors unless policy is tightened

The selected Charon revision treats registered extraction errors as recoverable by default. The main path records an `error_count`, serializes the resulting crate, and returns `Ok(error_count)` unless `error_on_warnings` is enabled. The process then prints that extraction generated warnings but exits successfully.

The current corpus already records the more important artifact consequence: the serialized `CrateData` can carry a `has_errors` marker and error nodes/partial bodies. The paired OCaml reader used by Aeneas does not by itself turn that marker into a stable cross-process classification.

This makes process success insufficient evidence that the translation was complete. A fail-closed Anneal invocation should use a strict Charon policy, preserve diagnostics, and reject partial/error-marked artifacts rather than infer support from exit zero.

Historical Anneal V1 passed `--abort-on-error`; that is useful precedent but not current V2 authority.

Basis: **source** + existing `charon-support-and-unsoundness-nightly-2026-06-03`; historical V1 source as non-current evidence.

### Aeneas records translation errors, but its public process result is intentionally coarse

`src/Errors.ml` stores registered errors in a global `error_list`. `craise` records an error and throws `CFailure`; translation code catches that recoverable exception around declarations so work can continue. At the end of `src/Main.ml`, any nonempty `error_list` makes the process exit 1.

This yields an important fail-closed property when the caller checks final status: registered Aeneas translation errors do not silently produce process success.

It does not yield a provenance taxonomy. The same exit status 1 is also used by CLI argument validation, missing or malformed LLBC, incompatible backend options, and other failures. Aeneas does not expose a typed JSON envelope saying `user`, `unsupported`, `internal`, or `infrastructure`.

Basis: **source** in pinned `src/Errors.ml` and `src/Main.ml`.

### Aeneas source spans tell you responsibility location, not failure ownership

Aeneas error records carry an optional Charon span. `format_error_message` renders it as a source location, including generated-from macro information where present. That is valuable for mapping a translation failure back to the responsible Rust construct.

But a source span is not proof that the source is invalid. An unsupported translator case can be precisely source-located. Conversely, an infrastructure/configuration error may have no source span.

The right use of the span is therefore a separate field such as:

```text
responsible_source = rust span | generated span | tool/config | unknown
```

rather than using “has user span” as the user/tool classifier.

Basis: **source** in pinned Aeneas `Errors.ml`; derived classification consequence.

### Aeneas has an explicit internal-error convention, but not a stable typed category

The pinned Aeneas error helpers include `sanity_check`, `internal_error`, and related variants. They emit the literal message “Internal error, please file an issue.” Optional `-print-error-emitters` adds the Aeneas implementation source file and line that emitted each error.

Those are strong debugging signals for a tool defect or violated Aeneas invariant. They are still text conventions and debug metadata, not a versioned machine-readable failure code. An Anneal wrapper may safely recognize the exact pinned convention as supporting evidence, but should preserve the original diagnostic and version rather than promote the string into an eternal protocol contract.

Basis: **source** in pinned `src/Errors.ml` and CLI handling in `src/Main.ml`.

### Aeneas can emit placeholders while still failing

`src/extract/ExtractErrors.ml` deliberately supports error recovery during extraction. `admit_raise` / `admit_string` first register an error and then emit an admission placeholder: `sorry` for Lean and `admit` for several other backends.

This is valuable for debugging or continued generation. It also creates a strict rule for automation: generated Lean file existence, or even syntactically plausible generated Lean, is not evidence that translation succeeded. The Aeneas process result and registered diagnostics remain authoritative; downstream Lean success cannot retrospectively erase an upstream registered translation failure.

Basis: **source** in pinned `src/extract/ExtractErrors.ml`.

### Aeneas warnings form a separate policy boundary

The selected Aeneas default does not treat warnings as errors. Some known semantic hazards are warning-level, including cases already documented in the current support/failure corpus. The repository's failure fixtures selectively enable `-warnings-as-errors` where they require fail-closed behavior.

A pipeline that needs a binary support decision must define which Aeneas warnings are fatal. “Process exited zero” under default warning policy can otherwise mean “translation completed with a warning about a promise-relevant limitation.”

This is not the same problem as classifying a nonzero result. It is a reminder that unsupported-or-risky behavior can arrive on a nominal success channel.

Basis: existing `aeneas-rust-support-failure-matrix-nightly-2026-06-03` plus pinned `Errors.ml` / `Main.ml`.

### Lean JSON is structured, but its severity is not a failure-origin category

At `v4.30.0-rc2`, Lean's `MessageSeverity` contains only `information`, `warning`, and `error`. `SerialMessage` preserves file name, positions, severity, message kind, and eagerly rendered message data. `lean --json` serializes these messages.

This gives Anneal excellent evidence about **where** a Lean failure occurred and **how Lean classified its severity**. It does not by itself tell why the error exists:

- a user-authored proof can fail;
- generated Lean can be ill-typed because Aeneas/Anneal emitted bad code;
- an import/environment/configuration problem can surface as an error;
- a specific named error kind may carry more meaning, but there is no universal provenance kind.

The classifier therefore has to combine message location/source correspondence with stage provenance and known message kinds. For example, an error mapped to user-authored inline Lean has different likely ownership from an error in generated scaffolding with no user-authored span, even if both have severity `error`.

Basis: **source** in pinned Lean `Message.lean` and `Language/Basic.lean`; current source-correspondence corpus for mapping categories.

### Lean exit 1 also conflates frontend and invocation/input failure

The Lean shell exits 1 when `Elab.runFrontend` returns no environment. It also returns or throws status 1 for conditions such as an unknown language header, missing/invalid arguments, option processing errors, and output-file creation failures.

Therefore `lean exited 1` is only a failure fact. It is not a proof failure label. Batch JSON diagnostics should be consumed when present; raw stderr and invocation context must also be preserved because some shell/setup failures occur outside the normal message stream.

Basis: **source** in pinned `src/Lean/Shell.lean`.

### Current Anneal V2 does not yet define a production failure taxonomy

At current `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, V2's public command surface is still `setup`. The archive integration test invokes `lake ... lean --json` and treats nonzero status as a generic test error containing stdout/stderr. There is not yet a production Rust→Charon→Aeneas→Lean diagnostic classifier on current V2 `main`.

Historical V1 implemented source mapping and re-rendering across Cargo/Charon/Lean, including an `[External Error]` fallback. It is useful design evidence, especially that source correspondence and external-stage provenance need to be carried together. It is not current architecture authority.

This means the classification model below is a reference fact set for future Anneal work, not a description of an already-implemented V2 public API.

Basis: **source** in current `anneal/src/main.rs`; historical V1 source clearly marked non-current.

### A useful Anneal classifier needs at least two axes

A robust stable model can be derived from the available upstream evidence without pretending the tools share a common taxonomy.

The first axis is **originating stage**:

- `rustc`
- `charon`
- `aeneas`
- `lean`
- `anneal/infrastructure`

The second axis is **failure class**, where classifications are evidence-backed and may remain ambiguous:

- `source-error`: source language/proof rejected under supported semantics;
- `unsupported-translation`: valid source shape rejected or only partially represented by the translator;
- `tool-internal`: panic, ICE, explicit internal invariant failure;
- `configuration`: invalid flags, incompatible modes, malformed/mismatched intermediate input;
- `infrastructure`: serialization, file I/O, process launch, archive/toolchain availability;
- `warning-policy`: promise-relevant warning promoted or requiring policy;
- `unknown`: evidence is insufficient to choose safely.

Each record should separately preserve source responsibility:

- original Rust;
- macro/generated Rust;
- generated Lean from Aeneas;
- generated Anneal scaffolding;
- user-authored Lean;
- external dependency/toolchain;
- none/unknown.

This three-part record—stage, failure class, source responsibility—is more stable than a single “user error” boolean. It also composes with the existing source-correspondence reports.

Basis: **derived** from the pinned source channels above and the current source-correspondence corpus.

### Classification should be monotonic: strong evidence narrows, weak evidence does not guess

The source evidence supports a conservative rule set:

| Observation | Safe conclusion | Unsafe shortcut |
| --- | --- | --- |
| rustc JSON level `error: internal compiler error` | rustc internal/ICE-class diagnostic | ordinary user source error |
| Charon exit 101 | Charon-side panic/crash | unsupported construct |
| Charon exit 2 | rustc-driver-side failure | necessarily bad user Rust |
| Charon exit 1 | Charon-side failure; inspect message/variant evidence | necessarily unsupported translation |
| Charon exit 0 with registered warnings/partial marker | process completed under non-strict policy | complete supported translation |
| Aeneas exit 1 | Aeneas invocation/translation failed | necessarily user error or necessarily tool bug |
| Aeneas “Internal error, please file an issue” | explicit internal-invariant signal at this pin | stable cross-version error code |
| Aeneas generated `sorry` plus nonzero status | extraction recovered with an admission after an error | proof-ready successful translation |
| Lean JSON severity `error` | Lean reported an error | user-authored proof is necessarily at fault |
| Lean exit 1 with no JSON diagnostic | Lean shell/frontend/infrastructure failure; preserve stderr/context | proof failure |

Anneal can add more specific classifiers for known pinned diagnostics. The default should move toward `unknown`, not toward blaming the user, when upstream evidence is ambiguous.

Basis: **derived** synthesis.

## Boundaries

**No fresh execution.** No rustc, Charon, Aeneas, Lean, or Anneal process was run. This report maps source-defined channels and relies on current reference reports for already-established support/failure semantics.

**No exhaustive diagnostic-string inventory.** Charon and Aeneas have many individual unsupported/error sites. This report describes the classification mechanisms, not every message.

**No claim that exit code 2 from Charon is a user-error code.** It means the rustc-driver side failed. Rustc itself has source, fatal configuration/I/O, and internal failure classes.

**No stable Aeneas machine taxonomy exists at this pin.** Recognizing “Internal error, please file an issue” or source-emitter metadata is useful pinned evidence, not a promised external schema.

**Lean message kinds are not globally classified here.** Some named kinds can support finer mappings, but there is no inspected universal partition into user versus tool errors.

**Warnings require policy.** Charon and Aeneas can expose important limitations without a nonzero default status. The final Anneal acceptance policy remains an architecture decision.

**Current V2 is incomplete.** Historical V1 behavior is not treated as current V2 semantics.

**Source location and blame are separate.** A tool limitation can point precisely to user source; a user proof failure can occur in a generated file; source correspondence must not be collapsed into failure ownership.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-27.

### rustc

Subject: `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`.

- `compiler/rustc_errors/src/lib.rs`, blob `55f10867c932167cdb1a5142f7ca3855deb9bf72`: `Level` semantic categories; `Bug`/`DelayedBug` versus `Fatal`/`Error`; serialized level strings.
- `compiler/rustc_errors/src/json.rs`, blob `04ac140f332618d6fa81254e9a16bc27c729eef5`: JSON diagnostic fields, including the explicit `error: internal compiler error` level.

### Charon

Subject: `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`.

- `charon/src/bin/charon-driver/main.rs`, blob `ab74f3f3d12a869bd8c3c94083b93b7dee1c2482`: `CharonFailure` variants, display messages, final process exit mapping, error-count policy.
- `charon/src/bin/charon-driver/driver.rs`, blob `3f90a7a31857aed462694066e5ffaa6e28b9dcfa`: rustc failure mapping, callback completion, strictness configuration.
- `charon/src/errors.rs`, blob `e4107c6deb5741d523d2220820d1ee0355adb3c0`: registered translation diagnostics and source spans.
- `charon/src/options.rs`, blob `f08f8bae08d7fb5f38773c0be038d925fe80cb4c`: `--abort-on-error` and `--error-on-warnings` controls.

Current reference report `charon-support-and-unsoundness-nightly-2026-06-03` supplies the already-established partial-artifact and `has_errors` behavior used here as corpus evidence.

### Aeneas

Subject: `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`.

- `src/Errors.ml`, blob `c135674b8601786616c6c20ad81ec388bb8cbfea`: registered errors, source spans, `CFailure`, explicit internal-error convention, warning/error policy, optional implementation emitter locations.
- `src/Main.ml`, blob `b3f373f8c449eeae0f9a50bb0ce2d2963903eddc`: CLI failure paths, LLBC compatibility validation, final `error_list` → exit 1, strictness switches.
- `src/extract/ExtractErrors.ml`, blob `9169ab076be376ee6150ef7f04b298b92a840965`: placeholder `sorry`/`admit` generation after registering extraction errors.

Current reference report `aeneas-rust-support-failure-matrix-nightly-2026-06-03` supplies the already-established support-versus-warning policy boundary.

### Lean

Subject: `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`.

- `src/Lean/Message.lean`, blob `a7f76198c582d1d2032bb24d13ad4cb7a272fa57`: message severity, kind, serialization.
- `src/Lean/Shell.lean`, blob `2ff5c4b0c82f876ddd4384c9c20dcaefebc1b90e`: batch/frontend exit logic and shell/invocation failures.
- Current reference reports `lean-json-cli-protocol-v4-30-0-rc2` and `lean-diagnostic-objects-severity-v4-30-0-rc2` establish the structured batch protocol and severity semantics.

### Anneal

Subject: `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`.

- `anneal/src/main.rs`, blob `b947700606677ea89c7a205f3ffcc75493508f63`: current V2 command surface and archive-test treatment of Lean process failures.
- `anneal/v1/src/diagnostics.rs`, blob `cd27b771e2f22bdb104c5335a70cfde3207e8fdb`: historical source-mapping/diagnostic integration only; not current V2 authority.

Evidence roles are **source**, current reference-corpus synthesis, and **derived** classification guidance. There is no fresh **execution** evidence.

## Revalidation

For another toolchain revision, revalidate the classification channels before carrying the mapping forward.

For rustc:

1. inspect `rustc_errors::Level` semantics and `to_str`;
2. confirm whether JSON still carries a distinct ICE level;
3. identify any new structured diagnostic category that separates fatal configuration/I/O from source errors.

For Charon:

1. inspect the `CharonFailure` enum and exact process exit mapping;
2. inspect whether rustc failures remain separately represented;
3. inspect registered-error recovery and whether partial artifacts can still accompany process success;
4. check strictness options and whether serialized `has_errors` is exposed to the consuming API.

For Aeneas:

1. inspect `Errors.ml` for typed exceptions/records and explicit internal-error markers;
2. inspect `Main.ml` for exit-code mapping and whether CLI/configuration and translation failures have gained distinct statuses;
3. inspect extraction recovery for placeholder admissions;
4. determine whether a structured machine-readable diagnostic protocol has replaced or supplemented textual logs.

For Lean:

1. inspect `MessageSeverity`, message-kind serialization, and batch JSON schema;
2. inspect shell/frontend exit rules separately from diagnostics;
3. inventory any machine-readable panic/internal-error signal rather than inferring it from generic `error`.

Then run a small exact-pin specimen suite and preserve raw bytes plus structured records:

- invalid Rust that rustc rejects normally;
- a forced/known rustc ICE fixture if upstream provides a safe test mechanism;
- valid Rust using a known unsupported Charon construct;
- Charon serialization/output-path failure;
- a Charon panic test only if a checked-in safe upstream fixture exists;
- valid LLBC triggering a known Aeneas unsupported translation;
- an Aeneas explicit internal/sanity-check fixture if upstream has a safe checked-in one;
- Lean syntax/type error in user-authored proof text;
- Lean error in generated scaffolding;
- Lean invocation/input failure with no normal frontend diagnostic.

For each specimen, record stage, process status, structured diagnostic fields, stderr/stdout, source-correspondence category, partial/generated artifacts, and the resulting Anneal classification. The purpose is not to snapshot wording; it is to verify that the classifier is based on stable structural evidence and fails closed to `unknown` when that evidence is absent.
