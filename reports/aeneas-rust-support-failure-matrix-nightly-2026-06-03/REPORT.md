# Aeneas Rust support and failure matrix at nightly-2026.06.03

## Summary

At `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, the release selected by Anneal as `nightly-2026.06.03`, "supported Rust" is not a single yes/no property. The useful boundary has three layers:

1. Charon must first translate the program with `--preset=aeneas`.
2. Aeneas must symbolically interpret and functionalize the resulting LLBC.
3. The selected backend must accept the extracted target program and any required external models.

Aeneas's own README describes the functional translator as covering a subset of **safe Rust**. It lists unsafe code and concurrency outside that model and gives one explicit safe-Rust control-flow limitation: returning from a nested loop or breaking/continuing to an outer loop is not supported.

The repository also contains a substantial executable fixture suite. The exact pinned test runner invokes Charon with `--preset=aeneas`, invokes Aeneas with `-abort-on-error`, `-checks`, `-sequential`, and backend-specific options, expects ordinary tests to succeed, and expects `known-failure` tests to fail. `tests/README.md` states that CI regenerates backend outputs, type-checks them with the target verifier, replays handwritten proofs, and checks that generated files are committed. The pinned tree contains checked-in Lean outputs for representative scalars, ADTs, arrays and slices, references and nested borrows, loops, traits, closures, dynamic-trait examples, constants, statics, drops, iterators, and other cases.

Those fixtures are strong preserved evidence about the tested subset, but they are not a language-completeness theorem. This report did not rerun Charon, Aeneas, or Lean. A checked-in successful example establishes a supported shape at the pinned source revision; it does not establish that every legal Rust program using the same surface feature is supported.

The failure boundary is similarly structured. Some cases are explicit hard errors, such as raw-pointer dereference and function-pointer calls. Some are source assertions or `Unimplemented` paths. Some are semantic abstractions rather than failures: references and lifetime parameters disappear from the pure target after guiding borrow translation, `Box<T>` becomes `T`, union/opaque declarations can become opaque, and drops are treated as no-ops by default unless `-eval-drops` is requested. One especially important case is warning-level rather than error-level: if an associated type survives Charon's lifting in mutually recursive traits or GAT-like situations, Aeneas warns that it cannot handle the type and that generated code will likely be incorrect. The dedicated regression fixture turns warnings into errors; the default Aeneas configuration does not.

Aeneas does not normally fail open on registered translation **errors**. It records `CFailure`s, can omit declarations that failed translation while continuing analysis, and exits with status 1 at the end when the error list is nonempty. `-abort-on-error` makes the first registered error fatal, and the repository test runner uses that mode. Warnings are separate: `warnings_as_errors` defaults to false, so a warning-level semantic hazard must be promoted or independently excluded when a consumer requires fail-closed verification.

For Anneal, the operational lesson is to treat the accepted input domain as a pinned, evidence-backed contract rather than "Rust that Charon accepts." A verification pipeline needs to pin both Charon and Aeneas, preserve Aeneas's exit status and diagnostics, decide whether warning-level hazards are fatal, and justify every semantic abstraction that matters to the Rust-level theorem.

## Applicability

Primary subject:

- repository: `AeneasVerif/aeneas`
- revision: `ac9f1bc5262a5e4ff1e24ca78617121382202727`
- release: `nightly-2026.06.03`
- relationship: selected by current Anneal at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`.

Paired input producer:

- repository: `AeneasVerif/charon`
- revision: `a535e914f74db4fd9e6be7048f4233270d8945c0`
- Charon version: `0.1.210`
- relationship: the exact Charon revision pinned by the Aeneas release.

This report characterizes the ordinary Aeneas functional translation, with the Lean backend used as the main preserved-fixture witness because Lean is Anneal's target backend. It does not characterize the ongoing separation-logic work advertised for unsafe and concurrent Rust.

"Fixture-backed" below means that the pinned Aeneas repository contains the Rust input and a corresponding checked-in Lean output under the ordinary test structure, and that the repository's test-runner protocol classifies the case as an ordinary Lean test rather than a Lean `known-failure`. This is preserved repository evidence, not a fresh execution result from this report.

"Unsupported" means the pinned source, pinned documentation, or a pinned known-failure artifact identifies a case as unsupported. It does not imply that every neighboring case is rejected.

"Semantic abstraction" means Aeneas accepts or represents a construct while intentionally discarding or changing information. Whether that abstraction is sound for a particular Anneal theorem is a separate proof obligation.

## Findings

### The support boundary begins after Charon, not at Rust source text

The pinned test runner always invokes Charon first with `--preset=aeneas`. If Charon fails, the runner aborts before Aeneas runs. `tests/README.md` explicitly says that Aeneas `known-failure` tests are for Aeneas failures and that tests causing Charon errors belong in Charon instead.

That division matters when constructing a matrix. An Aeneas fixture is evidence only for Rust shapes that Charon successfully lowered into the paired LLBC representation. Charon-specific exclusions, partial extraction, and semantic transformations remain separate input-boundary facts. The existing `charon-support-and-unsoundness-nightly-2026-06-03` report covers that producer boundary.

Aeneas also checks that imported LLBC records `preset = Some Aeneas`; otherwise `Main.ml` rejects the file and instructs the caller to regenerate it with `--preset=aeneas`.

Basis: **source** + pinned test-suite **documentation**.

### The repository supplies executable, backend-checked positive fixtures

`tests/README.md` defines the normal protocol:

- generate LLBC from each Rust input with Charon;
- run Aeneas for each enabled backend;
- check generated output by parsing/type-checking it with the target verifier;
- replay handwritten proofs that depend on generated output;
- have CI check that generated files are committed.

`tests/test_runner/run_test.ml` makes ordinary Aeneas success a hard requirement. Normal cases call `run_command_expecting_success`; the runner passes `-abort-on-error`, `-checks`, `-no-progress-bar`, `-sequential`, and diagnostic options. A `known-failure` case instead calls `run_command_expecting_failure` and can compare the captured output.

The pinned tree contains checked-in Lean outputs for, among others:

| Rust input | Preserved Lean output | What the fixture demonstrates |
| --- | --- | --- |
| `tests/src/scalars.rs` | `tests/lean/Scalars.lean` | integer scalar operations in the exercised forms |
| `tests/src/adt.rs` | `tests/lean/Adt.lean` | structs, methods, and ordinary ADT lowering |
| `tests/src/arrays.rs` | `tests/lean/Arrays.lean` | arrays and the exercised array operations |
| `tests/src/no_nested_borrows.rs` | `tests/lean/NoNestedBorrows.lean` | shared/mutable reference translation without nested-borrow signatures |
| `tests/src/nested-borrows.rs` | `tests/lean/NestedBorrows.lean` | exercised nested-borrow signatures |
| `tests/src/loops.rs` | `tests/lean/Loops.lean` | ordinary loops and loop-carried state in the exercised forms |
| `tests/src/traits.rs` | `tests/lean/Traits.lean` | ordinary traits, implementations, and methods in the exercised forms |
| `tests/src/closures.rs` | `tests/lean/Closures.lean` | several closure captures/calls |
| `tests/src/dyn.rs` | `tests/lean/Dyn.lean` | a bounded set of dynamic-trait operations |
| `tests/src/constants.rs` | `tests/lean/Constants.lean` | constants and constant expressions in the exercised forms |
| `tests/src/static.rs` | `tests/lean/Static.lean` | a bounded set of static-associated data forms |
| `tests/src/drop.rs` | `tests/lean/Drop.lean` | syntactic acceptance of the exercised drop-containing program, subject to the default drop abstraction below |

Other checked-in Lean fixtures cover slices, iterators, `Vec`, discriminants, default methods, blanket implementations, conversions, joins, recursive data structures, and numerous historical issue regressions.

This is useful positive evidence, but the unit of evidence is the fixture. For example, the presence of `Dyn.lean` does not override source paths that still reject other dynamic-trait shapes.

Basis: pinned test-suite **documentation** + preserved generated artifacts.

### The advertised functional model is a subset of safe Rust

The root README states the intended boundary directly: Aeneas "currently functionalizes a subset of safe Rust." It lists unsafe code and concurrency as limitations expected to be addressed by ongoing separation-logic work.

The same section identifies a remaining safe-Rust loop limitation: control flow that exits an outer loop from a nested loop is unsupported, including return from a nested loop and `break`/`continue` targeted at an outer loop.

This is the highest-level support statement for the pinned functional translator. The fixture suite refines it with concrete accepted and rejected shapes; it does not broaden the stated model to all Rust.

Basis: pinned upstream **documentation**.

### Raw-pointer types can cross signatures, but raw-pointer dereference is a pinned known failure

The ordinary pure type language retains raw-pointer types as marked `TRawPtr` values so signatures can be represented. That does not imply operational raw-pointer support.

`InterpPaths.ml` rejects raw-pointer dereference. The pinned fixture `tests/src/raw_pointers.rs` performs reads and writes through raw pointers and is annotated `//@ [lean] known-failure`. Its checked-in `raw_pointers.lean.out` records:

`Aeneas does not yet support dereferencing raw pointers.`

The test is skipped for non-Lean backends and expected to fail for Lean. This is a direct, preserved rejection boundary for the exact pinned source.

Basis: **source** + pinned known-failure artifact.

### Function-pointer calls and several pointer operations have hard rejection paths

`InterpStatements.ml` rejects `FnOpDynamic` with "Function pointers are not supported yet" in both concrete and symbolic call handling. `SymbolicToPureTypes.ml` also rejects function-pointer/arrow type forms in several translation paths.

Pointer-related source paths include further unsupported cases:

- `SymbolicToPureExpressions.ml` rejects `binop::offset`;
- `InterpExpressions.ml` rejects aggregated raw pointers;
- raw-pointer dereference is rejected as above;
- transmute is rejected by `SymbolicToPureExpressions.ml`.

These are source-level boundaries. They do not establish that every possible Rust syntax involving a function item, closure, cast, or pointer fails; ordinary function items and closures use different representations and have positive fixtures.

Basis: **source**.

### Trait support is substantial but shape-sensitive

The ordinary `traits.rs`, `blanket_impl.rs`, `defaulted_method.rs`, and `dyn.rs` tests have checked-in Lean outputs. That is positive evidence for the specific trait shapes they exercise.

The failure boundary is narrower than "traits unsupported" but important:

- `SymbolicToPureTypes.ml` rejects generic associated type `ItemClause` forms with "Generic Associated Types are not supported yet";
- several trait-reference/type paths reject dynamic-trait forms that do not fit the implemented translation;
- some function/trait-method type forms still hit `Unimplemented`.

The pinned `mutually-recursive-traits.rs` fixture captures an additional hazard. It is a Lean `known-failure` run with `-warnings-as-errors`. `SymbolicToPure.ml` detects an associated type that survived Charon's normal associated-type lifting, explains that this can happen with mutually recursive traits and GATs, and warns that Aeneas cannot handle the type and "the generated code will likely be incorrect." The checked-in `.lean.out` preserves that diagnostic.

Thus ordinary traits are fixture-backed, while GATs and some mutually recursive associated-type structures are outside the trusted translation boundary.

Basis: **source** + preserved positive and known-failure artifacts.

### The mutually-recursive-trait hazard is a warning by default

The trait diagnostic above is emitted with Aeneas's warning mechanism. `Config.ml` initializes `warnings_as_errors = false`.

The dedicated regression fixture explicitly supplies `-warnings-as-errors`, turning the warning into a nonzero result so the test harness can preserve it as a known failure. A caller that uses default warning policy does not get that protection merely from the diagnostic being emitted.

For Anneal this is a distinct class from an unsupported operation that raises `CFailure`: a fail-closed orchestration must decide whether this warning, and any other promise-relevant warning, is fatal.

Basis: **source** + known-failure fixture.

### Registered Aeneas translation errors ultimately produce a failing process

Aeneas has a recoverable error mechanism. `Errors.ml` records errors in `error_list`; when `fail_hard` is false, `craise` raises `CFailure`. Translation code catches those exceptions around functions, globals, signatures, type declarations, and traits so it can continue analyzing other declarations. Failed definitions may therefore be absent from the internal translated maps while the run continues.

This recovery is not equivalent to process success. At the end of `Main.ml`, Aeneas computes `has_errors` from `Errors.error_list` and executes `exit 1` when any registered errors remain.

With `-abort-on-error`, `fail_hard` is set and the first registered error raises a fatal OCaml `Failure` instead of recoverable `CFailure`. The pinned test runner uses `-abort-on-error` for ordinary tests and for Aeneas known failures other than borrow-check-only cases.

Therefore a consumer that faithfully checks Aeneas's final process status does not silently accept registered translation errors. This is stronger than Charon's separate best-effort partial-artifact behavior documented elsewhere.

Basis: **source**.

### Aeneas can still produce partial intermediate/output state before its final nonzero exit

Because translation catches `CFailure` per declaration and filters out failed definitions, later phases can proceed with a subset of translated declarations. Export code explicitly notes that some declarations may have been ignored "in case of errors."

The final process status remains nonzero when those errors were registered, but consumers must not treat the mere presence of generated files as proof of successful translation. The authoritative success observation is a clean Aeneas run under the required diagnostic policy plus successful backend validation.

Using `-abort-on-error` reduces this partial-progress window, but output files from an interrupted or failed run still require ordinary build hygiene.

Basis: **source** + **derived** operational consequence.

### Warnings and errors therefore have different fail-closed properties

The pinned default is:

- `fail_hard = false`;
- `warnings_as_errors = false`.

Registered translation errors cause a final exit status of 1 even when Aeneas recovers internally. Warnings do not. The test runner tightens both behavior classes where needed: it generally passes `-abort-on-error`, and specific warning-hazard fixtures add `-warnings-as-errors`.

An Anneal integration that promises not to fail open should not infer semantic completeness from process success alone until it has also defined which Aeneas warnings are promise-relevant and either made them fatal or proven them irrelevant.

Basis: **source** + **derived** orchestration requirement.

### Lifetimes, ordinary references, and `Box<T>` are accepted through semantic abstraction

The pure functional translation intentionally removes information rather than preserving Rust's source representation literally:

- generic region arguments are ignored after they have served the borrow translation;
- `TRef` translates to the referent's pure type;
- `Box<T>` translates to `T`;
- mutable-reference effects are represented through value flow and backward functions rather than a persistent heap/reference object.

These are core functionalization choices, not failures. The existing `aeneas-resource-semantics-nightly-2026-06-03` and `aeneas-rust-to-lean-translation-nightly-2026-06-03` reports document them in detail.

For a Rust-level theorem, "Aeneas supports references" therefore means that it supports particular reference behavior through an abstraction. It does not mean the resulting Lean program retains reference identity, allocation identity, or lifetime syntax.

Basis: **source** + existing corpus synthesis.

### Bound-region erasure has an explicit complex-binding limitation

`SymbolicToPureTypes.ml` says it "simply ignore[s] the bound regions" and notes that doing so disturbs De Bruijn indices in nested binders; the implementation currently ignores that problem because Aeneas does not handle complex binding situations.

This is not evidence that ordinary lifetime-bearing fixtures are broken. It is evidence that lifetime/region support has structural preconditions beyond ordinary surface syntax.

Generic Associated Types and other complex binder situations should therefore remain outside the default trusted domain unless the exact shape is independently covered.

Basis: **source**.

### Opaque and union type declarations are an abstraction boundary, not full field semantics

In `SymbolicToPureTypes.ml`, ordinary structs and enums become structured pure declarations, but unions, opaque declarations, and type-declaration errors map to `Opaque`.

An opaque target declaration can be a valid interface boundary when the proof does not need its representation. It is not evidence that Aeneas preserved field-level semantics for a Rust union or inaccessible external type.

This distinction is relevant when building a supported-feature matrix: "the crate translates" and "the proof model exposes the source representation" are different claims.

Basis: **source**.

### Drops are accepted by default through a no-op semantics

`Config.ml` initializes `drop_as_no_op = true`. The command-line option `-eval-drops` clears that flag, and `InterpStatements.ml` handles a `Drop` statement by returning `Unit` immediately when the flag is set.

The pinned `drop.rs` input has a checked-in Lean output, so the exercised Rust program is accepted by the default test configuration. That artifact is not evidence that ordinary default translation models Rust destructor side effects. The default semantics deliberately ignores the drop statement.

A theorem sensitive to destructor behavior must either use and validate `-eval-drops` or otherwise justify why drop effects are irrelevant.

Basis: **source** + preserved positive fixture.

### Static references and globals have narrower supported shapes

The pinned source contains special handling for static/shared references, but it rejects mutable `'static` references in relevant interpreter paths and has `Unimplemented` assertions around some global-reference cases. `Main.ml` also documents `-borrow-check-globals` as limited by an LLBC simplification for global initialization functions containing static references.

The checked-in `Static.lean` fixture therefore establishes only its exercised shapes, not arbitrary static/global reference behavior.

Basis: **source** + preserved positive fixture.

### Dynamic traits are implemented in some paths and rejected in others

The existence of `Dyn.lean` shows that some dynamic-trait examples pass the repository's normal Lean generation path. At the same revision, `SymbolicToPureTypes.ml` and `InterpExpressions.ml` contain rejection or assertion paths for other dynamic-trait representations and unsizing/upcast cases.

This is a useful example of why a feature-name checklist is too coarse. The supported unit is the concrete compiler/Charon representation plus Aeneas path, not merely the source keyword `dyn`.

Basis: **source** + preserved positive fixture.

### Panic/failure is represented, but this report does not widen that into full unwind support

The symbolic translator has explicit panic nodes and builds failure-valued pure expressions; arithmetic operations that can fail can produce `EPanic`, and generated pure code uses result/failure structure.

That establishes that ordinary Aeneas translation does not simply erase every panic. It does not establish faithful Rust unwinding, cleanup, or panic-runtime behavior. Charon's Aeneas preset separately performs a fallible-operation reconstruction that can lose unwinding information, as documented in the existing Charon support report.

Panic-sensitive Anneal claims must therefore combine the Aeneas result/failure model with the paired Charon extraction semantics rather than reading either layer in isolation.

Basis: **source** + existing corpus synthesis.

### The matrix is best treated as evidence classes, not a permanent whitelist

At this pin, a practical matrix is:

| Class | Pinned examples | Meaning |
| --- | --- | --- |
| Fixture-backed accepted shapes | scalars, ADTs, arrays/slices, ordinary references and nested borrows, ordinary loops, ordinary traits, closures, selected dyn-trait forms, constants/statics, iterators and collections | The exact fixture has a checked-in Lean output under the normal test protocol; neighboring Rust programs still require evidence |
| Explicit Aeneas rejection | raw-pointer dereference, function-pointer calls, pointer offset, transmute, several unsupported casts/rvalues | Source raises a registered translation error |
| Known warning hazard | associated types surviving lifting in mutually recursive traits/GAT-like situations | Default warning policy can continue; regression fixture promotes warning to error |
| Structural unsupported shapes | GAT item clauses, complex binders, some dynamic-trait forms, some static/global reference forms | Source has `Unsupported`, `Unimplemented`, or assertion paths |
| Semantic abstraction | lifetime/reference erasure, Box erasure, opaque/union declarations, default no-op drops | Translation can succeed while intentionally omitting source-level information |
| Producer-side limitation | constructs Charon cannot faithfully emit for the paired LLBC | Outside Aeneas's own known-failure harness; must be combined with Charon reports |
| Backend/model boundary | unknown external definitions and backend-specific target constraints | Translation may require builtin or handwritten models and target-specific validation |

This table is deliberately evidence-bounded. It should be regenerated from the exact pin rather than copied forward to a later Aeneas release.

Basis: **derived** from the pinned evidence above.

## Boundaries

- No fresh Charon, Aeneas, Lean, Coq, F*, or HOL4 execution was performed in this report.
- Checked-in generated files are preserved repository artifacts. They establish concrete fixture coverage at the pinned source tree but are not a fresh confirmation that the toolchain still reproduces those bytes in another environment.
- The fixture suite is not exhaustive over legal Rust programs. A positive row means "this shape is represented by pinned positive evidence," not "every program using this language feature is supported."
- This report does not duplicate the detailed Rust-to-Lean type/function mapping, borrow/resource semantics, trait translation, nested-borrow history, or panic/error representation reports already in the corpus or durable coordination journal.
- Charon failures are intentionally not classified as Aeneas known failures; the paired Charon support report owns that producer boundary.
- `drop.rs` is evidence for accepted syntax and the default configured abstraction, not full destructor semantics.
- `Dyn.lean` is evidence for specific dynamic-trait forms, not blanket dynamic-trait support.
- The mutually-recursive-trait diagnostic is warning-level by default. The known-failure fixture becomes fail-closed only because it passes `-warnings-as-errors`.
- This report does not characterize the ongoing separation-logic implementation for unsafe/concurrent Rust.
- The absence of a source/test hit here is not evidence that a feature is unsupported.
- Current Anneal design is not derived from these facts. They constrain what a future design must validate and preserve.

## Evidence

**Documentation — Aeneas pin.**

- `README.md`, blob `f331650bd4291d27ba6cee736ce51cf31da9cac1`: pipeline overview; targeted safe-Rust subset; nested-loop control-flow limitation; unsafe/concurrency boundary; backend setup.
- `tests/README.md`, blob `5aa96fab26146514d0ecb2e26fcc40a5a45c94d9`: test protocol, generated-output verification, CI intent, and `known-failure` semantics.

**Source — test protocol.**

- `tests/test_runner/Input.ml`, blob `042191ed5aecc9f591a7522e0c7d956b14e76842`: `Normal`, `Skip`, and `KnownFailure` actions and per-backend fixture configuration.
- `tests/test_runner/run_test.ml`, blob `0a4b726e995dca0132314dae00c421ffd7f3a7a4`: Charon `--preset=aeneas`; Aeneas ordinary-success versus known-failure expectations; `-abort-on-error`, `-checks`, and sequential test configuration.
- `tests/test_runner/Backend.ml`, blob `badc72ad55633bd28028df9c5b6908a3cc035aac`: enabled test backends at the pin.

**Source — Aeneas failure and continuation policy.**

- `src/Errors.ml`, blob `c135674b8601786616c6c20ad81ec388bb8cbfea`: registered error list, `CFailure`, `fail_hard`, warnings, and warning-to-error behavior.
- `src/Translate.ml`, blob `8376e580b542bf3ee28cc9e3d4c170a17b23d379`: per-declaration `CFailure` recovery and omission of failed translations.
- `src/Main.ml`, blob `b3f373f8c449eeae0f9a50bb0ce2d2963903eddc`: `--preset=aeneas` enforcement; final `error_list` check and exit 1; backend configuration.
- `src/Config.ml`, blob `99a9eba5ae67dde20dbfd8d835cdc2900fc60355`: defaults including `fail_hard = false`, `warnings_as_errors = false`, `drop_as_no_op = true`, and recoverable joins.

**Source — support and semantic boundaries.**

- `src/symbolic/SymbolicToPureTypes.ml`, blob `d35b6d67a65af220fdb56614ab1b51edc029b06f`: lifetime/reference/Box erasure; GAT and function-pointer limitations; opaque/union translation; dynamic-trait and complex-binder boundaries.
- `src/symbolic/SymbolicToPure.ml`, blob `95ba91f539e48009efa420dfa956c4c55581cb3a`: associated-type warning for mutually recursive traits/GAT-like cases.
- `src/symbolic/SymbolicToPureExpressions.ml`, blob `b24d12a8a8403a5bc8aae7b55c35ce0259b75bc8`: transmute/pointer-offset rejection, nested-borrow limitations in particular paths, and panic/result construction.
- `src/interp/InterpPaths.ml`, blob `ec23375a5ca0680500daea0248d2372c9901156e`: raw-pointer dereference rejection and borrow-aware place access.
- `src/interp/InterpStatements.ml`, blob `97452f658bbd773c16386592d31b0bf61da8891f`: function-pointer rejection, default no-op drops, panic/control-flow handling, and unsupported statement paths.
- `src/interp/InterpExpressions.ml`, blob `45fddae6eb4e46edb23a98c790c7edf17c586afa`: static-reference limits, dynamic-trait/unsizing limits, raw-pointer aggregate rejection, and unsupported operation paths.

**Preserved known-failure artifacts.**

- `tests/src/raw_pointers.rs`, blob `c77fa4735d4e6616fe4450747e4f3a4d108ca624`, and `tests/src/raw_pointers.lean.out`, blob `74eb81fcad39eaa685249c66d129e6b01ba5a883`: Lean known failure for raw-pointer dereference.
- `tests/src/mutually-recursive-traits.rs`, blob `074ff639d23a8eca640a8f0ea1b639da269cf894`, and `tests/src/mutually-recursive-traits.lean.out`, blob `d7d6c54d81761d6020aa8627592340ef43cc78f4`: warning-as-error known failure for associated types surviving trait transformation.

**Representative preserved positive artifacts.**

- `tests/src/scalars.rs` (`4901accdd5350d23e244208eba767f8488afcc3b`) → `tests/lean/Scalars.lean` (`a3f4d2be02d9ead24aa5a234febb490602573821`).
- `tests/src/adt.rs` (`cc31a7085737e5efd8910316d99adbd74d9df32c`) → `tests/lean/Adt.lean` (`f99cbd9c162d060dc55ea2614d7d0b8bfa32ca9e`).
- `tests/src/arrays.rs` (`478af7171452826436f56f12c88493debac8e0d0`) → `tests/lean/Arrays.lean` (`00b7716b63b41c4747889b42f2dee3796d3ab12d`).
- `tests/src/no_nested_borrows.rs` (`707f7d6e1201d1220380dd565a4178806cf3a9ec`) → `tests/lean/NoNestedBorrows.lean` (`e2a706b744e2e9a105e305cf8a2b353354209dae`).
- `tests/src/nested-borrows.rs` (`61d62cf0e0723a4019e024882e35fb8b212a67eb`) → `tests/lean/NestedBorrows.lean` (`61b3b2b31e50555182867a5b73fa510d05106e22`).
- `tests/src/loops.rs` (`b6b63ec1a8501046af3d153c51b44f34cdde5798`) → `tests/lean/Loops.lean` (`73df255602485533462c214cd011d66867f6b04f`).
- `tests/src/traits.rs` (`a20f6ee91960cbacf99e8899a32e789f7b855671`) → `tests/lean/Traits.lean` (`d234936b72231024fbccf0030a08023836e5eb6e`).
- `tests/src/closures.rs` (`525a3f8941c3224ddf32f818d168fef20f8a1b20`) → `tests/lean/Closures.lean` (`e60021de5406f9f21dacf6e994cbea1fb9264fa4`).
- `tests/src/dyn.rs` (`fa2b29298fcc157e4b05a61098553525fe867f5d`) → `tests/lean/Dyn.lean` (`1ca9dd626eea93ec47dee2094febb8541d41c2c3`).
- `tests/src/constants.rs` (`d75678acc60fd9482090ba8457242dfd801d96e3`) → `tests/lean/Constants.lean` (`9c6e588633544daa10581bd363eabba0fea52b70`).
- `tests/src/static.rs` (`fad3770875b1dd3beec5988357fcc993b645abd2`) → `tests/lean/Static.lean` (`9d31798665d488b70730ea60c928e82c790d308b`).
- `tests/src/drop.rs` (`7f232241c87e1e53b01dcef82ef99d808c068b0f`) → `tests/lean/Drop.lean` (`a0119232ebcddb64b81d919fa9c363cc56f8ba0b`).

**Related reference-corpus reports.**

- `reports/charon-support-and-unsoundness-nightly-2026-06-03/`: paired producer support and semantic hazards.
- `reports/aeneas-rust-to-lean-translation-nightly-2026-06-03/`: concrete functional translation.
- `reports/aeneas-resource-semantics-nightly-2026-06-03/`: lifetime/reference/Box erasure and raw-pointer resource boundary.
- `reports/aeneas-external-models-nightly-2026-06-03/`: external and standard-library model boundary.

No evidence gathered by this report is fresh **execution**.

## Revalidation

For a later Aeneas pin, rebuild the matrix from the new revision rather than assuming monotonic support.

The cheapest source/artifact pass is:

1. read the root support/limitations section;
2. diff `Errors.ml`, `Config.ml`, `Main.ml`, `Translate.ml`, `SymbolicToPureTypes.ml`, `SymbolicToPureExpressions.ml`, `InterpPaths.ml`, `InterpStatements.ml`, and `InterpExpressions.ml`;
3. enumerate `tests/src` options and `known-failure` cases;
4. map each normal Rust fixture to the selected backend's checked-in output;
5. inspect warning-only cases separately from hard errors;
6. pair the result with the exact Charon support matrix for the Charon commit selected by that Aeneas revision.

On a capable execution surface, run the exact pinned test suite and preserve commands, revisions, stdout/stderr, and hashes. At minimum, rerun a compact discriminating set:

- scalar/ADT/array control cases;
- shared, mutable, and nested-borrow cases;
- ordinary loop plus nested labeled outer-loop control flow;
- ordinary traits plus mutually recursive associated types and a GAT;
- closure and function-pointer cases;
- accepted dynamic-trait fixture plus an unsupported dynamic-trait/unsizing shape;
- raw-pointer pass-through plus raw-pointer dereference;
- default drop handling plus `-eval-drops`;
- one warning-only hazard both with and without `-warnings-as-errors`.

For Anneal specifically, run Aeneas once under the intended production flags and once with fail-closed diagnostic settings. Verify that every promise-relevant unsupported or approximated case either fails before proof acceptance or is explicitly excluded by the theorem's domain. Preserve the exact Lean output and then type-check it with the exact Lean toolchain selected by Anneal.