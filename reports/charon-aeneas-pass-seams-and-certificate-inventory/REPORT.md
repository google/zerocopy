# Charon and Aeneas pass seams and certificate inventory

## Summary

The pinned pipelines expose identifiable certificate seams, but their pass schedules and implementation checks do not establish semantic preservation. The original inventory records 52 scheduled Charon semantic invocations, 19 Aeneas prepasses, 50 pure micro-pass entries and nine postprocessing steps, with their gates and proposed relations. Several entries repeat. This is a source inventory, not a runtime count or proof coverage count.

The useful decomposition is capture/import, state and control-flow translation, symbolic borrow reconstruction, pure rewriting, and backend denotation. Each needs its own checked relation and admissibility conditions. Matching successful outputs across the pipeline cannot reveal a bad source prefix erased before the first checked representation.

## Applicability

Charon applies at `cf02e3f228f97ee7be3a415be56989053063326d`; Aeneas at `ca282ec2312a96f6a985a4d23a663690816d3f3e`. The Charon toolchain file selects nightly-2026-09-17. No fresh build of either revision was run. The sources were directly inspected through immutable public GitHub file identities; [inventory.json](inventory.json) preserves the original schedule/gate tabulation and 82 source coordinates without mirroring implementation source.

The PR documentation at `cce761ad53785973ec2f4a6b13715b770b340c87` supplies a separate downstream admission policy. The read-only parent execution uses legacy alpha24 binaries with the two hashes in REPORT.json. That execution is evidence of those binaries on two tiny functions, not evidence that the current source schedule ran or that any pass is certified.

## Findings

### Capture, compiler import and dependency origins

Basis: source + documentation; certificate obligations below are derived.

Charon's [driver](https://github.com/AeneasVerif/charon/blob/cf02e3f228f97ee7be3a415be56989053063326d/charon/src/bin/charon-driver/driver.rs#L33) sets MIR optimization level zero, preserves UB-relevant MIR and encodes dependency MIR; it disables alignment/null instrumentation and exposes a borrow-check bypass option. Its expansion and later-analysis hooks inspect compiler errors. [get_mir.rs](https://github.com/AeneasVerif/charon/blob/cf02e3f228f97ee7be3a415be56989053063326d/charon/src/bin/charon-driver/translate/get_mir.rs#L68) selects built/promoted/elaborated bodies when available, falls back to optimized local MIR if the requested body was stolen, and uses optimized/CTFE routes for nonlocal bodies.

Derived interface: capture must bind the selected crate, source bytes, edition, target, compiler/sysroot/dependencies, effective flags, cfg, macro/build-script/generated input, expansion identities and annotations, root selection, and actual per-body origin. The earliest relation must cover source bad-operation prefixes and implicit evaluations before any erasure. A compiler's successful type/borrow judgment is consumed evidence unless a separately checked theorem links it to that source representation. Checking normalized LLBC cannot retrospectively justify macro hygiene, resolution, const evaluation, monomorphization or an earlier optimization.

The pinned cce [admission design](https://github.com/google/zerocopy/blob/cce761ad53785973ec2f4a6b13715b770b340c87/verification/aeneas/ADMISSION_DESIGN.md#L340) conditions optimized-query admissibility on reviewed production origin and explains that current flags do not repair precompiled bodies. Its lines 366–371 allow either a reviewed common origin or rejection/preservation of a consequential distinction. A later local policy rejecting requested-promoted fallback is stricter; this report does not project that policy onto all dependency optimized/CTFE queries.

### Charon scheduled and enabled seams

Basis: source schedule and gate inspection; proposed relation classification is derived.

[transform/mod.rs](https://github.com/AeneasVerif/charon/blob/cf02e3f228f97ee7be3a415be56989053063326d/charon/src/transform/mod.rs#L91) schedules item cleanup, fused ULLBC passes, optional structured reconstruction and final cleanup. Its runner checks each pass gate; owned passes can transform carried bodies through preceding passes. The inventory includes every semantic invocation in this function, including repeated storage insertion, local removal and goto merging. Printers are observational seams, not semantic rewrites. This explicit scope does not enumerate every rustc-internal or Hax elaboration pass.

| Seam family | Required certificate relation and side conditions, derived |
| --- | --- |
| Names, comments, specification links | Binding identity and executable projection; renaming cannot change the referenced declaration. Attaching a specification requires an independent source/consumer identity check. |
| Trait clauses, associated types, default methods, specialization | Substitution and environment correspondence; exact dictionaries, callees, trait laws and hidden effects survive lifting/removal. |
| Constants, promoted initializers, generated helpers | Exact value, width, initialization and failure relation, with body origin; compile-time evaluation is executable behavior. |
| Storage, moves, drops and borrow structure | State relation tracks lifetime, initialization and access rights, or proves their erasure irrelevant for the admitted fragment. |
| CFG merging, duplicated returns, unreachable removal, LLBC structuring | Every source branch and first bad prefix has a matching target prefix; preserve guards, return/break/continue/abort/cleanup edges. Progress is separate. |
| Reconstructed fallible operations and assertions | The replacement arithmetic/index operation owns the removed guard and its failure classification; exact overflow mode and evaluation order matter. |
| Box/vector resugaring and allocator hiding | Allocation, initialization, failure, ownership and custom-allocator effects are represented or excluded with justified premises. |
| Layout guarantees and pointer metadata | Target/layout representation facts are preserved; they supply neither access authority nor a runtime storage-transfer theorem. |

Individual gates are recorded in inventory.json. The [Aeneas preset](https://github.com/AeneasVerif/charon/blob/cf02e3f228f97ee7be3a415be56989053063326d/charon/src/options.rs#L523) enables associated-type lifting, builtin boxes, operation/index calls, selected resugaring and cleanup. It does **not** enable desugar_drops or precise_drops. [desugar_drops.rs 62–64](https://github.com/AeneasVerif/charon/blob/cf02e3f228f97ee7be3a415be56989053063326d/charon/src/transform/normalize/desugar_drops.rs#L62) has its own flag. Options 606–639 impose compatibility constraints. A scheduled pass is therefore not automatically enabled, and an enabled pattern pass may make no changes.

[Type checking](https://github.com/AeneasVerif/charon/blob/cf02e3f228f97ee7be3a415be56989053063326d/charon/src/transform/typecheck_and_unify.rs#L645) is optional; it skips errored items, tolerates type errors in reused default-method copies and unifies body lifetimes. Derived: this establishes no blanket borrow-safety or semantic correspondence theorem.

### Imported LLBC, symbolic states and backward functions

Basis: source; relation requirements are derived.

Aeneas [Main.ml 583–602, 755–782](https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/src/Main.ml#L583) parses a crate, requires the serialized Aeneas preset, runs prepasses, then selects borrow checking or translation. Registered errors lead to exit 1 at line 812; external opaque definitions may still be emitted with a warning. The tiny LlbcOfJson module delegates its parser rather than proving an inversion theorem here.

[PrePasses.ml 2342–2412](https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/src/PrePasses.ml#L2342) includes region/closure repairs, dead-code/loop/join cleanup, shallow-borrow/storage erasure, panic/global decomposition, trait/type/static/vtable changes and renaming. A caught prepass failure records an ErrorBody. Derived: successful deserialization is distinct from schema fidelity, successful extraction and complete dependency admission; ErrorBody and missing/opaque definitions require rejection or exact registered summaries.

[Translate.ml 30–50, 121–134](https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/src/Translate.ml#L30) normally invokes symbolic interpretation before pure conversion, but target-dispatch bodies bypass that interpreter. A signature check rejects certain higher-ranked/free implied bounds. [Interp.ml 539–623](https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/src/interp/Interp.ml#L539) synthesizes forward and region-group backward endings and returns an error AST after a caught translation failure.

Before body interpretation, Interp.compute_contexts (52–167) selects declaration groups, analyzes types/functions and builds dependency contexts; RegionsHierarchy supplies signature groups (526). Translate.crate_to_pure (315–596) separately translates types, globals, signatures, traits and implementations. inventory.json records these analysis/translation/backend seams as well as scheduled rewrites. Their derived obligations include sound effect flags, complete extraction selection and dictionary/initializer preservation.

Derived relation: relate concrete source state to symbolic values, loans/borrows, abstractions and frames, then to a pure value plus its backward continuations. A borrow-ending update must restore the corresponding place and related resource state. Joins must cover both incoming states; loop fixed points must include entry and every iteration, preserve loans and handle break/continue/return/failure. Identifier freshness and alpha equivalence are proof side conditions, not semantic evidence by themselves. Inspection of [join interfaces](https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/src/interp/InterpJoin.mli#L77) identifies the relevant context-matching seams; it does not prove their soundness.

Concrete exclusions are visible: [raw dereference is rejected](https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/src/interp/InterpPaths.ml#L106); [statements 783–807](https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/src/interp/InterpStatements.ml#L783) default drops to no-ops, omit PlaceMention checks, map Abort to panic and reject UnwindResume. Disabling the drop no-op only invokes logical drop_value; this is not an execution of arbitrary Rust destructors. The cce admission policy consequently demands original-representation checks and rejects these unsupported effects.

### Pure rewrite and backend denotation seams

Basis: source; certificate design is derived.

[PureMicroPasses.ml](https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/src/pure/PureMicroPasses.ml#L13) defines the ordered 50-entry list. Postprocessing decomposes loop helpers/bodies, filters inputs, installs fixed-point calls, simplifies returns/asserts adds type annotations and optionally adds fuel. [Main.ml 513–549](https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/src/Main.ml#L513) sets backend-specific gates: Lean enables tuple-let merging/pure-call lifting and disallows fuel; Coq decomposes patterns; F* disables massert. Inventory gates describe these configurations, not a proof.

Two load-bearing rewrite premises are explicit in [PureMicroPassesGeneral.ml](https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/src/pure/PureMicroPassesGeneral.ml#L629): duplicate-call elimination anticipates unsoundness with stateful backward calls; unused monadic bindings survive unless the expression cannot fail or its failure is subsumed by the continuation (1159–1173). Derived: an effectful extension needs a new equality/effect theorem; preserving a single combined failure flag may still be too weak for outcome-sensitive safety.

Backend certificate endpoints should bind the full pure AST, builtin/environment identities, emitted Lean declaration and actual kernel denotation. Pure AST well-formedness checks are optional ([Config.ml 409–420](https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/src/Config.ml#L409)). [Extract.ml 703–741](https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/src/extract/Extract.ml#L703) emits sorry for Lean error expressions; a distinct termination template also contains sorry at 2050. Derived: exit status, error/opaque inventory, emitted source and closed theorem dependency audit are separate gates. Merely elaborating a file containing holes cannot certify translation or the consumer property.

### Legacy two-function execution and certifiability

Basis: read-only execution records acquired by the parent; direct inspection here.

The alpha24 probe chooses between two u8 arguments and updates the second field of a borrowed pair. Charon raw and Aeneas-preset invocations exited zero. The retained traces expose a unit-return assignment insertion and CFG structuring; Aeneas translation also exited zero. Source hash: `cb328552754e6c54ac06e827dea6c52f12c23fa2d987b55e0c2644472faaf7d0`. These executions establish availability and inspectable input/output seams only. This report neither reruns the binaries nor duplicates the separate certificate prototype.

Derived adoption gate: start with local, finite prefix relations for a declared subset and fail on unrecognized changes. Small binding/CFG/value certificates may be practical; symbolic borrow reconstruction needs richer state witnesses; backend denotation needs the actual Lean term. Each pass must identify generation, independent checking and the semantic soundness theorem separately. A future certificate's maintenance follows schema, compiler options, primitive effects and rewrite side conditions, not merely pass names.

## Boundaries

This answers the inventory/mechanism questions for the named top-level pipelines. It does not exhaust rustc/Hax internals, all imported parser implementation, every builtin, or all backend formatting cases. No upstream proof was replayed and no current-pin executable was built. The invented relations in inventory.json are obligations, not established upstream theorems.

Source-to-MIR adequacy, macro/annotation ownership, complete unsafe dependency support and generic/dynamic/FFI effects remain genuine unexamined implementation questions here. Implementing future Anneal certificates is separate engineering work; its absence does not invalidate the source inventory. Unsupported input, source UB, modeled panic, extraction failure and missing proof are distinct outcomes.

## Evidence

Primary identities and exact file blobs are in REPORT.json and inventory.json. Important additional blobs are driver `e8ad902cd513eb5308a422772c1b3fed6bb1eab1`, get_mir `84cdc67bbd56e4c51b4434cff57e0ebd1cf6e679`, translate_bodies `5993d8748e92f72e7f45f52365f8f0f6ff4440bc`, and Extract.ml `de0a81f6433881ba6b0a1d53e6a9677b8d555124`. Primary source links above name immutable revisions and narrow coordinates.

The parent acquisition records are preserved, with normalized paths and original artifact hashes, in the [fork certificate](../charon-fork-storage-certificate-alpha24/REPORT.md) and [returned-update certificate](../aeneas-pair-returned-update-alpha24/REPORT.md) packages, including original/final traces and generated definitions. The binary hashes identify observations without asserting a Git-source match. No upstream source mirror is included.

## Revalidation

Reacquire the immutable schedule, gates and named entry points; compare exact order and conditions to inventory.json. Check body origins separately from requested MIR level and flags. Run canonical package-format validation only in the parent-owned candidate. The local validate.py checks metadata, standard sections, coverage references and inventory structure; it does not replay upstream compiler semantics or certify any inventoried pass.

*Authored by an AI agent acting on joshlf's behalf.*
