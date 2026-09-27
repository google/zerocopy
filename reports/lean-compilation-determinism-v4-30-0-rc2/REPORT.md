# Lean compilation determinism at v4.30.0-rc2

## Summary

Lean `v4.30.0-rc2` contains explicit mechanisms that make selected parts of compilation independent of scheduling or unstable internal representation order, but the inspected source does not establish a global promise that two builds of the same module produce byte-identical outputs.

The strongest source-level guarantees are local. The frontend enables asynchronous elaboration by default, yet the realization machinery freezes the environment and options used for deferred work so its semantic result is independent of which thread happens to perform it. Module serialization deliberately chooses stable declaration order where filtering would otherwise make exported `.olean` bytes depend on private declarations. The non-GMP compacted-object path clears bignum padding rather than copying indeterminate padding bytes. The LCNF explicit-reference-counting pass assigns encounter-order indices when `FVarId` ordering would not be reproducible. Lean also buffers stderr during elaboration to give diagnostic output deterministic ordering under parallelism.

These mechanisms matter because they show where Lean itself has identified nondeterminism as correctness, artifact-stability, or test-stability debt. They do **not** compose into a source-level theorem of whole-build reproducibility. The same revision explicitly provides `#guard_msgs ordering := sorted` for commands whose message order is nondeterministic, and the realization API documents caller obligations that it cannot enforce, such as avoiding hidden captured inputs. No repeated clean-build experiment was run for this report, and native compiler outputs, object files, executables, timestamps, host ABI differences, and all environment-variable effects were not exhaustively audited.

For Anneal, therefore, “same Lean revision and same source” should not by itself be treated as proof that every emitted byte is reproducible. If byte identity or clean-build/cache-seeded equivalence becomes an architectural requirement, establish it for the exact artifact class with a preserved repeated-build probe. The source evidence here instead identifies the specific determinism mechanisms that such a probe should stress and revalidate.

Basis: **source** + upstream **documentation**, with derived limits stated explicitly. No fresh **execution** evidence.

## Applicability

The subject is `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, which the `v4.30.0-rc2` tag resolves to. Claims are limited to that immutable revision unless a later revision is separately checked.

This report uses **compilation determinism** in three narrower senses that should not be conflated:

1. **semantic scheduling determinism** — asynchronous work observes a stable logical environment rather than whichever environment state a worker thread happens to see;
2. **stable emitted ordering/representation** — an artifact writer or compiler pass chooses an order or byte representation that avoids known nondeterministic inputs; and
3. **observable diagnostic ordering** — parallel work is reported in an order independent of thread completion where the documented mechanism applies.

A fourth, stronger property is **whole-artifact reproducibility**: rebuilding the same inputs produces byte-identical `.olean`, `.ilean`, generated C, object, archive, executable, or other artifacts. The examined implementation demonstrates several ingredients that support this property but does not establish it globally. This report therefore does not claim whole-artifact reproducibility.

The existing `lean-olean-format-identity-v4-30-0-rc2` corpus report describes the `.olean` container, compatibility checks, and several of the serialization mechanisms summarized here. This report treats those mechanisms specifically as evidence about determinism and combines them with asynchronous elaboration, compiler-pass ordering, and diagnostic-ordering evidence. It does not replace the `.olean` format report or Lake's separate build/invalidation reports.

## Findings

### The frontend deliberately combines asynchronous elaboration with a serialized final environment

`Elab.runFrontend` sets `Elab.async` to `true` when the option is otherwise unset. It processes the file through the snapshot-based language pipeline, reports diagnostics, then calls `Language.Lean.waitForFinalCmdState?`. Only after obtaining that final command state does it serialize the module with `writeModule`.

Thus the normal frontend at this revision does not equate deterministic compilation with single-threaded elaboration. It permits asynchronous declaration work, waits for the resulting environment, and serializes that environment after the error gate.

This sequencing is important but insufficient by itself: waiting for all work to finish would still permit nondeterministic results if deferred computations observed timing-dependent environment state. Lean has a separate realization mechanism to address that problem.

Basis: **source** — `src/Lean/Elab/Frontend.lean`, `runFrontend`.

### Deferred realizations freeze their logical input state to neutralize thread choice

`Environment.enableRealizationsForConst` records an environment and option set for later realization. The corresponding `Lean.Meta.realizeValue` documentation states that when multiple environment branches request the same key, the realization is run with the environment and options captured at the enabling point for a local declaration, or with the post-import state for an imported declaration. It says this is done to achieve deterministic results despite the nondeterministic choice of which thread performs the realization.

`realizeConst` makes the same scheduling guarantee for asynchronously materialized helper constants: the effect should be as if the realization had run immediately after `enableRealizationsForConst`, even though whichever requester wins the atomic race may execute the work.

The implementation also acknowledges another scheduling-dependent quantity: the lower-level `Environment.realizeValue` says the operation is inherently nondeterministic in its number of heartbeats and saves/restores the heartbeat count around the operation. This is a local normalization of resource-accounting state, not evidence that wall-clock time or every runtime effect is deterministic.

Basis: **source** — `src/Lean/Environment.lean`, `enableRealizationsForConst` and `realizeValue`; `src/Lean/Meta/Basic.lean`, `realizeValue` and `realizeConst`.

### Realization determinism has explicit caller obligations and undefined cases

The realization API documents limits that prevent treating the mechanism as a universal determinism theorem.

For `realizeValue`, two calls associated with different declarations but the same key have undefined sharing behavior. The documentation therefore recommends that the key uniquely determine the declaration. It also cannot inspect arbitrary values captured by the `realize` closure; callers are advised to extract the realization into a separate function and pass only arguments determined by the key. Similar cautions apply to `realizeConst`.

These are meaning-bearing constraints. The mechanism can make thread assignment irrelevant only when the deferred computation's effective inputs are themselves captured by the intended state/key discipline. A metaprogram that closes over an uncontrolled external input can still introduce behavior outside this guarantee.

Basis: **source** — `src/Lean/Meta/Basic.lean`, documentation on `realizeValue` and `realizeConst`.

### Lean stabilizes `.olean` declaration order where export filtering would otherwise leak private state

`mkModuleData` obtains kernel constants in the deterministic order produced by `constants.foldStage2`. For the exported/server levels it then filters declarations that are not visible at that level. The source notes that although `foldStage2` itself is deterministic, filtering would make the remaining order depend on filtered-out elements — specifically causing exported `.olean` output to depend on `.olean.private` contents.

Lean therefore sorts the filtered constants by name before serializing them. This is a direct source-level invariant about an emitted artifact: private-only declarations should not perturb the order of declarations that remain in the lower-level module image merely because they occupied positions in the original deterministic traversal.

The private level does not take this filtering-and-resort branch; it serializes the full deterministic `foldStage2` traversal.

Basis: **source** — `src/Lean/Environment.lean`, `mkModuleData`.

### `.olean` compaction contains an explicit byte-nondeterminism fix for non-GMP bignums

The compacted-object writer's non-GMP bignum path allocates zeroed destination storage and copies the bignum fields individually. Its comment explains why: a raw `memcpy` of the C++ object would copy struct padding and “lead to non-deterministic outputs.” The digits are then copied separately.

This is unusually direct evidence that byte-level stability of serialized Lean objects is an implementation concern. It also illustrates why semantic equality does not automatically imply byte identity: uninitialized or otherwise irrelevant native representation bytes can leak into a serialized image unless the writer normalizes them.

The observation is deliberately narrow. The cited code is the `#else` branch when `LEAN_USE_GMP` is not defined. The source takes a different representation path when GMP is enabled, and this report does not infer the same padding mechanism or a whole-file reproducibility guarantee for that configuration.

Basis: **source** — `src/runtime/compact.cpp`, `object_compactor::insert_mpz`.

### Compiler IR includes explicit reproducible ordering where identifier order is unsuitable

The LCNF explicit-reference-counting pass stores an incrementing encounter-order index in its variable metadata. The source explains that the index is used to order variables “in a reproducible fashion when required” because the default ordering does not work for `FVarId`-based variables.

This is evidence that determinism concerns extend beyond `.olean` serialization into compiler transformations. It is still a local property: the index stabilizes ordering choices made by this pass. It does not establish that all compiler passes, generated C, native code, or linker outputs are reproducible.

Basis: **source** — `src/Lean/Compiler/LCNF/ExplicitRC.lean`, `Context.idx`.

### Diagnostic reporting actively hides some scheduling order, but Lean also supports nondeterministic command-message order

The pinned developer debugging guide says that stderr produced during elaboration is buffered and shown as messages after a command has elaborated because buffering is necessary to ensure deterministic ordering of messages under parallelism. Setting `stderrAsMessages=false` bypasses that buffering so debug output appears immediately; the resulting raw timing order should therefore not be treated as the deterministic message-order path.

The realization APIs reinforce this design: traces, diagnostics, and raw standard-stream output from deferred realizations are reported through `Core.logSnapshotTask`, with the stated goal that generated diagnostic locations are deterministic.

At the same time, `#guard_msgs` supports `ordering := sorted`, documented as useful for testing commands that are nondeterministic in their message ordering. That facility is important negative space. Lean does not pretend every producer's natural message sequence is deterministic; some tests deliberately compare a sorted multiset-like order instead.

Derived consequence: a test or integration protocol that depends on exact diagnostic ordering should identify the reporting path it is testing. “Lean parallelism is deterministic” is too strong; specific snapshot/buffering paths stabilize specific observable orderings, while other commands may still produce nondeterministic message order.

Basis: **documentation** + **source** — `doc/dev/debugging.md`; `src/Lean/Meta/Basic.lean`; `src/Init/Notation.lean`.

### The source evidence is a map of stabilization points, not a proof of whole-build byte identity

The inspected revision contains at least four independent stabilization techniques:

- capture a logical environment/options snapshot for asynchronously scheduled realization work;
- normalize declaration ordering before module serialization where filtering would make order depend on hidden declarations;
- normalize representation bytes where native padding would otherwise enter serialized output; and
- introduce explicit stable ordering keys where compiler-internal identifiers do not provide a suitable reproducible order.

These mechanisms are valuable precisely because they remove distinct sources of nondeterminism. Their existence also means that whole-build reproducibility cannot safely be inferred only from high-level source semantics: byte and ordering details in multiple implementation layers matter.

No inspected source statement says that every compilation output is byte-identical across repeated builds. The evidence here therefore supports the narrower conclusion that Lean engineers intentionally stabilize several important compilation paths while leaving a stronger reproducibility claim to be established artifact-by-artifact.

Basis: **derived** from the source findings above. This is a bounded conclusion, not an assertion that no stronger guarantee exists anywhere outside the examined evidence.

## Boundaries

- **No repeated-build experiment was run.** This report does not establish byte-for-byte equality of two clean compilations, two differently threaded compilations, or a clean build versus a cache-seeded build.
- **Artifact coverage is incomplete.** The source audit directly covers frontend finalization, `.olean` module-data construction/compaction, one LCNF compiler pass, and selected diagnostic paths. It does not establish determinism for `.ilean`, generated C, object files, archives, executables, debug information, native symbol tables, timestamps, filesystem metadata, or every persistent environment extension.
- **Host/toolchain variation was not tested.** No claim is made about cross-platform, cross-architecture, cross-libc, cross-compiler, or cross-linker byte identity.
- **GMP and non-GMP bignum serialization differ.** The explicit padding-normalization comment cited above is in the non-GMP path; this report does not generalize that exact mechanism to the GMP path.
- **Asynchronous realization has caller obligations.** Lean cannot verify arbitrary closure captures, and some cross-declaration key-sharing behavior is documented as undefined. The realization mechanism does not sanitize external nondeterministic inputs supplied by user metaprograms or plugins.
- **Message order is not globally stable.** The `#guard_msgs` sorted mode exists specifically for commands with nondeterministic message order. Deterministic buffered stderr/snapshot reporting should not be generalized to every diagnostic or debug-output producer.
- **The report is revision-pinned.** Adjacent Lean versions may add or remove stabilization mechanisms. In particular, no claim is made from this evidence about Lean 4.31 or later.
- **Lake is a separate layer.** Lake decides whether and how compilation runs, what artifacts are reused, and which inputs invalidate work. A deterministic Lean invocation would not by itself establish clean-build/cache-seeded equivalence or Lake cache correctness.

The broad #3720 item “Lean compilation determinism” should therefore not be interpreted as empirically closed by this source-only investigation if the intended requirement is whole-build reproducibility. The report preserves the source-level contract and the missing experiment separately.

## Evidence

All implementation source below is from `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, tagged `v4.30.0-rc2`. No **execution** evidence was produced.

- **Source:** `src/Lean/Elab/Frontend.lean`, blob `fd3760667db96a351b4f654720193c89bbee356e`, especially `runFrontend` around lines 139–201. It enables asynchronous elaboration by default, waits for the final command state, gates on errors, and only then calls `writeModule`.
- **Source:** `src/Lean/Environment.lean`, blob `8a485808c7b0e4c32959740efa012a37610b6914`, especially `enableRealizationsForConst` around lines 850–885; `mkModuleData`/`writeModule` around lines 1804–1878; and lower-level `realizeValue` around lines 2577 onward. These regions establish captured realization state, deterministic constant ordering plus re-sorting after visibility filtering, serialization sequencing, and the heartbeat-normalization comment for concurrent realization.
- **Source:** `src/Lean/Meta/Basic.lean`, blob `5f6a9cb368cdb8f364a094820f9103aba59b4010`, especially `realizeValue`/`realizeConst` around lines 2566–2680. The API documentation states the intended scheduling determinism and its key/capture limitations, and explains deterministic diagnostic localization.
- **Source:** `src/runtime/compact.cpp`, blob `c8bf24aa8206bc99cddde2fda2e4e2212b8a75b0`, `object_compactor::insert_mpz` around lines 280–307. The non-GMP path zeroes/copies fields individually because copying padding would produce nondeterministic output.
- **Source:** `src/Lean/Compiler/LCNF/ExplicitRC.lean`, blob `4b871deec6494398fc47d5d85520065b74c22523`, `Context.idx` around lines 226–234. The pass records encounter order for reproducible ordering when `FVarId` ordering is unsuitable.
- **Documentation:** `doc/dev/debugging.md`, blob `a742f9b6431b357b7c01635a36ec67b213f12cb3`, lines 24–27. Buffered stderr is described as necessary for deterministic message ordering under parallelism; disabling `stderrAsMessages` bypasses that path.
- **Source:** `src/Init/Notation.lean`, blob `5323fb54ab3f0e83aeb62b694469aa971367e9d6`, `guardMsgsOrdering` documentation around lines 802–807 and the corresponding command documentation around lines 900–905. Sorted message comparison is explicitly useful for commands with nondeterministic message ordering.

Related corpus evidence: `reports/lean-olean-format-identity-v4-30-0-rc2` independently documents the serialized module family and already notes several local determinism mechanisms while leaving the broader compilation-determinism question open. This report adds the async-realization, compiler-pass, and diagnostic-ordering dimensions and makes the missing whole-build experiment explicit.

## Revalidation

For another Lean revision, first perform a narrow source diff before running broad experiments:

1. inspect `Elab.runFrontend` for the async default, final-state wait, error gate, and module-write sequence;
2. inspect `Environment.enableRealizationsForConst`, lower-level `Environment.realizeValue`, and `Lean.Meta.realizeValue`/`realizeConst` for captured environment/options semantics, key sharing, closure-capture caveats, heartbeat handling, and diagnostic replay;
3. inspect `mkModuleData` for how constants and extension entries are ordered before serialization;
4. inspect `object_compactor::insert_mpz` and any other changed compactor cases for native padding or address-dependent bytes;
5. inspect compiler passes that introduce ordering over `FVarId`, hash-map, or set contents, beginning with `LCNF.ExplicitRC`; and
6. inspect message/snapshot reporting and `#guard_msgs` ordering semantics before depending on exact diagnostic order.

If whole-artifact reproducibility matters, use a preserved execution probe rather than extending these source findings by inference. A useful probe should compile one fixed module repeatedly under the same immutable toolchain while varying at least process identity and thread count, preserve hashes and exact bytes for `.olean`, `.olean.server`, `.olean.private`, `.ilean`, generated/native compilation outputs that matter, and compare diagnostics separately. Repeat from a clean build root and from the exact cache-seeded/prebuilt state Anneal intends to use. Record the full environment and toolchain identities so a mismatch can be localized rather than merely observed.

Such a probe should also contain cases that exercise each source-level stabilization point above: private declarations filtered from exported `.olean`, a large non-GMP integer where that configuration is relevant, asynchronous realizations, and an ExplicitRC ordering case. A passing run would establish only those tested artifact/configuration combinations; it would not justify cross-platform or adjacent-version generalization.
