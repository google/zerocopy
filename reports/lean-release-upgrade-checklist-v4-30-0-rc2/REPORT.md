# Lean release upgrade checklist for Anneal

## Summary

Changing Anneal's Lean release changes more than the proof checker executable. At the current baseline, Aeneas `nightly-2026.06.03` selects `leanprover/lean4:v4.30.0-rc2`, while Anneal independently downloads per-platform Lean `v4.30.0-rc2` archives under fixed hashes. The Aeneas Lean project also pins a concrete Lake dependency closure, including Mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`. Those identities together determine the environment in which generated Lean is parsed, elaborated, built, queried interactively, and checked.

A Lean upgrade can therefore affect several independent proof-relevant boundaries: the kernel/admission model; parser and elaborator acceptance of generated code; recursion and partiality syntax; tactic behavior; module serialization and invalidation; Lake dependency/build state; diagnostics and LSP/RPC behavior; native artifacts; and the packaged archive itself. A successful `lean --version`, a successful build of one file, or a matching release label does not establish those boundaries collectively.

For Anneal, the durable upgrade unit is the **exact Lean revision and archive bytes, the paired Lake package closure, and discriminating generated-code/proof evidence**. `upgrade-checklist.json` records twelve gates. A proposed release should be accepted only after each applicable gate is either re-established or reviewed as an intentional compatibility change. The checklist is intentionally asymmetric: a changed component need not trigger unrelated archaeology, but evidence about one layer cannot silently substitute for another.

This report defines the revalidation procedure. It does not evaluate or approve any newer Lean release.

## Applicability

The baseline is current Anneal source at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, Aeneas `nightly-2026.06.03` at `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, and Lean `v4.30.0-rc2` at `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`.

At that baseline:

- Aeneas `backends/lean/lean-toolchain` names `leanprover/lean4:v4.30.0-rc2`;
- Aeneas `backends/lean/lake-manifest.json` locks Mathlib to `5450b53e5ddc75d46418fabb605edbf36bd0beb6` and records the remaining Lean package closure;
- Anneal independently sets `leanVersion = "v4.30.0-rc2"`, maps each supported host to the corresponding upstream archive name, and fixes the unpacked toolchain by a per-platform recursive SHA-256;
- the Lean release is therefore consumed both as a language/proof implementation and as a packaged binary/toolchain artifact.

Use this checklist when replacing the Lean release, changing the archive construction for the same nominal release, or intentionally running Aeneas-generated Lean under a Lean/Lake environment different from the one Aeneas pins. It is not a general Lean release-engineering checklist. The evidence should be limited to the interfaces Anneal actually depends on, but those interfaces include both batch and interactive use when either is part of the intended architecture.

## Findings

### 1. Record the exact revision and the exact archive bytes

The version string is only one part of the identity Anneal consumes. Current Anneal maps four host classes to Lean release archives and fixes the resulting unpacked toolchain with distinct SHA-256 values. A future upgrade should preserve both identities: the Lean source revision denoted by the release and the exact per-platform artifacts Anneal executes.

For each supported platform, resolve the release tag to a commit, record the archive URL/name and digest, and record the Anneal source change that selects it. If an upstream artifact is replaced under the same tag or filename, the digest change is a distinct upgrade event even if the displayed Lean version is unchanged.

Basis: **source** (`anneal/flake.nix`, Aeneas `lean-toolchain`) + derived packaging boundary.

### 2. Keep Anneal's Lean selection and Aeneas' expectation explicit

Aeneas emits Lean against an explicitly selected Lean toolchain. Current Anneal independently selects the same `v4.30.0-rc2`. That agreement is useful evidence, but it is not automatically preserved when either side moves.

For a proposed Lean upgrade, compare Anneal's selected version with Aeneas `backends/lean/lean-toolchain`. If they diverge, treat the divergence as a compatibility edge that requires direct generated-code evidence. Do not infer compatibility from adjacent Lean releases or from the fact that the Aeneas binary itself still runs.

This is separate from the Aeneas release-upgrade checklist: an Aeneas upgrade may move Lean as one transitive edge, while a Lean-only experiment may intentionally hold Aeneas fixed and test that edge directly.

Basis: direct **source** pins.

### 3. Re-resolve the Lake package closure as part of the proof environment

Lean and Lake share one source/toolchain revision, while the generated Aeneas project additionally depends on a locked package graph. At the baseline, Aeneas' manifest pins Mathlib to `5450b53e…` and records exact revisions for its transitive packages.

A Lean upgrade should therefore record the new `lake-manifest.json` or another exact dependency closure rather than relying on unconstrained package resolution. Diff package revisions, source types, and manifest schema. Then load/build the generated project using that closure under the new Lean toolchain.

This gate is not merely package-management hygiene. Proof automation, imported theorems, generated model support, native extensions, and build artifacts can all change when the package graph changes even if Lean itself does not.

Basis: Aeneas manifest **source** + the pinned Lake dependency-resolution report.

### 4. Revalidate the logical trust boundary

At the baseline, Lean distinguishes ordinary axioms, `sorry`/`sorryAx`, `unsafe` declarations, compiler-side executable trust mechanisms, and explicit kernel-check bypasses such as `debug.skipKernelTC`. Those are meaning-bearing distinctions for Anneal's TCB audit promise.

A release upgrade should revalidate the subset of that model on which Anneal relies. More importantly, it should inspect representative final theorems rather than treating package-wide source searches as a theorem-specific trust audit. Compare transitive axiom dependencies with the accepted allowlist, and investigate any new assumption introduced by generated code, imported proof support, or changed tactics.

A proof that elaborates under the new release is not sufficient if its accepted assumptions changed unnoticed.

Basis: pinned Lean trust/admissions **source analysis** preserved in the reference corpus.

### 5. Treat generated Lean acceptance as an interface test

Aeneas-generated Lean is consumed by Lean's parser, elaborator, module/import system, name resolver, and compiler frontend. Those layers are revision-sensitive even when the kernel's core logic is unchanged. A syntactic or elaboration change can reject generated code; a name-resolution or import change can bind different declarations; a diagnostic change can alter Anneal's error mapping.

Preserve a fixed generated-Lean corpus and elaborate it under the exact proposed toolchain and locked package closure. Compare success/failure, required source changes, imports, warnings, and meaningful diagnostics. When a failure appears, use the focused reference reports to identify the responsible layer instead of treating every failure as a generic "Lean version mismatch."

The corpus should include code emitted by the translation patterns Anneal expects to support, not only hand-written Lean smoke tests.

Basis: published exact-pin reports for CLI/environment, modules/imports, name resolution, parser/elaborator positions, and generated Aeneas interfaces.

### 6. Re-run proof automation that Anneal actually depends on

Tactic names are not compatibility contracts. At the current pin, `simp`/`simp_all`, `grind`, and `omega` each have substantial revision-specific behavior. `simp_all` consumes context differently from `simp`; `grind` is an extensible bounded search engine; and the pinned `omega` implementation is intentionally incomplete because it omits dark/grey shadows. `linter.unusedSimpArgs` also records use through specific elaboration/info-tree machinery and has documented false-negative paths.

An upgrade should replay representative generated and user-authored proofs that use these facilities. Preserve the proof result and, where Anneal's assurance depends on it, the theorem's axiom dependencies. If proof scripts change, distinguish an intentional proof-engine migration from a semantic change in the generated program.

Do not interpret a tactic failure as a counterexample to the proposition, or a tactic success as evidence that source-to-Lean translation remained faithful. These tools live downstream of that translation boundary.

Basis: exact-pin `simp`, `grind`, `omega`, and unused-simp-argument reports.

### 7. Recheck recursion, termination, and partiality together

Lean elaborates ordinary accepted recursive definitions into kernel-checkable non-recursive terms through structural or well-founded recursion. `termination_by` and `decreasing_by` select or help construct that evidence. `unsafe`, `partial`, and `partial_fixpoint` occupy distinct paths.

This boundary is especially relevant to Aeneas. The current corpus records a source-level incompatibility between one Aeneas decreases-clause output path and Lean `v4.30.0-rc2` termination-suffix grammar. A newer Lean release may fix, reject differently, or otherwise change that interaction without changing unrelated proof behavior.

The upgrade corpus should therefore contain recursive functions and translated loops, including any generated termination clauses Anneal may rely on. Check both acceptance and the intended total/partial interpretation; do not equate "new syntax parses" with "the same termination claim is established."

Basis: pinned Lean termination report plus Aeneas recursion/loop/extrinsic-termination reports.

### 8. Treat `.olean`, `.ilean`, and Lake trace state as toolchain-sensitive build state

At the baseline, `.olean` is a native serialized `ModuleData` image with compatibility tied partly to Lean build identity and runtime representation. Release builds enable a Git-hash compatibility check, but the core loader does not establish source freshness. Lake separately mixes Lean identity into build traces and computes content hashes for module artifacts.

Those layers answer different questions. A `.olean` that the loader accepts is not thereby proven fresh for the current source graph. A Lake `.hash` or `.trace` file does not make an object valid for another Lean binary. Import lookup also depends on path/search configuration rather than a self-authenticating internal module identity.

A Lean upgrade should therefore default to rebuilding prepared artifacts unless Anneal has a narrower, tested reuse protocol. If reuse is important, revalidate the exact artifact classes, Lean Git identity, Lake trace/hash state, source/dependency freshness, and search-path configuration.

Basis: the pinned `.olean` identity and Lean/Lake trace/hash reports.

### 9. Revalidate interactive state and diagnostics separately from batch checking

The pinned Lean server supports the primitive Anneal would need for interactive proof work: a client can open a document, synchronize processing, and query tactic goals at a position through Lean-specific RPC over the LSP-managed worker. That protocol is stateful. Edits change document versions; old requests can be cancelled; worker restart invalidates RPC sessions; imported-file changes can mark dependents stale and require restart.

Diagnostics also have multiple layers. Lean's core `Message` severity, batch-rendered severity, process/build success, and LSP diagnostic shape are related but not identical. A version change can therefore alter an agent-facing interface even when the same proof succeeds.

If Anneal exposes batch diagnostics, LSP, MCP, or tactic-state queries, preserve compact protocol specimens and replay them after the upgrade. Verify coordinates/ranges, severity, named errors, document-version handling, processing barriers, stale-dependency behavior, session reconnect behavior, and tactic-state structure actually consumed by the client.

Basis: pinned server, environment-invalidation, CLI, and diagnostic-object reports.

### 10. Separate logical module artifacts from host-native products

Lake can produce `.olean`, `.ilean`, IR, generated C/bitcode, host objects, static/shared libraries, plugins, and executables. Host-native products participate in platform-specific build traces and cannot be treated as portable merely because the source-level Lean package is portable.

Current Anneal also packages a platform-specific Lean archive and manipulates prepared dependency trees. A Lean upgrade should inspect each supported archive class and revalidate native products retained in any prepared tree. Test the relocated/read-only environment Anneal will ship rather than only a mutable development checkout.

This gate is distinct from logical proof compatibility. A theorem can remain valid while a precompiled plugin or helper fails to load on a target platform.

Basis: pinned Lean-package native-artifact report + Anneal archive packaging source.

### 11. Require execution evidence for determinism or cache equivalence claims

The pinned Lean source contains deliberate stabilization mechanisms for asynchronous elaboration, serialized declaration order, object padding, compiler IR indexing, and diagnostic ordering. The same report explicitly does not establish a global guarantee of byte-identical builds.

Likewise, current Lake source explains cache and trace mechanics, but source inspection alone cannot establish that a clean build and Anneal's exact cache-seeded/prepared build produce all semantically relevant equivalent artifacts under a new release.

Only run this gate to the strength Anneal needs. If cache keys depend on byte identity, repeat clean builds and hash the relevant artifacts. If a prepared cache must be semantically equivalent to a clean build, compare the exact outputs and behaviors that consumers observe. Do not turn source-level determinism mechanisms into a broader reproducibility claim without a probe.

Basis: pinned Lean compilation-determinism and Lake cache/build-state reports. This gate deliberately preserves the empirical limitation.

### 12. Finish with the exact generated-code-to-proof composition

Component checks reduce diagnosis cost, but the final gate should exercise the composition Anneal will rely on. A compact corpus should include ordinary generated functions, borrowing, a loop and recursive function, model/trait-dependent code, diagnostic failures, and representative proofs using the automation Anneal expects to support.

Run that corpus through the exact packaged Lean/Lake environment and dependency closure. Preserve the generated Lean input, command/environment identity, build result, diagnostics, interactive transcript when relevant, and representative theorem axiom sets. If a prepared read-only dependency universe is part of the product, use it here rather than substituting a developer checkout.

This is regression and integration evidence, not a proof that the Rust-to-Lean translation is semantically correct. That correspondence remains a separate obligation. The value of the end-to-end gate is that a release cannot pass by satisfying each component in isolation while their composition fails.

Basis: **derived** from the independent exact-pin boundaries above.

## Boundaries

- No newer Lean release was selected or evaluated. This report defines upgrade gates; it does not approve an adjacent release.
- No fresh Lean, Lake, Aeneas, Mathlib, Nix, LSP, or server execution was performed for this report.
- The checklist does not require every upstream Lean or Mathlib test. It requires evidence targeted at Anneal's actual dependency and proof interfaces.
- Passing the checklist is not a proof of Rust-to-Lean semantic preservation. It is compatibility, regression, trust, and integration evidence around that separately justified boundary.
- A Lean-only upgrade may intentionally run Aeneas-generated code under a Lean version Aeneas did not pin. That is permitted only as an explicit compatibility experiment; it is not inferred safe from adjacency.
- `.olean` acceptance, Lake freshness, source freshness, and semantic equivalence are distinct properties. None substitutes automatically for the others.
- Proof-automation behavior is not required to be byte-for-byte or search-path identical across releases. Changed behavior must instead be understood where Anneal depends on it.
- Whole-build determinism and clean/cache-seeded equivalence require execution evidence if Anneal relies on them. This source-only report intentionally leaves those empirical claims open.
- Interactive protocol behavior matters only when Anneal's selected architecture uses it, but a batch-only smoke test cannot validate an interactive interface.
- The machine-readable checklist is a revalidation aid. Current Anneal authority, the exact proposed toolchain, and newer precisely scoped reference evidence remain controlling.

## Evidence

**Direct selection source.** `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`:

- `backends/lean/lean-toolchain` (blob `6c7e31fffe3e03be3e0d7021acd9cd848e44db26`) selects `leanprover/lean4:v4.30.0-rc2`;
- `backends/lean/lake-manifest.json` (blob `1a5af703163d8b39f4311aafe22ae171788179ee`) records the concrete package closure, including Mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.

**Direct Anneal packaging source.** `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `anneal/flake.nix` (blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`), selects Lean `v4.30.0-rc2`, maps Linux/macOS x86-64/AArch64 to upstream archive names, and fixes each unpacked toolchain with a platform-specific recursive SHA-256.

**Published exact-pin reference evidence.** Current `google/zerocopy` reference state `cd752204337905e7c9430ea6cba573cbaa49b4a9` contains focused reports used by this checklist for:

- `.olean` format/identity and Lake trace/hash boundaries;
- trust/admission mechanisms;
- server tactic-state queries and environment invalidation;
- termination checking and partiality boundaries;
- `simp`/`simp_all`, `grind`, and `omega` proof automation;
- Lake dependency resolution;
- package-native artifact handling;
- compilation determinism;
- CLI/environment selection; and
- diagnostic object/severity semantics.

`source-map.json` records the exact report blobs. These reports in turn preserve their exact pinned Lean implementation evidence; this checklist composes their version-sensitive conclusions rather than claiming fresh execution.

**Derived checklist.** `upgrade-checklist.json` turns those independent boundaries into twelve gates. The ordering is deliberate: identify the toolchain and package graph first; then revalidate logical, generated-code, proof, build, interactive, and platform behavior; then run the integrated path. A failure early in the graph can make later execution evidence uninterpretable or wasteful.

## Revalidation

When Anneal considers a new Lean release, copy `upgrade-checklist.json` and attach evidence to each applicable gate.

A narrow efficient sequence is:

1. **Resolve identities.** Record the Lean tag/commit, every platform archive/digest, Anneal selection, Aeneas `lean-toolchain`, and the locked Lake package graph. Stop if the intended graph is inconsistent.
2. **Diff the high-risk semantic boundaries.** Review trust/admission, recursive-definition/partiality, module serialization/invalidation, diagnostic/server protocol, and the proof automation Anneal actually uses. Use the focused source-map reports to avoid a repository-wide rediscovery pass.
3. **Run the fixed generated-Lean corpus.** Check elaboration, imports/names, representative proofs, expected failures, and theorem axiom sets under the exact new closure.
4. **Rebuild or explicitly validate prepared state.** Default to a clean build after a Lean change. If Anneal needs cache reuse, prove the narrower artifact/cache equivalence it depends on with preserved probes.
5. **Replay interactive specimens when relevant.** Open/edit/wait/query/restart a generated proof document and compare the protocol fields Anneal consumes.
6. **Run the packaged end-to-end path on required platform classes.** Use the archive, relocation/read-only layout, dependency tree, and invocation environment that Anneal will ship.
7. **Preserve the upgrade result.** Record exact commands, revisions, archive hashes, dependency manifests, generated inputs, outputs, diagnostics/protocol transcripts, and intentional compatibility changes.

If only one layer changed, rerun the smallest set of gates that transitively depends on it. For example, a Mathlib-only lockfile change need not imply a new `.olean` format investigation, but it does require proof/dependency and generated-project revalidation. A Lean revision change reaches many more gates because Lean owns the parser/elaborator, kernel-facing checking path, server, Lake implementation, and module artifact format in this environment.
