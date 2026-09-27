# Aeneas release upgrade checklist for Anneal

## Summary

Changing Anneal's Aeneas release is not a single-version substitution. At the current baseline, Aeneas `nightly-2026.06.03` resolves to `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`; that source pins Charon `a535e914f74db4fd9e6be7048f4233270d8945c0`, whose rustc-private driver pins Rust `nightly-2026-05-31`; the Aeneas Lean backend pins `leanprover/lean4:v4.30.0-rc2` and a concrete Lake dependency closure. Current Anneal independently packages the matching May 31 Rust and Lean `v4.30.0-rc2` environment around the Aeneas release.

An Aeneas upgrade can therefore change several proof-relevant interfaces even when the `aeneas` executable still starts: the Charon producer and Rust compiler, LLBC serialization and transformations, accepted Rust subset, warning/error boundary, functionalization semantics, generated Lean names and signatures, external models, proof library, termination treatment, logical assumptions, output determinism, and release-archive layout. The upstream release workflow's final smoke test is only `./aeneas --help`; that is useful packaging evidence but does not exercise those boundaries.

For Anneal, the minimum durable upgrade unit is the **resolved toolchain graph plus discriminating end-to-end evidence**, not the Aeneas nightly label. A candidate upgrade should not be treated as revalidated until each applicable gate in `upgrade-checklist.json` is either demonstrated unchanged or reviewed as an intentional semantic change. In particular, same-date Aeneas and Charon tags are not a compatibility contract, adjacent Aeneas nightlies do not preserve generated Lean as an interface, Lean acceptance does not certify Rust-to-Lean semantic preservation, and upstream checked-in generated tests use `-sequential` even though normal generation defaults to parallelism.

This report is a revalidation checklist. It does not claim that a hypothetical newer release passes any gate.

## Applicability

The baseline is current Anneal source at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` and the Aeneas release it selects, `nightly-2026.06.03`. The release tag resolves to Aeneas commit `ac9f1bc5262a5e4ff1e24ca78617121382202727`.

At that Aeneas revision:

- `charon-pin` and the locked `charon` flake input both select `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`;
- that Charon revision pins Rust `nightly-2026-05-31`;
- `backends/lean/lean-toolchain` selects `leanprover/lean4:v4.30.0-rc2`;
- `backends/lean/lake-manifest.json` pins Mathlib to `5450b53e5ddc75d46418fabb605edbf36bd0beb6` and records the remaining Lean package closure.

Current Anneal's Nix assembly independently selects Aeneas `nightly-2026.06.03`, Rust date `2026-05-31`, and Lean `v4.30.0-rc2`. The agreement is material because Charon's driver uses rustc-private APIs and because generated Aeneas Lean is elaborated in a concrete Lean/Lake environment.

The checklist is intended for replacing the Aeneas release used by Anneal or changing an equivalent part of that release graph. It is not a general Aeneas release-engineering checklist and does not require every upstream test when a narrower discriminating test establishes the Anneal-specific property. Conversely, a passing upstream release build does not waive an Anneal-specific gate.

## Findings

### 1. Resolve identities before comparing behavior

The first upgrade artifact should be a complete immutable identity graph:

`Anneal revision → Aeneas release tag → Aeneas commit → Aeneas-pinned Charon commit → Charon Rust toolchain`

and separately:

`Aeneas commit → Lean toolchain → Lake manifest revisions`.

The current baseline demonstrates why labels alone are insufficient. Aeneas `nightly-2026.06.03` pins Charon `a535e914…`, while Charon's own same-date `nightly-2026.06.03` tag denotes a different Charon commit. The published compatibility report also establishes that those two Charon revisions can share version `0.1.210` while differing in source history.

For a proposed release, resolve the tag, record the exact platform artifact digests actually consumed by Anneal, and derive the transitive pins from the resolved source. Do not infer a Charon or Rust identity from dates.

Basis: **source** (`charon-pin`, `flake.lock`, Charon `rust-toolchain`, Aeneas Lean toolchain/manifest, Anneal `flake.nix`) + published exact-revision **derived** compatibility analysis.

### 2. Revalidate the producer/compiler boundary as one unit

Aeneas consumes LLBC produced by Charon, and the selected Charon executable is coupled to a particular rustc-private toolchain. At the baseline, Charon `a535e914…` embeds `nightly-2026-05-31`; current Anneal deliberately supplies the matching managed Rust environment when invoking its bundled Charon.

An upgrade must therefore answer two questions together:

1. Which Charon revision is the intended LLBC producer for the new Aeneas?
2. Which compiler/toolchain must that Charon run against?

At minimum, require `charon-pin` and the locked Charon input to agree, read the pinned Charon `rust-toolchain`, and verify that Anneal's actual invocation path supplies that compiler. If Anneal later uses its independently declared `charon_lib`, that is a distinct producer/consumer compatibility edge and must be checked explicitly.

A successful `aeneas --help` says nothing about this edge.

Basis: **source** + the published Charon-toolchain and Aeneas–Charon compatibility reports.

### 3. Treat LLBC compatibility as semantic, not merely syntactic versioning

Aeneas's reader and Charon's serializer are a versioned boundary, but an equal Charon version string is not a proof that two producer revisions are semantically interchangeable. The baseline compatibility investigation found identical parser/serialization definitions across two nearby Charon revisions while also finding translation changes elsewhere.

For an upgrade, diff the LLBC schema/version machinery and transformation pipeline, then run at least one preserved LLBC specimen through the intended consumer. For stronger coverage, preserve a compact set of LLBC specimens covering the constructs Anneal depends on. If the Charon producer changes, regenerate those specimens from fixed Rust inputs and review both structural and semantic differences.

The relevant question is not merely "does it deserialize?" but "does the produced LLBC preserve the Rust behaviors on which the proof relies?"

Basis: published exact-revision **source** analysis of the Aeneas/Charon compatibility and translation-correctness boundaries.

### 4. Re-pin the Lean environment, not just Aeneas

The Aeneas Lean backend is part of the executable proof environment. The baseline pins Lean `v4.30.0-rc2` and a concrete Lake manifest whose direct Mathlib revision is `5450b53e…`. Changes to Aeneas can change its Lean toolchain, Mathlib closure, generated imports, proof tactics, or model library without changing the Rust-facing CLI.

For every upgrade:

- read `backends/lean/lean-toolchain`;
- record the exact Lake manifest revisions;
- compare Anneal's packaged Lean with the Aeneas expectation;
- rebuild/load the generated project with that exact environment;
- diff proof-support modules used by Anneal's annotations or generated specifications.

A generated file compiling under some nearby Lean version is not equivalent evidence.

Basis: **source** at the selected Aeneas revision + current Anneal packaging source.

### 5. Check the release artifact that Anneal will actually ship

The current Aeneas release workflow builds four platform archives, precompiles the Lean library, repackages the tree, and performs a final smoke test that extracts the archive and executes `./aeneas --help`. That smoke test demonstrates that one executable can start in the packaging environment. It does not exercise bundled Charon, LLBC translation, the generated Lean project, Mathlib artifacts, relocation, or Anneal's runtime environment construction.

An Anneal upgrade should inspect the exact archive layout on every supported platform and execute a small real translation from the unpacked archive. The minimum artifact-level test should invoke the bundled Charon, invoke Aeneas on its output, and elaborate the result using the packaged/prepared Lean environment. Platform-specific linkage and relocation failures belong here rather than being inferred away from Linux-only success.

Basis: Aeneas release-workflow **source** + Anneal packaging **source**.

### 6. Rebuild the supported-input and fail-closed matrix

The baseline support report establishes a three-layer boundary: Charon must translate under the Aeneas preset, Aeneas must functionalize the LLBC, and the Lean backend/models must accept the result. It also distinguishes hard errors from warnings and semantic abstractions.

That matrix is revision-sensitive. A new release can turn a failure into support, support into a warning, or a warning into accepted-but-different generated code. The upgrade review should diff the relevant limitation/error paths and run a compact matrix that includes successful constructs, known failures, and warning-only hazards. Run it under the flags Anneal intends to use, not only upstream test defaults.

For a fail-closed integration, the upgrade evidence must establish that promise-relevant unsupported constructs cannot silently become accepted proof input. Registered translation errors should remain nonzero-status failures, and the policy for warnings must be explicit.

Basis: published Aeneas support/failure **source** analysis.

### 7. Treat generated Lean as a revision-sensitive interface

Checked-in Aeneas history around the current nightly already shows that unchanged Rust fixtures can produce changed generated Lean after a Charon/toolchain update. Nearby releases can also keep sampled generated files byte-identical while changing the surrounding proof library. Those are two distinct compatibility dimensions.

For a proposed upgrade, regenerate representative fixtures from fixed inputs and compare:

- relative file set;
- declaration and namespace names;
- generated function signatures;
- forward/backward function structure for borrows;
- recursion/loop representation;
- imports and external-model references;
- theorem/proof-library dependencies.

A textual diff is necessary when existing annotations or proofs refer to generated names, but it is not sufficient. Review semantic and proof-environment changes separately.

Basis: published adjacent-release **source/history** analysis plus the current generated-function/specification corpus.

### 8. Revalidate model semantics and theorem-specific trust

Aeneas maps external Rust definitions into a revision-specific Lean model registry. At the current pin, model entries can change type parameters, failure behavior, lifting into `Result`, mutable-region handling, variants, fields, and opacity. A name match therefore carries semantic content; it is not only a pretty-printer mapping.

The current Aeneas Lean library also contains explicit axioms and `sorry`-derived assumptions, and Aeneas can emit admissions while recovering from extraction errors. Lean checks proofs about the generated Lean program, but it does not itself establish that the models or the translation faithfully denote Rust.

An upgrade must therefore diff the model registry and explicit trust-expanding constructs. For representative final theorems, record transitive axiom dependencies and compare them with an explicit allowlist. New model axioms or `sorryAx` dependencies require review even if all files compile.

Basis: published external-model, trusted-base, and translation-correctness **source** analyses.

### 9. Recheck recursion, divergence, and termination paths

Termination is especially sensitive to cross-version composition. The current corpus distinguishes partial translated semantics from proof-time termination arguments and records a source-level incompatibility between Aeneas's translation-time decreases-clause emission and Lean `v4.30.0-rc2` termination-suffix grammar.

A future Aeneas or Lean change can legitimately fix or redesign that path. The upgrade checklist must therefore revalidate recursive functions, loops, `partial_fixpoint`, `Result.div`, WP/specification behavior, and any generated decreases clauses against the exact Lean grammar selected by the release.

Do not infer that a fixed generator makes every translated program total, or that proof-time termination changes the semantics of the underlying partial generated function. Preserve the distinction in upgrade evidence.

Basis: published Aeneas recursion/loops/extrinsic-termination **source** analyses.

### 10. Separate same-revision determinism from adjacent-release stability

Two questions often collapse during upgrades:

- Does the same Aeneas revision produce the same bytes repeatedly from identical inputs?
- Does a different Aeneas revision preserve the same generated interface?

They require different evidence. The baseline determinism report identifies several implementation safeguards but also finds that upstream golden generation forces `-sequential`, while normal Aeneas translation defaults to parallel execution. It therefore leaves byte-for-byte determinism of the default parallel path unproven.

If Anneal uses generated bytes as cache identity or expects clean rebuild equivalence, the proposed release must receive an exact production-mode repeated-run probe. Separately, compare the new release's output with the old release for migration impact. A deterministic new generator can still produce intentionally incompatible output.

Basis: published generated-source-determinism and adjacent-release-stability analyses.

### 11. End with a compact end-to-end corpus, not a collection of component checks

The final gate should exercise the composition Anneal actually relies on. A compact corpus should include at least:

- scalar/ADT control cases;
- shared and mutable borrowing, including a nested-borrow case;
- an ordinary loop and a recursive function;
- a trait/model-dependent case;
- a case that is expected to fail;
- a proof whose axiom set is intentionally small and auditable.

For each fixture, preserve the Rust input, Charon/LLBC identity, Aeneas command/configuration, generated Lean tree, Lean result, and final theorem axiom set. If the production path is parallel, perform the reproducibility repetitions in that mode. If Anneal packages a prepared read-only toolchain, run the fixture through that packaged environment rather than an upstream development checkout.

Component source review remains valuable because an end-to-end corpus cannot prove complete semantic preservation. The two forms of evidence are complementary: source review locates changed obligations; the corpus catches concrete integration regressions.

Basis: **derived** from the independent upgrade-sensitive boundaries established by the current reference corpus.

## Boundaries

- No newer Aeneas release was selected or evaluated. This report defines what must be revalidated; it does not approve an upgrade.
- No fresh Charon, Aeneas, Rust, Lean, Lake, Nix, or release-archive execution was performed for this report.
- The checklist is not a proof of translation correctness. Passing it provides regression and integration evidence around a separately trusted or justified source-to-target bridge.
- The checklist intentionally does not require byte-identical generated Lean across releases. A reviewed semantic/interface change can be acceptable. It does require that Anneal not accidentally depend on an unreviewed change.
- The checklist does not assume support is monotonic. A newer release can add support, remove support, change a warning boundary, or change a model.
- The upstream release workflow may change. Its current `aeneas --help` smoke-test limitation is baseline evidence, not a permanent claim.
- The exact set of discriminating fixtures should evolve with Anneal's supported Rust subset. The categories above are a floor, not a claim of exhaustive language coverage.
- A package-wide search for axioms or `sorry` is not a theorem-specific trust audit. The final theorem's transitive dependency set remains the relevant logical-assumption evidence.
- The machine-readable checklist is an aid to revalidation. It does not override current Anneal authority, issue state, or a newer report about a newer precisely identified subject.

## Evidence

**Direct Aeneas source.** `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`:

- `charon-pin` (`06dbe0db…`) selects Charon `a535e914…`;
- `flake.lock` (`d6862b6e…`) locks the same Charon revision;
- `backends/lean/lean-toolchain` (`6c7e31ff…`) selects `leanprover/lean4:v4.30.0-rc2`;
- `backends/lean/lake-manifest.json` (`1a5af703…`) records the concrete Lean package closure, including Mathlib `5450b53e…`;
- `.github/workflows/release.yml` (`e248e9fd…`) defines the four-platform release build, Lean precompile, repackaging, and final `aeneas --help` smoke test.

The Git tag `nightly-2026.06.03` resolves to the Aeneas commit above.

**Direct Charon source.** `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, `charon/rust-toolchain` (`3c98116a…`), pins `nightly-2026-05-31` with the rustc-private components used by the driver.

**Direct Anneal source.** `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `anneal/flake.nix` (`433fcf5c…`), selects Aeneas `nightly-2026.06.03`, Rust date `2026-05-31`, and Lean `v4.30.0-rc2`, and constructs the packaged Aeneas/Rust/Lean environment.

**Published reference synthesis.** Current `google/zerocopy` reference commit `06fd273adf6ebcf860466cb0a1d50e26e6729cfe` supplies exact-subject reports for:

- Aeneas–Charon compatibility;
- Charon Rust-toolchain requirements;
- Aeneas architecture/translation pipeline;
- generated Lean stability across nearby releases;
- generated-source determinism;
- Rust support/failure behavior;
- translation-correctness obligations;
- external-model semantics;
- recursion, loops, and extrinsic termination;
- trusted-base and theorem-assumption boundaries.

`source-map.json` records the exact report paths/blobs used where material.

**Derived checklist.** `upgrade-checklist.json` converts those independent version-sensitive findings into eleven gates. The gate ordering is derived: establish immutable identity first, then producer/checker environments, then semantic/interface/trust/reproducibility behavior, and only then accept integrated evidence. The ordering avoids spending integration effort on an upgrade whose basic toolchain graph is already inconsistent.

## Revalidation

When Anneal considers a new Aeneas release, copy `upgrade-checklist.json` and record the proposed release's evidence against each gate.

A narrow efficient sequence is:

1. **Resolve and diff identities.** Record the new Aeneas commit, platform assets/digests, Charon pin/lock, Charon Rust toolchain, Lean toolchain, and Lake manifest. Stop if the graph is internally inconsistent.
2. **Diff high-risk source boundaries.** Review LLBC serialization/reader code, Aeneas error/support paths, functionalization passes, generated Lean extraction, model registry, recursion/termination code, and explicit trust-expanding constructs.
3. **Build an interface diff.** Regenerate the compact corpus from fixed inputs and compare LLBC, generated Lean, and proof-library dependencies against the current baseline.
4. **Run production-mode repetitions.** Establish byte-level determinism only if Anneal depends on it, using the exact concurrency and path environment Anneal will deploy.
5. **Run the packaged end-to-end corpus.** Exercise the exact archive and Anneal environment on every supported platform class needed by the release, require expected success/failure status, elaborate generated Lean, and audit representative final theorem axioms.
6. **Preserve the result.** Record commands, immutable revisions, artifact hashes, output trees, diagnostics, and any intentional compatibility break. Update the baseline only after the changed behavior is understood rather than merely because all executables started.

If only one transitive pin changed, do not automatically rerun unrelated research. Use the source map and current reports to identify which gates depend on that pin, then rerun the smallest probes that discriminate the affected behavior. If a changed source region crosses multiple gates—for example, a Charon update that changes LLBC and generated Aeneas output—revalidate the union rather than treating each repository version independently.
