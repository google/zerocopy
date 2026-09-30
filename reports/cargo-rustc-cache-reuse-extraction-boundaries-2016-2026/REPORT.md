# Cargo, rustc, and compiler-cache reuse: when a fresh build is not fresh extraction

## Summary

Cargo freshness, rustc incremental reuse, and compiler-wrapper caching answer different questions. Cargo decides whether a build unit needs to run at all. rustc, once invoked, can reuse compiler-internal query results from an earlier session. A wrapper cache such as sccache can intercept an invocation and return ordinary compiler outputs without executing rustc. Each layer is useful because it can avoid work, but each is sound only relative to the outputs and dependencies that its own contract models.

That distinction matters for Anneal because Charon's LLBC is not an ordinary Cargo output. The selected Charon frontend deliberately piggy-backs on Cargo by installing `charon-driver` as `RUSTC_WRAPPER`; the driver enters rustc, reads compiler state, translates the selected crate, and serializes LLBC outside Cargo's normal artifact contract. If Cargo considers a unit fresh, the wrapper need not run. If another wrapper answers from a compiler cache, the underlying compiler need not run. Neither event, by itself, establishes that a current LLBC side product was produced for the intended Anneal subject.

The useful boundary is therefore not “disable caches” versus “trust caches.” Anneal can retain ordinary Cargo, rustc, and compiler-cache reuse beneath extraction, but it needs a separate semantic-output contract above them. A reusable extraction result should have an explicit identity or receipt that covers the Rust compilation subject, effective compiler and translation configuration, tool identities, and the produced semantic artifact. When that receipt matches the requested generation, reuse is legitimate. When it does not, Anneal must cause the extraction-producing action to execute or restore an extraction artifact from a cache that treats that artifact and its key as first-class data. A successful ordinary build or cache hit is not a substitute.

## Applicability

This report addresses #3732 J048. It compares current Cargo fingerprinting and wrapper behavior at `rust-lang/cargo@f3865b2a4d1acc5276f6b3c67d0e057f4dab3928`, current rustc incremental architecture as documented for `rust-lang/rust@7d2cd0fbc092625ea371da704f15f80216d2220e`, current sccache documentation at `mozilla/sccache@54b6f72a5d3583e8ccb8b83d44e5d41400d8039c`, the Charon version selected by Anneal at `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, and Anneal's design contract at `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`.

The historical comparison uses Cargo's public 1.50 changelog for the 2021 introduction of `RUSTC_WORKSPACE_WRAPPER` and Rust's 2016 incremental-compilation design account. These sources establish design evolution and stated rationale, not a complete commit-by-commit history.

No fresh Cargo, rustc, sccache, or Charon execution was performed for this report. Existing `reference` execution reports supply adjacent evidence about Cargo input closure and Charon invalidation, but the judgments here come primarily from source and first-party documentation. The report distinguishes those roles below.

The report is specifically about *semantic side products of an instrumented compilation*: outputs such as Charon LLBC that exist because a compiler wrapper or callback ran. It does not imply that all compiler plugins, wrappers, code generators, or caches have identical behavior. The general conclusion applies only when a side product is outside the freshness or cache contract that decides whether the producing action runs.

## Findings

### “Up to date” is relative to an output contract

Cargo's fingerprint module defines freshness for a Cargo `Unit`. A missing fingerprint makes a unit dirty; changes in fingerprint fields or dependency fingerprints can make it dirty; source and dependency mtimes are also checked by the default mechanism, with an unstable checksum-based alternative. Cargo writes the updated fingerprint only after the unit finishes successfully.

The same source explicitly says this mechanism is a compromise rather than a complete observation of the process environment. It captures only part of the environment and notes that sandboxing or tracking every file access, environment variable, and network operation would be more complete but also more complex, slower, and platform-dependent. Cargo therefore gives a useful build-system guarantee: under the inputs its fingerprint logic models, the ordinary outputs of a fresh unit need not be rebuilt. It does not claim that every side effect of every process that might have run during a dirty build remains present or current.

Cargo's own history reinforces that cache identity is an evolving engineering contract. The fingerprint source records inputs that have been added or removed over time and explains why values such as absolute paths or raw modification times should not be part of the hash. Cargo 1.50, released 2021-02-11, added `RUSTC_WORKSPACE_WRAPPER` specifically with an artifact-identity rule: artifacts built through that workspace wrapper are cached independently of non-wrapped builds. Current documentation still says the workspace-wrapper path affects the filename hash. Cargo 1.79 later changed the initial compiler probe so configured wrappers also apply to the `rustc -vV` invocation. These are examples of wrapper and cache semantics changing as Cargo's model evolves.

Basis: current Cargo **source** + Cargo **documentation** + Cargo release-history **documentation**.

### Cargo can skip the compiler-wrapper action completely

Cargo calculates unit freshness before it schedules the compilation job. A fresh unit therefore does not need a compiler invocation merely to reconfirm the existing outputs. This is the intended benefit of the build cache.

That is enough to create a semantic distinction for instrumentation. Suppose a wrapper normally does two things during a dirty build:

1. it allows the compiler to produce the ordinary Cargo artifacts; and
2. it emits an additional semantic artifact in some other location.

If the next Cargo invocation classifies the unit as fresh, neither the compiler nor the wrapper needs to run. Cargo may still correctly report the build as fresh even if the wrapper's additional artifact has been deleted, was produced under different wrapper options, or was never part of Cargo's output set. The build and the side product have different contracts.

This is not a Cargo bug. The side product is outside the question Cargo was asked to answer unless the integration makes it a first-class tracked output or otherwise changes the build identity so that the producing action must run.

Basis: Cargo **source** + **derived** consequence of wrapper-based side effects.

### Wrapper selection has explicit artifact-identity rules, but those rules are not a general side-effect protocol

Cargo exposes two related wrapper mechanisms. `RUSTC_WRAPPER` wraps rustc generally. `RUSTC_WORKSPACE_WRAPPER` wraps workspace-member compilations, and current Cargo documentation states that it changes the filename hash so wrapper-produced workspace artifacts are cached separately from non-wrapped builds. If both are set, Cargo nests them as:

```text
$RUSTC_WRAPPER $RUSTC_WORKSPACE_WRAPPER $RUSTC
```

The 2021 addition of the workspace-specific wrapper was therefore not merely a convenience for launching another executable; it also supplied a namespace distinction for ordinary artifacts.

That mechanism is valuable for instrumented compilation, but it does not turn arbitrary wrapper side effects into Cargo outputs. In particular, a distinct filename hash says which ordinary artifacts can coexist; it does not attest that an out-of-band LLBC file exists, matches those artifacts, or was created by the requested translation options. A side-product integration still needs an explicit relation between the build identity and the side product.

The nesting rule also means wrapper composition is architectural state. A Charon wrapper, a cache wrapper, and any workspace-only instrumentation do not become safely composable merely because each works alone. Which wrapper is outermost determines which process can observe a cache hit, which process actually reaches rustc, and which side effects execute.

Basis: Cargo **documentation** + **derived** integration analysis.

### rustc incremental reuse begins after rustc has been invoked

rustc's incremental system solves a different problem. It decomposes compilation into queries and persists enough dependency information and result fingerprints to reuse work across compiler sessions. The red-green algorithm can mark a query green without rerunning it when its dependencies remain green; when a dependency changes, rustc may rerun a query and still discover that its result fingerprint is unchanged.

This means “rustc ran” does not imply “rustc recomputed every semantic fact.” That is intentional. The compiler's contract is that the reused query graph represents the current compilation under the dependencies rustc tracks, not that every internal computation executed anew.

The mechanism has its own hidden cost. Query-result fingerprints must be stable across sessions, dependency information must be persisted and loaded, and results must be hashed. The rustc development guide explicitly calls hashing a major source of incremental-compilation overhead and notes the theoretical possibility of hash collisions. The 2016 design account frames the tradeoff directly: retain intermediate results so unchanged computations can be skipped after an edit.

For Anneal, this is normally a lower-layer implementation detail rather than a reason to demand a cold compiler. If Charon actually enters the current rustc session and reads current MIR through supported callbacks, rustc may satisfy some compiler queries incrementally. Anneal need not equate “recomputed from scratch” with “fresh semantic output.” What it needs is evidence that the *extraction result* belongs to the requested compilation subject and current tool/configuration generation.

Basis: rustc **documentation** + historical Rust **documentation** + **derived** Anneal judgment.

### sccache can skip rustc, so its cache key becomes the compiler-output contract

sccache moves the reuse boundary outward. It is a compiler wrapper that can answer a compiler invocation from cached outputs instead of executing the compiler. Its Rust cache key includes the source digest, rustc path, host triple, sysroot path, digests of shared libraries in the sysroot, rlib dependencies, and parsed rustc arguments. This is a much more explicit input model than simply keying by a source pathname.

The same first-party documentation lists important boundaries. Rust invocations must have particular output forms to be cacheable. rustc incremental compilation must be disabled. Crates that invoke the system linker are not cached. The documentation also warns that procedural macros which read files from the filesystem may not be cached properly. These caveats illustrate the general rule: a transparent cache is only as sound as the dependencies its key models and the outputs it stores.

For ordinary supported rustc outputs, that can be an excellent contract. For an unrelated wrapper side effect, it is insufficient. A cache hit that restores an `.rlib` or metadata file but never executes the process that writes LLBC has done exactly what its compiler-cache contract requires while failing to produce the semantic side product Anneal needs.

A first-class semantic cache would be different. If it stores LLBC itself, keys that LLBC by a sufficient translation identity, restores it atomically, and records provenance that Anneal can validate, then a cache hit can satisfy the extraction contract without executing Charon. The important distinction is not cache versus no cache; it is whether the semantic artifact is part of the cache's declared value and key.

Basis: sccache **documentation** + **derived** side-product analysis.

### Charon's current Cargo integration demonstrates the side-product problem directly

The Charon revision selected by Anneal explains why it piggy-backs on Cargo: Cargo already knows the complicated rustc arguments and the hashed paths to compiled dependencies. `charon cargo` therefore launches Cargo as a build while setting `RUSTC_WRAPPER` to `charon-driver` and passing Charon options through an environment variable.

`charon-driver` runs for compiler jobs that Cargo actually dispatches. For the selected target crate it configures rustc for translation, disables normal code generation, enters rustc through callbacks, translates compiler state to Charon's representation, and stops after analysis. Charon then serializes the resulting translated crate as LLBC.

The crucial ownership boundary is therefore:

```text
Cargo unit freshness
    decides whether a rustc/wrapper job runs

Charon driver invocation
    produces the semantic translation

LLBC serialization
    publishes Charon's side product
```

Cargo does not thereby acquire an obligation to prove that a particular LLBC file is current. Charon is intentionally using Cargo to obtain compilation context, not extending Cargo's fingerprint schema with an LLBC result contract.

Existing Anneal reference work has already identified this as an upgrade-sensitive boundary. The interactive invalidation report explicitly says Cargo/rustc incremental compilation should not be treated as an Anneal semantic cache and that the current evidence does not prove, for every edit, when Cargo will invoke or skip Charon's wrapper. J048 sharpens the reason: wrapper dispatch and semantic-output freshness must be related explicitly rather than inferred from a successful Cargo command.

Basis: pinned Charon **source** + existing Anneal reference **execution/source synthesis** + **derived** composition.

### Normal build artifacts and instrumented side products need separate freshness predicates

The following table separates the contracts that can otherwise be conflated.

| Layer | Reuse decision | Value whose reuse is justified | What it does **not** automatically establish |
| --- | --- | --- | --- |
| Cargo unit freshness | Fingerprint, dep-info, source/dependency freshness, configured inputs | Cargo's ordinary outputs for that unit | That an arbitrary wrapper callback ran or an out-of-band semantic file exists/currently matches |
| rustc incremental | Query dependency graph and stable result fingerprints | Compiler-internal query/codegen work in a current rustc invocation | That an external extraction side product was published for this request |
| sccache-style compiler cache | Cache key over modeled compiler/source/argument/environment inputs | Cached supported compiler outputs | That nested/underlying instrumentation executed on a cache hit |
| Charon extraction | Current selected compiler invocation plus Charon translation options and callbacks | LLBC/ULLBC produced by that translation | By itself, long-term identity, freshness fencing, or publication ownership across requests |
| Anneal semantic reuse | Must be defined by Anneal/integration | A previously accepted semantic artifact for a precisely identified subject/environment/tool generation | Nothing stronger than the identity and evidence recorded in that semantic contract |

The mistake to avoid is importing a lower layer's notion of freshness as proof of the upper layer's artifact freshness.

Basis: preceding **source/documentation** findings + **derived** synthesis.

### Five integration strategies occupy different points in the cost/soundness space

**Always rebuild from a clean state.** Anneal could isolate every extraction in a fresh target tree and disable all reusable state. This makes the causal story simple, but it throws away useful dependency builds and compiler work. It also does not automatically make the wider environment hermetic: build scripts, procedural macros, native libraries, environment variables, and network access can still be hidden inputs unless separately controlled.

**Trust Cargo freshness or a compiler-cache hit.** This is cheapest, but insufficient for a semantic side product. It proves only that the lower layer accepted its own outputs as reusable.

**Use an instrumented build namespace.** A dedicated target directory or workspace-wrapper identity can prevent instrumented and ordinary build artifacts from silently sharing one output namespace. This reduces collisions and accidental cross-use. It still needs a semantic receipt because the extra artifact can be deleted, options can change, and a lower-level cache can still elide the process that would emit the side effect.

**Make the semantic artifact a first-class cached value.** This is the strongest reuse design. Key the semantic output by the effective compilation subject, compiler/toolchain identity, translation-tool identity and options, and every other material input that the integration can justify. Store the semantic artifact and its provenance together. A validated cache hit then *is* an extraction result rather than an inference from an unrelated build result. The cost is maintaining a sound key and migration story as tools evolve.

**Force only the extraction-producing action while reusing lower layers.** Anneal can permit Cargo to reuse dependencies and rustc to reuse compiler-internal work while ensuring the selected target reaches the extraction driver when no valid semantic receipt exists. This keeps most performance benefits without treating the ordinary build cache as semantic authority. The exact mechanism may be a dedicated wrapper mode, a private build identity, direct `charon rustc`, a targeted invalidation, or a future supported Charon service. The mechanism should follow the contract rather than define it accidentally.

Basis: **derived** comparison constrained by current Cargo, rustc, sccache, Charon, and Anneal contracts.

### Anneal should accept semantic reuse through an explicit extraction receipt

Anneal's design contract requires successful verification to identify the program or behavior to which it applies and forbids reporting a stronger promise than the evidence supports. The cache boundary should preserve the same discipline.

A minimally sufficient extraction receipt should identify at least:

- the Rust compilation subject: package/target plus effective feature, cfg, target, profile, compiler-argument, generated-source, build-script/procedural-macro, and dependency state to the extent that they can affect translation;
- the exact rustc/toolchain and Charon identities;
- Charon options and any configuration that changes the translated model;
- the semantic artifact identity, such as a digest of the LLBC bytes or a stronger structured identity;
- the causal generation or request that produced or restored it; and
- the preparation/environment identity needed to interpret the subject consistently.

The list is a requirement on *meaning*, not a mandate for one giant serialized key. Existing Cargo and Charon mechanisms may supply parts of it. Anneal can use a compositional identity whose components are produced by the owning layers rather than duplicating every dependency itself.

On a request, the orchestration rule can then be simple:

1. If a prior semantic result has a receipt that is valid for the exact requested subject/tool/configuration generation, reuse it.
2. Otherwise, ensure the extraction-producing action executes or a first-class semantic cache restores the requested result.
3. Validate and record the resulting semantic artifact before later proof stages or final publication can rely on it.
4. Keep ordinary Cargo/rustc/sccache reuse enabled wherever it does not undermine that semantic-output predicate.

This makes “fresh” evidence-based rather than process-based. A brand-new compiler process is neither necessary nor sufficient; an accepted semantic artifact with a valid identity is the object Anneal actually needs.

Basis: Anneal **normative project design** + current tool **source/documentation** + **derived** judgment.

### Cache correctness and publication correctness remain separate

Even a perfect extraction cache answers only “does this semantic artifact correspond to these inputs?” It does not settle whether this request is still the current user-visible generation, whether a concurrent edit superseded it, or whether the artifact may be published as the result for a newer subject.

Anneal therefore needs two fences:

- **semantic freshness**: the artifact corresponds to the identified compilation and translation inputs;
- **publication freshness**: the request is still authorized to make that artifact current after any concurrent changes.

The current reference corpus already uses this distinction for interactive generations. J048 adds that a compiler cache belongs below the semantic-freshness fence; it should not become a publication oracle.

Basis: existing Anneal reference **source/execution synthesis** + **derived** architecture judgment.

## Boundaries

No fresh execution was performed, so this report does not measure cache-hit rates, compile-time savings, incremental hashing overhead, or the latency cost of forcing Charon to run. It gives no quantitative threshold for when semantic caching is worth its implementation cost.

The report does not claim that current rustc incremental reuse can return stale compiler state when rustc's own dependency assumptions hold. If the selected Charon driver actually runs in the requested rustc session, compiler-internal reuse can be a valid implementation detail. The separate concern is whether that Charon invocation happened and whether the resulting LLBC is identified as the requested artifact.

The report does not claim that `RUSTC_WRAPPER` and `RUSTC_WORKSPACE_WRAPPER` have identical artifact-key behavior. Current Cargo documentation specifically assigns filename-hash separation to the workspace wrapper. Any design that depends on the exact fingerprint effect of the general wrapper should revalidate that behavior against the selected Cargo version instead of extrapolating from the workspace-wrapper rule.

sccache's documented Rust key is not treated as a proof of complete dependency capture. Its own documentation records unsupported or imperfect cases, including procedural macros that read filesystem data. Other compiler caches have different key schemas and capabilities and must be evaluated separately.

Cargo's fingerprint comments describe a pragmatic incomplete environment model. This report does not attempt to enumerate every omitted input, nor does it imply that an omitted input changes the specific Anneal/Charon subject. Whether an input is material depends on the compiler and translation behavior actually exercised.

The current Charon source establishes how its Cargo wrapper integration works at the pinned revision. It does not establish future Charon behavior, nor does it prove that a future Charon incremental/server mode should use the same receipt boundary.

A dedicated target directory or wrapper namespace reduces accidental cache aliasing but is not equivalent to hermetic execution. Build scripts, proc macros, native tools, environment state, filesystem reads, and other ambient inputs may still require independent capture or isolation.

The proposed extraction receipt is a derived architecture judgment, not adopted Anneal design policy. The exact subject identity, schema, storage system, and invalidation mechanism remain design choices.

## Evidence

**Cargo current implementation — `rust-lang/cargo@f3865b2a4d1acc5276f6b3c67d0e057f4dab3928`.**

- `src/compiler/fingerprint/mod.rs`, blob `ebaa5c34d2d8ff97baee0d86541ce3d96c6be5d4`: unit fresh/dirty contract, fingerprint inputs, dep-info behavior, mtime/checksum mechanisms, successful-build update rule, and the explicit completeness/performance tradeoff.
- `src/compiler/build_runner/compilation_files.rs`: `Metadata`/`UnitHash` output-separation machinery and the distinction between unit identity and rebuild fingerprinting.
- `src/util/rustc.rs`: compiler identity/fingerprint handling, including compiler executable metadata and rustup-related state.
- `doc/book/src/reference/config.md`: `build.rustc-wrapper`, `build.rustc-workspace-wrapper`, wrapper nesting, and workspace-wrapper filename-hash separation.
- Cargo Book changelog, Cargo 1.50 (`rust-1.50.0`, released 2021-02-11): addition of `RUSTC_WORKSPACE_WRAPPER` with independently cached artifacts, PR #8976.
- Cargo Book changelog, Cargo 1.79 (`rust-1.79.0`, released 2024-06-13): wrappers and `[env]` also apply to Cargo's initial `rustc -vV` probe, PR #13659.

**rustc incremental compilation — `rust-lang/rust@7d2cd0fbc092625ea371da704f15f80216d2220e`.**

- Rust Compiler Development Guide, “The rustc query system” / “Incremental compilation”: red-green dependency graph, persisted query fingerprints/results, marking green without reevaluation, stable hashing, cache promotion, and collision/cost discussion; observed 2026-09-30.
- Rust Blog, “Incremental Compilation,” 2016-09-08: original public rationale for decomposing compilation into reusable intermediate computations.

These are first-party **documentation**. This report did not pin a historical rustc implementation commit for the 2016 design.

**sccache — `mozilla/sccache@54b6f72a5d3583e8ccb8b83d44e5d41400d8039c`.**

- `docs/Caching.md`, blob `0f4ca650ef8af51bb30f813381d98859faf8ed13`: Rust cache-key inputs and compiler-cache key rationale.
- `docs/Rust.md`, blob `5d6f98c3cfc535fba674c49cbac7ae8149859f1f`: supported Rust invocation shape, procedural-macro filesystem caveat, requirement to disable rustc incremental compilation, linker restrictions, and `RUSTC_WRAPPER=sccache` integration.

These are project **documentation** rather than an independent proof that every relevant dependency is captured.

**Charon selected by Anneal — `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`.**

- `charon/src/bin/charon/main.rs`, blob `b4460ce4cd3baa32308718e79b6e194860b042a6`: rationale for piggy-backing on Cargo, `RUSTC_WRAPPER=charon-driver`, Cargo `build` orchestration, option transport, and final serialization.
- `charon/src/bin/charon-driver/driver.rs`, blob `3f90a7a31857aed462694066e5ffaa6e28b9dcfa`: selected-target detection, rustc callbacks, MIR-related compiler configuration, no-codegen mode, translation, and stop-after-analysis behavior.

These are pinned **source**.

**Anneal design authority — `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`.**

- `anneal/PRINCIPLES.md`, blob `d5339a95254eae14ac201139d07d9d36d48a19fb`: conditional verification promise and fail-closed principle.
- `anneal/DESIGN.md`, blob `0e8170979f3a466f2460c0ef7ec6d9a6b92650b8`: precise result identity/scope, evidence-bounded success, explicit trust, minimally sufficient mechanisms, and deliberate non-decision about component boundaries.

These files are the current project **normative design context** for the derived Anneal judgment.

**Adjacent published reference evidence.**

- `reports/anneal-3730-rust-input-snapshot-2026-09-29/REPORT.md`, blob `8d1ca9ff320e216be72abbca267c4372fcb8d0e1`: execution evidence that byte-identical main Rust source can compile differently when included files, Cargo feature selection, manifest defaults, or proc-macro-consumed attributes differ; also preserves an A→B→A ownership counterexample.
- `reports/anneal-interactive-pipeline-invalidation-graph-main-41f5b37/REPORT.md`: source/execution synthesis that keeps Cargo/rustc incremental reuse distinct from Anneal semantic caching and treats Charon wrapper invocation as an upgrade-sensitive boundary.

These reports are supporting evidence, not authority for the new J048 judgment.

## Revalidation

Revalidate the source boundary first. At the Cargo version Anneal actually uses, inspect the current fingerprint input table, wrapper configuration, workspace-wrapper output-hash behavior, and job scheduling path. At the Charon version Anneal selects, confirm whether Cargo still launches a wrapper, whether the selected target is translated only when that wrapper is invoked, and where semantic output is written. If Charon gains a server, persistent extraction cache, or explicit content identity, evaluate that new contract directly instead of carrying forward the wrapper assumptions.

Then run a small discriminating fixture. Use one workspace crate whose selected compiler wrapper writes both a normal compiler result and a uniquely identifiable semantic side file or receipt. Record Cargo's verbose/logged freshness decisions and every wrapper invocation. Exercise at least:

1. cold build;
2. unchanged second build;
3. delete only the semantic side product and rebuild;
4. change only extraction options carried outside ordinary rustc arguments;
5. change the workspace-wrapper path;
6. change the general wrapper path;
7. toggle rustc incremental mode;
8. place sccache outside the instrumenting wrapper, then inside it where supported;
9. force a compiler-cache hit after deleting the semantic side product;
10. change a procedural-macro-consumed external file that is not explicitly declared to Cargo; and
11. perform A→B→A input changes while retaining a stale receipt from the first A.

For each case, preserve the Cargo fingerprint explanation, actual process tree, compiler invocation arguments, ordinary output digests, semantic artifact digest, and receipt identity. Compare every accepted reused semantic artifact against a clean extraction under the same exact subject/tool/configuration identity.

The decisive assertion is not “the compiler ran.” It is: *the semantic artifact Anneal accepts is either freshly produced for this generation or restored under an explicit cache key whose identity is sufficient for the same claim.* Any proposed optimization should be rejected until the fixture demonstrates that assertion across the cache-hit and wrapper-elision cases it enables.