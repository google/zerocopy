# Aeneas incremental translation feasibility at nightly-2026.06.03

## Summary

Aeneas `nightly-2026.06.03` has useful declaration-local structure, but it does not expose an incremental translation protocol.

The public library gives an interactive host a stronger starting point than a file-only command. `Translate.translate_crate_to_pure` returns both the translation context and an in-memory pure translated crate. Function translation and the later pure micro-passes are already decomposed per function and can run in parallel. A host can therefore keep parsed LLBC and translated values alive instead of forcing every interaction through process startup and generated files.

That reuse is not the same as incremental recomputation. Every call to `translate_crate_to_pure` begins by constructing a fresh whole-crate context with `compute_contexts`. That step recomputes the crate-wide use graph, declaration membership, type analysis, and function analysis. The call then retranslates the selected types, globals, all selected function signatures and bodies, traits, and trait implementations before running micro-passes. No inspected API accepts a previous translation plus an edit set, computes invalidated declarations, or patches a prior translated crate.

The pre-pass and extraction stages add further whole-crate dependencies. `PrePasses.apply_passes` includes both per-function rewrites and crate-wide transformations. Extraction registers globally unique target names and computes function dependency/SCC structure before emitting declarations. A correct incremental layer therefore needs more than “rerun the edited function”: it needs stable snapshot identity, dependency tracking, invalidation across type/signature/trait/global and naming changes, and a way to replace or remove stale generated declarations.

The current architecture nevertheless makes future incrementalization plausible. Function translation receives explicit whole-crate contexts and maps rather than relying entirely on hidden process state, and independent functions are already parallelized. The practical near-term baseline is to treat one normalized LLBC crate as the invalidation unit while retaining the Aeneas process and in-memory values only for performance. Finer-grained reuse should be introduced only after an external or upstream dependency/invalidation model can prove when a retained result is still valid.

No Charon, Aeneas, OCaml, Lean, or benchmark execution was performed. The report characterizes the exact pinned source and separates source-established interfaces from performance hypotheses.

## Applicability

The primary subject is `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, release `nightly-2026.06.03`, selected by current Anneal.

This report asks a narrower question than the existing Aeneas architecture and library/process reports: after one LLBC input has been translated, what can the pinned implementation safely reuse when a later request changes part of that input?

“Incremental translation” here means semantic reuse across requests or source snapshots: retaining some previous Aeneas result, determining what changed, invalidating affected results, and recomputing only what is necessary. It does not mean:

- Aeneas's internal incremental maintenance of symbolic-interpreter bookkeeping within one evaluation;
- parallel translation of independent declarations in one run;
- reuse of the process-local Domainslib worker pool;
- Cargo or rustc incremental compilation before the LLBC boundary; or
- keeping an old generated file on disk.

Those mechanisms can reduce work, but none by itself establishes that a result from snapshot A is valid for snapshot B.

## Findings

### The public library exposes an in-memory reuse boundary

`Translate.translate_crate_to_pure` returns:

```text
trans_ctx * translated_crate
```

where `translated_crate` contains translated types, builtin function signatures, functions, globals, traits, and trait implementations. `extract_translated_crate` is a separate operation, and `translate_crate` is the convenience composition of the two.

A persistent host can therefore keep the LLBC crate, `trans_ctx`, and pure translated values in memory after a request. It does not have to serialize generated Lean merely to recover Aeneas's intermediate result.

That interface is an opportunity for an incremental adapter, not an incremental contract. No inspected entrypoint consumes an old `trans_ctx` or `translated_crate` when translating a new crate.

Basis: pinned **source**.

### Each pure-translation request constructs a fresh whole-crate context

`translate_crate_to_pure` starts with:

```text
let trans_ctx = compute_contexts crate
```

`compute_contexts` rebuilds several crate-wide structures from the supplied LLBC crate. It:

- computes `Deps.compute_graph_of_uses crate`;
- splits the complete declaration sequence and detects mixed recursive groups;
- walks declaration groups to determine which type, function, global, trait, and trait-implementation IDs are in the extraction set;
- analyzes the selected type declarations with `analyze_type_declarations`;
- analyzes the function map with `FunsAnalysis.analyze_module`; and
- constructs fresh maps for selected globals, traits, and trait implementations.

The returned context owns the supplied crate and those newly computed analyses. The function does not accept an earlier use graph, type-analysis result, or declaration cache.

The first invalidation boundary is therefore whole-crate context construction. A finer-grained adapter would need to understand which of these analyses are stable under an edit and provide a supported way to update or rebuild them.

Basis: pinned **source**.

### The main translation function retranslates every selected declaration class

After computing the context, `translate_crate_to_pure` translates all selected type definitions, then globals, then function signatures for the whole selected function set, then functions, trait declarations, and trait implementations.

Function signatures are deliberately computed before bodies so body translation can use the full signature map. Individual function translation also receives maps of translated types and globals plus the complete function-signature map. A function result is therefore not parameterized only by its own LLBC body.

The implementation catches declaration-local `CFailure`s and can continue past one failed function, global, trait, or implementation. That recovery boundary helps isolate work inside one run, but it does not create a reusable cache key across runs.

A correct incremental scheme must conservatively invalidate a retained function when relevant shared inputs change. At minimum, those inputs include the declaration itself and the whole-crate contexts/maps that its symbolic and pure translation consult. Source inspection here does not establish the minimal dependency closure.

Basis: pinned **source** + **derived** invalidation requirement.

### Function translation is already structurally decomposed enough to suggest a future incremental unit

Transparent and opaque functions are collected separately. Transparent functions are size-ranked, and both groups are processed through `parallel_filter_map`. Each call to `translate_function_to_pure` translates one `fun_decl` against immutable-looking shared translation inputs and catches its own recoverable failure.

Inside a function translation, Aeneas creates fresh local maps and generators for symbolic values, free variables, calls, and loop IDs. The later pure micro-pass stage likewise creates a per-task context with a domain-local fresh-variable generator, then applies the pass pipeline independently to each function before final cross-result finishing steps.

This decomposition is useful evidence that a function-sized recomputation unit is technically plausible. It is not evidence that function-sized invalidation is sufficient. The shared context, signature/type/global/trait maps, and extraction dependency structure still determine whether an old function translation remains valid.

Basis: pinned **source** + **derived** feasibility distinction.

### Pure micro-passes are parallel per function but still receive whole-program context

`PureMicroPasses.apply_passes_to_pure_fun_translations` builds maps of all translated functions, types, and trait implementations and puts them in each task's micro-pass context. It then applies the pass pipeline to individual functions in parallel, including loop decomposition and loop-body extraction.

After the per-function work, the pass pipeline performs final operations such as type annotation and reducibility processing over the collected translations.

This is another favorable implementation boundary for future incremental work: much of the expensive rewriting is already expressed as a function-local operation. But the operation is defined relative to maps of peer declarations. Reusing an old post-pass result therefore requires proving that the relevant shared maps and any final cross-result processing have not changed in a way that affects it.

Basis: pinned **source**.

### The pre-pass stage makes the normalized LLBC snapshot part of the cache identity

Before translation, the normal CLI calls `PrePasses.apply_passes` on the LLBC crate.

That function first performs a crate-wide `update_array_default` normalization. It then runs a fixed sequence of per-function passes and reconstructs the function map. Finally it performs additional crate-wide transformations including target-suffix stripping, marker-trait and type-alias filtering, static replacement, vtable removal, type-variable renaming, and trait-call simplification.

Some of these transformations can change declarations other than the syntactically edited function. For example, `update_array_default` can merge multiple generated array-`Default` implementations and selects a representative based partly on declaration membership.

An incremental cache below the pre-pass boundary must therefore be keyed by the normalized LLBC result, not merely by raw edited Rust text or one pre-normalization function body. Alternatively, an incremental pre-pass implementation would need its own invalidation model.

Basis: pinned **source** + **derived** cache-identity consequence.

### Extraction introduces global naming and dependency structure

`extract_translated_crate` does not print each pure declaration independently with a fixed local name.

It first constructs maps of all translated declarations and registers unique names across top-level types, functions, globals, traits, and trait implementations. The source explicitly says registration order matters because names in different declaration classes can clash.

Function extraction also reasons about dependency graphs and strongly connected components. One Rust function may produce forward, backward, and loop functions whose recursive grouping affects target syntax. Recursive-function metadata and decrease-clause handling are computed from the translated result before emission.

Consequently, a declaration-local pure translation can remain semantically reusable while its emitted target text still needs regeneration because another declaration changed naming or recursion structure. An incremental Anneal design should distinguish reuse of Aeneas semantic translation from reuse of final generated Lean bytes.

Basis: pinned **source** + **derived** stage distinction.

### The pinned library has process reuse, not request-scoped incremental state

The existing library/process report establishes that the `aeneas` Dune library is genuinely linkable and that its Domainslib pool is lazily created once and reused. It also establishes that configuration and error accumulation use process-global mutable refs, with the CLI relying on process termination for a clean request boundary.

Those facts matter to incremental execution because a persistent host can avoid repeated process and worker-pool setup. They do not supply snapshot identity, invalidation, or retained semantic caches.

A persistent host must therefore solve two independent problems:

1. **lifecycle isolation:** restore/reset mutable process state between requests and prevent conflicting concurrent requests; and
2. **semantic invalidation:** decide which result from an earlier LLBC snapshot remains valid.

Solving the first does not solve the second.

Basis: pinned **source** + current reference report `aeneas-library-process-architecture-nightly-2026-06-03`.

### The source's use of “incremental” inside the interpreter is unrelated to incremental crate translation

`InterpReduceCollapse.ml` contains an “incremental update of the context information.” It maintains borrow/loan lookup structures while abstractions are merged during one symbolic execution and, under sanity checks, recomputes the information from scratch to verify the incremental update.

That is local algorithmic incremental maintenance within an evaluation context. It does not cache translated Rust declarations between LLBC snapshots, expose edit/update operations, or provide a crate-level invalidation graph.

This distinction matters when surveying source by keyword: the presence of an internal incremental algorithm must not be mistaken for support for incremental Aeneas translation.

Basis: pinned **source**.

### The exact pin does not define the protocol an incremental Anneal adapter would need

Across the inspected entrypoints and translation structures, the exact pin defines no public operation for:

- assigning a generation or content identity to an LLBC snapshot;
- comparing two LLBC snapshots;
- accepting a changed/deleted declaration set;
- computing the transitive invalidation closure;
- updating `trans_ctx` after an edit;
- replacing a subset of a prior `translated_crate`;
- representing tombstones for removed declarations;
- validating that retained pure declarations were produced under the same relevant configuration; or
- incrementally updating extraction names, SCCs, and output files.

An adapter can build those concepts around the existing library, but then the correctness of reuse belongs to the adapter. The conservative supported behavior at this pin is still a fresh translation of the normalized LLBC crate.

Basis: pinned **source/interface inventory** + **derived** integration rule.

### The safest interactive baseline is process reuse with whole-crate semantic recomputation

For a first interactive Anneal architecture, the source supports a useful middle ground between “spawn everything from scratch” and “invent fine-grained invalidation immediately.”

A persistent Aeneas host can retain the OCaml process and its worker pool, receive a complete current LLBC crate, establish a clean request-state boundary, and call the ordinary whole-crate pipeline. That can remove process startup and avoid file-only integration without changing the semantic recomputation contract.

Finer-grained reuse can then be added behind explicit cache keys and dependency checks. A defensible progression is:

1. cache only by complete normalized LLBC snapshot plus Aeneas/configuration identity;
2. measure which stages dominate latency;
3. introduce reusable stage results only where dependencies are explicit;
4. add edit-driven invalidation tests for body, signature, type, trait, global, and declaration-add/remove changes; and
5. compare every incremental result against a clean whole-crate translation as the oracle.

The source decomposition suggests this is feasible engineering. It does not establish that doing so is trivial or already supported.

Basis: **derived** architecture guidance from the pinned interfaces.

## Boundaries

- No Aeneas, OCaml, Charon, Lean, Dune, or benchmark execution was performed.
- This report does not estimate latency or memory savings from process reuse or declaration-level caching.
- It does not prove a minimal invalidation graph. The source establishes broad shared inputs; a production cache requires stronger dependency accounting or conservative invalidation.
- It does not claim that `FunDeclId`, `TypeDeclId`, or other LLBC IDs are stable enough across independently regenerated LLBC snapshots to serve as cache keys without snapshot identity and validation.
- It does not establish byte-for-byte stability of generated Lean when semantically unrelated declarations change. Global naming and extraction ordering make that a separate empirical question.
- It does not characterize Charon's incremental capabilities; `charon-incremental-capabilities-0-1-210` is the companion subject.
- It does not characterize Cargo/rustc incremental compilation before LLBC generation.
- It does not recommend concurrent in-process Aeneas requests. The pinned library/process report establishes shared mutable configuration/error state that requires explicit isolation.
- The internal “incremental update” in `InterpReduceCollapse.ml` is scoped to one interpreter context and is not evidence of cross-request incremental translation.
- The recommended whole-crate-recomputation baseline is an integration strategy derived from current interfaces, not an upstream Aeneas guarantee.

## Evidence

Primary subject:

```text
AeneasVerif/aeneas
ac9f1bc5262a5e4ff1e24ca78617121382202727
release nightly-2026.06.03
```

Pinned translation/context source:

- `src/Translate.ml`, blob `8376e580b542bf3ee28cc9e3d4c170a17b23d379`: in-memory `translate_crate_to_pure` boundary; fresh `compute_contexts`; whole selected declaration-class translation; per-function parallel translation; micro-pass invocation; `extract_translated_crate`; whole `translate_crate` composition.
- `src/interp/Interp.ml`, blob `7b06ee4d1bdd302d9cbd85fc2e822c1f5324c1e5`: `compute_contexts`; fresh crate use graph; extraction-set derivation; type analysis; function analysis; whole context construction.
- `src/pure/PureMicroPasses.ml`, blob `e0662ab3153f3c401b44cbe6c0cad4e17157f063`: function-level micro-pass decomposition and parallelism; shared maps/context; loop decomposition; final collected-result processing.
- `src/PrePasses.ml`, blob `dc0ab803c26dafb14caf0da1bcc73e3499716835`: crate-wide and per-function normalization before translation, including `update_array_default` and later crate transforms.
- `src/interp/InterpReduceCollapse.ml`, blob `379bcd2d4904abf5e76a2f28877b2e293cf5f4e3`: internal incremental maintenance of borrow/loan context information within one interpreter operation, explicitly distinct from cross-request translation.

Pinned process-state source:

- `src/Parallel.ml`, blob `08f055cf2e87e0164bb3d02dc9f8dde2fc84034c`: persistent process-local Domainslib pool.
- `src/Errors.ml`, blob `c135674b8601786616c6c20ad81ec388bb8cbfea`: process-global error accumulators.
- `src/Config.ml`, blob `99a9eba5ae67dde20dbfd8d835cdc2900fc60355`: process-global mutable configuration.
- `src/Main.ml`, blob `b3f373f8c449eeae0f9a50bb0ce2d2963903eddc`: pre-pass call, one-input CLI lifecycle, translation dispatch, and global-error success boundary.

Current reference context:

- `reports/aeneas-library-process-architecture-nightly-2026-06-03`: public library versus one-shot process boundary and mutable-state constraints.
- `reports/aeneas-architecture-translation-pipeline-nightly-2026-06-03`: whole pipeline, declaration-local recovery/parallelism, and stage ordering.
- `reports/charon-incremental-capabilities-0-1-210`: companion candidate for the upstream Rust-to-LLBC incremental boundary; not native at the time this report package was prepared.

## Revalidation

Revalidate this report when any of the following changes:

1. Anneal changes its selected Aeneas release or revision.
2. Aeneas adds a server/session API, retained translation state, or an edit/invalidation API.
3. `translate_crate_to_pure`, `compute_contexts`, pre-passes, pure micro-passes, or extraction naming/dependency logic changes materially.
4. Aeneas replaces global configuration/error state with request-scoped state.
5. Anneal begins relying on declaration-level reuse rather than whole-crate recomputation.
6. An execution study establishes stable declaration identity, dependency fingerprints, or clean-vs-incremental equivalence under the edit classes listed below.

For a concrete feasibility probe at this exact pin, use a small crate with at least:

- two independent functions;
- one caller/callee pair;
- a shared struct or enum;
- a trait and implementation;
- a global/constant referenced by a function; and
- a loop that produces auxiliary pure functions.

Establish a clean whole-crate translation as the oracle. Then test body-only, signature, type-layout/field, trait-signature/impl, global-value/type, declaration-add, declaration-delete, and rename edits. For each edit, compare any proposed reused result with the clean translation at the pure-AST boundary and after Lean extraction. Treat a mismatch, stale declaration, stale name, or missing dependency-triggered recomputation as an invalidation failure.
