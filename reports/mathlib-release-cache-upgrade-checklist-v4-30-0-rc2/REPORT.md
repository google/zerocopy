# Mathlib release/cache upgrade checklist for Anneal

## Summary

Changing Anneal's Mathlib revision is not only a source-dependency update. At the current baseline, Aeneas `nightly-2026.06.03` resolves Mathlib input `v4.30.0-rc2` to `leanprover-community/mathlib4@5450b53e5ddc75d46418fabb605edbf36bd0beb6`; that Mathlib revision is paired with Lean `v4.30.0-rc2`, has its own locked Lake dependency graph, and supplies the repository-specific `lake exe cache` protocol that Anneal uses to materialize precompiled Mathlib state.

Anneal depends on several Mathlib-specific properties at once. The cache object name is a custom module hash derived from project/source/import state, while the `.ltar` header contains a different Lake dependency hash. A cache object contains more than `.olean`: required payload includes traces, `.olean`, `.ilean`, generated C, and sidecar hashes, with additional optional compiler products. Current Anneal downloads the linked `.ltar` objects with `lake exe cache get-` inside a Nix fixed-output derivation, separately reconstructs a package build tree, rewrites and prunes that tree, and then validates it through later Lake/Lean use.

For Anneal, the durable upgrade unit is therefore the **resolved Mathlib/Lake dependency graph plus cache protocol, payload, helper, packaging, and semantic-reuse evidence**, not the Mathlib tag alone. A candidate upgrade should not be accepted until each applicable gate in `upgrade-checklist.json` is demonstrated unchanged or reviewed as an intentional migration. In particular, successful download of `.ltar` files does not establish that their cache keys are still correct, that the payload is complete for Anneal's consumers, that the restored package tree is relocatable/read-only, or that a seeded build is semantically equivalent to a clean build.

This report is a revalidation checklist. It does not select or approve a newer Mathlib release.

## Applicability

The baseline is current Anneal source at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` and the Lean dependency graph bundled by Aeneas release `nightly-2026.06.03` at `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`.

Aeneas's `backends/lean/lakefile.lean` requires Mathlib from Git at `v4.30.0-rc2`. Its checked-in `lake-manifest.json` resolves that input to Mathlib commit `5450b53e5ddc75d46418fabb605edbf36bd0beb6` and records the inherited package closure. Its `lean-toolchain` selects Lean `v4.30.0-rc2`. The exact manifest, not the tag text alone, is the dependency identity Anneal currently consumes.

Current Anneal's Nix assembly extracts that Aeneas project metadata, runs `lake exe cache get-` in a network-enabled fixed-output derivation, preserves the downloaded Mathlib `.ltar` objects plus dependency source trees, decompresses the cache in a later derivation, prepares the Aeneas/Mathlib package state, prunes the final package tree, and verifies offline/reuse properties before assembling the toolchain archive.

The checklist applies when changing the Mathlib revision selected through Aeneas, changing the Mathlib cache implementation consumed by Anneal, changing a dependency-lock closure in a way that affects Mathlib cache identity, or changing Anneal's interpretation of the Mathlib cache. It is not a general Mathlib release-engineering checklist and does not require every upstream job when narrower Anneal-specific evidence establishes the relevant property.

## Findings

### 1. Resolve the exact Mathlib and dependency-closure identities first

The first upgrade artifact should identify the complete selected graph rather than only a Mathlib tag:

`Anneal revision → Aeneas release/revision → Lean toolchain → Aeneas Lake manifest → Mathlib commit → inherited package commits`.

At the current baseline, Aeneas names Mathlib `v4.30.0-rc2`, but the checked-in manifest resolves that input to commit `5450b53e…` and records concrete revisions for Batteries, Qq, Aesop, ProofWidgets, and the remaining inherited packages. Those transitive revisions can change independently of a human-facing Mathlib tag or can affect cache/build behavior even when Anneal's own source is unchanged.

For a proposed upgrade, record the new Mathlib commit and the entire manifest closure before comparing outputs. Treat a changed manifest entry as an upgrade input that requires review, not as incidental lockfile noise.

Basis: Aeneas **source** (`lakefile.lean`, `lake-manifest.json`, `lean-toolchain`) + current toolchain-coupling reference synthesis.

### 2. Revalidate Mathlib against the exact Lean/Lake release

Mathlib's cache code executes inside the selected Lean/Lake toolchain, and its package sources are written against that release. The current Mathlib revision carries `lean-toolchain = leanprover/lean4:v4.30.0-rc2`, matching Aeneas.

An upgrade must establish that the proposed Mathlib revision, Aeneas's Lean toolchain, and Anneal's packaged Lean toolchain agree. If the Mathlib upgrade also requires a Lean/Lake upgrade, apply the separate Lean and Lake upgrade checklists rather than treating the change as Mathlib-only.

At minimum, record Mathlib's own `lean-toolchain`, Aeneas's `lean-toolchain`, and the Lean revision actually packaged by Anneal. A successful cache download is not evidence that the restored `.olean`/`.ilean` artifacts are valid under a different Lean build.

Basis: exact Mathlib/Aeneas **source** + current Lean/Lake reference corpus.

### 3. Treat `lake exe cache` as a versioned Mathlib protocol

At the baseline, Mathlib implements a repository-specific cache executable. The retrieval commands are materially distinct: `get` downloads missing linked cache objects and decompresses them, `get!` forces both operations, and `get-` downloads missing objects without decompression. Anneal relies specifically on `get-` so network materialization and later cache expansion occur in separate Nix derivations.

For an upgrade, re-read the command dispatch and verify that Anneal's chosen command still has the same transport/install boundary. Record changes to endpoint selection, local cache directories, retry/partial-file behavior, object naming, and environment-variable overrides that affect reproducibility or mirroring.

If `get-` disappears, changes semantics, or starts mutating the package build tree, Anneal's current fixed-output architecture requires an explicit migration.

Basis: Mathlib **source** (`Cache/Main.lean`, `Cache/Requests.lean`) + current cache-protocol report.

### 4. Recompute the cache-key contract rather than assuming archive names remain comparable

At the baseline, each linked module's `.ltar` filename is a custom Mathlib `UInt64` cache key. The key incorporates a root hash and module-specific source/import information. The current executable source makes the root sensitive to Mathlib project files including `lakefile.lean`, `lean-toolchain`, and `lake-manifest.json`.

A cache-key algorithm change is semantically important even if the payload format remains readable. Conversely, an unchanged key algorithm is not enough when one of its inputs changes. For each upgrade, identify the current root/key computation and verify that the expected project/configuration inputs participate in invalidation.

Do not confuse the filename key with the different Lake `depHash` stored in the `.ltar` header. They answer different questions and must remain separately represented in tests and diagnostics.

Basis: Mathlib **source** (`Cache/Hashing.lean`, `Cache/Lean.lean`, `Cache/IO.lean`) + current cache-protocol report.

### 5. Revalidate the cache payload and helper/archive format together

A Mathlib cache object is a module-scoped bundle of Lake/Lean outputs. At the current pin, required payload includes the module trace, `.olean`, `.olean.hash`, `.ilean`, `.ilean.hash`, generated C, and generated C hash; optional payload includes server/private oleans, IR, extra data, and related hashes.

Anneal cannot safely assume this set is stable across Mathlib/Lean releases. A new compiler artifact can become semantically required even when an older `leantar` still extracts the files it recognizes. Likewise, a new `leantar`/LTAR format can alter path handling or archive-header semantics independently of Mathlib's module key.

For an upgrade, diff the source-defined build-path list and archive packing/unpacking logic, resolve the exact `leantar` implementation used by the selected Lean toolchain, and preserve at least one golden archive inventory. If the helper version or archive format changes, perform an exact old/new compatibility probe rather than relying on filename extension continuity.

Basis: Mathlib **source** (`Cache/IO.lean`) + current cache/native-artifact reference reports.

### 6. Preserve native and platform-specific artifact requirements

Lean/Lake package state can include host-native artifacts in addition to `.olean` and `.ilean`. Static/shared libraries, plugin/module shared libraries, executables, generated C, and object files have different build/restoration rules and may be platform-specific.

A Mathlib upgrade should therefore be validated on every Anneal-supported host class for which the prepared package tree is distributed. Record whether the cache now contains or expects additional native artifacts and whether any artifact is architecture- or ABI-specific. Do not infer portability from a successful pure-Lean module load on one platform.

This gate is especially important because Anneal records different fixed-output hashes per host system and already works around a cross-architecture helper-binary anomaly in the surrounding Lean distribution.

Basis: current native-artifact report + Anneal packaging **source**.

### 7. Regenerate Anneal's fixed-output Mathlib materialization identities

Anneal's `mathlib-cache-download` is a recursive Nix fixed-output derivation. Its expected hash commits to the resulting post-download directory tree, which includes cache objects and dependency source state after Anneal's cleanup, not merely one upstream archive checksum.

A legitimate Mathlib/dependency/cache upgrade is therefore expected to change the fixed-output result in many cases. For each supported host, regenerate the materialized output deliberately and review the diff before updating the expected hash. A matching new hash proves content equality to the reviewed candidate result; it does not prove provenance or semantic correctness by itself.

Keep the network-enabled fixed-output phase separate from later ordinary transformations. If the upgrade causes decompression/build/pruning to move into the network phase, that is an architectural change, not a hash refresh.

Basis: Anneal `flake.nix` **source** + current fixed-output report.

### 8. Recheck relocation, read-only, and offline consumption after restoration

The downloaded cache is only an intermediate state. Anneal later restores/prepares build products and consumes them from a packaged dependency universe. Lake's current behavior does not provide one switch that guarantees relocation, read-only operation, offline operation, and concurrent safety.

For a Mathlib upgrade, run the restored package through the same final topology Anneal distributes. Verify that relative manifest/package identities resolve after relocation, that no network access is required, and that no write to immutable shared package state is attempted on the intended consumer path. Preserve failed-write/network evidence rather than only successful compilation output.

A cache download succeeding in the producer location is not evidence for this consumer property.

Basis: current Lake read-only/relocation/offline report + Anneal prepared-archive history/source.

### 9. Revalidate dependency-closure pruning against the new package graph

Current Anneal prunes Mathlib to a source-level module closure seeded from non-Mathlib consumers and supplements that closure with trace-derived names. The implementation deliberately treats this as a conservative packaging optimization, not a theorem about arbitrary future Mathlib layouts.

A Mathlib upgrade can add new direct imports, generated consumers, source roots, native artifacts, metadata, or module-layout conventions. Re-run the closure computation on the proposed package tree, compare retained/deleted modules, and validate the final pruned tree with the production consumer path. Treat changes in Mathlib's module layout or import syntax assumptions as reasons to review the pruning algorithm itself.

Do not use source-module reachability to justify deleting package-level metadata or native artifacts that live outside the module-to-build-path mapping.

Basis: current pruning report + Anneal pruning **source**.

### 10. Compare clean and cache-seeded states semantically, not only by file presence

A cache-seeded environment can contain all expected filenames and still disagree with a clean build in source/configuration identity, trace state, module setup, native artifacts, or proof-relevant compiled content.

For a proposed upgrade, select a compact representative set of Aeneas/Anneal modules and compare clean versus seeded builds under the exact same toolchain and host. Required evidence should include successful elaboration, relevant `.olean`/`.ilean` and native artifact identity or justified equivalence, compatible trace/dependency state, and the same observable Lean theorem behavior. Raw path-bearing metadata may differ after relocation; classify those differences rather than demanding byte equality where path identity is intentionally changed.

Current Anneal sometimes relies on timestamp/old-mode behavior after rewriting dependency locations, so the acceptance test must exercise Anneal's actual final prepared state rather than only ordinary upstream hash-mode cache reuse.

Basis: current clean/cache-seeded equivalence report + Anneal **source**.

### 11. Validate one end-to-end cache lifecycle, not only component contracts

The final gate should exercise the complete lifecycle Anneal depends on:

1. resolve the exact Aeneas/Lean/Mathlib manifest graph;
2. run the production-equivalent `lake exe cache get-` network materialization;
3. verify the fixed-output result and object inventory;
4. restore the `.ltar` payload with the selected helper;
5. prepare/rewrite the dependency tree exactly as Anneal does;
6. prune the final tree;
7. move it to a fresh consumer location and make shared state read-only where intended;
8. deny or observe network access;
9. build/elaborate representative generated Lean and proofs;
10. record reuse/rebuild evidence and final theorem behavior.

Component source review remains necessary because one integration corpus cannot prove complete compatibility. The lifecycle probe is complementary: it catches mismatches among components whose local contracts still look plausible in isolation.

Basis: **derived** from the independent exact-pin boundaries established above.

## Boundaries

- No newer Mathlib release or commit was selected or evaluated. This report defines what must be revalidated; it does not approve an upgrade.
- No fresh Mathlib cache download, `leantar` extraction, Lake build, Lean elaboration, Nix build, relocation, read-only, offline, or cross-platform experiment was performed for this report.
- The checklist does not claim that Mathlib's current 64-bit module cache key is collision-proof or content-addresses final archive bytes. It records the current protocol and requires revalidation of the chosen key contract.
- The `.ltar` filename key and the archive-header Lake dependency hash remain distinct identities. Future code may redesign either layer.
- A fixed-output hash is an integrity/reproducibility boundary for one materialized result, not a provenance signature or semantic compatibility proof.
- Source-level dependency-closure pruning is conditional on its completeness assumptions. Passing this checklist does not elevate the current regex-based implementation into a complete Lean parser.
- Exact byte equality is not required for every relocated path-bearing artifact when the semantic consumer contract permits location changes. Such differences must be classified explicitly rather than ignored.
- The machine-readable checklist is an aid to revalidation. Current Anneal authority, current #3720 semantics, and later precisely identified evidence take precedence.

## Evidence

**Direct Aeneas source.** `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`:

- `backends/lean/lakefile.lean` (`c32062866e2f88d2eb768b904745e7104edddb0d`) requires Mathlib at `v4.30.0-rc2`;
- `backends/lean/lake-manifest.json` (`1a5af703163d8b39f4311aafe22ae171788179ee`) resolves Mathlib to `5450b53e…` and records the inherited dependency closure;
- `backends/lean/lean-toolchain` (`6c7e31fffe3e03be3e0d7021acd9cd848e44db26`) selects Lean `v4.30.0-rc2`.

**Direct Mathlib source.** `leanprover-community/mathlib4@5450b53e5ddc75d46418fabb605edbf36bd0beb6`:

- `Cache/Main.lean` (`12f69c07522f61db89318bc8331b5eb395b45377`) defines the cache CLI command surface;
- `Cache/Hashing.lean` (`418e884d1262cd8655ceddccf0e3c5894f742e46`) defines custom root/module cache hashing;
- `Cache/IO.lean` (`872ffe7ce8c608f6769e3e3cc5bb5dac8f9b001a`) defines payload paths, archive-header interpretation, packing, restoration, and decompression checks;
- `Cache/Requests.lean` (`2f59d1ec95d8f04574c74b869afd4473acf60406`) defines transport/cache request behavior;
- `Cache/Lean.lean` (`0934e22f2dc396411106b008016fba4569cf741d`) supplies cache-path/hash helpers;
- `lakefile.lean` (`2615d72c0aa5e414234eac5f7ade10f4f3890916`), `lake-manifest.json` (`86b358344ea45a46d99dc19ac861011583e6d6e5`), and `lean-toolchain` (`6c7e31ff…`) define the package/toolchain state participating in the selected cache contract.

**Direct Anneal source.** `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, especially `anneal/flake.nix` (`433fcf5c64da4f51b9fac471f1faf45c1f730cba`), defines the `get-` fixed-output download phase, per-host expected hashes, later cache expansion, package preparation/pruning, and final archive assembly.

**Published reference synthesis.** Current `google/zerocopy` reference commit `e1ef8f81d5e12ea48c35023ef8da740ca9dbfd10` supplies exact-subject reports for Mathlib cache protocol/artifact semantics, Mathlib dependency-closure pruning, Lean/Lake native artifacts, clean versus cache-seeded equivalence, Lake read-only/relocation/offline/concurrency behavior, Nix fixed-output acquisition, and the current complete toolchain version graph.

`source-map.json` records the exact report paths/blobs used for this checklist.

**Derived checklist.** `upgrade-checklist.json` converts those independent exact-pin findings into eleven gates. The ordering is intentional: establish identities and toolchain compatibility first; then cache keys/protocol/payload; then Anneal materialization, restoration, pruning, and semantic-equivalence evidence; finally require one integrated lifecycle probe.

## Revalidation

When Anneal considers a new Mathlib revision or changes the selected cache inputs, copy `upgrade-checklist.json` and attach concrete evidence to every applicable gate.

A narrow efficient sequence is:

1. Resolve the exact Aeneas revision, Lean release, Mathlib commit, and full Lake manifest closure.
2. Diff the old/new Mathlib `lean-toolchain`, `lakefile.lean`, manifest, and `Cache/` implementation before downloading anything.
3. Record changes to module-cache key inputs, object naming, command semantics, payload membership, archive/header handling, and helper version.
4. Materialize the network state under the production `get-` path for every supported host, inspect the tree diff, and establish reviewed new fixed-output identities.
5. Restore the cache with the exact selected helper and compare a bounded artifact inventory with a clean build.
6. Apply Anneal's rewrite/pruning steps and run a complete final-tree validation from a fresh location.
7. Make the intended shared state read-only and run with network denied or independently observed so hidden write/fetch requirements fail closed.
8. Compare clean and seeded representative modules semantically, including theorem behavior, setup/import state where relevant, native products, and rebuild/reuse evidence.
9. Preserve all commands, revisions, manifests, fixed-output hashes, archive inventories, trace/setup observations, host/architecture identities, and resulting proof/build outcomes as the upgrade evidence package.

Source-only gates should be completed before expensive platform probes. Empirical gates must not be marked satisfied merely because source inspection found no obvious incompatibility.