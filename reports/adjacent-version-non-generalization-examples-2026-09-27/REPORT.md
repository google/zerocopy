# Adjacent-version non-generalization examples for the Anneal stack

## Summary

An observation at one exact tool revision is evidence about that revision. It is not evidence that a neighboring release, a same-date tag in another repository, or even another commit reporting the same semantic version behaves identically.

The current Anneal stack contains two unusually clear examples.

First, Lake changed a verification-relevant ownership rule between Lean `v4.30.0-rc2` and `v4.31.0`. At `v4.30.0-rc2`, a dependency's compiled Lean configuration cache lives under the dependency checkout itself. At `v4.31.0`, change `41ecccec6d1244c5f89be2fc76638f22ba37cbc6` moves that cache into the containing workspace. The change alters read-only-tree behavior, cross-workspace contention, cache placement, and upgrade hygiene. Treating the two releases as interchangeable would erase the exact behavior Anneal needs to reason about.

Second, Charon demonstrates that labels can remain stable while relevant implementation identity changes. Aeneas `nightly-2026.06.03` pins Charon `a535e914f74db4fd9e6be7048f4233270d8945c0`. Anneal separately resolves Charon's repository-local tag `nightly-2026.06.03` to `0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`, 15 commits later. Both commits report Charon version `0.1.210`, but the older commit pins Rust `nightly-2026-05-31` while the later commit pins `nightly-2026-06-01`. Shared package version and shared release-date text therefore do not establish toolchain equivalence.

These are not merely cautions about naming. They show two distinct failure modes for adjacent-version reasoning:

1. **behavior can change across a nearby release boundary even when the component and feature are recognizably the same;** and
2. **different exact revisions can carry the same apparent version label while differing in a dependency that is semantically relevant to execution.**

For Anneal reference work, the safe default is therefore revision-scoped evidence. Reuse across revisions requires an explicit continuity argument: inspect the decision points that support the claim, compare the relevant source/history or artifacts, and run a targeted differential probe when behavior cannot be settled from immutable evidence alone. "Nearby" is useful for choosing what to compare; it is not a compatibility theorem.

No fresh Lean, Lake, Charon, Rust, Aeneas, or Anneal executable was run for this report. The examples come from immutable source, repository history, Git ancestry, and already-published exact-pin Anneal reference evidence.

## Applicability

This report supplies the concrete examples requested by the Anneal reference inventory item **Adjacent-version non-generalization examples**. It is methodological evidence for future research and upgrade work; it does not replace the dedicated reports for Lake configuration ownership, Charon toolchain requirements, or Anneal's full version-coupling graph.

The examples apply to the following exact identities.

**Lake example:**

- Lean/Lake `v4.30.0-rc2`: `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`.
- Lean/Lake `v4.31.0`: `leanprover/lean4@68218e876d2a38b1985b8590fff244a83c321783`.
- Introducing Lake change: `41ecccec6d1244c5f89be2fc76638f22ba37cbc6`, `feat: lake: hoist compiled configurations (#13683)`.

**Charon example:**

- Aeneas-selected Charon: `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`.
- Charon's own `nightly-2026.06.03` tag as resolved by Anneal: `AeneasVerif/charon@0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`.
- Both revisions declare package version `0.1.210`.
- Git ancestry places `0c91ca1a…` 15 commits ahead of `a535e914…`.

The rule here is deliberately narrow: claims should inherit the scope of the evidence that establishes them. An exact source statement may survive unchanged for many releases, but that continuity must be checked rather than inferred from proximity. Conversely, one changed implementation detail does not imply that every behavior changed. Revalidation should be claim-specific.

## Findings

### A nearby Lake release moved verification-relevant mutable state

At Lean `v4.30.0-rc2`, `LoadConfig` defines the general Lake directory as:

```text
cfg.pkgDir / defaultLakeDir
```

and `importConfigFile` derives the compiled-configuration directory from that package-local directory plus the assigned package name:

```text
cfg.lakeDir / "config" / <assigned package name>
```

For a dependency, `pkgDir` is the dependency checkout. The resulting `lakefile.olean`, trace, and lock files therefore live beneath the dependency's own `.lake/config/...` tree. This makes a compiled configuration physically package-owned even though its validity trace includes workspace-assigned identity such as package index and assigned name.

At Lean `v4.31.0`, `LoadConfig` adds a separate definition:

```text
cfg.wsDir / defaultLakeDir / "config" / toString cfg.pkgIdx
```

and `importConfigFile` uses that `configDir`. The compiled configuration now lives beneath the root workspace's `.lake/config/<index>` tree. The dependency source path and its general package `.lake` directory still exist, but this particular persisted state has moved into the workspace.

The difference is not cosmetic. It changes which processes can contend over one cache, which tree must be writable for ordinary configuration reuse, and which stale files can remain after an upgrade. An analysis that observed only `v4.30.0-rc2` and generalized to `v4.31.0` would incorrectly predict that independent workspaces sharing a dependency also share and rewrite that dependency's compiled-configuration cache. An analysis that observed only `v4.31.0` and projected backward would incorrectly describe the current Anneal pin.

The introducing commit states the intended behavioral reason directly: move compiled Lake configurations from the package's `.lake/config` to the workspace's `.lake/config` to remove potential contention between workspaces sharing a dependency. It also adds regression assertions for the new numeric workspace-local configuration directories. This is a concrete adjacent-release change with direct consequences for Anneal's prepared/read-only toolchain design.

### The Lake example also shows why revalidation must follow the claim, not the component name

The 4.31 change does not justify the broader sentence "Lake no longer writes dependency trees." The exact `v4.31.0` source still defines `cfg.lakeDir` as package-local, and the missing-trace branch of `importConfigFile` still calls `IO.FS.createDirAll cfg.lakeDir`. Package build products and other Lake state also remain separate concerns.

Therefore the correct cross-version conclusion is specific:

- compiled Lean **configuration cache placement** changed from dependency/package-local to workspace-local;
- the corresponding cross-workspace configuration-cache contention changed with it;
- broader dependency-tree mutability did not become equivalent to "read-only" merely because this one cache moved.

This matters for non-generalization in both directions. A version diff can prove that one claim changed while leaving neighboring claims unsettled. The right unit of continuity is the proposition Anneal needs, not "Lake behavior" as a whole.

### Charon keeps version `0.1.210` across two distinct revisions with different Rust pins

Aeneas `nightly-2026.06.03` pins Charon commit:

```text
a535e914f74db4fd9e6be7048f4233270d8945c0
```

That revision's `charon/Cargo.toml` declares:

```text
version = "0.1.210"
```

and its `charon/rust-toolchain` selects:

```text
nightly-2026-05-31
```

Anneal also has a separate Cargo dependency on Charon's repository-local tag `nightly-2026.06.03`. Its lockfile resolves that tag to:

```text
0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1
```

Git ancestry shows that revision is 15 commits ahead of the Aeneas pin. Yet its `charon/Cargo.toml` still declares version `0.1.210`. Its `charon/rust-toolchain` instead selects:

```text
nightly-2026-06-01
```

Thus two source revisions with the same package version have different exact Rust-toolchain requirements. For a rustc-driver project that uses unstable compiler-private APIs and dynamically linked rustc libraries, that dependency is not incidental version metadata. It participates in the executable compatibility boundary.

The example rules out two shortcuts:

- **same semantic version ⇒ same relevant behavior** is invalid here; and
- **same date-like nightly label across repositories ⇒ same transitive source/toolchain identity** is invalid here.

Aeneas's `nightly-2026.06.03` identifies an Aeneas release that pins the older Charon commit. Charon's own `nightly-2026.06.03` identifies the later Charon commit. Matching date text does not make those edges identical.

### Exact identity can matter even when the live boundary currently avoids the mismatch

Current Anneal's ordinary installed-toolchain path uses the Charon executable bundled with Aeneas, so the live Charon runtime path uses `a535e914…` and Rust `nightly-2026-05-31`. Anneal's independently locked `charon_lib` is compiled with `default-features = false`, and existing reference evidence does not identify an active cross-revision LLBC boundary through that library at the examined revision.

That fact prevents overclaiming: the repository contains two Charon identities, but their coexistence is not itself evidence that current Anneal executes an incompatible pair.

It also sharpens the non-generalization lesson. If future Anneal code begins using the independently locked library for a serialized representation, translation, or other shared semantic boundary, the old conclusion cannot simply be carried forward. The relevant edge changed even if both Charon nodes still print `0.1.210`. The future analysis must re-establish compatibility at the new boundary.

### Nearby source is useful as a comparison target, not as substituted evidence

Adjacent versions are often the cheapest place to start revalidation. A diff can show that a proof-critical function did not change, identify the exact patch that changed it, or reveal a new dependency. That makes neighboring revisions operationally valuable.

What adjacency does not provide is a default inference rule. The evidence must still connect the claim to the new identity.

For a source-defined claim, a useful continuity argument can be as small as:

1. resolve both versions to immutable commits;
2. identify the source decision points that establish the claim;
3. compare those decision points and their relevant dependencies;
4. check intervening history when a moved/renamed path or generated source could hide the change; and
5. preserve the conclusion at the new exact identity.

For an empirical claim, source continuity may be insufficient. Linker behavior, archive bytes, filesystem concurrency, performance, server protocol behavior, and clean/cache equivalence can depend on tools or environments beyond the inspected function. In those cases, adjacency narrows the differential test matrix but does not replace it.

### Version strings, tags, commits, and artifacts answer different identity questions

The Charon example is easiest to misuse when these layers are collapsed.

A package semantic version says what the project chose to expose as its package version. A repository tag names a repository object under that repository's naming policy. A commit identifies exact source state. A toolchain file identifies another dependency. A release asset hash identifies exact distributed bytes. These are related, but no one layer generally substitutes for all the others.

Anneal's current version-coupling graph therefore records exact revisions and artifact identities in addition to human-readable labels. This is not bookkeeping overhead. It prevents the same-version Charon pair above from collapsing into one node and prevents a date label in Aeneas from being mistaken for the identity of Charon's same-date tag.

### A durable report should make its revalidation surface explicit

The most reusable exact-pin reports identify the decision points a future worker must revisit. The two examples here suggest a practical pattern.

For Lake configuration ownership, revalidate `LoadConfig.lakeDir`, any separate `configDir`, the path chosen by `importConfigFile`, trace identity, dependency `wsDir`/`pkgDir` construction, and the concrete directory-creation calls. Those points directly support the ownership/contention claim.

For Charon toolchain coupling, resolve the exact Charon commit first, then inspect that commit's `charon/rust-toolchain`, wrapper toolchain-selection logic, rustc-private dependency boundary, and the consumer's effective Rust selection. A package version or nightly tag is retrieval context, not the final compatibility fact.

This approach avoids two bad extremes. It does not require redoing every investigation from first principles on every revision. It also does not treat an old report as current merely because the new version looks nearby.

## Boundaries

**No fresh execution.** This report did not run Lake, Lean, Charon, rustc, Aeneas, Cargo, Nix, or Anneal. The two examples are source/history facts whose decisive differences are visible in immutable revisions.

**Not a theorem that all adjacent versions differ.** The conclusion is only that proximity is not evidence of equality. A particular claim may remain valid unchanged across many revisions after revalidation.

**Not a general compatibility checklist.** The corpus has separate Lean, Lake, Aeneas, Charon, Rust-nightly, and archive upgrade checklists. This report supplies concrete examples and a scope rule; those checklists enumerate component-specific gates.

**No inference from one changed detail to whole-component incompatibility.** Lake's configuration-cache location changed, but other Lake behaviors may have remained identical. Charon's Rust nightly changed between the two exact commits, but their shared package version does not prove either broader equivalence or broader incompatibility.

**Current Anneal execution boundary preserved.** The existence of two Charon revisions in dependency state is not presented as a current runtime LLBC mismatch. Existing reference evidence says the ordinary executable path uses Aeneas's Charon pin at the examined main revision.

**Historical labels remain repository-relative.** The report does not assume that `nightly-2026.06.03` has one global meaning across Aeneas and Charon. The whole point of the second example is that it does not.

## Evidence

Evidence was materially revalidated on 2026-09-27.

**Lake v4.30.0-rc2** — `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`:

- `src/lake/Lake/Load/Config.lean`, blob `f1fe9b199f41e00d3cf10725b4dfc6b2d3623ec2`: `LoadConfig.lakeDir = cfg.pkgDir / defaultLakeDir`; no separate workspace-owned compiled-configuration directory.
- `src/lake/Lake/Load/Lean/Elab.lean`, blob `c72b295cb0b9d7365d21cf2ebd323a3cc4068eab`: `importConfigFile` places the `.olean`, trace, and lock beneath `cfg.lakeDir / "config" / <assigned package name>` and records workspace-relative trace identity.
- Existing native package `reports/lake-configuration-ownership-v4-30-0-rc2` supplies the full exact-pin ownership analysis.

**Lake v4.31.0** — `leanprover/lean4@68218e876d2a38b1985b8590fff244a83c321783`:

- `src/lake/Lake/Load/Config.lean`, blob `afdb0a19d9f5443f3cd6081014601744e538c523`: adds `LoadConfig.configDir = cfg.wsDir / defaultLakeDir / "config" / toString cfg.pkgIdx` while retaining package-local `lakeDir`.
- `src/lake/Lake/Load/Lean/Elab.lean`, blob `b3908d0cebb44cac15e48baa41cb439f6f94eaa5`: `importConfigFile` uses `cfg.configDir`; the missing-trace branch still contains `IO.FS.createDirAll cfg.lakeDir`.
- Commit `41ecccec6d1244c5f89be2fc76638f22ba37cbc6`, `feat: lake: hoist compiled configurations (#13683)`: states the cross-workspace contention motivation and adds regression assertions for workspace-local numeric configuration directories.
- Existing native package `reports/lake-configuration-ownership-v4-31-0` supplies the full exact-release follow-up analysis.

**Charon Aeneas pin** — `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`:

- `charon/Cargo.toml`, blob `8c9936202e7bdbdaaefbc19305363da1ab6c0084`: package version `0.1.210`; default `rustc` feature; rustc-driver structure.
- `charon/rust-toolchain`, blob `3c98116ae62afb83263fa1654037badaf569e1c1`: Rust `nightly-2026-05-31` plus rustc-internal components.
- Existing native packages `reports/charon-toolchain-requirements-nightly-2026-06-03` and `reports/anneal-toolchain-version-coupling-main-41f5b37` establish how this commit is selected by Aeneas and used by current Anneal.

**Charon repository-local nightly tag resolution** — `AeneasVerif/charon@0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`:

- `charon/Cargo.toml`, blob `8c9936202e7bdbdaaefbc19305363da1ab6c0084`: still package version `0.1.210`.
- `charon/rust-toolchain`, blob `3760bb48e9650e0c5d57c27a4ee5d5d358e59a3e`: Rust `nightly-2026-06-01`.
- Git ancestry comparison: this commit is 15 commits ahead of `a535e914…` with no divergence in that direction.
- Existing native package `reports/anneal-toolchain-version-coupling-main-41f5b37` establishes that Anneal's separate `charon_lib` tag resolves to this exact commit and distinguishes it from the Aeneas-bundled runtime Charon.

Evidence classes are immutable source, repository history, Git ancestry, and current native reference synthesis. There is no fresh execution evidence.

## Revalidation

For any claim being carried from one exact version to another, preserve the old report as evidence about the old identity and perform a claim-specific continuity check.

1. Resolve the new human-readable version or tag to an immutable source revision and, where relevant, exact distributed artifact hashes.
2. Identify the smallest source, manifest, generated-artifact, protocol, or runtime decision points that actually support the old claim.
3. Compare those decision points and the dependencies they rely on. Do not stop at a package version, matching date, or unchanged top-level filename.
4. Search intervening history when the implementation moved, was regenerated, or has a history-sensitive compatibility rule.
5. If the claim is source-defined and the supporting logic is materially unchanged, record a new exact-identity continuity conclusion rather than silently widening the old report's scope.
6. If the claim depends on runtime or environment behavior, run the narrow differential probe that distinguishes the relevant outcomes. Preserve exact versions, inputs, commands, and artifacts.
7. When a difference is found, narrow it to the affected proposition. Do not infer whole-component incompatibility unless the evidence supports that stronger conclusion.

For the two examples in this report, the cheapest recurring probes are concrete.

**Lake:** compare `LoadConfig.lakeDir`, any `configDir`, `importConfigFile` paths and directory creation, trace identity, and dependency load construction. If read-only or concurrency behavior matters, run the shared-dependency workspace probe described by the dedicated Lake reports.

**Charon:** resolve the exact Charon commit selected by the consumer, read its `charon/rust-toolchain`, and compare that requirement with the effective Rust toolchain and wrapper selection logic. If a consumer crosses an LLBC or other shared-representation boundary between two Charon revisions, separately compare that representation boundary instead of inferring compatibility from `0.1.210`.

A later report may cite these examples as reminders, but it should still state the exact revision to which each substantive behavior claim applies.