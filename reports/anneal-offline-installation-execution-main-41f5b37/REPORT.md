# Anneal offline installation and execution guarantees at main `41f5b37`

## Summary

Current Anneal has a useful but deliberately narrower offline contract than “all operations are network-disabled.” At `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, three phases need to be separated: obtaining an installation, consuming the prepared Lake dependency universe, and enforcing the absence of arbitrary network activity.

For **installation**, the distinction is exact. A fresh default `cargo anneal setup` selects Exocrate's remote source and performs an HTTP GET, so it is inherently network-dependent. `cargo anneal setup --local-archive <path>` selects a local file and has no Exocrate network operation on that source path. If the versioned installation directory already exists, Exocrate returns it before opening either the remote or local source, so ordinary resolution of that installation does not need to contact the configured archive origin. Current remote URLs are still explicit placeholders in `anneal/Cargo.toml`, so the default fresh-remote path is not yet a deployable release path at this revision.

For **prepared Lake consumption**, current archive construction is intentionally offline-oriented rather than accidentally cache-dependent. The producer obtains and vendors the Aeneas/Mathlib dependency sources, removes their Git metadata, rewrites dependency declarations and manifests to relative **path** dependencies, copies selected prebuilt Lake outputs into that tree, and performs an offline-oriented verification build before packaging. The consumer-side archive test then refuses inherited non-path manifest entries, constructs a fresh workspace whose entire inherited graph is path-based, and invokes the archived Lake/Lean binaries from the local toolchain. This eliminates Lake's ordinary Git clone/fetch path for the packaged dependency universe. It also preserves source/configuration state rather than assuming that `.olean` or cache artifacts alone are a complete workspace.

That architecture still does **not** amount to a hard “no network can occur” guarantee. The checked-in V2 archive-consumption test clears the process environment before invoking Lake, which removes ambient user cache endpoints and package URL overrides, but it does not place the process in a network-denied sandbox and it does not trace network syscalls. At the pinned Lake revision, the top-level `--offline` flag is parsed but ordinary `lake build` does not propagate it through `LakeOptions.mkLoadConfig`; current Anneal's consumer test does not pass it anyway. Path dependencies suppress the dependency Git network path, not arbitrary network access by package configuration, scripts, external tools, future cache configuration, or newly introduced code.

There is also a current product-surface boundary: V2's public CLI at this revision exposes only `setup`. The Lake/Lean execution path described here exists as archive construction and test-contract machinery, not yet as a complete public V2 verification command. Accordingly, the strongest supported statement is:

> A prepared current Anneal toolchain can be installed from a caller-supplied local archive without an Exocrate download, and its checked-in consumer architecture is designed to use a complete path-vendored Lake dependency graph and prebuilt artifacts without dependency clone/fetch. Current code does not enforce or empirically establish process-wide network denial for all execution.

No fresh Anneal, Nix, Lake, Lean, network-isolation, or syscall-tracing experiment was run for this report. The conclusions combine exact current source, checked-in CI/test contracts, the pinned Lake implementation, and already-preserved reference evidence.

## Applicability

The Anneal-specific findings apply to `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` and principally to:

- `anneal/src/main.rs`, which defines the V2 CLI, chooses local versus remote Exocrate installation sources, constructs the archive-reuse workspace, requires inherited path dependencies, and invokes Lake with a cleared environment;
- `exocrate/src/lib.rs`, which defines existing-installation resolution and local/remote source opening;
- `anneal/flake.nix`, which obtains, vendors, rewrites, prebuilds, and packages the Aeneas/Lean/Rust toolchain universe;
- `anneal/rewrite-lake-vendor.py`, which rewrites known dependency declarations and `lake-manifest.json` entries to path dependencies;
- `anneal/Cargo.toml`, which contains the current placeholder remote metadata; and
- `.github/workflows/anneal.yml`, which builds the omnibus archive once, passes it as a workflow artifact, and runs V2 tests with all features.

The Lake conclusions apply to `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), the Lean/Lake revision selected by the current Aeneas toolchain. In particular, the report relies on the exact `LakeOptions`, workspace loading, dependency materialization, and environment behavior at that pin. Adjacent Lean/Lake releases must be revalidated rather than assumed equivalent.

“Offline installation” means that resolving/populating the Exocrate toolchain installation does not require network access. “Offline execution” means that the prepared toolchain's intended consumer path can complete without obtaining missing dependency state from a network service. Neither phrase, unless explicitly qualified, means that the operating system prevents the process tree from opening sockets.

This report is a cross-layer synthesis. Detailed checksum/authentication semantics, extraction security, archive read-only permissions, cache/version path identity, generic Lake Git/path materialization, and Lake cache architecture remain owned by their dedicated reports. They are used here only where necessary to state the offline boundary.

## Findings

### Fresh default setup is network-dependent; local-archive setup is not

V2 exposes `cargo anneal setup` with one optional `--local-archive` argument. `setup_installation_dir` maps the absence of that option to `exocrate::Source::Remote(REMOTE)` and maps its presence to `exocrate::Source::Local(path)`.

Exocrate's `open_source` makes the network boundary explicit:

- `Source::Remote` executes `ureq::get(url).call()` and returns the HTTP response body as the archive reader;
- `Source::Local` executes `File::open(path)` and returns the local file as the archive reader.

Therefore a **fresh** default setup requires access to its configured remote URL, while a **fresh** local-archive setup has no source-download network operation in Exocrate. This statement is about Exocrate's installation source path. It does not authenticate the local archive, establish filesystem integrity, or prove that unrelated process initialization cannot use the network.

At this exact revision, the remote URLs in `anneal/Cargo.toml` are `example.com` placeholders accompanied by a FIXME requiring replacement before publication. The remote protocol is implemented, but the literal default metadata is not a production release origin.

Basis: current **source** in `anneal/src/main.rs`, `exocrate/src/lib.rs`, and `anneal/Cargo.toml`.

### An already-present installation bypasses archive-source access entirely

`Config::resolve_installation_dir_or_install` computes the versioned installation path and checks whether the target managed directory already exists. If it does, Exocrate returns `ResolvedExisting` before opening the supplied source. A second under-lock existence check protects the new-install path from process races.

This yields a stronger and useful distinction than “remote versus local” alone. Once the exact versioned installation directory already exists, resolving that installation does not require reading the remote URL or a local archive at all. Conversely, this is an **existence** fast path, not a revalidation path: Exocrate does not prove here that the installed tree still matches the original archive.

The separate cache/version-identity work explains which build/platform inputs choose that directory. The separate checksum/trust reports explain what was checked, or not checked, when it was initially populated. Neither changes the offline observation: existing-directory resolution occurs before source opening.

Basis: current **source** and checked-in Exocrate test contract.

### The packaged Lake dependency universe is deliberately converted to local path dependencies

Current archive production first obtains the dependency source universe and prebuilt Mathlib/Lake outputs. Before the final consumer archive is formed, Anneal changes the Lake source contract rather than merely copying a populated `.lake/packages` directory.

The producer:

1. copies the materialized package directories into the archive build;
2. removes `.git` directories from the vendored package set;
3. runs `rewrite-lake-vendor.py` over Aeneas and the package tree;
4. rewrites known `require` declarations from remote forms to relative paths;
5. rewrites matching `lake-manifest.json` entries to `type: "path"` entries and removes remote-source fields; and
6. seeds the vendored package tree with prebuilt Lake build products, including Mathlib outputs, before an offline-oriented build check.

This ordering matters. At the pinned Lake revision, a manifest entry that still says “Git” is not satisfied merely because a directory with the right source files exists. Lake can inspect Git `HEAD`, enter its update path, fetch, or reclone. A path entry instead materializes by direct filesystem path without Git clone/fetch. Current Anneal deliberately chooses the latter model before deleting Git metadata.

This finding reuses and revalidates the dedicated current-profile Lake source-materialization candidate. It does not absorb that report's complete Git/path decision table into this cross-layer report.

Basis: current **source** in `anneal/flake.nix` and `anneal/rewrite-lake-vendor.py`; pinned Lake **source** in `Lake/Load/Materialize.lean` and `Lake/Load/Resolve.lean`.

### The consumer rejects a non-path inherited graph before running Lake

The V2 archive-reuse test does not simply point Lake at the packaged Aeneas tree and hope that no dependency fetch occurs. `write_relative_archive_manifest` opens the archived Aeneas `lake-manifest.json` and requires every inherited package entry to have `type == "path"`. Encountering another source kind returns an error.

For accepted entries, the code canonicalizes the archived package directory, rewrites its `dir` relative to the new generated workspace, marks it inherited, and emits a fresh root manifest. Aeneas itself is added as another path package. The root workspace's `lakefile.lean` likewise requires Aeneas from its archive filesystem path.

The resulting consumer contract is therefore fail-closed with respect to this particular source-kind invariant: the checked-in consumer does not silently accept a Git entry that could cause Lake to clone or fetch. That is materially stronger than relying on the presence of prebuilt outputs alone.

Basis: current **source/test contract** in `anneal/src/main.rs`.

### The archive-reuse test removes ambient network/cache configuration, but does not deny network syscalls

`run_lake_archive_command` invokes the archived `lean/bin/lake` by absolute path, sets the generated workspace as its current directory, and calls `env_clear()` before setting only the platform dynamic-library search path needed for the packaged Lean libraries.

This removes ambient values such as:

- `HOME` and `XDG_CACHE_HOME`;
- `LAKE_CONFIG` and user Lake configuration;
- `LAKE_PKG_URL_MAP`;
- `LAKE_CACHE_ARTIFACT_ENDPOINT`, `LAKE_CACHE_REVISION_ENDPOINT`, and `LAKE_CACHE_SERVICE`;
- inherited `PATH`; and
- inherited Lean/Lake toolchain variables.

Lake then reconstructs its own environment from the co-located archived Lake/Lean installation. Because the generated manifest is path-only, the normal dependency materialization path does not need Git remotes. This is a strong test harness for accidental ambient-state dependence.

However, `env_clear()` is not a network sandbox. It neither blocks socket creation nor records whether a child attempted network I/O. Lake still has compiled defaults such as the Reservoir API base URL, and arbitrary package configuration or subprocesses could in principle perform network operations independent of the path-dependency mechanism. Thus a successful test run is evidence for a self-contained prepared state under the tested environment, not proof of process-wide zero-network behavior.

Basis: current **source/test contract** in `anneal/src/main.rs`; pinned Lake **source** in `Lake/Config/Env.lean`.

### Current Lake's top-level `--offline` flag is not the missing hard guarantee

The pinned Lake CLI includes an `offline : Bool` field and parses `--offline`. But `LakeOptions.mkLoadConfig`, which ordinary workspace-loading commands use, does not copy that field into `LoadConfig`. Existing pinned-source analysis therefore finds that ordinary `lake build --offline` is not a comprehensive network-denial mechanism at this revision; `new`/`init` use the option in narrower initialization paths.

Current Anneal's archive-reuse command does not pass `--offline` anyway. It runs:

- `lake --keep-toolchain --old build Generated`; and
- `lake --keep-toolchain env lean --json generated/Generated.lean`.

The practical offline property comes from the prepared graph and local toolchain state, not from a top-level Lake flag. Adding `--offline` to the current command line without revalidating Lake would therefore create a misleading sense of enforcement.

Basis: pinned Lake **source** in `Lake/CLI/Main.lean`; current Anneal **source/test contract**.

### Prebuilt artifacts and source vendoring solve different offline failure modes

The current toolchain carries both a local package graph and selected prebuilt Lake outputs. These are independent parts of the offline contract.

The path-vendored source/configuration graph prevents Lake from needing a Git clone/fetch merely to materialize and load the workspace. The prebuilt `.lake` products and timestamp/trace preparation aim to prevent expensive rebuilds that could require additional source/tool behavior. Neither part substitutes for the other:

- a complete cache with a missing or remotely described dependency graph can still trigger source materialization;
- a completely local path graph can still rebuild if the prepared artifacts are stale or incomplete; and
- a rebuild from local sources can still be network-free if every invoked build action is local, but that must be established separately rather than inferred from source materialization.

Current Anneal's producer explicitly seeds Mathlib build products into its vendored package tree so the offline-oriented build does not rebuild Mathlib or its dependencies from source. The final archive then includes the Aeneas, Lean, and Rust toolchain roots and checks for representative executables and Mathlib `.olean` artifacts.

Basis: current **source** in `anneal/flake.nix`; existing Lake source-materialization and cache-boundary evidence.

### V2 does not yet expose a production verification execution path

The V2 `Commands` enum in `anneal/src/main.rs` currently contains only `Setup(SetupArgs)`. The archive-reuse Lake commands live under tests guarded by the `exocrate_tests` feature. The current Anneal workflow builds the omnibus archive and runs V2 `cargo test --workspace --all-features`, which is intended to exercise those tests, but this report did not obtain a workflow run associated with the exact current commit through the available workflow query.

Accordingly, claims about “current V2 execution” must be phrased as **packaging/test-contract behavior**, not as a complete user-facing V2 verifier guarantee. Retained V1 has its own verification command and historical execution evidence, but V1 is explicitly not architectural authority for V2 except where the current corpus preserves it as history.

Basis: current **source** and workflow definition; no fresh execution transcript.

### Archive production is a separate network phase from archive consumption

Building the omnibus archive is not itself an offline consumer operation. `anneal/flake.nix` contains fixed-output/download stages for the Aeneas release, Rust and Lean toolchains, Mathlib cache artifacts, and other upstream inputs. Its Mathlib-cache download stage explicitly uses Lake cache download machinery and network-capable tools; the workflow can also restore Nix binary caches and build missing inputs.

The final archive is therefore best understood as a **materialization boundary**: network-dependent acquisition can happen once in the producer/release pipeline so that downstream consumers can operate from the resulting local artifact and installed tree. “Anneal can consume a prepared archive offline” must not be rewritten as “the archive can be produced without network access.”

Basis: current **source** in `anneal/flake.nix` and `.github/workflows/anneal.yml`.

## Boundaries

**No fresh network-denied execution.** This report did not run `cargo anneal setup`, Exocrate, Lake, Lean, Nix, or a verification workload under `unshare`, a firewall, a seccomp policy, a network namespace, or syscall tracing. Source and checked-in tests establish control flow; they do not replace a negative execution probe for unexpected sockets.

**No claim that local installation authenticates the archive.** `--local-archive` removes the remote download, but Exocrate's local source does not carry the remote SHA-256 check. Trust/checksum semantics are covered separately.

**No claim that an existing installation is intact.** Exocrate's fast path is based on the managed directory's existence/type. It does not rehash the installed tree before reuse.

**No claim that path dependencies make arbitrary package code offline.** Path materialization itself has no Git clone/fetch, but package configuration, hooks, scripts, external binaries, or future code can have their own network behavior.

**No claim that `--old` means offline.** `--old` affects Lake build freshness; it is not a network policy. Likewise, cache controls such as `LAKE_NO_CACHE` govern particular cache paths rather than all network access.

**No cross-version Lake generalization.** The `--offline` propagation and materialization findings are pinned to Lean/Lake `v4.30.0-rc2`. A later Lake release may change those semantics.

**No production V2 verifier claim.** V2 currently exposes only `setup`; the described Lake commands are packaging/test machinery. A future verify/LSP/MCP command must establish its own offline behavior, including every subprocess it introduces.

**No statement that current placeholder remote metadata is usable.** The remote path exists in code, but the checked-in URLs/hashes are explicitly placeholders before crate publication.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-27.

Current Anneal/Exocrate source at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`:

- `anneal/src/main.rs`, blob `b947700606677ea89c7a205f3ffcc75493508f63`: V2 CLI; local/remote source selection; existing setup call; archive-reuse workspace construction; path-only inherited-manifest requirement; `env_clear()` Lake invocations.
- `exocrate/src/lib.rs`, blob `88cc0d5dd91082070b6ef475a32bf42c25f52115`: existing-installation fast path; `ureq::get` remote source; local `File::open` source; installation interface.
- `anneal/flake.nix`, blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`: upstream materialization; Mathlib cache download; vendored packages; offline-oriented build preparation; omnibus archive contents and checks.
- `anneal/rewrite-lake-vendor.py`, blob `e61fc992837435a43b3e434ddd3b07aa7d13b48c`: rewrite of Lean/TOML requirements and manifests to relative local path dependencies.
- `anneal/Cargo.toml`, blob `9edee13427fd5e3699abd3709cc9f33d7652873e`: current Exocrate platform metadata and explicit placeholder-remote FIXME.
- `.github/workflows/anneal.yml`, blob `39f648acb45681707bb5f51624c279b44fa2e832`: archive producer job, immutable workflow-artifact fan-out, and V2 all-features test command.

Pinned Lake source at `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`):

- `src/lake/Lake/CLI/Main.lean`, blob `65b0e7fd0d6cd21d512edb49a276bcc65ae31c78`: `offline` option parsing, `mkLoadConfig`, `--keep-toolchain`, `--old`, and command loading behavior.
- `src/lake/Lake/Load/Workspace.lean`, blob `9f25dd62bc752ede695a25fc20371157eb65d64b`: manifest reuse versus update/materialization choice.
- `src/lake/Lake/Load/Materialize.lean`, blob `e098e5adbbf33a641fa5cf7d37d0bbd371956f4b`: path versus Git package materialization and locked-HEAD no-fetch/update behavior.
- `src/lake/Lake/Load/Resolve.lean`, blob `ec7c9978ab99b9a998a1c24d5e1e7ecce3cfa928`: manifest-driven recursive dependency materialization.
- `src/lake/Lake/Config/Env.lean`, blob `eed315c538de746a891d18f72564e88aea64e969`: default Reservoir/cache environment construction and network/cache-related environment variables.

Related durable corpus/candidate evidence used to avoid duplicate work:

- published `lake-readonly-relocation-offline-concurrency-v4-30-0-rc2`: broader Lake read-only/offline/concurrency authority boundary, including the fact that `--offline` is not a complete ordinary-build contract at this pin;
- current-profile ready candidate `9f8d8faf-58e0-4282-89b6-77d9d81a083a`: exact Lake source-materialization and prebuilt-tree clone/fetch behavior plus current Anneal path-vendoring synthesis;
- current-profile Exocrate candidates for remote checksum, local archive trust, archive extraction security, archive read-only behavior, and cache/version identity.

Evidence roles in this report are **source**, **checked-in test/workflow contract**, **published corpus evidence**, and **derived cross-layer synthesis**. There is no new **execution** evidence.

## Revalidation

For a future Anneal/Exocrate/Lake revision, revalidate the offline contract as a matrix rather than as one boolean.

First, revalidate installation source behavior:

1. Confirm whether setup still distinguishes local and remote archive sources.
2. Confirm the existing-installation check still happens before source opening.
3. Confirm remote opening still has a single explicit network boundary and local opening remains filesystem-only.
4. Record any new signature, checksum, repair, or remote metadata service that can introduce additional I/O.

Second, revalidate the prepared Lake graph:

1. Enumerate every manifest entry in the packaged dependency universe and require the intended source kind.
2. Confirm vendored dependencies are rewritten before Git metadata is removed.
3. Confirm the generated root manifest rejects or otherwise controls any remote-capable source kind.
4. Revalidate Lake's exact path/Git materialization semantics at the selected Lean revision.
5. Distinguish source materialization from build/cache reuse; do not use the presence of `.olean` files as evidence that no dependency acquisition can occur.

Third, run a **hard offline execution probe** at the exact selected revision. The minimum useful matrix is:

| Case | Setup | Expected result |
| --- | --- | --- |
| Fresh remote install | empty installation; network namespace denied | fails at the explicit remote HTTP boundary |
| Fresh local install | valid local archive; empty installation; network denied | installation succeeds without network |
| Existing install + remote source | complete existing version directory; remote unreachable | resolves existing installation without source access |
| Prepared V2 archive consumer | path-only archive; fresh generated workspace; network denied | Lake build/Lean check succeeds without clone/fetch/download |
| Corrupt source-kind invariant | one inherited manifest entry changed to Git; network denied | consumer rejects before Lake, or Lake fails in a documented way; must not silently fetch |
| Missing prepared artifact | path-only sources retained; selected cached output removed; network denied | behavior distinguishes a local rebuild from an attempted remote cache/source fetch |
| Hostile network-capable hook | deliberately instrumented package/config hook | network sandbox proves denial rather than merely observing no ordinary fetch |

Use an OS-level network-denial mechanism, not only `--offline`. Preserve the exact archive digest, installation path/version slug, generated manifest, command line, sanitized environment, stdout/stderr, process tree, and network/syscall trace. On Linux, a network namespace or equivalent firewall plus `strace`/eBPF observation would separate “would have attempted the network” from “happened not to.” Use a platform-appropriate equivalent on macOS.

Finally, if V2 gains a public `verify`, LSP, or MCP execution mode, repeat the matrix for the complete spawned-process graph. The present setup/test contract is not automatically inherited by new Charon, Aeneas, Lean-server, package-hook, or agent-tool subprocesses.
