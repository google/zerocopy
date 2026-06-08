# June 5-7 @joshlf Anneal Changes

This summary covers the Anneal-related work that landed or was pushed during
June 5-7, 2026. There were two distinct streams of activity:

1. `@joshlf` merged mainline PRs that move Anneal v1 setup and CI onto the
   Nix-built toolchain archive path.
2. `@joshlf` force-pushed amended commits onto `@mdittmer`'s open Anneal v2 PR
   stack. Those commits still list Mark as author, but Joshua as committer.

## Source Links

Mainline source at `origin/main` commit `83dbc577c`:

- Anneal v1 setup: <https://github.com/google/zerocopy/blob/83dbc577c/anneal/src/setup.rs>
- Anneal v1 Aeneas/Lake materialization and symlink handling: <https://github.com/google/zerocopy/blob/83dbc577c/anneal/src/aeneas.rs#L341-L430>
- Anneal v1 `lake --old` invocation: <https://github.com/google/zerocopy/blob/83dbc577c/anneal/src/aeneas.rs#L562-L572>
- Anneal v1 exocrate metadata: <https://github.com/google/zerocopy/blob/83dbc577c/anneal/Cargo.toml#L24-L41>
- Anneal v1 build-time metadata export: <https://github.com/google/zerocopy/blob/83dbc577c/anneal/build.rs#L22-L90>
- Shared exocrate installer: <https://github.com/google/zerocopy/blob/83dbc577c/exocrate/src/lib.rs>
- Anneal v2 Nix archive build: <https://github.com/google/zerocopy/blob/83dbc577c/anneal/v2/flake.nix#L292-L456>
- Anneal v2 Lake vendor rewriting: <https://github.com/google/zerocopy/blob/83dbc577c/anneal/v2/rewrite-lake-vendor.py#L129-L179>
- Anneal v2 cache pruning: <https://github.com/google/zerocopy/blob/83dbc577c/anneal/v2/prune-lake-cache.py#L80-L193>
- Anneal CI workflow: <https://github.com/google/zerocopy/blob/83dbc577c/.github/workflows/anneal.yml#L253-L356>
- Anneal release workflow: <https://github.com/google/zerocopy/blob/83dbc577c/.github/workflows/anneal-release.yml#L210-L380>

Relevant PRs:

- <https://github.com/google/zerocopy/pull/3438> - `[anneal] Move setup and CI onto Nix archive`
- <https://github.com/google/zerocopy/pull/3440> - `[anneal][release] Add exocrate archive metadata helpers`
- <https://github.com/google/zerocopy/pull/3441> - `[anneal][release] Publish Nix-built toolchain archives`
- <https://github.com/google/zerocopy/pull/3443> - `[anneal] Keep vendored Lake inputs older than archive caches`
- <https://github.com/google/zerocopy/pull/3444> - `[anneal][v2] Stabilize Nix omnibus archive builds`
- <https://github.com/google/zerocopy/pull/3445> - `[anneal][release] Upload toolchain archives before publishing release`
- <https://github.com/google/zerocopy/pull/3446> - `Release Anneal 0.1.0-alpha.24`

Open `@mdittmer` v2 stack amended by `@joshlf`:

- <https://github.com/google/zerocopy/pull/3398> - `[anneal][v2] Add Cargo dependencies`
- <https://github.com/google/zerocopy/pull/3399> - `[anneal][v2] Add utility functions: environment helpers and DirLock`
- <https://github.com/google/zerocopy/pull/3400> - `[anneal][v2] Add exocrate toolchain setup and Toolchain resolver`
- <https://github.com/google/zerocopy/pull/3401> - `[anneal][v2] Add Cargo workspace resolution and target resolution logic`
- <https://github.com/google/zerocopy/pull/3402> - `[anneal][v2] Add scanner module to map workspace packages to AnnealArtifacts`
- <https://github.com/google/zerocopy/pull/3403> - `[anneal][v2] Add DiagnosticMapper to map compiler errors back to Rust source code`
- <https://github.com/google/zerocopy/pull/3404> - `[anneal][v2] Add charon execution engine, expand command CLI, and integration tests`
- <https://github.com/google/zerocopy/pull/3405> - `[anneal][v2] Implement out-of-tree dependency chasing for expand command`
- <https://github.com/google/zerocopy/pull/3418> - `[anneal][v2] Add pinned charon_lib dependency`
- <https://github.com/google/zerocopy/pull/3436> - `[anneal][v2][exocrate] Add install fixup hook`

## What Landed On Main

### v1 setup now consumes the Nix-built archive

PR #3438 replaced the older v1 setup path with an exocrate-backed installer.
The v1 `setup` command now resolves a versioned toolchain directory under
`.anneal/toolchain` using metadata generated from `Cargo.toml`, `Cargo.lock`,
and the host platform. The archive layout is shared with the v2 Nix build:
`aeneas`, `lean`, `rust`, and the Lake cache live under the installed
toolchain root.

This makes v1 setup behave more like v2: CI first builds or downloads the same
Nix-produced archive, then v1 installs it with:

```text
cargo run --features __install_exocrate -- setup --local-archive ...
```

The important shift is that v1 no longer has a bespoke setup path that fetches
and arranges Aeneas, Lean, Rust, and Lake artifacts separately. It consumes the
same archive shape produced by the v2 flake.

### v2 owns the archive construction

PR #3444 stabilized the v2 Nix archive build. The flake now does the heavy
assembly work:

- downloads platform-specific Aeneas, Rust, Lean, and `leantar` inputs;
- downloads and unpacks the Mathlib cache;
- rewrites Lake dependencies to path dependencies;
- seeds package `.lake/build` directories with cache artifacts;
- rewrites trace files so absolute Nix and checkout paths do not leak into the
  final bundle;
- prunes unused Mathlib artifacts;
- runs layout and relocatability checks; and
- emits a portable `anneal-exocrate.tar.zst` archive.

In effect, v2 is now the build-system owner for the toolchain bundle consumed
by both v2 and v1.

### Release automation now publishes those archives

PRs #3440, #3441, #3445, and #3446 added and exercised release support for the
Nix-built archives:

- #3440 added archive metadata helpers.
- #3441 taught the release workflow to build and publish toolchain archives.
- #3445 changed ordering so the toolchain archives are uploaded before the
  crate release metadata is finalized.
- #3446 released `anneal` `0.1.0-alpha.24`, with `Cargo.toml` pointing to the
  published platform archives and expected SHA-256 values.

### CI now fans out from one archive build

The Anneal GitHub workflow now builds the Nix archive in a dedicated job and
uses it for v1 setup/tests and examples. The workflow also restores/saves Nix
caches and performs archive size/layout checks. This is a real simplification
for CI topology: the expensive archive build is centralized instead of being
implicitly reconstructed by every consumer job.

## What Was Pushed Onto Mark's v2 PR Stack

On June 7, `@joshlf` force-pushed amended commits onto Mark's open v2 PR stack.
The latest commits are still authored by Mark but were committed by Joshua.
The notable changes are:

- #3398 was changed from checked-in vendored Cargo dependencies to normal Cargo
  dependencies/lockfile updates. The giant `anneal/v2/vendor` approach was
  removed from that PR.
- #3418 likewise changed from vendoring `charon_lib` to adding a pinned
  dependency.
- #3399 through #3403 were mostly rebased with little or no patch-level change.
- #3404 gained feature-gating around exocrate-heavy tests and minor cleanup in
  the Charon/integration-test area.
- #3405 kept the out-of-tree dependency chasing work, but simplified one
  integration fixture by generating a small synthetic `log` path dependency
  instead of copying/truncating a real vendored crate. The current commit notes
  that some generated test plumbing still deserves review.
- #3436 moved the install fixup hook out of v2-specific setup code and into the
  shared top-level `exocrate` crate, because the installer is now shared by v1
  and v2 archive consumers.

The direction of these changes is consistent: avoid checking huge generated
vendor trees into the v2 Rust crate, keep archive construction in Nix, and move
installation behavior into the common exocrate layer.

## v1's Extra Complications

The new v1 setup path consumes the v2-style archive, but v1 still cannot simply
point Lake at the installed read-only archive in place. v1 generates a fresh
Lean workspace for each target Rust crate, and that generated workspace needs
path dependencies to Aeneas and its vendored Lake packages.

The current bridge is manual tree materialization:

- v1 copies Aeneas Lean sources and package metadata from the installed
  toolchain into the generated workspace;
- it preserves ordinary symlinks while copying;
- when it reaches a Lake build directory, it creates a symlink from the
  generated workspace back to the installed toolchain's `.lake/build` cache
  rather than copying several GiB of `.olean` and trace data;
- it makes copied files writable; and
- it normalizes Lake input mtimes to the Unix epoch and runs `lake --old`.

The mtime normalization plus `lake --old` keep Lake from deciding that the
copied inputs are newer than the prebuilt artifacts. The symlinked
`.lake/build` directories avoid the cost and disk usage of copying the Nix-built
cache into every generated v1 workspace.

That is the main complexity retained or reintroduced for v1: the archive is
built in a Nix/v2 style, but v1 still materializes a per-invocation workspace
and manually symlinks build-cache directories back to the shared installed
archive.

## Relationship To The Symlink Question

The v2 flake already demonstrates a cleaner model at archive-build time: create
path dependencies, seed their `.lake/build` directories with valid artifacts,
rewrite traces to portable paths, prune what is not needed, and freeze inputs so
Lake does not rebuild. The v1 implementation uses the result of that process,
but then reconstructs enough of the dependency tree inside each generated
workspace that it needs manual symlinks to avoid copying the expensive cache.

The open question for the June 8 investigation is whether v1 can instead
generate a workspace that directly uses a symlink-free, portable, prebuilt
package layout. The goal would be to preserve the performance benefits of
shared cache artifacts while removing per-run symlink management from the Rust
setup/build path.
