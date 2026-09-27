# Aeneas nightly-2026.06.03 release archive anatomy

## Summary

The Aeneas `nightly-2026.06.03` release publishes four platform-specific `tar.gz` archives: Linux and macOS, each for x86_64 and AArch64. The release workflow builds a common staged tree containing the `aeneas`, `charon`, and `charon-driver` executables, the full `backends/` source tree, and Charon's `rust-toolchain` file. It then precompiles the Lean backend in place before creating the final archive.

The archive is not an omnibus offline toolchain. It does not stage a Lean executable or Elan installation. The Lean precompile step uses the runner's Lean toolchain, builds the Aeneas Lean package, and then deletes `backends/lean/.lake/packages`, so dependency source checkouts are deliberately absent from the final staged tree. The checked-in Lake manifest still records the exact Mathlib dependency graph needed to reconstruct them.

Platform differences are intentionally narrow at the packaging layer. Linux selects Aeneas' static release derivation. macOS selects the ordinary release derivation and additionally rewrites the Aeneas executable's dynamic-library paths while bundling those libraries under `libs/`. All four variants use Charon's portable binaries and the same backend source tree.

This report reconstructs archive composition from the exact release workflow and Nix package definitions and verifies the four published asset names, sizes, and SHA-256 digests through the GitHub release record. It did not download and unpack the archive bytes, so exact post-tar file listings, permissions, timestamps, and binary linkage remain a separate execution check.

## Applicability

The findings apply to Aeneas release `nightly-2026.06.03`. The tag directly names commit `ac9f1bc5262a5e4ff1e24ca78617121382202727`; the packaging workflow, Nix release derivations, backend sources, and precompile script were examined at that exact commit.

The four binary release assets are identified separately by SHA-256 in `REPORT.json`. GitHub reports this release as a prerelease and reports the release object as mutable. The artifact digests are therefore the stronger identity for the exact downloadable bytes.

The report describes the binary release assets uploaded by `.github/workflows/release.yml`. GitHub's automatically generated source `tarball_url` and `zipball_url` are different artifacts: they are source snapshots of the tag, not the platform release archives described here.

The archive contents below are reconstructed from the staging and repackaging commands. Published asset metadata confirms that four archives with the expected names were uploaded. This run did not independently extract those assets to prove that every inferred staged entry is present byte-for-byte.

## Findings

### The release is a four-asset platform matrix

The workflow creates one prerelease named `nightly-YYYY.MM.DD` and then runs four independent build jobs:

| Asset | Build runner | Aeneas Nix attribute | Published size |
| --- | --- | --- | ---: |
| `aeneas-linux-x86_64.tar.gz` | self-hosted Linux/Nix | `aeneas-static-release` | 60,715,544 bytes |
| `aeneas-linux-aarch64.tar.gz` | Ubuntu 24.04 ARM | `aeneas-static-release` | 62,392,219 bytes |
| `aeneas-macos-x86_64.tar.gz` | macOS 15 Intel | `aeneas-release` | 60,658,870 bytes |
| `aeneas-macos-aarch64.tar.gz` | current macOS ARM runner | `aeneas-release` | 61,499,346 bytes |

Each build copies the Nix result into a writable `dist_staging/`, precompiles Lean there, repacks the directory as `tar.gz`, extracts it into a fresh staging directory, and runs `./aeneas --help` as the release smoke test.

Basis: **source** in `.github/workflows/release.yml` plus **release metadata** from GitHub's exact `nightly-2026.06.03` release record.

### The common archive root contains three executables, all backends, and Charon's Rust pin

`mk-aeneas-release` constructs the initial release tree with these root entries:

```text
aeneas
charon
charon-driver
rust-toolchain
backends/
```

`aeneas` comes from the selected Aeneas package. `charon` and `charon-driver` come from Charon's `charon-portable` package. `backends/` is copied recursively from the Aeneas source tree and therefore includes the Coq, F*, HOL4, and Lean backend sources.

The top-level `rust-toolchain` is not copied from an Aeneas-local toolchain declaration. The Nix expression explicitly copies `${inputs.charon}/rust-toolchain`. At the Charon revision pinned by this Aeneas release, that file selects `nightly-2026-05-31` and requests `rustc-dev`, `llvm-tools-preview`, `rust-src`, and `miri`.

This is useful for release consumers: the archive itself carries the Rust/Charon compiler pin needed to produce compatible LLBC, rather than requiring the consumer to infer it from the Aeneas version string.

Basis: **source** in `flake.nix` and `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0/rust-toolchain`.

### macOS adds bundled Aeneas dynamic libraries; Linux selects the static Aeneas derivation

The Linux matrix entries build `aeneas-static-release`; macOS builds `aeneas-release`. Both feed the same `mk-aeneas-release` staging function and therefore preserve the same basic archive layout.

On Darwin, `mk-aeneas-release` additionally runs `dylibbundler` on `./aeneas`. It rewrites the executable's dependency load paths to `@executable_path/libs` and places bundled libraries under a root `libs/` directory.

The source does not apply this bundling step to `charon` or `charon-driver`; those executables come from the separately defined `charon-portable` package. The report therefore does not infer their linkage details from Aeneas' Darwin bundling step.

Basis: **source** in `flake.nix`; the limitation on Charon linkage is **derived** from the scope of the bundling command.

### The Lean backend is built into the staged archive, but its dependency source checkouts are deleted

After copying the Nix release result, every matrix job enters `dist_staging/backends/lean` and runs `scripts/ci-precompile-lean.sh`.

That script:

1. selects the toolchain named by `lean-toolchain`;
2. attempts `lake exe cache get` for precompiled Mathlib artifacts, but continues if cache extraction fails;
3. runs `CI="" lake build`, deliberately overriding CI behavior so shared libraries needed for plugin loading are compiled;
4. deletes `.lake/packages`.

At this release, `backends/lean/lean-toolchain` names `leanprover/lean4:v4.30.0-rc2`. The checked-in `lake-manifest.json` pins Mathlib to commit `5450b53e5ddc75d46418fabb605edbf36bd0beb6` and records the transitive Lake package revisions.

The resulting archive therefore preserves the Aeneas Lean project sources and the project-local build state created by `lake build`, while deliberately omitting the dependency source checkouts that Lake materialized under `.lake/packages`.

Basis: **source** in `scripts/ci-precompile-lean.sh`, `backends/lean/lean-toolchain`, and `backends/lean/lake-manifest.json`.

### The release archive does not bundle the Lean toolchain

The release job installs Elan on build runners that do not already provide the Nix environment, and the precompile script uses Elan to select the checked-in Lean version. Neither the Nix release staging function nor the later repackaging command copies Elan or a Lean distribution into `dist_staging`.

The release archive therefore records which Lean toolchain to obtain and carries precompiled Aeneas Lean state, but it is not itself a self-contained Lean runtime. A consumer that needs to execute Lean must provide the selected Lean toolchain by some other mechanism.

This distinction matters for Anneal packaging: an Aeneas release archive can be one input to an offline omnibus toolchain, but the upstream Aeneas archive alone is not that omnibus.

Basis: **source** in `.github/workflows/release.yml`, `flake.nix`, and `scripts/ci-precompile-lean.sh`; the consumer consequence is **derived**.

### Removing `.lake/packages` means the release is not a complete offline Lean dependency universe

The checked-in Aeneas Lean manifest declares Mathlib and its transitive Git dependencies under `.lake/packages`. The release precompile script explicitly removes that directory after building.

Consequently, the upstream release does not retain those dependency source trees even when they were available during precompilation. The manifest preserves their exact revisions and allows them to be reconstructed, but reconstruction may require external source material unless a downstream package supplies it separately.

This is narrower than saying the archive cannot be used offline at all. The Aeneas executable and bundled backend source/build material may be usable without network access for some operations. The exact offline behavior of a downstream Lean consumer depends on what it asks Lake/Lean to resolve and what additional dependency/toolchain material the downstream package provides.

Basis: **source** plus **derived** consequence from the manifest location and explicit `rm -rf .lake/packages`.

### The final release smoke test verifies only the Aeneas executable

After producing each final `tar.gz`, the workflow extracts the archive and runs:

```console
./aeneas --help
```

The smoke test does not invoke `charon`, `charon-driver`, `lake`, or `lean`, and it does not compile a Lean consumer project from the final post-pruning archive.

The release process therefore establishes a direct final-archive execution check for `aeneas` itself, but not an equivalent final-archive check for the other bundled tools or backend workflows.

Basis: **source** in `.github/workflows/release.yml`.

### Exact asset identity is available even though the GitHub release object is mutable

GitHub's release record reports `immutable: false`, but each of the four uploaded assets has a SHA-256 digest:

- Linux x86_64: `00fb8ef427d4d06dcabd90f5196266e07731adf2a7466964ce6f4f6d1e8cbc11`
- Linux AArch64: `25402c4cbcb7da2d337cb168663542bc9c75ae9b10d2d2708f5289e8ca9d1902`
- macOS x86_64: `ba25ee857a76fa8f4c1022f6dff4072c9a01007453d67c61cfbaa1aa1c03e317`
- macOS AArch64: `76f78b645e338ec7e89329f0ad22792997f42bd9b5eb14643ac32ade224eeb61`

A downstream reproducibility or Nix rule should bind the chosen asset by digest rather than treating the release name alone as immutable identity.

Basis: **release metadata** plus **derived** identity guidance.

## Boundaries

**Exact final tar listings were not examined.** This run could not download and unpack the release assets. Archive composition is reconstructed from the exact staging/repackaging source and release metadata, not from an independently enumerated tar member list.

**Permissions, timestamps, ownership, and compression metadata were not characterized.** The workflow changes staged files to writable before precompilation and then runs ordinary `tar -czf`, but this report does not claim byte-level reproducibility or normalized metadata.

**Binary linkage was not inspected.** The source establishes that macOS runs `dylibbundler` on `aeneas` and Linux selects the static Aeneas derivation. It does not, by itself, establish the complete runtime-library dependency set of each final executable.

**No complete offline guarantee is claimed.** The archive omits Lean itself and removes `.lake/packages`. Whether a specific operation is offline depends on the operation and on downstream-provided toolchain/dependency material.

**No final-archive Lean execution was observed.** The workflow precompiles the Lean project before repackaging, but its final archive smoke test only runs `aeneas --help`.

**The GitHub release is not an immutable container.** The observed release record says `immutable: false`. The tag currently resolves directly to the pinned commit and the assets have strong digests; later mutation of the release object should be detected by rechecking those identities.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-27.

Primary source subject: `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, tag `nightly-2026.06.03`.

- `.github/workflows/release.yml`, blob `e248e9fdbecb3809f54ef58456db3faee448175f`: nightly tag/release creation, four-platform build matrix, staging, Lean precompile, tar creation, final `aeneas --help` smoke test, and upload.
- `flake.nix`, blob `05e71549416ac622d6f12edc1fc7c74e338949ba`: `aeneas-release`, `aeneas-static-release`, `mk-aeneas-release`, root archive staging, Charon portable binaries, Charon `rust-toolchain`, and Darwin `libs/` bundling.
- `scripts/ci-precompile-lean.sh`, blob `36287bb77a71c66326bcd3816ada526d41a5dee2`: Lean toolchain selection, Mathlib cache attempt, `CI="" lake build`, and `.lake/packages` deletion.
- `backends/lean/lean-toolchain`, blob `6c7e31fffe3e03be3e0d7021acd9cd848e44db26`: Lean `v4.30.0-rc2`.
- `backends/lean/lake-manifest.json`, blob `1a5af703163d8b39f4311aafe22ae171788179ee`: Mathlib and transitive dependency pins.
- `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0/rust-toolchain`, blob `4e348edab20d6bd5b195e758afe20f9d8258a3e1`: Rust `nightly-2026-05-31` and required components/targets.
- GitHub tag API: `refs/tags/nightly-2026.06.03` directly identifies commit `ac9f1bc5262a5e4ff1e24ca78617121382202727`.
- GitHub release API, release id `333508110`: prerelease metadata and the four uploaded asset names, sizes, ids, timestamps, and SHA-256 digests.

`release-assets.json` preserves the exact release-API asset identity fields used by this report. `source-map.json` preserves the source blobs and their evidence roles.

Evidence roles are **source**, **release metadata**, and **derived**. There is no fresh archive-extraction or executable **execution** evidence in this report.

## Revalidation

For another Aeneas release, first resolve the release tag to an immutable commit and read `.github/workflows/release.yml`, `flake.nix`, and `scripts/ci-precompile-lean.sh` at that commit. Those three files determine the matrix, staged root, platform-specific packaging, Lean precompile behavior, and final smoke test.

Then query the exact GitHub release record and preserve each binary asset's name, size, and digest. Compare the asset set with the workflow matrix rather than assuming every configured job uploaded successfully.

For the exact `nightly-2026.06.03` release, the cheapest missing discriminating probe is to download each asset by its recorded SHA-256, enumerate its tar members, and compare the four member sets. Record at minimum:

1. root entries and any platform-only paths such as `libs/`;
2. the surviving `backends/lean/.lake` subtree after `.lake/packages` removal;
3. file modes and symlink entries;
4. `file`, `ldd`/`otool -L`, or equivalent linkage output for `aeneas`, `charon`, and `charon-driver`;
5. successful `--help` execution for all three binaries;
6. whether a minimal Lean import can use the final archive with only the separately selected Lean toolchain and no network.

That probe would convert the inferred archive anatomy into direct final-asset evidence and would also answer the adjacent per-platform-content question without repeating the source reconstruction.
