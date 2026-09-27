# Nix fixed-output derivations used by Anneal for upstream archives and caches

## Summary

At `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, Anneal deliberately puts its network-derived toolchain inputs behind fixed-output boundaries before ordinary compilation and repackaging. The fixed-output layer covers the upstream Aeneas release archive, the synthesized Rust sysroot, the extracted Lean toolchain, the downloaded `leantar` release archive, and Mathlib's downloaded cache/package-source state.

Anneal uses two distinct hashing shapes. Single upstream archive files use Nixpkgs `fetchurl`. Multi-file or post-extraction results use custom fixed-output derivations with `outputHashMode = "recursive"`, `outputHashAlgo = "sha256"`, and platform-specific expected hashes. In those recursive cases, the hash commits to the resulting filesystem object rather than merely one downloaded archive byte stream.

The most important architectural boundary is Mathlib. A fixed-output derivation runs `lake exe cache get-` and records the downloaded `.ltar` cache plus dependency source material. A later ordinary derivation decompresses those archives and normalizes timestamps. The subsequent Aeneas/Lean build sets `MATHLIB_NO_CACHE_ON_UPDATE=1` and consumes already-materialized cache state. Network materialization and later build transformations are therefore separated rather than mixed into one ordinary build.

These hashes are integrity and reproducibility gates, not provenance signatures. They make changed outputs fail the expected-hash contract, but they do not prove who produced the bytes or that the configured expected hash was chosen from a trustworthy source.

## Applicability

This report describes the current Anneal Nix expression at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, specifically `anneal/flake.nix` blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`.

The expression supports four host systems:

- `x86_64-linux`;
- `aarch64-linux`;
- `x86_64-darwin`;
- `aarch64-darwin`.

The same upstream logical toolchain versions are selected across those systems, but Anneal records separate expected output hashes because the downloaded or reconstructed results are platform-specific.

The report uses Nix's documented fixed-output semantics to interpret the explicit `outputHash*` attributes. It does not claim a particular Nix executable version for the current Anneal flake: its `nixpkgs` input follows `nixos-unstable`, and the report did not execute the flake. The directly observed subject is Anneal's expression and its declared content identities.

This report is separate from the nearby #3720 subject on import-from-derivation/version extraction. `packages.test-ifd` consumes metadata from `aeneas-unpacked` and reconstructs dynamic Rust/Lean derivations using the already-declared output hashes, but the evaluation mechanics of that IFD path deserve their own report.

## Findings

### Anneal has five upstream acquisition boundaries with fixed expected content

`anneal/flake.nix` contains five materially distinct fixed-output acquisition patterns.

1. **Aeneas release archive.** `fetchAeneas` calls `pkgs.fetchurl` on `aeneas-${target}.tar.gz` from the selected GitHub release and supplies one platform-specific SHA-256.
2. **Rust toolchain.** `fetchRustToolchain` uses Anneal's `fetchToolchainAsset` helper. Its build downloads and merges Cargo, rustc, rust-std, rustc-dev, LLVM tools, Miri, and rust-src into one output directory. The complete directory is checked against a platform-specific recursive SHA-256.
3. **Lean toolchain.** `fetchLeanToolchain` uses the same helper to download and extract the selected Lean archive into `$out`, again under a platform-specific recursive SHA-256.
4. **`leantar`.** `fetchLeantar` uses `pkgs.fetchurl` for the platform-specific release archive. An ordinary derivation then unpacks that already hash-gated archive into a small executable package.
5. **Mathlib cache download.** `packages.mathlib-cache-download` is an explicit recursive fixed-output derivation. It runs `lake exe cache get-`, captures the downloaded `.ltar` cache and Lake dependency source material, sanitizes selected local metadata, and commits the resulting tree to one platform-specific SHA-256.

These are not interchangeable implementations of the same operation. The file fetchers bind an upstream archive object; the custom recursive derivations bind a synthesized or extracted filesystem tree.

Basis: **source** in `anneal/flake.nix` plus **documentation** from the Nix fixed-output derivation contract.

### `fetchToolchainAsset` hashes the extracted tree, not the downloaded archive

`fetchToolchainAsset` sets:

```nix
dontUnpack = true;
dontPatchShebangs = true;
dontPatchELF = true;
dontStrip = true;

outputHashMode = "recursive";
outputHashAlgo = "sha256";
outputHash = sha256;
```

Its callers put their own network and extraction commands in `buildPhase`. Nix's documented recursive/NAR mode hashes a filesystem object recursively, so Anneal's expected value applies to the constructed `$out` tree.

This distinction matters for Rust. The Rust toolchain is not fetched as one canonical upstream archive. Anneal downloads several dated component archives, extracts each, and overlays their payloads into one sysroot before the fixed-output check. The configured hash therefore identifies Anneal's merged sysroot result for that host system.

Lean also uses a recursive result hash even though the source is one tarball: the build decompresses the archive and strips its top-level directory before Nix validates the output tree.

Basis: **source** + **documentation**. Nix 2.30.3 documents that specifying `outputHash`, `outputHashAlgo`, and `outputHashMode` makes a fixed-output derivation and that recursive/NAR mode hashes the filesystem object recursively.

### Anneal suppresses automatic builder rewriting inside the recursive toolchain boundary

The shared helper disables shebang patching, ELF patching, and stripping. That choice keeps the fixed-output tree tied to Anneal's explicit download/extraction steps rather than to Nixpkgs' normal postprocessing hooks.

This does not mean the final Anneal archive is unmodified. Later ordinary derivations intentionally transform some binaries and filesystem state. For example, `packages.omnibus-tar` patches Linux ELF interpreters/RPATHs and strips executables after staging the assembled toolchain.

The fixed-output identity is therefore a boundary identity for upstream-materialized inputs, not the identity of the final omnibus archive.

Basis: **source**.

### Mathlib separates network acquisition from cache expansion

`packages.mathlib-cache-download` deliberately invokes:

```text
lake exe cache get-
```

rather than the ordinary `get` mode. The source comment states that `get-` downloads the linked `.ltar` files without decompressing them. The fixed-output derivation then preserves:

- the Mathlib cache files from `$TMPDIR/.cache/mathlib`;
- Lake dependency packages from `.lake/packages`.

Before finalizing that fixed output, it removes selected `.trace`/`.hash` files containing `/nix/store`, removes `mathlib/.lake`, and removes `.git` directories.

`packages.mathlib-cache-unpacked` is a later ordinary derivation. It copies the fixed package sources, expands every `.ltar` using the separately hash-gated `leantar`, and normalizes timestamps to the Unix epoch. The later `aeneas-compiled` derivation consumes this unpacked state and exports `MATHLIB_NO_CACHE_ON_UPDATE=1`, with an explicit comment that the cache was already fetched in the fixed-output derivation.

The fixed-output boundary therefore covers Anneal's sanitized downloaded cache/source state. It does not directly hash the final expanded cache tree or final Aeneas package.

Basis: **source**.

### Fixed-output content identities are per host system

Every current fixed-output family that produces host-specific binaries or cache state has a four-way hash table. `fod-inventory.json` in this report preserves the exact values.

The selected logical versions are shared:

- Aeneas: `nightly-2026.06.03`;
- Rust: `nightly-2026-05-31`;
- Lean: `v4.30.0-rc2`;
- `leantar`: `0.1.16`.

But the expected outputs vary across Linux/macOS and x86_64/AArch64. A later agent must therefore treat `{version, system, expected hash}` as a unit when reproducing one of these boundaries. Reusing a hash from a different platform is not a supported shortcut.

Basis: **source**.

### A fixed-output hash validates the result, not the retrieval location

Under Nix's fixed-output model, the expected output hash is known in advance and Nix rejects a result whose content does not match it. Consequently, changing an upstream URL without changing the resulting fixed output need not change the content identity, while changed output bytes/tree content require a matching expected-hash update.

That is useful for Anneal because upstream download operations may be impure while their admitted result is constrained. It does not turn the URL, release label, or builder script into part of the content identity.

The security boundary is correspondingly narrow: the configured hash detects output substitution relative to the expected content, but the flake author still chooses that expected hash. Nothing in this mechanism itself authenticates the upstream publisher or establishes that the selected bits are semantically safe.

Basis: **documentation** + **derived** application to Anneal.

### `fetchurl` and recursive fixed-output derivations serve different shapes

Nix's documented `fetchurl` pattern is a fixed-output fetch for one file. Anneal uses it where preserving an archive file as the network result is useful:

- the Aeneas release tarball;
- the `leantar` tarball.

Anneal uses custom recursive fixed-output derivations where the network result is naturally a directory tree assembled by multiple operations:

- merged Rust sysroot;
- extracted Lean toolchain;
- Mathlib cache plus dependency-source snapshot.

Later ordinary derivations may transform any of these fixed inputs. The presence of an ordinary transform after a fixed fetch is not a hole in the acquisition boundary; it means the later result is content-addressed through the normal dependency graph rather than itself declared as the same fixed output.

Basis: **source** + **documentation**.

### The Mathlib fixed output is intentionally more than raw download bytes

The Mathlib FOD performs deterministic-looking cleanup before Nix hashes its output: it deletes Git metadata, removes Mathlib's `.lake` directory, and deletes only trace/hash files that contain `/nix/store`.

That means its expected hash is not the SHA-256 of one upstream Mathlib cache artifact. It identifies the complete post-download, post-sanitization directory tree produced by this recipe. A hash update can therefore be caused by a change in any admitted cache file, dependency source, or cleanup-visible input.

This is important when diagnosing hash mismatches. Treat `mathlibCacheDownloadSha256` as an Anneal materialization hash, not an upstream release checksum.

Basis: **source** + **derived** consequence of recursive output hashing.

### IFD reuses the fixed-output contract rather than discovering new hashes

`packages.test-ifd` reads metadata generated from the selected Aeneas archive and uses it to reconstruct Rust and Lean derivations dynamically:

```nix
dynamicRust = fetchRustToolchain {
  inherit rustDate;
  sha256 = self.packages.${system}.rust-toolchain.outputHash;
};

dynamicLean = fetchLeanToolchain {
  inherit leanVersion;
  sha256 = self.packages.${system}.lean-toolchain.outputHash;
};
```

The dynamically recovered versions can therefore select URLs/build logic, but they do not supply freshly discovered expected hashes. The hash continues to come from Anneal's statically configured platform-specific fixed-output declaration.

This report records that boundary because it prevents a misleading interpretation of `test-ifd`: the test demonstrates dynamic version wiring against known content identities, not arbitrary unpinned network acquisition.

Basis: **source**. Detailed IFD evaluation semantics are **not examined** here.

## Boundaries

**No fresh Nix build.** This run inspected the exact flake and Nix documentation but did not execute any derivation, intentionally corrupt a hash, or test sandbox/network behavior.

**No claim that ordinary derivations are network-isolated on every host.** The architecture places intended network materialization in fixed-output derivations, but actual Nix sandbox/network policy depends on the executing Nix configuration and platform. This report does not upgrade that design intent into a host-independent runtime guarantee.

**No complete upstream provenance guarantee.** Expected SHA-256 values constrain admitted outputs. They do not authenticate the party that selected those values, verify release signatures, or establish semantic correctness.

**No claim that the fixed-output hash equals an upstream archive checksum unless the fixed output is that archive.** `fetchurl` cases are file-oriented. Rust, Lean, and Mathlib custom FODs use recursive filesystem-output hashing.

**No claim that later ordinary outputs are fixed-output derivations.** `mathlib-cache-unpacked`, `aeneas-compiled`, `omnibus-tar`, and `omnibus-archive` are downstream ordinary derivations in this expression.

**Import-from-derivation is adjacent scope.** `packages.test-ifd` is inspected only enough to show how it reuses existing fixed-output hashes. Evaluation-time dependency/version extraction belongs to the separate #3720 IFD subject.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-27.

Primary implementation source:

- `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `anneal/flake.nix`, blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`.
  - `fetchAeneas`;
  - `fetchToolchainAsset`;
  - `fetchRustToolchain`;
  - `fetchLeanToolchain`;
  - `fetchLeantar`;
  - `packages.mathlib-cache-download`;
  - `packages.mathlib-cache-unpacked`;
  - `packages.aeneas-compiled`;
  - `packages.test-ifd`.

Nix semantic references:

- Nix 2.30.3 Reference Manual, “Advanced Attributes”: fixed-output derivations require `outputHash`, `outputHashAlgo`, and `outputHashMode`; recursive/NAR mode hashes a filesystem object recursively.
- Nix 2.22 Reference Manual, “Advanced Attributes”: includes the simplified `fetchurl` fixed-output example and flat-versus-recursive distinction.

These Nix pages document the language semantics used to interpret Anneal's expression; they do not identify the exact Nix binary used by this commit.

Preserved report support material:

- `fod-inventory.json`: exact current platform/version/hash matrix and fixed-output boundary classification.
- `source-map.json`: implementation symbols, source identity, and documentation references.

Evidence roles: **source**, **documentation**, and **derived**. There is no fresh **execution** evidence.

## Revalidation

For another Anneal revision, inspect `anneal/flake.nix` before doing broader archaeology.

1. Search for `pkgs.fetchurl`, `outputHash`, `outputHashMode`, `curl`, `lake exe cache`, and any new downloader helpers.
2. Reconstruct the set of derivations that may perform network acquisition.
3. For each one, record whether the expected identity applies to a single file or a recursive result tree.
4. Compare the platform/version/hash tables with `fod-inventory.json`.
5. Follow each fixed output into downstream ordinary derivations so that post-fetch transforms are not mistaken for part of the same hash boundary.
6. Check `packages.test-ifd` separately if version extraction or evaluation-time behavior changed.

A capable execution surface can add a small discriminating probe:

- build one `fetchurl` case and one recursive FOD;
- replace each expected hash with an incorrect value and confirm Nix rejects the result while reporting the actual hash;
- rebuild with the correct hash and record the admitted store output;
- disable ordinary network access after the fixed outputs are available and verify the downstream cache-unpack/build path does not need to reacquire the same upstream material.

The last probe establishes only the tested build path under the recorded Nix configuration. It should not be generalized to every host or sandbox mode without matching evidence.
