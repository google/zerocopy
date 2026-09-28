# Byte-level reproducibility of the Anneal omnibus archive

## Summary

At `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, Anneal does not yet establish a byte-level reproducibility contract for its omnibus toolchain archive.

The build fixes many important inputs: Aeneas release assets are hash-pinned, the Rust and Lean toolchain derivations are recursive fixed-output derivations, the downloaded Mathlib cache is a recursive fixed-output derivation, and `anneal/flake.lock` pins Nixpkgs. Anneal also normalizes some timestamps. Those controls materially reduce variability, but they stop short of canonicalizing the final tar stream.

The final staging derivation creates a tar file with:

```console
tar -cf $out *
```

The pinned GNU tar is 1.35. Its own reproducibility guidance says that ordinary tar archives can differ because of metadata and directory-entry order, that directory sorting defaults to `none`, and that reproducible creation should control such dimensions as ordering, modification times, ownership, and group metadata. Anneal's final command does not pass those controls. Immediately before archiving, it resets the modification times of a narrow class of Aeneas source/configuration files, but it does not normalize every staged file or directory. In particular, the recipe creates the top-level staging directories and archives their metadata without assigning them a fixed timestamp.

The current archive layout check verifies names and required members. It does not rebuild independently or compare archive bytes. The compressed archive also has two configured variants: local `omnibus-archive` uses Zstandard level 1, while `omnibus-archive-ci` overrides the level to 6. Treat those as distinct byte-producing derivations rather than as interchangeable encodings of one canonical byte string.

The durable conclusion is therefore negative but useful: the current source does not justify deriving an expected omnibus-archive SHA-256 solely from the logical toolchain inputs, and a successful layout check is not evidence of byte reproducibility. A per-system, per-derivation reproducibility claim requires an independent paired-build comparison. If that comparison fails, compare the uncompressed tar files first; the source already identifies tar metadata and member ordering as uncontrolled dimensions.

A real `omnibus-tar` build was attempted on `aarch64-darwin` with Nix 2.35.2, but it stopped at the Mathlib cache fixed-output check before cache unpacking, Aeneas compilation, or tar creation. A direct retry of the Mathlib cache derivation also failed and produced a different actual hash, despite the same pinned Mathlib and listed dependency revisions. This is not an observed omnibus tar mismatch: no tar was produced and no paired archive comparison could run. Exact hashes and command/elapsed/resource summaries are in [`execution-observations.json`](execution-observations.json). Full build transcripts remain in the local campaign scratch; no successful archive output exists to preserve.

## Applicability

This report applies to Anneal's omnibus archive pipeline at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, especially `packages.omnibus-tar`, `packages.omnibus-archive`, and `packages.omnibus-archive-ci` in `anneal/flake.nix`.

The flake evaluates one package graph per default system and maps four systems to distinct upstream artifacts:

- `x86_64-linux`;
- `aarch64-linux`;
- `x86_64-darwin`;
- `aarch64-darwin`.

The Rust, Lean, and Aeneas asset identities differ by system, and Linux additionally rewrites ELF interpreters/RPATHs and strips executable files during final staging. Cross-system byte equality is therefore not a meaningful expectation. Reproducibility should be evaluated within one exact `system`, one exact source revision and `flake.lock`, and one exact archive derivation.

`omnibus-archive` and `omnibus-archive-ci` are also distinct configurations. The first sets `ANNEAL_ZSTD_LEVEL = 1`; the second overrides it to 6. A reproducibility experiment should compare repeated builds of the same one of those derivations. Equality between the two variants is neither required nor established.

The source analysis is based on immutable source, pinned package definitions, and GNU tar 1.35 documentation. A fresh Nix build was attempted on `aarch64-darwin`; it failed at the Mathlib fixed-output prerequisite. No tar-byte comparison or Zstandard execution was possible.

## Findings

### Most upstream byte inputs are strongly pinned

Anneal constrains several network-derived inputs before the final archive stage.

`fetchAeneas` uses `pkgs.fetchurl` with a per-platform SHA-256 for the selected `nightly-2026.06.03` release archive. `fetchToolchainAsset`, which backs both the Rust and Lean toolchains, is a recursive fixed-output derivation with an explicit SHA-256 and disables shebang patching, ELF patching, and stripping. `mathlib-cache-download` is likewise a recursive fixed-output derivation with a per-platform SHA-256. The flake lock fixes Nixpkgs at `549bd84d6279f9852cae6225e372cc67fb91a4c1`.

These controls are important: they make the downloaded/materialized trees content-addressed at their respective fixed-output boundaries. They do not imply that later ordinary derivations produce byte-identical outputs when rebuilt. `aeneas-compiled`, `omnibus-tar`, and `omnibus-archive` perform additional copying, building, patching, metadata mutation, archiving, and compression after those boundaries.

Basis: **source** in `anneal/flake.nix` and `anneal/flake.lock`.

### Timestamp normalization is real but not final-archive canonicalization

Anneal normalizes timestamps in two places for two narrower purposes.

`mathlib-cache-unpacked` expands the downloaded `.ltar` files and then runs:

```console
find $out -exec touch -h -d "1970-01-01 00:00:00" {} +
```

The adjacent source comment describes this as keeping the release archive reproducible. This normalizes the full output tree at that intermediate point.

Later, `aeneas-compiled` deliberately makes Lean source/configuration inputs older than already-unpacked build artifacts before `lake --old build`. The same source/configuration pattern is touched again after final staging because the source notes that Nix store finalization and the staging copy can collapse file mtimes. That second repair is:

```console
find $TMPDIR/dist_staging/aeneas -type f \
  \( -name "*.lean" -o -name "lakefile.lean" -o -name "lakefile.toml" \
     -o -name "lake-manifest.json" -o -name "lean-toolchain" \) \
  -exec touch -h -d "1970-01-01 00:00:00" {} +
```

This is deliberately selective. It touches only regular files under `dist_staging/aeneas` matching the Lake/source patterns. It does not normalize the entire `lean/` or `rust/` trees, Aeneas binaries and build artifacts, or any directory timestamps. The staging derivation itself creates `dist_staging`, `lean`, `rust`, and `aeneas` directories before creating the tar file.

The correct interpretation is therefore not “all archive timestamps are canonical.” The source establishes a full-tree normalization at one intermediate Mathlib-cache boundary and a selective ordering repair for Lake's old-mode reuse at the final staging boundary.

Basis: **source** in `anneal/flake.nix`; distinction between the two purposes is **derived** from the commands' scopes and surrounding comments.

### The final GNU tar command leaves documented reproducibility dimensions uncontrolled

The pinned Nixpkgs revision selects GNU tar 1.35. Anneal invokes it at the final uncompressed archive boundary as:

```console
cd $TMPDIR/dist_staging
tar -cf $out *
```

No reproducibility-specific tar flags are present.

GNU tar 1.35 documents that tar archives record file metadata including owner/group, permissions, and modification time. It also documents that directory sorting defaults to `none`: directory entries are read in operating-system order. Its “Making `tar` Archives More Reproducible” section recommends controlling, as applicable, directory order (`--sort=name`), timestamps (`--mtime` / `--clamp-mtime`), numeric owner representation, owner/group values, and modes.

Anneal's final recipe does not pass `--sort=name`, `--mtime`, `--clamp-mtime`, `--numeric-owner`, `--owner`, or `--group`. Its preceding `chmod -R a-w` removes write permission from the staging tree but does not canonicalize all remaining mode bits. Its selective `touch` leaves many file timestamps and all directory timestamps outside that final normalization.

This does not prove that two particular rebuilds must differ: a specific build environment can happen to produce identical metadata and directory order. It does prove that the current source recipe does not itself define all tar-header and traversal-order inputs that GNU tar identifies as relevant to byte-for-byte reproducibility.

Basis: **source** in `anneal/flake.nix`; **documentation** in the GNU tar 1.35 manual; conclusion about the missing source-level guarantee is **derived**.

### The layout check is structural, not a reproducibility test

`packages.omnibus-archive-layout-check` consumes `omnibus-archive-ci`, decompresses it, and writes `tar -tf` output to an entries file. It verifies:

- the only top-level names are `aeneas`, `lean`, and `rust`;
- several required executables, Lake configuration artifacts, and Mathlib cache files exist;
- at least one Mathlib `.olean` cache artifact exists;
- archive member names are not absolute or parent-relative;
- repository-checkout top-level paths do not appear.

The check does not compare the archive against an independently rebuilt archive, compare SHA-256 digests, compare uncompressed tar bytes, or inspect whether member metadata has been canonicalized. Passing this check establishes the tested layout and path-safety properties only.

Basis: **source** in `anneal/flake.nix`.

### Compression configuration is explicit, but it does not supply a canonical archive identity

The pinned Nixpkgs revision selects Zstandard 1.5.7. `omnibus-archive` compresses the staged tar with:

```console
zstd -$ZSTD_LEVEL $omnibusTar -o $out
```

and defaults `ZSTD_LEVEL` to 1. `omnibus-archive-ci` inherits the same derivation but overrides `ANNEAL_ZSTD_LEVEL` to 6.

Thus the project already has two intentionally distinct compression configurations for the same archive pipeline. The uncompressed tar is the appropriate first comparison boundary for diagnosing reproducibility. If two `omnibus-tar` builds differ, compressed-byte mismatch follows from an earlier stage and Zstandard is not the first question to investigate. If two raw tar files match, then repeated compression with the same pinned Zstandard package, same level, and same system becomes the next discriminating check.

Basis: **source** in `anneal/flake.nix` and the pinned Nixpkgs Zstandard package definition; diagnostic ordering is **derived**.

### Fixed-output inputs and a stable Nix derivation identity are not the missing experiment

The fixed-output derivations above establish the content expected at their own boundaries. This investigation did not independently rebuild the later ordinary derivations, so it does not use a Nix store path, derivation identity, or cached artifact as evidence that two independent executions emitted the same tar bytes.

For the same reason, an archive SHA recorded after one successful build is a useful artifact identity but not evidence that another builder will derive the same SHA. The missing evidence is a repeated-build comparison under recorded conditions.

Basis: **source** for which stages are fixed-output; **derived** boundary on what this investigation can claim without execution.

## Boundaries

**No tar or paired archive build completed.** The `omnibus-tar` derivation stopped at its Mathlib fixed-output prerequisite, and a direct retry of that prerequisite also failed. This report does not report an observed mismatch between two archive builds.

**No claim that every uncontrolled field actually varies in ordinary CI.** GNU tar documents the fields and ordering that can affect bytes. The current recipe leaves some of them to staged filesystem state. A particular host or Nix execution may happen to reproduce those values.

**No cross-platform byte-equality requirement.** The four systems use different Rust, Lean, and Aeneas assets. Linux also performs ELF-specific final-stage mutations. Compare repeated builds only within one exact system unless a separate requirement explicitly demands cross-platform equality.

**No equality claim between local and CI archive variants.** They use different Zstandard levels. Treat each derivation independently.

**No general Zstandard determinism claim.** Zstandard 1.5.7 is pinned by Nixpkgs, but this investigation did not execute it or establish a cross-version/cross-architecture deterministic-compression guarantee. The recommended experiment isolates compression only after raw-tar equality has been established.

**No conclusion about whether byte reproducibility is required for correctness.** The archive installer can authenticate a published artifact by its recorded checksum without requiring independent rebuilds to recreate that checksum. This report addresses the #3720 reproducibility question, not the separate remote/local checksum-semantics questions.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-27.

Primary Anneal source:

- `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `anneal/flake.nix`, blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`.
  - Lines 90–188: Aeneas fetch and recursive fixed-output Rust/Lean toolchain construction.
  - Lines 230–386: Aeneas extraction, fixed-output Mathlib-cache download, cache expansion, and full-tree timestamp normalization.
  - Lines 390–490: Aeneas Lean build, vendoring, old-mode timestamp repair, trace rewriting, pruning, and packaged output.
  - Lines 494–553: final staging, Linux ELF patch/strip, selective final timestamp repair, read-only chmod, and `tar -cf $out *`.
  - Lines 558–584: Zstandard compression levels for local and CI archive variants.
  - Lines 586–646: archive layout/path-safety checks.
- `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `anneal/flake.lock`, blob `92ac56b0a777d280f0a76e28f163b20ff6fb2003`.
  - Nixpkgs locked to `NixOS/nixpkgs@549bd84d6279f9852cae6225e372cc67fb91a4c1`.

Pinned archive/compression tools:

- `NixOS/nixpkgs@549bd84d6279f9852cae6225e372cc67fb91a4c1`, `pkgs/by-name/gn/gnutar/package.nix`, blob `51344245c45f756e32aa23f9ab0c1834e7cc626c`: GNU tar `1.35`.
- `NixOS/nixpkgs@549bd84d6279f9852cae6225e372cc67fb91a4c1`, `pkgs/tools/compression/zstd/default.nix`, blob `a014b652d313facb7d2bc0ad5f4c345347e1eaca`: Zstandard `1.5.7`.
- GNU tar 1.35 manual, `https://www.gnu.org/software/tar/manual/tar.html`, especially “Making `tar` Archives More Reproducible”, accessed 2026-09-27. The manual identifies unsorted directory order and archive metadata as byte-reproducibility inputs and documents the relevant canonicalization options.

Evidence roles are **source**, **documentation**, **execution**, and **derived**. Execution is limited to the failed prerequisite attempts recorded in `execution-observations.json`; it contains no archive-byte result.

## Revalidation

The cheapest decisive check for the current subject is a paired build of one exact archive derivation on one exact system.

1. Start from `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` with its committed `anneal/flake.lock`.
2. Independently build `anneal#omnibus-tar` twice under conditions that actually execute the derivation twice rather than reusing one Nix-store result. Copy each result out before the second execution can replace or reuse it.
3. Record the host system, Nix version, exact derivation path, and SHA-256 of each raw tar.
4. If the tar hashes differ, compare:
   - `tar -tf` member order;
   - a verbose numeric-owner/full-time listing;
   - per-member content hashes after extraction.
   This separates member-order/metadata differences from payload differences.
5. If the raw tar files are identical, compress that same tar twice with the exact pinned Zstandard package and the same configured level. Compare the `.zst` hashes.
6. Repeat separately for `omnibus-archive` level 1 and `omnibus-archive-ci` level 6 if both reproducibility contracts matter.
7. Repeat on each supported system for which reproducibility is required. Do not infer one platform's result from another.

If the goal changes from “measure current behavior” to “make reproducibility a source-level invariant,” first canonicalize the tar creation command using the relevant GNU tar 1.35 reproducibility controls, normalize the complete final staging metadata that the archive records, and add an independent rebuild comparison. Re-run the paired-build experiment after any change to Nixpkgs, the final staging recipe, upstream asset identities, or compression configuration.
