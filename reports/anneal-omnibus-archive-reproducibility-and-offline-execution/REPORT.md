# Anneal Omnibus Archive Reproducibility, Timestamp Ordering, Read-Only Semantics, Offline Execution, and Version Coupling

## Summary

This report synthesizes the construction, installation, cache-reuse, offline-execution, and version-coupling invariants of the Anneal omnibus toolchain archive at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` across five coupled dimensions:

1. **Read-Only Archive Payload Permissions (`chmod -R a-w`) and Exocrate Installation**:
   Anneal's omnibus packager (`anneal/flake.nix`, `packages.omnibus-tar`) removes write permission bits (`chmod -R a-w $TMPDIR/dist_staging`) from the entire staged `lean`, `rust`, and `aeneas` payload immediately before creating the tar archive. The Exocrate installer (`exocrate/src/lib.rs`, `exocrate/src/sync.rs`) unpacks that archive into a staging directory (`<final-name>.staging`) and atomically renames the directory into place without adding write bits back or performing a second `chmod` pass. Anneal's archive-cache reuse test (`anneal/src/main.rs::test_archive_lake_cache_reuse`) recursively requires the installed `aeneas` subtree to have no write bits (`0o222` clear on non-symlinks), then builds and checks a separate writable generated workspace that imports the installed Aeneas package without reconfiguring or rebuilding those read-only Lake artifacts. However, the installation root directory itself is created by Exocrate outside the tar member set and is not made read-only, the test only asserts `assert_no_write_bits` over `aeneas` (skipping symlinks and not checking `lean` or `rust`), and Exocrate treats an existing installation directory as `ResolvedExisting` without revalidating its contents or permissions. Read-only mode bits therefore act as an accidental-write guard supporting cache reuse, not a security boundary or tamper-evidence mechanism.

2. **Timestamp Normalization and `lake --old` Modification-Time Reuse (`v4.30.0-rc2`)**:
   Anneal manipulates file modification times for two distinct purposes that must not be conflated. First, `packages.mathlib-cache-unpacked` normalizes the entire unpacked Mathlib `.ltar` result to `1970-01-01 00:00:00` (`find $out -exec touch -h -d "1970-01-01 00:00:00" {} +`) to eliminate intermediate cache timestamp variance. Second, `aeneas-compiled` and `omnibus-tar` deliberately reset only Lean source and configuration inputs (`*.lean`, `lakefile.lean`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`) to the epoch so that Lake `v4.30.0-rc2` (`leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`) running with `--old` sees prebuilt outputs as strictly newer than those inputs after Git-to-path vendoring alters Lake dependency hashes. In Lake `v4.30.0-rc2`, `SavedTrace.replayIfUpToDate'` checks `checkHashUpToDate'` first; when hashes mismatch and `--old` is enabled, `MTime.checkUpToDate` requires a **strict inequality** (`self < mtime`), with `Module.recBuildLean` supplying `srcTrace.mtime` as the fallback reference. Equal timestamps fail old-mode reuse, and Lake marks mtime-accepted outputs as `OutputStatus.mtimeUpToDate` (`isCacheable = false`). Anneal repeats the selective source/config epoch touch in `omnibus-tar` because Nix store finalization and staging copies can collapse mtimes.

3. **Byte-Level Reproducibility Boundaries of the Omnibus Archive**:
   Although upstream byte inputs are strongly pinned—`fetchAeneas` (`pkgs.fetchurl`), `fetchToolchainAsset` (recursive fixed-output derivations for Rust and Lean), `mathlib-cache-download` (recursive fixed-output derivation), and `anneal/flake.lock` pinning `NixOS/nixpkgs@549bd84d6279f9852cae6225e372cc67fb91a4c1`—the final staging derivation creates the uncompressed tar via bare `tar -cf $out *` under GNU tar `1.35`. It does not pass `--sort=name` (directory sorting defaults to `none`), `--mtime` / `--clamp-mtime`, `--numeric-owner`, `--owner`, or `--group`, and selective epoch touching leaves non-Lean files and all directory timestamps unnormalized. Furthermore, local `omnibus-archive` (`ANNEAL_ZSTD_LEVEL = 1`) and `omnibus-archive-ci` (`ANNEAL_ZSTD_LEVEL = 6`) under Zstandard `1.5.7` are distinct byte-producing derivations, and `omnibus-archive-layout-check` verifies member names and path safety rather than archive byte equality.

4. **Offline Installation and Prepared-Toolchain Execution Contract**:
   Offline behavior separates into three distinct boundaries:
   - *Installation*: Fresh default `cargo anneal setup` uses `exocrate::Source::Remote(REMOTE)` (`ureq::get(url).call()`) and is network-dependent (with placeholder `example.com` URLs in `anneal/Cargo.toml`), whereas `cargo anneal setup --local-archive <path>` uses `exocrate::Source::Local(path)` (`File::open`) with zero network I/O, and an already-present versioned directory resolves via `ResolvedExisting` before opening any source.
   - *Prepared Lake consumption*: Producer staging vendors all Aeneas/Mathlib dependencies, deletes `.git` directories, rewrites `require` declarations and `lake-manifest.json` entries to `type: "path"` via `anneal/rewrite-lake-vendor.py`, and seeds prebuilt outputs. The consumer test (`write_relative_archive_manifest`) rejects any non-`path` inherited manifest entry before invoking Lake with `env_clear()`, eliminating Lake's Git clone/fetch path.
   - *Enforcement boundary*: Neither `env_clear()` nor Lake's top-level `--offline` flag (which `LakeOptions.mkLoadConfig` in `v4.30.0-rc2` does not propagate to `LoadConfig` during ordinary `lake build`) enforces OS-level process-wide network denial.

5. **Toolchain Version-Coupling Graph and Split Charon Pin**:
   Anneal's runtime toolchain coordinates three top-level version choices (`Aeneas nightly-2026.06.03` at `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, `Rust nightly`, and `Lean v4.30.0-rc2` at `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`), while Aeneas pins Charon `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (`0.1.210`, which selects `nightly`) and Mathlib `leanprover-community/mathlib4@5450b53e5ddc75d46418fabb605edbf36bd0beb6` plus eight transitive Lake packages (`plausible`, `LeanSearchClient`, `importGraph`, `proofwidgets`, `aesop`, `Qq`, `batteries`, `Cli`). In production Nix packages, `rustDate` and `leanVersion` are duplicated static bindings rather than dynamically derived from Aeneas (`packages.test-ifd` only extracts Lean's version and round-trips Anneal's static `rustDate`). Separately, `anneal/Cargo.toml` and `anneal/Cargo.lock` lock `charon_lib` (`default-features = false`, tag `nightly-2026.06.03`) to `AeneasVerif/charon@0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1` (also version `0.1.210`, 15 commits ahead of `a535e914f74db4fd9e6be7048f4233270d8945c0`).

## Applicability

The findings in this report apply to the following pinned subjects and configurations:

- **Zerocopy Anneal and Exocrate**: `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, specifically `anneal/flake.nix`, `anneal/flake.lock`, `anneal/rewrite-lake-vendor.py`, `anneal/src/main.rs`, `anneal/Cargo.toml`, `anneal/Cargo.lock`, `exocrate/src/lib.rs`, `exocrate/src/sync.rs`, and `.github/workflows/anneal.yml` across the four supported target systems (`x86_64-linux`, `aarch64-linux`, `x86_64-darwin`, `aarch64-darwin`).
- **Lean 4 and Lake**: `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), specifically Lake's build trace (`Lake/Build/Trace.lean`), common hash/mtime replay (`Lake/Build/Common.lean`), module compilation (`Lake/Build/Module.lean`), CLI option loading (`Lake/CLI/Main.lean`), workspace materialization (`Lake/Load/Workspace.lean`, `Lake/Load/Materialize.lean`, `Lake/Load/Resolve.lean`), and environment configuration (`Lake/Config/Env.lean`).
- **Aeneas, Charon, and Mathlib**: `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`), its pinned `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (`0.1.210`, `nightly`), Anneal's independently locked Cargo dependency `AeneasVerif/charon@0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1` (`0.1.210`, tag `nightly-2026.06.03`), and `leanprover-community/mathlib4@5450b53e5ddc75d46418fabb605edbf36bd0beb6`.
- **Nixpkgs Archive and Compression Tools**: `NixOS/nixpkgs@549bd84d6279f9852cae6225e372cc67fb91a4c1` providing GNU tar `1.35` (`pkgs/by-name/gn/gnutar/package.nix`) and Zstandard `1.5.7` (`pkgs/tools/compression/zstd/default.nix`).

Cross-system byte equality across the four host platforms is not applicable because each platform fetches distinct upstream Rust, Lean, and Aeneas binary assets and Linux performs ELF interpreter/RPATH rewriting and binary stripping during final staging. Similarly, `omnibus-archive` (`ANNEAL_ZSTD_LEVEL = 1`) and `omnibus-archive-ci` (`ANNEAL_ZSTD_LEVEL = 6`) are distinct derivations whose compressed outputs are not expected to match one another.

## Findings

### 1. Omnibus Archive Read-Only Payload Construction and Exocrate Installation Contract

#### 1.1 Anneal removes write bits only after the payload is fully staged
`packages.omnibus-tar` copies the selected Lean, Rust, and Aeneas derivations into `$TMPDIR/dist_staging/{lean,rust,aeneas}`. On Linux it then patches executable ELF interpreters/RPATHs and strips binaries. It checks staged Lake traces, performs its final Aeneas source/config timestamp adjustment, and only then runs:

```sh
chmod -R a-w $TMPDIR/dist_staging
cd $TMPDIR/dist_staging
tar -cf $out *
```

The permission transformation therefore covers the staged payload that the raw tar command consumes. `a-w` removes write permission for user, group, and other while preserving existing read and execute bits; it does not make binaries non-executable. Compression in `packages.omnibus-archive` is a subsequent derivation over the raw tar and does not mutate extracted permissions.

Basis: **source** — `anneal/flake.nix`, `packages.omnibus-tar` and `packages.omnibus-archive` ([`support/archive-read-only-behavior/source-map.json`](support/archive-read-only-behavior/source-map.json), [`support/archive-read-only-behavior/permission-model.json`](support/archive-read-only-behavior/permission-model.json)).

#### 1.2 Exocrate does not add a second read-only enforcement pass, and the installation root is outside the tar invariant
Anneal's setup command resolves either a local archive or the configured remote archive through `CONFIG.resolve_installation_dir_or_install`. Exocrate creates `<final-name>.staging` with `fs::create_dir_all` before extraction, passes that directory to its installation callback (which wraps the source in a zstd decoder and calls `tar::Archive::unpack(target_dir)`), and then renames the populated staging directory to the final versioned path.

There is no subsequent recursive `chmod`, `set_permissions`, or equivalent read-only transformation in the installer, and the final rename changes only the directory name/location. Because Anneal's tar contains the top-level payload entries `aeneas`, `lean`, and `rust` rather than the parent staging directory itself, `chmod -R a-w $TMPDIR/dist_staging` establishes modes only for extracted payload entries beneath the installation root, not for the installation root directory inode created by Exocrate.

Basis: **source** — `exocrate/src/lib.rs::install` and `exocrate/src/sync.rs::ManagedDirName::check_exists_or_create`; **derived** conclusion regarding the root directory inode.

#### 1.3 Post-install test coverage and existing-directory fast path
The feature-gated `test_archive_lake_cache_reuse` installs the Nix-built archive through `setup_installation_dir` and calls `assert_no_write_bits` on `toolchain_root/aeneas` before invoking Lean/Lake. On Unix, `assert_no_write_bits` rejects any non-symlink entry whose mode has `0o222` set and recursively descends into directories, returning immediately for symlinks. The test does not call `assert_no_write_bits` on `toolchain_root/lean` or `toolchain_root/rust`. It then creates `generated-workspace` in a separate temporary directory, copies `lean-toolchain`, writes generated Lean source and a Lake file, constructs a workspace-local manifest, and runs `lake --keep-toolchain --old build Generated` followed by `lake --keep-toolchain env lean --json ...`.

Furthermore, `resolve_installation_dir_or_install` asks `ManagedDirName::check_exists` whether the final path is already a directory; if so, it returns `ResolvedExisting` without reopening the archive, walking the payload, or revalidating permissions. Thus the read-only property is an accidental-write guard established at initial extraction, not a continuously enforced security or integrity boundary.

Basis: **source** — `anneal/src/main.rs::test_archive_lake_cache_reuse`, `assert_archive_lake_cache_reuse`, `assert_no_write_bits`, and `exocrate/src/lib.rs::Config::resolve_installation_dir_or_install`.

---

### 2. Archive Timestamp Normalization and Lake `v4.30.0-rc2` Old-Mode Reuse

#### 2.1 Lake ordinary freshness is hash-first; `--old` mode requires a strict timestamp inequality
In `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), `SavedTrace.replayIfUpToDate'` calls `checkHashUpToDate'`. If the current dependency trace hash equals the saved `depHash`, Lake checks only that the requested output exists and reports `OutputStatus.hashUpToDate`. If the hashes differ and `--old` is disabled, the target is out of date. If the hashes differ and `--old` is enabled, Lake falls back to `oldTrace.checkUpToDate info`.

At the pinned Lake revision, `MTime.checkUpToDate info self` reads the output's modification time and returns the strict inequality `self < mtime`: equal timestamps are **not** up to date. While `BuildTrace` combines mtimes with `max`, Lean module compilation in `Module.recBuildLean` computes `srcTrace` for the module source and explicitly passes `oldTrace := srcTrace.mtime` to both writable-cache and non-writable-cache saved-trace checks. Furthermore, `OutputStatus.isCacheable` returns `false` for `mtimeUpToDate`, so `buildArtifactUnlessUpToDate` and `Module.recBuildLean` refuse to promote mtime-accepted outputs into a writable artifact cache as if they were hash-validated.

Basis: **source** — Lake `src/lake/Lake/Build/Trace.lean`, `src/lake/Lake/Build/Common.lean`, and `src/lake/Lake/Build/Module.lean` ([`support/archive-timestamps-lake-reuse/timestamp-model.json`](support/archive-timestamps-lake-reuse/timestamp-model.json)).

#### 2.2 Two distinct timestamp normalizations in `anneal/flake.nix`
Anneal performs two different timestamp operations across three derivation stages:

1. **Whole-tree intermediate cache normalization (`packages.mathlib-cache-unpacked`)**:
   After expanding downloaded `*.ltar` archives, Anneal runs:
   ```sh
   find $out -exec touch -h -d "1970-01-01 00:00:00" {} +
   ```
   Assigning a uniform epoch timestamp across the entire unpacked cache output removes download/unpack timestamp jitter, but by itself cannot satisfy Lake's strict `input < output` inequality if both sources and outputs share the same epoch timestamp.
2. **Selective source/configuration epoch reset before verification build (`aeneas-compiled`) and final archiving (`omnibus-tar`)**:
   Because rewriting Git dependencies into vendored relative path dependencies changes Lake dependency hashes, `aeneas-compiled` resets only the five source/configuration file classes (`*.lean`, `lakefile.lean`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`) to `1970-01-01 00:00:00` before running `lake --old build`, leaving the copied prebuilt `.olean`/`.ilean` artifacts at their newer store timestamps (`> 1970-01-01 00:00:00`, e.g., Nix store timestamp `1970-01-01 00:00:01` UTC or build clock). Because Nix store finalization and staging copies into `$TMPDIR/dist_staging` can collapse file mtimes back together, `omnibus-tar` repeats the exact selective touch:
   ```sh
   find $TMPDIR/dist_staging/aeneas -type f \
     \( -name "*.lean" -o -name "lakefile.lean" -o -name "lakefile.toml" \
        -o -name "lake-manifest.json" -o -name "lean-toolchain" \) \
     -exec touch -h -d "1970-01-01 00:00:00" {} +
   ```
   immediately before `chmod -R a-w $TMPDIR/dist_staging` and `tar -cf $out *`.

Basis: **source** — `anneal/flake.nix`; **derived** interaction with Lake's strict `self < mtime` check.

---

### 3. Omnibus Archive Byte-Level Reproducibility Analysis

#### 3.1 Fixed-output upstream boundaries vs. uncontrolled tar metadata and traversal order
Anneal pins upstream byte inputs via fixed-output derivations: `fetchAeneas` (`pkgs.fetchurl`), `fetchToolchainAsset` (recursive fixed-output derivations for Rust and Lean with shebang/ELF patching and stripping disabled), and `mathlib-cache-download` (recursive fixed-output derivation), with `NixOS/nixpkgs@549bd84d6279f9852cae6225e372cc67fb91a4c1` locked in `anneal/flake.lock`.

However, `aeneas-compiled`, `omnibus-tar`, and `omnibus-archive` are ordinary derivations that execute after those fixed-output boundaries. In `omnibus-tar`, GNU tar `1.35` is invoked as `tar -cf $out *` without `--sort=name` (so directory traversal order defaults to operating-system order `none`), `--mtime`, `--clamp-mtime`, `--numeric-owner`, `--owner`, or `--group`. In addition, the selective `touch` in `omnibus-tar` only normalizes Lean source/configuration files under `dist_staging/aeneas`, leaving `lean/`, `rust/`, Aeneas binaries/build products, and newly created staging directory inodes (`dist_staging`, `lean`, `rust`, `aeneas`) with build-time timestamps.

Basis: **source** in `anneal/flake.nix` and `anneal/flake.lock`; **documentation** in GNU tar `1.35` manual ([`support/omnibus-archive-byte-reproducibility/source-map.json`](support/omnibus-archive-byte-reproducibility/source-map.json), [`support/omnibus-archive-byte-reproducibility/reproducibility-model.json`](support/omnibus-archive-byte-reproducibility/reproducibility-model.json)).

#### 3.2 Layout check vs. byte comparison, Zstandard levels, and prerequisite build observations
`packages.omnibus-archive-layout-check` decompresses `omnibus-archive-ci` and inspects `tar -tf` output to confirm that only `aeneas`, `lean`, and `rust` appear at the top level, required executables and Mathlib `.olean` files exist, and no absolute or parent-relative member names occur. It does not perform a paired rebuild or byte comparison. Meanwhile, `omnibus-archive` compresses `$omnibusTar` with `zstd -$ZSTD_LEVEL` at default level `1`, whereas `omnibus-archive-ci` overrides `ANNEAL_ZSTD_LEVEL` to `6`.

During execution probing on `aarch64-darwin` with Nix `2.35.2`, `omnibus-tar` stopped at the `mathlib-cache-download` fixed-output prerequisite before tar creation, and a direct retry of `mathlib-cache-download` produced a different actual output hash (`sha256-5949...` vs. `sha256-3b7f...`) due to upstream/tool acquisition variance recorded in [`support/omnibus-archive-byte-reproducibility/execution-observations.json`](support/omnibus-archive-byte-reproducibility/execution-observations.json), [`support/omnibus-archive-byte-reproducibility/execution/mathlib-cache-download-watchdog.json`](support/omnibus-archive-byte-reproducibility/execution/mathlib-cache-download-watchdog.json), and [`support/omnibus-archive-byte-reproducibility/execution/omnibus-tar-watchdog-attempt1.json`](support/omnibus-archive-byte-reproducibility/execution/omnibus-tar-watchdog-attempt1.json).

Basis: **source** and **execution** ([`support/omnibus-archive-byte-reproducibility/execution-observations.json`](support/omnibus-archive-byte-reproducibility/execution-observations.json)).

---

### 4. Offline Installation and Prepared-Toolchain Execution Guarantees

#### 4.1 Installation source selection and existing-directory fast path
`setup_installation_dir` in `anneal/src/main.rs` maps `cargo anneal setup` without `--local-archive` to `exocrate::Source::Remote(REMOTE)` (which calls `ureq::get(url).call()` in `exocrate/src/lib.rs`) and maps `--local-archive <path>` to `exocrate::Source::Local(path)` (which calls `File::open(path)`). Before opening either source, `Config::resolve_installation_dir_or_install` checks `ManagedDirName::check_exists` and returns `ResolvedExisting` if the target versioned directory already exists. At `41f5b37afe7060fd9fe08c00b200672cd76d77b9`, the remote URLs in `anneal/Cargo.toml` are explicit `example.com` placeholders.

Basis: **source** — `anneal/src/main.rs`, `exocrate/src/lib.rs`, `anneal/Cargo.toml` ([`support/offline-installation-execution/source-map.json`](support/offline-installation-execution/source-map.json), [`support/offline-installation-execution/offline-boundary-matrix.json`](support/offline-installation-execution/offline-boundary-matrix.json)).

#### 4.2 Producer path-vendoring and consumer fail-closed manifest rewriting
In `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`Lake/Load/Materialize.lean` and `Lake/Load/Resolve.lean`), a manifest entry of type `"git"` can still inspect Git `HEAD`, enter its update path, fetch, or reclone even when a directory exists on disk, whereas a `"path"` entry materializes directly from the local filesystem path. Accordingly:

1. **Producer (`anneal/flake.nix` + `anneal/rewrite-lake-vendor.py`)**: copies materialized package directories into the archive build, deletes `.git` directories, rewrites `require` declarations in Lakefiles to relative paths, rewrites `lake-manifest.json` entries to `type: "path"` while stripping remote URLs/revisions, and seeds prebuilt Mathlib/Lake outputs.
2. **Consumer (`anneal/src/main.rs::write_relative_archive_manifest`)**: inspects the archived Aeneas `lake-manifest.json` and rejects any inherited entry whose `type != "path"`, then rewrites each accepted entry's `dir` relative to the new generated workspace and adds Aeneas itself as a local path dependency.
3. **Environment sanitization vs. OS network sandboxing**: `run_lake_archive_command` calls `env_clear()` before invoking the archived `lean/bin/lake` (removing `HOME`, `XDG_CACHE_HOME`, `LAKE_CONFIG`, `LAKE_PKG_URL_MAP`, `LAKE_CACHE_ARTIFACT_ENDPOINT`, `LAKE_CACHE_REVISION_ENDPOINT`, `LAKE_CACHE_SERVICE`, and `PATH`), setting only the platform shared-library search path. However, `env_clear()` does not block socket syscalls, and Lake `v4.30.0-rc2`'s `--offline` CLI flag (`Lake/CLI/Main.lean`) is not copied into `LoadConfig` by `LakeOptions.mkLoadConfig` during ordinary `lake build`.

Basis: **source** — `anneal/flake.nix`, `anneal/rewrite-lake-vendor.py`, `anneal/src/main.rs`, and Lake `v4.30.0-rc2` `Lake/CLI/Main.lean`, `Lake/Load/Materialize.lean`, `Lake/Config/Env.lean`.

---

### 5. Toolchain Version-Coupling Graph and Split Charon Dependency

#### 5.1 Three-layer coupling graph at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`
Anneal's version selections span three overlapping dependency graphs ([`support/toolchain-version-coupling/coupling-graph.json`](support/toolchain-version-coupling/coupling-graph.json), [`support/toolchain-version-coupling/source-map.json`](support/toolchain-version-coupling/source-map.json)):

```text
google/zerocopy main 41f5b37afe7060fd9fe08c00b200672cd76d77b9
├─ Aeneas release nightly-2026.06.03
│  └─ AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727
│     ├─ charon-pin + flake.lock -> AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0 (v0.1.210)
│     │  └─ rust-toolchain -> nightly (rustc-dev, llvm-tools-preview, rust-src, miri)
│     ├─ backends/lean/lean-toolchain -> leanprover/lean4:v4.30.0-rc2 (3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc)
│     └─ backends/lean/lake-manifest.json
│        ├─ mathlib: 5450b53e5ddc75d46418fabb605edbf36bd0beb6 (inputRev: v4.30.0-rc2)
│        ├─ plausible: 86210d4ad1b08b086d0bd638637a75246523dbb8 (main)
│        ├─ LeanSearchClient: c5d5b8fe6e5158def25cd28eb94e4141ad97c843 (main)
│        ├─ importGraph: cdab3938ccabbdb044be6896e251b5814bec932e (main)
│        ├─ proofwidgets: 2db6054a44326f8c0230ee0570e2ddb894816511 (v0.0.98)
│        ├─ aesop: f0c6e183ea26531e82773feb4b73ab6595ca17a5 (v4.30.0-rc2)
│        ├─ Qq: 1cc7e819b9b9bc1e87c9edcccb62e0269e00a809 (v4.30.0-rc2)
│        ├─ batteries: 5c57f3857ba81924a88b2cdf4f062e34ec04ff11 (v4.30.0-rc2)
│        └─ Cli: 13567aed1ac4f12aea9484178e07e51f8c9f7658 (v4.30.0-rc2)
├─ Anneal static Nix bindings (anneal/flake.nix)
│  ├─ rustDate = "2026-05-31"
│  ├─ leanVersion = "v4.30.0-rc2"
│  ├─ leantar = "0.1.16"
│  └─ NixOS/nixpkgs@549bd84d6279f9852cae6225e372cc67fb91a4c1 (anneal/flake.lock)
└─ Anneal Cargo build graph (anneal/Cargo.toml + anneal/Cargo.lock)
   └─ charon_lib (tag = "nightly-2026.06.03", default-features = false)
      └─ AeneasVerif/charon@0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1 (v0.1.210, 15 commits ahead of a535e914…)
```

#### 5.2 Static vs. IFD-derived selectors and the split Charon commit
In `anneal/flake.nix`, production `packages.rust-toolchain` and `packages.lean-toolchain` use the static top-level bindings `rustDate = "2026-05-31"` and `leanVersion = "v4.30.0-rc2"`. While `packages.test-ifd` reads `metadata.json` from `packages.aeneas-unpacked`, only `lean-toolchain` is genuinely extracted from `backends/lean/lean-toolchain`; `RUST_DATE=${rustDate}` is injected from Anneal's own static binding and read back, and `test-ifd` reuses the static `outputHash` values from `rust-toolchain` and `lean-toolchain`.

In `anneal/Cargo.toml`, `charon_lib` is pinned to the Charon repository's `nightly-2026.06.03` tag with `default-features = false` (omitting the default `rustc` driver feature), which `anneal/Cargo.lock` resolves to `0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`—15 commits ahead of the `a535e914f74db4fd9e6be7048f4233270d8945c0` commit packaged inside the `nightly-2026.06.03` Aeneas release, even though both commits declare Cargo package version `0.1.210`.

Basis: **source** and **lockfile** in `anneal/flake.nix`, `anneal/Cargo.toml`, `anneal/Cargo.lock`, `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, and `AeneasVerif/charon` commits `a535e914f74db4fd9e6be7048f4233270d8945c0` and `0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`.

## Boundaries

- **Known not to apply (installation root and existing-directory revalidation)**: The `chmod -R a-w` transformation in `omnibus-tar` does not apply to the installation root directory created by Exocrate (`<final-name>.staging`), and `Config::resolve_installation_dir_or_install` does not revalidate modes or file hashes when returning `ResolvedExisting`.
- **Known not to apply (mtime fallback as content-hash proof)**: Successful `lake --old build` under epoch-normalized source/config timestamps establishes only `OutputStatus.mtimeUpToDate` (`self < mtime`), which Lake marks `isCacheable = false`; it does not establish that the vendored dependency graph has the same Lake `depHash` as the upstream Git dependency graph.
- **Known not to apply (uncontrolled tar bytes and `lake build --offline`)**: Current `tar -cf $out *` in `omnibus-tar` does not canonicalize directory traversal order, owner/group headers, or non-Lean/directory mtimes, and Lake `v4.30.0-rc2`'s `--offline` flag is not propagated by `LakeOptions.mkLoadConfig` during ordinary `lake build`.
- **Not examined (fresh end-to-end paired archive byte comparison and OS network sandboxing)**: Because the `aarch64-darwin` Nix build attempt halted at the `mathlib-cache-download` fixed-output prerequisite ([`support/omnibus-archive-byte-reproducibility/execution-observations.json`](support/omnibus-archive-byte-reproducibility/execution-observations.json)), no completed paired `omnibus-tar` byte comparison or OS-sandboxed (`unshare` / network-namespace / `sandbox-exec`) execution of the extracted archive was performed in this study.
- **Unsupported (Windows host archives and default placeholder remote URLs)**: Anneal's current flake and Exocrate matrix cover Linux and macOS on `x86_64` and `aarch64` only, and the remote archive URLs in `anneal/Cargo.toml` at `41f5b37afe7060fd9fe08c00b200672cd76d77b9` are unroutable `example.com` placeholders.

## Evidence

All primary source and execution artifacts are preserved in this package under `support/`:

1. **Read-Only Archive Payload and Exocrate Installer (`support/archive-read-only-behavior/`)**:
   - [`support/archive-read-only-behavior/source-map.json`](support/archive-read-only-behavior/source-map.json) and [`support/archive-read-only-behavior/permission-model.json`](support/archive-read-only-behavior/permission-model.json), mapping `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` (`anneal/flake.nix` blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`, `anneal/src/main.rs` blob `b947700606677ea89c7a205f3ffcc75493508f63`, `exocrate/src/lib.rs` blob `88cc0d5dd91082070b6ef475a32bf42c25f52115`, `exocrate/src/sync.rs` blob `85b6e203522e963af13d88ab4d3e7684ebb29252`).
2. **Archive Timestamp Normalization and Lake `v4.30.0-rc2` Reuse (`support/archive-timestamps-lake-reuse/`)**:
   - [`support/archive-timestamps-lake-reuse/timestamp-model.json`](support/archive-timestamps-lake-reuse/timestamp-model.json), recording the three `touch` sites in `anneal/flake.nix` and Lake's `MTime.checkUpToDate` (`src/lake/Lake/Build/Trace.lean` blob `656c991fab8a6475802373224514ec7e73f9b18b`), `SavedTrace.replayIfUpToDate'` / `OutputStatus.isCacheable` (`src/lake/Lake/Build/Common.lean` blob `c283fda65ba4d6e3138a0b4ab8252885bf78a014`), and `Module.recBuildLean` (`src/lake/Lake/Build/Module.lean`) in `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`.
3. **Omnibus Archive Byte Reproducibility (`support/omnibus-archive-byte-reproducibility/`)**:
   - [`support/omnibus-archive-byte-reproducibility/source-map.json`](support/omnibus-archive-byte-reproducibility/source-map.json) and [`support/omnibus-archive-byte-reproducibility/reproducibility-model.json`](support/omnibus-archive-byte-reproducibility/reproducibility-model.json), documenting `anneal/flake.nix` lines 90–646, `anneal/flake.lock` blob `92ac56b0a777d280f0a76e28f163b20ff6fb2003`, GNU tar `1.35` (`pkgs/by-name/gn/gnutar/package.nix` blob `51344245c45f756e32aa23f9ab0c1834e7cc626c`), and Zstandard `1.5.7` (`pkgs/tools/compression/zstd/default.nix` blob `a014b652d313facb7d2bc0ad5f4c345347e1eaca`).
   - [`support/omnibus-archive-byte-reproducibility/execution-observations.json`](support/omnibus-archive-byte-reproducibility/execution-observations.json), [`support/omnibus-archive-byte-reproducibility/execution/mathlib-cache-download-watchdog.json`](support/omnibus-archive-byte-reproducibility/execution/mathlib-cache-download-watchdog.json), and [`support/omnibus-archive-byte-reproducibility/execution/omnibus-tar-watchdog-attempt1.json`](support/omnibus-archive-byte-reproducibility/execution/omnibus-tar-watchdog-attempt1.json), recording the `aarch64-darwin` Nix `2.35.2` build observations on 2026-09-27.
4. **Offline Installation and Prepared-Toolchain Execution (`support/offline-installation-execution/`)**:
   - [`support/offline-installation-execution/source-map.json`](support/offline-installation-execution/source-map.json) and [`support/offline-installation-execution/offline-boundary-matrix.json`](support/offline-installation-execution/offline-boundary-matrix.json), covering `anneal/rewrite-lake-vendor.py` blob `e61fc992837435a43b3e434ddd3b07aa7d13b48c`, `.github/workflows/anneal.yml` blob `39f648acb45681707bb5f51624c279b44fa2e832`, and Lake `v4.30.0-rc2` (`Lake/CLI/Main.lean` blob `65b0e7fd0d6cd21d512edb49a276bcc65ae31c78`, `Lake/Load/Workspace.lean` blob `9f25dd62bc752ede695a25fc20371157eb65d64b`, `Lake/Load/Materialize.lean` blob `e098e5adbbf33a641fa5cf7d37d0bbd371956f4b`, `Lake/Load/Resolve.lean` blob `ec7c9978ab99b9a998a1c24d5e1e7ecce3cfa928`, `Lake/Config/Env.lean` blob `eed315c538de746a891d18f72564e88aea64e969`).
5. **Toolchain Version Coupling (`support/toolchain-version-coupling/`)**:
   - [`support/toolchain-version-coupling/source-map.json`](support/toolchain-version-coupling/source-map.json) and [`support/toolchain-version-coupling/coupling-graph.json`](support/toolchain-version-coupling/coupling-graph.json), recording the exact commit and manifest hashes across `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` (`anneal/Cargo.lock` blob `eeaa3f7119369d79b735d8c4836fc08bcc7f7e6d`), `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`charon-pin` blob `06dbe0dbf1d5b7f1e6f2a21889ab6bf770e89de6`, `backends/lean/lake-manifest.json` blob `1a5af703163d8b39f4311aafe22ae171788179ee`), and `AeneasVerif/charon` (`a535e914f74db4fd9e6be7048f4233270d8945c0` and `0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`).

## Revalidation

To revalidate these findings against a newer Anneal, Exocrate, Aeneas, or Lean/Lake revision:

1. **Read-Only and Timestamp Ordering Check**:
   - Inspect `packages.omnibus-tar` in `anneal/flake.nix` to verify whether selective epoch normalization (`1970-01-01 00:00:00`) still precedes `chmod -R a-w $TMPDIR/dist_staging` and `tar -cf $out *`, and verify in Lake (`Lake/Build/Trace.lean`, `Lake/Build/Common.lean`, `Lake/Build/Module.lean`) whether `MTime.checkUpToDate` still enforces strict `self < mtime` with `OutputStatus.isCacheable = false` for `mtimeUpToDate`.
   - Build or extract one archive, record mode bits and mtimes for the installation root and `aeneas`, `lean`, and `rust` subtrees, and test a negative fixture where a `.lean` source and its `.olean` output share an identical timestamp to confirm `lake --old --no-build build` rejects it.
2. **Paired Byte-Reproducibility Probe**:
   - Build `anneal#omnibus-tar` twice independently (`--rebuild` or isolated store) on the same host system, comparing SHA-256 digests, `tar -tf` entry order, verbose metadata headers (`tar -tvf --numeric-owner --full-time`), and per-member payload hashes before testing `zstd` compression at levels `1` and `6`.
   - If byte reproducibility becomes a required invariant, verify that `tar` is invoked with `--sort=name`, `--numeric-owner`, `--owner=0`, `--group=0`, and deterministic timestamps across non-Lean files and directory entries while preserving the `source < output` mtime gap required if `lake --old` remains in use.
3. **Hard Offline Execution Probe**:
   - Run `cargo anneal setup --local-archive <path>` and the generated-workspace Lake/Lean verification commands inside an OS-level network-denied sandbox (Linux `unshare -n` or macOS `sandbox-exec` denying `network*`) while tracing socket syscalls, testing both valid `type: "path"` manifests and a negative control with a `"git"` manifest entry.
4. **Version-Coupling Consistency Audit**:
   - Compare `rustDate` in `anneal/flake.nix` against `rust-toolchain` at the Charon revision named by Aeneas's `charon-pin`, compare `leanVersion` against Aeneas's `backends/lean/lean-toolchain`, verify all transitive revisions in `backends/lean/lake-manifest.json`, and check whether `anneal/Cargo.lock`'s `charon` commit matches Aeneas's `charon-pin` if `charon_lib` is ever wired into LLBC serialization or consumption.
