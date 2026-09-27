# Exocrate cache directory and version identity at Anneal main `41f5b37`

## Summary

Current Anneal does not install its packaged toolchain at a path derived from the archive filename or archive contents. It asks Exocrate for a **location root**, appends the fixed components `.anneal/toolchain`, and then appends a 64-hex-character **version slug compiled into the Anneal binary**. In the normal installed-tool path, the root is the platform user-cache directory. On Linux this follows `XDG_CACHE_HOME` only when that variable contains an absolute path, otherwise falling back to `$HOME/.cache`; on macOS it is `$HOME/Library/Caches`.

The version slug is SHA-256 over an ordered concatenation of the literal strings `../Cargo.toml` and `../Cargo.lock`, the complete bytes of those two Anneal files, and the compile-time OS and architecture strings. For `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, the four Anneal-supported platform slugs are preserved in `identity-matrix.json`.

This is deliberately a **change detector for the consuming build**, not a content address for the installed archive. It over-invalidates when unrelated `Cargo.toml` or `Cargo.lock` bytes change. Conversely, it does not directly hash the archive bytes, the local-archive path, `anneal/flake.nix`, `anneal/src/main.rs`, or Exocrate source. The normal remote case partly closes that gap because the remote URL and expected SHA-256 live in `anneal/Cargo.toml`, one of the hashed files. The `--local-archive` case does not: two different local archives used with the same compiled Anneal configuration select the same installation directory, and an existing directory is reused before Exocrate opens the newly supplied archive.

Two switches are independent and should not be conflated. `--local-archive` changes the **source** of bytes. The presence of the runtime `__ANNEAL_LOCAL_DEV` environment variable changes the **location root** from the user cache to `CARGO_MANIFEST_DIR/target` (or, if that variable is unavailable as UTF-8, the current directory's `target`). Supplying a local archive alone does not select the development location.

## Applicability

The Anneal-specific conclusions apply to `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, especially the `CONFIG` and `REMOTE` declarations in `anneal/src/main.rs`, the versioned `anneal/Cargo.toml` and `anneal/Cargo.lock`, and the in-tree Exocrate implementation selected by that revision.

The cache-root behavior also depends on `dirs 6.0.0`, resolved by the pinned `anneal/Cargo.lock` with crates.io checksum `c3e8aa94d75141228480295a7d0e7feb620b1a5ad9f12bc40be62411e38cce4e`. Current Anneal's remote metadata enumerates Linux and macOS on `x86_64` and `aarch64`; this report therefore gives exact normal-user paths for those operating systems. Exocrate itself has broader platform behavior, but that is not evidence that current Anneal supports all of those platforms.

`identity-matrix.json` records the exact derived slug values and input blob identities. The slug values were recomputed from the exact source bytes and macro algorithm; no Cargo build or Exocrate execution was performed in this investigation.

## Findings

### Normal Anneal setup is namespaced under the platform user cache

`setup_installation_dir` chooses `Location::UserGlobal` unless `std::env::var("__ANNEAL_LOCAL_DEV").is_ok()` succeeds. For `UserGlobal`, `Config::dir_path` starts from `dirs::cache_dir()`, appends Anneal's configured relative components `.anneal` and `toolchain`, and finally joins the compiled version slug.

Thus the normal shape is:

```text
<user-cache-root>/.anneal/toolchain/<version-slug>
```

Exocrate treats inability to obtain a cache root as `io::ErrorKind::NotFound` with `cache dir not found`. Anneal currently calls `resolve_installation_dir_or_install(...).expect("failed to resolve-or-install dependencies")`, so that error terminates setup rather than falling back to another base directory.

When creating a missing installation, `ManagedDirName::check_exists_or_create` creates the target's parent hierarchy with `create_dir_all` before opening its sibling lock file. The cache subtree therefore need not already exist.

Basis: source.

### Linux honors only an absolute `XDG_CACHE_HOME`

The exact selected `dirs 6.0.0` Linux implementation evaluates `XDG_CACHE_HOME`, passes it through an absolute-path check, and otherwise falls back to `home_dir().join(".cache")`.

For current Anneal on Linux, the normal path is therefore:

```text
$XDG_CACHE_HOME/.anneal/toolchain/<slug>     # when XDG_CACHE_HOME is absolute
$HOME/.cache/.anneal/toolchain/<slug>        # when XDG_CACHE_HOME is unset or rejected
```

A relative `XDG_CACHE_HOME` is not interpreted relative to the working directory. It is rejected by `dirs` and the home-directory fallback is used instead. This is an important distinction when tests or sandboxes deliberately override XDG locations.

Basis: source (`dirs 6.0.0` `src/lin.rs`) + source (`exocrate/src/lib.rs`).

### macOS uses `~/Library/Caches`, not XDG

The selected `dirs 6.0.0` macOS implementation defines `cache_dir()` as the user's home directory joined with `Library/Caches`. Current Anneal therefore uses:

```text
$HOME/Library/Caches/.anneal/toolchain/<slug>
```

for its normal macOS setup path. An `XDG_CACHE_HOME` setting does not participate in this macOS `dirs` implementation.

Basis: source (`dirs 6.0.0` `src/mac.rs`) + source (`exocrate/src/lib.rs`).

### `__ANNEAL_LOCAL_DEV` selects a separate location policy

Anneal's development-location switch tests the presence of `__ANNEAL_LOCAL_DEV` using `std::env::var(...).is_ok()`. If selected, Exocrate's `LocalDev` root is:

```text
$CARGO_MANIFEST_DIR/target
```

when `CARGO_MANIFEST_DIR` is available as a UTF-8 environment variable. Otherwise Exocrate falls back to:

```text
<current-working-directory>/target
```

The same `.anneal/toolchain/<version-slug>` suffix is then appended.

This switch is independent of archive source selection. `--local-archive PATH` chooses `Source::Local(PATH)`; it does not by itself choose `Location::LocalDev`. Conversely, setting `__ANNEAL_LOCAL_DEV` while omitting `--local-archive` still chooses the development location while selecting `Source::Remote(REMOTE)`.

Basis: source.

### The version slug hashes file-path literals, file bytes, OS, and architecture in a fixed order

Anneal invokes:

```text
rel_dir_path: [".anneal", "toolchain"]
versioned_files: &["../Cargo.toml", "../Cargo.lock"]
```

Exocrate's `config!` macro feeds these bytes to SHA-256 in this exact order:

1. UTF-8 bytes of the literal `../Cargo.toml`;
2. complete bytes of `anneal/Cargo.toml` included at compile time;
3. UTF-8 bytes of the literal `../Cargo.lock`;
4. complete bytes of `anneal/Cargo.lock` included at compile time;
5. `std::env::consts::OS` bytes;
6. `std::env::consts::ARCH` bytes.

It then lower-hex encodes the 32-byte digest. There are no version numbers, archive filenames, or timestamps added separately by the macro. The platform strings ensure that the four supported Anneal OS/architecture combinations receive different identities even from identical Cargo files.

For the pinned source bytes, the derived slugs are:

| Platform | Version slug |
| --- | --- |
| Linux x86_64 | `095860c3dfb234bd94737e78858b63e4884c2b3b46286c20f8a47ff0867467f3` |
| Linux aarch64 | `022cd27a2ab9e20a836f7e2958cb59c115b5e9cb1bd299b8461bf3097fefb08f` |
| macOS x86_64 | `b2f3efc6cd1e5ca6524feed124f741bbf4ce70e477f1b37594cef5e82ebf356c` |
| macOS aarch64 | `912e3f6c7ec7fe999c8032b67c71820d4c0246a684a68c30df13dd4fc40e9514` |

The exact file SHA-256 values and Git blob IDs used in that derivation are preserved in `identity-matrix.json`.

Basis: source + derived deterministic calculation.

### The slug is a build/configuration identity, not an archive content address

The macro documentation says `versioned_files` should refer to a source of truth that changes whenever the Exocrate contents might change, and explicitly recommends `Cargo.toml` plus `Cargo.lock` as a change detector. The implementation matches that description: the slug hashes those files, not the bytes later supplied to `Source::Remote` or `Source::Local`.

For Anneal's normal remote path, the URL and expected archive SHA-256 are stored in `anneal/Cargo.toml`. A checked-in change to either therefore changes the version slug as a side effect of changing the whole Cargo file. This is useful coupling, but it remains indirect: the slug itself is not the expected archive SHA-256 and does not prove that a directory contains those archive bytes.

The distinction is sharper for `--local-archive`. The local archive's path and contents are absent from the slug calculation. A second invocation with a different local archive but the same compiled Anneal binary/configuration resolves to the same versioned directory. If that directory already exists, `resolve_installation_dir_or_install` returns `ResolvedExisting` before `open_source` is called, so the newly supplied local path is not opened at all.

Basis: source + derived state-transition consequence.

### The selected inputs intentionally over-invalidate and can also under-track non-Cargo changes

Hashing all of `Cargo.toml` and `Cargo.lock` means that changes unrelated to the packaged toolchain can create a new version slug. Exocrate's own documentation calls this an over-approximation and notes that unrelated dependency or metadata changes can proliferate versions.

The converse is equally important for Anneal engineering: files not in the two-file hash do not directly contribute to the slug. For example, changes only to `anneal/flake.nix`, `anneal/src/main.rs`, or the in-tree `exocrate` implementation leave the slug unchanged **unless** they are accompanied by a byte change to `anneal/Cargo.toml` or `anneal/Cargo.lock`. Whether such a source change actually changes the packaged toolchain is a separate question; the point is that the namespace does not mechanically encode it.

That makes the version slug unsuitable as a general proof that a cached installation corresponds to every input which produced an archive. It is only as complete as the chosen change-detector files and the release process that updates them.

Basis: source + derived dependency analysis.

### Version directories persist; Exocrate does not implement user-cache eviction

Exocrate documents that it has no helper for cleaning old installed versions. Because each distinct slug is a sibling under the configured relative directory, normal Anneal user installations can accumulate under `.anneal/toolchain/` as the compiled slug changes.

The documentation's `cargo clean` observation concerns development installations under Cargo's `target` hierarchy. It does not imply that `cargo clean` removes the normal user-cache tree. Current Exocrate exposes no corresponding user-global garbage-collection policy.

Basis: documentation + source path construction.

### Path components are constrained to a conservative cross-platform subset

`Config::new` validates every `rel_dir_path` component and the version slug as one path component. It rejects empty names, `.` and `..`, path separators, null/control bytes, Windows-reserved characters, and Windows device-name stems. Anneal's fixed `.anneal`, `toolchain`, and lower-hex digest satisfy those constraints.

This matters to the cache-layout contract because the slug cannot smuggle path traversal or nested path components into `Config::dir_path`; it is always appended as a single validated component.

Basis: source.

## Boundaries

**No fresh filesystem execution.** The exact cache-root and slug conclusions come from pinned source, dependency source, and deterministic calculation. This run did not execute Anneal under varied `HOME`, `XDG_CACHE_HOME`, `CARGO_MANIFEST_DIR`, or working-directory environments.

**The four concrete slugs are source-derived, not compiler-observed.** They were recomputed from the exact fetched `anneal/Cargo.toml` and `anneal/Cargo.lock` bytes and the `config!` algorithm. A build probe would be a cheap independent confirmation but is not required to derive the values.

**Current remote metadata remains placeholder release metadata.** `anneal/Cargo.toml` explicitly says its remote URLs and hashes must be replaced before publishing the crate. The path/versioning mechanics are current source behavior; the literal `example.com` origins are not evidence of a deployed Anneal release service.

**User-cache location is not archive trust.** Choosing an XDG/macOS cache root says where Exocrate stores a managed directory. It does not establish archive authenticity, continuous integrity of an existing directory, read-only enforcement, or extraction safety. Those are separate #3720 subjects.

**Version identity is not semantic completeness.** A slug change does not imply toolchain semantics changed, and an unchanged slug does not prove every toolchain-producing input remained unchanged. The report establishes the actual hash inputs, not a stronger equivalence relation.

**Windows and other Exocrate platforms are outside Anneal's current remote support matrix.** `dirs 6.0.0` has Windows/other-platform behavior, but current Anneal's `parse_remote_archive!` declaration enumerates only Linux and macOS on x86_64/aarch64.

**Environment-variable behavior is process-local.** The resolved cache/development path depends on the environment seen by the running process. This report does not claim that shells, service managers, IDEs, or sandboxes propagate those variables identically.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-27.

### Anneal and Exocrate source

Primary source revision: `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`.

- `anneal/src/main.rs`, blob `b947700606677ea89c7a205f3ffcc75493508f63`
  - `CONFIG`: `.anneal/toolchain`, `../Cargo.toml`, `../Cargo.lock`;
  - `REMOTE`: Linux/macOS x86_64/aarch64 matrix;
  - `setup_installation_dir`: independent location/source selection.
- `anneal/Cargo.toml`, blob `9edee13427fd5e3699abd3709cc9f33d7652873e`
  - compile-time remote URL/SHA metadata and current placeholder warning;
  - exact version-slug input bytes.
- `anneal/Cargo.lock`, blob `eeaa3f7119369d79b735d8c4836fc08bcc7f7e6d`
  - exact version-slug input bytes;
  - resolves `dirs 6.0.0` with crates.io checksum `c3e8aa94d75141228480295a7d0e7feb620b1a5ad9f12bc40be62411e38cce4e` and `dirs-sys 0.5.0`.
- `exocrate/src/lib.rs`, blob `88cc0d5dd91082070b6ef475a32bf42c25f52115`
  - `Location`, `Config::dir_path`, `Config::new`, `validate_path`, `config!`, versioning/cleanup documentation.
- `exocrate/src/sync.rs`, blob `85b6e203522e963af13d88ab4d3e7684ebb29252`
  - creation of the parent hierarchy and managed sibling lock/staging paths.

Evidence role: **source**.

### `dirs 6.0.0`

The pinned lockfile selects `dirs 6.0.0`, crates.io SHA-256 `c3e8aa94d75141228480295a7d0e7feb620b1a5ad9f12bc40be62411e38cce4e`.

- Linux source: `https://docs.rs/crate/dirs/6.0.0/source/src/lin.rs`
  - `cache_dir()` accepts an absolute `XDG_CACHE_HOME` or falls back to `$HOME/.cache`.
- macOS source: `https://docs.rs/crate/dirs/6.0.0/source/src/mac.rs`
  - `cache_dir()` returns `$HOME/Library/Caches`.

Evidence role: **source**. The crate version and crates.io checksum bind these source observations to Anneal's resolved dependency rather than to the moving `dirs` latest release.

### Derived identity matrix

`identity-matrix.json` preserves:

- the exact ordered version-slug inputs;
- SHA-256 of the two included Anneal files;
- their Git blob IDs;
- the four supported OS/architecture slug outputs;
- normal and local-development path formulas.

Evidence role: **derived** from source. The SHA-256 implementation used for the independent calculation was sanity-checked against the standard `SHA-256("abc") = ba7816bf...15ad` vector before calculating these values.

`source-map.json` provides the compact source/index map for revalidation.

## Revalidation

For a later Anneal revision, the cheapest reliable revalidation is:

1. Inspect `anneal/src/main.rs` for the `CONFIG` `rel_dir_path`, `versioned_files`, `__ANNEAL_LOCAL_DEV` test, and source selection.
2. Inspect `exocrate/src/lib.rs` for `Config::dir_path` and `config!`. If neither region changed semantically, cache-root and slug semantics remain locally stable.
3. Check the resolved `dirs` version in `anneal/Cargo.lock`. If it changed, inspect that exact version's Linux/macOS `cache_dir()` implementations rather than assuming XDG/macOS behavior remained unchanged.
4. Recompute the slug from the literal path bytes, exact included file bytes, and compile-time OS/architecture. A minimal build-time assertion which prints or compares `CONFIG`'s resolved version component would independently confirm the derivation.
5. For local-archive identity, verify whether `Source::Local` still reaches the same fixed `CONFIG` and whether existing-directory resolution still occurs before `open_source`. If either changes, reassess the conclusion that local archive identity is not part of the namespace.
6. If the toolchain builder inputs change, compare them against `versioned_files`. Any input capable of changing archive contents without changing a hashed file remains outside the mechanical cache identity and should be treated explicitly by release/test policy.

Do not re-run broad archive or concurrency research merely to revalidate this report. The discriminating surfaces are the two path/versioning functions, Anneal's two `CONFIG` inputs, and the exact `dirs::cache_dir` implementation selected by the lockfile.
