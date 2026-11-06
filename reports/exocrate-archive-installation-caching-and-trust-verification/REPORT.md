# Exocrate Toolchain Archive Installation, Cache Identity, Staging Concurrency, and Trust Verification

## Summary

Anneal uses the in-tree `exocrate` crate (`exocrate/src/lib.rs` and `exocrate/src/sync.rs` in `google/zerocopy`) to resolve or install its packaged `.tar.zst` verification toolchain into a versioned cache directory. Synthesizing source and dependency analysis across `google/zerocopy` revisions `41f5b37afe7060fd9fe08c00b200672cd76d77b9` and `bd0956be95c5f798f0c0484921b9b9d1fc6e9988`, together with resolved dependencies `tar 0.4.46` (`composefs/tar-rs@fc459c149f83bf4daceaa52e17d351989002e1a9`) and `dirs 6.0.0`, establishes five core architectural and security properties:

1. **Compile-Time Consuming-Build Version Slug and Cache Root Policy**: Exocrate installs toolchains at `<root>/.anneal/toolchain/<version-slug>`, where `<version-slug>` is a 64-hex-character SHA-256 digest computed at compile time by `exocrate::config!` over the ordered concatenation of the literal path string `../Cargo.toml`, the complete bytes of `anneal/Cargo.toml`, the literal path string `../Cargo.lock`, the complete bytes of `anneal/Cargo.lock`, `std::env::consts::OS`, and `std::env::consts::ARCH`. Unless `__ANNEAL_LOCAL_DEV` is present in the process environment (which redirects `<root>` to `$CARGO_MANIFEST_DIR/target` or `./target`), `Location::UserGlobal` resolves `<root>` via `dirs 6.0.0` to `$XDG_CACHE_HOME` on Linux only when `XDG_CACHE_HOME` is an absolute path (otherwise `$HOME/.cache`) and to `$HOME/Library/Caches` on macOS.
2. **Sibling Staging, Advisory Cross-Process Locking, and Atomic Rename Publication**: When the target directory is absent, `ManagedDirName::check_exists_or_create` acquires an exclusive `fs2` lock on a persistent sibling `<target>.lock` file, rechecks target existence under the lock, removes any stale sibling `<target>.staging` directory, extracts the archive into a fresh `<target>.staging`, and publishes the completed tree via a single same-parent `fs::rename(<target>.staging, <target>)`. Cooperating processes therefore never observe a partially unpacked target directory, though same-process concurrent calls are explicitly unsupported, no `fsync` is performed for power-loss durability, and `Path::is_dir()` is the sole completion check on existing directories.
3. **Remote SHA-256 Stream Authentication vs. Pre-Authentication Staging Extraction (`google/zerocopy#3612`)**: For `Source::Remote`, `parse_remote_archive!` compiles a 32-byte SHA-256 digest from `anneal/Cargo.toml`. During `install`, `HashingReader` hashes the compressed `.tar.zst` HTTP response-body stream and explicitly drains any unread trailing bytes to `io::sink()` through EOF before comparing the digest and allowing final rename publication. However, because `install` streams `HashingReader` directly into `zstd` and `tar::Archive::unpack` **before** finalizing the SHA-256 digest, and because `check_exists_or_create` and `StagingGuard::drop` ignore `fs::remove_dir_all(<target>.staging)` errors, an unauthenticated archive can create files inside a read-only (`0500`) subdirectory in `<target>.staging` (assisted by `tar 0.4.46` deferring directory mode application until after child entries are written). Under an unprivileged user, cleanup of that read-only directory fails, allowing the unauthenticated residue to survive into the next installation attempt and be promoted alongside a subsequently authenticated archive (`google/zerocopy#3612`).
4. **Local-Archive Checksum Bypass and Existing-Directory Precedence**: Supplying `--local-archive <path>` selects `Source::Local(PathBuf)` without altering `Location` or the compiled version slug. `Config::open_source` returns `expected_sha = None` for local archives, so `install` unpacks the file without SHA-256 hashing or trailing-byte draining. Furthermore, because `Config::resolve_installation_dir_or_install` checks `ManagedDirName::check_exists` before calling `open_source`, an already-populated `<version-slug>` directory returns `ResolvedExisting` immediately without opening, reading, or comparing a newly supplied `--local-archive` path.
5. **`tar 0.4.46` Best-Effort Extraction Containment**: `tar::Archive::unpack` blocks ordinary `..` (`ParentDir`) traversal, canonicalizes parent directories against the destination root (`validate_inside_dst`) to prevent writes outside the destination through ancestor symlinks, validates hard-link targets inside the destination, and writes unrecognized entry typeflags as regular files rather than device nodes (`mknod`/`mkfifo`), while permitting outward-pointing symlinks to exist as extracted objects and excluding concurrent hostile mutation of the destination tree from its threat model.

## Applicability

These findings apply to the in-tree `exocrate` crate (`version = "0.1.0"`) and Anneal setup wiring in `google/zerocopy`, together with its locked upstream archive and directory dependencies:

- **Primary `google/zerocopy` Revisions**:
  - `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`: `exocrate/src/lib.rs` (blob `88cc0d5dd91082070b6ef475a32bf42c25f52115`), `exocrate/src/sync.rs` (blob `85b6e203522e963af13d88ab4d3e7684ebb29252`), `anneal/src/main.rs` (blob `b947700606677ea89c7a205f3ffcc75493508f63`), `anneal/src/setup.rs` (blob `9e17911f4d1e7695cc63fe9f8b2b20b2f0322f00`), `anneal/Cargo.toml` (blob `9edee13427fd5e3699abd3709cc9f33d7652873e`), and `anneal/Cargo.lock` (blob `eeaa3f7119369d79b735d8c4836fc08bcc7f7e6d`).
  - `google/zerocopy@bd0956be95c5f798f0c0484921b9b9d1fc6e9988`: `exocrate/src/lib.rs` (SHA-256 `0dc3aefdda8938c7bfbad2a2fddd736b903bae42541cfd27686549791558a5b6`), `exocrate/src/sync.rs` (SHA-256 `7f2fdecb9258b0fb5e249b2d476b7fdb471a4935bb1d48fa328269fd3db1c631`), `anneal/src/setup.rs` (SHA-256 `a0fa4997bafe4aa2f8eafa0423c1642627bc7fcdc255b93c69b580739592b991`), and `anneal/src/main.rs`.
- **Resolved External Dependencies**:
  - `composefs/tar-rs@fc459c149f83bf4daceaa52e17d351989002e1a9` (`tar 0.4.46`, crates.io SHA-256 `3f6221d9a6003c78398e3b239969f352578258df48c8eb051caadae0015bc840`).
  - `dirs 6.0.0` (crates.io SHA-256 `c3e8aa94d75141228480295a7d0e7feb620b1a5ad9f12bc40be62411e38cce4e`).

### Multi-Revision Coverage (`41f5b37afe70` and `bd0956be95c5` vs. Historical `2dad389b030e`)

- **Invariant Across `41f5b37afe7060fd9fe08c00b200672cd76d77b9` and `bd0956be95c5f798f0c0484921b9b9d1fc6e9988`**:
  - The complete Exocrate state machine (`Config::resolve_installation_dir`, `Config::resolve_installation_dir_or_install`, `Config::open_source`, `install`, `exocrate::config!`, `parse_remote_archive!`, `ManagedDirName::check_exists_or_create`, `StagingGuard`, `<target>.lock`, and `<target>.staging`), the independence of `--local-archive` from `__ANNEAL_LOCAL_DEV`, the placeholder status of `package.metadata.exocrate` remote URLs/hashes in `anneal/Cargo.toml`, and the pre-authentication staging extraction behavior are identical across both examined `google/zerocopy` revisions.
- **Differences Relative to `google/zerocopy@2dad389b030e9268d6645ac0bf0626b867e96068` and Unmerged Repair Commits**:
  - The September 2026 rejected-archive persistence reproduction (`google/zerocopy#3612`) was executed against `2dad389b030e9268d6645ac0bf0626b867e96068` via Anneal V1's active remote-archive path.
  - Three candidate repair commits referenced in `google/zerocopy#3612` (`7c15c7984a20b0c8f8b76574c052581f1abcfc8a`, `1ef6ed4b53f162352336dae0d73dd4d362796f57`, and `4d866f8381fb79cec80e7257f15f95674441da0e`) each branch directly from `2dad389b030e9268d6645ac0bf0626b867e96068` to spool/authenticate compressed archives before extraction, but none is an ancestor of `41f5b37afe7060fd9fe08c00b200672cd76d77b9` or `bd0956be95c5f798f0c0484921b9b9d1fc6e9988` (`main` is 30+ commits ahead of that merge base and retains the pre-authentication unpack and ignored `remove_dir_all` cleanup).

## Findings

### 1. Cache Root Selection and Compile-Time Version-Slug Identity

**Basis: source + derived**

In `anneal/src/main.rs` (and `anneal/src/setup.rs`) together with `exocrate/src/lib.rs` (`support/exocrate-cache-version-identity-main-41f5b37/identity-matrix.json` and `support/exocrate-cache-version-identity-main-41f5b37/source-map.json`), Anneal declares:

```text
rel_dir_path: [".anneal", "toolchain"]
versioned_files: &["../Cargo.toml", "../Cargo.lock"]
```

1. **Independent Location and Source Switches**:
   - `setup_installation_dir` selects `Location::LocalDev` when `std::env::var("__ANNEAL_LOCAL_DEV").is_ok()`, and `Location::UserGlobal` otherwise.
   - Independently, `--local-archive <path>` selects `Source::Local(path)`, whereas omitting `--local-archive` selects `Source::Remote(REMOTE)`. Passing `--local-archive` alone still installs into `Location::UserGlobal`.
2. **Platform Cache Root Resolution (`dirs 6.0.0`)**:
   - Under `Location::UserGlobal`, `Config::dir_path` starts at `dirs::cache_dir()` (returning `io::ErrorKind::NotFound` `"cache dir not found"` if `None`).
   - On Linux (`dirs 6.0.0` `src/lin.rs`), `cache_dir()` uses `XDG_CACHE_HOME` **only** when it is an absolute path (`$XDG_CACHE_HOME/.anneal/toolchain/<slug>`), rejecting relative `XDG_CACHE_HOME` values and falling back to `$HOME/.cache/.anneal/toolchain/<slug>`.
   - On macOS (`dirs 6.0.0` `src/mac.rs`), `cache_dir()` ignores `XDG_CACHE_HOME` and returns `$HOME/Library/Caches/.anneal/toolchain/<slug>`.
   - Under `Location::LocalDev`, the root is `$CARGO_MANIFEST_DIR/target/.anneal/toolchain/<slug>` (or `<cwd>/target/.anneal/toolchain/<slug>` if `CARGO_MANIFEST_DIR` is unset or non-UTF-8).
3. **Deterministic Version-Slug Derivation**:
   - `exocrate::config!` computes SHA-256 over six inputs in exact order: (1) UTF-8 bytes of `"../Cargo.toml"`, (2) raw bytes of `anneal/Cargo.toml`, (3) UTF-8 bytes of `"../Cargo.lock"`, (4) raw bytes of `anneal/Cargo.lock`, (5) `std::env::consts::OS`, and (6) `std::env::consts::ARCH`, then lower-hex encodes the 32-byte digest and validates every path component via `validate_path`.
   - At `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` (`anneal/Cargo.toml` SHA-256 `4939ca6c1bc1eb37da5ee3c2f74c349669f2e1714f23cc4cb5bf53f64f10e6be`, `anneal/Cargo.lock` SHA-256 `ff85e2a62b5db30cf56a251500738155a9bbbe4cc946a40b8a85ebbd170565d9`), the four supported platform slugs (`support/exocrate-cache-version-identity-main-41f5b37/identity-matrix.json`) are:
     - `linux` / `x86_64`: `095860c3dfb234bd94737e78858b63e4884c2b3b46286c20f8a47ff0867467f3`
     - `linux` / `aarch64`: `022cd27a2ab9e20a836f7e2958cb59c115b5e9cb1bd299b8461bf3097fefb08f`
     - `macos` / `x86_64`: `b2f3efc6cd1e5ca6524feed124f741bbf4ce70e477f1b37594cef5e82ebf356c`
     - `macos` / `aarch64`: `912e3f6c7ec7fe999c8032b67c71820d4c0246a684a68c30df13dd4fc40e9514`
   - Because the slug hashes `Cargo.toml` and `Cargo.lock` rather than archive contents, unrelated dependency edits over-invalidate the cache (accumulating old `<slug>` directories without automatic eviction), while edits confined to `anneal/flake.nix`, `anneal/src/main.rs`, or `exocrate/src/` do not change the slug unless `Cargo.toml` or `Cargo.lock` also changes.

### 2. Installation State Machine, Advisory Locking, and Atomic Sibling Rename

**Basis: source + derived**

`Config::resolve_installation_dir_or_install` (`exocrate/src/lib.rs`) and `ManagedDirName::check_exists_or_create` (`exocrate/src/sync.rs`, modeled in `support/exocrate-atomic-staging-rename-main-41f5b37/install-protocol.json` and `support/exocrate-atomic-staging-rename-main-41f5b37/source-map.json`) execute a six-step state machine:

| Step | State Transition | Concurrency & Failure Behavior |
| :--- | :--- | :--- |
| **1. Fast-Path Check** | `ManagedDirName::check_exists` checks `<target>` before opening the source or locking. | If `Path::is_dir()` is true, returns `ResolvedExisting` immediately (no content or manifest check). If a non-directory exists at `<target>`, returns `AlreadyExists`. |
| **2. Pre-Lock Source Open** | On `NotFound`, `Config::open_source` opens the local file or initiates `ureq::get(url).call()`. | Occurs **before** acquiring `<target>.lock`. Concurrent callers that both miss Step 1 open their sources in parallel; a caller whose source open fails returns an error even if a peer concurrently completes installation. |
| **3. Exclusive Lock & Recheck** | Creates parent directories, opens persistent sibling `<target>.lock`, calls `fs2::FileExt::lock_exclusive`, constructs `StagingGuard`, and re-runs `check_exists`. | If a peer process published `<target>` while this process waited on `<target>.lock`, `check_exists_or_create` marks `StagingGuard` complete and returns without unpacking—and `resolve_installation_dir_or_install` still reports `NewlyInstalled` to the caller. `<target>.lock` is intentionally never unlinked so concurrent processes cannot lock distinct unlinked inodes. |
| **4. Staging Reset** | Calls `let _ = fs::remove_dir_all(<target>.staging);` and `fs::create_dir_all(<target>.staging)?`. | Intended to clear leftover staging state from a prior `SIGKILL` or crash, but ignores errors from `remove_dir_all`. |
| **5. Population & Digest Check** | Streams decompression and `tar::Archive::unpack` into `<target>.staging`; for `Source::Remote`, drains trailing stream bytes and compares SHA-256. | On ordinary `Err` or Rust panic, `StagingGuard::drop` runs `let _ = fs::remove_dir_all(&self.staging);` and unlocks `<target>.lock` without renaming `<target>.staging` to `<target>`. |
| **6. Atomic Publication** | Executes `fs::rename(<target>.staging, <target>)`, marks `StagingGuard` complete, and unlocks `<target>.lock`. | Because `<target>.staging` and `<target>` share the same parent directory, POSIX rename atomically publishes the directory entry to cooperating readers. No `File::sync_all` or parent directory `fsync` is performed. |

`ManagedDirName::check_exists_or_create` explicitly documents that concurrent calls **within the same process** are unsupported: both callers share the single deterministic `<target>.staging` path without an in-process mutex, and OS file locks (`flock` / `fcntl`) do not provide guaranteed mutual exclusion across file descriptors in the same process across all platforms.

### 3. Remote Checksum Semantics vs. Local-Archive Trust Boundaries

**Basis: source + derived**

1. **Remote Archive Checksum Contract (`support/exocrate-remote-archive-checksum-main-41f5b37/checksum-contract.json`, `support/exocrate-remote-archive-checksum-main-41f5b37/source-map.json`)**:
   - `parse_remote_archive!` reads `package.metadata.exocrate` from `anneal/Cargo.toml` at compile time and decodes the 64-character hex string via `macro_util::decode_hex` into `sha256: [u8; 32]` (panicking at compile time on invalid hex or unsupported OS/arch pairs).
   - In `install`, `Source::Remote` wraps the HTTP response-body reader in `HashingReader<_, sha2::Sha256>`, feeding compressed `.tar.zst` bytes to SHA-256 as they are read by `zstd::Decoder` and `tar::Archive`.
   - Because `zstd::Decoder` can stop reading at the end of a compressed frame before the HTTP stream reaches EOF, `install` explicitly drops the decoder/archive and runs `io::copy(&mut reader, &mut io::sink())?` so that any appended trailing bytes alter the final SHA-256 digest and trigger `io::ErrorKind::InvalidData` (`"SHA-256 hash mismatch"`, tested by `test_install_trailing_garbage_hash_mismatch`).
   - Because `anneal/Cargo.toml` is part of `versioned_files`, updating the pinned remote URL or SHA-256 in `anneal/Cargo.toml` automatically changes the compiled `<version-slug>` directory, preventing a rebuilt binary from silently reusing an older remote archive's directory (`test_install_already_exists`).
2. **Local Archive Trust Contract (`support/exocrate-local-archive-trust-checksum-main-41f5b37/local-trust-contract.json`, `support/exocrate-local-archive-trust-checksum-main-41f5b37/source-map.json`)**:
   - `Source::Local(PathBuf)` carries no digest. `Config::open_source` returns `(File::open(path)?, None)`, causing `install` to unpack directly through `zstd::Decoder` and `tar::Archive` without `HashingReader`, SHA-256 comparison, or trailing-byte EOF draining (`test_install_without_hash_validation`).
   - Because `--local-archive` is excluded from `exocrate::config!` and `resolve_installation_dir_or_install` checks `check_exists` before calling `open_source`, the first local archive unpacked into `<version-slug>` persists for all subsequent runs of that Anneal binary: passing a different (or even nonexistent) `--local-archive` path on a second run returns `ResolvedExisting` without opening the new path (`test_config_resolve_installation_dir_or_install_local`).

### 4. Archive Extraction Containment (`tar 0.4.46`) and Pre-Authentication Staging Residue (`google/zerocopy#3612`)

**Basis: source + documentation + derived**

1. **`tar 0.4.46` Containment Guarantees and Limits (`support/exocrate-archive-extraction-security-main-41f5b37/security-model.json`, `support/exocrate-archive-extraction-security-main-41f5b37/source-map.json`)**:
   - In `composefs/tar-rs@fc459c149f83bf4daceaa52e17d351989002e1a9` (`src/archive.rs` blob `bffeb6f1b931e44afdb636532eef085b1db65ae0`, `src/entry.rs` blob `1a4c4e9b2f045afdc42b47a9dd7eb7bea462cdeb`), `EntryFields::unpack_in` skips any entry whose path contains a `ParentDir` (`..`) component and validates every parent directory via `validate_inside_dst` (canonicalizing both the target parent and `dst` root to prevent writing outside `dst` through an existing or archive-created ancestor symlink).
   - Hard links resolve their link target beneath `dst` and pass `validate_inside_dst` before `fs::hard_link`. Symlink entries are permitted to record outward-pointing link target strings on disk, provided no later archive entry writes *through* that symlink outside `dst`. Unrecognized TAR typeflags fall through to regular file creation rather than `mknod` or `mkfifo`.
   - `src/lib.rs` (blob `8a848f28ba58cf7e3cf2018c3a5e14f4751781eb`) explicitly excludes concurrent mutation of the destination tree by another local process from its containment threat model (TOCTOU symlink swaps).
2. **Pre-Authentication Staging Mutation and Ignored Cleanup Failure (`google/zerocopy#3612`)**:
   - In `Archive::_unpack`, `tar 0.4.46` defers applying directory entries (and their Unix mode bits) until after all non-directory descendants have been unpacked, so that restrictive directory permissions do not block extracting child files.
   - Because `exocrate/src/lib.rs::install` unpacks a `Source::Remote` stream into `<target>.staging` **before** checking the SHA-256 digest, a corrupted or attacker-supplied remote stream can extract `<target>.staging/unexpected/planted` followed by a directory entry setting `<target>.staging/unexpected` to mode `0500` (`r-x------`), and only then fail the SHA-256 check (`InvalidData`).
   - When `StagingGuard::drop` runs `let _ = fs::remove_dir_all(&self.staging);` as an unprivileged Unix user, unlinking `unexpected/planted` fails with `EACCES` because `unexpected/` lacks write permission, and the error is silently discarded.
   - On the next installation attempt for the same `<target>`, `ManagedDirName::check_exists_or_create` again runs `let _ = fs::remove_dir_all(&staging);` (which fails for the same reason and discards the error) and `fs::create_dir_all(&staging)?` (which succeeds on an existing directory). When the authentic archive is then unpacked into `<target>.staging` (merging its contents without touching `unexpected/`) and passes its SHA-256 check, `fs::rename(<target>.staging, <target>)` promotes both the authentic toolchain and the unauthenticated `unexpected/planted` residue into the final `<target>` installation directory.

## Boundaries

- **Not Examined**:
  - Live execution of multi-process `check_exists_or_create` lock races, same-process thread races, or filesystem power-loss crash injection in this synthesis pass (findings are established from commit-pinned Rust source, checked-in unit tests in `exocrate/src/lib.rs` and `exocrate/src/sync.rs`, and the preserved `google/zerocopy#3612` reproduction record).
  - HTTP transport security below `ureq::get(url).call()` (TLS root store configuration, redirect handling, proxy behavior, and DNS resolution).
- **Known Not to Apply**:
  - At `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` and `bd0956be95c5f798f0c0484921b9b9d1fc6e9988`, `anneal/Cargo.toml` contains placeholder `example.com` remote archive URLs and hashes marked with a pre-publication `FIXME`; the remote checksum findings characterize the active code path rather than a live production release server.
  - Exocrate's remote SHA-256 check does not authenticate `Source::Local` archives, does not prevent pre-authentication filesystem effects inside `<target>.staging`, and does not re-verify the contents of `<target>` once `Path::is_dir()` is true.
  - Atomic sibling `fs::rename` publication does not provide crash/power-loss durability (`fsync` / `File::sync_all` are absent) and does not protect against non-cooperating local processes mutating the cache directory or staging tree concurrently.
- **Unsupported**:
  - Concurrent calls to `ManagedDirName::check_exists_or_create` for the same target within a single process are explicitly unsupported by `exocrate/src/sync.rs`.
  - Platforms outside `{linux, macos} x {x86_64, aarch64}` hit `panic!("unsupported platform")` in Anneal's `parse_remote_archive!` invocation.

## Evidence

| Category | Preserved Support Files & Upstream Source Coordinates |
| :--- | :--- |
| **Archive Extraction Security & `tar 0.4.46` Containment** | `support/exocrate-archive-extraction-security-main-41f5b37/security-model.json`, `support/exocrate-archive-extraction-security-main-41f5b37/source-map.json`; `composefs/tar-rs@fc459c149f83bf4daceaa52e17d351989002e1a9` (`src/lib.rs` blob `8a848f28ba58cf7e3cf2018c3a5e14f4751781eb`, `src/archive.rs` blob `bffeb6f1b931e44afdb636532eef085b1db65ae0`, `src/entry.rs` blob `1a4c4e9b2f045afdc42b47a9dd7eb7bea462cdeb`, `Cargo.toml` blob `258f3abda123c1abfe64532c1ff485b50f81095a`); `google/zerocopy#3612` advisory against `2dad389b030e9268d6645ac0bf0626b867e96068` and unmerged side-branch commits `7c15c7984a20b0c8f8b76574c052581f1abcfc8a`, `1ef6ed4b53f162352336dae0d73dd4d362796f57`, `4d866f8381fb79cec80e7257f15f95674441da0e`. |
| **Atomic Staging, Locking, & State Machine** | `support/exocrate-atomic-staging-rename-main-41f5b37/install-protocol.json`, `support/exocrate-atomic-staging-rename-main-41f5b37/source-map.json`; `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` (`exocrate/src/sync.rs` blob `85b6e203522e963af13d88ab4d3e7684ebb29252`, `exocrate/Cargo.toml` blob `b6cd1948ac4ae66b25a33ed93c10ee23de9b35b3`) and `google/zerocopy@bd0956be95c5f798f0c0484921b9b9d1fc6e9988` (`exocrate/src/lib.rs`, `exocrate/src/sync.rs`, `anneal/src/setup.rs`, `anneal/src/main.rs`). |
| **Cache Directory & Version-Slug Identity** | `support/exocrate-cache-version-identity-main-41f5b37/identity-matrix.json`, `support/exocrate-cache-version-identity-main-41f5b37/source-map.json`; `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` (`anneal/src/main.rs` blob `b947700606677ea89c7a205f3ffcc75493508f63`, `anneal/Cargo.toml` blob `9edee13427fd5e3699abd3709cc9f33d7652873e`, `anneal/Cargo.lock` blob `eeaa3f7119369d79b735d8c4836fc08bcc7f7e6d`, `exocrate/src/lib.rs` blob `88cc0d5dd91082070b6ef475a32bf42c25f52115`); `dirs 6.0.0` (`src/lin.rs`, `src/mac.rs`). |
| **Local Archive Trust & Checksum Bypass** | `support/exocrate-local-archive-trust-checksum-main-41f5b37/local-trust-contract.json`, `support/exocrate-local-archive-trust-checksum-main-41f5b37/source-map.json`; `exocrate/src/lib.rs` (`Source::Local`, `Config::open_source`, `install`, `test_install_without_hash_validation`, `test_install_invalid_archive`, `test_config_resolve_installation_dir_or_install_local`). |
| **Remote Archive Checksum Contract** | `support/exocrate-remote-archive-checksum-main-41f5b37/checksum-contract.json`, `support/exocrate-remote-archive-checksum-main-41f5b37/source-map.json`; `exocrate/src/lib.rs` (`RemoteArchive`, `HashingReader`, `parse_remote_archive!`, `macro_util::decode_hex`, `test_install_new`, `test_install_hash_mismatch`, `test_install_trailing_garbage_hash_mismatch`, `test_install_already_exists`). |

## Revalidation

To revalidate these findings against a newer `google/zerocopy` or `exocrate` revision:

1. **Pre-Authentication Extraction and Staging Cleanup (`exocrate/src/lib.rs`, `exocrate/src/sync.rs`)**:
   - Check `install` in `exocrate/src/lib.rs`: determine whether `Source::Remote` streams are spooled and SHA-256 verified *before* passing bytes to `zstd` and `tar::Archive::unpack`, or whether extraction still precedes digest verification.
   - Check `ManagedDirName::check_exists_or_create` and `StagingGuard::drop` in `exocrate/src/sync.rs`: determine whether `fs::remove_dir_all` errors are still ignored (`let _ = ...`) or whether staging cleanup normalizes directory permissions / uses fresh unaliased staging directories and fails closed on cleanup errors.
2. **Cache Identity and Local-Archive Precedence (`anneal/src/main.rs`, `exocrate/src/lib.rs`, `anneal/Cargo.lock`)**:
   - Inspect `CONFIG` (`versioned_files` and `rel_dir_path`), `exocrate::config!`, and `setup_installation_dir` to verify whether `--local-archive` path or content digests have been incorporated into the installation directory slug, and whether `resolve_installation_dir_or_install` still returns `ResolvedExisting` before opening `Source::Local`.
   - Check the resolved versions of `tar` and `dirs` in `anneal/Cargo.lock`; if updated, diff `EntryFields::unpack_in` / `Archive::_unpack` in `tar` and `cache_dir()` in `dirs`.
3. **Executable Unit-Test and Two-Archive Reproducer Checks**:
   - Run `cargo test --manifest-path exocrate/Cargo.toml` to execute the checked-in lockfile, staging rollback, hash-mismatch, trailing-garbage, and local-existing-target tests.
   - Run the two-archive unprivileged Unix reproducer: attempt a remote install of a wrong-hash `.tar.zst` containing a mode-`0500` directory with a child file, followed by an authentic `.tar.zst` matching the expected SHA-256, and verify that the child file from the rejected archive is absent from the published `<target>` directory.
