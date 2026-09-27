# Exocrate local archive trust and checksum semantics at Anneal main 41f5b37

## Summary

Current Anneal's `--local-archive` option changes **where setup reads the toolchain archive**, but it does not add the local archive's path or contents to Exocrate's installation identity and it does not authenticate those bytes. Anneal passes the path as `Source::Local`. Exocrate opens that file and returns the reader with `expected_sha = None`; the installation path then sends the reader directly through zstd and tar without a SHA-256 wrapper or digest comparison.

For a fixed Anneal build and host platform, local and remote sources therefore address the same versioned installation directory. The directory name comes from Anneal's `Cargo.toml`, `Cargo.lock`, the configured versioned-file path strings, OS, and architecture—not from the selected local archive. If that directory already exists, Exocrate returns it before opening the supplied source. Its checked-in local-install test makes the consequence explicit: after one local archive has populated the target, a second call may supply a nonexistent local path and still resolve the existing target successfully.

The useful trust statement is consequently narrow: a new `Source::Local` installation trusts the bytes read from the caller-selected local file as archive input. Exocrate still requires those bytes to be acceptable to zstd/tar before ordinary successful publication, but it provides no content hash, signature, release identity check, or continuous installed-tree integrity check for this path. A different parseable local archive can populate the same namespace when no target is already present; once that target exists, later local-source choices do not replace or revalidate it.

## Applicability

These findings apply to `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, principally `exocrate/src/lib.rs`, `exocrate/src/sync.rs`, `anneal/src/main.rs`, `anneal/Cargo.toml`, and `anneal/Cargo.lock`.

The current `cargo anneal setup` CLI exposes `--local-archive <path-to-local-archive>`. When supplied, `setup_installation_dir` constructs `exocrate::Source::Local(local_archive)`; otherwise it uses `Source::Remote(REMOTE)`. Both choices are passed to the same `CONFIG.resolve_installation_dir_or_install` call. `CONFIG` uses `[".anneal", "toolchain"]` and versioned files `../Cargo.toml` and `../Cargo.lock`.

The report is specifically about the local-source trust/integrity boundary. The remote source uses a materially different checksum path, and archive extraction security has separate path/link/staging concerns. Those adjacent subjects constrain some conclusions here but are not merged into this report.

The checked-in tests cited below were inspected as source/test-contract evidence; they were not rerun in this investigation.

## Findings

### 1. `--local-archive` selects a filesystem path, not a digest-bearing source

Anneal parses the option as a `PathBuf`. Its setup logic chooses:

- `Source::Local(local_archive)` when the option is present;
- `Source::Remote(REMOTE)` otherwise.

`Source::Local` itself stores only a `PathBuf`. By contrast, `Source::Remote` carries a `RemoteArchive` containing both a URL and `[u8; 32]` SHA-256 value.

In `Config::open_source`, the local branch performs `File::open(path)` and returns the resulting reader together with `None` for the expected checksum. The remote branch returns its response-body reader with `Some(sha256)`.

That `Option<[u8; 32]>` is the branch point which determines whether `install` performs content authentication. The local-source API carries no field from which an expected digest could be obtained later.

Basis: source.

### 2. A new local installation performs no Exocrate checksum comparison

`install(reader, dst, expected_sha256)` has two branches. When an expected digest is present, Exocrate inserts a `HashingReader`, computes SHA-256 across the remote input through EOF, and compares the final digest. When the value is `None`, it instead constructs a zstd decoder directly over `reader`, constructs a tar archive over that decoder, and unpacks into the managed staging directory.

The local path reaches the `None` branch. It therefore has:

- no `HashingReader`;
- no SHA-256 finalization;
- no expected-versus-observed digest comparison;
- no hash-mismatch error path;
- no explicit post-decompression drain of the underlying input to make every file byte participate in an integrity check.

The final point is a boundary rather than a claim that particular trailing bytes are always unread: zstd/tar may read ahead. The source simply provides no local-source requirement to consume the entire file after extraction, because there is no digest whose domain must extend to EOF.

Basis: source.

### 3. Successful parsing is not content authentication

A malformed local `.tar.zst` can still fail because the zstd decoder or tar unpacker returns an I/O error. The checked-in `test_install_invalid_archive` exercises this no-hash path with bytes that are not a valid zstd/tar archive and expects failure.

That behavior establishes format/processing validity for the operations actually attempted; it does not authenticate the archive. Any different local byte string that the decompressor and extractor accept can proceed through the same success path. Exocrate does not compare the archive against a release digest, signature, expected file manifest, tool version, or reconstructed tree hash.

Thus “local” is a source-location category, not a stronger provenance assertion encoded by Exocrate.

Basis: source + checked-in test contract + derived trust-boundary distinction.

### 4. The local archive path and contents do not participate in Anneal's Exocrate version slug

Anneal defines `CONFIG` with:

`versioned_files: &["../Cargo.toml", "../Cargo.lock"]`.

The `exocrate::config!` macro computes the slug by hashing, in order:

1. each configured path string;
2. the complete bytes included from each configured file;
3. compile-time `std::env::consts::OS`;
4. compile-time `std::env::consts::ARCH`.

It then hex-encodes that SHA-256 and passes it to `Config::new`.

Neither the runtime `--local-archive` path nor the selected archive's bytes are inputs to this calculation. Consequently, for the same built Anneal configuration and platform, two different local archive paths—and two different byte contents at the same path—address the same Exocrate target directory.

This differs from the remote metadata case in one practical respect: Anneal's remote URL and expected digest live in `Cargo.toml`, so changing those checked-in values changes a versioned input. Runtime selection of a local file does not.

Basis: source + derived namespace consequence.

### 5. Existing installation state outranks the supplied local source

`Config::resolve_installation_dir_or_install` computes the installation directory and checks it before calling `open_source`. If the target is already a managed directory, the function returns `ResolvedExisting` immediately.

The supplied `Source` is therefore not opened on this fast path. For local sources, that means Exocrate does not check whether the given path exists, does not read it, and does not compare it with the existing installation.

The checked-in `test_config_resolve_installation_dir_or_install_local` records this behavior directly. It first installs a real local archive. It then calls the same configuration again with `Source::Local("/nonexistent/path/should/not/be/accessed")` and expects successful `ResolvedExisting` resolution of the first installation.

The managed-directory implementation also rechecks for an existing target after acquiring its writer lock, so another process may finish the shared target while a caller is waiting. That process-concurrency machinery is adjacent scope; the trust consequence here is simply that existing target presence can eliminate any need to consume the local source.

Basis: source + checked-in test contract.

### 6. For one namespace, the first successfully published local payload becomes the reused payload until the namespace changes or is removed

Combining the namespace and target-exists rules yields the operational consequence most likely to be missed:

1. Anneal chooses a versioned target from build metadata and platform.
2. A caller may choose any local archive path at runtime.
3. If the target is absent, that local file is opened and its decompressed tar contents are staged.
4. On successful population, Exocrate's managed-directory path renames staging to the fixed target.
5. Later setup calls for that same namespace return the existing target without consulting their supplied local archive.

Accordingly, `--local-archive` is not an alternate cache key. It is an alternate source for populating the current cache key. If two acceptable local archives differ, which one supplies the target depends on which one successfully populates the absent namespace first; a later invocation does not switch the target merely because it names a different archive.

This is a derived conclusion from the source-selection, version-slug, and existing-target rules. It does not add a claim about same-process concurrency, which Exocrate explicitly treats separately.

Basis: source + derived state transition.

### 7. The trust root for local archive integrity is outside Exocrate

On the local path, Exocrate receives only a filesystem path and eventually bytes from a `File`. The implementation has no independently authenticated expected value for those bytes.

A caller that requires “this is exactly the intended Anneal toolchain archive” therefore needs that guarantee from outside the local-source mechanism—for example from how the file was produced, transferred, selected, or independently verified. Current Exocrate does not convert such external trust into a persisted digest attached to the installation, and it does not recheck the installed tree on later resolution.

This report does not prescribe which external mechanism Anneal should use. It only identifies the current boundary: Exocrate's local mode delegates archive identity/integrity to the caller and environment.

Basis: source + direct trust-boundary analysis.

## Boundaries

- **No fresh execution.** The report revalidated source and checked-in tests but did not run Exocrate, mutate archives, or trace filesystem reads.
- **No remote-checksum generalization.** `Source::Remote` passes `Some(sha256)` and has a separate byte-domain/checksum contract. Those guarantees do not apply to `Source::Local`.
- **No claim that all local file bytes are consumed.** The no-hash branch has no explicit EOF drain after zstd/tar completion. Decoder buffering determines the exact bytes read beyond what is needed to unpack.
- **No archive-extraction sandbox claim.** Path traversal, symlink/hardlink containment, rejected-archive residue, and concurrent destination mutation belong to the archive-extraction-security subject.
- **No publication-durability claim.** Staging/rename atomicity and `fsync`/power-loss behavior are separate Exocrate state-machine subjects.
- **No same-process concurrency guarantee.** `ManagedDirName::check_exists_or_create` explicitly documents same-process concurrent calls as unsupported. This report uses only the existence/lock transitions needed to explain source bypass.
- **No installed-tree integrity guarantee.** Exocrate resolves an existing directory by state/existence; it does not hash the tree or compare it to the local archive on reuse.
- **No immutability guarantee for the source file while it is being read.** The local file is an ordinary filesystem input. This investigation did not characterize concurrent modification semantics of the underlying filesystem/file descriptor.
- **No assertion that a structurally valid archive is semantically usable by Anneal.** Later consumers may fail if expected tools/layouts are missing or incompatible; Exocrate's local installation path has no semantic manifest check that prevents such a payload from being published first.
- **No V1 continuity claim.** The report is about current main. Historical Anneal V1 behavior is not used as authority.

## Evidence

Primary source, observed 2026-09-27:

- `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `exocrate/src/lib.rs`, blob `88cc0d5dd91082070b6ef475a32bf42c25f52115`:
  - `Source` defines `Local(PathBuf)` without checksum metadata;
  - `Config::resolve_installation_dir_or_install` checks target existence before opening the source;
  - `Config::open_source` maps `Source::Local` to `File::open` plus `None`;
  - `install` sends the no-digest branch directly through zstd/tar and performs no SHA-256 comparison;
  - `config!` defines the slug inputs;
  - `test_install_without_hash_validation`, `test_install_invalid_archive`, and `test_config_resolve_installation_dir_or_install_local` preserve the intended local-source behavior as tests.
- Same revision, `exocrate/src/sync.rs`, blob `85b6e203522e963af13d88ab4d3e7684ebb29252`: `ManagedDirName::check_exists_or_create` supplies the under-lock existing-target recheck, staging population, and successful staging-to-target rename used in the state-transition analysis.
- Same revision, `anneal/src/main.rs`, blob `b947700606677ea89c7a205f3ffcc75493508f63`: current CLI option, `CONFIG`, and runtime local-versus-remote source selection.
- Same revision, `anneal/src/setup.rs`, blob `9e17911f4d1e7695cc63fe9f8b2b20b2f0322f00`: a second current-main setup helper carries the same `Source::Local` versus `Source::Remote` selection and the same versioned-file configuration; this is corroborating source, not evidence that every helper is reached by the current CLI.
- Same revision, `anneal/Cargo.toml`, blob `9edee13427fd5e3699abd3709cc9f33d7652873e`: one of the two Anneal versioned inputs and the location of remote metadata.
- Same revision, `anneal/Cargo.lock`, blob `eeaa3f7119369d79b735d8c4836fc08bcc7f7e6d`: the other Anneal versioned input.

The package preserves `local-trust-contract.json` as a compact state/trust matrix and `source-map.json` with exact implementation coordinates.

## Revalidation

For a later Exocrate/Anneal revision, the cheapest discriminating checks are:

1. Inspect the `Source` type and `Config::open_source`. If local sources now carry a digest/signature or return `Some(expected_sha)`, the core no-authentication finding has changed.
2. Inspect `install`. Determine whether the local/no-digest path still bypasses hashing and whether any new validation occurs before or after extraction.
3. Inspect `exocrate::config!` and Anneal's `CONFIG` invocation. List every version-slug input explicitly. Check whether the local path, local file contents, a local digest, or other source identity has become part of the namespace.
4. Inspect `resolve_installation_dir_or_install` and `ManagedDirName::check_exists_or_create`. Confirm whether existing targets still bypass source opening and whether any revalidation occurs on reuse.
5. Retain or rerun the checked-in local-install discriminator: install one local archive, then call the same configuration with a nonexistent or different local path. Success without accessing the second source demonstrates the existing-target bypass.
6. If byte-consumption semantics matter, use a file/reader probe that records reads while appending harmless trailing bytes to an otherwise valid `.tar.zst`. Do not infer EOF coverage from the remote path, whose explicit hash drain is absent here.
7. Revalidate archive extraction safety and publication durability independently; neither is established by a future local checksum unless their own state transitions also change.
