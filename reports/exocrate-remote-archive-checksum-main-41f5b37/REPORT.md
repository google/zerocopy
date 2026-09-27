# Exocrate remote archive checksum semantics at Anneal main 41f5b37

## Summary

Current Anneal supplies Exocrate with one compile-time `RemoteArchive` for the host OS/architecture. Its configured checksum is a 32-byte SHA-256 value decoded from exactly 64 hexadecimal digits in `anneal/Cargo.toml`. For a new remote installation, Exocrate hashes the **compressed HTTP response-body bytes exposed by its reader**, not the decompressed tar contents. The hash covers the stream through EOF: after tar/zstd extraction finishes, Exocrate explicitly drains the underlying hashing reader so trailing bytes which zstd did not need to decompress still affect the digest.

A matching digest is required for a new remote population to return success and become eligible for Exocrate's final publication step. A mismatch returns `InvalidData`. This is an integrity check relative to the checksum compiled into the Anneal binary; it is not a signature or a provenance mechanism for that checksum.

Two boundaries matter. First, current Exocrate performs tar extraction into staging **before** it finalizes and accepts the checksum. The checksum therefore gates successful population/publication, not all pre-authentication filesystem effects; the rejected-archive advisory is covered separately. Second, an already-existing managed installation is accepted by existence and is not rehashed against the current `RemoteArchive`. Anneal partly couples checksum changes to a fresh installation namespace because its Exocrate version slug hashes `Cargo.toml`, `Cargo.lock`, OS, and architecture, so changing the configured URL/checksum changes the target version directory absent a SHA-256 collision.

## Applicability

These findings apply to `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, especially `exocrate/src/lib.rs`, plus Anneal's `anneal/src/main.rs` and `anneal/Cargo.toml` at the same revision.

Anneal's setup command selects `Source::Remote(REMOTE)` when `--local-archive` is absent. `REMOTE` is constructed by `parse_remote_archive!` from platform-specific `package.metadata.exocrate` entries in `Cargo.toml`; `CONFIG` derives its version slug from `Cargo.toml`, `Cargo.lock`, the configured file-path strings, host OS, and host architecture.

Current `main` still marks the remote URLs and hashes as placeholders to be replaced before publishing the crate. The report therefore establishes the current **protocol and code-path contract**, not that the literal current `example.com` metadata is a deployed production release origin.

`Source::Local` follows a different trust model: Exocrate passes `None` as the expected checksum and performs no equivalent SHA-256 comparison. That is a separate #3720 subject and is not generalized from the remote findings here.

## Findings

### 1. The expected digest is compile-time platform metadata

`RemoteArchive` stores `url: &'static str` and `sha256: [u8; 32]`. `parse_remote_archive!` reads the selected `Cargo.toml` at compile time, matches the current `std::env::consts::{OS, ARCH}` against the OS/architecture pairs named at the macro invocation, and selects the corresponding metadata entry.

`macro_util::decode_hex` accepts exactly 64 hexadecimal bytes and decodes them to `[u8; 32]`; digits may be lowercase or uppercase. Invalid length or a non-hexadecimal nibble returns `None`, and the macro converts that to `panic!("invalid sha256")` in the const construction. There is no runtime text parsing or fallback from an invalid configured checksum to an unchecked remote install.

Anneal lists four supported metadata pairs in this invocation: Linux x86-64, macOS x86-64, Linux AArch64, and macOS AArch64. Unsupported pairs hit the macro's `panic!("unsupported platform")` path during constant evaluation.

Basis: source.

### 2. The checksum domain is the compressed response body, not decompressed tar contents

For `Source::Remote`, `Config::open_source` issues `ureq::get(url).call()`, turns the successful response body into a reader, and returns that reader together with `Some(sha256)`. `install` wraps the reader in `HashingReader`; every byte returned by the underlying reader is fed to `sha2::Sha256` before the same bytes are handed upward.

The layering is:

`remote response body reader -> HashingReader -> zstd decoder -> tar::Archive`.

Therefore the digest is over the `.tar.zst` response-body representation. Two byte-distinct compressed representations which decompress to the same tar tree have different expected SHA-256 values.

The phrase “response-body bytes” is intentional. The source hashes bytes exposed by the HTTP body reader; this report does not equate that with raw transport framing or other bytes consumed below that abstraction.

Basis: source.

### 3. Trailing bytes after the decompressible archive are intentionally authenticated

A zstd decoder can stop once it has enough input to finish decompression, leaving bytes unread in the underlying source. Current Exocrate accounts for that case explicitly. It drops the decoder/archive scope, then copies the remaining `HashingReader` bytes into an I/O sink until EOF before finalizing SHA-256.

As a result, bytes appended after an otherwise valid compressed archive still change the digest. The checked-in `test_install_trailing_garbage_hash_mismatch` constructs a valid `.tar.zst`, records its digest, appends `trailing garbage data`, and expects the installation to fail with `InvalidData` even though decompression/extraction can finish without needing those trailing bytes.

That checked-in test is source evidence for the intended invariant. This report did not independently execute it.

Basis: source, including checked-in test contract.

### 4. Digest mismatch is a population failure, not a successful installation

After draining the input, Exocrate finalizes the SHA-256 and compares `[u8; 32]` values directly. Inequality returns an `io::Error` with kind `InvalidData` and message `SHA-256 hash mismatch` from inside the managed-directory population closure.

The normal staging protocol publishes the staging directory only when that closure succeeds, so a checksum mismatch does not itself authorize the final staging-to-target rename. `test_install_hash_mismatch` records this expected ordinary-case behavior: wrong digest -> error -> no final target, with cleanup leaving no non-lock sibling in its uncomplicated test fixture.

This is weaker than saying that rejected bytes caused no filesystem effects. Extraction has already happened in staging by the time of comparison, and failure cleanup can itself fail. Those security consequences are the subject of the separate rejected-archive report.

Basis: source + checked-in test contract; staging/publication relationship cross-checked against `exocrate/src/sync.rs`.

### 5. Successful validation authenticates the input stream, not a reconstructed directory

The compared digest is computed over remote body bytes, while the output directory is produced earlier by zstd/tar extraction. Exocrate does not subsequently serialize the resulting directory and compare a content-tree hash. Thus the direct statement supported by the checksum is:

> the bytes read from the remote response body equal the byte string whose SHA-256 is the compiled expected digest.

Mapping those bytes to extracted filesystem state relies on the zstd/tar implementation and on staging being free of unrelated residue. The latter qualification is material because #3612 demonstrates that a failed earlier extraction can leave residue which a later digest-matching stream did not contain.

Basis: source + derived distinction between stream integrity and resulting-tree integrity.

### 6. Existing installations are not rehashed or compared with the remote digest

`Config::resolve_installation_dir_or_install` computes the target path and first calls `ManagedDirName::check_exists`. If the target already exists as a managed directory, it returns `ResolvedExisting` before opening the supplied source. The lower-level install path has a second under-lock target-exists check as part of its process-concurrency protocol.

The checked-in `test_install_already_exists` makes the intended behavior explicit at the lower layer: with a preexisting target, invalid archive bytes plus a deliberately wrong hash still return success without reading the source or validating the checksum.

Consequently the configured remote checksum is an **installation-time check for a new population**, not a continuous integrity check on an installed tree. Exocrate does not rehash installed files on reuse.

Basis: source + checked-in test contract.

### 7. Anneal couples metadata changes to installation identity

Anneal invokes `exocrate::config!` with `versioned_files: &["../Cargo.toml", "../Cargo.lock"]`. The macro hashes, in order, each configured path string and the corresponding complete file bytes, then the compile-time OS and architecture; it hex-encodes that SHA-256 as the version slug.

Because the platform URL and expected checksum live in Anneal's `Cargo.toml`, changing either metadata value also changes the version slug and therefore the installation directory, barring a SHA-256 collision. This provides an important practical boundary around “existing targets are not revalidated”: a binary rebuilt after changing its own checked-in remote checksum normally points at a distinct Exocrate installation namespace rather than silently accepting the old namespace.

The coupling is intentionally broader than checksum identity. Any change to the versioned `Cargo.toml` or `Cargo.lock`, even unrelated to the archive, also changes the slug. Exocrate documents that over-approximation as a versioning tradeoff.

Basis: source + derived namespace consequence.

### 8. The checksum's provenance is outside Exocrate's integrity mechanism

Exocrate receives an ordinary expected SHA-256 value from compile-time metadata and compares the remote body against it. SHA-256 here detects substitution/corruption **relative to trust in that expected value**. The mechanism contains no signature verification, transparency-log verification, or independent provenance check for the checksum itself.

For Anneal, the current source-of-truth location is checked-in `Cargo.toml`, which is also incorporated into Exocrate's installation version slug. Whether future release engineering obtains and reviews those checksum values securely is a separate supply-chain/release-provenance question.

Basis: source + direct trust-boundary analysis.

## Boundaries

- **No fresh network or checksum execution.** The report revalidated current source and checked-in tests but did not serve archives or execute the hash tests in this run.
- **Current Anneal remote metadata is placeholder-only.** The protocol is real; the literal current URLs/checksums are explicitly marked FIXME before publication.
- **Not raw HTTP wire bytes.** The checksum covers bytes delivered by Exocrate's response-body reader. This report does not claim inclusion of transfer framing or lower-level TLS/HTTP representation details.
- **Extraction-before-authentication is separate.** The checksum is checked after extraction effects. The resulting rejected-archive vulnerability and tar containment behavior are documented in the dedicated extraction-security candidate, not duplicated here.
- **No installed-tree integrity guarantee.** Existing targets are accepted without rehashing. File mutation after installation is outside this checksum check.
- **No guarantee that the expected digest is trustworthy.** The hash is not a signature and Exocrate does not establish the release process that generated it.
- **Local archives are separate.** `Source::Local` supplies no expected digest. Do not infer remote checksum guarantees for `--local-archive`.
- **No claim about cryptographic SHA-256 collision/preimage strength beyond using SHA-256.** The implementation uses SHA-256 as specified; this report does not independently analyze the primitive.
- **HTTP behavior below the reader abstraction was not audited.** Redirect policy, TLS root configuration, content decoding, proxies, and network retry behavior belong to the HTTP-client/network layer unless they alter the body bytes presented to Exocrate.

## Evidence

Primary source, observed 2026-09-27:

- `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `exocrate/src/lib.rs`, blob `88cc0d5dd91082070b6ef475a32bf42c25f52115`:
  - `RemoteArchive` and `Source` define the remote URL + 32-byte digest interface;
  - `Config::open_source` maps `Source::Remote` to the HTTP response-body reader plus `Some(sha256)`;
  - `install` defines hashing-reader placement, zstd/tar extraction ordering, trailing-byte drain, digest comparison, and mismatch error;
  - `parse_remote_archive!` and `macro_util::decode_hex` define platform selection and 64-hex-digit decoding;
  - `config!` defines the installation version slug from versioned files plus OS/architecture;
  - `test_install_new`, `test_install_hash_mismatch`, `test_install_trailing_garbage_hash_mismatch`, and `test_install_already_exists` preserve key intended behavior as tests.
- `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `anneal/src/main.rs`, blob `b947700606677ea89c7a205f3ffcc75493508f63`: Anneal's `CONFIG`, `REMOTE`, and remote-vs-local selection.
- Same revision, `anneal/Cargo.toml`, blob `9edee13427fd5e3699abd3709cc9f33d7652873e`: platform metadata and explicit placeholder/FIXME status.
- Same revision, `exocrate/src/sync.rs`, blob `85b6e203522e963af13d88ab4d3e7684ebb29252`: managed-directory population/publication boundary used to interpret mismatch as a failed population rather than a final rename.

The package preserves `checksum-contract.json` with the byte-domain, state ordering, namespace coupling, and trust boundaries, plus `source-map.json` with exact source coordinates and links to adjacent candidate subjects.

## Revalidation

For a later Exocrate/Anneal revision, use these narrow checks:

1. Inspect `RemoteArchive`, `parse_remote_archive!`, and `macro_util::decode_hex`. Record whether the expected digest is still compile-time platform metadata, its algorithm/encoding, and whether invalid metadata can degrade to unchecked operation.
2. Inspect `Config::open_source` and the exact reader layering in `install`. Identify the abstraction whose bytes enter the hasher and whether hashing occurs before or after any content transformation.
3. Verify EOF coverage. If decompression can terminate before the body reader reaches EOF, check whether the remaining body is deliberately consumed into the same digest. Preserve a trailing-byte test because it discriminates this behavior directly.
4. Inspect the target-exists fast paths. Determine whether an existing installation is revalidated, trusted by namespace identity, or accepted by existence alone.
5. Inspect Anneal's `config!` `versioned_files` and checksum metadata location. Confirm whether changing the configured digest changes the installation namespace; do not assume this if metadata moves outside the versioned inputs.
6. If high assurance is required, run three tiny probes against the examined revision: correct digest succeeds; one-byte digest mismatch fails; correct digest for a prefix plus appended trailing bytes fails. Separately test the existing-target fast path to establish whether it reads or hashes the source.
7. Revalidate extraction-security separately. Moving checksum verification before extraction would materially improve that boundary without changing the basic digest-domain conclusions.
