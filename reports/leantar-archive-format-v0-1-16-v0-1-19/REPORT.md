# `leantar` archive format and extraction behavior for Anneal's v4.30.0-rc2 toolchain

## Summary

Current Anneal does not use one `leantar` binary consistently across its Mathlib-cache pipeline. The selected Lean `v4.30.0-rc2` source defaults to bundling `leantar` `v0.1.19`, and the pinned Mathlib cache code looks up `leantar` in that Lean sysroot. Anneal's later offline unpacking stage, however, deliberately ignores the toolchain copy and fetches `leantar` `v0.1.16` directly for every supported host. This split matters because `v0.1.16` and `v0.1.19` share the same LTAR-family framing but differ materially in extraction failure semantics: `v0.1.16` writes destination files directly and rolls them back only after an error, while `v0.1.19` first writes temporary files and publishes them after the archive has been decoded.

The archive family is a purpose-built regular-file bundle, not POSIX tar. An archive starts with one of `LTAR`, `LTR2`, or `LTR3`, followed by an eight-byte little-endian Lake dependency hash. It then carries a NUL-terminated trace path and, depending on the version and trace shape, either a compact trace encoding or a zstd-compressed trace. File entries are NUL-terminated UTF-8 path strings; V3 prefixes ordinary file paths with a one-byte base-directory index. Payloads use a one-byte codec tag. Ordinary bytes use zstd; small decimal-hash files can be stored as a bare `u64`; Lean module `.olean` data uses a custom `lgz` codec wrapped in zstd, with a specialized grouped form for `.olean`, `.olean.server`, and `.olean.private`. Comments are represented as special empty-path records.

The format does not encode Unix modes, timestamps, ownership, directory entries, or symlinks. Packing follows source paths as ordinary files and unpacking creates ordinary files. The leading dependency hash is not an archive-content digest: the packer copies it from the Lake trace before writing payloads. Consequently it supports freshness/reuse decisions but does not authenticate archive bytes.

Two extraction boundaries are especially important for Anneal. First, neither examined version validates archive path strings for lexical containment before joining them to an extraction base, so `leantar` itself is not a path-traversal confinement boundary. Second, `v0.1.16` initializes `delete_corrupted` to true and, on `UnexpectedEof`, attempts to delete the input archive but does not mark the process failed. Anneal invokes `v0.1.16 -d -C ...` on fixed-output cache inputs without `-f`; a truncated archive can therefore take the special deletion path even though Anneal does not request it explicitly. Because the input is a Nix-store path, deletion may itself fail, and that deletion error is ignored. No fresh exploit or corruption probe was run, so this report preserves the source-level failure path rather than claiming a concrete current build accepted a corrupt archive.

## Applicability

The primary operational subject is `digama0/leangz@d251df00e50c98347dea3c95b1ad39a9b0d8db55`, tag `v0.1.16`, because `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` explicitly fetches that release for all four supported host systems and uses it in `packages.mathlib-cache-unpacked`.

The report also examines `digama0/leangz@bc36c619c90ae72572daad8498631d02bf45e488`, tag `v0.1.19`. `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, the source revision corresponding to the selected `v4.30.0-rc2` toolchain, sets `LEANTAR_VERSION` to `v0.1.19` when CMake does not find an existing `leantar`. The pinned Mathlib cache code at `5450b53e5ddc75d46418fabb605edbf36bd0beb6` resolves the executable as `<lean --print-prefix>/bin/leantar`. That establishes the source-defined toolchain path, but it is not a cryptographic statement about every published cache object's producer: Lean's build can use a preexisting `leantar` found by CMake, and this report did not inspect cache-service build logs for every object.

The `v0.1.16..v0.1.19` source comparison contains three commits: a trace-deserialization fix, an atomic-write change, and a follow-up that places temporary files in the target directory. No framing/codec change appears in that range. The two versions therefore share the LTAR/LTR2/LTR3 representation described here, while their destination-publication behavior differs.

This report covers `leantar` as used for Mathlib/Lake build artifacts. It does not describe the separate `leangz` single-olean CLI except where its codec implementation is reused by `leantar`.

## Findings

### The current Anneal pipeline downloads with the toolchain `leantar` available but unpacks with separately pinned `v0.1.16`

Pinned Mathlib's `getLeanTar` resolves the executable from the active Lean sysroot. Its `get-` mode downloads `.ltar` files without decompressing them, so Anneal's network-enabled fixed-output stage does not depend on the toolchain `leantar` for extraction.

Anneal then enters a distinct ordinary derivation, copies the downloaded Mathlib package trees, fetches a host-native `leantar` release directly from `digama0/leangz`, and runs that binary in parallel as:

`leantar -d -C $out <archive>`

The fetched version is explicitly `0.1.16`, even though Lean `v4.30.0-rc2` source defaults to `v0.1.19`. Anneal's nearby comment explains the direct fetch as a workaround for the Linux AArch64 Lean archive accidentally containing an x86-64 `leantar`; the implementation applies the separate `v0.1.16` fetch on every supported host rather than only AArch64.

Basis: **source**.

### LTAR-family versions are selected from the Lake trace representation

Both examined `leantar` versions recognize three four-byte magics:

- `LTAR` — V1;
- `LTR2` — V2;
- `LTR3` — V3.

Packing chooses the archive version by parsing the first trace file. A trace consisting only of a decimal integer selects V1. A JSON trace without `schemaVersion` that parses as the V2 `{depHash: ...}` shape selects V2. A JSON trace with `schemaVersion: "2025-09-10"` selects V3. Unknown or malformed trace forms become `BuildTrace::Bad` and make packing panic.

Immediately after the four-byte magic, all versions write the trace's dependency hash as an eight-byte little-endian `u64`. This is the same header field Mathlib reads when deciding whether installed artifacts already have a matching Lake `depHash`.

Basis: **source**.

### The header dependency hash is freshness metadata, not archive-byte authentication

The packer reads `depHash` from the Lake trace and writes that value into the archive header before encoding the trace and file payloads. It does not hash the resulting archive bytes and does not verify a content digest during unpacking.

The header therefore answers a Lake-state question: which dependency hash the archived module claims to represent. It does not establish that the subsequent paths and payload bytes are the unique bytes produced from that dependency state. This is consistent with the separate Mathlib cache-protocol report, which distinguishes Mathlib's source-derived object name from the archive-header Lake hash.

Basis: **source** + **derived**.

### V3 adds indexed extraction bases; paths remain UTF-8 NUL-terminated strings

The trace path is always encoded as a NUL-terminated string and is resolved against base directory zero. For ordinary entries, V1 and V2 also implicitly use base zero. V3 prefixes each ordinary path with one byte selecting a base directory, then stores the path as a NUL-terminated UTF-8 string. Grouped module payloads carry the same indexed-path encoding for the associated `.olean.server` and `.olean.private` paths.

Packing exposes the index with `-i <index> <file>`. Decompression accepts repeated `-C <DIR>` options as the initial base array. JSON stdin can override bases per archive: the `base` field may be one string or an array whose elements are strings or `null`, with each non-null element replacing the corresponding base slot.

Mathlib currently uses only the first override when consuming Mathlib as a dependency: it sends an object containing the `.ltar` path and a single `base` string pointing at the Mathlib dependency directory.

Basis: **source**.

### File payloads have six codec tags, including compact synthetic trace encodings

Both versions define these payload tags:

- `0` — zstd-compressed ordinary bytes;
- `1` — custom `lgz` Lean-module compression, itself wrapped in zstd with the bundled dictionary when default features are enabled;
- `2` — a plain eight-byte little-endian integer reconstructed as a decimal-text file;
- `3` — an eight-byte dependency hash reconstructed as the V2 JSON trace shape;
- `4` — a compact V3 Lean-module trace containing `depHash` plus output hashes;
- `5` — grouped custom `lgz` compression for `.olean`, `.olean.server`, and `.olean.private` together.

Compressed tags `0`, `1`, and `5` carry an eight-byte little-endian compressed byte length before the compressed payload. Ordinary non-olean files longer than the small decimal-hash special case are encoded with tag `0` at zstd level 19. An `.olean` file is eligible for the custom path only when its extension is `.olean` and its first five bytes are `olean`.

For V2/V3 trace payloads, a simple trace can avoid storing the original JSON entirely. A trace with no outputs can use tag `3`; a simple Lean-module output descriptor can use tag `4`, from which unpacking synthesizes canonical JSON. More complex traces are stored as ordinary zstd-compressed JSON.

Basis: **source**.

### Grouped Lean-module compression couples three adjacent `.olean` arguments

During packing, `leantar` recognizes a three-file module group only from argument order: a path ending in `.olean.private` becomes the trigger when the two immediately preceding file arguments end in `.olean` and `.olean.server`. The packer removes the preceding two entries and emits one tag-`5` record whose compressed payload expands into three byte ranges.

The grouping is therefore not inferred from matching basenames in a manifest. Callers must supply the files in the expected adjacency order. Mathlib's `mkBuildPaths`/`packCache` ordering is part of why this optimization is usable there.

Basis: **source**.

### `.ltar` preserves file bytes and selected trace structure, not general filesystem metadata

No record stores permissions, uid/gid, modification time, directory metadata, symlink targets, extended attributes, or similar tar-style metadata. Packing opens each source path as a file and memory-maps its bytes. Unpacking creates parent directories as needed and writes ordinary files.

Accordingly, `.ltar` is best understood as a Lake-artifact byte bundle with path and trace semantics, not as a general filesystem archive. A symlink supplied as a source path is followed by normal file opening rather than represented as a symlink entry; unpacking reconstructs bytes as a regular file.

Basis: **source** + **derived**.

### Comments are format records but do not participate in extraction paths

`-c COMMENT` emits a special record. In V3 it starts with base index zero, then an empty path string, then the NUL-terminated comment. V1/V2 omit the index byte. The `-k` mode scans records, skips payloads, and returns these comment strings.

Mathlib uses this facility when packing with an optional `git=mathlib4@<commit>` comment. That comment is informative metadata. Nothing in the examined `leantar` source authenticates it or binds it cryptographically to payload bytes.

Basis: **source**.

### `leantar` does not enforce extraction-path containment

On unpack, an archive path is decoded as UTF-8 and passed directly to `basedir[index].join(path)`. The implementation does not reject absolute-path syntax, parent-directory components, platform prefixes, or a canonical result outside the configured base, and it does not perform a post-join containment check.

Therefore the configured base is a relocation prefix, not a sandbox. A caller handling untrusted `.ltar` bytes must not rely on `-C` or JSON `base` to constrain all writes beneath that directory. The exact escape behavior of particular absolute/prefix strings is platform path-semantics dependent; no traversal specimen was executed for this report.

This boundary matters more because Mathlib's cache object name and the LTAR header are not content-authentication mechanisms. A system which trusts remotely supplied `.ltar` bytes is also trusting those bytes' embedded output paths unless it adds an independent validation layer.

Basis: **source** + **derived**.

### `v0.1.16` writes destination files during parsing; `v0.1.19` changed this to deferred publication

`v0.1.16` calls `File::create` or `std::fs::write` while decoding each record. It appends the resulting path to a rollback list. If a later record fails, it iterates the list and removes already-written outputs. This is best-effort rollback after mutation, not atomic archive extraction: existing files may already have been truncated/replaced, a process crash can interrupt rollback, and concurrent readers can observe intermediate files.

The `v0.1.16..v0.1.19` history contains a commit explicitly titled `feat: write files atomically`, followed by `fix: put temps in target dir`. At `v0.1.19`, extraction writes each decoded output into a `NamedTempFile`; only after the full archive has been parsed does it persist the accumulated temporary files to their final paths. If a persist operation fails, it attempts to remove paths already persisted during that final phase.

This is a material reason not to silently substitute the `v0.1.19` failure model when reasoning about current Anneal: Anneal explicitly executes `v0.1.16` in its offline Mathlib unpack stage.

Basis: **source** + **source history**.

### A truncated archive can be treated as success by the `v0.1.16` CLI's special corruption path

In `v0.1.16` `src/tar.rs`, both `json_stdin` and `delete_corrupted` are initialized to `true`. The `-j` and `-r`/`--delete-corrupted` options only assign `true` again. Thus deletion-on-corruption is active even when the caller does not pass the documented deletion option.

When `ltar::unpack` returns an `IOError` with kind `UnexpectedEof`, the CLI prints that it is removing the corrupted input and calls `remove_file`. It ignores the result of that removal and, unlike the ordinary error branch, does not set the process-wide failure flag. If no other archive in the invocation fails, the process exits zero.

Anneal's offline stage invokes one `v0.1.16` process per archive with `-d -C ...`, not `--delete-corrupted`, but the initialized default means the same branch applies. The archive inputs come from a Nix derivation path; if removal is prohibited there, the removal error is discarded by this code path. Source inspection therefore establishes a possible zero-exit path after `UnexpectedEof`. It does not establish that the current fixed-output cache contains a truncated archive or that later Anneal stages would fail to detect every resulting missing artifact.

Basis: **source** + **derived** application to current Anneal invocation.

### The reader trusts compressed length fields enough to allocate memory from them

For payload tags `0`, `1`, and `5`, unpacking reads an archive-supplied `u64` length, converts it to `usize`, resizes a `Vec` to that size, and then reads exactly that many bytes before invoking zstd/custom decompression. No archive-level compressed-size cap appears in the examined code.

This makes memory consumption part of the trust boundary for `.ltar` input. The report does not quantify allocator/platform limits or demonstrate a denial-of-service specimen.

Basis: **source**.

### Trace-hash matching can skip the entire archive or individual outputs

Unless `-f` is used, unpacking reads the destination trace before extracting. If its parsed dependency hash matches the archive header and only one base directory is in use, the function returns immediately without traversing the rest of the archive.

With multiple bases, it keeps scanning. For each record, if the trace hash matched and all paths represented by that record already exist, it seeks over the encoded payload instead of rewriting it. Thus freshness is keyed primarily to the trace hash plus output existence, not to byte comparison of every installed artifact.

Anneal's current offline invocation does not pass `-f`. Its extraction root begins freshly created in the derivation, so the normal intended case is full extraction, but the skip semantics remain part of the tool contract and matter for reused directories or other callers.

Basis: **source**.

### `v0.1.16` and `v0.1.19` are wire-compatible across the inspected change range, but not behaviorally interchangeable

The three commits between the exact tags are:

1. `7f12e76ca0384d558f568e9df441b43a747601d8` — `fix: deserialization bug`;
2. `6d1691e0a44be53e5cffbe113c6618207cfbf425` — `feat: write files atomically`;
3. `bc36c619c90ae72572daad8498631d02bf45e488` — `fix: put temps in target dir`.

The first adds serde defaults for omitted empty `log` and absent `outputs` fields in V3 traces. The latter two change file publication. The framing constants, codec tags, header encoding, path-index encoding, and packing layout are otherwise unchanged in the inspected diff.

That supports using `v0.1.16` to decode ordinary LTAR-family objects produced by the source-defined `v0.1.19` pipeline, but only at the wire-format level. The versions still differ in destination mutation and in how some preexisting V3 trace JSON is parsed for the skip decision.

Basis: **source history** + **derived** compatibility statement.

## Boundaries

- No `leantar` binary was executed and no `.ltar` specimen was generated, corrupted, traversed, or unpacked for this report.
- The report does not assert which exact `leantar` binary produced every object currently served by Mathlib's remote cache. It establishes the pinned Mathlib lookup path and Lean source default, not the complete cache-service deployment history.
- No cryptographic audit of zstd or the custom `lgz` codec was performed. Their internal compressed-stream integrity behavior is outside this report.
- The path-containment finding is source-level: no platform-specific absolute-path or `..` exploit specimen was run.
- The `UnexpectedEof` zero-exit path is source-level. The report does not claim a current Anneal build has silently accepted a corrupt cache object.
- The report does not characterize concurrency safety when multiple archives intentionally contain overlapping output paths. Current Anneal runs up to 48 independent `leantar` processes into one output tree; the intended Mathlib module layout is expected to partition ordinary file outputs, but no overlap audit was executed.
- `v0.1.19` improves publication atomicity within one archive but does not make a multi-archive Mathlib restore transaction atomic, and this report does not claim crash durability or `fsync` semantics for either version.
- `.ltar` has no content-authentication digest established here. Transport security and Mathlib cache-service trust are separate subjects; the existing Mathlib cache report covers the naming/retrieval protocol.
- The later Lean 4.31 Linux-AArch64 `leantar` bundling fix is outside this exact-pin report except as context for why Anneal carries a separate helper binary.

## Evidence

**Anneal source — current main authority.** `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `anneal/flake.nix`, blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`.

- host mappings define four `leantar` release hashes;
- `fetchLeantar` downloads `digama0/leangz` release artifacts;
- `packages.mathlib-cache-unpacked` invokes the separately fetched executable with `-d -C $out` in parallel;
- `packages.leantar` pins version `0.1.16`.

**Actual Anneal unpacker source.** `digama0/leangz@d251df00e50c98347dea3c95b1ad39a9b0d8db55`, tag `v0.1.16`.

- `src/ltar.rs`, blob `6b6e05f0a3a81bee69555a8a1ad74a1e06a6f381`: `LtarVersion`, `get_version`, `unpack`, `unpack_one`, `skip_one`, `pack`, `pack_zstd`, `comments`, codec constants, trace encodings, path/base handling, direct-write rollback.
- `src/tar.rs`, blob `866550bff26363763e1a670d1c6410d8868d5e16`: command-line parsing, JSON base overrides, parallel archive handling, corruption deletion and exit-status behavior.
- `Cargo.toml`, blob `441fc80b55cf13dde391af96a46de95c000f69a2`: package version `0.1.16` and default zstd/zstd-dictionary feature set.

**Toolchain-default leantar source.** `digama0/leangz@bc36c619c90ae72572daad8498631d02bf45e488`, tag `v0.1.19`.

- `src/ltar.rs`, blob `fb220b788c9c9ca00440d7cea7a779355f318377`: same format/parser plus temporary-file accumulation and deferred publish.
- `src/lib.rs`, blob `7cebb1db5eb95ad95c38acf93eed11e1ac55bca7`: `TempFile` backed by `tempfile::NamedTempFile`, persisted to the final destination.
- `src/tar.rs`, blob `4e806a9b0fc491117666b39ca7776164fa217036`: same CLI corruption path; archive creation also uses temporary publication.
- `Cargo.toml`, blob `e58fc7d12c01737727c7c36d13b94f3a11e40007`: package version `0.1.19` and `tempfile` dependency.

**Version-history comparison.** `digama0/leangz` compare `d251df00e50c98347dea3c95b1ad39a9b0d8db55...bc36c619c90ae72572daad8498631d02bf45e488`: three intervening commits, including the explicit atomic-write change. Observed 2026-09-27.

**Lean source selected by Aeneas.** `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, `CMakeLists.txt`, blob `3fa41c0cbc265ae4fba770b84d477b63372fa0af`.

- when no existing `leantar` is found, CMake sets `LEANTAR_VERSION v0.1.19`, chooses a platform archive, downloads it from `digama0/leangz`, and passes the executable into the build/install stages.

**Mathlib cache consumer at the exact selected revision.** `leanprover-community/mathlib4@5450b53e5ddc75d46418fabb605edbf36bd0beb6`, `Cache/IO.lean`, blob `872ffe7ce8c608f6769e3e3cc5bb5dac8f9b001a`.

- `getLeanTar` resolves the Lean-sysroot executable;
- `spawnLeanTarDecompress` sends JSON configuration to `leantar`;
- `packCache` supplies the trace first and optionally embeds the Mathlib Git comment;
- `readLtarHash` documents and parses the four-byte magic plus little-endian `u64` hash;
- `unpackCache` supplies a `base` override when Mathlib is consumed as a dependency.

**Related corpus evidence.** `reports/mathlib-lake-exe-cache-protocol-v4-30-0-rc2/` establishes the source-derived Mathlib cache key, `get`/`get!`/`get-` split, per-module artifact membership, and the distinction between the Mathlib object-name hash and the LTAR header's Lake dependency hash.

No evidence in this report is fresh **execution**.

## Revalidation

For another Anneal revision, first inspect the `packages.leantar` version and every `leantar` call site in `anneal/flake.nix`; do not assume it matches the selected Lean toolchain. Resolve the selected Lean revision and inspect its root `CMakeLists.txt` for the default `LEANTAR_VERSION`. Then compare those exact `digama0/leangz` revisions, focusing on `src/ltar.rs`, `src/tar.rs`, and any temporary-file abstraction.

A cheap format probe should create one minimal Lake V3 trace and files covering ordinary zstd, one `.olean`, a three-file `.olean`/`.server`/`.private` group, a comment, and at least two base indices. Pack with the producer candidate, decode the first twelve bytes independently, unpack with the consumer candidate under two `-C` roots, and byte-compare every output. Preserve the archive and a decoded record map as golden material.

A failure-semantics probe should truncate the archive at several boundaries: inside a path, inside an eight-byte length, and inside a compressed payload. Record output files, input-archive survival, stderr, and exit status under `v0.1.16` and the then-selected newer version. Run the probe in a disposable directory; it is intended to distinguish cleanup/exit behavior, not to validate untrusted production archives.

A confinement probe should use a synthetic archive with one path containing a parent component and one platform-appropriate absolute/prefixed path, unpack under a disposable root, and verify whether any write escapes that root. If future `leantar` adds lexical or canonical containment checks, preserve the exact source region and convert the current source-level boundary into a tested invariant.

Finally, validate Anneal's actual fixed-output cache inputs on a capable surface: enumerate archive magics, verify each archive header parses, run the selected unpacker into a fresh disposable root, and confirm every required Mathlib artifact expected by the subsequent Lake build exists. If the selected consumer remains older than the source-defined producer, keep the cross-version round-trip in the revalidation matrix rather than inferring compatibility from version order.
