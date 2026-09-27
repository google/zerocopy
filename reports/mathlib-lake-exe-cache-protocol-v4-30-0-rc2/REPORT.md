# Mathlib `lake exe cache` protocol and artifact format at v4.30.0-rc2

## Summary

Anneal's selected Aeneas release does not consume a generic Lake remote cache for Mathlib. It selects Mathlib `v4.30.0-rc2`, resolved by Aeneas's checked-in manifest to `leanprover-community/mathlib4@5450b53e5ddc75d46418fabb605edbf36bd0beb6`, and that revision carries Mathlib's repository-specific `lake exe cache` implementation. The protocol computes a custom 64-bit key for each cached Lean module, names the corresponding transport object `<16-hex-digits>.ltar`, and downloads those objects into a local Mathlib cache before optionally asking `leantar` to restore their contents into build directories.

The command variants deliberately split transport from installation. `get` downloads missing linked archives and decompresses them, `get!` forces both operations, and `get-` downloads missing linked archives without decompression. Anneal uses `get-` in its network-enabled fixed-output derivation, then reconstructs the prepared build tree in an ordinary derivation. That division is part of the protocol Anneal relies on, not an incidental CLI spelling.

The most important artifact-format distinction is that an archive carries two different hash identities at different layers. The `.ltar` **filename** is Mathlib's custom module-cache key. Separately, Mathlib's reader treats bytes 4–11 of an `LTAR`/`LTR2`/`LTR3` archive header as a little-endian Lake dependency hash and compares that value with the installed module trace's `depHash` when deciding whether decompression can be skipped. Code which treats those hashes as interchangeable can make incorrect cache-validity or relocation decisions.

## Applicability

Aeneas `ac9f1bc5262a5e4ff1e24ca78617121382202727` requires Mathlib from Git tag `v4.30.0-rc2`; its checked-in `backends/lean/lake-manifest.json` resolves that input revision to `5450b53e5ddc75d46418fabb605edbf36bd0beb6`. Its `lean-toolchain` selects Lean `v4.30.0-rc2`. This report therefore describes the Mathlib cache code Anneal's current Aeneas selection is built against, not Mathlib `master` and not later cache-service redesigns.

The protocol is directly relevant to Anneal's toolchain archive. Current Anneal `main` runs `lake exe cache get-` while network access is intentionally available, copies the resulting local Mathlib `.ltar` cache and dependency checkouts into a Nix output, and defers decompression/reconstruction to a later derivation. The same build logic later makes copied package trees writable, seeds build products, and performs offline verification. Anneal therefore depends on the precise boundary between “download archive object” and “install archive payload.”

## Findings

### The cache object is addressed by a Mathlib-specific module hash

At this revision, Mathlib computes one custom `UInt64` cache hash per covered module. `Hashing.getRootHash` hashes a generation counter together with the contents of Mathlib's `lakefile.lean`, `lean-toolchain`, and `lake-manifest.json`. `Hashing.getHash` then mixes that root hash with the module's relative `.lean` path, source contents, and hashes of covered transitive imports. `UInt64.asLTar` renders the resulting value as sixteen hexadecimal digits followed by `.ltar`.

This is the name used both in the local cache and on the wire. For the default Azure Mathlib repository, `mkFileURL` constructs `.../f/<filename>`; other repository/cache combinations include the repository name below `f/`. Parallel download configuration writes each response to `<cache>/<hash>.ltar.part`, and a successful non-parallel download likewise renames the partial file to the final `.ltar` path. Missing local archives are filtered before ordinary downloads, while forced downloads bypass that filter.

The source comment above `getRootHash` says the root hash also includes `Lean.githash`, but the implementation at this exact revision constructs the returned hash from `rootHashGeneration` and the three file-content hashes. This report follows executable source rather than extending the comment. The broader question of whether the selected key has all desirable sensitivity and collision properties is a separate inventory subject.

### `get-` is a transport-only operation

`Cache.Main` gives the three retrieval commands different state transitions:

- `get` downloads missing linked files and requests decompression.
- `get!` forces the download and unpack paths.
- `get-` downloads missing linked files but sets `decompress := false`.

`Requests.getFiles` performs downstream compatibility checks before using the cache: the project's `lean-toolchain` must match Mathlib's toolchain, and shared manifest entries must refer to matching sources. It then downloads the selected module-hash objects. If decompression is disabled, the operation ends after confirming the archives were downloaded; it does not call `unpackCache`.

This explains Anneal's fixed-output boundary. The networked derivation can materialize immutable remote objects without simultaneously mutating a Lake build tree. A later derivation can unpack or otherwise stage those bytes with network access absent. Replacing `get-` with `get` would move filesystem effects across that boundary.

### A `.ltar` is a per-module bundle of Lake build products

`IO.mkBuildPaths` defines the files Mathlib considers for one module archive. Required members are the module `.trace`, `.olean`, `.olean.hash`, `.ilean`, `.ilean.hash`, generated `.c`, and `.c.hash`. Optional members include `.olean.server`, `.olean.private`, their hash files, `.ir`, `.ir.hash`, and `.extra`.

`packCache` refuses to pack a module unless the required set exists. It passes the trace first to `leantar`, followed by the other existing paths, and can attach a `git=mathlib4@<commit>` comment. The archive is therefore not merely an `.olean` blob. It is a module-scoped snapshot containing Lake freshness metadata and multiple compiler products whose exact presence can vary with the build.

This matters to Anneal's archive pruning and relocation logic. Dropping or rewriting one member can change whether later Lake checks accept the unpacked module even if the outer Mathlib filename remains unchanged.

### The filename hash and the archive-header hash have different meanings

Mathlib's local cache filename comes from the custom module hash described above. `IO.readLtarHash`, however, interprets an archive's first twelve bytes as a four-byte `LTAR`, `LTR2`, or `LTR3` magic followed by an eight-byte little-endian hash. The caller documents that value as the Lake `depHash` embedded in the archive.

`IO.needsDecompression` reads this header hash, reads `depHash` from the currently installed module `.trace`, and skips decompression only when they match. Thus two independent questions are being answered:

1. **Which remote/local archive object corresponds to this source/import closure?** — the Mathlib custom hash in the filename.
2. **Does the installed Lake trace correspond to the build represented inside this archive?** — the Lake dependency hash in the archive header compared with `.trace.depHash`.

The distinction is operational. A system may possess the correctly named Mathlib cache object while still needing to unpack it because the installed Lake trace is absent or carries a different Lake dependency hash.

### Archive paths are not automatically location-neutral

For a downstream project consuming Mathlib, `unpackCache` can pass `leantar` a JSON object with both the archive file and a replacement `base` directory. Mathlib's source explains why: package-directory paths can appear inside generated `.ltar` files. The comment explicitly warns that changing generated archive contents without changing the custom file hash would invalidate the cache contract, and says such a format change must be paired with a root-hash invalidation.

This is a stronger constraint than “the downloaded bytes are content addressed.” At this revision, the filename is derived from source/project state, not from a cryptographic digest of the final archive bytes. A producer-side archive-layout or path-normalization change can therefore require an explicit cache-key generation/input change even when the source module is unchanged.

For Anneal, this means relocation work has two layers: prepare archives whose internal paths can be restored under the intended package base, and separately ensure the unpacked Lake traces/artifacts remain valid at the final location. The Mathlib cache tool's `base` redirection handles a particular downstream-package case; it is not a general proof that every payload byte is relocation-neutral.

### The network protocol is simple enough to mirror, but cache correctness is local-state dependent

At this pin, the read endpoint defaults to Mathlib's Azure cache unless Cloudflare is selected or `MATHLIB_CACHE_GET_URL` overrides it. Ordinary object retrieval maps a module hash to an HTTP object below `f/`; the CLI retries parallel downloads and reports missing objects. The repository also has upload and commit-manifest commands, but Anneal's current `get-` use is read-only.

A mirror only needs to serve the named `.ltar` objects to satisfy the transport half of `get-`. Correct consumption still depends on local Mathlib project metadata producing the expected custom hashes, downstream toolchain/manifest compatibility, and later `leantar`/Lake behavior when the bytes are installed. Mirroring transport objects does not erase those local preconditions.

## Boundaries

No network request, `leantar` invocation, or fresh Lean/Lake build was run for this report. Command behavior, filename construction, archive-member selection, header parsing, and downstream compatibility checks are established from the exact selected source revision. The current Anneal use of `get-` is established from `google/zerocopy` source at its current `main` revision.

This report does **not** fully specify the `leantar` binary format. It records only the header bytes and invocation semantics that Mathlib itself reads or supplies. The separate “`leantar` archive format and tool behavior” inventory item should establish framing, compression, path encoding, extraction safety, version compatibility, and any additional metadata directly from the `leantar` implementation.

This report also does not close the separate cache-key-sensitivity/collision inventory. It records enough of Mathlib's key construction to identify transport objects and to distinguish that key from Lake's `depHash`; it does not claim that the key is collision resistant or complete for every semantic build input.

Mathlib's cache service and trust model have continued evolving after this pin. Later `master` documentation and CI behavior must not be projected backward onto `5450b53e...` without source-history evidence.

## Evidence

- **Aeneas selects the Mathlib revision — source.** `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, `backends/lean/lakefile.lean`, requires Mathlib at input revision `v4.30.0-rc2`; `backends/lean/lake-manifest.json` resolves it to `5450b53e5ddc75d46418fabb605edbf36bd0beb6`; `backends/lean/lean-toolchain` selects Lean `v4.30.0-rc2`.
  - https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/backends/lean/lakefile.lean
  - https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/backends/lean/lake-manifest.json
  - https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/backends/lean/lean-toolchain

- **CLI split between `get`, `get!`, and `get-` — source.** `leanprover-community/mathlib4@5450b53e5ddc75d46418fabb605edbf36bd0beb6`, `Cache/Main.lean`, blob `12f69c07522f61db89318bc8331b5eb395b45377`, defines the commands and dispatches `get-` with decompression disabled.
  - https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Cache/Main.lean

- **Custom module-cache key — source.** Same revision, `Cache/Hashing.lean`, blob `418e884d1262cd8655ceddccf0e3c5894f742e46`, `getRootHash` and `getHash`; `Cache/Lean.lean`, blob `0934e22f2dc396411106b008016fba4569cf741d`, `UInt64.asLTar`.
  - https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Cache/Hashing.lean#L88-L165
  - https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Cache/Lean.lean

- **Transport naming and retrieval — source.** Same revision, `Cache/Requests.lean`, blob `2f59d1ec95d8f04574c74b869afd4473acf60406`, `mkFileURL`, `mkGetConfigContent`, `downloadFile`, `downloadFiles`, and `getFiles`; lines 581–653 implement downstream toolchain/manifest compatibility checks.
  - https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Cache/Requests.lean#L253-L341
  - https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Cache/Requests.lean#L501-L704

- **Artifact membership and archive creation — source.** Same revision, `Cache/IO.lean`, blob `872ffe7ce8c608f6769e3e3cc5bb5dac8f9b001a`, `mkBuildPaths` lines 268–307 and `packCache` lines 321–351.
  - https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Cache/IO.lean#L268-L351

- **Archive-header Lake hash and unpack decision — source.** Same file, `readLtarHash`, `needsDecompression`, and `unpackCache`, lines 379–464. The source recognizes `LTAR`, `LTR2`, and `LTR3`, decodes the following 8-byte little-endian value, and compares it with the installed trace `depHash`.
  - https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Cache/IO.lean#L379-L464

- **Mathlib user-facing protocol description — documentation at the exact pin.** Same revision, `Cache/README.md`, blob `2c25714653f41c9c378849abb8d59f92145fd9b3`. It describes command roles, `.ltar` cache files, cache directories, and read endpoints.
  - https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Cache/README.md

- **Anneal's two-stage consumption — source.** `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `anneal/flake.nix`, blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`, lines 325–350. The fixed-output derivation runs `lake exe cache get-`, copies the local Mathlib cache and package checkouts, and explicitly defers decompression to the ordinary derivation.
  - https://github.com/google/zerocopy/blob/41f5b37afe7060fd9fe08c00b200672cd76d77b9/anneal/flake.nix#L325-L350

## Revalidation

For source-only revalidation, first confirm that Aeneas still resolves Mathlib to `5450b53e5ddc75d46418fabb605edbf36bd0beb6` and that the cited Mathlib blobs are unchanged. The load-bearing invariants are: the three retrieval commands retain their download/decompression split; `UInt64.asLTar` remains the transport filename; `mkBuildPaths` and `packCache` still define a per-module archive with the trace first; `readLtarHash` still reads a distinct Lake hash from the archive; and `unpackCache` still uses that value to decide whether installed outputs need restoration.

An execution revalidation should use a clean cache directory. Run `lake exe cache get-` for one small covered module and record the resulting `.ltar` filename without unpacking it. Compute the module's Mathlib cache key through the pinned cache tool and verify that the filename matches. Inspect only the first twelve archive bytes and compare Mathlib's decoded header value with the `depHash` in the trace produced after unpacking. Then delete the unpacked products while retaining the archive and verify that a later unpack restores them without network access.

For the Anneal-specific boundary, repeat the networked `get-` stage in one directory, move or copy the downloaded cache and selected package tree into a second root, deny external network access, and perform only the reconstruction/unpack stage there. Record which paths are supplied through `leantar`'s downstream `base` redirection and which archive members retain producer-root strings. Treat any proposed producer-side normalization of `.ltar` bytes as a cache-format change unless the Mathlib custom cache key is invalidated at the same time.
