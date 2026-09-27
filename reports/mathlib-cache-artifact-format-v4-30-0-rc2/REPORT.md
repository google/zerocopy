# Mathlib cache artifact contents at the Anneal-selected v4.30.0-rc2 revision

## Summary

At `leanprover-community/mathlib4@5450b53e5ddc75d46418fabb605edbf36bd0beb6`, Mathlib's cache is a per-module archive store. Each selected Lean module maps to one hash-named `.ltar` file. Packing requires a core set of Lake/Lean outputs for that module and includes several additional outputs when present.

The core required files are the module's `.trace`, `.olean`, `.olean.hash`, `.ilean`, `.ilean.hash`, generated `.c`, and `.c.hash`. Optional files are `.olean.server`, `.olean.private`, their `.hash` files, `.ir`, `.ir.hash`, and `.extra`. Packing is skipped when any required file is absent. Optional files are simply omitted when absent.

Two hashes in this format serve different purposes. The archive filename comes from Mathlib's own per-module cache hash. Separately, Mathlib expects the first 12 archive bytes to carry an LTAR-family magic plus an 8-byte little-endian Lake `depHash`; that header hash is later compared with the installed module's `.trace` `depHash` to decide whether unpacking can be skipped. The implementation explicitly warns that the header hash is not the Mathlib cache hash.

The archive paths are not universally package-location neutral. Mathlib's source notes that package-directory paths for dependencies appear inside generated `.ltar` files. During downstream extraction, Mathlib modules receive an explicit base-directory redirect to the actual Mathlib dependency directory; other modules use the archived layout directly. This is enough to reject the attractive assumption that a Mathlib `.ltar` is simply a location-free bag of build bytes, but it does not characterize the binary leantar format or prove the relocation behavior of every archive entry.

Basis: source + upstream documentation + derived synthesis. No archive was freshly produced or decoded in this investigation.

## Applicability

The findings apply exactly to Mathlib commit `5450b53e5ddc75d46418fabb605edbf36bd0beb6`, which Aeneas `nightly-2026.06.03` resolves from its Mathlib `v4.30.0-rc2` requirement. Current Anneal selects that Aeneas release.

This report uses "artifact format" to mean Mathlib's logical cache object: how one module maps to an `.ltar`, which build outputs Mathlib asks leantar to pack, which are required or optional, how the archive is named and annotated, what header field Mathlib depends on, and how package paths participate in extraction.

It does **not** specify the complete LTAR/LTR2/LTR3 binary encoding. The leantar container representation, compression scheme, path-record encoding, corruption behavior, and standalone CLI semantics are a separate backlog subject. It also does not claim that the listed build products exhaust every semantically relevant state used by Lean or Lake outside Mathlib's cache implementation.

## Findings

### One cache object corresponds to one module and is named by Mathlib's cache hash

`packCache` iterates the selected `ModuleHashMap` one module at a time. For each module, it formats that module's Mathlib cache hash with `UInt64.asLTar`, producing a `.ltar` filename in the local Mathlib cache directory. The same filename function is used by download lookup and cleanup.

The filename hash is therefore the key by which Mathlib's cache service addresses a module artifact. The complete algorithm that computes that cache hash is outside this report; it is enough here that the filename is derived from Mathlib's module hash map rather than from the later LTAR header field.

Basis: source.

### Packing has seven required build outputs and seven optional outputs

`mkBuildPaths` constructs the candidate build-file list for one module. At this revision the required entries are:

- `.lake/build/lib/lean/<Module>.trace`;
- `.lake/build/lib/lean/<Module>.olean`;
- `.lake/build/lib/lean/<Module>.olean.hash`;
- `.lake/build/lib/lean/<Module>.ilean`;
- `.lake/build/lib/lean/<Module>.ilean.hash`;
- `.lake/build/ir/<Module>.c`;
- `.lake/build/ir/<Module>.c.hash`.

The optional entries are:

- `.olean.server` and `.olean.server.hash`;
- `.olean.private` and `.olean.private.hash`;
- `.ir` and `.ir.hash` under the Lean library output directory;
- `.extra` under the Lean library output directory.

`allExist` checks only entries marked required. If any required entry is missing, `packCache` does not produce an archive for that module. Once the required set exists, the packing command filters the list by actual file existence, so absent optional entries are omitted while present optional entries are archived.

This source list is more precise than `Cache/README.md`, whose concise format description mentions `.olean`, `.ilean`, `.trace`, generated `.c`, and associated hash files but does not enumerate the server/private/IR/extra variants.

Basis: source + documentation.

### The `.trace` file is structurally privileged during packing

Mathlib requires the `.trace` path to be first in the list passed to leantar. Both `mkBuildPaths` and `packCache` carry comments enforcing that ordering. `packCache` separates the first existing path as `trace`, then invokes leantar with the archive path, that trace path, an optional comment, and the remaining build paths.

Mathlib later treats the LTAR-family header as carrying the Lake `depHash`, and its unpack-reuse check compares that header value with the installed `.trace` file's `depHash`. Taken together, these source facts show that the trace is not merely another payload member: its dependency hash participates in the archive-level reuse contract.

This report does not infer the precise leantar algorithm that copies the trace hash into the header; that belongs in the leantar-format investigation. The Mathlib side only needs and checks the resulting header contract.

Basis: source + derived.

### Mathlib distinguishes the archive filename hash from the archive header hash

`readLtarHash` reads exactly 12 bytes from an archive: four bytes of magic followed by an eight-byte little-endian integer. It accepts the magic strings `LTAR`, `LTR2`, or `LTR3`. The function's documentation calls the integer the Lake `depHash`.

`needsDecompression` receives the Mathlib cache hash only to locate `<mathlibHash>.ltar`. It then reads the header hash from that file and separately reads `depHash` from the installed module's JSON `.trace`. The function skips decompression only when those latter two values are equal. Its comment explicitly states that the compared hash comes from the LTAR file header, "not the mathlib cache hash."

A future implementation must therefore preserve this distinction. Renaming or re-keying the remote/local cache namespace is a different concern from changing the trace/header value that represents installed Lake build state.

Basis: source.

### The archive can carry a Git provenance comment

The CLI-level packing helper passes the current `git rev-parse HEAD` value to `packCache`. When a comment is present, `packCache` adds `-c git=mathlib4@<commit>` to the leantar invocation. `lookup` later runs leantar's comment-listing mode and prints the embedded comments for the selected archive.

This comment is provenance metadata; it is not the cache filename and is not the header `depHash`. The implementation does not use the comment as the unpack-reuse criterion.

Basis: source.

### Package directory paths are part of Mathlib's archive-location contract

`mkBuildPaths` first determines the package source directory that owns the module, then constructs build paths beneath that package's `.lake/build` tree. Mathlib's unpack implementation contains an explicit design note: for dependency packages, the package-directory path appears inside generated `.ltar` files.

That path sensitivity explains a special downstream extraction rule. When Mathlib itself is a dependency rather than the root package, Mathlib modules are passed to leantar with a `base` equal to the actual Mathlib dependency directory. The code comments describe this as redirecting only Mathlib files. Modules from other cached packages are passed without that Mathlib-specific base override.

The source also warns that `mkBuildPaths` assumes dependencies do not customize Lake layout settings such as `srcDir`; if such a dependency is added, the function may construct the wrong build paths and must be adjusted.

These facts establish that package layout is part of the current logical artifact contract. They do not establish that every byte inside the packed build products is itself free of absolute paths.

Basis: source + derived.

### A format-affecting packing change can require global cache invalidation

The unpack implementation warns that changing generated `.ltar` files does not automatically change Mathlib's file/cache hash. It therefore requires any such format-affecting change to be accompanied by a root-hash change that invalidates all files, for example via a relevant `lakefile.lean`, `lean-toolchain`, or manifest change. `Cache/IO.lean` also maintains an explicit `rootHashGeneration` knob for invalidating caches when existing hash inputs are insufficient.

This is an important separation of responsibilities: the cache key is intended to select a compatible archive, but not every possible change to archive construction is intrinsically represented by the per-module hash. Maintainers must couple certain archive-format changes to a root-hash invalidation.

Basis: source + derived.

## Boundaries

**No fresh archive execution or decode.** The investigation did not run `pack`, `get`, `unpack`, or `leantar`; it did not preserve a concrete `.ltar` specimen. Claims about logical contents and the first 12 bytes come from Mathlib's implementation and comments.

**Not a full leantar-format report.** Only the LTAR-family magic and 64-bit header field that Mathlib directly reads are described. Record layout after byte 12, compression, path encoding, metadata preservation, comment representation, stable-format versions, corruption recovery, and standalone `leantar` behavior remain unexamined here.

**Not a complete cache-key report.** The distinction between filename hash and header `depHash` is established, but the full Mathlib hash formula and its semantic completeness are separate work.

**No proof of byte-level portability.** The archive's logical file list and path-redirection rules do not prove that `.olean`, `.ilean`, generated C, trace, hash, or optional files are portable across host OSes, architectures, Lean builds, or relocated workspaces.

**Custom Lake layouts are a known weak point.** `mkBuildPaths` documents that dependencies using `srcDir` or related layout customization can invalidate its assumptions. This report does not survey whether any package in the pinned Mathlib dependency graph exercises those options.

**Required/optional status is Mathlib-cache policy.** A file marked optional here may still matter to another workflow. The classification means only that this `packCache` implementation will build an archive without it.

## Evidence

Evidence was acquired on 2026-09-27 from `leanprover-community/mathlib4@5450b53e5ddc75d46418fabb605edbf36bd0beb6`.

- **Archive naming — source.** `Cache/Lean.lean`, blob `0934e22f2dc396411106b008016fba4569cf741d`, lines 27–29, defines `UInt64.asLTar`.
  https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Cache/Lean.lean#L27-L29

- **Required/optional build-path list and packing invocation — source.** `Cache/IO.lean`, blob `872ffe7ce8c608f6769e3e3cc5bb5dac8f9b001a`, lines 268–351.
  https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Cache/IO.lean#L268-L351

- **Header contract and unpack reuse test — source.** `Cache/IO.lean`, lines 361–424, especially `readTraceHash`, `readLtarHash`, and `needsDecompression`.
  https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Cache/IO.lean#L361-L424

- **Dependency-path embedding and downstream base redirection — source.** `Cache/IO.lean`, lines 419–457. The comments explicitly state that dependency package-directory paths appear in leantar files and show the Mathlib-specific `base` redirection used during unpack.
  https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Cache/IO.lean#L419-L457

- **Explicit global-invalidation knob — source.** `Cache/IO.lean`, lines 110–113, `rootHashGeneration`.
  https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Cache/IO.lean#L110-L113

- **Provenance comment and lookup behavior — source.** `Cache/IO.lean`, `packCache` lines 320–351 and `lookup` lines 474–484; `Cache/Main.lean`, lines 119–125, passes the current Git commit into packing.
  https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Cache/IO.lean#L320-L351
  https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Cache/IO.lean#L474-L484
  https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Cache/Main.lean#L119-L125

- **User-facing format description — documentation.** `Cache/README.md`, blob `2c25714653f41c9c378849abb8d59f92145fd9b3`, describes `.ltar` files as carrying compiled Lean/interface/trace/generated-C outputs and associated hashes, but does not enumerate every optional variant that `mkBuildPaths` can pack.
  https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Cache/README.md

- **Selection chain — source/manifest.** Aeneas `nightly-2026.06.03` is commit `ac9f1bc5262a5e4ff1e24ca78617121382202727`; its `backends/lean/lake-manifest.json` blob `1a5af703163d8b39f4311aafe22ae171788179ee` resolves Mathlib to `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.
  https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/backends/lean/lake-manifest.json#L1-L9

## Revalidation

For another Mathlib revision, first diff `Cache/IO.lean` at four discriminating points: `mkBuildPaths`, `packCache`, `readLtarHash`/`needsDecompression`, and `unpackCache`. Then inspect `Cache/Lean.lean` for archive naming and the cache invalidation generation. A change in any of these regions can alter the logical artifact contract even if the user-facing `lake exe cache` commands remain unchanged.

The cheapest execution probe is to build one small Mathlib module at the exact target revision, run cache packing into an isolated `MATHLIB_CACHE_DIR`, and preserve the single resulting `.ltar`. Record: the archive filename, the first 12 bytes, `leantar -k` comments, and the member list. Compare that member list with `mkBuildPaths`, including at least one module for which an optional output is absent if practical.

A downstream relocation probe should unpack the same archive from a tiny project where Mathlib resides beneath `.lake/packages/mathlib`. Verify where the Mathlib module's files land and compare the archive member paths with the `base` redirection used by `unpackCache`. Run any broader relocation/portability conclusion separately; a successful one-module unpack does not establish that every cached artifact is path-neutral or cross-platform.
