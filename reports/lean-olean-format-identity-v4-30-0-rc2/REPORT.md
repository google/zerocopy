# Lean 4 `.olean` format and identity at v4.30.0-rc2

## Summary

At Lean `v4.30.0-rc2`, a `.olean` is a native serialized image of Lean's `ModuleData`, not a portable logical interchange format and not a self-authenticating content-addressed module. Lean writes the exported module image as the base `.olean`; module-system builds may also write `.olean.server` and `.olean.private`, whose object graphs can share storage with earlier parts and therefore must be loaded as an ordered prefix. The payload contains declarations and persistent-environment-extension entries. Its runtime representation uses native Lean heap-object layouts and pointer-sized addresses.

The format header has a five-byte `olean` marker, structural header version `2`, encoding flags, a 33-byte Lean version string, a 40-byte Git hash, and a native `size_t` base address. The reader always checks the marker, header version, and flags. It checks the Git hash only when Lean was built with `LEAN_CHECK_OLEAN_VERSION`; the corresponding CMake option defaults to `OFF`, while Lean's release CI enables it for release builds. The stored Lean version string is not itself compared by the pinned reader.

A logical import such as `A.B.C` obtains its artifact identity from module-name-to-path resolution: Lean searches `LEAN_PATH` in order for `A/B/C.olean` and loads the first match. `ModuleData` does not contain a field naming the module whose file is being loaded, and the loader does not compare an internal module identity with the requested import name. Nor does Lean's core `.olean` loader compare the artifact against the source file's contents, timestamp, or digest. Freshness and build invalidation are therefore responsibilities of the surrounding build system, such as Lake, rather than properties established by the `.olean` loader itself.

For Anneal, the safe reuse rule is consequently stronger than “same `.olean` extension” or even “same displayed Lean version.” Reuse should bind to the exact Lean toolchain/build configuration and the build-system dependency state that produced the artifact. A release build's Git-hash check is a useful guard against cross-commit reuse, but it is not a source-freshness check and does not replace Lake's dependency/invalidation model.

Basis: exact pinned implementation source and same-revision upstream build documentation. No fresh Lean executable was run for this report.

## Applicability

The subject is `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, tagged `v4.30.0-rc2`, which is the Lean revision selected by the Anneal dependency state examined by the surrounding reference effort. Claims about the file header, serialization, import lookup, module-part structure, compatibility checks, and release-build configuration are limited to that revision unless a later revision is separately checked.

The report distinguishes three related notions that are easy to conflate:

1. **Logical module selection.** An import name is mapped through `LEAN_PATH` to a filesystem path such as `A/B/C.olean`.
2. **On-disk format compatibility.** The `.olean` reader checks a small header and then reconstructs a native Lean object graph.
3. **Build freshness or cache identity.** A build system decides whether a previously produced artifact still corresponds to the current source, options, dependencies, toolchain, and other inputs.

This report covers the first two directly and records the boundary to the third. Lake's trace/hash and invalidation behavior is a separate subject in the reference corpus; this report does not duplicate that machinery or treat `.olean` loading as an alternative to it.

The `CHECK_OLEAN_VERSION` distinction is configuration-sensitive. At this revision, `src/CMakeLists.txt` declares the option with default `OFF`. The same-revision release workflow adds `-DCHECK_OLEAN_VERSION=ON` for release jobs, which defines `LEAN_CHECK_OLEAN_VERSION` and causes the reader to reject a mismatched embedded Git hash. This establishes the behavior of source builds configured either way and of the checked-in release workflow. This investigation did not download and inspect the exact binary archive installed in Anneal's execution environment, so it does not independently prove which build flags a particular local executable has.

The binary payload is architecture/runtime sensitive. The header itself contains a native `size_t`, and the compacted payload is made from Lean runtime object layouts and pointer-like offsets. The source does not define a cross-endian or cross-word-size portable interchange contract. This report therefore does not generalize an artifact produced for one native ABI to another.

## Findings

### The file is a compacted `ModuleData` object graph

Lean describes `ModuleData` as the content of a `.olean` file and states that `compact.cpp` generates its disk image. At this revision the structure contains:

- whether the producer participated in the module system;
- direct imports;
- `constNames`, a redundant list used to speed import;
- serialized `ConstantInfo` declarations;
- extra constant names used by generated code; and
- persistent environment-extension entries keyed by extension name.

The surrounding `Environment` has substantially more process-local state than `ModuleData`. The `.olean` does not serialize an arbitrary live `Environment`; `mkModuleData` selects declarations and persistent extension entries appropriate for the requested export level and materializes a smaller module image.

That distinction matters for identity. `ModuleData` contains the imported dependency list and the declarations/extensions exported by the module, but it has no `mainModule` or equivalent self-name field. The writer receives the logical module name separately, and the loader receives the requested import name separately. The payload therefore does not authenticate “I am module `A.B.C`.”

Basis: source — `src/Lean/Environment.lean`, `ModuleData`, `mkModuleData`.

### Module-system builds use an ordered three-part `.olean` family

The module system defines three ordered `OLeanLevel`s:

- `exported` — public/exported information;
- `server` — information additionally useful to the language server; and
- `private` — complete private module data.

The convention is cumulative: each later level includes the information of previous levels. `OLeanLevel.adjustFileName` maps them to:

- base `.olean` for `exported`;
- `.olean.server` for `server`;
- `.olean.private` for `private`.

`writeModule` computes persistent-extension output once and calls `saveModuleDataParts` with those three parts. The lower-level constants are explicitly re-sorted after filtering so that exported `.olean` output does not accidentally depend on private-only constants. If IR emission is enabled, `.ir` is a separate compacted artifact with a deliberately different logical module name for base-address derivation.

The parts are not three independent serializations. `saveModuleDataParts` uses one compactor across them, and its API documentation states that objects shared with earlier parts are not duplicated. Consequently, a later part can depend on storage from earlier parts. `readModuleDataParts` must be given a prefix of the files produced by one `saveModuleDataParts` call. `findOLeanParts` therefore starts with the base `.olean`, adds `.server` if present, and only then adds `.private` if present.

This means `.olean.private` should not be copied, cached, or interpreted as a standalone module image detached from its matching preceding parts. The natural unit for a full private module artifact is the coherent ordered family produced together.

Basis: source — `src/Lean/Environment.lean`, `OLeanLevel`, `saveModuleDataParts`, `writeModule`, `findOLeanParts`.

### The header is small; most compatibility is implicit in the native object image

`src/library/module.cpp` defines the on-disk `olean_header`. At the pinned revision it consists of:

- five bytes: marker `olean`;
- one byte: header version, currently `2`;
- one byte: flags, with bit 0 identifying whether persisted bignums use GMP;
- 33 bytes: a Lean version string;
- 40 bytes: build Git hash;
- one native `size_t`: desired mapping base address; and
- the compacted payload, aligned as Lean objects require.

The source asserts that the header has no padding. Its byte size is therefore `80 + sizeof(size_t)`: 88 bytes on a 64-bit build and 84 bytes on a 32-bit build. The use of native `size_t` is itself part of the compatibility envelope.

The payload is not a field-by-field external schema. `object_compactor` copies Lean runtime objects into a contiguous region, replacing references with addresses relative to a deterministic base. On load, `compacted_region::read` either uses the memory mapping directly when it landed at the encoded base address or walks the copied region and fixes object pointers. The implementation includes object-type-specific relocation logic for constructors, arrays, thunks, refs, tasks, promises, and bignums.

The format is therefore coupled to Lean runtime object representation. A structural change can be incompatible even if a high-level declaration still “means the same thing.” Same-revision upstream developer documentation makes this explicit: downstream reuse is safe only when the build is “close enough” to have a compatible `.olean` format **including the structure of all relevant environment extensions**.

Basis: source + documentation — `src/library/module.cpp`, `src/runtime/compact.cpp`, `doc/dev/index.md`.

### Base addresses are derived from the module name for mmap efficiency, not module authentication

When saving parts, Lean hashes the separately supplied module `Name` to derive a deterministic candidate virtual base address, constrains it to the lower x86-64 userspace range, and aligns it to 64 KiB. Each part records the corresponding base address in its header. The goal is to make it likely that the file can be mapped read-only at the address already encoded into its object references.

If every requested part can be mapped at its encoded address, the object graph can be used without pointer relocation. If any part cannot be mapped there, the loader abandons that mmap strategy for all parts, copies them into one large allocation preserving their inter-part offsets, and fixes references while reading.

The encoded base address should therefore not be mistaken for a cryptographic or semantic module identifier. It is a deterministic placement hint derived from the producer's module name. The reader accepts the header's address; it does not recompute the base from the import name and compare the result. In particular, the reader has no explicit format-level check that a file found as `A/B/C.olean` was originally written under the logical module name `A.B.C`.

Derived consequence: renaming or misplacing an otherwise loadable `.olean` is not rejected by a self-name check, because there is no serialized self-name to compare. Other contents can still make such misuse fail later — for example, declarations may collide or imports may be inconsistent — but module-name/path agreement is not authenticated by the `.olean` format itself.

Basis: source + derived — `src/library/module.cpp` writer/reader; `ModuleData` in `src/Lean/Environment.lean`.

### Header acceptance depends on build configuration

The pinned reader first verifies that it can read a full header and that the five-byte marker matches. It then checks:

- `header.version == 2`;
- `header.flags` exactly match the current build's flags; and
- **only when `LEAN_CHECK_OLEAN_VERSION` is compiled in**, the 40-byte Git hash equals the current build's `LEAN_GITHASH`.

The 33-byte `lean_version` field is written but is not part of the reader's compatibility predicate at this revision. Therefore the displayed version string does not itself enforce compatibility.

`src/CMakeLists.txt` defines `CHECK_OLEAN_VERSION` as “Only load .olean files compiled with the current version of Lean” and defaults it to `OFF`. Turning it on forces Git-hash embedding and defines `LEAN_CHECK_OLEAN_VERSION`. The top-level CMake configuration forwards this option between bootstrapping stages because it changes `.olean` compatibility.

The checked-in release workflow enables `CHECK_OLEAN_VERSION=ON` for release configurations and explains why: it embeds the Git hash into the stage-1 library and prohibits reusing `.olean`s across commits. Fast non-release CI deliberately does not enable this because doing so would prevent reuse from a broader cache.

Thus there are two materially different compatibility regimes:

- **with Git-hash checking:** the reader rejects `.olean`s stamped by another Lean commit, in addition to version/flag checks;
- **without Git-hash checking:** distinct Lean commits can pass the header check if header version and flags match, even though higher-level object or extension representation might have changed.

The second case does not imply cross-commit semantic compatibility. It means only that the small header predicate did not reject the file.

Basis: source — `src/library/module.cpp`, `src/CMakeLists.txt`, top-level `CMakeLists.txt`, `.github/workflows/build-template.yml`.

### The header version is not the Lean language version

The header's one-byte `version` is documented as changing on structural changes to the **header**. The pinned reader requires exactly `2`. This is different from the 33-byte Lean version string and different again from the optional Git-hash equality check.

Consequently, “same `.olean` version” is ambiguous unless the speaker identifies which version they mean. At this revision:

- the file-header layout version is `2`;
- the file stores a human-facing Lean version string such as `4.30.0-rc2`;
- a release-style build may additionally require exact producer/consumer Git-hash equality; and
- actual payload compatibility also depends on the runtime object graph and persistent extension representations.

Upstream bootstrapping documentation reinforces that the payload format can change in ways that make a compiler unable to load a library generated by a previous stage. When that happens, Lean's staged build moves to a stage in which producer and consumer agree on the new format.

Basis: source + documentation — `src/library/module.cpp`, `doc/dev/bootstrap.md`.

### Persistent environment extensions are part of the compatibility contract

A `ModuleData` stores an array of `(extension name, serialized entries)` pairs. Persistent extensions decide what to export at each `.olean` level through `OLeanEntries`. During import, Lean constructs a mapping from currently registered extension names to extension indices and installs imported entries for matching extensions. Import initialization can register additional user-defined persistent extensions, after which Lean refreshes the imported-entry arrays.

This organization makes extension names explicit, but it does not add an independent schema version to each extension's serialized Lean value. Compatibility therefore depends on the consumer registering an extension under the expected name with a representation capable of interpreting the stored values. The upstream developer guide's warning about “structure of all relevant environment extensions” is an important part of the actual reuse rule.

For Anneal, this means that a `.olean` artifact cannot be safely identified only by the core Lean executable version while ignoring metaprogramming libraries that define persistent extensions. If a dependency changes an extension's representation while the low-level header remains acceptable, the format-level header has not established compatibility.

Basis: source + documentation — `src/Lean/Environment.lean` persistent-extension machinery; `doc/dev/index.md`.

### Logical module identity comes from search-path resolution

`Lean.Util.Path` documents the lookup rule directly. `LEAN_PATH` is an ordered list of roots. An import `A.B.C` resolves to `path/A/B/C.olean`; `import A` resolves to `path/A.olean`. `findOLean` returns the first candidate selected by the search path or reports an unknown module prefix.

The import machinery then records the loaded module under the `Import.module` name that caused that lookup. Because the payload has no self-name, the stable logical identity exposed by the loader is therefore the requested `Name` plus the search-path resolution that selects a concrete file.

Two consequences are useful for build and agent tooling:

1. Absolute artifact paths are not the semantic module names used by Lean source. Moving a coherent library tree can preserve logical import names if `LEAN_PATH` is updated consistently.
2. Search-path order matters. Two roots containing the same logical module path are not interchangeable merely because both have a file with the same relative name; Lean selects the first matching root.

This report does not claim that changing absolute paths is always harmless to an entire Lean/Lake workspace. Other generated files can embed paths, and that is covered by the separate path-embedding investigation. The narrower claim here is about core `.olean` lookup.

Basis: source — `src/Lean/Util/Path.lean`, `findOLean`; `src/Lean/Environment.lean`, `importModulesCore`.

### Core `.olean` loading is not source-freshness validation

Neither `olean_header` nor `ModuleData` contains a source-file digest, source modification time, or an explicit hash of all transitive build inputs. `findOLean` resolves the artifact by module name and path. `readModuleDataParts` checks the binary header and reconstructs the payload. These functions do not open the corresponding `.lean` source and compare it against the compiled module.

Therefore successful import means, roughly, “a file was found and accepted as a compatible serialized module image.” It does **not** mean “this image was freshly built from the current source tree and dependency state.” That stronger fact must be established by build orchestration and its recorded dependency hashes/traces.

For an Anneal cache or durable proof result, this distinction should be explicit. A raw `.olean` path is not enough evidence of source identity. A robust identity should include at least the exact Lean toolchain/build, the logical module/build target, and the build-system inputs or artifact digest that establish how these bytes relate to the source being verified.

Basis: source + derived — header and module-data fields, path lookup, reader behavior. The broader Lake identity mechanism is intentionally outside this report.

### Serialization contains local determinism measures but this report does not establish whole-file reproducibility

Several implementation details are clearly intended to make serialized output stable:

- lower-level exported constants are re-sorted so their order does not depend on private-only constants;
- the object compactor performs maximal sharing of byte-identical objects;
- non-GMP bignums are copied field-by-field into zeroed storage specifically because copying C++ padding bytes would create nondeterministic output; and
- the module-name-derived mmap base is deterministic.

These details are evidence that byte stability matters to the implementation. They are not a proof that two clean compilations of the same source necessarily produce byte-identical `.olean` files under every supported configuration. The broader compilation-determinism question requires its own experiment or audit and remains outside this report.

Basis: source — `src/Lean/Environment.lean`, `src/runtime/compact.cpp`, `src/library/module.cpp`.

### Writes avoid exposing partially written or currently mapped output files

`lean_save_module_data_parts` writes each part to a process-specific temporary filename and only renames the completed file into place after serialization. The source comment states the purpose: do not expose partially written files and do not modify a possibly memory-mapped existing file in place. On Windows the replacement path includes special handling so mapped files can be marked for deletion using POSIX-style semantics when available.

This is an important concurrency property of artifact replacement: readers should observe either the previous complete file or the newly renamed complete file, rather than a partially serialized `.olean`. It does not by itself serialize competing writers or provide a transaction across the entire family plus unrelated Lake metadata; callers still need build-level coordination.

Basis: source — `src/library/module.cpp`, `lean_save_module_data_parts`.

## Boundaries

- **No fresh execution.** This investigation did not compile a sample Lean module, hex-dump an emitted file, test a renamed artifact, or attempt cross-version/cross-architecture loading. The format and loader claims above come directly from exact pinned implementation source and checked-in documentation. Source-derived consequences are labeled as such.
- **Exact installed archive not inspected.** The same-revision release workflow enables Git-hash checking for release jobs, but this report did not independently hash or inspect the exact Lean executable/archive installed by Anneal. Code that depends on the presence of `LEAN_CHECK_OLEAN_VERSION` should verify the concrete toolchain or conservatively bind its own cache identity to the exact toolchain artifact.
- **No claim of cross-architecture portability.** The native `size_t` header field and native Lean object image give no basis for such a claim. This report also did not characterize every target ABI on which Lean can be built.
- **No whole-file determinism result.** Local stabilization mechanisms are documented, but repeat-build byte identity is a separate question.
- **No Lake freshness model here.** The fact that Lean core does not perform source freshness checks should not be read as a statement that normal `lake build` fails to invalidate stale modules. Lake maintains its own dependency traces/hashes; those are a separate layer.
- **No guarantee from header acceptance alone.** When Git-hash checking is disabled, passing marker/version/flag checks does not establish that two different Lean commits or extension sets are semantically compatible.
- **No stable external serialization API claim.** The implementation exposes Lean/C++ functions used by Lean itself, but this report does not treat the raw `.olean` bytes as a documented third-party protocol with forward/backward compatibility guarantees.
- **No claim that misnaming always succeeds.** The absence of a self-name check establishes only that the format reader does not directly reject a path/name mismatch on that basis. Other declarations, imports, initialization behavior, or build tooling can still cause failure.

## Evidence

All Lean source below is from `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` and was inspected on 2026-09-27.

- `src/library/module.cpp`, blob `97a53f87b06595049cdfe6016ec2c66fd40748b6`, especially:
  - `olean_header` at lines 77-101;
  - `lean_save_module_data_parts` at lines 107-197;
  - `lean_read_module_data_parts` at lines 209-366.
  - Immutable source: <https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/library/module.cpp#L77-L366>
- `src/Lean/Environment.lean`, blob `8a485808c7b0e4c32959740efa012a37610b6914`, especially:
  - `ModuleData` at lines 124-145;
  - `OLeanLevel` and `OLeanEntries` beginning at line 1531;
  - `saveModuleDataParts`/`readModuleDataParts` at lines 1747-1760;
  - filename levels and serialization at lines 1787-1881;
  - `findOLeanParts`/`importModulesCore` beginning at lines 2038-2053.
  - Immutable source: <https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Environment.lean#L124-L145>
  - Immutable source: <https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Environment.lean#L1531-L1564>
  - Immutable source: <https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Environment.lean#L1747-L1881>
  - Immutable source: <https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Environment.lean#L2038-L2145>
- `src/Lean/Util/Path.lean`, blob `b2af1878ec01bcf790f31401c0d46efd6b94c840`, module lookup documentation and `findOLean` around lines 1-14 and 116-128.
  - Immutable source: <https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Util/Path.lean#L1-L14>
  - Immutable source: <https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Util/Path.lean#L116-L128>
- `src/runtime/compact.cpp`, blob `c8bf24aa8206bc99cddde2fda2e4e2212b8a75b0`, object compaction and relocation:
  - base-address-aware compactor around lines 60-110;
  - deterministic non-GMP bignum serialization around lines 289-304;
  - region relocation at lines 387-505.
  - Immutable source: <https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/runtime/compact.cpp#L60-L110>
  - Immutable source: <https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/runtime/compact.cpp#L289-L304>
  - Immutable source: <https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/runtime/compact.cpp#L387-L505>
- `src/CMakeLists.txt`, blob `514b0540caa7adfef5e7c43b0da9b681cd9fc70d`, `CHECK_OLEAN_VERSION` default and `LEAN_CHECK_OLEAN_VERSION` definition at lines 114 and 153-156.
  - Immutable source: <https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/CMakeLists.txt#L108-L156>
- top-level `CMakeLists.txt`, blob `3fa41c0cbc265ae4fba770b84d477b63372fa0af`, forwards `CHECK_OLEAN_VERSION` as a setting that generates incompatible `.olean` format.
  - Immutable source: <https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/CMakeLists.txt#L14-L31>
- `.github/workflows/build-template.yml`, blob `fe6dfaa6de25279007102bb479d1daa9a8d2edaf`, release configuration enables `-DCHECK_OLEAN_VERSION=ON` and explains the cross-commit reuse boundary.
  - Immutable source: <https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/.github/workflows/build-template.yml>
- `doc/dev/bootstrap.md`, blob `0cc10355202d84f48666d7063ca87b0451beb03a`, lines around 46 explain that an `.olean` format change can make a stage-1 compiler unable to load the stdlib produced by stage 0.
  - Immutable source: <https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/doc/dev/bootstrap.md#L37-L58>
- `doc/dev/index.md`, blob `416271addadfddbd5424defae555aa5283d05bf8`, lines around 107 state that downstream modules can sometimes be reused with a nearby Lean build only when the `.olean` format, including relevant environment-extension structure, is compatible.
  - Immutable source: <https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/doc/dev/index.md#L101-L119>
- `src/Lean/Elab/Frontend.lean`, blob `fd3760667db96a351b4f654720193c89bbee356e`, shows successful frontend processing calling `writeModule` for `.olean` output and writing `.ilean` separately as JSON.
  - Immutable source: <https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Elab/Frontend.lean>

The current `google/zerocopy` Anneal redesign was separately observed at main commit `41f5b37afe7060fd9fe08c00b200672cd76d77b9`; the exact Lean subject identity above comes from the already reconstructed Anneal dependency state used by this reference program. This report's technical claims are about the pinned Lean source, not about moving Lean `master`.

## Revalidation

For another Lean revision, the cheapest reliable source revalidation is narrow:

1. Inspect `src/library/module.cpp` and compare `olean_header`, writer initialization, and reader compatibility predicate. Record any marker/header-version/flag/hash changes.
2. Inspect `src/Lean/Environment.lean` for `ModuleData`, `OLeanLevel`, `saveModuleDataParts`, `writeModule`, `findOLeanParts`, and the import-level lattice. Confirm whether parts still share storage and whether a self-module identity has been added.
3. Inspect `src/Lean/Util/Path.lean` to confirm module-name-to-path lookup and search-path precedence.
4. Inspect `src/runtime/compact.cpp` if the payload is still a compacted native object graph; changes there can alter runtime/ABI compatibility without obvious changes to `ModuleData`.
5. Inspect `src/CMakeLists.txt` and the release workflow for `CHECK_OLEAN_VERSION`. Do not infer that an arbitrary binary was built with the source default or with release CI flags; verify its provenance when the distinction matters.
6. Check upstream developer documentation for any changed compatibility statement about `.olean` and persistent environment extensions.

A small execution probe can cheaply test the source-derived boundaries when a runnable toolchain is available:

- compile one tiny module to `.olean` and inspect the first `80 + sizeof(size_t)` bytes;
- copy the artifact under a different module path and test whether core Lean rejects it specifically for self-name mismatch;
- rebuild the same source twice to test byte identity separately from semantic importability;
- attempt import with a known different-commit compiler built with and without `CHECK_OLEAN_VERSION`; and
- if testing multipart modules, move only `.olean.private` versus the complete prefix to confirm the dependency among parts.

Those probes should be treated as targeted confirmation, not as substitutes for reading the compatibility predicate. In particular, one successful cross-version import does not establish general forward/backward compatibility.