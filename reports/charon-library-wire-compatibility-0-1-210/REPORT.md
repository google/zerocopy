# Charon library and serialized LLBC compatibility at 0.1.210

## Summary

At `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (0.1.210), the Rust `charon_lib` API and serialized LLBC are two interfaces over related data, not interchangeable stability boundaries.

The in-memory Rust API exposes typed AST modules, IDs, visitors, transforms, options, and the public `CrateData`/`TranslatedCrate` structures. A Rust consumer compiled against `charon_lib` can work directly with those types without serializing them. The convenience functions `deserialize_llbc` and `deserialize_llbc_with_format` read a wire file but return only `TranslatedCrate`, deliberately dropping the surrounding `CrateData` envelope after deserialization.

The wire interface serializes `CrateData`: a Charon version string, `TranslatedCrate`, and `has_errors`. Both JSON and Postcard encode the same logical envelope. Rust deserialization rejects a file whenever its embedded version string is not exactly the current crate's `CARGO_PKG_VERSION`. The pinned OCaml JSON and Postcard loaders enforce the same exact `0.1.210` equality before decoding the translated crate.

This is a deliberately conservative compatibility rule. It does not attempt structural or semver compatibility across Charon versions: a 0.1.209 file is rejected by a 0.1.210 reader even if the relevant schema happened not to change, while two builds labeled 0.1.210 pass the version gate even though the gate itself cannot prove their generated schemas are identical. Repository tooling reduces that latter risk: `CharonVersion.ml` is generated from `Cargo.toml`, and CI requires the Charon version to change when generated OCaml JSON decoder files change. That is a maintenance check, not a formal schema-versioning proof and not an independent wire-schema identifier.

Serialization also has representation choices that are not semantic item identity. By default, hash-consed values may be encoded once and later referenced by wire-local `HashConsId`s. `--no-dedup-serialized-ast` instead writes them inline. The Rust deserializer and generated OCaml readers understand both representations. Those deduplication IDs are traversal/interning artifacts, not stable identifiers for Rust/LLBC types across files or runs.

One failure-state distinction is especially important to downstream consumers. `CrateData` retains `has_errors`, but Rust's `deserialize_llbc*` convenience functions return only `.translated`. The OCaml JSON loader accepts the third envelope field but ignores it, and the Postcard loader explicitly parses the trailing Boolean into `_has_errors` and discards it. A downstream pipeline that uses these convenience loaders must therefore obtain partial-translation status elsewhere if fail-closed behavior depends on it.

No fresh serialization, round-trip, Rust, or OCaml execution was performed. The report uses exact pinned source and checked-in parser-generation/version checks.

## Applicability

This report applies to:

- repository `AeneasVerif/charon`;
- revision `a535e914f74db4fd9e6be7048f4233270d8945c0`;
- Charon package/library version `0.1.210`;
- Rust `charon_lib`, its JSON/Postcard `CrateData` serialization, and the checked-in Charon-ML readers at that revision.

"API" below means the Rust library surface compiled into a consumer. "Wire format" means serialized `CrateData` bytes exchanged through JSON or Postcard. An API type can participate in the wire schema without every public API operation being serialized.

"Compatibility" below means whether the pinned reader accepts and correctly decodes the file format it is given. It does not mean semantic equivalence of two Charon translations produced from the same Rust source at different versions.

The existing ULLBC/LLBC schema report describes the AST fields and transformations. This report focuses on interface/version/encoding boundaries.

## Findings

### `charon_lib` is a typed Rust interface, not merely a JSON parser

The library root publicly exposes AST modules, IDs, errors, name matching, options, pretty-printing, transforms, and export machinery. It re-exports the main AST families so Rust consumers can manipulate `TranslatedCrate` and its declaration types directly.

The repository manifest builds this as the `charon_lib` library. The `rustc` feature is enabled by default because some functionality hooks rustc internals, but the manifest explicitly says `--no-default-features` can compile `charon-lib` on a stable toolchain. The `charon-driver` binary remains the separate rustc-private integration component.

Thus a consumer that already has an in-memory translated crate need not pass through JSON/Postcard to use the Charon AST.

Basis: pinned Charon **source**.

### Serialized LLBC uses the `CrateData` envelope

The wire boundary is `export::CrateData`, containing:

1. `charon_version`;
2. `translated : TranslatedCrate`;
3. `has_errors`.

The same envelope is used for ULLBC and LLBC; which body representation is present follows the translation options/data, not a different top-level serialization type.

`CrateData::new` derives the version from the running `charon_lib::VERSION`, copies the translation error state into `has_errors`, and stores the translated crate.

Basis: pinned Charon **source**.

### The wire-version identifier is the Cargo package version

`charon_lib::VERSION` is `env!("CARGO_PKG_VERSION")`. At the examined commit, the package version in `charon/Cargo.toml` is `0.1.210`.

`CharonVersion::deserialize` reads the file's version string and requires exact equality with that `VERSION`. If it differs, deserialization fails with an explicit incompatible-version error.

There is no separate schema revision, feature bitmap, minimum-reader version, or semver-range negotiation in this path.

Basis: pinned Charon **source**.

### Exact equality deliberately rejects adjacent versions

The source comment states that Charon/Charon-ML currently compare versions for equality. Therefore a reader at 0.1.210 rejects 0.1.209 or 0.1.211 at the envelope gate even if a particular file would otherwise happen to fit the same structural decoder.

This behavior prevents an unsupported cross-version parse from being mistaken for a supported compatibility promise. It also means package-version inequality is a sufficient reason for rejection, not evidence that the concrete schema necessarily changed between those two releases.

Basis: pinned Charon **source** + **derived** distinction.

### The OCaml readers enforce the same version number

`charon-ml/src/CharonVersion.ml` is generated from `charon/Cargo.toml` and contains:

```text
supported_charon_version = "0.1.210"
```

The JSON loader extracts `charon_version` from the top-level object and rejects unequal versions before parsing `translated`. The Postcard loader reads the leading version string and performs the same equality check before decoding the crate.

The Rust and OCaml consumers therefore agree on the intended package-version gate at this pinned revision.

Basis: pinned Charon **source**.

### Repository automation partially couples schema changes to version bumps

The root Makefile regenerates `CharonVersion.ml` from the first `version = ...` line in `charon/Cargo.toml`.

`scripts/ci-check-version-number.sh` compares a pull request with `origin/main`. If generated OCaml `Generated_*OfJson.ml` files changed but `CharonVersion.ml` did not, CI fails and instructs the contributor to increment the Cargo version and regenerate.

This is evidence of an explicit maintenance policy: generated JSON schema/parser changes should accompany a Charon version change.

It is not a complete mechanical proof that every incompatible wire change changes the version. The check is triggered by generated OCaml JSON decoder diffs; it does not prove semantic compatibility, inspect every manual envelope reader change, or independently version Postcard. The version gate remains a project-maintained package-version convention.

Basis: pinned Charon **source** + **derived** scope of the check.

### JSON and Postcard share logical data but have different encoding constraints

`serialize_to_file` selects either Serde JSON or Postcard for the same `CrateData`. `deserialize_from_file` likewise selects one decoder based on the requested `SerializationFormat`.

The Postcard reader additionally rejects trailing bytes after one `CrateData`. The JSON and Postcard encodings should therefore be treated as two encodings of the pinned logical schema, not byte-compatible or self-interpreting formats.

The CLI/output layer chooses the format explicitly and uses different filename extensions; format discovery/selection is outside `CrateData` itself.

Basis: pinned Charon **source**.

### Charon-ML has separately generated structural decoders

The OCaml implementation does not call Rust Serde. It has generated JSON and Postcard decoders corresponding to the Rust AST.

For JSON, `OfJson.crate_of_json` handles the top-level envelope and then calls the generated `translated_crate_of_json`. For Postcard, `OfPostcard.crate_of_postcard_file` decodes fields in serialization order and delegates the translated crate to the generated decoder.

The generated code must therefore remain synchronized with Rust's serialized representation. The version-generation and CI checks exist partly to make incompatibility explicit when those generated readers change.

Basis: pinned Charon **source**.

### Default serialization can deduplicate hash-consed values

`CrateData::serialize` chooses a `HashConsDedupSerializer` unless `translated.options.no_dedup_serialized_ast` is set.

For a hash-consed value, the deduplicating representation emits the full value with a `HashConsId` the first time and may emit a `Deduplicated(id)` reference on later occurrences. Without deduplication, it emits an untagged value directly.

The purpose is to avoid exploding highly shared serialized structures. This is an encoding optimization over equal AST values, not a source-item identity system.

Basis: pinned Charon **source**.

### Deduplication IDs are wire-local reconstruction aids

The hash-cons implementation creates `HashConsId`s from a process-global interning table. Its source notes that IDs depend on insertion order. Serialization then relies on traversal order: a full value must appear before a later deduplicated reference to the same ID.

The deserializer reconstructs an ID-to-value table while reading the file. A deduplicated reference whose full value has not previously been decoded is an error.

Therefore these IDs should not be persisted externally as stable semantic keys for an LLBC type or trait reference. Their meaning is tied to one encoded traversal and the corresponding reconstruction state.

Basis: pinned Charon **source** + **derived** identity boundary.

### Readers accept both deduplicated and untagged hash-cons representations

Rust deserialization always supplies a `HashConsDedupSerializer` state "just in case." The per-value decoder accepts:

- a full tagged hash-consed value;
- a later deduplicated ID;
- an untagged inline value.

The generated OCaml decoders implement the analogous variants and maintain their own maps for decoded hash-consed values.

Accordingly, `--no-dedup-serialized-ast` changes the physical wire representation and readability/size, but the pinned readers are designed to consume either form at the same Charon version.

Basis: pinned Charon **source**.

### Rust consumers can retain or accidentally discard `has_errors`

A Rust consumer that calls `CrateData::deserialize_from_file` gets the full envelope and can inspect `has_errors`.

The library convenience functions:

```text
deserialize_llbc
deserialize_llbc_with_format
```

instead deserialize `CrateData` and immediately return only `.translated`. They do not return `has_errors`.

This makes the distinction an API choice rather than missing wire information. A fail-closed consumer should use an interface that preserves the envelope or obtain translation-completeness evidence through another verified channel.

Basis: pinned Charon **source** + **derived** consumer obligation.

### Charon-ML parses but discards `has_errors`

The pinned JSON loader accepts either the two-field historical-looking envelope or a three-field object whose third field is ignored. With current Rust serialization, that third field is `has_errors`.

The pinned Postcard loader explicitly reads the Boolean after the translated crate into `_has_errors` and then discards it.

Thus Charon-ML's `GAst.crate` loader does not expose Charon's partial-output marker to its caller at this revision. Version compatibility and translation completeness are independent properties: passing the version gate does not say `has_errors == false`.

Basis: pinned Charon **source**.

### The JSON envelope parser is intentionally more permissive about the third field's name than Rust

`OfJson.crate_of_json` pattern-matches:

- `charon_version`, `translated`; or
- `charon_version`, `translated`, and one wildcard third association.

It does not inspect the wildcard key/value.

That accommodates the current `has_errors` field while preserving compatibility with the older two-field shape accepted by this parser. It is not general forward compatibility: an additional fourth field or reordered/unrecognized generated structure need not match the hand-written parser.

Basis: pinned Charon **source**.

### The in-memory API contains behavior that cannot be recovered from a file alone

A serialized crate contains AST data. `charon_lib` also exposes code: name matching, visitors, pretty printers, transformations, constructors, interning behavior, and other methods that operate on that data.

Serializing `CrateData` does not serialize those algorithms or provide an implementation-independent specification of them. A consumer that relies on a particular Charon transformation or helper semantics is coupled to the library behavior as well as, or instead of, the wire schema.

Conversely, a consumer that exchanges LLBC files across processes can avoid direct linkage to rustc-private machinery but becomes coupled to the pinned serialized representation and decoder.

Basis: pinned Charon **source** + **derived** interface distinction.

### Alpha status limits stability claims for both interfaces

The pinned README describes Charon as alpha software, says breaking API changes are planned, and directs users to `charon-lib` for manipulating output.

Combined with the exact-version wire rejection, this does not support a claim that either the Rust API or LLBC wire format follows a long-term backwards-compatibility guarantee at 0.1.210.

The durable contract for a consumer at this pin is therefore precise-version compatibility, not adjacent-version continuity.

Basis: upstream **documentation** + pinned **source**.

## Boundaries

- No fresh JSON/Postcard serialization, round-trip, Rust consumer, Charon-ML, or cross-version execution was performed.
- The report establishes source-defined rejection/decoding rules at 0.1.210. It does not empirically test every historical or future Charon version pair.
- Exact package-version equality is a gate, not proof that two separately built artifacts labeled with the same version are byte-for-byte or semantically identical.
- The CI version-number check is not claimed to detect every possible incompatible serialized change.
- The report does not promise that JSON object field order is irrelevant to the hand-written OCaml envelope matcher in arbitrary producer implementations.
- It does not characterize compatibility of third-party decoders that do not use Charon's Rust or OCaml loaders.
- It does not treat hash-cons IDs, declaration vector indices, or item names as globally stable identities merely because they are serialized.
- It does not claim a `has_errors == false` file is semantically complete for all Rust behavior; Charon support/coverage remains a separate issue.
- It does not choose whether Anneal should link `charon_lib`, consume serialized LLBC, or use another adapter boundary.

## Evidence

Primary subject:

```text
AeneasVerif/charon
a535e914f74db4fd9e6be7048f4233270d8945c0
version 0.1.210
```

**Rust source:**

- `charon/src/lib.rs`, blob `a5530a1778d231297d8e480cf11531b141125a4f`: public modules, `VERSION`, convenience LLBC deserializers.
- `charon/src/export.rs`, blob `d5428958eb870f9f8531a8d193385c6be782338a`: `CrateData`, exact version equality, JSON/Postcard readers/writers, `has_errors`.
- `charon/src/ast/mod.rs`, blob `c9004d68f0295823a11654947e77a1fc9c525c02`: public AST module/re-export surface.
- `charon/src/ast/hash_cons.rs`, blob `5d2e55e6845f5dc16c7ffe59c2ff79f688a411fd`: interning, `HashConsId`, deduplicated/untagged serialization and reconstruction.
- `charon/Cargo.toml`, blob `8c9936202e7bdbdaaefbc19305363da1ab6c0084`: version 0.1.210, `charon_lib`, optional rustc integration feature.

**OCaml source:**

- `charon-ml/src/CharonVersion.ml`, blob `ea6a2833a3432b63eb95b1bda95dc333f60d6b4b`: generated supported version `0.1.210`.
- `charon-ml/src/OfJson.ml`, blob `a30706a384a78d51cf5a2fe566028ba3e902d0a0`: JSON envelope, exact version check, ignored third field.
- `charon-ml/src/OfPostcard.ml`, blob `3236393ad4aaac8c3ec3648cc3f38fe6f248d86b`: Postcard version check, translated-crate decode, ignored `has_errors`, EOF check.
- `charon-ml/src/generated/Generated_OfJson.ml`, blob `b82b3475b953c231e39fb63ca93bc3adb9e0aa81`: generated structural JSON decoder and hash-cons reconstruction.
- `charon-ml/src/generated/Generated_OfPostcard.ml`, blob `0dc08b558440f3e31d864263147d6d2146324774`: generated structural Postcard decoder.

**Version-maintenance source:**

- `Makefile`, blob `f30b43029e000c0ae4f6f263fb256df2cc94e369`: generation of `CharonVersion.ml` from Cargo package version and Rust/ML test coupling.
- `scripts/ci-check-version-number.sh`, blob `b19228272129de72bd0efa377a61bd8d5c7d00ea`: requires a version update when generated OCaml JSON decoders change.
- `README.md`, blob `6470a71c857dcb64be248cdb5dfe67576d914c99`: `charon-lib` consumption guidance and alpha/breaking-change status.

No evidence above is fresh **execution**.

## Revalidation

For another Charon revision:

1. record `charon/Cargo.toml` package version;
2. inspect `lib.rs::VERSION` and public deserializer return types;
3. inspect `CrateData`, its field order, and `CharonVersion::deserialize`;
4. inspect JSON/Postcard serialization selection and hash-cons state;
5. inspect Charon-ML's generated supported version and both envelope loaders;
6. inspect version-generation/CI scripts to determine what changes trigger a required bump.

On an execution-capable surface, generate one minimal LLBC file in four forms:

- JSON with default deduplication;
- JSON with `--no-dedup-serialized-ast`;
- Postcard with default deduplication;
- Postcard without deduplication.

Decode all four using both the pinned Rust consumer and Charon-ML where supported. Preserve bytes/hashes and confirm that equal semantic ASTs are recovered.

Then change only the embedded version string in a copied JSON specimen and confirm exact-version rejection. For cross-version study, generate the same fixture with the adjacent Charon revisions and test each reader/producer pair; record whether rejection occurs at the version gate or later structural decoding.

Finally, deliberately produce or preserve a Charon file with `has_errors = true` and compare:

- `CrateData::deserialize_from_file`;
- `deserialize_llbc_with_format`;
- Charon-ML JSON/Postcard loaders.

This confirms which consumer interfaces expose partial-output state. It does not prove semantic completeness of a `has_errors = false` translation.
