# Charon serialization compatibility and `charon_lib` boundary at 0.1.210

## Summary

At `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (0.1.210), serialized ULLBC and LLBC are deliberately version-gated rather than advertised as a generally forward- or backward-compatible wire protocol. Both representations use the same top-level `CrateData` envelope. It contains Charon's package version, the `TranslatedCrate`, and a `has_errors` bit. The Rust JSON/Postcard reader and the generated OCaml readers reject a file whose embedded Charon version differs from the reader's supported version by exact string equality.

The version is Charon's Cargo package version: `charon_lib::VERSION` is `CARGO_PKG_VERSION`, and the OCaml `CharonVersion.ml` file is generated from `charon/Cargo.toml`. Charon's repository guidance gives that patch number a specific serialization role: any AST change must bump the patch version, then the generated OCaml types/parsers are regenerated. Two immediately preceding AST-changing commits demonstrate the policy in practice: adding `WithRetag` changed 0.1.208 to 0.1.209, and adding `TypeId` changed 0.1.209 to 0.1.210 while updating generated JSON/Postcard readers. This is strong repository policy and history, not a mechanical theorem that every future incompatible change will be versioned correctly.

The package version is also not a commit identity. Charon's nightly release workflow creates date tags without modifying `Cargo.toml`. Aeneas's pinned Charon `a535e914…` and Charon's own `nightly-2026.06.03` revision `0c91ca1…` are 15 commits apart yet both report 0.1.210. At those two exact revisions, `Cargo.toml`, `export.rs`, `lib.rs`, the OCaml JSON reader, and generated supported-version file are byte-identical. Same-version revisions can therefore exist, and a nightly tag cannot be substituted for the embedded serialization version.

`charon_lib` is a different compatibility surface from a serialized LLBC file. The Rust library exposes the in-memory AST, export envelope, options, name matching, pretty-printing, and transformation modules directly. `deserialize_llbc` and `deserialize_llbc_with_format` are convenience functions that read the versioned `CrateData` and return only its `TranslatedCrate`; callers that need `has_errors` or the envelope version must use the public `export::CrateData` reader instead. A Rust library consumer is coupled at compile time to the selected Charon source/API, while a file consumer is coupled at run time by the embedded package-version check plus the concrete JSON/Postcard schema.

Neither boundary is documented as a stable long-term API. The serialization comment says `CrateData` should be “as stable as possible,” but the reader intentionally rejects every different package version even when the structures might happen to remain parseable. The repository's AST-version policy protects the serialized boundary conservatively. It does not separately promise semantic-version compatibility for all public Rust APIs: for example, the commit that made `charon-lib` buildable on stable changed Cargo feature/API integration without changing the package version.

No fresh Charon execution or cross-version parsing was performed. The report uses exact source, generated readers, repository policy, release automation, and immutable history. A future cross-version execution probe remains useful for detecting accidental same-version schema drift, but it is not needed to establish the source-defined exact-version gate.

## Applicability

Primary subject:

- repository: `AeneasVerif/charon`;
- revision: `a535e914f74db4fd9e6be7048f4233270d8945c0`;
- package version: `0.1.210`;
- this is the Charon revision pinned by Aeneas release `nightly-2026.06.03` and therefore the runtime Charon selected by the current Anneal toolchain.

Comparison subject:

- repository: `AeneasVerif/charon`;
- revision: `0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`;
- tag: `nightly-2026.06.03`;
- package version: `0.1.210`.

The comparison revision is used only to establish that Charon's package/serialization version can remain constant across distinct commits/nightly release state. Existing corpus research establishes that it is 15 commits ahead of the Aeneas-pinned revision and that the examined serialization surface is identical across those two commits.

“Compatibility” in this report has three separate meanings:

1. **wire acceptance** — whether a reader accepts serialized bytes;
2. **schema compatibility** — whether producer and consumer agree on the serialized representation;
3. **semantic compatibility** — whether the accepted representation means the same thing for the downstream property being proved.

An exact version match is a source-defined prerequisite for Charon's readers. It is not by itself a proof of semantic compatibility.

## Findings

### ULLBC and LLBC share one versioned `CrateData` envelope

`charon/src/export.rs` defines `CrateData` for both ULLBC and LLBC. The envelope contains:

- `charon_version: CharonVersion`;
- `translated: TranslatedCrate`;
- `has_errors: bool`.

`TranslatedCrate` carries the representation-specific bodies and the rest of the crate-level AST. The envelope therefore versions a whole translated crate rather than one function or one body.

The `has_errors` bit is semantically relevant to consumers: it says the serialized description is partial because translation encountered errors. A successfully parsed file is not automatically a complete extraction.

Basis: pinned Charon **source**.

### Rust deserialization rejects every different Charon package version

`CharonVersion` has a custom `Deserialize` implementation. It reads the producer's version string and compares it with `crate::VERSION`; any inequality produces an “Incompatible version of charon” deserialization error.

`crate::VERSION` is defined in `lib.rs` as `env!("CARGO_PKG_VERSION")`. At the pinned revision, `charon/Cargo.toml` sets that version to `0.1.210`.

The Rust reader therefore has no compatibility range, major/minor rule, feature negotiation, migration table, or “try parsing anyway” fallback. Its declared rule is exact package-version equality.

Basis: pinned Charon **source**.

### The generated OCaml readers enforce the same exact version equality

`charon-ml/src/CharonVersion.ml` is generated from `charon/Cargo.toml` and records `supported_charon_version = "0.1.210"` at the pinned revision.

The JSON `crate_of_json` reader first extracts `charon_version` and compares it to that generated constant before converting the translated crate. The Postcard reader likewise reads the version first and returns an incompatibility error if it differs.

Aeneas's OCaml-facing Charon consumer is therefore not relying on a looser independent compatibility convention. The Rust producer and generated OCaml consumer share the same package-version epoch.

Basis: pinned Charon generated **source**.

### Exact version equality is deliberately conservative

The source comment on `CrateData` says the serialized representation must be “as stable as possible,” while the version-field comment immediately states that compatibility is currently decided by equality.

Those two facts should not be conflated. “Stable as possible” is a maintenance objective; exact equality is the implemented acceptance rule. If Charon 0.1.211 happened to retain a byte-compatible schema, a 0.1.210 reader would still reject its files solely because the version differs.

Conversely, an equal version does not mechanically prove semantic compatibility. It says the producer and consumer are inside the same maintainer-declared format epoch; correctness still depends on the versioning discipline having been followed and on the meanings of the represented constructs.

Basis: pinned Charon **source** + **derived** compatibility distinction.

### Charon policy requires an AST version bump for every AST change

The repository's `AGENTS.md` has an explicit Versioning rule:

> Any change to the AST must come with a version bump to make the deserializers emit nice errors.

It instructs maintainers to bump the patch version in `Cargo.toml` and run the test/generation workflow so the generated OCaml side follows the change.

This is the clearest available statement of what the package patch number is intended to track for serialized LLBC: AST compatibility, not merely release chronology.

The rule is maintainer policy, not a compiler-enforced invariant. The report therefore treats it as **documentation**, supported by history, rather than claiming that equal versions mathematically guarantee equal schemas.

Basis: upstream **documentation** in pinned repository guidance.

### Adjacent AST-changing commits demonstrate the versioning policy

Immutable history immediately preceding 0.1.210 shows the policy in use.

Commit `65dcdb566e05472a6bca8074318c05f729e30177` adds `WithRetag` to `Rvalue::Use`. The same commit changes the package and generated OCaml supported version from 0.1.208 to 0.1.209 and changes the generated JSON/Postcard readers to consume the new field.

Commit `89e2529761404c02ab5a4d0a61a483853e4ee9e6` adds `ConstantExprKind::TypeId`. The same commit changes 0.1.209 to 0.1.210 and updates the generated JSON/Postcard variant decoders; the Postcard enum tags after the insertion move accordingly.

These examples matter because they show the version bump guarding real wire-shape changes rather than being a cosmetic release number. They still do not prove that every historical or future AST change followed the rule.

Basis: immutable Charon **source history**.

### Nightly release tags do not define the serialization version

The pinned release workflow runs nightly, constructs a tag named `nightly-YYYY.MM.DD`, creates a prerelease, builds the checked-out Charon binaries, and uploads them. It does not edit or increment `charon/Cargo.toml` before tagging.

Thus date-tag identity and serialized-format identity are different coordinates. A new nightly may retain the same package version when no AST change requires a bump.

This is visible in the Anneal-era subjects: `a535e914…` and `0c91ca1…` are distinct Charon revisions but both use package version 0.1.210. The five examined files that define the Rust/OCaml serialization API are byte-identical between them:

- `charon/Cargo.toml`;
- `charon/src/export.rs`;
- `charon/src/lib.rs`;
- `charon-ml/src/OfJson.ml`;
- `charon-ml/src/CharonVersion.ml`.

A compatibility record should therefore retain both the immutable commit and Charon package version. The nightly tag alone is insufficient.

Basis: release-workflow **source** + exact-blob comparison **source**.

### JSON and Postcard carry the same logical envelope but have different wire properties

`CrateData::serialize_to_file` supports JSON and Postcard. `deserialize_from_file` selects the matching parser.

For JSON, Charon uses Serde's named representation, disables the JSON recursion limit, and grows the parsing stack as needed. The generated OCaml side contains explicit constructors/field parsers derived from the Rust AST.

For Postcard, Charon serializes the same Rust data model into a compact positional/binary representation. The Rust reader rejects trailing bytes after one `CrateData`. The generated OCaml Postcard parser likewise follows the generated field and enum order. AST changes such as adding `TypeId` can shift Postcard enum tags, as the 0.1.210 history demonstrates.

The package-version gate is common to both encodings. Postcard should therefore not be treated as a separately versioned stable binary ABI, and JSON should not be treated as version-independent merely because it uses field names.

Basis: pinned Charon **source** + immutable version-bump **history**.

### Serialization can hash-cons repeated AST values without changing the semantic API

`CrateData::serialize` normally uses `HashConsDedupSerializer`; `--no-dedup-serialized-ast` disables that stateful deduplication. The generated readers reconstruct the referenced values.

This means the wire representation contains serialization machinery beyond a naive direct JSON rendering of each Rust struct. Consumers should use Charon's generated/native readers rather than infer a stable hand-authored JSON schema from a few specimens.

The in-memory `TranslatedCrate` API is above this deduplication detail: after deserialization, callers operate on the reconstructed AST values.

Basis: pinned Charon **source**.

### `charon_lib` exposes a native Rust AST/API, not only a JSON parser

`charon/src/lib.rs` publicly exposes modules for IDs, ASTs, errors, export, name matching, options, pretty-printing, and transformations. It re-exports major AST modules and types for the older import structure.

A linked Rust consumer can therefore:

- work directly with `TranslatedCrate` and the Rust AST types;
- inspect or construct names, types, expressions, ULLBC/LLBC bodies, and metadata;
- use public transform/pretty-print/export infrastructure;
- deserialize JSON or Postcard through Charon's native reader.

That is a materially richer boundary than “consume serialized JSON.” It also couples the consumer directly to Charon's Rust source-level type/API surface.

Basis: pinned `charon_lib` **source**.

### The convenience deserializer discards envelope metadata

`charon_lib::deserialize_llbc(path)` assumes JSON. `deserialize_llbc_with_format(path, format)` supports JSON or Postcard. Both call `CrateData::deserialize_from_file` and then return only `.translated`.

As a result, a caller using only those helpers does not receive the envelope's `has_errors` field or the `CharonVersion` value. Version mismatch is still enforced during parsing, but the successfully parsed metadata is discarded by the convenience API.

A consumer that must distinguish complete from partial Charon output should deserialize the public `export::CrateData` itself rather than infer completeness from successful parsing or from `TranslatedCrate` alone.

Basis: pinned Charon **source**.

### Rust-library compatibility and file compatibility fail at different boundaries

A Rust consumer of `charon_lib` compiles against the concrete Rust definitions selected by Cargo. An incompatible source API normally manifests as a build/type error, or as changed behavior if the source API remains type-compatible but its semantics change.

A serialized consumer can be built and run separately from the producer. Its first declared compatibility check is the embedded package version, followed by decoding the concrete JSON/Postcard schema into that consumer's data model.

These are not interchangeable guarantees. Linking `charon_lib` from commit B does not automatically prove it can consume serialized output from Charon commit A; the file path still passes through the version/schema rules. Likewise, successful file parsing does not promise that every public Rust helper or transform API from the producer exists in the consumer.

Basis: pinned Charon **source** + **derived** boundary comparison.

### The package patch version is not a complete semantic-version contract for `charon_lib`

The repository guidance ties version bumps specifically to AST changes so deserializers can reject incompatible files. It does not state that every public Rust API change requires a package-version bump.

Commit `b028e082c417eda7cf419e9661ad9fff047ac1ac` illustrates the distinction. It changes the library's Cargo feature/build interface so `charon-lib` can compile on stable with `--no-default-features`, but the diff contains no package-version increment.

Thus 0.1.210 should be treated as an important serialized-AST compatibility coordinate, not as sufficient evidence that every `charon_lib` public API is frozen throughout all commits carrying that version.

Basis: upstream versioning **documentation** + immutable **source history**.

### Same-version source equality is useful evidence, but not a universal compatibility theorem

For `a535e914…` and `0c91ca1…`, the package version and the examined serializer/library entry-point blobs are identical. That is strong evidence that this particular declared interface did not change between those two commits.

It does not establish that every generated output is semantically identical. Other translation code changed between the commits, so two producers with the same serialized schema can emit different AST content for the same Rust source while remaining format-compatible.

This distinction is important for Anneal: wire compatibility answers whether an artifact can be read; semantic adequacy answers whether the artifact supports the Rust-level claim being made.

Basis: exact **source** comparison + **derived** distinction.

## Boundaries

- No fresh Charon, Rust, OCaml, JSON, Postcard, or cross-version execution was performed.
- The report establishes the source-defined exact-version gate and versioning policy. It does not empirically test every pair of same-version or adjacent-version commits.
- The repository's “any AST change must bump” rule is maintainer guidance, not a mechanically enforced proof. Equal package versions should not be treated as cryptographic schema identities.
- The report does not enumerate every Serde field-level compatibility behavior for manually modified JSON, unknown fields, missing fields, reordered fields, or malformed hash-cons references.
- The report does not claim JSON and Postcard bytes are deterministic across processes or platforms; determinism is a separate #3720 subject.
- Postcard's positional representation is described from source/history. No standalone Postcard wire-format specification is reproduced here.
- The report does not prove semantic equivalence between `a535e914…` and `0c91ca1…`; it establishes equality of the examined serialization/library-interface blobs and version number.
- `deserialize_llbc*` returning `TranslatedCrate` without `has_errors` is an API fact. The report does not claim every current downstream consumer uses those convenience functions.
- The report does not claim the whole Rust `charon_lib` API follows semantic versioning. No such stability promise was found in the pinned repository guidance.
- The report does not choose whether Anneal should consume Charon in-process or through serialized artifacts. That is design authority on `main`, not a reference fact.

## Evidence

Primary Charon subject:

```text
AeneasVerif/charon
a535e914f74db4fd9e6be7048f4233270d8945c0
version 0.1.210
```

**Source:**

- `charon/src/export.rs`, blob `d5428958eb870f9f8531a8d193385c6be782338a`: `CrateData`, exact `CharonVersion` equality gate, JSON/Postcard serialization and deserialization, hash-consing, trailing-byte rejection, `has_errors`.
- `charon/src/lib.rs`, blob `a5530a1778d231297d8e480cf11531b141125a4f`: public `charon_lib` modules/re-exports, `VERSION`, `deserialize_llbc`, and `deserialize_llbc_with_format`.
- `charon/Cargo.toml`, blob `8c9936202e7bdbdaaefbc19305363da1ab6c0084`: package version 0.1.210, library name, stable-capable no-rustc feature boundary.
- `charon/src/ast/mod.rs`, blob `c9004d68f0295823a11654947e77a1fc9c525c02`: public in-memory AST module surface.
- `charon/src/transform/mod.rs`, blob `8d9ec016c3b6e42ba0cbac180546551d4a52587a`: public transformation infrastructure available through `charon_lib`.
- `charon-ml/src/OfJson.ml`, blob `a30706a384a78d51cf5a2fe566028ba3e902d0a0`: generated/manual OCaml JSON crate reader and exact supported-version check.
- `charon-ml/src/CharonVersion.ml`, blob `ea6a2833a3432b63eb95b1bda95dc333f60d6b4b`: generated supported version 0.1.210.
- `.github/workflows/release.yml`, blob `6fb37440be5a89f199f7e00198e8f88bc1b6d91d`: date-based nightly tagging/building without a package-version bump step.

**Documentation / repository policy:**

- `AGENTS.md`, blob `2aaeaaff1c5cfab4f01d81133ed6a37b7f175455`: Versioning section requiring a patch bump for every AST change and regeneration through the test workflow.

**Immutable source history:**

- `65dcdb566e05472a6bca8074318c05f729e30177`: `Rvalue::Use` gains `WithRetag`; package/generated version changes 0.1.208 → 0.1.209 and generated JSON/Postcard parsers change.
- `89e2529761404c02ab5a4d0a61a483853e4ee9e6`: `ConstantExprKind::TypeId` is added; package/generated version changes 0.1.209 → 0.1.210 and generated JSON/Postcard parsers change, including shifted Postcard variant tags.
- `b028e082c417eda7cf419e9661ad9fff047ac1ac`: `charon-lib` feature/build interface changes to permit stable `--no-default-features` builds without a package-version increment.

**Exact comparison source:** `AeneasVerif/charon@0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`, Charon tag `nightly-2026.06.03`. At both comparison revisions, these blobs are identical: `charon/Cargo.toml`, `charon/src/export.rs`, `charon/src/lib.rs`, `charon-ml/src/OfJson.ml`, and `charon-ml/src/CharonVersion.ml`.

No evidence in this report is fresh **execution**.

## Revalidation

For a later Charon revision, the cheapest reliable source check is:

1. Record the immutable Charon commit and package version from `charon/Cargo.toml`.
2. Read `export.rs` and confirm the `CrateData` fields, accepted encodings, and `CharonVersion` compatibility rule.
3. Read `lib.rs` and record what the convenience deserializers return and which public modules are exposed.
4. Inspect generated OCaml version/JSON/Postcard readers and confirm they were regenerated for the same package version.
5. Read current repository versioning policy; do not assume the 0.1.210 rule is permanent.
6. Diff the previous compatible version's AST and generated readers. If an AST shape changed without a version bump, treat that as a compatibility defect rather than silently extending the meaning of the old version.
7. Treat nightly tags and package versions as separate coordinates.

On an execution-capable surface, preserve one small Rust fixture as both JSON and Postcard and run a matrix with producer/consumer revisions:

- same exact commit;
- two distinct commits carrying the same Charon package version;
- adjacent package versions across a known AST change.

For each pair, record producer/consumer commits and package versions, exact command, encoding, artifact hash, parse result/error, `has_errors`, and a canonical summary of the decoded AST. Include both the Rust `CrateData` reader and the generated OCaml reader.

The expected discriminator from the pinned source is that adjacent unequal versions fail at the explicit version gate, while same-version inputs proceed to schema decoding. A passing same-version probe establishes concrete parser compatibility for that fixture; it does not prove semantic equivalence of all translated Rust programs or all `charon_lib` APIs.