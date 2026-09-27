# Charon enum discriminants, niches, and layout at 0.1.210

## Summary

At `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (0.1.210), Charon represents two different facts about a Rust enum and keeps them separate:

1. each source-level variant has a **logical discriminant** in `Variant::discriminant`; and
2. each target-specific layout can have a **memory discriminator** plus per-variant tag writes in `Layout::discriminator` and `VariantLayout::tagger`.

That distinction matters because Rust's logical discriminant is not always the bytes that identify a variant in memory. Charon gets logical discriminants from rustc's `discriminant_for_variant`. Separately, it asks rustc for the target-specific layout and translates rustc's direct or niche tag encoding into a recursive `Discriminator` decision tree. For niche-encoded enums, a variant may have no tag write at all: its payload's valid-range niche identifies it. Charon can still describe how to distinguish that variant from explicitly tagged variants.

The memory-layout model is concrete enough to carry size, alignment, per-variant field offsets, uninhabitedness, representation options, tag-writing actions, and a decision tree for recovering the active variant from memory. Charon's pinned layout regression test checks the central consistency property directly: for every inhabited variant in every test layout, applying that variant's `tagger` and then querying the layout's `discriminator` must recover the same `VariantId`.

The layout model is not a complete serialization of rustc layout facts. `Layout` explicitly says it does **not** include general niche information. Charon exposes the niche encoding that rustc selected for enum discrimination when that encoding affects how variants are read or constructed, but it does not expose an arbitrary inventory of all valid ranges or otherwise-available niches. Its `ReprOptions` are also deliberately reduced: Rust-vs-C layout algorithm, align/pack modifier, transparent, and whether an explicit integer discriminant representation was specified. Less common representation modes and the full ABI classification are outside this structure.

Charon also keeps enum operations semantic in its IR. MIR discriminant reads remain `Rvalue::Discriminant`, enum construction names a `VariantId`, `SetDiscriminant` names a `VariantId`, and LLBC's match-reconstruction pass converts a discriminant-read-plus-integer-switch pattern into `Switch::Match` over variants using each variant's logical discriminant. This avoids making downstream consumers reverse-engineer Rust variants from target tag bytes for ordinary control flow.

No fresh Charon or rustc execution was performed in this run. The report is based on exact pinned source, checked-in test code, checked-in golden layout/output artifacts, and pinned repository history. The checked-in outputs are preserved upstream execution evidence, not fresh execution on this surface.

## Applicability

This report applies to:

- `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, Charon 0.1.210;
- Charon's embedded Rust toolchain `nightly-2026-05-31`;
- the ULLBC/LLBC schema and translation passes at that exact Charon revision.

It covers:

- enum variant identity and logical discriminant values;
- target-specific rustc layout queries and Charon's reduced `Layout` representation;
- direct and niche enum tag encodings;
- uninhabited and layoutless variants;
- representation options relevant to the stored layout;
- discriminant reads, enum construction, `SetDiscriminant`, and LLBC match reconstruction;
- checked-in layout and match tests that preserve behavior at this pin;
- nearby history that introduced the current discriminator/tagger representation.

It does not claim that Charon exposes every fact rustc knows about layout, validity, niches, ABI classification, provenance, or initialization. It also does not establish cross-revision or cross-target stability of any concrete Rust layout.

## Findings

### Charon separates logical discriminants from in-memory tags

`Variant` stores a `discriminant: Literal`. Its source documentation defines that value as the discriminant returned by `std::mem::discriminant` for the variant and explicitly warns that it can differ from the value stored in memory. Charon calls the memory value the **tag** and points to `Discriminator` and `VariantLayout::tagger` for that representation.

`Rvalue::Discriminant` repeats the same distinction. A discriminant read is a Rust-level operation: it returns the variant's logical discriminant, not necessarily the raw tag bytes selected by rustc's layout algorithm.

This is a useful boundary for Anneal. A proof about Rust `mem::discriminant`, a cast of a fieldless enum, or a match should use the logical variant discriminant. A proof about raw memory validity, writing an enum representation, or recovering the active variant from bytes needs the target-specific layout model instead.

Basis: Charon **source**.

### Logical discriminants come from rustc, including signed and explicit values

Charon's hax layer builds each enum `VariantDef` using rustc's:

`def.discriminant_for_variant(tcx, variant_idx)`.

It stores both the `u128` bit pattern and rustc's discriminant type. `translate_adt_def` later converts that value into a Charon `Literal` with the translated literal type.

This preserves cases where source order and discriminant value differ, including negative discriminants and explicitly chosen wide integer representations. The pinned layout fixture contains:

- `#[repr(i32)]` values `12`, `43`, and `123456`;
- `#[repr(i8)]` values `-1`, `0`, and `1`;
- `#[repr(u128)]` with `18446744073709551615`.

The checked-in golden layout records those values with the corresponding signed or unsigned integer types.

Basis: Charon **source** + preserved **execution** artifact.

### Charon obtains memory layout from rustc rather than recomputing Rust layout

For each translated type, Charon calls rustc's `tcx.layout_of(...)`. If rustc returns a layout, Charon translates a restricted subset into its own `Layout`; if layout computation fails, Charon stores no layout entry for that target.

For sized layouts Charon records `size` and ABI alignment. For unsized layouts those fields are `None`. The type declaration stores layouts in a map keyed by `TargetTriple`, and Charon separately records target pointer size and endianness.

This makes the layout data target-specific evidence. A layout extracted for one target must not be treated as a target-independent property of the Rust type.

Basis: Charon **source**.

### A Charon `Layout` records variant selection as an executable decision tree

The core layout structures are:

- `VariantLayout`, which records field offsets, whether the variant is uninhabited, and a `tagger`;
- `Discriminator`, which is either `Known(VariantId)`, `Invalid`, or `Branch { offset, int_ty, children, fallback }`;
- `Layout`, which records size, alignment, the optional discriminator, overall uninhabitedness, variant layouts, and representation options.

A `tagger` is a sequence of memory writes `(byte_offset, scalar_value)` needed to construct the selected variant's tag. A `Discriminator::Branch` says which integer to read from which offset, how ranges of values map to further discriminator nodes, and what to do when no child range matches.

This is stronger than merely storing a tag offset and tag type. The recursive tree can express invalid subranges and niche encodings whose interpretation is not a flat one-value-per-variant table.

Basis: Charon **source**.

### Direct-tag enums map rustc tag values to variants and reject other values

When rustc reports `Variants::Multiple` with `TagEncoding::Direct`, Charon:

1. finds the tag field offset;
2. translates rustc's tag primitive into a Charon integer type;
3. asks rustc for `tag_for_variant`;
4. adds a discriminator child mapping that exact tag value to the variant;
5. gives the variant a tagger that writes that value at the tag offset; and
6. uses `Discriminator::Invalid` as the fallback.

The checked-in `SimpleEnum` layout is the simplest example: a one-byte unsigned tag at offset 0 maps `0` and `1` to its two variants and treats other values as invalid. `SimpleAdt` shows the same structure with a `u32` tag and variant-specific field offsets.

Basis: Charon **source** + preserved **execution** artifact.

### Niche-encoded enums use the payload representation instead of requiring a tag write for every variant

For rustc `TagEncoding::Niche`, Charon still asks rustc for per-variant tag values. Explicitly tagged variants receive discriminator children and tagger writes. The untagged variant becomes the discriminator fallback and normally has an empty tagger.

The checked-in `NicheAdt` fixture is `None | Some(NonZero<u32>)`. Its layout is four bytes. Charon records:

- `0` at offset 0 as the explicit tag for `None`;
- `Some` as the fallback variant;
- no tagger write for `Some` because the nonzero payload itself carries the representation.

Likewise, `DiscriminantInNicheOfField` records the discriminator at byte offset 8 rather than assuming enum tags live at offset 0.

The important point is not that Charon has a generic notion of every possible niche. It records enough of **rustc's selected enum encoding** to construct and discriminate the variants for this layout.

Basis: Charon **source** + preserved **execution** artifact.

### Charon can represent invalid values inside a niche-encoded tag range

Niche encoding is not always equivalent to "some values mean explicit variants, everything else means the untagged variant." Some values inside the encoded range can be invalid.

Charon's translation handles this with a nested discriminator. If the untagged variant itself lies in the niche-variant range, Charon creates an inner discriminator whose fallback is `Invalid`, then places that tree under the outer niche range. The source comment says this is needed to detect the undefined behavior that occurs when a discriminant read encounters a value corresponding to the niched variant where that value is not valid.

The pinned `HasInvalidDiscr` regression fixture preserves this case. Its golden layout has an outer `u8` branch over `2..=4`; inside that range, `2` selects variant 0, `4` selects variant 2, and the inner fallback is `Invalid`. Outside the range, the untagged payload variant is selected. The fixture's source specifically records that reading `3` is undefined behavior for the tested representation.

Basis: Charon **source** + pinned regression **source** + preserved **execution** artifact.

### Uninhabited and layoutless variants are represented separately from valid inhabited variants

A type can have source variants that do not have a meaningful realizable layout for the current monomorphized type. Charon's `variant_layouts` therefore stores `Option<VariantLayout>` per variant.

For a single-layout enum, Charon can leave nonselected impossible variants as `None`. The checked-in `SingleVariantButNonZero = Result<!, ()>` demonstrates why variant index and memory tag cannot be conflated: only source variant index 1 is inhabited, and the discriminator is simply `Known(1)` while variant index 0 has no layout.

Other uninhabited variants can still have a layout record marked `uninhabited: true`; the layout round-trip test requires their tagger to be empty rather than pretending they can be constructed normally.

Basis: Charon **source** + preserved **execution** artifact.

### The pinned layout test checks tagger/discriminator consistency for every inhabited variant

`charon/tests/layout.rs` does more than snapshot JSON. After extracting the test crate, it iterates through every type with a discriminator and every variant layout.

For each inhabited variant, the test:

1. reads the variant's `tagger`;
2. supplies those tagger values when the discriminator asks to read memory;
3. chooses a non-tagged value for discriminator reads not covered by the variant's tagger; and
4. asserts that the discriminator returns the same `VariantId`.

For uninhabited variants, it asserts that any present tagger is empty.

This is strong preserved execution evidence for the representation invariant at this exact revision: the generated per-variant tag writes and generated discriminator agree on variant identity across the fixture set.

Basis: checked-in test **source** + preserved **execution** artifact.

### The layout fixture exercises more than ordinary `Option` niches

The pinned regression set covers materially different cases:

- ordinary direct tags;
- payload-carrying enum variants with different field offsets;
- `NonZero<u32>` niche encoding;
- a niche located at a nonzero byte offset;
- a `char` valid-range niche with tags outside the Unicode scalar-value range;
- signed discriminants;
- explicit `u128` discriminants;
- uninhabited variants;
- unions;
- `repr(C)` and `repr(packed)` field layouts;
- generic types whose layout is unavailable;
- a fixed-size generic pointer case;
- a niche encoding with an invalid value inside the tagged range.

This breadth does not prove completeness for all rustc layouts, but it gives substantially stronger evidence than a single `Option<NonNull<T>>` example.

Basis: checked-in test **source** + preserved **execution** artifact.

### Charon explicitly does not expose a general niche inventory

The `Layout` documentation says: "Does not include information about niches."

That statement coexists with the niche-aware enum discriminator described above. The correct interpretation is narrower than either extreme:

- Charon **does** preserve the consequences of rustc's selected niche encoding when it needs them to read or construct enum variants;
- Charon does **not** expose a general set of all otherwise-valid niches, scalar valid ranges, or optimization opportunities for arbitrary fields and types.

A downstream verifier must therefore not infer that absence of an explicit niche object means the type has no niches. Conversely, it should not reconstruct arbitrary validity constraints solely from the enum discriminator tree unless the intended claim is specifically about variant selection in that stored layout.

Basis: Charon **source** + **derived** representation boundary.

### `ReprOptions` is a reduced description of representation controls

For each layout, Charon stores:

- `ReprAlgorithm::Rust` or `ReprAlgorithm::C`;
- an optional `Align` or `Pack` modifier;
- `transparent: bool`;
- `explicit_discr_type: bool`.

The source explicitly excludes less-common or unstable representations such as `repr(simd)` and rustc-internal `repr(linear)` from this structure. It also does not store the complete source `repr` token stream.

The hax layer can see rustc's actual discriminant type derived from representation options, but Charon's reduced `ReprOptions` stores only whether that integer representation was explicit. The concrete memory discriminator independently records the integer type that must be read for the target layout, while each logical variant discriminant is itself a typed literal.

The golden layout also demonstrates the representation consequences Charon preserves: default Rust field reordering, `repr(C)` field order, and packed alignment/offsets.

Basis: Charon **source** + preserved **execution** artifact.

### Enum construction and projection use variant identities rather than raw tag values

Charon preserves variant identity through ordinary MIR translation:

- an enum aggregate is `AggregateKind::Adt(..., Some(variant_id), ...)`;
- `SetDiscriminant` stores a `VariantId`;
- a downcast selects a variant in the translated place type;
- a field projection on an enum carries that selected `VariantId`.

These are semantic operations over the enum declaration. The memory `tagger` exists in the type layout as the representation rule needed to realize the variant in bytes; ordinary IR consumers do not need to duplicate rustc's tag-selection logic for every construction or projection.

Basis: Charon **source**.

### MIR discriminant reads remain logical discriminant reads in ULLBC

A rustc MIR `Rvalue::Discriminant(place)` becomes Charon `Rvalue::Discriminant(place)` directly. Charon does not lower it to a raw integer read from `Layout::discriminator` during MIR translation.

That preserves Rust's semantic operation. The corresponding `Variant::discriminant` values describe the possible result, while the layout discriminator describes how a memory model could determine the active variant from bytes.

Basis: Charon **source**.

### LLBC reconstructs enum matches from logical discriminants

After control-flow reconstruction, Charon's `reconstruct_matches` pass recognizes the MIR pattern:

1. assign `Rvalue::Discriminant(place)` to a temporary;
2. immediately switch on the resulting integer.

The pass builds a map from each `Variant::discriminant` to its `VariantId`, rewrites the integer switch into `Switch::Match(place, ...)`, and removes the now-redundant discriminant read. If all logical discriminants are covered, it can drop the otherwise branch.

The pass can also recognize `core::intrinsics::discriminant_value` on a known enum and rewrite it into Charon's semantic discriminant operation. If the enum is opaque and Charon cannot see its variants, match reconstruction reports an error instead of guessing a mapping.

The checked-in `matches.out` fixture shows final LLBC matching directly on `E2::V1`, `E2::V2`, and `E2::V3` rather than exposing the intermediate integer tags.

Basis: Charon **source** + preserved **execution** artifact.

### Fieldless enum casts use logical discriminants

The pinned `issue-91-enum-to-discriminant-cast` fixture shows Charon translating casts of enums into:

`@discriminant(...)`

followed by the requested integer cast. The fixture includes an `Ordering` enum with source discriminants `-1`, `0`, and `1`.

This is consistent with the representation split: Rust enum-to-integer casts observe the logical discriminant, not an arbitrary optimized memory tag.

Basis: preserved **execution** artifact + Charon **source**.

### The current representation was introduced specifically to model MiniRust-style tag reads and invalid niche values

Pinned repository history records a concentrated redesign on May 13, 2026:

- commit `ca364ebd26c280f7b01e9dec38581f64ee80d462`, **"Copy MiniRust's variant tag representation"**;
- commit `8eeb1aad67b602fb7a2be9c1416df685241e54ee`, **"Detect that reading the niched discriminant is UB"**.

The first commit replaced a flatter discriminant-layout/tag representation with the recursive `Discriminator` tree and per-variant `tagger` used at the audited revision. The resulting generated bindings describe the structure as mirroring MiniRust's `Discriminator`.

Later nearby history includes:

- `3c55c65462133f6847d9bed7380497395a1564a2`, **"Move `ReprOptions` to be part of `Layout`"**;
- `80a5548302d54d45619f3da451877f1da922e32e`, **"Correctly represent layoutless variants"**.

This history explains why the present schema distinguishes logical variant discriminants, memory discriminator trees, per-variant taggers, and optional per-variant layouts rather than flattening those concepts.

Basis: pinned repository **history** + Charon **source**.

### For Anneal, Charon's stored layout is useful evidence but not a complete Rust validity model

The pinned schema can support important low-level questions: concrete size/alignment, field offsets, which variant a memory representation selects, which tag writes construct a variant, uninhabited variants, and selected representation flags.

It does not by itself establish every proposition required for a Rust-level memory-safety proof. In particular, it does not expose a general niche/valid-range inventory, does not claim to encode all rustc ABI classification, and can omit layout entirely when rustc cannot compute it for the translated type.

Anneal should therefore treat this as one explicit source of target-specific layout facts, not as a substitute for the complete Rust validity and operational model. The existing corpus reports on rustc layout/validity remain complementary rather than redundant.

Basis: Charon **source** + Anneal **derived** applicability.

## Boundaries

- No fresh rustc or Charon execution was performed.
- Checked-in Charon `.out` and `tests/layout.json` files are preserved upstream execution artifacts, not fresh observations from this run.
- The report does not prove that rustc's layout algorithm is stable across compiler versions or targets.
- It does not establish the normative Rust validity rules for arbitrary byte patterns; those belong to Rust/rustc semantics and separate corpus reports.
- `Layout` does not expose a general inventory of niches or scalar valid ranges. The report only claims that Charon represents the niche encoding rustc selected when that encoding appears in enum variant discrimination/construction.
- It does not claim every rustc ABI/layout field is preserved. The inspected Charon layout is intentionally restricted.
- It does not claim all representation attributes are represented by `ReprOptions`.
- Layout may be absent when rustc cannot compute it for the translated type, including important generic cases.
- Multi-target crates can carry more than one layout for a type. A consumer must select the layout for the target it is proving.
- The checked-in regression corpus is broad but not exhaustive over every direct/niche encoding rustc can produce.
- This report does not establish how Aeneas or Lean currently consume every layout field; it characterizes the Charon boundary that Anneal may need to preserve or model.
- It does not infer the memory bytes of an enum solely from `Variant::discriminant`; the report explicitly establishes that this would be unsound in general.

## Evidence

**Primary subject:** `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (0.1.210), Rust toolchain `nightly-2026-05-31`.

### Charon source

- `charon/src/ast/types.rs`, blob `548be29762fdc4f4d1cd652537db6f54065ff6ee`: `VariantLayout`, recursive `Discriminator`, `Layout`, `ReprOptions`, `TypeDecl::layout`, `TypeDeclKind::Enum`, and `Variant::discriminant`. [Immutable source](https://github.com/AeneasVerif/charon/blob/a535e914f74db4fd9e6be7048f4233270d8945c0/charon/src/ast/types.rs#L366-L589).
- `charon/src/ast/expressions.rs`, blob `eeb2143c714ee8b429a59c2aaf9f097afb18a940`: semantic `Rvalue::Discriminant` and enum aggregate representation. [Immutable source](https://github.com/AeneasVerif/charon/blob/a535e914f74db4fd9e6be7048f4233270d8945c0/charon/src/ast/expressions.rs#L720-L751).
- `charon/src/bin/charon-driver/hax/types/ty.rs`, blob `470ed2ff4d992efe30f8c4a09a3676111f304003`: rustc discriminant and representation-option translation, including actual rustc discriminant type. [Immutable source](https://github.com/AeneasVerif/charon/blob/a535e914f74db4fd9e6be7048f4233270d8945c0/charon/src/bin/charon-driver/hax/types/ty.rs#L212-L228) and [repr options](https://github.com/AeneasVerif/charon/blob/a535e914f74db4fd9e6be7048f4233270d8945c0/charon/src/bin/charon-driver/hax/types/ty.rs#L957-L975).
- `charon/src/bin/charon-driver/hax/types/new/full_def.rs`, blob `3589b2d6586a709384a1b870bb2184d3e97a401b`: enum variants populated via rustc `discriminant_for_variant` and rustc representation options. [Immutable source](https://github.com/AeneasVerif/charon/blob/a535e914f74db4fd9e6be7048f4233270d8945c0/charon/src/bin/charon-driver/hax/types/new/full_def.rs#L615-L647).
- `charon/src/bin/charon-driver/translate/translate_types.rs`, blob `35bef6ea79992c65ea934413765fa95f631274e6`: rustc layout query; direct/niche discriminator translation; invalid niche handling; single/empty layouts; variant discriminants; reduced repr options. [Immutable source](https://github.com/AeneasVerif/charon/blob/a535e914f74db4fd9e6be7048f4233270d8945c0/charon/src/bin/charon-driver/translate/translate_types.rs#L497-L718) and [variant discriminants/repr](https://github.com/AeneasVerif/charon/blob/a535e914f74db4fd9e6be7048f4233270d8945c0/charon/src/bin/charon-driver/translate/translate_types.rs#L857-L943).
- `charon/src/bin/charon-driver/translate/translate_items.rs`, blob `7964644be017856c6d165545a67bd6ef06e0c85c`: target-keyed layout attached to `TypeDecl`. [Immutable source](https://github.com/AeneasVerif/charon/blob/a535e914f74db4fd9e6be7048f4233270d8945c0/charon/src/bin/charon-driver/translate/translate_items.rs#L452-L470).
- `charon/src/bin/charon-driver/translate/translate_crate.rs`, blob `53536c6df6e241c9655840f6b1f8a4aca2113f90`: target pointer size and endianness registration. [Immutable source](https://github.com/AeneasVerif/charon/blob/a535e914f74db4fd9e6be7048f4233270d8945c0/charon/src/bin/charon-driver/translate/translate_crate.rs#L477-L485).
- `charon/src/bin/charon-driver/translate/translate_bodies.rs`, blob `c03ca8077f131a2ef701e9d27eaa9e69bb617124`: enum aggregate/variant IDs, downcasts/projections, discriminant reads, `SetDiscriminant`, and integer switches. [Immutable source](https://github.com/AeneasVerif/charon/blob/a535e914f74db4fd9e6be7048f4233270d8945c0/charon/src/bin/charon-driver/translate/translate_bodies.rs#L1078-L1217).
- `charon/src/transform/resugar/reconstruct_matches.rs`, blob `c81d3bc0c43dc47948b8d7edd1bbea906f4ae5e8`: logical-discriminant-to-variant map, `Switch::Match` reconstruction, opaque-enum error path, and `discriminant_value` reconstruction. [Immutable source](https://github.com/AeneasVerif/charon/blob/a535e914f74db4fd9e6be7048f4233270d8945c0/charon/src/transform/resugar/reconstruct_matches.rs#L1-L193).
- `charon/src/transform/mod.rs`, blob `8d9ec016c3b6e42ba0cbac180546551d4a52587a`: LLBC reconstruction pipeline invokes enum match reconstruction. [Immutable source](https://github.com/AeneasVerif/charon/blob/a535e914f74db4fd9e6be7048f4233270d8945c0/charon/src/transform/mod.rs#L195-L213).

### Preserved execution/regression evidence

- `charon/tests/layout.rs`, blob `521847f0d98fa5503f6fd4a13efe94d040d23c29`: layout fixture and tagger/discriminator round-trip assertion. [Immutable test](https://github.com/AeneasVerif/charon/blob/a535e914f74db4fd9e6be7048f4233270d8945c0/charon/tests/layout.rs#L9-L250).
- `charon/tests/layout.json`, blob `3bc14852304b384e56e7bc3313643b2b9b9eff13`: checked-in layouts for direct tags, niche encodings, field offsets, repr controls, uninhabited variants, explicit signed/wide discriminants, layoutless variants, and invalid niche values. [Immutable golden output](https://github.com/AeneasVerif/charon/blob/a535e914f74db4fd9e6be7048f4233270d8945c0/charon/tests/layout.json).
- `charon/tests/ui/matches.rs`, blob `95e53c383e795b62ebb59e6ee2874c9573cdf781`; `matches.out`, blob `dd9f0467fdfb91f06c9f3a6f0c7c705c423cacdc`: preserved enum-match reconstruction behavior. [Input](https://github.com/AeneasVerif/charon/blob/a535e914f74db4fd9e6be7048f4233270d8945c0/charon/tests/ui/matches.rs) and [output](https://github.com/AeneasVerif/charon/blob/a535e914f74db4fd9e6be7048f4233270d8945c0/charon/tests/ui/matches.out).
- `charon/tests/ui/issue-91-enum-to-discriminant-cast.rs`, blob `cb977d63d5172e0e0312e391fe1b0d85a1bec334`; output blob `f0cbe6bafeba9b0c8f24d4724285f08dfc5dc0b2`: preserved enum-cast lowering through semantic discriminant reads. [Input](https://github.com/AeneasVerif/charon/blob/a535e914f74db4fd9e6be7048f4233270d8945c0/charon/tests/ui/issue-91-enum-to-discriminant-cast.rs) and [output](https://github.com/AeneasVerif/charon/blob/a535e914f74db4fd9e6be7048f4233270d8945c0/charon/tests/ui/issue-91-enum-to-discriminant-cast.out).
- `charon/tests/ui/cross_compile_32_bit.rs`, blob `23f1e90d76c3ca35c561b4f288be65febc387df5`; output blob `2bd12593dde699d967ece9588d5cb4f67c62d9db`: checked-in 32-bit target case including a pointer-niche enum.
- `charon/tests/ui/cross_compile_big_endian.rs`, blob `75c9f92b344f68e3b1222978b9a145494e666c0f`; output blob `342f2eb5eadeab56a15a84ee13a0af6d89109c53`: checked-in big-endian target case with `repr(i64)` enum discriminants.

### Pinned history

- [`ca364ebd26c280f7b01e9dec38581f64ee80d462`](https://github.com/AeneasVerif/charon/commit/ca364ebd26c280f7b01e9dec38581f64ee80d462), **"Copy MiniRust's variant tag representation"**.
- [`8eeb1aad67b602fb7a2be9c1416df685241e54ee`](https://github.com/AeneasVerif/charon/commit/8eeb1aad67b602fb7a2be9c1416df685241e54ee), **"Detect that reading the niched discriminant is UB"**.
- [`3c55c65462133f6847d9bed7380497395a1564a2`](https://github.com/AeneasVerif/charon/commit/3c55c65462133f6847d9bed7380497395a1564a2), **"Move `ReprOptions` to be part of `Layout`"**.
- [`80a5548302d54d45619f3da451877f1da922e32e`](https://github.com/AeneasVerif/charon/commit/80a5548302d54d45619f3da451877f1da922e32e), **"Correctly represent layoutless variants"**.

No fresh **execution** evidence was produced in this run.

## Revalidation

For a future Charon revision, first diff:

1. `ast/types.rs` for `Variant`, `VariantLayout`, `Discriminator`, `Layout`, and `ReprOptions`;
2. `translate_types.rs` for rustc layout/discriminant extraction and direct/niche encoding;
3. hax enum/repr translation in `hax/types/ty.rs` and `hax/types/new/full_def.rs`;
4. enum operations in `translate_bodies.rs`;
5. `reconstruct_matches.rs` and the LLBC pass ordering;
6. `tests/layout.rs` and `tests/layout.json` for coverage and invariant changes.

On a capable execution surface, run a compact pinned matrix that preserves both the Rust input and serialized Charon output for:

- a plain fieldless enum;
- a data-carrying direct-tag enum;
- `Option<NonZero<u32>>` or an equivalent one-niche enum;
- a niche at a nonzero field offset;
- a niche encoding with an invalid value inside the encoded range;
- negative and very wide explicit discriminants;
- an enum with an uninhabited source variant whose inhabited variant has a nonzero `VariantId`;
- `repr(C)`, `repr(packed)`, and explicit integer reprs;
- a generic type whose layout is unavailable before monomorphization;
- at least two targets with different pointer width/endian properties;
- a match, `mem::discriminant`, enum-to-integer cast, construction, and `SetDiscriminant` path.

For every layout with an active discriminator, repeat Charon's own invariant check: use each inhabited variant's tagger to answer discriminator reads and require recovery of that same `VariantId`. Separately compare each logical `Variant::discriminant` against rustc's discriminant operation; do not substitute raw memory tag values for that check.

A successful matrix confirms the concrete representation for those revisions, targets, and examples. It does not establish a stable Rust ABI, a complete Rust validity model, or a complete inventory of every niche rustc may use.