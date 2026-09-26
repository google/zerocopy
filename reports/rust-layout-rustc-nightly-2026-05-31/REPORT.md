# Rust layout information available from rustc at nightly-2026-05-31

## Summary

At the Rust compiler revision behind Anneal-era nightly-2026-05-31, rustc computes substantially more layout information than the Rust language promises as a stable representation contract. Its internal layout model records size, ABI and preferred alignment, field offsets and memory order, enum variant layouts and tag encoding, scalar validity ranges and niches, inhabitation, backend representation categories, and whether a layout is sized. Type-aware traversal can recover per-field and per-variant layouts, and rustc separately computes the metadata type for potentially wide pointers.

These facts are target- and revision-specific compiler results. They must not be promoted into language guarantees for `repr(Rust)` types. The Rust Reference deliberately gives the default Rust representation only a small set of guarantees: fields are properly aligned, do not overlap, and the containing type's alignment is at least the maximum field alignment. Field order is otherwise not promised. Explicit representations such as `repr(C)`, primitive enum representations, `repr(transparent)`, `repr(align)`, and `repr(packed)` add specified constraints.

rustc's `LayoutData` separates recursive memory structure from backend representation. `FieldsShape` gives concrete offsets, `Variants` describes direct or niche enum tagging, and `BackendRepr` classifies scalar, scalar-pair, vector, scalable-vector, or memory forms. The source explicitly warns that backend representation alone is not a complete calling-convention promise. Call ABI additionally depends on target-specific pass-mode classification.

For DSTs, the ordinary static `size` field is not enough. Unsized layouts are marked through their backend representation, while the type system computes pointer metadata separately: slices and strings use `usize`, trait objects use `DynMetadata<T>`, and sized pointees use unit metadata. Generic tails can leave metadata unresolved until normalization.

No fresh rustc layout query or compiled layout probe was run.

## Applicability

Primary compiler subject:

- `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`
- toolchain date: nightly-2026-05-31

Normative language source:

- `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`

The report distinguishes two kinds of statement:

- Rust Reference guarantees, which constrain legal implementations for the described representation;
- rustc implementation results and APIs, which describe this exact compiler revision and target configuration.

Any concrete size, offset, niche, scalar validity range, or backend classification obtained from rustc is target-specific unless stronger language rules establish otherwise.

## Findings

### Rust language guarantees are narrower than rustc's computed layout

For the default Rust representation, the Reference guarantees proper field alignment, non-overlap, and enough overall alignment for every field. It does not guarantee declaration order, a stable field ordering algorithm, or a C-compatible layout.

Explicit `repr` attributes add stronger constraints. In particular, `repr(C)` gives specified struct and enum construction rules, primitive enum representations select integer-like tag representations, and `repr(transparent)`, `repr(align)`, and `repr(packed)` modify representation under their documented rules.

A rustc-computed offset for a `repr(Rust)` field is therefore an observation about the selected compiler/target, not a durable language theorem.

Basis: **normative**.

### LayoutData records size, alignment, fields, variants, niches, and backend form

The pinned `rustc_abi::LayoutData` contains:

- `fields`: memory placement of fields;
- `variants`: single- or multi-variant representation;
- `backend_repr`: codegen-facing scalar/vector/memory classification and scalar validity information;
- `largest_niche`: the largest known range of invalid scalar values available for niche use;
- `uninhabited`;
- ABI/preferred alignment;
- total static size;
- representation-alignment bookkeeping used by target ABIs.

This is a computed compiler data structure, not just a thin wrapper around `size_of` and `align_of`.

Basis: **source**.

### Field placement includes offsets and memory order

`FieldsShape` distinguishes primitives, unions, array-like layouts, and arbitrary struct-like layouts.

For an arbitrary layout, rustc stores an offset for each source-order field plus a permutation describing increasing memory order. The source notes that the offset vector itself need not be sorted because rustc may reorder fields.

The source also warns that gaps before, between, or after fields are not automatically disposable padding. Enum layouts can use such gaps for discriminant state.

Basis: **source**.

### Enum layout exposes direct and niche tag encodings

`Variants` distinguishes empty, single, and multiple-variant layouts. A multiple-variant layout records the tag scalar, the tag field, per-variant layouts, and a `TagEncoding`.

The tag encoding can be direct or niche-based. The niche form records an untagged variant, a variant range encoded into otherwise invalid values, and the starting niche value. The compiler source uses `Option<(usize, &T)>` as an example where a null reference value can encode `None` without a separate tag.

This is valuable semantic information for analyzing concrete machine representation, but it remains an implementation result unless the language or library separately promises the layout.

Basis: **source**.

### Scalar validity ranges and niches are part of the compiler layout model

A `Niche` records an offset, primitive scalar kind, and valid range. Values outside the valid range can be reserved to encode surrounding enum state.

`backend_repr` can also contain scalar or scalar-pair descriptions carrying value restrictions. That means rustc's layout representation combines byte placement with some validity information used for optimization and ABI reasoning.

A consumer must still distinguish these compiler-internal validity facts from the full Rust validity model and from library invariants.

Basis: **source**.

### TyAndLayout supports recursive field and variant traversal

`TyAndLayout` pairs a compiler type with a layout and exposes type-aware traversal. `field` obtains the layout of a field, and `for_variant` obtains the layout of a particular enum variant.

The source warns that a `TyAndLayout` need not be identical to `layout_of(ty)`: rustc creates layouts for entities with no standalone Rust type, including enum variants, synthetic discriminant fields, and wide pointers.

For downstream tooling, that warning matters. A layout object can describe a compiler-synthesized view, not only a source type queried in isolation.

Basis: **source**.

### Sizedness is represented separately from the static size field

`BackendRepr::Memory { sized }` distinguishes sized from unsized memory layouts. `LayoutData::is_unsized` derives unsizedness from the backend representation.

For an unsized type, a static `size` field cannot be interpreted as the complete runtime object size. The compiler representation explicitly distinguishes layouts whose full size is only known with runtime metadata.

Basis: **source**.

### rustc computes the metadata type for potentially wide pointers

The pinned type system exposes `ptr_metadata_ty_or_tail` and `ptr_metadata_ty`.

For sized pointees, metadata is unit. For `str` and slices, metadata is `usize`. For trait objects, metadata is the compiler's `DynMetadata<T>` type. For generic or alias tails whose metadata cannot yet be determined, rustc returns the unresolved tail or a projection through the pointee metadata mechanism.

This is type-level metadata information. It should not be confused with a concrete metadata value for a particular runtime pointer.

Basis: **source**.

### Pointer-layout advisory information is not the same thing as DST metadata

The ABI layer also has `PointeeInfo`, which records advisory facts about a pointer found at a layout offset: whether it is a raw/reference/box-like pointer, a guaranteed dereferenceable byte count, and alignment.

That information is intended for backend optimization and can be absent without changing correctness. It is different from the metadata component of a wide pointer.

Keeping these concepts separate avoids treating “pointee info” as a representation of slice length or trait-object metadata.

Basis: **source**.

### BackendRepr is not a complete function calling convention

`BackendRepr` classifies values as scalar, scalar pair, SIMD vector, scalable vector, or memory. Its own documentation says this mostly describes the syntactic form presented to codegen and does not by itself promise how a value is lowered to the platform calling convention.

The same source notes that call-ABI equivalence needs more than layout equality: target-specific pass mode also matters.

A verifier or FFI tool should therefore not infer complete argument/return ABI classification solely from `LayoutData::backend_repr`.

Basis: **source**.

### rustc_public exposes a deliberately smaller layout-shaped API, but it is still compiler-version data

The pinned `rustc_public::abi` layer exposes `TyAndLayout`, a serializable `LayoutShape`, field offsets, variants/tag encoding, ABI-category information, size, and ABI alignment.

That provides a more consumer-oriented surface than directly depending on every `rustc_abi` detail. It does not turn rustc's current `repr(Rust)` choices into language guarantees or establish a stable cross-version API contract for this report.

For durable reference use, exact compiler revision remains part of the subject identity.

Basis: **source** + **derived**.

## Boundaries

- No fresh layout query, `size_of`/offset probe, ABI dump, or cross-target build was run.
- The report does not enumerate every target-specific layout rule.
- It does not claim `repr(Rust)` field order, niche selection, enum encoding, or padding is stable across compiler revisions.
- It does not equate rustc scalar validity ranges with the complete Rust validity rules for arbitrary values.
- It does not infer library invariants from layout.
- It does not claim the static size stored for an unsized layout is a complete runtime object size.
- It distinguishes a wide pointer's metadata type from advisory `PointeeInfo`.
- It does not inventory function `FnAbi`/`PassMode` classification in detail; those are additional calling-convention layers.
- It does not establish that `rustc_abi` or `rustc_public` is a stable API across toolchains.
- It does not choose which layout API Anneal should consume.

## Evidence

**Normative Rust Reference.** `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`.

- `src/type-layout.md`, blob `2ee902aef043f4d299e009f6a69d1815d862e69e`: default Rust representation guarantees and explicit representation rules.

**Compiler source.** `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`.

- `compiler/rustc_abi/src/lib.rs`, blob `166c8bea6f3548307b004aa421ed37c556772ccf`: `LayoutData`, `FieldsShape`, `Variants`, `TagEncoding`, `Niche`, `BackendRepr`, and `PointeeInfo`.
- `compiler/rustc_abi/src/layout/ty.rs`, blob `b09afc9ec8af606d58b2afddff8510eaecb963ef`: `TyAndLayout`, field/variant traversal, and layout views without standalone Rust types.
- `compiler/rustc_middle/src/ty/sty.rs`, blob `9db9b1769ab9c891ef1aa0cdbdc83cde81e2487d`: `ptr_metadata_ty_or_tail`, `ptr_metadata_ty`, and pointer metadata typing.
- `compiler/rustc_ty_utils/src/layout.rs`, blob `9cc15a374ff702c2b5c90e179c8e797229f39a4e`: rustc type-layout query implementation.
- `compiler/rustc_public/src/abi.rs`, blob `1227fe23713cb172b8f1bd9d57162909e69ef663`: consumer-facing layout, field, variant, size/alignment, and ABI-shape representation.

No evidence above is fresh **execution**.

## Revalidation

For another compiler revision, first diff:

1. the default and explicit representation rules in the Rust Reference;
2. `LayoutData`, `FieldsShape`, `Variants`, `TagEncoding`, and `BackendRepr`;
3. `TyAndLayout` field/variant traversal;
4. pointer metadata typing in `rustc_middle::ty`;
5. the public ABI/layout projection if a downstream consumer relies on it.

On an execution-capable surface, query representative types across at least two targets: a reordered `repr(Rust)` struct, a `repr(C)` control, `Option<&T>`, a data-carrying enum, a union, `[T]`, `str`, and `dyn Trait`. Record size, alignment, field offsets, variant/tag encoding, niches, backend representation, pointer metadata type, and full function argument/return ABI where relevant. That establishes concrete outputs for those compiler/target pairs; it does not convert them into language guarantees.
