# Rust dynamically sized and slice layout at nightly-2026-05-31

## Summary

Rust's dynamically sized types separate two questions that unsafe-code proofs often blur: **the layout of the dynamically sized value** and **the representation of a pointer that carries enough metadata to locate that value**.

At the Anneal-era Rust pin, a slice value `[T]` has the same layout as the array section it denotes. Combining that rule with the array-layout contract gives a slice of length `n` dynamic size `n * size_of::<T>()`, alignment `align_of::<T>()`, and element `i` at byte offset `i * size_of::<T>()`. The length is pointer metadata, not part of the `[T]` value's byte extent. This distinction is especially important for zero-sized elements: a `[T]` slice can have nonzero or very large element count while its dynamic byte size remains zero, and all element offsets are zero.

`str` has the layout of `[u8]`, while additionally requiring valid UTF-8 for the operations that rely on the `str` invariant. Trait objects are different: the raw `dyn Trait` value has the layout of the concrete value it erases, and pointer metadata is a vtable that carries, among other things, that concrete type's size and alignment.

A struct may itself become dynamically sized when its last field is a DST. Its pointer metadata is the metadata of that last field. The metadata does **not** by itself equal the outer value's layout: `size_of_val_raw` documents the relevant quantity as the size of the entire value, including the statically sized prefix, and `DynMetadata::size_of` explicitly warns that a trait-object tail's vtable size is only the tail's concrete size. A verifier therefore needs both the enclosing layout rule and the tail metadata.

Pointer layout is a separate contract again. The Reference guarantees that a pointer to an unsized type is itself sized and no smaller or less aligned than a pointer to a sized type. A nearby explanatory page says DST pointers have twice the size of ordinary pointers, while the dedicated type-layout chapter explicitly marks the current two-word representation as something code should not rely on. At this pin, core's `Pointee` API exposes the semantic decomposition—data pointer plus `()`/length/vtable metadata—but that does not turn an implementation representation into a stable field-layout or ABI guarantee.

Finally, layout metadata is not access validity. A raw wide pointer can be constructed without proving that its data range exists. Producing a valid slice reference or `Box<[T]>` adds stronger conditions, including a valid length and a total pointed-to size no greater than `isize::MAX`; safe slice values also require initialized elements. Anneal should therefore keep **metadata shape**, **dynamic layout**, and **reference/access validity** as separate proof obligations.

No fresh rustc, Miri, Charon, Aeneas, or Lean execution was performed. The report records the exact pinned Reference and core-library contracts and derives the minimum layout formulas needed by a verifier.

## Applicability

The directly examined subjects are:

- `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, the compiler and core-library revision behind Anneal's `nightly-2026-05-31`; and
- `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`, the Reference revision examined with that compiler tree.

The report covers:

- raw slice values `[T]`;
- `str`;
- trait-object DSTs where their layout relation matters;
- structs whose final field is a DST;
- the metadata needed by pointers to those DSTs; and
- the boundary between dynamic layout and the validity of a wide reference or raw pointer.

It does not re-document every wide-pointer API. The separate wide-pointer-metadata candidate owns complete `Pointee`, `ptr::metadata`, `from_raw_parts`, metadata replacement, and raw dyn-trait metadata semantics. This report uses those APIs only to connect metadata to value layout.

It also does not repeat the complete aggregate-layout contract. A separate aggregate-layout candidate owns `repr(Rust)`, `repr(C)`, enum/union geometry, packing, and transparent layout. Here those rules matter only because the statically sized prefix of a DST-tail struct remains part of the outer value.

Where the Reference distinguishes guarantees from current implementation observations, this report keeps that distinction. In particular, it does not promote the common two-word DST-pointer representation into a cross-compilation language guarantee.

## Findings

### DSTs have run-time value layout, while their pointers remain sized

The Reference defines a dynamically sized type as one whose size is known only at run time. Slices, `str`, and trait objects are examples. A struct can also become dynamically sized by placing a DST in its final field.

The value still has a concrete size and alignment when a particular instance is used. `size_of_val` and `align_of_val` query those run-time properties through a reference. The unsizedness means the compiler cannot assign one compile-time `size_of::<T>()` and `align_of::<T>()` pair shared by all values of `T`.

Pointers to DSTs are themselves sized. This is what makes values such as `&[T]`, `&str`, and `&dyn Trait` ordinary sized values even though their pointees are not.

Basis: **normative** Reference `dynamically-sized-types.md` and `type-layout.md` + **documentation/source** in `core::mem`.

### A slice value has the layout of the array section it denotes

The Reference gives two rules that compose directly:

1. `[T; N]` has size `size_of::<T>() * N`, alignment `align_of::<T>()`, and element `i` at offset `i * size_of::<T>()`.
2. `[T]` has the same layout as the section of the array it slices.

For a slice value `[T]` of run-time length `n`, the derived layout is therefore:

```text
dynamic size      = size_of::<T>() * n
dynamic alignment = align_of::<T>()
element i offset  = size_of::<T>() * i
```

This is a statement about the **raw `[T]` value**, not about the representation of `&[T]`, `*const [T]`, `Box<[T]>`, or another pointer to it.

The length is nevertheless essential: it determines how many array elements the slice value contains and therefore its dynamic extent. At the core pointer API boundary, `[T]` metadata is that element count as a `usize`.

Basis: **normative** Reference array/slice layout + **documentation/source** in `core::ptr::Pointee` + **derived** formula.

### Zero-sized element slices decouple logical length from byte extent

If `size_of::<T>() == 0`, the slice formula yields zero dynamic bytes for every length:

```text
size_of_val::<[T]>(slice) = 0
```

and every element offset is `i * 0 == 0`.

The slice length still remains metadata and still counts logical elements. The resulting proof obligation is not “slice length equals accessible byte count.” For ZSTs, logical cardinality can change while the byte extent does not.

This also means distinct logical slice elements need not have distinct addresses. The Reference already warns more generally that zero-sized fields may share addresses; for slices the zero-stride result follows directly from the array element-offset formula.

The alignment does not collapse with the size. A zero-sized type can have nontrivial alignment, and the slice inherits the element type's alignment.

Basis: **normative** Reference size/alignment and array/slice layout + **derived** consequence.

### `str` is layout-compatible with `[u8]`, but adds a semantic validity invariant

The Reference specifies `str` as having the same layout as `[u8]`. It separately states that `str` operations assume valid UTF-8.

Thus the dynamic layout of a `str` of byte length `n` follows the `[u8]` slice layout. The length metadata counts bytes, not Unicode scalar values, characters, or grapheme clusters.

The same Reference section also guarantees that `&str` has the same layout as `&[u8]`. That pointer-layout equivalence does not erase the semantic difference: safe `str` operations may rely on UTF-8 validity in ways `[u8]` operations do not.

Basis: **normative** Reference `type-layout.md` and `types/textual.md`.

### Trait-object value layout comes from the erased concrete value

The Reference states that a raw trait object has the same layout as the concrete value the trait object represents. Pointers to trait objects carry a data pointer plus a vtable.

At the pinned core revision, `DynMetadata` documents that the vtable carries the concrete type's size and alignment in addition to drop and method information. Its `size_of` and `align_of` methods expose those dynamic properties.

This differs from slice metadata. A slice's metadata is a count from which its byte extent is derived using `T`; trait-object metadata carries type-specific layout information through the vtable.

Basis: **normative** Reference trait-object layout + **documentation/source** in `core::ptr::DynMetadata`.

### A DST-tail struct reuses the tail's metadata, but the outer layout includes its prefix

The Reference permits a struct to have a DST as its final field, which makes the struct itself dynamically sized. The pinned `Pointee` documentation states that such a struct's pointer metadata is the metadata of its last field.

That does not mean the last field's dynamic size is the outer struct's dynamic size.

The raw layout-query documentation says that, for a slice or trait-object tail, the **entire value** includes the dynamic tail plus a statically sized prefix. The exact placement of the tail and any padding are still governed by the enclosing struct's representation and actual field layout.

`DynMetadata::size_of` makes the same boundary concrete for trait-object tails. Its source comments use an enclosing value such as `(i32, dyn Send)` and warn that the vtable stores only the `dyn Send` part's size; `size_of_val_raw` for the outer value is different.

For Anneal, tail metadata therefore supplies input to the enclosing layout computation. It is not a precomputed `size_of_val` for the outer DST.

Basis: **normative** Reference DST-tail rule + **documentation/source** in `core::ptr::Pointee`, `core::mem::{size_of_val_raw, align_of_val_raw}`, and `DynMetadata`.

### Default `repr(Rust)` prevents a generic source-order formula for arbitrary DST-tail structs

The Reference's default `Rust` representation gives only soundness-required field-placement guarantees: each field offset respects that field's alignment, aggregate alignment is at least the maximum field alignment, and struct fields do not overlap in some ordering. It does not promise declaration-order field layout or any further geometry.

A source-level declaration whose final field is a DST is syntactically constrained to place that DST last, but that fact alone is not a license to invent a stable byte offset formula for the sized prefix under all future compilers. Proofs that require exact prefix/tail geometry need a representation contract or exact compiler-layout evidence appropriate to that subject.

This report therefore records the compositional rule—outer dynamic layout includes the prefix and the tail—without manufacturing a stronger default-layout guarantee than the Reference provides.

Basis: **normative** Reference default-layout and DST rules + **derived** limitation.

### Wide-pointer metadata has a semantic shape, not a generally stable two-word ABI layout

The Reference has two relevant statements that must not be silently collapsed.

The dynamically-sized-types chapter describes pointers to DSTs as twice the size of ordinary pointers and explains the extra information:

- slice and `str` pointers carry a length;
- trait-object pointers carry a vtable pointer.

The dedicated type-layout chapter gives the contractual guarantee more cautiously: a pointer to an unsized type is sized, and its size and alignment are each at least those of a pointer to a sized type. It then labels the familiar “twice `usize` size, same alignment” property as current behavior that code should not rely on.

Core's pinned `Pointee` API provides the semantic decomposition without requiring code to assume a field layout:

- `()` metadata for thin pointees;
- `usize` for `[T]` lengths;
- `usize` byte lengths for `str`;
- the final field's metadata for DST-tail structs; and
- `DynMetadata<dyn Trait>` for trait objects.

A verifier can model those semantic components. Code that needs an FFI-stable two-machine-word representation needs separate ABI authority rather than this language-level layout description.

Basis: **normative** Reference type-layout guarantee + **descriptive** Reference DST explanation + **documentation/source** in `core::ptr::Pointee`.

### Metadata sufficient to describe layout is not sufficient to make a valid reference

The pinned raw-parts API is deliberately safe: it can assemble a raw wide pointer from a data pointer and metadata even when the result is not safe to dereference. That demonstrates an important boundary for layout reasoning. Metadata can describe a putative dynamic layout without establishing a live allocation or valid reference.

The Reference's invalid-value rules add stronger requirements to wide references and `Box` values. Slice metadata must be a valid `usize`, and for a wide reference or `Box<[T]>`, the metadata is invalid if it makes the total pointed-to value larger than `isize::MAX`. References must also be aligned, non-null, non-dangling, and point to valid values, subject to the Reference's stated uncertainty around the complete aliasing/validity model.

For safe slice values, the slice-type chapter states that all elements are initialized. This is stronger than “the length metadata and element layout are arithmetically well formed.”

The raw-pointer case is intentionally weaker. A raw slice pointer can carry length metadata without proving that all represented elements exist in one allocation. Separate raw-pointer construction/access candidates own those operational rules.

Basis: **normative** Reference validity/slice rules + **documentation/source** in `core::ptr::from_raw_parts`.

### Raw layout queries still impose metadata well-formedness conditions

`size_of_val_raw` and `align_of_val_raw` can query a DST layout without first forming a Rust reference, but they are unsafe and document explicit preconditions.

For a slice tail, the length metadata must be initialized and the size of the **entire value**—dynamic tail plus statically sized prefix—must fit in `isize`; length zero is a documented special case. For a trait-object tail, the vtable must be valid and originate from an unsizing coercion, and the entire value must again fit in `isize`.

Those APIs therefore should not be modeled as pure arithmetic over arbitrary metadata bits. They expose layout from raw pointers only under subject-specific metadata conditions.

Basis: **documentation/source** in `core::mem::{size_of_val_raw, align_of_val_raw}`.

### A useful Anneal layout state keeps four quantities distinct

For an unsized pointee, a verifier can avoid several recurring category errors by tracking at least:

1. **data address/provenance** — where access would begin and under what provenance authority;
2. **metadata** — for example slice length or trait-object vtable;
3. **dynamic value layout** — the size/alignment and field/element offsets implied by the subject plus metadata; and
4. **access/reference validity** — whether the represented bytes actually exist, are aligned and initialized as required, and satisfy aliasing/lifetime/other type invariants.

For `[T]`, metadata and layout relate by the simple `n * size_of::<T>()` formula. For an enclosing DST-tail struct, the same metadata participates in a larger layout computation. For trait objects, metadata carries dynamic type layout through a vtable. In no case does “metadata has the expected Rust type” alone establish valid dereference.

This decomposition is **derived** from the pinned contracts and is intended as a verification model, not as a claim that rustc internally stores exactly these four records.

## Boundaries

**No fresh execution.** No rustc layout dump, Miri run, Charon translation, Aeneas translation, or Lean proof was executed. The report is source/specification grounded.

**No stable two-word ABI claim.** The current implementation commonly uses data plus one metadata word, and the Reference describes that shape, but its layout chapter explicitly says not to rely on the current twice-`usize` size for DST pointers.

**No complete default DST-tail offset algorithm.** The report does not infer declaration-order offsets or a stable compiler-chosen `repr(Rust)` layout beyond the Reference guarantees.

**No complete wide-pointer API report.** Pointer decomposition/reconstruction, metadata replacement, provenance behavior, and raw dyn-trait metadata uncertainty are owned by the wide-pointer-metadata candidate.

**No complete aggregate-layout report.** Sized structs, enums, unions, packing, `repr(C)`, and transparent representation are separate except where an outer prefix affects a DST-tail layout.

**No blanket raw-pointer validity claim from metadata.** Safe raw-pointer construction and raw metadata do not establish that the represented range is allocated or dereferenceable.

**Trait-object tail size is not whole-object size.** `DynMetadata::size_of` is the dynamic concrete type's size associated with that vtable. An enclosing DST-tail struct can require additional prefix and padding.

**The Reference itself contains differently worded pointer-size statements.** This report preserves the dedicated type-layout chapter's weaker guarantee and treats the other page's two-word description as explanatory/current behavior, not a stronger stable contract.

**UTF-8 remains a semantic invariant.** Equal `str`/`[u8]` layout does not mean arbitrary `[u8]` bytes are a valid `str`.

## Evidence

Primary Rust subject:

- repository: `rust-lang/rust`
- revision: `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`
- selected toolchain date: `2026-05-31`

Pinned core files:

- `library/core/src/ptr/metadata.rs`, blob `1eeadf1217b5f94b48a33de62cd82ad47941890c` — `Pointee::Metadata`, slice/`str`/DST-tail/trait-object metadata kinds, raw-parts construction, `DynMetadata` layout accessors, and the warning that vtable size is not enclosing DST size.
- `library/core/src/mem/mod.rs`, blob `62c612e7ba2a65bb1645faaa669abd2a1d35a6c2` — `size_of_val`, `align_of_val`, and raw layout-query contracts for slice and trait-object tails.

Primary Reference subject:

- repository: `rust-lang/reference`
- revision: `ad35aca481751a06afeb23820a672b0f3b11a476`

Pinned Reference files:

- `src/type-layout.md`, blob `2ee902aef043f4d299e009f6a69d1815d862e69e` — size/alignment, arrays, slices, `str`, trait-object raw value layout, unsized pointer layout guarantees, and default `repr(Rust)` constraints.
- `src/dynamically-sized-types.md`, blob `cd90adb75dc4dc9bd4c7af8ea24a1b5ca7dd7b0b` — DST taxonomy, metadata description, and final-field DST structs.
- `src/types/slice.md`, blob `e8be3a9f1ef48fe07a786238baccebca8f4abd39` — slice semantics and initialized-element guarantee.
- `src/types/textual.md`, blob `05068309a7bfb15a5b4612a24276308a5240c9d0` — `str` as `[u8]` layout plus UTF-8 invariant.
- `src/types/trait-object.md`, blob `7b07b6a05c0f282c814ccf3b73e89e8db8935cb3` — trait-object DST and data/vtable explanation.
- `src/behavior-considered-undefined.md`, blob `373052061c50fc2f6d1c07a91960d40bac505284` — wide-reference metadata validity and general reference validity boundaries.

Evidence was acquired or materially revalidated on 2026-09-27. No execution artifact is claimed.

## Revalidation

After a Rust toolchain or Reference revision change:

1. Re-read `type-layout.md` for array, slice, `str`, trait-object, unsized-pointer, and default-representation guarantees. Do not assume the current “do not rely” note about DST-pointer size is unchanged.
2. Re-read `dynamically-sized-types.md` and compare its pointer representation wording with the dedicated type-layout contract. Preserve any disagreement rather than silently selecting the stronger statement.
3. Re-read `core::ptr::Pointee` for metadata kinds, especially DST-tail forwarding, slice/`str` lengths, and `DynMetadata`.
4. Re-read `DynMetadata::{size_of, align_of}` and its enclosing-DST warning.
5. Re-read `size_of_val(_raw)` and `align_of_val(_raw)` for raw-query preconditions and how the implementation/documentation handles a statically sized prefix plus dynamic tail.
6. Re-read the Reference invalid-value section for slice metadata and total-size requirements on wide references/boxes.
7. Re-read `types/slice.md` and `types/textual.md` for initialization and UTF-8 invariants.
8. If an engineering decision depends on exact concrete pointer size, field offsets, or compiler-selected DST-tail geometry rather than the language guarantees, add an exact-toolchain execution artifact for the relevant targets and keep those observations scoped to those compiler/target identities.

For an Anneal regression probe, useful exact-pin cases include `[u8]`, `[u32]`, a zero-sized element slice, `str`, `dyn Trait`, and a struct with a slice or trait-object tail. Record `size_of_val`, `align_of_val`, pointer metadata, and any compiler layout output together. Treat those execution results as evidence about that exact compiler/target, not as replacements for the language-level guarantees above.
