# Rust wide-pointer metadata at nightly-2026-05-31

## Summary

At `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, Rust's pointer-metadata API models a raw pointer as a **data pointer plus metadata determined by the pointee type**. Thin pointees use `()` metadata. Wide pointees use non-zero metadata: `str` uses a byte length, `[T]` uses an element count, a DST struct reuses the metadata of its unsized tail field, and a `dyn Trait` uses `DynMetadata<dyn Trait>` backed by a compiler-generated vtable.

This split is structural, not a dereferenceability proof. `ptr::from_raw_parts` and `from_raw_parts_mut` are safe constructors, yet their documentation explicitly says the resulting raw pointer is not necessarily safe to dereference. For trait objects, supplied metadata must correspond to the same underlying erased concrete type. For slices, the metadata is a `usize` length, while actually converting or dereferencing the pointer imposes separate allocation, range, alignment, validity, and aliasing obligations.

Metadata also does not transfer pointer provenance. The pinned `with_metadata_of` methods make this boundary explicit: they combine the **data address/provenance of `self`** with metadata from another pointer, and warn that provenance is not combined. A pointer reconstructed with another pointer's metadata may only be used for addresses already authorized by the data pointer's provenance.

`DynMetadata` is a typed wrapper around vtable metadata. The vtable carries the erased concrete type's size, alignment, drop glue, and trait methods. Its `size_of`, `align_of`, and `layout` methods describe the concrete type represented by that vtable metadata; they are not generally the dynamic layout of an enclosing DST struct whose unsized tail happens to use that vtable. Vtable-pointer equality is also not a reliable type-identity test because equivalent vtables can be duplicated and different vtables can be deduplicated.

The bundled Reference imposes some wide-pointer **bit-validity** rules but preserves uncertainty. Wide metadata must match the unsized tail type. Slice metadata must be a valid `usize`. `dyn Trait` metadata is expected to be a compiler-generated vtable for the trait, but the Reference explicitly says the raw-pointer form of that requirement remains debated. The Reference's total-size `isize::MAX` validity bound is stated for wide references and `Box`, not for raw pointers themselves; a raw wide pointer can therefore exist under weaker conditions than are required to turn it into a reference or perform an access.

For Anneal, the reusable model is a product with distinct proof obligations:

1. **data pointer/address/provenance**;
2. **metadata kind and type compatibility**;
3. **metadata value validity**;
4. **dynamic-layout interpretation**; and
5. **operation-specific access/reference requirements**.

Collapsing these into "fat pointer = two machine words" loses exactly the semantic distinctions needed for sound unsafe-code verification.

The public pointer-metadata construction/decomposition surface is still unstable under `ptr_metadata` at this pin. This report describes its exact selected semantics and representation boundary, not a stability guarantee.

No fresh rustc, Miri, Charon, Aeneas, or Lean execution was performed.

## Applicability

This report applies to:

- `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, including `core::ptr`'s pointer-metadata implementation; and
- `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`, the Reference revision bundled by that compiler tree.

It covers the source-language/library semantics of:

- `Pointee::Metadata`;
- the `Thin` trait alias;
- `ptr::metadata`;
- `ptr::from_raw_parts` and `from_raw_parts_mut`;
- `DynMetadata`;
- `*const T::to_raw_parts` / `*mut T::to_raw_parts`;
- `with_metadata_of`; and
- Reference-level validity requirements for wide raw pointers, references, and `Box`.

The current public re-export of the pointer-metadata API is feature-gated under `ptr_metadata`. `with_metadata_of` is separately feature-gated under `set_ptr_value`. Their instability matters to source compatibility but does not make the inspected semantics unusable as exact-revision reference material.

This report does not define the complete layout of slices, trait objects, or arbitrary DST structs; it records the metadata contract needed to reason about their pointers. It also does not own `slice::from_raw_parts`, raw-pointer-to-reference conversion, pointer casts/provenance APIs, or Charon/Aeneas representation. Those are separate #3720 subjects.

## Findings

### Metadata is determined by the pointee type

`Pointee` is compiler-provided for every pointee type and exposes an associated `Metadata` type.

The pinned documentation gives the mapping:

| Pointee kind | Metadata |
| --- | --- |
| statically `Sized` type | `()` |
| `extern` type | `()` |
| `str` | byte length as `usize` |
| `[T]` | element count as `usize` |
| struct with DST tail | metadata of the last unsized field |
| `dyn Trait` | `DynMetadata<dyn Trait>` |

The API deliberately leaves room for future pointee kinds with different metadata.

The `Thin` trait alias denotes pointees whose metadata is `()`. It includes sized types and `extern` types.

A verifier should therefore model metadata by pointee kind, not by assuming every wide pointer has the same second-word semantics.

Basis: **core-library documentation/source** in `library/core/src/ptr/metadata.rs`.

### Wide pointers are logically data pointer plus metadata, not merely two integers

The pointer-metadata documentation describes pointers and references as having a data pointer and metadata. This is the semantic decomposition exposed by `to_raw_parts`, `metadata`, and `from_raw_parts`.

That decomposition should not be strengthened into an ABI claim that all wide pointers are always exactly two ordinary integer machine words with freely transmutable representation. The Reference separately says pointer-to-non-pointer transmutation semantics are unsettled, and `DynMetadata` source contains compiler-specific layout handling.

For verification, represent the components semantically:

- a pointer-valued data component carrying address/provenance; and
- metadata whose type/value rules depend on the unsized pointee.

Basis: **source/documentation** plus **derived representation boundary**.

### `metadata` extracts only the metadata component

`ptr::metadata<T>(ptr)` returns `<T as Pointee>::Metadata`.

The function accepts `*const T`; mutable pointers and references can be implicitly coerced for this purpose. For a string literal, the pinned example returns its byte length.

Extracting metadata does not access the pointee's bytes. It therefore should not be conflated with proving that the pointer is live, dereferenceable, or points to a valid value.

The metadata value can nevertheless carry semantic constraints of its own, particularly for slices and trait objects.

Basis: **core-library source/documentation**; access-boundary statement is **derived**.

### `to_raw_parts` preserves a typed metadata value while erasing the data-pointer pointee type

For `*const T`, `to_raw_parts` returns:

```text
(*const (), <T as Pointee>::Metadata)
```

and the mutable form returns:

```text
(*mut (), <T as Pointee>::Metadata)
```

The implementation uses a cast for the data pointer and `metadata(self)` for the metadata component.

This is a useful generic normalization: the data pointer becomes thin while metadata remains statically typed according to the original pointee. Reconstruction can later use `from_raw_parts` or its mutable counterpart.

The decomposition does not create new memory authority. The data pointer remains a pointer derived from the original pointer, and later access must still satisfy normal provenance/range obligations.

Basis: **source** in `const_ptr.rs` / `mut_ptr.rs`; provenance consequence is **derived** from the broader pointer model.

### `from_raw_parts` is safe because raw-pointer construction is weaker than dereference

`ptr::from_raw_parts` and `from_raw_parts_mut` combine a thin data pointer with metadata and return a possibly-wide raw pointer.

The API is safe, while its documentation immediately warns that the resulting pointer is not necessarily safe to dereference. That distinction is central: constructing a raw pointer value is weaker than using it for an access or converting it to a reference.

For slices, the constructor delegates access/reference requirements to the corresponding slice APIs. For trait objects, the documentation adds a metadata-specific condition: the metadata must come from a pointer to the **same underlying erased type**.

This means "constructor is safe" must never be translated into "any data/metadata pair may be dereferenced safely."

Basis: **core-library documentation/source**.

### Metadata compatibility and data-pointer provenance are independent

`with_metadata_of` exposes the separation particularly clearly.

The method:

- keeps the data-pointer value of `self`;
- discards `self`'s old metadata;
- takes metadata from another pointer;
- produces a pointer shaped by that metadata; and
- retains the provenance of `self`.

The documentation explicitly warns that provenance from the two pointers is **not combined**. Its negative example constructs an address numerically pointing at one object while retaining provenance for another; dereferencing the result is UB.

For Anneal, a proof that metadata was copied from a valid pointer does not justify the data address. Conversely, a data pointer with sufficient provenance does not establish that supplied metadata describes the intended DST.

Basis: **core-library documentation/source** in `with_metadata_of`; decomposition is **derived**.

### Slice metadata is an element count, not a byte count

For `[T]`, metadata is a `usize` number of elements. For `str`, metadata is a `usize` number of bytes.

Those units must remain distinct. A slice pointer's dynamic byte span depends on both metadata and the element layout. The pointer-metadata API itself does not establish that the corresponding byte range is live or contained in one allocation.

The bundled Reference says slice metadata must be a valid `usize`. It adds an `isize::MAX` total-size validity constraint for wide **references and `Box`**, but does not state that stronger condition for a raw slice pointer merely to exist as a value.

Later operations can impose stronger bounds. In particular, creating a slice reference or performing memory access must satisfy the relevant range/liveness rules.

Basis: **core-library documentation** + **normative Reference**; distinction about raw-pointer versus reference/`Box` wording is **derived directly from the scoped rule**.

### Trait-object metadata is vtable metadata for the erased concrete type

For `dyn Trait`, `Pointee::Metadata` is `DynMetadata<dyn Trait>`.

`DynMetadata` contains a pointer to a compiler-generated vtable carrying at least:

- size;
- alignment;
- `drop_in_place` implementation; and
- method pointers for the trait implementation.

The `from_raw_parts` documentation requires trait-object metadata to originate from a pointer to the same underlying erased type. This is stronger than "some vtable for the same trait."

The Reference also says `dyn Trait` wide metadata must be a compiler-generated vtable for the trait. It marks this requirement as still debated **for raw pointers**, so a durable verifier should preserve that uncertainty rather than treating the raw-pointer validity rule as fully settled.

Basis: **source/documentation** + **normative Reference with explicit uncertainty**.

### `DynMetadata::size_of` is not the complete dynamic size of every enclosing DST

`DynMetadata::size_of` reads the size associated with the vtable; `align_of` reads its alignment; `layout` combines them.

The source contains an important caveat. For a value such as a DST whose tail is `dyn Send`, the vtable size is the size of the concrete **tail** represented by the vtable, not necessarily the result of `size_of_val_raw` for the enclosing DST.

Therefore, given metadata for a struct with an unsized trait-object tail, `metadata.size_of()` is not by itself a formula for the full struct's dynamic allocation size. The sized prefix, field offset, padding, and DST layout rules still matter.

This is a common place where a superficially plausible "vtable size = object size" abstraction becomes wrong.

Basis: **source comment and implementation** in `DynMetadata`; full-DST consequence is **derived**.

### Vtable pointer equality is not a reliable type-identity test

`DynMetadata` implements equality/ordering/hash in terms of the underlying vtable pointer, but its documentation warns against interpreting equality as concrete type identity.

Two vtables for the same concrete type/trait can have different addresses because they can be duplicated across codegen units. Conversely, vtables for different concrete types/traits can have equal addresses if identical vtables are deduplicated.

A verifier or diagnostic that needs semantic concrete-type identity therefore cannot use `DynMetadata` pointer equality as a complete oracle.

Basis: **core-library documentation/source**.

### Wide raw-pointer bit validity is weaker and less settled than reference validity

The bundled Reference says metadata of a wide reference, `Box<T>`, or raw pointer must match the unsized tail type.

For slices, metadata must be a valid `usize`. For `dyn Trait`, metadata is described as a compiler-generated vtable for the trait, with an explicit note that the raw-pointer case remains debated.

The same Reference section imposes stronger general validity on references and `Box`: they must be aligned, non-null, non-dangling, and point to a valid dynamic value. A raw pointer does not acquire all of those obligations merely because it is wide.

This supports a layered model:

1. wide raw-pointer value/metadata validity;
2. data-pointer provenance/range for an intended operation;
3. dynamic layout derived from metadata;
4. typed value validity; and
5. stronger reference/`Box` aliasing and liveness invariants.

Basis: **normative Reference** + **derived layering**.

### Raw wide-pointer comparisons include metadata

The Reference says raw pointers compare by address, and when comparing raw pointers to dynamically sized types their additional data is also compared.

For slices, that means pointers with the same data address but different lengths need not compare equal as wide raw pointers. For trait objects, metadata comparison inherits the vtable-address caveat above.

Do not collapse wide raw-pointer equality to data-address equality when reproducing Rust-level comparison semantics.

Basis: **normative Reference** + `DynMetadata` **documentation** for the vtable caveat.

### Metadata replacement does not validate a resulting DST

`with_metadata_of`, `from_raw_parts`, and `from_raw_parts_mut` can construct combinations whose later dereference is invalid. The safe construction APIs deliberately postpone those obligations.

Examples of independent later failure modes include:

- data pointer provenance does not authorize the dynamic range;
- slice length makes a later access cross the allocation;
- data address is not suitably aligned for the actual dynamic value;
- trait-object metadata describes a different erased concrete type;
- the pointed-to bytes do not satisfy the actual dynamic type's validity requirements; or
- conversion to a reference violates aliasing/liveness rules.

Thus a metadata operation should be modeled as **pointer construction**, not as a checked DST cast.

Basis: **source/documentation** + **derived synthesis**.

### The public API is unstable, but the compiler semantic split is already explicit

At the selected revision, `ptr_metadata` gates the public re-export of `Pointee`, `Thin`, `metadata`, `from_raw_parts`, `from_raw_parts_mut`, and `DynMetadata`. `to_raw_parts` is likewise unstable under the pointer-metadata feature. `with_metadata_of` uses the separate `set_ptr_value` feature.

This affects what ordinary stable Rust source can call, not the existence of wide-pointer metadata in the language/compiler. Slices, strings, trait objects, and DST structs already rely on the data-plus-metadata representation boundary.

For Anneal, source feature support and semantic modeling should be recorded separately: rejecting an unstable library API does not remove the need to model compiler-generated wide pointers.

Basis: **source attributes** + **derived tool-design consequence**.

## Boundaries

**No fresh execution.** No compiler, Miri, Charon, Aeneas, or Lean probe was run.

**No complete DST layout report.** This report states metadata meanings and reconstruction rules. It does not derive complete struct/slice/trait-object layout or field offsets.

**No complete trait-object ABI commitment.** The core library documents vtable contents needed by `DynMetadata`, but this report does not claim a stable external ABI or a fixed serialized vtable layout.

**Raw `dyn Trait` metadata validity is explicitly unsettled.** The pinned Reference marks the raw-pointer requirement as debated. The report preserves that boundary.

**No blanket raw-slice `isize::MAX` bit-validity claim.** The pinned Reference's explicit total-size restriction is stated for wide references and `Box`. Later raw-pointer operations can still impose range/offset/access constraints.

**Metadata does not grant provenance.** This is established concretely by `with_metadata_of`; the report does not invent a more detailed provenance algebra.

**No claim that `DynMetadata` equality identifies the concrete type.** Upstream documentation explicitly rejects that inference.

**No claim that vtable size is the whole enclosing DST size.** The source specifically warns otherwise for unsized tails.

**No source-version continuity.** Revalidate these unstable APIs and the bundled Reference for another revision.

## Evidence

Evidence was materially revalidated on 2026-09-27.

Primary Rust subject:

- `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`
  - `library/core/src/ptr/metadata.rs`, blob `1eeadf1217b5f94b48a33de62cd82ad47941890c`: `Pointee`, metadata mapping, `Thin`, `metadata`, raw-parts constructors, `DynMetadata`, vtable semantics, size/alignment/layout, and vtable comparison caveats.
  - `library/core/src/ptr/const_ptr.rs`, blob `5cbbebf9f478819ee80e0c6486d622ae9ffdac00`: `to_raw_parts`, `with_metadata_of`, data-pointer/provenance behavior.
  - `library/core/src/ptr/mut_ptr.rs`, blob `53ef7f754d201a1dc08aa50a320266a8ab55245f`: mutable counterparts.
  - `library/core/src/ptr/mod.rs`, blob `ff2c18d685b65832c296731f23f1664779b874f2`: public feature-gated pointer-metadata re-export and general pointer/provenance model.

Bundled normative Reference:

- `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`
  - `src/types/pointer.md`, blob `ffd234a3b77dbb4d34f58b4e0b366a79ca7cc2f1`: raw-pointer semantics and comparison behavior for DST pointers.
  - `src/behavior-considered-undefined.md`, blob `373052061c50fc2f6d1c07a91960d40bac505284`: wide metadata bit-validity rules, the debated raw `dyn Trait` case, slice metadata, and stronger reference/`Box` validity.

Current neighboring corpus evidence was used only to maintain scope boundaries:

- `reports/rust-validity-well-defined-execution-nightly-2026-05-31` owns the broad typed-value/well-defined-execution boundary.
- Charon's current raw-pointer report records that the selected translation represents data pointer and metadata separately; that downstream representation does not replace the Rust source-language contract here.

Evidence roles are **source/documentation**, **normative Reference**, and **derived synthesis**. There is no fresh **execution** evidence.

## Revalidation

For another Rust revision:

1. inspect `library/core/src/ptr/metadata.rs` and diff the `Pointee::Metadata` mapping;
2. check whether `ptr_metadata` remains unstable and whether API signatures changed;
3. revalidate `from_raw_parts`' trait-object same-erased-type requirement;
4. inspect `DynMetadata`'s documented vtable contents, equality caveat, and `size_of` tail-size warning;
5. inspect `const_ptr.rs` and `mut_ptr.rs` for `to_raw_parts` and `with_metadata_of`, especially provenance wording;
6. inspect the bundled Reference's wide-metadata validity rules and whether the raw `dyn Trait` uncertainty has been resolved;
7. recheck which pointer categories, if any, carry a total-dynamic-size bound merely as a value-validity rule; and
8. recheck wide raw-pointer equality/comparison semantics.

A focused exact-toolchain probe can cheaply strengthen the report:

- round-trip `*const [u32]` through `to_raw_parts`/`from_raw_parts` and verify length metadata;
- construct two raw slice pointers with the same data address and different lengths and record pointer-comparison behavior;
- round-trip a `*const dyn Trait` and inspect `DynMetadata::{size_of, align_of, layout}`;
- use a DST struct with a sized prefix plus `dyn Trait` tail to demonstrate that `DynMetadata::size_of()` reports the tail concrete type rather than the entire dynamic struct;
- use `with_metadata_of` to combine one data pointer with another pointer's metadata, including a negative dereference case where provenance does not authorize the resulting address;
- compare vtable metadata in more than one codegen configuration, treating any equality pattern as execution evidence rather than semantic type identity; and
- exercise oversized slice metadata only in ways that do not prematurely form an invalid reference, then separately test the stronger reference-formation boundary.

Preserve exact commands, compiler/Miri versions, source, diagnostics, and generated IR if execution evidence is added. Miri behavior should be labeled as model/tool evidence where the Reference still marks semantics unsettled.
