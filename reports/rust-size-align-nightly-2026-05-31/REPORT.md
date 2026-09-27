# Rust `size_of`, `align_of`, `size_of_val`, and `align_of_val` at nightly-2026-05-31

## Summary

At the Rust revision behind Anneal's `nightly-2026-05-31` toolchain, the four stable memory-layout queries divide cleanly into **type-level** and **value-level** operations.

`size_of::<T>()` and `align_of::<T>()` apply to `Sized` types. They return compile-time type properties: the storage stride in bytes and the ABI-required minimum alignment. `size_of::<T>()` is specifically the byte offset between successive `T` values in an array, so it includes any padding needed to make the next array element properly aligned. Rust guarantees that a value's size is a multiple of its alignment; zero-sized values are the special case where size is zero while alignment may still exceed one.

`size_of_val(&x)` and `align_of_val(&x)` accept `T: ?Sized`. For a sized `T`, they report the same geometry as the type-level queries. For a dynamically sized value, they use the reference's runtime shape information. A slice's size follows the array section it represents; a trait object's size and alignment are those of its erased concrete value; and a struct with an unsized tail is measured as the **entire dynamic value**, not merely its tail.

The distinction between pointer layout and pointee layout is essential. `size_of::<&[T]>()` measures the representation of the reference itself. `size_of_val::<[T]>(slice)` measures the dynamically sized `[T]` value behind that reference. Likewise, a trait-object reference is a sized pointer value even though `size_of_val` reports the erased object's dynamic extent.

The value-level safe APIs take references. That matters for unsafe-code verification: the caller has already crossed the Rust reference-validity boundary before these functions run. The implementation converts the reference to the corresponding raw intrinsic and justifies the intrinsic's safety because the input is a reference. Rust also exposes unstable raw-pointer variants with explicit metadata/layout preconditions; those are useful evidence for what dynamic layout computation needs, but they do not make it sound to manufacture a reference merely to call the stable APIs.

These functions report **geometry**, not the rest of Rust's validity model. A returned size does not say that every byte in that extent is initialized, readable as `u8`, part of a field, or semantically meaningful. A returned alignment is an ABI-required minimum, not a provenance, allocation, lifetime, aliasing, or initialization proof. Anneal should therefore model these operations as layout observations while discharging pointer/reference and value-validity obligations separately.

No fresh compiler execution was performed for this report. The findings come from the exact `core` implementation/documentation and a precisely identified Rust Reference revision.

## Applicability

The library/API findings apply to `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`. Charon revision `a535e914f74db4fd9e6be7048f4233270d8945c0`, which Anneal pairs through Aeneas, pins `nightly-2026-05-31`; its `rust-toolchain` file requests that nightly together with `rustc-dev`, `rust-src`, Miri, and LLVM tools.

The language-layout findings in this report use `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`. The report records that Reference revision as a separate subject rather than inferring that an adjacent or current Reference has identical wording.

The four primary APIs are:

- `core::mem::size_of<T>() -> usize`;
- `core::mem::align_of<T>() -> usize`;
- `core::mem::size_of_val<T: ?Sized>(&T) -> usize`; and
- `core::mem::align_of_val<T: ?Sized>(&T) -> usize`.

`size_of` and `align_of` require `T: Sized` through their ordinary generic parameter. `size_of_val` and `align_of_val` explicitly relax that bound with `?Sized`.

This report covers the semantic quantities those APIs expose and the safety boundary around their dynamic forms. It does not attempt to reproduce the complete Rust layout algorithm for every representation, nor does it replace the separate corpus subjects for DST layout, padding/initialization, raw-pointer validity, wide-pointer metadata, or `size_of_val_raw`/`align_of_val_raw` safety.

## Findings

### `size_of::<T>()` reports array stride, not merely field payload

The `core::mem::size_of` documentation defines size as the offset in bytes between successive elements in an array of `T`, including alignment padding. It states the resulting identity directly: for any sized `T` and array length `n`, `[T; n]` has size `n * size_of::<T>()`.

The Rust Reference uses the same semantic definition. It says a value's size is the offset between successive array elements, including alignment padding, and that size is always a multiple of alignment. This formulation captures trailing padding that exists so the next array element begins at a valid address.

A zero-sized type remains an important edge case. The Reference treats zero as a multiple of every alignment and gives `[u16; 0]` as an example that may have size zero while retaining alignment two. Thus these implications are wrong:

```text
size_of::<T>() == 0  =>  align_of::<T>() == 1       // not valid
align_of::<T>() > 1  =>  size_of::<T>() > 0        // not valid
```

The actual relationship is weaker: size is a multiple of alignment, with zero allowed.

At this compiler revision, the stable wrapper returns `SizedTypeProperties::SIZE`; that associated constant is defined as `intrinsics::size_of::<Self>()`. The underlying intrinsic is documented as compile-time-only and uses the same array-stride definition.

Basis: **documentation + normative + source**.

### `align_of::<T>()` reports ABI-required minimum alignment

`core::mem::align_of` returns the ABI-required minimum alignment in bytes. Its documentation distinguishes this from a preferred alignment and says it is the alignment used for struct fields. The stable wrapper returns `SizedTypeProperties::ALIGN`, whose default definition is `intrinsics::align_of::<Self>()`.

The Rust Reference gives two additional language-level properties:

- alignment is at least one byte and always a power of two; and
- a value with alignment `n` may only be stored at an address that is a multiple of `n`.

The Reference also makes alignment target-sensitive. Primitive alignment is platform-specific and can be smaller than primitive size; it specifically notes common cases where 128-bit integers or 64-bit values receive smaller alignment on some targets. Code that treats `align_of::<T>() == size_of::<T>()` as a generic law is therefore unsound.

`align_of` is a geometry query. The fact that an address is numerically aligned to the returned value does not establish that a pointer has provenance for an allocation, is dereferenceable, points to initialized storage, satisfies aliasing rules, or is valid for the requested lifetime.

Basis: **documentation + normative + source + derived** separation from independent pointer-validity obligations.

### Type-level size and alignment are constant-evaluable properties of `Sized` types

Both stable type-level wrappers are `const fn`, `#[rustc_promotable]`, and backed by `SizedTypeProperties` constants. The corresponding intrinsics are documented as compile-time-only; code-generation backends do not implement them as ordinary runtime operations.

That implementation detail supports a useful modeling boundary for Anneal. For a fixed compilation subject, `size_of::<T>()` and `align_of::<T>()` are type/layout facts, not observations that require reading a runtime object. This does **not** make their numeric values universally stable. `core::mem::size_of` explicitly warns that type size is generally not stable across compilations except where Rust provides a specific guarantee, and the Reference likewise says type layout may change between compilations subject to documented guarantees.

A proof or cache that specializes these values must therefore bind them to enough target/compiler/layout context to justify reuse. The stable API name by itself does not make an arbitrary user-defined `repr(Rust)` layout part of Rust's cross-version ABI.

Basis: **source + documentation + normative + derived** toolchain-binding consequence.

### `size_of_val` and `align_of_val` extend the same geometry to `?Sized` values

The stable value-level functions accept `&T` where `T: ?Sized`. The `size_of_val` documentation says that its result is usually the same as `size_of::<T>()`, but for a type without statically known size—such as a slice or trait object—it returns the dynamically known size. `align_of_val` analogously returns the ABI-required minimum alignment of the type of the referenced value.

For a `Sized` `T`, the value has one compile-time size and alignment, so the value-level and type-level queries describe the same geometry. The Reference defines `Sized` precisely in these terms: all values of the type have the same size and alignment, both known at compile time.

For a DST, the value-level result depends on runtime shape metadata. This is not a different notion of size or alignment. The Reference says **all values** have size and alignment; `Sized` merely distinguishes the case where those quantities are uniform and statically known for the whole type.

Basis: **documentation + normative + source**.

### A slice's dynamic size follows the array section it represents

The Rust Reference states that an array `[T; N]` has size `size_of::<T>() * N` and alignment equal to `T`'s alignment. It then defines a slice's layout to be the same as the section of the array that it slices.

Therefore, for a valid slice reference of length `n`, `size_of_val::<[T]>(slice)` reports the extent of that `n`-element array section. In particular, this can be zero even when `n != 0` if `T` is zero-sized. The slice's alignment remains the element alignment, so a zero-byte slice value can still carry an alignment greater than one.

For `str`, the Reference states that the value has the same layout as a `[u8]` slice representing its UTF-8 bytes. The dynamic size is therefore its byte extent, not its Unicode scalar-value or grapheme count.

The `core` documentation includes the direct stable example of coercing `[u8; 13]` to `&[u8]` and observing `size_of_val == 13`.

Basis: **normative + documentation + derived** application of the array/slice rules.

### Trait-object queries report the erased concrete value's geometry

The Rust Reference states that a trait object has the same layout as the value the trait object is of. Pointer metadata source makes the mechanism concrete: `DynMetadata<dyn Trait>` represents vtable metadata, and the vtable contains the concrete type's size and alignment.

Accordingly, different `&dyn Trait` values can legitimately produce different dynamic sizes and alignments when they erase different concrete types. A verifier must not substitute `size_of::<&dyn Trait>()` or another pointer-layout quantity for the pointee geometry returned by `size_of_val`.

There is a second distinction for DST structs with a trait-object tail. `DynMetadata::size_of()` explicitly warns that its vtable size is **not** the same as `size_of_val_raw` for the complete outer value. Its example is conceptually `&(i32, dyn Send)`: the vtable stores the size of the `dyn Send` tail's concrete type, while `size_of_val`-style computation concerns the entire dynamically sized outer value, including the statically sized prefix and required layout adjustment.

Basis: **normative + source + derived** API consequence.

### Pointer representation and pointee geometry are separate queries

Pointers and references are themselves `Sized`, including pointers to DSTs. The Reference gives pointer/reference layout its own guarantees and separately describes slices and trait objects as unsized pointees.

This means the following expressions answer different questions:

```rust
size_of::<&[u32]>()   // size of the reference representation
size_of_val(slice)   // size of the [u32] value behind the reference
```

The same separation applies to alignment. `align_of::<&dyn Trait>()` describes the pointer/reference value's alignment; `align_of_val(trait_ref)` describes the erased concrete pointee's alignment.

This distinction is especially relevant to translation layers such as Charon and Aeneas, where data pointer and metadata may become explicit terms. Preserving enough metadata to represent a wide pointer is necessary for dynamic layout, but pointer-representation geometry is not a substitute for the pointee's dynamic geometry.

Basis: **normative + source + derived**.

### Safe value-level queries inherit the reference-validity boundary

The stable dynamic APIs accept `&T`, not a raw pointer. Their implementations call the unsafe `intrinsics::size_of_val` and `intrinsics::align_of_val`; each wrapper's safety comment justifies the call with the fact that `val` is a reference and therefore a valid raw pointer for the intrinsic.

The unstable raw counterparts make the lower-level requirements explicit. For an unsized slice tail, the length metadata must be initialized and the size of the entire value must fit in `isize` except for the documented zero-length special case. For a trait-object tail, the vtable metadata must be a valid vtable obtained through unsizing and the entire value size must fit in `isize`. Other unsized tails are conservatively disallowed, with a documented exception for unstable extern types whose layout may be unknowable.

Those raw-pointer contracts explain why the safe wrappers do not need an `unsafe` block at the call site: a valid Rust reference already carries stronger conditions than an arbitrary raw pointer. They do **not** justify forming a reference from raw components merely to invoke the stable API. Reference creation has independent validity, alignment, lifetime, aliasing, and dereferenceability obligations.

For Anneal, a useful proof decomposition is therefore:

1. establish that the `&T` operand is a valid reference under Rust's rules;
2. extract the dynamic layout from the type plus its valid metadata; and
3. use the returned size/alignment only as geometry facts, without treating them as evidence for unrelated pointer or value validity.

Basis: **source + documentation + derived** proof decomposition.

### Dynamic size is the size of the entire value, including a sized prefix

The raw dynamic-layout documentation repeatedly phrases its bound in terms of the size of the **entire value**: dynamic tail plus statically sized prefix. This matters for custom DST structs whose final field is a slice or trait object.

The Reference permits a DST as the last field of a struct and says that doing so makes the struct itself dynamically sized. The runtime metadata belongs to the tail, but `size_of_val(&outer)` is a query about the outer value. A correct implementation must combine the statically known prefix layout with the tail's dynamic geometry and any alignment/padding required by the complete value.

This is another reason not to identify `DynMetadata::size_of()` with `size_of_val` on an arbitrary outer DST: the former can describe the trait-object tail's concrete type while the latter describes the complete pointee.

Basis: **documentation + normative + source + derived**.

### `size_of` does not imply byte validity or initialization

The APIs expose layout extent. They do not classify the bytes inside that extent.

For example, the size definition deliberately includes alignment padding. Separate Rust rules determine whether padding bytes are initialized, whether reading them is permitted, which bit patterns are valid for a type, and what operations preserve or alter initialization. Likewise, a type can contain niches or invalid bit patterns even though `size_of` reports only an integer extent.

A verifier should therefore resist the tempting inference:

```text
0 <= i < size_of::<T>()  =>  byte i is initialized and freely readable
```

The premise establishes only that the offset lies within the type's reported storage stride. Initialization, provenance, allocation, and typed-value validity require separate evidence.

Basis: **derived**, from the documented geometry contract and the deliberately separate Rust validity/initialization rules. The latter are owned by neighboring corpus subjects rather than rederived here.

### The APIs do not promise cross-compilation layout stability

`size_of` documentation says type size is generally not stable across compilations, while noting specific stable cases such as primitive sizes and `repr(C)` layout when constituent field sizes are stable. The Reference frames its layout chapter similarly: implementations may change layout each compilation except where the language documents a guarantee.

This is not a caveat about whether one invocation returns the right answer. It is a boundary on reusing a numeric answer across subjects. If Anneal stores or proves a concrete `size_of::<T>() == k` fact for a type whose layout lacks a cross-compilation guarantee, that fact belongs to the identified compilation/target semantics unless a stronger language guarantee justifies generalization.

Alignment has the same concern and is additionally target-sensitive even for primitives in ways the Reference documents.

Basis: **documentation + normative + derived** reuse consequence.

## Boundaries

**No fresh execution.** This investigation did not compile a probe, run Miri, inspect LLVM IR, or compare target outputs. The report relies on exact source/documentation and normative Reference text.

**No full layout-algorithm reconstruction.** The report does not enumerate `repr(Rust)`, `repr(C)`, enum niche layout, packed/align interactions, unions, or every compiler layout algorithm. Those details belong to the dedicated struct/enum/union and niche/layout subjects.

**Raw dynamic-layout APIs are supporting evidence, not the primary subject.** `size_of_val_raw` and `align_of_val_raw` are unstable at this revision. Their safety contracts are used to expose the lower-level metadata requirements hidden by the stable reference-taking wrappers. This report does not claim to exhaust their semantics.

**Reference formation remains separate.** The stable APIs taking `&T` cannot be used to bypass the obligations for constructing a valid reference from raw storage.

**No padding-initialization claim.** A reported size includes layout padding where applicable, but says nothing by itself about whether those padding bytes are initialized or can be observed safely.

**No provenance or allocation claim.** Alignment and size do not establish provenance, allocation membership, dereferenceability, ownership, aliasing permission, or lifetime.

**No ABI equivalence claim from equal geometry.** Two types with the same size and alignment need not have the same field layout, valid values, calling convention, or ABI. The Reference explicitly distinguishes type layout from function-call ABI compatibility.

**No adjacent-version continuity.** The report applies only to its identified Rust/compiler and Reference revisions. A later compiler may retain the same stable surface while changing unspecified layout choices or implementation details.

## Evidence

Primary compiler/library subject: `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`.

- `library/core/src/mem/mod.rs`, blob `62c612e7ba2a65bb1645faaa669abd2a1d35a6c2` — stable `size_of`, `size_of_val`, `align_of`, `align_of_val`; unstable raw counterparts and their safety contracts; `SizedTypeProperties::{SIZE, ALIGN}`; documentation for size, alignment, target sensitivity, and dynamic values.
- `library/core/src/intrinsics/mod.rs`, blob `78d7314c58110b49839894a0f69377f4ee0d1204` — compile-time `size_of`/`align_of` intrinsics and unsafe dynamic `size_of_val`/`align_of_val` intrinsics.
- `library/core/src/ptr/metadata.rs`, blob `1eeadf1217b5f94b48a33de62cd82ad47941890c` — wide-pointer metadata categories and `DynMetadata::{size_of, align_of}`, including the explicit warning that vtable tail size is not the same as complete `size_of_val_raw` for an outer DST.

Toolchain-selection evidence:

- `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, `rust-toolchain`, blob `4e348edab20d6bd5b195e758afe20f9d8258a3e1` — selects `nightly-2026-05-31` and its Rust development/source components.

Normative language-layout subject: `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`.

- `src/type-layout.md`, blob `2ee902aef043f4d299e009f6a69d1815d862e69e` — definitions of size/alignment, `Sized`, primitive and pointer layout, array/slice/`str` layout, and trait-object layout.
- `src/dynamically-sized-types.md`, blob `cd90adb75dc4dc9bd4c7af8ea24a1b5ca7dd7b0b` — DST definition, wide-pointer shape, and permission for a DST as the final struct field.

The compiler commit itself was re-read from GitHub and is dated 2026-05-31. No execution evidence is included. Claims that combine API contracts into verification guidance are labeled **derived** in the Findings section.

## Revalidation

For another Rust toolchain or compiler revision, the cheapest reliable revalidation is narrow:

1. Diff `library/core/src/mem/mod.rs` around `size_of`, `align_of`, `size_of_val`, `align_of_val`, both raw dynamic-layout variants, and `SizedTypeProperties`.
2. Diff `library/core/src/intrinsics/mod.rs` around the four corresponding intrinsics, especially any changed safety language or change in compile-time/runtime treatment.
3. Diff `library/core/src/ptr/metadata.rs` if trait-object or DST-tail behavior matters, especially `Pointee` metadata and `DynMetadata::{size_of, align_of}`.
4. Re-read the selected Rust Reference revision's size/alignment, array/slice/`str`, trait-object, and DST sections. Do not assume current Reference text describes an older compiler subject or vice versa.
5. Reconfirm the Anneal/Charon toolchain pin before treating a later Rust revision as the active verification subject.

If source or normative wording changes materially, run a small target-matrix probe on the exact toolchain. Preserve source, target triples, compiler version, and output for at least:

- a sized primitive and a `repr(C)` aggregate with visible internal/trailing padding;
- a zero-sized type with alignment greater than one;
- `[T; N]` and `&[T]`, including a nonempty slice of a zero-sized `T`;
- `&str` with multibyte UTF-8 to distinguish byte size from character count;
- two `&dyn Trait` values with differently sized/aligned concrete types; and
- a struct with a dynamically sized tail, comparing tail metadata geometry with `size_of_val`/`align_of_val` of the whole value.

Run the same cases on every target for which Anneal wants a concrete numeric layout guarantee. A passing probe establishes those cases only; it does not turn unspecified `repr(Rust)` layout into a cross-version contract.
