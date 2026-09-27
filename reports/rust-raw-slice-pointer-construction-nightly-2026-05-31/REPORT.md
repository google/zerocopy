# Raw slice-pointer construction with `ptr::slice_from_raw_parts`

## Summary

At `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`nightly-2026-05-31`), `ptr::slice_from_raw_parts` and `ptr::slice_from_raw_parts_mut` are **safe constructors for raw wide slice pointers**. They combine a thin data pointer with a `usize` element count. They do not create a slice reference, read or write memory, check an allocation, require a non-null or aligned address, establish initialization, or establish shared/mutable aliasing rights.

That distinction is observable in the pinned API. The standard-library documentation constructs a raw slice from a null pointer and then reads its length; the raw-slice `len()` method is explicitly safe even when the pointer is null or unaligned. By contrast, turning the same raw wide pointer into `&[T]` or `&mut [T]` immediately incurs the stronger slice-reference contract: non-nullness and alignment even for empty/ZST slices, one-allocation coverage of the byte range, initialized `T` values, a total size no greater than `isize::MAX`, non-wrapping range arithmetic, and the appropriate aliasing/lifetime conditions.

The length is metadata, not evidence. `len = N` says that the wide pointer carries slice metadata `N`; it does not prove that `N` elements exist at the data pointer. The mutable constructor similarly does not prove exclusivity. A verifier should model these functions as metadata attachment to a raw pointer and defer memory-validity and aliasing obligations until an operation actually requires them.

The pinned Reference supports this separation. Slice metadata in a raw wide pointer must be a valid `usize`; the stronger `isize::MAX` metadata-validity restriction is stated specifically for wide references and `Box<T>`. Raw pointers have no liveness guarantee, and accesses through dangling or misaligned pointers are undefined. Thus a raw slice pointer can be constructible and inspectable while being unusable for dereference or reference formation.

Basis: pinned core-library **source/documentation** plus the bundled Rust Reference as **normative** language documentation. No fresh rustc or Miri execution was performed.

## Applicability

This report covers the stable free functions:

```rust
pub const fn ptr::slice_from_raw_parts<T>(data: *const T, len: usize) -> *const [T]
pub const fn ptr::slice_from_raw_parts_mut<T>(data: *mut T, len: usize) -> *mut [T]
```

at `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`. Both functions have been stable since Rust 1.42. The immutable constructor is const-stable since 1.64; the mutable constructor is const-stable since 1.83, so both are usable in const contexts at this selected nightly subject to const-evaluation rules.

The bundled Reference subject is `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`.

This report is deliberately about **raw slice-pointer construction**, not `slice::from_raw_parts` or `slice::from_raw_parts_mut`. The latter create references and are unsafe because their contracts must hold at reference formation. Wide-pointer metadata in general, raw-pointer provenance/validity in general, and reference creation from raw pointers have adjacent corpus subjects; they are used here only to draw the precise boundary around this operation.

At this pin, the unstable `*const T::cast_slice(len)` / `*mut T::cast_slice(len)` methods are thin wrappers around the same free functions under feature `ptr_cast_slice`. The general `ptr::from_raw_parts` / `from_raw_parts_mut` metadata constructors are still unstable under `ptr_metadata`; the slice-specific free functions are the stable surface.

## Findings

### Construction attaches a `usize` element count to the supplied data pointer

The implementation is intentionally small:

```rust
pub const fn slice_from_raw_parts<T>(data: *const T, len: usize) -> *const [T] {
    from_raw_parts(data, len)
}

pub const fn slice_from_raw_parts_mut<T>(data: *mut T, len: usize) -> *mut [T] {
    from_raw_parts_mut(data, len)
}
```

The pinned pointer-metadata implementation defines `[T]` metadata as the length in **items** as a `usize`. The general `from_raw_parts` family is documented as forming a possibly-wide raw pointer from a data pointer and metadata, while warning that the result is not necessarily safe to dereference.

Therefore the primitive operation can be modeled as:

```text
(data raw pointer, element_count: usize) -> raw pointer to [T] carrying element_count metadata
```

It is not a memory-range validation operation. The `len` argument is explicitly an element count, not a byte count.

Basis: **source/documentation** in pinned `library/core/src/ptr/mod.rs` and `library/core/src/ptr/metadata.rs`.

### Null or unaligned data does not make raw construction itself unsafe

Both constructors are safe functions. Their documentation says that actually using the returned value can be unsafe and defers slice-reference requirements to `slice::from_raw_parts` / `_mut`.

The pinned raw-slice methods make the boundary concrete. `*const [T]::len()` and `*mut [T]::len()` are safe even when the raw slice cannot become a slice reference because the data pointer is null or unaligned. Their examples construct a raw slice pointer with a null data pointer and length 3, then read back length 3.

This is stronger evidence than a null-plus-empty special case: the raw pointer can carry nonzero slice metadata while its data pointer is null. It remains a raw pointer. What fails is a later operation that demands a valid referent.

Basis: **source/documentation** in pinned `library/core/src/ptr/const_ptr.rs`, `mut_ptr.rs`, and `mod.rs`.

### A raw slice length is metadata, not a proof that the range exists

A raw pointer has no safety or liveness guarantee in the bundled Reference. For dynamically sized pointers, the extra data participates in the pointer representation; pointers to slices store the number of elements.

For raw wide slice pointers, the Reference's value-validity rule requires slice metadata to be a valid `usize`. Since the constructor receives `len: usize`, every ordinary function argument already satisfies that scalar-validity condition. The Reference places the additional condition that slice metadata not imply a dynamic size greater than `isize::MAX` specifically on wide references and `Box<T>`, not on raw slice-pointer values.

This does not make an oversized or otherwise impossible raw slice dereferenceable. The Reference separately defines a pointer as dangling when the bytes it points to are not all in one live allocation, notes that DST pointers describe their entire dynamic range, and makes accesses through dangling or misaligned pointers undefined. A raw slice can therefore carry metadata that describes a range the pointer does not authorize.

Derived verification rule: **do not turn `len` into an allocation fact merely because it appears in `*const [T]` / `*mut [T]` metadata**.

Basis: bundled Rust Reference **normative** documentation plus **derived** consequence for verification.

### Construction does not create or repair provenance

The stable slice constructor passes the supplied data pointer into the general raw-parts constructor and supplies `len` as metadata. The general constructor is explicitly safe while warning that its result may not be safe to dereference.

The construction therefore does not establish that the data pointer has provenance authorizing access to `len * size_of::<T>()` bytes. A null pointer, a dangling pointer, a one-past pointer, or another pointer insufficient for a later access can still be packaged with slice metadata. The provenance/access obligation remains attached to the eventual operation that uses the data address.

This report does not claim a complete formal provenance model; the bundled Reference leaves parts of pointer semantics unsettled. The narrow conclusion needed here is source-level: adding slice metadata is not documented or implemented as an operation that manufactures access authority.

Basis: **source/documentation** in `ptr::slice_from_raw_parts` and `ptr::from_raw_parts`; broader provenance boundary from the bundled Reference.

### The mutable constructor does not establish exclusivity

`ptr::slice_from_raw_parts_mut` is also safe and performs the same metadata construction while returning `*mut [T]`. It does not create an `&mut [T]`, so it does not by itself impose the exclusive-access lifetime associated with a mutable reference.

The contrast is visible in `slice::from_raw_parts_mut`. That unsafe function requires the memory range to be valid for reads and writes, requires initialized `T` values, and requires that the memory not be accessed through any other non-derived pointer for the lifetime of the returned mutable slice.

Derived verification rule: **`*mut [T]` is a raw-pointer capability, not proof of unique ownership**. Exclusivity must be justified when an operation requires it, most notably when forming a mutable reference or performing an access whose validity depends on aliasing rules.

Basis: **source/documentation** in pinned `library/core/src/ptr/mod.rs` and `library/core/src/slice/raw.rs`; **derived** verification consequence.

### Forming a slice reference activates the stronger range contract

`slice::from_raw_parts` and `slice::from_raw_parts_mut` make the boundary explicit. At this pin, their safety contracts require, as applicable:

- a non-null and properly aligned data pointer, including for zero-length slices and ZSTs;
- the complete slice memory range to lie within one allocation;
- validity for reads, and for the mutable form reads and writes, over `len * size_of::<T>()` bytes;
- `len` consecutive properly initialized values of `T`;
- total byte size no greater than `isize::MAX` and non-wrapping address calculation; and
- shared/mutable lifetime and aliasing discipline.

The implementation of `slice::from_raw_parts` performs the final reference formation as `&*ptr::slice_from_raw_parts(data, len)`, and the mutable form analogously uses `&mut *ptr::slice_from_raw_parts_mut(data, len)`. This is a useful semantic decomposition: safe raw metadata construction first, unsafe reference formation second.

This also explains the empty-slice edge case. `ptr::slice_from_raw_parts(null, 0)` is a permissible raw-pointer construction, but `&*` of that pointer does not become valid merely because the length is zero; a slice reference must still use a non-null aligned data pointer.

Basis: **source/documentation** in pinned `library/core/src/slice/raw.rs` and `library/core/src/ptr/mod.rs`.

### One-allocation and initialization requirements belong to the consumer, not the constructor

The slice-reference contract forbids stitching two adjacent allocations into one slice, even when their addresses happen to be contiguous. It also requires initialized `T` values. Neither condition is checked or promised by `ptr::slice_from_raw_parts`.

This matters for verification pipelines that model the constructor as if it were `slice::from_raw_parts`. Doing so would introduce false obligations at raw-pointer construction and could also incorrectly discharge later obligations after seeing that construction succeed. The correct split is:

1. raw constructor: form data-plus-length metadata;
2. raw metadata inspection: may inspect `len` without validating the data range;
3. access/reference conversion: prove the operation-specific range, provenance, initialization, alignment, and aliasing conditions.

Basis: **source/documentation** plus **derived** phase separation.

### The unstable `cast_slice` methods are aliases, not a different semantic primitive

At this pin, `*const T::cast_slice(len)` and `*mut T::cast_slice(len)` are unstable under `ptr_cast_slice`. Their bodies call `slice_from_raw_parts(self, len)` and `slice_from_raw_parts_mut(self, len)` respectively. Their documentation repeats the same safe-construction/unsafe-use distinction and null-pointer example.

A translator that sees these methods after feature-enabled Rust lowering should therefore not infer stronger safety facts than it would for the stable free functions. The semantic distinction is API surface, not memory validity.

Basis: **source/documentation** in pinned `const_ptr.rs` and `mut_ptr.rs`.

## Boundaries

**No fresh execution.** No rustc, Miri, Charon, Aeneas, or Lean process was run. Checked-in documentation examples and source were inspected; they were not executed in this investigation.

**No complete provenance model.** The report establishes that raw slice construction does not itself certify a dereferenceable range. It does not settle Rust's full provenance or aliasing model, which remains partially unspecified in the Reference.

**Raw-pointer value validity is narrower than dereference validity.** The claim that a `usize` length can be carried as raw-slice metadata should not be turned into a claim that all subsequent operations on the pointer are defined. Operation-specific contracts still apply.

**`slice::from_raw_parts` is adjacent, not the subject.** Its contract appears here only to identify when stronger obligations arise. A separate report can own reference-formation details.

**No claim that mutable raw pointers imply uniqueness.** They do not create a mutable reference. The exact aliasing rules are still not fully specified, but the absence of an exclusive-reference creation at this operation is direct.

**No generalization across revisions.** `ptr_cast_slice` is unstable at this pin, and pointer-validity wording can change. Revalidate before applying the details to another Rust revision.

## Evidence

Evidence was materially revalidated on 2026-09-27.

### Core library

Subject: `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`.

- `library/core/src/ptr/mod.rs`, blob `ff2c18d685b65832c296731f23f1664779b874f2`
  - `slice_from_raw_parts` and `slice_from_raw_parts_mut` signatures, stability, const stability, safe-construction/unsafe-use documentation, null-pointer examples, and delegation to raw-parts constructors.
- `library/core/src/ptr/metadata.rs`, blob `1eeadf1217b5f94b48a33de62cd82ad47941890c`
  - pointer data/metadata decomposition;
  - `[T]` metadata as item count `usize`;
  - general `from_raw_parts` / `_mut` statement that construction is safe while dereference may not be.
- `library/core/src/ptr/const_ptr.rs`, blob `5cbbebf9f478819ee80e0c6486d622ae9ffdac00`
  - unstable `cast_slice` wrapper;
  - stable raw-slice `len()` / `is_empty()` and explicit safety for null/unaligned raw pointers;
  - null pointer with length 3 example.
- `library/core/src/ptr/mut_ptr.rs`, blob `53ef7f754d201a1dc08aa50a320266a8ab55245f`
  - mutable counterparts of `cast_slice`, `len()`, and `is_empty()` with the same raw-pointer boundary.
- `library/core/src/slice/raw.rs`, blob `80b2176933dab215bef525076ceb9089c04389cb`
  - `slice::from_raw_parts` / `_mut` safety contracts and implementation through raw slice-pointer construction followed by reference formation.

### Bundled Rust Reference

Subject: `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`.

- `src/types/pointer.md`, blob `ffd234a3b77dbb4d34f58b4e0b366a79ca7cc2f1`
  - raw pointers have no safety/liveness guarantees;
  - DST raw-pointer comparisons include additional data;
  - thin raw-pointer value-validity boundary.
- `src/dynamically-sized-types.md`, blob `cd90adb75dc4dc9bd4c7af8ea24a1b5ca7dd7b0b`
  - slice pointers carry element-count metadata.
- `src/behavior-considered-undefined.md`, blob `373052061c50fc2f6d1c07a91960d40bac505284`
  - dangling/misaligned access UB;
  - DST ranges and allocation-size discussion;
  - raw-pointer scalar initialization validity;
  - wide-pointer metadata rules, including slice metadata as `usize` and the stronger `isize::MAX` condition for wide references and `Box<T>`;
  - unresolved aliasing boundaries.

No evidence above is fresh **execution** evidence.

## Revalidation

For another Rust revision, the cheapest reliable check is narrow:

1. inspect `library/core/src/ptr/mod.rs` and confirm both free functions remain safe, preserve the same argument/return types, and still delegate to raw-parts construction without validation;
2. inspect `library/core/src/ptr/metadata.rs` and confirm `[T]` metadata remains item-count `usize` and raw-parts construction remains safe-but-not-necessarily-dereferenceable;
3. inspect raw-slice `len()` in `const_ptr.rs` / `mut_ptr.rs` and confirm metadata inspection remains safe for null/unaligned pointers;
4. inspect `slice/raw.rs` for the then-current reference-formation contract, especially non-null/alignment rules for empty/ZST slices, one-allocation coverage, initialization, byte-size bounds, and mutable exclusivity;
5. inspect the bundled Reference's wide-pointer metadata and dangling/access wording, because that is where raw-pointer value validity can diverge from reference validity; and
6. if `ptr_cast_slice` has stabilized or changed, confirm whether it remains a thin alias of the same primitive.

A focused exact-toolchain execution probe can strengthen the report without replacing the source contract:

- construct `*const [u8]` and `*mut [u8]` from null data pointers with nonzero lengths and read `len()`;
- construct raw slices with deliberately unaligned data and read only metadata;
- demonstrate that converting null raw slices, including length zero, to references is rejected by Miri or another appropriate model;
- contrast a valid in-allocation raw slice with a raw slice whose metadata extends past the allocation; and
- include ZST cases to keep byte-size and element-count reasoning separate.

Record the exact rustc/Miri revisions and treat Miri results as **execution/model evidence**, not as a substitute for the Reference where language rules remain unsettled.
