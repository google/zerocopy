# `Box` raw conversions at Rust nightly-2026-05-31

## Summary

`Box::into_raw` is an ownership handoff, not a temporary pointer borrow. It consumes a `Box<T>`, suppresses the box destructor, and returns a non-null, properly aligned raw pointer whose pointee and allocation are now the caller's responsibility. `Box::from_raw` performs the inverse handoff only when the pointer still satisfies the `Box<T>` allocation, layout, value-validity, and ownership requirements. Reconstructing two owning boxes from one allocation can double-free it; losing the pointer returned by `into_raw` leaks the allocation unless the caller performs equivalent destruction and deallocation manually.

The same structure applies to allocator-aware and `NonNull` variants. The allocator-aware `into_*_with_allocator` APIs return the allocator together with the pointer because correct destruction includes deallocation through the allocator that owns the allocation. The `NonNull` forms encode non-nullness but do not discharge the remaining layout, validity, ownership, or allocator obligations.

These APIs are defined for `T: ?Sized`. For slices and trait objects, raw-pointer metadata is therefore part of the reconstruction contract: `Box` destruction computes the pointee layout from the raw pointer, so changing metadata can change the layout used for deallocation even if the data address is unchanged. A type-changing `into_raw`/cast/`from_raw` sequence needs a proof of compatible layout, metadata, value validity, and ownership; address equality alone is insufficient.

This matters directly to current zerocopy. One path constructs a `Box` from `NonNull::dangling()` for zero-sized values and from `alloc_zeroed` storage for non-zero-sized values. A test helper converts `Box<T>` to a raw pointer, casts it to `*mut ReadOnly<T>`, and reconstructs a box under an explicit same-layout and same-bit-validity justification. Those are examples of the two distinct proof patterns the standard-library contract requires.

## Applicability

Anneal currently selects the Rust distribution dated `2026-05-31`. The exact standard-library source examined here is:

```text
rust-lang/rust
f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1
1.98.0-nightly
library/alloc/src/boxed.rs
blob bd3f10a16dd9b27870c28db0a34bc9b569a36634
```

The current reference corpus independently identifies that rustc revision as the nightly used for the same toolchain date. The current zerocopy call sites examined here are at:

```text
google/zerocopy
41f5b37afe7060fd9fe08c00b200672cd76d77b9
```

The stable global-allocator pair is `Box::into_raw` / `Box::from_raw`. `Box::into_non_null` / `Box::from_non_null` are unstable under `box_vec_non_null` at this revision. `Box::into_raw_with_allocator`, `Box::from_raw_in`, and the allocator-aware `NonNull` variants are unstable under `allocator_api`.

This report is about ownership transfer and reconstruction through `Box` raw-conversion APIs. General allocation API semantics, raw-pointer arithmetic/access rules, `NonNull`'s full contract, and Rust's complete aliasing model are separate subjects.

## Findings

### 1. `into_raw` transfers cleanup responsibility out of `Box`

`Box::into_raw` is safe because it starts from an already-valid `Box<T>`. It consumes the box and returns `*mut T`; the documentation guarantees that the returned pointer is properly aligned and non-null. After the call, however, automatic box cleanup is gone. The caller must either reconstruct an owning box, manually drop the pointee and deallocate the storage using the correct layout/allocator, or intentionally leak it.

The implementation makes the ownership transition concrete. It wraps the box in `ManuallyDrop`, preventing normal destruction, and then produces the raw pointer. The function is marked `#[must_use = "losing the pointer will leak memory"]`.

This separates two properties that verification should not conflate:

- **memory safety at the conversion itself:** `into_raw` is safe;
- **resource correctness afterward:** the caller has acquired a future obligation to destroy/deallocate exactly once unless the leak is intentional.

A verifier that models only dereference safety can therefore miss a material `Box` invariant: a successful conversion can be memory-safe while still leaking ownership permanently.

### 2. `from_raw` creates an owning destructor/deallocator obligation immediately

`Box::from_raw` is unsafe because it turns a raw pointer into a unique owner. After the call, the resulting `Box` owns the pointer. Its destruction drops `T`; for non-zero-sized storage it then deallocates through the box's allocator.

For the global-allocator form, the standard-library memory-layout section requires that non-zero-sized storage come from `Global` with the layout appropriate for the pointee and that the pointer denote a valid value of the right type. Zero-sized values do not require an allocation, but the pointer must still be non-null and sufficiently aligned.

The most important temporal obligation is uniqueness of ownership. Calling `from_raw` twice on the same allocation can construct two owners that both attempt destruction/deallocation. The API documentation calls out double free explicitly. Consequently, a proof of `from_raw` cannot stop at “this address is allocated and aligned”; it must also establish that ownership of this allocation is being transferred exactly once.

### 3. `from_raw` does not validate the caller's proof at runtime

At this revision, the global form delegates to `from_raw_in(raw, Global)`. `from_raw_in` constructs the box with `Unique::new_unchecked(raw)` and stores the supplied allocator. There is no runtime check that the allocation came from that allocator, that the allocation layout matches `T`, that the pointee is a valid `T`, or that no competing owner exists.

Those conditions are therefore trust-boundary inputs to the unsafe operation. A translation or proof system that treats `from_raw` as a constructor with no preconditions would erase precisely the obligations that make the operation unsafe.

### 4. The deallocation layout comes from the pointee, including DST metadata

The raw-conversion implementations are defined on `Box<T>` and `Box<T, A>` for `T: ?Sized`, not only for sized `T`. Box destruction obtains `Layout::for_value_raw(ptr.as_ptr())`; it then calls the stored allocator's `deallocate` when that layout has non-zero size.

For a sized `T`, the type fixes the layout. For a dynamically sized pointee, metadata participates in determining the pointee layout. The raw pointer returned by `into_raw` for `Box<[T]>` or a trait object is therefore not just an address that can be freely reassembled with arbitrary metadata. Changing slice length, vtable metadata, or the destination unsized type can alter the layout/value represented by the pointer and can make later `from_raw` or destruction invalid.

This yields a useful verification rule: **preserve the full wide-pointer identity across an owning raw round trip unless a separate proof establishes a valid type/metadata transformation.**

### 5. Type-changing raw round trips need more than representation-size equality

Current zerocopy contains a test helper with this shape:

```text
Box<T>
  -> Box::into_raw
  -> cast to *mut ReadOnly<T>
  -> Box::from_raw
  -> Box<ReadOnly<T>>
```

The local safety comment justifies the cast by stating that `ReadOnly<T>` has the same layout and bit validity as `T`. That is the right category of proof: the conversion changes the eventual owning box type, so the destination pointer must still describe storage with a compatible box layout and a valid destination value.

For a general type-changing raw round trip, the proof must also preserve the allocator/deallocation contract and any relevant metadata. Merely observing that two raw pointers have the same address does not establish that dropping the reconstructed `Box<U>` is valid.

### 6. Zero-sized `Box` values still require a pointer invariant

The Box memory-layout contract treats zero-sized types specially: no allocation is required, but the box pointer must be non-null and sufficiently aligned. The implementation of Box destruction correspondingly skips deallocation when the computed layout size is zero.

Current zerocopy relies on exactly this distinction. Its zero-sized allocation path constructs a box with `Box::from_raw(NonNull::dangling().as_ptr())`; the adjacent comment cites the non-null/aligned ZST requirement. For non-zero-sized values, the same function obtains storage from `alloc_zeroed`, checks for allocation failure, and then calls `Box::from_raw`.

This is a concrete counterexample to a simplistic rule such as “every `Box::from_raw` pointer must name an allocated byte.” For ZSTs the correct requirement is an appropriate non-null aligned pointer, not a live non-zero allocation.

### 7. Allocator-aware raw conversion must carry allocator identity through the handoff

`Box<T, A>::into_raw_with_allocator` consumes the box and returns `(*mut T, A)`. Its documentation tells the caller to destroy `T` and release memory according to the Box layout, and `from_raw_in` requires that the raw pointer point to memory allocated by the supplied `alloc`.

The pair is deliberately shaped so the allocator value can travel with the raw pointer. Its implementation extracts both the raw pointer and the allocator from a `ManuallyDrop<Box<...>>`; the allocator is not silently replaced with `Global`.

For verification, “allocated somewhere” is therefore insufficient for `from_raw_in`. The allocation must belong to the allocator instance/value whose contract will later be used by the box destructor. Conversely, after `into_raw_with_allocator`, losing the allocator can make correct reconstruction or deallocation impossible even if the pointer itself survives.

### 8. `NonNull` variants remove only the null case

The `into_non_null` and allocator-aware `into_non_null_with_allocator` variants encode the guaranteed non-null result in `NonNull<T>`. Their inverse operations remain unsafe. The global `from_non_null` delegates to `from_raw`; the allocator-aware `from_non_null_in` delegates to `from_raw_in`.

Thus `NonNull` does not prove allocation provenance, layout compatibility, valid `T`, single ownership, or allocator identity. It proves the pointer is non-null. A verifier should preserve the remaining `Box` reconstruction obligations explicitly rather than treating `NonNull<T>` as an owning-pointer type.

### 9. The current aliasing guidance is important but intentionally non-normative

The pinned Box documentation includes a “Considerations for unsafe code” section that explicitly says it is **not normative** and may change. It summarizes the compiler's current behavior by saying that `Box<T>` has `&mut T`-like uniqueness and that raw pointers derived from a box may be invalidated after mutation through, movement of, or mutable borrowing of the box.

The raw conversion implementations themselves contain model-specific code and comments for Miri/Stacked Borrows. `into_raw` intentionally creates the pointer in a way that produces the desired retag; `into_raw_with_allocator` uses a different raw-deref route because the allocator-generic form should not impose the same uniqueness behavior.

These implementation comments are evidence that aliasing/provenance is part of the operation boundary, but they are not a complete normative Rust memory model. Anneal should therefore model the explicit Box ownership/layout contract independently of whichever aliasing model is eventually chosen for raw pointer semantics.

## Boundaries

No fresh rustc or Miri experiments were run for this report. All operation findings come from the exact pinned standard-library source and current zerocopy source. The report does not claim that the non-normative Box aliasing summary is a complete or permanently stable Rust rule.

The report does not attempt to specify every way a raw pointer may be accessed between `into_raw` and `from_raw`; those obligations belong to the raw-pointer validity, provenance, alignment, arithmetic, and read/write subjects. It also does not restate the allocator API's complete safety contract.

The report treats the current zerocopy raw casts only as examples of local proof structure. It does not independently prove every representation or validity claim made by those call sites. In particular, the `ReadOnly<T>` test helper's same-layout/same-bit-validity comment is a local premise, not a theorem established here.

`Box::leak`, `Pin<Box<T>>`, `Box::into_inner`, and uninitialized-box construction are adjacent APIs and are not covered except where their implementation appears in source context. This report also does not infer behavior for Rust revisions adjacent to the pinned nightly.

## Evidence

The primary source is `library/alloc/src/boxed.rs` at `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, blob `bd3f10a16dd9b27870c28db0a34bc9b569a36634`.

The memory-layout section states the Global-allocation/layout/valid-value requirements for non-zero-sized boxes and the non-null/aligned rule for zero-sized boxes. The global raw-conversion implementation documents and implements the ownership handoff in `from_raw` and `into_raw`; the allocator-aware implementation provides the corresponding `from_raw_in` and `into_raw_with_allocator` contracts. `Drop for Box<T, A>` computes `Layout::for_value_raw` and deallocates through the stored allocator only when size is non-zero. `source-map.json` records the exact line ranges.

Current Anneal's `anneal/flake.nix` at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`, sets `rustDate = "2026-05-31"` and downloads the dated rustc, rust-std, rustc-dev, and rust-src distributions. The existing reference package `rust-local-nested-items-nightly-2026-05-31` identifies the corresponding rustc source revision as `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` / `1.98.0-nightly`.

Current zerocopy evidence is pinned to `41f5b37afe7060fd9fe08c00b200672cd76d77b9`. `zerocopy/src/lib.rs`, blob `944f177c0b0bf66ebd136e5f21ae1b4c2bde48b5`, uses the ZST dangling-pointer pattern and the non-ZST global-allocation pattern. `zerocopy/src/impls.rs`, blob `4df786fd2104854e1fa259a63c29cd8781f8a404`, contains the type-changing `Box::into_raw` / pointer cast / `Box::from_raw` test helper.

`raw-conversion-contract.json` records the operation matrix and the cross-cutting ownership/layout rules in machine-readable form.

## Revalidation

For a Rust-nightly upgrade, first resolve the new exact rustc source revision. Re-read `library/alloc/src/boxed.rs` for the memory-layout section, the `from_raw`/`into_raw` implementations, allocator-aware and `NonNull` variants, and `Drop for Box<T, A>`. Diff both documentation and implementation: feature stabilization, aliasing guidance, allocator requirements, or DST layout handling can change independently.

For a zerocopy change, search current source for `Box::into_raw`, `Box::from_raw`, `Box::into_non_null`, `Box::from_non_null`, and allocator-aware variants. For every reconstruction, record the local proof of allocator/layout/value validity and unique ownership. For every type-changing round trip, separately record why the destination pointee type and metadata remain valid for both access and eventual deallocation.

A bounded dynamic probe, if stronger execution evidence is useful, should run under the exact pinned Miri toolchain and include: a normal sized round trip; a ZST dangling-pointer reconstruction; a boxed slice round trip preserving metadata; an intentionally altered slice-length reconstruction expected to be rejected or diagnosed by the chosen model; a custom-allocator round trip using the returned allocator; and a double-reconstruction negative case. Dynamic results should supplement, not replace, the source-level API contract.
