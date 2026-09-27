# Rust allocation and deallocation contracts at nightly-2026-05-31

## Summary

At the Rust revision behind nightly-2026-05-31, low-level allocation is governed by two related but materially different interfaces. The stable global-allocation functions (`alloc`, `alloc_zeroed`, `realloc`, and `dealloc`) inherit `GlobalAlloc`'s non-zero-size and exact-layout contracts. The unstable `Allocator` interface is deliberately more permissive: it supports zero-sized allocations, can expose an actual allocation size larger than the requested `Layout`, and defines deallocation in terms of a layout that *fits* the allocated block.

The most important lifetime rule is ownership transfer. A successful `realloc`, `Allocator::grow`, or `Allocator::shrink` invalidates the old allocation handle even when the numerical address does not change. A failed resize leaves the old allocation and its contents in place. Deallocation likewise requires the allocation to still be live and to be associated with the allocator that created it.

`Layout` is not itself proof that a request is valid for every allocator. It permits size zero, while `GlobalAlloc::alloc` and `alloc_zeroed` require non-zero size. Its guaranteed invariants are instead alignment and address-space bounds: alignment is non-zero and a power of two, and the size rounded up to that alignment is at most `isize::MAX`.

## Applicability

This report describes the allocation library in `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, the compiler/core-library revision used by the Anneal-era nightly-2026-05-31 baseline preserved elsewhere in the corpus.

The report covers:

- `Layout`;
- the stable global functions in `alloc::alloc`;
- the stable `GlobalAlloc` contract;
- the unstable `Allocator` trait where it materially differs from `GlobalAlloc`; and
- the `Global` adapter that implements `Allocator` on top of the global allocator.

It does not specify `Box` raw conversion, collection capacity invariants, provenance/aliasing rules for later pointer accesses, or a complete implementation-specific allocator model. Those have separate semantic obligations even when they use the allocation interfaces described here.

## Findings

### `Layout` describes size and alignment but permits zero-sized layouts

`Layout::from_size_align` accepts a pair only when alignment is non-zero, alignment is a power of two, and the requested size rounded up to that alignment is at most `isize::MAX`. `Layout::from_size_align_unchecked` makes the caller responsible for the same conditions; violating them is outside that function's safety contract.

The type does **not** require `size() > 0`. Its own documentation calls out the consequence: a zero-sized `Layout` is valid as a `Layout`, even though `GlobalAlloc` requires global allocation requests to have non-zero size.

This distinction is easy to lose in a verifier. “Well-formed `Layout`” and “valid input to this allocator operation” are separate predicates.

Basis: **documentation/source** in `core::alloc::Layout`.

### The stable global functions inherit `GlobalAlloc`, including its zero-size restriction

`alloc`, `alloc_zeroed`, `realloc`, and `dealloc` are thin unsafe wrappers around compiler-provided global-allocator shims. Their safety sections delegate to the corresponding `GlobalAlloc` methods.

For `GlobalAlloc::alloc` and `alloc_zeroed`, the caller must supply a non-zero-size layout. Passing a zero-sized layout is documented as undefined behavior. Allocation failure is represented by a null return unless the allocator chooses a stronger failure mode such as aborting.

`alloc_zeroed` adds one guarantee to successful allocation: the allocated bytes are initialized to zero. That is a byte-initialization guarantee, not a claim that the all-zero bit pattern is a valid value of an arbitrary Rust type. Typed-value validity remains a separate obligation.

Basis: **documentation/source** in `alloc::alloc` and `core::alloc::GlobalAlloc`; the typed-value distinction is **derived** from the interface boundary and neighboring Rust validity rules.

### Deallocation requires allocation identity, liveness, and the matching layout

`GlobalAlloc::dealloc` requires `ptr` to identify a block that is still allocated by that allocator and requires `layout` to be the same layout used for the allocation. Violating either condition is undefined behavior.

The free `dealloc` function forwards this contract unchanged. Its implementation immediately constructs a `NonNull<u8>` with `new_unchecked`, which is consistent with the stronger inherited precondition: a null pointer is not a valid deallocation argument merely because a layout accompanies it.

The reusable rule is therefore stronger than “pointer has an allocated-looking address.” A deallocation obligation includes the allocator relationship, current liveness, and the allocation layout.

Basis: **documentation/source**.

### Successful global reallocation transfers ownership; failed reallocation does not

`GlobalAlloc::realloc` requires the old pointer to denote a block allocated by the same allocator, the old `Layout` to be exactly the allocation layout, `new_size > 0`, and the new size rounded up to the old alignment to remain at most `isize::MAX`.

On a non-null return, ownership of the old block has transferred. The documentation explicitly says that any access through the old pointer is undefined behavior **even if the allocation remained at the same numerical address**. The returned pointer is the handle for subsequent access. The new allocation keeps the old alignment and uses `new_size`; deallocation must use that resulting layout. Bytes in `0..min(old_size, new_size)` preserve their previous values.

On a null return, the transfer did not occur: the old allocation remains allocated and its contents remain unaltered.

This success/failure split is a verification-relevant state transition. A model that treats `realloc` as merely changing a byte-range length misses the ownership handoff and can incorrectly keep both old and new pointers usable after success.

Basis: **documentation/source** in `GlobalAlloc::realloc`.

### Allocation failure is not guaranteed to be a recoverable null or `Err`

`GlobalAlloc` permits implementations that abort on exhaustion rather than return null. The unstable `Allocator` documentation similarly encourages `Err` but explicitly allows implementations backed by native allocators that abort.

`handle_alloc_error` provides a separate “stop here” path. It is guaranteed to diverge, but the mechanism is configuration-dependent: it may panic (and therefore unwind or abort according to panic configuration) or abort directly. At this revision the documented default for programs linked with `std` is to print an error and abort; `no_std` defaults through `panic!` and its panic handler.

A verifier therefore should not encode allocation failure as a single universal control-flow shape. Null/`Err`, panic/unwind, and abort are interface- and configuration-dependent possibilities.

Basis: **documentation/source**.

### `GlobalAlloc` implementations must not unwind

The `GlobalAlloc` safety contract says that unwinding from global-allocator methods is undefined behavior at this revision. Implementations must therefore satisfy a stronger failure constraint than ordinary Rust functions.

This restriction belongs to allocator implementations, not to every caller of allocation code. For example, `handle_alloc_error` has its own documented configuration-dependent panic/abort behavior after an allocation failure has been detected.

Basis: **documentation/source** in `core::alloc::GlobalAlloc` and `alloc::alloc::handle_alloc_error`.

### `Allocator` deliberately differs from `GlobalAlloc` on zero size and layout matching

The unstable `Allocator` trait is not just a typed spelling of `GlobalAlloc`. Its documentation explicitly allows zero-sized allocations. An implementation must convert any underlying allocator's inability to represent them into valid `Allocator` behavior.

It also returns `NonNull<[u8]>`, carrying both a non-null pointer and the actual allocation size. The actual size may exceed `layout.size()`. As a result, later operations use a *fits* relation rather than requiring the exact original `Layout`: the block must still be allocated at the layout's alignment, and `layout.size()` must lie between the originally requested size and the actual returned size.

For the standard `Global` adapter, the runtime implementation does not forward a zero-size request into `GlobalAlloc`. It returns an aligned dangling pointer with slice length zero. For non-zero allocations, its comments note that its own allocation strategy does not return excess capacity, so a fitting layout effectively reduces to the exact original layout at that boundary.

Basis: **documentation/source** in `core::alloc::Allocator` and `alloc::alloc::Global`.

### `Allocator::grow` and `shrink` preserve the same success/failure ownership split

For `Allocator::grow` and `shrink`, the input pointer must denote a currently allocated block from that allocator and the old layout must fit it. `grow` requires the new requested size to be at least the old requested size; `shrink` requires the reverse. The new layout may use a different alignment.

On `Ok`, ownership of the old memory block transfers to the allocator and any access through the old pointer is undefined behavior, even if the operation happened in place. The returned pointer is the new access handle. On `Err`, ownership does not transfer and the old block remains unaltered.

The default implementations make the model visible: allocate a new block, copy the overlap, then deallocate the old block only after allocation succeeds. Implementations may optimize this, but callers may rely on the documented transition rather than on the default algorithm.

Basis: **documentation/source**.

### Zeroing describes bytes, not initialized typed values

Both `GlobalAlloc::alloc_zeroed` and `Allocator::allocate_zeroed` guarantee zeroed bytes in the returned block. `Allocator::grow_zeroed` specifies which newly exposed bytes are guaranteed zero and which already-allocated excess bytes may be preserved or zeroed.

These guarantees are useful for raw storage. They do not establish that interpreting the bytes as an arbitrary `T` is sound. A type may reject the all-zero representation, and pointer/reference creation may impose additional validity, alignment, provenance, and aliasing conditions.

For verification, allocation state and typed-value state should therefore remain separate: “allocated and zero-filled” is not equivalent to “contains a valid value of the eventual type.”

Basis: **documentation/source** for byte guarantees; the typed-state conclusion is **derived**.

### Allocation occurrence itself is not a reliable observable of ordinary optimized code

The `GlobalAlloc` safety documentation warns allocator implementations not to rely on heap allocation calls actually occurring merely because source contains heap-allocating constructs. The optimizer may remove or stack-promote allocations when doing so preserves program behavior, and the documentation explicitly says allocation occurrence is not itself part of program behavior for such reasoning.

This is narrower than saying explicit allocator APIs have no semantics. The reusable boundary is that verification must not justify program behavior from an assumed count of underlying heap allocations unless the relevant API contract independently makes that observation meaningful.

Basis: **documentation**; the boundary statement is **derived** and intentionally conservative.

## Boundaries

**No allocator implementation model.** This report records library contracts, not jemalloc, libc malloc, system allocator, or platform heap internals.

**No complete pointer/provenance model.** Successful allocation establishes a live memory block under these APIs, but later dereference, reference formation, arithmetic, aliasing, provenance, concurrency, and typed-value rules remain separate. Neighboring corpus reports cover those obligations.

**No `Box` ownership report.** `Box` raw conversion and allocator-aware `Box` APIs add ownership obligations beyond this report. They should not be inferred from the raw allocation interface alone.

**No collection-capacity model.** `Vec`, `String`, and other collections may expose capacity or reserve semantics on top of allocators; those abstractions are not examined here.

**`Allocator` is unstable.** Its contract is preserved because it materially explains `Global` and future allocator-aware APIs at this exact revision. Do not infer stability or adjacent-version continuity from this report.

**No fresh execution.** The report did not run allocator probes, Miri, or platform-specific out-of-memory experiments. The central findings are source/documentation contracts and therefore do not require a particular allocator implementation to be observed.

## Evidence

Evidence was acquired on 2026-09-27 from `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`.

- **Documentation/source:** `library/core/src/alloc/layout.rs`, blob `66f5310db83102e28535faf0e4586ba447b4d7a6`, especially `Layout`, `from_size_align`, and `from_size_align_unchecked`: layout well-formedness and zero-size permissibility.
- **Documentation/source:** `library/core/src/alloc/global.rs`, blob `e97398aa5dc4a3f923d014cecc3734906121d0a9`, `GlobalAlloc`: currently-allocated definition, no-unwind requirement, zero-size allocation prohibition, deallocation identity/layout requirements, `alloc_zeroed`, and `realloc` transfer/failure semantics.
- **Documentation/source:** `library/core/src/alloc/mod.rs`, blob `102fb19efc8eabbe32ddb9a5d3a2f7e0ac186b16`, `Allocator`: zero-sized allocation support, currently-allocated and fitting-layout definitions, actual-size return, and grow/shrink transfer semantics.
- **Source/documentation:** `library/alloc/src/alloc.rs`, blob `8729e98278a82c17cf5a6b201246ca04db17dcf6`: stable free-function forwarding, the `Global` adapter's zero-size path, runtime grow/shrink implementation, and `handle_alloc_error` divergence behavior.

Neighboring corpus reports useful when consuming this report include `rust-raw-pointer-validity-provenance-alignment-nightly-2026-05-31`, `rust-nonnull-nightly-2026-05-31`, and the separate `Box` raw-conversion work when published. Those reports provide obligations that allocation alone does not discharge.

## Revalidation

For another Rust revision, inspect four narrow source regions before repeating broader research:

1. `library/core/src/alloc/layout.rs`: confirm `Layout`'s alignment/size invariant and whether zero-size remains permitted.
2. `library/core/src/alloc/global.rs`: compare the `GlobalAlloc` safety section and the contracts of `alloc`, `dealloc`, `alloc_zeroed`, and `realloc`, especially zero-size and successful-resize ownership transfer.
3. `library/core/src/alloc/mod.rs`: compare `Allocator`'s currently-allocated and fitting-layout definitions plus `allocate`, `deallocate`, `grow`, and `shrink`.
4. `library/alloc/src/alloc.rs`: compare the stable forwarding functions, `Global`'s zero-size behavior, and `handle_alloc_error`.

A compact execution probe can supplement the source comparison when allocator implementation behavior matters: use a custom `GlobalAlloc` to record calls for non-zero allocations; separately exercise `Allocator` zero-size behavior, resize success/failure, and allocation-error configuration. Do not use allocation counts as the proof of a language-level observable; the `GlobalAlloc` documentation explicitly warns against that inference.