# `NonNull` semantics at nightly-2026-05-31

## Summary

At `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `NonNull<T>` is not an owned or dereferenceable pointer abstraction. Its defining extra value invariant over an ordinary raw pointer is much narrower: the pointer value must never be null. It may still dangle, be unusable for an access, carry insufficient provenance, refer to uninitialized storage, or fail the stronger requirements for forming `&T` or `&mut T`.

That non-null invariant has two important consequences. First, creating `NonNull<T>` through `new_unchecked` from a null raw pointer is immediate undefined behavior even if the pointer is never dereferenced. Second, the standard library guarantees the null-pointer optimization: `Option<NonNull<T>>` has the same size and alignment as `NonNull<T>` for the examples and contract documented by the type. The forbidden null representation can encode `None`.

`NonNull<T>` is deliberately covariant in `T`, unlike `*mut T`. That is convenient for pointer-owning data structures, but it is not always sound for a user-defined abstraction that exposes mutation of `T`. Such an abstraction can need an explicit invariant marker such as `PhantomData<Cell<T>>`. `NonNull<T>` is also explicitly neither `Send` nor `Sync`; the type does not itself establish thread-safe ownership or exclusive access.

The type preserves the same provenance/address distinction as raw pointers. `addr`, `with_addr`, and `map_addr` follow Strict Provenance; `without_provenance` creates a non-null address-only pointer with no allocation authority; exposed-provenance APIs retain the ordinary integer-round-trip uncertainty. `NonNull::dangling()` is a particularly useful counterexample to the idea that non-null means usable: it returns a well-aligned, non-null, provenance-free pointer intended for lazy-allocation bookkeeping, and its address can coincidentally equal the address of live storage. The documentation therefore forbids using it as a unique “not initialized” sentinel.

Safe conversion from `&T` to `NonNull<T>` does not grant write permission. The type-level documentation explicitly warns that a `NonNull<T>` derived from a shared reference must not be used to mutate the referent or create a mutable reference unless the mutation is inside an `UnsafeCell`. `as_ptr` returning `*mut T` changes the raw pointer type, not the provenance/aliasing authority from which the pointer came.

For verification, model `NonNull<T>` as a raw-pointer-like value plus a permanent **non-null representation invariant**, not as “valid pointer to T.” Then separately prove the operation-specific obligations for provenance/range, alignment, initialization, aliasing, lifetime, metadata, and ownership when the value is actually used.

This report is based on the exact pinned core-library source/documentation and bundled Rust Reference. No fresh rustc or Miri execution was performed.

## Applicability

This report applies to:

- `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, the compiler/core-library revision associated with Anneal's relevant `nightly-2026-05-31`; and
- `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`, the Reference revision examined with that compiler tree.

The primary implementation/documentation subject is `core::ptr::NonNull<T>` in `library/core/src/ptr/non_null.rs`. The report covers its value invariant, representation contract, variance, thread-marker behavior, constructors/conversions, Strict/Exposed Provenance APIs, `dangling`, raw-pointer exposure, reference conversion, and the way its convenience methods inherit raw-pointer safety contracts.

This report intentionally does not duplicate the complete contracts of pointer arithmetic, raw reads/writes, bulk copy, wide-pointer metadata, raw-slice construction, or general reference creation. Those are separate #3720 subjects. Here those operations appear only to establish what `NonNull<T>` adds—or does not add—to the underlying raw-pointer obligations.

The Rust Reference says the full pointer provenance and aliasing model remains incomplete. The pinned core documentation nevertheless gives strong API contracts that are enough for the distinctions in this report. Where the report synthesizes a verification rule from those contracts, that synthesis is labeled **derived** rather than presented as a complete formal Rust memory model.

## Findings

### The permanent type invariant is non-nullness, not dereferenceability

The `NonNull<T>` type documentation describes the type as a raw mutable pointer that is non-zero. It states that, unlike `*mut T`, the pointer must always be non-null even if it is never dereferenced. The actual representation is a transparent wrapper around a compiler-recognized non-null pointer pattern.

This is a **value invariant**. `new_unchecked` therefore requires its raw pointer argument to be non-null; violating that precondition is undefined behavior at construction time. The implementation contains an unsafe-precondition assertion, but that assertion is diagnostic machinery rather than a replacement for the semantic precondition. `new` is the safe constructor because it tests nullness and returns `None` instead of constructing an invalid `NonNull<T>`.

No constructor-level check establishes the broader properties needed for later access. A non-null raw address can still be dangling, misaligned for a requested access, outside a live allocation, or carry no usable provenance. `NonNull::new` filters only nullness.

Basis: **documentation + source** in `library/core/src/ptr/non_null.rs`; the separation between value validity and later access is also consistent with the bundled Reference's invalid-value and pointer-access rules.

### `NonNull::dangling` deliberately demonstrates that non-null is weaker than “valid for access”

For sized `T`, `NonNull::dangling()` constructs a non-null pointer at an address based on `align_of::<T>()`, using `without_provenance`. Its documentation calls the result dangling but well-aligned and gives lazy allocation as its intended bookkeeping use.

Two consequences matter for verification:

1. `dangling()` does not carry allocation provenance and must not be dereferenced for an ordinary non-zero-sized access merely because it is aligned and non-null.
2. Its numeric address can coincidentally be the address of live storage. The documentation explicitly says this means it must not be used as a “not initialized yet” sentinel. Allocation state must be tracked separately.

This is a reusable counterexample to three invalid implications:

```text
non-null => allocated            false
aligned  => dereferenceable      false
same address as live object => same access authority   false
```

Basis: **documentation + source** in `NonNull::dangling` and the pinned `core::ptr` provenance documentation. The three-line implication table is **derived** synthesis.

### The null-pointer optimization is a representation guarantee, not an access guarantee

The type is `#[repr(transparent)]` and marked by rustc as having the non-null optimization guarantee. The type documentation guarantees that `NonNull<T>` and `Option<NonNull<T>>` have the same size and alignment in the stated representation contract, including examples for a thin pointer and `str`.

The optimization is possible because the null representation is unavailable to a valid `NonNull<T>` and can therefore encode `None`.

Do not invert that fact into an access guarantee. A value occupying the non-null niche can still be dangling or provenance-free. The representation fact says which bit/pointer state is forbidden for the wrapper; it does not prove that every other state is dereferenceable.

Basis: **documentation + source** in the `NonNull` representation declaration; the last distinction is **derived**.

### `NonNull<T>` is covariant, which can be unsound for mutation-exposing abstractions

The pinned type documentation explicitly says `NonNull<T>` is covariant over `T`. It also explains the engineering consequence: if a user-defined type exposes mutation through a `NonNull<T>` and that mutation could exploit lifetime subtyping, the enclosing type may need an additional invariant field such as `PhantomData<Cell<T>>` or `PhantomData<&'a mut T>`.

The bundled Reference defines covariance as allowing subtype relations to pass through a generic constructor and notes that `*const T` is covariant while `*mut T` is invariant. `NonNull<T>`'s implementation is transparently built over a const-pointer-shaped non-null representation, which is consistent with its documented covariance.

A verifier should therefore not infer “mutable pointer type implies invariant in `T`.” The public abstraction is covariant even though `as_ptr` produces `*mut T` and mutation convenience operations exist. Soundness of a higher-level mutable container must account for the variance of its fields separately.

Basis: **documentation + source** in `non_null.rs` and **normative** variance definitions in the bundled Rust Reference.

### `NonNull<T>` is explicitly neither `Send` nor `Sync`

The exact source has negative implementations of both `Send` and `Sync` for `NonNull<T>`, with comments explaining that the referenced data may be aliased.

That prevents treating the wrapper alone as evidence of transferable ownership or cross-thread shared safety. Higher-level pointer-owning types such as `Box`, `Vec`, `Rc`, or custom containers establish their own auto-trait behavior from stronger invariants; the raw non-null wrapper does not supply those invariants itself.

For Anneal, this should remain a distinct proposition from provenance and aliasing. “Pointer is non-null and can be copied” does not imply “pointer may safely cross a thread boundary.”

Basis: **source** in the explicit negative impls; the final sentence is **derived**.

### Safe conversion from a shared reference does not grant mutability

`NonNull::from_ref` and `From<&T> for NonNull<T>` are safe and infallible because a Rust reference is non-null. The resulting wrapper nevertheless exposes an underlying `*mut T` through `as_ptr`.

The type-level documentation addresses the apparent mismatch directly: mutating through a pointer derived from a shared reference remains undefined behavior unless the relevant bytes are inside `UnsafeCell<T>`. The same applies to manufacturing a mutable reference from such a shared-reference-derived pointer. Code using that conversion is responsible for ensuring that `as_mut` is not called and that `as_ptr` is not used for unauthorized mutation.

Thus `as_ptr: NonNull<T> -> *mut T` is a representation/API conversion. It does not upgrade the mutability component of provenance or erase the aliasing restrictions inherited from the original shared reference.

Basis: **documentation + source** in the type-level `NonNull` docs and `from_ref` / `as_ptr`; the provenance phrasing is **derived** from the pinned `core::ptr` model, which says shared-reference provenance does not permit writes except through `UnsafeCell`.

### `Copy` duplicates the pointer value, not ownership of the referent

`NonNull<T>` implements `Copy` and `Clone`. Multiple wrapper values can therefore designate the same address/provenance without any runtime tracking.

That is compatible with the preceding facts because `NonNull<T>` is not an ownership token. Copying it does not establish that multiple mutable accesses are legal, does not duplicate a uniquely owned resource, and does not lengthen the allocation lifetime. Those properties belong to the source provenance and the higher-level abstraction that manages the pointer.

This is particularly important when modeling structures that use `NonNull<T>` internally: the wrapper copy is a pointer-value copy, not a semantic `Clone` of `T` and not proof of alias-safe ownership duplication.

Basis: **source** for `Copy`/`Clone`; ownership consequences are **derived** from the absence of ownership semantics plus the pointer/aliasing contracts.

### Strict Provenance APIs preserve the non-null invariant while keeping address and access authority separate

The selected revision exposes `NonNull` equivalents of the raw-pointer Strict Provenance APIs:

- `addr(self) -> NonZero<usize>` extracts the numeric address. The result can be `NonZero` because the wrapper's permanent invariant excludes address zero.
- `with_addr(self, NonZero<usize>) -> Self` changes the address while carrying the provenance of `self`.
- `map_addr` derives a new non-zero address and delegates to `with_addr`.
- `without_provenance(NonZero<usize>) -> Self` creates a non-null pointer with no provenance.

`without_provenance` is especially important: constructing a valid `NonNull<T>` value does not require allocation provenance. It only requires a non-zero address. Such a value can be valid *as a `NonNull<T>`* while still being unusable for ordinary memory access.

The raw-pointer module states that provenance constrains the memory a pointer may access and that a pointer with absent provenance cannot perform ordinary non-zero-sized memory access. `NonNull` preserves that separation; its non-null value invariant is orthogonal to access authority.

Basis: **documentation + source** in `NonNull::{addr,with_addr,map_addr,without_provenance}` and the pinned `core::ptr` provenance documentation.

### Exposed Provenance carries the same uncertainty as raw pointers

`expose_provenance` returns a non-zero address while conceptually exposing the pointer's provenance; `with_exposed_provenance` constructs a non-null pointer at a non-zero address by attempting to recover some previously exposed provenance.

The `NonNull` methods explicitly defer to the equivalent raw-pointer APIs. The pinned raw-pointer documentation says Exposed Provenance is materially less settled than Strict Provenance, does not specify which exposed provenance will be chosen, and cannot justify an eventual access if no suitable exposed provenance exists.

`NonNull` therefore narrows the resulting address to non-zero but does not make integer-pointer provenance recovery deterministic or formally complete.

Basis: **documentation + source** in `non_null.rs` plus the pinned `core::ptr` Exposed Provenance discussion.

### `as_ref` and `as_mut` require the full raw-pointer-to-reference contract

`NonNull::as_ref` and `NonNull::as_mut` are unsafe. Both state that the pointer must be “convertible to a reference.” Their returned lifetime parameter is chosen by the caller rather than mechanically tied to the lifetime of the `NonNull` wrapper, so the caller must ensure the referent remains valid for the returned reference's lifetime and that aliasing rules are satisfied.

The `NonNull` invariant discharges only one small part of reference formation: non-nullness. It does not by itself prove:

- live allocation coverage/dereferenceability;
- alignment;
- a valid initialized `T` for `as_ref` / `as_mut`;
- shared-versus-unique aliasing conditions;
- a sufficiently long referent lifetime; or
- valid wide-pointer metadata where applicable.

Those requirements belong to the general raw-pointer-to-reference subject and the underlying reference validity rules.

Basis: **documentation + source** in `as_ref`/`as_mut`, plus the bundled Reference's reference validity and aliasing rules. The decomposed obligation list is **derived** and intentionally defers the full reference-creation analysis to its separate corpus subject.

### `as_uninit_ref` / `as_uninit_mut` relax initialization, not reference validity

The selected nightly also has unstable `as_uninit_ref` and `as_uninit_mut` methods for sized `T`. They return references to `MaybeUninit<T>` rather than `T`, so the source storage may be uninitialized.

That does not turn an arbitrary `NonNull<T>` into a reference. The methods still require the pointer to be convertible to a reference: allocation coverage, alignment, lifetime, and aliasing remain relevant. What changes is the pointee validity requirement, because `MaybeUninit<T>` is designed to admit uninitialized representations.

This is a useful semantic split for verification: **reference-valid storage** and **initialized valid `T`** are separate propositions. The `MaybeUninit` view can discharge the latter without weakening the former.

Basis: **documentation + source** in the unstable `as_uninit_ref` / `as_uninit_mut` methods plus the pinned `MaybeUninit` contract; the two-proposition formulation is **derived**.

### Convenience methods inherit raw-pointer operation contracts rather than gaining safety from `NonNull`

The implementation provides methods such as `add`, `sub`, `offset`, `read`, `read_unaligned`, `write`, `copy_to`, and `copy_from`. Their implementations delegate to the corresponding raw-pointer operations and their documentation directs users to those raw-pointer safety contracts.

The wrapper's invariant can remove a null check from reasoning, but it does not discharge range/provenance, alignment, initialization, overlap, or ownership requirements of those operations. For example, `read` still needs a valid aligned initialized `T` to read; `read_unaligned` only relaxes alignment; bulk copies still carry their byte-range/overlap contracts.

The source notably omits wrapping-offset convenience methods with a comment that they are not implemented because wrapping address arithmetic can produce null, which would violate the `NonNull` value invariant. This is a concrete place where the wrapper changes the API surface even though most operation semantics are inherited.

Basis: **source** in `non_null.rs`; detailed operation contracts belong to the dedicated pointer-arithmetic/read-write/copy reports.

### Wide `NonNull` values preserve the non-null data-pointer invariant but metadata remains a separate obligation

`NonNull<T>` supports unsized pointees. The selected revision includes `from_raw_parts` / `to_raw_parts` for metadata-bearing pointers and `NonNull<[T]>::slice_from_raw_parts` for raw slice pointers.

The raw slice constructor is safe because it constructs a raw pointer value rather than a slice reference. Its documentation explicitly says dereferencing remains unsafe; even its `len` accessor is safe when the pointer address is not dereferenceable. Later conversion to a reference imposes the normal slice requirements: a single live allocation range, alignment even for zero-length slices, total size within the required bounds, and aliasing/lifetime conditions.

This illustrates the general rule: `NonNull` can carry wide metadata without asserting that the metadata and address describe a valid referenceable object. The exact validity rules for wide raw-pointer metadata remain partly unsettled in the bundled Reference, so this report does not claim a complete general metadata invariant beyond the API contracts inspected.

Basis: **source/documentation** in `NonNull::{from_raw_parts,to_raw_parts}` and `NonNull<[T]>::slice_from_raw_parts` / reference-conversion helpers; **normative boundary** from the bundled Reference's wide-pointer validity caveat.

### Verification should keep five propositions distinct

A compact verifier model for this subject should distinguish:

1. **Non-null value invariant:** the `NonNull<T>` representation is not null. This must hold whenever the wrapper exists.
2. **Address/provenance state:** what allocation authority, if any, the pointer carries.
3. **Operation-relative access validity:** whether the requested byte range is live, in-bounds as required, and accessible for the operation.
4. **Typed/reference validity:** whether alignment, initialization, metadata, aliasing, and lifetime are sufficient to produce/use `T`, `&T`, or `&mut T`.
5. **Higher-level ownership/concurrency invariant:** whether the enclosing abstraction is allowed to mutate, duplicate, free, or transfer the pointee.

`NonNull<T>` itself establishes proposition 1. Particular constructors may carry additional facts from their inputs—for example a pointer produced from `&mut T` starts from a valid reference—but the wrapper type does not remember those facts as a complete dynamic capability. Later uses must prove the relevant propositions again from the program's invariants.

Basis: **derived** synthesis from the pinned type, provenance, reference-validity, variance, and auto-trait contracts.

## Boundaries

**No complete Rust memory model is claimed.** The bundled Reference and core pointer documentation both preserve uncertainty around the exact provenance/aliasing model. This report uses only the stable/public contracts needed to characterize `NonNull<T>`.

**No ownership is inferred.** `NonNull<T>` is `Copy`, covariant, and neither `Send` nor `Sync`. Higher-level containers can impose stronger ownership/thread-safety invariants, but those are not properties of this wrapper alone.

**No dereferenceability from construction alone.** `new` and `new_unchecked` establish non-nullness only. `dangling` intentionally produces a non-dereferenceable example.

**No mutation authority from `*mut T` exposure.** `as_ptr` returning `*mut T` does not legalize mutation if provenance came from `&T`; the `UnsafeCell` exception remains the ordinary one.

**No complete wide-pointer metadata model.** The Reference says some raw-wide-pointer metadata validity questions remain debated. The report records the inspected APIs without resolving that open semantic area.

**No duplicate coverage of raw pointer primitives.** Pointer arithmetic, reads/writes, bulk copy, reference creation, raw slices, and wide metadata each have broader independent contracts. This report records only what the `NonNull` wrapper adds to or inherits from them.

**Nightly-only APIs are revision-specific.** `as_uninit_ref`, `as_uninit_mut`, metadata helpers, and other unstable methods observed here are exact-pin evidence, not a stable cross-version API promise.

**No fresh execution.** No rustc, Miri, Charon, Aeneas, or Lean probe was run. Source contracts and Reference text are sufficient for the main distinctions, but execution could strengthen diagnostics/revalidation examples.

## Evidence

Evidence was materially acquired or revalidated on 2026-09-27.

Primary core-library subject:

- `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`
  - `library/core/src/ptr/non_null.rs`, blob `86e9d01381a5198a4694137fafa75beb6a4f9f06`: representation/non-null contract; covariance warning; `!Send`/`!Sync`; constructors; `dangling`; Strict/Exposed Provenance methods; reference conversions; raw-pointer exposure; convenience delegation; wide-pointer/slice helpers.
  - `library/core/src/ptr/mod.rs`, blob `ff2c18d685b65832c296731f23f1664779b874f2`: address/provenance model, no-provenance pointers, shared-reference write restrictions, Strict Provenance, and Exposed Provenance caveats.

Bundled language reference:

- `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`
  - `src/behavior-considered-undefined.md`, blob `373052061c50fc2f6d1c07a91960d40bac505284`: invalid-value production, custom valid ranges including `NonNull`, raw-pointer initializedness, reference validity, pointer access, and open aliasing/wide-metadata questions.
  - `src/subtyping.md`, blob `1e9d6c15eaf98d32d45dec52ed9b8cb0a0cefabe`: definitions of covariance/invariance and built-in pointer/reference variance.
  - `src/memory-model.md`, blob `cc3cf02ec0adba12134ad6cb82e51a4b864da784`: incomplete-memory-model warning and abstract bytes.

Current corpus/candidate boundaries were checked so this report would not silently absorb separate subjects. In particular, current adjacent work covers raw-pointer validity, pointer arithmetic, read/write, bulk copy, pointer casts/provenance, wide metadata, `MaybeUninit`, and raw-pointer-to-reference conversion. Those were treated as neighboring evidence/scope boundaries, not as native fulfillment of `NonNull`.

Evidence roles are **normative**, **documentation**, **source**, and **derived**. There is no fresh **execution** evidence.

## Revalidation

For a different Rust revision, revalidate the wrapper before rerunning a broad pointer-semantics survey:

1. Diff the type-level `NonNull` documentation and representation declaration in `library/core/src/ptr/non_null.rs`. Confirm the permanent non-null contract, covariance warning, null-pointer optimization, and `!Send`/`!Sync` status.
2. Recheck `new_unchecked` and `new` to determine exactly what construction establishes.
3. Recheck `dangling`, especially whether it remains provenance-free/well-aligned and whether the “not an initialization sentinel” warning changes.
4. Recheck `from_ref` / `From<&T>` and the shared-reference mutation warning. This is a high-value soundness boundary for abstractions that use `NonNull` internally.
5. Recheck `addr`, `with_addr`, `map_addr`, `without_provenance`, `expose_provenance`, and `with_exposed_provenance` against the raw-pointer provenance documentation.
6. Recheck `as_ptr`, `as_ref`, `as_mut`, and uninitialized-reference helpers. Preserve any changed relationship among non-nullness, initialization, reference conversion, and lifetime obligations.
7. Search convenience methods for operations newly omitted or added because they can create a null pointer; the current source explicitly omits wrapping-offset variants for that reason.
8. Recheck wide-pointer constructors and slice helpers only if Anneal needs those surfaces; compare against the bundled Reference's current metadata-validity statements.
9. Diff `src/subtyping.md` and the Reference invalid-value section for changes to variance or the special valid range attributed to `NonNull`.

A bounded Miri/rustc probe can supplement this source review:

- construct `NonNull::new(null_mut())` and confirm safe rejection;
- attempt `new_unchecked(null_mut())` under Miri and preserve the exact diagnostic;
- create `NonNull::dangling()` and show that safe address/format operations work while an attempted non-zero-sized dereference is rejected;
- derive `NonNull` from `&T` and attempt mutation through `as_ptr` under Miri to exercise the shared-reference boundary; and
- compare `size_of::<NonNull<T>>()` with `size_of::<Option<NonNull<T>>>()` for thin and one wide pointee.

Preserve exact commands, toolchain, target, and diagnostics if these probes are run. They demonstrate checked implementations; they do not replace the pinned API and Reference contracts or settle open aliasing/provenance questions.
