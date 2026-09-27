# Rust reference creation from raw pointers at nightly-2026-05-31

## Summary

At `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, turning a raw pointer into a Rust reference is itself a safety-critical semantic event. It is not enough that a later load or store would happen to be valid. The exact `core::ptr` documentation says that `&*ptr`, `&mut *ptr`, `ptr.as_ref()`, `ptr.as_ref_unchecked()`, `ptr.as_mut()`, and `ptr.as_mut_unchecked()` require the raw pointer to be **convertible to the corresponding reference at the moment the reference is created**, and those requirements apply even when the resulting reference is unused.

For a direct reference to `T`, the pinned core-library contract requires all of the following: proper alignment, non-nullness, dereferenceability of the pointee extent, a valid `T` value, and the appropriate reference-aliasing discipline. Dereferenceability is provenance-sensitive: the relevant byte range must lie within the allocation authorized by the pointer's provenance. Shared and mutable references then impose different ongoing restrictions. While a shared reference is live, its pointed-to memory cannot be mutated except through `UnsafeCell`; while a mutable reference is live, the memory cannot be accessed through other non-derived pointers/references and no other reference may point to it. The Reference explicitly says Rust's exact aliasing rules remain unsettled, so these rules are a current minimum/overview rather than a complete final aliasing model.

The raw-pointer APIs do not tie the returned lifetime to another safe input lifetime. Their `unsafe fn` signatures return an inferred generic `'a`; the caller must therefore ensure that the allocation, pointee validity, and aliasing facts hold for the lifetime the returned reference is actually used with. A numerically correct address is not enough, and a short-lived or unused reference is not exempt from the creation-time validity rules.

The pinned API provides a narrower escape hatch for uninitialized storage: `as_uninit_ref` / `as_uninit_mut` return references to `MaybeUninit<T>`. That changes the referent type so initialized/valid-`T` contents are not required, but it does **not** eliminate the reference obligations for the `MaybeUninit<T>` object itself: non-nullness when a reference is produced, alignment, live dereferenceable storage, lifetime, and shared-versus-mutable aliasing restrictions still apply.

For Anneal and unsafe-code review, the reusable rule is: **prove reference formation, not merely eventual access**. If the available facts justify only a raw pointer, keep a raw pointer. Use `&raw` rather than `&`/`&mut` for misaligned, uninitialized, or alias-sensitive places, and delay reference creation until every reference invariant can be established for the intended lifetime.

This report is specification/source based. No fresh rustc or Miri execution was performed.

## Applicability

This report applies to:

- `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, the compiler/core-library revision associated with Anneal's Charon Rust nightly `nightly-2026-05-31`; and
- `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`, the Rust Reference revision bundled by that compiler source tree.

The scope is **reference formation from raw pointers**. It covers direct shared and mutable references, the stable `as_ref`/`as_mut` families, the unstable `as_uninit_ref`/`as_uninit_mut` boundary where it clarifies initialization, and the distinction between ordinary and raw borrow operators.

Adjacent corpus subjects remain separate:

- raw-pointer value validity, provenance, and general access validity are covered by the dedicated raw-pointer validity report candidate;
- pointer arithmetic, reads/writes, copies, casts, and wide-pointer metadata each have distinct inventory items;
- `slice::from_raw_parts` / `slice::from_raw_parts_mut` and `ptr::slice_from_raw_parts` have their own slice-specific inventory items;
- `MaybeUninit` has its own inventory item; this report uses it only to explain what changing the referent type does and does not relax; and
- a complete normative aliasing model does not currently exist in the Reference.

The phrase **convertible to a reference** below follows the exact pinned `core::ptr` terminology. It denotes the conditions needed to create a shared or mutable reference from a raw pointer; it is intentionally stronger than raw-pointer value validity and stronger than merely having a matching numerical address.

## Findings

### Reference formation has its own immediate safety contract

The pinned `core::ptr` module has a dedicated **Pointer to reference conversion** section. For conversions such as `&*ptr` and `&mut *ptr`, it requires:

1. proper alignment;
2. non-nullness;
3. dereferenceability;
4. a valid pointee value of type `T`; and
5. the appropriate Rust aliasing discipline.

The documentation then makes the timing explicit: **these rules apply even if the result is unused**.

That last rule is important for verification. An argument of the form “the code creates an invalid reference but never dereferences it” does not discharge the safety obligation. Producing the reference is already the operation that requires the invariants.

The bundled Reference reaches the same boundary from two directions. Its invalid-value rules require references to be aligned, non-null, non-dangling, and to point to a valid value. Its raw-borrow section warns that using `&` / `&mut` on a misaligned or invalid place, or where reference aliasing assumptions would be wrong, is undefined behavior even though a raw pointer to that place can still be constructed.

Basis: **source/documentation** in `library/core/src/ptr/mod.rs` plus **normative** Rust Reference rules in `behavior-considered-undefined.md` and `expressions/operator-expr.md`.

### A raw pointer's address does not establish dereferenceability

The same `core::ptr` module defines dereferenceability in provenance-sensitive terms. For a non-zero-sized access, the relevant memory range must be entirely inside the allocation identified by the raw pointer's provenance. Rust treats distinct stack variables as distinct allocations for this purpose.

Therefore, proving that `ptr.addr()` or an integer cast numerically falls inside a live object is not enough. The raw pointer must carry access authority for the allocation and range that the eventual reference denotes.

For a direct `&T` or `&mut T`, the relevant extent is the pointee value. Dynamically sized references additionally depend on their metadata and dynamic extent; those metadata-specific rules are delegated to the wide-pointer and slice reports.

Basis: **source/documentation** in `library/core/src/ptr/mod.rs`; the “address alone is insufficient” conclusion is **derived** from its explicit provenance-based definition of dereferenceability.

### Shared and mutable references impose ongoing, different aliasing obligations

Reference creation does not only validate a snapshot of bytes. It creates a reference whose existence constrains later accesses.

At this pin, `core::ptr` summarizes the rule as follows:

- for a mutable reference, while the reference exists, the pointed-to memory must not be read or written through any other pointer/reference not derived from that reference;
- for a shared reference, while the reference exists, the pointed-to memory must not be mutated except inside `UnsafeCell`.

The bundled Reference gives the same general outline and explicitly says the **exact aliasing rules are not determined yet**. It also states bounds on reference liveness: a reference cannot be live longer than the syntactic lifetime assigned by the borrow checker; dereference, reborrow, passing, and returning can make it live, with additional call-duration constraints for passed references.

For Anneal, this means an unsafe proof should not replace the concrete creation site with a vague statement such as “the pointer does not alias.” It should identify which kind of reference is being created, what competing pointers/references exist, which are derived from the new reference, where `UnsafeCell` may permit mutation, and how long the returned reference can remain live.

Do not strengthen this into a claim that the Reference fully specifies Stacked Borrows, Tree Borrows, or another operational aliasing model. It does not.

Basis: **source/documentation** in `core::ptr` + **normative but explicitly incomplete** aliasing guidance in the Rust Reference.

### The returned lifetime is an unsafe caller obligation, not something recovered from the raw pointer

`*const T::as_ref`, `*const T::as_ref_unchecked`, `*mut T::as_ref`, `*mut T::as_mut`, and the corresponding unchecked methods all return a reference with a generic lifetime `'a` that is not tied by the type signature to a safe borrowed input.

For example, the pinned signatures have the shapes:

```rust
pub const unsafe fn as_ref<'a>(self) -> Option<&'a T>
pub const unsafe fn as_ref_unchecked<'a>(self) -> &'a T
pub const unsafe fn as_mut<'a>(self) -> Option<&'a mut T>
pub const unsafe fn as_mut_unchecked<'a>(self) -> &'a mut T
```

The caller therefore cannot treat a successful null check or raw-pointer provenance as automatically choosing the right lifetime. The allocation and referenced value must remain live, and the corresponding aliasing restrictions must be upheld, for the lifetime in which the produced reference is considered live.

A helper that returns `&'a T` from a raw pointer should normally tie `'a` to some trusted owner/borrow in its API or otherwise have an explicit safety contract establishing why that lifetime is valid. Merely accepting `*const T` does not provide such a relationship.

Basis: **source** in `const_ptr.rs` / `mut_ptr.rs` + **normative** reference liveness bounds; API-design consequence is **derived**.

### `as_ref` and `as_mut` only discharge the null branch

The stable nullable conversion methods are still unsafe:

- `ptr.as_ref()` returns `None` when `ptr` is null; otherwise the pointer must be convertible to a shared reference.
- `ptr.as_mut()` returns `None` when `ptr` is null; otherwise the pointer must be convertible to a mutable reference.

The checked null branch does not validate alignment, provenance/range, pointee validity, aliasing, or lifetime for an arbitrary non-null pointer. The unchecked variants remove only the nullable result and require convertibility unconditionally.

This is a useful review distinction. Code such as:

```rust
unsafe { ptr.as_ref() }
```

is not justified by “`as_ref` handles null.” Its proof must establish the disjunction in the API contract: **null, or fully convertible to a reference**.

During const evaluation these nullable methods can also panic if nullness cannot be determined. That is an exact API behavior at this pin, but it does not change their runtime safety contract.

Basis: **source/documentation** in `docs/as_ref.md`, `const_ptr.rs`, and `mut_ptr.rs`.

### `&raw` is the construction mechanism when reference invariants are not yet available

The Reference distinguishes ordinary borrow operators from raw borrow operators.

`&` and `&mut` produce references and place the location into the corresponding borrowed state. `&raw const` and `&raw mut` instead produce raw pointers. The Reference says raw borrows **must** be used when the place can be misaligned, can contain a value invalid for its declared type, or when creating a reference would introduce incorrect aliasing assumptions.

Its examples show both important cases:

- taking `&packed.f2` for a potentially unaligned packed field would create an invalid reference, while `&raw const packed.f2` is permitted; and
- taking a reference to an uninitialized `bool` field would be UB, while a raw pointer can be formed and later initialized with a raw-pointer write.

This gives a practical rule for generated proof scaffolding and unsafe Rust: **do not create a reference merely to obtain an address**. If the operation needs only a raw address/place, form a raw pointer and keep it raw until reference invariants actually hold.

Basis: **normative** Rust Reference, `expressions/operator-expr.md`.

### Uninitialized storage changes the referent type, not the other reference obligations

At this pin, the unstable `as_uninit_ref` and `as_uninit_mut` methods let raw pointers produce references to `MaybeUninit<T>`. The documentation states the exact relaxation: unlike `as_ref` / `as_mut`, the pointee does not have to be initialized as a `T` because the created reference is to `MaybeUninit<T>`.

The conversion still creates an ordinary Rust reference. The pointer therefore still has to meet the reference requirements for the new referent type: appropriate alignment, non-nullness when a reference is produced, dereferenceable live storage, lifetime, and shared-versus-mutable aliasing obligations.

This avoids a common invalid inference:

```text
storage may be uninitialized
therefore a reference to it has no validity/aliasing/lifetime requirements
```

The correct inference is narrower:

```text
storage may be uninitialized as T
therefore use a referent type whose validity permits that state
while still proving the reference itself is sound
```

The separate `MaybeUninit` report owns the full initialized/uninitialized-value contract.

Basis: **source/documentation** in `docs/as_uninit_ref.md`, `const_ptr.rs`, and `mut_ptr.rs`; decomposition of the remaining obligations is **derived** from `core::ptr`'s reference-conversion contract.

### Zero-sized pointees do not make null or misaligned references valid

The Reference's dangling definition has a special zero-size rule: if the pointed-to size is zero, the pointer is trivially not dangling, even if the raw pointer itself is null. That does **not** make a null reference valid, because reference validity separately requires non-nullness and alignment.

Similarly, the core-library conversion contract requires proper alignment even where no bytes are touched. A verifier should therefore not justify `&*ptr` merely with `size_of::<T>() == 0`.

For a zero-sized direct reference, the byte-extent/liveness part can become vacuous, but the independent reference-value requirements remain. Pointee validity can also matter for zero-sized types: for example, Rust's uninhabited `!` type cannot have a value at all.

Basis: **normative** Reference invalid-value/dangling rules + **source/documentation** `core::ptr` alignment/reference-conversion rules; decomposition is **derived**.

### Pointee validity at creation is the conservative contract, with an explicit standards uncertainty

The exact pinned `core::ptr` conversion section requires the pointer to point to a valid value of `T` and says the rules apply even if the result is unused. It immediately notes that the initialized-value part is “not yet fully decided,” while recommending initialization as the only safe approach.

The bundled Reference likewise says a reference must point to a valid value, but marks that last requirement as still under debate.

The durable conclusion is therefore deliberately conservative:

- **for code intended to be sound under the selected toolchain's documented contract, establish an initialized, valid `T` before creating `&T` or `&mut T`;**
- if the storage is intentionally not yet a valid `T`, keep it raw or use a reference to an appropriate wrapper such as `MaybeUninit<T>` when that wrapper's own reference invariants are satisfied; and
- do not present the exact frontier of reference pointee-validity as permanently settled Rust language semantics.

Basis: **source/documentation + normative specification with explicit uncertainty**.

### A useful proof obligation is “reference-ready over lifetime L,” not “pointer looks valid”

For an unsafe verification interface, the evidence above supports a structured obligation for creating a direct reference from a raw pointer:

```text
ReferenceReadyShared<T>(p, L):
  p is non-null
  p is aligned for T
  p's provenance authorizes the full pointee extent
  the extent stays in live storage for L
  the storage denotes a valid T at creation
  shared-reference mutation restrictions hold while live in L

ReferenceReadyMut<T>(p, L):
  p is non-null
  p is aligned for T
  p's provenance authorizes the full pointee extent
  the extent stays in live storage for L
  the storage denotes a valid T at creation
  mutable-reference exclusivity restrictions hold while live in L
```

This is not proposed as a new normative Rust predicate. It is a **derived review decomposition** of the selected documentation. Its value is that each conjunct has a different evidence source and failure mode. In particular, address/provenance, object lifetime, bit/value validity, and aliasing should not be collapsed into one opaque “valid pointer” assertion.

For dynamically sized `T`, the pointee extent and validity additionally depend on metadata; those details belong in the corresponding wide-pointer/slice reports.

Basis: **derived** synthesis from the preceding normative/source obligations.

## Boundaries

**Exact aliasing semantics remain unresolved.** The Reference and `core::ptr` both say the exact aliasing rules are not fully determined. This report preserves their current minimum/overview rules and does not make Stacked Borrows, Tree Borrows, Miri, or another operational model normative.

**Pointee-validity-at-reference-creation is explicitly debated.** The selected core documentation still requires a valid `T` and recommends initialization as the only safe approach; the Reference marks the exact point as under debate. This report records the conservative selected-toolchain contract rather than claiming the debate is closed.

**Slice construction is not exhaustively covered.** `slice::from_raw_parts` and `slice::from_raw_parts_mut` add range, single-allocation, length/metadata, total-size, and slice-wide aliasing obligations. They have separate inventory coverage. This report establishes the common reference-formation boundary only.

**Wide trait-object references are not exhaustively covered.** Metadata compatibility and vtable identity belong in the wide-pointer report. A raw pointer to a DST can be a valid raw-pointer value under conditions weaker than those needed for a reference to that DST.

**`MaybeUninit` is not exhaustively covered.** The report uses `as_uninit_ref`/`as_uninit_mut` only to show that changing the referent type can relax pointee-value initialization without relaxing unrelated reference requirements.

**No fresh execution.** No rustc, Miri, Charon, Aeneas, or Lean process was run. No claim here depends on experimental Miri behavior.

**No claim that arbitrary raw-pointer dereference syntax immediately performs a memory access.** The Reference distinguishes place formation, raw borrowing, loading/storing, and reference creation. This report is specifically about the reference-creation event and does not replace the read/write or place-projection reports.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-27.

Primary compiler/core-library subject: `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`.

- `library/core/src/ptr/mod.rs`, blob `ff2c18d685b65832c296731f23f1664779b874f2` — pointer access/dereferenceability model, alignment, explicit pointer-to-reference conversion contract, aliasing overview, and the rule that conversion requirements apply even if the result is unused.
- `library/core/src/ptr/const_ptr.rs`, blob `5cbbebf9f478819ee80e0c6486d622ae9ffdac00` — `*const T::{as_ref, as_ref_unchecked, as_uninit_ref}` signatures and implementations.
- `library/core/src/ptr/mut_ptr.rs`, blob `53ef7f754d201a1dc08aa50a320266a8ab55245f` — `*mut T::{as_ref, as_mut, as_ref_unchecked, as_mut_unchecked, as_uninit_mut}` contracts and implementations.
- `library/core/src/ptr/docs/as_ref.md`, blob `2c7d6e149b76a5ec0f58677eaa51925d57aac041` — nullable shared-reference conversion safety condition.
- `library/core/src/ptr/docs/as_uninit_ref.md`, blob `5b9a1ecb85b91e3d8668352a1169983d36574d80` — explicit relaxation for uninitialized storage when the produced referent type is `MaybeUninit<T>`.

Bundled normative subject: `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`.

- `src/types/pointer.md`, blob `ffd234a3b77dbb4d34f58b4e0b366a79ca7cc2f1` — distinction between raw pointers and references, raw-pointer dereference unsafety, and `&*` / `&mut *` conversion.
- `src/expressions/operator-expr.md`, blob `6c5e4ffbf1532597c3ffe9a800ca80e0fb3cec8a` — ordinary borrow semantics, raw-borrow semantics, and concrete misalignment/uninitialized examples where reference creation is UB but raw-pointer construction is allowed.
- `src/behavior-considered-undefined.md`, blob `373052061c50fc2f6d1c07a91960d40bac505284` — current aliasing outline, reference liveness bounds, dangling definition, reference validity, wide-reference metadata constraints, and explicit unresolved-validity notes.

Related current/reference work used only for scope boundaries:

- `rust-validity-well-defined-execution-nightly-2026-05-31` — broad validity versus well-defined execution;
- current raw-pointer validity candidate — operation-relative pointer validity/provenance/alignment;
- current wide-pointer metadata candidate — DST metadata and data-pointer/provenance separation.

There is no fresh **execution** evidence in this package.

## Revalidation

For another Rust revision, the cheapest discriminating revalidation is:

1. inspect `library/core/src/ptr/mod.rs` around **Pointer to reference conversion** and record any changes to alignment, non-nullness, dereferenceability, pointee validity, aliasing, or the “even if unused” rule;
2. inspect `const_ptr.rs`, `mut_ptr.rs`, and their included docs for the exact `as_ref` / `as_mut` / unchecked / uninitialized-reference signatures and safety text;
3. diff the Reference's `behavior-considered-undefined.md` sections on aliasing, dangling pointers, and invalid reference values;
4. diff `expressions/operator-expr.md` around ordinary versus raw borrows; and
5. if any rule has moved from “unresolved” to a more precise normative statement, update this report rather than silently retaining the older conservative boundary.

A compact execution-strengthening probe can then check diagnostics/Miri behavior without making that behavior normative:

- create but never use a reference from a null pointer;
- create but never use a reference from a misaligned pointer;
- create a raw pointer with `&raw` to a packed field and use `read_unaligned`;
- create `&T` from intentionally uninitialized storage versus `&MaybeUninit<T>` over the same storage;
- keep a shared or mutable reference live while attempting a conflicting raw-pointer access; and
- include a zero-sized pointee case to prevent byte-count reasoning from accidentally dropping the independent non-null/alignment rules.

Preserve exact compiler revision, command line, source, diagnostics/Miri output, and whether the probe observes language diagnostics, Miri's current operational model, or both. A successful probe only strengthens the observed behavior of that exact toolchain; it does not resolve the Reference's acknowledged aliasing/validity uncertainties.
