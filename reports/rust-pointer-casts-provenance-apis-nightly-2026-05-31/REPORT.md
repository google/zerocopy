# Rust raw-pointer casts and provenance APIs at nightly-2026-05-31

## Summary

At the Rust revision behind `nightly-2026-05-31`, a raw pointer is not interchangeable with its numeric address. The pinned `core::ptr` documentation describes a pointer as carrying an address plus provenance: the address identifies a location, while provenance participates in determining which memory accesses that pointer may perform. The stable Strict Provenance APIs make this separation explicit.

`addr()` extracts the address without exposing the pointer's provenance. `with_addr()` and `map_addr()` change the address while retaining the provenance of an existing pointer. `without_provenance()` constructs a pointer with an address but no allocation provenance. These APIs support address manipulation without asking the implementation to infer provenance from an integer.

Ordinary pointer-to-integer casts and `expose_provenance()` take a different path. They return an address and mark the pointer's provenance as exposed. Integer-to-pointer casts and `with_exposed_provenance()` can then pick up some previously exposed provenance, but the exact choice is intentionally unspecified. The core documentation says Exposed Provenance is on materially less solid semantic footing than Strict Provenance and may not work with tools or architectures that track provenance precisely. If no exposed provenance can justify the eventual use of the reconstructed pointer, the program has undefined behavior.

Raw-pointer-to-raw-pointer casts do not grant new access rights. The Reference defines how their data and metadata components are transformed: sized-to-sized casts return the pointer unchanged; wide-to-thin casts discard metadata; compatible wide-to-wide casts preserve the metadata exactly. `cast_mut` and `cast_const` change the raw-pointer mutability marker but do not establish that writes or reads are legal. Alignment, liveness, aliasing, initialization, metadata validity, and provenance obligations arise from later operations and remain separate.

The key verification distinction is therefore **address transformation versus access authority**. A proof that two pointer values have the same address does not establish that they authorize the same access. Conversely, extracting or changing an address through Strict Provenance APIs does not itself dereference memory and can be safe even when the resulting pointer is not usable for a non-zero-sized access.

No fresh rustc or Miri execution was performed. Findings come from the exact pinned Rust Reference and `core::ptr` source/documentation. Existing corpus reports remain authoritative for the broader validity/aliasing and operational-model boundaries; this report isolates the cast/address/provenance interfaces that a verifier must model distinctly.

## Applicability

This report applies to:

- `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, the compiler/core-library revision behind the Anneal-era `nightly-2026-05-31` toolchain; and
- `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`, the exact Reference revision examined with it.

It covers raw-pointer casts and the stable Strict/Exposed Provenance address APIs present at that pin: `addr`, `with_addr`, `map_addr`, `without_provenance`, `expose_provenance`, `with_exposed_provenance`, their mutable counterparts, ordinary raw-pointer `as` casts, and the convenience raw-pointer `cast`/`cast_const`/`cast_mut` methods.

The report does not define Rust's complete pointer-provenance or aliasing model. Both the Reference and `core::ptr` documentation explicitly preserve unresolved areas. The stable conclusion is narrower: provenance is semantically relevant to access, Strict Provenance APIs preserve or deliberately omit it in specified ways, and Exposed Provenance deliberately admits an ambiguous reconstruction mechanism.

Wide-pointer metadata is discussed only where the Reference's cast rules determine what a raw-pointer cast does. Construction and validity of metadata, `DynMetadata`, `from_raw_parts`, vtable correctness, slice lengths, and other wide-pointer obligations belong to the separate wide-pointer metadata subject.

## Findings

### Raw pointers carry access-relevant provenance in addition to an address

The pinned `core::ptr` module documentation states that a pointer conceptually consists of an address plus provenance. Provenance records the origin and access authority of the pointer and participates in deciding which allocation a memory access may target. Equal addresses are therefore not enough to make two pointers interchangeable for access.

The module gives the central example through wrapping arithmetic: a pointer may be moved numerically outside its allocation and later back in while retaining the same provenance. Conversely, changing a pointer's numeric address to equal another allocation's address does not transfer the second allocation's provenance.

This report does not assume a more detailed provenance calculus than the pinned documentation defines. The exact shape of Rust provenance and aliasing remains unsettled; what is stable here is that access legality depends on more than the integer address.

Basis: **documentation** in `library/core/src/ptr/mod.rs` + **normative** Reference UB rules for pointer access.

### `addr()` extracts an address without exposing provenance

For both `*const T` and `*mut T`, `addr()` returns the pointer's address portion and deliberately does **not** expose its provenance. The shared `addr.md` documentation contrasts this with `self as usize`: `addr()` discards provenance but does not make that provenance available to a later integer-to-pointer reconstruction.

The documentation directs code that needs a dereferenceable pointer after address manipulation to retain an original pointer and use `with_addr()` or `map_addr()`. This makes the provenance flow explicit: the integer carries the address, while the retained pointer supplies the provenance.

On the pinned implementation, `addr()` first casts to a thin `*const ()`/`*mut ()` and then performs a sysroot-internal pointer-to-integer transmute. The source comments explicitly warn that the transmute's semantics are an implementation technique with special sysroot status, not a stable public guarantee about arbitrary `transmute`.

Basis: **documentation** in `library/core/src/ptr/docs/addr.md` + **source** in `const_ptr.rs` / `mut_ptr.rs`.

### `with_addr()` and `map_addr()` preserve the source pointer's provenance

`with_addr(addr)` constructs a pointer with the supplied numeric address and the provenance of `self`. The documentation describes it as the Strict Provenance replacement for the ambiguous pattern `addr as *const T` or `addr as *mut T` when an existing pointer with the required provenance is available.

At this revision, `with_addr()` is implemented through a wrapping byte offset from `self`. Its contract therefore inherits the wrapping-arithmetic property: creating the pointer is not itself a claim that the new address is currently in bounds, but later non-zero-sized accesses must still be justified by the retained provenance and the operation's other safety requirements.

`map_addr(f)` is a convenience operation: it computes `f(self.addr())` and then calls `with_addr`, so the address transformation is explicit while provenance continues to come from `self`.

This is the reusable tagged-pointer pattern at this pin. Code may extract low address bits, modify them as integers, and restore the address through `map_addr`; it must not infer that an arbitrary equal numeric address grants access to another allocation.

Basis: **documentation** + **source** in `const_ptr.rs`, `mut_ptr.rs`, and the Strict Provenance section of `ptr/mod.rs`.

### `without_provenance()` deliberately creates an address-only pointer

`without_provenance(addr)` and `without_provenance_mut(addr)` construct thin raw pointers with the given address and no provenance. The core documentation says such a pointer is not associated with any actual allocation. A suitably aligned no-provenance pointer can still participate in zero-sized accesses, but a non-zero-sized memory access through it is undefined behavior.

This API is semantically different from an integer-to-pointer `as` cast. The latter uses the Exposed Provenance model and may pick up a previously exposed provenance; `without_provenance` explicitly does not.

The implementation uses an integer-to-pointer transmute internally and again marks that as a sysroot implementation technique rather than a stable statement about general `transmute` semantics.

Basis: **documentation** + **source** in `library/core/src/ptr/mod.rs`.

### Pointer-to-integer `as` and `expose_provenance()` expose provenance

The Reference says a raw-pointer-to-integer cast produces the machine address, with possible truncation if the integer type is narrower than the pointer representation. The core documentation adds the memory-model effect relevant here: a pointer-to-`usize` cast exposes the pointer's provenance so that an integer-to-pointer reconstruction may later recover some exposed provenance.

`expose_provenance()` is the explicit API for this behavior. It is documented as equivalent to `self as usize`: it returns the address and marks the provenance as exposed. Its implementation casts to a thin unit pointer before the integer cast, so for a wide pointer the exposed/address operation concerns the data-pointer component rather than preserving metadata in the integer.

The important distinction from `addr()` is not the ordinary machine address returned on common platforms; it is the semantic side effect. `addr()` promises not to expose provenance. `expose_provenance()` does expose it.

Basis: **normative** Reference cast rules + **documentation/source** in `const_ptr.rs`, `mut_ptr.rs`, and `ptr/mod.rs`.

### Integer-to-pointer `as` and `with_exposed_provenance()` use an intentionally ambiguous reconstruction

The Reference describes integer-to-raw-pointer casts as interpreting the integer as an address and warns that such pointers interact with a still-developing memory model. The core documentation gives the stronger provenance account used by this toolchain: `with_exposed_provenance(addr)` is fully equivalent to `addr as *const T` (and the mutable form to `addr as *mut T`).

The result may pick up some provenance that was previously exposed by `expose_provenance()` or a pointer-to-integer cast. Memory outside the Rust abstract machine, such as qualifying MMIO memory, is also treated specially as exposed. The exact provenance selected is not specified, and the documentation explicitly says there is no definite specification for which memory the resulting pointer may access.

The ambiguity does not erase ordinary Rust obligations. If no exposed provenance justifies the way the returned pointer is later used, the program has undefined behavior; aliasing invalidation continues to apply even to provenance that was exposed earlier.

This is why Exposed Provenance is not a substitute for a proof that `with_addr` could have supplied. It is an explicit escape hatch for cases where integer-to-pointer reconstruction cannot be avoided, not a deterministic provenance-recovery operator.

Basis: **normative** Reference warning + **documentation/source** in `library/core/src/ptr/mod.rs` and `const_ptr.rs` / `mut_ptr.rs`.

### Strict and Exposed Provenance have materially different verification contracts

For a verifier, the stable APIs divide into three provenance flows:

1. `with_addr` / `map_addr`: retain a specific source pointer's provenance while changing its address;
2. `without_provenance`: create a pointer with no allocation provenance; and
3. `with_exposed_provenance` or an integer-to-pointer `as` cast: ask the implementation to associate the address with some provenance from the exposed-provenance universe.

Only the first flow identifies which existing pointer supplies the provenance. The second supplies none. The third is intentionally under-specified.

A proof system that collapses all three into `usize -> ptr` loses a distinction that the pinned Rust API was designed to expose. Conversely, a proof system need not assign a complete formal semantics to Exposed Provenance merely to be honest: it can reject that path, model it conservatively, or make it an explicit trust/unsupported boundary while providing stronger reasoning for Strict Provenance code.

Basis: **documentation** + **derived** verification consequence.

### Raw-pointer-to-raw-pointer casts transform type/metadata, not access authority

The Reference gives explicit rules for `*const T` / `*mut T` to `*const U` / `*mut U` casts:

- sized-to-sized: the pointer is returned unchanged;
- unsized-to-sized: the data pointer remains and the source metadata is discarded;
- compatible unsized-to-unsized: the pointer is returned unchanged and the metadata is preserved exactly.

Compatibility rules for unsized metadata constrain which wide-to-wide casts are accepted. Slice metadata is always considered compatible, even though preserving the element count while changing the element type can change the number of bytes described. Trait-object casts have stricter rules for the principal trait, auto traits, trailing lifetimes, generics, and associated types. Struct/tuple unsized tails inherit the metadata compatibility of their final field.

The stable `cast<U>()` method is a type-directed convenience implemented as `self as _`. Because `U` is sized in this method, casting a wide pointer through `cast<U>()` keeps the data pointer and discards metadata. It does not check whether the address is aligned for `U`, whether the pointee is valid as `U`, or whether later access is permitted.

Full wide-pointer metadata validity is outside this report; the relevant cast result is only that metadata can be preserved or discarded according to the Reference's cast rules rather than recomputed from memory.

Basis: **normative** Reference `as` cast rules + **source** in `const_ptr.rs` / `mut_ptr.rs`.

### `cast_mut()` and `cast_const()` do not upgrade memory permissions

`*const T::cast_mut()` changes the raw-pointer mutability marker without changing the pointee type. `*mut T::cast_const()` performs the reverse conversion. Both are safe functions and are implemented as raw-pointer casts.

This is a type-level conversion, not evidence that the underlying allocation is writable or that Rust's aliasing rules permit mutation. A `*mut T` can exist even when writing through it would be undefined behavior; the legality of a later write depends on the provenance, allocation, mutability/aliasing state, alignment, and other requirements of that operation.

For proof construction, the conversion should therefore preserve the source pointer's access authority rather than mint a new write capability merely because the destination type is `*mut T`.

Basis: **source/documentation** in `const_ptr.rs` / `mut_ptr.rs` + **derived** consequence from separate pointer-access UB rules.

### `with_metadata_of()` demonstrates that metadata and provenance come from different operands

The unstable `with_metadata_of` API is useful as a boundary example. It takes the data-pointer value and provenance from `self`, but metadata from a second pointer. Its documentation explicitly warns that provenance is **not** combined: the resulting pointer may only access addresses justified by `self`'s provenance, even if the metadata came from a pointer into another allocation.

This is not a stable API contract Anneal must depend on, and the separate wide-pointer report should own its full semantics. It is nevertheless direct pinned evidence against a tempting inference: taking metadata from a valid pointer does not transfer that pointer's allocation provenance to the data address.

Basis: **documentation/source** in `const_ptr.rs` / `mut_ptr.rs`.

### Pointer equality by address is weaker than provenance equivalence

The pinned `core::ptr` overview says arbitrary pointers may be compared by address and emphasizes that equal addresses do not make their provenance interchangeable. A pointer at the end of one allocation can numerically equal a pointer at the start of another allocation while still carrying different access authority.

This matters when validating transformations that normalize or hash pointer addresses. Equality of `addr()` results is an address fact only. Any later memory-access proof must still establish that the pointer being used carries provenance and other permissions appropriate for the target allocation.

Basis: **documentation** in `ptr/mod.rs` + **derived** verification consequence.

## Boundaries

- **No fresh execution.** No rustc, Miri, CTFE, Charon, Aeneas, or Anneal specimen was run. Findings are exact pinned Reference/core-library semantics and source.
- **No complete provenance calculus.** The pinned documentation explicitly says Rust's exact provenance and aliasing semantics are not fully settled. The report records stable API distinctions without filling those open regions with a private formal model.
- **Exposed Provenance remains intentionally ambiguous.** The evidence does not establish a deterministic rule selecting provenance for an integer-to-pointer cast.
- **Wide-pointer validity is separate.** This report records pointer-cast metadata transformation only. Slice-length validity, trait-vtable validity, raw-parts construction, metadata APIs, and DST access obligations remain in the dedicated wide-pointer subject.
- **Pointer arithmetic is separate.** `with_addr` is implemented through wrapping byte offset and inherits its provenance behavior, but the complete `offset` / `add` / `sub` / wrapping arithmetic contract belongs to the pointer-arithmetic report.
- **Memory accesses are separate.** `read`, `write`, unaligned/volatile variants, copy operations, and raw-to-reference conversion impose additional operation-specific obligations not repeated here.
- **Function-pointer casts are not inventoried.** The Reference separately permits function-item/function-pointer conversions to raw pointers or integers; this report is about raw-pointer value/provenance semantics.
- **Const evaluation is stricter.** The Reference imposes additional provenance-related restrictions in const contexts. Those rules are covered by the broader validity report and must not be silently generalized to ordinary runtime behavior.
- **The implementation's internal `transmute` is not a public semantic promise.** `addr` and `without_provenance_mut` use sysroot-internal transmute implementations whose comments explicitly deny a stable generalization to arbitrary user `transmute`.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-27.

**Normative — Rust Reference** at `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`:

- `src/expressions/operator-expr.md`, blob `6c5e4ffbf1532597c3ffe9a800ca80e0fb3cec8a`: `as` cast table; pointer-to-address and address-to-pointer rules; raw-pointer-to-raw-pointer cast behavior; wide-pointer metadata compatibility.
- `src/types/pointer.md`, blob `ffd234a3b77dbb4d34f58b4e0b366a79ca7cc2f1`: raw-pointer value properties and current thin-pointer transmutation validity boundary.
- `src/behavior-considered-undefined.md`, blob `373052061c50fc2f6d1c07a91960d40bac505284`: pointer-access UB, unresolved aliasing outline, raw-pointer initialization, wide-pointer metadata validity, and const-context provenance restrictions.

**Documentation and source — pinned core library** at `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`:

- `library/core/src/ptr/mod.rs`, blob `ff2c18d685b65832c296731f23f1664779b874f2`: provenance overview; Strict versus Exposed Provenance; `without_provenance` / mutable counterpart; `with_exposed_provenance` / mutable counterpart; address-comparison boundary.
- `library/core/src/ptr/const_ptr.rs`, blob `5cbbebf9f478819ee80e0c6486d622ae9ffdac00`: `cast`, `cast_mut`, `addr`, `expose_provenance`, `with_addr`, `map_addr`, `with_metadata_of`, and `to_raw_parts` implementations/contracts.
- `library/core/src/ptr/mut_ptr.rs`, blob `53ef7f754d201a1dc08aa50a320266a8ab55245f`: mutable-pointer counterparts, including `cast`, `cast_const`, `addr`, `expose_provenance`, `with_addr`, and `map_addr`.
- `library/core/src/ptr/docs/addr.md`, blob `785b88a9987090d4d04ebe614fee3fc0d89794ec`: shared `addr()` contract distinguishing discarded-but-unexposed provenance from Exposed Provenance.

**Related current corpus evidence** at `google/zerocopy@reference` head `b6c1ba9f891840fc95a1de167bc17ebc38f5cf07`:

- `rust-validity-well-defined-execution-nightly-2026-05-31`, `REPORT.md` blob `f07b6f624ce7fa77db88885df8a5f02e7dc2ba4a`: separates raw-pointer value validity from operation-relative access validity and preserves unresolved provenance/aliasing boundaries.
- `rust-ub-and-operational-models-nightly-2026-05-31`, `REPORT.md` blob `ecb20487cd204065bd09443f416501e2395c8f38`: establishes the authority boundary among the Reference, Miri, and experimental operational models.
- `charon-raw-pointers-unsafe-operations-0-1-210`: records that Charon collapses rustc's `PointerExposeProvenance` and `PointerWithExposedProvenance` cast reasons into its more general raw-pointer cast representation, which is a separate downstream representation issue.

No fresh **execution** evidence was produced.

## Revalidation

For another Rust revision, revalidate the smallest surfaces that determine these distinctions:

1. diff the Strict/Exposed Provenance sections and no-provenance constructors in `library/core/src/ptr/mod.rs`;
2. diff `addr`, `expose_provenance`, `with_addr`, `map_addr`, `cast`, and const/mut cast methods in `const_ptr.rs` and `mut_ptr.rs`;
3. diff `src/expressions/operator-expr.md` for raw-pointer `as` cast and metadata rules;
4. diff the Reference's raw-pointer validity and UB sections for any stronger/weaker provenance, metadata, or aliasing requirements.

On an execution-capable surface, add a small Miri/rustc discriminator matrix at the exact toolchain pin:

- `addr()` followed by an integer-to-pointer cast, with and without a separate exposed provenance;
- `map_addr()` tagged-pointer roundtrip that leaves and re-enters the original allocation's address range;
- `without_provenance()` used only as a sentinel, then attempted for a non-zero-sized read;
- `expose_provenance()` followed by `with_exposed_provenance()` for a live allocation;
- `cast_mut()` from a pointer whose underlying memory must remain non-writable, followed by an attempted write;
- sized-to-sized and wide-to-thin raw-pointer casts, recording data address and metadata behavior.

Preserve the exact Rust/Miri revisions, source, command, target, diagnostics, and outputs. Such a probe can confirm how the selected implementation diagnoses representative cases. It does not turn Miri's provenance model into the normative Rust language model or resolve the Reference's explicitly unsettled regions.
