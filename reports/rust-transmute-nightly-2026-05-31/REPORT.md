# Rust transmutation semantics at nightly-2026-05-31

## Summary

At the Rust revision behind Anneal's `nightly-2026-05-31`, `mem::transmute` is an unsafe **by-value reinterpretation**, not an unchecked byte-array cast. It requires `Src` and `Dst` to have equal size, consumes the source, and produces a `Dst`; both values must be valid at their respective types. The operation is described as a bitwise move, but by-value movement means source or destination padding is **not guaranteed to be preserved**. Equal size is therefore only the first obligation. Destination bit validity, reference/pointer obligations, lifetimes, aliasing, ownership, and library invariants can still make a same-sized transmutation unsound.

`mem::transmute_copy` has a materially different contract. It borrows the source, leaves it logically present, and reads a `Dst`-sized prefix as a `Dst`. The public documentation says `Dst` larger than `Src` is invalid; the inspected implementation also has an explicit size assertion before the read. It compensates for stricter destination alignment by selecting `ptr::read_unaligned`, so destination alignment does not by itself require the address of `src` to satisfy `align_of::<Dst>()`. Because the original `Src` remains, the operation can duplicate ownership or resource state even when the resulting bits are a valid `Dst`.

The pinned core source also contains intentionally more specialized unstable transmutation mechanisms. `intrinsics::transmute_unchecked` removes the normal compile-time same-size check. `mem::transmute_prefix` permits size-mismatched union-style reinterpretation when the resulting partially initialized destination is valid. `mem::TransmuteFrom` asks the compiler to prove union-transmutability while allowing the programmer to assume selected alignment, lifetime, library-safety, or language-validity obligations. These are distinct contracts, not alternate spellings of stable `mem::transmute`.

For verification, model a transmutation as a **typed state transition** with explicit obligations. Do not model `transmute` as "same size implies safe" or as a memcpy that preserves padding. Do not model `transmute_copy` as ownership-neutral merely because its memory read succeeds.

## Applicability

The primary subject is `rust-lang/rust` revision `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, the compiler/core revision associated with the Anneal-era `nightly-2026-05-31` toolchain. The normative invalid-value and const-provenance rules are read from `rust-lang/reference` revision `ad35aca481751a06afeb23820a672b0f3b11a476`, the Reference revision examined with that compiler.

The stable API conclusions concern:

- `core::mem::transmute`, which is a re-export of the compiler intrinsic with special call-site size checking; and
- `core::mem::transmute_copy`.

The report also records the exact-revision contracts of related unstable APIs because they sharpen the semantic boundaries:

- `core::intrinsics::transmute_unchecked`;
- `core::mem::transmute_prefix`;
- `core::mem::transmute_neo`; and
- `core::mem::TransmuteFrom` with `Assume`.

Those unstable APIs are **not** treated as cross-version promises. They are evidence about the design surface at this revision.

The report does not generalize these findings to adjacent Rust nightlies. It also does not claim a complete Rust memory, provenance, or aliasing model; the pinned Reference explicitly says the memory model is incomplete.

## Findings

### `transmute` checks size, then transfers the remaining proof obligations to the caller

`core::mem` re-exports `crate::intrinsics::transmute` rather than wrapping it. The source comment gives the reason: the compiler performs special "types have equal size" checking at the call site.

The intrinsic documentation then gives the semantic contract:

1. `Src` and `Dst` must have the same size; compilation fails if equality cannot be established.
2. The operation is semantically a bitwise **move** from `Src` into `Dst`.
3. The original source is forgotten rather than separately dropped.
4. The source must be valid as `Src`.
5. The result must be valid as `Dst`.

Basis: core documentation/source + normative Reference validity rules.

The size check is therefore not a validity proof. A same-sized conversion such as an arbitrary byte to `bool`, an integer to a reference, or a value to an enum with an invalid discriminant can still immediately produce an invalid value and trigger undefined behavior. The Reference makes this general: producing an invalid value is immediate UB, and "producing" includes values returned by primitive operations.

For a verifier, the reusable rule is:

> `transmute::<Src, Dst>(x)` requires `size_of::<Src>() == size_of::<Dst>()`, `x` valid as `Src`, and the transferred representation valid as `Dst`, plus any semantic invariants represented by `Dst`.

The destination obligation is stronger than "the destination type has the same layout size."

### By-value transmutation does not promise to preserve padding

The `transmute` documentation explicitly warns that source and destination are passed by value. If either type contains padding, that padding is not guaranteed to be preserved by the transmutation.

Basis: core documentation.

This matters for both executable semantics and proof modeling. A proof may not use `transmute` as evidence that every source memory byte—including padding bytes and any abstract initialization/provenance state carried by them—appears unchanged in the destination representation. This differs from raw untyped copy APIs whose documented contract is explicitly about byte copying and initialization-state preservation.

The pinned Reference reinforces why this distinction is meaningful: Rust memory bytes are abstract and can be uninitialized or carry pointer provenance. Hardware byte equality is not a complete model of Rust memory state.

Derived consequence: when the correctness argument needs padding preservation, `transmute` is the wrong primitive to model as a byte-preserving copy. The proof should identify the actual operation that provides the needed byte-level contract.

### Alignment of the by-value `Src` and `Dst` slots is not the transmute hazard

The `transmute` docs say alignment of the transmuted values themselves is not a caller concern: normal value passing already gives `Src` and `Dst` properly aligned storage.

Basis: core documentation.

That does **not** make alignment irrelevant when the representation contains pointers or references. If the destination is, for example, a reference, that reference's pointee alignment and other validity obligations still apply. Likewise, transmuting a container representation can violate the container's internal alignment or layout invariants even though the outer by-value slots were aligned.

The documentation's `Vec<&T>` to `Vec<Option<&T>>` example makes this distinction concrete. Even if the inner types happen to be same-sized, blindly transmuting the `Vec` depends on `Vec` representation and invariants. A no-copy reconstruction through raw parts still requires the inner element size and alignment to be suitable.

Verification consequence: keep **value-slot alignment** separate from **alignment encoded or required by the destination value**.

### A transmute can change lifetime/type interpretation without making the new interpretation true

The documentation includes lifetime-extension and invariant-lifetime examples specifically to show that `transmute` can manufacture a type with a different lifetime.

Basis: core documentation.

The new type does not create the referent lifetime, ownership, exclusivity, or aliasing facts it asserts. Those facts remain caller obligations. The Reference's validity and aliasing sections apply when references are produced and used.

Similarly, the documented `split_at_mut` example rejects "same type and same size" as sufficient reasoning: transmuting one `&mut [T]` into another and then using both can produce overlapping mutable references. The transmute itself can preserve bits perfectly while the surrounding ownership/aliasing state is unsound.

Verification consequence: a transmuted reference-like value should import the destination reference obligations into the proof state. It should not be treated as a proof of those obligations.

### Pointer/integer transmutation is a special provenance-sensitive boundary

The pinned `transmute` documentation gives unusually strong warnings for pointer/integer conversions.

For pointer-to-integer transmutation:

- in a const context it is UB when the pointer carries provenance, except for the documented case where the pointer was originally created from integer data;
- outside const evaluation, the documentation says this touches unspecified parts of Rust's memory model and should be avoided.

For integer-to-pointer transmutation:

- the operation is described as largely unspecified and likely not equivalent to an `as` cast;
- the documentation says non-zero-sized memory accesses through a pointer constructed this way are currently considered UB.

These restrictions extend through compound types. The docs also preserve a deliberate `MaybeUninit<usize>` distinction: transmuting pointer representation into `MaybeUninit<usize>` can defer the point at which it becomes an integer value; calling `assume_init` then completes the problematic interpretation.

Basis: core documentation + normative Reference const-provenance rule.

The pinned Reference independently states the const-evaluation validity rule: bytes interpreted as integer data must not carry provenance, while pointer data has its own provenance-fragment requirements. This is a direct reason not to collapse pointers to machine integers in a verification model.

For raw pointer to raw/function-pointer conversions, use the more specific pointer/cast contract where available. The core docs explicitly demonstrate raw-pointer-to-function-pointer transmutation after first converting the function pointer to a raw pointer, avoiding an integer-to-pointer transmute.

### `transmute_copy` is a typed prefix read that leaves the source logically alive

`mem::transmute_copy<Src, Dst>(&Src)` does not have `transmute`'s move semantics. Its documentation says it interprets the source address as `&Dst` and reads a `Dst` without moving the contained `Src`. It thereby creates a copy while the original source remains.

Basis: core documentation/source.

This changes the ownership proof. If the copied representation carries unique ownership, drop responsibility, or another linear resource, the caller can end up with two logical owners. A valid memory read does not justify later using or dropping both copies.

The exact implementation:

1. asserts `size_of::<Src>() >= size_of::<Dst>()`;
2. uses `ptr::read_unaligned` when `Dst` requires stricter alignment than `Src`; otherwise
3. uses `ptr::read`.

The public docs describe `Dst` larger than `Src` as an invalid invocation that can cause UB. The inspected implementation additionally rejects that case with an assertion before performing the typed read. This implementation detail is useful diagnostic evidence, not a reason to weaken the unsafe API contract.

The alignment branch is important: `transmute_copy` does not require the `&Src` address to satisfy `align_of::<Dst>()`; it deliberately handles the stricter-alignment case with an unaligned read.

`transmute_copy` also differs from an untyped `ptr::copy`: it constructs a typed `Dst`. Destination validity is therefore required, and surrounding reasoning must use typed-copy/padding rules rather than assuming an untyped byte-for-byte copy contract.

### `transmute_unchecked` isolates what the normal size check buys

`core::intrinsics::transmute_unchecked` has the same runtime operation as `transmute` when both are well formed, but it removes the normal compile-time size equality guarantee. Its documentation says unequal sizes are UB at runtime.

Basis: core intrinsic documentation/source.

This gives a useful decomposition:

- ordinary `transmute` discharges **size equality** statically;
- it does **not** discharge destination validity, ownership, lifetimes, aliasing, or pointee invariants;
- `transmute_unchecked` moves even size equality back into the unsafe caller's obligation.

The intrinsic is not intended as a direct stable user API at the inspected revision.

### The unstable prefix/neo APIs deliberately separate equal-size and union-style semantics

The inspected `core::mem` contains two unstable experimental functions under issue `#155079`.

`transmute_neo` performs a const size-equality assertion and then calls `transmute_unchecked`. It is explicitly an experimental iteration surface and is not intended to stabilize under that name.

`transmute_prefix` instead defines a `repr(C)` union-style conversion over the common prefix:

- if `Src` is larger, only the first `size_of::<Dst>()` bytes are interpreted as `Dst`;
- if sizes are equal, it uses `transmute_unchecked`;
- if `Dst` is larger, the source bytes are followed by uninitialized bytes up to the destination size.

The safety contract requires the resulting destination representation—including any uninitialized suffix—to be valid as `Dst`, and requires destination safety invariants to hold.

Basis: core documentation/source.

This is a useful counterexample to the idea that all transmutation is inherently equal-sized. Equal size is the stable `transmute` API's chosen static contract, not a universal property of every sound bit reinterpretation. A larger destination can be valid when the additional bytes are padding or otherwise allowed to remain uninitialized.

### `TransmuteFrom` exposes a compiler-proved transmutability contract, not a stable layout promise

The unstable `TransmuteFrom<Src, ASSUME>` trait is implemented by the compiler, not explicitly by user code. The compiler provides an implementation when it can prove a union-style transmutation sound subject to the selected `Assume` flags.

The four explicit assumption dimensions are:

- alignment of references in the destination;
- lifetimes of references;
- library safety invariants;
- language-level bit validity.

An assumption set to `false` remains a compiler proof obligation; setting it to `true` transfers that obligation to the programmer.

Basis: core documentation/source.

The trait's documentation is explicit that its implementation does **not** guarantee portability across toolchains/targets/compilations or SemVer stability across type-defining crate versions. It also notes that union-transmutation can be more permissive than `transmute_copy`, including cases where a smaller source is extended by trailing uninitialized destination bytes that are permitted padding.

For verification architecture, this API is useful evidence that Rust itself distinguishes several proof dimensions that a single "same representation" predicate would collapse. It is not evidence that those unstable proof categories are a finalized language-level transmutation calculus.

### Compact obligation matrix

The following matrix is the practical result for an unsafe-Rust verifier.

| Operation | Size condition | Source after operation | Destination validity | Alignment boundary | Padding/extra bytes |
| --- | --- | --- | --- | --- | --- |
| `mem::transmute` | equal size, checked at call site | consumed/forgotten as `Src` | caller must establish valid `Dst` | value slots handled; destination reference/pointer obligations remain | padding not guaranteed preserved |
| `mem::transmute_copy` | public contract requires `Dst <= Src`; implementation asserts it | original `Src` remains | caller must establish valid copied `Dst` | implementation uses unaligned read if necessary | typed prefix read; not an untyped preservation contract |
| `intrinsics::transmute_unchecked` | caller obligation; mismatch is UB | consumed | caller must establish valid `Dst` | same semantic destination obligations | same runtime operation as valid `transmute` |
| `mem::transmute_prefix` | size mismatch permitted | consumed | initialized prefix + any uninitialized suffix must form valid `Dst` | destination invariants still apply | larger `Dst` can have uninitialized tail |
| `mem::transmute_neo` | equal size asserted in const evaluation | consumed | caller obligation | same destination obligations | experimental equal-size frontend |
| `TransmuteFrom` | compiler checks union-transmutability modulo assumptions | consumed | compiler or caller according to `Assume` | explicit assumption dimension | may permit trailing uninitialized bytes |

Basis: source/documentation + derived synthesis.

## Boundaries

**Not examined:** no fresh rustc or Miri executions were run. In particular, this report does not preserve a diagnostic matrix for invalid bool/enum/reference transmutations, unequal-size compilation failures, const provenance failures, or ownership duplication.

**Not examined:** this is not a complete report on pointer casts, Strict/Exposed Provenance APIs, reference formation, `MaybeUninit`, typed-copy padding, or aggregate layout. Those subjects have independent contracts; they are mentioned only where transmutation directly depends on them.

**Unknown/explicitly unsettled:** the pinned Rust memory model and exact aliasing/provenance semantics are incomplete. The report preserves the stable API and Reference boundaries that are documented at these revisions rather than inventing missing semantics.

**Known not to follow from this report:** equal size does not imply safe transmutability. Equal size plus destination bit validity still does not, by itself, prove library invariants, ownership/resource correctness, lifetime validity, or aliasing safety.

**Known not to follow from this report:** `transmute` does not provide byte-for-byte padding preservation.

**Known not to follow from this report:** current implementation assertions inside `transmute_copy` do not turn its unsafe preconditions into a stable recoverable-error API.

**Unsupported as a portability assumption:** an implementation of unstable `TransmuteFrom` is not evidence of cross-toolchain, cross-target, cross-compilation, or SemVer-stable representation compatibility.

## Evidence

All source observations below were acquired on 2026-09-27.

**Rust compiler/core library**

Repository: `rust-lang/rust`  
Revision: `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`

- `library/core/src/intrinsics/mod.rs`, blob `78d7314c58110b49839894a0f69377f4ee0d1204`
  - `transmute`
  - `transmute_unchecked`
  - Evidence role: documentation + source.
  - Establishes equal-size checking, bitwise-move semantics, validity, padding caveat, pointer/integer rules, lifetime/aliasing examples, and unchecked-size boundary.

- `library/core/src/mem/mod.rs`, blob `62c612e7ba2a65bb1645faaa669abd2a1d35a6c2`
  - `pub use crate::intrinsics::transmute`
  - `transmute_copy`
  - `transmute_prefix`
  - `transmute_neo`
  - Evidence role: documentation + source.
  - Establishes the special call-site size-check rationale, `transmute_copy` prefix/alignment implementation, and exact-revision unstable prefix/neo semantics.

- `library/core/src/mem/transmutability.rs`, blob `e26c1b8fa1e19b5c209aba1a0c45e179ffaf238f`
  - `TransmuteFrom`
  - `Assume`
  - Evidence role: documentation + source.
  - Establishes compiler-proved union-transmutability, programmer assumptions, trailing-uninitialized permissiveness, and portability/stability limits.

**Rust Reference**

Repository: `rust-lang/reference`  
Revision: `ad35aca481751a06afeb23820a672b0f3b11a476`

- `src/behavior-considered-undefined.md`, blob `373052061c50fc2f6d1c07a91960d40bac505284`
  - invalid-value rules;
  - reference/raw-pointer validity;
  - const provenance restrictions;
  - aliasing caveat.
  - Evidence role: normative.

- `src/memory-model.md`, blob `cc3cf02ec0adba12134ad6cb82e51a4b864da784`
  - abstract initialized/uninitialized bytes and optional provenance;
  - explicit statement that the memory model is incomplete.
  - Evidence role: normative.

The report's machine-readable `operation-matrix.json` captures the operation-level proof boundary. `source-map.json` records the immutable source coordinates used above.

## Revalidation

For another Rust revision, the cheapest reliable revalidation is:

1. Diff `core::intrinsics::transmute` and `transmute_unchecked`, especially:
   - size-check wording;
   - validity requirements;
   - padding guarantee;
   - pointer/integer and const-provenance guidance.
2. Diff `core::mem::transmute_copy`, checking:
   - its size condition;
   - whether oversize destination is rejected by assertion or another mechanism;
   - aligned versus unaligned read behavior.
3. If the unstable surface matters, diff `transmute_prefix`, `transmute_neo`, and `mem::transmutability::{TransmuteFrom, Assume}` independently. Do not infer continuity from their names.
4. Diff the Reference's invalid-value, const-provenance, and memory-model sections.
5. Re-run a small exact-toolchain discriminator suite if execution evidence is needed:
   - equal-size valid scalar transmute;
   - unequal-size ordinary `transmute` compile failure;
   - invalid `u8 -> bool`;
   - source/destination types with padding;
   - `transmute_copy` with stricter `Dst` alignment;
   - `transmute_copy` with `Dst` larger than `Src`;
   - non-`Copy` ownership duplication with `transmute_copy`;
   - pointer/integer conversions in const evaluation;
   - lifetime/reference cases whose soundness depends on external obligations.

A passing execution suite only confirms those specimens. The source/Reference diff remains necessary because transmutation's public contract contains proof obligations and negative guarantees that a few executions cannot establish.
