# Rust raw-pointer bulk-copy primitives at nightly-2026-05-31

## Summary

At `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `core::ptr::copy` and `core::ptr::copy_nonoverlapping` are **untyped byte-copy operations with typed alignment**. They copy `count * size_of::<T>()` bytes and preserve the initialization state of those bytes exactly. The source bytes need not form valid initialized `T` values; they may be uninitialized or otherwise violate `T`'s validity requirements. This is materially different from `ptr::read`, which produces a `T` and therefore requires an initialized valid value.

The two primitives differ primarily in overlap. `copy_nonoverlapping` requires the source and destination ranges not to overlap and has `memcpy`-like semantics. `copy` permits overlap and is specified as if the source bytes were first copied into a temporary array and then into the destination, giving `memmove`-like semantics. The pinned `copy` contract adds an important overlapping-range condition: the destination must remain valid while the source range is read. Allowing overlap therefore does not erase provenance, aliasing, lifetime, or mutability constraints.

Both functions require source and destination alignment for `T`, even when the effective byte count is zero. For a nonzero byte count, the source must be valid for reads and the destination valid for writes over the complete byte range. For zero-byte copies, the explicit access-validity requirements are waived, while alignment remains required. The general `core::ptr` validity model still distinguishes pointer provenance and access permission from numeric address.

Both functions make bitwise copies regardless of whether `T: Copy`. They do not implement Rust move semantics and do not drop overwritten destination contents. Copying a non-`Copy` resource-owning representation can therefore create multiple bytewise representations whose later use or destruction must be controlled by the surrounding unsafe abstraction. The standard `Vec::append` example demonstrates the intended move-like protocol: logically remove the source elements first, copy their bytes, then extend the destination length.

All ordinary accesses through these functions are non-atomic. Runtime unsafe-precondition checks in the implementation cover only selected easy-to-test conditions and are not a substitute for the full library contract.

For Anneal, these primitives need proof obligations at four separate layers: **byte-range read/write authority**, **alignment**, **overlap policy**, and **post-copy initialization/ownership state**. A model that treats them as typed assignment, or that requires every source byte range to already contain valid `T` values, is unsound or needlessly incomplete.

This report is based on pinned core-library source/documentation and the bundled Rust Reference. No fresh rustc, Miri, Charon, Aeneas, or Lean execution was performed.

## Applicability

This report applies to:

- `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, the compiler and core-library revision behind Anneal's relevant `nightly-2026-05-31`; and
- `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`, the Reference revision bundled by that Rust tree.

It covers:

- `core::ptr::copy`;
- `core::ptr::copy_nonoverlapping`;
- `*const T::{copy_to, copy_to_nonoverlapping}`;
- `*mut T::{copy_to, copy_to_nonoverlapping, copy_from, copy_from_nonoverlapping}`.

The pointer methods are thin wrappers around the free functions and inherit the same safety contracts. The `copy_from*` methods reverse only argument order: `self` is the destination.

This report does not cover `read`, `write`, volatile access, atomics, `write_bytes`, `swap`, typed assignment, `MaybeUninit` APIs as a whole, or the complete initialization/padding model. It also does not define Rust's still-unsettled general aliasing/provenance model. Those are separate subjects.

The current corpus report `rust-validity-well-defined-execution-nightly-2026-05-31` supplies the broader distinction between value validity and operation-relative pointer validity. The separate raw-pointer-validity and read/write candidates refine adjacent parts of that boundary; this report focuses only on bulk copy.

## Findings

### Bulk copy is explicitly untyped

The pinned documentation for both `copy` and `copy_nonoverlapping` says the copy is untyped: the copied data may be uninitialized or otherwise violate the requirements of `T`, and the initialization state is preserved exactly.

That wording establishes a stronger and more useful contract than "copy `count` values of type `T`." The generic type parameter determines element size and alignment, but it does not require the source region to contain `count` initialized valid Rust values.

This distinction is essential for unsafe initialization patterns. A byte range can be valid to read as raw storage while some bytes are uninitialized. Bulk copy can reproduce that initialization mask without first producing a `T`. By contrast, `ptr::read<T>` produces a typed value and therefore carries a typed initialization requirement.

For verification, do not add a source-value-validity obligation that the API itself does not have. Track byte initialization state through the copy instead.

Basis: **core-library contract/source** in `library/core/src/ptr/mod.rs`.

### `copy_nonoverlapping` is a `memcpy`-like primitive with an explicit disjointness obligation

`copy_nonoverlapping<T>(src, dst, count)` copies `count * size_of::<T>()` bytes and requires:

- the source range to be valid for reads, unless the effective byte count is zero;
- the destination range to be valid for writes, unless the effective byte count is zero;
- both pointers to be properly aligned for `T`; and
- the source and destination byte ranges not to overlap.

Its implementation delegates to `crate::intrinsics::copy_nonoverlapping` after an unsafe-precondition assertion that checks selected properties such as alignment/non-nullness and non-overlap.

The disjointness rule is a semantic precondition, not merely a performance recommendation. Code that cannot establish it must use `copy`.

Basis: **core-library contract/source**.

### `copy` permits overlap but preserves a destination-validity condition during the source read

`copy<T>(src, dst, count)` has `memmove`-like semantics. The documentation specifies the result as if the source bytes were copied to a temporary array and then from that temporary into the destination. This avoids the ordinary directional-clobber problem of a naive overlapping copy.

The safety contract nevertheless contains more than "overlap is allowed." The destination must be valid for writes over the entire byte range **and remain valid while the source is read** over the same-sized range. The documentation explains that, when the ranges overlap, source reads must not invalidate the destination pointer.

This condition matters for provenance/aliasing models. A verifier cannot justify an overlapping `copy` merely from arithmetic overlap safety. It must also establish that the permission used for source reads and destination writes is compatible over the operation's lifetime.

The exact general Rust aliasing model remains unsettled at this revision, so this report preserves the library contract instead of inventing a stronger formal rule.

Basis: **core-library contract/source**, with the proof-boundary statement **derived**.

### Alignment remains typed even though the bytes are not

Both primitives require `src` and `dst` to be aligned for `T`.

The requirement remains even when `count * size_of::<T>() == 0`. This creates a useful separation:

- the **memory access** can be empty, so the explicit read/write-validity requirement is waived;
- the **pointer alignment** obligation remains because the API is parameterized by `T`.

Thus "untyped copy" does not mean "byte-aligned copy." If code has arbitrary byte-aligned storage, it can choose `T = u8` or otherwise arrange an appropriately aligned pointer, but it cannot pass a misaligned `*const T`/`*mut T` to these APIs merely because the bytes themselves are opaque.

Basis: **core-library contract/source**.

### Zero-byte copies waive access validity but not alignment

The two safety contracts say the source/destination need be valid for the corresponding memory access **or the effective byte count must be zero**.

The surrounding `core::ptr` documentation defines general read/write validity more strictly: null is never valid for reads/writes, while any non-null pointer is valid for a zero-sized access. The bulk-copy functions therefore carry their own explicit zero-byte exception to access validity.

Their documentation separately requires proper alignment even for an effective size of zero.

A verifier should encode those as separate predicates. Treating "zero bytes" as a universal exemption would incorrectly erase alignment.

The implementation's runtime precondition helper is not the semantic authority here. Its `zero_size` parameter can skip selected null/alignment diagnostics in cases such as `T` being zero-sized or `count == 0`; the documented safety contract is the normative library boundary that unsafe callers must satisfy.

Basis: **core-library documentation/source**; runtime-check distinction is **derived** from the gap between documented preconditions and checked predicates.

### The complete byte ranges, not only starting addresses, need authority

For a nonzero effective byte count, the source must be valid for reads of the entire `count * size_of::<T>()` range and the destination valid for writes of the entire range.

The module-level pointer documentation explains the relevant lower bound: provenance identifies an allocation and a pointer is dereferenceable only when the complete accessed range lies within that allocation. Provenance also carries spatial, temporal, and mutability permissions.

A proof that both starting addresses happen to lie in live allocations is therefore insufficient. The full range must be authorized for the corresponding operation, and the permissions must remain valid during the copy.

This is especially important for large counts, pointers near allocation boundaries, subslices whose provenance has been narrowed, and overlapping `copy` operations.

Basis: **core-library module documentation**; proof formulation is **derived**.

### Initialization state is copied exactly

The explicit statement that initialization state is preserved means a useful bulk-copy model needs more than output bytes. It must preserve which bytes are initialized.

If a source byte is initialized, its copied destination byte becomes initialized with the same bit value. If a source byte is uninitialized, the corresponding destination byte remains uninitialized after the copy. Copying does not "launder" uninitialized bytes into initialized typed data merely because the generic parameter is `T`.

This also means bulk copy can be valid even when immediately interpreting the destination as `T` would not be. A later typed read or value production must separately prove that the resulting representation satisfies `T`'s validity requirements.

Padding is a particularly important later consumer of this rule, but the full padding/typed-copy model is left to the separate initialization subjects.

Basis: **core-library contract** plus **derived verification consequences**.

### Bitwise copy does not imply logical `Copy`

Both functions create bitwise copies regardless of whether `T: Copy`.

The documentation warns that, for non-`Copy` `T`, using both the source-region values and destination-region values can violate memory safety. The operation itself does not invoke a move constructor, clear the source, adjust a length, transfer a destructor obligation, or otherwise tell Rust's abstract ownership model that a value moved.

The caller must implement that protocol around the raw copy. The pinned `copy_nonoverlapping` documentation demonstrates this with a manual `Vec::append`: it sets the source vector length to zero before copying and increases the destination length afterward. Those length changes are what prevent the old source elements from later being dropped and what make the destination elements logically live.

For Anneal, the raw operation should therefore copy representation and initialization state; ownership/resource transfer belongs to surrounding proof obligations.

Basis: **core-library documentation**; Anneal boundary is **derived**.

### Overwritten destination contents are not dropped

Neither primitive performs Rust assignment. The implementation delegates to raw-copy intrinsics and has no destructor step for overwritten destination bytes.

If the destination range previously represented live resource-owning values, blindly overwriting them can lose the only reachable representation of those resources. That can leak resources or violate a higher-level abstraction protocol even when the raw byte access itself satisfies the library's memory-safety preconditions.

This is not a claim that every such leak is language-level UB. It is a reminder that a verifier modeling `copy` as ordinary assignment would prove the wrong resource behavior by silently introducing destruction that the operation does not perform.

Basis: **source** plus **derived resource/verification consequence**.

### Ordinary bulk copies are non-atomic

The pinned `core::ptr` module documentation says accesses performed by functions in the module are non-atomic. Concurrent conflicting access can therefore be undefined behavior even if range, provenance, alignment, and overlap requirements otherwise hold.

`copy` allowing overlap within one operation does not make it an atomic move. `copy_nonoverlapping` being analogous to `memcpy` likewise says nothing about synchronization.

Detailed concurrency/memory-ordering semantics are separate inventory subjects, but an Anneal primitive model must not silently promote these operations to atomic transactions.

Basis: **core-library module documentation**.

### Pointer methods are semantic wrappers, not separate primitives

At this revision:

- `*const T::copy_to` calls `ptr::copy(self, dest, count)`;
- `*const T::copy_to_nonoverlapping` calls `ptr::copy_nonoverlapping(self, dest, count)`;
- the corresponding `*mut T::copy_to*` methods do the same;
- `*mut T::copy_from(src, count)` calls `ptr::copy(src, self, count)`;
- `*mut T::copy_from_nonoverlapping(src, count)` calls `ptr::copy_nonoverlapping(src, self, count)`.

The `copy_from*` forms intentionally have the opposite apparent argument order because `self` is the destination.

A verifier can normalize these method forms to the two free-function semantics without creating new primitive rules, provided it preserves source/destination identity correctly.

Basis: **core-library source** in `const_ptr.rs` and `mut_ptr.rs`.

### Runtime UB assertions are partial diagnostics, not proof of safety

The implementations contain `ub_checks::assert_unsafe_precondition!` calls. They can detect selected conditions such as nullness/alignment and, for `copy_nonoverlapping`, overlap.

They do not establish the complete access contract: full provenance, allocation lifetime, read/write authority, aliasing compatibility, initialization/resource protocols, or concurrency safety are not reduced to those runtime predicates.

The absence of a runtime assertion failure therefore does not prove that a call was valid Rust. Anneal must derive its obligations from the documented semantic contract, not from whichever checks happen to be instrumented in this compiler revision.

Basis: **core-library source** and **derived comparison with the documented contract**.

### A compact verification contract separates four independent dimensions

For the pinned revision, a useful proof matrix is:

| Primitive | Range authority | Alignment | Overlap | Initialization/ownership result |
| --- | --- | --- | --- | --- |
| `copy_nonoverlapping` | source readable, destination writable over full effective range; waived for zero bytes | both aligned for `T`, including zero bytes | ranges must be disjoint | copy bytes + initialization state exactly; caller controls logical ownership |
| `copy` | same, plus destination remains valid while source is read | both aligned for `T`, including zero bytes | overlap permitted | memmove-like byte result; initialization state copied exactly; caller controls logical ownership |

This decomposition prevents several common errors:

- requiring initialized valid `T` source values when the API deliberately permits uninitialized bytes;
- treating a zero-byte copy as removing alignment;
- treating overlap permission as erasing provenance/aliasing constraints;
- treating raw copy as Rust assignment or a move; and
- using runtime UB checks as a complete proof.

Basis: **derived synthesis** from the pinned contracts.

## Boundaries

**No fresh execution.** No Rust compiler, Miri, Charon, Aeneas, or Lean probe was run. The report records the exact pinned contracts and implementation structure.

**No complete aliasing/provenance formalization.** The pinned pointer documentation explicitly says the precise validity and aliasing rules are not fully determined. This report preserves the operation-relative "valid for reads/writes" contract and does not invent stronger semantics.

**No complete padding model.** The report establishes that bulk copy is untyped and preserves initialization state. It does not settle every padding or typed-copy consequence; those remain dedicated #3720 subjects.

**No `MaybeUninit` API survey.** `MaybeUninit` is relevant to storage initialization but has its own separate contract surface.

**No volatile or atomic equivalence.** These functions are ordinary non-atomic accesses and should not be substituted for volatile or atomic primitives.

**No blanket claim that overwriting live values is UB.** Losing a destructor obligation can leak or violate a library invariant without necessarily constituting immediate language-level UB. The surrounding abstraction decides the stronger resource obligation.

**No claim that runtime UB checks are exhaustive.** They are implementation diagnostics beneath the public unsafe contract.

**No adjacent-version continuity.** Revalidate the exact core-library contracts and wrappers for another Rust revision.

## Evidence

Evidence was materially revalidated on 2026-09-27.

Primary Rust subject:

- `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`
  - `library/core/src/ptr/mod.rs`, blob `ff2c18d685b65832c296731f23f1664779b874f2`: module-level pointer validity/provenance/alignment/non-atomic rules; authoritative contracts and implementations for `copy` and `copy_nonoverlapping`.
  - `library/core/src/ptr/const_ptr.rs`, blob `5cbbebf9f478819ee80e0c6486d622ae9ffdac00`: `copy_to` and `copy_to_nonoverlapping` wrapper methods.
  - `library/core/src/ptr/mut_ptr.rs`, blob `53ef7f754d201a1dc08aa50a320266a8ab55245f`: mutable-pointer `copy_to*` and `copy_from*` wrappers.

Bundled normative Reference:

- `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`
  - `src/behavior-considered-undefined.md`, blob `373052061c50fc2f6d1c07a91960d40bac505284`: data races, misaligned/dangling accesses, aliasing uncertainty, and invalid-value boundaries used only to constrain derived claims.

Current corpus boundary:

- `reports/rust-validity-well-defined-execution-nightly-2026-05-31`: general value-validity and well-defined-execution boundary.
- Current uncommitted raw-pointer-validity and read/write candidates cover adjacent operation-specific questions and were not treated as native fulfillment.

Evidence roles are **core-library contract/source**, **normative Reference**, **current corpus boundary**, and **derived verification synthesis**.

## Revalidation

For another Rust revision:

1. inspect `library/core/src/ptr/mod.rs` for both bulk-copy contracts and implementations;
2. confirm whether "untyped" and exact initialization-state preservation remain explicit;
3. diff the zero-byte access-validity exceptions and the separate alignment rule;
4. diff `copy`'s overlapping-range destination-validity language;
5. recheck `copy_nonoverlapping`'s exact disjointness rule;
6. inspect the general `core::ptr` validity/provenance and non-atomic-access documentation;
7. inspect `const_ptr.rs` and `mut_ptr.rs` to ensure method forms remain wrappers with the same source/destination ordering;
8. inspect the bundled Rust Reference for changes to invalid values, dangling/misaligned access, races, or aliasing guidance; and
9. treat changes to runtime unsafe-precondition assertions as diagnostics unless the public contract changes too.

A bounded execution-strengthening probe on the exact nightly should preserve exact commands/toolchain identity and include at least:

- non-overlapping initialized copy;
- overlapping `copy` in both directions;
- overlapping `copy_nonoverlapping` as a negative case;
- a partial/uninitialized byte-range copy through `MaybeUninit` storage, followed by bytewise inspection that does not prematurely produce an invalid `T`;
- zero-count copies with valid aligned dangling pointers and deliberately misaligned pointers;
- a range crossing an allocation boundary as a negative case;
- a non-`Copy` move-like protocol showing source logical deactivation before later destruction;
- a destination containing a resource-owning value to demonstrate that raw copy does not drop it; and
- a concurrent conflicting-access negative case under a tool/model that can observe the relevant data race.

Execution evidence should strengthen this source-level contract, not replace it. Any Miri-specific rejection should be identified as model/tool evidence unless independently grounded in the pinned language/library contract.
