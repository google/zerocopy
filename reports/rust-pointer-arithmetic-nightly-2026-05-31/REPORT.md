# Rust raw-pointer arithmetic at nightly-2026-05-31

## Summary

At `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, the raw-pointer arithmetic APIs divide into two semantic families.

`offset`, `add`, and `sub` are unsafe, optimization-friendly operations with immediate in-bounds requirements. Their mathematical byte offset must fit in `isize`; when that offset is nonzero, the source pointer must carry provenance derived from an allocation and the entire half-open range between source and result must stay within that allocation. The result may be exactly one-past-the-end: the pinned documentation explicitly uses `vec.as_ptr().add(vec.len())` as a safe example. Crossing an allocation boundary is already undefined behavior at the arithmetic operation, even if the resulting pointer is never dereferenced.

`wrapping_offset`, `wrapping_add`, and `wrapping_sub` make the arithmetic operation itself safe and defer the in-bounds requirement to later use. They can leave an allocation and later re-enter it. They do **not** turn address equality into provenance equality: a wrapping result retains the provenance of its source pointer, so numerically landing on another allocation does not permit access to that allocation.

The byte variants apply the same two models after casting the data pointer to `u8`. Unlike element-wise arithmetic, they also work for non-`Sized` pointees. For a wide pointer, `byte_offset`, `byte_add`, `byte_sub`, and their wrapping counterparts change only the data pointer and preserve the original metadata unchanged.

These arithmetic APIs do not themselves establish alignment, referent validity, initialization, or permission for a later read/write. Those are separate access obligations. Conversely, the immediate unsafe arithmetic methods impose an allocation/provenance condition even before any access when their computed byte offset is nonzero.

The report is based on the exact pinned core-library source and documentation. No fresh Rust, Miri, Charon, or Aeneas execution was performed.

## Applicability

This report covers the `*const T` and `*mut T` arithmetic methods in the core library at the Rust revision behind Anneal's `nightly-2026-05-31` toolchain:

- `offset`, `add`, `sub`;
- `byte_offset`, `byte_add`, `byte_sub`;
- `wrapping_offset`, `wrapping_add`, `wrapping_sub`;
- `wrapping_byte_offset`, `wrapping_byte_add`, `wrapping_byte_sub`.

The `*const T` and `*mut T` implementations expose the same arithmetic contract. The mutable-pointer file mirrors the same method families and lowers them through the same pointer intrinsics/convenience composition.

This report does not cover pointer-distance methods such as `offset_from`, pointer-to-integer or integer-to-pointer conversion, `with_addr`/`map_addr`, raw-pointer reads/writes, or reference creation. Those operations have additional contracts and correspond to separate #3720 inventory items.

The core pointer documentation explicitly says Rust's complete provenance and aliasing rules are not fully specified at this revision. This report therefore records only the guarantees and obligations stated by the pinned API contract; it does not substitute a stronger provenance model from Miri, Stacked Borrows, Tree Borrows, or compiler implementation behavior.

## Findings

### `offset` requires an `isize`-representable in-allocation byte displacement

For `*const T` and `*mut T`, `offset(count: isize)` interprets `count` in units of `T`. The pinned shared documentation states two safety requirements.

First, the mathematical product

```text
count * size_of::<T>()
```

must fit in `isize`; this is a mathematical requirement, not wrapping integer arithmetic.

Second, when that byte offset is nonzero, `self` must be derived from a pointer to an allocation, and the entire half-open range between `self` and the result must remain inside that allocation. The range is `self..result` for a nonnegative offset and `result..self` for a negative offset.

The half-open formulation permits a result exactly one byte-range boundary past the allocation. The documentation makes this concrete by stating that `vec.as_ptr().add(vec.len())` is safe for `Vec<T>`.

Crossing from one allocation to another is not rescued by the fact that the result happens to have a plausible address. For `offset`, the allocation-bound condition applies at the arithmetic operation itself.

Basis: **library contract/source** in `library/core/src/ptr/docs/offset.md` and the `offset` implementations.

### `add` and `sub` are directional conveniences with the same immediate contract

`add(count: usize)` moves forward by `count` elements; `sub(count: usize)` moves backward. Their safety text repeats the same two requirements:

- `count * size_of::<T>()` must fit in `isize`;
- for a nonzero byte displacement, the source and entire traversed range must remain within the source allocation.

These methods are not merely integer-address operations. The source implementations ultimately use the pointer `offset` intrinsic, and the public contract preserves the same allocation/provenance boundary.

The implementation contains runtime UB-precondition checks for some address-overflow cases. At this pin, `add` and `sub` gate their expensive arithmetic checks under debug assertions, while `offset` has its own address-overflow check. These checks do not replace the unsafe contract: they cannot in general establish provenance, allocation membership, or every language-level precondition.

Basis: **library contract/source** in `library/core/src/ptr/docs/add.md`, `library/core/src/ptr/const_ptr.rs`, and `library/core/src/ptr/mut_ptr.rs`.

### In-bounds arithmetic does not require dereferencing or producing a `T`

The immediate arithmetic contract is about the byte displacement and allocation provenance/range. It does not say that the source or result must currently be dereferenceable as a properly aligned, initialized `T`.

That distinction matters for unsafe proofs. A raw pointer can be manipulated without performing a memory access. Later reads, writes, reference creation, and typed-value production carry their own requirements for alignment, validity, initialization, aliasing, lifetime, and mutability.

The pinned `core::ptr` module documentation makes the general distinction explicit: there is no context-free question "is this pointer valid"; validity is relative to an access. Pointer arithmetic therefore cannot be treated as an implicit proof that a later access is valid.

Basis: **library documentation** in `library/core/src/ptr/mod.rs` plus the narrower arithmetic contracts above.

### One-past-the-end is permitted; crossing the allocation is not

The unsafe methods permit the result to lie at the boundary immediately after an allocation when the traversed half-open range remains in bounds. This is the ordinary one-past pattern used by iteration.

A second step beyond that boundary is different. Once the mathematical range extends outside the same allocation, `offset`/`add`/`sub` violate their immediate safety precondition, regardless of whether the out-of-bounds pointer would only be compared and never dereferenced.

This is the central distinction from the wrapping methods: non-wrapping pointer arithmetic carries an immediate "same allocation, in-bounds path" proof obligation.

Basis: **library contract/source** in `offset.md` and `add.md`.

### Zero-sized pointees collapse the byte displacement to zero

The unsafe contracts are phrased in terms of the computed byte offset. For `size_of::<T>() == 0`, every element count produces a mathematical byte offset of zero. The allocation/range precondition is explicitly conditional on the computed offset being nonzero.

The implementation reflects the no-movement behavior: `sub` has an explicit zero-sized-type fast path returning `self`, while the other element-arithmetic paths lower through pointer intrinsics with a zero element size.

This does **not** mean a resulting ZST raw pointer can automatically be converted into a reference or used by every API. Reference construction and APIs requiring non-null/aligned pointers have separate contracts. The narrow conclusion is that element-wise pointer arithmetic itself does not move the address for a zero-sized pointee under this pinned API.

Basis: **library contract/source**; the no-movement conclusion is **derived** from the stated byte-offset formula and implementation.

### Wrapping arithmetic delays the allocation-bound check

`wrapping_offset` is a safe method implemented with `intrinsics::arith_offset`, which the source comments as having no call prerequisites. `wrapping_add` and `wrapping_sub` are safe conveniences built on `wrapping_offset`.

Their documentation deliberately contrasts them with `offset`/`add`/`sub`:

- crossing object boundaries is immediate UB for the non-wrapping operations;
- wrapping arithmetic may produce an out-of-bounds pointer;
- dereferencing that pointer while it is out of bounds remains UB;
- leaving the allocation and later re-entering it is permitted.

For example, the documentation says that applying an offset and then its wrapping inverse can return to the original pointer even if an intermediate pointer left the allocation.

The safe method call therefore means "forming this pointer value is allowed", not "the result is valid for memory access."

Basis: **library contract/source** in `library/core/src/ptr/const_ptr.rs` and `mut_ptr.rs`.

### Wrapping arithmetic preserves source provenance

The wrapping documentation says the result "remembers" the allocation attached to `self`. A numerical address reached from one allocation does not acquire the provenance of another allocation at that address.

The core pointer module explains the model behind that rule: pointer values contain an address plus provenance; derived pointers inherit provenance, and ordinary derivation cannot grow the permissions of that provenance. It specifically uses `wrapping_offset` as an example of a pointer retaining its originating allocation even while its address lies far outside that allocation.

Consequently, arithmetic such as

```text
x.wrapping_offset((y_addr - x_addr) ...)
```

cannot manufacture permission to access `y` when `x` and `y` belong to different allocations merely because the final numerical address equals `y`'s address.

The exact internal structure of Rust provenance remains unspecified at this revision. The durable contract here is the non-transfer of source provenance across address arithmetic, not a commitment to one complete provenance model.

Basis: **library documentation/contract** in `library/core/src/ptr/mod.rs` and the wrapping-method docs.

### Byte arithmetic operates on the data pointer and preserves metadata

The byte methods are implemented as convenience compositions:

- cast the pointer's data address to `*const u8`/`*mut u8`;
- perform the corresponding element arithmetic in units of `u8`;
- reconstruct the original pointer shape with `with_metadata_of(self)`.

For non-`Sized` pointees, the documentation explicitly says the operation changes only the data pointer and leaves metadata untouched.

Thus:

- `byte_offset`, `byte_add`, and `byte_sub` inherit the unsafe in-bounds contract of `offset`/`add`/`sub`, measured in bytes;
- `wrapping_byte_offset`, `wrapping_byte_add`, and `wrapping_byte_sub` inherit the safe-to-form/deferred-access contract of their wrapping counterparts;
- slice length or trait-object metadata is not recomputed to match the shifted data address.

The last point is important for verification. Preserving metadata makes byte arithmetic mechanically available on wide pointers, but it does not establish that the resulting data-pointer/metadata pair describes a valid dereferenceable DST.

Basis: **source/documentation** in `const_ptr.rs` and `mut_ptr.rs`.

### Element arithmetic requires `T: Sized`; byte arithmetic is the wide-pointer escape hatch

The element methods `offset`, `add`, `sub`, and their wrapping versions carry `T: Sized` bounds. Their element count is only meaningful when each element has a statically known size.

The byte methods do not require `T: Sized`. They operate on the data pointer as `u8` and then preserve metadata. At this revision, they are the direct raw-pointer method family for moving the data address of a wide pointer without discarding its metadata.

This distinction should be encoded explicitly in any verifier or model. Treating all pointer arithmetic as "pointer plus integer" loses both the unit (`T` elements versus bytes) and the wide-pointer metadata rule.

Basis: **source** in `const_ptr.rs` and `mut_ptr.rs`.

### Arithmetic safety is independent from alignment

The arithmetic contracts do not add an alignment requirement. The general core-pointer documentation says raw-pointer alignment is an operation-specific access requirement: most read/write functions require proper alignment, while some unaligned operations do not.

Byte arithmetic can obviously move a data address to an address not aligned for the original pointee type while preserving the original pointer metadata. Forming such a pointer is distinct from performing an aligned typed access through it.

For unsafe-code auditing, "pointer arithmetic was legal" and "the resulting access is aligned" are separate proof obligations.

Basis: **library documentation** in `library/core/src/ptr/mod.rs` plus the byte-arithmetic implementation.

### Non-wrapping operations expose optimization-relevant promises

The public docs recommend the unsafe non-wrapping methods when their constraints can be satisfied because they enable more aggressive optimization. The compiler may rely on the in-allocation/no-wrap promises even when the program never dereferences the result.

This is why replacing an unsafe `offset` proof obligation with "the address arithmetic on this machine does not trap" is unsound. The semantic promise exists for optimization, not only for eventual hardware memory access.

Conversely, wrapping arithmetic intentionally avoids making that immediate promise and gives the optimizer less in-bounds information.

Basis: **library contract** in `offset.md` and `add.md`; optimization consequence is explicitly documented.

### Anneal should preserve the operation family, unit, and provenance obligation

For source-to-model verification, these methods should not collapse into one generic integer-pointer addition.

At minimum, a semantic model needs to distinguish:

1. element-count versus byte-count arithmetic;
2. immediate in-allocation arithmetic (`offset`/`add`/`sub`) versus safe-to-form wrapping arithmetic;
3. source provenance retention;
4. the `T: Sized` restriction on element arithmetic;
5. metadata preservation for wide-pointer byte arithmetic; and
6. later access obligations such as alignment and validity.

A translation that preserves only the resulting numerical address can miss UB in the non-wrapping operations and can incorrectly grant access to another allocation after wrapping arithmetic. A translation that models all arithmetic as immediately in-bounds can reject programs that intentionally leave and re-enter an allocation using the wrapping methods.

Basis: **derived verification consequence** from the pinned API contracts.

## Boundaries

**No fresh execution.** No Rust, Miri, Charon, Aeneas, or generated-code experiment was run. The report records exact pinned library contracts and source lowering.

**No complete provenance model.** The pinned core documentation explicitly says Rust provenance and aliasing are not fully specified. The report uses only the guarantees needed by these APIs: derived provenance remains attached to the source allocation and address equality alone does not transfer access permission.

**No pointer-distance methods.** `offset_from`, `byte_offset_from`, and unsigned distance helpers have additional same-allocation and divisibility requirements and are outside this inventory item.

**No address/provenance conversion survey.** `addr`, `with_addr`, `map_addr`, exposed-provenance APIs, and pointer/integer casts belong to the separate provenance-preserving/exposing inventory item.

**No memory-access contract.** `read`, `write`, unaligned access, copy operations, reference creation, and typed-value validity are separate scopes. Arithmetic may be well-defined while a later access is not.

**No claim that runtime UB checks make unsafe arithmetic safe.** The source contains diagnostic UB-precondition checks for some arithmetic overflow conditions. Caller obligations remain semantic and include facts those checks cannot establish.

**No general DST-validity claim.** Byte arithmetic preserves wide-pointer metadata mechanically; it does not prove that the unchanged metadata is valid for the shifted data address.

**No adjacent-version generalization.** These claims are pinned to `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`.

## Evidence

Evidence was inspected on 2026-09-27 at the exact Rust revision behind the Anneal-era nightly.

Primary subject:

- `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`
  - `library/core/src/ptr/const_ptr.rs`, blob `5cbbebf9f478819ee80e0c6486d622ae9ffdac00` — `*const T` implementations and wrapping/byte-method documentation.
  - `library/core/src/ptr/mut_ptr.rs`, blob `53ef7f754d201a1dc08aa50a320266a8ab55245f` — mirrored `*mut T` method families.
  - `library/core/src/ptr/docs/offset.md`, blob `f04f5606ab297a8e62e9215064ee839148197c64` — shared `offset` safety contract.
  - `library/core/src/ptr/docs/add.md`, blob `6e2e87f5f811b5d26f25e331346e8d545ebb4e7d` — shared `add` safety contract.
  - `library/core/src/ptr/mod.rs`, blob `ff2c18d685b65832c296731f23f1664779b874f2` — pointer validity, alignment, allocation, and provenance documentation.

Current reference context used only to preserve scope boundaries:

- `reports/rust-validity-well-defined-execution-nightly-2026-05-31` distinguishes raw-pointer value validity from validity for a particular access and leaves individual raw-pointer API contracts to focused subjects.
- Charon/Aeneas raw-pointer reports describe how the selected translation stack represents or rejects pointer operations; they are not substitutes for the Rust source-language API contract recorded here.

Evidence roles are **library contract/source**, **library documentation**, and **derived** verification consequences. There is no fresh **execution** evidence.

## Revalidation

For a later Rust revision, first inspect the shared pointer arithmetic documentation and method implementations:

1. `library/core/src/ptr/docs/offset.md`;
2. `library/core/src/ptr/docs/add.md`;
3. the `offset`, `add`, `sub`, and wrapping families in `const_ptr.rs` and `mut_ptr.rs`;
4. all six byte-arithmetic methods and their metadata reconstruction;
5. the provenance/allocation discussion in `ptr/mod.rs`.

Specifically check whether later Rust changes any of these boundaries:

- whether non-wrapping arithmetic still requires the mathematical byte displacement to fit `isize`;
- whether the source/result range must remain in one allocation and how one-past results are phrased;
- whether wrapping arithmetic still preserves provenance while allowing temporary out-of-bounds addresses;
- whether element operations remain `T: Sized`;
- whether byte methods still preserve metadata unchanged; and
- whether zero-sized pointee behavior or the conditional allocation requirement changes.

A focused execution suite can add implementation evidence without replacing the contract. Useful cases include:

- one-past `add` followed by an in-bounds `sub`;
- an `offset` that crosses the allocation boundary but is never dereferenced;
- wrapping out of bounds and then back in before dereference;
- a wrapping result whose numerical address equals a different allocation;
- byte arithmetic that misaligns a typed pointer but performs no access;
- wide slice-pointer byte arithmetic demonstrating unchanged metadata; and
- zero-sized pointee arithmetic with large counts.

Run those cases under the exact selected toolchain and, where appropriate, Miri. Treat Miri results as implementation/model evidence, not as a replacement for the pinned library contract or for unresolved language-level provenance rules.
