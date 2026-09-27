# Raw-pointer validity, provenance, and alignment at nightly-2026-05-31

## Summary

At the Rust revision behind nightly-2026-05-31, a raw-pointer **value** has much weaker requirements than an operation that reads, writes, offsets, or converts through that pointer. The Rust Reference requires a raw-pointer value to be initialized, but it does not require every raw pointer merely to exist as a value to be non-null, aligned, backed by live storage, or usable for an access. The pinned `core::ptr` documentation therefore rejects a context-free question such as “is this pointer valid?”: the relevant question is whether the pointer is valid for a particular operation and access size.

For a non-zero-sized ordinary memory access, address equality is insufficient. The pointer must identify a live allocation range that contains the accessed bytes, and its provenance must authorize the access. Operations can add further conditions. Ordinary typed reads and writes require alignment; `read_unaligned` and `write_unaligned` deliberately remove that alignment precondition but retain the read/write validity requirements. Creating a reference from a raw pointer is stronger still: the pointer must be aligned, non-null, dereferenceable for the pointee, point to a valid `T`, and satisfy the applicable aliasing rules.

Provenance is part of pointer semantics even though Rust does not yet have a complete final provenance or aliasing model. The pinned core documentation describes a pointer as an address plus provenance that carries spatial, temporal, and mutability permissions. Strict Provenance APIs expose a useful stable discipline: `addr` discards provenance without exposing it; `with_addr` and `map_addr` preserve the provenance of an existing pointer; `without_provenance` creates an address-only pointer that cannot justify ordinary non-zero-sized memory access. Exposed Provenance exists for unavoidable pointer-integer-pointer round trips, but its documentation explicitly says its semantics are substantially less settled.

Alignment is likewise operation-specific. A raw pointer can be misaligned as a value. The Reference says a place based on a misaligned pointer becomes undefined behavior when loaded from or stored to, and the required alignment comes from the type of the pointer used by the last dereference—not merely the final field type. `&raw const` and `&raw mut` can form raw pointers to misaligned places without first creating an invalid reference, which is why the standard library directs packed-field code to those forms before `read_unaligned` or `write_unaligned`.

The practical verification boundary is therefore layered: **raw-pointer representation**, **access provenance/range**, **operation-specific alignment and initialization**, and **reference-formation/aliasing** are distinct obligations. Proving one does not discharge the others.

This report is source- and specification-based. No rustc, Miri, Charon, Aeneas, or generated Lean execution was performed.

## Applicability

This report applies to:

- `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, the compiler and core-library source used by the Rust nightly associated with the Anneal/Charon pin; and
- `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`, the Reference revision bundled by that Rust tree.

The report narrows the broader corpus report `rust-validity-well-defined-execution-nightly-2026-05-31` to the exact obligations attached to raw-pointer values and uses. The neighboring `rust-ub-and-operational-models-nightly-2026-05-31` report owns the broader authority boundary around incomplete Rust semantics, Miri, Stacked Borrows, and Tree Borrows.

This report uses four terms deliberately:

1. **raw-pointer value validity**: whether a value of type `*const T` or `*mut T` may exist as a Rust value;
2. **valid for an access**: whether a pointer may perform one particular read or write of a specified size;
3. **provenance**: semantic access authority beyond a pointer's numerical address; and
4. **convertible to a reference**: whether a raw pointer may be used to create `&T` or `&mut T`.

These are related but not interchangeable.

Pointer arithmetic has its own inventory item. This report records the provenance/range facts needed to understand access validity and uses `offset` only to explain the boundary; it does not replace a complete pointer-arithmetic report.

## Findings

### Raw-pointer value validity is deliberately weak

The Reference's invalid-value rules require raw pointers to be initialized. They do not impose the reference rules of non-nullness, alignment, liveness, or a valid pointee merely because a raw-pointer value exists.

The raw-pointer type chapter states the same distinction operationally: raw pointers have no safety or liveness guarantees, and copying or dropping one does not affect another value's lifecycle. Dereferencing a raw pointer is unsafe, but the presence of an `unsafe` block only asserts that the caller has discharged the operation's extra safety conditions; it does not weaken those conditions.

For thin raw pointers, the Reference goes further on bit validity. Transmuting an integer or integer array into `*const T` or `*mut T` for `T: Sized` is always valid as a pointer value, while the resulting pointer is not thereby usable for dereference. The Reference explicitly warns that such a transmuted pointer may not be dereferenced even for a zero-sized pointee.

The durable distinction is therefore:

> a bit pattern can be a valid raw-pointer value without carrying the authority or other conditions required for a memory operation.

Basis: **normative** Rust Reference.

### Wide raw-pointer metadata has its own validity constraints

Raw pointers to dynamically sized types carry metadata in addition to the data address. The Reference requires slice metadata to be a valid `usize`. For `dyn Trait`, it describes the expected metadata as a pointer to a compiler-generated vtable for the trait, while explicitly noting that this requirement remains debated for raw pointers.

This is a value-validity issue, not yet an access proof. Even valid wide-pointer metadata does not show that the data pointer has the required provenance, liveness, range, alignment, aliasing permission, or initialized pointee.

For a verifier, “raw pointer” therefore cannot always be modeled as one machine address. The representation obligation for a wide raw pointer includes metadata, and some of that metadata contract is itself not fully settled.

Basis: **normative**, including an explicit uncertainty boundary.

### Access validity is relative to operation and size

The pinned `core::ptr` module says directly that it makes no sense to ask whether a pointer is simply valid. Validity depends on whether the operation is a read or write and on the number of bytes accessed.

Its minimum guarantees distinguish zero- and non-zero-sized accesses:

- null is excluded from the module's general notion of validity for reads and writes;
- for a zero-sized access, every non-null pointer is generally valid for reads/writes under that general notion;
- for a non-zero-sized access, the pointer must at least be dereferenceable: the entire accessed range must lie within the allocation identified by the pointer's provenance; and
- dereferenceability is necessary but not sufficient, because aliasing, mutability, synchronization, alignment, and operation-specific conditions can add requirements.

The module then warns that individual functions can have exceptions to the general definition. In particular, some operations such as `read` and `write` permit null pointers when the total access size is zero, while reference-producing operations do not.

The proof obligation must therefore be attached to the exact operation. A reusable predicate named only `valid_pointer(p)` is too coarse unless its meaning includes operation, byte range, and all relevant extra conditions.

Basis: **documentation** in the exact pinned core library.

### Reference and library documentation use “dangling” at different granularities

The Reference defines a pointer/reference as dangling when not all bytes it points to belong to the same live allocation. Under that definition, a zero-sized pointee is trivially never dangling, even at null, because there are no pointed-to bytes.

The `core::ptr` module uses an access-oriented shorthand: it calls a pointer dangling when it is invalid for any non-zero-sized access, and gives null, freed, out-of-bounds, and `NonNull::dangling()` pointers as examples.

These descriptions serve different purposes. A proof should not rely on the bare word “dangling” without preserving its source and access size. The stable operational question is whether the concrete operation's byte range is backed by the required live allocation and authority.

Basis: **normative** + **documentation**; the terminology guidance is **derived**.

### Provenance determines which memory an address may access

The pinned `core::ptr` documentation models a pointer as two semantic components:

- a numerical address; and
- provenance that determines which memory the pointer has permission to access.

It says provenance can constrain spatial extent, temporal extent, and mutability. Pointers derived from an allocation's original pointer inherit provenance; operations may shrink permissions, but ordinary derivation cannot grow them or recombine two disjoint provenances into a larger authority.

The key access rule is explicit: accessing memory through a pointer whose provenance does not cover that memory is undefined behavior. Equal numerical addresses do not repair this. A stale pointer does not regain authority just because a new allocation later occupies the same address, and two pointers at numerically equal boundary addresses remain tied to their different provenance.

The same documentation explicitly says the full structure of provenance is not decided because it interacts with unresolved aliasing rules. The stable result is therefore **that provenance constrains access**, not that one complete provenance calculus has been standardized.

Basis: **documentation**, with the unresolved-model boundary preserved.

### Strict Provenance separates addresses from access authority

At this revision, the stable Strict Provenance APIs make the address/provenance distinction explicit.

`pointer::addr` extracts an address while discarding provenance and, unlike a pointer-to-integer cast, does not expose that provenance for later recovery. Its documentation says that casting the resulting address back to a pointer yields a pointer without provenance, and dereferencing that reconstructed pointer is undefined behavior.

`with_addr` and `map_addr` solve a different problem. They change or map the numerical address while preserving the provenance of an existing pointer. Their intended use is pointer tagging or address manipulation where the program still retains a pointer with sufficient authority for the eventual access.

The module also permits deliberately provenance-less raw pointers, including sentinels, so long as the program does not use them for operations that require non-zero-sized memory authority. This again separates pointer representation from dereferenceability.

These APIs do not fully specify Rust provenance, but they provide a source-level discipline that an analysis can recognize: address extraction alone is not evidence of later access authority; a preserved provenance path matters.

Basis: **documentation/source** in the pinned core library.

### Exposed Provenance is intentionally weaker evidence

Rust also supports pointer-integer-pointer patterns through Exposed Provenance. The pinned documentation describes `expose_provenance` as extracting an address while conceptually adding the pointer's provenance to a set of exposed provenances. `with_exposed_provenance` can later synthesize a pointer from an address, but the documentation says there is no argument that uniquely identifies which exposed provenance should be chosen.

The same section says the semantics are on substantially less solid footing than Strict Provenance, may be unsupported or poorly supported by tools such as Miri and CHERI, and currently cannot guarantee which provenance a reconstructed pointer receives. It gives one hard boundary: if no previously exposed provenance can justify the way the resulting pointer is used, the program has undefined behavior.

For verification, an exposed-provenance round trip is therefore not equivalent to `with_addr`. A proof that needs a specific provenance cannot silently treat an integer cast as preserving that provenance.

Basis: **documentation** with explicit uncertainty.

### Alignment is an access condition, not a raw-pointer representation condition

The core pointer documentation states that a pointer valid for a memory range is not necessarily aligned for its pointee type. Most typed pointer operations impose alignment separately, while `read_unaligned` and `write_unaligned` are named exceptions.

`ptr::read<T>` makes the split concrete. Its safety contract requires:

- `src` valid for reads, unless `T` is zero-sized;
- proper alignment even when `T` has size zero; and
- a properly initialized `T` at the source.

`ptr::read_unaligned<T>` removes only the alignment requirement. It still requires the pointer to be valid for reads and the bytes to represent a properly initialized `T`. `write` and `write_unaligned` have the analogous distinction for writes.

Thus proving alignment does not prove access validity, and choosing an unaligned operation removes only the alignment obligation. Provenance, range/liveness, write permission, concurrency, and typed-value requirements remain separate.

Basis: **documentation/source** in `core::ptr`.

### Misalignment is determined by the pointer that was dereferenced

The Reference defines a place as based on a misaligned pointer when the last `*` projection in place computation used a pointer not aligned for that pointer's pointee type.

This can be stricter than the alignment of the final field. If `ptr: *const S` must be 8-byte aligned, then `(*ptr).byte_field` is based on a misaligned pointer when `ptr` is not 8-byte aligned even if `byte_field: u8` itself needs only 1-byte alignment.

The Reference says a place based on a misaligned pointer leads to undefined behavior when it is loaded from or stored to. It separately permits `&raw const` and `&raw mut` on such a place. By contrast, producing `&` or `&mut` must satisfy reference validity, including the applicable alignment requirement.

This distinction explains the standard library's packed-field guidance: `&packed.field as *const _` is wrong because it first creates an unaligned reference, even if that reference is immediately cast away. `&raw const packed.field` avoids the intermediate reference and can then be passed to `read_unaligned`.

Basis: **normative** + **documentation**.

### Forming a reference from a raw pointer is a stronger operation than raw access

The `core::ptr` documentation defines when a raw pointer is convertible to a reference. The pointer must be:

- properly aligned;
- non-null;
- dereferenceable for the pointee;
- pointing to a valid value of `T`; and
- consistent with the applicable reference aliasing rules.

For a mutable reference, the documentation requires exclusivity against non-derived accesses while the reference exists. For a shared reference, it prohibits mutation except through `UnsafeCell`.

These requirements apply even when the produced reference is unused. A transformation that turns a raw pointer into `&T` or `&mut T` therefore creates obligations that an operation such as `read_unaligned` does not have.

A verifier must not model `&*raw` as a harmless syntactic coercion. It is a semantic strengthening from a permissive raw-pointer value to a reference with stronger validity and aliasing invariants.

Basis: **documentation** + the Reference's independent invalid-reference and aliasing UB rules.

### Alignment tests inspect an address property, not provenance or liveness

`pointer::is_aligned` and `is_aligned_to` check the address against the requested power-of-two alignment. For non-sized pointees, the latter checks only the data pointer and ignores metadata.

A successful alignment test therefore establishes only an address divisibility property. It does not show that the allocation is live, that the accessed range is in bounds, that provenance authorizes the access, that a pointee is initialized, or that aliasing permits the operation.

This matters for proof factoring: an alignment predicate is useful, but it should not be named or consumed as if it were a general pointer-validity predicate.

Basis: **source/documentation**; the proof-design consequence is **derived**.

### Pointer arithmetic can preserve or require provenance without proving access

The pinned `offset` contract requires the non-zero offset to stay within one allocation derived through the pointer's provenance, with the traversed range in bounds and the byte offset fitting `isize`. `wrapping_offset`, by contrast, can temporarily produce an address outside the provenance and later return; dereferencing while out of bounds remains undefined.

These functions show why “the pointer has an address inside allocation X now” is not a complete account. The derivation history/provenance can remain semantically relevant.

The detailed arithmetic matrix belongs to the separate pointer-arithmetic inventory item. For this report, the important fact is that provenance constrains both accesses and some pointer-manipulation operations before any load or store occurs.

Basis: **documentation/source**.

### Const evaluation adds provenance-validity restrictions that should not be generalized to runtime

The Reference adds extra provenance-related value-validity rules specifically in const contexts. Integer-like values may not carry provenance, and pointer-like values must contain either no provenance or correctly ordered fragments of one original pointer.

Those restrictions are important when Anneal evaluates or generates constants, but they are not stated as the general runtime validity rule for raw-pointer values. Runtime code still has the separate access/provenance obligations described above.

A verification model should keep “runtime raw-pointer access authority” distinct from “CTFE value-validity restrictions.” Treating every const-evaluation restriction as a runtime rule would strengthen Rust's documented runtime semantics without support.

Basis: **normative**.

### The reusable verification model is a conjunction of distinct obligations

For a representative typed read from `p: *const T`, the pinned sources support at least these separate questions:

1. **Pointer value:** is the raw-pointer value itself initialized and, for a wide pointer, is its metadata valid enough for the type?
2. **Range/liveness:** does the read's byte range belong to the relevant live allocation?
3. **Provenance:** does `p` carry authority for that range at this time and for this kind of access?
4. **Alignment:** if the chosen operation requires it, is the data pointer aligned for `T`?
5. **Initialization/type validity:** will the operation produce a valid initialized `T`?
6. **Aliasing/mutability:** do the applicable unresolved-but-real pointer/reference rules permit this access?
7. **Concurrency:** is the non-atomic access compatible with concurrent accesses?

Reference creation adds non-nullness, reference validity, and the stronger reference aliasing invariants. Unaligned operations remove the alignment clause, not the others. Zero-sized operations have operation-specific exceptions and should not be generalized from the non-zero-sized case.

This factorization is **derived** from the pinned sources. It is not a claim that Rust's complete unsafe-code semantics has been formalized.

## Boundaries

**No complete final provenance model.** The core documentation says provenance affects access legality, but also says its exact structure remains unsettled with aliasing.

**No complete final aliasing model.** The Reference identifies aliasing violations as UB while stating that the exact rules are not yet determined. This report does not substitute Stacked Borrows, Tree Borrows, or another experimental model.

**Operation-specific exceptions matter.** The general `core::ptr` notion of validity excludes null, but individual zero-sized operations such as `read` and `write` document exceptions. Reference creation does not inherit those exceptions. Do not lift one operation's preconditions to all pointer uses.

**“Dangling” is source-sensitive.** The Reference's pointed-to-byte definition and `core::ptr`'s non-zero-access shorthand differ at zero size. The report therefore prefers explicit range/liveness conditions where the distinction matters.

**Wide raw-pointer metadata remains partly unsettled.** The Reference marks the raw-pointer `dyn Trait` metadata requirement as debated.

**Thin integer-to-pointer transmutation has a specific caveat.** The Reference says the resulting thin raw pointer is a valid pointer value but may not be dereferenced even for a ZST. This report does not weaken that statement based on separate zero-sized-access rules in `core::ptr`.

**Pointer arithmetic is only bounded here.** `offset`, `wrapping_offset`, and provenance are used to expose the access boundary. The separate pointer-arithmetic inventory item should own the complete arithmetic API and overflow/in-bounds matrix.

**Volatile and external/MMIO access are out of scope.** The pinned `read_volatile`/`write_volatile` contracts contain a separate model for memory outside Rust allocations. Those rules should not be inferred from ordinary raw-pointer access.

**Library abstractions can add more invariants.** Proving the raw-pointer obligations here does not prove that an enclosing `Vec`, `Box`, allocator, FFI object, or other abstraction satisfies its own safety contract.

**No fresh execution.** The report does not claim observed rustc/Miri behavior for test cases on this revision.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-27.

**Normative — Rust Reference.** `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`.

- `src/types/pointer.md`, blob `ffd234a3b77dbb4d34f58b4e0b366a79ca7cc2f1`: raw-pointer type semantics, weak liveness guarantees, raw dereference as unsafe, thin raw-pointer bit validity, and wide-pointer metadata validity.
- `src/behavior-considered-undefined.md`, blob `373052061c50fc2f6d1c07a91960d40bac505284`: access through dangling/misaligned places, place-projection bounds, invalid-value production, raw-pointer initialization, wide metadata, misaligned-place rules, dangling definition, and const-context provenance validity.
- `src/unsafe-keyword.md`, blob `7658c1f5c5425d03e2183e89b55260e5e9fd889b`: `unsafe` as an obligation to satisfy extra safety conditions rather than permission to invoke UB.

**Documentation/source — pinned core library.** `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`.

- `library/core/src/ptr/mod.rs`, blob `ff2c18d685b65832c296731f23f1664779b874f2`: access-relative pointer validity, allocation model, alignment, pointer-to-reference conversion, provenance, Strict/Exposed Provenance, `read`/`write`, and unaligned variants.
- `library/core/src/ptr/const_ptr.rs`, blob `5cbbebf9f478819ee80e0c6486d622ae9ffdac00`: raw-pointer `addr`, `with_addr`, `map_addr`, `as_ref`, `offset`, `wrapping_offset`, `is_aligned`, and related method contracts.
- `library/core/src/ptr/docs/addr.md`, blob `785b88a9987090d4d04ebe614fee3fc0d89794ec`: exact Strict Provenance contract for address extraction.
- `library/core/src/ptr/docs/as_ref.md`, blob `2c7d6e149b76a5ec0f58677eaa51925d57aac041`: reference-conversion precondition.
- `library/core/src/ptr/docs/offset.md`, blob `f04f5606ab297a8e62e9215064ee839148197c64`: same-allocation/provenance and in-bounds contract for `offset`.

**Current neighboring corpus authority.**

- `reports/rust-validity-well-defined-execution-nightly-2026-05-31`: establishes the broader distinction among typed value validity, pointer validity for an access, and library invariants.
- `reports/rust-ub-and-operational-models-nightly-2026-05-31`: establishes the authority boundary around incomplete Rust semantics and experimental executable models.

Evidence roles are **normative**, **documentation/source**, and **derived**. There is no fresh **execution** evidence.

## Revalidation

For another Rust toolchain, first resolve the exact `rust-lang/rust` revision and its exact `src/doc/reference` submodule revision. Revalidate both sides of the contract rather than assuming that library docs and Reference prose moved in lockstep.

Inspect, in order:

1. `src/types/pointer.md` for raw-pointer bit validity and wide-metadata rules.
2. `src/behavior-considered-undefined.md` for dangling, misalignment, invalid-value, aliasing, and const-provenance changes.
3. `library/core/src/ptr/mod.rs` for the definitions of access validity, provenance, allocation, alignment, and reference conversion.
4. `const_ptr.rs`/`mut_ptr.rs` and their included docs for `addr`, `with_addr`, exposed-provenance APIs, alignment queries, and pointer arithmetic.
5. `ptr::read`, `read_unaligned`, `write`, and `write_unaligned` for operation-specific exceptions, especially zero-size and null behavior.
6. Current accepted t-opsem/Reference changes before strengthening any statement about the exact provenance or aliasing model.

On an execution-capable surface, preserve a compact discriminating fixture matrix rather than a single “raw pointers work” test:

- null, dangling, and provenance-less raw pointers that are created but never accessed;
- aligned and intentionally misaligned typed reads;
- a packed field obtained via `&raw const` and read with `read_unaligned`;
- the same field incorrectly routed through an intermediate reference;
- `addr` followed by an integer-to-pointer cast versus `with_addr`;
- an exposed-provenance round trip where Miri behavior is recorded with exact flags;
- a live allocation whose address is reused after deallocation to show that numeric address equality does not restore authority; and
- ZST cases, recorded separately because zero-sized access and raw-pointer transmutation have special rules.

Record exact compiler/Miri revision, flags, target, and whether each case is testing a settled Reference rule, a core-library safety contract, or an experimental provenance/aliasing model. Passing Miri cases would confirm only the executions and model exercised; they would not complete Rust's still-unsettled provenance or aliasing semantics.
