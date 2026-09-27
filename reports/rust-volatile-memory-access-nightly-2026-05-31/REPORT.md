# Rust volatile memory access at nightly-2026-05-31

## Summary

At `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (`nightly-2026-05-31`), `ptr::read_volatile` and `ptr::write_volatile` have two deliberately different validity regimes.

For memory inside a Rust allocation, a volatile access obeys the ordinary `read`/`write` rules, including provenance and non-atomic concurrency rules. Volatility adds one guarantee: the compiler treats the access as externally observable, so it will not elide it or reorder it across other externally observable events.

For memory outside every Rust allocation, such as memory-mapped device registers, the pointer does not need ordinary Rust allocation provenance. Any address value, including zero, can be used if the target hardware defines the access. The access still has strict conditions: it must be properly aligned, must not trap, its hardware side effects must not affect Rust-allocated memory, and a volatile read must produce a properly initialized valid `T`.

Volatile does **not** make an access atomic and does not provide inter-thread synchronization. It also does not guarantee one hardware load/store for arbitrary `T`: rustc explicitly permits a volatile value access to split into multiple target-dependent hardware operations, with no stability guarantee on the split. Code for MMIO registers that require one transaction must therefore choose a representation and target contract that independently justify that assumption.

Zero-sized volatile accesses are no-ops and may be ignored, but the pointer must still satisfy `align_of::<T>()`. `read_volatile` bitwise-copies `T` even when `T: !Copy`; using both logical copies can violate ownership rules. `write_volatile` does not drop the overwritten destination or the source argument; semantically it moves the source into the destination. These ownership details make scalar `Copy` register types the conservative model for ordinary MMIO.

No fresh compiler, Miri, or hardware execution was performed. The findings come from the exact pinned standard-library API contract and implementation source.

## Applicability

This report applies to:

- repository: `rust-lang/rust`;
- revision: `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`;
- selected toolchain date: `nightly-2026-05-31`;
- stable APIs `core::ptr::read_volatile` and `core::ptr::write_volatile`;
- their raw-pointer and `NonNull` convenience wrappers to the extent those wrappers delegate to the same functions.

The report distinguishes **inside a Rust allocation** from **outside all Rust allocations** because the API contract does. An address used for MMIO is not merely an unusual pointer into a Rust allocation; the provenance relaxation applies only to the outside-all-Rust-allocations case.

The report does not define device-specific ordering, transaction width, bus semantics, cacheability, or architecture memory barriers. Those properties come from the target/hardware environment and can be stronger or more restrictive than Rust's volatile API contract.

## Findings

### Volatile accesses are externally observable but non-atomic

The public API documentation says volatile operations are intended for I/O memory and are considered externally observable events, like syscalls but less opaque. rustc guarantees that they are not elided or reordered across other externally observable events.

That guarantee does not turn volatile into an atomic synchronization primitive. The same documentation states that volatile access has no special bearing on concurrent access from multiple threads and behaves like a non-atomic access for that purpose. The intrinsics module likewise describes volatile intrinsics as ordered relative to other volatile intrinsics and separately distinguishes atomic intrinsics as the synchronization mechanism with memory orderings.

For verification, `volatile` and `atomic` must therefore remain distinct proof obligations. A proof that an MMIO access is preserved by the compiler does not establish a data-race-free inter-thread protocol.

Basis: **documentation + source** in `library/core/src/ptr/mod.rs` and `library/core/src/intrinsics/mod.rs`.

### Inside a Rust allocation, ordinary pointer rules still apply

For an address inside a Rust allocation, `read_volatile` behaves like `ptr::read` and `write_volatile` behaves like `ptr::write`, except for the externally observable/no-elision-and-reordering guarantee.

The ordinary access rules remain in force, including provenance, allocation bounds, alignment, initialization for reads, and non-atomic aliasing/concurrency requirements. Volatility is not an escape hatch from Rust's pointer model when the memory is Rust-managed.

This distinction matters for unsafe abstractions that use volatile access on ordinary fields, globals, or heap objects. Such code still needs the same provenance and aliasing justification as the corresponding non-volatile access.

Basis: **documentation** in `library/core/src/ptr/mod.rs`.

### Outside all Rust allocations, provenance is intentionally relaxed

For I/O memory outside every Rust allocation, the API contract does not require the pointer to be ordinarily valid for a Rust read or write. The address can be any integer address, including `0` and `usize::MAX`, and the pointer's provenance is irrelevant; the documentation explicitly permits construction with `ptr::without_provenance`.

This relaxation is conditional. The hardware semantics must define the access. It must not trap. Any side effects caused by the access must not affect memory inside a Rust allocation.

The outside-allocation rule is therefore not a general permission to dereference arbitrary integer addresses. It is a specialized contract for non-Rust memory whose behavior is supplied by the target environment.

Basis: **documentation** in `library/core/src/ptr/mod.rs`.

### Alignment remains mandatory, including for zero-sized types

Both `read_volatile` and `write_volatile` require the pointer to be properly aligned for `T`. The implementation contains an unsafe-precondition check for `align_of::<T>()` before calling the compiler intrinsic.

The documentation repeats that alignment requirement for zero-sized types. Although a volatile operation on a zero-sized `T` is a no-op and may be ignored, an unaligned pointer still violates the function's safety contract.

This matches the broader raw-pointer rule that alignment requirements are operation-specific and can survive a zero-byte access.

Basis: **documentation + source** in `library/core/src/ptr/mod.rs`.

### A volatile read must produce a valid initialized `T`

`read_volatile<T>` creates a bitwise copy and requires the read to produce a properly initialized value of type `T`.

For MMIO, that makes the choice of `T` part of the safety proof. If a device register can return arbitrary bit patterns, a Rust type with invalid bit patterns—such as many enums, references, or `bool`—cannot be used merely because the machine load itself is supported. The register representation must admit every hardware value that can actually appear, or the code must use a different byte/integer representation and validate before constructing the narrower Rust type.

This conclusion is **derived** directly from the API's initialized-value requirement.

Basis: **documentation + derived** in `library/core/src/ptr/mod.rs`.

### `read_volatile` preserves the ownership hazards of `ptr::read`

`read_volatile` bitwise-copies `T` regardless of whether `T: Copy`. The original memory remains unchanged. For a non-`Copy` value, subsequently treating both the returned value and the original memory as independently owned values can violate memory safety.

The API documentation explicitly points to the ownership hazard and says storing non-`Copy` types in volatile memory is almost certainly incorrect.

A verifier should therefore not model `read_volatile` as an ordinary Rust move out of memory. It is a raw bitwise read with the same ownership caveat as `ptr::read`, plus volatile observability.

Basis: **documentation** in `library/core/src/ptr/mod.rs`.

### `write_volatile` drops neither the old destination nor its source argument

`write_volatile` overwrites the destination without reading or dropping its old contents. On Rust-managed memory this can leak resources that required destruction.

The function also does not drop the source argument after the store; semantically, the source value is moved into the destination. This matches `ptr::write`-style ownership rather than assignment through a Rust reference.

These semantics matter when reasoning about abstractions that apply volatile operations to resource-owning values. Volatility does not add destructor behavior.

Basis: **documentation** in `library/core/src/ptr/mod.rs`.

### One Rust volatile access may become multiple hardware accesses

The API contract has explicit **Load splitting** and **Store splitting** sections. A simple scalar such as a thin pointer will typically map to one access when the target supports a load/store of exactly that size and alignment. Other values can split into multiple accesses in an unspecified, target-dependent way. Even scalars such as `u128` can split; the documentation gives size/power-of-two examples and states that the splitting strategy has no stability guarantee.

Therefore `read_volatile::<T>` or `write_volatile::<T>` does not by itself prove a one-transaction MMIO operation. If a device register requires exactly one access of a specific width, that property must be justified from the chosen scalar type, alignment, target instruction support, and architecture/device contract. A composite Rust type is especially unsuitable when transaction decomposition matters.

Basis: **documentation + derived** in `library/core/src/ptr/mod.rs`.

### Volatile is not a general memory fence

The preservation guarantee is about the volatile access as an externally observable event. The same API contract explicitly rejects using volatile for inter-thread synchronization.

A program that needs ordering or synchronization of ordinary shared Rust memory must use the appropriate atomic operations, fences, locks, or target-specific mechanisms. Volatile access can coexist with those mechanisms, but it does not substitute for them.

This statement is intentionally narrower than a claim about every compiler reordering of ordinary loads/stores around every volatile operation. The report establishes the API's synchronization boundary, not an exhaustive optimizer model.

Basis: **documentation + derived boundary** in `library/core/src/ptr/mod.rs` and `library/core/src/intrinsics/mod.rs`.

### A verifier needs two validity modes for volatile pointers

The exact contract is easiest to preserve as a two-branch rule:

| Case | Provenance/allocation requirement | Additional obligations |
| --- | --- | --- |
| Inside Rust allocation | Ordinary read/write validity and provenance | Proper alignment; read yields valid initialized `T`; ordinary non-atomic concurrency/aliasing rules; ownership rules |
| Outside all Rust allocations | Ordinary Rust allocation provenance not required; integer-address construction permitted | Hardware defines access; no trap; side effects do not affect Rust allocations; proper alignment; read yields valid initialized `T` |

Both branches are non-atomic. Both can be no-ops for zero-sized `T`, while still requiring alignment. Neither branch supplies a stable promise about how a large/non-native `T` is split into hardware accesses.

This table is **derived** from the two cases and safety sections in the pinned public API documentation.

## Boundaries

**No fresh execution.** No rustc, Miri, emulator, or hardware probe was run.

**No device model.** The report does not establish whether any concrete physical address is MMIO, whether a register access can trap, what side effects it has, or what widths/orderings the device permits.

**No transaction-count guarantee.** The standard-library contract explicitly leaves load/store splitting target-dependent and unstable.

**No inter-thread synchronization.** Volatile accesses are non-atomic. A correct hardware-I/O sequence can still be an invalid Rust data-race protocol if multiple threads access the same Rust memory without synchronization.

**No general provenance bypass.** Provenance is irrelevant only for the outside-all-Rust-allocations I/O case. Volatile operations on Rust allocations retain ordinary provenance requirements.

**No arbitrary invalid-value reads.** A volatile read must yield a valid initialized `T`; the API does not provide a safe way to materialize an invalid Rust value merely because the source is hardware.

**No assertion about compiler barriers beyond the documented contract.** The report does not generalize the externally-observable ordering guarantee into a complete optimizer or CPU-memory-ordering model.

## Evidence

Primary subject: `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (`nightly-2026-05-31`).

- `library/core/src/ptr/mod.rs`, blob `ff2c18d685b65832c296731f23f1664779b874f2`, especially the `read_volatile` and `write_volatile` documentation/implementations: two validity regimes, alignment, initialized-value requirement, ownership behavior, non-atomicity, zero-sized behavior, and load/store splitting.
- `library/core/src/intrinsics/mod.rs`, blob `78d7314c58110b49839894a0f69377f4ee0d1204`, **Volatiles** and **Atomics** module documentation: volatile ordering versus the separate atomic-intrinsic family.
- `library/core/src/ptr/non_null.rs`, blob `b9b42c1efe05a97354be95140923c1b517de84ee`: convenience `NonNull::read_volatile` and `write_volatile` delegate to the `ptr` APIs and inherit their safety concerns. The report does not depend on wrapper-specific semantics.

Observation date: 2026-09-27.

## Revalidation

For another Rust revision, first inspect the `read_volatile` and `write_volatile` documentation in `library/core/src/ptr/mod.rs`. The high-value discriminators are:

1. whether the inside-allocation and outside-allocation cases still exist;
2. whether outside-allocation pointers still ignore provenance and permit `without_provenance`;
3. the no-trap and no-Rust-memory-side-effect conditions;
4. whether alignment is still mandatory for zero-sized operations;
5. the read-validity requirement for `T`;
6. the non-atomic/inter-thread synchronization boundary; and
7. whether load/store splitting remains unspecified.

Then inspect the implementations to confirm the public functions still route to `volatile_load`/`volatile_store` and that any explicit unsafe-precondition checks remain consistent with the prose contract.

For stronger operational evidence on a concrete target, add target-specific probes rather than trying to infer hardware behavior from LLVM or Rust IR alone. Useful probes include a scalar register-width case, a type wider than the native machine access, and an alignment failure under Miri where Miri supports the relevant memory class. Such probes establish only that target/runtime configuration; they do not replace the standard-library contract or the device specification.
