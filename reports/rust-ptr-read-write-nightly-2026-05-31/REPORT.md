# `ptr::read`, `read_unaligned`, `write`, and `write_unaligned` at nightly-2026-05-31

## Summary

At `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, the four primitive raw-pointer access operations divide along two independent axes: **read versus write** and **aligned versus unaligned**.

`ptr::read` and `ptr::read_unaligned` produce a typed `T` while leaving the source storage unchanged. The source must be valid for a `size_of::<T>()` read under Rust's pointer/provenance/aliasing rules, and it must contain a properly initialized, valid `T`. `read` additionally requires `align_of::<T>()` alignment; `read_unaligned` deliberately removes that alignment requirement. Producing the returned `T` is a typed operation, so the phrase “bitwise copy” in the ownership documentation must not be upgraded into a guarantee that every padding byte or abstract provenance detail of the complete object representation is preserved.

`ptr::write` and `ptr::write_unaligned` consume a typed `T` and place it into destination storage **without reading or dropping the previous destination value**. The destination therefore need not already contain an initialized `T`; these operations are appropriate for initializing uninitialized storage. `write` requires alignment, while `write_unaligned` does not. If the previous destination value owned resources, overwriting it without arranging for its destruction leaks those resources rather than implicitly dropping them.

The aligned and unaligned operations also differ subtly for zero-sized types. `read` and `write` explicitly allow the memory-access-validity premise to be replaced by “`T` is a ZST,” while retaining the alignment requirement. The public contracts of `read_unaligned` and `write_unaligned` contain no corresponding ZST exception: they require a pointer valid for reads or writes, and the module-level definition says null is never valid. Thus the aligned operations can accept a null pointer for an inhabited ZST, whereas the unaligned operations' documented contracts still exclude null.

All four are ordinary **non-atomic** memory accesses. A verifier therefore needs separate obligations for range/provenance/aliasing, alignment where applicable, source typed validity for reads, ownership/resource state, and concurrency. Debug UB checks in the implementation test only a small subset of those obligations and are not a soundness mechanism.

This is a pinned source/specification report. No fresh rustc, Miri, Charon, Aeneas, or Anneal execution was performed.

## Applicability

The directly examined implementation is the core library at `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, the compiler revision behind Anneal's `nightly-2026-05-31`. The directly examined language-level background is `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`.

The report covers the free functions:

- `core::ptr::read`;
- `core::ptr::read_unaligned`;
- `core::ptr::write`; and
- `core::ptr::write_unaligned`.

It also covers their inherent raw-pointer method forms because the pinned `*const T` / `*mut T` implementations delegate directly to those free functions and state that callers must uphold the same safety contracts.

The core pointer module's phrase **valid for reads/writes** is operation-relative rather than a timeless property of a pointer. For these single-value operations the implicit access size is `size_of::<T>()`. For nonzero-sized accesses, dereferenceability requires the accessed range to lie within the live allocation selected by pointer provenance; that condition is necessary but not always sufficient because Rust's complete aliasing rules remain unsettled. The report therefore treats “valid for reads/writes” as a primitive obligation constrained by the pinned documentation rather than pretending to supply a complete memory model.

The report does not subsume separate reference-corpus subjects for raw-pointer provenance generally, pointer arithmetic, bulk copies, `MaybeUninit`, padding, reference creation, volatile accesses, atomics, or allocation APIs. It uses those concepts only where they determine the four operations' contracts.

## Findings

### The four operations form a small contract matrix

| Operation | Access requirement | Alignment | Existing destination initialization | Typed-value requirement | Ownership effect |
| --- | --- | --- | --- | --- | --- |
| `read<T>(src)` | `src` valid for reads, or `T` is ZST | required even for ZST | n/a | source must contain initialized valid `T` | returns another `T`; source storage remains unchanged |
| `read_unaligned<T>(src)` | `src` valid for reads | not required | n/a | source must contain initialized valid `T` | returns another `T`; source storage remains unchanged |
| `write<T>(dst, src)` | `dst` valid for writes, or `T` is ZST | required even for ZST | not required | `src` is the typed value being moved | old destination is not dropped; `src` is moved into destination |
| `write_unaligned<T>(dst, src)` | `dst` valid for writes | not required | not required | `src` is the typed value being moved | old destination is not dropped; `src` is moved into destination |

The aligned functions' ZST exception is explicit in their safety text. The unaligned functions' safety text instead requires validity without that exception. This matters because the pointer module defines null as never valid, even for zero-sized accesses, while separately noting that specific operations such as `read` and `write` can make an explicit zero-size exception.

Basis: **documentation + source** in `library/core/src/ptr/mod.rs`.

### Read validity is not only an address-range check

For a nonzero-sized access, the pointer module says a pointer must at least be dereferenceable: provenance identifies an allocation, and the full access range must fit inside that live allocation. It immediately warns that dereferenceability is necessary but not always sufficient because validity also depends on aliasing rules that are not yet fully defined.

The same module says its ordinary memory accesses are non-atomic. Concurrent accesses to the same memory from different threads are undefined unless all concurrent accesses only read. Thus a proof of `read` or `read_unaligned` cannot stop at “the address is mapped” or even “the bytes fit in an allocation.” It needs enough provenance, liveness, aliasing, and concurrency state to establish the operation-relative read permission.

The Reference independently lists data races, accesses through dangling pointers, and aligned loads/stores through misaligned pointer-based places among undefined behavior. Its validity list also says producing an invalid typed value is immediate UB.

Basis: **documentation** in the pinned core pointer module + **normative** Rust Reference.

### Reads additionally require a valid initialized `T`

Both read variants explicitly require the source to point to a properly initialized value of type `T`. This is stronger than merely having readable bytes.

The Reference's invalid-value rules make the reason visible: producing a value happens when a value is read from a place or passed through primitive/function boundaries, and producing an invalid value is immediate UB. The validity conditions are type-directed. For example, scalar integers, floats, and raw pointers must be initialized; `bool` has only two valid values; enums need a valid discriminant and valid fields; references carry still stronger conditions.

Therefore an Anneal obligation for `ptr::read::<T>` needs at least two conceptually distinct premises:

1. **memory-access authority** — the source range is valid for the read under provenance/liveness/aliasing/concurrency rules; and
2. **typed-value validity** — reading those bytes as `T` produces a valid initialized `T`.

A readable `MaybeUninit<T>` allocation, for example, does not by itself justify `ptr::read::<T>` if the contained `T` has not been initialized and made valid.

Basis: **documentation** in `core::ptr` + **normative** Reference invalid-value rules + **derived** verification decomposition.

### `read` is aligned; `read_unaligned` removes only that premise

`ptr::read` requires `src` to be properly aligned for `T`, including when `T` has size zero. The implementation contains a debug-only unsafe-precondition assertion for alignment/non-nullness and lowers the actual access through the private `read_via_copy` intrinsic, which the surrounding source describes as a typed MIR load.

`ptr::read_unaligned` removes the alignment requirement, not the other requirements. Its public safety contract still requires `src` to be valid for reads and to contain an initialized valid `T`. The implementation copies `size_of::<T>()` bytes into a fresh `MaybeUninit<T>` and then calls `assume_init`.

This distinction is especially important for packed fields. Creating `&packed.field as *const _` first creates an unaligned reference and is already invalid; the documentation instructs callers to create a raw pointer with `&raw const packed.field` and then use `read_unaligned`.

For verification, “unaligned” should therefore be modeled as a targeted relaxation of the alignment premise, not as a general relaxation of provenance, range, initialization, aliasing, or data-race rules.

Basis: **documentation + source** in `core::ptr`; **normative** Reference misaligned-place rules.

### A read duplicates representation-level ownership even though the source bytes remain in place

The read documentation deliberately says two things that must be understood together:

- the source memory is unchanged; and
- the operation creates a copy of `T` regardless of whether `T: Copy`.

For `T: !Copy`, continuing to use both the returned value and the original source value can violate memory safety. The canonical example is an owning value such as `String`: after `read`, both representations can name the same allocation. Dropping or otherwise consuming both as independent owners can double-free. A common safe pattern is to regard the source as logically moved-out and later overwrite it with `ptr::write` without dropping the stale representation.

This is not ordinary Rust move syntax: the bits at `src` are not automatically deinitialized. The proof state must carry the logical ownership transition explicitly.

Basis: **documentation** in `core::ptr::read` / `read_unaligned` + **derived** ownership obligation.

### “Bitwise copy” is not a complete-padding preservation guarantee

The read documentation uses “bitwise copy” to explain why non-`Copy` ownership can be duplicated. At this same Rust revision, however, the implementation intentionally makes `read` a **typed** load (`read_via_copy`) rather than an untyped `copy_nonoverlapping` operation. The pinned `MaybeUninit` documentation separately states the general typed-copy rule: moving or copying a typed value preserves the non-padding contents needed for the value but may lose initialized padding bytes, and copying reference-containing values can implicitly reborrow them.

`read_unaligned` uses an untyped byte copy internally to a fresh `MaybeUninit<T>`, but its result crosses the typed `assume_init` boundary. Its public contract likewise promises the returned `T`, not equality of every padding byte in the source's complete object representation.

Therefore neither read function should be used as a proof primitive for “all `size_of::<T>()` abstract bytes, including initialized padding and provenance fragments, are reproduced identically in the returned value.” Use the dedicated untyped-copy operations when exact byte-initialization preservation is the required property, and carry a separate argument for later typed interpretation.

Basis: **source** in `core::ptr` and private intrinsics + **documentation** in `MaybeUninit` + **derived** boundary. The dedicated initialization/padding report owns the broader typed-copy semantics.

### `write` can initialize storage and never reads the old `T`

`ptr::write` overwrites a destination without reading or dropping the previous contents. Its safety contract requires the destination to be valid for writes (or `T` to be a ZST) and aligned, but it does **not** require the destination to already contain an initialized `T`.

This makes `write` suitable for:

- initializing allocated but uninitialized `T` storage; and
- filling storage that has been logically moved out with `ptr::read`.

The implementation uses `write_via_move`, and its source comment says this lowers to a typed `*dst = move src` operation without the normal assignment behavior of first dropping the old destination value.

A verifier should therefore not model `ptr::write(dst, src)` as ordinary Rust `*dst = src`. Ordinary assignment to an initialized place includes destruction/replacement semantics for the old value; `ptr::write` intentionally omits that destruction.

Basis: **documentation + source** in `core::ptr` and `core::intrinsics`.

### Overwriting a live owner can leak resources without being UB by itself

Because `write` and `write_unaligned` do not drop the old contents, overwriting an initialized value that owns resources can leak those resources. The documentation explicitly calls this safe but cautions that allocations or resources can be leaked.

The key modeling distinction is between **memory safety** and **resource-accounting correctness**. If `dst` satisfies the write-access contract, the primitive does not require proof that the old logical owner has been dropped. A higher-level specification may still require that resources are eventually released. Anneal should avoid silently turning “no leak” into a Rust UB premise unless another semantic rule actually requires it.

Basis: **documentation** + **derived** verification consequence.

### `write_unaligned` relaxes alignment but preserves the rest of the write contract

`ptr::write_unaligned` allows an unaligned destination. It still requires the destination to be valid for writes, does not drop the previous destination contents, and semantically moves `src` into the destination.

Its implementation performs an untyped `copy_nonoverlapping` from the by-value `src` parameter's storage into `dst`, then directly invokes the forget intrinsic so that `src` is not dropped. That implementation detail does not strengthen the public contract into a caller-visible guarantee that every pre-call padding byte of the caller's original value survives: passing `src` by value is itself a typed move boundary.

For packed fields, the same raw-pointer-formation rule as the read case applies. Use `&raw mut packed.field`; creating a reference to an unaligned field before casting is already invalid.

Basis: **documentation + source** in `core::ptr`; **documentation** in `MaybeUninit` for typed-copy/padding boundary.

### Zero-sized types have a deliberately nonuniform null-pointer edge case

The pointer module defines null as never “valid for reads/writes,” including zero-sized accesses. It then says particular operations can explicitly permit null when their total access size is zero.

`read` and `write` do exactly that: their first safety bullet is “valid for reads/writes **or `T` must be a ZST**.” They still require proper alignment even for a ZST. For an inhabited ZST, this makes a null pointer acceptable under those pointer/range premises; address zero satisfies ordinary power-of-two alignment.

`read_unaligned` and `write_unaligned` do not contain that exception. Their contracts simply require validity for reads/writes. Under the same module definition, null therefore remains outside their documented contract even though their implementations ultimately perform a zero-byte copy for a ZST.

The read functions' typed-value-validity requirement also remains. An uninhabited zero-sized type does not become readable merely because no bytes are transferred.

For Anneal, the ZST rule should be attached to the **specific operation contract**, not inferred globally from `size_of::<T>() == 0`.

Basis: **documentation** in the pinned pointer module + **derived** comparison of the four explicit contracts.

### Debug UB assertions are incomplete diagnostics, not proof obligations discharged at runtime

The aligned `read` and `write` implementations contain `#[cfg(debug_assertions)]` calls to Rust's unsafe-precondition checking machinery. These checks cover alignment and nullness, with their ZST exception. They do not establish allocation provenance, full range validity, aliasing permission, source initialization/type validity, or absence of a data race.

The unaligned variants do not need the alignment check and are implemented through lower-level copy machinery.

A verifier must use the documented safety contract, not the presence or absence of these runtime/debug assertions, as the obligation boundary. Passing an assertion is not evidence that the unsafe operation is sound; disabling debug assertions does not weaken the language-level precondition.

Basis: **source** + **derived** verification consequence.

### Raw-pointer method syntax does not change the contract

At the pinned revision:

- `*const T::read` delegates to `ptr::read`;
- `*const T::read_unaligned` delegates to `ptr::read_unaligned`;
- `*mut T::read` and `*mut T::read_unaligned` delegate to the same read functions;
- `*mut T::write` delegates to `ptr::write`; and
- `*mut T::write_unaligned` delegates to `ptr::write_unaligned`.

Each method explicitly says the caller must uphold the corresponding free function's safety contract. A verification frontend may therefore normalize method syntax to the free-function operation without losing semantics, provided it preserves the same pointer value and type.

Basis: **source** in `library/core/src/ptr/const_ptr.rs` and `mut_ptr.rs`.

## Boundaries

**No fresh execution.** This report did not run rustc, Miri, Charon, Aeneas, or Anneal. It records exact pinned public contracts and implementation structure. A future execution probe can strengthen diagnostics/model-coverage claims, but the documented unsafe preconditions do not depend on such a probe.

**Rust's full aliasing/provenance model is still incomplete.** The pinned pointer documentation and Reference both say the exact rules are not completely settled. This report preserves the minimum stated validity requirements and does not invent a total operational semantics.

**Padding and provenance identity across typed copies are not fully re-derived here.** The report records only the consequence needed to avoid treating these accesses as whole-object byte-preservation primitives. The dedicated initialization/padding and provenance reports should remain the detailed authorities for those subjects.

**No `read_volatile` / `write_volatile`.** Volatile accesses deliberately have a different contract, including a special outside-Rust-allocation case, and are outside this package.

**No atomics.** These functions are ordinary non-atomic accesses. Atomic ordering, synchronization, and the atomic memory model are separate subjects.

**No `copy` / `copy_nonoverlapping`.** Those are untyped range-copy operations with different initialization/padding semantics and their own overlap contracts.

**No `drop_in_place`, `replace`, or `swap`.** They compose related primitives but have additional contracts. In particular, `drop_in_place` has a distinct and partly unresolved validity boundary.

**Const evaluation is not separately characterized.** The four functions are const-stable at this compiler revision, but const evaluation applies additional provenance restrictions recorded elsewhere in the Reference. This report's runtime-oriented contract should not be read as an exhaustive const-eval model.

**Adjacent versions are not covered.** No continuity is inferred for another Rust nightly merely because the APIs are stable.

## Evidence

Primary compiler/core subject: `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`nightly-2026-05-31`).

- `library/core/src/ptr/mod.rs`, blob `ff2c18d685b65832c296731f23f1664779b874f2`:
  - module-level validity/provenance/non-atomic/alignment contract near the file beginning;
  - `read` around lines 1586–1741;
  - `read_unaligned` around lines 1743–1825;
  - `write` around lines 1827–1956;
  - `write_unaligned` around lines 1958–2025.
- `library/core/src/ptr/const_ptr.rs`, blob `5cbbebf9f478819ee80e0c6486d622ae9ffdac00` — inherent `read` / `read_unaligned` delegations around lines 1182–1225.
- `library/core/src/ptr/mut_ptr.rs`, blob `53ef7f754d201a1dc08aa50a320266a8ab55245f` — inherent read delegations around lines 1274–1317 and write delegations around lines 1429–1491.
- `library/core/src/intrinsics/mod.rs`, blob `78d7314c58110b49839894a0f69377f4ee0d1204` — private `read_via_copy` / `write_via_move` intrinsics around lines 2204–2220.
- `library/core/src/mem/maybe_uninit.rs`, blob `7e2c6b9b3bcb2d66af376243d95c541e5bd4024` — typed-copy, padding, and implicit-reborrow documentation around lines 275–318.

Primary Reference subject: `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`.

- `src/behavior-considered-undefined.md`, blob `373052061c50fc2f6d1c07a91960d40bac505284` — data races; dangling/misaligned accesses; incomplete aliasing rules; production of invalid values; misaligned load/store distinction; type-directed validity.
- `src/memory-model.md`, blob `cc3cf02ec0adba12134ad6cb82e51a4b864da784` — initialized and uninitialized abstract bytes.

Native corpus state was checked at `google/zerocopy` `reference@b6c1ba9f891840fc95a1de167bc17ebc38f5cf07`. Its 105-report `CATALOG.json` has no dedicated package for this four-operation contract; the existing `rust-validity-well-defined-execution-nightly-2026-05-31` report is a broader validity/UB boundary, not a replacement for this operation-specific matrix. Live issue #3720 still listed **`ptr::read` / `read_unaligned` / `write` / `write_unaligned`** as unchecked when this evidence was gathered.

No execution evidence is claimed.

## Revalidation

For another Rust revision, the cheapest source-level revalidation is narrow:

1. Re-read the pointer module's top-level **Safety** and **Alignment** text. Check whether “valid for reads/writes,” ZST validity, provenance, and non-atomic concurrency rules changed.
2. Diff the safety sections and implementations of `read`, `read_unaligned`, `write`, and `write_unaligned` in `library/core/src/ptr/mod.rs`.
3. Confirm whether the aligned operations still carry an explicit ZST exception and whether the unaligned operations still omit it.
4. Confirm whether `read`/`write` remain typed operations (`read_via_copy` / `write_via_move`) and whether the unaligned variants still use byte copying plus typed construction/move suppression.
5. Re-read `MaybeUninit`'s typed-copy/padding/reborrow notes before making any claim about complete representation preservation.
6. Re-check the Reference's dangling/misaligned/data-race/invalid-value rules and any newly stabilized aliasing/provenance model.
7. Confirm that raw-pointer inherent methods still delegate without adding or relaxing preconditions.

If stronger operational evidence is needed, run a bounded exact-revision Miri/rustc specimen matrix covering:

- aligned initialized read;
- unaligned initialized read via `&raw const`;
- aligned and unaligned writes into `MaybeUninit<T>` storage;
- non-`Copy` read followed by disciplined source overwrite versus double use;
- aligned ZST read/write through null;
- unaligned ZST null calls, treated as contract-violating even if an implementation happens not to touch memory;
- invalid/uninitialized `T` reads;
- dangling/out-of-bounds pointers;
- packed-field raw-pointer formation; and
- conflicting concurrent non-atomic access where a suitable concurrency interpreter/model exists.

Preserve compiler commit, target, flags, exact source, and observed diagnostics. Such experiments can test enforcement and tool modeling, but they should not replace the public unsafe contracts as the semantic source of truth.
