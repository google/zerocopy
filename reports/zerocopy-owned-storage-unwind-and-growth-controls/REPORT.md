# Owned storage, unwind restoration and vector growth controls

## Summary

The exact PR-stack zerocopy crate passed an original safe-client control for physically unaligned `Unalign<T>` write-back, including an intentional callback unwind and one final destruction. Conditional Boolean transmutation returned each of 254 rejected source bytes unchanged. Vector insertion/growth, a capacity-overflow error, a bounds panic and a zero-sized insertion had the expected contents and cleanup behavior.

A separate Lean model checks single-owner transfer and restoration for both normal and exceptional exits. Its failure and duplication controls expose obligations lost by a byte-only abstraction. The model is manually related to the Rust implementation; it does not prove its pointer, allocator, callback or compiler correspondence.

## Applicability

The crate is the unchanged Git archive of `google/zerocopy@cce761ad53785973ec2f4a6b13715b770b340c87`. The owned client uses Rust 1.99.0 `b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`, edition 2024, native aarch64, default Cargo debug/unwind behavior, and zerocopy `alloc`/`std` features. Dependencies were built offline in a fresh task-owned extraction. The original proof model uses Lean 4.34.1 `5045d0056413266e57c625dcd7c365b10e377c52` and `Std`; no upstream verifier was installed or run.

## Findings

### F1. Unalign restores ownership before safe code resumes

Basis: source + execution + derived.

`wrappers.rs:Unalign::update` has a direct path when `align_of::<T>() == 1`. Otherwise it reads the unaligned owner into an aligned local and wraps that local in `WriteBackOnDrop`; the guard's destructor takes the `ManuallyDrop` value and writes it to the original receiver. The callback accesses the local. Both explicit normal guard destruction and callback unwinding must restore the receiver before the next safe access. Merely proving that the callback returns a value omits this transfer.

The original client places a non-Copy `Tracked` with `Rc<Cell<usize>>` destruction accounting in a packed wrapper inside an eight-aligned container. It checks that the receiver is physically misaligned for `Tracked`, changes 7 to 11 normally, changes 11 to 29 before an intentional panic, catches that unwind, and safely reads the restored 29 through another update. The outside prefix remains 19; the tracked payload is not destroyed during transfer and is destroyed once when the wrapper is dropped. The alignment-one u8 path separately preserves a mutation to 9 during unwind. These intentionally raised callback panics are test inputs, not unexpected internal failures.

`Ownership.lean` distinguishes target and temporary ownership using `Option Nat`. `move_one_owner` and `update_one_owner` check exclusive ownership, and `update_restored` quantifies over both exit constructors and arbitrary old/new values and destruction count. Missing cleanup leaves the target absent; assigning ownership to both locations violates the invariant. This is a simple resource protocol, rather than evidence that a raw bitwise copy has acquired a second usable owner.

### F2. Conditional conversion and rejected growth preserve their source

Basis: source + execution.

`util/macro_util.rs:try_transmute` wraps the source in `ManuallyDrop<ReadOnly<_>>`, validates the selected destination representation, then either reads a destination or reconstructs the original source in the error. All 256 u8-to-bool inputs were exercised. Two accepted values match their independent u8 Boolean encodings; 254 rejected values returned the original byte through `into_src`. This uses the public accessor as an observation and therefore does not independently verify that accessor. No invalid Boolean was constructed by a deliberately incorrect implementation.

`lib.rs:FromZeros::insert_vec_zeroed` checks the insertion position, calls `try_reserve`, moves the possibly overlapping suffix, zeros the new elements, and increases length. The reserve result justifies bounds/overflow before the unsafe operations. The control inserts four u16 zeros in the middle, observes increased capacity and preserved prefix/suffix, then appends two zeros. An additional count of `usize::MAX` returns an error without changing the vector; an invalid position intentionally panics without changing it. Creating sixteen zeroed u16 values and inserting three zero-sized elements also pass.

The overflow control does not simulate a failing allocator under ordinary memory pressure. Increased capacity does not prove that the allocation address changed, nor does it promise address stability. A real reallocation certificate must consume the old allocation's rights and establish the new allocation identity, initialized extent, preserved elements and appropriate freeability.

### F3. The proof interfaces constrain abstraction and compiler certificates

Basis: original definitions + execution + derived.

The Lean insertion operation is `take position ++ replicate additional 0 ++ drop position`. Checked laws cover zero insertion, append-at-end and reserve failure preserving the old list. These represent content interfaces only. The ownership model's restored state does not model real addresses, partial initialization, overlapping copy semantics, destructor panics or concurrent observers. Their adequacy belongs in a separate heap interpretation.

An unsafe-library certificate should identify callback effects and normal/unwind exits; the moved-out receiver's temporary unusability; exactly one transferable owner; cleanup action and destination; allocator result and old/new identities; every initialized/valid element; bounds and arithmetic; and destructor obligations. Unknown callees cannot be justified solely by their return-value specification. A `drop_as_no_op` translation can preserve a byte result while erasing required write-back, so its permitted source class or additional certificate must expose that distinction. The pinned Aeneas configuration boundary is documented in the [pass report](../charon-aeneas-pass-seams-and-certificate-inventory/REPORT.md).

All eight owned Lean endpoints were accepted. The definitional restoration, missing-cleanup and reserve-failure endpoints print no axioms; the other laws print `propext`. These are exact observations conditional on the selected checker and imports. They are not a proof of Rust operational adequacy.

## Boundaries

Not examined: an end-to-end formal proof of these actual Rust bodies, native allocator failure injection, full arbitrary callbacks, destructor panics, double unwinding, process abort, OOM abort, address reuse, custom allocators, padding-copy observability, or concurrent access. The normal/unwind controls cover one non-Copy native payload and one direct u8 path. They are not Kani, Miri or RustBelt verification runs.

The first extraction command used the default Python 3.9, which lacks tarfile's `filter` argument. It stopped before any compilation and left an empty private extraction. That attempt was preserved; a fresh directory and the already available Python 3.14 data filter resolved the environmental mismatch. This was not unsupported zerocopy semantics.

## Evidence

Source: [Unalign implementation](https://github.com/google/zerocopy/blob/cce761ad53785973ec2f4a6b13715b770b340c87/zerocopy/src/wrappers.rs#L329), `update`, guard and destructor, lines 340–394; [conditional helper](https://github.com/google/zerocopy/blob/cce761ad53785973ec2f4a6b13715b770b340c87/zerocopy/src/util/macro_util.rs#L525), lines 525–590; [vector insertion](https://github.com/google/zerocopy/blob/cce761ad53785973ec2f4a6b13715b770b340c87/zerocopy/src/lib.rs#L4098), lines 4098–4132.

Execution: `support/main.rs`, `Ownership.lean`, statuses and exact stdout/stderr. The native result reports three restoration controls, exactly one destruction, 256 conditional inputs and six growth controls, all matching. `results.json` records roughly 2.44 seconds compilation and 52 ms process execution, neither a proof-cost ranking nor a concurrency benchmark. `artifact-identities.json` binds retained files. Evidence acquired 2026-10-14.

## Revalidation

Extract the exact crate into disposable scratch; make an edition-2024 client depending on it with `alloc` and `std`, copy `main.rs`, and run `cargo build --offline` followed by the built executable. Require the full expected result and statuses. Run the specified Lean binary on `Ownership.lean` and check all eight endpoints/dependency lists. Reinspect the guard, reserve-before-copy order and selected callback/drop configuration before interpreting a changed source. New ownership/panic cases require their own resource/exception relation, rather than reuse of the content-only laws.

*Authored by an AI agent acting on joshlf's behalf.*
