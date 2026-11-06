# Rust Allocation, `Box` Raw Conversions, Typed Storage Transfer, and MIR Drop Elaboration

## Summary

Sound verification of heap-allocated and by-value storage transformations in Rust and `zerocopy` requires tracking five distinct semantic layers that cannot be collapsed into untyped byte arrays or syntactic `Drop` markers:

1. **Allocation and deallocation contracts (`Layout`, `GlobalAlloc`, `Allocator`, `Global`):** `core::alloc::Layout` permits zero-sized layouts (`size() == 0`) provided alignment is a non-zero power of two and the size rounded up to alignment is at most `isize::MAX`. However, `GlobalAlloc::alloc` and `alloc_zeroed` make zero-sized requests undefined behavior, require exact `Layout` matching on `dealloc` and `realloc`, and forbid unwinding from allocator implementations. By contrast, the unstable `core::alloc::Allocator` trait permits zero-sized allocations, returns `NonNull<[u8]>` carrying an actual allocation size that may exceed `layout.size()`, and requires a *fitting* layout on deallocation and resize (`alloc::alloc::Global` bridges zero-sized requests by returning `NonNull::slice_from_raw_parts(layout.dangling(), 0)` without invoking `GlobalAlloc`). Across both traits, successful reallocation (`realloc`, `grow`, `shrink`) transfers ownership and invalidates the old pointer even when the numerical address is unchanged, whereas failed reallocation leaves the original allocation live and unaltered.
2. **`Box` raw-pointer ownership handoff (`into_raw`, `from_raw`, allocator-aware and `NonNull` forms):** `Box::into_raw` consumes a `Box<T>`, suppresses its destructor via `ManuallyDrop`, and hands off a non-null, aligned raw pointer together with a linear obligation to destroy `T` and deallocate its storage (or intentionally leak it). `Box::from_raw` performs the unchecked inverse handoff (`Unique::new_unchecked`): for non-zero-sized pointees the storage must belong to the matching allocator with layout `Layout::for_value_raw(ptr)` (which depends on wide-pointer slice-length or vtable metadata when `T: ?Sized`), whereas for zero-sized pointees no live allocation is required (`NonNull::dangling().as_ptr()` suffices) provided the pointer is non-null, aligned, and points to a valid `T`.
3. **Typed storage transfer, uninitialized padding, and conditional conversion exits:** Untyped byte copies (`core::ptr::copy_nonoverlapping`) preserve byte-level initialization state (`Initialized` vs. `Uninit`), whereas by-value `core::mem::transmute` does not guarantee preservation of padding bytes and `MaybeUninit<T>` does not require padding bytes to be initialized for `assume_init`. In `zerocopy`, by-value `try_transmute<Src, Dst>` wraps the source in `ManuallyDrop<ReadOnly<Src>>` before validation so that success performs a bitwise `core::ptr::read_unaligned` of `ReadOnly<Dst>` without running `Src`'s destructor, validation failure restores original `Src` ownership via `ManuallyDrop::into_inner`, and validation panic leaks the suppressed source without exposing a duplicate owner. Similarly, `Unalign<T>::update` moves a misaligned non-`Copy` field onto the stack inside a `WriteBackOnDrop` guard whose destructor writes the updated value back to the packed receiver on both normal return and callback unwinding.
4. **Compiler MIR drop elaboration vs. downstream verifier extraction (`rustc`, Charon, Aeneas):** Rust source semantics condition destruction on runtime initialization: local scopes drop variables in reverse declaration order, whereas struct and tuple fields drop in forward declaration order, and partial moves deinitialize moved fields while leaving sibling fields droppable. `rustc` lowers pre-elaboration MIR `Drop` terminators through `ElaborateDrops` (`MaybeInitializedPlaces` and `MaybeUninitializedPlaces` dataflow), classifying drops as `Dead`, `Static`, `Conditional` (guarded by compiler-synthesized stack Boolean flags such as `_16: bool`), or `Open` (recursively expanded into per-field drop ladders with `unwind terminate(cleanup)` double-panic guards). At the pinned toolchain, Charon's default and `--preset=aeneas` modes extract `MirLevel::Promoted` (before `ElaborateDrops`, tagging drops as `DropKind::Conditional`), while Aeneas defaults to `drop_as_no_op = true` and even under `-eval-drops` only invalidates the symbolic place (`VBottom`) without invoking the retained destructor function pointer.
5. **Operational `ResumeUnwind` frame cleanup and MiniRust lowering (`rustc` 1.99.0/1.99.1, MiniRust, Lean 4.34.1):** Because `<T as Drop>::drop(&mut self)` reads and mutates its receiver's fields, clearing a drop flag before destructor entry cannot be lowered to `MiniRust::Statement::Deinit` (which overwrites payload bytes with `Uninit`). In MiniRust, `ResumeUnwind` pops the callee frame first, deallocates live callee stack locals via `storage_dead`, runs `self.mem.end_call(frame.extra)?` (releasing Tree Borrows protectors in list order with non-rollback partial state mutation if a strong protector faults mid-list), and jumps to `caller.unwind_block`. Meanwhile, `tooling/minimize` lowers MIR `Drop` to `Terminator::Call` with `unwind_block: None` and rejects `TerminatorKind::UnwindTerminate` with `span_bug!`. Seven Lean 4.34.1 operational models (141 `#print axioms` audits) and an executable `zerocopy` ownership/growth harness verify these state transitions and their negative controls.

## Applicability

This report synthesizes evidence across the pinned Rust compiler/library snapshots, Rust Reference revisions, downstream verification tools, MiniRust specifications, `zerocopy` revisions, and Lean 4 proof artifacts declared in `REPORT.json`:

- **Rust compiler and standard library (multi-version coverage):**
  - `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` and `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (`1.98.0-nightly`, toolchain date `2026-05-31`): primary sources for `core::alloc::{Layout, GlobalAlloc, Allocator}`, `alloc::alloc::{alloc, dealloc, realloc, alloc_zeroed, Global, handle_alloc_error}`, `alloc::boxed::Box` raw conversions, and `rustc_mir_transform::elaborate_drops`.
  - `rust-lang/rust@d8ef4f3fe7031514cbd7d056b7b058814987ecec`: standard-library contracts for `core::ptr::copy_nonoverlapping`, `core::intrinsics::transmute`, `core::mem::{MaybeUninit, ManuallyDrop, forget}`, `core::alloc::GlobalAlloc`, and `alloc::raw_vec::RawVec`.
  - `rust-lang/rust@b940084d7eb6a299eb4bfeb8e34901bc051e7ac4` (release `1.99.0`, examined on `aarch64-apple-darwin`) and `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67` (release `1.99.1`, examined on `x86_64-unknown-linux-gnu`, edition `2024`): used for `Runtime(PostCleanup)` MIR drop-elaboration captures (`cleanup_binding.mir` and `cleanup_binding.1.99.1.mir`) and native execution of the `zerocopy` owned-storage, unwind, and vector-growth controls.
- **Rust Reference revisions:** `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476` (bundled with `2026-05-31`), `2dafab96d919d6ab2884488e970bf95610ff83eb`, and `82da570bafd9efed421bdbae0f8603ede8dd308b` (normative drop order, partial moves, assignment destruction, type layout, and panic/unwind rules).
- **Downstream verification extractors and operational specifications:**
  - Charon `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (`0.1.210`) and Aeneas `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`).
  - MiniRust `minirust/minirust@d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed` (`spec/lang/syntax.md`, `spec/lang/step/statements.md`, `spec/lang/step/terminators.md`, `spec/mem/tree_borrows/memory.md`, `tooling/minimize/src/bb.rs`).
  - Lean 4 kernel checker `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`4.34.1`, `x86_64-unknown-linux-gnu`).
- **`zerocopy` repository:** `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` and `google/zerocopy@8fb35253fbc703cb2cd0997f4efcda76cf9062b6` (`zerocopy/src/lib.rs`, `zerocopy/src/impls.rs`, `zerocopy/src/wrappers.rs`, `zerocopy/src/util/macro_util.rs`), plus the preserved owned input bundle (`source_sha256: 75a13d53c6848933548808660af50b58637387840f5aeec89a380ecb184b907e`).

**Cross-version invariance vs. version-specific differences:**
- *Invariant across examined `rustc` revisions (`2026-05-31` nightly `14210df0e27c` / `f8a08b688cbe`, `d8ef4f3fe703`, `1.99.0` `b940084d7eb6`, and `1.99.1` `58cf8f9c35b3`):* `Layout` well-formedness rules, `GlobalAlloc` vs. `Allocator` zero-size and layout-matching contracts, `Box::into_raw`/`Box::from_raw` ownership and ZST/DST rules, forward struct-field vs. reverse scope-local drop order, and `ElaborateDrops` `Dead`/`Static`/`Conditional`/`Open` lowering. In particular, compiling `cleanup.rs` under `rustc 1.99.0` (`aarch64-apple-darwin`) and `rustc 1.99.1` (`x86_64-unknown-linux-gnu`) produces byte-for-byte identical `Runtime(PostCleanup)` MIR for `exercise`, `<Leaf as Drop>::drop`, and `make` (differing only in the 40-character sysroot commit hash inside `EVENTS::{constant#0}`).
- *Version-sensitive distinctions:*
  - `ManuallyDrop<T>` documentation in `library/core/src/mem/manually_drop.rs` (lines 94–144 at `d8ef4f3fe7031514cbd7d056b7b058814987ecec`) explicitly notes that calling `ManuallyDrop::drop` and then moving the enclosing `ManuallyDrop<Box<T>>` had a stronger uniqueness restriction prior to Rust 1.96; verifiers must not backport post-1.96 `ManuallyDrop<Box<T>>` move permissions to pre-1.96 toolchains.
  - `Box::into_non_null` / `Box::from_non_null` (gated under `box_vec_non_null`) and `Allocator` / `Box::into_raw_with_allocator` / `Box::from_raw_in` (gated under `allocator_api`) remain unstable across the examined snapshots.

## Findings

### 1. Low-Level Allocation, Reallocation, and Deallocation Contracts (`Layout`, `GlobalAlloc`, `Allocator`, `Global`)

`Basis: documentation | source | derived`

At `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` and `rust-lang/rust@d8ef4f3fe7031514cbd7d056b7b058814987ecec` (structured in `support/rust-allocation-deallocation/allocation-contract-matrix.json` and `support/rust-allocation-deallocation/source-map.json`), low-level heap allocation is split across two distinct trait contracts:

| Dimension | `core::alloc::GlobalAlloc` & `alloc::alloc::{alloc, alloc_zeroed, realloc, dealloc}` | `core::alloc::Allocator` & `alloc::alloc::Global` |
| --- | --- | --- |
| Stability | Stable | Unstable (`#![feature(allocator_api)]`) |
| Zero-sized `Layout` (`size() == 0`) | **Undefined behavior** for `alloc` and `alloc_zeroed`; `realloc` requires `new_size > 0`. | **Permitted.** `Global::allocate` intercepts `layout.size() == 0` and returns `Ok(NonNull::slice_from_raw_parts(layout.dangling(), 0))` without calling `GlobalAlloc`. |
| Return representation | `*mut u8` (null indicates recoverable exhaustion unless allocator aborts). | `Result<NonNull<[u8]>, AllocError>` carrying both base address and actual byte length ($\ge \text{layout.size}()$). |
| Deallocation layout precondition | `ptr` must be currently allocated by this allocator and `layout` must be the **exact** `Layout` used to allocate/reallocate it (`dealloc` wraps `ptr` in `NonNull::new_unchecked`). | `ptr` must be currently allocated by this allocator and `layout` must **fit** the block (identical alignment, and `layout.size()` between requested size and returned slice length). |
| Resize (`realloc` vs. `grow`/`shrink`) | `realloc(ptr, layout, new_size)` keeps `layout.align()`, requires `0 < new_size` with rounded `new_size <= isize::MAX`, and preserves `0..min(layout.size(), new_size)`. | `grow`/`grow_zeroed` require `new_layout.size() >= old_layout.size()`; `shrink` requires `new_layout.size() <= old_layout.size()`. Alignment may change. |
| Ownership transfer on resize | On non-null (`Ok`) return, ownership of the old block transfers and **any access through the old pointer is UB even if the numerical address is unchanged**. On null (`Err`) return, the old block and its contents remain live and intact. | Same success/failure ownership split as `GlobalAlloc::realloc`. |
| Unwind & failure policy | Unwinding from any `GlobalAlloc` method is **undefined behavior**. `handle_alloc_error` diverges (aborts by default under `std`, panics under `no_std`). | Implementations may return `Err(AllocError)` or abort if backed by an aborting native allocator. |

Additional verification-critical invariants:
- **`Layout` well-formedness vs. allocator admissibility (`library/core/src/alloc/layout.rs`):** `Layout::from_size_align` and `from_size_align_unchecked` require `align` to be a non-zero power of two and `size` rounded up to `align` not to exceed `isize::MAX`. Because `Layout` allows `size == 0`, proving a `Layout` well-formed does not discharge the non-zero size precondition of `GlobalAlloc::alloc` or `alloc_zeroed`.
- **Byte zeroing vs. typed value validity:** `GlobalAlloc::alloc_zeroed`, `Allocator::allocate_zeroed`, and `Allocator::grow_zeroed` guarantee that newly exposed bytes are initialized to `0x00`. This discharges byte-initialization obligations (`FromZeros` in `zerocopy`), not arbitrary Rust type validity (e.g., `NonZeroU8` or references).
- **Optimizer elision of heap allocations (`library/core/src/alloc/global.rs`):** `GlobalAlloc` explicitly permits the compiler to elide, merge, or stack-promote heap allocations when observable program behavior is preserved; proofs must not rely on a specific number of underlying `GlobalAlloc` invocations.

### 2. `Box` Raw Conversions, Wide-Pointer Metadata, and Allocator Identity

`Basis: documentation | source | derived`

At `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (`library/alloc/src/boxed.rs`, mapped in `support/rust-box-raw-conversions/raw-conversion-contract.json` and `support/rust-box-raw-conversions/source-map.json`), `Box<T, A>` raw conversions separate memory safety at conversion time from linear resource ownership afterward:

1. **`Box::into_raw` and `Box::into_non_null` (lines 1382–1502):** Safe operations that consume `Box<T>`, wrap it in `ManuallyDrop` to suppress automatic destruction, and return a non-null, aligned raw pointer (`*mut T` or `NonNull<T>`). The caller acquires the obligation to reconstruct an owning `Box`, manually drop the pointee and deallocate its storage, or intentionally leak it.
2. **`Box::from_raw` and `Box::from_non_null` (lines 54–69, 1274–1380):** Unsafe operations that delegate to `from_raw_in(ptr, Global)` and construct `Unique::new_unchecked(ptr)` with **zero runtime validation**. Soundness requires four distinct caller proofs:
   - **Allocation / ZST provenance:** If `size_of_val(&*ptr) > 0`, the memory block must have been allocated by `Global` with the exact `Layout` of `*ptr`. If `size_of_val(&*ptr) == 0`, no heap allocation is required, but `ptr` must be non-null and aligned for `T` (e.g., `NonNull::dangling().as_ptr()`).
   - **Pointee validity:** `*ptr` must be a valid, initialized value of type `T`.
   - **Unique ownership:** Ownership of the allocation is transferred to the new `Box<T>` at most once; calling `from_raw` twice on the same allocation causes a double drop and double free.
   - **Wide-pointer metadata preservation (`T: ?Sized`, lines 1947–1961):** Because `Drop for Box<T, A>` computes `let layout = Layout::for_value_raw(ptr.as_ptr())` and calls `self.1.deallocate( ptr.cast(), layout)` when `layout.size() != 0`, changing slice length or trait-object vtable metadata across an `into_raw` / `from_raw` round trip alters the deallocation `Layout` and causes UB unless the new type/metadata has an identical `Layout` and valid representation.
3. **Allocator-aware raw conversions (`into_raw_with_allocator`, `from_raw_in`, lines 1505–1735):** `Box<T, A>::into_raw_with_allocator` returns `(*mut T, A)` so that the owning allocator instance travels with the raw pointer; `from_raw_in(ptr, alloc)` requires `ptr` to have been allocated by `alloc`. Notably, under Miri/Stacked Borrows comments in `boxed.rs`, `into_raw` performs a mutable reborrow retag assuming `Box<T, Global>` uniqueness, whereas `into_raw_with_allocator` uses a raw dereference path to avoid imposing the same uniqueness retag across arbitrary custom allocators.
4. **Concrete `zerocopy` proof patterns (`google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`):**
   - `zerocopy/src/lib.rs` (lines 3860–3894) implements `FromZeros` boxed allocation by branching on `layout.size() == 0`: the ZST branch calls `Box::from_raw(NonNull::dangling().as_ptr())`, while the non-ZST branch calls `alloc_zeroed(layout)`, checks for null, and passes the pointer to `Box::from_raw`.
   - `zerocopy/src/impls.rs` (lines 1474–1484) converts `Box<T>` into `Box<ReadOnly<T>>` via `Box::into_raw`, pointer cast to `*mut ReadOnly<T>`, and `Box::from_raw`, justified by `ReadOnly<T>` being `#[repr(transparent)]` with identical layout, metadata, and bit validity as `T`.

### 3. Typed Storage Transfer, `MaybeUninit`, `ManuallyDrop`, and Conditional Conversion Exits in `zerocopy`

`Basis: normative | source | execution | derived`

Inspecting the Rust standard library at `rust-lang/rust@d8ef4f3fe7031514cbd7d056b7b058814987ecec`, the Rust Reference at `2dafab96d919d6ab2884488e970bf95610ff83eb`, and `google/zerocopy@8fb35253fbc703cb2cd0997f4efcda76cf9062b6` establishes the boundary between untyped byte operations and typed ownership transfers:

1. **Untyped byte copy vs. typed transmutation (`library/core/src/ptr/mod.rs` line 458, `library/core/src/intrinsics/mod.rs` line 783, `library/core/src/mem/maybe_uninit.rs` lines 57 and 118):**
   - `core::ptr::copy_nonoverlapping(src, dst, count)` copies `count * size_of::<T>()` abstract bytes while preserving each byte's initialization state (`Init` vs. `Uninit`) and provenance, requiring readable/writable ranges, non-overlap, and proper alignment even when `count == 0`.
   - By contrast, `core::mem::transmute` is a typed by-value move whose contract explicitly does **not** guarantee preservation of uninitialized or padding bytes, and `MaybeUninit::assume_init` does not require struct/array padding bytes to be initialized. Consequently, a verification model cannot represent arbitrary typed Rust moves as byte-for-byte initialized `u8` slice copies unless the source type satisfies a no-padding invariant (`IntoBytes`).
2. **Physical byte admission vs. mathematical decoding in Lean storage models:**
   - In the experimental Lean storage-model formulation (inlined here from the prototype declarations), abstract-machine bytes are represented as:
     ```lean
     inductive AMByte where
       | uninit : AMByte
       | init   : UInt8 → AMByte

     def Initialized (bytes : List AMByte) : Prop :=
       ∀ b ∈ bytes, ∃ v : UInt8, b = AMByte.init v
     ```
   - A `BitDecoder α` pairs a byte width with `run : List AMByte → Option α` and a separate law `BitDecoder.Initialized` requiring all accepted byte lists to satisfy `Initialized`. Above this, `RustModel T` separates an optional physical `representation : Option (BitDecoder RawT)` (where `initializedRepresentation` requires `representation.isSome` and `BitDecoder.Initialized`, ensuring every byte including any padding is initialized) from a pure mathematical `decode : RawT → Option MathT`. `decodeBitsResult` checks physical representation admission first; `decodeResult` preserves prior divergence/failure and rejects values outside `decode`, while `spec_decodeResult_iff` and `dspec_decodeResult_iff` separate total-correctness from partial-correctness claims.
   - Similarly, in the opaque external helper model (`copy_unchecked` and `transmute_unchecked`), `copy_unchecked` requires a readable source slice and exclusive destination slice of `U8` payloads and guards destination length (preserving prefix/suffix on offset copy), while `transmute_unchecked` admits only the `U8`-to-`Bool` instantiation (`0` or `1`) and fails closed on other byte values or type instantiations.
3. **Three-exit ownership accounting in `zerocopy::util::macro_util::try_transmute` (`zerocopy/src/util/macro_util.rs`, lines 525–591 at `8fb35253fbc703cb2cd0997f4efcda76cf9062b6`):**
   - Given `Src: IntoBytes` and `Dst: TryFromBytes` with a static assertion `size_of::<Dst>() == size_of::<Src>()`, `try_transmute` wraps `src` in `let src = mem::ManuallyDrop::new(ReadOnly::new(src))` before constructing the candidate `Ptr` via `CastSizedExact` and running `Dst::is_safe(ptr.reborrow_shared())`:
     - **Success exit (`is_safe == true`):** Reads `dst` via `unsafe { core::ptr::read_unaligned(ptr.as_inner().as_ptr()) }` and returns `Ok(ReadOnly::into_inner(dst))`. `Src`'s destructor remains suppressed in `ManuallyDrop`, so exactly one owner (`Dst`) survives.
     - **Validation failure exit (`is_safe == false`):** No destination read is performed; `ReadOnly::into_inner(mem::ManuallyDrop::into_inner(src))` reconstructs the original `Src` value and returns `Err(ValidityError::new(src))`, restoring source ownership exactly once.
     - **Validation panic/unwind exit:** Because `src` is already wrapped in `ManuallyDrop` before `Dst::is_safe` runs and no destination read precedes validation, an unwind inside `is_safe` leaks `src` without double-dropping or exposing an unvalidated `Dst`.
4. **Unaligned write-back on normal and unwind exits in `Unalign<T>::update` (`zerocopy/src/wrappers.rs`, lines 339–393 at `8fb35253fbc703cb2cd0997f4efcda76cf9062b6`) and `FromZeros::insert_vec_zeroed` (`zerocopy/src/lib.rs`, lines 4032–4066):**
   - When `align_of::<T>() > 1`, `Unalign<T>::update` moves the inner `T` out via `ptr::read(self).into_inner()` into a stack-aligned `WriteBackOnDrop { copy: ManuallyDrop::new(copy), slf: self }`. Its `Drop` implementation calls `ManuallyDrop::take(&mut self.copy)` and `ptr::write(self.slf, Unalign::new(copy))`. Whether the user callback `f(&mut write_back.copy)` returns normally (hitting explicit `drop(write_back)`) or unwinds on panic, `WriteBackOnDrop::drop` restores the modified `T` to `*self` before caller-visible safe code can observe `*self` again.
   - `FromZeros::insert_vec_zeroed(v, position, additional)` asserts `position <= v.len()`, calls `v.try_reserve(additional)` (returning `Err(AllocError)` on capacity overflow without mutating `v`), shifts the suffix `[position..v.len()]` to `position + additional` via `ptr::copy_to`, zeros `[position..position + additional]` via `write_bytes(0, additional)`, and updates `v.set_len(v.len() + additional)`.
   - Executing the native control suite (`support/zerocopy-owned-storage-unwind-and-growth-controls/main.rs`, `support/zerocopy-owned-storage-unwind-and-growth-controls/results.json`, `support/zerocopy-owned-storage-unwind-and-growth-controls/native.stdout`) on `rustc 1.99.0` (`b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`) confirms: (a) a physically misaligned `Unalign<Tracked>` inside `#[repr(C, packed)] struct Packet` updates `7 -> 11` normally and `11 -> 29` across a caught callback panic with `drops == 0` during transfers and `drops == 1` when the container drops; (b) all 256 `u8 -> bool` `try_transmute!` inputs accept `0` and `1` and restore all 254 rejected bytes via `into_src()`; and (c) all 6 `insert_vec_zeroed`/`extend_vec_zeroed`/`new_vec_zeroed` controls (interior insert, append, `usize::MAX` reserve error, out-of-bounds panic, 16-element zeroed allocation, and ZST `()` insert) preserve vector contents and capacity invariants.
   - The companion Lean 4.34.1 resource model (`support/zerocopy-owned-storage-unwind-and-growth-controls/Ownership.lean`, `support/zerocopy-owned-storage-unwind-and-growth-controls/lean.stdout`) checks 8 theorems (`move_one_owner`, `update_restored`, `update_one_owner`, `missing_cleanup_loses_target`, `wrong_copy_duplicates_owner`, `insertion_zero_budget`, `insertion_at_end`, `reserve_failure_preserves`), proving that omitting unwind cleanup loses the target owner (`target = none`) and naive bitwise copying without `ManuallyDrop` violates `oneOwner`.

### 4. `rustc` MIR Drop Elaboration vs. Charon and Aeneas Extraction Boundaries

`Basis: normative | source | execution | derived`

Under the Rust Reference (`src/destructors.md`, `src/expressions.md`, `src/expressions/block-expr.md` across `ad35aca48175`, `2dafab96d919`, and `82da570bafd9`), local variables and temporaries in a lexical scope are dropped in **reverse declaration/creation order**, whereas fields of a struct or tuple are dropped in **forward declaration order** (field 0 before field 1), and moving a field out of a non-`Drop` struct deinitializes only that field.

1. **`rustc` `ElaborateDrops` pass (`compiler/rustc_mir_transform/src/elaborate_drops.rs` and `elaborate_drop.rs` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):**
   - Pre-elaboration MIR (`Built`, `Promoted`) places tentative `Drop` terminators at scope exits and overwrites. `ElaborateDrops` runs `MaybeInitializedPlaces` and `MaybeUninitializedPlaces` move-path dataflow to classify each drop as:
     - `Dead` (statically uninitialized: removed);
     - `Static` (statically initialized: unconditional drop);
     - `Conditional` (dynamically initialized or uninitialized as a whole: guarded by a compiler-synthesized stack Boolean drop flag); or
     - `Open` (partially moved aggregate: decomposed into a per-field drop ladder that drops remaining initialized fields in forward declaration order and routes any panic inside a cleanup destructor to `UnwindAction::Terminate(UnwindTerminateReason::InCleanup)`).
2. **Concrete `Runtime(PostCleanup)` MIR anatomy (`support/rustc-mir-drop-elaboration-and-minirust-unwind-cleanup/cleanup.rs`, `support/rustc-mir-drop-elaboration-and-minirust-unwind-cleanup/cleanup_binding.mir`, `support/rustc-mir-drop-elaboration-and-minirust-unwind-cleanup/cleanup_binding.1.99.1.mir`):**
   - In `exercise(second_panics, forget_second, first_drop_panics)` (lines 811–918 of both MIR dumps), `_4: Pair` has two `Leaf` fields (`_4.0` and `_4.1`), where `<Leaf as Drop>::drop` (lines 690–743) mutates `((*_1).1: u8)` via `wrapping_add(1)`, records `DropEnter`, optionally panics if `((*_1).2: bool)` is set, and otherwise increments `((*_1).1: u8)` again and records `DropExit`:
     - **Pre-aggregate temporary cleanup (`bb0`, `bb1`, `bb9`, `bb10`):** `_16: bool` (the stack drop flag for `_4.1`) is initialized to `false` at `bb0`. While constructing `_6 = make(2, second_panics, false)` at `bb1`, `_4` is not yet live; an unwind from `make(2, ...)` jumps to `bb9 (cleanup)`, which drops only the first constructor temporary `_5` with `unwind terminate(cleanup)` before `bb10: resume`.
     - **Selective drop-flag allocation (`bb2`, `bb3`, `bb4`, `bb6`, `bb13`, `bb14`):** `rustc` allocates **no** drop flag for `_4.0` because its consumption is tracked entirely by CFG progression (`bb6` drops `_4.0` unconditionally on scope exit). `_16` tracks `_4.1`: `bb2` sets `_16 = const true` upon constructing `_4`; the `if forget_second` branch (`bb4`) sets `_16 = const false` before moving `_4.1` into `std::mem::forget`; and `bb13` tests `switchInt(copy _16) -> [0: bb7, otherwise: bb14]` to conditionally drop `_4.1`.
     - **First-destructor panic and non-retry (`bb6 -> bb11 -> bb12 -> bb10`):** If `drop((_4.0: Leaf))` panics at `bb6`, its unwind edge transitions to `bb11 (cleanup)`, which never retries `_4.0`, checks `_16`, and if `true` runs `bb12 (cleanup): drop((_4.1: Leaf)) -> [return: bb10, unwind terminate(cleanup)]`.
   - All four runtime event traces (`normal`, `second_constructor_panics`, `forget_second`, `first_destructor_panics`) are verified by execution in `support/rustc-mir-drop-elaboration-and-minirust-unwind-cleanup/cleanup-binding-results.json`.
3. **Two independent loss boundaries in Charon and Aeneas:**
   - **Charon (`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`):** `charon/src/options.rs` defaults `MirLevel` to `Promoted`, and `Preset::Aeneas` does not enable `--precise-drops`. On `Built`/`Analysis` MIR, `translate_bodies.rs` emits `DropKind::Conditional` (`charon/src/ast/gast.rs`), before `rustc` has generated drop flags or open-drop field ladders. Passing `--precise-drops` switches to `MirLevel::Elaborated` (`DropKind::Precise`), but Charon documents that retrieving drop glue for polymorphic types can trigger internal `rustc` panics.
   - **Aeneas (`AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`):** `src/Config.ml` sets `drop_as_no_op = true` by default, causing `InterpStatements.eval_statement` (`src/interp/InterpStatements.ml`) to treat LLBC `Drop (p, _, _)` as a no-op. Even when `-eval-drops` is passed, `eval_statement` calls `drop_value` (which replaces the symbolic place with `VBottom`, the same operation used for `StorageDead`), ignoring both `DropKind` and the retained `drop_in_place` function pointer. Consequently, standard Aeneas functional translations do not execute user `Drop::drop` side effects (such as `WriteBackOnDrop` in `zerocopy::Unalign::update`).

### 5. MiniRust `ResumeUnwind` Frame-Cleanup Ordering, `minimize` Lowering Gap, and Lean 4.34.1 Operational Proofs

`Basis: source | execution | derived`

Auditing `minirust/minirust@d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed` and the seven machine-checked Lean 4.34.1 proof modules in `support/rustc-mir-drop-elaboration-and-minirust-unwind-cleanup/` (`lean-check-results.json`, 141 `#print axioms` audits, zero `sorryAx`) establishes four operational constraints for low-level MIR verification:

1. **Why drop-flag clearing is not `MiniRust::Statement::Deinit` (`spec/lang/step/statements.md:134-155`):** `Statement::Deinit(place)` overwrites the target memory range with `List::from_elem(Uninit, size)`. Because `<Leaf as Drop>::drop(&mut self)` reads and increments `self.payload` inside the destructor body after the drop obligation has been consumed, clearing a drop flag before destructor invocation must preserve the payload bytes in memory (`clear_before_call_keeps_payload` in `CleanupElaboration.lean`).
2. **Exact four-phase `ResumeUnwind` execution (`spec/lang/step/terminators.md:424-454`, `spec/lang/machine.md:267-301`, `spec/mem/tree_borrows/memory.md:153-174, 259-262`):**
   - Step 1 (`pop`): Pops the active callee `StackFrame` from `active_thread_mut().stack` first.
   - Step 2 (`storage_dead`): Deallocates every remaining live stack local in the popped callee frame via `self.mem.deallocate(..., AllocationKind::Stack)`.
   - Step 3 (`end_call`): Invokes `self.mem.end_call(frame.extra)?` using the **popped callee frame's** `frame.extra.protectors` list. For each `(id, tag)` in list order, Tree Borrows performs an implicit read across the allocation for strong protectors and removes `tag` from `extra.protectors`. If protector $k$ faults with UB (e.g., `Frozen` or `Disabled` violation), `?` short-circuits **without rolling back** the frame pop, stack-local deallocations, or protector releases $0 \dots k-1$.
   - Step 4 (jump): Jumps to `caller.unwind_block` on the new top frame, or raises UB if the stack is empty (`BottomOfStack`) or `caller.unwind_block == None`.
3. **`tooling/minimize` lowering gap (`tooling/minimize/src/bb.rs:220-274`):** `minimize` lowers `rs::TerminatorKind::Drop` to `Terminator::Call` with `unwind_block: None` (discarding the MIR cleanup edge) and rejects `rs::TerminatorKind::UnwindTerminate` with `span_bug!`. Thus `minimize` cannot execute caller cleanup blocks (`bb11`/`bb12`) when a destructor unwinds.
4. **Summary of Lean 4.34.1 operational verification modules (`support/rustc-mir-drop-elaboration-and-minirust-unwind-cleanup/`):**
   - `Combined.lean` (10 audits): Couples byte-copy validation with post-copy frame cleanup (`copy_then_cleanup_verified`) and proves that cleanup UB followed by an infinite `.spin` loop is still rejected (`cleanup_failure_then_spin`, `reachable_cleanup_failure_unsafe`).
   - `CleanupElaboration.lean` (11 audits): Proves lockstep simulation (`simulation`), safety transfer (`safety_transfer`), and finite-prefix event-trace preservation (`finite_prefix_trace`) between a high-level obligation-list machine and an elaborated CFG machine across all 5 specimens (`ordinary_cleanup_order`, `second_constructor_unwind_cleans_only_first`, `partial_move_skips_second`, `panicking_drop_is_not_retried`, `destructor_bad_prefix_before_later_loop`).
   - `EffectfulDestructor.lean` (11 audits), `TwoCleanup.lean` (23 audits), and `EffectfulControls.lean` (42 audits): Formalize a 4-step effectful destructor engine (`readU8`, wrapping increment, `writeRaw`, `returned`/`unwound`) over permissioned memory, proving `MemoryWF` preservation across UB residuals, two-field CFG controller simulation where `_4.0` uses PC progression and `_4.1` uses `secondOwed : Bool`, and negative mutant discriminators (`Negative.rollback_changes_second_entry`, `Negative.retry_duplicates_entry_event`, `BeforeUnwind.read_preserved_and_write_fails_before_exit_choice`).
   - `ResumeUnwindPhase.lean` (19 audits) and `ResumeUnwindPhaseControls.lean` (25 audits): Prove exact reification agreement (`run_agrees`) and `WellSized` preservation (`runF_preserves`) between monolithic (`TreeMemory`) and per-allocation (`TreeFactoredMemory`) two-frame `ResumeUnwind` runners, plus 4-allocation discriminators refuting wrong-frame protector lists (`wrong_list_value_discriminator`), delayed frame pop (`late_pop_config_differs`), and whole-phase error rollback (`rollback_memory_differs`).

## Boundaries

- **Not examined:**
  - Platform heap implementation internals (`jemalloc`, `libc::malloc`, OS virtual-memory mappings), hardware DWARF/SEH unwind tables, or `rust_eh_personality` ABI routines.
  - Drop elaboration across arbitrary `async` coroutines/generators, complex loop-carried partial moves, or inline assembly.
  - Complete `std::vec::Vec` allocator-wrapper paths beyond `FromZeros::insert_vec_zeroed` and the inspected `RawVec` baseline.
- **Unknown:**
  - Whether upstream MiniRust will add a native `Terminator::Terminate` and update `tooling/minimize` to lower MIR `Drop` unwind edges and `UnwindTerminate` without `span_bug!`.
  - A mechanized end-to-end correspondence theorem connecting native `rustc` compilation of `zerocopy` to the Lean `AMByte`/`BitDecoder` and `Ownership` models.
- **Known not to apply:**
  - Zero-sized `Layout` validity does **not** make `GlobalAlloc::alloc(layout)` or `alloc_zeroed(layout)` defined; zero-sized global allocation requests are UB.
  - Typed value validity (`T`) does **not** imply that padding bytes are initialized, and `core::mem::transmute` does **not** guarantee padding-byte preservation.
  - Clearing a drop obligation before destructor entry does **not** map to `MiniRust::Statement::Deinit`, and scope-exit reverse drop order does **not** apply to struct/tuple fields (which drop in forward declaration order).
  - Default Charon (`--preset=aeneas` on `Promoted` MIR) and default Aeneas (`drop_as_no_op = true`, or `-eval-drops` place invalidation) do **not** model the side effects of user `Drop::drop` implementations such as `WriteBackOnDrop` in `Unalign<T>::update`.
- **Unsupported:**
  - `tooling/minimize` at `minirust/minirust@d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed` explicitly rejects `rs::TerminatorKind::UnwindTerminate` (`span_bug!`) and drops the `unwind` target of `rs::TerminatorKind::Drop` (`unwind_block: None`).

## Evidence

### Primary Upstream Sources

- **Rust allocation and `Box` contracts (`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, and `d8ef4f3fe7031514cbd7d056b7b058814987ecec`):**
  - `library/core/src/alloc/layout.rs` (blob `66f5310db83102e28535faf0e4586ba447b4d7a6`): `Layout`, `from_size_align`, `from_size_align_unchecked`.
  - `library/core/src/alloc/global.rs` (blobs `e97398aa5dc4a3f923d014cecc3734906121d0a9` and `e1e08ab7a2cb9a2ef20c1616032bce6034677b10`): `GlobalAlloc` safety contract, non-zero size requirement, no-unwind rule, `dealloc`, `realloc`.
  - `library/core/src/alloc/mod.rs` (blob `102fb19efc8eabbe32ddb9a5d3a2f7e0ac186b16`) and `library/alloc/src/alloc.rs` (blob `8729e98278a82c17cf5a6b201246ca04db17dcf6`): `Allocator`, fitting-layout rule, `Global` zero-size handling, `handle_alloc_error`.
  - `library/alloc/src/boxed.rs` (blob `bd3f10a16dd9b27870c28db0a34bc9b569a36634`, lines 54–69, 124–134, 1274–1735, 1947–1961): `Box` memory layout, `into_raw`, `from_raw`, allocator-aware and `NonNull` variants, `Drop for Box<T, A>`.
  - `library/core/src/mem/maybe_uninit.rs` (blobs `7e2c6b9b3bcb2d66af376243d95c541e5bd4024d` and `94703940baa1f8dfdbcf84f157f5dfebad93931e`), `library/core/src/mem/manually_drop.rs` (blob `3fb844c7c2927876ad082f2ba904e51d520a0f1e`), `library/core/src/mem/mod.rs` (blobs `a22e52f3a3bc72edbdeaa526f3a45f4d0c7a49d7` and `42c7224fb41a2b13db3977b747d3d4a2de15df7e`), `library/core/src/ptr/mod.rs` (blob `be3dc5e013b32bcffe9fd3e8d8d85382300508b8`), `library/core/src/intrinsics/mod.rs` (blob `3a5ec85f507ec7c9ba8712eea5adc58c07491643`), `library/core/src/ops/drop.rs` (blob `5d4b9f7dbeb9b4de002c0a5e91605216e75049b7`).
- **Rust compiler MIR drop elaboration (`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):**
  - `compiler/rustc_mir_build/src/builder/scope.rs` (blob `3343bec30caf58a38d129dc4a2787f7e0828d15c`), `compiler/rustc_mir_transform/src/elaborate_drops.rs` (blob `3787276919cf5b4b827bd167d421e0dc2bb7223c`), `compiler/rustc_mir_transform/src/elaborate_drop.rs` (blob `0eb7db8dbed2d6f04223b42447591664b5f98daa`).
- **Charon, Aeneas, and MiniRust sources:**
  - `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`: `charon/src/options.rs` (blob `f08f8bae08d7fb5f38773c0be038d925fe80cb4c`), `charon/src/ast/gast.rs` (blob `23044319a8f763d241912c5d693ed94cf597682f`), `charon/src/bin/charon-driver/translate/translate_bodies.rs` (blob `c03ca8077f131a2ef701e9d27eaa9e69bb617124`).
  - `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`: `src/Config.ml` (blob `99a9eba5ae67dde20dbfd8d835cdc2900fc60355`), `src/interp/InterpStatements.ml` (blob `97452f658bbd773c16386592d31b0bf61da8891f`).
  - `minirust/minirust@d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`: `spec/lang/syntax.md`, `spec/lang/step/statements.md`, `spec/lang/step/terminators.md`, `spec/lang/machine.md`, `spec/mem/tree_borrows/memory.md`, `tooling/minimize/src/bb.rs` (blob `45f794ea44bab2524861136279d282f8df7074b8`).
- **`zerocopy` sources (`google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` and `8fb35253fbc703cb2cd0997f4efcda76cf9062b6`):**
  - `zerocopy/src/lib.rs` (blobs `944f177c0b0bf66ebd136e5f21ae1b4c2bde48b5` and `6040d6e0dd140e9fceb3bb9ed48aa55e0358f5cf`, lines 3860–3894 for `Box` ZST/non-ZST allocation and lines 4032–4066 for `FromZeros::insert_vec_zeroed`).
  - `zerocopy/src/impls.rs` (blob `4df786fd2104854e1fa259a63c29cd8781f8a404`, lines 1474–1484 for `Box<T>` to `Box<ReadOnly<T>>` raw cast).
  - `zerocopy/src/util/macro_util.rs` (blob `f374a089f414614ea81764ae1ee078af05d27109`, lines 525–591 for `try_transmute`).
  - `zerocopy/src/wrappers.rs` (blob `2d4ff5515918a8e486683d1863289e4105da3022`, lines 339–393 for `Unalign<T>::update` and `WriteBackOnDrop`).

### Preserved Package Support Artifacts

- **Allocation and `Box` contract matrices (observed 2026-09-27):**
  - `support/rust-allocation-deallocation/allocation-contract-matrix.json` and `support/rust-allocation-deallocation/source-map.json`
  - `support/rust-box-raw-conversions/raw-conversion-contract.json` and `support/rust-box-raw-conversions/source-map.json`
- **`rustc` MIR drop-elaboration captures and Lean 4.34.1 `ResumeUnwind` models (observed 2026-10-24):**
  - `support/rustc-mir-drop-elaboration-and-minirust-unwind-cleanup/cleanup.rs`, `support/rustc-mir-drop-elaboration-and-minirust-unwind-cleanup/cleanup_binding.mir` (`rustc 1.99.0`), `support/rustc-mir-drop-elaboration-and-minirust-unwind-cleanup/cleanup_binding.1.99.1.mir` (`rustc 1.99.1`), and `support/rustc-mir-drop-elaboration-and-minirust-unwind-cleanup/cleanup-binding-results.json`
  - `support/rustc-mir-drop-elaboration-and-minirust-unwind-cleanup/Combined.lean`, `support/rustc-mir-drop-elaboration-and-minirust-unwind-cleanup/CleanupElaboration.lean`, `support/rustc-mir-drop-elaboration-and-minirust-unwind-cleanup/EffectfulDestructor.lean`, `support/rustc-mir-drop-elaboration-and-minirust-unwind-cleanup/TwoCleanup.lean`, `support/rustc-mir-drop-elaboration-and-minirust-unwind-cleanup/EffectfulControls.lean`, `support/rustc-mir-drop-elaboration-and-minirust-unwind-cleanup/ResumeUnwindPhase.lean`, `support/rustc-mir-drop-elaboration-and-minirust-unwind-cleanup/ResumeUnwindPhaseControls.lean`, and `support/rustc-mir-drop-elaboration-and-minirust-unwind-cleanup/lean-check-results.json`
- **`zerocopy` storage-transfer, unwind, and vector-growth artifacts (observed 2026-10-14):**
  - `support/zerocopy-owned-storage-unwind-and-growth-controls/main.rs`, `support/zerocopy-owned-storage-unwind-and-growth-controls/Ownership.lean`, `support/zerocopy-owned-storage-unwind-and-growth-controls/results.json`, `support/zerocopy-owned-storage-unwind-and-growth-controls/artifact-identities.json`, `support/zerocopy-owned-storage-unwind-and-growth-controls/initial-environment-failure.json`, `support/zerocopy-owned-storage-unwind-and-growth-controls/compile.stdout`, `support/zerocopy-owned-storage-unwind-and-growth-controls/compile.stderr`, `support/zerocopy-owned-storage-unwind-and-growth-controls/native.stdout`, `support/zerocopy-owned-storage-unwind-and-growth-controls/native.stderr`, `support/zerocopy-owned-storage-unwind-and-growth-controls/lean.stdout`, `support/zerocopy-owned-storage-unwind-and-growth-controls/lean.stderr`, `support/zerocopy-owned-storage-unwind-and-growth-controls/version.stdout`, and `support/zerocopy-owned-storage-unwind-and-growth-controls/version.stderr`

## Revalidation

1. **Source contract diffing across `rust-lang/rust`, Charon, Aeneas, MiniRust, and `zerocopy`:**
   - Diff `library/core/src/alloc/{layout.rs,global.rs,mod.rs}`, `library/alloc/src/{alloc.rs,boxed.rs}`, and `library/core/src/mem/{maybe_uninit.rs,manually_drop.rs,mod.rs}` for changes to zero-size allocation rules, `realloc`/`grow`/`shrink` pointer invalidation, `Box` raw-conversion contracts, or `ManuallyDrop` invariants.
   - Diff `compiler/rustc_mir_transform/src/{elaborate_drops.rs,elaborate_drop.rs}`, Charon's `MirLevel`/`Preset::Aeneas`/`DropKind` mapping, Aeneas's `drop_as_no_op` and `InterpStatements.eval_statement`, and MiniRust's `ResumeUnwind` and `tooling/minimize/src/bb.rs` `Drop`/`UnwindTerminate` translation.
   - Diff `zerocopy/src/util/macro_util.rs` (`try_transmute`), `zerocopy/src/wrappers.rs` (`Unalign::update`), and `zerocopy/src/lib.rs` (`FromZeros::insert_vec_zeroed`).
2. **Re-running the `rustc` MIR drop-elaboration and runtime trace probe (`cleanup.rs`):**
   ```bash
   mkdir -p ./build/mir-probe
   rustc +1.99.1 support/rustc-mir-drop-elaboration-and-minirust-unwind-cleanup/cleanup.rs \
     --crate-name cleanup_binding \
     --edition=2024 \
     -C opt-level=0 \
     -C panic=unwind \
     -C codegen-units=1 \
     --emit=mir,link \
     -o ./build/mir-probe/cleanup_binding
   ./build/mir-probe/cleanup_binding
   ```
   Verify that the emitted MIR matches `support/rustc-mir-drop-elaboration-and-minirust-unwind-cleanup/cleanup_binding.1.99.1.mir` across `exercise`, `<Leaf as Drop>::drop`, and `make`, and that stdout matches the four traces in `support/rustc-mir-drop-elaboration-and-minirust-unwind-cleanup/cleanup-binding-results.json`.
3. **Re-running the Lean 4.34.1 operational models and ownership proofs:**
   ```bash
   lean -j1 -M2048 support/zerocopy-owned-storage-unwind-and-growth-controls/Ownership.lean
   for mod in Combined CleanupElaboration EffectfulDestructor TwoCleanup EffectfulControls ResumeUnwindPhase ResumeUnwindPhaseControls; do
     lean -j1 -M2048 -o "./build/AnnealResearch/${mod}.olean" \
       "support/rustc-mir-drop-elaboration-and-minirust-unwind-cleanup/${mod}.lean"
   done
   ```
   Confirm exit code `0`, zero warnings, and `#print axioms` output matching `support/zerocopy-owned-storage-unwind-and-growth-controls/lean.stdout` and `support/rustc-mir-drop-elaboration-and-minirust-unwind-cleanup/lean-check-results.json`.
4. **Re-running the `zerocopy` native ownership, unwind, and vector-growth harness:**
   Compile `support/zerocopy-owned-storage-unwind-and-growth-controls/main.rs` against `zerocopy` with `alloc` and `std` features enabled (`--edition=2024 -C panic=unwind`) and confirm the output line `unaligned_normal=1;unaligned_unwind=1;direct_unwind=1;drop_exactly_once=1;conditional_inputs=256;restores=254;growth_controls=6;all_match=true`.
