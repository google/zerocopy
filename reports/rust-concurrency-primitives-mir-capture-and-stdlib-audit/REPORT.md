# MIR Capture and Stdlib Surface Audit of Rust Concurrency Primitives for Anneal

## Summary

At `google/zerocopy` (`a4f1182901bf9000022b46b6b0ff32159d36c981`), Anneal captures **zero** concurrent or atomic primitives end-to-end—neither toy `core::sync::atomic` spinlocks nor `std::sync` / `alloc::sync` primitives—because `anneal-rustc-capture` and `Trusted.MirAst` / `Trusted.MirSemantics` currently omit atomics, `UnsafeCell`, `Result<T, T>` / payload enums, arbitrary ADT structs, `Drop`, unwinding cleanup blocks, and OS `futex` FFI. Empirically auditing `rustc 1.98.0-nightly` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`) at Anneal's capture point (`mir_drops_elaborated_and_const_checked`, i.e., `runtime-post-cleanup`) and source-auditing the pinned `rust-src` standard library reveals three governing facts for selecting an initial weak-memory verification target:

1. **Cross-crate atomics stay un-inlined at capture time:** At `runtime-post-cleanup`, calls to `AtomicBool`/`AtomicU32` stay as un-inlined cross-crate calls to `core::sync::atomic::Atomic::<T>::{load, store, swap, compare_exchange, compare_exchange_weak, fetch_add, fetch_sub}` taking runtime `Ordering` values, plus `Result::<T, T>::{is_ok, is_err}`, `discriminant` + downcast projections, `UnsafeCell::<T>::get`, and `core::hint::spin_loop`. Even `-Copt-level=3` / `-Zinline-mir=yes` stops one level below at `core::sync::atomic::atomic_*` rather than reaching the 17 `#[rustc_intrinsic]` `core::intrinsics::atomic_*` signatures directly.
2. **Profile v2's no-mixing invariant breaks immediately upon adding `UnsafeCell`:** `Trusted.MirSemantics.BodyStaticAdmittedV2` explicitly rejects bodies mixing `&` references and `*mut`/`*const` raw pointers (`bodyMixesRefsAndRawPtrsV2`), relying on the documented assumption that Profile v2 has no `UnsafeCell`. Every realistic `RawSpinLock` or `AtomicOnce` method taking `&self` and calling `UnsafeCell::get() -> *mut T` violates that non-mixing check once `UnsafeCell` is added.
3. **Clean stdlib vs. toy ranking (`Easiest -> Hardest`):**
   - **Lowest-friction toy target (`core`-only, zero `Drop`, zero FFI, zero allocation):** A raw-method `RawSpinLock` (`AtomicBool` + `UnsafeCell<u64>`, `unsafe fn unlock`) or `core`-only 3-state spin `AtomicOnceU64` (`AtomicU32` + `UnsafeCell<MaybeUninit<u64>>`), needing only atomic intrinsics/`Atomic<T>` support, `UnsafeCell`, `Result<T, T>`, `spin_loop`, and struct field projections—without `Drop`, unwinding, `Box`, or syscalls.
   - **Easiest real `std` kernel primitive (`103` lines, zero closures/`Drop`/poison/`SeqCst`/fences):** `std::sys::sync::mutex::futex::Mutex` (`Atomic<u32>` states `0`/`1`/`2` + bounded `spin()` + `futex_wait`/`futex_wake`), whereas `std::sys::sync::once::futex::Once` (`211` lines) immediately drags in `Cell<u32>`, `CompletionGuard` `Drop`, `&mut dyn FnMut(&OnceState)`, `panic!`, and poisoning, and public `std::sync::{nonpoison::Mutex, Mutex, OnceLock, RwLock}` / `alloc::sync::Arc` drag in RAII `Drop` guards, unwind cleanup pads (under `-Cpanic=unwind`), `Box`/`Allocator`, `Release`-`Acquire` fences (`Arc::drop`), or `thread::panicking()` TLS.

## Applicability

These measurements apply to:

- **`google/zerocopy` (`anneal/` subtree)** at commit `a4f1182901bf9000022b46b6b0ff32159d36c981`: `trusted/rustc-capture/src/{capture.rs, extract.rs, ir.rs}`, `trusted/lean/Trusted/MirAst/{Types, Statements, Terminators}.lean`, `trusted/lean/Trusted/MirSemantics/{Memory, Step, Boundary, Contract}.lean`, and `trusted/lean/Trusted/{Framework.lean, Framework/Instances.lean}`.
- **`rust-lang/rust`** pinned toolchain `1.98.0-nightly` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, commit date `2026-05-30`): both live `rustc` MIR emission (`--edition=2024`, `-Zmir-preserve-ub`, `-Cdebug-assertions=no`, `-Coverflow-checks=no`, comparing `-Copt-level={0,1,3}` and `-Cpanic={abort,unwind}`) and the bundled `library/{core,alloc,std}` sources.

Observations cover `x86_64-unknown-linux-gnu` / Unix `futex` backends (`std/src/sys/sync/*/futex.rs` and `std/src/sys/pal/unix/futex.rs`); non-futex platform backends (`pthread`, `windows7`, `sgx`, `no_threads`, `queue`) were not inspected in detail.

## Findings

### 1. Live Anneal Capture & Profile v1/v2 Baseline Gaps (`google/zerocopy@a4f1182901bf`)

Basis: source (`anneal/trusted/rustc-capture/src/{capture.rs, extract.rs, ir.rs}`, `Trusted/MirAst/*`, `Trusted/MirSemantics/{Boundary, Step, Memory}.lean`, `Trusted/Framework/Instances.lean`).

| Layer | Current Capability (`origin/main` `a4f1182901bf`) | Exact Fail-Closed Concurrency Blockers | Source Location |
| :--- | :--- | :--- | :--- |
| **Capture MIR Stage** | Hooks `mir_drops_elaborated_and_const_checked` (`Runtime(PostCleanup)`) with `-Zmir-preserve-ub`, `-Cdebug-assertions=no`, `-Coverflow-checks=no`; forbids `cfg(miri)` and `ergonomic_clones` | Captures *before* `ForceInline`, leaving all cross-crate `core::sync::atomic::Atomic::<T>::*` and `UnsafeCell::get` calls un-inlined | `capture.rs:87-89, 1079, 1324, 2568` |
| **`MirTy` Type Universe** | Admits `bool`, `int` (`i8..i128`, `isize/usize`), `()`, `!`, `char`, `Ordering`, local fieldless `enum`, tuples (`(int, bool)` `OverflowPair`), `&`/`*` ptrs, `[T]`, `[T; N]`, `RangeTo/From<usize>` | Refuses arbitrary structs/unions, `Atomic<T>`, `UnsafeCell<T>`, `Cell<T>`, `MaybeUninit<T>`, `ManuallyDrop<T>`, `NonNull<T>`, `Result<T, E>` (enum with payload), `Box<T>`, closures, `dyn Trait` | `extract.rs:146-330`; `MirAst/Types.lean` |
| **Statements & Unwinds** | `Assign`, `StorageLive`, `StorageDead`, `Nop`, unprojected `PlaceMention` (`Sized`); `UnwindAction::{Continue, Unreachable, Terminate}` | Refuses `SetDiscriminant`, `Intrinsic`, `Drop`, `CoroutineDrop`, `InlineAsm`, `Cleanup(_)` on `Assert`/`Call` (`unwind_action` line `1477`), `UnwindResume` | `extract.rs:1117-1154, 1472-1479, 2251-2252`; `MirAst/Statements.lean` |
| **Calls (`CoreCall` / `Local`)** | Profile v1 admits closed `core_call_op` table (`slice::{len, get_unchecked}`, `ptr::{const,mut}_ptr::add`, `usize::unchecked_sub`, `int::to_le_bytes`, `[T; N]::eq`), 6 `sysroot_num` ops, non-generic safe intra-crate calls; Profile v2 rejects **all** `.call`/`.sysrootCall` in `evalStepV2` | Zero atomic/fence calls in `core_call_op`; `callsAdmitted` rejects `unsafe fn` local callees, generic monomorphizations, `#[track_caller]`, and external (`std`/`libc`) functions | `extract.rs:1296-1455, 1966-2034`; `Step.lean:3302-3325`; `State.lean:511-516` |
| **Aliasing & Thread Isolation** | `MirProfileV2` unconditionally emits `.callerMemoryThreadIsolation "mir_profile_v2"`; `BodyStaticAdmittedV2` forbids mixing `&` and `*` locals (`!bodyMixesRefsAndRawPtrsV2`) | Single-threaded `MemoryState` (`List Allocation` + monotonic `AllocId`); explicit `Boundary.lean:435` note states `!bodyMixesRefsAndRawPtrsV2` relies on omitting `UnsafeCell` | `Boundary.lean:431-462`; `Instances.lean:245-260`; `Memory.lean:46-48` |
| **Stdlib Mode (`--stdlib-crate`)** | Supports standalone `#![no_core]` `--stdlib-crate core` with shape-checking (`check_local_ordering`) | Explicitly forbids `cfg(miri)` (`check_no_cfg_miri`) and warns that admitting `Assert` panics, `drop_in_place`, `UnsafeCell`/`Freeze`, or `owned_box` requires local shape validators | `capture.rs:2245-2291` |

---

### 2. Compiler Atomic Lowering at `runtime-post-cleanup` vs. `optimized_mir` (`rustc 1.98.0-nightly`)

Basis: source (`core/src/intrinsics/mod.rs:95-262`, `core/src/sync/atomic.rs:366-419, 3885-4105`, `core/src/cell.rs:2319-2367`) + execution (`support/probe_stdlib_and_toy_mir.py`, direct `rustc` MIR checks).

1. **Struct Representation of `Atomic*`:** In `rustc 1.98.0-nightly` (`f8a08b688`), `AtomicBool`, `AtomicU32`, `AtomicUsize`, and `AtomicPtr<T>` are all type aliases of the generic `#[repr(C)] #[rustc_diagnostic_item = "Atomic"] struct Atomic<T: AtomicPrimitive> { v: UnsafeCell<T::Storage> }` (`core/src/sync/atomic.rs:366-418`). Thus **every** atomic variable in MIR contains `UnsafeCell` (`#[lang = "unsafe_cell"]`, `#[repr(transparent)]`).
2. **Closed 17-Intrinsic Backend Surface:** Inside `core/src/intrinsics/mod.rs:95-262`, all compiler atomics are `#[rustc_intrinsic] #[rustc_nounwind]` functions parameterized by compile-time `const ORD: AtomicOrdering` generics (and `ORD_SUCC`, `ORD_FAIL` on `atomic_cxchg` / `atomic_cxchgweak`): `atomic_{cxchg, cxchgweak, load, store, xchg, xadd, xsub, and, nand, or, xor, max, min, umin, umax, fence, singlethreadfence}`. Safe helpers (`core::sync::atomic::atomic_load`, etc., lines `3885-4094`) dispatch runtime `Ordering` values via `match` arms to those `const`-generic intrinsics and panic on invalid runtime orderings (e.g., `Acquire` store or `Release` failure CAS ordering).
3. **Why Capture Never Sees `core::intrinsics::atomic_*` Directly `[real measurement]`:**
   - **At `runtime-post-cleanup` (Anneal's `mir_drops_elaborated_and_const_checked` stage):** Zero cross-crate MIR inlining has run (`ForceInline` runs *later* at `3-2-003.ForceInline`, `optimized_mir`). Consequently, `RawSpinLock::try_lock` emits a call to `Atomic::<bool>::compare_exchange(move _4, const false, const true, move _5, move _6)` followed by `Result::<bool, bool>::is_ok(move _2)` (3 basic blocks). Even `Ordering::Acquire` / `Ordering::Relaxed` are material locals assigned enum variants and passed by value rather than `const` generic parameters!
   - **At `-Zinline-mir=yes` / `-Copt-level=3` (`--emit=mir`):** `Atomic::<bool>::load` inlines one level into `UnsafeCell::<Align1<u8>>::get` -> `&raw const ((*_1).0)` -> `PtrToPtr` cast to `*const u8` -> `core::sync::atomic::atomic_load::<u8>(move _3, const Ordering::Acquire)`, and `Atomic::<u32>::compare_exchange` inlines into `core::sync::atomic::atomic_compare_exchange::<u32>(..., const Ordering::Acquire, const Ordering::Relaxed)` (`atomic_bool::compare_exchange` expands extra `fetch_or`/`swap` dead scopes in the MIR scope tree and maps `Result<u8, u8>` to `Result<bool, bool>` via `discriminant(_2)` + `((_2 as Ok).0: u8)`). Only direct calls to `core::intrinsics::atomic_*` (requiring `#![feature(core_intrinsics)]`) emit `atomic_load::<u32, core::intrinsics::AtomicOrdering::Acquire>` directly at `runtime-post-cleanup`.
   - **Capture Design Implication:** Either Anneal intercepts the `core::sync::atomic::Atomic::<T>::*` + `core::cell::UnsafeCell::*` methods at `runtime-post-cleanup` in `CoreCallOp` (pinning to sysroot `core` via `core_def_path`), OR Anneal traverses monomorphized `tcx.instance_mir` of `Atomic<T>::*` down to `core::intrinsics::atomic_*` (and handles `Atomic<T>`/`UnsafeCell<T>`/`Result<T, T>`/`PtrToPtr` projections + dead-branch elimination for invalid runtime `Ordering` panics).

---

### 3. Empirical MIR & Source Census: Toy Primitives vs. Rust Standard Library (`f8a08b688`)

Basis: execution (`support/probe_stdlib_and_toy_mir.py` / `support/mir_census_summary.json` under `-Zmir-preserve-ub -Copt-level=0 -Cdebug-assertions=no -Coverflow-checks=no`) + source inspection (`library/std/src/sys/sync/*/futex.rs`, `std/src/sys/pal/unix/futex.rs`, `std/src/sync/{once,once_lock,poison}.rs`, `std/src/sync/nonpoison/mutex.rs`, `alloc/src/sync.rs`).

#### Part A: Measured Toy & Extracted-Core MIR Constructs (`runtime-post-cleanup`, `-Cpanic=abort` vs `-Cpanic=unwind`)

| Primitive & Method (`[real measurement]`) | BBs (`abort` / `unwind`) | Atomics & Orderings Used | Non-Atomic Calls & MIR Features Required | Unblocked by `Drop` / `Unwind` Exclusion? |
| :--- | :---: | :--- | :--- | :--- |
| **`RawSpinLock::{try_lock, lock, unlock, with_lock_set}`** (`AtomicBool` + `UnsafeCell<u64>`, manual `unsafe unlock`) | `try_lock`: 3 / 3<br>`lock`: 11 / 11<br>`unlock`: 2 / 2<br>`with_lock_set`: 4 / 4 | `compare_exchange(Acq, Rlx)`, `compare_exchange_weak(Acq, Rlx)`, `load(Rlx)`, `store(Rel)` | `Atomic::<bool>::*`, `UnsafeCell::<u64>::{new, get}`, `Result::<bool,bool>::{is_ok, is_err}`, `spin_loop`, mixed `&RawSpinLock` + `*mut u64` | **Yes** (`0` `Drop`, `0` unwind cleanup, `0` `Assert`, `0` FFI) |
| **`AtomicOnceU64::{get, get_or_init_val}`** (`AtomicU32` 3-state + `UnsafeCell<MaybeUninit<u64>>`, `core`-only) | `get`: 7 / 7<br>`get_or_init_val`: 21 / 21 | `load(Acq)`, `compare_exchange(Acq, Acq)`, `store(Rel)` | `Atomic::<u32>::*`, `UnsafeCell::get`, `MaybeUninit::<u64>::{uninit, write, assume_init}`, `discriminant` + `(_14 as Err).0`, `spin_loop`, mixed `&` + `*mut` | **Yes** (`0` `Drop`, `0` unwind cleanup, `0` FFI) |
| **`TicketLock::{lock, unlock}`** (`next/serving: AtomicU32` + `UnsafeCell<u64>`) | `lock`: 7 / 7<br>`unlock`: 4 / 4 | `fetch_add(Rlx)`, `load(Acq)`, `load(Rlx)`, `store(Rel)` | `Atomic::<u32>::*`, `u32::wrapping_add` (already in `SysrootNumOp`!), `spin_loop` | **Yes** (`0` `Drop`, `0` unwind cleanup, `0` FFI) |
| **`SeqLockPair::{write, read}`** (`AtomicU64` + `UnsafeCell<[u64; 2]>`) | `write`: 10 / 10<br>`read`: 11 / 11 | `load(Rlx, Acq)`, `store(Rel)`, `fence(Rel, Acq)` | `fence`, `u64::wrapping_add`, `UnsafeCell::<[u64; 2]>::get`, `spin_loop`, `Assert` (slice/array or non-atomic read data race—see Warning below!) | **Needs `fence`**; **WARNING:** naive NA reader loads are **data-race UB** under C++20/RC11 |
| **`ArcCountCore::{clone_count, drop_is_last}`** (isolated `ArcInner` refcount arithmetic + fence) | `clone_count`: 4 / 4<br>`drop_is_last`: 6 / 6 | `fetch_add(Rlx)`, `fetch_sub(Rel)`, `fence(Acq)` | `Atomic::<usize>::*`, `core::intrinsics::abort`, `fence(Acquire)` (no `Box`/`NonNull`/`Weak`) | **Yes** (`0` `Drop`, `0` cleanup; requires modeling `fence(Acquire)`) |
| **`GuardSpinLock::with_guard_scope`** (RAII `SpinGuard` + call to non-trivial inner fn) | `5` (`abort`) / `7` (`unwind`) | `swap(Acq)`, `store(Rel)` | `TerminatorKind::Drop` even under `panic=abort`; under `panic=unwind`, emits `bb (cleanup):` + `drop(_1)` + `resume` + drop-flag `bool` | **No** (`Drop` terminator required even under `panic=abort`) |
| **`FutexMutexCore::{lock, lock_contended, spin, unlock}`** (`std` algorithm w/ futex stub) | `lock`: 7 / 7<br>`lock_contended`: 19 / 19<br>`unlock`: 6 / 6 | `compare_exchange(Acq, Rlx)`, `swap(Acq, Rel)`, `load(Rlx)` | `discriminant(_7)` + `(_7 as Err).0`, `spin_loop`, 2 abstract external futex stubs (`stub_futex_wait`, `stub_futex_wake`), `0` `SeqCst`, `0` fences | **Needs futex `AssumedStub`** (`0` `Drop`, `0` cleanup, `0` `UnsafeCell` on lock core itself) |

#### Part B: Real Rust Standard Library Concurrency Primitives (`nightly-2026-05-31` `rust-src`, Ranked Easiest -> Hardest)

Basis: source (`std/src/sys/sync/*/futex.rs`, `std/src/sys/pal/unix/futex.rs`, `std/src/sync/{once,once_lock,poison}.rs`, `std/src/sync/nonpoison/mutex.rs`, `alloc/src/sync.rs`) + execution (`std_o0_abort` / `std_o0_unwind` in `support/mir_census_summary.json`).

| Rank | Stdlib Primitive & Exact Source | LOC | Atomic Ops & Orderings | Beyond-Toy Verification Requirements (`nightly-2026-05-31`) |
| :---: | :--- | :---: | :--- | :--- |
| **1** | **`std::sys::sync::mutex::futex::Mutex`** (`sys/sync/mutex/futex.rs:1-103`) | `103` | `Atomic<u32>`: `compare_exchange(Acq,Rlx)`, `swap(Acq,Rel)`, `load(Rlx)` | **Cleanest real `std` kernel primitive:** `0` `SeqCst`, `0` fences, `0` `Drop`, `0` closures, `0` `panic!`, `0` poisoning, `0` generics. Needs `Atomic<u32>`, `Result<u32,u32>`, `spin_loop`, and 2 external FFI/futex stubs (`futex_wait`, `futex_wake` via `libc::syscall(SYS_futex, ...)`). |
| **2** | **`std::sys::sync::condvar::futex::Condvar`** (`sys/sync/condvar/futex.rs:1-56`) | `56` | `Atomic<u32>`: `fetch_add(Rlx)`, `load(Rlx)` | Tiny (`56` LOC) + no fences/Drop/panics, **but** couples to `&sys::Mutex::unlock`/`lock`, `Option<Duration>` -> `Timespec::now(CLOCK_MONOTONIC)` timeout arithmetic, and kernel futex wakeup ordering. |
| **3** | **`std::sync::nonpoison::Mutex<T>`** (`sync/nonpoison/mutex.rs:49-505` + `sys::Mutex`) | `649` (+`103`) | Same as Rank 1 + `get_mut` | Adds `UnsafeCell<T>`, generic `T: ?Sized`, `MutexGuard<'a, T>` (`Deref`/`DerefMut`/`Drop` calling `sys::Mutex::unlock`), `NonNull`/`ManuallyDrop` (`MappedMutexGuard`), plus `unwind` cleanup blocks (`call_nonpoison_mutex`: `5` -> `7` BBs) and `mem::forget(guard)` permanent-lock leak hazard. |
| **4** | **`std::sys::sync::once::futex::Once`** (`sys/sync/once/futex.rs:1-211`) | `211` | `Atomic<u32>`: `load(Acq)`, `compare_exchange_weak(Acq,Acq)` & `(Rlx,Acq)`, `swap(Rel)`, `get_mut` | Harder than `sys::Mutex`: adds `Cell<u32>`, `CompletionGuard<'a>` `impl Drop`, **`&mut dyn FnMut(&OnceState)` trait-object closure dispatch**, `panic!` / `assert!` poisoning paths (`#[track_caller]`), and `futex_wake_all`. |
| **5** | **`std::sync::Once` & `OnceLock<T>`** (`sync/once.rs:1-402`, `once_lock.rs:1-709`) | `402` / `709` | Delegates to `sys::Once` (`OnceLock` adds `Relaxed` fast path via `Once::is_completed` / `UnsafeCell<MaybeUninit<T>>`) | Wraps caller `F: FnOnce()` inside `let mut f = Some(f); ... f.take().unwrap()()`, generic closures + `dyn FnMut`, `OnceLock` `Drop` calling `assume_init_drop()` (`value: UnsafeCell<MaybeUninit<T>>`), `Option<&T>` / `Result<(), T>`. |
| **6** | **`std::sys::sync::rwlock::futex::RwLock`** (`sys/sync/rwlock/futex.rs:1-359`) | `359` | `Atomic<u32>`: `try_update`, `compare_exchange(_weak)`, `fetch_add/sub`, `load` (`Rlx/Acq/Rel`) | Bit-packed 30-bit reader count + `READERS_WAITING` (`1<<30`) + `WRITERS_WAITING` (`1<<31`), **two** futexes (`state` + `writer_notify`), higher-order closure `try_update` / `spin_until(impl Fn)`, `downgrade()`, and overflow `assert!`. |
| **7** | **`std::sync::Mutex<T>`** (`sync/poison/mutex.rs:1-946`, `sync/poison.rs:60-200`) | `946` (+`389`) | Same as Rank 3 + `AtomicBool` (`Rlx`) poison flag | Under `-Cpanic=unwind`, `poison::Flag` uses **`std::thread::panicking()`** (thread-local panic counter) in `Flag::guard`/`done`; under `-Cpanic=abort` (`#![cfg_attr(not(panic = "unwind"), ...)]`), `Flag` becomes zero-sized and `PoisonError` carries `_never: !`, though `Result<MutexGuard, PoisonError<_>>` callers still unwrap (`6` -> `8` BBs abort->unwind). |
| **8** | **`alloc::sync::Arc<T>`** (`alloc/src/sync.rs:61-2882`, `4976` total) | `4976` | `Atomic<usize>`: `fetch_add(Rlx)`, `fetch_sub(Rel)`, **`atomic::fence(Acq)`**, CAS, `try_update` | Hardest standalone `alloc` primitive: heap `Box`/`Allocator`/`Layout` + `NonNull<ArcInner<T: ?Sized>>`, **`Release` RMW -> `Acquire` fence synchronization** (`Drop::drop` lines `2836-2868`, falling back to `load(Acq)` only under `cfg(sanitize = "thread")`), `Weak` count (`drop_slow`), `drop_in_place`, `MAX_REFCOUNT` + `intrinsics::abort()`. |

**Cross-cutting caller-level MIR measurement (`std_o0_abort` vs. `std_o0_unwind`):** Even tiny safe callers touching `Mutex`, `RwLock`, `Condvar`, or `Arc` emit `TerminatorKind::Drop` under **both** `-Cpanic=abort` and `-Cpanic=unwind` (e.g., `call_nonpoison_mutex`: `drop=True` in both; `call_arc_clone_drop`: `bb=5 -> 9` with `clean=True` under `unwind`), whereas `Once::is_completed` and `OnceLock::{get, set}` callers emit `0` `Drop` terminators and `0` cleanup pads—meaning caller code only sees `Drop`/cleanup if RAII guards (`MutexGuard`, `RwLockGuard`, `Arc`) or `Result`/`Option` wrappers are dropped in scope.

---

### 4. Recommended Incremental Unblocking Sequence for Anneal Capture

Basis: derived from Sections 1–3 (`extract.rs`, `Boundary.lean`, `mir_census_summary.json`).

1. **Milestone A — Toy `RawSpinLock` & `AtomicOnceU64` (`core`-only, zero `Drop`/FFI):**
   - Admit `UnsafeCell<T>` (`#[lang = "unsafe_cell"]`, checked structurally in `check_stdlib_capability` if `--stdlib-crate core`), `Atomic<T>` (`#[rustc_diagnostic_item = "Atomic"]`), `MaybeUninit<T>`, non-generic/instantiated struct ADTs + field projections, `Result<T, E>` (or 2-variant enum with scalar payload) + downcast projection, `core_call_op` interception of `core::sync::atomic::Atomic::<T>::*` + `UnsafeCell::get` + `spin_loop`, and revise `bodyMixesRefsAndRawPtrsV2` (`Boundary.lean:445`) so `&UnsafeCell<T>` -> `*mut T` preserves safety invariants without globally forbidding mixed locals.
2. **Milestone B — Toy `ArcCountCore` (`fence(Acquire)`) & `std::sys::sync::mutex::futex::Mutex` (first real `std` item):**
   - Add `core::sync::atomic::fence` to the atomic op table and map `std::sys::pal::unix::futex::{futex_wait, futex_wake}` (or `libc::syscall(SYS_futex, ...)`) to `Trusted.Framework.AssumedStub` external axioms with spurious-wakeup nondeterminism and wake-to-wakeup release/acquire synchronization. Notice `std::sys::sync::mutex::futex::Mutex` requires **neither** `Drop` **nor** unwinding **nor** `dyn Trait` **nor** `Box`.
3. **Milestone C — Safe RAII Stdlib Primitives (`std::sync::nonpoison::Mutex<T>`, `std::sync::Once` / `OnceLock<T>`, `alloc::sync::Arc<T>`):**
   - Add `TerminatorKind::Drop` (with `-Cpanic=abort` first to avoid `(cleanup)` unwinding pads and `thread::panicking()` TLS, then `UnwindAction::Cleanup` + `UnwindResume` for unwind safety), `&mut dyn FnMut` / closure monomorphization (`Once`), and heap `Allocator`/`Box`/`NonNull` (`Arc`).

## Boundaries

1. **Textual MIR Parsing Scope (`support/probe_stdlib_and_toy_mir.py`):** In `std_o0_abort` / `std_o0_unwind`, `call_once_init` emits multi-line formatted MIR calls (`std::sync::Once::call_once::<{closure@...}>`) that the single-line call regex in `probe_stdlib_and_toy_mir.py` leaves empty in `non_atomic_calls`; the underlying `std::sync::Once::call_once` and `sys::sync::once::futex::Once::call` bodies were audited directly from the pinned `rust-src` files (`once.rs:156-167`, `once/futex.rs:146-210`).
2. **Precompiled `std` MIR Bodies:** `rustc --emit=mir` on a downstream wrapper crate emits the wrapper's own `runtime-post-cleanup` MIR (`Once::is_completed`, `Mutex::lock`, `Arc::clone` as cross-crate `Call` terminators) rather than re-dumping upstream `std`/`alloc` MIR bodies; upstream `std`/`alloc` complexity and atomic/FFI usage were established by direct source audit of `rust-src` at the exact pinned commit `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` plus standalone `-Zmir-preserve-ub` MIR compilation of the exact `FutexMutexCore` / `AtomicOnceU64` / `ArcCountCore` core algorithms.
3. **Not Examined:** Non-Linux futex implementations (`windows7.rs`, `pthread.rs`, `queue.rs` mutex/once fallbacks), `#[inline]` heuristics under `--stdlib-crate std`, and multi-thread `std::thread::spawn` / `thread::scope` TLS destructor chains (`std/src/thread/mod.rs`).

## Evidence

- `support/probe_stdlib_and_toy_mir.py` (`515` lines, SHA-256 `241cf72a08d1a4d255bd4577e15fe140d12bde41aded4d1072a3e740134ae229`) — reproducible probe compiling toy & extracted-core concurrency primitives (`-Copt-level={0,1}`, `-Cpanic={abort,unwind}`, `-Zmir-preserve-ub`, `-Zdump-mir=runtime-post-cleanup`, `--emit=mir`) and auditing 11 `library/{core,alloc,std}` synchronization source files from `rustc --print sysroot`.
- `support/mir_census_summary.json` (SHA-256 `24e3655f48dab537a2a72cfc1c2f8138ac22c7c6c5280cd292565f9b9304d01b`) — normalized JSON capture generated on `rustc 1.98.0-nightly (f8a08b688 2026-05-30)` (`25` toy `post_cleanup` bodies, `10` `std_wrap` bodies, `11` `rust-src` files).
- **Primary Upstream Sources Inspected (`google/zerocopy@a4f1182901bf9000022b46b6b0ff32159d36c981` & `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):**
  - Anneal capture & Lean TCB: `anneal/trusted/rustc-capture/src/{capture.rs, extract.rs, ir.rs}`, `anneal/trusted/lean/Trusted/MirAst/{Types, Statements, Terminators}.lean`, `anneal/trusted/lean/Trusted/MirSemantics/{Memory, Step, Boundary, Contract}.lean`, `anneal/trusted/lean/Trusted/{Framework.lean, Framework/Instances.lean}`.
  - Rust stdlib: `library/core/src/intrinsics/mod.rs:95-262`, `library/core/src/sync/atomic.rs:366-419, 3885-4105`, `library/core/src/cell.rs:2319-2367`, `library/std/src/sys/sync/mutex/futex.rs:1-103`, `library/std/src/sys/sync/once/futex.rs:1-211`, `library/std/src/sys/sync/rwlock/futex.rs:1-359`, `library/std/src/sys/sync/condvar/futex.rs:1-56`, `library/std/src/sys/pal/unix/futex.rs:1-160`, `library/std/src/sync/nonpoison/mutex.rs:49-505`, `library/std/src/sync/poison.rs:60-200`, `library/std/src/sync/once.rs:150-225`, `library/std/src/sync/once_lock.rs:140-280`, `library/alloc/src/sync.rs:47-90, 385-445, 2130-2185, 2395-2450, 2820-2882`.
- **Cross-Referenced Corpus Reports:**
  - `anneal-concurrent-mir-capture-target-audit-and-lean-miri-closure` (earlier capture-target & `lean-miri` `UPSTREAM_PIN.json` +33/+25/+39 closure audit).
  - `rust-std-concurrency-intrinsics-futex-mpmc-scope-and-tls-destructor-semantics` (upstream intrinsic/futex/linear-guard analysis).

## Revalidation

1. **Re-run the MIR and `rust-src` census (`<4s`) on any pinned `nightly` toolchain with `rust-src` installed:**
   ```bash
   python3 -B reports/rust-concurrency-primitives-mir-capture-and-stdlib-audit/support/probe_stdlib_and_toy_mir.py \
     --toolchain +nightly-2026-05-31 \
     --out /tmp/mir_census_recheck.json
   ```
   Verify whether `Atomic::<T>::*` remains un-inlined at `runtime-post-cleanup`, whether `sys/sync/mutex/futex.rs` still avoids `Drop`/`SeqCst`/fences/closures, and compare any new intrinsics in `library/core/src/intrinsics/mod.rs`.

2. **Check Anneal's capture and Profile v2 admission diff on a newer `google/zerocopy` checkout (`<1s`):**
   ```bash
   grep -n "mir_drops_elaborated_and_const_checked\|bodyMixesRefsAndRawPtrsV2\|fn core_call_op" \
     anneal/trusted/rustc-capture/src/{capture,extract}.rs \
     anneal/trusted/lean/Trusted/MirSemantics/Boundary.lean
   ```
   Confirms whether `UnsafeCell`, `Atomic<T>`, `Drop`, or mixed `&`/`*mut` bodies have since been admitted.
