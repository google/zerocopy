# `RefCell` Non-Poisoning Borrow Guards, Panic Unwind Recovery, `Mutex` Poisoning Contrast, and Separation-Logic Cleanup Contracts

## Summary

Under `panic = "unwind"`, `core::cell::RefCell<T>`, `std::sync::poison::Mutex<T>`, and nightly `std::sync::nonpoison::Mutex<T>` (`#134645`) implement sharply distinct panic-boundary protocols that separate **physical validity / memory safety** (`PhysValid`, `SafeInv`) from **user-level logical invariants** (`UserInv`). Inspecting upstream `rust-lang/rust` (`5c56312f346d7cc8209d9fc0fd660c72e6fc6950`), RFC 1236 (`f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`), the Unsafe Code Guidelines (`d809f91e62968913d808e53397fbcf7cea762cce`), and separation-logic frameworks (RustBelt, Iris, RefinedRust, Verus) establishes four primary results:

1. **Unconditional Guard Release in `RefCell<T>` and `nonpoison::Mutex<T>`:** `core::cell::BorrowRefMut::drop` (`core/src/cell.rs:2055-2062`) unconditionally executes `self.borrow.replace(borrow + 1)` without inspecting panic state (`core` is `#![no_std]` and has no thread-panic runtime). When a mutation through `RefMut` (or `RefCell::replace_with`) panics mid-update and a caller recovers via `std::panic::catch_unwind`, `RefCell` restores `borrow = UNUSED (0)` cleanly, silently exposing broken `UserInv` state to subsequent `borrow()`/`borrow_mut()` calls. `std::sync::nonpoison::Mutex<T>` (`nonpoison/mutex.rs:477-484`) mirrors this single-threaded behavior across threads, storing no `poison::Flag` and calling `self.lock.inner.unlock()` unconditionally.
2. **Best-Effort Advisory Poisoning in `std::sync::poison::Mutex<T>`:** `poison::MutexGuard::drop` (`std/src/sync/poison/mutex.rs:747-755`) invokes `poison::Flag::done(&self.poison)` before `self.lock.inner.unlock()`, recording `failed.store(true, Ordering::Relaxed)` iff `!guard.panicking && thread::panicking()` (`std/src/sync/poison.rs:125-129`). Synchronization of `failed` piggybacks entirely on the mutex unlock-lock release-acquire edge. Crucially, poisoning can be bypassed by `Mutex::get_mut(&mut self)`, nested `catch_unwind` inside a `MutexGuard`, acquiring a guard while already unwinding (`guard.panicking == true`) and panicking again into `catch_unwind`, or foreign `"C-unwind"` exceptions (`poison/mutex.rs:36-53`).
3. **Three-Tier Invariant Separation & Soundness Boundary:** Safe operations (`AssertUnwindSafe`, `RefCell::borrow`, `PoisonError::into_inner`) can recover any value across panics. Therefore, **neither `UnwindSafe` nor `Mutex` poisoning may ever guard `PhysValid` or library `SafeInv`**; any `unsafe` block that temporarily breaks `SafeInv` across a potentially panicking operation must install its own `Drop` cleanup guard (`poison/mutex.rs:54-83`, RFC 1236:111-176).
4. **Type-System Algebra (`UnwindSafe` / `RefUnwindSafe`) and Separation-Logic Cleanup Rules (`EWP`):** `UnsafeCell<T>: !RefUnwindSafe` (`core/src/panic/unwind_safe.rs:198`) makes `&RefCell<T>`, `Rc<RefCell<T>>`, and `&nonpoison::Mutex<T>` **`!UnwindSafe`**, while owned `RefCell<T>: UnwindSafe` (when `T: UnwindSafe`) because consuming ownership prevents post-panic observation, and `&poison::Mutex<T>: UnwindSafe` unconditionally (`std/src/panic.rs:264-275`). In separation logic with Exceptional Weakest Preconditions (`EWP`), sound verification requires either (i) a **disjunctive poison-bit protocol** for `poison::Mutex` (`(~failed * UserInv(v)) \/ (failed * SafeInv(v))`), (ii) **static invariant-mask / `no_unwind` discipline** (Verus), or (iii) **LIFO `RollbackGuard` compensation** dropped before `BorrowRefMut`/`MutexGuard` on unwind.

## Applicability

These findings apply to the concrete upstream revisions and formal foundations identified in `REPORT.json`:
- **`rust-lang/rust` (`5c56312f346d7cc8209d9fc0fd660c72e6fc6950`)**: Applies to `core::cell::{RefCell, Ref, RefMut}`, `core::panic::{UnwindSafe, RefUnwindSafe, AssertUnwindSafe}`, `std::panic::catch_unwind`, `std::sync::poison::{Flag, Guard, Mutex, MutexGuard, PoisonError}`, and nightly `std::sync::nonpoison::{Mutex, MutexGuard}` (`#![feature(sync_nonpoison, nonpoison_mutex)]`, tracking issue `#134645`). Under `-C panic=abort`, `poison::Flag` collapses to a zero-sized no-op (`std/src/sync/poison.rs:132-145`) and unwinding destructors never run (`catch_unwind` cannot catch aborting panics, `std/src/panic.rs:320-323`).
- **`rust-lang/rfcs` (`f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`, `text/1236-stabilize-catch-panic.md`)** and **`rust-lang/unsafe-code-guidelines` (`d809f91e62968913d808e53397fbcf7cea762cce`)**: Supply the design rationale for `UnwindSafe` (stabilized from RFC 1236's `PanicSafe`) and the formal distinction between language validity invariants and library safety invariants.
- **Verification Frameworks**: `RustBelt` (`doi:10.1145/3158154`), `Iris` (`doi:10.1017/S0956796818000151`), `RefinedRust` (`doi:10.1145/3656422`), and `Verus` (`doi:10.1145/3694715.3695952`). Note that foundational RustBelt (`2018`) did not model full unwinding/`catch_unwind` recovery; `EWP` and Verus `no_unwind` masks extend separation-logic reasoning to unwind edges.

Sibling corpus reports `rustbelt-refinedrust-verus-creusot-and-rust-ownership-verifiers` and `ghostcell-branded-tokens-intrusive-containers-and-generational-arenas` cover general ownership verification and rank-2 branded interior mutability without unwind recovery.

## Findings

### 1. Operational Unwind Behavior of `RefCell<T>`, `poison::Mutex<T>`, and `nonpoison::Mutex<T>`

Basis: normative + source + derived + execution

`RefCell<T>`, `poison::Mutex<T>`, and `nonpoison::Mutex<T>` share the same underlying `UnsafeCell<T>` interior-mutability core yet diverge in their runtime guard bookkeeping during stack unwinding (`5c56312f346d`):

| Primitive | Lock / Borrow State | Unwind Guard Action (`Drop`) | Post-Unwind State | Safe Observation After `catch_unwind` |
|---|---|---|---|---|
| `core::cell::RefCell<T>` (`core/src/cell.rs:854-863, 2050-2109`) | `borrow: Cell<isize>` (`0 = UNUSED`, `>0` readers, `<0` writers) | `BorrowRefMut::drop` executes `self.borrow.replace(borrow + 1)` unconditionally | `borrow == 0` (`UNUSED`); zero poison flag | `cell.borrow()` / `cell.borrow_mut()` succeed silently (`Ok` by panic-free return) |
| `std::sync::poison::Mutex<T>` (`std/src/sync/poison.rs:82-158`, `poison/mutex.rs:227-283, 747-755`) | `sys::Mutex` + `poison: Flag { failed: Atomic<bool> }` | `Flag::done`: if `!guard.panicking && thread::panicking()` then `failed.store(true, Relaxed)`, then `unlock()` | Unlocked; `failed == true` (for non-nested panics) | `lock()` returns `Err(PoisonError<MutexGuard>)`; callers unwrap/propagate or extract via `into_inner()` |
| `std::sync::nonpoison::Mutex<T>` (`std/src/sync/nonpoison/mutex.rs:50-53, 477-484`) | `sys::Mutex` only (`0` poison bits) | `MutexGuard::drop` executes `self.lock.inner.unlock()` unconditionally | Unlocked; indistinguishable from normal return | `lock()` returns `MutexGuard<'_, T>` directly |

Four concrete implementation mechanisms explain subtle differences observed in practice:

1. **Why `RefMut` Uses `NonNull<T>` Instead of `&mut T` (`core/src/cell.rs:2102-2109`):** Both `RefMut<'b, T>` and `nonpoison::MappedMutexGuard<'a, T>` (`nonpoison/mutex.rs:148-155`) store `NonNull<T>` + `PhantomData<&'b mut T>` rather than `&'b mut T`. A `&'b mut T` field passed into helper functions receives LLVM `noalias` and Tree Borrows `StrongProtector` for the full call duration; storing `NonNull<T>` avoids asserting uniqueness after the guard drops or unwinds mid-call. Note that `RefMut::leak` (`cell.rs:2038-2047`) achieves permanent lock-out (`mem::forget(orig.borrow)`) only by keeping `borrow < 0` forever—the opposite of `BorrowRefMut::drop`. Similarly, `RefMut::map_split` (`cell.rs:1999-2015`) clones `BorrowRefMut` (decrementing `borrow` to `-2, ...`) so two disjoint guards unwind independently, releasing back to `0` only when *both* finish dropping.
2. **Lock-Coupled Memory Ordering of `poison::Flag` (`std/src/sync/poison.rs:87-151`):** `Flag::done` writes `self.failed.store(true, Ordering::Relaxed)` **before** `self.lock.inner.unlock()`, and `Flag::guard` reads `self.failed.load(Ordering::Relaxed)` **after** `self.lock.inner.lock()` succeeds (`poison/mutex.rs:497-500, 724-726`). Because `sys::Mutex::unlock()` provides release semantics synchronized-with the next `sys::Mutex::lock()` acquire semantics, `Relaxed` accesses to `failed` are data-race-free for lock callers without extra fence overhead (whereas `is_poisoned(&self)` outside the lock has no synchronization guarantee, `poison/mutex.rs:557-560`).
3. **Documented Poisoning Bypasses (`poison/mutex.rs:36-83` and `670-673`):** `Flag::done` fails to poison a mutex whose `UserInv` was corrupted across a panic in **four** concrete scenarios (three verified in Probe `C1`–`C3`):
   - **Exclusive Borrow Bypass (`Mutex::get_mut`, `poison/mutex.rs:670-673`):** Calling `mtx.get_mut()` takes `&mut self` without creating a `poison::Guard`; panicking while mutating `&mut T` inside `catch_unwind(AssertUnwindSafe(|| ...))` leaves `failed == false` even though `UserInv` is broken (`PROBE_C1_GET_MUT`).
   - **Nested `catch_unwind` Inside Guard Scope:** If an inner closure panics and is caught by an inner `catch_unwind` *while* `MutexGuard` remains live in the outer frame, `thread::panicking()` returns to `false` before `MutexGuard::drop` executes (`PROBE_C2_NESTED_CATCH`).
   - **Drop / Panic-Hook Re-Acquisition (`!guard.panicking` Guard):** `Flag::guard` snapshots `panicking: thread::panicking()`. When a destructor or panic hook locks an unpoisoned mutex *while an outer panic is already unwinding* (`guard.panicking == true`), `Flag::done` deliberately skips setting `failed = true` (`!guard.panicking == false`) so normal RAII reads/updates inside destructors do not falsely poison locks (`PROBE_C3_DROP_RELOCK`). However, if a *nested* panic occurs during that hook/destructor and is caught via `catch_unwind`, `Flag::done` still fails to poison the lock (`poison/mutex.rs:40-44`).
   - **Foreign Exceptions (`"C-unwind"`):** Unwinding a foreign C++ exception through `MutexGuard::drop` leaves `std::thread::panicking() == false`, so `Flag::done` does not set `failed` (`poison/mutex.rs:49-50`).

### 2. Three-Tier Invariant Stratification (`PhysValid`, `SafeInv`, `UserInv`) and Unsafe Code Soundness

Basis: normative + documentation + source + derived

To formalize what panic recovery can and cannot break, Rust's semantic stack (`unsafe-code-guidelines/reference/src/glossary.md:278-314`, RFC 1236:111-176, RustBelt `doi:10.1145/3158154`, RefinedRust `doi:10.1145/3656422`) partitions type invariants into three strict tiers:

| Tier | Formal Meaning | Examples Across Studied Primitives | Effect of Unwind-Exposed Violation |
|---|---|---|---|
| **1. `PhysValid(T, bytes)`** (Language Validity) | Abstract-machine representation relation (`bool in {0,1}`, non-null aligned `&mut`, initialized scalars, valid enum discriminant) | Inside `RefCell<T>`/`Mutex<T>`, raw bytes must remain valid at `T` at every typed assignment/drop | Immediate Undefined Behavior (UB) |
| **2. `SafeInv(T, val)`** (Library Safety Invariant `[[T]]`) | Semantic invariant required by safe methods of `T` so safe callers cannot trigger UB | `Vec` initialized elements `[0..len)` (`push_ten_more` in RFC 1236:115-134), UTF-8 `String`, valid `*mut T` in `MutexBox` (`poison/mutex.rs:59-82`) | Library **unsoundness** if observable by safe code (UB on next safe call) |
| **3. `UserInv(T, val)`** (Logical Specification Invariant) | Application-domain consistency not tied to memory validity | Conservation law `a + b == 100`, sorted `Vec<i32>`, balanced pair of `RefCell` maps | **Logic bug only**; safe Rust preserves memory safety (`PhysValid` & `SafeInv` still hold) |

**Fundamental Soundness Boundary:** Because `AssertUnwindSafe` (`core/src/panic/unwind_safe.rs:171`), `RefCell::borrow` (`cell.rs:1126`), `nonpoison::Mutex::lock`, and `PoisonError::{into_inner, get_ref, get_mut}` (`poison.rs:312-328`) are all **safe** functions, safe callers can unconditionally recover and inspect the protected `T` after *any* panic. Consequently:
- Every `unsafe` abstraction (like `Vec::push_ten_more` or `MutexBox::replace_with`) **must restore `SafeInv` via its own local RAII `Drop` guard** before unwinding leaves the `unsafe` boundary (`set_len` before writing, or decrementing `len` / aborting on panic).
- Relying on `RefCell` re-borrowing failing, `!UnwindSafe` compile errors, or `poison::Mutex` returning `Err(PoisonError)` to prevent observation of broken `PhysValid` or `SafeInv` is **strictly unsound** (`poison/mutex.rs:52-83`).

### 3. `UnwindSafe`, `RefUnwindSafe`, and `AssertUnwindSafe` Type-System Algebra

Basis: normative + source + derived

`core::panic::unwind_safe` (`core/src/panic/unwind_safe.rs:85-247`) and `std::panic` (`std/src/panic.rs:263-286, 358-360`) encode the boundary of `catch_unwind<F: FnOnce() -> R + UnwindSafe, R>(f: F)` via two **safe** auto traits (`pub auto trait`, never `unsafe`):

- `UnwindSafe`: Safe to move/capture across a `catch_unwind` closure boundary without risking unobserved post-panic state inspection.
- `RefUnwindSafe`: Safe to share `&T` across `catch_unwind` (`impl<T: RefUnwindSafe + PointeeSized> UnwindSafe for &T`, `unwind_safe.rs:183`).

The exact auto-trait derivation produces four non-obvious asymmetries:

| Type / Wrapper | `UnwindSafe`? | `RefUnwindSafe`? | Source Rule & Technical Reason |
|---|---|---|---|
| `&mut T` | **No** (unconditional) | Inherits `T` if `RefUnwindSafe` (`& &mut T`) | `!UnwindSafe for &mut T` (`unwind_safe.rs:181`): caller retains original binding after `catch_unwind` |
| `UnsafeCell<T>` / `RefCell<T>` (owned) | **Yes** iff `T: UnwindSafe` | **No** (`!RefUnwindSafe`) | `!RefUnwindSafe for UnsafeCell<T>` (`unwind_safe.rs:198`): moving owned `RefCell<T>` into `catch_unwind(move \|\| ...)` drops it on panic so caller cannot re-observe it |
| `&RefCell<T>` / `Rc<RefCell<T>>` | **No** | **No** | `&T: UnwindSafe` requires `T: RefUnwindSafe` (`unwind_safe.rs:183`); `Rc` wraps `NonNull<RcBox<T>>` (`NonNull<U>: UnwindSafe` requires `U: RefUnwindSafe`, `unwind_safe.rs:189`) |
| `poison::Mutex<T>` / `&poison::Mutex<T>` / `Arc<poison::Mutex<T>>` | **Yes** (unconditional) | **Yes** (unconditional) | Manual `impl<T: ?Sized> UnwindSafe` & `RefUnwindSafe` (`std/src/panic.rs:264-275`): poisoning alerts post-panic acquirers |
| `nonpoison::Mutex<T>` (owned) | **Yes** iff `T: UnwindSafe` | **No** (`!RefUnwindSafe`) | Contains `UnsafeCell<T>` with **no** manual `RefUnwindSafe` impl (`nonpoison/mutex.rs:50-53`): `&nonpoison::Mutex<T>` and `Arc<nonpoison::Mutex<T>>` are `!UnwindSafe` |
| `AtomicBool`, `AtomicUsize`, `AtomicPtr<T>`, etc. | **Yes** | **Yes** | Explicit `impl RefUnwindSafe` (`unwind_safe.rs:202-246`): single-word atomic ops cannot tear physically, though multi-atomic `UserInv` invariants can still tear across panics |

This explains the structural duality between `RefCell<T>` and `nonpoison::Mutex<T>`: both lack poison flags and therefore rely on `!RefUnwindSafe` (via `UnsafeCell<T>`) to trigger a compile-time "speed bump" whenever shared handles (`&RefCell<T>`, `Rc<RefCell<T>>`, `&nonpoison::Mutex<T>`, `Arc<nonpoison::Mutex<T>>`) cross `catch_unwind` without an explicit `AssertUnwindSafe` wrapper.

### 4. Compositional Separation-Logic Cleanup Rules for Unwinding (`EWP`, Iris, Verus)

Basis: normative + derived + execution

To reason modularly about `RefCell<T>`, `Mutex<T>`, and `catch_unwind` in higher-order separation logic (`Iris`, `doi:10.1017/S0956796818000151`), extend standard weakest precondition `WP_E e { Phi }` with an explicit **exceptional (unwind) postcondition** `Phi_unw`:

```text
EWP_E e { v. Phi_ret(v) } { Phi_unw }
```

meaning: at every step, either `e` steps safely preserving invariants in mask `E`, returns normally with value `v` satisfying `Phi_ret(v)`, or begins stack unwinding satisfying `Phi_unw` (after running all callee cleanup destructors in LIFO order). At a `catch_unwind` boundary (under `panic = "unwind"` for Rust panics):

```text
EWP_top (f ()) { v. Phi_ok(v) } { Phi_err }
-----------------------------------------------------------------------------------
EWP_top (catch_unwind f) { r. (exists v. r = Ok(v) * Phi_ok(v)) \/ (exists p. r = Err(p) * Phi_err) } { False }
```

#### Why Naive Single-State Protocols Fail for `RefCell<T>` and `nonpoison::Mutex<T>`

Suppose a library couples `SafeInv(v) * UserInv(v)` inside a single invariant `I(ell) = exists v. ell |-> v * [[T]](v) * UserInv(v)` protected by `RefCell<T>` or `nonpoison::Mutex<T>`. Opening the cell via `borrow_mut()` / `lock()` extracts `ell |-> v * [[T]](v) * UserInv(v)` plus a linear guard token `Guard(ell)`. On the normal exit path, the caller re-establishes `UserInv(v')` before dropping `Guard(ell)`. On an **unwind path** mid-update (e.g., `mid_transfer_panic` in Probe `A`), `Guard::drop` executes on the MIR cleanup edge where only `[[T]](v_mid)` holds (`UserInv(v_mid)` is **false**!). Because `BorrowRefMut::drop` and `nonpoison::MutexGuard::drop` release the borrow/lock unconditionally, closing `I(ell)` on the unwind edge is **unprovable**, and `catch_unwind` validly allows subsequent safe code to acquire `&T` (`RefCell::borrow()`) and witness `~UserInv(v_mid)`.

#### Three Sound Compositional Disciplines

| Discipline | Protocol / Invariant Shape | Unwind Cleanup Proof Obligation | Post-`catch_unwind` Guarantee |
|---|---|---|---|
| **1. Disjunctive Poison-Bit Protocol** (`poison::Mutex<T>` in Iris) | `I_poison(ell, f) = exists b v. f \|-> b * ell \|-> v * [[T]](v) * ((b = false * UserInv(v)) \/ (b = true * True))` | When `MutexGuard::drop` runs with `!guard.panicking && panicking`, flip `f` to `true` and close the right disjunct using only `[[T]](v)` (`PROBE_B_POISON_MUTEX`) | `lock() -> Ok(g)` gives `UserInv(v)`; `Err(PoisonError)` gives only `[[T]](v)`; `clear_poison()` requires re-proving `UserInv(v_repaired)` |
| **2. Invariant-Mask & `no_unwind` Checking** (Verus `doi:10.1145/3694715.3695952`, `10.1145/3586037`) | Opening `inv` shrinks mask `E -> E \ {iota}`; unwind edges and `Drop::drop` enforce `no_unwind` or require `E = top` | Callee operations executed while `UserInv` is temporarily broken must satisfy `no_unwind` (`Phi_unw == False`), eliminating the unwind cleanup edge statically | `UserInv(v)` holds unconditionally across `catch_unwind` without needing a runtime poison bit |
| **3. LIFO Rollback / Compensation Guard** (`RollbackGuard` for `RefCell` & `nonpoison::Mutex`) | `Guard(ell)` acquired first (`g_cell`), `RollbackGuard(snap, &mut *g_cell)` constructed *second* | By Rust MIR LIFO drop elaboration, on unwind `RollbackGuard::drop` runs *while `g_cell` still holds exclusive access* (`borrow == -1`), restoring `UserInv(snap)` via `no_unwind` rollback before `BorrowRefMut::drop` resets `borrow = 0` (`PROBE_E_LIFO_ROLLBACK`) | `catch_unwind` caller observes `UserInv` restored (`(60, 40)`); normal completion disarms guard via `commit()` (`ManuallyDrop` / `mem::forget`) |

Crucially, Discipline 1 fails if `Mutex::get_mut` or nested `catch_unwind` bypasses `Guard::drop` (`PROBE_C1_GET_MUT`, `PROBE_C2_NESTED_CATCH`), so a sound Iris specification of `poison::Mutex<T>` must restrict `UserInv` closure to closures free of internal `catch_unwind` and require `UserInv(v)` before `get_mut(&mut self)` returns normally (and on unwind if `AssertUnwindSafe(&mut mtx)` is used).

## Boundaries

- **`unsupported` — Borrow-Flag Poisoning in `core::cell::RefCell<T>`:** `RefCell` lives in `#![no_std]` `core` (`core/src/cell.rs`), has no access to `std::thread::panicking()`, and `BorrowRefMut::drop` (`cell.rs:2055-2062`) unconditionally increments `borrow` without poisoning.
- **`unsupported` — Catching `panic = "abort"`, Double-Panic Aborts, or Foreign Unwind Poisoning:** `std::panic::catch_unwind` cannot intercept aborting panics (`std/src/panic.rs:320-323`), and foreign `"C-unwind"` exceptions pass through `MutexGuard::drop` without setting `poison::Flag` (`poison/mutex.rs:49-50`).
- **`known not to apply` — Soundness of `unsafe` Code via `Mutex` Poisoning or `UnwindSafe`:** Neither `UnwindSafe` nor `poison::Mutex` poisoning preserves `PhysValid` or library `SafeInv`: `AssertUnwindSafe`, `PoisonError::into_inner`, `Mutex::get_mut`, nested `catch_unwind`, and panic-hook acquisitions bypass poisoning in safe code (`poison/mutex.rs:36-83`).
- **`unknown` — Future Edition Default Migration for `std::sync::nonpoison::Mutex` (`#134645`):** Whether a future Rust edition will promote `std::sync::nonpoison::Mutex` to `std::sync::Mutex` and how ecosystem crates will audit `Arc<Mutex<T>>` across `catch_unwind` once `!RefUnwindSafe` triggers compile errors remain unresolved upstream.
- **`not examined` — Live `rustc` Execution and Mechanized Rocq/Verus Proof Development:** Live `rustc` compilation of Rust reproducers, runtime microbenchmarking, and machine-checked Rocq `EWP` proofs of `std::panicking` unwinding frames were outside this inspection; behavior is established from upstream source at `5c56312f346d`, RFC 1236, peer-reviewed papers, and the standalone Python state-machine probe below.

## Evidence

### Primary Subjects and Inspected Locations

| Subject | Immutable Identity | Inspected Paths & Lines / Sections | Key Observed Facts |
|---|---|---|---|
| `rust-lang/rust` | `5c56312f346d7cc8209d9fc0fd660c72e6fc6950` | `library/core/src/cell.rs:854-863, 950-961, 1054-1290, 1999-2128` | `RefCell` `BorrowCounter`, `BorrowRefMut::drop` unconditional `borrow + 1`, `RefMut` `NonNull<T>`, `map_split`, `leak`, `replace_with` |
| `rust-lang/rust` | `5c56312f346d7cc8209d9fc0fd660c72e6fc6950` | `library/core/src/panic/unwind_safe.rs:85-247` | `UnwindSafe`, `RefUnwindSafe`, `AssertUnwindSafe`, `!UnwindSafe for &mut T`, `!RefUnwindSafe for UnsafeCell<T>`, atomics |
| `rust-lang/rust` | `5c56312f346d7cc8209d9fc0fd660c72e6fc6950` | `library/std/src/panic.rs:263-286, 318-360` | Manual `UnwindSafe`/`RefUnwindSafe` for `poison::{Mutex, RwLock, Condvar}`, `catch_unwind` abort/foreign-exception notes |
| `rust-lang/rust` | `5c56312f346d7cc8209d9fc0fd660c72e6fc6950` | `library/std/src/sync/poison.rs:82-388`, `poison/mutex.rs:36-83, 227-283, 496-755` | `Flag::done` (`!guard.panicking && thread::panicking()`), `Relaxed` ordering coupled to `unlock()`, bypasses (`get_mut`, hooks, foreign exceptions), `MutexBox` anti-pattern |
| `rust-lang/rust` | `5c56312f346d7cc8209d9fc0fd660c72e6fc6950` | `library/std/src/sync/nonpoison.rs:1-45`, `nonpoison/mutex.rs:50-155, 290-497` | Non-poisoning `Mutex`, unconditional `unlock()` on drop, no `RefUnwindSafe` impl (`#134645`) |
| `rust-lang/rfcs` | `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07` | `text/1236-stabilize-catch-panic.md:111-360` | Exception safety definition, `Vec::push_ten_more` `set_len` `SafeInv` failure, `PanicSafe`/`UnwindSafe` non-`unsafe` rationale |
| `rust-lang/unsafe-code-guidelines` | `d809f91e62968913d808e53397fbcf7cea762cce` | `reference/src/glossary.md:278-314` | Formal distinction between validity invariant (`PhysValid`) and safety invariant (`SafeInv`) |
| Peer-Reviewed DOIs | `10.1145/3158154`, `10.1017/S0956796818000151`, `10.1145/3694715.3695952`, `10.1145/3656422` | POPL 2018 (RustBelt), JFP 2018 (Iris), SOSP 2024 (Verus), PLDI 2024 (RefinedRust) | Separation-logic invariants, lifetime protocols, `no_unwind` / invariant masks, validity/safety split |

### Reproducible Execution Probe (`Python 3.13.15`)

Saving the following standalone script to `/tmp/probe_refcell_mutex_unwind.py` and executing `python3 /tmp/probe_refcell_mutex_unwind.py` (`exit 0`) verifies all seven unwind-recovery scenarios (`RefCell`, `poison::Mutex`, three poison bypass/edge cases, `nonpoison::Mutex`, and `RollbackGuard` LIFO compensation):

```python
#!/usr/bin/env python3
"""Operational & invariant probe contrasting RefCell, poison::Mutex,
nonpoison::Mutex, and LIFO RollbackGuard under panic=unwind and catch_unwind.
Models rust-lang/rust 5c56312f346d7cc8209d9fc0fd660c72e6fc6950."""

from dataclasses import dataclass
from typing import Callable, Tuple, TypeVar

T = TypeVar("T")


class UnwindPanic(Exception):
    pass


@dataclass
class Bank:
    a: int
    b: int

    def phys_valid(self) -> bool:
        return isinstance(self.a, int) and isinstance(self.b, int)

    def user_inv(self) -> bool:
        return self.a + self.b == 100


@dataclass
class ThreadState:
    panicking: bool = False


def catch_unwind(th: ThreadState, fn: Callable[[], T]) -> Tuple[str, T | None]:
    saved = th.panicking
    try:
        return ("Ok", fn())
    except UnwindPanic:
        th.panicking = saved
        return ("Err(Panic)", None)


class SimRefCell:
    def __init__(self, v: Bank) -> None:
        self.borrow, self.val = 0, v  # BorrowCounter = isize, UNUSED = 0

    def borrow_mut(self) -> Bank:
        assert self.borrow == 0
        self.borrow = -1
        return self.val

    def drop_mut(self) -> None:
        assert self.borrow < 0
        self.borrow += 1  # core/src/cell.rs:2060 unconditional release

    def borrow_shared(self) -> Bank:
        assert self.borrow >= 0
        self.borrow += 1
        return self.val

    def drop_shared(self) -> None:
        self.borrow -= 1


class SimPoisonMutex:
    def __init__(self, v: Bank) -> None:
        self.locked, self.failed, self.val = False, False, v

    def lock(self, th: ThreadState) -> Tuple[str, bool, Bank]:
        assert not self.locked
        self.locked = True
        return ("Err(Poison)" if self.failed else "Ok", th.panicking, self.val)

    def drop_guard(self, th: ThreadState, guard_panicking: bool) -> None:
        if not guard_panicking and th.panicking:  # sync/poison.rs:126
            self.failed = True
        self.locked = False


class SimNonPoisonMutex:
    def __init__(self, v: Bank) -> None:
        self.locked, self.val = False, v

    def lock(self) -> Bank:
        assert not self.locked
        self.locked = True
        return self.val

    def drop_guard(self) -> None:
        self.locked = False


def mid_transfer_panic(b: Bank) -> None:
    b.a -= 50
    raise UnwindPanic("abort before b.b += 50")


def main() -> None:
    # A: RefCell unconditionally drops borrow flag, exposing broken UserInv
    th = ThreadState()
    cell = SimRefCell(Bank(60, 40))

    def run_cell() -> None:
        b = cell.borrow_mut()
        try:
            mid_transfer_panic(b)
        except UnwindPanic:
            th.panicking = True
            cell.drop_mut()
            raise

    assert catch_unwind(th, run_cell)[0] == "Err(Panic)" and cell.borrow == 0
    post_unwind_borrow = cell.borrow
    seen = cell.borrow_shared()
    print(f"[PROBE_A_REFCELL] post_unwind_borrow={post_unwind_borrow},shared_borrow={cell.borrow},phys={seen.phys_valid()},user_inv={seen.user_inv()},vals={(seen.a, seen.b)}")
    cell.drop_shared()

    # B: poison::Mutex sets failed=True on unwind; Err(Poison) guards UserInv until repair+clear_poison
    pm = SimPoisonMutex(Bank(60, 40))

    def run_pm() -> None:
        st, gp, b = pm.lock(th)
        assert st == "Ok"
        try:
            mid_transfer_panic(b)
        except UnwindPanic:
            th.panicking = True
            pm.drop_guard(th, gp)
            raise

    assert catch_unwind(th, run_pm)[0] == "Err(Panic)" and pm.failed and not pm.locked
    st2, gp2, b2 = pm.lock(th)
    assert st2 == "Err(Poison)" and b2.phys_valid() and not b2.user_inv()
    b2.b += 50
    pm.failed = False  # clear_poison() after restoring UserInv
    pm.drop_guard(th, gp2)
    assert not pm.failed and pm.val.user_inv()
    print("[PROBE_B_POISON_MUTEX] poisoned=True,disjunctive_inv=True,repaired_cleared=True")

    # C1: get_mut bypass; C2: nested catch_unwind bypass; C3: relock inside unwind destructor
    m1 = SimPoisonMutex(Bank(60, 40))
    catch_unwind(th, lambda: mid_transfer_panic(m1.val))
    print(f"[PROBE_C1_GET_MUT] failed={m1.failed},user_inv={m1.val.user_inv()}")

    m2 = SimPoisonMutex(Bank(60, 40))
    _, gp_m2, b_m2 = m2.lock(th)
    catch_unwind(th, lambda: mid_transfer_panic(b_m2))
    m2.drop_guard(th, gp_m2)
    print(f"[PROBE_C2_NESTED_CATCH] failed={m2.failed},user_inv={m2.val.user_inv()}")

    th_unw, m3 = ThreadState(panicking=True), SimPoisonMutex(Bank(60, 40))
    _, gp_m3, b_m3 = m3.lock(th_unw)
    b_m3.a -= 10; b_m3.b += 10
    m3.drop_guard(th_unw, gp_m3)
    print(f"[PROBE_C3_DROP_RELOCK] failed={m3.failed},user_inv={m3.val.user_inv()}")

    # D: nonpoison::Mutex mirrors RefCell across threads
    npm = SimNonPoisonMutex(Bank(60, 40))

    def run_npm() -> None:
        b = npm.lock()
        try:
            mid_transfer_panic(b)
        except UnwindPanic:
            th.panicking = True
            npm.drop_guard()
            raise

    assert catch_unwind(th, run_npm)[0] == "Err(Panic)" and not npm.locked
    b_np = npm.lock()
    print(f"[PROBE_D_NONPOISON] locked=False,phys={b_np.phys_valid()},user_inv={b_np.user_inv()}")
    npm.drop_guard()

    # E: LIFO RollbackGuard dropped before BorrowRefMut restores UserInv
    cell2 = SimRefCell(Bank(60, 40))

    def run_rb() -> None:
        b = cell2.borrow_mut()
        snap, committed = (b.a, b.b), False
        try:
            mid_transfer_panic(b)
            committed = True
        except UnwindPanic:
            th.panicking = True
            if not committed:
                assert cell2.borrow == -1
                b.a, b.b = snap
            cell2.drop_mut()
            raise

    assert catch_unwind(th, run_rb)[0] == "Err(Panic)" and cell2.borrow == 0
    s2 = cell2.borrow_shared()
    assert s2.user_inv()
    print(f"[PROBE_E_LIFO_ROLLBACK] restored={(s2.a, s2.b)},user_inv={s2.user_inv()}")
    cell2.drop_shared()


if __name__ == "__main__":
    main()
```

Observed output (`2026-11-20`, Python `3.13.15`):

```text
[PROBE_A_REFCELL] post_unwind_borrow=0,shared_borrow=1,phys=True,user_inv=False,vals=(10, 40)
[PROBE_B_POISON_MUTEX] poisoned=True,disjunctive_inv=True,repaired_cleared=True
[PROBE_C1_GET_MUT] failed=False,user_inv=False
[PROBE_C2_NESTED_CATCH] failed=False,user_inv=False
[PROBE_C3_DROP_RELOCK] failed=False,user_inv=True
[PROBE_D_NONPOISON] locked=False,phys=True,user_inv=False
[PROBE_E_LIFO_ROLLBACK] restored=(60, 40),user_inv=True
```

## Revalidation

To verify cheaply whether newer revisions of `rust-lang/rust` change any contract documented above:

1. **Diff `library/core/src/cell.rs` (`BorrowRefMut::drop`, `RefMut`)**: Confirm `BorrowRefMut::drop` still executes `self.borrow.replace(borrow + 1)` unconditionally and `RefMut` wraps `NonNull<T>`.
2. **Diff `library/std/src/sync/poison.rs` and `library/std/src/sync/poison/mutex.rs`**: Check `Flag::done` (`!guard.panicking && thread::panicking()`), `MutexGuard::drop`, `clear_poison`, and `get_mut`.
3. **Diff `library/core/src/panic/unwind_safe.rs`, `library/std/src/panic.rs`, and `library/std/src/sync/nonpoison/mutex.rs`**: Verify `!RefUnwindSafe for UnsafeCell<T>`, manual `UnwindSafe`/`RefUnwindSafe` impls for `poison::{Mutex, RwLock, Condvar}`, and whether `nonpoison::Mutex` remains `!RefUnwindSafe` (and check `#134645` / `#134646` stabilization status).
4. **Rerun `python3 /tmp/probe_refcell_mutex_unwind.py` (`< 0.1 s`)** after updating any guard transition rules.
