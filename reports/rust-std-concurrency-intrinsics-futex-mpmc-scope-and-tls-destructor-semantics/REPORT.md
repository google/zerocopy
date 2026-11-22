# Rust Standard Library Concurrency Surface: Const-Generic Atomic Intrinsics, Futex Synchronization, `mpmc` Protocols, Guard-Leak Deadlocks, `thread::scope`, and TLS Destructors

## Summary

Verifying the soundness and liveness of Rust's standard library concurrency
primitives (`core::sync`, `core::task`, `alloc::sync`, `std::sync`, and
`std::thread`) at `rust-lang/rust` `49d734536222bf28bb6d07d885b3a81d145981da`
requires modeling a closed compiler/OS boundary together with five subtle
semantic invariants that naive C++20 or affine separation-logic models get
wrong:

1. **Closed 17-Intrinsic Compiler Atomic Surface:** Legacy ordering-suffixed
   compiler intrinsics are gone. All `core::sync::atomic` operations lower
   through exactly **17** `#[rustc_intrinsic]` declarations in
   `library/core/src/intrinsics/mod.rs:99-290`, parameterized by const
   `AtomicOrdering` (`ORD_SUCC` and `ORD_FAIL` on `atomic_cxchg` /
   `atomic_cxchgweak`; single `ORD` on the remaining 15; plus `const VOLATILE:
   bool` on `atomic_load` and `atomic_store`). Six two-type RMW intrinsics
   (`atomic_{xadd,xsub,and,nand,or,xor}<T, U>`) accept `T = *mut V, U = usize`
   so `AtomicPtr::fetch_{ptr_add,byte_add,or,and,xor}` preserve pointer
   provenance without integer-to-pointer casts.
2. **Zero `volatile` or Inline-`asm!` UB in `std::sync` (`mpmc` Synchronization
   Split):** `library/std/src/sync/` and `library/std/src/sys/sync/` contain
   zero `read_volatile`, `write_volatile`, or `asm!` calls. In `std::sync::mpmc`
   (backing `std::sync::mpsc` and unstable `std::sync::oneshot`), `array.rs`
   and `list.rs` transfer `T` through `UnsafeCell<MaybeUninit<T>>` non-atomic
   reads and writes synchronized by per-slot `Release`/`Acquire` stamps/flags
   and prevent sleeper/notifier Store-Buffering (`SB`) lost wakeups via direct
   `Ordering::SeqCst` atomic operations on `SyncWaker::is_empty`, `head`, and
   `tail`. By contrast, zero-capacity `zero.rs` uses `Mutex<Inner>` with plain
   `Waker` (zero `SeqCst` operations) and passes raw pointers to
   stack-allocated `Packet<T>` frames across threads, requiring timed-out stack
   owners to spin in `packet.wait_ready()` (`Acquire`) before returning.
3. **OS `futex` Internal `SeqCst` Fence vs. Spurious-Wakeup Asymmetry:** User
   code in `std`'s Linux `futex` backends (`Mutex`, `RwLock`, `Condvar`, `Once`,
   `Parker`) issues **zero** user-space `SeqCst` fences, relying on the OS
   kernel's `FUTEX_WAIT_BITSET` and `FUTEX_WAKE` syscalls to serialize the
   waiter's value check + enqueue against the waker's prior atomic store. Miri
   models this via `atomic_fence(SeqCst)` on both `FUTEX_WAIT` and `FUTEX_WAKE`
   (upgrading `FUTEX_WAIT`'s check load from `Relaxed` in `rust-lang/miri`
   `bc1b6da0` to `Acquire` in `rust-lang/rust` `49d73453`), while omitting
   unprompted spurious wakeups that real Linux `FUTEX_WAIT` permits without
   happens-before synchronization.
4. **Refutation of Affine Guard Ownership and `<=` Shared-Read Lock Levels for
   Deadlock Freedom:** In `#![forbid(unsafe_code)]` safe Rust on multi-threaded
   targets, (a) `core::mem::forget(mutex.lock().unwrap())` safely leaks a
   `MutexGuard` without running `Drop::drop`, permanently leaving a single-lock
   program deadlocked (whereas unwinding under `-C panic=unwind` runs
   `MutexGuard::drop`, poisoning and unlocking the mutex without deadlocking);
   (b) reentrant `Once::call_once` deadlocks the initializing thread; and (c)
   holding `RwLockReadGuard` while a concurrent `RwLock::write()` sets
   `WRITERS_WAITING` causes a second `RwLock::read()` on the same thread to
   deadlock. Deadlock-freedom specifications therefore require **linear**
   `MustRelease` guard obligations and strict `<` lock-level ordering even on
   `std::sync::RwLock::read`.
5. **LLVM `noalias` Guard Representation, `thread::scope` Release Sequences,
   and `LocalKey` Post-Destroy Divergence:** `RwLockReadGuard` and all
   `Mapped*Guard`s store `NonNull<T>` rather than `&T`/`&mut T` so unlocking
   mid-`Drop::drop` does not violate function-entry `noalias` protectors.
   `thread::scope` protects non-`'static` stack borrows via `'scope`/`'env`
   invariance, `catch_unwind`, and a C++20 release sequence of `Packet::drop`
   `fetch_sub(1, Release)` operations into `num_running_threads.load(Acquire) ==
   0`. During thread exit, `native` `#[thread_local]` storage keeps destroyed
   `Drop` keys permanently in `State::Destroyed`, whereas `os` key-based TLS
   resets the key to null after `drop` and lazily re-initializes if accessed by
   a later destructor.

## Applicability

These findings apply to `rust-lang/rust` commit
`49d734536222bf28bb6d07d885b3a81d145981da` across `library/core/src/{intrinsics,
sync,task,hint}`, `library/alloc/src/{sync.rs,task.rs}`, `library/std/src/{sync,
thread,panicking.rs,rt.rs}`, `library/std/src/sys/{sync,thread,thread_local}`,
and `src/tools/miri/src/{concurrency,shims/unix/linux_like/sync.rs}`. For the
historical Miri `FUTEX_WAIT` load-ordering comparison in Finding 3,
`rust-lang/miri` commit `bc1b6da0d31959f0fb30c273955dd95304109cba`
(`src/shims/unix/linux/sync.rs`) is compared directly against the in-tree Miri
sources at `rust-lang/rust` `49d734536222bf28bb6d07d885b3a81d145981da`.

Platform-conditional behavior is scoped explicitly per OS backend (`futex` on
Linux, Android, Windows 8+, FreeBSD, OpenBSD, DragonFly, Fuchsia, and Wasm
atomics; intrusive `queue` / `pthread` / `darwin` on macOS and non-futex Unix;
`windows7` keyed events/SRWLOCK; and `no_threads` on single-threaded targets).
Deadlock execution observations were run on Linux `x86_64` with `-C
panic=unwind`.

## Findings

### 1. Closed Compiler Atomic Intrinsic Surface and `Atomic<T>` / `Waker` Contracts

`Basis: source`

Across all files in `library/core/src/intrinsics/`, exactly **17**
`#[rustc_intrinsic]` declarations implement atomic accesses and fences
(`library/core/src/intrinsics/mod.rs:99-290`; alongside 7 non-atomic
`volatile_*` intrinsics at `lines 998-1054`):

- **Compare-exchange (2 intrinsics, two const orderings):**
  `atomic_cxchg<T, const ORD_SUCC: AtomicOrdering, const ORD_FAIL:
  AtomicOrdering>(dst: *mut T, old: T, src: T) -> (T, bool)` (`lines 101-105`)
  and `atomic_cxchgweak<T, const ORD_SUCC: AtomicOrdering, const ORD_FAIL:
  AtomicOrdering>` (`lines 119-123`).
- **Load and store (2 intrinsics, ordering + volatility const generics):**
  `atomic_load<T, const ORD: AtomicOrdering, const VOLATILE: bool>(src: *const
  T) -> T` (`line 136`) and `atomic_store<T, const ORD: AtomicOrdering, const
  VOLATILE: bool>(dst: *mut T, val: T)` (`line 147`). Standard `Atomic<T>`
  passes `VOLATILE = false`; unstable `load_volatile` / `store_volatile` pass
  `VOLATILE = true`.
- **Single-type RMWs (5 intrinsics):** `atomic_xchg` (`line 157`), `atomic_max`
  (`line 232`), `atomic_min` (`line 243`), `atomic_umin` (`line 254`), and
  `atomic_umax` (`line 265`), each parameterized by `<T, const ORD:
  AtomicOrdering>`.
- **Provenance-preserving two-type RMWs (6 intrinsics):** `atomic_xadd` (`line
  168`), `atomic_xsub` (`line 179`), `atomic_and` (`line 190`), `atomic_nand`
  (`line 201`), `atomic_or` (`line 212`), and `atomic_xor` (`line 223`), each
  parameterized by `<T, U = T, const ORD: AtomicOrdering>(dst: *mut T, src: U)
  -> T`. Instantiating `T = *mut V, U = usize` implements strict-provenance
  `AtomicPtr::fetch_{ptr_add,ptr_sub,byte_add,byte_sub,or,and,xor}`
  (`library/core/src/sync/atomic.rs:2195-2753`), preserving the provenance of
  the pointer stored at `dst`. `AtomicPtr::compare_exchange[_weak]` compares
  integer addresses while returning the loaded pointer's provenance.
- **Fences (2 intrinsics):** `atomic_fence<const ORD: AtomicOrdering>()` (`line
  277`) and `atomic_singlethreadfence<const ORD: AtomicOrdering>()` (`line
  289`).

All public `AtomicBool`, `AtomicPtr<T>`, and `Atomic{I,U}{8,16,32,64,128,size}`
types alias generic `#[repr(C)] pub struct Atomic<T: AtomicPrimitive> { v:
UnsafeCell<T::Storage> }` (`atomic.rs:258-340`), where `T::Storage` enforces
`align_of == size_of` (`atomic.rs:4299-4356`). Const-evaluatable dispatchers
(`atomic_load`, `atomic_store`, `atomic_compare_exchange`, `fence` at
`atomic.rs:3960-4272`) panic on `Acquire`/`AcqRel` stores, `Release`/`AcqRel`
loads, `Relaxed` fences, and `Release`/`AcqRel` CAS failure orderings, while
accepting `failure` stronger than `success` (per C++17 `P0418R2`, e.g.,
`SeqCst` failure with `Relaxed` success). Target-specific lowerings inside
`atomic.rs` include `EMULATE_ATOMIC_BOOL` (`lines 400-406`, emulating `bool`
`swap`/CAS via `fetch_or`/`fetch_and` on RISC-V and LoongArch without sub-word
AMO) and `AtomicBool::fetch_nand` (`lines 1245-1259`, using `fetch_xor`/`swap`
because bitwise `!(1u8) == 0xFE` would write an invalid `bool` bit pattern).

In `library/core/src/sync/sync_view.rs:84-96`, `Exclusive<T>` has been renamed
to `SyncView<T>` (`#[doc(alias = "Exclusive")]`), implementing `Sync`
unconditionally for `T: ?Sized` by requiring `&mut self` for `get_mut` and `T:
Sync` on `&SyncView<T> -> &T` projections. In `library/core/src/task/wake.rs`,
`RawWakerVTable` (`lines 91-215`) fixes field order `(clone, wake,
wake_by_ref, drop)`; `Waker` (`lines 252-555`) is unconditionally `Send + Sync`
(wrapping `self` in `ManuallyDrop` before calling `(vtable.wake)(data)`),
whereas `LocalWaker` (`lines 601-905`) is `!Send + !Sync`, and `Waker::noop()`
(`lines 324-337`) uses `ptr::null()` with a static no-op vtable.

---

### 2. `alloc::sync::{Arc, Weak}` Multi-Word Synchronization Protocols

`Basis: source + derived`

`library/alloc/src/sync.rs` (`lines 393-400, 2044-2954`) coordinates three
distinct multi-word atomic protocols over `ArcInner<T> { strong: Atomic<usize>,
weak: Atomic<usize>, data: T }` (where `ArcInner` initially sets `strong = 1`
and `weak = 1`, representing the collective weak reference held by all strong
owners):

1. **`clone` and `drop` (`lines 1696-1718, 2243-2295`):** `Arc::clone` executes
   `strong.fetch_add(1, Relaxed)` and calls `abort()` if `old_size >
   MAX_REFCOUNT` (`isize::MAX as usize`). `Arc::drop` executes
   `strong.fetch_sub(1, Release) != 1`; the final strong owner executes
   `acquire!(strong)` (`atomic::fence(Acquire)` normally, or
   `strong.load(Acquire)` under ThreadSanitizer at `lines 66-81`) to
   synchronize with the C++20 release sequence of all prior `fetch_sub(1,
   Release)` drops before entering `drop_slow`. `drop_slow` (`lines 2243-2256`)
   constructs a stack `_weak = Weak { ptr: self.ptr }` *before* calling
   `ptr::drop_in_place(&mut (*ptr).data)` so that if `T::drop` unwinds,
   `_weak`'s destructor still decrements `weak` (`fetch_sub(1, Release)` +
   `acquire!(weak)`) and deallocates the `ArcInner` allocation.
2. **`is_unique` / `get_mut` vs. `downgrade` (`lines 2044-2080, 2932-2954`):**
   `is_unique` temporarily locks `weak` via `weak.compare_exchange(1,
   usize::MAX, Acquire, Relaxed)`, checks `strong.load(Acquire) == 1`, and
   restores `weak.store(1, Release)`. Concurrently, `Arc::downgrade` loops on
   `weak.load(Relaxed)`, spins (`hint::spin_loop()`) whenever `cur ==
   usize::MAX`, panics above `MAX_REFCOUNT`, and increments via
   `weak.compare_exchange_weak(cur, cur + 1, Acquire, Relaxed)`.
3. **`make_mut` (`lines 2648-2727`):** Transitions `strong` `1 -> 0` via
   `strong.compare_exchange(1, 0, Acquire, Relaxed)` (preventing concurrent
   `Weak::upgrade`, which only increments `strong` when `strong >= 1`), checks
   `weak.load(Relaxed) == 1`, and arms an unwind guard that restores
   `strong.store(1, Release)` if cloning `T` or allocating the replacement
   `Arc` panics. `Weak::new()` (`lines 3132-3134`) uses sentinel
   `NonNull::without_provenance(NonZeroUsize::MAX)` without allocating, and
   data accesses project via `&raw mut (*ptr).data` rather than `&mut
   ArcInner<T>` to preserve aliasing validity of `strong` and `weak`.

---

### 3. Linux OS Syscall Reduction, Miri `futex` Semantics, and `std::sync::mpmc`

`Basis: source + derived`

On `target_os = "linux"`, all blocking and synchronization modules in
`library/std/src/sync/` (`poison` and `nonpoison` `Mutex`, `RwLock`, `Condvar`;
`Once`, `OnceLock`, `LazyLock`, `Barrier`, `ReentrantLock`, `mpmc`, `mpsc`, and
unstable `oneshot`) and `library/std/src/thread/` (`park`, `scope`, `spawn`,
`LocalKey`) reduce to the 17 compiler atomic intrinsics, global heap
allocation, and a bounded OS/libc call surface:

- **Futex wait/wake (`library/std/src/sys/sync/futex/unix.rs:28-108`):**
  `futex_wait` invokes `SYS_futex` with `FUTEX_WAIT_BITSET |
  FUTEX_PRIVATE_FLAG` and mask `u32::MAX` (computing absolute timeouts via
  `clock_gettime(CLOCK_MONOTONIC)` and reading `__errno_location()`). Both
  `futex_wake` (count `1`) and `futex_wake_all` (count `i32::MAX`) invoke
  `FUTEX_WAKE | FUTEX_PRIVATE_FLAG` (`FUTEX_WAKE_BITSET` is never called by
  `std`).
- **Scheduler yield (`library/std/src/sync/mpmc/utils.rs:126-136`):**
  `Backoff::spin_heavy` (called on contended slot/block/packet waits in
  `mpmc/{array,list,zero}.rs`) invokes `thread::yield_now()` ->
  `libc::sched_yield()`.
- **Thread lifecycle and TLS (`sys/thread/unix.rs`, `sys/thread_local/`):**
  `spawn` / `join` / drop invoke `pthread_create`, `pthread_join`,
  `pthread_detach`, `pthread_attr_{init,setstacksize,destroy}`,
  `dlsym("__pthread_get_minstack")` (glibc), `SYS_gettid`,
  `pthread_setname_np`, and `sigaltstack`/`mmap` stack-guard setup; TLS
  destructors register via `__cxa_thread_atexit_impl` and fallback/cleanup
  `pthread_key_create` (`destructors/linux_like.rs:15-54`,
  `guard/key.rs:8-31`).

**OS `futex` Internal `SeqCst` Fence and Spurious-Wakeup Asymmetry:**
None of `futex::{Mutex, RwLock, Condvar, Once, Parker}` issues a user-space
`fence(SeqCst)` before `futex_wait` or `futex_wake` (for example,
`condvar/futex.rs:16-43` uses `Ordering::Relaxed` exclusively on
`Condvar.futex`, relying on `mutex.unlock()` `Release` -> notifier
`mutex.lock()` `Acquire` to order the waiter's pre-unlock `futex.load(Relaxed)`
before the notifier's `futex.fetch_add(1, Relaxed)`). Preventing Store-Buffering
lost wakeups between a waiter setting `CONTENDED`/`PARKED` and a waker releasing
the state word relies on the kernel's `futex` hash-bucket serialization.

In Miri (`rust-lang/miri` `bc1b6da0` `src/shims/unix/linux/sync.rs:124-177,
245-260` and `rust-lang/rust` `49d73453`
`src/tools/miri/src/shims/unix/linux_like/sync.rs:101-230`), `FUTEX_WAIT`
atomically executes `atomic_fence(SeqCst)` + atomic check of `*addr == val` +
waiter enqueue, and `FUTEX_WAKE` executes `atomic_fence(SeqCst)` + `release ->
acquire` vector-clock transfer (`src/concurrency/sync.rs:641-653`) to each
woken thread (`FUTEX_WAKE` does not dereference `*addr`). Two model subtleties
matter for formal verification:

1. Miri upgraded `FUTEX_WAIT`'s check load from `AtomicReadOrd::Relaxed`
   (`bc1b6da0` `linux/sync.rs:170`) to `AtomicReadOrd::Acquire` (`49d73453`
   `linux_like/sync.rs:148`), which additionally rejects read-only allocations
   and acquires prior `Release` stores on `addr` even on `-1`/`EAGAIN`.
2. Miri's `UnblockKind` (`src/tools/miri/src/concurrency/thread.rs:34-39`) has
   only `Ready` and `TimedOut`—it never generates unprompted spurious wakeups
   on `FUTEX_WAIT`. Because Linux `FUTEX_WAIT` can return `-EINTR` or wake
   spuriously without any `FUTEX_WAKE` (and thus without `acquire` clock
   synchronization), a sound operational model of `futex_wait` must include a
   demonic spurious-return branch without happens-before synchronization so
   non-looping callers are caught.

**`std::sync::mpmc` Synchronization Split (`library/std/src/sync/mpmc/`):**
Whole-subtree inspection confirms zero `volatile` or `asm!` usage across
`std::sync` and `std::sys::sync`:

- **Bounded `array.rs` (`lines 23-309, 548-568`) and unbounded `list.rs` (`lines
  28-405, 556-619`):** Transfer `T` via non-atomic `UnsafeCell<MaybeUninit<T>>`
  writes and reads bracketed by `slot.stamp` (`Release` store / `Acquire` load)
  or `slot.state` (`fetch_or(WRITE, Release)` / `load(Acquire)` +
  `fetch_or(READ, AcqRel)`). Sleeper/notifier Store-Buffering lost wakeups are
  prevented without `fence(SeqCst)` because sleepers run
  `SyncWaker::register` (`is_empty.store(false, SeqCst)`, `waker.rs:156`)
  followed by `SeqCst` loads of `head` and `tail` (`array.rs:548-561`,
  `list.rs:593-619`), while notifiers claim slots via `SeqCst` CAS on
  `tail`/`head` (`array.rs:158, 242`, `list.rs:234, 336`) followed by
  `is_empty.load(SeqCst)` in `SyncWaker::notify` (`waker.rs:172`). Because all
  four accesses in the 2-thread `SB` shape are `SeqCst`, C++20 `S` (`P0668R5`
  `psc_base`) forbids both threads missing each other.
- **Zero-capacity `zero.rs` (`lines 23-62, 65-139, 186-282`):** Wraps
  `Mutex<Inner>` containing plain `Waker` (`zero` `SeqCst` operations, `zero`
  `SyncWaker`/`head`/`tail`). Blocking `send` and `recv` allocate `Packet<T>`
  directly on the caller's stack frame and publish `(&raw mut packet) as *mut
  ()` into `Mutex<Inner>`. When a peer claims that entry, it writes/reads
  `(*packet).msg` on the sleeper's stack and sets `(*packet).ready.store(true,
  Release)` (`lines 108, 127`). If `wait_until` times out after a peer has
  already popped the entry, the stack owner **must** spin in
  `packet.wait_ready()` (`ready.load(Acquire)`, `lines 58, 210, 276`) before
  returning, preventing cross-thread stack-use-after-return.
- **Provenance separation (`select.rs:13-30`):** `Operation::hook` extracts
  `ptr::from_mut(r).addr()` purely as a non-dereferenced integer identifier,
  while `Token` (`ArrayToken`, `ListToken`, `ZeroToken`) preserves raw-pointer
  provenance.

---

### 4. Guard-Leak and Reentrant Deadlocks vs. Unwind Poisoning and `noalias`

`Basis: source + execution + derived`

Compiling `support/single_primitive_deadlock_probes.rs` (`#![forbid(unsafe_code)]`)
with `rustc --edition=2021 -O` on Linux `x86_64` (`-C panic=unwind`) establishes
three concrete refutations for concurrent deadlock-freedom specifications:

1. **Guard Leaks Refute Affine Lock-Order Deadlock Freedom:** Calling
   `core::mem::forget(m.lock().unwrap())` (or leaking a guard via `Box::leak`
   or an `Rc<RefCell<...>>` cycle) in safe Rust skips `MutexGuard::drop`,
   leaving `futex::Mutex` permanently in `LOCKED` (`1`) so any subsequent
   `m.lock()` deadlocks (`forget_deadlock` times out, whereas `drop_control`
   exits `0`). Memory safety is preserved: `Mutex::into_inner` and
   `Mutex::get_mut` require ownership or `&mut Mutex<T>` (proving the leaked
   guard's `'a` borrow has ended), and `pthread::Mutex::drop`
   (`sys/sync/mutex/pthread.rs:58-71`) probes `try_lock()` and intentionally
   leaks its `OnceBox` if locked to avoid POSIX `pthread_mutex_destroy` UB.
   Consequently, proving deadlock freedom requires **linear** guard obligations
   that can only be discharged by `Drop::drop` / explicit unlock, never silently
   discarded.
2. **Unwinding Releases Locks; `GLOBAL_PANIC_COUNT` Uses `Relaxed` `CoWW`+`CoWR`:**
   Under `-C panic=unwind`, panicking while holding `MutexGuard` runs
   `MutexGuard::drop` (`sync/poison/mutex.rs:741-749`), calling
   `self.lock.poison.done(&self.poison)` and `self.lock.inner.unlock()` so
   subsequent `m.lock()` returns `Err(PoisonError)` immediately without
   deadlocking (`panic_unlock_control` exits `0`). `poison::Flag`
   (`sync/poison.rs:82-140`) uses `Ordering::Relaxed` exclusively inside the
   lock critical section, poisoning iff `!guard.panicking &&
   thread::panicking()` (so acquiring and dropping a `Mutex` inside a `Drop`
   impl while already unwinding does *not* poison the lock; `RwLockReadGuard`
   never poisons; and `RwLockWriteGuard::downgrade` at `poison/rwlock.rs:883-895`
   `forget`s the write guard, skipping `poison.done`). `thread::panicking()`
   (`panicking.rs:408-476`) fast-paths `GLOBAL_PANIC_COUNT.load(Relaxed) == 0`
   without TLS access: because each panicking thread executes `fetch_add(1,
   Relaxed)` sequenced-before its matching `fetch_sub(1, Relaxed)`, total
   modification-order prefix positivity plus same-thread `CoWR` guarantees a
   panicking thread never observes `0`.
3. **Single-Primitive Reentrancy Deadlocks (`Once` and Writer-Preferring
   `RwLock`):**
   - `Once::call_once` (and `OnceLock::get_or_init` / `LazyLock::force`)
     deadlocks deterministically on reentrant invocation on all multi-threaded
     targets (`once_reentrant` times out; `once/futex.rs:157-207`,
     `once/queue.rs:199-307`), whereas single-threaded `once/no_threads.rs:104-106`
     panics immediately.
   - Both `rwlock/futex.rs` (`lines 47-162, 231-261`) and `rwlock/queue.rs`
     (`lines 150-157, 396-444`) are writer-preferring: once a waiting writer
     sets `WRITERS_WAITING` (or `QUEUED`), `is_read_lockable` returns `false`.
     A thread holding `r1 = rw.read().unwrap()` that calls `rw.read()` a second
     time after a concurrent writer arrives blocks waiting for that writer while
     holding `r1`, deadlocking (`rwlock_recursive_read_deadlock` times out;
     `rwlock_control` exits `0`). Sound lock-order logics must therefore treat
     `std::sync::RwLock::read` as requiring strict `< level(rw)`, never `<=`.
4. **Guard `NonNull<T>` Representation for LLVM `noalias` (`poison/mutex.rs:321-325`,
   `poison/rwlock.rs:128-233`):** While `MutexGuard<'a, T>` holds `&'a
   Mutex<T>` (whose data lives inside `UnsafeCell<T>`, suppressing Tree Borrows
   function-entry `Frozen`/`Unique` protectors), `RwLockReadGuard` and all
   `Mapped*Guard` types store `NonNull<T>` rather than `&'a T` or `&'a mut T`.
   Passing `&T` or `&mut T` by value into `Drop::drop` would assert LLVM
   `noalias` / Tree Borrows `StrongProtector` across the entire `drop` call
   even though `unlock()` happens before `drop` returns, allowing another
   thread to mutate `*data` while `drop`'s frame is still active.

---

### 5. `std::thread::scope` Soundness and `LocalKey` Destructor Divergence

`Basis: source + derived`

In `library/std/src/thread/scoped.rs` (`lines 16-71, 141-207`) and
`lifecycle.rs` (`lines 55-81, 169-199`):

- `Scope<'scope, 'env>` makes both `'scope` and `'env` **invariant**
  (`PhantomData<&'scope mut &'scope ()>`), passes only `&'scope Scope<'scope,
  'env>` to `f` under `for<'scope>` (so callers cannot `mem::forget` an owned
  `Scope`), wraps `f(&scope)` in `catch_unwind`, and executes an inline loop
  `while scope.data.num_running_threads.load(Acquire) != 0 { main_thread.park()
  }` (`lines 158-164`) *before* `resume_unwind` or normal return.
- Each spawned thread increments `num_running_threads.fetch_add(1, Relaxed)`
  (capped at `usize::MAX / 2` to prevent wraparound if `2^{63}`
  `ScopedJoinHandle`s are forgotten via `mem::forget`, which safely hangs
  `scope` in `park()` rather than dangling `'env` stack borrows). Inside
  `Packet::drop`—strictly *after* dropping the thread's `Result<T>`—each
  completing thread runs `num_running_threads.fetch_sub(1, Release)`. Those
  contiguous RMWs form a single C++20 release sequence on `num_running_threads`,
  synchronizing every child's stack accesses and `T::drop` with `scope`'s final
  `load(Acquire) == 0`.

In `library/std/src/sys/thread_local/`:

- **Native `#[thread_local]` (`native/{mod,eager,lazy}.rs`):** Specializes
  `const`/lazy × `needs_drop::<T>()`. Keys without `Drop` never register
  destructors and remain valid throughout thread exit; `Drop` keys transition
  to `State::Destroyed` *before* `drop_in_place` and **permanently return
  `Err(AccessError)`** on any reentrant or subsequent destructor access.
- **OS key-based TLS (`os.rs:195-247`):** Sets sentinel `1` during `drop`
  (returning `Err(AccessError)` on self-reentrancy), then resets the OS key to
  `null` (`line 242`); a *later* TLS destructor accessing that `LocalKey`
  lazily **re-initializes** a fresh value (iterating up to
  `PTHREAD_DESTRUCTOR_ITERATIONS` on Unix or 5 passes on Windows GNU
  `key/windows.rs:184`, after which mutually resurrecting values leak). Panics
  escaping any TLS destructor abort via `DtorUnwindGuard` (`mod.rs:223`).

## Boundaries

- **Known not to apply:**
  - Under `-C panic=abort`, panicking while holding `MutexGuard` terminates the
    process immediately without running `MutexGuard::drop` (`PoisonError<T>` is
    uninhabited via `_never: !` at `sync/poison.rs:197`).
  - Under `-C panic=unwind`, if a thread acquires `Mutex` while *already*
    unwinding (`thread::panicking() == true`) and catches a nested panic via
    `catch_unwind`, `MutexGuard::drop` unlocks the mutex **without** setting
    the poison flag (`!guard.panicking && thread::panicking()` is `false` at
    `sync/poison.rs:126-128`).
  - On Fuchsia (`sys/sync/mutex/fuchsia.rs:126-132`), leaking a `MutexGuard`
    and calling `lock()` on the **same** thread panics (`ZX_ERR_INVALID_ARGS`)
    rather than deadlocking (whereas `lock()` on a different thread deadlocks).
  - On `!target_has_threads` (`sys/sync/once/no_threads.rs:104-106`), reentrant
    `Once::call_once` panics immediately rather than deadlocking.
- **Not examined:**
  - Third-party concurrency crates (`crossbeam`, `parking_lot`, `tokio`,
    `rayon`, `dashmap`) are covered in separate corpus packages rather than in
    this standard-library report.
  - Proprietary/RTOS `std::sys` sync backends (`solid_asp3`, `teeos`, `xous`,
    `zkvm`) beyond their dispatch signatures.

## Evidence

- **Primary source (`rust-lang/rust` @ `49d734536222bf28bb6d07d885b3a81d145981da`,
  observed `2026-11-22`):**
  - `library/core/src/intrinsics/mod.rs:99-290, 998-1054` (17 atomic/fence + 7
    volatile intrinsics).
  - `library/core/src/sync/atomic.rs:258-440, 1245-1259, 2195-2753, 3960-4514`
    (`Atomic<T>`, `EMULATE_ATOMIC_BOOL`, `fetch_nand`, `AtomicPtr` provenance).
  - `library/core/src/sync/sync_view.rs:84-96` (`SyncView<T>`),
    `library/core/src/task/wake.rs:91-905` (`Waker` / `LocalWaker`).
  - `library/alloc/src/sync.rs:66-81, 1696-1718, 2044-2080, 2243-2295,
    2648-2727, 2932-2954, 3132-3134` (`Arc` / `Weak`).
  - `library/std/src/sync/{poison.rs, poison/mutex.rs, poison/rwlock.rs,
    nonpoison/mutex.rs, mpmc/array.rs, mpmc/list.rs, mpmc/zero.rs,
    mpmc/waker.rs, mpmc/select.rs, mpmc/utils.rs, oneshot.rs}` and
    `library/std/src/panicking.rs:408-476`.
  - `library/std/src/sys/sync/{futex/unix.rs, mutex/futex.rs, mutex/pthread.rs,
    rwlock/futex.rs, rwlock/queue.rs, condvar/futex.rs, condvar/pthread.rs,
    once/futex.rs, once/queue.rs, once/no_threads.rs, thread_parking/futex.rs}`.
  - `library/std/src/thread/{scoped.rs, lifecycle.rs, current.rs, functions.rs}`
    and `library/std/src/sys/thread_local/{mod.rs, native/eager.rs,
    native/lazy.rs, os.rs, destructors/linux_like.rs, guard/key.rs,
    key/windows.rs}`.
  - `src/tools/miri/src/shims/unix/linux_like/sync.rs:101-230` and
    `src/tools/miri/src/concurrency/{sync.rs:641-653, thread.rs:34-39}`
    (compared with `rust-lang/miri` @ `bc1b6da0d31959f0fb30c273955dd95304109cba`
    `src/shims/unix/linux/sync.rs:124-260`).
- **Executable probe (`support/single_primitive_deadlock_probes.rs`, observed
  `2026-11-22` on Linux `x86_64`):**
  Compiled with `rustc --edition=2021 -O` (`#![forbid(unsafe_code)]`). Running
  each mode under a `400ms` timeout produced:
  - `forget_deadlock`, `once_reentrant`, `rwlock_recursive_read_deadlock` ->
    `TIMEOUT` (deterministic deadlock);
  - `drop_control`, `once_control`, `rwlock_control` -> `exit=0` (`TERMINATED`);
  - `panic_unlock_control` -> `exit=0` (`TERMINATED_POISONED`).

## Revalidation

1. **Intrinsic and `volatile`/`asm!` surface check:** On a newer `rust-lang/rust`
   checkout, scan `library/core/src/intrinsics/` for `#[rustc_intrinsic]`
   declarations matching `atomic|fence` (expecting 17 declarations unless new
   intrinsics such as bytewise unordered atomic copies land) and scan
   `library/std/src/{sync,sys/sync}` for `(read_volatile|write_volatile|asm!)`
   (expecting 0 matches).
2. **Deadlock and unwind contrast reproducer:** Compile and run
   `rustc --edition=2021 -O support/single_primitive_deadlock_probes.rs -o
   /tmp/probe` across all seven modes (`timeout 0.5s /tmp/probe <mode>`),
   verifying that the three deadlock witnesses time out while all four controls
   exit `0`. This probe checks runtime lock/once state machines on the host OS
   backend; re-inspect `sys/sync/{rwlock,once}/` directly when checking other
   target OSes.
