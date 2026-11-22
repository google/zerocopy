# Rust Ecosystem Concurrency Primitives (`crates.io`): Weak-Memory Synchronization Protocols, `parking_lot` `Relaxed` Upgrade Bugs, `crossbeam` UB/Fence Gaps, Cancellation Compensation, and Work-Stealing Deadlocks

## Summary

Deductive verification of major third-party Rust concurrency libraries (`crossbeam`,
`parking_lot` / `lock_api`, `tokio::sync`, `once_cell`, `arc-swap`, `dashmap`,
`rayon-core`, `portable-atomic`, `atomic-waker`, and `futures`, spanning 788
source files and 220,840 lines of Rust) exposes concrete abstract-machine
Undefined Behavior, weak-memory ordering defects, target-ISA/OS assumptions, and
deadlock/cancellation invariants that do not appear in `std::sync`:

1. **Confirmed Weak-Memory `Ordering::Relaxed` Soundness Bugs in `parking_lot
   0.12.5` (`src/raw_rwlock.rs`):** While `RawRwLock::upgrade` (`line 369`) and
   the `try_upgrade` fast path (`line 384`) use `Ordering::Acquire`, four
   timed/slow upgradable transitions use `Ordering::Relaxed`:
   - `try_upgrade_until` (`lines 481-486`) and `try_upgrade_for` (`lines
     494-499`) execute `state.fetch_sub((ONE_READER | UPGRADABLE_BIT) -
     WRITER_BIT, Ordering::Relaxed)` and immediately return `true` (granting
     `&mut T`) when `state & READERS_MASK == ONE_READER`, failing to acquire
     prior shared readers' `unlock_shared` (`Ordering::Release`, `line 134`).
   - `try_upgrade_slow` (`lines 859-865`, entered from `try_upgrade` whenever
     `PARKED_BIT != 0`) transitions to `WRITER_BIT` via
     `compare_exchange_weak(..., Relaxed, Relaxed)` without `Ordering::Acquire`.
   - `unlock_upgradable_slow` (`lines 815-821, 835-841`) clears `ONE_READER |
     UPGRADABLE_BIT` via `compare_exchange_weak(..., Relaxed, Relaxed)`
     *before* `ThreadParker::unpark_lock` or bucket unlock runs (`parking_lot.rs:1074-1084`),
     allowing a barging `lock_exclusive` writer (`lines 68-71, 621-626`) to
     mutate `&mut T` without happens-before from reads under
     `RwLockUpgradableReadGuard` (including on `lines 815-821` when
     `bump_upgradable_slow` hits `force_fair` after waiter timeout with
     `result.unparked_threads == 0`, because `line 804` omits `unparked_threads
     != 0`).
2. **True C++20/Rust Abstract-Machine UB in `crossbeam` vs. `portable-atomic`'s
   UB-Free `SeqLock`:** `crossbeam-utils 0.8.23` (`atomic_cell.rs:997-1000,
   1094-1205`) still exhibits (a) unsynchronized `ptr::read_volatile` vs.
   non-atomic `ptr::write`/`ptr::replace` data races for non-ZST types failing
   `can_transmute` into `AtomicU{8,16,32,64}` (transitively hit by
   `crossbeam-channel 0.5.15`'s `flavors/tick.rs:20` `AtomicCell<Instant>` on
   64-bit Linux / `timespec`-backed Unix targets) and (b) uninitialized padding
   transmutes into primitive integers for padded types matching integer size and
   alignment (such as `(u8, [u64; 0])`). `crossbeam-deque 0.8.8`
   (`deque.rs:96-108, 681`) likewise races speculative `ptr::read_volatile` in
   `Stealer::steal*` against `ptr::write_volatile` in `Worker::push`. By
   contrast, `portable-atomic 1.13.1` (`imp/fallback/mod.rs:109-168`) eliminates
   the `SeqLock` data race by accessing plain-old-data storage as
   `&[AtomicU64; LEN]` / `&[AtomicU32; LEN]` chunks with `Ordering::Relaxed`.
3. **Cross-Crate `SeqCst` RMW vs. `fence(SeqCst)` Gap (`crossbeam-epoch` +
   `crossbeam-deque`):** On `x86`/`x86_64` with `not(miri)`, `crossbeam-epoch
   0.9.21` (`internal.rs:412-444`) replaces `store(Relaxed); fence(SeqCst)` in
   `Local::pin()` with `compare_exchange(..., SeqCst, SeqCst)` +
   `compiler_fence(SeqCst)`. Under abstract C++20 (`P0668R5`) and RC11, a
   `SeqCst` RMW on `local.epoch` does not order subsequent `Acquire` loads on
   distinct atomics—and `crossbeam-deque 0.8.8` (`deque.rs:660-672, 774-786,
   1016-1028`) skips its own `fence(SeqCst)` between `front.load(Acquire)` and
   `back.load(Acquire)` whenever `!epoch::is_pinned()`, relying on
   `epoch::pin()` to emit one. Verifying unmodified `x86_64` builds therefore
   requires modeling target-ISA `x86-TSO` store-buffer drain rather than pure
   C++20/RC11 alone.
4. **External Queue Happens-Before, Post-Unmap `FUTEX_WAKE`, and Stack-Pinned
   Intrusive Cancellation:** `parking_lot::RawMutex` fair unlock (`TOKEN_HANDOFF`,
   `raw_mutex.rs:299-306`) performs zero atomic operations on `RawMutex.state`,
   transferring happens-before solely through `ThreadParker`, and intentionally
   invokes `SYS_futex(FUTEX_WAKE)` on potentially unmapped stack/TLS pointers
   after bucket unlock (`linux.rs:140-145`). `tokio::sync` (`batch_semaphore.rs`,
   `notify.rs`) embeds `PhantomPinned` *inside* `UnsafeCell` (`linked_list.rs:62-105`)
   to suppress `&mut` `noalias` during concurrent waitlist traversal and runs
   exact permit-return compensation inside `Drop` on future cancellation.
5. **Crate-Specific Deadlock Topologies (`DashMap` vs. `parking_lot::RwLock`,
   and `rayon` Work-Stealing):** `dashmap 6.2.1` (`lock.rs:182-250`) implements
   a custom **reader-preferring** `RawRwLock` (`WRITERS_PARKED` does not block
   shared locks), so nested `get` calls on the **same shard** never deadlock
   even with a parked writer (unlike `parking_lot::RwLock::read`), whereas
   cross-shard `get` + `len()`/`iter()` can still AB-BA deadlock against
   `IterMut::next` (`iter.rs:242-265`). `rayon-core 1.13.0` avoids deadlock on
   pure Rayon latches via recursive stealing in `WorkerThread::wait_until_cold`
   (`registry.rs:780-842`), but exhibits four distinct OS-blocking deadlock
   modes (inline reentrancy, pool starvation, cactus-stack thief inversion, and
   cross-pool cycles).

## Applicability

These findings apply to the exact released `crates.io` archive versions and
SHA-256 digests listed in `REPORT.json`: `crossbeam-utils 0.8.23`,
`crossbeam-epoch 0.9.21`, `crossbeam-deque 0.8.8`, `crossbeam-queue 0.3.13`,
`crossbeam-channel 0.5.15`, `lock_api 0.4.14`, `parking_lot 0.12.5`,
`parking_lot_core 0.9.12`, `tokio 1.54.1`, `once_cell 1.21.4`, `arc-swap 1.8.0`,
`dashmap 6.2.1`, `rayon-core 1.13.0`, `portable-atomic 1.13.1`,
`atomic-waker 1.1.2`, and `futures-{core,util,channel} 0.3.34`. The report
characterizes their combined synchronization, memory-reclamation, aliasing,
deadlock, and cancellation requirements as verification targets under C++20/RC11
weak memory, Tree/Stacked Borrows, and target ISA (`x86_64`, `aarch64`,
`riscv64`) semantics.

## Findings

### 1. Abstract-Machine UB and C++20 Fence Gaps vs. UB-Free `SeqLock` Construction

`Basis: normative + source + derived`

Across all 20 crates (`220,840` lines of source), programmatic comment-stripped
scanning (`support/scan_crates_concurrency_hazards.py`) identifies **3**
`read_volatile`/`write_volatile` sites, **10** `compiler_fence` sites, **124**
`asm!` blocks (`4` in `parking_lot` x86 HLE + `120` in `portable-atomic`), and
**55** `transmute`/`transmute_copy` sites:

- **`crossbeam-utils 0.8.23` (`src/atomic/atomic_cell.rs:368-381, 997-1205`) and
  `crossbeam-channel 0.5.15` (`src/flavors/tick.rs:20`):**
  1. Zero-sized types (`size_of::<T>() == 0`) dispatch to no-op `AtomicUnit`
     (`lines 368, 1047-1069`). Non-ZST types failing `can_transmute` into
     `AtomicU{8,16,32,64}` (including all sizes `> 0` outside `{1,2,4,8}` and
     under-aligned `{2,4,8}`-byte types) fall back to a 67-shard `SeqLock` table
     where `atomic_load` executes `ptr::read_volatile(src.cast::<MaybeUninit<T>>())`
     (`line 1101`) concurrently with unsynchronized non-atomic `ptr::write` /
     `ptr::replace` (`lines 1132, 1152, 1205`)—an unconditional C++20/Rust data
     race (`r[undefined.race]`). On 64-bit Linux and other `timespec`-backed
     Unix targets where `size_of::<Instant>() == 16` (unlike 64-bit macOS, where
     `Instant` is an 8-byte `u64`), `crossbeam_channel::tick` (`tick.rs:20`,
     `delivery_time: AtomicCell<Instant>`) hits this data race whenever two
     threads receive concurrently.
  2. For types satisfying `can_transmute` (`size_of::<A>() == size_of::<B>() &&
     align_of::<A>() >= align_of::<B>()`, `lines 997-1000`) that contain
     uninitialized padding bytes (such as `(u8, [u64; 0])` or `#[repr(align(8))]
     enum Test { Field(u32), FieldLess }`), `atomic_load` (`line 1088`) and
     `mem::transmute_copy::<T, u{8,16,32,64}>` (`lines 1127, 1146, 1173-1174`)
     materialize uninitialized bits inside primitive integers—immediate Rust
     typed-validity UB.
  3. Additionally, `crossbeam-channel 0.5.15` (`src/select_macro.rs:778, 808`)
     transmutes `Result<SelectedOperation<'_>, {TrySelectError,
     SelectTimeoutError}>` into `Option<SelectedOperation<'_>>`, relying on
     unspecified `repr(Rust)` enum niche layout equivalence.
- **`crossbeam-deque 0.8.8` (`src/deque.rs:96-108, 681, 814-874, 1049-1132`):**
  `Buffer::write` (`line 97`) and `Buffer::read` (`line 107`) invoke
  `ptr::write_volatile` and `ptr::read_volatile` on `MaybeUninit<T>`. Because
  `Stealer::steal*` reads slot `f` *before* `front.compare_exchange(f, f + 1,
  SeqCst, Relaxed)` (`line 689`), a single owner `Worker` performing `cap`
  `pop`+`push` cycles wraps circular index `f & (cap - 1)` and races
  `write_volatile` against `read_volatile`.By contrast, `crossbeam-queue 0.3.13`
  (`ArrayQueue` in `array_queue.rs:154-170, 332-357` and `SegQueue` in
  `seg_queue.rs:257-277, 404-430`) gates all `UnsafeCell<MaybeUninit<T>>` slot
  accesses behind `Release`/`Acquire` slot stamps or `WRITE`/`READ`/`DESTROY`
  bitmasks with zero `volatile` races.
- **UB-Free `SeqLock` Reference Pattern (`portable-atomic 1.13.1`,
  `src/imp/fallback/{mod.rs:109-168, seq_lock.rs:38-156}`):** Casts
  `UnsafeCell<$int_type>` to `&[AtomicU64; Self::LEN]` (or `AtomicU32` on
  32-bit targets) and uses `Ordering::Relaxed` chunked atomic loads (`line 142`)
  and stores (`line 166`) inside `optimistic_read` (`state.load(Acquire)` ...
  `fence(Acquire); state.load(Relaxed) == stamp`) and `write` (`state.swap(1,
  Acquire); fence(Release)` ... `state.store(stamp + 2, Release)`), plus an
  inline-`asm!` stack `xchg` `sc_fence()` (`imp/x86.rs:61`) when `order ==
  Ordering::SeqCst`.
- **Cross-Crate `x86_64` `not(miri)` `SeqCst` Fence Gap (`crossbeam-epoch
  0.9.21/src/internal.rs:412-444` + `crossbeam-deque 0.8.8/src/deque.rs:660-672`):**
  When `guard_count == 0` on `x86`/`x86_64` with `not(miri)`, `Local::pin()`
  executes `self.epoch.compare_exchange(Epoch::starting(), new_epoch, SeqCst,
  SeqCst)` + `compiler_fence(SeqCst)` instead of `store(new_epoch, Relaxed);
  fence(SeqCst)`. Under C++20 (`P0668R5`) and RC11, a `SeqCst` RMW on
  `self.epoch` neither orders subsequent `Acquire` pointer loads against
  `Global::try_advance`'s `fence(SeqCst)` (`internal.rs:235`) nor substitutes
  for the `fence(SeqCst)` that `crossbeam-deque`'s `Stealer::steal*` elides when
  `!epoch::is_pinned()` (`deque.rs:665-672`, permitting a C++20 double-pop race
  between `Stealer::steal`'s `front.load(Acquire)` -> `back.load(Acquire)` and
  `Worker::pop`'s `back.store(b - 1, Relaxed); fence(SeqCst);
  front.load(Relaxed)` at `deque.rs:508-513`). Soundness holds on `x86_64`
  hardware only because `lock cmpxchg` drains the x86 store buffer (`x86-TSO`)
  while `compiler_fence(SeqCst)` blocks LLVM reordering.

---

### 2. Weak-Memory Ordering Defects in `parking_lot 0.12.5` and `tokio::sync::oneshot`

`Basis: source + derived`

In `parking_lot 0.12.5` (`src/raw_rwlock.rs`, wrapping `&T` / `&mut T` via
`lock_api 0.4.14` `src/rwlock.rs:2256-2295`):

1. **`try_upgrade_until` (`lines 480-490`) and `try_upgrade_for` (`lines
   493-503`):** Both execute:
   ```rust
   let state = self.state.fetch_sub(
       (ONE_READER | UPGRADABLE_BIT) - WRITER_BIT,
       Ordering::Relaxed,
   );
   if state & READERS_MASK == ONE_READER {
       true
   } else {
       self.upgrade_slow(...)
   }
   ```
   Suppose Thread A holds `RwLockUpgradableReadGuard` (`ONE_READER |
   UPGRADABLE_BIT`), Thread B acquires a shared `RwLockReadGuard` (legal while
   `WRITER_BIT == 0`), reads `*data` non-atomically, and drops its guard via
   `unlock_shared` (`self.state.fetch_sub(ONE_READER, Ordering::Release)`, `line
   134`). Thread A then calls `try_upgrade_for`, observing `READERS_MASK ==
   ONE_READER` via `Ordering::Relaxed` and immediately mutating `*data` via
   `&mut T`. Because `Release` + `Relaxed` does not synchronize in C++20/RC11,
   Thread B's non-atomic read and Thread A's non-atomic write form a data race
   on weak-memory architectures (`ARMv8`, `RVWMO`, `POWER`).
2. **`try_upgrade_slow` (`lines 853-869`):** Entered from `try_upgrade` (`lines
   380-392`) whenever `PARKED_BIT != 0` (e.g., a writer parked on `addr + 1`
   while shared readers drained) or on spurious `compare_exchange_weak` failure;
   transitions `state` to `WRITER_BIT | (state & PARKED_BIT)` with
   `(Ordering::Relaxed, Ordering::Relaxed)` and returns `true` without
   `Ordering::Acquire`.
3. **`unlock_upgradable_slow` (`lines 800-850`):** Inside `unpark_filter`'s
   callback (`parking_lot_core 0.9.12/src/parking_lot.rs:1074`), before
   `ThreadParker::unpark_lock()` (`Release`, `line 1080`) or
   `bucket.mutex.unlock()` (`Release`, `line 1084`) runs, `lines 835-841` clear
   `ONE_READER | UPGRADABLE_BIT` on `self.state` using `(Ordering::Relaxed,
   Ordering::Relaxed)`. A barging thread calling `lock_exclusive` (`CAS(0,
   WRITER_BIT, Acquire, Relaxed)` at `lines 68-71`, or `CAS(PARKED_BIT,
   PARKED_BIT | WRITER_BIT, Acquire, Relaxed)` at `lines 621-626`) acquires
   `&mut T` without touching `bucket.mutex`, racing with non-atomic reads
   performed under `RwLockUpgradableReadGuard`. Moreover, `line 804` (`if
   force_fair || result.be_fair`) omits `result.unparked_threads != 0` (present
   in `unlock_exclusive_slow` at `line 654`), so `bump_upgradable_slow` (`line
   927`) after a waiter timeout also clears `self.state` to `0` via
   `Ordering::Relaxed` at `lines 815-821` with zero `unpark_lock()` calls.

In `tokio 1.54.1` (`src/sync/oneshot.rs:1569-1574`), `State::set_closed`
executes `cell.fetch_or(CLOSED, Ordering::Acquire)` (unlike `set_complete` and
task-unsetting helpers at `lines 1541-1582`, which use `AcqRel`). Consequently,
`rx.close()` (`line 947`) does not establish happens-before to a sender
observing `tx.is_closed() == true` (`Acquire`, `lines 776, 828`) when no waker
slot is taken.

---

### 3. Reclamation, External Happens-Before, Stack Pinning, and Provenance Idioms

`Basis: source + derived`

- **Reclamation Diversity Beyond 3-Epoch EBR:**
  - `arc-swap 1.8.0` (`src/debt/{fast.rs, helping.rs, list.rs}`,
    `src/strategy/hybrid.rs:46-66`): Readers reserve a zero-refcount pointer
    debt in thread-local `FastSlots` (`swap(ptr, SeqCst)` confirmed by
    `storage.load(SeqCst)` to preserve `AtomicPtr` provenance); `swap` writers
    (`lib.rs:483`) `SeqCst`-swap `ptr` and pay live reader debts by
    incrementing `Arc` strong counts (`T::inc`) and CAS-clearing debt slots with
    `Release` (`debt/mod.rs:76`), falling back to wait-free `HelpingSlots` +
    `NODE_COOLDOWN` (`active_writers == 0`) on 30/62-bit generation wraparound.
  - `tokio::sync::mpsc` (`src/sync/mpsc/{list.rs:67-178, block.rs:188-256}`) and
    `crossbeam-queue::SegQueue` (`src/seg_queue.rs:101-117, 430`): Reclaim
    blocks without EBR—`tokio::mpsc` tracks single-consumer
    `observed_tail_position > block_end`, while `SegQueue` and
    `crossbeam-deque::Injector` race `fetch_or(READ, AcqRel)` against
    `fetch_or(DESTROY, AcqRel)` on every slot.
- **External Wait-Queue Happens-Before & Post-Unmap `FUTEX_WAKE` (`parking_lot`):**
  On fair unlock (`TOKEN_HANDOFF`, `raw_mutex.rs:299-306`), `RawMutex` leaves
  `LOCKED_BIT = 1` untouched on `RawMutex.state`; exclusive `&mut T` ownership
  and happens-before transfer solely via `Bucket.mutex` +
  `ThreadParker::unpark_lock` (`futex.store(0, Release)`, `linux.rs:98`) ->
  waiter `park` (`futex.load(Acquire)`, `linux.rs:68`). Afterwards,
  `UnparkHandle::unpark` (`linux.rs:140-145`) invokes `SYS_futex(FUTEX_WAKE)` on
  the raw `futex: *const AtomicI32` *after* releasing `Bucket.mutex`, when the
  woken thread may already have popped its stack or exited (relying on Linux
  `sys_futex` returning `-EFAULT` without user-space dereference).
- **Stack-Pinned Intrusive Lists & LLVM `noalias` (`tokio`, `rayon`):**
  `tokio 1.54.1` (`src/util/linked_list.rs:62-105, 433-450`) places
  `PhantomPinned` *inside* `UnsafeCell<PointersInner<T>>` (so `&mut` to the
  wrapper is `!Unpin`, suppressing Tree Borrows / LLVM `noalias` protectors) and
  projects exclusively via `ptr::addr_of_mut!`; `NotifyWaitersList::drop`
  (`notify.rs:360-373`) unlinks its stack sentinel if a user `Waker::wake()`
  panics. `rayon-core 1.13.0` (`latch.rs:46-50, 426-456`) passes `*const Self`
  into `Latch::set` because signaling `state.swap(SET, AcqRel)` lets the owner
  immediately pop its `StackJob` frame (leaving a minor residual temporary `&T`
  `dereferenceable` window at `latch.rs:215` and `job.rs:121`).
- **Strict-Provenance Split:** `portable-atomic` (`64` sites), `once_cell`
  (`imp_std.rs:245-287`), `futures-util` (`bilock.rs:296`), and `tokio`
  (`util/ptr_expose.rs` Miri side-table) preserve or explicitly expose pointer
  provenance, whereas `crossbeam-epoch` (`atomic.rs:1294-1314`, storing tagged
  pointers in `AtomicUsize`), `parking_lot_core` (`word_lock.rs:150, 204`), and
  `arc-swap` (`helping.rs`) rely on permissive `ptr as usize as *const T` casts.

---

### 4. Multi-Primitive Deadlock Topologies and Async Cancellation Compensation

`Basis: source + derived`

- **Canonical Two-Bucket Requeue Ordering (`parking_lot_core 0.9.12`,
  `src/parking_lot.rs:416-467`):** `Condvar` requeue locks two dynamic hash
  buckets in strict ascending index order `min(h1, h2)` then `max(h1, h2)`
  (matching `grow_hashtable`'s `0..len` lock order at `lines 264-275`), locking
  only once when `h1 == h2` (`lines 425-427`). Using a single `parking_lot::Condvar`
  concurrently with two distinct `RawMutex` instances panics deterministically
  (`condvar.rs:310-312, 348-350`).
- **`parking_lot::RwLock` vs. `DashMap` Reader-Preference Split:**
  - `parking_lot::RwLock::read` (`raw_rwlock.rs:511-520`) blocks new readers
    whenever `WRITER_BIT != 0` (deadlocking nested `read()` + `read()` if a
    writer arrives, unless `read_recursive()` is used; double
    `upgradable_read()` or `read()` + `upgradable_read()` + `upgrade()` also
    self-deadlock at `lines 576, 874, 984`).
  - `dashmap 6.2.1` (`src/lock.rs:182-250`) instead uses a custom
    **reader-preferring** `RawRwLock` (`WRITERS_PARKED = 0b0010` does not cause
    `state.checked_add(ONE_READER)` to overflow or match `ONE_WRITER = !0b0011`),
    so nested `get` calls **on the same shard** never deadlock even with a
    parked writer. However, holding `Ref` + calling a same-shard write op (or
    all-shard `retain`/`clear`/`shrink_to_fit`/`iter_mut`), holding
    `RefMut`/`Entry` (`entry()` write-locks eagerly even when vacant,
    `lib.rs:1190`) + any overlapping op, or holding `get` on shard `1` + calling
    all-shard `len()`/`iter()` while another thread's `IterMut::next`
    (`iter.rs:242-265`) holds shard `0`'s write guard and advances to shard `1`
    deadlocks. Panicking inside `DashMap::alter` aborts via `AbortOnPanic`
    (`util.rs:10-23`).
- **`rayon-core 1.13.0` Helping vs. Four OS-Blocking Deadlock Modes
  (`src/{join/mod.rs:132-186, registry.rs:543-563, 780-842}`):** Pure Rayon
  `join(A, B)` avoids deadlock when stolen `B` blocks on a Rayon latch because
  `wait_until_cold` steals and executes pool work on the waiting worker's stack.
  Deadlock still occurs under: (1) *unstolen inline reentrancy* (holding OS
  `Mutex M` across `join(A, B)` when `B` runs inline on the same OS thread and
  locks `M`), (2) *pool starvation* (`A` OS-parks on a channel/condvar/barrier
  waiting for un-stolen `B` when all workers are OS-blocked), (3) *cactus-stack
  thief inversion* (Worker 2 steals `B`, locks OS `Mutex M`, calls `join(B1,
  B2)`, and enters `wait_until(&job_b2)` while holding `M`, while Worker 1
  steals `B2` and OS-blocks on `M.lock()`), and (4) *cross-pool OS lock cycles*
  (`in_worker_cross` steals only the calling pool's tasks).
- **Async Cancellation Compensation vs. Blocking Traps:**
  - `tokio::sync::batch_semaphore` (`Acquire::drop`, `lines 776-778`),
    `tokio::sync::Notify` (`drop_notified`, `lines 1364-1370`), and
    `futures::lock::Mutex` (`MutexLockFuture::drop`, `lines 167-176`) actively
    return or forward satisfied permits/wakeups inside `Drop` when a waiting
    future is cancelled.
  - `tokio::sync::Barrier::wait` (`barrier.rs:152`) mutates `arrived += 1`
    without `Drop` rollback and is **not** cancel-safe;
    `crossbeam_channel::SelectedOperation::drop` (`select.rs:1295-1298`) panics
    unconditionally if dropped without completing the selected operation;
    `tokio::sync::watch::Ref` (`watch.rs:221-241`) holds a synchronous
    `std::sync::RwLockReadGuard` (deadlocking single-thread executors if held
    across `.await`); `tokio::sync::mpsc::Receiver::try_recv` (`chan.rs:477-485`)
    synchronously parks the OS thread on `TryPopResult::Busy`; and
    `futures::channel::mpsc` (`queue.rs:142-163`) busy-yields (`yield_now()`) on
    preempted `Inconsistent` Vyukov pushes.

## Boundaries

- **Known not to apply:**
  - `crossbeam-utils` `AtomicCell<T>` zero-sized types (`size_of::<T>() == 0`)
    use lock-free `AtomicUnit` (`atomic_cell.rs:368`) and do not enter the
    `SeqLock` `read_volatile` path.
  - On 64-bit macOS/Darwin, `std::time::Instant` is 8 bytes (`u64`), so
    `crossbeam_channel::tick` uses lock-free `AtomicU64` rather than the
    16-byte `SeqLock` fallback hit on 64-bit Linux/`timespec` Unix targets.
  - `DashMap` reader-preference deadlock freedom applies only to shared reads on
    the **same shard** (`get` + `get`); multi-shard `len()`/`iter()` can still
    interleave in opposite shard order against `IterMut::next`.
- **Not examined (dynamic execution):**
  - The `parking_lot 0.12.5` `raw_rwlock.rs` `Ordering::Relaxed` bugs and the
    `crossbeam-epoch`/`crossbeam-deque` C++20 `SeqCst` RMW gap were established
    by primary-source inspection and axiomatic C++20/RC11 trace derivation; no
    ARMv8 hardware litmus run or dynamic Loom/GenMC execution was run in this
    pass.
  - Optional `tokio` I/O driver (`mio`/`io_uring`), timers, and work-stealing
    run-queue internals outside `src/sync/`, `src/util/{linked_list,ptr_expose}.rs`,
    and `src/runtime/task/state.rs` were not audited for weak-memory defects.

## Evidence

- **Unpacked `crates.io` release archives (verified against SHA-256 digests in
  `REPORT.json`, observed `2026-11-22`):**
  - `crossbeam-utils-0.8.23/src/{atomic/atomic_cell.rs:43,368-381,997-1205,
    atomic/seq_lock.rs:26-95, atomic/consume.rs:34-62, sync/parker.rs:310-415,
    sync/sharded_lock.rs:280-540, sync/wait_group.rs:48-148}`.
  - `crossbeam-epoch-0.9.21/src/{internal.rs:146-496, atomic.rs:1041-1339,
    sync/list.rs:130-285, sync/queue.rs:38-180}`.
  - `crossbeam-deque-0.8.8/src/deque.rs:92-108, 401-1160, 1299-1620`.
  - `crossbeam-queue-0.3.13/src/{array_queue.rs:148-378, seg_queue.rs:101-435}`.
  - `crossbeam-channel-0.5.15/src/{flavors/tick.rs:20, flavors/zero.rs:82-475,
    context.rs:94-135, select.rs:1295-1298, select_macro.rs:778-808}`.
  - `parking_lot-0.12.5/src/{raw_mutex.rs:58-308, raw_rwlock.rs:65-877,
    condvar.rs:96-390, once.rs:94-260, elision.rs:56-119}`,
    `parking_lot_core-0.9.12/src/{word_lock.rs:39-296, parking_lot.rs:175-467,
    1020-1427, thread_parker/linux.rs:58-150}`, and
    `lock_api-0.4.14/src/{rwlock.rs:2256-2295, remutex.rs:45-210}`.
  - `tokio-1.54.1/src/{sync/batch_semaphore.rs:213-781, sync/notify.rs:360-1373,
    sync/oneshot.rs:776-1582, sync/mpsc/list.rs:67-410, sync/mpsc/block.rs:188-260,
    sync/chan.rs:475-486, sync/watch.rs:221-241,935,1545,
    sync/broadcast.rs:1263-1354, sync/barrier.rs:145-175,
    util/linked_list.rs:62-105,433-450, util/ptr_expose.rs:11-74,
    runtime/task/state.rs:15-250}`.
  - `once_cell-1.21.4/src/{imp_std.rs:47-287, race.rs:68-475}`,
    `arc-swap-1.8.0/src/{lib.rs:483, debt/mod.rs:76-114, debt/helping.rs:135-333,
    debt/list.rs:113-287, strategy/hybrid.rs:46-66}`,
    `dashmap-6.2.1/src/{lib.rs:460-1230, lock.rs:28-250, iter.rs:175-265,
    util.rs:10-90}`, `rayon-core-1.13.0/src/{latch.rs:46-456, join/mod.rs:132-186,
    job.rs:116-123, registry.rs:543-842, sleep/mod.rs:170-220}`,
    `portable-atomic-1.13.1/src/{imp/x86.rs:49-74, imp/atomic128/x86_64.rs:113-255,
    imp/atomic128/aarch64.rs:44-950, imp/riscv.rs:58-265,
    imp/fallback/mod.rs:109-168, imp/fallback/seq_lock.rs:38-156,
    utils.rs:235-654}`, `atomic-waker-1.1.2/src/lib.rs:199-428`, and
    `futures-{core,util,channel}-0.3.34` (`bilock.rs:38-297`, `mutex.rs:104-384`,
    `oneshot.rs:208-235`, `mpsc/queue.rs:99-163`).
- **Programmatic hazard scan (`support/scan_crates_concurrency_hazards.py`):**
  Verified exact site counts across all 788 `.rs` files (`3,162` `unsafe`, `124`
  `asm!`, `3` `volatile`, `10` `compiler_fence`, `41` `fence()`, `636` `SeqCst`,
  `55` `transmute`, `73` strict-provenance calls).

## Revalidation

1. **Automated hazard delta scan:** Run
   `python3 support/scan_crates_concurrency_hazards.py <crate_dir>...` on newer
   unpacked crate versions to detect changes in `volatile`, `compiler_fence`,
   `asm!`, `fence()`, `transmute`, or strict-provenance site counts before
   re-auditing modified files.
2. **Targeted bug checks on crate upgrades:**
   - In `parking_lot/src/raw_rwlock.rs`, inspect `try_upgrade_until`,
     `try_upgrade_for`, `try_upgrade_slow`, and `unlock_upgradable_slow` to
     check whether `Ordering::Relaxed` has been upgraded to `Acquire` /
     `Release` and whether `force_fair || result.be_fair` checks
     `result.unparked_threads != 0`.
   - In `crossbeam-utils/src/atomic/atomic_cell.rs` and
     `crossbeam-deque/src/deque.rs`, check whether `ptr::read_volatile` /
     `write_volatile` and `can_transmute` have been replaced by chunked atomics
     or `AtomicMaybeUninit`, and in `crossbeam-epoch/src/internal.rs` check
     whether `Local::pin()` on `x86_64` emits a real `fence(SeqCst)` or inline
     `asm!` barrier.
