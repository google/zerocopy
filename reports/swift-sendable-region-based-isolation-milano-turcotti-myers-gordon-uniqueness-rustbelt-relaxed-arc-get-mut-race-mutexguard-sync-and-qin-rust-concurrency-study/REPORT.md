# Release under concurrency: Swift sendability and region isolation, Rust marker traits and scoped spawning, their soundness proofs, three standard-library incidents, RustSec marker advisories, and two Rust concurrency-bug studies

## Summary

- **Two mechanisms, one invariant.** Deployed languages keep released storage out of reach of concurrent tasks in two ways. (1) *Transfer checks*: a value crosses a task boundary only if its type is thread-safe (Swift `Sendable`, Rust `Send`/`Sync`) or it is transferred together with everything reachable from it (Swift `sending` of a disconnected region, Rust move of a `Send` value). (2) *Lifetime bounding*: a spawned task must finish before borrowed storage can be released (Swift task groups, `std::thread::scope`, `crossbeam::scope`, `rayon::scope`). A statically placed release, meaning a deallocation inserted at a program point fixed at compile time, is safe only if (2) holds for every borrow still live at that point. Basis: normative + source + derived.
- **Swift's region checker ignores release.** In `RegionAnalysis.cpp` at the pinned revision, `DestroyValueInst`, `DeallocStackInst`, `DeallocBoxInst`, `DeallocRefInst` and `EndBorrowInst` are all translated as `Ignored`. Releasing a value after sending it is therefore never diagnosed. This is consistent only because Swift releases are reference-count decrements, so protection against freeing reachable storage is dynamic. Swift's static checks police *uses* after a send, not *releases*. Basis: source + derived.
- **Rust's scoped-spawn interfaces implement join-before-return at run time.** All three wait for every child before the scope returns. They differ in how they treat panics. A leaked `std::thread::ScopedJoinHandle` turns into a scope that never returns. It does not turn into an early return. A bounded probe observed the scope still blocked 2 s after the child finished. Basis: source + execution.
- **The soundness proofs assume less than the deployed libraries need.**
  - RustBelt (POPL 2018) models only non-atomic and sequentially consistent (SC) atomic accesses, and does not handle unwinding after panics.
  - RustBelt Relaxed (POPL 2020) uses ORC11, which omits SC accesses and fences.
  - The verified libraries include `thread::spawn` and `rayon::join`. They include neither `std::thread::scope` nor `crossbeam::scope`.
  - Both papers define `Send` (resp. `Sync`) semantically: the ownership (resp. sharing) predicate does not depend on the thread identifier.
  - Basis: documentation (papers).
- **Three standard-library incidents, three mechanisms:**
  - `MutexGuard<T>: Sync` required only `T: Send`. This was a marker-implementation bug, found by verification and fixed in 3.8 days.
  - The uniqueness check behind `Arc::get_mut` used a relaxed load. This was an atomic-ordering bug, found by verification and fixed in 10.7 days.
  - `Arc::drop` kept a `&self` into storage that another thread could free. This was a bug in the lifetime of a reference during release. It was reported by a user, and was closed after 1,380.8 days by a code-generation change rather than a library change.
  - Only the third is a release-under-concurrency hazard in the strict sense. The same hazard pattern recurs in the completion signalling of lifetime-bounded spawning itself.
  - Basis: source + documentation (issue records) + derived.
- **RustSec, measured at the pinned revision:**
  - 68 non-withdrawn advisories carry the `thread-safety` category.
  - 60 of them mention `Send` or `Sync`.
  - 3 of those 60 explicitly mention use-after-free, dangling, or double free.
  - 52 of the 60 are dated 2020.
  - Basis: execution (script in `support/`).
- **Empirical studies.**
  - Qin et al. (PLDI 2020) studied 170 bugs: 70 memory-safety and 100 concurrency. Of the 70 memory-safety bugs, 30 are lifetime violations: 10 invalid free, 14 use-after-free, 6 double free. Of the 100 concurrency bugs, 59 are blocking and 41 non-blocking. 23 of the 38 shared-memory non-blocking bugs share data through unsafe code.
  - Yu, Song and Zhang (2019) studied 18 bugs. Seven of their ten deadlocks are double locks caused by implicit (scope-end) unlocking.
  - In both studies, statically placed release of a *lock guard* is a recurring cause of deadlock. In other words, static release placement harms liveness, not memory safety.
  - Basis: documentation.

## Applicability

**Subjects and their relation.** The report compares release-safety mechanisms across two languages, interpreting each implementation through its formal basis:

- Swift: proposals at `swiftlang/swift-evolution@58a97fabc7233f58af6b8a1e8d3d5a25fb4f7060` and the compiler at `swiftlang/swift@df95e655b44760b7d16a7da561cbedb3f4294fed`.
- Rust: the standard library at `rust-lang/rust@c7d5ba59d8e11ee2e2204b173458eec4cb41c973`, and two libraries, `crossbeam-rs/crossbeam@a28f40fdddb70bea8e5faf0efad9af0be4b9dbea` and `rayon-rs/rayon@599425d4a4c64714632817f48496dbc53f656a90`.
- Formal basis: Milano–Turcotti–Myers and Gordon et al. for Swift (SE-0414 states that it is "based on work from" the former). RustBelt and RustBelt Relaxed for Rust.
- The incidents are read from the public `rust-lang/rust` issue records.
- The advisories are read from `rustsec/advisory-db@f291af9b1cc0d21dfcea1709d6b037963cef262b`.
- The two studies are read from their published PDFs.

**Execution scope.**

- Rust probes ran on the nightly toolchain `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)`, commit `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, LLVM 23.1.5, target `x86_64-unknown-linux-gnu`, with its bundled Miri. That toolchain's standard library is a different revision from the library source pin above. The behaviours probed (compile-time rejections, scope join, panic propagation) were also read in the source pin. No difference between the two was observed, but none was checked line by line.
- No Swift toolchain was available. Swift behaviour is therefore stated from source and from the upstream test suite only.
- `crossbeam` and `rayon` were read, not executed.

**Version notes.**

- SE-0302 is marked "Implemented (Swift 5.7)", SE-0304 "Implemented (Swift 5.5)", and SE-0414 and SE-0430 "Implemented (Swift 6.0)". SE-0414 is behind the upcoming-feature flag `RegionBasedIsolation`.
- SE-0304's text gives `addTask` an `@Sendable` operation. At the pinned compiler revision, `stdlib/public/Concurrency/TaskGroup+addTask.swift.gyb:43` declares `operation: sending @escaping @isolated(any) () async throws -> ChildTaskResult`, so the proposal text and the implementation differ.
- `std::thread::scope` was stabilized in Rust 1.63.0 (2022-08-11), per `RELEASES.md` at the pin.

## Findings

### 1. Mechanism taxonomy at the release point

| Mechanism | What it guarantees at a release point | Enforcement | Escape hatch |
| :-- | :-- | :-- | :-- |
| Swift `Sendable` (SE-0302) | values of the type may be used concurrently without data races | conformance checking of stored properties; `@Sendable` closures capture only `Sendable` values | `@unchecked Sendable` (SE-0302 lines 239, 301) |
| Swift region isolation (SE-0414) and `sending` (SE-0430) | a non-`Sendable` value crosses a boundary only as a whole disconnected region; no use in the source domain after the send | flow-sensitive SIL dataflow (`SendNonSendable`) | `nonisolated(unsafe)` (mentioned in SE-0430 line 529); `@unchecked Sendable` |
| Swift task groups (SE-0304) | "child tasks within the task group scope must complete when the scope exits" (line 212); no reference to a child task can escape (line 361) | runtime: the group awaits children (line 358) | unstructured `Task {}` and detached tasks |
| Rust `Send`/`Sync` | `T: Send`: ownership may move across threads; `&T: Send` iff `T: Sync` (marker.rs:106) | trait solving at spawn bounds | `unsafe impl Send/Sync` |
| `std::thread::scope` | all spawned threads joined before `scope` returns; closures `F: FnOnce() -> T + Send + 'scope` | borrow checker (`'scope`) + runtime counter and park | none within safe code |
| `crossbeam::scope` | same; children joined, child panics returned as `Err` | `F: Send + 'env`; `WaitGroup` + join of all handles | none within safe code |
| `rayon::scope` | `OP`/spawned bodies complete before return; first panic re-raised | `BODY: FnOnce(&Scope<'scope>) + Send + 'scope`; `CountLatch` | none within safe code |

Basis: normative (proposals) + source.

### 2. Swift: specification and compiler implementation

**Regions (SE-0414 lines 152–220).**

- An *isolation region* is "a set of non-`Sendable` values that can only be aliased or reachable from values that are within the isolation region". It is disconnected, actor-isolated, task-isolated, or invalid.
- Merge rules for `y = f(a0, …, an)`:
  1. All regions of non-`Sendable` arguments merge after `f` executes.
  2. A non-`Sendable` `y` joins the merged region. If every argument is `Sendable`, `y` gets a fresh disconnected region.
  3. Assigning to a `var` merges the new region into the old one if the variable was captured by reference; otherwise the old region is forgotten.
- The proposal calls these rules conservative: "any `a_i` could become reachable from `a_j`".
- "An isolation region can never be accessed by multiple isolation domains at once."
- SE-0430 (lines 158–170) defines a send of a non-`Sendable` value as "a complete transfer of the value's entire region", which requires the value to be in a disconnected region.

**Implementation.** `include/swift/SILOptimizer/Utils/PartitionUtils.h:640` defines `enum class PartitionOpKind`, whose primitives include `Merge` (683), `Send` (686), `UndoSend` (690) and `Require` (693): "Require the region of a value to be non-sent". Basic blocks compile to vectors of `PartitionOp`s, and "a fixed point partition is found over the CFG". `RegionAnalysis.cpp:2108` defines `TranslationSemantics`, and lines 4134–4150 list the instructions that are `Ignored`:

```text
// These instructions are ignored because they cannot affect the region that a
// value is within or because even though they are technically a use we would
// rather emit an error on a better instruction.
CONSTANT_TRANSLATION(DeallocBoxInst, Ignored)
CONSTANT_TRANSLATION(DeallocRefInst, Ignored)
CONSTANT_TRANSLATION(DeallocStackInst, Ignored)
CONSTANT_TRANSLATION(DestroyValueInst, Ignored)
CONSTANT_TRANSLATION(EndBorrowInst, Ignored)
CONSTANT_TRANSLATION(EndLifetimeInst, Ignored)
```

**Consequence (derived).** Release-like SIL instructions never generate `Require`, so "release after send" is outside what the checker diagnoses. This is sound for reference types only because release is a reference-count decrement, and storage is freed when the count reaches zero, not at the static release point. The compiler has a hidden frontend flag `-assume-single-threaded` (`include/swift/Option/FrontendOptions.td:1303–1306`, help text "Assume that code will be executed in a single-threaded environment"). This indicates that default code generation does not assume single-threaded execution. The atomicity of the runtime retain/release entry points was not examined. Swift has no analogue of a statically placed free of shared storage that the region checker would need to order after the last concurrent use.

**Diagnostics.** `SendNonSendable.cpp` (5,783 lines) contains `class SendNonSendableImpl` (line 1806) and the pass `SendNonSendable` (5760). The most frequently referenced diagnostic identifiers are `regionbasedisolation_named_send_yields_race` (6 sites) and `regionbasedisolation_type_send_yields_race` (5). `regionbasedisolation_named_value_used_after_explicit_sending` is emitted at line 2183. The upstream test `test/Concurrency/transfernonsendable.swift` (2,429 lines, 365 `expected-` annotations) encodes the user-visible text. Lines 161–169:

```text
await a.useKlass(ns0)
// expected-warning @-2 {{sending 'ns0' risks causing data races}}
// expected-note @-3 {{sending 'ns0' to actor-isolated instance method 'useKlass' risks causing data races between actor-isolated and local nonisolated uses}}
...
    closure() // expected-note {{access can happen concurrently}}
```

Basis: source (compiler and tests); no Swift execution.

### 3. Formal basis of region isolation

**Milano, Turcotti, Myers (PLDI 2022).**

- A thread's *reservation* is the part of the heap it may access. The goal is that reservations stay disjoint. Regions are "a purely compile-time construct which groups objects that enter or leave a thread's reservation as a unit".
- Inter-region references are stored in `iso` fields. A *focus* mechanism prevents conflicting tracking of aliases. The dynamic primitive `if disconnected(x, y)` decides at run time whether a region can be split. The proposed implementation uses a reference count over non-`iso` heap references that is updated only on field assignment.
- Results: Theorem 6.1 (Progress) and Theorem 6.2 (Preservation) over "sound configurations". The paper states "A formal paper proof of soundness that shows well typed programs have no destructive data races", and a type checker "implemented in OCaml, and verified in Coq".
- No statement about deallocation or about relaxed memory was found in the text examined.

**Gordon, Parkinson, Parsons, Bromfield, Duffy (OOPSLA 2012).**

- Permission qualifiers (writable, readable, immutable, isolated). Recovery rules T-RECOVISO and T-RECOVIMM restore isolation or immutability "without any explicit alias tracking".
- Two parallel rules: T-PAR (`NoWrit(Γ1) NoWrit(Γ2)` ⊢ `C1||C2`) and T-ASYNC (`IsoOrImm(Γ1)`).
- Soundness is proved by embedding into the Views framework.
- The C# variant is used by a Microsoft team that "has written several million lines of code".
- The paper records a lifetime-bounding precondition directly: "T-PAR is not used for asynchronous tasks because it is unsound: recovery (T-RECOVISO and T-RECOVIMM) is not valid if a shared readable reference to mutable data can live arbitrarily long after the 'recovery block' in an asynchronous task. Thus T-PAR is used only for applicable static constructs such as parallel for loops."

**Correspondence (derived).**

| Implemented Swift rule | Calculus counterpart | Gap |
| :-- | :-- | :-- |
| conservative merge on every call (SE-0414 rules 1–3) | region merge on aliasing | Swift has no `iso` fields or focus, so it merges more often |
| `sending` = disconnected region transfer | moving a dominating reference out of a reservation | none at this level |
| no `if disconnected` | dynamic split primitive | Swift cannot split a merged region at run time; the proposal lists a "disconnect operator" only as a future direction (SE-0414 "Disconnected Fields and the Disconnect Operator") |
| release ignored | calculus has no explicit free | both rely on non-static reclamation |
| `@unchecked Sendable`, `nonisolated(unsafe)` | no counterpart | outside any proof |

### 4. Rust: marker traits and three scoped-spawn interfaces

**Marker traits (`library/core/src/marker.rs`).**

- `pub unsafe auto trait Send` (line 93), with `impl<T: PointeeSized> !Send for *const T {}` (98) and `unsafe impl<T: Sync + PointeeSized> Send for &T {}` (106).
- `pub unsafe auto trait Sync` (658), with `!Sync` for raw pointers (673, 675).

**`std::thread::scope`** (`library/std/src/thread/scoped.rs`, 358 lines):

- `spawn` requires `F: FnOnce() -> T + Send + 'scope, T: Send + 'scope` (201–204).
- `scope` (141–174) runs `f` under `catch_unwind`, then executes `while scope.data.num_running_threads.load(Ordering::Acquire) != 0 { … park() }`, then re-raises `f`'s panic or panics with `"a scoped thread panicked"` if any unjoined child panicked.
- The decrement lives in `Packet::drop` (`lifecycle.rs:175–205`). It runs "only after the `result` has been dropped, since dropping it might still use things it borrowed from 'scope" (200–202).
- `ScopeData` sits in an `Arc` "so that other threads can finish their `decrement_num_running_threads` even after this function returns" (145–146). This is exactly the release-under-concurrency pattern of Finding 6, incident C.
- The increment guards overflow "to make sure there's no chance it overflows to 0, which would result in unsoundness … This can only reasonably happen by mem::forget()'ing a lot of ScopedJoinHandles" (49–52).

**`crossbeam::scope`** (`crossbeam-utils/src/thread.rs`, 627 lines):

- `scope` (146–203) returns `thread::Result<R>`.
- If unwinding begins before all children are joined, an `AbortOnPanic` guard calls `std::process::abort()`: "promote it to an aborting panic to prevent any threads from escaping the scope" (169–171).
- It waits on a `WaitGroup` (174–175), joins every remaining handle, and returns child panics as `Err(Box::new(panics))` (199).
- `spawn` requires `F: Send + 'env, T: Send + 'env` (258–262).
- The `'env` bound is erased with `unsafe { mem::transmute(closure) }` to `Box<dyn FnOnce() + Send + 'static>` (458–460).

**`rayon::scope`** (`rayon-core/src/scope/mod.rs`, 885 lines):

- `scope` requires `OP: FnOnce(&Scope<'scope>) -> R + Send` (306–308), and `spawn` requires `BODY: FnOnce(&Scope<'scope>) + Send + 'scope` (566–568).
- `complete` runs the body, `job_completed_latch.wait(owner)`, then `maybe_propagate_panic()` (696–704). Only the first panic is kept, by `compare_exchange` (735–757).
- Job completion calls `Latch::set(&(*this).job_completed_latch)` through a raw `*const Self` (718–731).

| Property | std | crossbeam | rayon |
| :-- | :-- | :-- | :-- |
| child closure bound | `Send + 'scope` | `Send + 'env` | `Send + 'scope` |
| join mechanism | atomic counter + park | `WaitGroup` + `join()` | `CountLatch` |
| child panic | `scope` panics `"a scoped thread panicked"` | `scope` returns `Err(panics)` | first panic re-raised |
| unwinding before join | caught; waits, then resumes | abort | caught; waits |
| leaked join handle | scope blocks forever (probe P5) | not examined | no per-spawn handle |

Basis: source + execution (std only).

### 5. What the semantic soundness proofs assume

**RustBelt (Jung, Jourdan, Krebbers, Dreyer; DOI 10.1145/3158154).**

- "We then define T to be Send if T's ownership predicate does not depend on the thread id parameter (and Sync if T's sharing predicate does not depend on the thread id parameter)."
- λRust adopts "a simplified memory model featuring only non-atomic and sequentially consistent atomic operations".
- Footnote 10: "we are not handling unwinding after panics, and all atomic memory operations are sequentially consistent, while Rust's standard library uses weaker atomic accesses."
- Libraries verified: "Arc, Rc, Cell, RefCell, Mutex, RwLock, mem::swap, thread::spawn, rayon::join, and take_mut".
- The paper reports uncovering a standard-library bug "[Jung 2017]", which is the `MutexGuard` incident below.

**RustBelt Relaxed (Dang, Jourdan, Kaiser, Dreyer; DOI 10.1145/3371102).**

- Built on ORC11, an operational C11 fragment with a race detector for non-atomics: "ORC11 omits SC accesses and fences because (1) they are not used by any of the libraries verified in RustBelt, and (2) it is still an open question how to develop a separation logic for reasoning about SC accesses in a relaxed-memory setting."
- Re-verified `thread::spawn`, `rayon::join`, `Mutex`, `RwLock` and the full `Arc`/`Weak`. The sequential libraries "remain largely unchanged".
- Introduces *synchronized ghost state* for reclamation under relaxed memory.
- Reports finding the `Arc` data race (§5.3). Its Fig. 10 gives the corrected `is_unique` as `CASacq(a.weak, 1, −1)` followed by `∗acq a.strong == 1`.

**Coverage gaps (derived).** Neither proof covers:

- `std::thread::scope` (stabilized 2022, after both papers), or `crossbeam::scope`;
- unwinding, which all three scoped interfaces handle in different ways;
- SC atomics (RBrlx);
- the `dereferenceable` attribute contract on reference arguments that made incident C undefined behaviour.

The `rayon::join` proof is the only verified lifetime-bounded spawn interface.

### 6. Incidents: release or invalidation under concurrency

| | A: `MutexGuard<Cell<i32>>` was `Sync` | B: `Arc::get_mut` insufficient synchronization | C: `Arc::drop` dangling `&self` |
| :-- | :-- | :-- | :-- |
| Issue | rust-lang/rust #41622, 2017-04-29 | #51780, 2018-06-25 | #55005, 2018-10-12 |
| Mechanism that failed | marker implementation: `Sync` required `T: Send` instead of `T: Sync` | atomic ordering: relaxed read of the strong count in `is_unique` | lifetime of a reference during release: `&self` of `AtomicUsize::fetch_sub` outlives the decrement that lets another thread free the `ArcInner` |
| Found by | verification (RustBelt; report by GitHub user RalfJung) | verification (RustBelt Relaxed §5.3; report by GitHub user jhjourdan) | user report on the Rust internals forum, filed by RalfJung; Miri reproductions posted 2022-06 |
| Fix | PR #41624, merged 2017-05-03 (3.8 days) | PR #52031 "Strenghten synchronization in `Arc::is_unique`", merged 2018-07-06 (10.7 days) | PR #98017 "do not mark interior mutable shared refs as dereferenceable", merged 2022-07-23; issue closed 2022-07-24 (1,380.8 days) |
| Release involved? | no: race on `Cell` contents | no free; exclusive access granted early | yes |
| Static release affected? | indirectly: a wrong marker breaks the premise "no other thread holds access" | no: dynamic ownership decision; the static analogue is release after a join, where the join supplies happens-before | yes: any protocol "signal done, then the other side frees" must not keep even a dormant reference past the signal |

**Lines at the pinned revision, showing the fixed state.**

- `library/std/src/sync/poison/mutex.rs:292` `impl<T: ?Sized> !Send for MutexGuard<'_, T> {}`, and `:297` `unsafe impl<T: ?Sized + Sync> Sync for MutexGuard<'_, T> {}`.
- `library/alloc/src/rcs/arc.rs:2937` `if this.inner().weak.compare_exchange(1, usize::MAX, Acquire, Relaxed).is_ok() {`, then `:2941` `let unique = this.inner().strong.load(Acquire) == 1;` and `:2946` `this.inner().weak.store(1, Release);`.
- `Arc::drop` (2982–3018) still begins `if self.inner().strong.fetch_sub(1, Release) != 1 { return; }` (2986) and fences with `acquire!(self.inner().strong)` (3018).

Incident C's fix was therefore a change to the language/code-generation contract, not to `Arc`.

**Issue text (historical code).**

- #41622: "`MutexGuard<T>` implements `Sync` whenever `T` implements `Send`, which is plain wrong."
- #51780: "`Arc::get_mut` only uses a relaxed read of the strong counter (via `is_unique`)."
- #55005 quotes `pub fn fetch_sub(&self, …) { unsafe { atomic_sub(self.v.get(), val, order) } // HERE }`, and explains that at HERE "the `&self` still points to the strong reference count in the `ArcInner` -- so `&self` dangles".

**Recurrence in lifetime-bounded spawning.** The #55005 timeline cross-references:

- rayon PR #934 "Fix a use-after-free race in SpinLatch::set, and release 1.9.3" (merged 2022-05-13);
- rayon PR #1011 "Use pointers instead of `&self` in `Latch::set`" (merged 2023-01-21);
- crossbeam issue #545 "epoch: Miri reports SB violation", about which the issue thread says crossbeam "has a similar bug".

The current rayon scope still passes `this: *const Self` into `execute_job_closure` and `Latch::set` (scope/mod.rs:718–731). std keeps `ScopeData` alive with an `Arc` (scoped.rs:145–146).

Derived lesson: the join that makes static release safe is itself a release-under-concurrency protocol. After the child's final signal, the parent may free the frame that holds the latch or counter. The child must touch nothing in that frame after the signalling store.

### 7. RustSec advisories for thread-safety marker implementations

**Query** (`support/count_rustsec_marker_advisories.py`, run on `rustsec/advisory-db@f291af9…`): parse the leading TOML block of every `crates/*/RUSTSEC-*.md`, and exclude `withdrawn` advisories (25 of 1,535 parsed).

| Class | Definition | Count |
| :-- | :-- | --: |
| A | `categories` contains `thread-safety` | 68 |
| B | A ∧ title/body/keywords mention `Send` or `Sync` as a word | 60 |
| C | B ∧ (`memory-corruption` category ∨ use-after-free/dangling/double-free text) | 51 |
| D | B ∧ explicit use-after-free/dangling/double-free text | 3 |

By year: A = {2020: 53, 2021: 3, 2022: 2, 2023: 2, 2026: 8}, and B = {2020: 52, 2021: 2, 2022: 1, 2023: 1, 2026: 4}.

The three D advisories:

- RUSTSEC-2020-0044 (`atom`): an unsound `Send` "potentially leading to use-after-free issues through memory races".
- RUSTSEC-2026-0242 (`dcrypt-api`): "concurrent replacement or clearing could free a value while another thread cloned it".
- RUSTSEC-2026-0454 (`surrealdb-core` via `reblessive`): unconditional `unsafe impl Send/Sync` allowing "Data race and double free".

Typical B titles are "lacks bound on its Send and Sync traits" or "unconditionally implements Send/Sync". That is the same mechanism as incident A, in third-party code.

Classification (derived): all B advisories defeat transfer checks (mechanism 1). None reports a failure of lifetime bounding (mechanism 2). The keyword classes are heuristic; the full B list is preserved in `support/rustsec_counts.txt` for manual audit.

### 8. Empirical concurrency-bug studies

**Qin, Chen, Yu, Song, Zhang (PLDI 2020; DOI 10.1145/3385412.3386036).**

- Corpus: 850 unsafe usages and 170 bugs (70 memory-safety, 100 concurrency) from five applications, five libraries, CVE/RustSec, and the standard library. 145 of the 170 were fixed after 2016.
- Table 2, memory bugs:
  - Wrong access: buffer overflow 21, null dereference 12, uninitialized read 7.
  - Lifetime violation: invalid free 10, use-after-free 14, double free 6.
  - By propagation: safe 1, unsafe 23, safe→unsafe 31, unsafe→safe 15.
  - Insight 4 states "All memory-safety issues involve unsafe code". Table 2 nevertheless lists one bug in the "safe" row. The paper's explanation for this was not found in the text examined.
- Table 3, the 59 blocking bugs: Mutex and RwLock 38, Condvar 10, Channel 6, Once 1, other 4. Insight 6: "Lacking good understanding in Rust's lifetime rules is a common cause for many blocking bugs." The paper also states that automatic unlock "can cause bugs when programmers have some misunderstanding of lifetime".
- The 41 non-blocking bugs:
  - 3 are message-passing bugs.
  - 38 are shared-memory bugs (Table 4). 23 share data through unsafe or interior-unsafe code: global 3, raw pointer 12, `Sync` implementation 3, OS/hardware 5. 15 share through safe code: atomic 5, `Mutex` 10.
  - 13 involve interior mutability.
  - Fixes: 20 enforce atomicity, 10 enforce ordering, 5 avoid sharing, 1 makes a local copy, 2 change application logic.
- The authors built two static detectors, for use-after-free and double lock, which found ten previously unknown bugs.

**Yu, Song, Zhang (arXiv:1902.01906v1).** The corpus is 18 bugs from Servo, TiKV and Rand.

- Deadlocks: 10. Seven are double locks; "due to implicit unlock in Rust, double locks are the root causes for seven deadlocks". Three are channel cycles.
- Data races: 8, of which 3 are in safe code and 5 in unsafe code.

**Category against mechanism (derived).**

| Category (source) | Count | Would statically placed release be affected? | Excluded by |
| :-- | --: | :-- | :-- |
| Lifetime violation in memory bugs (Qin T2) | 30 | yes: wrong release point or double release | borrow checker + `Send`/`Sync`, for safe code only; every case involves unsafe code |
| Double lock via scope-end unlock (Qin T3 subset; Yu 7/10) | Qin: not separately counted; Yu: 7 | yes, for liveness: the release is placed too late | neither mechanism; requires earlier or explicit release |
| Shared via raw pointer or manual `Sync` (Qin T4) | 15 | yes, if the shared storage is released while still referenced | defeats both mechanisms (unsafe escape hatch) |
| Shared via `Mutex` or atomic, logic race (Qin T4) | 15 | no: no release involved | not a memory-safety property |
| Data race in safe code (Yu) | 3 | not determinable from the text examined | n/a |

### 9. Probes

Source: `support/probes/`, run by `run_probes.sh`, sequentially, pinned to 8 CPUs with `taskset`, with a 60 s `timeout`, and GNU `time` for peak RSS. Basis: execution, real toolchain; P7 is a toy model.

| Probe | Program | Result |
| :-- | :-- | :-- |
| P1 | `drop(v)` inside `thread::scope` while a child borrows `v` | rejected: `E0373` + `E0505 cannot move out of 'v' because it is borrowed` |
| P1b | same, with `drop(v)` after the scope | accepted; prints `3` |
| P2 | `thread::spawn` borrowing a local | rejected: `E0373 closure may outlive the current function` |
| P3 | `Rc` clone moved into a scoped child | rejected: `E0277 Rc<u32> cannot be sent between threads safely` |
| P4 | `assert_sync::<MutexGuard<'static, Cell<i32>>>()` | rejected: `E0277 Cell<i32> cannot be shared between threads safely` (fix for incident A present) |
| P5 | `mem::forget` a `ScopedJoinHandle`; watchdog after 2.3 s | child prints `finished`; watchdog fires: `scope() still blocked ~2 s after the child finished`; exit 3 |
| P6 | child panics inside `scope`, caught by `catch_unwind` | `scope() panicked with: Some("a scoped thread panicked")` |
| P7 (toy model, not `Arc`) | writer does a non-atomic write then `fetch_sub(Release)`; reader spins on `load(ORDER) == 1` then writes, under Miri with `-Zmiri-many-seeds=0..32` | `ORDER = Acquire`: 0 of 32 seeds report a race. `ORDER = Relaxed`: 31 of 32 seeds report `Data race detected between (1) non-atomic write … and (2) non-atomic read`; 1 seed completes without report |

The P5 mechanism, from source: the `Arc<Packet>` held by the forgotten handle is never dropped, so `decrement_num_running_threads` never runs. A leak therefore becomes non-termination rather than unsoundness. P7 demonstrates only that Miri detects the synchronization pattern of incident B in a 30-line reimplementation.

### 10. Performance and resource footprint (L1–L6)

| Level | Quantity | Value | Basis |
| :-- | :-- | :-- | :-- |
| L1 authoring | implementation size, Swift region checker | `RegionAnalysis.cpp` 5,341 lines; `SendNonSendable.cpp` 5,783; `PartitionUtils.h` 2,856; `RegionAnalysis.h` 687 | measured (`wc -l`) |
| L1 | implementation size, scoped spawn | std `scoped.rs` 358; crossbeam `thread.rs` 627; rayon `scope/mod.rs` 885 | measured |
| L1 | industrial use of a uniqueness/immutability system | "several million lines of code" | cited (Gordon et al.) |
| L1 | repair latency of incidents | 3.8 d, 10.7 d, 1,380.8 d | derived from issue and PR timestamps |
| L1 | proof effort, RustBelt/RBrlx | not measured | — |
| L2 | build time of rustc, swiftc, or the Coq proofs | not measured | — |
| L3 | rustc time and peak RSS for the probe files | 0.03–0.11 s wall; 101–137 MB peak RSS (8 CPUs) | measured |
| L3 | Swift region analysis time | not measured (no toolchain) | — |
| L3 | Milano et al. checker | "capable of checking our most complex examples in seconds" | cited |
| L4 | runtime cost of `std::thread::scope` | one `Arc<ScopeData>` allocation per scope; one atomic increment and decrement per child; park/unpark of the owner | source (counted); time not measured |
| L4 | runtime cost of Swift region checks | none at run time (compile-time pass) | derived |
| L5 | Miri check of P7, 32 seeds | 0.16–0.52 s wall | measured |
| L5 | Coq replay of RustBelt/RBrlx | not measured | — |
| L6 | peak RSS, Miri P7 runs | 187–193 MB | measured |
| L6 | binary size and runtime memory of scoped interfaces | not measured | — |

### 11. Human comprehensibility and conceptual simplicity (C1, C2)

**C1, comprehensibility.**

- Swift asks a programmer to hold about eight interacting concepts: `Sendable`, `@Sendable`, four region kinds, `sending`, `inout sending`, and two unchecked escape hatches. Region merging is nonlocal, since any call merges argument regions (SE-0414 rule 1).
- Swift diagnostics pair a send site with "access can happen concurrently" notes (upstream test). That is legible, but it explains a merge history the user never wrote down.
- Rust's scoped-spawn errors are local: `E0373`, `E0505` and `E0277`, each with a "required by a bound" note pointing at `scoped.rs:203` (probe stderr).
- The empirical studies show where mental models fail: implicit lock release at scope end (Qin Insight 6; Yu, 7 of 10 deadlocks).
- None of the studies measures comprehension of Swift regions. That is not examined.

**C2, simplicity.**

- Both languages enforce one invariant ("no concurrent access survives a release") with two mechanisms: transfer checks and lifetime bounding.
- Gordon et al. show that the two do not compose freely: recovery is unsound without bounded lifetimes (T-PAR versus asynchronous tasks).
- A minimal unifying abstraction (derived) is a *scoped capability*: a borrow token whose lifetime cannot cross the join that precedes a release. Transfer of a disconnected region is then the special case in which the token is surrendered at the send.
- This reading does not hide complexity in an adapter. It does move the burden onto the join protocol, which incident C and the rayon and crossbeam fixes show is itself fragile.

### 12. Validation of implementations (V1–V4)

| Axis | Evidence | Status |
| :-- | :-- | :-- |
| V1 specification adequacy | Swift upstream diagnostic tests (365 annotations in one file); RustSec advisories falsify third-party marker contracts after release; RustBelt verification falsified a standard-library marker (incident A) | source/documentation; mutation testing of the region checker not examined |
| V2 checker soundness fuzzing | — | not examined for either compiler |
| V3 concurrency validation | Miri race detection (P7 toy model; Miri reproductions of incident C reported in #55005); ORC11 race detector in RBrlx | execution (toy) + documentation; Loom and GenMC not examined |
| V4 human mental models | Qin Insight 6 and Suggestion 6 (IDE highlighting of implicit unlock); Yu double-lock analysis | documentation |

## Boundaries

- **Not examined.**
  - Executing Swift diagnostics (no Swift toolchain).
  - Swift runtime atomicity of retain/release.
  - `async let` and actor-isolated region details beyond the cited proposal sections.
  - Executing `crossbeam` and `rayon` scopes.
  - The leaked-handle behaviour of crossbeam.
  - Coq replay of RustBelt and RustBelt Relaxed.
  - Whether Milano et al.'s Coq artifact covers the type checker only or also soundness (the paper calls the soundness proof a "paper proof").
  - The history of the removed pre-1.0 `thread::scoped` guard API.
- **Unknown.**
  - Whether any Qin et al. use-after-free crossed threads. The table does not split this out.
  - Whether the toolchain standard library used for probes differs from the library source pin in the probed functions.
- **Known not to apply.** The P7 result is a property of a toy reimplementation and of Miri, not of `Arc` at any revision. Its 0-of-32 Acquire result is bounded search, not proof.
- **Unsupported claims to avoid.**
  - "Swift regions prevent release-after-send." Release is ignored by design.
  - "RustBelt proves `std::thread::scope` sound." It is not among the verified libraries.
  - "RustSec counts measure prevalence." They count reported advisories, and 52 of 60 in class B come from one year.
  - "Incident C was an `Arc` bug." It was closed by a code-generation contract change.
- **Heuristic classification.** Classes B–D are keyword filters over advisory text. Some B entries may concern `Send`/`Sync` only incidentally. The list is preserved for audit.

## Evidence

All repository evidence was observed on 2026-11-21 (UTC).

- **Swift Evolution** `swiftlang/swift-evolution@58a97fabc7233f58af6b8a1e8d3d5a25fb4f7060`:
  - `proposals/0302-concurrent-value-and-concurrent-closures.md` (lines 239, 301);
  - `proposals/0304-structured-concurrency.md` (212, 358, 361);
  - `proposals/0414-region-based-isolation.md` (152–220, 383–420, 2038);
  - `proposals/0430-transferring-parameters-and-results.md` (158–200, 529).
- **Swift compiler** `swiftlang/swift@df95e655b44760b7d16a7da561cbedb3f4294fed`:
  - `include/swift/SILOptimizer/Utils/PartitionUtils.h:640–693`;
  - `lib/SILOptimizer/Analysis/RegionAnalysis.cpp:2108–2160, 4134–4150`;
  - `lib/SILOptimizer/Mandatory/SendNonSendable.cpp:1806, 2183, 5748, 5760`;
  - `stdlib/public/Concurrency/TaskGroup+addTask.swift.gyb:43`;
  - `include/swift/Option/FrontendOptions.td:1303–1306`;
  - `test/Concurrency/transfernonsendable.swift:150–170`.
- **Rust standard library** `rust-lang/rust@c7d5ba59d8e11ee2e2204b173458eec4cb41c973`:
  - `library/core/src/marker.rs:93–106, 658–675`;
  - `library/std/src/thread/scoped.rs:16–69, 141–174, 201–204`;
  - `library/std/src/thread/lifecycle.rs:56–80, 163–205`;
  - `library/alloc/src/rcs/arc.rs:278–280, 2784–2795, 2929–2950, 2982–3018`;
  - `library/std/src/sync/poison/mutex.rs:238, 257, 292, 297`;
  - `RELEASES.md` (Version 1.63.0 lists `thread::scope`).
- **crossbeam** `crossbeam-rs/crossbeam@a28f40fdddb70bea8e5faf0efad9af0be4b9dbea`: `crossbeam-utils/src/thread.rs:146–203, 217, 258–262, 458–460`.
- **rayon** `rayon-rs/rayon@599425d4a4c64714632817f48496dbc53f656a90`: `rayon-core/src/scope/mod.rs:306–308, 566–568, 696–768`.
- **RustSec** `rustsec/advisory-db@f291af9b1cc0d21dfcea1709d6b037963cef262b`: `crates/`, `EXAMPLE_ADVISORY.md`. Script and full output in `support/`.
- **Issue and PR records** (GitHub REST API, read-only):
  - rust-lang/rust issues #41622, #51780, #55005, including the timeline of #55005;
  - rust-lang/rust PRs #41624, #52031, #98017;
  - rayon-rs/rayon PRs #934, #1011;
  - crossbeam-rs/crossbeam issue #545.
- **Literature.** DOIs were verified against Crossref metadata for title, authors and venue:
  - 10.1145/3519939.3523443 (Milano, Turcotti, Myers, PLDI 2022, pp. 458–473);
  - 10.1145/2384616.2384619 (Gordon, Parkinson, Parsons, Bromfield, Duffy, OOPSLA 2012, pp. 21–40);
  - 10.1145/3158154 (Jung, Jourdan, Krebbers, Dreyer, PACMPL 2(POPL); Crossref issue date 2017-12-27);
  - 10.1145/3371102 (Dang, Jourdan, Kaiser, Dreyer, PACMPL 4(POPL); Crossref date 2019-12-20);
  - 10.1145/3385412.3386036 (Qin, Chen, Yu, Song, Zhang, PLDI 2020, pp. 763–779);
  - arXiv:1902.01906v1 (Yu, Song, Zhang, 5 Feb 2019), verified against the arXiv PDF header.

  Quotations come from the authors' or publisher-hosted PDFs as text-extracted on the observation date.
- **Execution.**
  - Environment: `support/ENV.txt`.
  - Probe sources: `support/probes/`.
  - Raw outputs: `support/probe_output/`, with absolute paths replaced by `$TOOLCHAIN`, `$MIRI_SYSROOT`, `probes`, `out`.

## Revalidation

- **Swift release handling.** At a new revision, grep `RegionAnalysis.cpp` for `CONSTANT_TRANSLATION(DestroyValueInst` and `DeallocStackInst`. If either stops being `Ignored`, Finding 2's consequence changes.
- **Swift `addTask` signature.** Re-read `TaskGroup+addTask.swift.gyb` to recheck the `sending` versus `@Sendable` difference.
- **Rust scope semantics.** Rerun `support/probes/run_probes.sh probes out [miri-sysroot]` (about 5 s total). P5 must still exit 3 with the watchdog line. If it prints `after scope`, the leaked-handle behaviour changed. Also diff `scoped.rs:141–174` and `lifecycle.rs:175–205`.
- **Incident fixes.** Check `mutex.rs` for `Sync + ?Sized` on `MutexGuard`, and `arc.rs` `is_unique` for `strong.load(Acquire)`.
- **RustSec counts.** Rerun `python3 support/count_rustsec_marker_advisories.py <advisory-db checkout>` at the new revision and diff against `support/rustsec_counts.txt`.
- **Proof coverage.** Search the RustBelt artifacts (not examined here) for `scope` to see whether newer mechanizations cover `std::thread::scope` or unwinding.
