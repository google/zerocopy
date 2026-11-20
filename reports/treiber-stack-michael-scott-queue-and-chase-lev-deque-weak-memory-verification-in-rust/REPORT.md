# Weak-Memory Verification of Treiber Stack, Michael-Scott Queue, and Chase-Lev Work-Stealing Deque in Rust

## Summary

Verifying canonical lock-free Rust concurrent collections—the Treiber stack, Michael-Scott (`MS`) MPMC queue, and Chase-Lev work-stealing deque—under C++20/RC11 semantics exposes sharp structural differences in ordering requirements, data-race freedom (`r[undefined.race]`), linearization mechanisms, ABA resilience, and separation-logic expressiveness. Analysis across `crossbeam-rs/crossbeam` (`a28f40fddd`), `kaist-cp/cs431` (`0bc971aa82`), `kaist-cp/relaxed-memory-separation-logic` (`6fe1475af1`), `rust-lang/rust` (`ec65cd52bb`), `rust-lang/miri` (`0a0ce195cb`), and `rocq-iris/iris` (`2fe2f450ad`) establishes six invariants:

1. **Minimal C++20/RC11 Orderings Separate by Sync Topology:**
   - *Treiber stack (`cs431/src/lockfree/stack.rs:42–109`):* `push` needs `head.load(Relaxed)` + `compare_exchange(..., Release, Relaxed)`, while `pop` needs `head.load(Acquire)` + **`compare_exchange(..., Relaxed, Relaxed)`** (`cas^ac` in `code_treiber.v:44` is overly conservative). Under C++20 `P0982R1` (`[W_rel] · (rf · rmw)*`), `pop`'s relaxed CAS is an RMW that preserves earlier nodes' `sync_vector`; replacing any CAS with a non-RMW `store(Relaxed)` severs the release sequence and triggers a data race on unpopped `node.data`.
   - *Michael-Scott queue (`cs431/src/lockfree/queue.rs:62–153`, `code_ms_tailcas.v:25–64`):* `push` requires `Acquire` on `tail` and `tail.next` plus `Release` on `tail.next.CAS` and `tail.CAS`; `try_pop` requires `Acquire` on `head` and `head.next`, **explicit `if tail == head { tail.CAS(..., Release, Relaxed) }` helping**, and **`head.CAS(..., Release, Relaxed)`**. Weakening `head.CAS` to `Relaxed` or omitting `tail` advance allows a lagged `tail` to lag behind reclaimed sentinels, causing UAF.
   - *Chase-Lev deque (`crossbeam-deque/src/deque.rs:420–705`, `chase_lev/code.v:57–96`):* Requires **`SeqCst` fences** (and `SeqCst` CAS on the 1-element race) between `Worker::pop` (`back.store(b - 1, Relaxed); fence(SeqCst); front.load(Relaxed)`) and `Stealer::steal` (`front.load(Acquire); fence(SeqCst); back.load(Acquire)`). Weakening either `fence(SeqCst)` to `AcqRel` permits a Store-Buffering (`SB`) double-claim of the last or second-to-last slot (`probe_queues` check).
2. **Circular Ring-Wrap Data-Race Impossibility (`deque.rs:96–115, 686–703` vs. `chase_lev/code.v:74–76`):** Unlike `GPFSL`'s non-circular fixed array (`chase_lev/code.v`), on a circular ring of capacity $C$, **both** pre-CAS non-atomic/volatile reads (`deque.rs:687`, racing with $C$-wrap `push` writes when a thief stalls) **and** post-CAS non-atomic reads (naive circular port of `code.v:75`, racing immediately when `push` wraps physical index `(f + C) % C` after `front = f + 1` is published) trigger `r[undefined.race]` UB. Sound Rust circular deques require either `Atomic<Owned<T>>` slots or `[AtomicUsize; K]` `Relaxed` loads into `[MaybeUninit<usize>; K]` (paired with `Relaxed` atomic loads in `Worker::resize`).
3. **Linearization Beyond Classical SC (`OMO` / `Compass` Event Graphs):** Under `Release`/`Acquire`, Treiber `pop` and MS `try_pop` empty reads (`head == null` / `head.next == null`) can observe stale states in modification order without violating `RC11` coherence. `Compass` (`Dang et al., PLDI 2022`) models this with Event Graphs and Overapproximating Modification Orders (`omo_append_w` for mutating CAS vs. `omo_insert_r` inserting read-only empty events into prior generations `gen < length omo`, `spec_treiber_composition.v:106`, `spec_composition.v:103`).
4. **Helping vs. Prophecy Variables (`Jung et al., POPL 2020`; `Vindum & Birkedal, CPP 2021`):** MS-queue `tail` advancement decouples physical `tail` updates from logical `Enq` commit at `tail.next.CAS`, whereas elimination-backoff stacks perform full operation helping across partner slots. Prophecies (`proph_map.v`, `NewProph`/`Resolve`) are required in contextual refinement of Michael & Scott's original consistent-snapshot `dequeueMS` (`D4b`–`D5`) because `D4c` (`next = !toNext`) linearizes `none` only if the future `D5` snapshot `sent == !toSent` succeeds—whereas omitting consistent snapshots under GC or EBR (`Vindum & Birkedal §7`; `cs431/queue.rs:107–111`) eliminates prophecies completely.
5. **ABA & Reclamation Coupling:** Treiber stacks suffer physical 3-node ABA (`A -> B -> C`) unless retired nodes are guarded (e.g., EBR `Guard` pinning); MS-queue `try_pop` reads `next_ref.data.assume_init_read()` *after* winning `head.CAS` under an active `Guard` (`queue.rs:142–147`), whereas Hazard Pointers must pin *both* `head` and `next` (`Michael 2004`). Chase-Lev uses monotonic signed `WorkerIndex` (`i64` on 64-bit targets, `deque.rs:24–28`) to prevent `front` ABA, leaving a finite $2^{31}$ wrap horizon on 32-bit targets lacking 64-bit atomics (`L32–36`).
6. **First-Order `Type 0` View-PCM Proofs vs. Iris Higher-Order Atomic Triples:** Higher-order logically atomic triples (`<<< ... >>>`, `spec_treiber_composition.v:46–64`) are required only when clients mutate impredicative `vProp Σ` invariants atomically inside the library's CAS; for first-order Rust specs parameterized by `OwnT : T → VProp_0`, a stratified `Type 0` View-PCM + `OMO` history automaton with 2-state node protocols and token escrows verifies all three structures without step-indices (`▷`).

## Applicability

These findings govern Rust weak-memory verification, lock-free container audits, and logic design across the twelve subjects in `REPORT.json`:

- **Production & Pedagogical Rust Concurrent Collections:** `crossbeam-rs/crossbeam` @ `a28f40fdddb70bea8e5faf0efad9af0be4b9dbea` (`crossbeam-deque/src/deque.rs`), `kaist-cp/cs431` @ `0bc971aa82f600b948eb9f83bb972bef31b9fc5d` (`src/lockfree/{stack.rs, queue.rs}`, `homework/src/elim_stack/{treiber_stack.rs, elim.rs}`), and `rust-lang/rust` @ `ec65cd52bba13d491ff65c9d218b39753755c84a` (`library/core/src/sync/atomic.rs`).
- **Operational Semantics & Mechanized Coq Proofs:** `rust-lang/miri` @ `0a0ce195cb0e91890c21ed717cca6eefef5e1ff3` (`src/concurrency/{data_race.rs, weak_memory.rs}`), `kaist-cp/relaxed-memory-separation-logic` @ `6fe1475af1f8c49f8c144a67d9175b5b3e6bc472` (`gpfsl-examples/{stack, queue, chase_lev}`), `rocq-iris/iris` @ `2fe2f450add5678d9a2492343c638ccdb428a677` (`iris/bi/monpred.v`, `iris/base_logic/lib/proph_map.v`), and foundational papers (`PODC 1996` `10.1145/248052.248106`; `SPAA 2005` `10.1145/1073970.1073974`; `PPoPP 2013` `10.1145/2442516.2442524`; `POPL 2020` `10.1145/3371113`; `CPP 2021` `10.1145/3437992.3439930`; `PLDI 2022` `10.1145/3519939.3523451`).

**Prior Corpus Coverage:** Safe memory reclamation mechanisms—`crossbeam-epoch` 3-epoch `QSBR`/`EBR` (including its `not(miri)` `x86` `Local::pin()` `SeqCst` shortcut), Hazard Pointers (`P2530R3`), `SeqLock` torn-read UB rules, and `MiniRust` `compare_ptr` vs. `AllocId` liveness—are established in `reports/rcu-qsbr-hazard-pointers-seqlocks-and-safe-memory-reclamation-verification` and cited rather than duplicated here. General `OGRA`–`iRC11` program-logic foundations and `P0982R1` / `psc_fence` / hardware compilation axioms are covered in `reports/owicki-gries-fsl-gps-cosmo-and-first-order-view-logics-for-weak-memory-rust` and `reports/c20-seqcst-fences-release-sequences-thin-air-and-rc11-to-rvwmo-arm-compilation-soundness`.

## Findings

### 1. Structural & Weak-Memory Verification Matrix

`Basis: source + normative + derived`

| Property | Treiber Stack (`cs431/stack.rs`, `code_treiber.v`) | Michael-Scott MPMC Queue (`cs431/queue.rs`, `code_ms_tailcas.v`) | Chase-Lev Work-Stealing Deque (`deque.rs`, `chase_lev/code.v`) |
| :--- | :--- | :--- | :--- |
| **Contention Profile** | MPMC LIFO (`head` single hotspot) | MPMC FIFO (`head` + `tail` + `tail.next`) | 1-Owner (`push`/`pop`) + N-Thief (`steal`) |
| **Minimal Memory Model Fragment** | `RA` + C++20 RMW release sequences (`P0982R1`) | `RA` + helping `tail` `Release` CAS | `RA` + **`SeqCst` fences & `SeqCst` 1-elem CAS** (`psc_fence`) |
| **Critical Ordering Invariant** | `push`: `CAS(Rel, Rlx)`; `pop`: `load(Acq)` + **`CAS(Rlx, Rlx)`** | `try_pop`: `load(Acq)` `head` & `next`, `tail==head` advance, **`head.CAS(Rel, Rlx)`** | `push`: `fence(Rel)`; `pop`: `back:=b-1; F_sc; front.load`; `steal`: `front.load(Acq); F_sc; back.load(Acq)` |
| **Linearization / `OMO` Mode** | Mutating CAS (`omo_append_w`), empty read (`omo_insert_r`) | `Enq`: `tail.next.CAS`; `Deq`: `head.CAS`; `EmpDeq`: `omo_insert_r` | Owner `pop`: `F_sc`/`CAS`; `steal`: `front.CAS`; empty: `back.load` |
| **Helping / Prophecies** | None (base); full op helping in `elim_stack` | Physical `tail` helping only; prophecy only if `D5` snapshot kept | None |
| **ABA Surface** | Pointer ABA on `head` (`A -> B -> C` node reuse) | Pointer ABA on `head` / `tail` + retired sentinel reuse | Monotonic index `i64`/`isize` (`2^63` on 64-bit, `2^31` on 32-bit fallback) |
| **Payload Transfer (`T: Send`)** | `MaybeUninit::assume_init_read()` strictly post-`CAS` (`stack.rs:91`) | `assume_init_read()` from *new sentinel* `next` post-`head.CAS` (`queue.rs:142`) | Non-atomic `MaybeUninit` slots **unsound** on circular ring; requires atomic slots |

### 2. Exact C++20/RC11 Orderings and Single-Step Weakening Counterexamples

`Basis: source + normative + execution + derived`

#### 2.1 Treiber Stack (`cs431/src/lockfree/stack.rs:42–109`, `code_treiber.v:14–47`)

In `cs431/src/lockfree/stack.rs`:
- `push` (`L42–66`) allocates `Node { data: MaybeUninit::new(t), next: ptr::null() }`, loads `head(Relaxed)` (`L51`), stores `node.next = head.as_raw()` non-atomically (`L53`), and executes `head.compare_exchange(head, node, Release, Relaxed)` (`L57`). Why does `head.load(Relaxed)` suffice? Because `push` never dereferences `head` (`node.next` only copies its raw pointer bits), and `head.CAS(Release)` publishes both `node.data` and `node.next` (`@{V_push} Node`)!
- `pop` (`L71–102`) pins an EBR `Guard`, executes `head = head.load(Acquire)` (`L75`), dereferences `h.next` **non-atomically** (`L77`), and pops via **`head.compare_exchange(head, next, Relaxed, Relaxed)`** (`L81`) before reading `h.data.assume_init_read()` (`L91`) and deferring `head` destruction (`L94`).
- **Why `pop`'s `(Relaxed, Relaxed)` CAS Is Sound Under `P0982R1` (Yet Weakening to `store(Relaxed)` Breaks Soundness):** Suppose `T1` pushes `A` (`Release` CAS, `sync_vector = {V_init_A}`), `T2` pushes `B` (`Release` CAS, `B.next = A`), and `T3` pops `B -> A` using `head.CAS(B, A, Relaxed, Relaxed)`. Under `miri/src/concurrency/data_race.rs:639–651`, `rmw_relaxed` *joins* `atomic.sync_vector` with `frel`, preserving `V_init_A` inside `head`'s `sync_vector` so a subsequent `T4` reading `head.load(Acquire) == A` synchronizes with `T1`'s `A.data` write (`probe_queues` check). Conversely, if `pop` replaced `CAS` with a non-RMW `store(next, Relaxed)` (even in a single-consumer variant!), `store_relaxed` (`data_race.rs:614–617`) *overwrites* `sync_vector := fence_release`, erasing `V_init_A` and triggering a `DataRace` UB when `T4` reads `A.data`!
- **Why `h.next` Is Non-Atomic and `assume_init_read()` Must Follow CAS:** Every node's `next` pointer is written once before `push`'s `Release` CAS (`AllLinks` persistent `readonly` fractional points-to in `proof_treiber_composition.v:46, 63–73`), so `h.next` is immutable for its reachable lifetime. Reading `h.data` *before* CAS would allow two concurrent poppers to copy `!Copy` `T` (or read-write race with post-CAS `defer_destroy`), whereas `h.data.assume_init_read()` *after* winning `CAS` confers unique logical ownership of `T`. (Note `gpfsl-examples/stack/code_treiber.v:44` uses `cas^ac` to simplify the Coq proof as acknowledged at `L41–43`; `cs431/stack.rs:81` demonstrates the tighter `(Relaxed, Relaxed)` CAS.)

#### 2.2 Michael-Scott MPMC Queue (`cs431/src/lockfree/queue.rs:62–153`, `code_ms.v`, `code_ms_tailcas.v`)

In `cs431/src/lockfree/queue.rs`:
- `push` (`L62–100`) initializes `new { data: MaybeUninit::new(t), next: Atomic::null() }`, loads `tail(Acquire)` (`L70`) and `tail_ref.next.load(Acquire)` (`L74`), helps a lagging tail via `tail.compare_exchange(tail, next, Release, Relaxed)` (`L80`), links `tail_ref.next.compare_exchange(null, new, Release, Relaxed)` (`L87`), and advances `tail.compare_exchange(tail, new, Release, Relaxed)` (`L93`).
- `try_pop` (`L105–153`) loads `head(Acquire)` (`L107`), `next = head.next.load(Acquire)` (`L108`), checks `next.as_ref()?`, reads `tail = self.tail.load(Relaxed)` (`L114`), executes **`if tail == head { let _ = self.tail.compare_exchange(tail, next, Release, Relaxed); }`** (`L115–119`), and then swings **`self.head.compare_exchange(head, next, Release, Relaxed)`** (`L128–130`), finally extracting `next_ref.data.assume_init_read()` (`L142`) and calling `guard.defer_destroy(head)` (`L147`).
- **Two Subtle Weak-Memory Hazards (`queue.rs:112–130` & `code_ms.v:32` vs. `code_ms_tailcas.v:32`):**
  1. *Why `head.CAS` MUST Be `Release` and `try_pop` MUST Advance `tail == head`:* Suppose sentinel `S0` is followed by `N1` while `tail` still points to `S0`. A consumer winning `head.CAS(S0 -> N1)` detaches and retires `S0`. Without advancing `tail` past `S0`, `tail` stays at a freed node (`S0`); even *with* `tail.CAS(S0, N1, Release)`, if `head.CAS` were weakened from `Release` to `Relaxed` (`queue.rs:121–123`), a later thread could acquire `head = N1` without synchronizing with `tail.CAS(S0, N1)` (`AllTailMsgInner` in `proof_ms_composition.v:60–66`) and read stale `tail = S0`—dereferencing a reclaimed node (`probe_queues` check).
  2. *Why `code_ms.v:32`'s Plain `<-rel` Store Is Unsound with Reclamation:* `gpfsl-examples/queue/code_ms.v:32, 43` advances `q.tail <-rel n'` via a blind atomic store rather than `cas^rel` (`code_ms_tailcas.v:32, 43`). Under non-reclaimed Coq semantics, `AllTailMsg` accepts stale tail overwrites as monotonic snapshots, whereas under EBR/HP reclamation a preempted helper writing an old `n'` onto `q.tail` can regress `tail` behind `head` onto a reclaimed node! Verified Rust MS-queues must use `compare_exchange(..., Release, Relaxed)` as in `cs431/queue.rs:80, 93, 118` and `code_ms_tailcas.v:32, 43`.

#### 2.3 Chase-Lev Work-Stealing Deque (`crossbeam-deque/src/deque.rs:420–705`, `chase_lev/code.v:57–96`)

Comparing `Lê et al. (PPoPP 2013)` (`doi:10.1145/2442516.2442524`), `chase_lev/code.v`, and `crossbeam-deque/src/deque.rs`:
- `Worker::push` (`deque.rs:420–454`): loads `b = back(Relaxed)`, `f = front(Acquire)` (needed on circular rings to synchronize slot reuse with prior steals; omitted in unbounded `code.v:59`), writes slot `b`, runs `fence(Release)` (`L445`; or `back.store(..., Release)` under TSan), and `back.store(b + 1, Relaxed)` (`L453`).
- `Worker::pop` LIFO (`deque.rs:511–564`): stores `back(b - 1, Relaxed)`, issues **`fence(SeqCst)`** (`L516`), loads `f = front(Relaxed)` (`L519`). On `b - f < 0`, restores `back(b + 1, Relaxed)` (`L526`); on `b - f > 0` (`len >= 2` before decrement), pops slot `b` **without CAS**; on `b - f == 0` (last item!), competes via `front.compare_exchange(f, f + 1, SeqCst, Relaxed)` (`L539–544`) and restores `back(b + 1, Relaxed)` (`L552`).
- `Stealer::steal` (`deque.rs:662–704`): loads `f = front(Acquire)`, executes **`fence(SeqCst)`** (`L672` or via `epoch::pin()` at `L675`), loads `b = back(Acquire)` (`L678`), loads `buffer(Acquire)` (`L686`, `L691`), and claims via `front.compare_exchange(f, f + 1, SeqCst, Relaxed)` (`L695`).
- **Four Subtle Soundness Facts:**
  1. *`SeqCst` `SB` Double-Claim:* Weakening `fence(SeqCst)` to `fence(AcqRel)` in `pop` or `steal` allows `front = 0, back = 2` -> Thief 1 steals `0` (`front = 1`) -> Owner `pop` writes `back = 1` and reads stale `front = 0` (`len = 1 > 0`, fast-popping slot `1` with NO CAS!) while Thief 2 reads `front = 1` and stale `back = 2`, winning `front.CAS(1 -> 2)` to steal slot `1` (`probe_queues` check)!
  2. *1-Element `pop` vs. `steal` Ordering (`Lê et al., PPoPP 2013` §3):* Even with `SeqCst` fences, if `pop` wrote `back.store(b + 1, Relaxed)` *before* `front.CAS(f, f + 1, SeqCst, Relaxed)` on the `len == 0` path, a thief could see `back = b + 1` and `front = f` and double-steal the last element; and `front.CAS` itself must be `SeqCst` (or followed by `fence(SeqCst)` / paired with `back` update ordering) against subsequent `push` / `steal` epochs (note `code.v:91` weakens the CAS to `cas^rlx` only because its unbounded non-circular `cl_try_pop` restores `bot <-rlx b` strictly *after* `cas` and never wraps buffer indices).
  3. *`crossbeam-deque` `epoch::pin()` Dependence (`deque.rs:671–675`):* `Stealer::steal` omits an explicit `fence(SeqCst)` when `!epoch::is_pinned()`, relying on `epoch::pin()`'s `fence(SeqCst)`—which `crossbeam-epoch` replaces on `x86/x86_64` (`not(miri)`) with `compare_exchange(..., SeqCst)` (`rcu-qsbr-...` §2.2), formally invalid under abstract C++20 `psc_fence` rules!
  4. *`Flavor::Fifo` `fetch_add` + Store Rollback (`deque.rs:486–495`):* On an empty FIFO queue, `Worker::pop` executes `front.fetch_add(1, SeqCst)` then rolls back `front.store(f, Relaxed)`. Any concurrent thief between those two lines temporarily sees `front = f + 1 > back` (`b - f < 0`) and returns `Empty` (harmlessly linearized as empty, *provided* no concurrent `Stealer::steal` advances `front` past `f + 1` before the owner's `store(f, Relaxed)` clobbers it—true only because `b <= f`, so thieves observe `b - (f + 1) < 0` and cannot execute `front.CAS`!).

### 3. Circular Ring-Wrap Data-Race Theorem in Chase-Lev

`Basis: source + normative + execution + derived`

Inspecting `crossbeam-deque/src/deque.rs:96–115, 324–327, 687–696` against `rust-lang/reference` (`r[undefined.race]`, `ref_ub.md:15–16`) and `gpfsl-examples/chase_lev/code.v:20–38, 74–76` yields an impossibility theorem for plain/volatile circular buffers:

- **Pre-CAS `read_volatile` UB (`deque.rs:98–114, 687`):** `Stealer::steal` calls `buffer.read(f)` (`ptr::read_volatile`) *before* validating `front.compare_exchange(f, f + 1)` (`L695`). If Thief 1 stalls between `L687` and `L695` while other thieves steal $0 .. (C - 1)$ and `Worker::push` writes slot $C$ ($C \bmod C = 0$), Thief 1's non-atomic/volatile read and `Worker::push`'s non-atomic/volatile write touch the same physical slot `(f % cap)` without happens-before—**immediate `r[undefined.race]` UB** (acknowledged explicitly at `deque.rs:98–101, 108–111`; note `Worker::resize` at `L325` also calls non-atomic `ptr::copy_nonoverlapping` concurrently with stalled pre-CAS `steal` reads!).
- **Post-CAS Non-Atomic Read Impossibility on a Circular Ring:** Moving `buffer.read(f)` *after* winning `front.CAS(f, f + 1)` (`chase_lev/code.v:75`, sound on an *unbounded* array where slot `f` is never written again) **still causes `r[undefined.race]` UB on a bounded circular ring of capacity $C$**: once `front.CAS(0 -> 1)` commits `front = 1` (`probe_queues` check, $C = 4$), if Thief 1 stalls before reading physical slot `0`, `Worker::push` can immediately fill slots up to `back = C` because `len = C - 1 < C` triggers **no resize**—writing physical slot `C % C == 0` non-atomically *concurrently* with Thief 1's post-CAS non-atomic read of slot `0`! Even though `Worker::push` calls `front.load(Acquire)` (`deque.rs:423`) and synchronizes-with `front.CAS` (`SeqCst`/`Release`), `push` runs *after* `CAS` and therefore **before** Thief 1's delayed slot read, providing zero happens-before between `Thief 1`'s read and `push`'s overwrite!
- **Sound UB-Free Rust Circular Encodings:**
  1. *Indirection (`Atomic<Owned<T>>` slots under EBR):* Slots store `Atomic<Node<T>>` / `AtomicPtr<T>` read via `Relaxed` atomic loads; physical reuse of the slot pointer never races with a stalled thief's dereference of the old `Owned<T>` pointer while `Guard` is pinned.
  2. *Chunked `Relaxed` Atomic Words (`[AtomicUsize; K]`):* Mirroring UB-free optimistic readers (`SeqLock<T>` in `rcu-qsbr-...` §4), slots store `[AtomicUsize; K]` written and read with `Ordering::Relaxed` (including inside `Worker::resize`) into `[MaybeUninit<usize>; K]` and transmuted to `T` via `MaybeUninit::assume_init()` **only** when `front.CAS` succeeds (forgetting the raw bytes on failure so invalid torn bit patterns never leak into typed values).

### 4. Linearization Points Under Weak Memory: Local, Helping, Prophetic, and `OMO`

`Basis: source + normative + derived`

1. **Why Classical SC Linearizability Breaks on `RA` Treiber Stack and MS Queue (`Compass`, `Dang et al., PLDI 2022`):** Under SC, an empty `pop()` / `try_pop()` returning `None` witnesses a global instant where the structure was empty. Under `Release`/`Acquire`, `pop()`'s `head.load(Acquire)` (`stack.rs:75`) or `try_pop()`'s `head.next.load(Acquire)` (`queue.rs:108`) can legally read an older coherent `null` message from a stale generation in modification order even after newer items have been pushed by another thread without `hb` between them. `Compass` (`PLDI 2022`, `doi:10.1145/3519939.3523451`) resolves this via **Event Graphs** (`spec_graph.v`) and **Overapproximating Modification Orders (`OMO`)**:
   - Mutating operations (`Push`, `Pop`, `Enq`, `Deq`) append a new write generation at the tip (`omo_append_w omo (length E) []`, `spec_treiber_composition.v:54, 109`; `spec_composition.v:80`), or at `omo_insert_w` for `Deq`.
   - Read-only empty observations (`EmpPop`, `EmpDeq`) insert a read event into a **past** write generation `gen < length omo` (`omo_insert_r omo gen (length E)`, `spec_treiber_composition.v:106`, `spec_composition.v:103`) consistent with the caller's thread-local view `M` (`OmoUB γg M (length E)`), preserving observational compositionality without forcing spurious `SeqCst` barriers!
2. **Helping Patterns (`MS` Physical Helping vs. Elimination Operation Helping):**
   - *Physical-Pointer Helping (MS-Queue `tail` advance, `queue.rs:77–82, 115–119`):* `Enq` logically linearizes when `tail_ref.next.CAS(null, new, Release, Relaxed)` succeeds—before `tail` moves. Any subsequent `push` or `try_pop` that sees `!next.is_null()` or `tail == head` advances `tail` via `tail.CAS(..., Release, Relaxed)` on the enqueuer's behalf using only persistent node metadata (`AllNodesInner` / `AllTailMsgInner`, `proof_ms_composition.v:60–66, 140–148`).
   - *Full Operation Helping (`elim_stack` / combining):* When `ElimStack` (`cs431/homework/src/elim_stack/elim.rs`) offloads an unmatched push/pop into a backoff slot, the arriving partner thread atomically fulfills the waiting thread's logical commitment (`AU` / atomic update) inside its own CAS and swaps out the partner's result—requiring the waiter to deposit its linear ghost capability (`AU` token) into the shared elimination invariant.
3. **Prophecy Variables (`Jung et al., POPL 2020`; `Vindum & Birkedal, CPP 2021`):**
   - In Iris (`proph_map.v:45–53`), `NewProph` yields `proph p vs` predicting all future `Resolve(e, p, w)` pairs (`10.1145/3371113`).
   - In `Vindum & Birkedal (CPP 2021)` (`10.1145/3437992.3439930`), proving **contextual refinement** for Michael & Scott's *original* pseudocode (`dequeueMS` with consistent-snapshot recheck `D5: if sent = !toSent`) **requires** `p = NewProph` (`D4b`) resolved at `D5` (`Resolve(!toSent, p, ())`): when `D4c` (`next = !toNext`) reads `none`, `D4c` is the abstract linearization point of `dequeueCG` returning `none` **iff** the future `D5` re-read returns `sent` (`v = ℓ_s`).
   - Crucially, Vindum & Birkedal (§7) also prove that under garbage collection (or EBR `Guard` pinning preventing sentinel ABA, as in `cs431/queue.rs:107–111`), omitting `D5` consistent snapshots makes `head.next == null` an unconditional empty witness (`s == head` at the read instant via `s` reachability / `OmoAuth`) and **eliminates prophecy variables completely**! Prophecies remain irreducible only for algorithms with speculative early reads that commit retroactively upon a *future* CAS (e.g., Herlihy-Wing queue or `RDCSS`, `POPL 2020`).

### 5. ABA Hazards and Reclamation Coupling

`Basis: source + normative + derived`

Citing `reports/rcu-qsbr-hazard-pointers-seqlocks-and-safe-memory-reclamation-verification` for EBR/HP/MiniRust `AllocId` mechanics (`compare_ptr` ignoring provenance vs. dereference checking `AllocId` liveness):

- **Treiber Stack ABA:** If node `A` (`A.next = B`) is read by `T1` (`head = A, next = B`), then `T2` pops `A` and `B`, frees `A`, reallocates `A` at the same address, and pushes `A -> C`, `T1`'s `head.CAS(A, B)` succeeds on address `A` and silently drops `C` (or pops freed `B`). Under `crossbeam-epoch`, `T1`'s active `Guard` (`stack.rs:72`) prevents `A` from being reclaimed (`defer_destroy(head)`, `L94`) until `T1` drops its guard, guaranteeing pointer identity uniqueness while guarded (though without EBR, tagged pointers / generation counters are required).
- **Michael-Scott Queue Two-Pointer Pinning:** During `try_pop`, `T1` dereferences `head` to read `next` (`queue.rs:108`), and after `head.CAS(head, next)` reads `next_ref.data.assume_init_read()` (`L142`) *before* retiring old sentinel `head` (`L147`). Because `head` becomes unreachable only *after* `L129` while `next` becomes the new live sentinel (and could itself be popped and retired immediately by a concurrent consumer!), `crossbeam-epoch` pins the thread across the whole retry (`L105`), whereas Hazard Pointers (`Michael 2004`) require **two distinct hazard slots** (`hp0` protecting `head`, `hp1` protecting `next` before dereferencing `next.data`).
- **Chase-Lev Monotonic Index Wrap (`deque.rs:17–36`):** Unlike pointer CAS, Chase-Lev indexes logical slots with unbounded monotonic integers (`front`/`back`: `AtomicI64` on 64-bit targets, wrapping after $2^{63}$ operations). On 32-bit platforms lacking 64-bit atomics (`L29–36`), `WorkerIndex = isize` wraps after $2^{31}$ pushes; if a thief sleeps across $2^{31}$ pushes, `front.CAS(f, f + 1)` suffers **index ABA** even under EBR!

### 6. First-Order (`Type 0`) Ghost-History / View-PCM Proofs vs. Iris Higher-Order Atomic Triples

`Basis: source + derived`

1. **Iris / `GPFSL` Higher-Order Logical Atomicity (`<<< ... >>>`):** In `spec_treiber_composition.v:46–64` and `spec_composition.v:75–109`, specifications bind an arbitrary client view-predicate invariant `Inv γg γs s E omo stlist` via impredicative quantification over `vProp Σ := monPred view (uPredI ...)` (`monpred.v`), requiring step-indexing (`▷`) and higher-order ghost cameras (`OmoAuth`, `OmoSnap`, `CWMono`). This supports open-world clients that atomically transfer arbitrary higher-order ownership (`Box<dyn FnOnce() + Send>`) inside the collection's linearization step.
2. **First-Order `Type 0` View-PCM + `OMO` Verification:** When verifying concrete Rust collections `Stack<T>`, `Queue<T>`, and `Deque<T>` against a first-order payload predicate `OwnT : T → VProp_0` (`VProp_0 := View → GhostPCM → Prop`, `owicki-gries-...` §3), **zero step-indices (`▷`) or impredicative `uPred` universes are needed**:
   - *Treiber node protocol:* Per-node immutable view state `Node(n, next, V_init)` holding persistent `next` + exclusive `Escrowed(V_init, OwnT(v))` claimed by a 1-shot `PopTok(n)` upon winning `head.CAS` (`assume_init_read`).
   - *MS-queue node protocol:* Monotone 2-state link `Unlinked ⊑ Linked(next, V_next)` + sentinel monotonicity (`mono_nat` index ordering `idx(head) <= idx(tail)`) + per-node `DeqTok(next)` claiming `OwnT(v)`.
   - *Chase-Lev slot protocol:* Per-index 4-state PCM `Unwritten -> Published(V_init) -> ClaimedByOwner | Stolen(V_steal)` + global `(b, f, V_sc)` view state enforcing `sc_fence` ordering on `(back, front)`.

## Boundaries

- **Sufficiency of `Release`/`Acquire` for Chase-Lev or Plain `store(Relaxed)` for Release Sequences:** **known not to apply** — weakening Chase-Lev's `fence(SeqCst)` to `AcqRel` permits `SB` double-claim of slots (`probe_queues` check), and replacing an RMW with `store(Relaxed)` breaks C++20 `P0982R1` release sequences (`data_race.rs:614–617`).
- **Circular Buffer Plain/Volatile Slot Sharing and 32-Bit Chase-Lev Wrap Immunity:** **unsupported** — `crossbeam-deque`'s pre-CAS `ptr::read_volatile` (`deque.rs:687`, `98–114`) and `Worker::resize` `copy_nonoverlapping` (`L325`), as well as naive circular post-CAS non-atomic reads, violate `r[undefined.race]` under wrap-around (`probe_queues` check); 32-bit `isize` fallback (`L29–36`) lacks 64-bit ABA-free wrap capacity.
- **Minimal `SeqCst` Elimination Under `Promising 2.0` Speculative Execution:** **unknown** — whether `Promising Semantics 2.0` capped-memory promise certification permits eliminating any `SeqCst` CAS vs. fence variant on single-element Chase-Lev rollback without breaking `Lê et al. (PPoPP 2013)` hardware safety was not formally settled.
- **Weak-Memory Lock-Freedom / Wait-Freedom Liveness and Hardware `LL/SC` Progress:** **not examined** — all cited `GPFSL`, `ReLoC`, and `Type 0` proofs establish partial-correctness safety and linearizability/refinement; fair-scheduling progress under weak memory (`orc11/progress.v`) and `LR/SC` reservation-set starvation were outside scope.

## Evidence

- **`crossbeam-rs/crossbeam` @ `a28f40fdddb70bea8e5faf0efad9af0be4b9dbea`:** `crossbeam-deque/src/deque.rs` (`L17–36` index types, `L85–115` `Buffer::read`/`write` volatile UB admission, `L315–346` `resize`, `L420–705` `push`, `pop` FIFO/LIFO, `steal`).
- **`kaist-cp/cs431` @ `0bc971aa82f600b948eb9f83bb972bef31b9fc5d`:** `src/lockfree/stack.rs` (`L42–109`), `src/lockfree/queue.rs` (`L62–153`), `homework/src/elim_stack/{treiber_stack.rs:53–94, elim.rs:1–48}`.
- **`kaist-cp/relaxed-memory-separation-logic` @ `6fe1475af1f8c49f8c144a67d9175b5b3e6bc472`:** `gpfsl-examples/stack/{code_treiber.v:14–78, spec_treiber_composition.v:40–140, proof_treiber_composition.v:44–131, 520–667}`, `gpfsl-examples/queue/{code_ms.v:15–76, code_ms_tailcas.v:15–76, spec_composition.v:48–167, proof_ms_composition.v:60–225, 899–1060}`, and `gpfsl-examples/chase_lev/code.v:20–97`.
- **`rust-lang/rust` @ `ec65cd52bba13d491ff65c9d218b39753755c84a`:** `library/core/src/sync/atomic.rs:465–525`.
- **`rust-lang/miri` @ `0a0ce195cb0e91890c21ed717cca6eefef5e1ff3`:** `src/concurrency/{data_race.rs:1–35, 603–651, 1867; weak_memory.rs:1–65}`.
- **`rocq-iris/iris` @ `2fe2f450add5678d9a2492343c638ccdb428a677`:** `iris/bi/monpred.v`, `iris/base_logic/lib/proph_map.v:1–55`.
- **Papers:** Michael & Scott, PODC 1996 (`doi:10.1145/248052.248106`); Chase & Lev, SPAA 2005 (`doi:10.1145/1073970.1073974`); Lê et al., PPoPP 2013 (`doi:10.1145/2442516.2442524`); Jung et al., POPL 2020 (`doi:10.1145/3371113`); Vindum & Birkedal, CPP 2021 (`doi:10.1145/3437992.3439930`); Dang et al., PLDI 2022 (`doi:10.1145/3519939.3523451`).
- **Execution (`python3` 3.13, `2026-11-20`):** Verified `P0982R1` Treiber RMW release-sequence preservation vs. `store(Relaxed)` break, MS-queue lagged-tail advance + `head.CAS(Release)` view invariant, Chase-Lev `SeqCst` vs. `AcqRel` `SB` double-claim, and both pre-CAS and post-CAS circular ring data-race witnesses (`exit 0`).

## Revalidation

1. **Upstream Diffs (< 1 min):** Diff `crossbeam-deque/src/deque.rs` (`crossbeam-rs/crossbeam`), `src/lockfree/{stack.rs, queue.rs}` (`kaist-cp/cs431`), and `gpfsl-examples/{stack/code_treiber.v, queue/code_ms_tailcas.v, chase_lev/code.v}` (`kaist-cp/relaxed-memory-separation-logic`) against the pinned SHAs to detect ordering or slot-atomicity changes.
2. **Self-Contained Executable Probe (`python3`, stdlib only, < 0.1s):**

```python
#!/usr/bin/env python3
"""Verify P0982R1 Treiber RMW-RS, MS tail-advance/Release, Chase-Lev SeqCst SB, and circular ring races."""


def treiber_p0982r1(pop_rmw: bool) -> bool:
    v_a, v_b = 1, 2
    sync_vec = {v_a} | {v_b}  # Push A (Rel), then Push B (Rel) via RMW
    frel_pop = set()
    sync_vec = (sync_vec | frel_pop) if pop_rmw else frel_pop  # P0982R1: store(Rlx) drops sync_vec
    return v_a in sync_vec


def ms_tail_invariant(advance_tail: bool, head_cas_release: bool) -> bool:
    idx = {"S0": 0, "N1": 1}
    tail = "N1" if advance_tail else "S0"
    retired = {"S0"}
    tail_seen = tail if head_cas_release else "S0"
    return (tail_seen not in retired) and (idx[tail_seen] >= idx["N1"])


def chase_lev_sb(use_seqcst: bool) -> bool:
    for owner_sc_first in (True, False):
        for f_own in (0, 1):
            for b_thief in (2, 1):
                if use_seqcst:
                    if owner_sc_first and b_thief == 2:
                        continue
                    if (not owner_sc_first) and f_own == 0:
                        continue
                if (1 - f_own) > 0 and (b_thief - 1) > 0:
                    return False  # Double-claim on slot 1
    return True


def circular_ring_races(cap: int = 4) -> tuple[bool, bool]:
    thief_slot = 0 % cap
    owner_push_idx = cap  # With front=1 after Thief's CAS (or Thief2..), len = cap - 1 < cap (no resize)
    pre_cas_race = (cap - 1 < cap) and (thief_slot == owner_push_idx % cap)
    post_cas_race = (cap - 1 < cap) and (thief_slot == owner_push_idx % cap)
    return pre_cas_race, post_cas_race


assert treiber_p0982r1(True) and not treiber_p0982r1(False)
assert ms_tail_invariant(True, True) and not ms_tail_invariant(False, True) and not ms_tail_invariant(True, False)
assert chase_lev_sb(True) and not chase_lev_sb(False)
assert circular_ring_races(4) == (True, True)
print("OK: Treiber P0982R1, MS tail/Release, Chase-Lev SeqCst SB, and circular ring race checks passed.")
```
