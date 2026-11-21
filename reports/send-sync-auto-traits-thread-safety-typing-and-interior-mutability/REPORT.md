# Send and Sync in a toy capability model: auto-trait derivation, thread-safety typing and interior mutability (Lean 4)

## Summary

This package mechanizes, in Lean 4 with the core library and no Mathlib, a small capability model of
Rust's `Send` and `Sync` traits (namespace `Toy.SendSync`). A toy type `T` denotes a footprint `fp T` of three event
lists: what an owner of a `T` can do, what a holder of a shared reference `&T` can do, and what other parties may
still do concurrently. `SemSend T` and `SemSync T` say that moving a `T`, respectively sharing a `&T`, with a second
thread creates no data race between jointly satisfiable conflicting events and makes no thread release a lock
acquisition that another thread made. Over this model the package proves 22 results: characterizations of `SemSend`
and `SemSync` for references, `Cell`, `RefCell`, `Rc`, `Arc`, `Mutex`, `MutexGuard`, products, sums, boxes and user
wrappers that restrict their field's shared capabilities (optionally with an unsafe `Sync` impl); soundness of a
structural auto-trait checker `autoCheck` for sound primitive impl tables and justified unsafe impls; exactness of
that checker with the standard table on types without user wrappers; and refutations of the rules "`Sync` implies
`Send`" and "`Send` implies `Sync`". A further card collects proved positive and negative examples of the core
definitions. Each of the 8 listed hypotheses is tight, with a proved counterexample in which all other hypotheses
hold and the conclusion fails; each card has a proved non-vacuity witness; each impossibility result has a proved
positive control.

Model–system relation: none proved. These are statements about the toy capability model `Toy.SendSync`; they neither establish nor refute the corresponding claims about Rust's `Send` and `Sync` traits, rustc's auto-trait implementation, or the standard library types `Cell`, `RefCell`, `Rc`, `Arc`, `Mutex`, `MutexGuard`. Each comparison with Rust is a separate claim labelled `Basis: derived (modeling bridge)`, with its
reasoning; the Lean kernel checks the model statements and nothing else.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

The results (each bullet is the leading sentence of the card's plain-language claim, verbatim;
companion conclusions stated in later sentences of a claim are omitted here and appear in the card under
**Findings**):

- **`link-sync-iff-ref-send`** (characterization, T0, definitional). For every toy type `T`, `SemSync T` holds if and only if `SemSend (.ref T)` holds, with no assumption: the footprint of `.ref T` is defined from the shared footprint of `T` (`own := shr T`, `alias := shr T ++ alias T`), and the equivalence holds by `Iff.rfl`.
- **`structural-soundness`** (theorem, T0, shallow). For every impl table `tb` with `TableSound tb` (each primitive rule, when its condition holds of the argument's semantic `SemSend`/`SemSync`, yields the semantic property of the primitive type) and every toy type `T` with `ImplsSound T` (every unsafe `Sync` impl on a wrapper node of `T` is semantically justified), `(autoCheck tb T).1 = true` implies `SemSend T` and `(autoCheck tb T).2 = true` implies `SemSync T`.
- **`std-table-sound`** (theorem, T0, shallow). The table `stdTable` (`Cell`/`RefCell`: `Send` if the argument is `Send`, never `Sync`; `Rc`: neither; `Arc`: both if the argument is `Send` and `Sync`; `Mutex`: both if the argument is `Send`; `MutexGuard`: never `Send`, `Sync` if the argument is `Sync`) satisfies `TableSound`.
- **`std-checker-exact-wrap-free`** (characterization, T1, shallow). For every toy type `T` with `WrapFree T` (no user wrapper node), `(autoCheck stdTable T).1 = true` holds if and only if `SemSend T`, and `(autoCheck stdTable T).2 = true` holds if and only if `SemSync T`.
- **`cell-send-iff`** (characterization, T0, shallow). For every toy type `U`, `SemSend (.cell U)` holds if and only if `SemSend U` holds; the same holds for `.refCell U` (`semSend_refCell_iff`).
- **`cell-not-sync`** (impossibility, T1, shallow). For every toy type `U`, `SemSync (.cell U)` fails (and so does `SemSync (.refCell U)`): two threads holding a shared reference can both write the cell's storage (resp. the borrow flag) with no claim, a data race.
- **`rc-neither`** (impossibility, T1, shallow). For every toy type `U`, neither `SemSend (.rc U)` nor `SemSync (.rc U)` holds: two handles (one per thread, both holding the allocation, claim `via []`) can both write the non-atomic count.
- **`arc-send-iff`** (characterization, T1, shallow). For every toy type `U`, `SemSend (.arc U)` holds if and only if both `SemSend U` and `SemSync U` hold, and `SemSync (.arc U)` holds if and only if both `SemSend U` and `SemSync U` hold (`semSync_arc_iff`); `arc_race_iff` decomposes the transfer race of `.arc U` into the races of `U`.
- **`mutex-sync-iff`** (characterization, T1, shallow). For every toy type `U`, `SemSync (.mutex U)` holds if and only if `SemSend U` holds, and `SemSend (.mutex U)` holds if and only if `SemSend U` holds (`semSend_mutex_iff`).
- **`guard-sync-iff`** (characterization, T1, shallow). For every toy type `U`, `SemSync (.guard U)` holds if and only if `SemSync U` holds.
- **`guard-not-send`** (impossibility, T1, definitional). Under the model's release-affinity rule (`NoForeignRelease`: every acquisition that a release event executed by the other thread names, by a claim `held l a` on the event's own location `l`, was made by the other thread; every release event of every model footprint names an acquisition, by `fp_relNamesAcq`; a guard's acquisition was made by the origin thread), `SemSend (.guard U)` fails for every toy type `U`, because the guard's owner footprint contains the release of its own acquisition.
- **`false-rule-sync-implies-send`** (impossibility, T1, shallow). It is not the case that every toy type `T` with `SemSync T` has `SemSend T`; witnesses: `.guard .plain`, and the guard-free `.wrap (.rc .plain) .none u` for either `u` (`wrap_rc_none_semSync_not_semSend`).
- **`false-rule-send-implies-sync`** (impossibility, T1, shallow). It is not the case that every toy type `T` with `SemSend T` has `SemSync T`; witness: `.cell .plain`.
- **`shared-write-free-send-implies-sync`** (theorem, T1, shallow). For every toy type `T` whose shared footprint `(fp T).shr` contains no write event (hypothesis `hro`) and which satisfies `SemSend T` (hypothesis `hs`), `SemSync T` holds.
- **`own-in-shared-sync-implies-send`** (theorem, T1, shallow). For every toy type `T` whose owner footprint `(fp T).own` is contained in its shared footprint `(fp T).shr` (hypothesis `hsub`) and which satisfies `SemSync T` (hypothesis `hy`), `SemSend T` holds.
- **`unsafe-sync-obligation`** (characterization, T0, definitional). For every field type `f`, view `v` and impl flag `u`, `SemSync (.wrap f v u)` holds if and only if `SyncObligation f v` holds (every conflicting pair formed by an exposed shared capability on the other thread and an exposed shared capability or an alias capability of the field on the origin thread is never simultaneously enabled, and no exposed capability makes the other thread release an acquisition it did not make); this restates the definition of `SemSync` for wrappers, and the flag `u` does not occur on the right-hand side.
- **`wrap-view-restriction`** (theorem, T1, shallow). For every field type `f`, view `v` and impl flag `u` such that `SemSync f` holds (hypothesis), `SemSync (.wrap f v u)` holds: restricting the shared capabilities of a semantically `Sync` field by any view keeps the wrapper semantically `Sync`.
- **`wrap-cell-obligation`** (characterization, T1, shallow). For every toy type `U` and flag `u`, a read-only wrapper over `Cell<U>` is semantically `Sync`, `SemSync (.wrap (.cell U) .readOnly u)`, if and only if `OwnReadsRaceFree U` holds: reads through the owner capabilities of `U` that a read-only view keeps (no access under an acquisition by the executing thread), executed by the other thread, race with no alias capability of `U`.
- **`wrap-refcell-obligation`** (characterization, T1, shallow). For every toy type `U` and flag `u`, a read-only wrapper over `RefCell<U>` is semantically `Sync`, `SemSync (.wrap (.refCell U) .readOnly u)`, if and only if `ShrReadsRaceFree U` holds: reads through the shared capabilities of `U` that a read-only view keeps, executed by the other thread, race with no alias capability of `U`.
- **`wrap-rc-obligation`** (characterization, T1, shallow). For every toy type `U`, view `v` and flag `u`, `SemSync (.wrap (.rc U) v u)` holds if and only if `v = .none`: a read-only view still exposes the non-atomic count read, which races with count writes through other handles.
- **`checker-incomplete`** (counterexample, T1, shallow). The wrapper `.wrap (.cell .plain) .readOnly false` (no unsafe impl) satisfies `SemSync`, and its shared reference satisfies `SemSend`, while `autoCheck stdTable` rejects both.
- **`structural-constructors`** (characterization, T1, shallow). For all toy types `A` and `B`, `SemSend (.prod A B)` holds if and only if `SemSend A` and `SemSend B` hold, and `SemSync (.prod A B)` holds if and only if `SemSync A` and `SemSync B` hold (`semSync_prod_iff`); the same two characterizations hold for `.sum A B` (`semSend_sum_iff`, `semSync_sum_iff`, which reuse the product proofs because `fp (.sum A B) = fp (.prod A B)` for all `A` and `B`, by `rfl`: `fp_sum_eq_prod`).
- **`definition-examples`** (theorem, T0, definitional). The core definitions admit their intended positive examples and reject their intended negative examples: `Race`, `Compatible`, `NoForeignRelease`, `RelNamesAcq`, `View.expose` (with `Ev.acquires`), `fp`, `SemSend`, `SemSync`, `autoCheck`, `TableSound`, `ImplsSound`, `WrapFree`, `SyncObligation`, `OwnReadsRaceFree` and `ShrReadsRaceFree`, each on the concrete instances stated in the listed theorems.

**Non-claims.** Every result has non-claims, listed under **Boundaries** (the global non-claims
first, then the non-claims of each result). Read them before relying on a result.

## Applicability

The findings are statements about the Lean definitions in `lean/ToySendSync/` (Lake library
`ToySendSync`, namespace `Toy.SendSync`), checked by the Lean 4 kernel of toolchain `leanprover/lean4:v4.34.1`, with
no Lake dependencies (core Lean and no Mathlib). Model–system relation: none proved. These are statements about the toy capability model `Toy.SendSync`; they neither establish nor refute the corresponding claims about Rust's `Send` and `Sync` traits, rustc's auto-trait implementation, or the standard library types `Cell`, `RefCell`, `Rc`, `Arc`, `Mutex`, `MutexGuard`. No embedding, abstraction or simulation between the
model and Rust is proved, so no theorem transfers to Rust; the remarks that relate the model to Rust are
modeling-bridge reasoning, labelled as such.

### Model fidelity

This is a toy model. Its definitions are meant to capture the informal reading of `Send` ("it is
safe to send it to another thread") and `Sync` ("`T` is `Sync` if and only if `&T` is `Send`") in the Rust
documentation, for a fixed finite set of type constructors whose footprints are chosen by hand from the documented
signatures and behaviour of the corresponding standard-library operations. The model, and the footprint choices that
matter for reading the results, are as follows.

A toy type `T` denotes a footprint `fp T` of three event lists:

* `own`: what an owner of a `T` can do (including everything a sharer can, `shr_subset_own`);
* `shr`: what a holder of a shared reference `&T` can do;
* `alias`: what another party may still do concurrently over locations reachable from the value: other clones of
  a counted allocation, the lender of a borrow (restricted to shared access), other lockers of a borrowed mutex.

Events carry a kind (`rd` non-atomic read, `wr` non-atomic write, `atomic` atomic read-modify-write, `rel` release of a
lock acquisition, which is not a memory access), a location (a path in the type tree), and claims (`held lk a`: the lock
at `lk` is held by acquisition `a`; `via p`: the executing thread holds a handle to the counted allocation `p`;
`uniq p`: it holds one and the other thread holds none). Two threads are modelled: `Tid.origin`, which created the
value, and `Tid.other`. A data race (`Race B A`) is an event of `B` (other thread) and an event of `A` (origin thread)
at the same location, both accesses, at least one a write, not both atomic, whose claims can hold together in one
synchronization snapshot (`Compatible`): a lock has at most one holder, and a unique handle excludes a handle on the
other thread.

There is no execution semantics. A race is a conflicting pair whose claims are jointly satisfiable in some snapshot,
and every snapshot counts. No result quantifies over executions, schedules or runs of a generated semantics; the
quantifiers range over the events of finite lists and over all snapshots. The footprint table `fp` and the views of
`View.expose` are modeling choices that may omit or merge operations of real types, so race freedom in `Toy.SendSync`
is not a conservative statement about Rust executions. Wherever a card says that a snapshot used by a race witness
corresponds to a state of a Rust program, that is a modeling-bridge remark (not proved here).

* `SemSend T := ¬ Race (fp T).own (fp T).alias ∧ NoForeignRelease .other (fp T).own`: moving a `T` to the other thread.
* `SemSync T := ¬ Race (fp T).shr ((fp T).shr ++ (fp T).alias) ∧ NoForeignRelease .other (fp T).shr`: sharing `&T`.
* `NoForeignRelease t es` (release affinity): every acquisition that a release event of `es`, executed by thread `t`,
  releases was made by `t`. The released acquisition is the one named by the event's claim `held l a` on its own
  location `l`; other claims are preconditions. A release event without such a claim names no acquisition and is not
  constrained (`nfr_example_unnamed_release`); every release event of every footprint `fp T` carries one
  (`fp_relNamesAcq`, with `RelNamesAcq`), so on the model's footprints each release must release an acquisition made by
  `t`. A `fresh` acquisition was made by the executing thread; a guard's acquisition was made by the thread that created
  the guard, which in both scenarios is the origin thread (`Acq.maker`).
* `autoCheck tb T` computes `(send, sync)` verdicts structurally from an impl table `tb` for the six primitives,
  fixed rules for `plain`, `&T`, `&mut T`, componentwise conjunction for `box`/`prod`/`sum`, and for a wrapper the
  field's verdicts with `sync` forced by an unsafe impl flag.

Footprint choices that matter for reading the results:

* A shared reference to `Cell<U>` reaches the owner capabilities of `U`: `Cell::get` copies the content out, and
  `Cell::replace`, `Cell::set` and `Cell::take` move it out or drop it. The footprint of `Cell<U>` has the cell's storage
  at the root location.
* `RefCell<U>` has a different footprint (`fp_refCell_plain`, `fp_shr_cell_ne_refCell_plain`). Its root location is the
  borrow flag. A shared reference reads and writes the flag (`RefCell::borrow`, `RefCell::borrow_mut`, dropping
  `Ref`/`RefMut`), reaches the shared capabilities of `U` through a shared borrow (`RefCell::borrow`, or the unsafe
  `RefCell::try_borrow_unguarded`, which reads the flag without updating it), and reaches the owner capabilities of `U`
  under a mutable borrow registered in the flag (claim `held [] .fresh`: `RefCell::borrow_mut`, and `replace`,
  `replace_with`, `swap`, `take`, which borrow mutably). The owner of a `RefCell<U>` also reaches the owner capabilities of
  `U` without the flag (`RefCell::get_mut`, `into_inner`). The claim treats the flag as a lock with one exclusive holder,
  a modeling choice; shared borrows carry no claim, because the model has no reader-count claim. In Rust the flag is a
  non-atomic `Cell<BorrowCounter>` and `RefCell<T>` is not `Sync`; in the model the flag's unclaimed reads and writes
  make `RefCell<U>` not semantically `Sync` (`not_semSync_refCell`).
* `SemSend` and `SemSync` give `Cell<U>` and `RefCell<U>` the same verdict for every `U`
  (`cell_refCell_semSend_semSync_agree`), and so does `autoCheck stdTable` (`autoCheck_std_cell_eq_refCell`), as the
  standard library gives both types the same impl bounds. The two types differ under a read-only wrapper: the `Cell`
  content condition is `OwnReadsRaceFree`, the `RefCell` content condition is the weaker `ShrReadsRaceFree`, and
  `wrap_readOnly_cell_refCell_differ` separates them.
* A thread that locks a `Mutex` through a shared reference also releases that `fresh` acquisition; dropping a guard
  releases the guard's acquisition.
* `.box U` and `.refMut U` have the footprint of `U`; a wrapper's owner and alias capabilities are those of its field;
  `.sum A B` has the footprint of `.prod A B` (`fp_sum_eq_prod`): no discriminant and no variant exclusivity.
* Locations are path-relative: a location names the value at a position, not a particular value moved into or out of
  that position over time (`mem::replace` through `&mut T` or through a guard). A value moved out keeps the path of
  its former position; its alias capabilities carry no lock claim, so conflicts between moved-out content and its own
  aliases are retained.
* A user wrapper `.wrap f v u` restricts the shared capabilities of its field by a view: `.full` (all of them),
  `.readOnly` (exactly the `rd` events that need no acquisition by the executing thread, `Ev.acquires`) or `.none`
  (nothing). A read-only view therefore drops writes, atomic updates, releases, and every access that first requires
  locking a mutex or registering a mutable borrow in a `RefCell`'s flag, since both write lock state; of a `Mutex` it
  keeps nothing, because every shared capability in the definition of `fp (.mutex U)` carries the claim `held [] .fresh`
  (instance: `expose_readOnly_mutex_example`). Views filter events one at a time: an API operation that reads data
  but also writes metadata (`RefCell::borrow` writes the borrow flag) is not a read-only operation in this sense, and
  capabilities handed out by the API (for example a copied-out reference) are filtered like the others.

### Known gaps between the model and Rust

* There is no execution semantics: no result quantifies over executions, schedules or runs of a generated semantics, there are no memory orderings and no happens-before relation, and two atomic read-modify-write events never race with each other. Race freedom in the model is not a conservative statement about Rust executions.
* Two threads are modelled. The other thread executes every checked event, and every guard reachable from the value is taken to be created by the origin thread (`Acq.maker`).
* `Ty` is finite and monomorphic: it has no recursive types (for which rustc resolves auto traits coinductively), no generic user wrappers, no negative impls on user types, no multi-field wrappers, and no `UnsafeCell`, raw pointers, `PhantomData`, `dyn Trait`, closures or `async` futures. Lifetimes and scoped threads are not modelled. Unsafe `Send` impls are not modelled; the wrapper flag of `.wrap f v u` models an unsafe `Sync` impl.
* Six standard-library primitives are modelled (`Cell`, `RefCell`, `Rc`, `Arc`, `Mutex`, `MutexGuard`). Other types (for example `RwLock` and its guards, atomic integer types, `Weak`, `OnceCell`, channels) are not modelled.
* `.box U` and `.refMut U` have the footprint of `U`; `.sum A B` has the footprint of `.prod A B` (`fp_sum_eq_prod`); locations are path-relative. A view filters events one at a time, so an API operation that reads data and writes metadata is not read-only in the model's sense.

### Subjects and how they relate

* **Lean 4 toolchain** (`leanprover/lean4`, tag `v4.34.1`, commit
  `5045d0056413266e57c625dcd7c365b10e377c52`): the subject that was executed. Every theorem in this package is
  kernel-checked with it.
* **Rust source and documentation** (`rust-lang/rust` tag `1.100.0`, commit
  `0ef1bc386059596dada8fb65b50425aab2ea637a`; the Rustonomicon, `rust-lang/nomicon` commit
  `b0bb569883a3e65ab19d4f1adf1b8dbc1629d0a6`; the Rust Reference, `rust-lang/reference` commit
  `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`; Rust RFCs, `rust-lang/rfcs` commit
  `f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4`): read, not executed. The footprints of the six primitives and the impl
  table `stdTable` transcribe documented API signatures and impl declarations from these sources, and the
  modeling-bridge lines compare the theorems with the documented behaviour. The report concerns the model
  interpreted against these documents; it makes no claim that the model is faithful to them beyond what each bridge
  line argues.
* **RustBelt** (POPL 2018, DOI 10.1145/3158154) and **RustBelt Meets Relaxed Memory** (POPL 2020, DOI
  10.1145/3371102): prior art compared in the cards. The package does not reuse their definitions.

### Toolchain

Lean `leanprover/lean4:v4.34.1` (pinned in `lean/lean-toolchain`); core Lean and no Mathlib, no Lake dependencies (`lean/lakefile.toml` declares one library, `ToySendSync`).

## Findings

Every card below states its tier, kind and depth, quotes its Lean statements verbatim with their source line ranges (proofs elided as `:= …`), and gives its hypothesis ledger, non-vacuity witness, positive control (for impossibility results), prior art and design question. The definitions are quoted first, each followed by the proved positive and negative examples attached to it, if any (the card `definition-examples` lists all of them). Every card's non-claims are under **Boundaries**.

### Definitions

#### `Path`

Locations and lock/allocation identities are paths in the type tree of the value under consideration.

```lean
-- lean/ToySendSync/Model.lean:34-34
abbrev Path := List Nat
```

#### `Tid`

The two threads: the origin thread, which created the value, and another thread.

```lean
-- lean/ToySendSync/Model.lean:38-41
inductive Tid where
  | origin
  | other
  deriving DecidableEq, Repr
```

#### `Tid.flip`

The other thread of the two.

```lean
-- lean/ToySendSync/Model.lean:44-46
def Tid.flip : Tid → Tid
  | .origin => .other
  | .other => .origin
```

#### `Acq`

Lock acquisitions: `fresh` (made by the executing thread itself: locking a mutex through a shared reference, or registering a mutable borrow in a `RefCell`'s flag) or `guard g` (owned by the guard at path `g`, made by the thread that created that guard).

```lean
-- lean/ToySendSync/Model.lean:52-55
inductive Acq where
  | fresh
  | guard (g : Path)
  deriving DecidableEq, Repr
```

#### `Claim`

Preconditions of an event: a lock held by an acquisition; a handle to a counted allocation; a unique handle.

```lean
-- lean/ToySendSync/Model.lean:62-66
inductive Claim where
  | held (lk : Path) (a : Acq)
  | via (alloc : Path)
  | uniq (alloc : Path)
  deriving DecidableEq, Repr
```

#### `Claim.path`

The path a claim constrains.

```lean
-- lean/ToySendSync/Model.lean:69-72
def Claim.path : Claim → Path
  | .held p _ => p
  | .via p => p
  | .uniq p => p
```

#### `Kind`

Non-atomic read, non-atomic write, atomic read-modify-write, release (not a memory access).

```lean
-- lean/ToySendSync/Model.lean:76-81
inductive Kind where
  | rd
  | wr
  | atomic
  | rel
  deriving DecidableEq, Repr
```

#### `Kind.isAccess`

Memory accesses.

```lean
-- lean/ToySendSync/Model.lean:84-86
def Kind.isAccess : Kind → Bool
  | .rel => false
  | _ => true
```

#### `Kind.isWrite`

Writes (atomic read-modify-writes count as writes).

```lean
-- lean/ToySendSync/Model.lean:89-92
def Kind.isWrite : Kind → Bool
  | .wr => true
  | .atomic => true
  | _ => false
```

#### `Kind.isAtomic`

Atomic accesses.

```lean
-- lean/ToySendSync/Model.lean:95-97
def Kind.isAtomic : Kind → Bool
  | .atomic => true
  | _ => false
```

#### `Kind.isRead`

Non-atomic reads: the kind of event a read-only view exposes (which in addition requires `Ev.acquires = false`).

```lean
-- lean/ToySendSync/Model.lean:100-102
def Kind.isRead : Kind → Bool
  | .rd => true
  | _ => false
```

#### `Ev`

A capability event: kind, location, claims.

```lean
-- lean/ToySendSync/Model.lean:106-110
structure Ev where
  kind : Kind
  loc : Path
  claims : List Claim
  deriving DecidableEq, Repr
```

#### `Claim.isFresh`

A claim that a lock is held by an acquisition the executing thread made itself.

```lean
-- lean/ToySendSync/Model.lean:113-115
def Claim.isFresh : Claim → Bool
  | .held _ .fresh => true
  | _ => false
```

#### `Ev.acquires`

The event runs under an acquisition made by the executing thread itself; making that acquisition writes lock state (locking a mutex, registering a mutable borrow in a `RefCell`'s flag).

```lean
-- lean/ToySendSync/Model.lean:120-120
def Ev.acquires (e : Ev) : Bool := e.claims.any Claim.isFresh
```

Example (with `View.expose`) `expose_readOnly_example_acquires`:

```lean
-- lean/ToySendSync/Results.lean:87-89
theorem expose_readOnly_example_acquires :
    View.expose .readOnly [rootEv .rd [.held [] .fresh], rootEv .rd [.held [] (.guard [])]] =
      [rootEv .rd [.held [] (.guard [])]] := …
```

#### `Holder`

Lock holders in a snapshot.

```lean
-- lean/ToySendSync/Model.lean:123-126
inductive Holder where
  | thread (t : Tid)
  | guard (g : Path)
  deriving DecidableEq, Repr
```

#### `Snap`

A synchronization snapshot: one holder per lock (a function), and per allocation which threads hold a handle. Every snapshot is treated as reachable; no relation to the states of real executions is established.

```lean
-- lean/ToySendSync/Model.lean:132-134
structure Snap where
  lock : Path → Option Holder
  holds : Path → Tid → Bool
```

#### `Acq.holder`

The holder an acquisition denotes for a given thread.

```lean
-- lean/ToySendSync/Model.lean:137-139
def Acq.holder (t : Tid) : Acq → Holder
  | .fresh => .thread t
  | .guard g => .guard g
```

#### `Sat`

Satisfaction of one claim by a thread in a snapshot.

```lean
-- lean/ToySendSync/Model.lean:142-145
def Sat (σ : Snap) (t : Tid) : Claim → Prop
  | .held p a => σ.lock p = some (a.holder t)
  | .via p => σ.holds p t = true
  | .uniq p => σ.holds p t = true ∧ σ.holds p t.flip = false
```

#### `SatAll`

Satisfaction of a list of claims.

```lean
-- lean/ToySendSync/Model.lean:148-148
def SatAll (σ : Snap) (t : Tid) (cs : List Claim) : Prop := ∀ c ∈ cs, Sat σ t c
```

#### `Compatible`

Two claim lists (other thread, origin thread) can hold in one snapshot.

```lean
-- lean/ToySendSync/Model.lean:152-153
def Compatible (cs₁ cs₂ : List Claim) : Prop :=
  ∃ σ : Snap, SatAll σ .other cs₁ ∧ SatAll σ .origin cs₂
```

Positive example `compatible_example_via_via`:

```lean
-- lean/ToySendSync/Results.lean:38-38
theorem compatible_example_via_via : Compatible [.via []] [.via []] := …
```

Negative example `not_compatible_example_uniq_via`:

```lean
-- lean/ToySendSync/Results.lean:42-42
theorem not_compatible_example_uniq_via : ¬ Compatible [.uniq []] [.via []] := …
```

#### `Concurrent`

Two events can be enabled at the same time.

```lean
-- lean/ToySendSync/Model.lean:157-157
def Concurrent (e₁ e₂ : Ev) : Prop := Compatible e₁.claims e₂.claims
```

#### `Conflicting`

Same location, both accesses, at least one write, not both atomic.

```lean
-- lean/ToySendSync/Model.lean:161-164
def Conflicting (e₁ e₂ : Ev) : Prop :=
  e₁.loc = e₂.loc ∧ e₁.kind.isAccess = true ∧ e₂.kind.isAccess = true ∧
    (e₁.kind.isWrite = true ∨ e₂.kind.isWrite = true) ∧
    ¬ (e₁.kind.isAtomic = true ∧ e₂.kind.isAtomic = true)
```

#### `Race`

A data race: a conflicting pair, one event per thread, simultaneously enabled in some snapshot.

```lean
-- lean/ToySendSync/Model.lean:172-173
def Race (B A : List Ev) : Prop :=
  ∃ e₁ ∈ B, ∃ e₂ ∈ A, Conflicting e₁ e₂ ∧ Concurrent e₁ e₂
```

Positive example `race_example_write_read`:

```lean
-- lean/ToySendSync/Results.lean:13-13
theorem race_example_write_read : Race [rootEv .wr] [rootEv .rd] := …
```

Positive example `race_example_locked_vs_unlocked`:

```lean
-- lean/ToySendSync/Results.lean:33-33
theorem race_example_locked_vs_unlocked : Race [rootEv .wr [.held [] .fresh]] [rootEv .wr] := …
```

Negative example `not_race_example_read_read`:

```lean
-- lean/ToySendSync/Results.lean:17-17
theorem not_race_example_read_read : ¬ Race [rootEv .rd] [rootEv .rd] := …
```

Negative example `not_race_example_atomic_atomic`:

```lean
-- lean/ToySendSync/Results.lean:21-21
theorem not_race_example_atomic_atomic : ¬ Race [rootEv .atomic] [rootEv .atomic] := …
```

Negative example `not_race_example_locked_writes`:

```lean
-- lean/ToySendSync/Results.lean:26-27
theorem not_race_example_locked_writes :
    ¬ Race [rootEv .wr [.held [] .fresh]] [rootEv .wr [.held [] .fresh]] := …
```

#### `Acq.maker`

The thread that made an acquisition, seen from the executing thread: itself for `fresh`; for a guard's acquisition, the thread that created the guard, which in both scenarios of `SemSend`/`SemSync` is the origin thread.

```lean
-- lean/ToySendSync/Model.lean:179-181
def Acq.maker (t : Tid) : Acq → Tid
  | .fresh => t
  | .guard _ => .origin
```

#### `NoForeignRelease`

Release affinity: every acquisition that a release event executed by thread `t` releases was made by `t`. The released acquisition is named by the event's claim `held l a` on its own location `l`; other claims are preconditions. A release event without such a claim is not constrained.

```lean
-- lean/ToySendSync/Model.lean:187-188
def NoForeignRelease (t : Tid) (es : List Ev) : Prop :=
  ∀ e ∈ es, ∀ a : Acq, e.kind = .rel → Claim.held e.loc a ∈ e.claims → a.maker t = t
```

Positive example `nfr_example`:

```lean
-- lean/ToySendSync/Results.lean:46-46
theorem nfr_example : NoForeignRelease .other [rootEv .rd, rootEv .wr] := …
```

Positive example `nfr_example_fresh_release`:

```lean
-- lean/ToySendSync/Results.lean:50-50
theorem nfr_example_fresh_release : NoForeignRelease .other [rootEv .rel [.held [] .fresh]] := …
```

Positive example `nfr_example_precondition`:

```lean
-- lean/ToySendSync/Results.lean:56-57
theorem nfr_example_precondition :
    NoForeignRelease .other [⟨.rel, [0], [.held [] (.guard []), .held [0] .fresh]⟩] := …
```

Positive example (vacuous) `nfr_example_unnamed_release`:

```lean
-- lean/ToySendSync/Results.lean:102-103
theorem nfr_example_unnamed_release :
    NoForeignRelease .other [rootEv .rel []] ∧ ¬ RelNamesAcq [rootEv .rel []] := …
```

Negative example `not_nfr_example`:

```lean
-- lean/ToySendSync/Results.lean:67-67
theorem not_nfr_example : ¬ NoForeignRelease .other [rootEv .rel [.held [] (.guard [])]] := …
```

Negative example `not_nfr_example_placed`:

```lean
-- lean/ToySendSync/Results.lean:72-73
theorem not_nfr_example_placed :
    ¬ NoForeignRelease .other [⟨.rel, [0], [.held [] .fresh, .held [0] (.guard [0])]⟩] := …
```

#### `RelNamesAcq`

Every release event of a list names the acquisition it releases (a `held` claim on its own location). Every footprint satisfies it (`fp_relNamesAcq`).

```lean
-- lean/ToySendSync/Model.lean:193-194
def RelNamesAcq (es : List Ev) : Prop :=
  ∀ e ∈ es, e.kind = .rel → ∃ a : Acq, Claim.held e.loc a ∈ e.claims
```

Positive example `relNamesAcq_example`:

```lean
-- lean/ToySendSync/Results.lean:111-111
theorem relNamesAcq_example : RelNamesAcq [rootEv .rel [.held [] (.guard [])]] := …
```

Negative example `nfr_example_unnamed_release`:

```lean
-- lean/ToySendSync/Results.lean:102-103
theorem nfr_example_unnamed_release :
    NoForeignRelease .other [rootEv .rel []] ∧ ¬ RelNamesAcq [rootEv .rel []] := …
```

#### `Holder.reloc`

Relocation of a lock holder into a child position.

```lean
-- lean/ToySendSync/Model.lean:199-201
def Holder.reloc (i : Nat) : Holder → Holder
  | .thread t => .thread t
  | .guard g => .guard (i :: g)
```

#### `Acq.reloc`

Relocation of an acquisition into a child position.

```lean
-- lean/ToySendSync/Model.lean:204-206
def Acq.reloc (i : Nat) : Acq → Acq
  | .fresh => .fresh
  | .guard g => .guard (i :: g)
```

#### `Claim.reloc`

Relocation of a claim into a child position.

```lean
-- lean/ToySendSync/Model.lean:209-212
def Claim.reloc (i : Nat) : Claim → Claim
  | .held p a => .held (i :: p) (a.reloc i)
  | .via p => .via (i :: p)
  | .uniq p => .uniq (i :: p)
```

#### `Ev.place`

Placing a child event at position `i` with added root claims.

```lean
-- lean/ToySendSync/Model.lean:216-217
def Ev.place (r : List Claim) (i : Nat) (e : Ev) : Ev :=
  { kind := e.kind, loc := i :: e.loc, claims := r ++ e.claims.map (Claim.reloc i) }
```

#### `place`

Placing a list of child events.

```lean
-- lean/ToySendSync/Model.lean:220-220
def place (r : List Claim) (i : Nat) (es : List Ev) : List Ev := es.map (Ev.place r i)
```

#### `rootEv`

An event at the root location of a node.

```lean
-- lean/ToySendSync/Model.lean:223-223
def rootEv (k : Kind) (cs : List Claim := []) : Ev := ⟨k, [], cs⟩
```

#### `View`

What a user wrapper exposes through a shared reference: everything, the non-atomic reads that need no acquisition by the executing thread (`rd` events with `Ev.acquires = false`), or nothing.

```lean
-- lean/ToySendSync/Model.lean:237-241
inductive View where
  | full
  | readOnly
  | none
  deriving DecidableEq, Repr
```

#### `View.expose`

The exposed events of a view. `readOnly` keeps exactly the `rd` events that need no acquisition by the executing thread: no write, atomic read-modify-write or release, and no access under a `fresh` acquisition.

```lean
-- lean/ToySendSync/Model.lean:244-247
def View.expose : View → List Ev → List Ev
  | .full, es => es
  | .readOnly, es => es.filter (fun e => e.kind.isRead && !e.acquires)
  | .none, _ => []
```

Example `expose_readOnly_example`:

```lean
-- lean/ToySendSync/Results.lean:80-81
theorem expose_readOnly_example :
    View.expose .readOnly [rootEv .rd, rootEv .wr, rootEv .atomic, rootEv .rel] = [rootEv .rd] := …
```

Example `expose_readOnly_example_acquires`:

```lean
-- lean/ToySendSync/Results.lean:87-89
theorem expose_readOnly_example_acquires :
    View.expose .readOnly [rootEv .rd [.held [] .fresh], rootEv .rd [.held [] (.guard [])]] =
      [rootEv .rd [.held [] (.guard [])]] := …
```

Example `expose_readOnly_mutex_example`:

```lean
-- lean/ToySendSync/Results.lean:95-96
theorem expose_readOnly_mutex_example :
    View.expose .readOnly (fp (.mutex (.ref (.cell .plain)))).shr = [] := …
```

#### `Ty`

Toy types: plain data, the six library primitives, structural constructors, and user wrappers with an optional unsafe `Sync` impl.

```lean
-- lean/ToySendSync/Model.lean:255-269
inductive Ty where
  | plain
  | cell (t : Ty)
  | refCell (t : Ty)
  | rc (t : Ty)
  | arc (t : Ty)
  | mutex (t : Ty)
  | guard (t : Ty)
  | box (t : Ty)
  | ref (t : Ty)
  | refMut (t : Ty)
  | prod (a b : Ty)
  | sum (a b : Ty)
  | wrap (f : Ty) (v : View) (unsafeSync : Bool)
  deriving DecidableEq, Repr
```

#### `Fp`

A capability footprint: owner, shared-reference, and alias capabilities.

```lean
-- lean/ToySendSync/Model.lean:273-277
structure Fp where
  own : List Ev
  shr : List Ev
  alias : List Ev
  deriving Repr
```

#### `fp`

The footprint of each type. This table is the modeling content of the package: it encodes the ownership discipline (who may still act on which locations, under which claims).

```lean
-- lean/ToySendSync/Model.lean:295-340
def fp : Ty → Fp
  | .plain => ⟨[rootEv .rd, rootEv .wr], [rootEv .rd], []⟩
  | .cell t =>
    let c := fp t
    let s := [rootEv .rd, rootEv .wr] ++ place [] 0 c.own
    ⟨s, s, place [] 0 c.alias⟩
  | .refCell t =>
    let c := fp t
    let s := [rootEv .rd, rootEv .wr] ++ place [] 0 c.shr ++ place [.held [] .fresh] 0 c.own
    ⟨place [] 0 c.own ++ s, s, place [] 0 c.alias⟩
  | .rc t =>
    let c := fp t
    let h := [rootEv .rd [.via []], rootEv .wr [.via []]] ++ place [.via []] 0 c.shr ++
      place [.uniq []] 0 c.own
    ⟨h, h, h ++ place [] 0 c.alias⟩
  | .arc t =>
    let c := fp t
    let h := [rootEv .atomic [.via []]] ++ place [.via []] 0 c.shr ++ place [.uniq []] 0 c.own
    ⟨h, h, h ++ place [] 0 c.alias⟩
  | .mutex t =>
    let c := fp t
    let s := place [.held [] .fresh] 0 c.own ++ [rootEv .rel [.held [] .fresh]]
    ⟨place [] 0 c.own ++ s, s, place [] 0 c.alias⟩
  | .guard t =>
    let c := fp t
    ⟨place [.held [] (.guard [])] 0 c.own ++ [rootEv .rel [.held [] (.guard [])]],
      place [.held [] (.guard [])] 0 c.shr,
      place [.held [] .fresh] 0 c.own ++ place [] 0 c.alias⟩
  | .box t => fp t
  | .ref t =>
    let c := fp t
    ⟨c.shr, c.shr, c.shr ++ c.alias⟩
  | .refMut t => fp t
  | .prod a b =>
    let x := fp a
    let y := fp b
    ⟨place [] 0 x.own ++ place [] 1 y.own, place [] 0 x.shr ++ place [] 1 y.shr,
      place [] 0 x.alias ++ place [] 1 y.alias⟩
  | .sum a b =>
    let x := fp a
    let y := fp b
    ⟨place [] 0 x.own ++ place [] 1 y.own, place [] 0 x.shr ++ place [] 1 y.shr,
      place [] 0 x.alias ++ place [] 1 y.alias⟩
  | .wrap f v _ =>
    let c := fp f
    ⟨c.own, v.expose c.shr, c.alias⟩
```

Example `fp_cell_plain`:

```lean
-- lean/ToySendSync/Results.lean:195-198
theorem fp_cell_plain :
    fp (.cell .plain) =
      ⟨[rootEv .rd, rootEv .wr, ⟨.rd, [0], []⟩, ⟨.wr, [0], []⟩],
        [rootEv .rd, rootEv .wr, ⟨.rd, [0], []⟩, ⟨.wr, [0], []⟩], []⟩ := …
```

Example `fp_refCell_plain`:

```lean
-- lean/ToySendSync/Results.lean:203-208
theorem fp_refCell_plain :
    fp (.refCell .plain) =
      ⟨[⟨.rd, [0], []⟩, ⟨.wr, [0], []⟩, rootEv .rd, rootEv .wr, ⟨.rd, [0], []⟩,
          ⟨.rd, [0], [.held [] .fresh]⟩, ⟨.wr, [0], [.held [] .fresh]⟩],
        [rootEv .rd, rootEv .wr, ⟨.rd, [0], []⟩, ⟨.rd, [0], [.held [] .fresh]⟩,
          ⟨.wr, [0], [.held [] .fresh]⟩], []⟩ := …
```

Example `fp_shr_cell_ne_refCell_plain`:

```lean
-- lean/ToySendSync/Results.lean:211-211
theorem fp_shr_cell_ne_refCell_plain : (fp (.cell .plain)).shr ≠ (fp (.refCell .plain)).shr := …
```

#### `SemSend`

Semantic `Send`: transfer to the other thread, with the origin thread keeping the alias capabilities, admits no data race and no foreign release.

```lean
-- lean/ToySendSync/Model.lean:348-349
def SemSend (T : Ty) : Prop :=
  ¬ Race (fp T).own (fp T).alias ∧ NoForeignRelease .other (fp T).own
```

Positive example `semSend_examples`:

```lean
-- lean/ToySendSync/Results.lean:215-217
theorem semSend_examples :
    SemSend .plain ∧ SemSend (.cell .plain) ∧ SemSend (.arc .plain) ∧
      SemSend (.mutex (.cell .plain)) ∧ SemSend (.ref (.mutex (.cell .plain))) := …
```

Negative example `not_semSend_examples`:

```lean
-- lean/ToySendSync/Results.lean:224-225
theorem not_semSend_examples :
    ¬ SemSend (.rc .plain) ∧ ¬ SemSend (.guard .plain) ∧ ¬ SemSend (.ref (.cell .plain)) := …
```

#### `SemSync`

Semantic `Sync`: sharing a reference with the other thread, with the origin thread keeping shared and alias capabilities, admits no data race and no foreign release.

```lean
-- lean/ToySendSync/Model.lean:355-356
def SemSync (T : Ty) : Prop :=
  ¬ Race (fp T).shr ((fp T).shr ++ (fp T).alias) ∧ NoForeignRelease .other (fp T).shr
```

Positive example `semSync_examples`:

```lean
-- lean/ToySendSync/Results.lean:229-231
theorem semSync_examples :
    SemSync .plain ∧ SemSync (.mutex (.cell .plain)) ∧ SemSync (.arc .plain) ∧
      SemSync (.guard .plain) := …
```

Negative example `not_semSync_examples`:

```lean
-- lean/ToySendSync/Results.lean:236-237
theorem not_semSync_examples :
    ¬ SemSync (.cell .plain) ∧ ¬ SemSync (.refCell .plain) ∧ ¬ SemSync (.rc .plain) := …
```

#### `Prim`

The library primitives whose traits come from an impl table.

```lean
-- lean/ToySendSync/Model.lean:361-368
inductive Prim where
  | cell
  | refCell
  | rc
  | arc
  | mutex
  | guard
  deriving DecidableEq, Repr
```

#### `Prim.apply`

The type a primitive builds from its argument.

```lean
-- lean/ToySendSync/Model.lean:371-377
def Prim.apply : Prim → Ty → Ty
  | .cell, t => .cell t
  | .refCell, t => .refCell t
  | .rc, t => .rc t
  | .arc, t => .arc t
  | .mutex, t => .mutex t
  | .guard, t => .guard t
```

#### `Rule`

An impl-table rule: `allowed = false` is a negative impl; otherwise the impl holds when the argument has the required traits.

```lean
-- lean/ToySendSync/Model.lean:381-385
structure Rule where
  allowed : Bool
  needSend : Bool
  needSync : Bool
  deriving DecidableEq, Repr
```

#### `Rule.eval`

A rule evaluated on the argument's checker verdicts.

```lean
-- lean/ToySendSync/Model.lean:388-389
def Rule.eval (r : Rule) (s y : Bool) : Bool :=
  r.allowed && (!r.needSend || s) && (!r.needSync || y)
```

#### `Rule.Holds`

A rule's condition on propositions about the argument.

```lean
-- lean/ToySendSync/Model.lean:392-393
def Rule.Holds (r : Rule) (s y : Prop) : Prop :=
  r.allowed = true ∧ (r.needSend = true → s) ∧ (r.needSync = true → y)
```

#### `Table`

An impl table for the primitives.

```lean
-- lean/ToySendSync/Model.lean:396-398
structure Table where
  send : Prim → Rule
  sync : Prim → Rule
```

#### `stdTable`

The table mirroring the documented standard-library impls of the cited revision.

```lean
-- lean/ToySendSync/Model.lean:404-418
def stdTable : Table where
  send
    | .cell => ⟨true, true, false⟩
    | .refCell => ⟨true, true, false⟩
    | .rc => ⟨false, false, false⟩
    | .arc => ⟨true, true, true⟩
    | .mutex => ⟨true, true, false⟩
    | .guard => ⟨false, false, false⟩
  sync
    | .cell => ⟨false, false, false⟩
    | .refCell => ⟨false, false, false⟩
    | .rc => ⟨false, false, false⟩
    | .arc => ⟨true, true, true⟩
    | .mutex => ⟨true, true, false⟩
    | .guard => ⟨true, false, true⟩
```

#### `autoCheck`

The structural checker.

```lean
-- lean/ToySendSync/Model.lean:423-450
def autoCheck (tb : Table) : Ty → Bool × Bool
  | .plain => (true, true)
  | .cell t =>
    let r := autoCheck tb t
    ((tb.send .cell).eval r.1 r.2, (tb.sync .cell).eval r.1 r.2)
  | .refCell t =>
    let r := autoCheck tb t
    ((tb.send .refCell).eval r.1 r.2, (tb.sync .refCell).eval r.1 r.2)
  | .rc t =>
    let r := autoCheck tb t
    ((tb.send .rc).eval r.1 r.2, (tb.sync .rc).eval r.1 r.2)
  | .arc t =>
    let r := autoCheck tb t
    ((tb.send .arc).eval r.1 r.2, (tb.sync .arc).eval r.1 r.2)
  | .mutex t =>
    let r := autoCheck tb t
    ((tb.send .mutex).eval r.1 r.2, (tb.sync .mutex).eval r.1 r.2)
  | .guard t =>
    let r := autoCheck tb t
    ((tb.send .guard).eval r.1 r.2, (tb.sync .guard).eval r.1 r.2)
  | .box t => autoCheck tb t
  | .ref t => ((autoCheck tb t).2, (autoCheck tb t).2)
  | .refMut t => autoCheck tb t
  | .prod a b =>
    ((autoCheck tb a).1 && (autoCheck tb b).1, (autoCheck tb a).2 && (autoCheck tb b).2)
  | .sum a b =>
    ((autoCheck tb a).1 && (autoCheck tb b).1, (autoCheck tb a).2 && (autoCheck tb b).2)
  | .wrap f _ u => ((autoCheck tb f).1, u || (autoCheck tb f).2)
```

Example `autoCheck_examples`:

```lean
-- lean/ToySendSync/Results.lean:241-248
theorem autoCheck_examples :
    autoCheck stdTable (.arc .plain) = (true, true) ∧
      autoCheck stdTable (.arc (.cell .plain)) = (false, false) ∧
      autoCheck stdTable (.mutex (.cell .plain)) = (true, true) ∧
      autoCheck stdTable (.guard .plain) = (false, true) ∧
      autoCheck stdTable (.ref (.cell .plain)) = (false, false) ∧
      autoCheck stdTable (.wrap (.cell .plain) .readOnly false) = (true, false) ∧
      autoCheck stdTable (.wrap (.cell .plain) .readOnly true) = (true, true) := …
```

#### `TableSound`

Soundness of a table relative to the semantics (one direction: rule condition implies the semantic property).

```lean
-- lean/ToySendSync/Model.lean:455-458
def TableSound (tb : Table) : Prop :=
  ∀ (p : Prim) (U : Ty),
    ((tb.send p).Holds (SemSend U) (SemSync U) → SemSend (p.apply U)) ∧
    ((tb.sync p).Holds (SemSend U) (SemSync U) → SemSync (p.apply U))
```

Negative example `not_tableSound_rcSendTable`:

```lean
-- lean/ToySendSync/Results.lean:992-992
theorem not_tableSound_rcSendTable : ¬ TableSound rcSendTable := …
```

Positive example (no positive rule) `tableSound_noImplTable`:

```lean
-- lean/ToySendSync/Results.lean:620-620
theorem tableSound_noImplTable : TableSound noImplTable := …
```

#### `ImplsSound`

Every unsafe `Sync` impl on a wrapper node inside `T` is semantically justified.

```lean
-- lean/ToySendSync/Model.lean:461-474
def ImplsSound : Ty → Prop
  | .plain => True
  | .cell t => ImplsSound t
  | .refCell t => ImplsSound t
  | .rc t => ImplsSound t
  | .arc t => ImplsSound t
  | .mutex t => ImplsSound t
  | .guard t => ImplsSound t
  | .box t => ImplsSound t
  | .ref t => ImplsSound t
  | .refMut t => ImplsSound t
  | .prod a b => ImplsSound a ∧ ImplsSound b
  | .sum a b => ImplsSound a ∧ ImplsSound b
  | .wrap f v u => (u = true → SemSync (.wrap f v u)) ∧ ImplsSound f
```

Examples `implsSound_examples`:

```lean
-- lean/ToySendSync/Results.lean:998-999
theorem implsSound_examples :
    ImplsSound (.wrap (.cell .plain) .readOnly true) ∧ ¬ ImplsSound (.wrap (.cell .plain) .full true) := …
```

#### `WrapFree`

`T` contains no user wrapper.

```lean
-- lean/ToySendSync/Model.lean:477-490
def WrapFree : Ty → Prop
  | .plain => True
  | .cell t => WrapFree t
  | .refCell t => WrapFree t
  | .rc t => WrapFree t
  | .arc t => WrapFree t
  | .mutex t => WrapFree t
  | .guard t => WrapFree t
  | .box t => WrapFree t
  | .ref t => WrapFree t
  | .refMut t => WrapFree t
  | .prod a b => WrapFree a ∧ WrapFree b
  | .sum a b => WrapFree a ∧ WrapFree b
  | .wrap _ _ _ => False
```

Examples `wrapFree_examples`:

```lean
-- lean/ToySendSync/Results.lean:1004-1004
theorem wrapFree_examples : WrapFree (.arc (.mutex (.cell .plain))) ∧ ¬ WrapFree (.wrap .plain .full false) := …
```

#### `SyncObligation`

The proof obligation of an unsafe `Sync` impl on a wrapper, as an explicit invariant.

```lean
-- lean/ToySendSync/Model.lean:497-500
def SyncObligation (f : Ty) (v : View) : Prop :=
  (∀ e₁ ∈ v.expose (fp f).shr, ∀ e₂ ∈ v.expose (fp f).shr ++ (fp f).alias,
      Conflicting e₁ e₂ → ¬ Concurrent e₁ e₂) ∧
    NoForeignRelease .other (v.expose (fp f).shr)
```

Negative example `not_syncObligation_cell_full`:

```lean
-- lean/ToySendSync/Results.lean:1008-1008
theorem not_syncObligation_cell_full : ¬ SyncObligation (.cell .plain) .full := …
```

#### `OwnReadsRaceFree`

Reads through the owner capabilities of `U` that a read-only view keeps (other thread) race with no alias capability of `U` (origin thread): the condition on the content of a `Cell<U>` under a read-only wrapper.

```lean
-- lean/ToySendSync/Model.lean:507-508
def OwnReadsRaceFree (U : Ty) : Prop :=
  ¬ Race (View.expose .readOnly (fp U).own) (fp U).alias
```

Examples `ownReadsRaceFree_examples`:

```lean
-- lean/ToySendSync/Results.lean:264-266
theorem ownReadsRaceFree_examples :
    OwnReadsRaceFree .plain ∧ OwnReadsRaceFree (.guard .plain) ∧
      ¬ OwnReadsRaceFree (.ref (.cell .plain)) ∧ ¬ OwnReadsRaceFree (.rc .plain) := …
```

#### `ShrReadsRaceFree`

Reads through the shared capabilities of `U` that a read-only view keeps (other thread) race with no alias capability of `U` (origin thread): the condition on the content of a `RefCell<U>` under a read-only wrapper.

```lean
-- lean/ToySendSync/Model.lean:515-516
def ShrReadsRaceFree (U : Ty) : Prop :=
  ¬ Race (View.expose .readOnly (fp U).shr) (fp U).alias
```

Examples `shrReadsRaceFree_examples`:

```lean
-- lean/ToySendSync/Results.lean:277-279
theorem shrReadsRaceFree_examples :
    ShrReadsRaceFree .plain ∧ ShrReadsRaceFree (.wrap (.ref (.cell .plain)) .none false) ∧
      ¬ ShrReadsRaceFree (.ref (.cell .plain)) ∧ ¬ ShrReadsRaceFree (.rc .plain) := …
```

#### `rcSendTable`

A deliberately unsound table (declares `Rc<T>: Send`).

```lean
-- lean/ToySendSync/Results.lean:652-652
def rcSendTable : Table := { stdTable with send := fun p => if p = .rc then ⟨true, false, false⟩ else stdTable.send p }
```

#### `noImplTable`

A table with no positive rule.

```lean
-- lean/ToySendSync/Results.lean:617-617
def noImplTable : Table := ⟨fun _ => ⟨false, false, false⟩, fun _ => ⟨false, false, false⟩⟩
```

### Card `link-sync-iff-ref-send`

**Plain claim.** For every toy type `T`, `SemSync T` holds if and only if `SemSend (.ref T)` holds, with no assumption: the footprint of `.ref T` is defined from the shared footprint of `T` (`own := shr T`, `alias := shr T ++ alias T`), and the equivalence holds by `Iff.rfl`. Companions, for every toy type `U`: `SemSync (.ref U)` holds if and only if `SemSync U` holds (`semSync_ref_iff`, a short race decomposition); `SemSend (.refMut U)` holds if and only if `SemSend U` holds, and `SemSync (.refMut U)` holds if and only if `SemSync U` holds (`semSend_refMut_iff`, `semSync_refMut_iff`, both by `Iff.rfl` because `fp (.refMut U)` is defined as `fp U`).

**Kind.** characterization. **Tier.** T0. **Depth.** definitional.

Statement (`semSync_iff_semSend_ref`):

```lean
-- lean/ToySendSync/Results.lean:290-290
theorem semSync_iff_semSend_ref (T : Ty) : SemSync T ↔ SemSend (.ref T) := …
```

Companion (`semSync_ref_iff`):

```lean
-- lean/ToySendSync/Characterize.lean:142-142
theorem semSync_ref_iff (U : Ty) : SemSync (.ref U) ↔ SemSync U := …
```

Companion (`semSend_refMut_iff`):

```lean
-- lean/ToySendSync/Characterize.lean:138-138
theorem semSend_refMut_iff (U : Ty) : SemSend (.refMut U) ↔ SemSend U := …
```

Companion (`semSync_refMut_iff`):

```lean
-- lean/ToySendSync/Characterize.lean:140-140
theorem semSync_refMut_iff (U : Ty) : SemSync (.refMut U) ↔ SemSync U := …
```

Explicit form of the left-hand side of `semSync_iff_semSend_ref`:

```lean
¬ Race (fp T).shr ((fp T).shr ++ (fp T).alias) ∧ NoForeignRelease .other (fp T).shr
```

Explicit form of the right-hand side of `semSync_iff_semSend_ref`:

```lean
¬ Race (fp (.ref T)).own (fp (.ref T)).alias ∧ NoForeignRelease .other (fp (.ref T)).own
```

Explicit form of the right-hand side of `semSync_iff_semSend_ref` with `fp (.ref T)` reduced (`(fp (.ref T)).own` is `(fp T).shr` and `(fp (.ref T)).alias` is `(fp T).shr ++ (fp T).alias` by definition, so this is literally the left-hand side):

```lean
¬ Race (fp T).shr ((fp T).shr ++ (fp T).alias) ∧ NoForeignRelease .other (fp T).shr
```

**Hypothesis ledger.** No hypotheses beyond the universally quantified variables.

**Non-vacuity witness.** `.plain` satisfies both sides. (`semSync_iff_semSend_ref_nonvacuous`)

```lean
-- lean/ToySendSync/Results.lean:293-293
theorem semSync_iff_semSend_ref_nonvacuous : SemSync .plain ∧ SemSend (.ref .plain) := …
```

**Non-claims.** Listed under **Boundaries** (global non-claims, then *Non-claims of each result*, `link-sync-iff-ref-send`); read them before relying on this result.

**Prior art.**

* Rust core library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/core/src/marker.rs: `pub unsafe auto trait Send` (line 92); `impl<T: PointeeSized> !Send for *const T {}` (line 97); `unsafe impl<T: Sync + PointeeSized> Send for &T {}` (line 105); `Sync` documentation (lines 511-539): "The precise definition is: a type `T` is [`Sync`] if and only if `&T` is [`Send`]", "`&mut T` is [`Send`] if and only if `T` is [`Send`]", "`&T` and `&mut T` are [`Sync`] if and only if `T` is [`Sync`]"; `pub unsafe auto trait Sync` (line 657); `impl<T: PointeeSized> !Sync for *const T {}` (line 672).
* Ralf Jung, Jacques-Henri Jourdan, Robbert Krebbers, Derek Dreyer. "RustBelt: Securing the Foundations of the Rust Programming Language." Proc. ACM Program. Lang. 2(POPL), Article 66, January 2018. DOI 10.1145/3158154. Section 1.2 (Challenge #3) and Section 4.1: a type is Send if its ownership predicate does not depend on the thread-identifier parameter; Section 4.3 ("Interpreting shared references"): Sync means that the sharing predicate does not depend on the thread identifier, and the ownership predicate of a shared reference is defined from the sharing predicate; Section 2.5.1: "&T is Send if and only if T is Sync". RustBelt's predicates are thread-indexed Iris predicates, not race-freedom scenarios as in this package.
* The Rustonomicon, chapter "Send and Sync", rust-lang/nomicon commit b0bb569883a3e65ab19d4f1adf1b8dbc1629d0a6, src/send-and-sync.md: lines 8-9 ("A type is Send if it is safe to send it to another thread"; "T is Sync if and only if `&T` is Send"); lines 20-29 (automatic derivation; `Cell`/`RefCell` not Sync; `Rc` neither); lines 177-205 (the obligations argued for `unsafe impl Send`/`Sync` on the `Carton` example).
* Rust RFC 0458 "Send Improvements", rust-lang/rfcs commit f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4, text/0458-send-improvements.md (start date 2014-11-10): makes `&T` `Send` if and only if `T` is `Sync` (lines 11-16, with `unsafe impl<'a, T> Send for &'a T where T: Sync + 'a {}` at line 15), and argues with its `RcMut` example (line 95; code at lines 169-182) that `Sync` does not imply `Send`.

**Design question.** Rust's `Send` and `Sync` are auto traits computed structurally with manual unsafe impls, and `T: Sync` is defined as `&T: Send`. What does each trait certify in a model with threads, shared references and interior mutability; when are the structural rules sound; which primitives need opt-outs/opt-ins and why; and which tempting rules are false?

Basis: execution (Lean kernel check) — every Lean statement quoted in this card (main theorem, companions, counterexamples, non-vacuity witness and positive control) is kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — **Claim:** the model's link between `SemSync T` and `SemSend (.ref T)` mirrors the documented definition of `Sync` ("a type `T` is `Sync` if and only if `&T` is `Send`"). **Reasoning:** the footprint of `.ref T` gives the receiving thread the shared capabilities of `T` and makes the lender's shared and alias capabilities the concurrent party; the link then holds by definition, so the agreement is a design choice of the model, not evidence about rustc. **Sources:** the `marker.rs` lines and RustBelt sections listed under **Prior art** above. This claim is not established by the Lean kernel.

### Card `structural-soundness`

**Plain claim.** For every impl table `tb` with `TableSound tb` (each primitive rule, when its condition holds of the argument's semantic `SemSend`/`SemSync`, yields the semantic property of the primitive type) and every toy type `T` with `ImplsSound T` (every unsafe `Sync` impl on a wrapper node of `T` is semantically justified), `(autoCheck tb T).1 = true` implies `SemSend T` and `(autoCheck tb T).2 = true` implies `SemSync T`. Corollary (`autoCheck_std_sound_of_implsSound`): for every toy type `T` with `ImplsSound T`, the same two implications hold for `stdTable`. Step lemma (`rule_holds_of_eval`): if a rule evaluates to `true` on Boolean verdicts that imply propositions `S` and `Y`, its propositional condition holds of `S` and `Y`.

**Kind.** theorem. **Tier.** T0. **Depth.** shallow.

Statement (`autoCheck_sound_of_tableSound_of_implsSound`):

```lean
-- lean/ToySendSync/Results.lean:528-530
theorem autoCheck_sound_of_tableSound_of_implsSound (tb : Table) (htb : TableSound tb) :
    ∀ T : Ty, ImplsSound T →
      ((autoCheck tb T).1 = true → SemSend T) ∧ ((autoCheck tb T).2 = true → SemSync T) := …
```

Companion (`autoCheck_std_sound_of_implsSound`):

```lean
-- lean/ToySendSync/Results.lean:671-672
theorem autoCheck_std_sound_of_implsSound (T : Ty) (hT : ImplsSound T) :
    ((autoCheck stdTable T).1 = true → SemSend T) ∧ ((autoCheck stdTable T).2 = true → SemSync T) := …
```

Companion (`rule_holds_of_eval`):

```lean
-- lean/ToySendSync/Results.lean:519-520
theorem rule_holds_of_eval {r : Rule} {s y : Bool} {S Y : Prop} (hs : s = true → S)
    (hy : y = true → Y) (h : r.eval s y = true) : r.Holds S Y := …
```

Companion (`rcSendTable`): quoted in the Definitions section above.

Companion (`TableSound`): quoted in the Definitions section above.

Companion (`ImplsSound`): quoted in the Definitions section above.

Unfolded (prose):

```text
Proof outline: induction on `T`. Primitive nodes use `TableSound` (rule conditions
are conjunctions of required argument traits, hence monotone); wrapper nodes use
`ImplsSound` when the flag is set and `semSync_wrap_of_semSync` otherwise; the other
nodes use the per-constructor characterizations.
```

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `htb : TableSound tb` | The table's declared impls for the primitives must be semantically sound. | tight | `autoCheck_sound_tableSound_tight` | a concrete table (`rcSendTable`) and a concrete type (`.rc .plain`) |
| `ImplsSound T` | Unsafe `Sync` impls on wrappers bypass the structural rule and must be justified. | tight | `autoCheck_sound_implsSound_tight` | a concrete wrapper type (`.wrap (.cell .plain) .full true`) with `stdTable` |

Counterexample `autoCheck_sound_tableSound_tight`:

```lean
-- lean/ToySendSync/Results.lean:657-659
theorem autoCheck_sound_tableSound_tight :
    ImplsSound (.rc .plain) ∧ (autoCheck rcSendTable (.rc .plain)).1 = true ∧
      ¬ SemSend (.rc .plain) := …
```

Counterexample `autoCheck_sound_implsSound_tight`:

```lean
-- lean/ToySendSync/Results.lean:665-667
theorem autoCheck_sound_implsSound_tight :
    TableSound stdTable ∧ (autoCheck stdTable (.wrap (.cell .plain) .full true)).2 = true ∧
      ¬ SemSync (.wrap (.cell .plain) .full true) := …
```

**Non-vacuity witness.** `stdTable` with `T = .arc (.mutex (.cell .plain))`, which the checker accepts for both traits. (`autoCheck_sound_nonvacuous`)

```lean
-- lean/ToySendSync/Results.lean:646-648
theorem autoCheck_sound_nonvacuous :
    TableSound stdTable ∧ ImplsSound (.arc (.mutex (.cell .plain))) ∧
      autoCheck stdTable (.arc (.mutex (.cell .plain))) = (true, true) := …
```

**Non-claims.** Listed under **Boundaries** (global non-claims, then *Non-claims of each result*, `structural-soundness`); read them before relying on this result.

**Prior art.**

* The Rust Reference, rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c, src/special-types-and-traits.md, rules `lang-types.auto-traits.*` (lines 156-181): automatic implementation for `&T`, `&mut T` and aggregates ("Structs, enums, unions, and tuples implement the trait if all of their fields do"), suppression of the automatic implementation by a generic impl ("the standard library implements `Send` for all `&T` where `T` is `Sync`"), and negative impls.
* The Rustonomicon, chapter "Send and Sync", rust-lang/nomicon commit b0bb569883a3e65ab19d4f1adf1b8dbc1629d0a6, src/send-and-sync.md: lines 8-9 ("A type is Send if it is safe to send it to another thread"; "T is Sync if and only if `&T` is Send"); lines 20-29 (automatic derivation; `Cell`/`RefCell` not Sync; `Rc` neither); lines 177-205 (the obligations argued for `unsafe impl Send`/`Sync` on the `Carton` example).
* RustBelt (Jung, Jourdan, Krebbers, Dreyer, POPL 2018, DOI 10.1145/3158154), Section 1.2 and Section 6: a Coq proof of the soundness of the type system (fundamental theorem and adequacy, Section 7) and of the verification conditions of libraries that use unsafe code, including `Arc`, `Rc`, `Cell`, `RefCell`, `Mutex` and `RwLock`; Section 6.1 notes that its model of `Cell<T>` is never Sync and that "Cell<T> is Send if and only if T is"; Section 6.2 concludes that `mutex(τ)` is both Send and Sync when τ is Send. RustBelt proves sufficiency (soundness of the impls and typing rules); it does not state impossibility theorems of the form proved here.
* Rust RFC 0019 "Opt-in Built-in Traits", rust-lang/rfcs commit f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4, text/0019-opt-in-builtin-traits.md (start date 2014-09-18): `Send` and `Share` (later renamed `Sync`) become library traits with default (structural) impls and negative impls.

**Design question.** Rust's `Send` and `Sync` are auto traits computed structurally with manual unsafe impls, and `T: Sync` is defined as `&T: Send`. What does each trait certify in a model with threads, shared references and interior mutability; when are the structural rules sound; which primitives need opt-outs/opt-ins and why; and which tempting rules are false?

Basis: execution (Lean kernel check) — every Lean statement quoted in this card (main theorem, companions, counterexamples, non-vacuity witness and positive control) is kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — **Claim:** `autoCheck` follows the documented auto-trait rules for the constructors of `Ty`, so the theorem reads as: in the model, structural derivation is sound when the primitive impls are sound and every unsafe `Sync` impl is justified. **Reasoning:** the Rust Reference documents that structs, enums, unions and tuples implement an auto trait if all their fields do, that `&T` and `&mut T` follow fixed rules, and that a generic impl replaces the automatic one; `autoCheck` encodes these rules for `.prod`, `.sum`, `.box`, `.ref`, `.refMut` and `.wrap`. The rules for features absent from `Ty` (see **Applicability**) are not covered. **Sources:** the Reference lines and RFC listed under **Prior art** above. This claim is not established by the Lean kernel.

### Card `std-table-sound`

**Plain claim.** The table `stdTable` (`Cell`/`RefCell`: `Send` if the argument is `Send`, never `Sync`; `Rc`: neither; `Arc`: both if the argument is `Send` and `Sync`; `Mutex`: both if the argument is `Send`; `MutexGuard`: never `Send`, `Sync` if the argument is `Sync`) satisfies `TableSound`. Each of its seven positive rules (`allowed = true`) has its condition met at the argument `plain`, and the primitive over `plain` then has the semantic property (`stdTable_positive_rules_nonvacuous`). Companion (`autoCheck_std_cell_eq_refCell`): for every toy type `U`, `autoCheck stdTable (.cell U) = autoCheck stdTable (.refCell U)`, by `rfl`.

**Kind.** theorem. **Tier.** T0. **Depth.** shallow.

Statement (`stdTable_sound`):

```lean
-- lean/ToySendSync/Results.lean:599-599
theorem stdTable_sound : TableSound stdTable := …
```

Companion (`stdTable`): quoted in the Definitions section above.

Companion (`stdTable_positive_rules_nonvacuous`):

```lean
-- lean/ToySendSync/Results.lean:626-631
theorem stdTable_positive_rules_nonvacuous :
    ∀ p : Prim,
      ((stdTable.send p).allowed = true →
          (stdTable.send p).Holds (SemSend .plain) (SemSync .plain) ∧ SemSend (p.apply .plain)) ∧
      ((stdTable.sync p).allowed = true →
          (stdTable.sync p).Holds (SemSend .plain) (SemSync .plain) ∧ SemSync (p.apply .plain)) := …
```

Companion (`tableSound_noImplTable`):

```lean
-- lean/ToySendSync/Results.lean:620-620
theorem tableSound_noImplTable : TableSound noImplTable := …
```

Companion (`noImplTable`): quoted in the Definitions section above.

Companion (`autoCheck_std_cell_eq_refCell`):

```lean
-- lean/ToySendSync/Results.lean:640-641
theorem autoCheck_std_cell_eq_refCell (U : Ty) :
    autoCheck stdTable (.cell U) = autoCheck stdTable (.refCell U) := …
```

**Hypothesis ledger.** No hypotheses beyond the universally quantified variables.

**Non-vacuity witness.** Closed statement; the seven positive rules fire at argument `plain` with true conclusions. (`stdTable_positive_rules_nonvacuous`)

**Non-claims.** Listed under **Boundaries** (global non-claims, then *Non-claims of each result*, `std-table-sound`); read them before relying on this result.

**Prior art.**

* Rust core library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/core/src/cell.rs: `unsafe impl<T: ?Sized> Send for Cell<T> where T: Send {}` (line 320); `impl<T: ?Sized> !Sync for Cell<T> {}` (line 328); `unsafe impl<T: ?Sized> Send for RefCell<T> where T: Send {}` (line 1439); `impl<T: ?Sized> !Sync for RefCell<T> {}` (line 1442).
* Rust core library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/core/src/cell.rs: `impl<T: ?Sized> !Sync for UnsafeCell<T> {}` (line 2316); lines 322-326 note that `Cell`'s explicit negative impl is redundant because `Cell` wraps `UnsafeCell`.
* Rust alloc library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/alloc/src/rc.rs: `impl<T: ?Sized, A: Allocator> !Send for Rc<T, A> {}` (line 334); `impl<T: ?Sized, A: Allocator> !Sync for Rc<T, A> {}` (line 342); and library/core/src/marker.rs lines 74-79 (the `Send` documentation's example of two threads updating an `Rc` reference count).
* Rust alloc library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/alloc/src/sync.rs: `unsafe impl<T: ?Sized + Sync + Send, A: Allocator + Send + Sync> Send for Arc<T, A> {}` (line 284) and the same bounds for `Sync` (line 286); the "Thread Safety" documentation (lines 124-147) explains with `Arc<RefCell<T>>` why `T: Sync` is required.
* Rust std library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/std/src/sync/poison/mutex.rs: `unsafe impl<T: ?Sized + Send> Send for Mutex<T> {}` (line 238, rationale lines 233-235: the owned `T` can be acquired via `into_inner`); `unsafe impl<T: ?Sized + Send> Sync for Mutex<T> {}` (line 257, rationale lines 240-254, citing `Mutex<Rc<_>>` and noting "it is not necessary for `T` to be `Sync`").
* Rust std library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/std/src/sync/poison/mutex.rs: `impl<T: ?Sized> !Send for MutexGuard<'_, T> {}` (line 289; lines 282-287: "On platforms that use POSIX threads ... there is a requirement to release mutex locks on the same thread they were acquired"); `unsafe impl<T: ?Sized + Sync> Sync for MutexGuard<'_, T> {}` (line 294; lines 291-292: a `&T` is obtainable from `&MutexGuard` via `Deref`).
* Rust std library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/std/src/sync/poison/rwlock.rs: `unsafe impl<T: ?Sized + Send> Send for RwLock<T> {}` (line 104); `unsafe impl<T: ?Sized + Send + Sync> Sync for RwLock<T> {}` (line 107); `RwLockReadGuard` and `RwLockWriteGuard` are `!Send` (lines 140, 168) and `Sync` when `T: Sync` (lines 143, 171).
* RustBelt (Jung, Jourdan, Krebbers, Dreyer, POPL 2018, DOI 10.1145/3158154), Section 1.2 and Section 6: a Coq proof of the soundness of the type system (fundamental theorem and adequacy, Section 7) and of the verification conditions of libraries that use unsafe code, including `Arc`, `Rc`, `Cell`, `RefCell`, `Mutex` and `RwLock`; Section 6.1 notes that its model of `Cell<T>` is never Sync and that "Cell<T> is Send if and only if T is"; Section 6.2 concludes that `mutex(τ)` is both Send and Sync when τ is Send. RustBelt proves sufficiency (soundness of the impls and typing rules); it does not state impossibility theorems of the form proved here.
* Hoang-Hai Dang, Jacques-Henri Jourdan, Jan-Oliver Kaiser, Derek Dreyer. "RustBelt Meets Relaxed Memory." Proc. ACM Program. Lang. 4(POPL), Article 34, January 2020. DOI 10.1145/3371102. Section 1 and Section 5.3: re-verifies RustBelt's library proofs, including `Arc`, under a relaxed-memory semantics. The model here has no memory orderings.

**Design question.** Rust's `Send` and `Sync` are auto traits computed structurally with manual unsafe impls, and `T: Sync` is defined as `&T: Send`. What does each trait certify in a model with threads, shared references and interior mutability; when are the structural rules sound; which primitives need opt-outs/opt-ins and why; and which tempting rules are false?

Basis: execution (Lean kernel check) — every Lean statement quoted in this card (main theorem, companions, counterexamples, non-vacuity witness and positive control) is kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — **Claim:** `stdTable` transcribes the documented impl bounds of `Cell`, `RefCell`, `Rc`, `Arc`, `Mutex` and `MutexGuard` at `rust-lang/rust` tag `1.100.0`, and the theorem shows that these bounds are sound for the model's footprints of those types. **Reasoning:** each rule of `stdTable` was compared with the impl declaration lines listed under **Prior art** above. Soundness for the real types depends on whether the footprints capture their APIs, which is not proved. **Sources:** the `cell.rs`, `rc.rs`, `sync.rs` and `mutex.rs` lines listed under **Prior art** above. This claim is not established by the Lean kernel.

### Card `std-checker-exact-wrap-free`

**Plain claim.** For every toy type `T` with `WrapFree T` (no user wrapper node), `(autoCheck stdTable T).1 = true` holds if and only if `SemSend T`, and `(autoCheck stdTable T).2 = true` holds if and only if `SemSync T`.

**Kind.** characterization. **Tier.** T1. **Depth.** shallow.

Statement (`autoCheck_std_exact_of_wrapFree`):

```lean
-- lean/ToySendSync/Results.lean:677-679
theorem autoCheck_std_exact_of_wrapFree :
    ∀ T : Ty, WrapFree T →
      ((autoCheck stdTable T).1 = true ↔ SemSend T) ∧ ((autoCheck stdTable T).2 = true ↔ SemSync T) := …
```

Companion (`WrapFree`): quoted in the Definitions section above.

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `WrapFree T` | User wrappers can restrict their shared API below what the structural rule assumes. | tight | `autoCheck_std_exact_wrapFree_tight` | a concrete type with one wrapper node (`.wrap (.cell .plain) .readOnly false`) |

Counterexample `autoCheck_std_exact_wrapFree_tight`:

```lean
-- lean/ToySendSync/Results.lean:760-762
theorem autoCheck_std_exact_wrapFree_tight :
    ¬ ((autoCheck stdTable (.wrap (.cell .plain) .readOnly false)).2 = true ↔
        SemSync (.wrap (.cell .plain) .readOnly false)) := …
```

**Non-vacuity witness.** `.arc (.mutex (.cell .plain))` is wrapper-free. (`autoCheck_std_exact_nonvacuous`)

```lean
-- lean/ToySendSync/Results.lean:756-756
theorem autoCheck_std_exact_nonvacuous : WrapFree (.arc (.mutex (.cell .plain))) := …
```

**Non-claims.** Listed under **Boundaries** (global non-claims, then *Non-claims of each result*, `std-checker-exact-wrap-free`); read them before relying on this result.

**Prior art.**

* Rust core library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/core/src/cell.rs: `unsafe impl<T: ?Sized> Send for Cell<T> where T: Send {}` (line 320); `impl<T: ?Sized> !Sync for Cell<T> {}` (line 328); `unsafe impl<T: ?Sized> Send for RefCell<T> where T: Send {}` (line 1439); `impl<T: ?Sized> !Sync for RefCell<T> {}` (line 1442).
* Rust alloc library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/alloc/src/rc.rs: `impl<T: ?Sized, A: Allocator> !Send for Rc<T, A> {}` (line 334); `impl<T: ?Sized, A: Allocator> !Sync for Rc<T, A> {}` (line 342); and library/core/src/marker.rs lines 74-79 (the `Send` documentation's example of two threads updating an `Rc` reference count).
* Rust alloc library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/alloc/src/sync.rs: `unsafe impl<T: ?Sized + Sync + Send, A: Allocator + Send + Sync> Send for Arc<T, A> {}` (line 284) and the same bounds for `Sync` (line 286); the "Thread Safety" documentation (lines 124-147) explains with `Arc<RefCell<T>>` why `T: Sync` is required.
* Rust std library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/std/src/sync/poison/mutex.rs: `unsafe impl<T: ?Sized + Send> Send for Mutex<T> {}` (line 238, rationale lines 233-235: the owned `T` can be acquired via `into_inner`); `unsafe impl<T: ?Sized + Send> Sync for Mutex<T> {}` (line 257, rationale lines 240-254, citing `Mutex<Rc<_>>` and noting "it is not necessary for `T` to be `Sync`").
* Rust std library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/std/src/sync/poison/mutex.rs: `impl<T: ?Sized> !Send for MutexGuard<'_, T> {}` (line 289; lines 282-287: "On platforms that use POSIX threads ... there is a requirement to release mutex locks on the same thread they were acquired"); `unsafe impl<T: ?Sized + Sync> Sync for MutexGuard<'_, T> {}` (line 294; lines 291-292: a `&T` is obtainable from `&MutexGuard` via `Deref`).
* Rust core library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/core/src/marker.rs: `pub unsafe auto trait Send` (line 92); `impl<T: PointeeSized> !Send for *const T {}` (line 97); `unsafe impl<T: Sync + PointeeSized> Send for &T {}` (line 105); `Sync` documentation (lines 511-539): "The precise definition is: a type `T` is [`Sync`] if and only if `&T` is [`Send`]", "`&mut T` is [`Send`] if and only if `T` is [`Send`]", "`&T` and `&mut T` are [`Sync`] if and only if `T` is [`Sync`]"; `pub unsafe auto trait Sync` (line 657); `impl<T: PointeeSized> !Sync for *const T {}` (line 672).

**Design question.** Rust's `Send` and `Sync` are auto traits computed structurally with manual unsafe impls, and `T: Sync` is defined as `&T: Send`. What does each trait certify in a model with threads, shared references and interior mutability; when are the structural rules sound; which primitives need opt-outs/opt-ins and why; and which tempting rules are false?

Basis: execution (Lean kernel check) — every Lean statement quoted in this card (main theorem, companions, counterexamples, non-vacuity witness and positive control) is kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — **Claim:** within the model, the transcribed standard-library bounds are neither more permissive nor stricter than the semantic properties on types without user wrappers. **Reasoning:** the theorem gives both directions for every `WrapFree` toy type; for a Rust type built from the modelled constructors, the conclusion transfers to the extent that the footprints capture the real APIs, which is not proved. **Sources:** the impl declarations listed under **Prior art** above. This claim is not established by the Lean kernel.

### Card `cell-send-iff`

**Plain claim.** For every toy type `U`, `SemSend (.cell U)` holds if and only if `SemSend U` holds; the same holds for `.refCell U` (`semSend_refCell_iff`). Consequently, for every toy type `U`, `SemSend (.cell U)` holds if and only if `SemSend (.refCell U)` holds, and `SemSync (.cell U)` holds if and only if `SemSync (.refCell U)` holds (`cell_refCell_semSend_semSync_agree`; both sides of the second fail, by `not_semSync_cell` and `not_semSync_refCell`). Instance: `Cell<plain>` is semantically `Send` and not semantically `Sync` (`cell_plain_semSend_not_semSync`).

**Kind.** characterization. **Tier.** T0. **Depth.** shallow.

Statement (`semSend_cell_iff`):

```lean
-- lean/ToySendSync/Characterize.lean:19-19
theorem semSend_cell_iff (U : Ty) : SemSend (.cell U) ↔ SemSend U := …
```

Companion (`semSend_refCell_iff`):

```lean
-- lean/ToySendSync/Characterize.lean:28-28
theorem semSend_refCell_iff (U : Ty) : SemSend (.refCell U) ↔ SemSend U := …
```

Companion (`cell_plain_semSend_not_semSync`):

```lean
-- lean/ToySendSync/Results.lean:299-299
theorem cell_plain_semSend_not_semSync : SemSend (.cell .plain) ∧ ¬ SemSync (.cell .plain) := …
```

Companion (`cell_refCell_semSend_semSync_agree`):

```lean
-- lean/ToySendSync/Results.lean:305-306
theorem cell_refCell_semSend_semSync_agree (U : Ty) :
    (SemSend (.cell U) ↔ SemSend (.refCell U)) ∧ (SemSync (.cell U) ↔ SemSync (.refCell U)) := …
```

**Hypothesis ledger.** No hypotheses beyond the universally quantified variables.

**Non-vacuity witness.** `U = .plain`: `Cell<plain>` is semantically `Send`. (`cell_plain_semSend_not_semSync`)

**Non-claims.** Listed under **Boundaries** (global non-claims, then *Non-claims of each result*, `cell-send-iff`); read them before relying on this result.

**Prior art.**

* Rust core library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/core/src/cell.rs: `unsafe impl<T: ?Sized> Send for Cell<T> where T: Send {}` (line 320); `impl<T: ?Sized> !Sync for Cell<T> {}` (line 328); `unsafe impl<T: ?Sized> Send for RefCell<T> where T: Send {}` (line 1439); `impl<T: ?Sized> !Sync for RefCell<T> {}` (line 1442).
* Rust core library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/core/src/cell.rs: `Cell::set` (line 436, in `impl<T> Cell<T>` at line 404), `Cell::replace` (line 513), `Cell::get` (line 555, in `impl<T: Copy> Cell<T>` at line 539), `Cell::take` (line 674): every one takes `&self` and moves, copies or drops the content; `RefCell::try_borrow_unguarded` (line 1395, an `unsafe fn`) reads the borrow flag (line 1396) without updating it.
* Rust core library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/core/src/cell.rs: `pub struct RefCell<T: ?Sized>` (line 852) has the borrow flag field `borrow: Cell<BorrowCounter>` (line 853); `RefCell::borrow(&self) -> Ref<'_, T>` (line 1124, through `try_borrow` at line 1161) and `RefCell::borrow_mut(&self) -> RefMut<'_, T>` (line 1224, through `try_borrow_mut` at line 1258) update the flag; `RefCell::replace` (line 1028, body `mem::replace(&mut self.borrow_mut(), t)` at line 1029), `replace_with` (line 1052), `swap` (line 1082) and `take` (line 1433, which calls `replace`) borrow mutably; `RefCell::get_mut(&mut self)` (line 1333) and `into_inner(self)` (line 998) reach the content without the flag; `RefCell::try_borrow_unguarded` (line 1395, an `unsafe fn`) reads the flag (line 1396) without updating it.
* RustBelt (Jung, Jourdan, Krebbers, Dreyer, POPL 2018, DOI 10.1145/3158154), Section 1.2 and Section 6: a Coq proof of the soundness of the type system (fundamental theorem and adequacy, Section 7) and of the verification conditions of libraries that use unsafe code, including `Arc`, `Rc`, `Cell`, `RefCell`, `Mutex` and `RwLock`; Section 6.1 notes that its model of `Cell<T>` is never Sync and that "Cell<T> is Send if and only if T is"; Section 6.2 concludes that `mutex(τ)` is both Send and Sync when τ is Send. RustBelt proves sufficiency (soundness of the impls and typing rules); it does not state impossibility theorems of the form proved here.
* The Rustonomicon, chapter "Send and Sync", rust-lang/nomicon commit b0bb569883a3e65ab19d4f1adf1b8dbc1629d0a6, src/send-and-sync.md: lines 8-9 ("A type is Send if it is safe to send it to another thread"; "T is Sync if and only if `&T` is Send"); lines 20-29 (automatic derivation; `Cell`/`RefCell` not Sync; `Rc` neither); lines 177-205 (the obligations argued for `unsafe impl Send`/`Sync` on the `Carton` example).

**Design question.** Rust's `Send` and `Sync` are auto traits computed structurally with manual unsafe impls, and `T: Sync` is defined as `&T: Send`. What does each trait certify in a model with threads, shared references and interior mutability; when are the structural rules sound; which primitives need opt-outs/opt-ins and why; and which tempting rules are false?

Basis: execution (Lean kernel check) — every Lean statement quoted in this card (main theorem, companions, counterexamples, non-vacuity witness and positive control) is kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — **Claim:** the model's verdicts agree with the documented impls `unsafe impl<T: ?Sized> Send for Cell<T> where T: Send` and `unsafe impl<T: ?Sized> Send for RefCell<T> where T: Send`. **Reasoning:** the footprints of `.cell U` and `.refCell U` give the owner the owner capabilities of `U` (moving the cell moves its content), and their shared capabilities transcribe the documented `&self` operations (`Cell::get`, `set`, `replace`, `take`; `RefCell::borrow`, `borrow_mut`). **Sources:** the `cell.rs` lines listed under **Prior art** above. This claim is not established by the Lean kernel.

### Card `cell-not-sync`

**Plain claim.** For every toy type `U`, `SemSync (.cell U)` fails (and so does `SemSync (.refCell U)`): two threads holding a shared reference can both write the cell's storage (resp. the borrow flag) with no claim, a data race.

**Kind.** impossibility. **Tier.** T1. **Depth.** shallow.

Statement (`not_semSync_cell`):

```lean
-- lean/ToySendSync/Characterize.lean:23-23
theorem not_semSync_cell (U : Ty) : ¬ SemSync (.cell U) := …
```

Companion (`not_semSync_refCell`):

```lean
-- lean/ToySendSync/Characterize.lean:42-42
theorem not_semSync_refCell (U : Ty) : ¬ SemSync (.refCell U) := …
```

Companion (`mutex_cell_rc_plain_not_semSync`):

```lean
-- lean/ToySendSync/Results.lean:369-369
theorem mutex_cell_rc_plain_not_semSync : ¬ SemSync (.mutex (.cell (.rc .plain))) := …
```

**Hypothesis ledger.** No hypotheses beyond the universally quantified variables.

**Non-vacuity witness.** Universally quantified negative statement; instance `U = .plain`. (`cell_plain_semSend_not_semSync`)

**Positive control.** For `U = .plain`, a read-only wrapper over the cell and a mutex around the cell are semantically `Sync`. (`cell_positive_control`)

```lean
-- lean/ToySendSync/Results.lean:410-411
theorem cell_positive_control :
    SemSync (.wrap (.cell .plain) .readOnly false) ∧ SemSync (.mutex (.cell .plain)) := …
```

**Non-claims.** Listed under **Boundaries** (global non-claims, then *Non-claims of each result*, `cell-not-sync`); read them before relying on this result.

**Prior art.**

* Rust core library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/core/src/cell.rs: `unsafe impl<T: ?Sized> Send for Cell<T> where T: Send {}` (line 320); `impl<T: ?Sized> !Sync for Cell<T> {}` (line 328); `unsafe impl<T: ?Sized> Send for RefCell<T> where T: Send {}` (line 1439); `impl<T: ?Sized> !Sync for RefCell<T> {}` (line 1442).
* Rust core library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/core/src/cell.rs: `impl<T: ?Sized> !Sync for UnsafeCell<T> {}` (line 2316); lines 322-326 note that `Cell`'s explicit negative impl is redundant because `Cell` wraps `UnsafeCell`.
* Rust core library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/core/src/cell.rs: `pub struct RefCell<T: ?Sized>` (line 852) has the borrow flag field `borrow: Cell<BorrowCounter>` (line 853); `RefCell::borrow(&self) -> Ref<'_, T>` (line 1124, through `try_borrow` at line 1161) and `RefCell::borrow_mut(&self) -> RefMut<'_, T>` (line 1224, through `try_borrow_mut` at line 1258) update the flag; `RefCell::replace` (line 1028, body `mem::replace(&mut self.borrow_mut(), t)` at line 1029), `replace_with` (line 1052), `swap` (line 1082) and `take` (line 1433, which calls `replace`) borrow mutably; `RefCell::get_mut(&mut self)` (line 1333) and `into_inner(self)` (line 998) reach the content without the flag; `RefCell::try_borrow_unguarded` (line 1395, an `unsafe fn`) reads the flag (line 1396) without updating it.
* Ralf Jung, Jacques-Henri Jourdan, Robbert Krebbers, Derek Dreyer. "RustBelt: Securing the Foundations of the Rust Programming Language." Proc. ACM Program. Lang. 2(POPL), Article 66, January 2018. DOI 10.1145/3158154. Section 1.2 (Challenge #3) and Section 4.1: a type is Send if its ownership predicate does not depend on the thread-identifier parameter; Section 4.3 ("Interpreting shared references"): Sync means that the sharing predicate does not depend on the thread identifier, and the ownership predicate of a shared reference is defined from the sharing predicate; Section 2.5.1: "&T is Send if and only if T is Sync". RustBelt's predicates are thread-indexed Iris predicates, not race-freedom scenarios as in this package.
* RustBelt (Jung, Jourdan, Krebbers, Dreyer, POPL 2018, DOI 10.1145/3158154), Section 1.2 and Section 6: a Coq proof of the soundness of the type system (fundamental theorem and adequacy, Section 7) and of the verification conditions of libraries that use unsafe code, including `Arc`, `Rc`, `Cell`, `RefCell`, `Mutex` and `RwLock`; Section 6.1 notes that its model of `Cell<T>` is never Sync and that "Cell<T> is Send if and only if T is"; Section 6.2 concludes that `mutex(τ)` is both Send and Sync when τ is Send. RustBelt proves sufficiency (soundness of the impls and typing rules); it does not state impossibility theorems of the form proved here.
* The Rustonomicon, chapter "Send and Sync", rust-lang/nomicon commit b0bb569883a3e65ab19d4f1adf1b8dbc1629d0a6, src/send-and-sync.md: lines 8-9 ("A type is Send if it is safe to send it to another thread"; "T is Sync if and only if `&T` is Send"); lines 20-29 (automatic derivation; `Cell`/`RefCell` not Sync; `Rc` neither); lines 177-205 (the obligations argued for `unsafe impl Send`/`Sync` on the `Carton` example).

**Design question.** Rust's `Send` and `Sync` are auto traits computed structurally with manual unsafe impls, and `T: Sync` is defined as `&T: Send`. What does each trait certify in a model with threads, shared references and interior mutability; when are the structural rules sound; which primitives need opt-outs/opt-ins and why; and which tempting rules are false?

Basis: execution (Lean kernel check) — every Lean statement quoted in this card (main theorem, companions, counterexamples, non-vacuity witness and positive control) is kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — **Claim:** the model's verdict agrees with the documented negative impls `impl<T: ?Sized> !Sync for Cell<T>` and `impl<T: ?Sized> !Sync for RefCell<T>`. **Reasoning:** `Cell::set` takes `&self` and writes the storage, and `RefCell::borrow` and `borrow_mut` take `&self` and update the borrow flag, a `Cell<BorrowCounter>`; the model represents both as unclaimed writes at the root location. **Sources:** the `cell.rs` lines and Rustonomicon lines listed under **Prior art** above. This claim is not established by the Lean kernel.

### Card `rc-neither`

**Plain claim.** For every toy type `U`, neither `SemSend (.rc U)` nor `SemSync (.rc U)` holds: two handles (one per thread, both holding the allocation, claim `via []`) can both write the non-atomic count.

**Kind.** impossibility. **Tier.** T1. **Depth.** shallow.

Statement (`not_semSend_rc_and_not_semSync_rc`):

```lean
-- lean/ToySendSync/Results.lean:416-416
theorem not_semSend_rc_and_not_semSync_rc (U : Ty) : ¬ SemSend (.rc U) ∧ ¬ SemSync (.rc U) := …
```

Companion (`not_semSend_rc`):

```lean
-- lean/ToySendSync/Characterize.lean:49-49
theorem not_semSend_rc (U : Ty) : ¬ SemSend (.rc U) := …
```

Companion (`not_semSync_rc`):

```lean
-- lean/ToySendSync/Characterize.lean:55-55
theorem not_semSync_rc (U : Ty) : ¬ SemSync (.rc U) := …
```

Companion (`rc_plain_neither`):

```lean
-- lean/ToySendSync/Results.lean:311-311
theorem rc_plain_neither : ¬ SemSend (.rc .plain) ∧ ¬ SemSync (.rc .plain) := …
```

**Hypothesis ledger.** No hypotheses beyond the universally quantified variables.

**Non-vacuity witness.** Universally quantified negative statement; instance `U = .plain`. (`rc_plain_neither`)

**Positive control.** With an atomic count (`.arc .plain`) both properties hold. (`arc_plain_nonvacuous`)

```lean
-- lean/ToySendSync/Results.lean:348-349
theorem arc_plain_nonvacuous :
    SemSend (.arc .plain) ∧ SemSync (.arc .plain) ∧ SemSend .plain ∧ SemSync .plain := …
```

**Non-claims.** Listed under **Boundaries** (global non-claims, then *Non-claims of each result*, `rc-neither`); read them before relying on this result.

**Prior art.**

* Rust alloc library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/alloc/src/rc.rs: `impl<T: ?Sized, A: Allocator> !Send for Rc<T, A> {}` (line 334); `impl<T: ?Sized, A: Allocator> !Sync for Rc<T, A> {}` (line 342); and library/core/src/marker.rs lines 74-79 (the `Send` documentation's example of two threads updating an `Rc` reference count).
* The Rustonomicon, chapter "Send and Sync", rust-lang/nomicon commit b0bb569883a3e65ab19d4f1adf1b8dbc1629d0a6, src/send-and-sync.md: lines 8-9 ("A type is Send if it is safe to send it to another thread"; "T is Sync if and only if `&T` is Send"); lines 20-29 (automatic derivation; `Cell`/`RefCell` not Sync; `Rc` neither); lines 177-205 (the obligations argued for `unsafe impl Send`/`Sync` on the `Carton` example).
* RustBelt (Jung, Jourdan, Krebbers, Dreyer, POPL 2018, DOI 10.1145/3158154), Section 1.2 and Section 6: a Coq proof of the soundness of the type system (fundamental theorem and adequacy, Section 7) and of the verification conditions of libraries that use unsafe code, including `Arc`, `Rc`, `Cell`, `RefCell`, `Mutex` and `RwLock`; Section 6.1 notes that its model of `Cell<T>` is never Sync and that "Cell<T> is Send if and only if T is"; Section 6.2 concludes that `mutex(τ)` is both Send and Sync when τ is Send. RustBelt proves sufficiency (soundness of the impls and typing rules); it does not state impossibility theorems of the form proved here.
* Hoang-Hai Dang, Jacques-Henri Jourdan, Jan-Oliver Kaiser, Derek Dreyer. "RustBelt Meets Relaxed Memory." Proc. ACM Program. Lang. 4(POPL), Article 34, January 2020. DOI 10.1145/3371102. Section 1 and Section 5.3: re-verifies RustBelt's library proofs, including `Arc`, under a relaxed-memory semantics. The model here has no memory orderings.

**Design question.** Rust's `Send` and `Sync` are auto traits computed structurally with manual unsafe impls, and `T: Sync` is defined as `&T: Send`. What does each trait certify in a model with threads, shared references and interior mutability; when are the structural rules sound; which primitives need opt-outs/opt-ins and why; and which tempting rules are false?

Basis: execution (Lean kernel check) — every Lean statement quoted in this card (main theorem, companions, counterexamples, non-vacuity witness and positive control) is kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — **Claim:** the model's verdict agrees with the documented negative impls `!Send` and `!Sync` for `Rc` and with the `Send` documentation's example of two threads updating an `Rc` reference count. **Reasoning:** every handle can update the non-atomic count (cloning and dropping), modelled as writes under the claim `via []`, with no lock claim (`held`). **Sources:** the `rc.rs` and `marker.rs` lines listed under **Prior art** above. This claim is not established by the Lean kernel.

### Card `arc-send-iff`

**Plain claim.** For every toy type `U`, `SemSend (.arc U)` holds if and only if both `SemSend U` and `SemSync U` hold, and `SemSync (.arc U)` holds if and only if both `SemSend U` and `SemSync U` hold (`semSync_arc_iff`); `arc_race_iff` decomposes the transfer race of `.arc U` into the races of `U`. Neither conjunct follows from the other: `Arc<Cell<plain>>` (content `SemSend`, not `SemSync`; `arc_cell_plain_content_not_semSync_arc_neither`), `Arc<MutexGuard<plain>>` (content `SemSync`, not `SemSend`, by release affinity; `arc_guard_plain_content_not_semSend_arc_neither`) and `Arc` of a wrapper around `Rc<plain>` exposing nothing, for either impl flag (content `SemSync`, not `SemSend`, by a data race, while the transfer of the `Arc` makes no foreign release; `arc_wrap_rc_none_content_not_semSend_arc_neither`) are neither semantically `Send` nor semantically `Sync`.

**Kind.** characterization. **Tier.** T1. **Depth.** shallow.

Statement (`semSend_arc_iff`):

```lean
-- lean/ToySendSync/Characterize.lean:71-71
theorem semSend_arc_iff (U : Ty) : SemSend (.arc U) ↔ SemSend U ∧ SemSync U := …
```

Companion (`semSync_arc_iff`):

```lean
-- lean/ToySendSync/Characterize.lean:94-94
theorem semSync_arc_iff (U : Ty) : SemSync (.arc U) ↔ SemSend U ∧ SemSync U := …
```

Companion (`arc_race_iff`):

```lean
-- lean/ToySendSync/Characterize.lean:63-65
theorem arc_race_iff (U : Ty) :
    Race (fp (.arc U)).own ((fp (.arc U)).own ++ place [] 0 (fp U).alias) ↔
      Race (fp U).shr (fp U).shr ∨ Race (fp U).shr (fp U).alias ∨ Race (fp U).own (fp U).alias := …
```

Companion (`arc_cell_plain_content_not_semSync_arc_neither`):

```lean
-- lean/ToySendSync/Results.lean:317-319
theorem arc_cell_plain_content_not_semSync_arc_neither :
    SemSend (.cell .plain) ∧ ¬ SemSync (.cell .plain) ∧
      ¬ SemSend (.arc (.cell .plain)) ∧ ¬ SemSync (.arc (.cell .plain)) := …
```

Companion (`arc_guard_plain_content_not_semSend_arc_neither`):

```lean
-- lean/ToySendSync/Results.lean:327-329
theorem arc_guard_plain_content_not_semSend_arc_neither :
    SemSync (.guard .plain) ∧ ¬ SemSend (.guard .plain) ∧
      ¬ SemSend (.arc (.guard .plain)) ∧ ¬ SemSync (.arc (.guard .plain)) := …
```

Companion (`arc_wrap_rc_none_content_not_semSend_arc_neither`):

```lean
-- lean/ToySendSync/Results.lean:338-341
theorem arc_wrap_rc_none_content_not_semSend_arc_neither (u : Bool) :
    SemSync (.wrap (.rc .plain) .none u) ∧ ¬ SemSend (.wrap (.rc .plain) .none u) ∧
      ¬ SemSend (.arc (.wrap (.rc .plain) .none u)) ∧ ¬ SemSync (.arc (.wrap (.rc .plain) .none u)) ∧
      NoForeignRelease .other (fp (.arc (.wrap (.rc .plain) .none u))).own := …
```

Explicit form of the right-hand side of `semSend_arc_iff`:

```lean
(¬ Race (fp U).own (fp U).alias ∧ NoForeignRelease .other (fp U).own) ∧
  (¬ Race (fp U).shr ((fp U).shr ++ (fp U).alias) ∧ NoForeignRelease .other (fp U).shr)
```

Explicit form of the left-hand side of `semSend_arc_iff` (footprint of `.arc U` expanded):

```lean
¬ Race ([rootEv .atomic [.via []]] ++ place [.via []] 0 (fp U).shr ++ place [.uniq []] 0 (fp U).own)
    (([rootEv .atomic [.via []]] ++ place [.via []] 0 (fp U).shr ++ place [.uniq []] 0 (fp U).own) ++
      place [] 0 (fp U).alias) ∧
  NoForeignRelease .other ([rootEv .atomic [.via []]] ++ place [.via []] 0 (fp U).shr ++ place [.uniq []] 0 (fp U).own)
```

**Hypothesis ledger.** No hypotheses beyond the universally quantified variable `U`. Characterization cards record the independence of right-hand-side conjuncts as companion theorems, not as hypotheses: `arc_cell_plain_content_not_semSync_arc_neither` (the `SemSync U` conjunct), `arc_guard_plain_content_not_semSend_arc_neither` and `arc_wrap_rc_none_content_not_semSend_arc_neither` (the `SemSend U` conjunct; the second is guard-free and fails by a data race).

**Non-vacuity witness.** `U = .plain`: all four propositions hold. (`arc_plain_nonvacuous`)

**Non-claims.** Listed under **Boundaries** (global non-claims, then *Non-claims of each result*, `arc-send-iff`); read them before relying on this result.

**Prior art.**

* Rust alloc library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/alloc/src/sync.rs: `unsafe impl<T: ?Sized + Sync + Send, A: Allocator + Send + Sync> Send for Arc<T, A> {}` (line 284) and the same bounds for `Sync` (line 286); the "Thread Safety" documentation (lines 124-147) explains with `Arc<RefCell<T>>` why `T: Sync` is required.
* Ralf Jung, Jacques-Henri Jourdan, Robbert Krebbers, Derek Dreyer. "RustBelt: Securing the Foundations of the Rust Programming Language." Proc. ACM Program. Lang. 2(POPL), Article 66, January 2018. DOI 10.1145/3158154. Section 1.2 (Challenge #3) and Section 4.1: a type is Send if its ownership predicate does not depend on the thread-identifier parameter; Section 4.3 ("Interpreting shared references"): Sync means that the sharing predicate does not depend on the thread identifier, and the ownership predicate of a shared reference is defined from the sharing predicate; Section 2.5.1: "&T is Send if and only if T is Sync". RustBelt's predicates are thread-indexed Iris predicates, not race-freedom scenarios as in this package.
* RustBelt (Jung, Jourdan, Krebbers, Dreyer, POPL 2018, DOI 10.1145/3158154), Section 1.2 and Section 6: a Coq proof of the soundness of the type system (fundamental theorem and adequacy, Section 7) and of the verification conditions of libraries that use unsafe code, including `Arc`, `Rc`, `Cell`, `RefCell`, `Mutex` and `RwLock`; Section 6.1 notes that its model of `Cell<T>` is never Sync and that "Cell<T> is Send if and only if T is"; Section 6.2 concludes that `mutex(τ)` is both Send and Sync when τ is Send. RustBelt proves sufficiency (soundness of the impls and typing rules); it does not state impossibility theorems of the form proved here.
* Hoang-Hai Dang, Jacques-Henri Jourdan, Jan-Oliver Kaiser, Derek Dreyer. "RustBelt Meets Relaxed Memory." Proc. ACM Program. Lang. 4(POPL), Article 34, January 2020. DOI 10.1145/3371102. Section 1 and Section 5.3: re-verifies RustBelt's library proofs, including `Arc`, under a relaxed-memory semantics. The model here has no memory orderings.

**Design question.** Rust's `Send` and `Sync` are auto traits computed structurally with manual unsafe impls, and `T: Sync` is defined as `&T: Send`. What does each trait certify in a model with threads, shared references and interior mutability; when are the structural rules sound; which primitives need opt-outs/opt-ins and why; and which tempting rules are false?

Basis: execution (Lean kernel check) — every Lean statement quoted in this card (main theorem, companions, counterexamples, non-vacuity witness and positive control) is kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — **Claim:** the model's verdicts agree with the documented impls that make `Arc<T>` `Send` and `Sync` when `T: Send + Sync` (allocator bounds aside). **Reasoning:** a handle on another thread can reach `&T` (which needs `Sync`) and, as the last handle, can drop or move out the `T` (which needs `Send`); the footprint of `.arc U` places the shared capabilities of `U` under `via []` and its owner capabilities under `uniq []`. **Sources:** the `sync.rs` lines listed under **Prior art** above. This claim is not established by the Lean kernel.

### Card `mutex-sync-iff`

**Plain claim.** For every toy type `U`, `SemSync (.mutex U)` holds if and only if `SemSend U` holds, and `SemSend (.mutex U)` holds if and only if `SemSend U` holds (`semSend_mutex_iff`). `SemSync U` is not needed: `Mutex<Cell<plain>>` is semantically `Sync` while `Cell<plain>` is not (`mutex_cell_plain_semSync_content_not_semSync`); with non-`SemSend` content `Rc<plain>`, `Mutex<Rc<plain>>` is neither (`mutex_rc_plain_content_not_semSend_mutex_neither`).

**Kind.** characterization. **Tier.** T1. **Depth.** shallow.

Statement (`semSync_mutex_iff`):

```lean
-- lean/ToySendSync/Characterize.lean:114-114
theorem semSync_mutex_iff (U : Ty) : SemSync (.mutex U) ↔ SemSend U := …
```

Companion (`semSend_mutex_iff`):

```lean
-- lean/ToySendSync/Characterize.lean:109-109
theorem semSend_mutex_iff (U : Ty) : SemSend (.mutex U) ↔ SemSend U := …
```

Companion (`mutex_cell_plain_semSync_content_not_semSync`):

```lean
-- lean/ToySendSync/Results.lean:362-363
theorem mutex_cell_plain_semSync_content_not_semSync :
    SemSend (.cell .plain) ∧ SemSync (.mutex (.cell .plain)) ∧ ¬ SemSync (.cell .plain) := …
```

Companion (`mutex_rc_plain_content_not_semSend_mutex_neither`):

```lean
-- lean/ToySendSync/Results.lean:355-356
theorem mutex_rc_plain_content_not_semSend_mutex_neither :
    ¬ SemSend (.rc .plain) ∧ ¬ SemSync (.mutex (.rc .plain)) ∧ ¬ SemSend (.mutex (.rc .plain)) := …
```

Explicit form of the left-hand side of `semSync_mutex_iff` (footprint of `.mutex U` expanded):

```lean
¬ Race (place [.held [] .fresh] 0 (fp U).own ++ [rootEv .rel [.held [] .fresh]])
    ((place [.held [] .fresh] 0 (fp U).own ++ [rootEv .rel [.held [] .fresh]]) ++ place [] 0 (fp U).alias) ∧
  NoForeignRelease .other (place [.held [] .fresh] 0 (fp U).own ++ [rootEv .rel [.held [] .fresh]])
```

**Hypothesis ledger.** No hypotheses beyond the universally quantified variable `U`. The right-hand side `SemSend U` is not a hypothesis; its role is shown by `mutex_rc_plain_content_not_semSend_mutex_neither` (content not `SemSend`, both properties fail).

**Non-vacuity witness.** `U = .cell .plain`: `Cell<plain>` is semantically `Send`, and `Mutex<Cell<plain>>` is semantically `Sync` though `Cell<plain>` is not. (`mutex_cell_plain_semSync_content_not_semSync`)

**Non-claims.** Listed under **Boundaries** (global non-claims, then *Non-claims of each result*, `mutex-sync-iff`); read them before relying on this result.

**Prior art.**

* Rust std library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/std/src/sync/poison/mutex.rs: `unsafe impl<T: ?Sized + Send> Send for Mutex<T> {}` (line 238, rationale lines 233-235: the owned `T` can be acquired via `into_inner`); `unsafe impl<T: ?Sized + Send> Sync for Mutex<T> {}` (line 257, rationale lines 240-254, citing `Mutex<Rc<_>>` and noting "it is not necessary for `T` to be `Sync`").
* Rust std library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/std/src/sync/poison/rwlock.rs: `unsafe impl<T: ?Sized + Send> Send for RwLock<T> {}` (line 104); `unsafe impl<T: ?Sized + Send + Sync> Sync for RwLock<T> {}` (line 107); `RwLockReadGuard` and `RwLockWriteGuard` are `!Send` (lines 140, 168) and `Sync` when `T: Sync` (lines 143, 171).
* RustBelt (Jung, Jourdan, Krebbers, Dreyer, POPL 2018, DOI 10.1145/3158154), Section 1.2 and Section 6: a Coq proof of the soundness of the type system (fundamental theorem and adequacy, Section 7) and of the verification conditions of libraries that use unsafe code, including `Arc`, `Rc`, `Cell`, `RefCell`, `Mutex` and `RwLock`; Section 6.1 notes that its model of `Cell<T>` is never Sync and that "Cell<T> is Send if and only if T is"; Section 6.2 concludes that `mutex(τ)` is both Send and Sync when τ is Send. RustBelt proves sufficiency (soundness of the impls and typing rules); it does not state impossibility theorems of the form proved here.

**Design question.** Rust's `Send` and `Sync` are auto traits computed structurally with manual unsafe impls, and `T: Sync` is defined as `&T: Send`. What does each trait certify in a model with threads, shared references and interior mutability; when are the structural rules sound; which primitives need opt-outs/opt-ins and why; and which tempting rules are false?

Basis: execution (Lean kernel check) — every Lean statement quoted in this card (main theorem, companions, counterexamples, non-vacuity witness and positive control) is kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — **Claim:** the model's verdicts agree with the documented impls that make `Mutex<T>` `Send` and `Sync` when `T: Send`, and with the documentation's remark that `T: Sync` is not necessary. **Reasoning:** a thread that locks the mutex through a shared reference reaches the owner capabilities of `T` under the claim `held [] .fresh`, which no event of the other thread under the same lock can share in a snapshot; the owner reaches the content without the lock (`into_inner`). **Sources:** the `mutex.rs` lines listed under **Prior art** above. This claim is not established by the Lean kernel.

### Card `guard-sync-iff`

**Plain claim.** For every toy type `U`, `SemSync (.guard U)` holds if and only if `SemSync U` holds. Instances (`guard_sync_examples`): `MutexGuard<plain>` is semantically `Sync`; `Cell<plain>` is not semantically `Sync`, and neither is `MutexGuard<Cell<plain>>`.

**Kind.** characterization. **Tier.** T1. **Depth.** shallow.

Statement (`semSync_guard_iff`):

```lean
-- lean/ToySendSync/Characterize.lean:128-128
theorem semSync_guard_iff (U : Ty) : SemSync (.guard U) ↔ SemSync U := …
```

Companion (`guard_sync_examples`):

```lean
-- lean/ToySendSync/Results.lean:374-375
theorem guard_sync_examples :
    SemSync (.guard .plain) ∧ ¬ SemSync (.cell .plain) ∧ ¬ SemSync (.guard (.cell .plain)) := …
```

Explicit form of the left-hand side of `semSync_guard_iff` (footprint of `.guard U` expanded):

```lean
¬ Race (place [.held [] (.guard [])] 0 (fp U).shr)
    (place [.held [] (.guard [])] 0 (fp U).shr ++
      (place [.held [] .fresh] 0 (fp U).own ++ place [] 0 (fp U).alias)) ∧
  NoForeignRelease .other (place [.held [] (.guard [])] 0 (fp U).shr)
```

**Hypothesis ledger.** No hypotheses beyond the universally quantified variable `U`. The role of the right-hand side is shown by `guard_sync_examples` (content not `SemSync`, guard not `SemSync`).

**Non-vacuity witness.** `U = .plain`: `plain` and `MutexGuard<plain>` are semantically `Sync`. (`guard_plain_semSync_not_semSend`)

```lean
-- lean/ToySendSync/Results.lean:381-382
theorem guard_plain_semSync_not_semSend :
    SemSync .plain ∧ SemSync (.guard .plain) ∧ ¬ SemSend (.guard .plain) := …
```

**Non-claims.** Listed under **Boundaries** (global non-claims, then *Non-claims of each result*, `guard-sync-iff`); read them before relying on this result.

**Prior art.**

* Rust std library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/std/src/sync/poison/mutex.rs: `impl<T: ?Sized> !Send for MutexGuard<'_, T> {}` (line 289; lines 282-287: "On platforms that use POSIX threads ... there is a requirement to release mutex locks on the same thread they were acquired"); `unsafe impl<T: ?Sized + Sync> Sync for MutexGuard<'_, T> {}` (line 294; lines 291-292: a `&T` is obtainable from `&MutexGuard` via `Deref`).
* rust-lang/rust issue 41622, "MutexGuard<Cell<i32>> must not be Sync" (https://github.com/rust-lang/rust/issues/41622, opened 2017-04-29, closed 2017-05-03; read on 2026-11-21): it reports that `MutexGuard<Cell<i32>>` satisfied the `Sync` bound at the time, which permitted a data race; RustBelt (POPL 2018, Section 1.1 and Section 1.2) cites it; at the commit above the impl reads `unsafe impl<T: ?Sized + Sync> Sync for MutexGuard<'_, T> {}` with `#[stable(feature = "mutexguard", since = "1.19.0")]` (library/std/src/sync/poison/mutex.rs lines 291-294).
* RustBelt (Jung, Jourdan, Krebbers, Dreyer, POPL 2018, DOI 10.1145/3158154), Section 1.2 and Section 6: a Coq proof of the soundness of the type system (fundamental theorem and adequacy, Section 7) and of the verification conditions of libraries that use unsafe code, including `Arc`, `Rc`, `Cell`, `RefCell`, `Mutex` and `RwLock`; Section 6.1 notes that its model of `Cell<T>` is never Sync and that "Cell<T> is Send if and only if T is"; Section 6.2 concludes that `mutex(τ)` is both Send and Sync when τ is Send. RustBelt proves sufficiency (soundness of the impls and typing rules); it does not state impossibility theorems of the form proved here.

**Design question.** Rust's `Send` and `Sync` are auto traits computed structurally with manual unsafe impls, and `T: Sync` is defined as `&T: Send`. What does each trait certify in a model with threads, shared references and interior mutability; when are the structural rules sound; which primitives need opt-outs/opt-ins and why; and which tempting rules are false?

Basis: execution (Lean kernel check) — every Lean statement quoted in this card (main theorem, companions, counterexamples, non-vacuity witness and positive control) is kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — **Claim:** the model's verdict agrees with the documented impl `unsafe impl<T: ?Sized + Sync> Sync for MutexGuard<'_, T>`. **Reasoning:** a shared reference to a guard yields `&T` through `Deref`, modelled as the shared capabilities of `U` under the guard's claim. **Sources:** the `mutex.rs` lines and the upstream issue listed under **Prior art** above. This claim is not established by the Lean kernel.

### Card `guard-not-send`

**Plain claim.** Under the model's release-affinity rule (`NoForeignRelease`: every acquisition that a release event executed by the other thread names, by a claim `held l a` on the event's own location `l`, was made by the other thread; every release event of every model footprint names an acquisition, by `fp_relNamesAcq`; a guard's acquisition was made by the origin thread), `SemSend (.guard U)` fails for every toy type `U`, because the guard's owner footprint contains the release of its own acquisition. Companion (`guard_transfer_race_iff`): for every `U`, the transfer race of `.guard U` holds if and only if the transfer race of `U` holds. Companion (`fp_relNamesAcq`): for every toy type `T`, every release event of `(fp T).own`, `(fp T).shr` and `(fp T).alias` carries a claim `held l a` on its own location `l` (`RelNamesAcq`), so release affinity constrains every release event of the model's footprints.

**Kind.** impossibility. **Tier.** T1. **Depth.** definitional.

Statement (`not_semSend_guard`):

```lean
-- lean/ToySendSync/Characterize.lean:122-122
theorem not_semSend_guard (U : Ty) : ¬ SemSend (.guard U) := …
```

Companion (`guard_transfer_race_iff`):

```lean
-- lean/ToySendSync/Results.lean:390-391
theorem guard_transfer_race_iff (U : Ty) :
    Race (fp (.guard U)).own (fp (.guard U)).alias ↔ Race (fp U).own (fp U).alias := …
```

Companion (`guard_rc_plain_transfer_race`):

```lean
-- lean/ToySendSync/Results.lean:402-403
theorem guard_rc_plain_transfer_race :
    Race (fp (.guard (.rc .plain))).own (fp (.guard (.rc .plain))).alias := …
```

Companion (`guard_plain_semSync_not_semSend`):

```lean
-- lean/ToySendSync/Results.lean:381-382
theorem guard_plain_semSync_not_semSend :
    SemSync .plain ∧ SemSync (.guard .plain) ∧ ¬ SemSend (.guard .plain) := …
```

Companion (`fp_relNamesAcq`):

```lean
-- lean/ToySendSync/Results.lean:136-137
theorem fp_relNamesAcq (T : Ty) :
    RelNamesAcq (fp T).own ∧ RelNamesAcq (fp T).shr ∧ RelNamesAcq (fp T).alias := …
```

Companion (`RelNamesAcq`): quoted in the Definitions section above.

Unfolded (prose):

```text
The owner footprint of `.guard U` contains the event
`rootEv .rel [.held [] (.guard [])]`, which releases the guard's acquisition; its maker
is the origin thread, so the `NoForeignRelease .other` conjunct of
`SemSend (.guard U)` fails whatever `U` is.
```

**Hypothesis ledger.** No hypotheses beyond the universally quantified variables.

**Non-vacuity witness.** Universally quantified negative statement; instance `U = .plain`. (`guard_plain_semSync_not_semSend`)

**Positive control.** Without the release-affinity conjunct, the transfer of `MutexGuard<plain>` is race-free. (`guard_plain_transfer_race_free`)

```lean
-- lean/ToySendSync/Results.lean:397-397
theorem guard_plain_transfer_race_free : ¬ Race (fp (.guard .plain)).own (fp (.guard .plain)).alias := …
```

**Non-claims.** Listed under **Boundaries** (global non-claims, then *Non-claims of each result*, `guard-not-send`); read them before relying on this result.

**Prior art.**

* Rust std library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/std/src/sync/poison/mutex.rs: `impl<T: ?Sized> !Send for MutexGuard<'_, T> {}` (line 289; lines 282-287: "On platforms that use POSIX threads ... there is a requirement to release mutex locks on the same thread they were acquired"); `unsafe impl<T: ?Sized + Sync> Sync for MutexGuard<'_, T> {}` (line 294; lines 291-292: a `&T` is obtainable from `&MutexGuard` via `Deref`).

**Design question.** Rust's `Send` and `Sync` are auto traits computed structurally with manual unsafe impls, and `T: Sync` is defined as `&T: Send`. What does each trait certify in a model with threads, shared references and interior mutability; when are the structural rules sound; which primitives need opt-outs/opt-ins and why; and which tempting rules are false?

Basis: execution (Lean kernel check) — every Lean statement quoted in this card (main theorem, companions, counterexamples, non-vacuity witness and positive control) is kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — **Claim:** the model's verdict agrees with the documented negative impl `impl<T: ?Sized> !Send for MutexGuard<'_, T>`, whose documentation gives the POSIX requirement to release a lock on the thread that acquired it. **Reasoning:** `NoForeignRelease` models that requirement; the guard's owner footprint contains the release of its acquisition. **Sources:** the `mutex.rs` lines listed under **Prior art** above. This claim is not established by the Lean kernel.

### Card `false-rule-sync-implies-send`

**Plain claim.** It is not the case that every toy type `T` with `SemSync T` has `SemSend T`; witnesses: `.guard .plain`, and the guard-free `.wrap (.rc .plain) .none u` for either `u` (`wrap_rc_none_semSync_not_semSend`).

**Kind.** impossibility. **Tier.** T1. **Depth.** shallow.

Statement (`not_forall_semSync_imp_semSend`):

```lean
-- lean/ToySendSync/Results.lean:432-432
theorem not_forall_semSync_imp_semSend : ¬ ∀ T : Ty, SemSync T → SemSend T := …
```

Companion (`wrap_rc_none_semSync_not_semSend`):

```lean
-- lean/ToySendSync/Results.lean:437-438
theorem wrap_rc_none_semSync_not_semSend (u : Bool) :
    SemSync (.wrap (.rc .plain) .none u) ∧ ¬ SemSend (.wrap (.rc .plain) .none u) := …
```

Companion (`guard_plain_own_not_subset_shr`):

```lean
-- lean/ToySendSync/Results.lean:513-514
theorem guard_plain_own_not_subset_shr :
    ¬ ∀ e ∈ (fp (.guard .plain)).own, e ∈ (fp (.guard .plain)).shr := …
```

**Hypothesis ledger.** No hypotheses beyond the universally quantified variables.

**Non-vacuity witness.** Witness `.guard .plain`. (`guard_plain_semSync_not_semSend`)

**Positive control.** If every owner capability of `T` is also a shared capability, `SemSync T` implies `SemSend T`. (`semSync_imp_semSend_of_own_subset_shr`)

```lean
-- lean/ToySendSync/Results.lean:483-484
theorem semSync_imp_semSend_of_own_subset_shr (T : Ty)
    (hsub : ∀ e ∈ (fp T).own, e ∈ (fp T).shr) (hy : SemSync T) : SemSend T := …
```

**Non-claims.** Listed under **Boundaries** (global non-claims, then *Non-claims of each result*, `false-rule-sync-implies-send`); read them before relying on this result.

**Prior art.**

* Rust std library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/std/src/sync/poison/mutex.rs: `impl<T: ?Sized> !Send for MutexGuard<'_, T> {}` (line 289; lines 282-287: "On platforms that use POSIX threads ... there is a requirement to release mutex locks on the same thread they were acquired"); `unsafe impl<T: ?Sized + Sync> Sync for MutexGuard<'_, T> {}` (line 294; lines 291-292: a `&T` is obtainable from `&MutexGuard` via `Deref`).
* Rust core library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/core/src/sync/sync_view.rs: `unsafe impl<T: ?Sized> Sync for SyncView<T> {}` (lines 108-109: the impl at line 109, marked as unstable feature `exclusive_wrapper` by the attribute at line 108), justified because "a `&SyncView<T>` for non-`Sync` `T` has no API whatsoever" (lines 13-21).
* Rust RFC 0458 "Send Improvements", rust-lang/rfcs commit f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4, text/0458-send-improvements.md (start date 2014-11-10): makes `&T` `Send` if and only if `T` is `Sync` (lines 11-16, with `unsafe impl<'a, T> Send for &'a T where T: Sync + 'a {}` at line 15), and argues with its `RcMut` example (line 95; code at lines 169-182) that `Sync` does not imply `Send`.

**Design question.** Rust's `Send` and `Sync` are auto traits computed structurally with manual unsafe impls, and `T: Sync` is defined as `&T: Send`. What does each trait certify in a model with threads, shared references and interior mutability; when are the structural rules sound; which primitives need opt-outs/opt-ins and why; and which tempting rules are false?

Basis: execution (Lean kernel check) — every Lean statement quoted in this card (main theorem, companions, counterexamples, non-vacuity witness and positive control) is kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — **Claim:** the refutation agrees with the documented existence of types that are `Sync` and not `Send` (`MutexGuard`), and with RFC 0458's argument that `Sync` does not imply `Send`. **Reasoning:** the witness `.guard .plain` models a guard over plain data, whose failure to be `Send` comes from release affinity; the guard-free witness fails by a data race on a counted allocation. **Sources:** the `mutex.rs`, `sync_view.rs` and RFC lines listed under **Prior art** above. This claim is not established by the Lean kernel.

### Card `false-rule-send-implies-sync`

**Plain claim.** It is not the case that every toy type `T` with `SemSend T` has `SemSync T`; witness: `.cell .plain`.

**Kind.** impossibility. **Tier.** T1. **Depth.** shallow.

Statement (`not_forall_semSend_imp_semSync`):

```lean
-- lean/ToySendSync/Results.lean:442-442
theorem not_forall_semSend_imp_semSync : ¬ ∀ T : Ty, SemSend T → SemSync T := …
```

Companion (`cell_plain_shr_has_write`):

```lean
-- lean/ToySendSync/Results.lean:508-508
theorem cell_plain_shr_has_write : ¬ ∀ e ∈ (fp (.cell .plain)).shr, e.kind.isWrite = false := …
```

**Hypothesis ledger.** No hypotheses beyond the universally quantified variables.

**Non-vacuity witness.** Witness `.cell .plain`. (`cell_plain_semSend_not_semSync`)

**Positive control.** If the shared footprint of `T` contains no write, `SemSend T` implies `SemSync T`. (`semSend_imp_semSync_of_shr_no_write`)

```lean
-- lean/ToySendSync/Results.lean:447-448
theorem semSend_imp_semSync_of_shr_no_write (T : Ty)
    (hro : ∀ e ∈ (fp T).shr, e.kind.isWrite = false) (hs : SemSend T) : SemSync T := …
```

**Non-claims.** Listed under **Boundaries** (global non-claims, then *Non-claims of each result*, `false-rule-send-implies-sync`); read them before relying on this result.

**Prior art.**

* Rust core library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/core/src/cell.rs: `unsafe impl<T: ?Sized> Send for Cell<T> where T: Send {}` (line 320); `impl<T: ?Sized> !Sync for Cell<T> {}` (line 328); `unsafe impl<T: ?Sized> Send for RefCell<T> where T: Send {}` (line 1439); `impl<T: ?Sized> !Sync for RefCell<T> {}` (line 1442).
* Rust core library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/core/src/marker.rs: `pub unsafe auto trait Send` (line 92); `impl<T: PointeeSized> !Send for *const T {}` (line 97); `unsafe impl<T: Sync + PointeeSized> Send for &T {}` (line 105); `Sync` documentation (lines 511-539): "The precise definition is: a type `T` is [`Sync`] if and only if `&T` is [`Send`]", "`&mut T` is [`Send`] if and only if `T` is [`Send`]", "`&T` and `&mut T` are [`Sync`] if and only if `T` is [`Sync`]"; `pub unsafe auto trait Sync` (line 657); `impl<T: PointeeSized> !Sync for *const T {}` (line 672).

**Design question.** Rust's `Send` and `Sync` are auto traits computed structurally with manual unsafe impls, and `T: Sync` is defined as `&T: Send`. What does each trait certify in a model with threads, shared references and interior mutability; when are the structural rules sound; which primitives need opt-outs/opt-ins and why; and which tempting rules are false?

Basis: execution (Lean kernel check) — every Lean statement quoted in this card (main theorem, companions, counterexamples, non-vacuity witness and positive control) is kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — **Claim:** the refutation agrees with the documented impls that make `Cell<T>` `Send` (for `T: Send`) and not `Sync`. **Reasoning:** the witness `.cell .plain` models `Cell<u32>`-like plain content. **Sources:** the `cell.rs` and `marker.rs` lines listed under **Prior art** above. This claim is not established by the Lean kernel.

### Card `shared-write-free-send-implies-sync`

**Plain claim.** For every toy type `T` whose shared footprint `(fp T).shr` contains no write event (hypothesis `hro`) and which satisfies `SemSend T` (hypothesis `hs`), `SemSync T` holds.

**Kind.** theorem. **Tier.** T1. **Depth.** shallow.

Statement (`semSend_imp_semSync_of_shr_no_write`):

```lean
-- lean/ToySendSync/Results.lean:447-448
theorem semSend_imp_semSync_of_shr_no_write (T : Ty)
    (hro : ∀ e ∈ (fp T).shr, e.kind.isWrite = false) (hs : SemSend T) : SemSync T := …
```

Companion (`shr_subset_own`):

```lean
-- lean/ToySendSync/Lemmas.lean:393-393
theorem shr_subset_own : ∀ T : Ty, ∀ e ∈ (fp T).shr, e ∈ (fp T).own := …
```

Companion (`arc_plain_shr_has_write_semSync`):

```lean
-- lean/ToySendSync/Results.lean:477-478
theorem arc_plain_shr_has_write_semSync :
    ¬ (∀ e ∈ (fp (.arc .plain)).shr, e.kind.isWrite = false) ∧ SemSync (.arc .plain) := …
```

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hro : ∀ e ∈ (fp T).shr, e.kind.isWrite = false` | A write in the shared footprint can race with another sharer even when transfer is race-free. | tight | `cell_plain_semSend_not_semSync` | an instance with `T = .cell .plain` (`SemSend` holds, `SemSync` fails) |
| `hs : SemSend T` | A write-free shared footprint can still race with alias capabilities (writes by other handles). | tight | `semSend_imp_semSync_of_shr_no_write_semSend_tight` | an instance with `T = .wrap (.rc .plain) .readOnly false` (`hro` holds, `SemSync` fails) |

Counterexample `cell_plain_semSend_not_semSync`: quoted above.

Counterexample `semSend_imp_semSync_of_shr_no_write_semSend_tight`:

```lean
-- lean/ToySendSync/Results.lean:468-470
theorem semSend_imp_semSync_of_shr_no_write_semSend_tight :
    (∀ e ∈ (fp (.wrap (.rc .plain) .readOnly false)).shr, e.kind.isWrite = false) ∧
      ¬ SemSync (.wrap (.rc .plain) .readOnly false) := …
```

**Non-vacuity witness.** `T = .plain`. (`semSend_imp_semSync_of_shr_no_write_nonvacuous`)

```lean
-- lean/ToySendSync/Results.lean:461-462
theorem semSend_imp_semSync_of_shr_no_write_nonvacuous :
    (∀ e ∈ (fp .plain).shr, e.kind.isWrite = false) ∧ SemSend .plain := …
```

**Non-claims.** Listed under **Boundaries** (global non-claims, then *Non-claims of each result*, `shared-write-free-send-implies-sync`); read them before relying on this result.

**Prior art.**

* Rust core library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/core/src/marker.rs: `pub unsafe auto trait Send` (line 92); `impl<T: PointeeSized> !Send for *const T {}` (line 97); `unsafe impl<T: Sync + PointeeSized> Send for &T {}` (line 105); `Sync` documentation (lines 511-539): "The precise definition is: a type `T` is [`Sync`] if and only if `&T` is [`Send`]", "`&mut T` is [`Send`] if and only if `T` is [`Send`]", "`&T` and `&mut T` are [`Sync`] if and only if `T` is [`Sync`]"; `pub unsafe auto trait Sync` (line 657); `impl<T: PointeeSized> !Sync for *const T {}` (line 672).
* The Rust Reference, rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c, src/special-types-and-traits.md: rule `lang-types.auto-traits.auto-impl` (lines 161-162): "If no explicit implementation or negative implementation is written out for an auto trait for a given type, then the compiler implements it automatically according to the following rules:"; rule `lang-types.auto-traits.aggregate` (lines 170-171): "Structs, enums, unions, and tuples implement the trait if all of their fields do."

**Design question.** Rust's `Send` and `Sync` are auto traits computed structurally with manual unsafe impls, and `T: Sync` is defined as `&T: Send`. What does each trait certify in a model with threads, shared references and interior mutability; when are the structural rules sound; which primitives need opt-outs/opt-ins and why; and which tempting rules are false?

Basis: execution (Lean kernel check) — every Lean statement quoted in this card (main theorem, companions, counterexamples, non-vacuity witness and positive control) is kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — **Claim:** the theorem is the model's form of the folklore rule that a `Send` type whose shared API performs no writes (no interior mutability) is also `Sync`. **Reasoning:** in the model, a shared footprint without writes gives the holder of `&T` no write. Rust's auto-trait derivation does not use this rule: `Sync` is derived structurally from fields, as documented in the Rust Reference. **Sources:** the lines listed under **Prior art** above. This claim is not established by the Lean kernel.

### Card `own-in-shared-sync-implies-send`

**Plain claim.** For every toy type `T` whose owner footprint `(fp T).own` is contained in its shared footprint `(fp T).shr` (hypothesis `hsub`) and which satisfies `SemSync T` (hypothesis `hy`), `SemSend T` holds.

**Kind.** theorem. **Tier.** T1. **Depth.** shallow.

Statement (`semSync_imp_semSend_of_own_subset_shr`):

```lean
-- lean/ToySendSync/Results.lean:483-484
theorem semSync_imp_semSend_of_own_subset_shr (T : Ty)
    (hsub : ∀ e ∈ (fp T).own, e ∈ (fp T).shr) (hy : SemSync T) : SemSend T := …
```

Companion (`plain_own_not_subset_shr_semSend`):

```lean
-- lean/ToySendSync/Results.lean:502-503
theorem plain_own_not_subset_shr_semSend :
    ¬ (∀ e ∈ (fp .plain).own, e ∈ (fp .plain).shr) ∧ SemSend .plain := …
```

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hsub : ∀ e ∈ (fp T).own, e ∈ (fp T).shr` | Owner-only capabilities can fail on transfer while sharing is fine: a guard's release (`.guard .plain`), or an owner-only handle whose alias races (the guard-free `.wrap (.rc .plain) .none false`, `wrap_rc_none_semSync_not_semSend`). | tight | `guard_plain_semSync_not_semSend` | an instance with `T = .guard .plain` (`SemSync` holds, `SemSend` fails) |
| `hy : SemSync T` | Equal owner and shared footprints can both race with alias capabilities. | tight | `semSync_imp_semSend_of_own_subset_shr_semSync_tight` | an instance with `T = .rc .plain` (`hsub` holds, `SemSend` fails) |

Counterexample `guard_plain_semSync_not_semSend`: quoted above.

Counterexample `semSync_imp_semSend_of_own_subset_shr_semSync_tight`:

```lean
-- lean/ToySendSync/Results.lean:496-497
theorem semSync_imp_semSend_of_own_subset_shr_semSync_tight :
    (∀ e ∈ (fp (.rc .plain)).own, e ∈ (fp (.rc .plain)).shr) ∧ ¬ SemSend (.rc .plain) := …
```

**Non-vacuity witness.** `T = .arc .plain`. (`semSync_imp_semSend_of_own_subset_shr_nonvacuous`)

```lean
-- lean/ToySendSync/Results.lean:490-491
theorem semSync_imp_semSend_of_own_subset_shr_nonvacuous :
    (∀ e ∈ (fp (.arc .plain)).own, e ∈ (fp (.arc .plain)).shr) ∧ SemSync (.arc .plain) := …
```

**Non-claims.** Listed under **Boundaries** (global non-claims, then *Non-claims of each result*, `own-in-shared-sync-implies-send`); read them before relying on this result.

**Prior art.**

* Rust core library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/core/src/marker.rs: `pub unsafe auto trait Send` (line 92); `impl<T: PointeeSized> !Send for *const T {}` (line 97); `unsafe impl<T: Sync + PointeeSized> Send for &T {}` (line 105); `Sync` documentation (lines 511-539): "The precise definition is: a type `T` is [`Sync`] if and only if `&T` is [`Send`]", "`&mut T` is [`Send`] if and only if `T` is [`Send`]", "`&T` and `&mut T` are [`Sync`] if and only if `T` is [`Sync`]"; `pub unsafe auto trait Sync` (line 657); `impl<T: PointeeSized> !Sync for *const T {}` (line 672).
* Rust std library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/std/src/sync/poison/mutex.rs: `impl<T: ?Sized> !Send for MutexGuard<'_, T> {}` (line 289; lines 282-287: "On platforms that use POSIX threads ... there is a requirement to release mutex locks on the same thread they were acquired"); `unsafe impl<T: ?Sized + Sync> Sync for MutexGuard<'_, T> {}` (line 294; lines 291-292: a `&T` is obtainable from `&MutexGuard` via `Deref`).

**Design question.** Rust's `Send` and `Sync` are auto traits computed structurally with manual unsafe impls, and `T: Sync` is defined as `&T: Send`. What does each trait certify in a model with threads, shared references and interior mutability; when are the structural rules sound; which primitives need opt-outs/opt-ins and why; and which tempting rules are false?

Basis: execution (Lean kernel check) — every Lean statement quoted in this card (main theorem, companions, counterexamples, non-vacuity witness and positive control) is kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — **Claim:** the theorem is the model's form of the observation that a `Sync` type whose owner can do nothing that a sharer cannot do is also `Send`; `MutexGuard` is the documented type whose owner can do more (release the lock on drop). **Reasoning:** the counterexample to the containment hypothesis is `.guard .plain`, whose owner footprint contains the release event. **Sources:** the lines listed under **Prior art** above. This claim is not established by the Lean kernel.

### Card `unsafe-sync-obligation`

**Plain claim.** For every field type `f`, view `v` and impl flag `u`, `SemSync (.wrap f v u)` holds if and only if `SyncObligation f v` holds (every conflicting pair formed by an exposed shared capability on the other thread and an exposed shared capability or an alias capability of the field on the origin thread is never simultaneously enabled, and no exposed capability makes the other thread release an acquisition it did not make); this restates the definition of `SemSync` for wrappers, and the flag `u` does not occur on the right-hand side. Companion (`semSync_wrap_full_iff`): for every `f` and `u`, `SemSync (.wrap f .full u)` holds if and only if `SemSync f` holds, by `Iff.rfl`. When the obligation fails, the checker still accepts the unsafe impl: for `.wrap (.cell .plain) .full true`, `autoCheck stdTable` returns `true` for `Sync`, and the wrapper's shared footprint races with its shared and alias footprints (`unsafeSync_wrap_cell_full_accepted_but_racy`).

**Kind.** characterization. **Tier.** T0. **Depth.** definitional.

Statement (`semSync_wrap_iff_syncObligation`):

```lean
-- lean/ToySendSync/Results.lean:772-773
theorem semSync_wrap_iff_syncObligation (f : Ty) (v : View) (u : Bool) :
    SemSync (.wrap f v u) ↔ SyncObligation f v := …
```

Companion (`SyncObligation`): quoted in the Definitions section above.

Companion (`semSync_wrap_full_iff`):

```lean
-- lean/ToySendSync/Characterize.lean:189-189
theorem semSync_wrap_full_iff (f : Ty) (u : Bool) : SemSync (.wrap f .full u) ↔ SemSync f := …
```

Companion (`unsafeSync_wrap_cell_full_accepted_but_racy`):

```lean
-- lean/ToySendSync/Results.lean:946-949
theorem unsafeSync_wrap_cell_full_accepted_but_racy :
    (autoCheck stdTable (.wrap (.cell .plain) .full true)).2 = true ∧
      Race (fp (.wrap (.cell .plain) .full true)).shr
        ((fp (.wrap (.cell .plain) .full true)).shr ++ (fp (.wrap (.cell .plain) .full true)).alias) := …
```

Explicit form of the left-hand side of `semSync_wrap_iff_syncObligation`:

```lean
¬ Race (v.expose (fp f).shr) (v.expose (fp f).shr ++ (fp f).alias) ∧
  NoForeignRelease .other (v.expose (fp f).shr)
```

**Hypothesis ledger.** No hypotheses beyond the universally quantified variables.

**Non-vacuity witness.** `f = .cell .plain`, `v = .readOnly`: `SyncObligation (.cell .plain) .readOnly` holds. (`syncObligation_nonvacuous`)

```lean
-- lean/ToySendSync/Results.lean:955-955
theorem syncObligation_nonvacuous : SyncObligation (.cell .plain) .readOnly := …
```

**Non-claims.** Listed under **Boundaries** (global non-claims, then *Non-claims of each result*, `unsafe-sync-obligation`); read them before relying on this result.

**Prior art.**

* The Rustonomicon, chapter "Send and Sync", rust-lang/nomicon commit b0bb569883a3e65ab19d4f1adf1b8dbc1629d0a6, src/send-and-sync.md: lines 8-9 ("A type is Send if it is safe to send it to another thread"; "T is Sync if and only if `&T` is Send"); lines 20-29 (automatic derivation; `Cell`/`RefCell` not Sync; `Rc` neither); lines 177-205 (the obligations argued for `unsafe impl Send`/`Sync` on the `Carton` example).
* Rust core library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/core/src/sync/sync_view.rs: `unsafe impl<T: ?Sized> Sync for SyncView<T> {}` (lines 108-109: the impl at line 109, marked as unstable feature `exclusive_wrapper` by the attribute at line 108), justified because "a `&SyncView<T>` for non-`Sync` `T` has no API whatsoever" (lines 13-21).
* Ralf Jung, Jacques-Henri Jourdan, Robbert Krebbers, Derek Dreyer. "RustBelt: Securing the Foundations of the Rust Programming Language." Proc. ACM Program. Lang. 2(POPL), Article 66, January 2018. DOI 10.1145/3158154. Section 1.2 (Challenge #3) and Section 4.1: a type is Send if its ownership predicate does not depend on the thread-identifier parameter; Section 4.3 ("Interpreting shared references"): Sync means that the sharing predicate does not depend on the thread identifier, and the ownership predicate of a shared reference is defined from the sharing predicate; Section 2.5.1: "&T is Send if and only if T is Sync". RustBelt's predicates are thread-indexed Iris predicates, not race-freedom scenarios as in this package.

**Design question.** Rust's `Send` and `Sync` are auto traits computed structurally with manual unsafe impls, and `T: Sync` is defined as `&T: Send`. What does each trait certify in a model with threads, shared references and interior mutability; when are the structural rules sound; which primitives need opt-outs/opt-ins and why; and which tempting rules are false?

Basis: execution (Lean kernel check) — every Lean statement quoted in this card (main theorem, companions, counterexamples, non-vacuity witness and positive control) is kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — **Claim:** `SyncObligation f v` is the model's form of the obligation that the Rustonomicon argues for an `unsafe impl Sync` on a user type, and, like rustc, `autoCheck` accepts the unsafe impl without checking it. **Reasoning:** an `unsafe impl` is the programmer's assertion; the model records it as the wrapper flag, which the checker trusts and the semantics ignores. **Sources:** the Rustonomicon and RustBelt entries listed under **Prior art** above. This claim is not established by the Lean kernel.

### Card `wrap-view-restriction`

**Plain claim.** For every field type `f`, view `v` and impl flag `u` such that `SemSync f` holds (hypothesis), `SemSync (.wrap f v u)` holds: restricting the shared capabilities of a semantically `Sync` field by any view keeps the wrapper semantically `Sync`. Companion (`semSync_wrap_none`), with no hypothesis: for every `f` and `u`, `SemSync (.wrap f .none u)` holds.

**Kind.** theorem. **Tier.** T1. **Depth.** shallow.

Statement (`semSync_wrap_of_semSync`):

```lean
-- lean/ToySendSync/Characterize.lean:180-181
theorem semSync_wrap_of_semSync (f : Ty) (v : View) (u : Bool) :
    SemSync f → SemSync (.wrap f v u) := …
```

Companion (`semSync_wrap_none`):

```lean
-- lean/ToySendSync/Characterize.lean:192-192
theorem semSync_wrap_none (f : Ty) (u : Bool) : SemSync (.wrap f .none u) := …
```

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness | Counterexample | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `SemSync f` | A view that keeps a racing pair of the field's shared capabilities (for example the full view) keeps the race. | tight | `semSync_wrap_of_semSync_tight` | an instance with `f = .cell .plain`, `v = .full`, `u = false` (`SemSync f` fails and `SemSync (.wrap f v u)` fails) |

Counterexample `semSync_wrap_of_semSync_tight`:

```lean
-- lean/ToySendSync/Results.lean:961-962
theorem semSync_wrap_of_semSync_tight :
    ¬ SemSync (.cell .plain) ∧ ¬ SemSync (.wrap (.cell .plain) .full false) := …
```

**Non-vacuity witness.** `f = .arc .plain`, `v = .readOnly`, `u = false`: `SemSync (.arc .plain)` holds, and so does `SemSync (.wrap (.arc .plain) .readOnly false)`. (`semSync_wrap_of_semSync_nonvacuous`)

```lean
-- lean/ToySendSync/Results.lean:967-968
theorem semSync_wrap_of_semSync_nonvacuous :
    SemSync (.arc .plain) ∧ SemSync (.wrap (.arc .plain) .readOnly false) := …
```

**Non-claims.** Listed under **Boundaries** (global non-claims, then *Non-claims of each result*, `wrap-view-restriction`); read them before relying on this result.

**Prior art.**

* The Rustonomicon, chapter "Send and Sync", rust-lang/nomicon commit b0bb569883a3e65ab19d4f1adf1b8dbc1629d0a6, src/send-and-sync.md: lines 8-9 ("A type is Send if it is safe to send it to another thread"; "T is Sync if and only if `&T` is Send"); lines 20-29 (automatic derivation; `Cell`/`RefCell` not Sync; `Rc` neither); lines 177-205 (the obligations argued for `unsafe impl Send`/`Sync` on the `Carton` example).
* Rust core library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/core/src/sync/sync_view.rs: `unsafe impl<T: ?Sized> Sync for SyncView<T> {}` (lines 108-109: the impl at line 109, marked as unstable feature `exclusive_wrapper` by the attribute at line 108), justified because "a `&SyncView<T>` for non-`Sync` `T` has no API whatsoever" (lines 13-21).

**Design question.** Rust's `Send` and `Sync` are auto traits computed structurally with manual unsafe impls, and `T: Sync` is defined as `&T: Send`. What does each trait certify in a model with threads, shared references and interior mutability; when are the structural rules sound; which primitives need opt-outs/opt-ins and why; and which tempting rules are false?

Basis: execution (Lean kernel check) — every Lean statement quoted in this card (main theorem, companions, counterexamples, non-vacuity witness and positive control) is kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — **Claim:** exposing fewer operations of a field that is `Sync` keeps a wrapper `Sync`; the extreme case (exposing nothing) is the documented justification of the unsafe `Sync` impl of `SyncView`. **Reasoning:** every view selects a sublist of the field's shared capabilities, and restricting the events of either side to a sublist preserves race freedom and release affinity. **Sources:** the `sync_view.rs` lines listed under **Prior art** above. This claim is not established by the Lean kernel.

### Card `wrap-cell-obligation`

**Plain claim.** For every toy type `U` and flag `u`, a read-only wrapper over `Cell<U>` is semantically `Sync`, `SemSync (.wrap (.cell U) .readOnly u)`, if and only if `OwnReadsRaceFree U` holds: reads through the owner capabilities of `U` that a read-only view keeps (no access under an acquisition by the executing thread), executed by the other thread, race with no alias capability of `U`. A wrapper exposing the full shared API of `Cell<U>` is never semantically `Sync` (`not_semSync_wrap_cell_full`), and one exposing nothing always is (`semSync_wrap_none`). `SemSend U` implies `OwnReadsRaceFree U` (`ownReadsRaceFree_of_semSend`) and is not equivalent to it: `MutexGuard<plain>` is not semantically `Send`, satisfies `OwnReadsRaceFree`, and the read-only wrapper over `Cell<MutexGuard<plain>>` is semantically `Sync` for either flag (`wrap_cell_guard_plain_readOnly_semSync`). `OwnReadsRaceFree (.guard U)` holds if and only if `OwnReadsRaceFree U` holds (`ownReadsRaceFree_guard_iff`). For `U = .ref (.cell .plain)` the condition fails and, for either flag, the read-only wrapper over `Cell<U>` is not semantically `Sync` (`wrap_cell_ref_cell_readOnly_not_semSync`); for either flag, a read-only wrapper over `Arc<Cell<plain>>` is not semantically `Sync` either (`wrap_arc_cell_readOnly_not_semSync`).

**Kind.** characterization. **Tier.** T1. **Depth.** shallow.

Statement (`semSync_wrap_cell_readOnly_iff_ownReadsRaceFree`):

```lean
-- lean/ToySendSync/Results.lean:791-792
theorem semSync_wrap_cell_readOnly_iff_ownReadsRaceFree (U : Ty) (u : Bool) :
    SemSync (.wrap (.cell U) .readOnly u) ↔ OwnReadsRaceFree U := …
```

Companion (`not_semSync_wrap_cell_full`):

```lean
-- lean/ToySendSync/Results.lean:784-784
theorem not_semSync_wrap_cell_full (U : Ty) (u : Bool) : ¬ SemSync (.wrap (.cell U) .full u) := …
```

Companion (`semSync_wrap_none`):

```lean
-- lean/ToySendSync/Characterize.lean:192-192
theorem semSync_wrap_none (f : Ty) (u : Bool) : SemSync (.wrap f .none u) := …
```

Companion (`OwnReadsRaceFree`): quoted in the Definitions section above.

Companion (`ownReadsRaceFree_of_semSend`):

```lean
-- lean/ToySendSync/Results.lean:808-808
theorem ownReadsRaceFree_of_semSend (U : Ty) (h : SemSend U) : OwnReadsRaceFree U := …
```

Companion (`ownReadsRaceFree_guard_iff`):

```lean
-- lean/ToySendSync/Results.lean:253-253
theorem ownReadsRaceFree_guard_iff (U : Ty) : OwnReadsRaceFree (.guard U) ↔ OwnReadsRaceFree U := …
```

Companion (`wrap_cell_ref_cell_readOnly_not_semSync`):

```lean
-- lean/ToySendSync/Results.lean:821-822
theorem wrap_cell_ref_cell_readOnly_not_semSync (u : Bool) :
    ¬ OwnReadsRaceFree (.ref (.cell .plain)) ∧ ¬ SemSync (.wrap (.cell (.ref (.cell .plain))) .readOnly u) := …
```

Companion (`wrap_cell_guard_plain_readOnly_semSync`):

```lean
-- lean/ToySendSync/Results.lean:830-832
theorem wrap_cell_guard_plain_readOnly_semSync (u : Bool) :
    ¬ SemSend (.guard .plain) ∧ OwnReadsRaceFree (.guard .plain) ∧
      SemSync (.wrap (.cell (.guard .plain)) .readOnly u) := …
```

Companion (`wrap_arc_cell_readOnly_not_semSync`):

```lean
-- lean/ToySendSync/Results.lean:838-839
theorem wrap_arc_cell_readOnly_not_semSync (u : Bool) :
    ¬ SemSync (.wrap (.arc (.cell .plain)) .readOnly u) := …
```

Explicit form of the right-hand side of `semSync_wrap_cell_readOnly_iff_ownReadsRaceFree` (`OwnReadsRaceFree` unfolded):

```lean
¬ Race (View.expose .readOnly (fp U).own) (fp U).alias
```

**Hypothesis ledger.** No hypotheses beyond the universally quantified variables. The content condition is not vacuous: for `U = .ref (.cell .plain)` it fails and the wrapper is not semantically `Sync` (`wrap_cell_ref_cell_readOnly_not_semSync`); `SemSend U` is not equivalent to it: `MutexGuard<plain>` satisfies it without being semantically `Send` (`wrap_cell_guard_plain_readOnly_semSync`).

**Non-vacuity witness.** `U = .plain`: `OwnReadsRaceFree .plain` holds, and the read-only wrapper over `Cell<plain>` is semantically `Sync`. (`wrap_cell_plain_readOnly_nonvacuous`)

```lean
-- lean/ToySendSync/Results.lean:813-814
theorem wrap_cell_plain_readOnly_nonvacuous (u : Bool) :
    OwnReadsRaceFree .plain ∧ SemSync (.wrap (.cell .plain) .readOnly u) := …
```

**Non-claims.** Listed under **Boundaries** (global non-claims, then *Non-claims of each result*, `wrap-cell-obligation`); read them before relying on this result.

**Prior art.**

* The Rustonomicon, chapter "Send and Sync", rust-lang/nomicon commit b0bb569883a3e65ab19d4f1adf1b8dbc1629d0a6, src/send-and-sync.md: lines 8-9 ("A type is Send if it is safe to send it to another thread"; "T is Sync if and only if `&T` is Send"); lines 20-29 (automatic derivation; `Cell`/`RefCell` not Sync; `Rc` neither); lines 177-205 (the obligations argued for `unsafe impl Send`/`Sync` on the `Carton` example).
* Rust core library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/core/src/cell.rs: `unsafe impl<T: ?Sized> Send for Cell<T> where T: Send {}` (line 320); `impl<T: ?Sized> !Sync for Cell<T> {}` (line 328); `unsafe impl<T: ?Sized> Send for RefCell<T> where T: Send {}` (line 1439); `impl<T: ?Sized> !Sync for RefCell<T> {}` (line 1442).
* Rust core library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/core/src/cell.rs: `Cell::set` (line 436, in `impl<T> Cell<T>` at line 404), `Cell::replace` (line 513), `Cell::get` (line 555, in `impl<T: Copy> Cell<T>` at line 539), `Cell::take` (line 674): every one takes `&self` and moves, copies or drops the content; `RefCell::try_borrow_unguarded` (line 1395, an `unsafe fn`) reads the borrow flag (line 1396) without updating it.

**Design question.** Rust's `Send` and `Sync` are auto traits computed structurally with manual unsafe impls, and `T: Sync` is defined as `&T: Send`. What does each trait certify in a model with threads, shared references and interior mutability; when are the structural rules sound; which primitives need opt-outs/opt-ins and why; and which tempting rules are false?

Basis: execution (Lean kernel check) — every Lean statement quoted in this card (main theorem, companions, counterexamples, non-vacuity witness and positive control) is kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — **Claim:** for a user wrapper around `Cell<U>` with an `unsafe impl Sync` whose shared API performs reads alone, the model's obligation is `OwnReadsRaceFree U`. **Reasoning:** the documented `&self` operations of `Cell` copy the content out (`Cell::get` for `Copy` content) or move it out (`replace`, `take`), so a sharer reaches the owner capabilities of `U`; whether a particular Rust wrapper's API is read-only in the model's sense is a modeling question. **Sources:** the `cell.rs` and Rustonomicon lines listed under **Prior art** above. This claim is not established by the Lean kernel.

### Card `wrap-refcell-obligation`

**Plain claim.** For every toy type `U` and flag `u`, a read-only wrapper over `RefCell<U>` is semantically `Sync`, `SemSync (.wrap (.refCell U) .readOnly u)`, if and only if `ShrReadsRaceFree U` holds: reads through the shared capabilities of `U` that a read-only view keeps, executed by the other thread, race with no alias capability of `U`. For every `U`, the read-only view of the shared footprint of `RefCell<U>` is the borrow-flag read followed by the read-only view of the shared capabilities of `U` placed at the content position (`expose_readOnly_refCell_shr`): the flag write and every access under a mutable borrow are dropped. For every `U`, `OwnReadsRaceFree U` implies `ShrReadsRaceFree U` (`shrReadsRaceFree_of_ownReadsRaceFree`). The two conditions differ: for `W = .wrap (.ref (.cell .plain)) .none false`, `OwnReadsRaceFree W` fails and `ShrReadsRaceFree W` holds, and for either flag `u` the read-only wrapper over `Cell<W>` is not semantically `Sync` while the read-only wrapper over `RefCell<W>` is (`wrap_readOnly_cell_refCell_differ`). For `U = .ref (.cell .plain)`, `ShrReadsRaceFree U` fails and, for either flag, the read-only wrapper over `RefCell<U>` is not semantically `Sync` (`wrap_refCell_ref_cell_readOnly_not_semSync`); for `U = .plain` and either flag it is semantically `Sync` (`semSync_wrap_refCell_plain_readOnly`).

**Kind.** characterization. **Tier.** T1. **Depth.** shallow.

Statement (`semSync_wrap_refCell_readOnly_iff_shrReadsRaceFree`):

```lean
-- lean/ToySendSync/Results.lean:870-871
theorem semSync_wrap_refCell_readOnly_iff_shrReadsRaceFree (U : Ty) (u : Bool) :
    SemSync (.wrap (.refCell U) .readOnly u) ↔ ShrReadsRaceFree U := …
```

Companion (`ShrReadsRaceFree`): quoted in the Definitions section above.

Companion (`expose_readOnly_refCell_shr`):

```lean
-- lean/ToySendSync/Results.lean:856-858
theorem expose_readOnly_refCell_shr (U : Ty) :
    View.expose .readOnly (fp (.refCell U)).shr =
      [rootEv .rd] ++ place [] 0 (View.expose .readOnly (fp U).shr) := …
```

Companion (`shrReadsRaceFree_of_ownReadsRaceFree`):

```lean
-- lean/ToySendSync/Results.lean:884-885
theorem shrReadsRaceFree_of_ownReadsRaceFree (U : Ty) (h : OwnReadsRaceFree U) :
    ShrReadsRaceFree U := …
```

Companion (`wrap_readOnly_cell_refCell_differ`):

```lean
-- lean/ToySendSync/Results.lean:914-918
theorem wrap_readOnly_cell_refCell_differ (u : Bool) :
    ¬ OwnReadsRaceFree (.wrap (.ref (.cell .plain)) .none false) ∧
      ShrReadsRaceFree (.wrap (.ref (.cell .plain)) .none false) ∧
      ¬ SemSync (.wrap (.cell (.wrap (.ref (.cell .plain)) .none false)) .readOnly u) ∧
      SemSync (.wrap (.refCell (.wrap (.ref (.cell .plain)) .none false)) .readOnly u) := …
```

Companion (`wrap_refCell_ref_cell_readOnly_not_semSync`):

```lean
-- lean/ToySendSync/Results.lean:901-903
theorem wrap_refCell_ref_cell_readOnly_not_semSync (u : Bool) :
    ¬ ShrReadsRaceFree (.ref (.cell .plain)) ∧
      ¬ SemSync (.wrap (.refCell (.ref (.cell .plain))) .readOnly u) := …
```

Companion (`semSync_wrap_refCell_plain_readOnly`):

```lean
-- lean/ToySendSync/Results.lean:849-850
theorem semSync_wrap_refCell_plain_readOnly (u : Bool) :
    SemSync (.wrap (.refCell .plain) .readOnly u) := …
```

Explicit form of the right-hand side of `semSync_wrap_refCell_readOnly_iff_shrReadsRaceFree` (`ShrReadsRaceFree` unfolded):

```lean
¬ Race (View.expose .readOnly (fp U).shr) (fp U).alias
```

**Hypothesis ledger.** No hypotheses beyond the universally quantified variables `U` and `u`. The content condition is not vacuous: it fails for `U = .ref (.cell .plain)` (`wrap_refCell_ref_cell_readOnly_not_semSync`).

**Non-vacuity witness.** `U = .plain`: `ShrReadsRaceFree .plain` holds, and the read-only wrapper over `RefCell<plain>` is semantically `Sync`. (`wrap_refCell_plain_readOnly_nonvacuous`)

```lean
-- lean/ToySendSync/Results.lean:894-895
theorem wrap_refCell_plain_readOnly_nonvacuous (u : Bool) :
    ShrReadsRaceFree .plain ∧ SemSync (.wrap (.refCell .plain) .readOnly u) := …
```

**Non-claims.** Listed under **Boundaries** (global non-claims, then *Non-claims of each result*, `wrap-refcell-obligation`); read them before relying on this result.

**Prior art.**

* The Rustonomicon, chapter "Send and Sync", rust-lang/nomicon commit b0bb569883a3e65ab19d4f1adf1b8dbc1629d0a6, src/send-and-sync.md: lines 8-9 ("A type is Send if it is safe to send it to another thread"; "T is Sync if and only if `&T` is Send"); lines 20-29 (automatic derivation; `Cell`/`RefCell` not Sync; `Rc` neither); lines 177-205 (the obligations argued for `unsafe impl Send`/`Sync` on the `Carton` example).
* Rust core library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/core/src/cell.rs: `pub struct RefCell<T: ?Sized>` (line 852) has the borrow flag field `borrow: Cell<BorrowCounter>` (line 853); `RefCell::borrow(&self) -> Ref<'_, T>` (line 1124, through `try_borrow` at line 1161) and `RefCell::borrow_mut(&self) -> RefMut<'_, T>` (line 1224, through `try_borrow_mut` at line 1258) update the flag; `RefCell::replace` (line 1028, body `mem::replace(&mut self.borrow_mut(), t)` at line 1029), `replace_with` (line 1052), `swap` (line 1082) and `take` (line 1433, which calls `replace`) borrow mutably; `RefCell::get_mut(&mut self)` (line 1333) and `into_inner(self)` (line 998) reach the content without the flag; `RefCell::try_borrow_unguarded` (line 1395, an `unsafe fn`) reads the flag (line 1396) without updating it.
* Rust core library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/core/src/cell.rs: `Cell::set` (line 436, in `impl<T> Cell<T>` at line 404), `Cell::replace` (line 513), `Cell::get` (line 555, in `impl<T: Copy> Cell<T>` at line 539), `Cell::take` (line 674): every one takes `&self` and moves, copies or drops the content; `RefCell::try_borrow_unguarded` (line 1395, an `unsafe fn`) reads the borrow flag (line 1396) without updating it.

**Design question.** Rust's `Send` and `Sync` are auto traits computed structurally with manual unsafe impls, and `T: Sync` is defined as `&T: Send`. What does each trait certify in a model with threads, shared references and interior mutability; when are the structural rules sound; which primitives need opt-outs/opt-ins and why; and which tempting rules are false?

Basis: execution (Lean kernel check) — every Lean statement quoted in this card (main theorem, companions, counterexamples, non-vacuity witness and positive control) is kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — **Claim:** for a user wrapper around `RefCell<U>` whose shared API never writes the borrow flag (as with the unsafe `RefCell::try_borrow_unguarded`, documented to read the flag without updating it), the model's obligation is `ShrReadsRaceFree U`; a wrapper exposing `RefCell::borrow` writes the flag and is not read-only in this sense. **Reasoning:** a shared borrow reaches the shared capabilities of `U`, a mutable borrow registered in the flag reaches its owner capabilities, and the read-only view drops the flag write and every access under a mutable borrow. **Sources:** the `cell.rs` lines listed under **Prior art** above. This claim is not established by the Lean kernel.

### Card `wrap-rc-obligation`

**Plain claim.** For every toy type `U`, view `v` and flag `u`, `SemSync (.wrap (.rc U) v u)` holds if and only if `v = .none`: a read-only view still exposes the non-atomic count read, which races with count writes through other handles.

**Kind.** characterization. **Tier.** T1. **Depth.** shallow.

Statement (`semSync_wrap_rc_iff`):

```lean
-- lean/ToySendSync/Results.lean:927-928
theorem semSync_wrap_rc_iff (U : Ty) (v : View) (u : Bool) :
    SemSync (.wrap (.rc U) v u) ↔ v = .none := …
```

**Hypothesis ledger.** No hypotheses beyond the universally quantified variables.

**Non-vacuity witness.** `v = .none`. (`wrap_rc_none_semSync_not_semSend`)

**Non-claims.** Listed under **Boundaries** (global non-claims, then *Non-claims of each result*, `wrap-rc-obligation`); read them before relying on this result.

**Prior art.**

* Rust alloc library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/alloc/src/rc.rs: `impl<T: ?Sized, A: Allocator> !Send for Rc<T, A> {}` (line 334); `impl<T: ?Sized, A: Allocator> !Sync for Rc<T, A> {}` (line 342); and library/core/src/marker.rs lines 74-79 (the `Send` documentation's example of two threads updating an `Rc` reference count).
* Rust alloc library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/alloc/src/rc.rs: `Rc::strong_count` (lines 1897-1899) returns `this.inner().strong()` (line 1898), a read of the non-atomic count; `Rc::weak_count` (line 1879); `Deref::deref` for `Rc` (lines 2535-2541) returns `&self.inner().value` and reads no count.
* Rust core library, rust-lang/rust commit 0ef1bc386059596dada8fb65b50425aab2ea637a (tag 1.100.0), library/core/src/sync/sync_view.rs: `unsafe impl<T: ?Sized> Sync for SyncView<T> {}` (lines 108-109: the impl at line 109, marked as unstable feature `exclusive_wrapper` by the attribute at line 108), justified because "a `&SyncView<T>` for non-`Sync` `T` has no API whatsoever" (lines 13-21).

**Design question.** Rust's `Send` and `Sync` are auto traits computed structurally with manual unsafe impls, and `T: Sync` is defined as `&T: Send`. What does each trait certify in a model with threads, shared references and interior mutability; when are the structural rules sound; which primitives need opt-outs/opt-ins and why; and which tempting rules are false?

Basis: execution (Lean kernel check) — every Lean statement quoted in this card (main theorem, companions, counterexamples, non-vacuity witness and positive control) is kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — **Claim:** a user wrapper around `Rc<U>` that exposes the count readers `Rc::strong_count` or `Rc::weak_count` has no read-only view that is `Sync` in the model. **Reasoning:** the documentation shows that these readers read the non-atomic count, while `Deref::deref` for `Rc` reads no count; a wrapper exposing `Deref` alone is not represented. **Sources:** the `rc.rs` and `sync_view.rs` lines listed under **Prior art** above. This claim is not established by the Lean kernel.

### Card `checker-incomplete`

**Plain claim.** The wrapper `.wrap (.cell .plain) .readOnly false` (no unsafe impl) satisfies `SemSync`, and its shared reference satisfies `SemSend`, while `autoCheck stdTable` rejects both.

**Kind.** counterexample. **Tier.** T1. **Depth.** shallow.

Statement (`autoCheck_std_incomplete`):

```lean
-- lean/ToySendSync/Results.lean:977-981
theorem autoCheck_std_incomplete :
    SemSync (.wrap (.cell .plain) .readOnly false) ∧
      (autoCheck stdTable (.wrap (.cell .plain) .readOnly false)).2 = false ∧
      SemSend (.ref (.wrap (.cell .plain) .readOnly false)) ∧
      (autoCheck stdTable (.ref (.wrap (.cell .plain) .readOnly false))).1 = false := …
```

**Hypothesis ledger.** No hypotheses beyond the universally quantified variables.

**Non-vacuity witness.** Concrete closed statement. (`autoCheck_std_incomplete`)

**Non-claims.** Listed under **Boundaries** (global non-claims, then *Non-claims of each result*, `checker-incomplete`); read them before relying on this result.

**Prior art.**

* The Rust Reference, rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c, src/special-types-and-traits.md, rules `lang-types.auto-traits.*` (lines 156-181): automatic implementation for `&T`, `&mut T` and aggregates ("Structs, enums, unions, and tuples implement the trait if all of their fields do"), suppression of the automatic implementation by a generic impl ("the standard library implements `Send` for all `&T` where `T` is `Sync`"), and negative impls.
* The Rustonomicon, chapter "Send and Sync", rust-lang/nomicon commit b0bb569883a3e65ab19d4f1adf1b8dbc1629d0a6, src/send-and-sync.md: lines 8-9 ("A type is Send if it is safe to send it to another thread"; "T is Sync if and only if `&T` is Send"); lines 20-29 (automatic derivation; `Cell`/`RefCell` not Sync; `Rc` neither); lines 177-205 (the obligations argued for `unsafe impl Send`/`Sync` on the `Carton` example).

**Design question.** Rust's `Send` and `Sync` are auto traits computed structurally with manual unsafe impls, and `T: Sync` is defined as `&T: Send`. What does each trait certify in a model with threads, shared references and interior mutability; when are the structural rules sound; which primitives need opt-outs/opt-ins and why; and which tempting rules are false?

Basis: execution (Lean kernel check) — every Lean statement quoted in this card (main theorem, companions, counterexamples, non-vacuity witness and positive control) is kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — **Claim:** structural derivation is incomplete in the model, in the same way as Rust requires an `unsafe impl Sync` for a struct with a `Cell` field even when its API reads alone. **Reasoning:** by the documented auto-trait rule, a struct implements `Sync` automatically if all its fields do, and `Cell` is not `Sync`. **Sources:** the Reference and Rustonomicon lines listed under **Prior art** above. This claim is not established by the Lean kernel.

### Card `structural-constructors`

**Plain claim.** For all toy types `A` and `B`, `SemSend (.prod A B)` holds if and only if `SemSend A` and `SemSend B` hold, and `SemSync (.prod A B)` holds if and only if `SemSync A` and `SemSync B` hold (`semSync_prod_iff`); the same two characterizations hold for `.sum A B` (`semSend_sum_iff`, `semSync_sum_iff`, which reuse the product proofs because `fp (.sum A B) = fp (.prod A B)` for all `A` and `B`, by `rfl`: `fp_sum_eq_prod`). For every toy type `U`, `SemSend (.box U) ↔ SemSend U` and `SemSync (.box U) ↔ SemSync U` (`semSend_box_iff`, `semSync_box_iff`), and for every view `v` and flag `u`, `SemSend (.wrap U v u) ↔ SemSend U` (`semSend_wrap_iff`); these three hold by `Iff.rfl`.

**Kind.** characterization. **Tier.** T1. **Depth.** shallow.

Statement (`semSend_prod_iff`):

```lean
-- lean/ToySendSync/Characterize.lean:153-153
theorem semSend_prod_iff (A B : Ty) : SemSend (.prod A B) ↔ SemSend A ∧ SemSend B := …
```

Companion (`semSync_prod_iff`):

```lean
-- lean/ToySendSync/Characterize.lean:162-162
theorem semSync_prod_iff (A B : Ty) : SemSync (.prod A B) ↔ SemSync A ∧ SemSync B := …
```

Companion (`semSend_sum_iff`):

```lean
-- lean/ToySendSync/Characterize.lean:171-171
theorem semSend_sum_iff (A B : Ty) : SemSend (.sum A B) ↔ SemSend A ∧ SemSend B := …
```

Companion (`semSync_sum_iff`):

```lean
-- lean/ToySendSync/Characterize.lean:174-174
theorem semSync_sum_iff (A B : Ty) : SemSync (.sum A B) ↔ SemSync A ∧ SemSync B := …
```

Companion (`semSend_box_iff`):

```lean
-- lean/ToySendSync/Characterize.lean:134-134
theorem semSend_box_iff (U : Ty) : SemSend (.box U) ↔ SemSend U := …
```

Companion (`semSync_box_iff`):

```lean
-- lean/ToySendSync/Characterize.lean:136-136
theorem semSync_box_iff (U : Ty) : SemSync (.box U) ↔ SemSync U := …
```

Companion (`semSend_wrap_iff`):

```lean
-- lean/ToySendSync/Characterize.lean:177-177
theorem semSend_wrap_iff (f : Ty) (v : View) (u : Bool) : SemSend (.wrap f v u) ↔ SemSend f := …
```

Companion (`fp_sum_eq_prod`):

```lean
-- lean/ToySendSync/Results.lean:427-427
theorem fp_sum_eq_prod (A B : Ty) : fp (.sum A B) = fp (.prod A B) := …
```

**Hypothesis ledger.** No hypotheses beyond the universally quantified variables.

**Non-vacuity witness.** `A = B = .plain`. (`prod_plain_nonvacuous`)

```lean
-- lean/ToySendSync/Results.lean:420-421
theorem prod_plain_nonvacuous :
    SemSend (.prod .plain .plain) ∧ SemSync (.prod .plain .plain) ∧ SemSend .plain ∧ SemSync .plain := …
```

**Non-claims.** Listed under **Boundaries** (global non-claims, then *Non-claims of each result*, `structural-constructors`); read them before relying on this result.

**Prior art.**

* The Rust Reference, rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c, src/special-types-and-traits.md, rules `lang-types.auto-traits.*` (lines 156-181): automatic implementation for `&T`, `&mut T` and aggregates ("Structs, enums, unions, and tuples implement the trait if all of their fields do"), suppression of the automatic implementation by a generic impl ("the standard library implements `Send` for all `&T` where `T` is `Sync`"), and negative impls.
* RustBelt (Jung, Jourdan, Krebbers, Dreyer, POPL 2018, DOI 10.1145/3158154), Section 4.2: products are interpreted by separating conjunction of the components' ownership predicates, and owned pointers by the ownership predicate of the pointee, so thread independence of the components gives thread independence of the product.

**Design question.** Rust's `Send` and `Sync` are auto traits computed structurally with manual unsafe impls, and `T: Sync` is defined as `&T: Send`. What does each trait certify in a model with threads, shared references and interior mutability; when are the structural rules sound; which primitives need opt-outs/opt-ins and why; and which tempting rules are false?

Basis: execution (Lean kernel check) — every Lean statement quoted in this card (main theorem, companions, counterexamples, non-vacuity witness and positive control) is kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — **Claim:** the characterizations agree with the documented auto-trait rule "Structs, enums, unions, and tuples implement the trait if all of their fields do" for products and sums, and with the rules for `Box`. **Reasoning:** `.sum A B` has the footprint of `.prod A B`, so the sum case is modelled without a discriminant and without variant exclusivity. **Sources:** the Reference lines and RustBelt section listed under **Prior art** above. This claim is not established by the Lean kernel.

### Card `definition-examples`

**Plain claim.** The core definitions admit their intended positive examples and reject their intended negative examples: `Race`, `Compatible`, `NoForeignRelease`, `RelNamesAcq`, `View.expose` (with `Ev.acquires`), `fp`, `SemSend`, `SemSync`, `autoCheck`, `TableSound`, `ImplsSound`, `WrapFree`, `SyncObligation`, `OwnReadsRaceFree` and `ShrReadsRaceFree`, each on the concrete instances stated in the listed theorems. Every listed theorem is a closed statement about concrete instances.

**Kind.** theorem. **Tier.** T0. **Depth.** definitional.

Statement (`compatible_example_via_via`):

```lean
-- lean/ToySendSync/Results.lean:38-38
theorem compatible_example_via_via : Compatible [.via []] [.via []] := …
```

Statement (`not_compatible_example_uniq_via`):

```lean
-- lean/ToySendSync/Results.lean:42-42
theorem not_compatible_example_uniq_via : ¬ Compatible [.uniq []] [.via []] := …
```

Statement (`race_example_write_read`):

```lean
-- lean/ToySendSync/Results.lean:13-13
theorem race_example_write_read : Race [rootEv .wr] [rootEv .rd] := …
```

Statement (`race_example_locked_vs_unlocked`):

```lean
-- lean/ToySendSync/Results.lean:33-33
theorem race_example_locked_vs_unlocked : Race [rootEv .wr [.held [] .fresh]] [rootEv .wr] := …
```

Statement (`not_race_example_read_read`):

```lean
-- lean/ToySendSync/Results.lean:17-17
theorem not_race_example_read_read : ¬ Race [rootEv .rd] [rootEv .rd] := …
```

Statement (`not_race_example_atomic_atomic`):

```lean
-- lean/ToySendSync/Results.lean:21-21
theorem not_race_example_atomic_atomic : ¬ Race [rootEv .atomic] [rootEv .atomic] := …
```

Statement (`not_race_example_locked_writes`):

```lean
-- lean/ToySendSync/Results.lean:26-27
theorem not_race_example_locked_writes :
    ¬ Race [rootEv .wr [.held [] .fresh]] [rootEv .wr [.held [] .fresh]] := …
```

Statement (`nfr_example`):

```lean
-- lean/ToySendSync/Results.lean:46-46
theorem nfr_example : NoForeignRelease .other [rootEv .rd, rootEv .wr] := …
```

Statement (`nfr_example_fresh_release`):

```lean
-- lean/ToySendSync/Results.lean:50-50
theorem nfr_example_fresh_release : NoForeignRelease .other [rootEv .rel [.held [] .fresh]] := …
```

Statement (`nfr_example_precondition`):

```lean
-- lean/ToySendSync/Results.lean:56-57
theorem nfr_example_precondition :
    NoForeignRelease .other [⟨.rel, [0], [.held [] (.guard []), .held [0] .fresh]⟩] := …
```

Statement (`nfr_example_unnamed_release`):

```lean
-- lean/ToySendSync/Results.lean:102-103
theorem nfr_example_unnamed_release :
    NoForeignRelease .other [rootEv .rel []] ∧ ¬ RelNamesAcq [rootEv .rel []] := …
```

Statement (`relNamesAcq_example`):

```lean
-- lean/ToySendSync/Results.lean:111-111
theorem relNamesAcq_example : RelNamesAcq [rootEv .rel [.held [] (.guard [])]] := …
```

Statement (`not_nfr_example`):

```lean
-- lean/ToySendSync/Results.lean:67-67
theorem not_nfr_example : ¬ NoForeignRelease .other [rootEv .rel [.held [] (.guard [])]] := …
```

Statement (`not_nfr_example_placed`):

```lean
-- lean/ToySendSync/Results.lean:72-73
theorem not_nfr_example_placed :
    ¬ NoForeignRelease .other [⟨.rel, [0], [.held [] .fresh, .held [0] (.guard [0])]⟩] := …
```

Statement (`expose_readOnly_example`):

```lean
-- lean/ToySendSync/Results.lean:80-81
theorem expose_readOnly_example :
    View.expose .readOnly [rootEv .rd, rootEv .wr, rootEv .atomic, rootEv .rel] = [rootEv .rd] := …
```

Statement (`expose_readOnly_example_acquires`):

```lean
-- lean/ToySendSync/Results.lean:87-89
theorem expose_readOnly_example_acquires :
    View.expose .readOnly [rootEv .rd [.held [] .fresh], rootEv .rd [.held [] (.guard [])]] =
      [rootEv .rd [.held [] (.guard [])]] := …
```

Statement (`expose_readOnly_mutex_example`):

```lean
-- lean/ToySendSync/Results.lean:95-96
theorem expose_readOnly_mutex_example :
    View.expose .readOnly (fp (.mutex (.ref (.cell .plain)))).shr = [] := …
```

Statement (`fp_cell_plain`):

```lean
-- lean/ToySendSync/Results.lean:195-198
theorem fp_cell_plain :
    fp (.cell .plain) =
      ⟨[rootEv .rd, rootEv .wr, ⟨.rd, [0], []⟩, ⟨.wr, [0], []⟩],
        [rootEv .rd, rootEv .wr, ⟨.rd, [0], []⟩, ⟨.wr, [0], []⟩], []⟩ := …
```

Statement (`fp_refCell_plain`):

```lean
-- lean/ToySendSync/Results.lean:203-208
theorem fp_refCell_plain :
    fp (.refCell .plain) =
      ⟨[⟨.rd, [0], []⟩, ⟨.wr, [0], []⟩, rootEv .rd, rootEv .wr, ⟨.rd, [0], []⟩,
          ⟨.rd, [0], [.held [] .fresh]⟩, ⟨.wr, [0], [.held [] .fresh]⟩],
        [rootEv .rd, rootEv .wr, ⟨.rd, [0], []⟩, ⟨.rd, [0], [.held [] .fresh]⟩,
          ⟨.wr, [0], [.held [] .fresh]⟩], []⟩ := …
```

Statement (`fp_shr_cell_ne_refCell_plain`):

```lean
-- lean/ToySendSync/Results.lean:211-211
theorem fp_shr_cell_ne_refCell_plain : (fp (.cell .plain)).shr ≠ (fp (.refCell .plain)).shr := …
```

Statement (`semSend_examples`):

```lean
-- lean/ToySendSync/Results.lean:215-217
theorem semSend_examples :
    SemSend .plain ∧ SemSend (.cell .plain) ∧ SemSend (.arc .plain) ∧
      SemSend (.mutex (.cell .plain)) ∧ SemSend (.ref (.mutex (.cell .plain))) := …
```

Statement (`not_semSend_examples`):

```lean
-- lean/ToySendSync/Results.lean:224-225
theorem not_semSend_examples :
    ¬ SemSend (.rc .plain) ∧ ¬ SemSend (.guard .plain) ∧ ¬ SemSend (.ref (.cell .plain)) := …
```

Statement (`semSync_examples`):

```lean
-- lean/ToySendSync/Results.lean:229-231
theorem semSync_examples :
    SemSync .plain ∧ SemSync (.mutex (.cell .plain)) ∧ SemSync (.arc .plain) ∧
      SemSync (.guard .plain) := …
```

Statement (`not_semSync_examples`):

```lean
-- lean/ToySendSync/Results.lean:236-237
theorem not_semSync_examples :
    ¬ SemSync (.cell .plain) ∧ ¬ SemSync (.refCell .plain) ∧ ¬ SemSync (.rc .plain) := …
```

Statement (`autoCheck_examples`):

```lean
-- lean/ToySendSync/Results.lean:241-248
theorem autoCheck_examples :
    autoCheck stdTable (.arc .plain) = (true, true) ∧
      autoCheck stdTable (.arc (.cell .plain)) = (false, false) ∧
      autoCheck stdTable (.mutex (.cell .plain)) = (true, true) ∧
      autoCheck stdTable (.guard .plain) = (false, true) ∧
      autoCheck stdTable (.ref (.cell .plain)) = (false, false) ∧
      autoCheck stdTable (.wrap (.cell .plain) .readOnly false) = (true, false) ∧
      autoCheck stdTable (.wrap (.cell .plain) .readOnly true) = (true, true) := …
```

Statement (`not_tableSound_rcSendTable`):

```lean
-- lean/ToySendSync/Results.lean:992-992
theorem not_tableSound_rcSendTable : ¬ TableSound rcSendTable := …
```

Statement (`tableSound_noImplTable`):

```lean
-- lean/ToySendSync/Results.lean:620-620
theorem tableSound_noImplTable : TableSound noImplTable := …
```

Statement (`implsSound_examples`):

```lean
-- lean/ToySendSync/Results.lean:998-999
theorem implsSound_examples :
    ImplsSound (.wrap (.cell .plain) .readOnly true) ∧ ¬ ImplsSound (.wrap (.cell .plain) .full true) := …
```

Statement (`wrapFree_examples`):

```lean
-- lean/ToySendSync/Results.lean:1004-1004
theorem wrapFree_examples : WrapFree (.arc (.mutex (.cell .plain))) ∧ ¬ WrapFree (.wrap .plain .full false) := …
```

Statement (`not_syncObligation_cell_full`):

```lean
-- lean/ToySendSync/Results.lean:1008-1008
theorem not_syncObligation_cell_full : ¬ SyncObligation (.cell .plain) .full := …
```

Statement (`ownReadsRaceFree_examples`):

```lean
-- lean/ToySendSync/Results.lean:264-266
theorem ownReadsRaceFree_examples :
    OwnReadsRaceFree .plain ∧ OwnReadsRaceFree (.guard .plain) ∧
      ¬ OwnReadsRaceFree (.ref (.cell .plain)) ∧ ¬ OwnReadsRaceFree (.rc .plain) := …
```

Statement (`shrReadsRaceFree_examples`):

```lean
-- lean/ToySendSync/Results.lean:277-279
theorem shrReadsRaceFree_examples :
    ShrReadsRaceFree .plain ∧ ShrReadsRaceFree (.wrap (.ref (.cell .plain)) .none false) ∧
      ¬ ShrReadsRaceFree (.ref (.cell .plain)) ∧ ¬ ShrReadsRaceFree (.rc .plain) := …
```

Companion (`Path`): quoted in the Definitions section above.

Companion (`Tid`): quoted in the Definitions section above.

Companion (`Tid.flip`): quoted in the Definitions section above.

Companion (`Acq`): quoted in the Definitions section above.

Companion (`Claim`): quoted in the Definitions section above.

Companion (`Claim.path`): quoted in the Definitions section above.

Companion (`Kind`): quoted in the Definitions section above.

Companion (`Kind.isAccess`): quoted in the Definitions section above.

Companion (`Kind.isWrite`): quoted in the Definitions section above.

Companion (`Kind.isAtomic`): quoted in the Definitions section above.

Companion (`Kind.isRead`): quoted in the Definitions section above.

Companion (`Ev`): quoted in the Definitions section above.

Companion (`Claim.isFresh`): quoted in the Definitions section above.

Companion (`Ev.acquires`): quoted in the Definitions section above.

Companion (`Holder`): quoted in the Definitions section above.

Companion (`Snap`): quoted in the Definitions section above.

Companion (`Acq.holder`): quoted in the Definitions section above.

Companion (`Sat`): quoted in the Definitions section above.

Companion (`SatAll`): quoted in the Definitions section above.

Companion (`Compatible`): quoted in the Definitions section above.

Companion (`Concurrent`): quoted in the Definitions section above.

Companion (`Conflicting`): quoted in the Definitions section above.

Companion (`Race`): quoted in the Definitions section above.

Companion (`Acq.maker`): quoted in the Definitions section above.

Companion (`NoForeignRelease`): quoted in the Definitions section above.

Companion (`RelNamesAcq`): quoted in the Definitions section above.

Companion (`Holder.reloc`): quoted in the Definitions section above.

Companion (`Acq.reloc`): quoted in the Definitions section above.

Companion (`Claim.reloc`): quoted in the Definitions section above.

Companion (`Ev.place`): quoted in the Definitions section above.

Companion (`place`): quoted in the Definitions section above.

Companion (`rootEv`): quoted in the Definitions section above.

Companion (`View`): quoted in the Definitions section above.

Companion (`View.expose`): quoted in the Definitions section above.

Companion (`Ty`): quoted in the Definitions section above.

Companion (`Fp`): quoted in the Definitions section above.

Companion (`fp`): quoted in the Definitions section above.

Companion (`SemSend`): quoted in the Definitions section above.

Companion (`SemSync`): quoted in the Definitions section above.

Companion (`Prim`): quoted in the Definitions section above.

Companion (`Prim.apply`): quoted in the Definitions section above.

Companion (`Rule`): quoted in the Definitions section above.

Companion (`Rule.eval`): quoted in the Definitions section above.

Companion (`Rule.Holds`): quoted in the Definitions section above.

Companion (`Table`): quoted in the Definitions section above.

Companion (`stdTable`): quoted in the Definitions section above.

Companion (`autoCheck`): quoted in the Definitions section above.

Companion (`TableSound`): quoted in the Definitions section above.

Companion (`ImplsSound`): quoted in the Definitions section above.

Companion (`WrapFree`): quoted in the Definitions section above.

Companion (`SyncObligation`): quoted in the Definitions section above.

Companion (`OwnReadsRaceFree`): quoted in the Definitions section above.

Companion (`ShrReadsRaceFree`): quoted in the Definitions section above.

Companion (`rcSendTable`): quoted in the Definitions section above.

Companion (`noImplTable`): quoted in the Definitions section above.

**Hypothesis ledger.** No hypotheses beyond the universally quantified variables.

**Non-vacuity witness.** Closed statements about concrete instances; for example `semSend_examples` (five concrete types are semantically `Send`). (`semSend_examples`)

**Non-claims.** Listed under **Boundaries** (global non-claims, then *Non-claims of each result*, `definition-examples`); read them before relying on this result.

**Prior art.**

* The Rustonomicon, chapter "Send and Sync", rust-lang/nomicon commit b0bb569883a3e65ab19d4f1adf1b8dbc1629d0a6, src/send-and-sync.md: lines 8-9 ("A type is Send if it is safe to send it to another thread"; "T is Sync if and only if `&T` is Send"); lines 20-29 (automatic derivation; `Cell`/`RefCell` not Sync; `Rc` neither); lines 177-205 (the obligations argued for `unsafe impl Send`/`Sync` on the `Carton` example).

**Design question.** Rust's `Send` and `Sync` are auto traits computed structurally with manual unsafe impls, and `T: Sync` is defined as `&T: Send`. What does each trait certify in a model with threads, shared references and interior mutability; when are the structural rules sound; which primitives need opt-outs/opt-ins and why; and which tempting rules are false?

Basis: execution (Lean kernel check) — every Lean statement quoted in this card (main theorem, companions, counterexamples, non-vacuity witness and positive control) is kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — this card makes no claim about a real system; its theorems test the model's definitions on concrete instances.

## Boundaries

### Global non-claims (they apply to every result)

* Model–system relation: none proved. These are statements about the toy capability model `Toy.SendSync`; they neither establish nor refute the corresponding claims about Rust's `Send` and `Sync` traits, rustc's auto-trait implementation, or the standard library types `Cell`, `RefCell`, `Rc`, `Arc`, `Mutex`, `MutexGuard`. No embedding, abstraction or simulation between the model and Rust is proved.
* No result quantifies over executions, schedules or runs of a generated semantics. A race is a conflicting pair of events whose claims are jointly satisfiable in some synchronization snapshot, and every snapshot counts. Race freedom in `Toy.SendSync` is not a conservative statement about Rust executions; wherever a card says that a snapshot used by a race witness corresponds to a state of a Rust program, that is a modeling-bridge remark (not proved here).
* The footprint table `fp` and the views of `View.expose` are modeling choices that may omit or merge operations of real types.
* `Ty` is finite and monomorphic (see **Applicability**); the theorems neither establish nor refute anything about the type features it omits.
* Non-vacuity witnesses and counterexamples are concrete toy types; they do not show that any particular Rust type satisfies or violates a hypothesis.

### Non-claims of each result (verbatim from `results.json`)

#### `link-sync-iff-ref-send`

* Proved by `Iff.rfl`: the link is a consequence of how the footprint of `.ref T` is chosen, not a property discovered about an independent semantics of `Send`.
* A different but plausible choice, for example letting the lender of a borrow keep `alias T` without `shr T`, would break the link (not proved here).
* `fp (.refMut U)` is defined as `fp U`, so the model does not distinguish owning a `U` from holding `&mut U`. In Rust, ownership moves through `&mut T` by `mem::swap`/`mem::replace`, and dropping `&mut MutexGuard` does not unlock; the definition collapses this into the owner capabilities of `U` (for example `SemSend (.refMut (.guard .plain))` fails through the guard's own release event, not through a swap, by `semSend_refMut_iff` and `not_semSend_guard`).
* Locations are path-relative: a location names the value at a position, not a particular value moved into or out of it over time (for example by `mem::replace` through `&mut T` or through a guard).
* In Rust, `unsafe impl<T: Sync + PointeeSized> Send for &T {}` gives `T: Sync` ⇒ `&T: Send`; whether rustc's trait solver derives `T: Sync` from a where-clause `&'a T: Send` is not addressed. Sending `&'a T` to `std::thread::spawn` also needs `'a = 'static` unless scoped threads are used; lifetimes are not modelled.
* Model–system relation: none proved. These are statements about the toy capability model `Toy.SendSync`; they neither establish nor refute the corresponding claims about Rust's `Send` and `Sync` traits, rustc's auto-trait implementation, or the standard library types `Cell`, `RefCell`, `Rc`, `Arc`, `Mutex`, `MutexGuard`.

#### `structural-soundness`

* This card states soundness; it does not say the checker accepts every semantically `Send`/`Sync` type; see `autoCheck_std_incomplete` and `autoCheck_std_exact_of_wrapFree`.
* The structural constructors `.box`, `.ref`, `.refMut`, `.prod`, `.sum` and the wrapper rule are fixed in `autoCheck`; the six primitive rules are the table parameters. Unsafe `Send` impls are not modelled.
* The tightness witnesses use one concrete type each (`.rc .plain` with `rcSendTable`; `.wrap (.cell .plain) .full true` with `stdTable`).
* `Ty` is finite and monomorphic: it has no recursive types (for which rustc resolves auto traits coinductively), no generic user wrappers, no negative impls on user types, no multi-field wrappers, and no `UnsafeCell`, raw pointers, `PhantomData`, `dyn Trait`, closures or `async` futures. The theorem neither establishes nor refutes anything about those.
* Model–system relation: none proved. These are statements about the toy capability model `Toy.SendSync`; they neither establish nor refute the corresponding claims about Rust's `Send` and `Sync` traits, rustc's auto-trait implementation, or the standard library types `Cell`, `RefCell`, `Rc`, `Arc`, `Mutex`, `MutexGuard`.

#### `std-table-sound`

* `stdTable` transcribes the documented impl bounds of the cited standard-library revision; that transcription is a modeling bridge, not a checked fact.
* `TableSound` constrains positive rules alone: the table with no positive rule satisfies it too (`tableSound_noImplTable`). That `stdTable`'s rules accept every semantically `Send`/`Sync` wrapper-free type is the separate result `autoCheck_std_exact_of_wrapFree`.
* `RwLock` is not in the table. In the cited standard library `RwLock<T>: Sync` requires `T: Send + Sync`, unlike `Mutex<T>: Sync`, which requires `T: Send`; the `Mutex` rule is not a statement about reader-writer locks.
* `Kind.atomic` treats atomic read-modify-writes as pairwise non-conflicting and has no memory orderings, so the `Arc` rule here is independent of orderings. This neither establishes nor refutes the soundness of an `Arc` implementation with particular orderings; for example, rust-lang/rust issue 51780, "Insufficient synchronization in `Arc::get_mut`" (https://github.com/rust-lang/rust/issues/51780, opened 2018-06-25, closed 2018-07-06), reports a race between two accesses to the content of an `Arc`, which the issue attributes to `Arc::get_mut` reading the strong count with a relaxed load (it proposes an acquire load).
* Allocator parameters (`A: Allocator + Send + Sync` on `Arc`) and `?Sized` are not modelled.
* `stdTable` gives `Cell` and `RefCell` the same rules, as the cited standard library gives them the same impl bounds, so the checker does not distinguish `.cell U` from `.refCell U` (`autoCheck_std_cell_eq_refCell`). `SemSend` and `SemSync` of the bare types agree as well (`cell_refCell_semSend_semSync_agree`); under a read-only wrapper the semantics separates them (`wrap_readOnly_cell_refCell_differ`).
* Model–system relation: none proved. These are statements about the toy capability model `Toy.SendSync`; they neither establish nor refute the corresponding claims about Rust's `Send` and `Sync` traits, rustc's auto-trait implementation, or the standard library types `Cell`, `RefCell`, `Rc`, `Arc`, `Mutex`, `MutexGuard`.

#### `std-checker-exact-wrap-free`

* Exactness holds for the toy primitives and the footprints chosen for them; it does not say that the standard library's bounds are necessary for the real types.
* The tightness witness is a read-only wrapper over `Cell<plain>` without an unsafe impl; the same type witnesses `autoCheck_std_incomplete`. With the unsafe impl flag set, wrappers can also make the checker accept a type that is not semantically `Sync` (`autoCheck_sound_implsSound_tight`).
* Exactness on `WrapFree` types is a property of `Toy.SendSync`. In Rust, other constructs make auto-trait verdicts differ from data-race freedom, for example `PhantomData<Cell<u32>>`, a zero-sized `Cell<()>`, enums with uninhabited variants, and raw pointers (`*const T` is `!Send` and `!Sync` by negative impls); none of these is modelled, and the theorem neither establishes nor refutes anything about them.
* Model–system relation: none proved. These are statements about the toy capability model `Toy.SendSync`; they neither establish nor refute the corresponding claims about Rust's `Send` and `Sync` traits, rustc's auto-trait implementation, or the standard library types `Cell`, `RefCell`, `Rc`, `Arc`, `Mutex`, `MutexGuard`.

#### `cell-send-iff`

* `Cell<U>` is not semantically `Send` for every `U`: for `U = .rc .plain` it is not (by this card and `not_semSend_rc`).
* The owner footprint of `.cell U` is the cell's storage plus the owner capabilities of `U`; its shared footprint is the same list (a shared reference reaches the content through `Cell::get`, `replace`, `set`, `take`). The owner footprint of `.refCell U` is the owner capabilities of `U` (reached without the flag, as by `RefCell::get_mut` and `into_inner`) followed by its shared footprint: borrow-flag reads and writes, the shared capabilities of `U` (shared borrow), and the owner capabilities of `U` under the claim `held [] .fresh` (mutable borrow). Both characterizations depend on the owner capabilities of `U` and its aliases.
* The two footprints differ (`fp_shr_cell_ne_refCell_plain`), but `SemSend` and `SemSync` of the bare types do not separate `Cell<U>` from `RefCell<U>` for any `U` (`cell_refCell_semSend_semSync_agree`), and the standard-table checker gives them the same verdicts (`autoCheck_std_cell_eq_refCell`). The model separates them under a read-only wrapper (`wrap_readOnly_cell_refCell_differ`, card `wrap-refcell-obligation`).
* `RefCell`'s `Ref`/`RefMut` guards are not modelled as types. The claim `held [] .fresh` on accesses under a mutable borrow treats the borrow flag as a lock with one exclusive holder, a modeling choice; shared borrows carry no claim. In Rust the flag is a non-atomic `Cell<BorrowCounter>` and `RefCell<T>` is not `Sync`; in the model the flag's unclaimed reads and writes make `.refCell U` not semantically `Sync` (`not_semSync_refCell`).
* Model–system relation: none proved. These are statements about the toy capability model `Toy.SendSync`; they neither establish nor refute the corresponding claims about Rust's `Send` and `Sync` traits, rustc's auto-trait implementation, or the standard library types `Cell`, `RefCell`, `Rc`, `Arc`, `Mutex`, `MutexGuard`.

#### `cell-not-sync`

* The race needs no synchronization snapshot beyond the trivial one: the two writes carry no claims.
* Escape hatches, for `U = .plain` (`cell_positive_control`): hiding the cell's writes behind a read-only wrapper, or putting the cell behind a mutex. Neither works for every `U`: `Mutex<Cell<Rc<plain>>>` is not semantically `Sync` (`mutex_cell_rc_plain_not_semSync`), and a read-only wrapper over `Cell<U>` is semantically `Sync` exactly when `OwnReadsRaceFree U` holds (`semSync_wrap_cell_readOnly_iff_ownReadsRaceFree`). Atomics, zero-sized content and `SyncUnsafeCell` are not modelled.
* A read-only view drops every write, including metadata writes, and every access under a mutable borrow: `SemSync (.wrap (.refCell .plain) .readOnly u)` holds (`semSync_wrap_refCell_plain_readOnly`), which models a wrapper that never writes the borrow flag (such as one exposing the unsafe `RefCell::try_borrow_unguarded`), not one exposing `RefCell::borrow`, which writes the flag. For `RefCell<U>` the read-only wrapper is semantically `Sync` exactly when `ShrReadsRaceFree U` holds (`semSync_wrap_refCell_readOnly_iff_shrReadsRaceFree`).
* RustBelt models `Cell<T>` with a thread-dependent sharing predicate (Section 6.1); it does not state an impossibility theorem of this form.
* Model–system relation: none proved. These are statements about the toy capability model `Toy.SendSync`; they neither establish nor refute the corresponding claims about Rust's `Send` and `Sync` traits, rustc's auto-trait implementation, or the standard library types `Cell`, `RefCell`, `Rc`, `Arc`, `Mutex`, `MutexGuard`.

#### `rc-neither`

* The witnessing snapshot has both threads holding a handle to the allocation; that a Rust program reaches that state by cloning and transferring one clone is a modeling-bridge remark (not proved here).
* Escape hatches: an atomic count (`arc_plain_nonvacuous`); and the impossibility assumes that another handle may remain on the origin thread (`(fp (.rc U)).alias` contains the handle capabilities). A design that statically guarantees uniqueness (no other clone exists, as after a successful `Rc::try_unwrap`) is outside this statement (not proved here).
* `Kind.atomic` has no memory orderings: the positive control does not establish that an atomic count with particular orderings avoids data races on the content; for example, rust-lang/rust issue 51780, "Insufficient synchronization in `Arc::get_mut`" (https://github.com/rust-lang/rust/issues/51780, opened 2018-06-25, closed 2018-07-06), reports a race between two accesses to the content of an `Arc`, which the issue attributes to `Arc::get_mut` reading the strong count with a relaxed load (it proposes an acquire load).
* Model–system relation: none proved. These are statements about the toy capability model `Toy.SendSync`; they neither establish nor refute the corresponding claims about Rust's `Send` and `Sync` traits, rustc's auto-trait implementation, or the standard library types `Cell`, `RefCell`, `Rc`, `Arc`, `Mutex`, `MutexGuard`.

#### `arc-send-iff`

* The `SemSend U` requirement of `SemSync (.arc U)` uses a snapshot in which the other thread is the unique holder of the allocation and owns the content. Modeling bridge (not proved here): in Rust, if `Arc<U>` were `Sync` without `U: Send`, a thread holding `&Arc<U>` could clone an owned handle, keep it beyond the origin thread's handles (for example in a pool thread's storage), and drop the last handle, dropping the `U` on a thread that did not create it; moving a clone to a third thread is not the mechanism, since that move would itself need `Arc<U>: Send`. Movement of handles between threads other than the origin thread is collapsed into the two-thread check.
* `Kind.atomic` treats atomic count updates as pairwise non-conflicting and has no memory orderings (`Relaxed`, `Acquire`, `Release`, `SeqCst`); the characterization neither establishes nor refutes that an `Arc` implementation with particular orderings is free of data races; for example, rust-lang/rust issue 51780, "Insufficient synchronization in `Arc::get_mut`" (https://github.com/rust-lang/rust/issues/51780, opened 2018-06-25, closed 2018-07-06), reports a race between two accesses to the content of an `Arc`, which the issue attributes to `Arc::get_mut` reading the strong count with a relaxed load (it proposes an acquire load).
* Weak references (`Weak`) and allocator parameters are not modelled.
* Model–system relation: none proved. These are statements about the toy capability model `Toy.SendSync`; they neither establish nor refute the corresponding claims about Rust's `Send` and `Sync` traits, rustc's auto-trait implementation, or the standard library types `Cell`, `RefCell`, `Rc`, `Arc`, `Mutex`, `MutexGuard`.

#### `mutex-sync-iff`

* Lock-protected accesses on the two threads are excluded because a snapshot has one lock holder; the model does not represent acquisition and release steps, poisoning, or deadlock. The release of a `fresh` acquisition is never foreign (`nfr_example_fresh_release`).
* The rule is specific to an exclusive lock. It is not a statement about reader-writer locks: in the cited standard library `RwLock<T>: Sync` requires `T: Send + Sync`, and `RwLock` is not modelled.
* Locations are path-relative: content moved into or out of the mutex (for example by `mem::replace` through a guard) keeps the path of its position; its own alias capabilities carry no lock claim, so they still conflict with the lock-protected accesses.
* Model–system relation: none proved. These are statements about the toy capability model `Toy.SendSync`; they neither establish nor refute the corresponding claims about Rust's `Send` and `Sync` traits, rustc's auto-trait implementation, or the standard library types `Cell`, `RefCell`, `Rc`, `Arc`, `Mutex`, `MutexGuard`.

#### `guard-sync-iff`

* Accesses made through the same guard on two threads are not excluded by the lock (one acquisition); accesses by other lockers are.
* Sharing `&MutexGuard<'a, T>` with another thread in Rust also needs the lifetimes to outlive the other thread (scoped threads); lifetimes are not modelled. `RwLockReadGuard`/`RwLockWriteGuard` are not modelled.
* Model–system relation: none proved. These are statements about the toy capability model `Toy.SendSync`; they neither establish nor refute the corresponding claims about Rust's `Send` and `Sync` traits, rustc's auto-trait implementation, or the standard library types `Cell`, `RefCell`, `Rc`, `Arc`, `Mutex`, `MutexGuard`.

#### `guard-not-send`

* Depth: `not_semSend_guard` is a membership check against the definition of `fp (.guard U)` (definitional); the companion `guard_transfer_race_iff` is a shallow race decomposition, and the companion `fp_relNamesAcq` is shallow (an induction on the toy type that combines list-membership facts about `place` and `++` at each constructor).
* For content `U` whose transfer is race-free (for example `SemSend` content such as `.plain`), the guard's failure comes from the release-affinity conjunct alone (`guard_plain_transfer_race_free`). For content whose transfer races (for example `.rc .plain`), the guard's transfer races as well (`guard_rc_plain_transfer_race`, by `guard_transfer_race_iff`).
* Dropping the release-affinity rule (as for lock implementations without a same-thread unlock requirement) does not make `MutexGuard<U>` `Send` for every `U`: by `guard_transfer_race_iff`, race-free transfer of the guard is equivalent to race-free transfer of `U` (`guard_rc_plain_transfer_race`). Platforms or lock libraries without the requirement are not modelled.
* `NoForeignRelease` inspects the acquisition named by the release event's `held` claim on its own location (`Acq.maker`) and accepts a release event without such a claim (`nfr_example_unnamed_release`); no footprint of the model contains one (`fp_relNamesAcq`). The thread executing every checked event is the other thread, and every guard reachable from the value is taken to be created by the origin thread.
* Model–system relation: none proved. These are statements about the toy capability model `Toy.SendSync`; they neither establish nor refute the corresponding claims about Rust's `Send` and `Sync` traits, rustc's auto-trait implementation, or the standard library types `Cell`, `RefCell`, `Rc`, `Arc`, `Mutex`, `MutexGuard`.

#### `false-rule-sync-implies-send`

* The guard witness violates the positive control's hypothesis (`guard_plain_own_not_subset_shr`).
* The guard-free witness is a wrapper with no shared API, the pattern of the standard library's unstable `SyncView`. Other `Sync`-but-not-`Send` patterns (such as a `Deref`-only wrapper over `Rc<T>` with `T: Sync`) are not modelled, since the model offers no view that exposes the content of an `Rc` without its count.
* Model–system relation: none proved. These are statements about the toy capability model `Toy.SendSync`; they neither establish nor refute the corresponding claims about Rust's `Send` and `Sync` traits, rustc's auto-trait implementation, or the standard library types `Cell`, `RefCell`, `Rc`, `Arc`, `Mutex`, `MutexGuard`.

#### `false-rule-send-implies-sync`

* The witness violates the positive control's hypothesis (`cell_plain_shr_has_write`).
* Whether a Rust type "looks immutable" is a property of its signatures, which the model does not represent; the positive control is about the footprint, not about signatures (for example a type with a `&self` method that updates an internal `Cell` cache has a write in its shared footprint).
* Model–system relation: none proved. These are statements about the toy capability model `Toy.SendSync`; they neither establish nor refute the corresponding claims about Rust's `Send` and `Sync` traits, rustc's auto-trait implementation, or the standard library types `Cell`, `RefCell`, `Rc`, `Arc`, `Mutex`, `MutexGuard`.

#### `shared-write-free-send-implies-sync`

* Relies on `shr_subset_own` (an owner can do everything a sharer can), which holds for every toy type by construction of `fp`.
* Atomic accesses count as writes here (`Kind.isWrite`), so the hypothesis excludes them.
* `hro` is sufficient, not necessary: `Arc<plain>` has an atomic write in its shared footprint and is semantically `Sync` (`arc_plain_shr_has_write_semSync`). A weaker hypothesis excluding non-atomic writes alone is not stated here.
* A write-free shared footprint without `SemSend T` does not give `SemSync T` (`semSend_imp_semSync_of_shr_no_write_semSend_tight`).
* Model–system relation: none proved. These are statements about the toy capability model `Toy.SendSync`; they neither establish nor refute the corresponding claims about Rust's `Send` and `Sync` traits, rustc's auto-trait implementation, or the standard library types `Cell`, `RefCell`, `Rc`, `Arc`, `Mutex`, `MutexGuard`.

#### `own-in-shared-sync-implies-send`

* The hypothesis `hsub` holds for `.cell`, `.rc`, `.arc` and `.ref` nodes of the model (their `own` and `shr` coincide by definition of `fp`), not in general for `.refCell` nodes, whose owner footprint adds flag-free access to the content (`fp_refCell_plain`); it is not claimed for any Rust type.
* `hsub` is sufficient, not necessary: `plain` has an owner-only write and is semantically `Send` (`plain_own_not_subset_shr_semSend`).
* `own ⊆ shr` without `SemSync T` does not give `SemSend T` (`semSync_imp_semSend_of_own_subset_shr_semSync_tight`).
* Model–system relation: none proved. These are statements about the toy capability model `Toy.SendSync`; they neither establish nor refute the corresponding claims about Rust's `Send` and `Sync` traits, rustc's auto-trait implementation, or the standard library types `Cell`, `RefCell`, `Rc`, `Arc`, `Mutex`, `MutexGuard`.

#### `unsafe-sync-obligation`

* Reference point: `semSync_wrap_iff_syncObligation` is the unfolded definition of `SemSync` for wrappers (depth definitional: it moves a negation across two existentials), kept so that the obligation of an unsafe `Sync` impl has a name; `semSync_wrap_full_iff` is definitional too. The wrapper results with content are the cards `wrap-view-restriction`, `wrap-cell-obligation`, `wrap-refcell-obligation` and `wrap-rc-obligation`.
* Views filter capability events one at a time. `.readOnly` keeps exactly the `rd` events that need no acquisition by the executing thread (`Ev.acquires`): it drops lock releases, atomic updates and metadata writes, and every access that first requires locking a mutex or registering a mutable borrow in a `RefCell`'s flag. For `RefCell<U>` it keeps the borrow-flag reads and the reads through the shared capabilities of `U` (`semSync_wrap_refCell_readOnly_iff_shrReadsRaceFree`), which models an API that never writes the borrow flag (such as one exposing the unsafe `RefCell::try_borrow_unguarded`), not one exposing `RefCell::borrow`, which writes the flag. Of a `Mutex` it keeps nothing (`expose_readOnly_mutex_example`).
* The wrapper has a single field and can only restrict shared capabilities; wrappers that achieve `Sync` by adding synchronization (locks, atomics, thread-identity checks), multi-field invariants, safety invariants beyond data-race freedom, unsafe `Send` impls and wrappers that restrict their owner API are not modelled.
* Model–system relation: none proved. These are statements about the toy capability model `Toy.SendSync`; they neither establish nor refute the corresponding claims about Rust's `Send` and `Sync` traits, rustc's auto-trait implementation, or the standard library types `Cell`, `RefCell`, `Rc`, `Arc`, `Mutex`, `MutexGuard`.

#### `wrap-view-restriction`

* Depth: `semSync_wrap_of_semSync` is shallow (every view exposes a sublist of the field's shared capabilities, and races and release affinity are monotone in the lists); `semSync_wrap_none` is shallow (the empty view exposes no event).
* The converse does not hold: a read-only wrapper over `Cell<plain>` is semantically `Sync` (`cell_positive_control`) although `Cell<plain>` is not (`not_semSync_cell`). The cards `wrap-cell-obligation`, `wrap-refcell-obligation` and `wrap-rc-obligation` characterize, for their fields, when a restricted view of a field that is not semantically `Sync` is semantically `Sync`.
* Restriction is a filter of the field's shared capabilities; the wrapper's owner and alias capabilities are those of its field. Wrappers that add synchronization or restrict their owner API are not modelled.
* Model–system relation: none proved. These are statements about the toy capability model `Toy.SendSync`; they neither establish nor refute the corresponding claims about Rust's `Send` and `Sync` traits, rustc's auto-trait implementation, or the standard library types `Cell`, `RefCell`, `Rc`, `Arc`, `Mutex`, `MutexGuard`.

#### `wrap-cell-obligation`

* A shared reference to `Cell<U>` reaches the owner capabilities of `U` (`Cell::get` copies the content out for `Copy` content; `Cell::replace`, `set` and `take` move it out or drop it). The view keeps the non-acquiring `rd` events (`Ev.acquires = false`) among them, including such reads through a copied-out reference, and drops every `rd` event that carries a `fresh` claim (`Ev.acquires = true`), such as a read that first locks a `Mutex` reached through a copied-out reference (for example, the read-only view of the shared footprint of `Mutex<&Cell<plain>>` is empty: `expose_readOnly_mutex_example`). Because of this filter, `OwnReadsRaceFree U` is not the same as race freedom of the transfer of `U`: for a guard-free content whose owner capabilities include accesses under such a lock (for example a reference to `Mutex<&Cell<plain>>`), the transfer of `U` can race through those accesses while `OwnReadsRaceFree U` holds (not proved here). A Rust wrapper whose `get` hands out a `Copy` value that permits writes (for example `&'a Cell<u32>`) does not have a read-only capability set in this sense; for that content the model's read-only wrapper already fails to be semantically `Sync` (`wrap_cell_ref_cell_readOnly_not_semSync`), because reads of the inner cell race with writes by the lender of the reference.
* The characterization is for a wrapper that owns the cell directly. Hiding writes on a wrapper around a cell shared through other handles does not help: a read-only wrapper over `Arc<Cell<plain>>` is not semantically `Sync` (`wrap_arc_cell_readOnly_not_semSync`).
* The characterization is specific to `Cell`. For a read-only wrapper over `RefCell<U>` the condition is `ShrReadsRaceFree U` (card `wrap-refcell-obligation`), which is implied by `OwnReadsRaceFree U` and differs from it (`wrap_readOnly_cell_refCell_differ`).
* Locations are path-relative: values copied or moved out of the cell keep the path of the content position. This identification makes reads through a copied-out reference visible to the content's aliases; it also identifies an independent copy of plain data with the content position, which can only add conflicts (for `U = .plain` the content has no aliases, so none arise).
* Model–system relation: none proved. These are statements about the toy capability model `Toy.SendSync`; they neither establish nor refute the corresponding claims about Rust's `Send` and `Sync` traits, rustc's auto-trait implementation, or the standard library types `Cell`, `RefCell`, `Rc`, `Arc`, `Mutex`, `MutexGuard`.

#### `wrap-refcell-obligation`

* The read-only view models a wrapper whose API never writes the borrow flag, such as one exposing the unsafe `RefCell::try_borrow_unguarded`. A wrapper exposing `RefCell::borrow` writes the flag and is not read-only in this sense; with the full view a wrapper over `RefCell<U>` is not semantically `Sync` for any `U` (`semSync_wrap_full_iff` with `not_semSync_refCell`).
* The view keeps the non-acquiring `rd` events (`Ev.acquires = false`) of the shared capabilities of `U`, including such reads through references handed out by the content, and drops their writes like the others. It also drops every `rd` event that carries a `fresh` claim (`Ev.acquires = true`), that is, every read that first needs a lock acquisition or a mutable borrow by the executing thread; for example, the read-only view of the shared footprint of `Mutex<&Cell<plain>>` is empty (`expose_readOnly_mutex_example`). As for `Cell`, a Rust API that hands out a reference permitting writes does not have a read-only capability set in this sense.
* The separating content `W` is a wrapper around `&Cell<plain>` that exposes nothing through a shared reference while its owner can use the inner cell. A shared reference to `Cell<W>` reaches the owner capabilities of `W` (in Rust, `Cell::get` copies a `Copy` value out), whereas a shared borrow of `RefCell<W>` reaches its shared capabilities alone. Whether a particular Rust type corresponds to `W` is a modeling-bridge question (not proved here).
* Locations are path-relative, as for `Cell`: capabilities reached through the shared borrow keep the path of the content position.
* Model–system relation: none proved. These are statements about the toy capability model `Toy.SendSync`; they neither establish nor refute the corresponding claims about Rust's `Send` and `Sync` traits, rustc's auto-trait implementation, or the standard library types `Cell`, `RefCell`, `Rc`, `Arc`, `Mutex`, `MutexGuard`.

#### `wrap-rc-obligation`

* The `.readOnly` view keeps the non-acquiring `rd` events (`Ev.acquires = false`) of the field's shared footprint, including the count read and such reads available after obtaining a unique handle; it drops every `rd` event that carries a `fresh` claim (`Ev.acquires = true`), such as a read that first locks a `Mutex` or registers a mutable borrow in a `RefCell` inside the content. A view exposing the content without the count is not offered by the model.
* In Rust, `Rc::strong_count` and `Rc::weak_count` read the non-atomic count, while `Deref::deref` for `Rc` reads no count. A wrapper exposing `Deref` alone (no `Clone`, no count readers) avoids the count race and is a different design, which the model does not represent; it neither establishes nor refutes anything about it.
* Model–system relation: none proved. These are statements about the toy capability model `Toy.SendSync`; they neither establish nor refute the corresponding claims about Rust's `Send` and `Sync` traits, rustc's auto-trait implementation, or the standard library types `Cell`, `RefCell`, `Rc`, `Arc`, `Mutex`, `MutexGuard`.

#### `checker-incomplete`

* Together with `autoCheck_std_sound_of_implsSound`, the standard-table checker is sound on every type satisfying `ImplsSound` and incomplete on types with wrappers; on wrapper-free types it is exact (`autoCheck_std_exact_of_wrapFree`). Without `ImplsSound` it can accept types that are not semantically `Sync` (`autoCheck_sound_implsSound_tight`).
* The witness is shared with `autoCheck_std_exact_wrapFree_tight` (the tightness of `WrapFree`); this card adds the shared-reference conjunct. In Rust an `unsafe impl Sync` on such a wrapper is how the gap is bridged; this card does not claim that wrappers are the only source of incompleteness in Rust (`PhantomData`, zero-sized types, uninhabited variants and raw pointers are not modelled).
* Model–system relation: none proved. These are statements about the toy capability model `Toy.SendSync`; they neither establish nor refute the corresponding claims about Rust's `Send` and `Sync` traits, rustc's auto-trait implementation, or the standard library types `Cell`, `RefCell`, `Rc`, `Arc`, `Mutex`, `MutexGuard`.

#### `structural-constructors`

* Depth: the product characterizations are shallow (race decomposition over disjoint paths); the `.box` and `.wrap` companions are definitional (`Iff.rfl`), and the `.sum` companions are the product proofs (`fp_sum_eq_prod`).
* The footprint of `.sum A B` is that of `.prod A B`: no discriminant, no variant exclusivity, and no uninhabited variants; enums with an uninhabited non-`Send` variant are not modelled.
* Rust's `Box<T, A>` also depends on the allocator `A`, which is not modelled. `semSend_wrap_iff` holds by `Iff.rfl` because wrappers cannot restrict their owner or drop capabilities in this model; wrappers that soundly `unsafe impl Send` by restricting ownership are not modelled. Unions, trait objects, closures and futures are not modelled.
* Cross-component races are impossible because components occupy disjoint paths.
* Model–system relation: none proved. These are statements about the toy capability model `Toy.SendSync`; they neither establish nor refute the corresponding claims about Rust's `Send` and `Sync` traits, rustc's auto-trait implementation, or the standard library types `Cell`, `RefCell`, `Rc`, `Arc`, `Mutex`, `MutexGuard`.

#### `definition-examples`

* Reference point: these theorems test the definitions on concrete instances; they carry no general claim. Universally quantified facts about the definitions (for example `fp_sum_eq_prod`, `fp_relNamesAcq`, `autoCheck_std_cell_eq_refCell`) are companions of other cards.
* Model–system relation: none proved. These are statements about the toy capability model `Toy.SendSync`; they neither establish nor refute the corresponding claims about Rust's `Send` and `Sync` traits, rustc's auto-trait implementation, or the standard library types `Cell`, `RefCell`, `Rc`, `Arc`, `Mutex`, `MutexGuard`.

### Escape hatches of the impossibility results

* `cell-not-sync` concerns the full shared API of the cell: a read-only wrapper over `Cell<plain>` and a mutex around `Cell<plain>` are semantically `Sync` (`cell_positive_control`).
* `rc-neither` rests on the non-atomic count: with an atomic count (`.arc .plain`) both properties hold (`arc_plain_nonvacuous`).
* `guard-not-send` rests on the release-affinity conjunct of `SemSend`: without it, the transfer of `MutexGuard<plain>` is race-free (`guard_plain_transfer_race_free`); for content whose transfer races, the guard's transfer races as well (`guard_rc_plain_transfer_race`).
* `false-rule-sync-implies-send` is defeated by the containment hypothesis `hsub`: if every owner capability of `T` is also a shared capability, `SemSync T` implies `SemSend T` (`semSync_imp_semSend_of_own_subset_shr`).
* `false-rule-send-implies-sync` is defeated by the hypothesis `hro`: if the shared footprint of `T` contains no write, `SemSend T` implies `SemSync T` (`semSend_imp_semSync_of_shr_no_write`).

### Hypotheses with unknown tightness

None. Every hypothesis listed in `results.json` (8 in total) is `tight`, with a proved counterexample in which all other hypotheses hold and the conclusion fails; the cards with an empty hypothesis list have no hypotheses beyond universally quantified variables.

### Disproved or dropped draft statements

None. Every statement of the package was proved as stated; no statement was weakened, disproved or removed.

### Not examined

* Standard-library types other than the six modelled primitives, for example `RwLock` and its guards (whose documented impls are cited for comparison under the card `mutex-sync-iff`), atomic integer types, `Weak`, `OnceCell`, `LazyLock` and channels.
* Unsafe `Send` impls, generic user wrappers, negative impls on user types and recursive types.
* Memory orderings and relaxed-memory behaviour.
* Lock implementations without a same-thread unlock requirement.
* Whether rustc's trait solver derives `T: Sync` from a where-clause `&'a T: Send`, and lifetimes in general.

## Evidence

### Kernel-check record

Toolchain `leanprover/lean4:v4.34.1` (`leanprover/lean4`, tag `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`, read from the GitHub API on 2026-11-21). Lake project `lean/` with one library `ToySendSync` (modules `ToySendSync.Model`, `ToySendSync.Lemmas`, `ToySendSync.Place`, `ToySendSync.Characterize`, `ToySendSync.Results`) and no dependencies (core Lean and no Mathlib). Observed 2026-11-21: `lake build` succeeds with no `sorry` warnings; no Lean source contains `sorry`, `admit`, `native_decide`, `axiom` or `opaque` declarations, `implemented_by`, `@[extern]` or `unsafe`; all 704 non-internal declarations of the library depend on axioms among `propext`, `Classical.choice`, `Quot.sound` (in fact on `Quot.sound`, `propext` at most; per declaration in `audit/axioms.json`). Every result is `Basis: execution (Lean kernel check)`.

### Statement and closure hashes

For each Lean name in the fields `lean`, `lean_names`, `nonvacuity_witness_lean`, `positive_control_lean` and hypothesis `counterexample` of `results.json`, `audit/statements.json` records the SHA-256 of the statement and of its definition closure (computed as described under **Revalidation**). Roles: `R` main theorem, `R (example)` theorem of the definition-examples card, `C` companion or registered definition, `CE` tightness counterexample, `NV` non-vacuity witness, `PC` positive control.

| Lean name | Used by (card: role) | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
|---|---|---|---|---|
| `Toy.SendSync.Acq` | definition-examples: C | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.SendSync.Acq.holder` | definition-examples: C | none | `bb2b14caff2998fb51d8b0495c720054584c710a7f227a5094bb8711124c669b` | `18a963683118779a407f26f39f2fad327f2b029c5a97280bc534d8d9e1b448e0` (10) |
| `Toy.SendSync.Acq.maker` | definition-examples: C | none | `f223f0375e3eb629ded40aba2ce9b11eb965b17b4d6aa4d73fa0ab9cc4635f1a` | `353b15047493ffaeace6830acea18c83e7c915f315105889ee2e5eb1610349a1` (7) |
| `Toy.SendSync.Acq.reloc` | definition-examples: C | none | `146ec80e9343b08009ad4c95b800b9318c5777e1eccd602e8abc5d109c5a6690` | `53d360b8e9c969da60ebcf9f4519a2c234f48db2fe18fafb66262be8ec9a389a` (4) |
| `Toy.SendSync.Claim` | definition-examples: C | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.SendSync.Claim.isFresh` | definition-examples: C | propext | `cda071246e39b3e11d243f9859ba2bab254405e133a3b17df03b77419f4c8db9` | `64750f7933ca69919ca91d90835db8c6b843640e62ba2e88cc5eafa467f227ea` (8) |
| `Toy.SendSync.Claim.path` | definition-examples: C | none | `b4e2d07473105f1b2696dbf6e854c95a9bb0ce23e647985d79ebde5a15df4b34` | `64750f7933ca69919ca91d90835db8c6b843640e62ba2e88cc5eafa467f227ea` (8) |
| `Toy.SendSync.Claim.reloc` | definition-examples: C | none | `2f51fb112b034f7609b43584c8275019705483a659a51d299611ce3b4a092155` | `64750f7933ca69919ca91d90835db8c6b843640e62ba2e88cc5eafa467f227ea` (8) |
| `Toy.SendSync.Compatible` | definition-examples: C | none | `f760b7ebcb8e3fe8a4e53f902cc16d48c97d4619a673b96f7dc0736dfe6cf08a` | `64750f7933ca69919ca91d90835db8c6b843640e62ba2e88cc5eafa467f227ea` (8) |
| `Toy.SendSync.Concurrent` | definition-examples: C | none | `89fa3b5003a9339801d5bedd68203be8e125c42ce739b8ae4418de1a0bc3a5bb` | `eab84d5089f79393dfc116bd5490102af9121812babfe622e352fd864a7687cd` (15) |
| `Toy.SendSync.Conflicting` | definition-examples: C | propext | `89fa3b5003a9339801d5bedd68203be8e125c42ce739b8ae4418de1a0bc3a5bb` | `eab84d5089f79393dfc116bd5490102af9121812babfe622e352fd864a7687cd` (15) |
| `Toy.SendSync.Ev` | definition-examples: C | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.SendSync.Ev.acquires` | definition-examples: C | propext | `73388b8b64f413836fa43ec8805103bf364768e21bdb257f886cd3b229e0030f` | `eab84d5089f79393dfc116bd5490102af9121812babfe622e352fd864a7687cd` (15) |
| `Toy.SendSync.Ev.place` | definition-examples: C | none | `5f088556acf510a7b3e2a5ac6cd295fac9bf6b9f7f37087d70c07f2969a65cbe` | `eab84d5089f79393dfc116bd5490102af9121812babfe622e352fd864a7687cd` (15) |
| `Toy.SendSync.Fp` | definition-examples: C | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.SendSync.Holder` | definition-examples: C | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.SendSync.Holder.reloc` | definition-examples: C | none | `b238cf905c1d0d7f0e6460f303ee07a8197d8cb75448de6af018a89b2181875d` | `d12b8d05164af70154f308d5e4515865e76e5b1e9efc48f8424e8c3eee8ad672` (7) |
| `Toy.SendSync.ImplsSound` | structural-soundness: C; definition-examples: C | propext | `dc67da8ced1b590f01d5242db8dd7fa6e991dc37a0588c071969b36443542ee5` | `6b2cb26a6a7ccad941a8cb0f1e6a2b85c4ade694fae5f0d35275fd2176eff931` (18) |
| `Toy.SendSync.Kind` | definition-examples: C | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.SendSync.Kind.isAccess` | definition-examples: C | propext | `b17170a61d8582b722c1cf20538768796c89a057edd7d7e8c316490755bf2cda` | `5a87e3a7125d20de5f60a0ee9889e38f7530dcbf36f584dd2b207c3a0d09790e` (5) |
| `Toy.SendSync.Kind.isAtomic` | definition-examples: C | propext | `b17170a61d8582b722c1cf20538768796c89a057edd7d7e8c316490755bf2cda` | `5a87e3a7125d20de5f60a0ee9889e38f7530dcbf36f584dd2b207c3a0d09790e` (5) |
| `Toy.SendSync.Kind.isRead` | definition-examples: C | propext | `b17170a61d8582b722c1cf20538768796c89a057edd7d7e8c316490755bf2cda` | `5a87e3a7125d20de5f60a0ee9889e38f7530dcbf36f584dd2b207c3a0d09790e` (5) |
| `Toy.SendSync.Kind.isWrite` | definition-examples: C | propext | `b17170a61d8582b722c1cf20538768796c89a057edd7d7e8c316490755bf2cda` | `5a87e3a7125d20de5f60a0ee9889e38f7530dcbf36f584dd2b207c3a0d09790e` (5) |
| `Toy.SendSync.NoForeignRelease` | definition-examples: C | none | `06d4c9c4c91bdfb8ed8a8fc5208011f55234b0d676ae6803478b34cdc71485c3` | `687ede777b4daa517c5e24135014c0d38e87b4a20f446a3b06b90679ed14fd65` (18) |
| `Toy.SendSync.OwnReadsRaceFree` | wrap-cell-obligation: C; definition-examples: C | propext | `ca9f73fadbd3f4b7b7d05884afbe86c93bc8c642b578b06f3b080e5709afb015` | `6b2cb26a6a7ccad941a8cb0f1e6a2b85c4ade694fae5f0d35275fd2176eff931` (18) |
| `Toy.SendSync.Path` | definition-examples: C | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.SendSync.Prim` | definition-examples: C | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.SendSync.Prim.apply` | definition-examples: C | none | `b9743c58aab97c4fb7d8c02b16432e3fa7e835732b1196c2190503cbc9e59c9d` | `e146e838f5d002d83550feb605f2e9746230dcf0d7cb4673387c33fc55ce0af1` (25) |
| `Toy.SendSync.Race` | definition-examples: C | propext | `5e22743989be380ecd10f0df6f3f83db282a7f2b8d859fa0f39b55eb3e656ee7` | `eab84d5089f79393dfc116bd5490102af9121812babfe622e352fd864a7687cd` (15) |
| `Toy.SendSync.RelNamesAcq` | guard-not-send: C; definition-examples: C | none | `c4462a412d0b1da6ef2acd622d7ebb02575b6ff241dd0a64c86f30e9096e250d` | `eab84d5089f79393dfc116bd5490102af9121812babfe622e352fd864a7687cd` (15) |
| `Toy.SendSync.Rule` | definition-examples: C | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.SendSync.Rule.Holds` | definition-examples: C | none | `e1dc5ee6999a9b006832ae81e20eff084098d40823fc1285433d168ed2f0137c` | `684753013ffddf448f9640c5a9c7ce484590e245029e08b7b28bb93b4179143f` (2) |
| `Toy.SendSync.Rule.eval` | definition-examples: C | none | `55aa3c936237a1e16adb8959d2f18986b5bb0982a37fb4f15cafef6f8266477c` | `684753013ffddf448f9640c5a9c7ce484590e245029e08b7b28bb93b4179143f` (2) |
| `Toy.SendSync.Sat` | definition-examples: C | none | `56eaf8bb796f9a18f09e16ab15a9fae535d2f521ddf161d02d205181effd24c9` | `5ca5bfcbd69dfa50523b6f8321c44f4dde5ebc0cddf6ee872fdf8c53010a7527` (16) |
| `Toy.SendSync.SatAll` | definition-examples: C | none | `d281b9e6fd70df2abbfec6d2f8dc71413bfc6297473a471434669e76396f1209` | `5ca5bfcbd69dfa50523b6f8321c44f4dde5ebc0cddf6ee872fdf8c53010a7527` (16) |
| `Toy.SendSync.SemSend` | definition-examples: C | propext | `3723a0791d672df43b8a441bc415c676e1f8f47fccc252b9aba8b28128fe2877` | `6b2cb26a6a7ccad941a8cb0f1e6a2b85c4ade694fae5f0d35275fd2176eff931` (18) |
| `Toy.SendSync.SemSync` | definition-examples: C | propext | `3723a0791d672df43b8a441bc415c676e1f8f47fccc252b9aba8b28128fe2877` | `6b2cb26a6a7ccad941a8cb0f1e6a2b85c4ade694fae5f0d35275fd2176eff931` (18) |
| `Toy.SendSync.ShrReadsRaceFree` | wrap-refcell-obligation: C; definition-examples: C | propext | `ca9f73fadbd3f4b7b7d05884afbe86c93bc8c642b578b06f3b080e5709afb015` | `6b2cb26a6a7ccad941a8cb0f1e6a2b85c4ade694fae5f0d35275fd2176eff931` (18) |
| `Toy.SendSync.Snap` | definition-examples: C | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.SendSync.SyncObligation` | unsafe-sync-obligation: C; definition-examples: C | propext | `b33d429df43c4edaf08320ab2602eb19fb060f500c3b968001b91cab4b353cb6` | `6b2cb26a6a7ccad941a8cb0f1e6a2b85c4ade694fae5f0d35275fd2176eff931` (18) |
| `Toy.SendSync.Table` | definition-examples: C | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.SendSync.TableSound` | structural-soundness: C; definition-examples: C | propext | `1872b3f7aaf93c6fedf1179ccca4bab45dfc880bd97477923742f486f349d3c3` | `30740ea48fe3e7ce5fae84902c9ae3857d905c92e3a7a41e0aec74bfd44f2a15` (11) |
| `Toy.SendSync.Tid` | definition-examples: C | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.SendSync.Tid.flip` | definition-examples: C | none | `bfc241eab65751b405f0524ab829309aea00bf3aa7ac4c912adefa274cf3a7f6` | `8aa1a71fc7a1879db58ac04932d89e6dd99f675fe5b757b258bfbec739313e82` (3) |
| `Toy.SendSync.Ty` | definition-examples: C | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.SendSync.View` | definition-examples: C | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.SendSync.View.expose` | definition-examples: C | propext | `8a2ad1eefd7b035e0afab5009e69d129bafd080778de7fc7450e946a93ddd70c` | `c6839aac3f1da623981711e7677b890786d7dbb6619340588022a34b292a423e` (19) |
| `Toy.SendSync.WrapFree` | std-checker-exact-wrap-free: C; definition-examples: C | none | `dc67da8ced1b590f01d5242db8dd7fa6e991dc37a0588c071969b36443542ee5` | `6b2cb26a6a7ccad941a8cb0f1e6a2b85c4ade694fae5f0d35275fd2176eff931` (18) |
| `Toy.SendSync.arc_cell_plain_content_not_semSync_arc_neither` | arc-send-iff: C | Quot.sound, propext | `80ebece88a0ba0c08e731ecd50be5727e3c96ec7bed351e10a341aca2f160a7e` | `cceba79b2527622d62ebd46dc51978e5940f7eaa89b9a8a46e76289bdb50bdee` (111) |
| `Toy.SendSync.arc_guard_plain_content_not_semSend_arc_neither` | arc-send-iff: C | Quot.sound, propext | `22a30acf7f383ee8e907450653482af39c2a27a5432b06516de3399450aad479` | `cceba79b2527622d62ebd46dc51978e5940f7eaa89b9a8a46e76289bdb50bdee` (111) |
| `Toy.SendSync.arc_plain_nonvacuous` | rc-neither: PC; arc-send-iff: NV | Quot.sound, propext | `f79e31ec809e4ad49a0360ab61e0aae45cd5428af55fb56f378ffd31ecb6df79` | `cceba79b2527622d62ebd46dc51978e5940f7eaa89b9a8a46e76289bdb50bdee` (111) |
| `Toy.SendSync.arc_plain_shr_has_write_semSync` | shared-write-free-send-implies-sync: C | Quot.sound, propext | `de175db23ea14b194e287a647cc1d669ebcce804c5986d26dc1ad48442efb80c` | `7f0fe3b1db041c6aa049e1b61bf750aa28d29364ba50ae23baca5ea95e70b291` (110) |
| `Toy.SendSync.arc_race_iff` | arc-send-iff: C | Quot.sound, propext | `fbcb3348a7f77ef0c8fb9397faad44820b97597fc3d7809b594a7ce05d9fa68d` | `f991b1ec68391c4ffee26e34f94ab7b4d9ef8a1342ed5e90945f31167f565eb8` (107) |
| `Toy.SendSync.arc_wrap_rc_none_content_not_semSend_arc_neither` | arc-send-iff: C | Quot.sound, propext | `271a4b1647a12de5e95fafc8ad498537278af04252e62731cea28e51a514b2e0` | `cceba79b2527622d62ebd46dc51978e5940f7eaa89b9a8a46e76289bdb50bdee` (111) |
| `Toy.SendSync.autoCheck` | definition-examples: C | none | `dc51d476712b020701d1cf7c5819ad3de04f172564fce3b18ab8d866968787fd` | `30331a72b2baba89ded0d99559f5a1634258ffcce4270f9ae3b970a221bafb6a` (29) |
| `Toy.SendSync.autoCheck_examples` | definition-examples: R (example) | none | `012bec0146fd7523da35b0868a3efb99c63bf8e843bc5fbf3e084d49ece26538` | `a2cf8cc38403cc4293b91add699bee3dc81cb2125cc9a2db7e3d267b7bd35e7b` (47) |
| `Toy.SendSync.autoCheck_sound_implsSound_tight` | structural-soundness: CE | Quot.sound, propext | `23b6812f5cc9e8c383edc65f4eb2281d0c05326e8d480f8fcb602c3e8a093f77` | `da11945afb1bc894151876de0462b5900eb2e4b8e742061619207fa04ceef521` (138) |
| `Toy.SendSync.autoCheck_sound_nonvacuous` | structural-soundness: NV | Quot.sound, propext | `f08850a2dde5ac0509d0a05ae5e6ec13615292273239148c77f4736b0dc61606` | `bd5afa0bf19f95fdf0234be11a1d187536f20ef6411ab86c77346eb2d60b80e6` (140) |
| `Toy.SendSync.autoCheck_sound_of_tableSound_of_implsSound` | structural-soundness: R | Quot.sound, propext | `d53aff23954d6f6df3187decee808493a2aa1633eb98f657317407001c5a2ba6` | `b1c2c957fec57ef0a740c62451da7dfb5d03ff7ad24b26cdf77136617ed20344` (138) |
| `Toy.SendSync.autoCheck_sound_tableSound_tight` | structural-soundness: CE | propext | `b0ccffc229fe6429c1d584411da3bfe66b76f516773928b42ee7335c4512153d` | `1332ed794d9d3f9cd0b94340f98ceefc0163945171177d521e7b385cd7388657` (141) |
| `Toy.SendSync.autoCheck_std_cell_eq_refCell` | std-table-sound: C | none | `dbe24be182d5ee9b5389ce5ead0730b17742a134780c0a029405653bfa5af983` | `a2cf8cc38403cc4293b91add699bee3dc81cb2125cc9a2db7e3d267b7bd35e7b` (47) |
| `Toy.SendSync.autoCheck_std_exact_nonvacuous` | std-checker-exact-wrap-free: NV | none | `574fbdd316412f4730ea6e62e07604f0964a703b9724b74ccba0ff5431333739` | `5bd7b251b86f7effb9518bd99f8d911d6d9a8236db2db81a48ee1ed1ad7cfbff` (26) |
| `Toy.SendSync.autoCheck_std_exact_of_wrapFree` | std-checker-exact-wrap-free: R | Quot.sound, propext | `2247c1c5dc36db5fbd9427b2b9e11cb2d4bdcd39b0a313c580fc7a502975c388` | `0260d591b31837fbbb52bf62126ebdaacb23d8fc6f6a5b3af977d7e38ae94c5b` (136) |
| `Toy.SendSync.autoCheck_std_exact_wrapFree_tight` | std-checker-exact-wrap-free: CE | Quot.sound, propext | `16b4c293850e1f2e63ff5ffae11f63ea80d4ee5e4b079cb85c42aa21c9b64eed` | `9abd9ed2fff4dcf5285d991d89e67bc3cc1772fff3ec2cdd0741d00ed1d5fe28` (133) |
| `Toy.SendSync.autoCheck_std_incomplete` | checker-incomplete: R; checker-incomplete: NV | Quot.sound, propext | `bcf0550b9a11f79207905f9e994af75a3b2a9beb34e23228db84dccb7f05f983` | `99a40a4c80fb542018410a14cd80a106e6524ef63de3369fc332d99d28494620` (134) |
| `Toy.SendSync.autoCheck_std_sound_of_implsSound` | structural-soundness: C | Quot.sound, propext | `98345696a98596cad7b1449aa3c568bedf4741352f75a4963972fe8af0d2b6c6` | `61778e151bf36feca2df2dbb182a3ce913d82ba1a62fc0589a3a37234ecb4e80` (136) |
| `Toy.SendSync.cell_plain_semSend_not_semSync` | cell-send-iff: C; cell-send-iff: NV; cell-not-sync: NV; false-rule-send-implies-sync: NV; shared-write-free-send-implies-sync: CE | Quot.sound, propext | `50f83aa66421a104847f877b286ae201a1df61a0c20c1cae02cea141349575bd` | `cceba79b2527622d62ebd46dc51978e5940f7eaa89b9a8a46e76289bdb50bdee` (111) |
| `Toy.SendSync.cell_plain_shr_has_write` | false-rule-send-implies-sync: C | propext | `4d0173bc8a591efc972951665961faee1cc1f79801c659761a4faf9ee2e6f07e` | `844f183b30d290b3d2a02b0f963e0402b981d3237eb196c7be4f2b6adae5c67e` (80) |
| `Toy.SendSync.cell_positive_control` | cell-not-sync: PC | Quot.sound, propext | `a753871ddd25c39a64d01df5110049531e70f9266cf84b8fee0b925bf3de55fe` | `7f0fe3b1db041c6aa049e1b61bf750aa28d29364ba50ae23baca5ea95e70b291` (110) |
| `Toy.SendSync.cell_refCell_semSend_semSync_agree` | cell-send-iff: C | Quot.sound, propext | `aed956846ef32436ac8463cbe2aca5d260bfc9f9d017ed9f0db9e4c9fed3bb10` | `cceba79b2527622d62ebd46dc51978e5940f7eaa89b9a8a46e76289bdb50bdee` (111) |
| `Toy.SendSync.compatible_example_via_via` | definition-examples: R (example) | propext | `4f4766e21a40b2bba474bb4c890ea4f818356b4987cb550fff0c86681cba1e88` | `fbebb3b4ec93284c6fc1e8cdcb5a7846d4dc9914aa776804ba1761cdb644a372` (32) |
| `Toy.SendSync.expose_readOnly_example` | definition-examples: R (example) | propext | `15b0541f5bc326e6e7bc84e126f8f7346e734a08ea3f2b82fd76218f48eb2fb0` | `32da328cd63b8c5fb2cdc524e510e9261315aa4dc5987d635fb0f610de930d00` (43) |
| `Toy.SendSync.expose_readOnly_example_acquires` | definition-examples: R (example) | propext | `df41fe0e298b286520a4864e313b89a6f46064db7d5a74f8db92a56e38e94632` | `32da328cd63b8c5fb2cdc524e510e9261315aa4dc5987d635fb0f610de930d00` (43) |
| `Toy.SendSync.expose_readOnly_mutex_example` | definition-examples: R (example) | propext | `eb90bab801ae88853c97a40da6932d8f8af84e1b282ac372c21672875019e462` | `403fbbefa1d64cefb50c15e1198f813e8c081045ffc021a59e33cb3b6afab9fe` (77) |
| `Toy.SendSync.expose_readOnly_refCell_shr` | wrap-refcell-obligation: C | propext | `648c63a2e56d6a0ad84a24a2aa38b6021e5127abfa353e38dc2b9f4211dccaf7` | `403fbbefa1d64cefb50c15e1198f813e8c081045ffc021a59e33cb3b6afab9fe` (77) |
| `Toy.SendSync.fp` | definition-examples: C | propext | `2ce91283174e21f1092d18bc9664c1c06174f0e15c5553c2263f2fcbe93393b0` | `2cbec1297759824de27ac4ae85902805de8b1e3f549d68cf94d3f57a6d6afe1a` (35) |
| `Toy.SendSync.fp_cell_plain` | definition-examples: R (example) | propext | `ae77c64521471235f02dff9aed8224560ad8f09ca6830d450042877ed0ac0576` | `403fbbefa1d64cefb50c15e1198f813e8c081045ffc021a59e33cb3b6afab9fe` (77) |
| `Toy.SendSync.fp_refCell_plain` | definition-examples: R (example) | propext | `bc26828c401d203ba35ff21b5d799b12c27d34f5f3fa893cf1ac6fa17021f349` | `403fbbefa1d64cefb50c15e1198f813e8c081045ffc021a59e33cb3b6afab9fe` (77) |
| `Toy.SendSync.fp_relNamesAcq` | guard-not-send: C | Quot.sound, propext | `d8d1387d1b5e57d5fb004abf6191b07f803e8129a2572324c25db325807c2c00` | `d01476fd9df5dd86fa1a916d8fea2d41e5700f248e66e27d7a20f6f4f44ad33b` (78) |
| `Toy.SendSync.fp_shr_cell_ne_refCell_plain` | definition-examples: R (example) | propext | `ddf03a19b44d6c91cc0094edf96d712b47a7cd03c6ba6a23f8a59e022f578d6e` | `403fbbefa1d64cefb50c15e1198f813e8c081045ffc021a59e33cb3b6afab9fe` (77) |
| `Toy.SendSync.fp_sum_eq_prod` | structural-constructors: C | propext | `11286dcc6876d8530130b71fc6311199062e57edbce3c851db0dca1ad73cdaa9` | `403fbbefa1d64cefb50c15e1198f813e8c081045ffc021a59e33cb3b6afab9fe` (77) |
| `Toy.SendSync.guard_plain_own_not_subset_shr` | false-rule-sync-implies-send: C | propext | `2eeaeb309f281705465dbccf5e69e6b395f474384f707d9a69ce1776a3b035bb` | `403fbbefa1d64cefb50c15e1198f813e8c081045ffc021a59e33cb3b6afab9fe` (77) |
| `Toy.SendSync.guard_plain_semSync_not_semSend` | guard-sync-iff: NV; guard-not-send: C; guard-not-send: NV; false-rule-sync-implies-send: NV; own-in-shared-sync-implies-send: CE | Quot.sound, propext | `5440d28893d80acc58be8354ae458689dcf1eec5b0105cd5522ebc41fa0a2d47` | `cceba79b2527622d62ebd46dc51978e5940f7eaa89b9a8a46e76289bdb50bdee` (111) |
| `Toy.SendSync.guard_plain_transfer_race_free` | guard-not-send: PC | Quot.sound, propext | `8f36aba8b6a481d7145a8b2c7c4c5f247a1170475cc968823f62c91773a38b93` | `f991b1ec68391c4ffee26e34f94ab7b4d9ef8a1342ed5e90945f31167f565eb8` (107) |
| `Toy.SendSync.guard_rc_plain_transfer_race` | guard-not-send: C | Quot.sound, propext | `3e0ab6cafade8403bf9b8238bd0d1481e85e4b77dcd2f7885a2338f1d0aba263` | `f991b1ec68391c4ffee26e34f94ab7b4d9ef8a1342ed5e90945f31167f565eb8` (107) |
| `Toy.SendSync.guard_sync_examples` | guard-sync-iff: C | Quot.sound, propext | `21dd8c9cb87a3135b3167c79e63944ef012fab966950b3476e6c60678c3abd4d` | `7f0fe3b1db041c6aa049e1b61bf750aa28d29364ba50ae23baca5ea95e70b291` (110) |
| `Toy.SendSync.guard_transfer_race_iff` | guard-not-send: C | Quot.sound, propext | `a2fad513728ab64f1a1abfac8b3a4d4c404c908d123b9bc127692be03650c8b4` | `f991b1ec68391c4ffee26e34f94ab7b4d9ef8a1342ed5e90945f31167f565eb8` (107) |
| `Toy.SendSync.implsSound_examples` | definition-examples: R (example) | Quot.sound, propext | `57696d5f8c3ae232313fd83882a14db6f0329001af38da6652579c3e800bf222` | `f42c38801d9f6faa8f8d59f5c22b367e97335c1641177840284f7472f7ead4f2` (112) |
| `Toy.SendSync.mutex_cell_plain_semSync_content_not_semSync` | mutex-sync-iff: C; mutex-sync-iff: NV | Quot.sound, propext | `d3aff872129d265029775e9c7d931284388698dd7cda9b562b88696fdd08072e` | `cceba79b2527622d62ebd46dc51978e5940f7eaa89b9a8a46e76289bdb50bdee` (111) |
| `Toy.SendSync.mutex_cell_rc_plain_not_semSync` | cell-not-sync: C | Quot.sound, propext | `3491579a5a1815606fffa5c4bb072eaee31c964c957424374fbcff74389e6e9b` | `7f0fe3b1db041c6aa049e1b61bf750aa28d29364ba50ae23baca5ea95e70b291` (110) |
| `Toy.SendSync.mutex_rc_plain_content_not_semSend_mutex_neither` | mutex-sync-iff: C | Quot.sound, propext | `1ef2aa213057ff18f27e852c9ce2e7366ead54a45626b6c8b077f36116574aea` | `cceba79b2527622d62ebd46dc51978e5940f7eaa89b9a8a46e76289bdb50bdee` (111) |
| `Toy.SendSync.nfr_example` | definition-examples: R (example) | none | `68f6a1eacf065e35f9ac85213e50f8850650e1e1de6fc3d8a7bb75da760fbfe2` | `c5beec1a8e9a1ef8fd54bf7ff29dc6a76057751dfece31b224b3eda10bd9d4a2` (27) |
| `Toy.SendSync.nfr_example_fresh_release` | definition-examples: R (example) | propext | `f0555057056720d80a62861cc1cb0aff0b380bae9f3b0c4a7c1a20abb0344a34` | `c5beec1a8e9a1ef8fd54bf7ff29dc6a76057751dfece31b224b3eda10bd9d4a2` (27) |
| `Toy.SendSync.nfr_example_precondition` | definition-examples: R (example) | propext | `0bb13b9586a892cfced17cbfeba0a5d99d662c8810d291120da8bdde057c5feb` | `23e1bbfc7e702ee8db476325023402f24593149afcf8687740bf00e03520bd0a` (26) |
| `Toy.SendSync.nfr_example_unnamed_release` | definition-examples: R (example) | propext | `7342617e048a64e875add706cedde7a02814ec869081914f0880aef48c6fd79f` | `b12588dc98a0389a526949d85cc0136360072156dc08132b22a3e41f9dec2591` (28) |
| `Toy.SendSync.noImplTable` | std-table-sound: C; definition-examples: C | none | `702d6d8eb15415cd8368c30b3d7051d580ac0ff00f5869f20f97049d4290f556` | `30740ea48fe3e7ce5fae84902c9ae3857d905c92e3a7a41e0aec74bfd44f2a15` (11) |
| `Toy.SendSync.not_compatible_example_uniq_via` | definition-examples: R (example) | propext | `d2db292b730cdacb6f23d0a1a74995cdaa30f8ff9f375ff1e6391d7dffb72838` | `fbebb3b4ec93284c6fc1e8cdcb5a7846d4dc9914aa776804ba1761cdb644a372` (32) |
| `Toy.SendSync.not_forall_semSend_imp_semSync` | false-rule-send-implies-sync: R | Quot.sound, propext | `a19acb116bf553a3167c9eb04c0aea8d5918bd0ebd26ebf73bd1917d84071646` | `cceba79b2527622d62ebd46dc51978e5940f7eaa89b9a8a46e76289bdb50bdee` (111) |
| `Toy.SendSync.not_forall_semSync_imp_semSend` | false-rule-sync-implies-send: R | Quot.sound, propext | `7e4241fe10c49105ba20be0b455c76576b9531a480afb896b54db8ad645d476e` | `cceba79b2527622d62ebd46dc51978e5940f7eaa89b9a8a46e76289bdb50bdee` (111) |
| `Toy.SendSync.not_nfr_example` | definition-examples: R (example) | propext | `fcbf1fd6b51345b516bc3029a8d254a112bcc1fc977deba7c7b9f28683ddd944` | `c5beec1a8e9a1ef8fd54bf7ff29dc6a76057751dfece31b224b3eda10bd9d4a2` (27) |
| `Toy.SendSync.not_nfr_example_placed` | definition-examples: R (example) | propext | `e884eda566df5a8b6c95a4c33404dc9e1fa2912cb8535bb6bac415f37458ae8a` | `23e1bbfc7e702ee8db476325023402f24593149afcf8687740bf00e03520bd0a` (26) |
| `Toy.SendSync.not_race_example_atomic_atomic` | definition-examples: R (example) | propext | `47df1e089a46ecc41e10967c52438362498612d2cdc415f88cc76cf613df8d35` | `8abd4c0718dab906627e6fbfb540b06d9a0e029db79ca4a2b06d7d47656bb198` (58) |
| `Toy.SendSync.not_race_example_locked_writes` | definition-examples: R (example) | propext | `ad1db6d814e402ce318f8a3193306f18cbabade3d6b55b8350d907ae7e2ce261` | `8abd4c0718dab906627e6fbfb540b06d9a0e029db79ca4a2b06d7d47656bb198` (58) |
| `Toy.SendSync.not_race_example_read_read` | definition-examples: R (example) | propext | `17e58786cf8c966f9affa73ece39fd0ca2f9cf1c41432fa57d2337bb5f534733` | `8abd4c0718dab906627e6fbfb540b06d9a0e029db79ca4a2b06d7d47656bb198` (58) |
| `Toy.SendSync.not_semSend_examples` | definition-examples: R (example) | propext | `8aca4c42efcbe4f499d4fe7f5433247e95cc31af54c1bbe35d654c5185a56694` | `98abfbd8f1031acf90152fd5055e9ee533db023b1d839a224c2c790b15ddb5ce` (110) |
| `Toy.SendSync.not_semSend_guard` | guard-not-send: R | propext | `33e74378b60eebb41c33ce65901ef7bfe30d7ff4eab072250a9ce6948450b340` | `98abfbd8f1031acf90152fd5055e9ee533db023b1d839a224c2c790b15ddb5ce` (110) |
| `Toy.SendSync.not_semSend_rc` | rc-neither: C | propext | `3cf3b35259b7de9f73d667dda165c77a048f5e9822b68427db51e92d40eb3f9c` | `98abfbd8f1031acf90152fd5055e9ee533db023b1d839a224c2c790b15ddb5ce` (110) |
| `Toy.SendSync.not_semSend_rc_and_not_semSync_rc` | rc-neither: R | propext | `55940b8b9bd79bb4a70f515335d4af45f780cf15348e2b3c3d3d8005c44f4715` | `cceba79b2527622d62ebd46dc51978e5940f7eaa89b9a8a46e76289bdb50bdee` (111) |
| `Toy.SendSync.not_semSync_cell` | cell-not-sync: R | propext | `6ec922914cbd69f0e86e7f305541672ac786ea4ef07a0ec6825c6ff8d08b9d04` | `7f0fe3b1db041c6aa049e1b61bf750aa28d29364ba50ae23baca5ea95e70b291` (110) |
| `Toy.SendSync.not_semSync_examples` | definition-examples: R (example) | propext | `fc392e9e262f81b00b7af0883dfb55ea62d360f2d3b337ca2a4d0920524778d8` | `7f0fe3b1db041c6aa049e1b61bf750aa28d29364ba50ae23baca5ea95e70b291` (110) |
| `Toy.SendSync.not_semSync_rc` | rc-neither: C | propext | `ed53924264aa5460b7f6933337b92e2c7590ad9dd2acb61d25898e6f22ab7660` | `7f0fe3b1db041c6aa049e1b61bf750aa28d29364ba50ae23baca5ea95e70b291` (110) |
| `Toy.SendSync.not_semSync_refCell` | cell-not-sync: C | propext | `beed799376a362c3e4bbc193d3ceb215382f6a75336e448be7005e126dfb1c6f` | `7f0fe3b1db041c6aa049e1b61bf750aa28d29364ba50ae23baca5ea95e70b291` (110) |
| `Toy.SendSync.not_semSync_wrap_cell_full` | wrap-cell-obligation: C | propext | `bcb8299fffd3fcf4526a6abba4f2a3b51340e6ea559f0b1788b8699c3094ce75` | `7f0fe3b1db041c6aa049e1b61bf750aa28d29364ba50ae23baca5ea95e70b291` (110) |
| `Toy.SendSync.not_syncObligation_cell_full` | definition-examples: R (example) | propext | `26ec49b66dcbdc08594a0736d0104e6727af2aef286846d6abe7bc96285b744f` | `d45842423a1f44376b04f54f1532629d1af0a0c3166cf4082d183d2fbfed2c5b` (109) |
| `Toy.SendSync.not_tableSound_rcSendTable` | definition-examples: R (example) | propext | `b4f4bc6057b16a1ce6a8050c5f6aaa6068bd96dcc04c7414fd0d185575e7e62b` | `bb411953f51aaa166a3357d0163b44c58b9fc5689ecd70da0251250de9df2e70` (140) |
| `Toy.SendSync.ownReadsRaceFree_examples` | definition-examples: R (example) | Quot.sound, propext | `86f12d3ecefe9d42a7477a65f9a943f240d5141d596c444da859169435e3bd22` | `91493070ea96600b8812f89794cf7c5cd8648340965b013cd83897475f810929` (108) |
| `Toy.SendSync.ownReadsRaceFree_guard_iff` | wrap-cell-obligation: C | Quot.sound, propext | `b5486b895ffc01caf6bd9aa499a7d8e11b1a193ee7890089b32e5ef8a9284a77` | `91493070ea96600b8812f89794cf7c5cd8648340965b013cd83897475f810929` (108) |
| `Toy.SendSync.ownReadsRaceFree_of_semSend` | wrap-cell-obligation: C | propext | `110f6417548eba99c6cd85f96e489e14073d7423e2491003b7b88a726975ec5e` | `2bb4005e1231a1f41d7a8126a49c9e6255a37dc3c42641ac72d76ee9e49d8edd` (111) |
| `Toy.SendSync.place` | definition-examples: C | none | `81c52fd963e56eb445c957372955afe6a55aee46898fb1a499de1ac6f68babb1` | `eab84d5089f79393dfc116bd5490102af9121812babfe622e352fd864a7687cd` (15) |
| `Toy.SendSync.plain_own_not_subset_shr_semSend` | own-in-shared-sync-implies-send: C | propext | `c9a4b0f989fe5d2cafcc8c58b5d39a6d2e733dd0a5b3ada1bfef967f32585654` | `98abfbd8f1031acf90152fd5055e9ee533db023b1d839a224c2c790b15ddb5ce` (110) |
| `Toy.SendSync.prod_plain_nonvacuous` | structural-constructors: NV | Quot.sound, propext | `829920a1370589a629a46380b4c7993a43d87ab97c17e40d35f63f59a28198ea` | `cceba79b2527622d62ebd46dc51978e5940f7eaa89b9a8a46e76289bdb50bdee` (111) |
| `Toy.SendSync.race_example_locked_vs_unlocked` | definition-examples: R (example) | propext | `08e7fc32d112c2139d7cbeed2b2f4440a83b4f626ae555d9268c6bd0644fabaf` | `8abd4c0718dab906627e6fbfb540b06d9a0e029db79ca4a2b06d7d47656bb198` (58) |
| `Toy.SendSync.race_example_write_read` | definition-examples: R (example) | propext | `fb63b3d72ee187d48ebeb12b4a9a68f9e61792cd004f3ae15340799099858488` | `8abd4c0718dab906627e6fbfb540b06d9a0e029db79ca4a2b06d7d47656bb198` (58) |
| `Toy.SendSync.rcSendTable` | structural-soundness: C; definition-examples: C | none | `702d6d8eb15415cd8368c30b3d7051d580ac0ff00f5869f20f97049d4290f556` | `30740ea48fe3e7ce5fae84902c9ae3857d905c92e3a7a41e0aec74bfd44f2a15` (11) |
| `Toy.SendSync.rc_plain_neither` | rc-neither: C; rc-neither: NV | propext | `51361207c21c72bd74719da8c91e5dfc6f9ab80993005a77059ba894f5f78803` | `cceba79b2527622d62ebd46dc51978e5940f7eaa89b9a8a46e76289bdb50bdee` (111) |
| `Toy.SendSync.relNamesAcq_example` | definition-examples: R (example) | propext | `e1d9b02be18cc449b0c56bd0d1d659b793dcf1bd67eb9c11e9db78f0dce0b917` | `c0c85e88973f657d217c32050d2e6d96605431f974ec467e0499b0398c6cece9` (20) |
| `Toy.SendSync.rootEv` | definition-examples: C | none | `c6c8d13bac94c7daf135773d090b420ad92ee420bd765157221da9a1bd659ef8` | `eab84d5089f79393dfc116bd5490102af9121812babfe622e352fd864a7687cd` (15) |
| `Toy.SendSync.rule_holds_of_eval` | structural-soundness: C | propext | `f7da1ae1c0a0e5c443941f0d1b64e4478df5b5678aeb9cb797c11a313112b4f2` | `084c693450a005568e05429caad2f49a3ca8f79c6205b45d5d330a0a594a3dc9` (7) |
| `Toy.SendSync.semSend_arc_iff` | arc-send-iff: R | Quot.sound, propext | `f24ba94e54d3b8f36e37d288cd514300361fdda9b14a28caec0b9fac03ebb0fb` | `cceba79b2527622d62ebd46dc51978e5940f7eaa89b9a8a46e76289bdb50bdee` (111) |
| `Toy.SendSync.semSend_box_iff` | structural-constructors: C | propext | `aeaa69d80304a54627c95660158284d5d9c0013e097756aeaba506e2cebe3fba` | `98abfbd8f1031acf90152fd5055e9ee533db023b1d839a224c2c790b15ddb5ce` (110) |
| `Toy.SendSync.semSend_cell_iff` | cell-send-iff: R | Quot.sound, propext | `dbba7491cc37cee5461e30c3689c1d6ef90872461d7ee77258835ce89884c74d` | `98abfbd8f1031acf90152fd5055e9ee533db023b1d839a224c2c790b15ddb5ce` (110) |
| `Toy.SendSync.semSend_examples` | definition-examples: R (example); definition-examples: NV | Quot.sound, propext | `1bfc938851e8486738db73449a6829bf01b3947a554f124b396557e873f7827d` | `98abfbd8f1031acf90152fd5055e9ee533db023b1d839a224c2c790b15ddb5ce` (110) |
| `Toy.SendSync.semSend_imp_semSync_of_shr_no_write` | false-rule-send-implies-sync: PC; shared-write-free-send-implies-sync: R | Quot.sound, propext | `ae94de95a4e8dd7a146f6d0549367a7226c686640015f0a9ab093a18dbec0323` | `cceba79b2527622d62ebd46dc51978e5940f7eaa89b9a8a46e76289bdb50bdee` (111) |
| `Toy.SendSync.semSend_imp_semSync_of_shr_no_write_nonvacuous` | shared-write-free-send-implies-sync: NV | propext | `b7ea24c105423315e9b2015725fbae7cdb8bf23ad9aa6339b4c6bf42dab2e15c` | `98abfbd8f1031acf90152fd5055e9ee533db023b1d839a224c2c790b15ddb5ce` (110) |
| `Toy.SendSync.semSend_imp_semSync_of_shr_no_write_semSend_tight` | shared-write-free-send-implies-sync: CE | propext | `9893c244ecc40d7f91c6231a186165f4ba16b640010e9bee6537cebf76219db3` | `7f0fe3b1db041c6aa049e1b61bf750aa28d29364ba50ae23baca5ea95e70b291` (110) |
| `Toy.SendSync.semSend_mutex_iff` | mutex-sync-iff: C | Quot.sound, propext | `6cf44550be927ab363f0f017f361a5923d5c2f2ccc2abcede78f17631e6ab285` | `98abfbd8f1031acf90152fd5055e9ee533db023b1d839a224c2c790b15ddb5ce` (110) |
| `Toy.SendSync.semSend_prod_iff` | structural-constructors: R | Quot.sound, propext | `c2f7dea22ef2c296087c4c5865519a9378cccf57bac14144d44d33abef07a5ba` | `98abfbd8f1031acf90152fd5055e9ee533db023b1d839a224c2c790b15ddb5ce` (110) |
| `Toy.SendSync.semSend_refCell_iff` | cell-send-iff: C | Quot.sound, propext | `c3dce9b4e79079f69be30cb67ea1eace6295b96438f637bec2a05b7817a1e111` | `98abfbd8f1031acf90152fd5055e9ee533db023b1d839a224c2c790b15ddb5ce` (110) |
| `Toy.SendSync.semSend_refMut_iff` | link-sync-iff-ref-send: C | propext | `8778c9c0ea6f4fc101e341630f463aac2657953710a5fefe6ba861339049a4f6` | `98abfbd8f1031acf90152fd5055e9ee533db023b1d839a224c2c790b15ddb5ce` (110) |
| `Toy.SendSync.semSend_sum_iff` | structural-constructors: C | Quot.sound, propext | `dac7508c0cbe86045f6f4deb0b470a27537adcfa81169bf96c7ccffb7528a97e` | `98abfbd8f1031acf90152fd5055e9ee533db023b1d839a224c2c790b15ddb5ce` (110) |
| `Toy.SendSync.semSend_wrap_iff` | structural-constructors: C | propext | `aee2becb46dbf88c4a375311788176b357717067afc9ba7a2eba9161154aa5b6` | `98abfbd8f1031acf90152fd5055e9ee533db023b1d839a224c2c790b15ddb5ce` (110) |
| `Toy.SendSync.semSync_arc_iff` | arc-send-iff: C | Quot.sound, propext | `f04925b814090a28e93e862a279a31e2c7389edaa762e6da2a753f1a5487f9e0` | `cceba79b2527622d62ebd46dc51978e5940f7eaa89b9a8a46e76289bdb50bdee` (111) |
| `Toy.SendSync.semSync_box_iff` | structural-constructors: C | propext | `af40b5781df8faa7788fdf2f355b8767222f18456a484a71e4c4c5a22fec943e` | `7f0fe3b1db041c6aa049e1b61bf750aa28d29364ba50ae23baca5ea95e70b291` (110) |
| `Toy.SendSync.semSync_examples` | definition-examples: R (example) | Quot.sound, propext | `54728c9e7f9d9367e51d95c493dd94fa78af2ba361dbf1571b5dbbb490ca1a11` | `7f0fe3b1db041c6aa049e1b61bf750aa28d29364ba50ae23baca5ea95e70b291` (110) |
| `Toy.SendSync.semSync_guard_iff` | guard-sync-iff: R | Quot.sound, propext | `f79671a4adda19257d672cb593674e688fd9048164d1ec5dc43869361c483b5c` | `7f0fe3b1db041c6aa049e1b61bf750aa28d29364ba50ae23baca5ea95e70b291` (110) |
| `Toy.SendSync.semSync_iff_semSend_ref` | link-sync-iff-ref-send: R | propext | `620ceed23f7d87ca64a46589531a15c8096c282c946787d6cf4e52ec16752b50` | `cceba79b2527622d62ebd46dc51978e5940f7eaa89b9a8a46e76289bdb50bdee` (111) |
| `Toy.SendSync.semSync_iff_semSend_ref_nonvacuous` | link-sync-iff-ref-send: NV | propext | `18d713ec8bb9fcbc8a998af7cfbf11aa06e652382e23ce03fcff5329d2abf64c` | `cceba79b2527622d62ebd46dc51978e5940f7eaa89b9a8a46e76289bdb50bdee` (111) |
| `Toy.SendSync.semSync_imp_semSend_of_own_subset_shr` | false-rule-sync-implies-send: PC; own-in-shared-sync-implies-send: R | propext | `531c2e88b64a9620186006c53218fbcdbad998a18ff62e7155adfcc272a812f3` | `cceba79b2527622d62ebd46dc51978e5940f7eaa89b9a8a46e76289bdb50bdee` (111) |
| `Toy.SendSync.semSync_imp_semSend_of_own_subset_shr_nonvacuous` | own-in-shared-sync-implies-send: NV | Quot.sound, propext | `936060009bfcee99bc69d1953230c78db7e1a7744c9b188cfc81802720daa337` | `7f0fe3b1db041c6aa049e1b61bf750aa28d29364ba50ae23baca5ea95e70b291` (110) |
| `Toy.SendSync.semSync_imp_semSend_of_own_subset_shr_semSync_tight` | own-in-shared-sync-implies-send: CE | propext | `4f952188b6fdd9fa8adf37f022f92f718f2f8a98653c5bdda50d8f4329cc04b7` | `98abfbd8f1031acf90152fd5055e9ee533db023b1d839a224c2c790b15ddb5ce` (110) |
| `Toy.SendSync.semSync_mutex_iff` | mutex-sync-iff: R | Quot.sound, propext | `28d0777827a263032f7e35e348a415b3be459849c795cfd08fe3e92ccbc8bf05` | `cceba79b2527622d62ebd46dc51978e5940f7eaa89b9a8a46e76289bdb50bdee` (111) |
| `Toy.SendSync.semSync_prod_iff` | structural-constructors: C | Quot.sound, propext | `64b03041cce611a3de2412ef230ac44ef30285ac7cd4768d1b9510058bcc6179` | `7f0fe3b1db041c6aa049e1b61bf750aa28d29364ba50ae23baca5ea95e70b291` (110) |
| `Toy.SendSync.semSync_refMut_iff` | link-sync-iff-ref-send: C | propext | `c5287e84ef63213019d929d57a504b187e605e3c5830f0a8d4ca2e5660eab31f` | `7f0fe3b1db041c6aa049e1b61bf750aa28d29364ba50ae23baca5ea95e70b291` (110) |
| `Toy.SendSync.semSync_ref_iff` | link-sync-iff-ref-send: C | propext | `10605ff2167bc3dcc8bc0062e0ea75e8aba9105b51c26e33c58656461be2530d` | `7f0fe3b1db041c6aa049e1b61bf750aa28d29364ba50ae23baca5ea95e70b291` (110) |
| `Toy.SendSync.semSync_sum_iff` | structural-constructors: C | Quot.sound, propext | `a6adc05f75c42d6b7a5769ca24a8f2523927392d99da49ee4a20aa51498a7673` | `7f0fe3b1db041c6aa049e1b61bf750aa28d29364ba50ae23baca5ea95e70b291` (110) |
| `Toy.SendSync.semSync_wrap_cell_readOnly_iff_ownReadsRaceFree` | wrap-cell-obligation: R | Quot.sound, propext | `3007ed89e1bc18905e5b7ded55f1f1898c3675dd0abd9d4d676159adcb43a6ee` | `474ec21aaab77d396d52993c0ee6288132ff067b30cf8574d43a706cca580dc1` (111) |
| `Toy.SendSync.semSync_wrap_full_iff` | unsafe-sync-obligation: C | propext | `48d65c73457eba97a23f24fa8dbfe7f296ada2a289ec2ac5891f286ed061fc1f` | `7f0fe3b1db041c6aa049e1b61bf750aa28d29364ba50ae23baca5ea95e70b291` (110) |
| `Toy.SendSync.semSync_wrap_iff_syncObligation` | unsafe-sync-obligation: R | propext | `44011b031541cd155a1a038acca45c8fdd4c8f07a3e23f2017ccb802c60ad05f` | `20fc5c5a56270315eb9f246914ed55d0fa89aeacbc6fdde2bcb42c37b56fdb94` (111) |
| `Toy.SendSync.semSync_wrap_none` | wrap-view-restriction: C; wrap-cell-obligation: C | propext | `b18b4d240f10e00d0f749127dcf2ba33560dfd1489817f523147c35e85c40ae7` | `7f0fe3b1db041c6aa049e1b61bf750aa28d29364ba50ae23baca5ea95e70b291` (110) |
| `Toy.SendSync.semSync_wrap_of_semSync` | wrap-view-restriction: R | propext | `74cb744dc79e7bf71f02953358eedea01c61ca13f13284cc4fcedde7d947c13f` | `7f0fe3b1db041c6aa049e1b61bf750aa28d29364ba50ae23baca5ea95e70b291` (110) |
| `Toy.SendSync.semSync_wrap_of_semSync_nonvacuous` | wrap-view-restriction: NV | Quot.sound, propext | `ab64bf284018f6c7877f98c1a4270d3bed2a23f5a583524ffdead2c60395a039` | `7f0fe3b1db041c6aa049e1b61bf750aa28d29364ba50ae23baca5ea95e70b291` (110) |
| `Toy.SendSync.semSync_wrap_of_semSync_tight` | wrap-view-restriction: CE | propext | `36956792640e73a5d5004bc4b3c6230b4a403b8c330168962248484b7e4741d9` | `7f0fe3b1db041c6aa049e1b61bf750aa28d29364ba50ae23baca5ea95e70b291` (110) |
| `Toy.SendSync.semSync_wrap_rc_iff` | wrap-rc-obligation: R | propext | `94354d5e9440bd7d27cb7393a19e76f79bc6fc6ec376ed3b47f6eb9d8f1eef9a` | `7f0fe3b1db041c6aa049e1b61bf750aa28d29364ba50ae23baca5ea95e70b291` (110) |
| `Toy.SendSync.semSync_wrap_refCell_plain_readOnly` | wrap-refcell-obligation: C | propext | `c35d61ba1ae8ae432665e958b0dbcec1275c73e64c2ad1f947075fa88b349c74` | `7f0fe3b1db041c6aa049e1b61bf750aa28d29364ba50ae23baca5ea95e70b291` (110) |
| `Toy.SendSync.semSync_wrap_refCell_readOnly_iff_shrReadsRaceFree` | wrap-refcell-obligation: R | Quot.sound, propext | `300807de32dca963e3e4aeeb108b15ededa65e59c9330f1d41085e7788c9ecc4` | `0a1f1e4b08280b13a368c6f12fb7293cb02c3b54a31c518543ee1c0d21162d0c` (111) |
| `Toy.SendSync.shrReadsRaceFree_examples` | definition-examples: R (example) | propext | `045381c8ca4ceefdb360b33ab9b109762eaf60ef53cfcb4e5ba10f994ce391c9` | `8ea8eefb7ca38f90351ac9f382ae75089e8a743fe71ea9224aa51476775d30e9` (108) |
| `Toy.SendSync.shrReadsRaceFree_of_ownReadsRaceFree` | wrap-refcell-obligation: C | Quot.sound, propext | `4f5e590b73fac51f04877ec21c21cedad64b193004c8e7c0cf2837853cb8cd54` | `b2b11ce42366f7ce0c5fb00ebf420ed90f34ecf46180e137cde48fb5d7b5619f` (109) |
| `Toy.SendSync.shr_subset_own` | shared-write-free-send-implies-sync: C | Quot.sound, propext | `90d0598227cef08333c297957c2aa283febe25648978564604feba378fb60bdf` | `403fbbefa1d64cefb50c15e1198f813e8c081045ffc021a59e33cb3b6afab9fe` (77) |
| `Toy.SendSync.stdTable` | std-table-sound: C; definition-examples: C | none | `702d6d8eb15415cd8368c30b3d7051d580ac0ff00f5869f20f97049d4290f556` | `30740ea48fe3e7ce5fae84902c9ae3857d905c92e3a7a41e0aec74bfd44f2a15` (11) |
| `Toy.SendSync.stdTable_positive_rules_nonvacuous` | std-table-sound: C; std-table-sound: NV | Quot.sound, propext | `31ff66681afac89913959ece40a4c998931d56b9daa896c75091343c3a6f680f` | `3f18005709a482b38734e2ad904d055dbd0142a194378fd83680e2f2743700ac` (134) |
| `Toy.SendSync.stdTable_sound` | std-table-sound: R | Quot.sound, propext | `1c7948e0aebf32fa4304c057e2df5f75f0b4b37003861ac90e4ad3b76671733e` | `c602cbb922e36bf60e49a2c640c0859188cb7ec5261a133c0bab704c746e039b` (135) |
| `Toy.SendSync.syncObligation_nonvacuous` | unsafe-sync-obligation: NV | Quot.sound, propext | `cb8d4e5575965dddd18db9be8396c7fef0ddb94d183136b52f56781854f8bb0d` | `d45842423a1f44376b04f54f1532629d1af0a0c3166cf4082d183d2fbfed2c5b` (109) |
| `Toy.SendSync.tableSound_noImplTable` | std-table-sound: C; definition-examples: R (example) | propext | `7b0d6e0a0fada6c42effa36ea0651b4083dc996e280a3197fea2ced4d1daa043` | `30a4e16815013ce44298e6bd342db2e06dbb85a59e7eb59345a66aad3e8bd310` (134) |
| `Toy.SendSync.unsafeSync_wrap_cell_full_accepted_but_racy` | unsafe-sync-obligation: C | propext | `29d90233ad310eb884c7e2e40c0ae1547e5dd58cf1a0f112f90c154192599251` | `4fc9142aa617496b5750e2c85dbd4222ce8c9145556ab3e3e2dc074ade4e38ca` (130) |
| `Toy.SendSync.wrapFree_examples` | definition-examples: R (example) | none | `274e100f33a8ea8018f83f8339cc1cea88652aee1c09e75b713ee48a273d86a6` | `5bd7b251b86f7effb9518bd99f8d911d6d9a8236db2db81a48ee1ed1ad7cfbff` (26) |
| `Toy.SendSync.wrap_arc_cell_readOnly_not_semSync` | wrap-cell-obligation: C | propext | `94ab34725c3bc9cb13d4a5a1a3924db9b30af28091f1003bc17a0cdf5ecb6441` | `7f0fe3b1db041c6aa049e1b61bf750aa28d29364ba50ae23baca5ea95e70b291` (110) |
| `Toy.SendSync.wrap_cell_guard_plain_readOnly_semSync` | wrap-cell-obligation: C | Quot.sound, propext | `4a4c6d2549f795c6d2a5f0c01e7f4ee6e6124c137af45763eb6466406d5a2637` | `8a60acfdc8dbb1e971e88967f02fc810a518793d40a5e3372c8a2af18e745eab` (112) |
| `Toy.SendSync.wrap_cell_plain_readOnly_nonvacuous` | wrap-cell-obligation: NV | Quot.sound, propext | `8c4b06932e71456cc4d0200a023d9abecf512e09c22dae2f886ab932e4575a1e` | `474ec21aaab77d396d52993c0ee6288132ff067b30cf8574d43a706cca580dc1` (111) |
| `Toy.SendSync.wrap_cell_ref_cell_readOnly_not_semSync` | wrap-cell-obligation: C | Quot.sound, propext | `245c448e69d1321aabd357112cb18cc12a71903ffbf828ed8c3078e2a912db03` | `474ec21aaab77d396d52993c0ee6288132ff067b30cf8574d43a706cca580dc1` (111) |
| `Toy.SendSync.wrap_rc_none_semSync_not_semSend` | false-rule-sync-implies-send: C; wrap-rc-obligation: NV | propext | `82877dfb19b213c0d0dada02edce4e307c93abfde791aefedc10cddc595a2893` | `cceba79b2527622d62ebd46dc51978e5940f7eaa89b9a8a46e76289bdb50bdee` (111) |
| `Toy.SendSync.wrap_readOnly_cell_refCell_differ` | wrap-refcell-obligation: C | Quot.sound, propext | `38605f13729ca6ae49d2d3cf749d19e94899153d92c3085aa07443bf71539d81` | `021293f4939407ae0deee90961a8a39aa4609010aafc270cb5b5187bd8256c4f` (112) |
| `Toy.SendSync.wrap_refCell_plain_readOnly_nonvacuous` | wrap-refcell-obligation: NV | propext | `b921e9fdd31a2082ecd8b866c44ef9a01c31c4fd180d338ae77bf81446e5cfb4` | `0a1f1e4b08280b13a368c6f12fb7293cb02c3b54a31c518543ee1c0d21162d0c` (111) |
| `Toy.SendSync.wrap_refCell_ref_cell_readOnly_not_semSync` | wrap-refcell-obligation: C | Quot.sound, propext | `42458e666303a068540917e1a90f291b959f36b30f98631b9256f7591848eb1d` | `0a1f1e4b08280b13a368c6f12fb7293cb02c3b54a31c518543ee1c0d21162d0c` (111) |

### Primary sources

All sources below were read at the stated revisions on 2026-11-21. The exact lines each card relies on are listed in that card's **Prior art** entry.

* Lean 4: `leanprover/lean4`, tag `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52` (commit dated 2026-09-24).
* Rust: `rust-lang/rust`, tag `1.100.0` (annotated tag object `6b503e798d0cc01ca1052eeefaccee43893b0ff6`, tagged 2026-11-12), commit `0ef1bc386059596dada8fb65b50425aab2ea637a`; files `library/core/src/marker.rs`, `library/core/src/cell.rs`, `library/core/src/sync/sync_view.rs`, `library/alloc/src/rc.rs`, `library/alloc/src/sync.rs`, `library/std/src/sync/poison/mutex.rs`, `library/std/src/sync/poison/rwlock.rs`.
* The Rustonomicon: `rust-lang/nomicon`, commit `b0bb569883a3e65ab19d4f1adf1b8dbc1629d0a6` (commit dated 2026-10-17), `src/send-and-sync.md`.
* The Rust Reference: `rust-lang/reference`, commit `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` (commit dated 2026-11-17), `src/special-types-and-traits.md`, rules `lang-types.auto-traits.*` (lines 156-181).
* Rust RFCs: `rust-lang/rfcs`, commit `f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4` (commit dated 2025-11-29), `text/0019-opt-in-builtin-traits.md` and `text/0458-send-improvements.md`.
* Ralf Jung, Jacques-Henri Jourdan, Robbert Krebbers, Derek Dreyer. "RustBelt: Securing the Foundations of the Rust Programming Language." Proc. ACM Program. Lang. 2(POPL), Article 66, January 2018. DOI 10.1145/3158154.
* Hoang-Hai Dang, Jacques-Henri Jourdan, Jan-Oliver Kaiser, Derek Dreyer. "RustBelt Meets Relaxed Memory." Proc. ACM Program. Lang. 4(POPL), Article 34, January 2020. DOI 10.1145/3371102.
* `rust-lang/rust` issue 41622, "MutexGuard<Cell<i32>> must not be Sync", https://github.com/rust-lang/rust/issues/41622 (cited under the card `guard-sync-iff`).
* `rust-lang/rust` issue 51780, "Insufficient synchronization in `Arc::get_mut`", https://github.com/rust-lang/rust/issues/51780 (cited in the non-claims of the cards `std-table-sound`, `rc-neither` and `arc-send-iff`).

### Related work (not relied on)

These works are related to the package's topic; no card relies on a claim from them. Bibliographic records were checked
against publisher metadata.

* Chandrasekhar Boyapati, Robert Lee, Martin Rinard. "Ownership Types for Safe Programming: Preventing Data Races and
  Deadlocks." OOPSLA 2002, pp. 211-230. DOI 10.1145/582419.582440. A static ownership type system guaranteeing data-race
  and deadlock freedom with lock-ownership invariants.
* Colin S. Gordon, Matthew J. Parkinson, Jared Parsons, Aleks Bromfield, Joe Duffy. "Uniqueness and Reference
  Immutability for Safe Parallelism." OOPSLA 2012. DOI 10.1145/2384616.2384619. Uniqueness and reference immutability for
  race-free parallelism.
* Sylvan Clebsch, Sophia Drossopoulou, Sebastian Blessing, Andy McNeil. "Deny Capabilities for Safe, Fast Actors."
  AGERE! 2015. DOI 10.1145/2824815.2824816. Reference capabilities defined by which aliases they deny, related in spirit
  to the `own`/`shr`/`alias` footprints here.
* Hans-J. Boehm, Sarita V. Adve. "Foundations of the C++ Concurrency Memory Model." PLDI 2008. DOI
  10.1145/1375581.1375591. The C++ concurrency memory model (data-race-free programs and atomic operations); `Conflicting`
  and `Race` here have no happens-before relation and no memory orderings.

## Revalidation

**Requirements.** `elan` (so that `lake` uses the toolchain pinned in `lean/lean-toolchain`) and `python3`. No network access is needed after the toolchain is installed; the Lean project has no dependencies.

**Primary check (one command).** From the package directory:

```sh
python3 support/revalidate.py .
```

It copies `lean/` to a temporary directory (the package is not modified), runs `lake build`, rejects any Lean source containing `sorry`, `admit`, `native_decide` or an `axiom` declaration, and then elaborates an inline audit program that (1) computes, with Lean's `collectAxioms`, the axioms of every declaration of the `ToySendSync` library and fails if any uses an axiom other than `propext`, `Classical.choice`, `Quot.sound`; and (2) for every Lean name referenced by `results.json` (fields `lean`, `lean_names`, `nonvacuity_witness_lean`, `positive_control_lean`, and hypothesis `counterexample`s), recomputes two SHA-256 hashes and compares them with `audit/statements.json`:

- the **statement hash**: SHA-256 of `toString (repr ci.type)`, the Lean `repr` of the declaration's elaborated type;
- the **closure hash**: SHA-256 of the newline-joined, sorted list of entries `name : repr(type)` (plus ` := repr(value)` for non-theorems) for every constant of the `ToySendSync` library reachable from the statement's type through types, definition bodies and inductive constructors (theorem bodies excluded). A change to any definition a statement depends on therefore changes its closure hash; documentation comments are not part of either hash.

It prints `REVALIDATED` and exits with status 0 if and only if every check passes. Expected output ends with `ok   axioms (704 declarations)`, `ok   statement hashes (183 hashed names; 0 referenced names exist but carry no recorded hash)` and `REVALIDATED`.

**Manual equivalent.**

```sh
cd lean
lake build                              # builds library ToySendSync; must succeed with no `sorry` warnings
lake env lean RevalidationAudit.lean    # prints `#print axioms` for every name recorded in audit/statements.json
```

`lean/RevalidationAudit.lean` is outside the library target (it is not built by `lake build`). It imports `ToySendSync` and issues `#print axioms` for each of the 183 Lean names recorded in `audit/statements.json` (every package-local name that `REPORT.md` cites); elaboration fails if a name is missing, and each printed line must list a subset of `propext`, `Classical.choice`, `Quot.sound`. The recorded per-declaration axioms are in `audit/axioms.json`.

**Cheaper discriminating checks.** If the Lean toolchain is the sole change, re-running the primary check is sufficient: a changed elaboration of any statement or definition shows up as a hash mismatch even when the build succeeds. If a definition in `lean/ToySendSync/` is edited, every card whose closure includes it is stale; the closure hashes identify which. A passing revalidation establishes the kernel-checked statements alone; it does not re-check any modeling-bridge claim or citation, which must be re-read against the sources listed under **Evidence** (for the standard library, diff the cited files between commit `0ef1bc386059596dada8fb65b50425aab2ea637a` and the revision of interest, and compare the impl declarations with `stdTable`).
