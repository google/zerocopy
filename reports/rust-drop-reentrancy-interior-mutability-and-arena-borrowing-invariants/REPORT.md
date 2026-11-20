# Reentrant Drop Semantics, Interior Mutability, and Arena Borrowing Invariants in Rust Verification

## Summary

`Basis: normative + source + execution + derived`

User-defined destructors (`Drop::drop(&mut self)`) run arbitrary Rust code across scope exits, assignments, container clears, and stack unwinding. When an interior-mutable cell (`UnsafeCell<T>`, `Cell<T>`, `RefCell<T>`), reference-counted container (`Rc<RefCell<...>>`), or fixed-slot arena drops an element whose `Drop` implementation holds a shared handle to the enclosing structure, naive two-state ownership protocols break:

1. **Move-before-drop and pre-poising vs. post-drop reset:** When `T` can be moved to the stack prior to dropping, `Cell::set` (`Cell::replace`), `Rc::drop` (`dec_strong` + `_weak` guard before `drop_slow`), `Vec::truncate`/`Vec::clear` (shrinking `self.len` before `drop_in_place`), `LinkedList::clear` (moving list links out), and `Slab::try_remove` prevent reentrant aliasing and double drops. By contrast, `tokio-rs/slab::Slab::clear` (`src/lib.rs:615-619`) resets `self.len = 0` and `self.next = 0` *after* `self.entries.clear()`: if an element destructor panics (for instance, on a blocked reentrant `RefCell::borrow_mut()`), unwinding leaves `entries.len() == 0` while `self.next > 0`, causing a subsequent `slab.insert` (`L1092-1105`) to hit `unreachable!()`.
2. **In-place destruction requires a 4-state `SlotTag` draining machine:** Neither `drop_then_free` (`3/6` failing scenarios: reentrant `get` aliasing, reentrant `remove` double-drop, and unwind double-drop) nor `free_then_drop` (`2/6` failing scenarios: reentrant `insert` pops the freed slot from the LIFO freelist and overwrites it while `<T as Drop>::drop(&mut self)` holds a protected `&mut T`, violating Tree Borrows exclusivity and `Pin`'s drop guarantee) is sound. Transitioning `Live(g) -> Draining(g)` (unborrowable and absent from the freelist) *before* releasing the spine lock and dropping under an RAII `FinishDrainGuard` that completes `Draining(g) -> Vacant(g + 1)` on normal return or unwind passes `6/6` scenarios.
3. **Two-tier `PCM.Excl` factoring:** Splitting ownership into `Excl(SpineMeta)` plus per-slot tokens `SlotPerm(i) : Excl(SlotVal)`—stored inside the spine invariant when `Live`/`Vacant` and extracted when `Draining(g)`—allows closing the container invariant before `<T as Drop>::drop` runs, permitting safe reentrancy on all slots $j \neq i$.
4. **Cross-verifier discipline:** RustBelt (`10.1145/3158154`) forces invariant closure via Iris mask $\mathcal{E}$ across non-atomic `drop_in_place`; RefinedRust (`10.1145/3656422`) splits `own`/`shr`/`laid_out` permissions; Creusot (`10.1007/978-3-031-17244-1_6`) pairs prophetic `Resolve` with linear `Ghost<&mut Perm<PCell<T>>>`; Verus (`10.1145/3586037`) bans `requires` and enforces `opens_invariants none` + `no_unwind` on every `impl Drop` (`well_formed.rs:1747-1767`); Anneal verifies post-drop-elaboration `Runtime(PostCleanup)` MIR with `PureLift` `PermTree` and prelude-only `Init.*` state machines.

## Applicability

`Basis: documentation + source`

This report characterizes synchronous drop reentrancy and interior-mutable container invariants across the sixteen subjects in `REPORT.json`:

- **Rust language, compiler, and stdlib (`rust-lang/rust@4b5350e87e48`, `rust-lang/reference@a286e1ecb8ce`, `rust-lang/rfcs@f43d5789b838`):** Covers destructor order, `Cell`, `UnsafeCell`, `RefCell`, `Rc`/`Weak`, `Vec`, `LinkedList`, and `Pin` drop guarantees.
- **Concrete Rust arenas and kernel tables (`tokio-rs/slab@7d1d8ab00a7b`, `orlp/slotmap@eccedefc5e09`, `tock/tock@ba6aa7edc014`):** Covers freelist slots, generational indices, panic-unwind corruption, and `Grant::enter` vs. `try_enter`.
- **Verifiers and operational models (`creusot-rs/creusot@601d97891bb0`, `verus-lang/verus@0dab219272ac`, `proofs-rs/lean-miri@c92d1d9754c9`, `joshlf/anneal@c131b320eeeb`, `leanprover/lean4` `v4.34.1` `5045d0056413`):** Compares invariant masks, linear ghost permissions, prophetic `Resolve`, and prelude-only Lean 4 encodings.
- **Relationship to adjacent corpus packages:** Complements `rust-pin-drop-guarantee-mem-forget-leaks-and-async-cancellation-invariants` (which covers `mem::forget` leaks and async `.await` cancellation) with synchronous `Drop::drop` reentrancy; extends `fixed-arena-capability-forests-transitive-revocation-and-bounded-batch-invariants` to dynamic draining slot tags; and refines the `Drop` comparisons in `rustbelt-refinedrust-verus-creusot-and-rust-ownership-verifiers`, `creusot-std-prophetic-resolve-perm-containers-and-iterator-laws`, `verus-vstd-views-permissions-prophecies-and-os-verification`, and `rust-safety-tag-taxonomies-rudra-hazards-and-stdlib-contracts`.

## Findings

### 1. Destructor Ordering, Pre-Poising, and `Rc<RefCell<...>>` Unwind Hazards

`Basis: normative + source + derived`

Per the Rust Reference (`rust-lang/reference@a286e1ecb8ce`, `src/destructors.md:7-19`), dropping `T` invokes `<T as Drop>::drop(&mut self)` (if `T: Drop`) and then recursively drops fields in declaration order (structs, active enum variants, tuples), array/slice elements from index `0` upward, or trait-object pointees. Passing `&mut self` demands exclusive access across `self`'s footprint throughout the call (`src/behavior-considered-undefined.md:24-40`), except where shared `&T` accesses `UnsafeCell<U>` without an overlapping `&mut T`.

Bae et al. (SOSP 2021, `10.1145/3477132.3483570`) identify **panic / higher-order drop** bugs as a major class of Rust soundness flaws because arbitrary destructors execute before container invariants are restored. Standard containers avoid reentrant aliasing and double-drop unwinding via **move-before-drop** and **pre-poising** (establishing valid empty/shrunk container metadata *before* `ptr::drop_in_place`):

| Container / Method | Source Location | State Update Before `Drop::drop` | Reentrant Access During `Drop::drop` | Panic Unwinding During `Drop::drop` |
| :--- | :--- | :--- | :--- | :--- |
| **`Cell::set`** | `core/src/cell.rs:438-443, 515-519` | `mem::replace(&mut *self.value.get(), val)` swaps `val` in first | Reentrant `get`/`set` accesses valid `val`; no `&mut` overlap | Old `T` on stack drops once; `cell` holds valid `val` |
| **`Rc::drop`** | `alloc/src/rcs/rc.rs:405-417, 2654-2662, 3715-3729` | `dec_strong()` to `0` (`L2657`); binds `_weak` (`L409`) before `drop_in_place` (`L415`) | `Weak::upgrade` (`L3721`) checks `strong() == 0` -> `None`; block stays live | `_weak` drops on unwind, releasing allocation once |
| **`Vec::truncate` / `clear`** | `alloc/src/vec/mod.rs:1736-1756, 3133-3150` | Writes `self.len = len` / `0` (`L1753`, `L3147`) before `drop_in_place` | Via `Rc<RefCell<Vec<T>>>`, reentrant `borrow_mut` panics in `RefCell` | Teardown observes `self.len == 0` (leaks tail, zero double drops) |
| **`LinkedList::clear` / `Drop`** | `alloc/src/collections/linked_list.rs:748-758, 1245-1262` | Moves `(head, tail, len)` into local `LinkedList` (`L751-757`); `DropGuard` drains | Original list is empty (`len = 0`); `RefCell` still guards reentrant `&mut` | `DropGuard` (`L1247-1260`) keeps calling `pop_front_node()` |
| **`Slab::try_remove`** | `tokio-rs/slab@7d1d8ab0`, `src/lib.rs:1124-1144` | Replaces slot with `Entry::Vacant(self.next)`, `len -= 1`, `next = key` before return | Returned `val` drops in caller after `&mut self` ends | Invariants fully restored before `val` drops |
| **`Slab::clear`** | `tokio-rs/slab@7d1d8ab0`, `src/lib.rs:615-619, 1092-1105` | Runs `self.entries.clear()` (`entries.len = 0`) *before* `self.len = 0; self.next = 0` | Under `Rc<RefCell<Slab<T>>>`, reentrant `borrow_mut` panics and triggers unwind | **Broken post-catch state:** if `self.next > 0`, unwind leaves `entries.len() == 0` with `self.next > 0`; `slab.insert` hits `unreachable!()` (`L1101`) |
| **`SlotMap::clear` / `Drain`** | `orlp/slotmap@eccedefc`, `src/basic.rs:506-514, 659-685` | `clear()` calls `self.drain()`, updating version/freelist per yielded slot | `Drain` retains `&mut self`; `Drain::drop` finishes remaining slots | Unwind resumes draining remaining occupied slots |

Two source subtleties control soundness:

1. **Why `Cell::set` delegates to `Cell::replace` instead of `*self.value.get() = val`:** In Rust MIR (`compiler/rustc_mir_transform/src/{elaborate_drops,add_moves_for_packed_drops}.rs`), direct assignment `*ptr = val` elaborates as `drop(*ptr); *ptr = move val;`. If `T::drop(&mut self)` holds a shared `&Cell<T>` (e.g., via `Rc<Cell<RecursiveDrop>>`) and calls `cell.set(other)`, `<T as Drop>::drop` and the reentrant `mem::replace` form overlapping `&mut T` references to the same `UnsafeCell` bytes—immediately violating Tree Borrows (`proofs-rs/lean-miri@c92d1d9754c9`, `Miri/TreeBorrows/RetagPolicy.lean:56-92`) and double-dropping the old `T`. Calling `self.replace(val)` moves the old `T` onto the stack *before* running `T::drop`. *(Conversely, Creusot's `PCell::set` at `creusot-std/src/cell/pcell.rs:77-85` validly writes `*self.0.get() = val` because its `perm: Ghost<&mut Perm<PCell<T>>>` argument makes reentrant `PCell` access inside `T::drop` statically impossible.)*
2. **How `RefCell` panic-on-reentrancy exposes `Slab::clear` post-reset bugs:** During `rc.borrow_mut().clear()`, `RefCell` sets `borrow` (`library/core/src/cell.rs:976-983, 1089-1220`) to `WRITING` (`< 0`). A reentrant `rc.borrow_mut()` panics before creating an aliased `&mut`, immediately unwinding `clear()`. Because `Slab::clear` (`src/lib.rs:615-619`) assigns `self.len = 0; self.next = 0;` *after* `self.entries.clear()`, catching the unwind leaves `entries.len() == 0` while `self.next` still points to a previously removed index `k > 0`; a subsequent `slab.insert(x)` enters `insert_at(k, x)` (`L1095`: `k == self.entries.len()` is `false`), indexes `self.entries.get(k) == None`, and aborts at `unreachable!()` (`L1101`). Similarly, `tock/tock` (`kernel/src/grant.rs:1248-1318`) distinguishes panicking `.enter()` from `.try_enter()`, which silently skips an already-entered grant (`None`).

---

### 2. The 4-State `SlotTag` Draining Machine and `Pin` Custom `Drop` Hazards

`Basis: source + execution + derived`

Move-before-drop is illegal whenever elements must be destroyed **in place**—for example, `!Unpin` entries bound by RFC 2349's `Pin` drop guarantee (`library/core/src/pin.rs:509-587`, forbidding storage relocation or reuse until `Drop::drop` exits) or large fixed-arena capability/descriptor slots whose destructors invoke reentrant callbacks against `&Arena`. Exhaustive state-space evaluation establishes why a dedicated **`Draining`** state is mandatory:

```text
  [Vacant(g, next)] ──alloc──> [Live(g)] ──begin_drain──> [Draining(g)]
         ^                                                       |
         |                                                       | FinishDrainGuard::drop
         +----------- push_freelist(g + 1) <---------------------+ (normal return OR unwind)
```

1. **Naive Order A (`drop_then_free` while `Live(g)`):** Leaving `tag[i] = Live(g)` across `drop_in_place(&mut slot[i])` fails `3/6` reentrancy traces: reentrant `get(i)` aliases `<T as Drop>::drop(&mut self)`'s protected `&mut T` (`StrongProtector` in `Miri/TreeBorrows/RetagPolicy.lean:84-86`, `TypedRetag.lean:114-122`); reentrant `remove(i)` double-drops `slot[i]`; and a panic in `T::drop` leaves `tag[i] == Live(g)`, causing container teardown to double-drop `slot[i]`.
2. **Naive Order B (`free_then_drop` — pushing to freelist before `drop_in_place`):** Transitioning `tag[i] = Vacant` and pushing `i` onto the freelist before `drop_in_place` blocks `get(i)`/`remove(i)` double-drops, **but fails `2/6` traces (`reentrant_insert` and `reentrant_insert_other`)**: any LIFO freelist pops `i` first (`free_head == i`) and writes a new value into `slot[i]` while `T::drop(&mut slot[i])` still holds an active `&mut T` and `Pin` forbids storage reuse!
3. **Sound 4-State `SlotTag` Protocol (`Live(g) -> Draining(g) -> Vacant(g + 1)`):**
   - *Step 1 (spine locked):* Check `tag[i] == Live(g)`, decrement `live_len`, extract slot `i`'s permission token, and set `tag[i] = Draining(g)` without pushing `i` onto the freelist.
   - *Step 2 (spine unlocked):* Construct `FinishDrainGuard { arena, idx: i }` on the caller's stack (unreachable by `mem::forget` from `T::drop`) and invoke `ptr::drop_in_place(slot_ptr)`. Reentrant `get(i)`/`remove(i)` observe `Draining(g)` and return `None`; reentrant `insert` only pops a distinct `.vacant` index $j \neq i$.
   - *Step 3 (`FinishDrainGuard::drop`, normal or unwind):* Re-acquire the spine, increment generation to `g + 1` (preventing ABA key aliasing), set `tag[i] = Vacant(g + 1)`, and push `i` onto the freelist.

**`Pin` + custom `Drop` hazard (`library/core/src/pin.rs:521-565`):** Because `Drop::drop` takes `&mut Self` rather than `Pin<&mut Self>`, custom destructors on `!Unpin` nodes must neither move self-borrowed fields out of `&mut self` nor unlock/invoke callbacks before unlinking intrusive neighbor pointers, lest reentrant traversal observe dangling links.

---

### 3. `PCM.Excl` Lock-Token Discipline and Two-Tier Ownership Decomposition

`Basis: source + derived`

Exclusive ownership of a resource $X$ is modeled by the exclusive Partial Commutative Monoid $\text{Excl}(\alpha) ::= \bot \mid \text{unit} \mid \text{some}(x : \alpha)$ with $\text{some}(a) \cdot \text{some}(b) = \bot$. Holding a single monolithic token $\text{Excl}(\text{Arena})$ across `Drop::drop` forbids all reentrant container operations. Reentrant safety on disjoint slots $j \neq i$ uses **two-tier decomposition**:

1. **Spine Lock Token (`Excl(SpineMeta)`):** Protects `tags`, `free_head`, and `live_len` inside an interior-mutable cell/lock, acquired only for atomic state transitions (`begin_drain`, `try_lookup`, `alloc_other`, `finish_drain`) and closed before any user destructor executes.
2. **Per-Slot Tokens (`SlotPerm(i) : Excl(SlotVal)`):** Coupled to `tags[i]` by the spine invariant:
   - `tags[i] ∈ {Live(g), Vacant(g)}` $\implies$ `SlotPerm(i)` resides *inside* the spine invariant.
   - `tags[i] == Draining(g)` $\implies$ `SlotPerm(i)` has been **moved out** into the active `drop` frame!
   By $\text{some}(a) \cdot \text{some}(b) = \bot$, no reentrant call entering the spine invariant can mint a second `&mut` to `slot[i]` or push `i` onto the freelist while `SlotPerm(i)` sits in the draining stack frame.

---

### 4. Verifier Comparison: RustBelt, RefinedRust, Creusot, Verus, and Anneal

`Basis: normative + documentation + source + derived`

| Verifier | Primary Reference / Source | Ownership & Interior Mutability Model | Reentrant `Drop::drop` Discharge Mechanism | Hard Constraints & Tradeoffs |
| :--- | :--- | :--- | :--- | :--- |
| **RustBelt** | Jung et al., POPL 2018 (`10.1145/3158154`) | Iris invariants $I^{\mathcal{N}}$, ghost PCMs (`Excl`, `Auth`), lifetime logic | $\llbracket T \rrbracket$ bundles `ty_drop`; opening $I^{\mathcal{N}}$ drops $\mathcal{N}$ from mask $\mathcal{E}$ for *one atomic step* | `Drop::drop` is non-atomic and demands mask $\top$, forcing $I^{\mathcal{N}}$ closure (`Draining` + extracted `Excl`) before `drop_in_place` |
| **RefinedRust** | Gaher et al., PLDI 2024 (`10.1145/3656422`) | Lithium separation logic (`own` place, `shr` invariant, `laid_out` bytes) | Extracts `own` place from backing `laid_out` storage across `drop` steps | Requires re-establishing `shr` container invariants before running arbitrary element drops |
| **Creusot** | Denis et al., ICFEM 2022 (`10.1007/978-3-031-17244-1_6`); `creusot-rs/creusot@601d9789` | Prophetic `&mut` (`*x`, `^x`), `Resolve::resolve` (`resolve.rs:9-33`), `Invariant` (`invariant.rs:80-100`), `PCell` + `Perm` (`pcell.rs:25-108`) | `resolve(x)` discharges borrow ends purely; `PCell::set` (`pcell.rs:77-85`) holds `Ghost<&mut Perm<PCell<T>>>`, blocking reentrant access by `T::drop` | Interior-mutable containers without external `Perm` tokens must restore `Invariant` before arbitrary calls/drops (`#[trusted]` primitives) |
| **Verus** | Lattuada et al., OOPSLA 2023 (`10.1145/3586037`); `verus-lang/verus@0dab2192` | Linear `tracked` `PointsTo`, `AtomicInvariant` (`inv_masks.rs`), `LocalInvariant` (`InvariantBlockGuard<'a>` + `OpenInvariantCredit`, `invariant.rs:215-345`) | `vir/src/well_formed.rs:1747-1767` enforces **3 hard compiler checks** on every `impl Drop`: no `requires`, `opens_invariants none`, and `no_unwind` | Implicit scope-exit drops inside open invariant blocks cannot open further invariants or unwind, preventing invariant-mask reentrancy |
| **Anneal** | `joshlf/anneal@c131b320` (`TrustedBoundary.lean`, `PureLift/{PermTree,SpatialPin}.lean`) | Post-drop-elaboration `Runtime(PostCleanup)` MIR + `PermTree` loan sets + prelude `Init.*` state machines | Compiler drop elaboration (`elaborate_drop` + `add_moves_for_packed_drops`) is already materialized in captured MIR | Verified `theory/` proofs must stay within `Init.*` (`Type 0`, zero `sorry`/custom axioms); `SlotTag` + `Excl` state machines check directly over MIR |

Crucially, `verus/source/vir/src/well_formed.rs:1747-1767` explains why Verus forbids `requires`, `opens_invariants`, and unwinding in `Drop::drop`: because Rust calls `drop` implicitly on every exiting or unwinding scope (including inside an open `AtomicInvariant` or `LocalInvariant` block), permitting a destructor to open invariants or panic would collide with active invariant masks (`MaskSet` in `inv_masks.rs`) or leak invariants mid-unwind. Meanwhile, `vstd/invariant.rs:215-266, 276-345` protects `!Sync` `LocalInvariant` from reentrant `into_inner` or cross-thread `Send` via lifetime-pinned `InvariantBlockGuard<'a>` and from Landin's-knot logical paradoxes via exec-only `OpenInvariantCredit` tokens.

---

### 5. Prelude-Only Lean 4 (`v4.34.1`) Mechanization (`Verification.DropReentrancyArena`)

`Basis: source + derived`

The following Lean 4 module obeys `joshlf/anneal@c131b320` Pass-1 syntax constraints (`trusted/audit/TrustedBoundary.lean:487-595`: `prelude` + `Init.*` only, zero `sorry`, zero custom axioms, no `do`, `{ x with ... }`, or `omega`):

```lean
prelude
import Init.Core
import Init.Data.Nat.Basic
import Init.Data.List.Basic

namespace Verification.DropReentrancyArena

/-- Exclusive PCM: `unit`, exclusive `some val`, or alias conflict `invalid` (⊥). -/
inductive Excl (α : Type) where
  | unit
  | some (val : α)
  | invalid

def Excl.mul {α : Type} : Excl α → Excl α → Excl α
  | .unit, x         => x
  | x, .unit         => x
  | .invalid, _      => .invalid
  | _, .invalid      => .invalid
  | .some _, .some _ => .invalid

def Excl.valid {α : Type} : Excl α → Bool
  | .invalid => false
  | _        => true

theorem excl_no_double_acquire {α : Type} (a b : α) :
    Excl.valid (Excl.mul (.some a) (.some b)) = false := rfl

/-- 4-state slot tag eliminating reentrant aliasing (`Live`) and premature reuse (`Vacant`). -/
inductive SlotTag where
  | vacant   (gen : Nat) (nextFree : Option Nat)
  | live     (gen : Nat)
  | draining (gen : Nat)

structure SlotCell where
  tag      : SlotTag
  slotPerm : Excl Nat

def listGetOpt {α : Type} : List α → Nat → Option α
  | [], _        => none
  | x :: _, 0    => some x
  | _ :: xs, n+1 => listGetOpt xs n

def listSetAt {α : Type} : List α → Nat → α → List α
  | [], _, _        => []
  | _ :: xs, 0, v   => v :: xs
  | x :: xs, n+1, v => x :: listSetAt xs n v

structure ArenaSpine where
  slots    : List SlotCell
  freeHead : Option Nat
  liveLen  : Nat

def beginDrain (sp : ArenaSpine) (idx : Nat) : Option (ArenaSpine × Excl Nat) :=
  match listGetOpt sp.slots idx with
  | some ⟨.live g, perm⟩ =>
    let slots' := listSetAt sp.slots idx ⟨.draining g, .unit⟩
    some (⟨slots', sp.freeHead, sp.liveLen - 1⟩, perm)
  | _ => none

def reentrantLookup (sp : ArenaSpine) (idx : Nat) : Option Nat :=
  match listGetOpt sp.slots idx with
  | some ⟨.live g, _⟩ => some g
  | _ => none

def reentrantAlloc (sp : ArenaSpine) : Option (ArenaSpine × Nat × Nat) :=
  match sp.freeHead with
  | none => none
  | some headIdx =>
    match listGetOpt sp.slots headIdx with
    | some ⟨.vacant g nextF, perm⟩ =>
      let slots' := listSetAt sp.slots headIdx ⟨.live g, perm⟩
      some (⟨slots', nextF, sp.liveLen + 1⟩, headIdx, g)
    | _ => none

def finishDrain (sp : ArenaSpine) (idx : Nat) (perm : Excl Nat) : Option ArenaSpine :=
  match listGetOpt sp.slots idx with
  | some ⟨.draining g, .unit⟩ =>
    let slots' := listSetAt sp.slots idx ⟨.vacant (g + 1) sp.freeHead, perm⟩
    some ⟨slots', some idx, sp.liveLen⟩
  | _ => none

def sampleArena : ArenaSpine :=
  ⟨[⟨.live 1, .some 0⟩, ⟨.vacant 1 none, .some 1⟩], some 1, 1⟩

theorem draining_blocks_reentrant_lookup :
    match beginDrain sampleArena 0 with
    | some (sp1, _) => reentrantLookup sp1 0 = none
    | none => False := rfl

theorem draining_blocks_slot_reuse_during_drop :
    match beginDrain sampleArena 0 with
    | some (sp1, _) =>
      match reentrantAlloc sp1 with
      | some (_, allocatedIdx, _) => Nat.beq allocatedIdx 0 = false
      | none => False
    | none => False := rfl

theorem finishDrain_advances_gen_aba_safe :
    match beginDrain sampleArena 0 with
    | some (sp1, perm0) =>
      match finishDrain sp1 0 perm0 with
      | some sp2 =>
        match listGetOpt sp2.slots 0 with
        | some ⟨.vacant g _, .some _⟩ => g = 2
        | _ => False
      | none => False
    | none => False := rfl

end Verification.DropReentrancyArena
```

## Boundaries

`Basis: normative + source + derived`

- **Multi-threaded `Arc::drop` weak-memory ordering (`not examined`):** This analysis covers single-thread and lock-serialized reentrancy (`Rc`, `Cell`, `RefCell`, arenas, `LocalInvariant`, `Grant`); `Arc::drop` `Release`/`Acquire` memory-model fences were `not examined`.
- **Unstable `AsyncDrop` (`#![feature(async_drop)]`, `unknown`):** Interactions between multi-poll async destructors, reentrant executor wakeups, and invariant masks remain `unknown` pending stabilization.
- **Verus `Drop` restrictions (`known not to apply` generally):** Verus's compiler rules requiring `opens_invariants none` and `no_unwind` on `impl Drop` (`well_formed.rs:1747-1767`) are `known not to apply` to general Rust `std` destructors, which may lock or panic.
- **Type-level prevention of `core::mem::forget` (`unsupported`):** Under RFC 1066, forbidding callers from leaking an owned value is `unsupported` in Rust; `FinishDrainGuard` avoids this because it lives on `remove`/`clear`'s active stack frame outside `T::drop`'s ownership.
- **Dynamic Lean 4 execution (`not examined`):** `Verification.DropReentrancyArena` was statically syntax-audited against `TrustedBoundary.lean`; executing `lean` locally was `not examined` in this pass (see Revalidation).

## Evidence

`Basis: source + documentation + execution`

- **`rust-lang/rust` (`4b5350e87e487aed08ab2f9f0160a4b2616438bc`):** `library/core/src/cell.rs:438-443, 515-519, 976-983, 1089-1220, 1397-1413, 2215-2501`; `library/core/src/pin.rs:509-587`; `library/alloc/src/rcs/rc.rs:405-417, 2654-2662, 3715-3729`; `library/alloc/src/vec/mod.rs:1736-1756, 3133-3150`; `library/alloc/src/collections/linked_list.rs:748-758, 1245-1262`.
- **`rust-lang/reference` (`a286e1ecb8ce193d50056e4bb042eea9b23876ef`) & `rust-lang/rfcs` (`f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`):** `src/destructors.md:7-19`; `src/behavior-considered-undefined.md:24-40`; RFCs 1066 and 2349.
- **Arenas & Verifiers:** `tokio-rs/slab@7d1d8ab00a7b8b1978b4bf21d9ae9633ac8c0b05` (`src/lib.rs:615-619, 1030-1036, 1092-1144`); `orlp/slotmap@eccedefc5e09746944678ddcb854d1d709abb444` (`src/basic.rs:506-514, 659-685`); `tock/tock@ba6aa7edc014505d2e6f0123b2b6059ba6ee7dec` (`kernel/src/grant.rs:1248-1318`); `creusot-rs/creusot@601d97891bb0bc0b569686cc946ef4980560b5d8` (`creusot-std/src/{resolve.rs,invariant.rs,cell/pcell.rs}`); `verus-lang/verus@0dab219272ac2353320bd177ebb3929453b90a9e` (`source/vstd/invariant.rs`, `source/vir/src/{inv_masks.rs,well_formed.rs:1747-1767}`); `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a` (`Miri/TreeBorrows/RetagPolicy.lean`, `Miri/Interpreter/TypedRetag.lean`); `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`trusted/audit/TrustedBoundary.lean:487-595`, `theory/Anneal/PureLift/PermTree.lean`).
- **Literature:** Jung et al. (`10.1145/3158154`), Gaher et al. (`10.1145/3656422`), Denis et al. (`10.1007/978-3-031-17244-1_6`), Lattuada et al. (`10.1145/3586037`), Bae et al. (`10.1145/3477132.3483570`).
- **Probe Execution (`2026-11-20`, Python 3, Linux `x86_64`, `Basis: execution`):** Ran the §Revalidation probe (`exit 0`), observing `drop_then_free: 3/6 failing`, `free_then_drop: 2/6 failing`, `slab_clear_post_reset: 5/6 failing`, and `four_state_slot_tag_guard: 0/6 failing` (`DROP_REENTRANCY_PROBE_OK`).

## Revalidation

`Basis: execution + derived`

1. **Source Diff Checks:** Diff `core/src/cell.rs`, `alloc/src/vec/mod.rs`, `tokio-rs/slab/src/lib.rs`, `creusot-std/src/cell/pcell.rs`, and `verus/source/vir/src/well_formed.rs` across newer upstream revisions.
2. **Deterministic Reentrancy & Unwind Probe (Python 3.10+ stdlib only, `< 0.1s`):**

```python
#!/usr/bin/env python3
from __future__ import annotations
from dataclasses import dataclass

@dataclass(frozen=True)
class TraceOutcome:
    protocol: str
    scenario: str
    aliasing_ub: bool
    double_drop: bool
    pin_violated: bool
    post_catch_corruption: bool

def simulate(protocol: str, scenario: str) -> TraceOutcome:
    slots = [
        {"tag": "live", "gen": 1, "active_mut": False},
        {"tag": "live", "gen": 1, "active_mut": False},
    ]
    freelist: int | None = None
    live_len, entries_len = 2, 2
    aliasing_ub = double_drop = pin_violated = post_catch_corruption = False
    drop_counts = [0, 0]

    def alloc_slot() -> int | None:
        nonlocal freelist, live_len, aliasing_ub, pin_violated, post_catch_corruption
        if protocol == "slab_clear_post_reset" and freelist is not None and freelist >= entries_len:
            post_catch_corruption = True
            return None
        if freelist is None:
            return None
        idx = freelist
        if slots[idx]["active_mut"]:
            aliasing_ub = pin_violated = True
        freelist = None
        slots[idx]["tag"] = "live"
        live_len += 1
        return idx

    def try_get_slot(idx: int) -> bool:
        nonlocal aliasing_ub
        if slots[idx]["tag"] == "live":
            if slots[idx]["active_mut"]:
                aliasing_ub = True
            return True
        return False

    def drop_slot(idx: int) -> None:
        nonlocal double_drop
        drop_counts[idx] += 1
        if drop_counts[idx] > 1:
            double_drop = True
        slots[idx]["active_mut"] = True
        try:
            if scenario == "reentrant_get_same":
                try_get_slot(idx)
            elif scenario == "reentrant_remove_same":
                if slots[idx]["tag"] == "live":
                    drop_slot(idx)
            elif scenario in ("reentrant_insert", "reentrant_insert_other"):
                alloc_slot()
            elif scenario == "panic_unwind":
                raise RuntimeError("destructor panic")
        finally:
            slots[idx]["active_mut"] = False

    if scenario == "reentrant_insert_other":
        slots[1]["tag"] = "vacant"
        freelist = 1
        live_len = 1

    try:
        if protocol == "drop_then_free":
            drop_slot(0)
            slots[0]["tag"] = "vacant"
            freelist = 0
            live_len -= 1
        elif protocol == "free_then_drop":
            slots[0]["tag"] = "vacant"
            freelist = 0
            live_len -= 1
            drop_slot(0)
        elif protocol == "slab_clear_post_reset":
            freelist, entries_len = 1, 0
            if scenario in ("reentrant_get_same", "reentrant_remove_same", "reentrant_insert"):
                raise RuntimeError("RefCell already mutably borrowed")
            drop_slot(0)
            live_len, freelist = 0, None
        elif protocol == "four_state_slot_tag_guard":
            assert slots[0]["tag"] == "live"
            slots[0]["tag"] = "draining"
            live_len -= 1
            try:
                drop_slot(0)
            finally:
                slots[0]["gen"] += 1
                slots[0]["tag"] = "vacant"
                if freelist is None:
                    freelist = 0
    except RuntimeError:
        if protocol == "drop_then_free" and slots[0]["tag"] == "live":
            drop_counts[0] += 1
            if drop_counts[0] > 1:
                double_drop = True
        elif protocol == "slab_clear_post_reset":
            alloc_slot()
        elif protocol == "four_state_slot_tag_guard":
            assert slots[0]["tag"] == "vacant" and slots[0]["gen"] == 2
            alloc_slot()

    return TraceOutcome(protocol, scenario, aliasing_ub, double_drop, pin_violated, post_catch_corruption)

if __name__ == "__main__":
    scenarios = ["noop", "reentrant_get_same", "reentrant_remove_same", "reentrant_insert", "reentrant_insert_other", "panic_unwind"]
    protocols = ["drop_then_free", "free_then_drop", "slab_clear_post_reset", "four_state_slot_tag_guard"]
    summary = {}
    for proto in protocols:
        fails = [r for s in scenarios for r in [simulate(proto, s)] if r.aliasing_ub or r.double_drop or r.pin_violated or r.post_catch_corruption]
        summary[proto] = fails
        print(f"{proto}: {len(fails)}/{len(scenarios)} failing -> {[(f.scenario, f.aliasing_ub, f.double_drop, f.pin_violated, f.post_catch_corruption) for f in fails]}")
    assert len(summary["drop_then_free"]) == 3
    assert len(summary["free_then_drop"]) == 2
    assert len(summary["slab_clear_post_reset"]) == 5
    assert len(summary["four_state_slot_tag_guard"]) == 0
    print("DROP_REENTRANCY_PROBE_OK")
```

3. **Lean `v4.34.1` Replay:** Extract `Verification.DropReentrancyArena` to `/tmp/DropReentrancyArena.lean` and run `lean /tmp/DropReentrancyArena.lean` (`5045d0056413`); confirm exit `0`, zero `sorry`, and clean `#print axioms`.
