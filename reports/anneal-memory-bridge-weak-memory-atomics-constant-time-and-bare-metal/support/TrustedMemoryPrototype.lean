-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Trusted.Refinement
import Trusted.MirAst

/-!
# Trusted Weak-Memory Views and Memory State (`Trusted/Memory.lean`)

This module defines the operational memory state for `Trusted.MirSemantics`,
combining:
1. A timestamp/view-based weak-memory model for C++20 / Rust atomic accesses
   (`Timestamp`, `View`, `instPreorderView`, `AtomicMsg`, `visibleAtomicMsgs`,
   `applyAtomicLoad`), where thread views form a partial order (`Preorder View`)
   and atomic loads make demonic choices over visible messages in the
   per-location modification order.
2. Deterministic non-atomic memory accesses (`readNA`, `writeNA`) gated by
   happens-before view checks so unsynchronized conflicting accesses trigger
   Undefined Behavior (data race).

Every declaration that models a Rust memory-model rule cites the normative Rust
Reference or `core::sync::atomic` documentation at the repository's pinned
revisions (`rust-lang/reference@82da570bafd9efed421bdbae0f8603ede8dd308b` and
`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`).

This module belongs to `trusted/lean/` and contains only definitions,
structures,
and instances (zero theorems). All view-lattice lemmas, single-threaded/lock
ownership helpers (`OwnLoc`), and atomic verification lemmas live in `theory/`.
-/

namespace Trusted

/-- Modification-order timestamp for a memory location.

    In C++20 / Rust operational timestamp semantics, each memory location has a
    totally ordered modification order indexed by `Timestamp`:

    > "Rust atomics currently follow the same rules as [C++20 atomics][cpp],
    > specifically the rules from the [`intro.races`][cpp-intro.races] section,
    > without the "consume" memory ordering."

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/sync/atomic.rs#L27-L28 -/
@[candidate memory]
abbrev Timestamp := Nat

/-- Thread or message coherence view mapping each memory location identifier to
    the latest modification-order timestamp observed at that location.

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/sync/atomic.rs#L56-L58 -/
@[candidate memory]
abbrev View := Nat → Timestamp

/-- Pointwise partial order (`v₁ ≤ v₂`) on coherence views: `v₁` is at or
    behind `v₂` when every location's timestamp in `v₁` is `≤` its timestamp in
    `v₂`. -/
@[candidate memory]
instance instPreorderView : Preorder View where
  le v₁ v₂ := ∀ loc, v₁ loc ≤ v₂ loc
  le_refl _ _ := Nat.le_refl _
  le_trans h₁ h₂ loc := Nat.le_trans (h₁ loc) (h₂ loc)

/-- Initial bottom view assigning timestamp `0` to every location. -/
@[candidate memory]
def View.bot : View :=
  fun _ => 0

/-- Advance view `v` at location `loc` to at least timestamp `ts`. -/
@[candidate memory]
def View.bump (v : View) (loc : Nat) (ts : Timestamp) : View :=
  fun l => if l == loc then max (v l) ts else v l

/-- Pointwise join (least upper bound) of two coherence views `v₁` and `v₂`.

    Used when an `Acquire` load synchronizes with a prior `Release` store and
    incorporates the message's release view into the reading thread's view:

    > "When coupled with a load, if the loaded value was written by a store
    > operation with [`Release`] (or stronger) ordering, then all subsequent
    > operations become ordered after that store. In particular, all subsequent
    > loads will see data written before the store."

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/sync/atomic.rs#L489-L492 -/
@[candidate memory]
def View.join (v₁ v₂ : View) : View :=
  fun loc => max (v₁ loc) (v₂ loc)

/-- A store event in the modification order of an atomic `usize` location,
    recording the target location `loc`, its modification-order timestamp `ts`,
    the stored `usize` payload `bits`, and the release view `relView` attached
    to the store.

    Corresponds to a modification of an atomic object in `core::sync::atomic`:

    > "When the C++ standard talks about "the value of an atomic object", this
    > refers to the result of doing an atomic load (via the operations provided
    > in this module). A "modification of an atomic object" refers to an atomic
    > store."

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/sync/atomic.rs#L31-L34 -/
@[candidate memory]
structure AtomicMsg where
  loc : Nat
  ts : Timestamp
  bits : Nat
  relView : View

/-- Operational memory state combining the active thread's coherence view
    (`curView`), the modification-order history of atomic locations
    (`atomicMsgs`), and the deterministic non-atomic memory store (`naVal`,
    `naWriteTs`, `naReadTs`).

    Separating non-atomic locations from the atomic message history reflects
    Rust's data-race rule (`r[undefined.race]`): non-atomic accesses cannot race
    without triggering immediate UB, whereas atomic accesses choose
    nondeterministically among modification-order messages consistent with
    `curView`:

    > "The most important aspect of this model is that *data races* are
    > undefined behavior. A data race is defined as conflicting
    > non-synchronized accesses where at least one of the accesses is
    > non-atomic. Here, accesses are *conflicting* if they affect overlapping
    > regions of memory and at least one of them is a write."

    Sources:
    - https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/behavior-considered-undefined.md#L15-L16
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/sync/atomic.rs#L44-L49 -/
@[candidate memory]
structure MemState where
  curView : View
  atomicMsgs : List AtomicMsg
  naVal : Nat → Option MirVal
  naWriteTs : Nat → Timestamp
  naReadTs : Nat → Timestamp

/-- Empty initial memory state with bottom views and no allocated locations. -/
@[candidate memory]
def MemState.empty : MemState where
  curView := View.bot
  atomicMsgs := []
  naVal := fun _ => none
  naWriteTs := fun _ => 0
  naReadTs := fun _ => 0

/-- Deterministic non-atomic read at `loc`.

    Returns `some (v, m')` if `loc` holds an initialized value `v` and its last
    non-atomic write timestamp `m.naWriteTs loc` is visible in `m.curView loc`
    (no unsynchronized concurrent write); returns `none` on uninitialized access
    or data race (`r[undefined.race]`, `r[undefined.invalid]`).

    Sources:
    - https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/behavior-considered-undefined.md#L15-L16
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/sync/atomic.rs#L44-L49 -/
@[candidate memory]
def MemState.readNA (m : MemState) (loc : Nat) : Option (MirVal × MemState) :=
  if decide (m.naWriteTs loc ≤ m.curView loc) then
    match m.naVal loc with
    | some v =>
      some (v, { m with
        naReadTs := View.bump m.naReadTs loc (m.curView loc) })
    | none => none
  else
    none

/-- Deterministic non-atomic write of `v` at `loc`.

    Returns `some m'` if both the last write (`m.naWriteTs loc`) and last read
    (`m.naReadTs loc`) at `loc` are visible in `m.curView loc` (no
    unsynchronized conflicting access); returns `none` on a data race
    (`r[undefined.race]`).

    Sources:
    - https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/behavior-considered-undefined.md#L15-L16
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/sync/atomic.rs#L44-L49 -/
@[candidate memory]
def MemState.writeNA (m : MemState) (loc : Nat) (v : MirVal) : Option MemState :=
  if decide (m.naWriteTs loc ≤ m.curView loc) && decide (m.naReadTs loc ≤ m.curView loc) then
    let nextTs := m.curView loc + 1
    some { m with
      curView := View.bump m.curView loc nextTs
      naVal := fun l => if l == loc then some v else m.naVal l
      naWriteTs := View.bump m.naWriteTs loc nextTs
      naReadTs := View.bump m.naReadTs loc nextTs }
  else
    none

/-- Modification-order messages at atomic location `loc` that are visible to the
    active thread under read-read / write-read coherence (`m.curView loc ≤
    msg.ts`).

    In C++20 / Rust relaxed and acquire loads, a thread cannot observe a
    modification-order message older than the timestamp already recorded in its
    coherence view for `loc`:

    > "In its weakest [`Ordering::Relaxed`], only the memory directly touched
    > by the operation is synchronized."

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/sync/atomic.rs#L451-L452 -/
@[candidate memory]
def MemState.visibleAtomicMsgs (m : MemState) (loc : Nat) : List AtomicMsg :=
  m.atomicMsgs.filter fun msg =>
    msg.loc == loc && decide (m.curView loc ≤ msg.ts)

/-- Update `MemState` after an atomic load with ordering `ord` observes message
    `msg`:
    - `AtomicOrdering.relaxed`: bumps `curView` at `msg.loc` to `msg.ts`.
    - `AtomicOrdering.acquire`: bumps `curView` at `msg.loc` to `msg.ts` and
      joins `curView` with `msg.relView`.

    Sources:
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/sync/atomic.rs#L466-L503
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/sync/atomic.rs#L3990-L4001 -/
@[candidate memory]
def MemState.applyAtomicLoad (m : MemState) (ord : AtomicOrdering) (msg : AtomicMsg) : MemState :=
  let bumped := View.bump m.curView msg.loc msg.ts
  match ord with
  | .relaxed => { m with curView := bumped }
  | .acquire => { m with curView := View.join bumped msg.relView }

end Trusted
