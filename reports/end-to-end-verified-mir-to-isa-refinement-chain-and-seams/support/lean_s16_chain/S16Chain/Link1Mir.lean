-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

namespace S16Chain

/-!
# Link 1: Anneal `Runtime(PostCleanup)` MIR Semantics & Verified Contracts

Models the exact `Runtime(PostCleanup)` MIR bodies and weakest-precondition
contracts (`wpMir`) for the two Anneal-verified fixtures:
1. `add_bounded(x: usize, y: usize) -> usize` (from
   `theory/Anneal/FunctionalTranslation.lean` @ `a7ac07321`):
   6 basic blocks with `Le(x, 1000)`, `Le(y, 1000)`, `AddWithOverflow(x, y)`,
   and `assert(!move (_5.1: bool))`.
2. `alloc_passthrough(x: usize) -> usize` (from `tests/fixtures/refs.rs` @
   `b1f15f743`):
   Stack-allocated local reference `r = &x; *r`.
-/

/-- Mathematical `usize` bound on 64-bit targets (`2^64 - 1`). -/
def usizeMax : Nat := 18446744073709551615

/-- Abstract MIR outcome distinguishing normal termination, panic (assertion
failure), and undefined behavior (`ub`). -/
inductive MirOutcome (α : Type) where
  | returned (v : α)
  | panic
  | ub
  deriving DecidableEq, Repr

/-- Abstract MIR state over mathematical `Nat` locals (`_0.._5`) and abstract
allocation slots (`AllocId → Option Nat`). -/
structure MirState where
  locals : Nat → Option Nat
  allocs : Nat → Option Nat

/-- High-level functional specification for `add_bounded`. -/
def HighLevelAddBoundedSpec (x y : Nat) : Nat :=
  if x ≤ 1000 ∧ y ≤ 1000 then x + y else 0

/-- Operational evaluation of the 6-block `addBoundedBody` MIR CFG:
  - `bb0`: `_3 = (x ≤ 1000); switchInt(_3) -> [false: bb4, true: bb1]`
  - `bb1`: `_4 = (y ≤ 1000); switchInt(_4) -> [false: bb4, true: bb2]`
  - `bb2`: `_5 = AddWithOverflow(x, y); assert(!_5.1) -> [ok: bb3, fail: panic]`
  - `bb3`: `_0 = _5.0; goto bb5`
  - `bb4`: `_0 = 0; goto bb5`
  - `bb5`: `return _0` -/
def evalMirAddBounded (st : MirState) : MirOutcome Nat :=
  match st.locals 1, st.locals 2 with
  | some x, some y =>
    if x ≤ 1000 then
      if y ≤ 1000 then
        if x + y ≤ usizeMax then
          .returned (x + y)
        else
          .panic
      else
        .returned 0
    else
      .returned 0
  | _, _ => .ub

/-- Anneal weakest-precondition contract (`wpMir`) for `add_bounded`:
for any initial `MirState` where `_1 = some x` and `_2 = some y`, `add_bounded`
never panics or triggers UB, and returns `HighLevelAddBoundedSpec x y`. -/
theorem link1_anneal_mir_add_bounded_verified
    (st : MirState) (x y : Nat)
    (hx : st.locals 1 = some x) (hy : st.locals 2 = some y) :
    evalMirAddBounded st = .returned (HighLevelAddBoundedSpec x y) := by
  unfold evalMirAddBounded HighLevelAddBoundedSpec usizeMax
  rw [hx, hy]
  by_cases h1 : x ≤ 1000
  · by_cases h2 : y ≤ 1000
    · have h_no_ovf : x + y ≤ 18446744073709551615 := by omega
      simp [h1, h2, h_no_ovf]
    · simp [h1, h2]
  · simp [h1]

/-- Operational evaluation of `alloc_passthrough(x: usize) -> usize`:
allocates slot `0` with value `x`, forms reference `&slot[0]`, and dereferences
it into `_0`. -/
def evalMirAllocPassthrough (st : MirState) : MirOutcome Nat :=
  match st.locals 1 with
  | some x =>
    let st1 : MirState := { st with allocs := fun a => if a = 0 then some x else st.allocs a }
    match st1.allocs 0 with
    | some v => .returned v
    | none => .ub
  | none => .ub

theorem link1_anneal_mir_alloc_passthrough_verified
    (st : MirState) (x : Nat) (hx : st.locals 1 = some x) :
    evalMirAllocPassthrough st = .returned x := by
  simp [evalMirAllocPassthrough, hx]

end S16Chain
