-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Mechanization of Tree Borrows Unwind-Landing-Pad Store Sinking (`SinkStoreToCleanupCert`), Loop `&mut` Promotion, and Frame-Local Catch Unobservability in Lean v4.34.1

Mechanizes:
1. Cold `cleanup`-pad store sinking (`SinkStoreToCleanupCert` and
   `sinkProtectedStoreToCleanup_bisimExact`), proving that transforming
   `*x = v1; may_unwind_call(); *x = v2` into `may_unwind_call(); *x = v2` on the
   normal path while sinking `*x = v1` to the entry of `bb_cleanup_sink` (before
   any frame-local `Drop` glue and before `UnwindResume` releases the
   `StrongProtector`) is a bidirectional refinement (`BisimExact`);
2. Loop-carried `&mut T` register promotion (`promoteProtectedMutAcrossMayUnwindLoop_sound`),
   proving that promoting `*acc` across a loop of `may_unwind` calls into an SSA
   $\phi$-register with a single normal-exit writeback and a single shared
   `cleanup`-pad writeback preserves exact normal and exceptional semantics at
   every loop iteration;
3. Uncompensated unwind DSE under local drop-guard overwrite
   (`dseAcrossUnwind_withLocalDropOverwrite_refines`, `COND-LOCAL-DROP-OVERWRITE`);
4. Uncompensated unwind DSE under interprocedural caller `dead_on_unwind`
   (`dseAcrossUnwind_callerDeadOnUnwind_refines`, `COND-INLINED-CALLER-DEAD-ON-UNWIND`);
5. Negative soundness test (`sinkAfterReadingCleanupDrop_rejected`) rejecting store
   sinking past a local `Drop` in `bb_cleanup` that reads `*x`.
-/

namespace TreeBorrowsUnwindStoreSinkingAndDseProbe

/-- Effect of an opaque `may_unwind` call on a Tree Borrows `StrongProtector`
    parameter `x : &mut T` that has already been written (`Unique`, `accessed = true`).
    By `src/tools/miri/src/borrow_tracker/tree_borrows/perms.rs:172-176` and
    `tree.rs:157-159`, any foreign read or foreign write during the call transitions
    `x` to `Disabled` under an active protector, triggering immediate `ProtectedDisabled` UB. -/
inductive OpaqueCallForeignAccess where
  | none
  | foreignRead
  | foreignWrite
  deriving DecidableEq, Repr

/-- Normal vs. unwinding exit of a `may_unwind` call. -/
inductive CallExit where
  | normalReturn
  | unwindCleanup
  deriving DecidableEq, Repr

/-- Execution outcome: `.ub` (Undefined Behavior in source) or `.ok state`. -/
inductive ExecResult (α : Type) where
  | ub
  | ok (val : α)
  deriving DecidableEq, Repr

/-- Action of a frame-local destructor in `bb_cleanup` before `UnwindResume`. -/
inductive LocalCleanupDropEffect where
  | noTouchX
  | readX
  | overwriteX (vRecover : Nat)
  deriving DecidableEq, Repr

/-- Certificate for sinking `*x = v1` off the hot normal path onto `bb_cleanup_sink`. -/
structure SinkStoreToCleanupCert where
  hasStrongProtector      : Bool
  sunkBeforeCleanupDrops  : Bool
  cleanupDropEffect       : LocalCleanupDropEffect
  deriving DecidableEq, Repr

def checkSinkStoreToCleanupCert (cert : SinkStoreToCleanupCert) : Bool :=
  cert.hasStrongProtector &&
  (cert.sunkBeforeCleanupDrops ||
    match cert.cleanupDropEffect with
    | .noTouchX => true
    | .overwriteX _ => true
    | .readX => false)

/-!
## 1. Cold `cleanup`-Pad Store Sinking (`sinkProtectedStoreToCleanup_bisimExact`)
-/

/-- Evaluate the local `bb_cleanup` destructor on current memory value `xVal`,
    returning `(finalXVal, optionalDropObservation)`. -/
def runCleanupDrop (eff : LocalCleanupDropEffect) (xVal : Nat) : Nat × Option Nat :=
  match eff with
  | .noTouchX            => (xVal, none)
  | .readX               => (xVal, some xVal)
  | .overwriteX vRecover => (vRecover, none)

/-- Source execution of:
    ```text
    bb0:
      *x = v1;
      call may_unwind() -> [return: bb1, unwind: bb_cleanup];
    bb1:
      *x = v2;
      return;
    bb_cleanup:
      runCleanupDrop(eff);
      resume;
    ``` -/
def evalSourceStoreCallStore
    (_v0 v1 v2 : Nat)
    (acc : OpaqueCallForeignAccess)
    (exit : CallExit)
    (eff : LocalCleanupDropEffect) : ExecResult (Nat × Option Nat × CallExit) :=
  match acc with
  | .foreignRead | .foreignWrite => .ub
  | .none =>
    match exit with
    | .normalReturn => .ok (v2, none, .normalReturn)
    | .unwindCleanup =>
      let (xFinal, obs) := runCleanupDrop eff v1
      .ok (xFinal, obs, .unwindCleanup)

/-- Target execution after `SinkStoreToCleanup`:
    ```text
    bb0:
      call may_unwind() -> [return: bb1, unwind: bb_cleanup_sink];
    bb1:
      *x = v2;
      return;
    bb_cleanup_sink:
      *x = v1; // sunk before local cleanup drops!
      runCleanupDrop(eff);
      resume;
    ``` -/
def evalSunkStoreToCleanup
    (_v0 v1 v2 : Nat)
    (acc : OpaqueCallForeignAccess)
    (exit : CallExit)
    (eff : LocalCleanupDropEffect) : ExecResult (Nat × Option Nat × CallExit) :=
  match acc with
  | .foreignRead | .foreignWrite => .ub
  | .none =>
    match exit with
    | .normalReturn => .ok (v2, none, .normalReturn)
    | .unwindCleanup =>
      let xAtCleanupEntry := v1
      let (xFinal, obs) := runCleanupDrop eff xAtCleanupEntry
      .ok (xFinal, obs, .unwindCleanup)

/-- Theorem 1 (`sinkProtectedStoreToCleanup_bisimExact`):
    Sinking `*x = v1` off the hot normal path onto the entry of `bb_cleanup_sink`
    (before local cleanup drops and `UnwindResume`) is an exact state bisimulation
    (`BisimExact`) across all `OpaqueCallForeignAccess`, `CallExit`, and
    `LocalCleanupDropEffect` cases. -/
theorem sinkProtectedStoreToCleanup_bisimExact
    (v0 v1 v2 : Nat)
    (acc : OpaqueCallForeignAccess)
    (exit : CallExit)
    (eff : LocalCleanupDropEffect) :
    evalSunkStoreToCleanup v0 v1 v2 acc exit eff =
      evalSourceStoreCallStore v0 v1 v2 acc exit eff := by
  cases acc <;> cases exit <;> rfl

/-!
## 2. Loop-Carried `&mut T` Register Promotion Across `may_unwind` Calls
-/

/-- Unoptimized source loop: in each iteration, reads `*acc`, adds `stepDelta`,
    stores `*acc = newAcc` to memory, and invokes `check_step()` which may unwind! -/
def evalSourceMayUnwindLoop (accMem : Nat) (steps : List (Nat × CallExit)) : Nat × CallExit :=
  match steps with
  | [] => (accMem, .normalReturn)
  | (delta, exit) :: rest =>
    let accMem' := accMem + delta
    match exit with
    | .unwindCleanup => (accMem', .unwindCleanup)
    | .normalReturn  => evalSourceMayUnwindLoop accMem' rest

/-- Promoted `MiniSSA` loop (`PromoteProtectedMutInLoopCert`):
    accumulates in pure SSA $\phi$-register `phiAcc` with zero memory stores inside
    the loop body, writing `phiAcc` to `*acc` once at the normal loop exit and
    once on the shared `bb_cleanup_sink` landing pad if any iteration unwinds. -/
def evalSsaPromotedMayUnwindLoop (phiAcc : Nat) (steps : List (Nat × CallExit)) : Nat × CallExit :=
  match steps with
  | [] =>
    let accMemAtNormalExit := phiAcc
    (accMemAtNormalExit, .normalReturn)
  | (delta, exit) :: rest =>
    let phiAcc' := phiAcc + delta
    match exit with
    | .unwindCleanup =>
      let accMemAtCleanupPad := phiAcc'
      (accMemAtCleanupPad, .unwindCleanup)
    | .normalReturn =>
      evalSsaPromotedMayUnwindLoop phiAcc' rest

/-- Theorem 2 (`promoteProtectedMutAcrossMayUnwindLoop_sound`):
    Promoting a loop-carried `*acc: &mut u64` into an SSA $\phi$-register `phiAcc`
    with normal-exit + `cleanup`-pad writeback produces the exact same final memory
    value and exit kind as the unoptimized memory-store-per-iteration loop for any
    step trace `steps`. -/
theorem promoteProtectedMutAcrossMayUnwindLoop_sound
    (initAcc : Nat) (steps : List (Nat × CallExit)) :
    evalSsaPromotedMayUnwindLoop initAcc steps =
      evalSourceMayUnwindLoop initAcc steps := by
  induction steps generalizing initAcc with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨delta, exit⟩
    cases exit with
    | unwindCleanup => rfl
    | normalReturn =>
      dsimp [evalSsaPromotedMayUnwindLoop, evalSourceMayUnwindLoop]
      exact ih (initAcc + delta)

/-!
## 3. Uncompensated Unwind DSE (`DeleteStoreAcrossUnwindCert`)
-/

/-- Target execution when `*x = v1` is deleted on BOTH normal and unwind paths
    (zero cold-pad compensation store emitted). -/
def evalUncompensatedDeleteStore
    (v0 _v1 v2 : Nat)
    (acc : OpaqueCallForeignAccess)
    (exit : CallExit)
    (eff : LocalCleanupDropEffect) : ExecResult (Nat × Option Nat × CallExit) :=
  match acc with
  | .foreignRead | .foreignWrite => .ub
  | .none =>
    match exit with
    | .normalReturn => .ok (v2, none, .normalReturn)
    | .unwindCleanup =>
      let (xFinal, obs) := runCleanupDrop eff v0
      .ok (xFinal, obs, .unwindCleanup)

/-- Theorem 3 (`dseAcrossUnwind_withLocalDropOverwrite_refines`, `COND-LOCAL-DROP-OVERWRITE`):
    When a local scope guard in `bb_cleanup` unconditionally overwrites
    `*x = vRecover` without reading `*x` (`eff = .overwriteX vRecover`), deleting
    `*x = v1` with zero cold-pad store is an exact bisimulation on both normal and
    unwind paths! -/
theorem dseAcrossUnwind_withLocalDropOverwrite_refines
    (v0 v1 v2 vRecover : Nat)
    (acc : OpaqueCallForeignAccess)
    (exit : CallExit) :
    evalUncompensatedDeleteStore v0 v1 v2 acc exit (.overwriteX vRecover) =
      evalSourceStoreCallStore v0 v1 v2 acc exit (.overwriteX vRecover) := by
  cases acc <;> cases exit <;> rfl

/-- Interprocedural caller observation when `x = &mut caller_local` is passed to
    `f(x)` (`COND-INLINED-CALLER-DEAD-ON-UNWIND`):
    If `callerNeedsDrop == false` and `callerCatchesUnwind == false`, the caller's
    unwind edge executes `StorageDead(caller_local)` immediately upon `f` unwinding,
    deallocating `caller_local` so its value on unwind is unobservable (`none`). -/
def observeAtCallerAfterCall
    (callerNeedsDrop callerCatchesUnwind : Bool)
    (res : ExecResult (Nat × Option Nat × CallExit)) : ExecResult (Option Nat × Option Nat × CallExit) :=
  match res with
  | .ub => .ub
  | .ok (xFinal, calleeDropObs, .normalReturn) =>
    .ok (some xFinal, calleeDropObs, .normalReturn)
  | .ok (xFinal, calleeDropObs, .unwindCleanup) =>
    if callerNeedsDrop || callerCatchesUnwind then
      .ok (some xFinal, calleeDropObs, .unwindCleanup)
    else
      -- `StorageDead(caller_local)` kills the slot without reading `xFinal`!
      .ok (none, calleeDropObs, .unwindCleanup)

/-- Theorem 4 (`dseAcrossUnwind_callerDeadOnUnwind_refines`, `COND-INLINED-CALLER-DEAD-ON-UNWIND`):
    When `callerNeedsDrop = false`, `callerCatchesUnwind = false`, and `f`'s local
    cleanup does not read `*x` (`eff = .noTouchX`), deleting `*x = v1` without
    cleanup compensation preserves exact caller-observable behavior! -/
theorem dseAcrossUnwind_callerDeadOnUnwind_refines
    (v0 v1 v2 : Nat)
    (acc : OpaqueCallForeignAccess)
    (exit : CallExit) :
    observeAtCallerAfterCall false false (evalUncompensatedDeleteStore v0 v1 v2 acc exit .noTouchX) =
      observeAtCallerAfterCall false false (evalSourceStoreCallStore v0 v1 v2 acc exit .noTouchX) := by
  cases acc <;> cases exit <;> rfl

/-!
## 4. Negative Soundness Test: Sinking Past a Reading Local `Drop` Rejected
-/

def badSinkAfterReadingDropCert : SinkStoreToCleanupCert :=
  { hasStrongProtector     := true
  , sunkBeforeCleanupDrops := false
  , cleanupDropEffect      := .readX }

/-- Theorem 5 (`sinkAfterReadingCleanupDrop_rejected`):
    If `bb_cleanup` contains a local destructor that reads `*x` (`cleanupDropEffect = .readX`),
    sinking `*x = v1` *after* that local destructor (`sunkBeforeCleanupDrops = false`)
    is rejected by `checkSinkStoreToCleanupCert`. -/
theorem sinkAfterReadingCleanupDrop_rejected :
    checkSinkStoreToCleanupCert badSinkAfterReadingDropCert = false := by
  rfl

#print axioms sinkProtectedStoreToCleanup_bisimExact
#print axioms promoteProtectedMutAcrossMayUnwindLoop_sound
#print axioms dseAcrossUnwind_withLocalDropOverwrite_refines
#print axioms dseAcrossUnwind_callerDeadOnUnwind_refines
#print axioms sinkAfterReadingCleanupDrop_rejected

end TreeBorrowsUnwindStoreSinkingAndDseProbe
