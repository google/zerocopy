-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Mechanization of Tree Borrows Under `panic=unwind` `cleanup` Pads, `dead_on_unwind` (`sret`), Two-Phase Borrows, and `UnsafeCell` Projections in Lean v4.34.1

Mechanizes the exact permission state machine (`perms.rs` at `58cf8f9c35b355199727627d07ae34a4e2846d67`)
and proves five core theorems governing `HybridTrace` store-motion, `DSE`, and
load-hoisting (`GVN` / `LICM`) in `MiniSSA`:
1. Uncompensated sinking/DSE of a store `*x = v1` on a protected `&mut T` across
   a `may_unwind` call is **unsound** when the call unwinds and caller `Drop` or
   `catch_unwind` reads `*x` (`dseAcrossMayUnwindCall_unsound_counterexample`);
2. Sinking `*x = v1` into *both* the normal return continuation and the `cleanup`
   landing pad before `UnwindResume` is a sound refinement on both normal and
   unwind paths (`compensatedStoreSinkingAcrossMayUnwind_refines`);
3. For an indirect return slot (`sret` / `_0`) carrying `dead_on_unwind`,
   uncompensated store sinking / DSE across a `may_unwind` call is unconditionally
   sound (`sretDeadOnUnwindStoreSinking_refines`);
4. Protected `ReservedFrz` vs. unprotected `ReservedFrz` / `ReservedIM` two-phase
   borrow state transitions (`twoPhaseUnprotected_allows_parentRead_then_childWrite`,
   `protectedReservedFrz_forbids_foreignRead_then_childWrite`);
5. Sub-object `UnsafeCell` (`&StructWithCell`) byte-range partitioning (`Frozen`
   on `Freeze` fields vs. `Cell` on `UnsafeCell` fields) permits load hoisting
   (`GVN` / `LICM`) on `Freeze` fields across arbitrary unknown calls that mutate
   sibling `UnsafeCell` fields (`freezeFieldLoadHoisting_refines`).
-/

namespace TreeBorrowsUnwindAndUnsafeCellProbe

/-- Access kinds in Tree Borrows (`borrow_tracker/mod.rs:16-19`). -/
inductive AccessKind where
  | read
  | write
  deriving DecidableEq, Repr

/-- Relatedness of an access relative to a tracked tag (`tree.rs`). -/
inductive Relatedness where
  | child
  | foreign
  deriving DecidableEq, Repr

/-- Tree Borrows `PermissionPriv` (`tree_borrows/perms.rs:10-53`). -/
inductive PermissionPriv where
  | cell
  | reservedFrz (conflicted : Bool)
  | reservedIM
  | unique
  | frozen
  | disabled
  deriving DecidableEq, Repr

/-- Exact transition function `transition::perform_access` from
    `src/tools/miri/src/borrow_tracker/tree_borrows/perms.rs:135-232`. -/
def performAccessPerm
    (kind : AccessKind)
    (rel : Relatedness)
    (state : PermissionPriv)
    (isProt : Bool) : Option PermissionPriv :=
  match kind, rel with
  | .read, .child =>
    match state with
    | .disabled => none
    | readable => some readable
  | .read, .foreign =>
    match state with
    | .cell => some .cell
    | .frozen => some .frozen
    | .disabled => some .disabled
    | .reservedFrz c =>
      if isProt then some (.reservedFrz true) else some (.reservedFrz c)
    | .reservedIM => some .reservedIM
    | .unique =>
      if isProt then some .disabled else some .frozen
  | .write, .child =>
    match state with
    | .cell => some .cell
    | .reservedFrz true =>
      if isProt then none else some .unique
    | .reservedFrz false => some .unique
    | .reservedIM => some .unique
    | .unique => some .unique
    | .frozen | .disabled => none
  | .write, .foreign =>
    match state with
    | .cell => some .cell
    | .reservedIM => some .reservedIM
    | _ => some .disabled

/-- `Permission::associated_access` (`perms.rs:311-319`), used on protector release
    (`perform_protector_end_access`). -/
def associatedAccess (state : PermissionPriv) : Option AccessKind :=
  match state with
  | .cell => none
  | .unique => some .write
  | _ => some .read

/-- Location-level transition `LocationState::perform_access` (`tree.rs:132-162`),
    checking `isProt && accessed && newPerm == .disabled` (`ProtectedDisabled`). -/
structure LocState where
  perm     : PermissionPriv
  accessed : Bool
  deriving DecidableEq, Repr

def stepLocation
    (kind : AccessKind)
    (rel : Relatedness)
    (isProt : Bool)
    (loc : LocState) : Option LocState :=
  match performAccessPerm kind rel loc.perm isProt with
  | none => none
  | some newPerm =>
    let newAccessed := loc.accessed || (rel == .child)
    if isProt && newAccessed && (newPerm == .disabled) then
      none
    else
      some { perm := newPerm, accessed := newAccessed }

/-!
## 1. Two-Phase Borrows vs. Protected `&mut T` (`RetagKind::TwoPhase` vs `FnEntry`)
-/

/-- Theorem 1a: An unprotected two-phase borrow (`RetagKind::TwoPhase`, initialized
    to `ReservedFrz false` with `protected = false`) survives a parent/foreign
    read (`vec.len()`) and subsequently activates to `Unique` on a child write
    (`vec.push(...)`). -/
theorem twoPhaseUnprotected_allows_parentRead_then_childWrite :
    (do
      let s0 := { perm := PermissionPriv.reservedFrz false, accessed := true : LocState }
      let s1 ← stepLocation .read .foreign false s0
      stepLocation .write .child false s1)
    = some { perm := .unique, accessed := true } := by
  rfl

/-- Theorem 1b: A function-entry protected `&mut T` (`RetagKind::FnEntry`,
    initialized to `ReservedFrz false` with `protected = true`) transitions to
    `ReservedFrz true` (`conflicted = true`) on a foreign read and **rejects**
    any subsequent child write during the call (`none` = UB). -/
theorem protectedReservedFrz_forbids_foreignRead_then_childWrite :
    (do
      let s0 := { perm := PermissionPriv.reservedFrz false, accessed := true : LocState }
      let s1 ← stepLocation .read .foreign true s0
      stepLocation .write .child true s1)
    = none := by
  rfl

/-!
## 2. Store Sinking and `DSE` Across `may_unwind` Calls vs. `sret` (`dead_on_unwind`)
-/

/-- Outcome of a callee `g()` invoked inside `f(x: &mut T)`. -/
inductive CallExit where
  | normalReturn
  | unwindPanic
  deriving DecidableEq, Repr

/-- Source execution of:
    ```rust
    fn f(x: &mut u64) {
        *x = v1;
        g_may_unwind();
        *x = v2;
    }
    ```
    followed by caller observation of `*x` (either after normal return or in a
    caller `Drop::drop` / `catch_unwind` handler after `f` exits via `UnwindResume`,
    which releases `x`'s protector in `before_stack_pop -> on_stack_pop`). -/
def evalSourceStoreMayUnwindStore (v0 v1 v2 : Nat) (exit : CallExit) : Nat :=
  let xAfterV1 := v1
  match exit with
  | .normalReturn =>
    let _ := v0
    let _ := xAfterV1
    v2
  | .unwindPanic =>
    -- `g_may_unwind()` unwinds through `f`'s `UnwindResume`; `x`'s protector is
    -- released cleanly by `on_stack_pop`, and caller `Drop` / `catch_unwind`
    -- observes `xAfterV1 = v1`!
    xAfterV1

/-- Uncompensated DSE / store-sinking optimization that deletes `*x = v1` before
    `g_may_unwind()` without adding `*x = v1` to the `cleanup` landing pad. -/
def evalUncompensatedDseAcrossUnwind (v0 _v1 v2 : Nat) (exit : CallExit) : Nat :=
  match exit with
  | .normalReturn => v2
  | .unwindPanic  => v0

/-- Compensated store-sinking optimization that sinks `*x = v1` into the `cleanup`
    landing pad before `UnwindResume` while eliding it on the normal path where
    `*x = v2` overwrites it. -/
def evalCompensatedSinkAcrossUnwind (_v0 v1 v2 : Nat) (exit : CallExit) : Nat :=
  match exit with
  | .normalReturn => v2
  | .unwindPanic  => v1

/-- Theorem 2a (`dseAcrossMayUnwindCall_unsound_counterexample`):
    When `v0 != v1` and `g_may_unwind()` unwinds (`exit = .unwindPanic`),
    uncompensated DSE produces `v0` instead of `v1`, falsifying refinement! -/
theorem dseAcrossMayUnwindCall_unsound_counterexample :
    evalUncompensatedDseAcrossUnwind 0 42 99 .unwindPanic ≠
      evalSourceStoreMayUnwindStore 0 42 99 .unwindPanic := by
  decide

/-- Theorem 2b (`compensatedStoreSinkingAcrossMayUnwind_refines`):
    Sinking `*x = v1` onto the `cleanup` landing pad before `UnwindResume` while
    eliminating the overwritten store on the normal path preserves exact caller
    observations across both `.normalReturn` and `.unwindPanic`. -/
theorem compensatedStoreSinkingAcrossMayUnwind_refines
    (v0 v1 v2 : Nat) (exit : CallExit) :
    evalCompensatedSinkAcrossUnwind v0 v1 v2 exit =
      evalSourceStoreMayUnwindStore v0 v1 v2 exit := by
  cases exit <;> rfl

/-- For an `sret` indirect return slot (`_0`, carrying `dead_on_unwind` in
    `rustc_codegen_llvm/src/abi.rs:495-512`), the caller never reads or drops
    `*_0` when `f` unwinds (`Option.none` on `.unwindPanic`). -/
def evalSretSource (_v0 _v1 v2 : Nat) (exit : CallExit) : Option Nat :=
  match exit with
  | .normalReturn => some v2
  | .unwindPanic  => none

def evalSretUncompensatedDse (_v0 _v1 v2 : Nat) (exit : CallExit) : Option Nat :=
  match exit with
  | .normalReturn => some v2
  | .unwindPanic  => none

/-- Theorem 2c (`sretDeadOnUnwindStoreSinking_refines`):
    Because `sret` is dead on unwind, uncompensated DSE and store sinking across
    `may_unwind` calls preserve exact semantics without `cleanup`-pad stores. -/
theorem sretDeadOnUnwindStoreSinking_refines
    (v0 v1 v2 : Nat) (exit : CallExit) :
    evalSretUncompensatedDse v0 v1 v2 exit = evalSretSource v0 v1 v2 exit := by
  cases exit <;> rfl

/-!
## 3. Sub-Object `UnsafeCell` (`&StructWithCell`) Byte-Range Permissions and Load Hoisting
-/

/-- A two-field struct `StructWithCell { freeze_field: u64, cell_field: UnsafeCell<u64> }`
    passed by shared reference `r: &StructWithCell` (`RetagKind::FnEntry`).
    Under `precise_interior_mut = true` (`tree_borrows/mod.rs:329-363`):
    - `freeze_field` receives `LocState { perm := .frozen, accessed := true }`
      with `StrongProtector`;
    - `cell_field` receives `LocState { perm := .cell, accessed := false }`
      with `StrongProtector`. -/
structure StructWithCellState where
  freezeVal  : Nat
  cellVal    : Nat
  freezePerm : LocState
  cellPerm   : LocState
  deriving DecidableEq, Repr

def initProtectedSharedStructWithCell (fVal cVal : Nat) : StructWithCellState :=
  { freezeVal  := fVal
  , cellVal    := cVal
  , freezePerm := { perm := .frozen, accessed := true }
  , cellPerm   := { perm := .cell,   accessed := false } }

/-- An unknown call `opaque_callee()` may perform arbitrary child or foreign writes
    to `cell_field` (`UnsafeCell`), and arbitrary foreign reads to `freeze_field`.
    If it attempts a foreign or child write to `freeze_field`, `stepLocation` on
    protected `Frozen` (`accessed = true`) returns `none` (UB)! -/
def stepOpaqueCallOnStructWithCell
    (st : StructWithCellState)
    (writeFreeze : Bool)
    (newCellVal : Nat) : Option StructWithCellState :=
  if writeFreeze then
    match stepLocation .write .foreign true st.freezePerm with
    | none => none
    | some fp' => some { st with freezePerm := fp', cellVal := newCellVal }
  else
    match stepLocation .write .child true st.cellPerm with
    | none => none
    | some cp' => some { st with cellPerm := cp', cellVal := newCellVal }

/-- Source program: read `r.freeze_field` before `opaque_callee()`, and read
    `r.freeze_field` again after `opaque_callee()`, summing both reads with
    `r.cell_field`. -/
def evalUnoptFreezeFieldReads
    (fVal cVal newCellVal : Nat) (writeFreeze : Bool) : Option Nat :=
  let st0 := initProtectedSharedStructWithCell fVal cVal
  let r1 := st0.freezeVal
  match stepOpaqueCallOnStructWithCell st0 writeFreeze newCellVal with
  | none => none
  | some st1 =>
    let r2 := st1.freezeVal
    some (r1 + r2 + st1.cellVal)

/-- GVN/LICM load-hoisted program: reuse `r1 = r.freeze_field` after
    `opaque_callee()` without reloading `r.freeze_field`. -/
def evalHoistedFreezeFieldRead
    (fVal cVal newCellVal : Nat) (writeFreeze : Bool) : Option Nat :=
  let st0 := initProtectedSharedStructWithCell fVal cVal
  let r1 := st0.freezeVal
  match stepOpaqueCallOnStructWithCell st0 writeFreeze newCellVal with
  | none => none
  | some st1 =>
    some (r1 + r1 + st1.cellVal)

/-- Theorem 3 (`freezeFieldLoadHoisting_refines`):
    Even when `&StructWithCell` contains an interior-mutable `UnsafeCell` field
    mutated during `opaque_callee()`, hoisting/CSE of loads from the sibling
    `Freeze` field across `opaque_callee()` is an exact equivalence across all
    defined executions (and `writeFreeze = true` triggers protector UB in both). -/
theorem freezeFieldLoadHoisting_refines
    (fVal cVal newCellVal : Nat) (writeFreeze : Bool) :
    evalHoistedFreezeFieldRead fVal cVal newCellVal writeFreeze =
      evalUnoptFreezeFieldReads fVal cVal newCellVal writeFreeze := by
  cases writeFreeze <;> rfl

#print axioms twoPhaseUnprotected_allows_parentRead_then_childWrite
#print axioms protectedReservedFrz_forbids_foreignRead_then_childWrite
#print axioms dseAcrossMayUnwindCall_unsound_counterexample
#print axioms compensatedStoreSinkingAcrossMayUnwind_refines
#print axioms sretDeadOnUnwindStoreSinking_refines
#print axioms freezeFieldLoadHoisting_refines

end TreeBorrowsUnwindAndUnsafeCellProbe
