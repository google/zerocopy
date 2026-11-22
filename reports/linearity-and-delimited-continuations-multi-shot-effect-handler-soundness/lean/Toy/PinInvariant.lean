/-!
# Toy Model: Structural `Pin` Invariant Separation and Drop-Before-Storage-Reuse Guarantee

A self-contained, Mathlib-free Lean 4 (`v4.34.1`) toy model of a Rust-style stackless
self-referential coroutine / `Future` state machine illustrating:
  1. Moving an unpinned suspended self-referential coroutine to a different address
     invalidates its internal self-pointer (`unpinned_move_breaks_self_ref`).
  2. Reusing/overwriting storage of a pinned coroutine without running `Drop` first
     (e.g., invalidating a pinned `ManuallyDrop` inner value) breaks the `Pin` drop
     guarantee (`skip_drop_then_reuse_violates_drop_guarantee`).
  3. Affine `mem::forget` without storage reuse preserves the `Pin` invariants
     (`mem_forget_without_reuse_preserves_pin_invariants`).
  4. Any finite trace of `Pin`-conforming operations (pin, poll, structural in-place field
     mutation, drop, reuse-after-drop, or forget-without-reuse) preserves both internal
     self-pointer validity and the drop-before-storage-reuse guarantee
     (`pinned_trace_preserves_invariants`).

Model–system relation: none proved. This is an abstract finite-state toy model of the
`std::pin` / RFC 2349 contract, not a mechanized proof of `rustc` MIR lowering or Stacked
Borrows / Tree Borrows.
-/

namespace Toy.PinInvariant

/-- Fixed byte offset of the interior payload field inside the coroutine frame. -/
def payloadOffset : Nat := 8

/-- Execution state of a stackless self-referential coroutine. -/
inductive CoroState where
  | unpolled
  /-- Suspended after creating an interior pointer `selfPtr` to `&self.payload`. -/
  | suspended (selfPtr : Nat)
  | completed
  deriving DecidableEq, Repr

/-- Backing storage lifecycle state for the coroutine's memory slot. -/
inductive StorageState where
  | allocated
  | dropped
  | reused
  | leaked
  deriving DecidableEq, Repr

/-- Abstract representation of a coroutine frame placed at `addr`. -/
structure CoroFrame where
  addr : Nat
  payload : Nat
  state : CoroState
  storage : StorageState
  everPinned : Bool
  droppedBeforeReuse : Bool
  deriving DecidableEq, Repr

/-- Construct a fresh unpolled coroutine at memory address `addr`. -/
def CoroFrame.fresh (addr : Nat) (initPayload : Nat) : CoroFrame :=
  { addr := addr
    payload := initPayload
    state := .unpolled
    storage := .allocated
    everPinned := false
    droppedBeforeReuse := false }

/-- Internal self-pointer validity: whenever the coroutine is suspended in live allocated
    storage, its stored interior pointer targets `&self.payload = addr + payloadOffset`. -/
def SelfRefValid (c : CoroFrame) : Prop :=
  ∀ p, c.storage = .allocated → c.state = .suspended p → p = c.addr + payloadOffset

/-- Rust `std::pin` Drop guarantee (drop-before-storage-reuse):
    once a `!Unpin` value has been pinned (`everPinned = true`), its backing storage may
    only enter `.reused` if `Drop::drop` ran first (`droppedBeforeReuse = true`). -/
def DropBeforeReuseGuarantee (c : CoroFrame) : Prop :=
  c.everPinned = true → c.storage = .reused → c.droppedBeforeReuse = true

/-- Combined `Pin` safety invariant, strengthened with storage-state consistency
    (`storage = .dropped → droppedBeforeReuse = true`) so trace induction closes cleanly. -/
def PinInvariant (c : CoroFrame) : Prop :=
  SelfRefValid c ∧
  DropBeforeReuseGuarantee c ∧
  (c.storage = .dropped → c.droppedBeforeReuse = true)

/-- Mechanical Rust move (`memcpy` of bytes without pointer fixup): relocates the frame to
    `newAddr` while leaving the stored `selfPtr` bits unchanged. -/
def unpinnedMove (c : CoroFrame) (newAddr : Nat) : CoroFrame :=
  { c with addr := newAddr }

/-- Unsound storage invalidation without running `Drop` (models e.g. projecting `Pin`
    through `ManuallyDrop` and freeing/overwriting the backing slot). -/
def unsafeReuseWithoutDrop (c : CoroFrame) : CoroFrame :=
  { c with storage := .reused }

/-- Safe operations permitted under the `Pin<P>` API discipline. -/
inductive PinOp where
  /-- Pin the allocated coroutine in place (`Pin::new_unchecked` / `Box::pin` / `pin!`). -/
  | pinInPlace
  /-- Poll a pinned allocated coroutine (`Future::poll(self: Pin<&mut Self>, ...)`). -/
  | poll (nextPayload : Nat)
  /-- Structural in-place field mutation at the pinned address (does not move `self`). -/
  | mutateFieldInPlace (newPayload : Nat)
  /-- Run `Drop::drop` in place before any storage reuse. -/
  | runDrop
  /-- Reclaim/overwrite storage ONLY after `Drop` has run. -/
  | reuseAfterDrop
  /-- Affine `std::mem::forget`: skip `Drop` and leak storage permanently (never reused). -/
  | memForget
  deriving DecidableEq, Repr

/-- Single step of a `Pin`-conforming operation. Operations outside their precondition are
    modeled as no-ops (rejected by Rust's borrow/type checker or `Pin` method signatures). -/
def stepPinOp (op : PinOp) (c : CoroFrame) : CoroFrame :=
  match op with
  | .pinInPlace =>
      if c.storage = .allocated then { c with everPinned := true } else c
  | .poll nextPayload =>
      if c.everPinned = true ∧ c.storage = .allocated then
        match c.state with
        | .unpolled =>
            { c with
                payload := nextPayload
                state := .suspended (c.addr + payloadOffset) }
        | .suspended _ =>
            { c with
                payload := nextPayload
                state := .completed }
        | .completed => c
      else c
  | .mutateFieldInPlace newPayload =>
      if c.storage = .allocated then { c with payload := newPayload } else c
  | .runDrop =>
      if c.storage = .allocated then
        { c with
            state := .completed
            storage := .dropped
            droppedBeforeReuse := true }
      else c
  | .reuseAfterDrop =>
      if c.storage = .dropped then { c with storage := .reused } else c
  | .memForget =>
      if c.storage = .allocated then { c with storage := .leaked } else c

/-- Execute a finite sequence of `Pin`-conforming operations. -/
def runPinTrace : List PinOp → CoroFrame → CoroFrame
  | [], c => c
  | op :: rest, c => runPinTrace rest (stepPinOp op c)

/-! ### Discriminating Theorems (Part d) -/

/-- Theorem (d1): Moving a suspended self-referential coroutine to any distinct address
    `newAddr ≠ c.addr` breaks internal self-pointer validity (`¬ SelfRefValid`). -/
theorem unpinned_move_breaks_self_ref
    (c : CoroFrame) (p newAddr : Nat)
    (hAlloc : c.storage = .allocated)
    (hSusp : c.state = .suspended p)
    (hValid : SelfRefValid c)
    (hNeq : newAddr ≠ c.addr) :
    ¬ SelfRefValid (unpinnedMove c newAddr) := by
  intro hMovedValid
  have hpOld : p = c.addr + payloadOffset := hValid p hAlloc hSusp
  have hpNew : p = newAddr + payloadOffset := hMovedValid p hAlloc hSusp
  have hAddEq : newAddr + payloadOffset = c.addr + payloadOffset := hpNew.symm.trans hpOld
  exact hNeq (Nat.add_right_cancel hAddEq)

/-- Theorem (d2): Reusing/overwriting storage of a pinned coroutine without running `Drop`
    first violates the `Pin` drop-before-storage-reuse guarantee. -/
theorem skip_drop_then_reuse_violates_drop_guarantee
    (c : CoroFrame)
    (hPinned : c.everPinned = true)
    (hNotDropped : c.droppedBeforeReuse = false) :
    ¬ DropBeforeReuseGuarantee (unsafeReuseWithoutDrop c) := by
  intro hGuar
  have hTrue : c.droppedBeforeReuse = true := hGuar hPinned rfl
  rw [hNotDropped] at hTrue
  cases hTrue

/-- Theorem (d3): Affine `mem::forget` without storage reuse preserves `PinInvariant`,
    separating affine drop-skipping (leaking) from unsound storage reuse. -/
theorem mem_forget_without_reuse_preserves_pin_invariants
    (c : CoroFrame) (hInv : PinInvariant c) :
    PinInvariant (stepPinOp .memForget c) := by
  rcases hInv with ⟨hSelf, hDrop, hCons⟩
  simp only [stepPinOp]
  split
  · refine ⟨?_, ?_, ?_⟩
    · intro p hAlloc _
      cases hAlloc
    · intro _ hReused
      cases hReused
    · intro hDropped
      cases hDropped
  · exact ⟨hSelf, hDrop, hCons⟩

/-- Single-step preservation lemma for every `PinOp`. -/
theorem stepPinOp_preserves_invariant
    (op : PinOp) (c : CoroFrame) (hInv : PinInvariant c) :
    PinInvariant (stepPinOp op c) := by
  rcases hInv with ⟨hSelf, hDrop, hCons⟩
  cases op with
  | pinInPlace =>
      simp only [stepPinOp]
      split
      · rename_i hAlloc
        refine ⟨hSelf, ?_, hCons⟩
        intro _ hReused
        rw [hAlloc] at hReused
        cases hReused
      · exact ⟨hSelf, hDrop, hCons⟩
  | poll nextPayload =>
      simp only [stepPinOp]
      split
      · rename_i hCond
        cases hSt : c.state with
        | unpolled =>
            refine ⟨?_, ?_, hCons⟩
            · intro p _ hSusp
              cases hSusp
              rfl
            · intro _ hReused
              rw [hCond.2] at hReused
              cases hReused
        | suspended oldP =>
            refine ⟨?_, ?_, hCons⟩
            · intro p _ hSusp
              cases hSusp
            · intro _ hReused
              rw [hCond.2] at hReused
              cases hReused
        | completed =>
            exact ⟨hSelf, hDrop, hCons⟩
      · exact ⟨hSelf, hDrop, hCons⟩
  | mutateFieldInPlace newPayload =>
      simp only [stepPinOp]
      split
      · exact ⟨hSelf, hDrop, hCons⟩
      · exact ⟨hSelf, hDrop, hCons⟩
  | runDrop =>
      simp only [stepPinOp]
      split
      · refine ⟨?_, ?_, ?_⟩
        · intro p hAlloc _
          cases hAlloc
        · intro _ hReused
          cases hReused
        · intro _
          rfl
      · exact ⟨hSelf, hDrop, hCons⟩
  | reuseAfterDrop =>
      simp only [stepPinOp]
      split
      · rename_i hDropped
        refine ⟨?_, ?_, ?_⟩
        · intro p hAlloc _
          cases hAlloc
        · intro _ _
          exact hCons hDropped
        · intro hDr
          cases hDr
      · exact ⟨hSelf, hDrop, hCons⟩
  | memForget =>
      exact mem_forget_without_reuse_preserves_pin_invariants c ⟨hSelf, hDrop, hCons⟩

/-- Theorem (d4): Any finite trace of `Pin`-conforming operations starting from a fresh
    unpolled coroutine preserves both `SelfRefValid` and `DropBeforeReuseGuarantee`,
    and never alters the coroutine's address `addr`. -/
theorem pinned_trace_preserves_invariants
    (ops : List PinOp) (addr initPayload : Nat) :
    let final := runPinTrace ops (CoroFrame.fresh addr initPayload)
    PinInvariant final ∧ final.addr = addr := by
  have hAux : ∀ (ts : List PinOp) (c : CoroFrame),
      PinInvariant c → c.addr = addr →
      PinInvariant (runPinTrace ts c) ∧ (runPinTrace ts c).addr = addr := by
    intro ts
    induction ts with
    | nil =>
        intro c hInv hAddr
        exact ⟨hInv, hAddr⟩
    | cons op rest ih =>
        intro c hInv hAddr
        have hStepInv := stepPinOp_preserves_invariant op c hInv
        have hStepAddr : (stepPinOp op c).addr = addr := by
          cases op <;> simp only [stepPinOp] <;> split <;> first | exact hAddr | (cases c.state <;> exact hAddr)
        exact ih (stepPinOp op c) hStepInv hStepAddr
  have hFreshInv : PinInvariant (CoroFrame.fresh addr initPayload) := by
    refine ⟨?_, ?_, ?_⟩
    · intro p _ hSusp; cases hSusp
    · intro _ hReused; cases hReused
    · intro hDropped; cases hDropped
  exact hAux ops (CoroFrame.fresh addr initPayload) hFreshInv rfl

end Toy.PinInvariant
