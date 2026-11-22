import Toy.Relocation

/-!
# Reentrancy: exclusive borrows against callbacks and finalizers

Part (b) shows that handles and branded views stay *valid* across a safepoint.  Validity is
not exclusivity: reentrant code holds its own handle to the same object and may use it.

Here relocation is abstracted away (objects are named by identity) and each object carries a
dynamic borrow flag.  An outer native frame takes an exclusive borrow of object `o`, writes
`v`, enters the runtime, and afterwards reads `o` again through the borrow it still holds.
Code that assumes exclusivity (a compiler forwarding the stored `v` to the later load) is
right exactly when no reentrant access to `o` succeeded in between.

* `runU` — reentrant accesses are not checked.
* `runC` — a reentrant access to an exclusively borrowed object is refused.

Reentrant code arrives two ways: as an explicit callback, or as finalizers that the
collector schedules at a safepoint (`RT.pending`).
-/

namespace Toy

/-- An object: a payload and a dynamic exclusive-borrow flag. -/
structure Cell where
  val  : Val
  excl : Bool

abbrev Store := Nat → Cell

/-- What reentrant code attempts, through its own handle to object `o`. -/
inductive Act where
  | write (o : Nat) (v : Val)
  | read (o : Nat)

/-- What happened to an attempt. -/
inductive Ev where
  /-- the access went through -/
  | acc (o : Nat)
  /-- the dynamic borrow check refused it -/
  | denied (o : Nat)

/-- The object an action targets. -/
def Act.target : Act → Nat
  | .write o _ => o
  | .read o => o

/-- Unchecked: every reentrant access goes through. -/
def stepU (st : Store) : Act → Store × Ev
  | .write o v => (upd st o { st o with val := v }, .acc o)
  | .read o => (st, .acc o)

/-- Checked: an access to an exclusively borrowed object is refused. -/
def stepC (st : Store) (a : Act) : Store × Ev :=
  if (st a.target).excl then (st, .denied a.target) else stepU st a

/-- Run a list of reentrant actions, collecting the event log. -/
def run (step : Store → Act → Store × Ev) : Store → List Act → Store × List Ev
  | st, [] => (st, [])
  | st, a :: as =>
    let r := step st a
    let rest := run step r.1 as
    (rest.1, r.2 :: rest.2)

abbrev runU := run stepU
abbrev runC := run stepC

/-- The outer frame: exclusively borrow `o`, store `v`, enter the runtime (which runs the
reentrant `acts`), then load `o` again through the borrow still held. -/
def holder (step : Store → Act → Store × Ev) (st : Store) (o : Nat) (v : Val)
    (acts : List Act) : Val :=
  ((run step (upd st o ⟨v, true⟩) acts).1 o).val

/-- A checked step leaves an exclusively borrowed object untouched and logs no access to it. -/
theorem stepC_excl (st : Store) (a : Act) (o : Nat) (he : (st o).excl = true) :
    (stepC st a).1 o = st o ∧ (stepC st a).2 ≠ .acc o := by
  unfold stepC
  by_cases ht : (st a.target).excl = true
  · simp [ht]
  · have hne : a.target ≠ o := by
      intro e
      rw [e] at ht
      exact ht he
    simp only [ht]
    cases a with
    | write o' v =>
      have hne' : o ≠ o' := fun e => hne e.symm
      refine ⟨?_, ?_⟩
      · simp [stepU, upd_other _ _ hne']
      · intro e
        simp [stepU] at e
        exact hne e
    | read o' =>
      refine ⟨rfl, ?_⟩
      intro e
      simp [stepU] at e
      exact hne e

/-- (c, positive half) **Checked reentrancy preserves an exclusive borrow.**  Whatever the
reentrant code attempts, an exclusively borrowed object is unchanged afterwards and the event
log records no successful access to it. -/
theorem checked_reentrancy_preserves_exclusive : ∀ (acts : List Act) (st : Store) (o : Nat),
    (st o).excl = true →
    (runC st acts).1 o = st o ∧ ∀ e, e ∈ (runC st acts).2 → e ≠ .acc o := by
  intro acts
  induction acts with
  | nil =>
    intro st o _
    refine ⟨rfl, ?_⟩
    intro e he
    cases he
  | cons a as ih =>
    intro st o he
    obtain ⟨h1, h2⟩ := stepC_excl st a o he
    have he' : ((stepC st a).1 o).excl = true := by rw [h1]; exact he
    obtain ⟨i1, i2⟩ := ih (stepC st a).1 o he'
    refine ⟨?_, ?_⟩
    · show (run stepC (stepC st a).1 as).1 o = st o
      rw [i1, h1]
    · intro e hmem
      have hmem' : e ∈ (stepC st a).2 :: (run stepC (stepC st a).1 as).2 := hmem
      cases hmem' with
      | head => exact h2
      | tail _ ht => exact i2 e ht

/-- (c, positive half, as the outer frame sees it) Under checked reentrancy the load after
the call returns the stored value, for every reentrant action list: forwarding the store to
the load is justified. -/
theorem holder_checked (st : Store) (o : Nat) (v : Val) (acts : List Act) :
    holder stepC st o v acts = v := by
  unfold holder
  have he : ((upd st o ⟨v, true⟩) o).excl = true := by simp
  rw [(checked_reentrancy_preserves_exclusive acts _ o he).1]
  simp

/-- (c) **Unchecked reentrancy violates an exclusive borrow.**  A single reentrant write
through another handle changes what the outer frame loads through the borrow it still holds,
and the log shows a successful access to an exclusively borrowed object.  Forwarding the store
to the load is wrong for this run. -/
theorem unchecked_reentrancy_breaks_exclusive (st : Store) (o : Nat) (v w : Val) (hvw : v ≠ w) :
    holder stepU st o v [.write o w] = w ∧
    holder stepU st o v [.write o w] ≠ v ∧
    Ev.acc o ∈ (runU (upd st o ⟨v, true⟩) [.write o w]).2 := by
  have e : holder stepU st o v [.write o w] = w := by
    simp [holder, run, stepU]
  refine ⟨e, ?_, ?_⟩
  · rw [e]
    exact fun c => hvw c.symm
  · simp [run, stepU]

/-- (c) An unchecked reentrant *read* observes the outer frame's in-flight value while the
exclusive borrow is outstanding. -/
theorem unchecked_reentrant_read_observes (st : Store) (o : Nat) (v : Val) :
    Ev.acc o ∈ (runU (upd st o ⟨v, true⟩) [.read o]).2 := by
  simp [run, stepU]

/-! ## Finalizers as reentrancy that nobody called -/

/-- Runtime state: the store, plus finalizer bodies whose objects the collector has found
unreachable. -/
structure RT where
  st      : Store
  pending : List (List Act)

/-- Synchronous policy: a collection triggered by an allocation runs every pending finalizer
before returning to the allocating frame. -/
def allocSync (step : Store → Act → Store × Ev) (rt : RT) : RT :=
  { st := (run step rt.st rt.pending.flatten).1, pending := [] }

/-- Deferred policy: allocation collects but leaves finalizers queued until an explicit poll. -/
def allocDeferred (rt : RT) : RT := rt

/-- The explicit poll point of the deferred policy. -/
def poll (step : Store → Act → Store × Ev) (rt : RT) : RT := allocSync step rt

/-- The outer frame again, but it makes no call back: it only allocates. -/
def holderAlloc (alloc : RT → RT) (st : Store) (o : Nat) (v : Val)
    (pending : List (List Act)) : Val :=
  ((alloc { st := upd st o ⟨v, true⟩, pending := pending }).st o).val

/-- (c, finalizer form) **A synchronous unchecked finalizer violates an exclusive borrow at
an allocation.**  The outer frame made no call back; the collector did. -/
theorem sync_unchecked_finalizer_breaks_exclusive (st : Store) (o : Nat) (v w : Val)
    (hvw : v ≠ w) :
    holderAlloc (allocSync stepU) st o v [[.write o w]] = w ∧
    holderAlloc (allocSync stepU) st o v [[.write o w]] ≠ v := by
  have e : holderAlloc (allocSync stepU) st o v [[.write o w]] = w := by
    simp [holderAlloc, allocSync, run, stepU]
  exact ⟨e, by rw [e]; exact fun c => hvw c.symm⟩

/-- Synchronous finalizers under the dynamic borrow check cannot disturb the borrow. -/
theorem sync_checked_finalizer_preserves_exclusive (st : Store) (o : Nat) (v : Val)
    (pending : List (List Act)) :
    holderAlloc (allocSync stepC) st o v pending = v := by
  unfold holderAlloc allocSync
  have he : ((upd st o ⟨v, true⟩) o).excl = true := by simp
  show ((run stepC (upd st o ⟨v, true⟩) pending.flatten).1 o).val = v
  rw [(checked_reentrancy_preserves_exclusive pending.flatten _ o he).1]
  simp

/-- Deferred finalizers cannot disturb the borrow at an allocation even when unchecked: they
have not run.  (Immediate from the definition of the policy; the content is in the policy.) -/
theorem deferred_finalizer_preserves_exclusive (st : Store) (o : Nat) (v : Val)
    (pending : List (List Act)) :
    holderAlloc allocDeferred st o v pending = v := by
  simp [holderAlloc, allocDeferred]

/-- The deferred policy moves the hazard rather than removing it: polling while the exclusive
borrow is still outstanding runs the unchecked finalizer after all. -/
theorem deferred_then_poll_breaks_exclusive (st : Store) (o : Nat) (v w : Val) (hvw : v ≠ w) :
    ((poll stepU (allocDeferred { st := upd st o ⟨v, true⟩, pending := [[.write o w]] })).st
      o).val ≠ v := by
  have e : ((poll stepU (allocDeferred
      { st := upd st o ⟨v, true⟩, pending := [[.write o w]] })).st o).val = w := by
    simp [poll, allocSync, allocDeferred, run, stepU]
  rw [e]
  exact fun c => hvw c.symm

end Toy
