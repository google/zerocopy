import ToyAlias.Stack

/-!
# Unknown code, outcomes, and refinement with UB

Unknown code (a call to a function the optimizer cannot see) is modelled as a finite
sequence of callee operations. The callee addresses tags through an *environment*:
initially the list of tags passed to it, extended by every tag the callee creates
itself. So the callee can only use tags it was given or tags it derived from them.
The callee may perform externally observable actions that do not touch the tracked
location (`emit`), and it may **halt**: end the whole program without returning
(modelling `exit`, an abort, or divergence). Every value the callee reads or emits is
observable.

Callee reborrows are unprotected. The callee is non-adaptive: its operation sequence
(including the values it writes or emits) is fixed in advance and cannot depend on the
values it reads.
-/

namespace Toy.Alias

/-- One operation of unknown code. Indices refer to the callee's tag environment. -/
inductive COp where
  /-- Read through the `i`-th tag of the environment; the value is observed. -/
  | read (i : Nat)
  /-- Write `v` through the `i`-th tag of the environment. -/
  | write (i : Nat) (v : Nat)
  /-- Reborrow from the `i`-th tag with permission `p` (unprotected); the new tag is
  appended to the environment. -/
  | retag (i : Nat) (p : Perm)
  /-- An externally observable action that does not touch the tracked location (output,
  or an access to memory that no item of the tracked location constrains); the value `v`
  is observed. -/
  | emit (v : Nat)
  /-- End the whole program here (exit, abort, or divergence): control never returns. -/
  | halt
  deriving DecidableEq, Repr

/-- Outcome of running code: undefined behavior; the program ended inside unknown code
after the observations `obs`; or the code finished with observations `obs` (callee
reads and emitted values, followed by the values the known code returns) in final
state `m`. -/
inductive Outcome where
  | ub
  | halted (obs : List Nat)
  | done (obs : List Nat) (m : Mem)
  deriving DecidableEq, Repr

/-- Prepend an observation to a non-UB outcome. -/
def Outcome.consObs (v : Nat) : Outcome → Outcome
  | .ub => .ub
  | .halted obs => .halted (v :: obs)
  | .done obs m => .done (v :: obs) m

/-- Sequencing: continue a `done` outcome with `k`, and propagate `ub` and `halted`
unchanged. -/
def Outcome.bind : Outcome → (List Nat → Mem → Outcome) → Outcome
  | .ub, _ => .ub
  | .halted obs, _ => .halted obs
  | .done obs m, k => k obs m

/-- Lift a partial step: `none` is UB. -/
def liftO {α : Type} : Option α → (α → Outcome) → Outcome
  | none, _ => .ub
  | some a, k => k a

/-- Run unknown code `c` with tag environment `env` from state `m`. An out-of-range
environment index is UB. -/
def runCallee : List Tag → List COp → Mem → Outcome
  | _, [], m => .done [] m
  | _, .halt :: _, _ => .halted []
  | env, .emit v :: c, m => (runCallee env c m).consObs v
  | env, .read i :: c, m =>
    liftO env[i]? fun t =>
    liftO (read t m) fun (v, m') =>
    (runCallee env c m').consObs v
  | env, .write i v :: c, m =>
    liftO env[i]? fun t =>
    liftO (write t v m) fun m' =>
    runCallee env c m'
  | env, .retag i p :: c, m =>
    liftO env[i]? fun t =>
    liftO (retag t p false m) fun (t', m') =>
    runCallee (env ++ [t']) c m'

/-- Positive example: unknown code holding the root tag reads the value, then halts. -/
theorem runCallee_example_pos :
    runCallee [0] [.read 0, .halt] initMem = .halted [0] := by decide

/-- Positive example: unknown code can create a child of a tag it holds and use it. -/
theorem runCallee_example_child :
    runCallee [0] [.retag 0 .unique, .write 1 5, .read 1] initMem =
      .done [5] ⟨5, [⟨.unique, 1, false⟩, ⟨.unique, 0, false⟩], 2⟩ := by decide

/-- Positive example: unknown code holding no tags can still act observably and return. -/
theorem runCallee_example_emit :
    runCallee [] [.emit 3, .emit 4] initMem = .done [3, 4] initMem := by decide

/-- Negative example: unknown code cannot use a tag it does not hold (index out of
range is UB). -/
theorem runCallee_example_neg : runCallee [] [.read 0] initMem = .ub := by decide

/-- **Refinement with UB.** The semantics is deterministic, so each program has exactly
one outcome. The target refines the source if, whenever the source has no UB, the
target has exactly the source's outcome (same observations, same halting behaviour,
and, for `done`, the same final state including the borrow stack and the tag counter).
Source UB permits any target outcome. Because the final state is compared, any
continuation that runs on it behaves identically; in this model protectors never end,
so such a continuation still runs with the entry protector active (function return is
not modelled). Equality of the final borrow stack is stronger than what a
simulation-based contextual refinement requires. -/
def Refines (tgt src : Outcome) : Prop := src ≠ .ub → tgt = src

instance (tgt src : Outcome) : Decidable (Refines tgt src) := by
  unfold Refines; infer_instance

/-- Positive example: anything refines a UB source. -/
theorem refines_of_src_ub : Refines (.halted [3]) .ub := by decide

/-- Positive example: an outcome refines itself. -/
theorem refines_refl_example : Refines (.done [1] initMem) (.done [1] initMem) := by decide

/-- Negative example: a UB target does not refine a defined source. -/
theorem not_refines_tgt_ub : ¬ Refines .ub (.done [] initMem) := by decide

/-- Negative example: different observations are not a refinement. -/
theorem not_refines_obs : ¬ Refines (.halted [0]) (.halted [5]) := by decide

/-- The externally visible part of an outcome: `none` for UB; otherwise whether control
returned, the observations, and (if control returned) the stored value. The borrow
stack and the tag counter are internal bookkeeping and are omitted. -/
def Outcome.visible : Outcome → Option (Bool × List Nat × Option Nat)
  | .ub => none
  | .halted obs => some (false, obs, none)
  | .done obs m => some (true, obs, some m.val)

/-- Refinement of visible behaviour only: whenever the source has no UB, the target has
the same visible outcome. It is implied by `Refines` (`Refines.visibly`). A failure of
`VisiblyRefines` exhibits a difference in UB, halting, observations, or stored value,
not merely in borrow-tracking state. -/
def VisiblyRefines (tgt src : Outcome) : Prop := src ≠ .ub → tgt.visible = src.visible

instance (tgt src : Outcome) : Decidable (VisiblyRefines tgt src) := by
  unfold VisiblyRefines; infer_instance

/-- `Refines` implies `VisiblyRefines`. -/
theorem Refines.visibly {tgt src : Outcome} (h : Refines tgt src) : VisiblyRefines tgt src :=
  fun hs => by rw [h hs]

/-- Positive example: outcomes that differ only in the borrow stack refine visibly (but
not in the sense of `Refines`). -/
theorem visiblyRefines_example_pos :
    VisiblyRefines (.done [1] ⟨0, [], 1⟩) (.done [1] initMem) ∧
      ¬ Refines (.done [1] ⟨0, [], 1⟩) (.done [1] initMem) := by decide

/-- Negative example: a different final stored value is a visible difference. -/
theorem visiblyRefines_example_neg :
    ¬ VisiblyRefines (.done [] initMem) (.done [] ⟨5, initMem.stack, initMem.next⟩) := by
  decide

/-- Unknown code preserves `TagsBelowNext` (on every returning execution). -/
theorem tagsBelowNext_runCallee {env : List Tag} {c : List COp} {m m' : Mem}
    {obs : List Nat} (h : TagsBelowNext m) (hrc : runCallee env c m = .done obs m') :
    TagsBelowNext m' := by
  induction c generalizing env m obs with
  | nil => simp [runCallee] at hrc; obtain ⟨_, rfl⟩ := hrc; exact h
  | cons op c ih =>
    cases op with
    | halt => simp [runCallee] at hrc
    | emit v =>
      simp only [runCallee] at hrc
      cases hrec : runCallee env c m with
      | ub => simp [hrec, Outcome.consObs] at hrc
      | halted _ => simp [hrec, Outcome.consObs] at hrc
      | done obs' m₂ =>
        simp only [hrec, Outcome.consObs, Outcome.done.injEq] at hrc
        obtain ⟨_, rfl⟩ := hrc
        exact ih h hrec
    | read i =>
      unfold runCallee at hrc
      cases hi : env[i]? with
      | none => simp [hi, liftO] at hrc
      | some t =>
        simp only [hi, liftO] at hrc
        cases hr : read t m with
        | none => simp [hr] at hrc
        | some vm =>
          rcases vm with ⟨v, m₁⟩
          simp only [hr] at hrc
          cases hrec : runCallee env c m₁ with
          | ub => simp [hrec, Outcome.consObs] at hrc
          | halted _ => simp [hrec, Outcome.consObs] at hrc
          | done obs' m₂ =>
            simp only [hrec, Outcome.consObs, Outcome.done.injEq] at hrc
            obtain ⟨_, rfl⟩ := hrc
            exact ih (tagsBelowNext_read h hr) hrec
    | write i v =>
      unfold runCallee at hrc
      cases hi : env[i]? with
      | none => simp [hi, liftO] at hrc
      | some t =>
        simp only [hi, liftO] at hrc
        cases hw : write t v m with
        | none => simp [hw] at hrc
        | some m₁ =>
          simp only [hw] at hrc
          exact ih (tagsBelowNext_write h hw) hrc
    | retag i p =>
      unfold runCallee at hrc
      cases hi : env[i]? with
      | none => simp [hi, liftO] at hrc
      | some t =>
        simp only [hi, liftO] at hrc
        cases hrt : retag t p false m with
        | none => simp [hrt] at hrc
        | some tm =>
          rcases tm with ⟨t', m₁⟩
          simp only [hrt] at hrc
          exact ih (tagsBelowNext_retag h hrt) hrc

end Toy.Alias
