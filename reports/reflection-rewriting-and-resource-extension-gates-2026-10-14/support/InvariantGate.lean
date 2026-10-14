import Lean

/-- The consumer fixes both the transition relation and the safety predicate. -/
inductive Reach (init : α → Prop) (step : α → α → Prop) : α → Prop where
  | initial {s} : init s → Reach init step s
  | next {s t} : Reach init step s → step s t → Reach init step t

structure InvariantEvidence (init : α → Prop) (step : α → α → Prop)
    (safe : α → Prop) (candidate : α → Prop) : Prop where
  initiation : ∀ s, init s → candidate s
  preservation : ∀ s t, candidate s → step s t → candidate t
  consequence : ∀ s, candidate s → safe s

theorem invariant_gate (e : InvariantEvidence init step safe candidate)
    (h : Reach init step s) : safe s := by
  apply e.consequence
  induction h with
  | initial hi => exact e.initiation _ hi
  | next _ st ih => exact e.preservation _ _ ih st

def initial (n : Nat) : Prop := n = 0
def evenStep (n m : Nat) : Prop := m = n + 2
def proposed (n : Nat) : Prop := n % 2 = 0

theorem proposed_checked : InvariantEvidence initial evenStep proposed proposed where
  initiation := by intro n hn; subst n; simp [proposed]
  preservation := by
    intro n m hn hm
    subst m
    simpa [proposed, Nat.add_mod] using hn
  consequence := by intro _ h; exact h

theorem all_reachable_even (h : Reach initial evenStep n) : proposed n :=
  invariant_gate proposed_checked h

/-- A proof of Boolean checking is separately required; computation alone is not this field. -/
structure CheckerAdequacy (Statement Witness : Type) (meaning : Statement → Prop) where
  check : Statement → Witness → Bool
  sound : ∀ s w, check s w = true → meaning s

#print axioms invariant_gate
#print axioms proposed_checked
#print axioms all_reachable_even

