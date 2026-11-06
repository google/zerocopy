import Std
namespace Ownership
structure Slot where
  target : Option Nat
  temporary : Option Nat
  drops : Nat
  deriving DecidableEq

def stored (value drops : Nat) : Slot := ⟨some value, none, drops⟩
def moved (value drops : Nat) : Slot := ⟨none, some value, drops⟩
def oneOwner (s : Slot) : Prop :=
  (s.target.isSome = true ∧ s.temporary.isSome = false) ∨
  (s.target.isSome = false ∧ s.temporary.isSome = true)
def moveOut (s : Slot) : Slot := ⟨none, s.target, s.drops⟩
def restore (s : Slot) : Slot := ⟨s.temporary, none, s.drops⟩
inductive Exit where | normal | unwind deriving DecidableEq
def callback (next : Nat) (_exit : Exit) (s : Slot) : Slot := { s with temporary := some next }
def update (old next drops : Nat) (exit : Exit) : Slot :=
  restore (callback next exit (moveOut (stored old drops)))

theorem move_one_owner (value drops : Nat) : oneOwner (moveOut (stored value drops)) := by
  simp [oneOwner, moveOut, stored]
theorem update_restored (old next drops : Nat) (exit : Exit) :
    update old next drops exit = stored next drops := rfl
theorem update_one_owner (old next drops : Nat) (exit : Exit) :
    oneOwner (update old next drops exit) := by
  simp [update, restore, callback, moveOut, stored, oneOwner]
theorem missing_cleanup_loses_target (old next drops : Nat) :
    (callback next .unwind (moveOut (stored old drops))).target = none := rfl
theorem wrong_copy_duplicates_owner (value drops : Nat) :
    ¬ oneOwner ⟨some value, some value, drops⟩ := by simp [oneOwner]

def insert (old : List Nat) (position additional : Nat) : List Nat :=
  old.take position ++ List.replicate additional 0 ++ old.drop position

theorem insertion_zero_budget (old : List Nat) (position : Nat) :
    insert old position 0 = old := by simp [insert]
theorem insertion_at_end (old : List Nat) (additional : Nat) :
    insert old old.length additional = old ++ List.replicate additional 0 := by simp [insert]

def reserve (old : List Nat) (position additional : Nat) (success : Bool) : List Nat :=
  if success then insert old position additional else old

theorem reserve_failure_preserves (old : List Nat) (position additional : Nat) :
    reserve old position additional false = old := rfl

#print axioms move_one_owner
#print axioms update_restored
#print axioms update_one_owner
#print axioms missing_cleanup_loses_target
#print axioms wrong_copy_duplicates_owner
#print axioms insertion_zero_budget
#print axioms insertion_at_end
#print axioms reserve_failure_preserves
end Ownership
