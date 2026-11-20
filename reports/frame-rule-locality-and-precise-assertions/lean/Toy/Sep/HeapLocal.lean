import Toy.Sep.NonLocal

/-!
# Standard heap commands are local

Lookup, mutation, allocation (with a nondeterministically chosen fresh address,
with or without recording that address) and deallocation are all
safety-monotone and have the frame property. Contrast with `allocAt`,
`allocLeast`, `isAllocTest` in `Toy.Sep.NonLocal`.
-/

namespace Toy.Sep

variable {V : Type}

/-- **Lookup `[r] := [k]` is local.** -/
theorem lookup_safetyMono_and_frameProp (k r : Nat) :
    SafetyMono (lookup (V := V) k r) ∧ FrameProp (lookup (V := V) k r) := by
  refine ⟨fun h h' _ hs => ?_, fun h h' h'' hd hs hrun => ?_⟩
  · rw [safe_lookup_iff] at hs ⊢
    exact ⟨by rw [Heap.union_val_of_ne_none hs.1]; exact hs.1,
           by rw [Heap.union_val_of_ne_none hs.2]; exact hs.2⟩
  · rw [safe_lookup_iff] at hs
    rcases hrun with ⟨_, hf⟩ | ⟨_, _, he⟩
    · cases hf
    · injection he with he
      have h'r := Heap.right_none_of_disj hd hs.2
      have hvk := Heap.union_val_of_ne_none (h' := h') hs.1
      refine ⟨h.set r (h.val k), Or.inr ⟨hs.1, hs.2, rfl⟩, fun j => ?_, ?_⟩
      · by_cases hj : j = r
        · subst hj; exact Or.inr h'r
        · simp only [Heap.set_val, hj, ite_false]; exact hd j
      · rw [he, hvk]; exact (Heap.set_join h'r _).symm

/-- **Mutation `[k] := v` is local.** -/
theorem mutate_safetyMono_and_frameProp (k : Nat) (v : V) :
    SafetyMono (mutate k v) ∧ FrameProp (mutate k v) := by
  refine ⟨fun h h' _ hs => ?_, fun h h' h'' hd hs hrun => ?_⟩
  · rw [safe_mutate_iff] at hs ⊢
    rw [Heap.union_val_of_ne_none hs]; exact hs
  · rw [safe_mutate_iff] at hs
    rcases hrun with ⟨_, hf⟩ | ⟨_, he⟩
    · cases hf
    · injection he with he
      have h'k := Heap.right_none_of_disj hd hs
      refine ⟨h.set k (some v), Or.inr ⟨hs, rfl⟩, fun j => ?_, ?_⟩
      · by_cases hj : j = k
        · subst hj; exact Or.inr h'k
        · simp only [Heap.set_val, hj, ite_false]; exact hd j
      · rw [he]; exact (Heap.set_join h'k _).symm

/-- **Allocation at a nondeterministically chosen fresh address is local.** The
nondeterminism is essential: the deterministic variant `allocLeast` violates the
frame property (`Toy.Sep.allocLeast_not_frameProp`). Since `alloc` never faults,
this is an immediate consequence of `Toy.Sep.alloc_frameProp`. -/
theorem alloc_safetyMono_and_frameProp (v : V) :
    SafetyMono (alloc v) ∧ FrameProp (alloc v) :=
  ⟨fun _ _ _ _ => safe_alloc v _, alloc_frameProp v⟩

/-- **Allocation recording the fresh address in cell `r` (`[r] := cons(v)`) is
local.** Heap values are `Nat` here, so that an address can be stored in a cell. -/
theorem allocInto_safetyMono_and_frameProp (r v : Nat) :
    SafetyMono (allocInto r v) ∧ FrameProp (allocInto r v) := by
  refine ⟨fun h h' _ hs => ?_, fun h h' h'' hd hs hrun => ?_⟩
  · rw [safe_allocInto_iff] at hs ⊢
    rw [Heap.union_val_of_ne_none hs]; exact hs
  · rw [safe_allocInto_iff] at hs
    rcases hrun with ⟨_, hf⟩ | ⟨_, k, hk, he⟩
    · cases hf
    · injection he with he
      simp only [Heap.union_eq, Heap.join_val] at hk
      have hk1 : h.val k = none := by cases e : h.val k <;> simp_all
      have hk2 : h'.val k = none := by rw [hk1] at hk; simpa using hk
      have h'r := Heap.right_none_of_disj hd hs
      refine ⟨(h.set k (some v)).set r (some k), Or.inr ⟨hs, k, hk1, rfl⟩, fun j => ?_, ?_⟩
      · by_cases hjr : j = r
        · subst hjr; exact Or.inr h'r
        · by_cases hjk : j = k
          · subst hjk; exact Or.inr hk2
          · simp only [Heap.set_val, hjr, hjk, ite_false]; exact hd j
      · rw [he]; simp only [Heap.union_eq]; rw [Heap.set_join h'r, Heap.set_join hk2]

/-- **Deallocation `free k` is local.** -/
theorem free_safetyMono_and_frameProp (k : Nat) :
    SafetyMono (free (V := V) k) ∧ FrameProp (free (V := V) k) := by
  refine ⟨fun h h' _ hs => ?_, fun h h' h'' hd hs hrun => ?_⟩
  · rw [safe_free_iff] at hs ⊢
    rw [Heap.union_val_of_ne_none hs]; exact hs
  · rw [safe_free_iff] at hs
    rcases hrun with ⟨_, hf⟩ | ⟨_, he⟩
    · cases hf
    · injection he with he
      have h'k := Heap.right_none_of_disj hd hs
      refine ⟨h.set k none, Or.inr ⟨hs, rfl⟩, fun j => ?_, ?_⟩
      · by_cases hj : j = k
        · subst hj; exact Or.inr h'k
        · simp only [Heap.set_val, hj, ite_false]; exact hd j
      · rw [he]; exact (Heap.set_join h'k _).symm

end Toy.Sep
