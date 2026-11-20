import ToyParMove.Swaps

/-!
The xor-swap idiom `a ^= b; b ^= a; a ^= b` over `w`-bit words. It exchanges `a` and `b` when
they are distinct locations and zeroes the location when they alias, so it is a correct swap
primitive exactly for distinct operands (or an aliased operand that holds zero).
-/
set_option linter.unusedSectionVars false

namespace Toy.ParMove

section XorDefs
variable {Loc : Type} [DecidableEq Loc] {w : Nat}

/-- `a ^= b`: xor the current contents of `b` into `a`. -/
def xorAssign (σ : Loc → BitVec w) (a b : Loc) : Loc → BitVec w := upd σ a (σ a ^^^ σ b)

/-- The **xor-swap** idiom `a ^= b; b ^= a; a ^= b`. -/
def xorSwap (σ : Loc → BitVec w) (a b : Loc) : Loc → BitVec w :=
  xorAssign (xorAssign (xorAssign σ a b) b a) a b

/-- Left-to-right execution of a list of swaps, each implemented by the xor-swap idiom. -/
def runXorSwaps (ss : List (Loc × Loc)) (σ : Loc → BitVec w) : Loc → BitVec w :=
  ss.foldl (fun τ p => xorSwap τ p.1 p.2) σ

end XorDefs

section XorFacts
variable {Loc : Type} [DecidableEq Loc] {w : Nat}

/-- **Xor-swap on distinct locations is a swap.** -/
theorem xorSwap_eq_swapStore_of_ne {a b : Loc} (hab : a ≠ b) (σ : Loc → BitVec w) :
    xorSwap σ a b = swapStore σ a b := by
  funext l
  have hba : b ≠ a := Ne.symm hab
  by_cases ha : l = a
  · subst ha
    simp only [xorSwap, xorAssign, upd, swapStore, hab, hba, ite_true, ite_false]
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp only [BitVec.getLsbD_xor]
    cases (σ l).getLsbD i <;> cases (σ b).getLsbD i <;> rfl
  · by_cases hb : l = b
    · subst hb
      simp only [xorSwap, xorAssign, upd, swapStore, hab, hba, ite_true, ite_false]
      apply BitVec.eq_of_getLsbD_eq
      intro i _
      simp only [BitVec.getLsbD_xor]
      cases (σ a).getLsbD i <;> cases (σ l).getLsbD i <;> rfl
    · simp [xorSwap, xorAssign, upd, swapStore, ha, hb]

/-- **Xor-swap on an aliased location zeroes it** (and leaves every other location alone). -/
theorem xorSwap_self (σ : Loc → BitVec w) (a : Loc) : xorSwap σ a a = upd σ a 0#w := by
  funext l
  by_cases ha : l = a
  · subst ha; simp [xorSwap, xorAssign, upd]
  · simp [xorSwap, xorAssign, upd, ha]

/-- **Characterization.** The xor-swap of `a` and `b` agrees with the true swap iff the operands
are distinct locations or the aliased (common) operand holds zero. -/
theorem xorSwap_eq_swapStore_iff (σ : Loc → BitVec w) (a b : Loc) :
    xorSwap σ a b = swapStore σ a b ↔ (a ≠ b ∨ σ a = 0#w) := by
  constructor
  · intro h
    by_cases hab : a = b
    · subst hab
      right
      have := congrFun h a
      rw [xorSwap_self] at this
      simp [swapStore] at this
      exact this.symm
    · exact Or.inl hab
  · rintro (hab | h0)
    · exact xorSwap_eq_swapStore_of_ne hab σ
    · by_cases hab : a = b
      · subst hab
        rw [xorSwap_self]
        funext l
        by_cases hl : l = a
        · subst hl; simp [swapStore, h0]
        · simp [upd, swapStore, hl]
      · exact xorSwap_eq_swapStore_of_ne hab σ

/-- **Xor-swap sequences are swap sequences when no swap is a self-swap.** -/
theorem runXorSwaps_eq_runSwaps_of_no_self :
    ∀ {ss : List (Loc × Loc)}, (∀ p ∈ ss, p.1 ≠ p.2) → ∀ σ : Loc → BitVec w,
      runXorSwaps ss σ = runSwaps ss σ
  | [], _, _ => rfl
  | p :: ss, h, σ => by
    show runXorSwaps ss (xorSwap σ p.1 p.2) = runSwaps ss (swapStore σ p.1 p.2)
    rw [xorSwap_eq_swapStore_of_ne (h p (List.mem_cons_self ..))]
    exact runXorSwaps_eq_runSwaps_of_no_self (fun q hq => h q (List.mem_cons_of_mem _ hq)) _

theorem cycleSwaps_no_self {ls : List Loc} (hn : ls.Nodup) : ∀ p ∈ cycleSwaps ls, p.1 ≠ p.2 := by
  cases ls with
  | nil => simp [cycleSwaps]
  | cons l₀ rest =>
    intro p hp
    simp only [cycleSwaps, List.mem_map] at hp
    obtain ⟨x, hx, rfl⟩ := hp
    intro e
    have e' : l₀ = x := e
    exact (List.nodup_cons.1 hn).1 (e' ▸ hx)

/-- Corollary: the xor-swap implementation of the `k - 1` cycle swaps realizes a duplicate-free
cycle. -/
theorem runXorSwaps_cycleSwaps {ls : List Loc} (hn : ls.Nodup) (σ : Loc → BitVec w) :
    runXorSwaps (cycleSwaps ls) σ = pmove (cycleMoves ls) σ := by
  rw [runXorSwaps_eq_runSwaps_of_no_self (cycleSwaps_no_self hn), runSwaps_cycleSwaps hn]

end XorFacts

/-! ### Tightness, counterexamples, non-vacuity for the xor-swap results -/

/-- Illustration in parallel-swap form: a parallel swap `[(a,b),(b,a)]` whose operands were
allocated to the same register `0` means "leave register 0 alone", and so does the true swap, but
the xor-swap idiom zeroes it. -/
theorem xorSwap_unsafe_for_aliased_parallel_swap :
    pmove [((0 : Nat), (0 : Nat)), (0, 0)] (fun _ : Nat => (1#8 : BitVec 8)) 0 = 1#8 ∧
    swapStore (fun _ : Nat => (1#8 : BitVec 8)) 0 0 0 = 1#8 ∧
    xorSwap (fun _ : Nat => (1#8 : BitVec 8)) 0 0 0 = 0#8 :=
  ⟨by decide, by decide, by decide⟩

/-- Counterexample (hypothesis `a ≠ b` of `xorSwap_eq_swapStore_of_ne`): the operands alias and
the conclusion fails. -/
theorem xorSwap_eq_swapStore_needs_ne :
    ¬ ((0 : Nat) ≠ 0) ∧
    xorSwap (fun _ : Nat => (1#8 : BitVec 8)) 0 0 ≠ swapStore (fun _ : Nat => (1#8 : BitVec 8)) 0 0 :=
  ⟨fun h => h rfl, fun h => absurd (congrFun h 0) (by decide)⟩

/-- Counterexample (hypothesis "no self-swap" of `runXorSwaps_eq_runSwaps_of_no_self`). -/
theorem runXorSwaps_needs_no_self :
    ¬ (∀ p ∈ [((0 : Nat), (0 : Nat))], p.1 ≠ p.2) ∧
    runXorSwaps [((0 : Nat), (0 : Nat))] (fun _ : Nat => (1#8 : BitVec 8)) ≠
      runSwaps [(0, 0)] (fun _ : Nat => (1#8 : BitVec 8)) :=
  ⟨by decide, fun h => absurd (congrFun h 0) (by decide)⟩

/-- Counterexample (hypothesis `Nodup` of `runXorSwaps_cycleSwaps`): for the list `[0,1,0]` the
swap list contains the self-swap `(0,0)`, which the xor-swap idiom turns into a zeroing. -/
theorem runXorSwaps_cycleSwaps_needs_nodup :
    ¬ ([0, 1, 0] : List Nat).Nodup ∧
    runXorSwaps (cycleSwaps [0, 1, 0]) (fun l : Nat => if l = 0 then 1#8 else 2#8) ≠
      pmove (cycleMoves [0, 1, 0]) (fun l : Nat => if l = 0 then 1#8 else 2#8) ∧
    runXorSwaps (cycleSwaps [0, 1, 0]) (fun l : Nat => if l = 0 then 1#8 else 2#8) 0 = 0#8 ∧
    pmove (cycleMoves [0, 1, 0]) (fun l : Nat => if l = 0 then 1#8 else 2#8) 0 = 1#8 :=
  ⟨by decide, fun h => absurd (congrFun h 0) (by decide), by decide, by decide⟩

/-- Non-vacuity of `xorSwap_eq_swapStore_of_ne`: concrete 8-bit values at distinct locations. -/
theorem nonvacuity_xorSwap :
    (0 : Nat) ≠ 1 ∧
    xorSwap (fun l : Nat => if l = 0 then 0x5A#8 else 0xC3#8) 0 1 0 = 0xC3#8 ∧
    xorSwap (fun l : Nat => if l = 0 then 0x5A#8 else 0xC3#8) 0 1 1 = 0x5A#8 :=
  ⟨by decide, by decide, by decide⟩

/-- Non-vacuity of `runXorSwaps_eq_runSwaps_of_no_self` and of `runXorSwaps_cycleSwaps`. -/
theorem nonvacuity_runXorSwaps :
    (∀ p ∈ [((0 : Nat), (1 : Nat)), (0, 2)], p.1 ≠ p.2) ∧ ([0, 1, 2] : List Nat).Nodup := by
  decide

/-- Non-claim witness: at width `0` every word is `0#0`, so the aliased xor-swap is harmless. -/
theorem xorSwap_eq_swapStore_width_zero (σ : Nat → BitVec 0) (a b : Nat) :
    xorSwap σ a b = swapStore σ a b :=
  (xorSwap_eq_swapStore_iff σ a b).2 (Or.inr (Subsingleton.elim _ _))

/-! ### Definition examples (`xorSwap`, `runXorSwaps`) -/

/-- Positive example (`xorSwap`, `runXorSwaps`): distinct operands are exchanged; a list of two
xor-swaps realizes the 3-cycle on `[0,1,2]` at location `0`. -/
theorem xorSwap_examples :
    xorSwap (fun l : Nat => if l = 0 then 0x5A#8 else 0xC3#8) 0 1 0 = 0xC3#8 ∧
    runXorSwaps [((0 : Nat), (1 : Nat)), (0, 2)]
      (fun l : Nat => if l = 0 then 1#8 else if l = 1 then 2#8 else 3#8) 0 = 3#8 := by decide

/-- Negative example (`xorSwap`): an aliased operand holding a nonzero value is zeroed rather
than left unchanged. -/
theorem xorSwap_alias_example :
    xorSwap (fun _ : Nat => (1#8 : BitVec 8)) 0 0 0 = 0#8 := by decide

end Toy.ParMove
