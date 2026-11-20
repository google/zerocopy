import ToyParMove.Cycles

/-!
Cycles with a swap primitive. `k - 1` swaps realize a `k`-cycle exactly, and no shorter swap
sequence does (from an injective store, or uniformly for all stores over a value type with two
distinct values).
-/
set_option linter.unusedSectionVars false

namespace Toy.ParMove

section SwapDefs
variable {Loc V : Type} [DecidableEq Loc]

/-- `swapStore σ a b` exchanges the contents of `a` and `b`; it is the identity when `a = b`.
Captures an exchange instruction (for example x86 `xchg reg, reg`). -/
def swapStore (σ : Loc → V) (a b : Loc) : Loc → V :=
  fun l => if l = a then σ b else if l = b then σ a else σ l

/-- Left-to-right execution of a list of swaps. -/
def runSwaps (ss : List (Loc × Loc)) (σ : Loc → V) : Loc → V :=
  ss.foldl (fun τ p => swapStore τ p.1 p.2) σ

/-- The swap realization of the cycle `l₀ :: rest`: swap `l₀` with each later element in turn
(`k - 1` swaps). -/
def cycleSwaps : List Loc → List (Loc × Loc)
  | [] => []
  | l₀ :: rest => rest.map fun x => (l₀, x)

end SwapDefs

section SwapFacts
variable {Loc V W : Type} [DecidableEq Loc]

@[simp] theorem runSwaps_nil (σ : Loc → V) : runSwaps [] σ = σ := rfl

@[simp] theorem runSwaps_cons (p : Loc × Loc) (ss : List (Loc × Loc)) (σ : Loc → V) :
    runSwaps (p :: ss) σ = runSwaps ss (swapStore σ p.1 p.2) := rfl

theorem length_cycleSwaps (ls : List Loc) : (cycleSwaps ls).length = ls.length - 1 := by
  cases ls <;> simp [cycleSwaps]

theorem swapStore_comp (f : V → W) (τ : Loc → V) (a b : Loc) :
    swapStore (f ∘ τ) a b = f ∘ swapStore τ a b := by
  funext l
  simp only [swapStore, Function.comp]
  by_cases h1 : l = a
  · rw [ite_eq_left h1, ite_eq_left h1]
  · rw [ite_eq_right h1, ite_eq_right h1]
    by_cases h2 : l = b
    · rw [ite_eq_left h2, ite_eq_left h2]
    · rw [ite_eq_right h2, ite_eq_right h2]

theorem runSwaps_comp (f : V → W) : ∀ (ss : List (Loc × Loc)) (τ : Loc → V),
    runSwaps ss (f ∘ τ) = f ∘ runSwaps ss τ
  | [], _ => rfl
  | p :: ss, τ => by
    rw [runSwaps_cons, runSwaps_cons, swapStore_comp, runSwaps_comp f ss]

/-- One step of the swap realization: swapping `l₀` with `x` first and then realizing the
shorter cycle `l₀ :: rest` realizes the cycle `l₀ :: x :: rest`. -/
theorem pmove_cycle_swap_step {l₀ x : Loc} {rest : List Loc} (hn : (l₀ :: x :: rest).Nodup)
    (σ : Loc → V) :
    pmove (cycleMoves (l₀ :: rest)) (swapStore σ l₀ x) = pmove (cycleMoves (l₀ :: x :: rest)) σ := by
  have hn1 : (l₀ :: rest).Nodup := by
    have := List.nodup_cons.1 hn
    exact List.nodup_cons.2 ⟨fun h => this.1 (List.mem_cons_of_mem _ h),
      (List.nodup_cons.1 this.2).2⟩
  have hF1 := functional_of_wellFormed (wellFormed_cycleMoves hn1)
  have hF2 := functional_of_wellFormed (wellFormed_cycleMoves hn)
  have hl₀x : l₀ ≠ x := fun e => (List.nodup_cons.1 hn).1 (by simp [e])
  have hl₀r : l₀ ∉ rest := fun h => (List.nodup_cons.1 hn).1 (List.mem_cons_of_mem _ h)
  have hxr : x ∉ rest := (List.nodup_cons.1 (List.nodup_cons.1 hn).2).1
  funext l
  by_cases h0 : l = l₀
  · subst h0
    rw [pmove_of_mem hF1 (show (l, rest.getLastD l) ∈ cycleMoves (l :: rest) by simp [cycleMoves]),
      pmove_of_mem hF2 (show (l, rest.getLastD x) ∈ cycleMoves (l :: x :: rest) by
        show (l, rest.getLastD x) ∈ (l, (x :: rest).getLastD l) :: chain l (x :: rest)
        rw [List.getLastD_cons]; exact List.mem_cons_self ..)]
    cases rest with
    | nil => simp [swapStore]
    | cons y ys =>
      simp only [List.getLastD_cons]
      have hm : ys.getLastD y ∈ y :: ys := List.getLastD_mem_cons
      have h1 : ys.getLastD y ≠ l := fun e => hl₀r (e ▸ hm)
      have h2 : ys.getLastD y ≠ x := fun e => hxr (e ▸ hm)
      simp only [swapStore, h1, h2, ite_false]
  · by_cases hx : l = x
    · subst hx
      rw [pmove_of_not_mem_dsts (by rw [dsts_cycleMoves]; simp [Ne.symm hl₀x, hxr]),
        pmove_of_mem hF2 (show (l, l₀) ∈ cycleMoves (l₀ :: l :: rest) by simp [cycleMoves, chain])]
      simp [swapStore, h0]
    · cases rest with
      | nil =>
        rw [pmove_of_not_mem_dsts (by rw [dsts_cycleMoves]; simp [h0]),
          pmove_of_not_mem_dsts (by rw [dsts_cycleMoves]; simp [h0, hx])]
        simp [swapStore, h0, hx]
      | cons y ys =>
        by_cases hy : l = y
        · subst hy
          rw [pmove_of_mem hF1 (show (l, l₀) ∈ cycleMoves (l₀ :: l :: ys) by
                simp [cycleMoves, chain]),
            pmove_of_mem hF2 (show (l, x) ∈ cycleMoves (l₀ :: x :: l :: ys) by
                simp [cycleMoves, chain])]
          simp [swapStore]
        · by_cases hys : l ∈ dsts (chain y ys)
          · obtain ⟨s, hs⟩ := mem_dsts.1 hys
            have hsm : s ∈ y :: ys := srcs_chain_subset y ys (mem_srcs.2 ⟨l, hs⟩)
            have hs0 : s ≠ l₀ := fun e => hl₀r (e ▸ hsm)
            have hsx : s ≠ x := fun e => hxr (e ▸ hsm)
            rw [pmove_of_mem hF1 (show (l, s) ∈ cycleMoves (l₀ :: y :: ys) by
                  simp [cycleMoves, chain, hs]),
              pmove_of_mem hF2 (show (l, s) ∈ cycleMoves (l₀ :: x :: y :: ys) by
                  simp [cycleMoves, chain, hs])]
            simp [swapStore, hs0, hsx]
          · rw [dsts_chain] at hys
            rw [pmove_of_not_mem_dsts (by rw [dsts_cycleMoves]; simp [h0, hy, hys]),
              pmove_of_not_mem_dsts (by rw [dsts_cycleMoves]; simp [h0, hx, hy, hys])]
            simp [swapStore, h0, hx]

/-- **Upper bound with swaps: `k - 1` swaps.** For a duplicate-free cycle `ls`, the `k - 1`
swaps of `cycleSwaps ls` realize the cycle exactly (at every location, from every store). -/
theorem runSwaps_cycleSwaps {ls : List Loc} (hn : ls.Nodup) (σ : Loc → V) :
    runSwaps (cycleSwaps ls) σ = pmove (cycleMoves ls) σ := by
  cases ls with
  | nil => rfl
  | cons l₀ rest =>
    induction rest generalizing σ with
    | nil =>
      funext l
      by_cases h : l = l₀ <;> simp [cycleSwaps, cycleMoves, chain, pmove, lookupSrc, h]
    | cons x rest ih =>
      have hn1 : (l₀ :: rest).Nodup := by
        have := List.nodup_cons.1 hn
        exact List.nodup_cons.2 ⟨fun h => this.1 (List.mem_cons_of_mem _ h),
          (List.nodup_cons.1 this.2).2⟩
      show runSwaps ((l₀, x) :: cycleSwaps (l₀ :: rest)) σ = _
      rw [runSwaps_cons, ih _ hn1, pmove_cycle_swap_step hn]

end SwapFacts

/-! ### Lower bound with swaps: a union-find potential -/

section UnionFind
variable {Loc V : Type} [DecidableEq Loc]

/-- Union-find step: merge the class of `p.1` into the class of `p.2` (classes are labelled by
representatives `r x`). -/
def ufMerge (r : Loc → Loc) (p : Loc × Loc) : Loc → Loc :=
  fun x => if r x = r p.1 then r p.2 else r x

def ufRun (ss : List (Loc × Loc)) (r : Loc → Loc) : Loc → Loc := ss.foldl ufMerge r

/-- A value can only travel along swap edges: the class of the location a value came from is the
class of the location holding it. -/
theorem ufRun_invariant : ∀ (ss : List (Loc × Loc)) (τ r : Loc → Loc), (∀ l, r (τ l) = r l) →
    ∀ l, ufRun ss r (runSwaps ss τ l) = ufRun ss r l
  | [], _, _, h => h
  | p :: ss, τ, r, h => by
    apply ufRun_invariant ss (swapStore τ p.1 p.2) (ufMerge r p)
    intro l
    by_cases ha : l = p.1
    · have e : swapStore τ p.1 p.2 l = τ p.2 := by simp [swapStore, ha]
      rw [e]
      simp only [ufMerge, h, ha, ite_true]
      by_cases hb : r p.2 = r p.1 <;> simp [hb]
    · by_cases hb : l = p.2
      · have e : swapStore τ p.1 p.2 l = τ p.1 := by
          rw [hb]; simp [swapStore, show p.2 ≠ p.1 from fun e => ha (hb.trans e)]
        rw [e]
        simp only [ufMerge, h, hb, ite_true]
        by_cases hb' : r p.2 = r p.1 <;> simp [hb']
      · have e : swapStore τ p.1 p.2 l = τ l := by simp [swapStore, ha, hb]
        rw [e]
        simp only [ufMerge, h]

theorem dedupL_eq_self {α : Type} [DecidableEq α] : ∀ {l : List α}, l.Nodup → dedupL l = l
  | [], _ => rfl
  | a :: l, h => by
    have h' := List.nodup_cons.1 h
    simp [dedupL, h'.1, dedupL_eq_self h'.2]

theorem length_dedupL_le_map_merge (L : List Loc) (p q : Loc) :
    (dedupL L).length ≤ (dedupL (L.map fun y => if y = p then q else y)).length + 1 := by
  have hsub : dedupL L ⊆ p :: dedupL (L.map fun y => if y = p then q else y) := by
    intro y hy
    by_cases e : y = p
    · simp [e]
    · refine List.mem_cons_of_mem _ (mem_dedupL.2 (List.mem_map.2 ⟨y, mem_dedupL.1 hy, ?_⟩))
      simp [e]
  have := length_le_of_nodup_of_subset (nodup_dedupL L) hsub
  simpa using this

theorem length_dedupL_ufRun : ∀ (ss : List (Loc × Loc)) (r : Loc → Loc) (ls : List Loc),
    (dedupL (ls.map r)).length ≤ (dedupL (ls.map (ufRun ss r))).length + ss.length
  | [], _, _ => by simp [ufRun]
  | p :: ss, r, ls => by
    have h1 : ls.map (ufMerge r p) = (ls.map r).map (fun y => if y = r p.1 then r p.2 else y) := by
      simp [ufMerge, List.map_map, Function.comp_def]
    have h2 := length_dedupL_le_map_merge (ls.map r) (r p.1) (r p.2)
    have h3 := length_dedupL_ufRun ss (ufMerge r p) ls
    rw [h1] at h3
    have e : ufRun (p :: ss) r = ufRun ss (ufMerge r p) := rfl
    rw [e, List.length_cons]
    omega

theorem length_dedupL_le_one_of_const {L : List Loc} {c : Loc} (h : ∀ x ∈ L, x = c) :
    (dedupL L).length ≤ 1 := by
  have hsub : dedupL L ⊆ [c] := fun y hy => by simp [h y (mem_dedupL.1 hy)]
  simpa using length_le_of_nodup_of_subset (nodup_dedupL L) hsub

theorem chain_connected (R : Loc → Loc) : ∀ (h : Loc) (ys : List Loc),
    (∀ m ∈ chain h ys, R m.1 = R m.2) → ∀ x ∈ ys, R x = R h
  | _, [], _ => by simp
  | h, y :: ys, hc => by
    have hy : R y = R h := hc (y, h) (by simp [chain])
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hy
    · rw [chain_connected R y ys (fun m hm => hc m (by simp [chain, hm])) x hx, hy]

/-- **Lower bound with swaps: `k - 1` swaps.** For a duplicate-free cycle `ls` of length `k`
and an injective store `σ`, any list of swaps that turns `σ` into the cycle's target (at every
location) has at least `k - 1` swaps. -/
theorem cycle_length_sub_one_le_of_injective_of_runSwaps {ls : List Loc} {σ : Loc → V}
    {ss : List (Loc × Loc)} (hn : ls.Nodup) (hσ : Function.Injective σ)
    (hreal : runSwaps ss σ = pmove (cycleMoves ls) σ) : ls.length - 1 ≤ ss.length := by
  have hF := functional_of_wellFormed (wellFormed_cycleMoves hn)
  -- Reduce to the identity store.
  have hid : runSwaps ss (id : Loc → Loc) = pmove (cycleMoves ls) id := by
    have e1 : runSwaps ss σ = σ ∘ runSwaps ss id := runSwaps_comp σ ss id
    have e2 : pmove (cycleMoves ls) σ = σ ∘ pmove (cycleMoves ls) id := pmove_comp σ _ id
    funext l
    exact hσ (by have := congrFun (e1.symm.trans (hreal.trans e2)) l; exact this)
  let R := ufRun ss (id : Loc → Loc)
  have hinv : ∀ l, R (runSwaps ss id l) = R l := ufRun_invariant ss id id (fun _ => rfl)
  have hedge : ∀ m ∈ cycleMoves ls, R m.1 = R m.2 := by
    intro m hm
    have := hinv m.1
    rw [hid, pmove_of_mem hF (show (m.1, m.2) ∈ cycleMoves ls from hm)] at this
    exact this.symm
  cases ls with
  | nil => simp
  | cons l₀ rest =>
    have hall : ∀ x ∈ (l₀ :: rest).map R, x = R l₀ := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      rcases List.mem_cons.1 hy with rfl | hy
      · rfl
      · exact chain_connected R l₀ rest (fun m hm => hedge m (by simp [cycleMoves, hm])) y hy
    have h1 : (dedupL ((l₀ :: rest).map (ufRun ss id))).length ≤ 1 :=
      length_dedupL_le_one_of_const hall
    have h2 := length_dedupL_ufRun ss id (l₀ :: rest)
    rw [List.map_id, dedupL_eq_self hn] at h2
    simp only [List.length_cons] at h2 ⊢
    omega

/-- A swap sequence that realizes `M` from the identity store on locations realizes `M` from
every store. -/
theorem runSwaps_eq_pmove_of_id {ss M : List (Loc × Loc)}
    (h : runSwaps ss (id : Loc → Loc) = pmove M id) (σ : Loc → V) :
    runSwaps ss σ = pmove M σ := by
  have e1 := runSwaps_comp σ ss id
  have e2 := pmove_comp σ M id
  simp only [Function.comp_id] at e1 e2
  rw [e1, e2, h]

/-- **Lower bound with swaps, uniformly in the store.** Over a value type with two distinct
values, any list of swaps that turns every store into the target of a duplicate-free cycle of
length `k` has at least `k - 1` swaps. -/
theorem cycle_length_sub_one_le_of_two_values_of_runSwaps {ls : List Loc}
    {ss : List (Loc × Loc)} (a b : V) (hab : a ≠ b) (hn : ls.Nodup)
    (hreal : ∀ σ : Loc → V, runSwaps ss σ = pmove (cycleMoves ls) σ) :
    ls.length - 1 ≤ ss.length := by
  apply cycle_length_sub_one_le_of_injective_of_runSwaps (V := Loc) (σ := id) hn (fun _ _ h => h)
  funext l
  apply eq_of_forall_store a b hab
  intro σ
  have e1 := congrFun (runSwaps_comp σ ss id) l
  have e2 := congrFun (pmove_comp σ (cycleMoves ls) id) l
  simp only [Function.comp_id, Function.comp] at e1 e2
  rw [← e1, ← e2]
  exact congrFun (hreal σ) l

end UnionFind

/-! ### Definition examples (`swapStore`, `runSwaps`, `cycleSwaps`) -/

/-- Positive example (`swapStore`): exchanging `0` and `1` leaves `2` alone; a swap is not a
copy (the plain move `0 := 1` leaves the old value of `1` at `1`). -/
theorem swapStore_example :
    swapStore (id : Nat → Nat) 0 1 0 = 1 ∧ swapStore (id : Nat → Nat) 0 1 1 = 0 ∧
    swapStore (id : Nat → Nat) 0 1 2 = 2 ∧
    swapStore (id : Nat → Nat) 0 1 1 ≠ upd (id : Nat → Nat) 0 1 1 := by decide

/-- Positive example (`cycleSwaps`, `runSwaps`): the two swaps of the 3-cycle on `[0,1,2]`
produce the cycle's target. -/
theorem cycleSwaps_example :
    cycleSwaps ([0, 1, 2] : List Nat) = [(0, 1), (0, 2)] ∧
    (runSwaps [((0 : Nat), (1 : Nat)), (0, 2)] (id : Nat → Nat) 0 = 2 ∧
      runSwaps [((0 : Nat), (1 : Nat)), (0, 2)] (id : Nat → Nat) 1 = 0 ∧
      runSwaps [((0 : Nat), (1 : Nat)), (0, 2)] (id : Nat → Nat) 2 = 1) := by decide

/-- Negative example (`runSwaps`): the same two swaps in the other order give a different
permutation. -/
theorem runSwaps_order_matters :
    runSwaps [((0 : Nat), (2 : Nat)), (0, 1)] (id : Nat → Nat) 0 ≠
      runSwaps [((0 : Nat), (1 : Nat)), (0, 2)] (id : Nat → Nat) 0 := by decide

/-- At `k = 0` the bound `ls.length - 1` is `0` by truncated subtraction. -/
theorem length_cycleSwaps_nil :
    (cycleSwaps ([] : List Nat)).length = 0 ∧ ([] : List Nat).length - 1 = 0 := by decide

end Toy.ParMove
