import ToyMonitor.Monitor

/-!
# Concrete instances, and positive / negative examples for every definition

All examples are fully proved.
-/

namespace Toy.Monitor

open Assn

/-! ## Concrete heaps, contracts, and programs used throughout -/

/-- Two allocated bytes, at addresses `0` and `1`, both holding `0`. -/
def hTwo : Heap
  | 0 => some 0
  | 1 => some 0
  | _ => none

/-- One allocated byte, at address `0`, holding `0`. -/
def hOne : Heap := Heap.single 0 0

/-- The imprecise contract `owned 0 ∨ owned 1`. -/
def C : Assn := .or (owned 0) (owned 1)

/-- A precise contract that is not disjunction-precise:
`((owned 0 ∗ owned 1) ∨ owned 0) ∗ owned 1`. In any heap its only possible witness is
the two-cell fragment on `{0, 1}` (split as `owned 0` | `owned 1`), but its inner
disjunction is imprecise. -/
def C' : Assn := .sep (.or (.sep (owned 0) (owned 1)) (owned 0)) (owned 1)

/-- Callee with contract `C`/`C` that reads byte `0`. -/
def runL : Prog := .call C C (.read 0)

/-- Callee with contract `C`/`C` that reads byte `1`. -/
def runR : Prog := .call C C (.read 1)

/-- A callee with contract `C'`/`C'` that does nothing. -/
def runP : Prog := .call C' C' .skip

/-- A strategy that always proposes `[0]` regardless of the contract (unsound). -/
def sBad : Strategy := fun _ _ => some [0]

/-- A strategy that always proposes `[0, 1]` regardless of the contract (unsound). -/
def sAll : Strategy := fun _ _ => some [0, 1]

/-! ## Small helper facts -/

@[simp] theorem hTwo_zero : hTwo 0 = some 0 := rfl
@[simp] theorem hTwo_one : hTwo 1 = some 0 := rfl
theorem hTwo_of_ne (a : Addr) (h0 : a ≠ 0) (h1 : a ≠ 1) : hTwo a = none := by
  match a, h0, h1 with
  | 0, h, _ => exact absurd rfl h
  | 1, _, h => exact absurd rfl h
  | _ + 2, _, _ => rfl

/-- The one-cell fragment at `0` is a sub-fragment of `hTwo`. -/
theorem sub_single0_hTwo : Heap.Sub (Heap.single 0 0) hTwo := by
  intro a v h
  by_cases ha : a = 0
  · subst ha
    simp [Heap.single] at h
    subst h; rfl
  · simp [Heap.single, ha] at h

/-- The one-cell fragment at `1` is a sub-fragment of `hTwo`. -/
theorem sub_single1_hTwo : Heap.Sub (Heap.single 1 0) hTwo := by
  intro a v h
  by_cases ha : a = 1
  · subst ha
    simp [Heap.single] at h
    subst h; rfl
  · simp [Heap.single, ha] at h

@[simp] theorem Heap.restrict_apply (g : Heap) (F : List Addr) (a : Addr) :
    g.restrict F a = if a ∈ F then g a else none := rfl

@[simp] theorem Heap.remove_apply (g : Heap) (F : List Addr) (a : Addr) :
    g.remove F a = if a ∈ F then none else g a := rfl

@[simp] theorem Heap.single_apply (p : Addr) (v : Val) (a : Addr) :
    Heap.single p v a = if a = p then some v else none := rfl

@[simp] theorem Heap.union_apply (g₁ g₂ : Heap) (a : Addr) :
    Heap.union g₁ g₂ a = (match g₁ a with | some v => some v | none => g₂ a) := rfl

/-- `owned p` holds exactly of fragments with one cell, at `p`. -/
theorem sat_owned_iff (p : Addr) (g : Heap) :
    sat (owned p) g ↔ (g p).isSome = true ∧ ∀ a, a ≠ p → g a = none := by
  simp only [owned, sat]
  constructor
  · rintro ⟨v, hv, -, hrest⟩
    exact ⟨by simp [hv], hrest⟩
  · rintro ⟨hs, hrest⟩
    cases hgp : g p with
    | none => simp [hgp] at hs
    | some v => exact ⟨v, rfl, by simp, hrest⟩

/-! ## `sat` -/

/-- Positive: `pointsTo 0 3` holds of the one-cell fragment `0 ↦ 3`. -/
theorem sat_pointsTo_single : sat (pointsTo 0 3) (Heap.single 0 3) := by
  refine ⟨3, by simp, by decide, ?_⟩
  intro a ha
  simp [ha]

/-- Positive: `owned 0 ∗ owned 1` holds of `hTwo`. -/
theorem sat_owned0_sep_owned1_hTwo : sat (.sep (owned 0) (owned 1)) hTwo := by
  refine ⟨Heap.single 0 0, Heap.single 1 0, ?_, ?_, ?_, ?_⟩
  · intro a
    by_cases h : a = 0 <;> simp [h]
  · intro a
    by_cases h0 : a = 0
    · subst h0; rfl
    · by_cases h1 : a = 1
      · subst h1; rfl
      · simp [h0, h1, hTwo_of_ne a h0 h1]
  · exact (sat_owned_iff 0 _).2 ⟨rfl, fun a ha => by simp [ha]⟩
  · exact (sat_owned_iff 1 _).2 ⟨rfl, fun a ha => by simp [ha]⟩

/-- Negative: no fragment satisfies `owned 0 ∗ owned 0` (ownership is exclusive). -/
theorem not_sat_owned0_sep_owned0 (g : Heap) : ¬ sat (.sep (owned 0) (owned 0)) g := by
  rintro ⟨g₁, g₂, hdisj, -, h₁, h₂⟩
  have h1 := ((sat_owned_iff 0 g₁).1 h₁).1
  have h2 := ((sat_owned_iff 0 g₂).1 h₂).1
  rcases hdisj 0 with h | h <;> simp [h] at h1 h2

/-- Negative: exactness — `owned 0` does not hold of the two-cell fragment `hTwo`. -/
theorem not_sat_owned0_hTwo : ¬ sat (owned 0) hTwo := by
  intro h
  have := ((sat_owned_iff 0 hTwo).1 h).2 1 (by decide)
  simp at this

/-! ## `SepP` -/

/-- Positive: `hTwo` splits as `owned 0` ∗ `owned 1`. -/
theorem sepP_owned0_owned1_hTwo : SepP (sat (owned 0)) (sat (owned 1)) hTwo :=
  sat_owned0_sep_owned1_hTwo

/-- Negative: no fragment splits as `owned 0` ∗ `owned 0`. -/
theorem not_sepP_owned0_owned0 (g : Heap) : ¬ SepP (sat (owned 0)) (sat (owned 0)) g :=
  not_sat_owned0_sep_owned0 g

/-! ## `IsFootprint` -/

/-- Positive: `[0]` is a footprint of `owned 0` in `hTwo`. -/
theorem isFootprint_owned0_hTwo : IsFootprint (owned 0) hTwo [0] := by
  refine ⟨by decide, (sat_owned_iff 0 _).2 ⟨rfl, fun a ha => by simp [ha]⟩⟩

/-- Negative: `[0, 1]` is not a footprint of `owned 0` in `hTwo` (too large). -/
theorem not_isFootprint_owned0_hTwo_01 : ¬ IsFootprint (owned 0) hTwo [0, 1] := by
  rintro ⟨-, h⟩
  have := ((sat_owned_iff 0 _).1 h).2 1 (by decide)
  simp at this

/-- Negative: `[2]` is not a footprint of `owned 2` in `hTwo` (byte 2 is unallocated). -/
theorem not_isFootprint_owned2_hTwo : ¬ IsFootprint (owned 2) hTwo [2] := by
  rintro ⟨h, -⟩
  have := h 2 (by simp)
  simp [hTwo_of_ne 2 (by decide) (by decide)] at this

/-! ## `Precise` and `DisjPrecise` -/

/-- Positive: `owned p` is precise. -/
theorem precise_owned (p : Addr) : Precise (owned p) := by
  intro g g₁ g₂ hs₁ hs₂ h₁ h₂
  obtain ⟨hp₁, hr₁⟩ := (sat_owned_iff p g₁).1 h₁
  obtain ⟨hp₂, hr₂⟩ := (sat_owned_iff p g₂).1 h₂
  funext a
  by_cases ha : a = p
  · subst ha
    cases e₁ : g₁ a with
    | none => simp [e₁] at hp₁
    | some v₁ =>
      cases e₂ : g₂ a with
      | none => simp [e₂] at hp₂
      | some v₂ =>
        have := (hs₁ a v₁ e₁).symm.trans (hs₂ a v₂ e₂)
        simp [this]
  · rw [hr₁ a ha, hr₂ a ha]

/-- `pointsTo p v` holds exactly of the one-cell fragment `p ↦ v`. -/
theorem sat_pointsTo_iff (p : Addr) (v : Val) (g : Heap) :
    sat (pointsTo p v) g ↔ g p = some v ∧ ∀ a, a ≠ p → g a = none := by
  simp only [pointsTo, sat]
  constructor
  · rintro ⟨w, hw, hwv, hrest⟩
    have : w = v := by simpa using hwv
    subst this
    exact ⟨hw, hrest⟩
  · rintro ⟨hv, hrest⟩
    exact ⟨v, hv, by simp, hrest⟩

/-- Positive: `pointsTo 0 0 ∨ pointsTo 0 1` is precise (the disjuncts are
distinguished by the value at `0`). -/
theorem precise_pointsTo00_or_pointsTo01 : Precise (.or (pointsTo 0 0) (pointsTo 0 1)) := by
  intro g g₁ g₂ hs₁ hs₂ h₁ h₂
  have key : ∀ g', Heap.Sub g' g → sat (.or (pointsTo 0 0) (pointsTo 0 1)) g' →
      g' 0 = g 0 ∧ ∀ a, a ≠ 0 → g' a = none := by
    intro g' hs h
    rcases h with h | h
    · obtain ⟨hv, hr⟩ := (sat_pointsTo_iff 0 0 g').1 h
      exact ⟨by rw [hv, hs 0 0 hv], hr⟩
    · obtain ⟨hv, hr⟩ := (sat_pointsTo_iff 0 1 g').1 h
      exact ⟨by rw [hv, hs 0 1 hv], hr⟩
  obtain ⟨a₁, r₁⟩ := key g₁ hs₁ h₁
  obtain ⟨a₂, r₂⟩ := key g₂ hs₂ h₂
  funext a
  by_cases ha : a = 0
  · subst ha; rw [a₁, a₂]
  · rw [r₁ a ha, r₂ a ha]

/-- Negative: `owned 0 ∨ owned 1` is not precise (in `hTwo` both one-cell fragments
are witnesses). -/
theorem not_precise_C : ¬ Precise C := by
  intro hp
  have := hp hTwo (Heap.single 0 0) (Heap.single 1 0) sub_single0_hTwo sub_single1_hTwo
    (Or.inl ((sat_owned_iff 0 _).2 ⟨rfl, fun a ha => by simp [ha]⟩))
    (Or.inr ((sat_owned_iff 1 _).2 ⟨rfl, fun a ha => by simp [ha]⟩))
  have := congrFun this 0
  simp at this

/-- Positive: `pointsTo 0 0 ∨ pointsTo 0 1` is disjunction-precise. -/
theorem disjPrecise_pointsTo00_or_pointsTo01 :
    DisjPrecise (.or (pointsTo 0 0) (pointsTo 0 1)) :=
  ⟨precise_pointsTo00_or_pointsTo01, trivial, trivial⟩

/-- Negative: `owned 0 ∨ owned 1` is not disjunction-precise. -/
theorem not_disjPrecise_C : ¬ DisjPrecise C := fun h => not_precise_C h.1

/-- The inner disjunction `(owned 0 ∗ owned 1) ∨ owned 0` of `C'` is imprecise. -/
theorem not_precise_C'_inner : ¬ Precise (.or (.sep (owned 0) (owned 1)) (owned 0)) := by
  intro hp
  have := hp hTwo hTwo (Heap.single 0 0) (fun _ _ h => h) sub_single0_hTwo
    (Or.inl sat_owned0_sep_owned1_hTwo)
    (Or.inr ((sat_owned_iff 0 _).2 ⟨rfl, fun a ha => by simp [ha]⟩))
  have := congrFun this 1
  simp at this

/-- Negative: `C'` is not disjunction-precise. -/
theorem not_disjPrecise_C' : ¬ DisjPrecise C' := fun h => not_precise_C'_inner h.1.1

/-! ## Strategies -/

/-- Positive: `fpAtom` is sound. -/
theorem fpAtom_strategySound : StrategySound fpAtom := by
  intro A g F hF
  cases A with
  | cell p P =>
    simp only [fpAtom] at hF
    cases hgp : g p with
    | none => simp [hgp] at hF
    | some v =>
      simp only [hgp] at hF
      by_cases hP : P v = true
      · simp only [hP, ↓reduceIte, Option.some.injEq] at hF
        subst hF
        refine ⟨by simp [hgp], v, by simp [hgp], hP, fun a ha => by simp [ha]⟩
      · simp [hP] at hF
  | pure b =>
    simp only [fpAtom] at hF
    by_cases hb : b = true
    · simp only [hb, ↓reduceIte, Option.some.injEq] at hF
      subst hF
      exact ⟨by simp, hb, fun a => by simp⟩
    · simp [hb] at hF
  | sep _ _ => simp [fpAtom] at hF
  | or _ _ => simp [fpAtom] at hF

/-- Negative: `sBad` is not sound (`[0]` is not a footprint of `pointsTo 0 1` in
`hOne`, where byte `0` holds `0`). -/
theorem not_strategySound_sBad : ¬ StrategySound sBad := by
  intro h
  obtain ⟨-, hsat⟩ := h (pointsTo 0 1) hOne [0] rfl
  have := ((sat_pointsTo_iff 0 1 _).1 hsat).1
  simp [hOne] at this

/-- Positive: `fpAtom` recovers every witness of every atomic `cell` contract. -/
theorem fpAtom_recoversEveryWitness_cell (p : Addr) (P : Val → Bool) : RecoversEveryWitness fpAtom (.cell p P) := by
  intro g g' hsub ⟨v, hv, hP, hrest⟩
  have hgp : g p = some v := hsub p v hv
  refine ⟨[p], by simp [fpAtom, hgp, hP], by simp [hgp], ?_⟩
  funext a
  by_cases ha : a = p
  · subst ha; simp [hgp, hv]
  · simp [ha, hrest a ha]

/-- Negative: `fpGreedy` does not recover every witness of `owned 0 ∨ owned 1` (it commits to
`owned 0` even when the intended witness is the cell at `1`). -/
theorem not_recoversEveryWitness_fpGreedy_C : ¬ RecoversEveryWitness fpGreedy C := by
  intro hc
  obtain ⟨F, hF, -, heq⟩ := hc hTwo (Heap.single 1 0) sub_single1_hTwo
    (Or.inr ((sat_owned_iff 1 _).2 ⟨rfl, fun a ha => by simp [ha]⟩))
  have hF' : fpGreedy C hTwo = some [0] := by decide
  rw [hF'] at hF
  cases hF
  have := congrFun heq 0
  simp at this

/-- Negative: `fpSearch` does not recover every witness of `owned 0 ∨ owned 1` either (its first
footprint is the cell at `0`). -/
theorem not_recoversEveryWitness_fpSearch_C : ¬ RecoversEveryWitness fpSearch C := by
  intro hc
  obtain ⟨F, hF, -, heq⟩ := hc hTwo (Heap.single 1 0) sub_single1_hTwo
    (Or.inr ((sat_owned_iff 1 _).2 ⟨rfl, fun a ha => by simp [ha]⟩))
  have hF' : fpSearch C hTwo = some [0] := by decide
  rw [hF'] at hF
  cases hF
  have := congrFun heq 0
  simp at this

/-- Witness recovery (`RecoversEveryWitness`) is only possible for precise contracts
(whatever the strategy): the single answer `s A g` must carve out every witness. -/
theorem precise_of_recoversEveryWitness (s : Strategy) (A : Assn) (hc : RecoversEveryWitness s A) : Precise A := by
  intro g g₁ g₂ hs₁ hs₂ h₁ h₂
  obtain ⟨F₁, hF₁, -, e₁⟩ := hc g g₁ hs₁ h₁
  obtain ⟨F₂, hF₂, -, e₂⟩ := hc g g₂ hs₂ h₂
  rw [hF₁] at hF₂
  cases hF₂
  rw [← e₁, ← e₂]

/-- Example computations: greedy footprints. -/
example : fpGreedy (.sep (owned 0) (owned 1)) hTwo = some [0, 1] := by decide
example : fpGreedy (.sep (owned 0) (owned 0)) hTwo = none := by decide
example : fpGreedy C hTwo = some [0] := by decide
/-- Consumption-style `sep`: the second `C` is evaluated after byte `0` was consumed. -/
example : fpGreedy (.sep C C) hTwo = some [0, 1] := by decide
example : fpGreedyR C hTwo = some [1] := by decide
/-- Greedy commits to the left disjunct of `C'`'s inner disjunction and fails;
exhaustive search finds the witness. -/
example : fpGreedy C' hTwo = none := by decide
example : fpSearch C' hTwo = some [0, 1] := by decide
example : fpAll C hTwo = [[0], [1]] := by decide

/-! ## `exec`, `initOwn`, `transfer` -/

example : exec (.write 0 5) hOne 0 = some 5 := by decide
/-- A store to an unallocated byte leaves the heap unchanged. -/
example : exec (.write 3 5) hOne 3 = none := by decide
example : initOwn [0, 1] 1 = some 0 := by decide
example : transfer [0] 0 1 (initOwn [0, 1]) 0 = some 1 := by decide
example : transfer [0] 0 1 (initOwn [0, 1]) 1 = some 0 := by decide

/-! ## `monitor` / `Accepts` -/

/-- Positive: a callee given `owned 0` that stores `5` and returns `pointsTo 0 5`
is accepted. -/
theorem accepts_strict_fpAtom_write_call :
    Accepts MonCfg.strict fpAtom (.call (owned 0) (pointsTo 0 5) (.write 0 5)) hOne [0] := by
  decide

/-- Negative: reading a byte the frame does not own is rejected. -/
theorem not_accepts_read_unowned : ¬ Accepts MonCfg.strict fpAtom (.read 1) hTwo [0] := by
  decide

/-- Negative: a callee that reads a byte its caller kept is rejected. -/
theorem not_accepts_callee_reads_kept_byte :
    ¬ Accepts MonCfg.strict fpAtom (.call (owned 0) (owned 0) (.read 1)) hTwo [0, 1] := by
  decide

/-- Negative: a callee whose postcondition does not return everything it was given
is rejected by the leak check. -/
theorem not_accepts_strict_leak :
    ¬ Accepts MonCfg.strict fpAtom (.call (owned 0) .emp .skip) hOne [0] := by
  decide

/-- Negative: the precondition `owned 0 ∗ owned 0` cannot be met. -/
theorem not_accepts_double_owned_pre :
    ¬ Accepts MonCfg.strict fpGreedy (.call (.sep (owned 0) (owned 0)) .emp .skip) hTwo [0, 1] := by
  decide

/-! ## `Satisfies`, `SatisfiesBy`, `UnannotConfined` -/

/-- Positive: the store-5 callee satisfies its contract. -/
theorem satisfies_write_call :
    Satisfies (.call (owned 0) (pointsTo 0 5) (.write 0 5)) hOne [0] := by
  refine ⟨[0], ⟨by decide, (sat_owned_iff 0 _).2 ⟨by decide, fun a ha => by simp [ha]⟩⟩,
    ⟨by simp, by decide⟩, ⟨by decide, (sat_pointsTo_iff 0 5 _).2 ⟨by decide, fun a ha => by simp [ha]⟩⟩⟩

/-- If `F` is a footprint of `owned 0` inside `hTwo` restricted to `[0, 1]`, then `1 ∉ F`. -/
theorem not_mem_one_of_isFootprint_owned0 (F : List Addr)
    (h : IsFootprint (owned 0) (hTwo.restrict [0, 1]) F) : 1 ∉ F := by
  intro h1
  have := ((sat_owned_iff 0 _).1 h.2).2 1 (by decide)
  simp [h1] at this

/-- If `F` is a footprint of `owned 1` inside `hTwo` restricted to `[0, 1]`, then `0 ∉ F`. -/
theorem not_mem_zero_of_isFootprint_owned1 (F : List Addr)
    (h : IsFootprint (owned 1) (hTwo.restrict [0, 1]) F) : 0 ∉ F := by
  intro h0
  have := ((sat_owned_iff 1 _).1 h.2).2 0 (by decide)
  simp [h0] at this

/-- Negative: a callee given `owned 0` must not read byte `1`. -/
theorem not_satisfies_callee_reads_kept_byte :
    ¬ Satisfies (.call (owned 0) (owned 0) (.read 1)) hTwo [0, 1] := by
  rintro ⟨F, hF, ⟨h1, -⟩, -⟩
  exact not_mem_one_of_isFootprint_owned0 F hF h1

/-- Negative: exactness — the postcondition must describe the callee's whole final
fragment, so returning `emp` after receiving `owned 0` does not satisfy the contract. -/
theorem not_satisfies_leaky_post : ¬ Satisfies (.call (owned 0) .emp .skip) hOne [0] := by
  rintro ⟨F, hF, -, hpost⟩
  have h0 : 0 ∈ F := by
    refine Classical.byContradiction fun h0 => ?_
    have := ((sat_owned_iff 0 _).1 hF.2).1
    simp [h0] at this
  have := hpost.2.2 0
  simp [h0, exec, hOne] at this

/-- Positive: `SatisfiesBy fpAtom` for the store-5 callee. -/
theorem satisfiesBy_fpAtom_write_call :
    SatisfiesBy fpAtom (.call (owned 0) (pointsTo 0 5) (.write 0 5)) hOne [0] := by
  refine ⟨[0], by decide, ⟨by decide, (sat_owned_iff 0 _).2 ⟨by decide, fun a ha => by simp [ha]⟩⟩,
    ⟨by simp, by decide⟩, [0], by decide, fun a => Iff.rfl,
    ⟨by decide, (sat_pointsTo_iff 0 5 _).2 ⟨by decide, fun a ha => by simp [ha]⟩⟩⟩

/-- Negative: with `fpGreedy`, the run `runR` does not satisfy its contracts *by the
greedy footprints* (greedy transfers byte `0`, the callee reads byte `1`). -/
theorem not_satisfiesBy_fpGreedy_runR : ¬ SatisfiesBy fpGreedy runR hTwo [0, 1] := by
  rintro ⟨F, hF, -, ⟨h1, -⟩, -⟩
  have hF' : fpGreedy C (hTwo.restrict [0, 1]) = some [0] := by decide
  rw [hF'] at hF
  cases hF
  simp at h1

/-- Positive: an unannotated callee that only stores to byte `0`, inside a callee
given `owned 0`, stays within its caller's footprint. -/
theorem unannotConfined_inside :
    UnannotConfined fpAtom (.call (owned 0) (owned 0) (.unannot (.write 0 7))) hTwo [0, 1] := by
  intro F hF
  have : F = [0] := by
    have h : fpAtom (owned 0) (hTwo.restrict [0, 1]) = some [0] := by decide
    rw [h] at hF; cases hF; rfl
  subst this
  intro _
  exact ⟨by simp, by decide⟩

/-- Negative: an unannotated callee that stores to byte `1`, inside a callee given
only `owned 0`, leaves its caller's footprint. -/
theorem not_unannotConfined_outside :
    ¬ UnannotConfined fpAtom (.call (owned 0) (owned 0) (.unannot (.write 1 7))) hTwo [0, 1] := by
  intro h
  have := h [0] (by decide) rfl
  simp at this

/-- Positive: accesses of *annotated* code are not constrained by `UnannotConfined` (the
monitor checks them), so a top-level read of an unowned byte is confined in this sense. -/
theorem unannotConfined_annotated_read_unconstrained :
    UnannotConfined fpAtom (.read 1) hTwo [0] := fun h => absurd h (by decide)

/-- Negative: an unannotated top-level helper reading a byte the top frame does not own is
not confined. -/
theorem not_unannotConfined_top_read :
    ¬ UnannotConfined fpAtom (.unannot (.read 1)) hTwo [0] := by
  intro h
  have := h rfl
  simp at this

/-! ## Trusted (uninstrumented) unannotated callees -/

/-- A callee given `owned 0` whose unannotated helper calls an annotated function with
the precondition `pointsTo 0 1`, which is false in `hOne` (byte `0` holds `0`). -/
def pCallback : Prog :=
  .call (owned 0) (owned 0) (.unannot (.call (pointsTo 0 1) (owned 0) .skip))

/-- Positive: with unannotated callees trusted, an out-of-frame store by the unannotated
helper is not checked (the run is accepted). -/
theorem accepts_trusted_unannot_store :
    Accepts ⟨true, false⟩ fpAtom (.call (owned 0) (owned 0) (.unannot (.write 1 7))) hTwo [0, 1] := by
  decide

/-- Negative: with unannotated callees trusted, an annotated callee called *from* the
unannotated helper is still monitored: its false precondition makes the monitor reject. -/
theorem not_accepts_trusted_nested_annotated_call :
    ¬ Accepts ⟨true, false⟩ fpAtom pCallback hOne [0] := by
  decide

/-! ## `ExistsFootprintComplete` -/

/-- Positive: `fpAtom` finds a footprint for every atomic `cell` contract whenever one
exists. -/
theorem fpAtom_existsFootprintComplete_cell (p : Addr) (P : Val → Bool) :
    ExistsFootprintComplete fpAtom (.cell p P) := by
  intro g g' hsub ⟨v, hv, hP, _⟩
  have hgp : g p = some v := hsub p v hv
  refine ⟨[p], by simp [fpAtom, hgp, hP], by simp [hgp], v, by simp [hgp], hP, ?_⟩
  intro a ha
  simp [ha]

/-- Negative: `fpAtom` gives up on every disjunction, so it is not existentially complete
for `owned 0 ∨ owned 1`. -/
theorem not_existsFootprintComplete_fpAtom_C : ¬ ExistsFootprintComplete fpAtom C := by
  intro hc
  obtain ⟨F, hF, -⟩ := hc hTwo (Heap.single 0 0) sub_single0_hTwo
    (Or.inl ((sat_owned_iff 0 _).2 ⟨rfl, fun a ha => by simp [ha]⟩))
  simp [fpAtom, C] at hF

end Toy.Monitor
