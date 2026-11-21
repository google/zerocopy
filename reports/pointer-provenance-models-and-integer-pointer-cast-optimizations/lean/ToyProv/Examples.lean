import ToyProv.Lemmas

/-!
# Definition examples

Positive and negative examples for the operational definitions, for 8 of the 11 state predicates, and for 8 of the 10
transformation relations. Negative transformation examples are proved by case analysis, not by closed evaluation.
-/

namespace Toy.Prov

/-- Two adjacent two-byte allocations: `A` at address 16 (id 0) and `B` at 18 (id 1). -/
def twoBlocks : Prog := [.alloc 0 2, .alloc 1 2]

/-- State after `twoBlocks` in model `m` (the unique execution). -/
def stTwo (m : Model) : St := match exec m twoBlocks init with
  | some s :: _ => s
  | _ => init

/-! ### `alloc` (bump allocation, adjacency) -/
theorem ex_alloc_adjacent_pos : (stTwo .strict).blocks = [⟨16, 2, true⟩, ⟨18, 2, true⟩] := by decide
theorem ex_alloc_zero_neg : ∀ m, beh m [.alloc 0 0] = [.ub] := by intro m; cases m <;> decide

/-! ### `canAccess` -/
-- strict: an in-bounds access through B's own provenance is allowed
theorem ex_canAccess_pos : canAccess .strict (stTwo .strict) ⟨some 1, 18⟩ 2 = true := by decide
-- strict: the one-past-the-end pointer of A (same address as B's start) is rejected
theorem ex_canAccess_neg : canAccess .strict (stTwo .strict) ⟨some 0, 18⟩ 2 = false := by decide
-- flat: the same address is accepted, provenance is ignored
theorem ex_canAccess_flat_pos : canAccess .flat (stTwo .flat) ⟨none, 18⟩ 2 = true := by decide
-- flat: an address outside every live block is rejected
theorem ex_canAccess_flat_neg : canAccess .flat (stTwo .flat) ⟨none, 20⟩ 2 = false := by decide
-- strict: a provenance-less pointer is rejected
theorem ex_canAccess_none_neg : canAccess .strict (stTwo .strict) ⟨none, 18⟩ 2 = false := by decide

/-! ### `candidates` -/
/-- `stTwo .exposed` with both allocations exposed. -/
def stTwoExp : St := { stTwo .exposed with exposed := [0, 1] }
-- the shared boundary address 18 is in the closed range of both A (one past the end) and B
theorem ex_candidates_pos : candidates stTwoExp 18 = [0, 1] := by decide
-- an unexposed allocation is never a candidate
theorem ex_candidates_neg : candidates (stTwo .exposed) 18 = [] := by decide
-- an address beyond every closed range has no candidate
theorem ex_candidates_far_neg : candidates stTwoExp 21 = [] := by decide

/-! ### `mergeProv` / `provsOf` -/
theorem ex_mergeProv_pos : mergeProv (some 0) (some 0) = some 0 := by decide
theorem ex_mergeProv_neg : mergeProv none (some 0) = none ∧ mergeProv (some 0) (some 1) = none := by
  decide
theorem ex_provsOf_pos : provsOf (some 0) (some 1) = [0, 1] ∧ provsOf (some 0) (some 0) = [0] := by
  decide
theorem ex_provsOf_neg : provsOf none none = [] := by decide

/-! ### `decodeInt` / `decodePtr` -/
theorem ex_decodeInt_pos : decodeInt (.ptrFrag ⟨some 0, 16⟩ 0) (.ptrFrag ⟨some 0, 16⟩ 1) = some (16, [0]) := by
  decide
-- same address, different provenances: defined, and both provenances are exposed
theorem ex_decodeInt_mixed_pos :
    decodeInt (.ptrFrag ⟨some 0, 16⟩ 0) (.ptrFrag ⟨some 1, 16⟩ 1) = some (16, [0, 1]) ∧
      decodeInt (.ptrFrag ⟨none, 16⟩ 0) (.ptrFrag ⟨some 0, 16⟩ 1) = some (16, [0]) := by
  decide
-- fragments of pointers with different addresses: UB
theorem ex_decodeInt_neg : decodeInt (.ptrFrag ⟨some 0, 16⟩ 0) (.ptrFrag ⟨some 0, 18⟩ 1) = none := by decide
-- fragments in the wrong order: UB
theorem ex_decodeInt_order_neg : decodeInt (.ptrFrag ⟨some 0, 16⟩ 1) (.ptrFrag ⟨some 0, 16⟩ 0) = none := by
  decide
theorem ex_decodeInt_uninit_neg : decodeInt .uninit (.intFrag 3 1) = none := by decide
theorem ex_decodePtr_pos : decodePtr (.ptrFrag ⟨some 0, 16⟩ 0) (.ptrFrag ⟨some 0, 16⟩ 1) = some (.inl ⟨some 0, 16⟩) := by
  decide
theorem ex_decodePtr_int_pos : decodePtr (.intFrag 16 0) (.intFrag 16 1) = some (.inr 16) := by decide
-- same address, different provenances: a pointer without provenance (not UB)
theorem ex_decodePtr_mixed_pos :
    decodePtr (.ptrFrag ⟨some 0, 16⟩ 0) (.ptrFrag ⟨some 1, 16⟩ 1) = some (.inl ⟨none, 16⟩) := by
  decide
theorem ex_decodePtr_neg : decodePtr (.intFrag 16 0) (.ptrFrag ⟨some 0, 16⟩ 1) = none := by decide
theorem ex_decodePtr_addr_neg : decodePtr (.ptrFrag ⟨some 0, 16⟩ 0) (.ptrFrag ⟨some 0, 18⟩ 1) = none := by
  decide

/-! ### `castToPtr` -/
-- exposed: the boundary address has two candidates, hence two successors
theorem ex_castToPtr_pos : (castToPtr .exposed stTwoExp 5 18).length = 2 := by decide
-- strict: always exactly one successor, without provenance
theorem ex_castToPtr_strict_neg : (castToPtr .strict stTwoExp 5 18).length = 1 := by decide

/-! ### `beh` (angelic resolution) -/
/-- In `exposed`, `int2ptr 18` with both A and B exposed has two resolutions: storing through
the A-resolution (one past A's end) is UB, through the B-resolution it is defined. -/
def angelicProg : Prog :=
  [.alloc 0 2, .alloc 1 2, .ptr2int 2 0, .ptr2int 3 1, .int2ptr 4 3, .const 5 7, .store 4 5, .obs 5]
theorem ex_runs_two_resolutions : runs .exposed angelicProg = [.ub, .done [7]] := by decide
-- angelic: the UB resolution is discarded because a defined one exists
theorem ex_beh_angelic_pos : beh .exposed angelicProg = [.done [7]] := by decide
-- in strict the cast yields no provenance, so the program is UB
theorem ex_beh_strict_neg : beh .strict angelicProg = [.ub] := by decide

/-! ### `Refines` -/
-- removing UB is a refinement
theorem ex_refines_pos : Refines .strict [.const 0 1, .obs 0] [.obs 0] := by decide
-- changing the output of a defined program is not
theorem ex_refines_neg : ¬ Refines .strict [.const 0 2, .obs 0] [.const 0 1, .obs 0] := by decide
-- introducing UB into a defined program is not
theorem ex_refines_ub_neg : ¬ Refines .strict [.obs 0] [.const 0 1, .obs 0] := by decide

/-! ### `AllAfter` and side-condition predicates -/
theorem ex_allAfter_addrEq_pos : AllAfter .strict [.alloc 0 2, .alloc 1 2, .offset 2 0 2] (addrEqC 2 1) := by
  decide
theorem ex_allAfter_addrEq_neg : ¬ AllAfter .strict [.alloc 0 2, .alloc 1 2] (addrEqC 0 1) := by decide
-- equal addresses but different provenance: not the same value (except in flat)
theorem ex_sameVal_neg : ¬ AllAfter .strict [.alloc 0 2, .alloc 1 2, .offset 2 0 2] (sameValC 2 1) := by
  decide
theorem ex_sameVal_flat_pos : AllAfter .flat [.alloc 0 2, .alloc 1 2, .offset 2 0 2] (sameValC 2 1) := by
  decide
theorem ex_sameVal_pos : AllAfter .strict [.alloc 0 2, .copy 1 0] (sameValC 1 0) := by decide
theorem ex_intIsAddrOf_pos : AllAfter .exposed [.alloc 0 2, .ptr2int 1 0] (intIsAddrOfC 1 0) := by decide
theorem ex_intIsAddrOf_neg : ¬ AllAfter .exposed [.alloc 0 2, .const 1 17] (intIsAddrOfC 1 0) := by decide
theorem ex_bothExposed_pos :
    AllAfter .exposed [.alloc 0 2, .alloc 1 2, .ptr2int 2 0, .ptr2int 3 1] (bothExposedC 0 1) := by decide
theorem ex_bothExposed_neg : ¬ AllAfter .exposed [.alloc 0 2, .alloc 1 2, .ptr2int 2 0] (bothExposedC 0 1) := by
  decide
theorem ex_candEqProv_pos : AllAfter .exposed [.alloc 0 2, .ptr2int 1 0] (candEqProvC 0) := by decide
-- after exposing both, B's start is also A's one-past-the-end: two candidates
theorem ex_candEqProv_neg :
    ¬ AllAfter .exposed [.alloc 0 2, .alloc 1 2, .ptr2int 2 0, .ptr2int 3 1] (candEqProvC 1) := by decide
theorem ex_candSubProv_pos : AllAfter .exposed [.alloc 0 2] (candSubProvC 0) := by decide
theorem ex_candSubProv_neg :
    ¬ AllAfter .exposed [.alloc 0 2, .alloc 1 2, .ptr2int 2 0, .ptr2int 3 1] (candSubProvC 1) := by decide
theorem ex_provIsCand_pos : AllAfter .exposed [.alloc 0 2, .ptr2int 1 0] (provIsCandC 0) := by decide
theorem ex_provIsCand_neg : ¬ AllAfter .exposed [.alloc 0 2] (provIsCandC 0) := by decide
theorem ex_provNe_pos : AllAfter .strict [.alloc 0 2, .alloc 1 2] (provNeC 0 1) := by decide
theorem ex_provNe_neg : ¬ AllAfter .strict [.alloc 0 2, .offset 1 0 1] (provNeC 0 1) := by decide
-- in flat no pointer has provenance, so provNeC never holds there
theorem ex_provNe_flat_neg : ¬ AllAfter .flat [.alloc 0 2, .alloc 1 2] (provNeC 0 1) := by decide

/-! ### `Instr.substUse` / `Instr.reads` -/
theorem ex_substUse_pos : (Instr.store 1 1).substUse 1 2 = .store 2 2 := by decide
theorem ex_substUse_dst_neg : (Instr.copy 1 3).substUse 1 2 = .copy 1 3 := by decide
theorem ex_reads_pos : (Instr.store 1 4).reads 4 = true := by decide
theorem ex_reads_neg : (Instr.load 4 .int 1).reads 4 = false := by decide

/-! ### Transformation relations -/
theorem ex_substAddrEq_pos :
    SubstAddrEq .strict ([.alloc 0 2, .alloc 1 2, .offset 2 0 2] ++ .obs 1 :: [])
      ([.alloc 0 2, .alloc 1 2, .offset 2 0 2] ++ .obs 2 :: []) :=
  ⟨_, _, _, 1, 2, rfl, rfl, by decide⟩

/-- A one-instruction program can only be split with `pre = []`. -/
theorem split_singleton {pre post : Prog} {i j : Instr} (h : [j] = pre ++ i :: post) :
    pre = [] ∧ i = j ∧ post = [] := by
  cases pre with
  | nil => simp at h; exact ⟨rfl, h.1.symm, h.2⟩
  | cons a pre => cases pre <;> simp at h

-- at the start of a program no register holds a pointer, so no substitution is justified
theorem ex_substAddrEq_neg : ¬ SubstAddrEq .strict [.obs 1] [.obs 2] := by
  rintro ⟨pre, i, post, q, p, h1, -, h3⟩
  obtain ⟨rfl, -, -⟩ := split_singleton h1
  have := AllAfter_nil.mp h3
  simp [addrEqC, init] at this

theorem ex_substSameVal_pos :
    SubstSameVal .strict ([.alloc 0 2, .copy 1 0] ++ .obs 1 :: []) ([.alloc 0 2, .copy 1 0] ++ .obs 0 :: []) :=
  ⟨_, _, _, 1, 0, rfl, rfl, by decide⟩
theorem ex_substSameVal_neg : ¬ SubstSameVal .strict [.obs 1] [.obs 2] := by
  rintro ⟨pre, i, post, q, p, h1, -, h3⟩
  obtain ⟨rfl, -, -⟩ := split_singleton h1
  have := AllAfter_nil.mp h3
  simp [sameValC, init] at this

theorem ex_substIntEq_pos :
    SubstIntEq .exposed ([.alloc 0 2, .copy 1 0, .ptr2int 2 0] ++ .obs 1 :: [])
      ([.alloc 0 2, .copy 1 0, .ptr2int 2 0] ++ .obs 0 :: []) :=
  ⟨_, _, _, 1, 0, rfl, rfl, by decide⟩
theorem ex_substIntEq_neg : ¬ SubstIntEq .exposed [.obs 1] [.obs 2] := by
  rintro ⟨pre, i, post, q, p, h1, -, h3⟩
  obtain ⟨rfl, -, -⟩ := split_singleton h1
  have := AllAfter_nil.mp h3
  simp [addrEqC, init] at this

theorem ex_int2ptrToCopy_pos :
    Int2ptrToCopy .exposed ([.alloc 0 2, .ptr2int 1 0] ++ .int2ptr 2 1 :: [])
      ([.alloc 0 2, .ptr2int 1 0] ++ .copy 2 0 :: []) :=
  ⟨_, _, 2, 1, 0, rfl, rfl, by decide⟩
theorem ex_int2ptrToCopy_neg : ¬ Int2ptrToCopy .exposed [.int2ptr 2 1] [.copy 2 0] := by
  rintro ⟨pre, post, d, k, p, h1, -, h3⟩
  obtain ⟨rfl, -, -⟩ := split_singleton h1
  have := AllAfter_nil.mp h3
  simp [intIsAddrOfC, init] at this

theorem ex_copyToInt2ptr_pos :
    CopyToInt2ptr .exposed ([.alloc 0 2, .ptr2int 1 0] ++ .copy 2 0 :: [])
      ([.alloc 0 2, .ptr2int 1 0] ++ .int2ptr 2 1 :: []) :=
  ⟨_, _, 2, 1, 0, rfl, rfl, by decide⟩
theorem ex_copyToInt2ptr_neg : ¬ CopyToInt2ptr .exposed [.copy 2 0] [.int2ptr 2 1] := by
  rintro ⟨pre, post, d, k, p, h1, -, h3⟩
  obtain ⟨rfl, -, -⟩ := split_singleton h1
  have := AllAfter_nil.mp h3
  simp [intIsAddrOfC, init] at this

theorem ex_dropUnusedPtr2int_pos :
    DropUnusedPtr2int .exposed ([.alloc 0 2] ++ .ptr2int 1 0 :: [.obs 0]) ([.alloc 0 2] ++ [.obs 0]) :=
  ⟨_, _, 1, 0, rfl, rfl, by decide, by decide⟩
-- the cast's result is read later, so it may not be dropped
theorem ex_dropUnusedPtr2int_neg :
    ¬ DropUnusedPtr2int .exposed [.alloc 0 2, .ptr2int 1 0, .obs 1] [.alloc 0 2, .obs 1] := by
  rintro ⟨pre, post, d, p, h1, h2, h3, -⟩
  match pre, h1 with
  | [], h1 => simp at h1
  | [_], h1 =>
    simp at h1
    obtain ⟨-, ⟨rfl, rfl⟩, rfl⟩ := h1
    simp [Instr.reads] at h3
  | [_, _], h1 => simp at h1
  | _ :: _ :: _ :: _, h1 => simp at h1

/-- A defined instance in `exposed`: A is exposed by `k := (int)A`, so the cast picks A, and the
source outputs `[9]`. -/
theorem ex_forwardAcrossCast_pos :
    ForwardAcrossCast .exposed
      ([.alloc 0 2, .ptr2int 2 0, .const 3 5, .const 4 9] ++
        [.int2ptr 5 2, .store 0 3, .store 5 4, .load 6 .int 0] ++ [.obs 6])
      ([.alloc 0 2, .ptr2int 2 0, .const 3 5, .const 4 9] ++
        [.int2ptr 5 2, .store 0 3, .store 5 4, .copy 6 3] ++ [.obs 6]) ∧
      beh .exposed ([.alloc 0 2, .ptr2int 2 0, .const 3 5, .const 4 9] ++
        [.int2ptr 5 2, .store 0 3, .store 5 4, .load 6 .int 0] ++ [.obs 6]) = [.done [9]] :=
  ⟨⟨_, _, 5, 2, 0, 3, 4, 6, by decide, by decide, rfl, rfl, by decide⟩, by decide⟩
-- no register is set before the window, so `v` does not hold an integer and the side condition
-- `isIntC v` fails
theorem ex_forwardAcrossCast_neg :
    ¬ ForwardAcrossCast .exposed [.int2ptr 5 2, .store 0 3, .store 5 4, .load 6 .int 0]
      [.int2ptr 5 2, .store 0 3, .store 5 4, .copy 6 3] := by
  rintro ⟨pre, post, r, k, a, v, w, x, -, -, h1, -, h3⟩
  have hl := congrArg List.length h1
  simp at hl
  have hpre : pre = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst hpre
  have := AllAfter_nil.mp h3
  simp [isIntC, init] at this

/-- A defined instance in `exposed`: A is initialised to 1 and exposed; the cast picks A. -/
theorem ex_dseAcrossCast_pos :
    DSEAcrossCast .exposed
      ([.alloc 0 2, .const 1 1, .store 0 1, .ptr2int 2 0, .const 3 5, .const 4 6] ++
        [.int2ptr 5 2, .store 0 3, .load 6 .int 5, .store 0 4] ++ [.obs 6])
      ([.alloc 0 2, .const 1 1, .store 0 1, .ptr2int 2 0, .const 3 5, .const 4 6] ++
        [.int2ptr 5 2, .load 6 .int 5, .store 0 4] ++ [.obs 6]) ∧
      beh .exposed ([.alloc 0 2, .const 1 1, .store 0 1, .ptr2int 2 0, .const 3 5, .const 4 6] ++
        [.int2ptr 5 2, .store 0 3, .load 6 .int 5, .store 0 4] ++ [.obs 6]) = [.done [5]] :=
  ⟨⟨_, _, 5, 2, 0, 3, 6, .int, 4, by decide, by decide, by decide, rfl, rfl⟩, by decide⟩
-- the load overwrites `a` itself, so the first store is not dead
theorem ex_dseAcrossCast_neg :
    ¬ DSEAcrossCast .exposed [.int2ptr 5 2, .store 0 3, .load 0 .int 5, .store 0 4]
      [.int2ptr 5 2, .load 0 .int 5, .store 0 4] := by
  rintro ⟨pre, post, r, k, a, v, x, ty, w, -, -, hx, h1, -⟩
  have hl := congrArg List.length h1
  simp at hl
  have hpre : pre = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst hpre
  simp at h1
  obtain ⟨-, ⟨ha, -⟩, ⟨hx', -⟩, -⟩ := h1
  exact hx (hx'.symm.trans ha)

/-! ### `SemRefines` -/
/-- A cast-free program: store 7 through a copy of A, read A. -/
def r6dSrcEx : Prog := [.alloc 0 2, .copy 1 0, .const 2 7, .store 1 2, .load 3 .int 0, .obs 3]
/-- B initialised to 7, then read through A's one-past-the-end pointer. -/
def onePastReadProg : Prog :=
  [.alloc 0 2, .alloc 1 2, .const 4 7, .store 1 4, .offset 2 0 2, .load 3 .int 2, .obs 3]
-- flat is more defined than strict on a read through the one-past-the-end pointer: strict has
-- UB, so strict's behaviour is refined by flat's
theorem ex_semRefines_pos :
    beh .flat onePastReadProg = [.done [7]] ∧ beh .strict onePastReadProg = [.ub] ∧
      SemRefines .flat .strict onePastReadProg := by
  decide
-- both models defined with the same output
theorem ex_semRefines_eq_pos :
    beh .flat r6dSrcEx = [.done [7]] ∧ beh .strict r6dSrcEx = [.done [7]] ∧
      SemRefines .flat .strict r6dSrcEx := by
  decide
-- the reverse fails: flat is defined, strict is not
theorem ex_semRefines_neg : ¬ SemRefines .strict .flat onePastReadProg := by
  decide

end Toy.Prov
