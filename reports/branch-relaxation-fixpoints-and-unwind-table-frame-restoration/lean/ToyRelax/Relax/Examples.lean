import ToyRelax.Relax.Basic

/-!
# Concrete instances and definition examples for the relaxation model

Every core definition gets at least one proved positive example (an intended
instance it admits) and one proved negative example (an instance it must
reject).  The concrete programs defined here are reused as witnesses by the
results file.
-/

namespace Toy.Relax

/-! ### Concrete parameters and programs -/

/-- Short branches have size 1 and reach 1; long branches have size 2. -/
def chainPrm : Params := ⟨1, 2, 1⟩

/-- A two-branch promotion chain: branch 1 jumps back over a 2-byte
instruction (out of reach from the start); branch 2 jumps back over branch 1,
which is in reach only while branch 1 is short. -/
def chainProg : Prog := [.fixed 2, .branch 0, .branch 1]

/-- Short size 1, long size 2, reach 2. -/
def alignPrm : Params := ⟨1, 2, 2⟩

/-- Alignment padding between two branches: branch 0 jumps to the alignment
directive, branch 2 jumps back to it.  Growing branch 0 shrinks the padding. -/
def alignProg : Prog := [.branch 1, .align 4, .branch 1]

/-- The assignment with only branch 0 long. -/
def alignB : Asg := promote allShort 0

/-- An encoding where the "long" form is *smaller* than the short form
(short size 2, long size 1, reach 1). -/
def invPrm : Params := ⟨2, 1, 1⟩

/-- Branch 0 jumps to itself; branch 1 jumps back over branch 0. -/
def invProg : Prog := [.branch 0, .branch 0]

/-- Short size 1, long size 2, reach 2; monotone sizes (no alignment). -/
def oscPrm : Params := ⟨1, 2, 2⟩

/-- Two mutually spanning branches: branch 1 jumps forward over branch 2 and
branch 2 jumps back over branch 1. -/
def oscProg : Prog := [.fixed 1, .branch 3, .branch 0]

/-- Zero-size short branches: short size 0, long size 1, reach 5. -/
def zeroPrm : Params := ⟨0, 1, 5⟩

/-- A branch to itself followed by a 1-byte instruction. -/
def zeroProg : Prog := [.branch 0, .fixed 1]

/-- Short size 1, long size 2, reach 5. -/
def fwdPrm : Params := ⟨1, 2, 5⟩

/-- A forward branch over two 1-byte instructions. -/
def fwdProg : Prog := [.branch 2, .fixed 1, .fixed 1]

/-- A promotion chain followed by a self-branch that stays short: short 1,
long 2, reach 1 (`chainPrm`). -/
def chainExtraProg : Prog := [.fixed 2, .branch 0, .branch 1, .branch 3]

/-- The valid assignment with exactly positions 1, 2 and 3 long. -/
def chainExtraB : Asg := fun i => decide (1 ≤ i ∧ i ≤ 3)

/-- A single branch to itself: its distance is always 0. -/
def selfProg : Prog := [.branch 0]

/-- Two forward branches over an alignment directive (with `alignPrm`):
grow-and-shrink started from all-short cycles with period 4. -/
def alignOscProg : Prog := [.branch 2, .branch 3, .align 4]

/-- Inverted sizes (short 2, long 1, reach 3), no alignment. -/
def invOscPrm : Params := ⟨2, 1, 3⟩

/-- Two mutually spanning branches after a 2-byte instruction (with
`invOscPrm`): grow-and-shrink started from all-short cycles with period 2. -/
def invOscProg : Prog := [.fixed 2, .branch 3, .branch 0]

/-- A short branch to an alignment directive (with `fwdPrm`): promoting the
branch makes the padding 0 bytes, so instruction 1 and 2 share an address. -/
def alignZeroProg : Prog := [.branch 1, .align 2, .fixed 1]

/-- Two backward branches that are both in reach while short (with
`chainPrm`); promoting branch 1 alone pushes branch 2 out of reach. -/
def cascadeValidProg : Prog := [.fixed 1, .branch 0, .branch 1]

/-! ### `padTo` -/

theorem padTo_example_pos : padTo 4 1 = 3 := by decide
theorem padTo_example_aligned : padTo 4 8 = 0 := by decide

/-! ### `addr`, `size`, `dist` -/

theorem addr_example : addr chainPrm chainProg allShort 3 = 4 := by decide
theorem size_example_long : size chainPrm chainProg (promote allShort 1) 1 = 2 := by decide
theorem size_example_align : size alignPrm alignProg allShort 1 = 3 := by decide
theorem size_example_align_shrinks : size alignPrm alignProg alignB 1 = 2 := by decide
theorem dist_example : dist chainPrm chainProg allShort 1 0 = 2 := by decide

/-! ### `Asg.Le` -/

theorem asgLe_example_pos : Asg.Le allShort (promote allShort 0) := Asg.Le.allShort _

theorem asgLe_example_neg : ¬ Asg.Le (promote allShort 0) allShort := by
  intro h
  have := h 0 (by decide)
  cases this

/-- `Asg.Le` compares every index, including ones that hold no branch: here
`a` and `b` agree at the only branch position and `b` is valid, yet
`¬ Asg.Le a b` because `a` is `true` at the irrelevant index 99. -/
theorem asgLe_compares_nonbranch_positions :
    Valid fwdPrm selfProg allShort ∧ Asg.LeOnBranches selfProg (promote allShort 99) allShort ∧
    ¬ Asg.Le (promote allShort 99) allShort := by
  refine ⟨by decide, ?_, ?_⟩
  · intro i hi ha
    rcases i with _ | i
    · revert ha; decide
    · simp [isBranchAt, selfProg] at hi
  · intro h
    have := h 99 (by decide)
    cases this

theorem asgLeOnBranches_example_pos :
    Asg.LeOnBranches chainProg (promote allShort 0) allShort := by
  intro i hi ha
  rcases i with _ | i
  · simp [isBranchAt, chainProg, Instr.isBranch] at hi
  · simp [promote, allShort] at ha

theorem asgLeOnBranches_example_neg :
    ¬ Asg.LeOnBranches chainProg (promote allShort 1) allShort := by
  intro h
  have := h 1 (by decide) (by decide)
  cases this

/-! ### `outOfReach` and `Valid` -/

theorem outOfReach_example_pos : outOfReach chainPrm chainProg allShort 1 = true := by decide
theorem outOfReach_example_neg : outOfReach chainPrm chainProg allShort 2 = false := by decide
/-- A long branch is never out of reach. -/
theorem outOfReach_example_long : outOfReach chainPrm chainProg (promote allShort 1) 1 = false := by
  decide

theorem valid_example_pos : Valid chainPrm [.fixed 1, .branch 0] allShort := by decide
theorem valid_example_pos_long : Valid chainPrm chainProg (fun _ => true) := by decide
theorem valid_example_neg : ¬ Valid chainPrm chainProg allShort := by decide
/-- Promoting branch 1 alone is not enough: branch 2 then falls out of reach. -/
theorem valid_example_neg_cascade : ¬ Valid chainPrm chainProg (promote allShort 1) := by decide

/-! ### `step`, `relax`, `relaxLoop` -/

theorem step_example : step chainPrm chainProg allShort 1 = true ∧
    step chainPrm chainProg allShort 2 = false := by decide

theorem relax_example : relax chainPrm chainProg allShort 1 = true ∧
    relax chainPrm chainProg allShort 2 = true := by decide

theorem relaxLoop_example_pos :
    (relaxLoop chainPrm chainProg 3 allShort).isSome = true := by decide

theorem relaxLoop_example_neg : relaxLoop chainPrm chainProg 2 allShort = none := by decide

/-! ### `stepGS` -/

/-- Grow-and-shrink demotes a long branch that fits short. -/
theorem stepGS_example_demotes : stepGS oscPrm oscProg (promote allShort 1) 1 = false := by decide
theorem stepGS_example_promotes : stepGS oscPrm oscProg (promote allShort 1) 2 = true := by decide

/-! ### `stepGSCurrent` (contrast definition) -/

/-- Reading the current layout, the long branch that `stepGS` demotes
(`stepGS_example_demotes`) stays long: its own long size lies in its span. -/
theorem stepGSCurrent_example_keeps_long :
    stepGSCurrent oscPrm oscProg (promote allShort 1) 1 = true := by decide

/-- A short branch within reach stays short. -/
theorem stepGSCurrent_example_short : stepGSCurrent oscPrm oscProg allShort 1 = false := by
  decide

/-! ### `NoAlign` -/

theorem noAlign_example_pos : NoAlign chainProg := by decide
theorem noAlign_example_neg : ¬ NoAlign alignProg := by decide

/-! ### `totalSize` -/

theorem totalSize_example : totalSize alignPrm alignProg allShort = 5 ∧
    totalSize alignPrm alignProg alignB = 5 := by decide

/-! ### `SizesMonotone` and `DistMonotone` -/

/-- **Result 2c (concrete sufficient condition for monotone sizes).**  A
program without alignment directives, under parameters with
`shortSize ≤ longSize`, has every instruction size monotone in the
assignment. -/
theorem sizesMonotone_of_noAlign_of_short_le_long {prm : Params} {p : Prog}
    (hna : NoAlign p) (hsl : prm.shortSize ≤ prm.longSize) : SizesMonotone prm p := by
  intro a b hab k
  unfold size
  rcases hk : p[k]? with _ | ins
  · exact Nat.le_refl _
  · have hmem : ins ∈ p := List.mem_of_getElem? hk
    cases ins with
    | fixed s => exact Nat.le_refl _
    | branch t =>
      simp only [instrSize]
      cases ha : a k
      · cases b k
        · exact Nat.le_refl _
        · exact hsl
      · rw [hab k ha]
        exact Nat.le_refl _
    | align m =>
      have := hna _ hmem
      simp [Instr.isAlign] at this

theorem sizesMonotone_example_pos : SizesMonotone chainPrm chainProg :=
  sizesMonotone_of_noAlign_of_short_le_long (by decide) (by decide)

theorem sizesMonotone_example_neg_align : ¬ SizesMonotone alignPrm alignProg := by
  intro h
  have := h allShort alignB (Asg.Le.allShort _) 1
  revert this
  decide

theorem sizesMonotone_example_neg_inverted : ¬ SizesMonotone invPrm invProg := by
  intro h
  have := h allShort (promote allShort 0) (Asg.Le.allShort _) 0
  revert this
  decide

theorem distMonotone_example_neg_align : ¬ DistMonotone alignPrm alignProg := by
  intro h
  have := h allShort alignB (Asg.Le.allShort _) 2 1 rfl
  revert this
  decide

theorem distMonotone_example_neg_inverted : ¬ DistMonotone invPrm invProg := by
  intro h
  have := h allShort (promote allShort 0) (Asg.Le.allShort _) 1 0 rfl
  revert this
  decide

/-! ### `AllSizesPositive` -/

theorem allSizesPositive_of_structural {prm : Params} {p : Prog}
    (hs : 0 < prm.shortSize) (hl : 0 < prm.longSize)
    (hf : ∀ s, Instr.fixed s ∈ p → 0 < s) (hna : NoAlign p) : AllSizesPositive prm p := by
  intro a k hk
  unfold size
  rcases hpk : p[k]? with _ | ins
  · rw [List.getElem?_eq_getElem hk] at hpk
    cases hpk
  · have hmem : ins ∈ p := List.mem_of_getElem? hpk
    cases ins with
    | fixed s => exact hf s hmem
    | branch t =>
      simp only [instrSize]
      cases a k
      · exact hs
      · exact hl
    | align m =>
      have := hna _ hmem
      simp [Instr.isAlign] at this

theorem allSizesPositive_example_pos : AllSizesPositive fwdPrm fwdProg := by
  apply allSizesPositive_of_structural (by decide) (by decide) _ (by decide)
  intro s hs
  simp [fwdProg] at hs
  omega

theorem allSizesPositive_example_neg : ¬ AllSizesPositive zeroPrm zeroProg := by
  intro h
  have := h allShort 0 (by decide)
  revert this
  decide

/-! ### `SizesPositiveAt` -/

theorem sizesPositiveAt_example_pos : SizesPositiveAt fwdPrm alignZeroProg allShort := by decide

/-- After promoting branch 0 the alignment directive pads 0 bytes. -/
theorem sizesPositiveAt_example_neg :
    ¬ SizesPositiveAt fwdPrm alignZeroProg (promote allShort 0) := by decide

/-! ### `emitDisp` -/

theorem emitDisp_example_pos : emitDisp chainPrm cascadeValidProg allShort 2 = some (-1) := by
  decide

/-- A short branch out of reach has no encodable displacement. -/
theorem emitDisp_example_neg_reach : emitDisp chainPrm chainProg allShort 1 = none := by decide

/-- A position without a branch has no displacement. -/
theorem emitDisp_example_neg_nonbranch : emitDisp chainPrm chainProg allShort 0 = none := by decide

/-- A long branch always has an encodable displacement. -/
theorem emitDisp_example_long : emitDisp chainPrm chainProg (promote allShort 1) 1 = some (-2) := by
  decide

/-! ### `disp` and `JumpsTo` -/

/-- The displacement computed from a layout lands on the target in that same
layout. -/
theorem jumpsTo_disp_self (prm : Params) (p : Prog) (a : Asg) (i t : Nat) :
    JumpsTo prm p a i (disp prm p a i t) t := by
  unfold JumpsTo disp
  omega

theorem jumpsTo_example_pos : JumpsTo fwdPrm fwdProg allShort 0 2 2 := by decide

/-- A displacement computed for the all-short layout, reused after promoting
the branch itself, lands one instruction early. -/
theorem jumpsTo_example_neg : ¬ JumpsTo fwdPrm fwdProg (promote allShort 0) 0 2 2 := by decide

/-! ### `LandsExactly` -/

/-- The short forward branch of `fwdProg` is within reach, its displacement is
2, and that displacement lands on instruction 2 and on no other index `≤ 3`. -/
theorem landsExactly_example_pos : LandsExactly fwdPrm fwdProg allShort 0 2 :=
  ⟨2, by decide, by decide⟩

/-- With a zero-size short branch, its displacement 0 lands on index 0 (its
target) and also on index 1, which has the same address. -/
theorem landsExactly_example_neg_zero : ¬ LandsExactly zeroPrm zeroProg allShort 0 0 := by
  rintro ⟨d, hd, h⟩
  have he : emitDisp zeroPrm zeroProg allShort 0 = some 0 := by decide
  rw [he] at hd
  cases hd
  have h1 := (h 1 (by decide)).mp (by decide)
  revert h1
  decide

/-- A short branch out of reach has no encodable displacement, so it does not
land exactly. -/
theorem landsExactly_example_neg_reach : ¬ LandsExactly chainPrm chainProg allShort 1 0 := by
  rintro ⟨d, hd, _⟩
  rw [emitDisp_example_neg_reach] at hd
  cases hd

end Toy.Relax
