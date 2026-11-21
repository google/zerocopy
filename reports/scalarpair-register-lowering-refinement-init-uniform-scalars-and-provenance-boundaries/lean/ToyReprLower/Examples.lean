import ToyReprLower.Union

/-!
# Positive and negative examples for the definitions
-/

namespace Toy.ReprLower

/-- The full range: every data vector. -/
def fullRange : List Nat → Bool := fun _ => true

/-- A non-zero range: some data byte is non-zero (a `NonZero`/non-null style niche). -/
def nonZeroRange : List Nat → Bool := fun ds => ds.any (· != 0)

/-- A range that admits exactly the data vectors of length `2` (used only to probe the
in-bounds hypotheses). -/
def len2Range : List Nat → Bool := fun ds => ds.length == 2

/-! ## Abstract bytes and their order -/

-- positive: adding provenance makes a byte more defined; uninit is below everything
example : (AByte.bits 1).leb (.ptrFrag 1 7 0) = true := by decide
example : AByte.uninit.leb (.ptrFrag 1 7 0) = true := by decide
-- negative: dropping provenance, changing data, or initializing-to-uninit is not "more defined"
example : (AByte.ptrFrag 1 7 0).leb (.bits 1) = false := by decide
example : (AByte.bits 1).leb (.bits 2) = false := by decide
example : (AByte.bits 1).leb .uninit = false := by decide

example : BytesLe [.uninit, .bits 1] [.bits 0, .ptrFrag 1 7 0] := by decide
example : ¬ BytesLe [.bits 1] [.bits 1, .bits 2] := by decide
example : ¬ BytesLe [.ptrFrag 1 7 0] [.bits 1] := by decide

/-! ## Segments, coherence, pointer lowering -/

example : seg [.bits 0, .bits 1, .bits 2] 1 5 = [.bits 1, .bits 2] := by decide
example : fragsFrom 7 0 [.ptrFrag 1 7 0, .ptrFrag 2 7 1] = true := by decide
example : fragsFrom 7 0 [.ptrFrag 2 7 1, .ptrFrag 1 7 0] = false := by decide
example : fragsFrom 7 0 [.ptrFrag 1 7 0, .ptrFrag 2 8 1] = false := by decide

-- positive: one pointer's fragments in order keep their provenance
example : ptrProv [.ptrFrag 1 7 0, .ptrFrag 2 7 1] = some 7 := by decide
example : ptrLower [.ptrFrag 1 7 0, .ptrFrag 2 7 1] = .ptr (some 7) [1, 2] := by decide
-- plain bytes, mixed provenance, shifted positions, or a mix of plain bytes and fragments give a
-- provenance-free pointer (MiniRust `decode_ptr`)
example : ptrLower [.bits 1, .bits 2] = .ptr none [1, 2] := by decide
example : ptrProv [.ptrFrag 1 7 0, .ptrFrag 2 8 1] = none := by decide
example : ptrLower [.ptrFrag 1 7 0, .ptrFrag 2 8 1] = .ptr none [1, 2] := by decide
example : ptrLower [.ptrFrag 1 7 1, .ptrFrag 2 7 2] = .ptr none [1, 2] := by decide
example : ptrLower [.bits 1, .ptrFrag 2 7 1] = .ptr none [1, 2] := by decide

example : coherentFor (.int 2) [.bits 1, .bits 2] = true := by decide
example : coherentFor (.int 2) [.ptrFrag 1 7 0, .ptrFrag 2 7 1] = false := by decide
example : coherentFor (.ptr 2) [.ptrFrag 1 7 0, .ptrFrag 2 7 1] = true := by decide
example : coherentFor (.ptr 2) [.bits 1, .bits 2] = true := by decide
example : coherentFor (.ptr 2) [.ptrFrag 2 7 1, .ptrFrag 1 7 0] = false := by decide
example : coherentFor (.ptr 2) [.ptrFrag 1 7 0, .ptrFrag 2 8 1] = false := by decide

/-! ## Lowering and raising one scalar -/

-- positive: a union scalar keeps partially initialized bytes and fragments as they are
example : lowerScalar (.union (.int 2)) [.bits 1, .uninit] = .raw [.bits 1, .uninit] := rfl
-- positive: an initialized integer scalar reads fully initialized in-range bytes
example : lowerScalar (.initialized (.int 2) fullRange) [.bits 1, .bits 2] = .int [1, 2] := by decide
-- positive: an initialized pointer scalar reads one pointer's fragments with its provenance
example : lowerScalar (.initialized (.ptr 2) fullRange) [.ptrFrag 1 7 0, .ptrFrag 2 7 1] =
    .ptr (some 7) [1, 2] := by decide
-- negative: partial initialization or out-of-range data give poison
example : lowerScalar (.initialized (.int 2) fullRange) [.bits 1, .uninit] = .poison := by decide
example : lowerScalar (.initialized (.int 1) nonZeroRange) [.bits 0] = .poison := by decide
-- mismatched fragments under a pointer scalar give a provenance-free pointer, not poison
example : lowerScalar (.initialized (.ptr 2) fullRange) [.ptrFrag 1 7 0, .ptrFrag 2 8 1] =
    .ptr none [1, 2] := by decide
-- an integer scalar built from pointer fragments is provenance-free
example : lowerScalar (.initialized (.int 2) fullRange) [.ptrFrag 1 7 0, .ptrFrag 2 7 1] =
    .int [1, 2] := by decide

example : raiseScalar (.initialized (.int 2) fullRange) .poison = [.uninit, .uninit] := by decide
example : raiseScalar (.initialized (.ptr 2) fullRange) (.ptr (some 7) [1, 2]) =
    [.ptrFrag 1 7 0, .ptrFrag 2 7 1] := by decide
example : raiseScalar (.initialized (.ptr 2) fullRange) (.ptr none [1, 2]) ≠
    [.ptrFrag 1 7 0, .ptrFrag 2 7 1] := by decide

/-! ## Representations -/

example : (BRepr.pair (.initialized (.int 1) fullRange) (.initialized (.int 1) fullRange) 2).inExtent 1
    = false := by decide
example : (BRepr.pair (.initialized (.int 1) fullRange) (.initialized (.int 1) fullRange) 2).inExtent 2
    = true := by decide
example : BRepr.memory.inExtent 5 = true := rfl

-- positive: padding raises to uninit, scalars raise at their offsets
example : raise 3 (.pair (.initialized (.int 1) fullRange) (.initialized (.int 1) fullRange) 2)
    (.two (.int [1]) (.int [2])) = [.bits 1, .uninit, .bits 2] := by decide
-- negative: a lowered value of the wrong shape raises to all-uninit bytes
example : raise 2 (.scalar (.union (.int 2))) (.two (.int [1]) (.int [2])) = [.uninit, .uninit] := by
  decide

/-! ## Refinement and the conditions -/

example : RoundTripRefines 2 (.scalar (.union (.int 2))) (· = [.bits 1, .uninit]) := by
  intro x hx; cases hx; decide
example : ¬ RoundTripRefines 2 (.scalar (.initialized (.int 2) fullRange)) (· = [.bits 1, .uninit]) := by
  intro h; have := h _ rfl; revert this; decide

example : OutsideExtentsUninit 2 (.scalar (.initialized (.int 1) fullRange)) (· = [.bits 1, .uninit]) := by
  intro x hx; cases hx; decide
example : ¬ OutsideExtentsUninit 2 (.scalar (.initialized (.int 1) fullRange)) (· = [.bits 1, .bits 2]) := by
  intro h; have := h _ rfl 1 (by decide) (by decide); revert this; decide

example : InitUniform (.scalar (.initialized (.int 2) fullRange)) (· = [.uninit, .uninit]) := by
  intro x hx; cases hx; decide
example : ¬ InitUniform (.scalar (.initialized (.int 2) fullRange)) (· = [.bits 1, .uninit]) := by
  intro h; have := h _ rfl; revert this; decide

example : RangeIncl (.scalar (.initialized (.int 1) nonZeroRange)) (· = [.bits 3]) := by
  intro x hx; cases hx; decide
example : ¬ RangeIncl (.scalar (.initialized (.int 1) nonZeroRange)) (· = [.bits 0]) := by
  intro h; have := h _ rfl; revert this; decide
-- the range is consulted only on fully initialized bytes
example : rangeInclAt (.initialized (.int 2) nonZeroRange) [.bits 0, .uninit] = true := by decide
example : rangeInclAt (.initialized (.int 2) nonZeroRange) [.uninit, .uninit] = true := by decide
example : rangeInclAt (.initialized (.int 2) nonZeroRange) [.bits 0, .bits 0] = false := by decide

example : ProvCoherent (.scalar (.initialized (.ptr 2) fullRange))
    (· = [.ptrFrag 1 7 0, .ptrFrag 2 7 1]) := by
  intro x hx; cases hx; decide
example : ¬ ProvCoherent (.scalar (.initialized (.int 2) fullRange))
    (· = [.ptrFrag 1 7 0, .ptrFrag 2 7 1]) := by
  intro h; have := h _ rfl; revert this; decide

/-! ## Typed reads and outcomes -/

example : readPtr 0 2 [.ptrFrag 1 7 0, .ptrFrag 2 7 1] = some (.ptr (some 7) [1, 2]) := by decide
example : readPtr 0 2 [.ptrFrag 1 7 0, .ptrFrag 2 8 1] = some (.ptr none [1, 2]) := by decide
example : readInt 0 2 [.bits 1, .uninit] = none := by decide
example : readInt 0 2 [.ptrFrag 1 7 0, .ptrFrag 2 7 1] = some (.int [1, 2]) := by decide
example : OutLe (some (.ptr none [1])) (some (.ptr (some 7) [1])) := by decide
example : ¬ OutLe (some (.ptr (some 7) [1])) (some (.ptr none [1])) := by decide
example : OutLe none (some (.int [1])) := by decide
example : ¬ OutLe (some (.int [1])) none := by decide

/-! ## Register-level reinterpretation -/

example : regCastScalar (.initialized (.ptr 2) fullRange) (.initialized (.int 2) fullRange)
    (.ptr (some 7) [1, 2]) = .int [1, 2] := rfl
example : regCastScalar (.initialized (.int 2) fullRange) (.initialized (.ptr 2) fullRange)
    (.int [1, 2]) = .ptr none [1, 2] := rfl
example : regCastScalar (.initialized (.ptr 2) fullRange) (.union (.int 2))
    (.ptr (some 7) [1, 2]) = .raw [.ptrFrag 1 7 0, .ptrFrag 2 7 1] := by decide
example : regCastScalar (.union (.int 2)) (.initialized (.int 2) fullRange)
    (.raw [.bits 1, .uninit]) = .raw [.bits 1, .uninit] := rfl

example : DisciplineCompat (.initialized (.int 1) nonZeroRange) (.initialized (.int 1) fullRange) := by
  intro ds _ _; rfl
example : ¬ DisciplineCompat (.initialized (.int 1) fullRange) (.initialized (.int 1) nonZeroRange) := by
  intro h; have := h [0] rfl rfl; revert this; decide
example : DisciplineCompat (.union (.int 1)) (.union (.ptr 1)) := trivial
example : ¬ DisciplineCompat (.union (.int 1)) (.initialized (.int 1) fullRange) := id
example : DisciplineCompatAnyLen (.initialized (.int 1) nonZeroRange) (.initialized (.int 1) fullRange) := by
  intro ds _; rfl
example : ¬ DisciplineCompatAnyLen (.initialized (.int 2) fullRange) (.initialized (.int 2) len2Range) := by
  intro h; have := h [0] rfl; revert this; decide
-- a pair reinterpreted as an `initialized` scalar is not modelled: the lowered value passes unchanged
example : regCast (.pair (.initialized (.int 1) fullRange) (.initialized (.int 1) fullRange) 1)
    (.scalar (.initialized (.int 2) fullRange)) (.two (.int [1]) (.int [2])) =
    .two (.int [1]) (.int [2]) := rfl
example : regCast (.pair (.initialized (.int 1) fullRange) (.initialized (.int 1) fullRange) 1)
    (.scalar (.union (.int 2))) (.two (.int [1]) (.int [2])) = .one (.raw [.bits 1, .bits 2]) := rfl

/-! ## Unions -/

example : unionMove trivialUnionValidity nzOrU8 [.uninit] = some [.uninit] := by decide
example : unionMove trivialUnionValidity nzOrU8 [] = none := by decide
example : unionMove emptyUnionValidity nzOrU8 [.uninit] = none := by decide
example : readField u8Field [.bits 0] = some [.bits 0] := by decide
example : readField nonZeroU8Field [.bits 0] = none := by decide
example : writeBytes [.bits 7, .uninit, .bits 9] 1 [.bits 1] = [.bits 7, .bits 1, .bits 9] := by decide
example : writeBytes [.bits 7] 1 [.bits 1] = [.bits 7] := by decide
example : nicheInheritingMove nonZeroU8Field [.bits 5] = some [.bits 5] := by decide
example : nicheInheritingMove nonZeroU8Field [.bits 0] = none := by decide
example : ¬ FieldwiseUninhabited nzOrU8 := by
  intro h; have := h u8Field (by simp [nzOrU8]) [.bits 0]; revert this; decide
example : writeMask 3 1 1 = [false, true, false] := by decide
example : laneSelect [false, true] [.bits 7, .uninit] [.bits 0, .bits 1] = [.bits 7, .bits 1] := by
  decide
example : mergeWrite (.raw [.bits 7, .uninit]) 1 [.bits 1] = .raw [.bits 7, .bits 1] := by decide
example : mergeWrite (.int [7]) 0 [.bits 1] = .int [7] := rfl
example : wholeWrite 2 .uninit 1 [.bits 1] = .raw [.uninit, .bits 1] := by decide
example : hasUndef (.raw [.bits 1, .uninit]) = true := by decide
example : hasUndef (.int [1]) = false := rfl
example : passArg true (.raw [.bits 1]) = some (.raw [.bits 1]) := by decide
example : passArg true (.raw [.uninit]) = none := by decide

end Toy.ReprLower
